#!/usr/bin/env python3
import base64
import hashlib
import html
import json
import os
import re
import random
import pymysql
import threading
import time
from pathlib import Path
from functools import wraps
from flask import Flask, g, jsonify, request, send_from_directory, session, redirect, url_for, render_template_string
from flask_sock import Sock
from Crypto.Cipher import AES
from apscheduler.schedulers.background import BackgroundScheduler
from datetime import datetime

BASE_DIR = Path(__file__).resolve().parent
DB_CONFIG = {
    "host": "127.0.0.1",
    "user": "oldchat",
    "password": "PASSWORD",
    "database": "oldchat",
    "charset": "utf8mb4",
    "autocommit": False
}
DATA_DIR = BASE_DIR / "data"
UPLOAD_DIR = BASE_DIR / "uploads"
UPDATE_DIR = BASE_DIR / "update"
UPDATE_FILE = UPDATE_DIR / "update.json"
LEGACY_UPDATE_FILE = DATA_DIR / "update.json"
TABLE_FIELDS = {
    "users": ["id","telephone","password","oldchat_id","user_name","head_url","cover_url","signature","sex","location","birthday","type","balance","old_coins","last_daily_reward"],
    "groups": ["id","group_id","group_name","owner_id","members","description","image_path","maxusers","authority","affiliations","receive","is_common","is_in","share_location","type"],
    "friendships": ["id","user_tel","friend_tel"],
    "friend_requests": ["id","user_tel","friend_tel","status","created_at"],
    "moments": ["id","user_tel","content","image_url","image_urls","likes","comments","created_at"],
    "messages": ["id","conversation_id","sender_tel","sender_name","sender_head_url","message_type","media_url","receiver_id","is_group","content","timestamp"],
    "bugs": ["id","user_tel","content","device","app_version","created_at"],
    "reports": ["id","reporter_tel","target_tel","device_id","reason","created_at","status","ban_until","handled_at","handler"],
    "group_requests": ["id","group_id","user_tel","created_at","status","handled_at","handler"],
    "group_announcements": ["id","group_id","content","creator","created_at","updated_at","status"],
    "group_announcement_reads": ["id","announcement_id","group_id","user_tel","read_at"],
    "device_bans": ["id","device_id","status","ban_until","created_at","updated_at","reason","handler"],
    "user_devices": ["id","user_tel","device_id","ip","created_at","updated_at"],
    "transactions": ["id","from_user","to_user","amount","type","description","created_at"],
    "banned_words": ["id","word","created_at"],
}

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 100 * 1024 * 1024
sock = Sock(app)
app.secret_key = os.environ.get("OLDCHAT_SECRET_KEY", "oldchat-secret")
ADMIN_USER = os.environ.get("OLDCHAT_ADMIN_USER", "admin")
ADMIN_PASSWORD = os.environ.get("OLDCHAT_ADMIN_PASS", "admin123")

SECRET_KEY = b"OldChatEncrypt16"
SECRET_IV = b"OldChatInitVect1"
WS_CLIENTS = {}
WS_LOCK = threading.Lock()
CALL_WS_CLIENTS = {}
CALL_WS_LOCK = threading.Lock()

import time
import threading
from collections import defaultdict, deque
from functools import wraps

RATE_LIMIT = defaultdict(lambda: deque(maxlen=100))
RATE_LIMIT_LOCK = threading.Lock()

def rate_limit(limit_per_sec=3, exempt_paths=('/health', '/uploads/', '/update/', '/ws', '/ws_call')):
    def decorator(f):
        @wraps(f)
        def decorated(*args, **kwargs):
            path = request.path
            if path.startswith(exempt_paths) or path == '/':
                return f(*args, **kwargs)
            client_ip = request.headers.get('X-Forwarded-For', request.remote_addr).split(',')[0].strip()
            key = f"{client_ip}:{path}"
            now = time.time()
            with RATE_LIMIT_LOCK:
                dq = RATE_LIMIT[key]
                while dq and dq[0] < now - 1:
                    dq.popleft()
                if len(dq) >= limit_per_sec:
                    return json_response("0", "", "请求过于频繁，请稍后再试"), 429
                dq.append(now)
            return f(*args, **kwargs)
        return decorated
    return decorator

def message_rate_limit(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        client_ip = request.headers.get('X-Forwarded-For', request.remote_addr).split(',')[0].strip()
        key = f"msg:{client_ip}"
        now = time.time()
        with RATE_LIMIT_LOCK:
            if key not in RATE_LIMIT:
                RATE_LIMIT[key] = []
            RATE_LIMIT[key] = [t for t in RATE_LIMIT[key] if now - t < 1]
            if len(RATE_LIMIT[key]) >= 1:
                return jsonify({"status":"0","data":"","info":"发送消息过快，请稍后再试"}), 429
            RATE_LIMIT[key].append(now)
        return f(*args, **kwargs)
    return decorated

ALLOWED_IMAGE_MAGIC = {
    b'\xff\xd8\xff': 'jpg',
    b'\x89PNG\r\n\x1a\n': 'png',
    b'GIF87a': 'gif',
    b'GIF89a': 'gif',
    b'RIFF....WEBP': 'webp',
}
ALLOWED_MEDIA_MAGIC = {
    b'\xff\xd8\xff': 'jpg',
    b'\x89PNG\r\n\x1a\n': 'png',
    b'GIF87a': 'gif', b'GIF89a': 'gif',
    b'RIFF....WEBP': 'webp',
    b'....ftyp': 'mp4',
    b'....ftypisom': 'mp4',
    b'ID3': 'mp3',
    b'OggS': 'ogg',
    b'RIFF....WAVE': 'wav',
}
def validate_file_header(file_stream, allowed_magic_dict):
    header = file_stream.read(12)
    file_stream.seek(0)
    for magic, ext in allowed_magic_dict.items():
        if header.startswith(magic):
            return True
    return False

def now_ms(): return int(time.time()*1000)
def parse_int(v, d=0):
    try: return int(str(v))
    except: return d
def parse_bool(v): return str(v).strip().lower() in ("1","true","yes","on")
def parse_datetime(value, is_end=False):
    if not value: return 0
    text=str(value).strip()
    if text.isdigit(): return int(text) if len(text)>10 else int(text)*1000
    for fmt in ("%Y-%m-%d","%Y-%m-%d %H:%M","%Y-%m-%d %H:%M:%S"):
        try:
            ts=int(time.mktime(time.strptime(text,fmt))*1000)
            if is_end and fmt=="%Y-%m-%d": ts+=24*3600*1000-1
            return ts
        except: continue
    return 0
def format_datetime(ts_ms):
    if ts_ms<=0: return ""
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ts_ms/1000.0))
def admin_logged_in(): return bool(session.get("admin"))
def get_param(name, default=""):
    payload=getattr(g,"payload",None)
    if payload and name in payload:
        v=payload.get(name,default)
        return "" if v is None else str(v)
    return request.values.get(name,default)
def get_optional_param(name):
    payload=getattr(g,"payload",None)
    if payload:
        if name not in payload: return None
        v=payload.get(name)
        return "" if v is None else str(v)
    if name not in request.values: return None
    v=request.values.get(name)
    return "" if v is None else str(v)
def get_optional_param_any(*names):
    for n in names:
        v=get_optional_param(n)
        if v is not None: return v
    return None
def get_device_id():
    return (get_param("device_id","").strip() or get_param("deviceId","").strip())
def get_client_ip():
    forwarded=request.headers.get("X-Forwarded-For","")
    if forwarded:
        parts=[i.strip() for i in forwarded.split(",") if i.strip()]
        if parts: return parts[0]
    real_ip=request.headers.get("X-Real-IP","").strip()
    if real_ip: return real_ip
    return request.remote_addr or ""
def encrypt_text(text):
    if text is None: return ""
    cipher=AES.new(SECRET_KEY,AES.MODE_CBC,SECRET_IV)
    pad_len=16-(len(text.encode())%16)
    data=text.encode()+bytes([pad_len])*pad_len
    return base64.b64encode(cipher.encrypt(data)).decode()
def decrypt_text(text):
    if not text: return ""
    decoded=base64.b64decode(text)
    cipher=AES.new(SECRET_KEY,AES.MODE_CBC,SECRET_IV)
    dec=cipher.decrypt(decoded)
    pad_len=dec[-1]
    if pad_len<=16: dec=dec[:-pad_len]
    return dec.decode()
@app.before_request
def decode_payload():
    g.payload=None
    g.encrypted_request=False
    payload=get_param("payload")
    if payload:
        try:
            decrypted=decrypt_text(payload)
            g.payload=json.loads(decrypted)
            g.encrypted_request=True
        except: pass
def json_response(status,data,info=""):
    if not isinstance(data,str): data=json.dumps(data,ensure_ascii=True)
    if getattr(g,"encrypted_request",False):
        data=encrypt_text(data)
        info=encrypt_text(info or "")
        return jsonify({"status":status,"data":data,"info":info,"enc":"1"})
    return jsonify({"status":status,"data":data,"info":info,"enc":"0"})
def hash_password(raw): return hashlib.md5(f"hJy*(){raw}".encode()).hexdigest()
def normalize_password(value): return hash_password(value.strip()) if value else ""
def build_upload_filename(ext):
    safe_ext=ext if ext and ext.startswith(".") else f".{ext}" if ext else ".dat"
    for _ in range(5):
        suffix=f"{now_ms()}_{random.randint(1000,9999)}"
        name=f"{suffix}{safe_ext}"
        if not (UPLOAD_DIR/name).exists(): return name
    return f"{now_ms()}_{random.randint(1000,9999)}{safe_ext}"
def init_storage():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
    UPDATE_DIR.mkdir(parents=True, exist_ok=True)
    ensure_update_file()
    conn = pymysql.connect(**DB_CONFIG)
    try:
        with conn.cursor() as cur:
            for table, fields in TABLE_FIELDS.items():
                cur.execute("SELECT COUNT(*) FROM information_schema.tables WHERE table_schema = DATABASE() AND table_name = %s", (table,))
                exists = cur.fetchone()[0] > 0
                if not exists:
                    other_fields = [f for f in fields if f != 'id']
                    cols = ",\n".join(f"`{f}` TEXT" for f in other_fields)
                    sql = f"CREATE TABLE `{table}` (id INT AUTO_INCREMENT PRIMARY KEY, {cols}) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4"
                    print(f"\n=== 创建表 {table} ===\n{sql}\n")
                    cur.execute(sql)
                else:
                    cur.execute(f"DESCRIBE `{table}`")
                    existing_cols = {row[0] for row in cur.fetchall()}
                    for field in fields:
                        if field not in existing_cols and field != 'id':
                            try:
                                alter_sql = f"ALTER TABLE `{table}` ADD COLUMN `{field}` TEXT"
                                print(f"添加字段 {table}.{field}: {alter_sql}")
                                cur.execute(alter_sql)
                            except Exception as e:
                                print(f"添加字段失败 {table}.{field}: {e}")
        conn.commit()
        print("数据库初始化完成")
    except Exception as e:
        print(f"初始化出错: {e}")
        conn.rollback()
        raise
    finally:
        conn.close()
def read_table(table: str) -> list:
    conn = pymysql.connect(**DB_CONFIG)
    try:
        with conn.cursor(pymysql.cursors.DictCursor) as cur:
            cur.execute(f"SELECT * FROM `{table}`")
            return list(cur.fetchall())
    finally:
        conn.close()
def write_table(table: str, rows: list) -> None:
    if not rows:
        return
    fields = TABLE_FIELDS[table]
    conn = pymysql.connect(**DB_CONFIG)
    try:
        with conn.cursor() as cur:
            cur.execute(f"DELETE FROM `{table}`")
            placeholders = ','.join(['%s'] * len(fields))
            sql = f"INSERT INTO `{table}` ({','.join(fields)}) VALUES ({placeholders})"
            cur.executemany(sql, [[row.get(f, '') for f in fields] for row in rows])
        conn.commit()
    finally:
        conn.close()
def next_id(rows):
    max_id=0
    for r in rows:
        try: max_id=max(max_id, int(r.get("id") or 0))
        except: pass
    return max_id+1
def find_user(users,tel):
    for u in users:
        if u.get("telephone")==tel: return u
    return {}
def find_group(groups,group_id):
    for g in groups:
        if g.get("group_id")==group_id: return g
    return {}
def split_members(val): return [m.strip() for m in re.split(r"[、,]",str(val)) if m.strip()]
def join_members(members): return "、".join([m for m in members if m])
def is_group_admin(group_row,user_tel):
    if not group_row or not user_tel: return False
    if group_row.get("owner_id")==user_tel: return True
    admins=split_members(group_row.get("authority",""))
    return user_tel in admins
def is_group_member(group_row,user_tel):
    if not group_row or not user_tel: return False
    if group_row.get("owner_id")==user_tel: return True
    members=split_members(group_row.get("members",""))
    return user_tel in members
def resolve_user_identifier(users, identifier):
    if not identifier: return ""
    for u in users:
        if u.get("telephone")==identifier or u.get("oldchat_id")==identifier:
            return u.get("telephone")
    return ""
def build_conversation_id(a,b):
    a,b=(a or "").strip(),(b or "").strip()
    if not a or not b: return ""
    return f"{a}_{b}" if a<=b else f"{b}_{a}"
def user_to_dict(row):
    if not row: return {}
    return {
        "id": str(row.get("id", "")),
        "telephone": row.get("telephone", ""),
        "oldChatId": row.get("oldchat_id", "") or row.get("telephone", ""),
        "userName": row.get("user_name", ""),
        "headUrl": row.get("head_url", ""),
        "coverUrl": row.get("cover_url", ""),
        "signature": row.get("signature", ""),
        "sex": row.get("sex", ""),
        "location": row.get("location", ""),
        "birthday": row.get("birthday", ""),
        "type": row.get("type", ""),
        "balance": row.get("balance", "0"),
        "old_coins": row.get("old_coins", "0"),   # 新增
    }
def group_to_dict(row):
    if not row: return {}
    base = {
        "id": str(row.get("id", "")),
        "group_id": row.get("group_id", ""),
        "group_name": row.get("group_name", ""),
        "owner_id": row.get("owner_id", ""),
        "members": row.get("members", ""),
        "description": row.get("description", ""),
        "image_path": row.get("image_path", ""),
        "maxusers": row.get("maxusers", ""),
        "authority": row.get("authority", ""),
        "affiliations": row.get("affiliations", ""),
        "receive": row.get("receive", ""),
        "is_common": row.get("is_common", ""),
        "is_in": row.get("is_in", ""),
        "share_location": row.get("share_location", ""),
        "type": row.get("type", ""),
    }
    base["groupId"] = base["group_id"]
    base["groupName"] = base["group_name"]
    base["ownerId"] = base["owner_id"]
    base["imagePath"] = base["image_path"]
    base["isCommon"] = base["is_common"]
    base["isIn"] = base["is_in"]
    base["shareLocation"] = base["share_location"]
    return base
def message_to_dict(row):
    if not row: return {}
    base = {
        "id": str(row.get("id", "")),
        "conversation_id": row.get("conversation_id", ""),
        "sender_tel": row.get("sender_tel", ""),
        "sender_name": row.get("sender_name", ""),
        "sender_head_url": row.get("sender_head_url", ""),
        "message_type": row.get("message_type", ""),
        "media_url": row.get("media_url", ""),
        "receiver_id": row.get("receiver_id", ""),
        "is_group": row.get("is_group", ""),
        "content": row.get("content", ""),
        "timestamp": str(row.get("timestamp", "0")),
    }
    base["conversationId"] = base["conversation_id"]
    base["senderTel"] = base["sender_tel"]
    base["senderName"] = base["sender_name"]
    base["senderHeadUrl"] = base["sender_head_url"]
    base["messageType"] = base["message_type"]
    base["mediaUrl"] = base["media_url"]
    base["receiverId"] = base["receiver_id"]
    base["isGroup"] = base["is_group"]
    return base
def parse_json_list(raw):
    if raw is None: return []
    if isinstance(raw,list): return raw
    try: v=json.loads(str(raw))
    except: v=[]
    return v if isinstance(v,list) else [str(raw)] if raw else []
def ensure_update_file():
    if UPDATE_FILE.exists(): return
    if LEGACY_UPDATE_FILE.exists():
        try: UPDATE_FILE.write_text(LEGACY_UPDATE_FILE.read_text(encoding="utf-8"),encoding="utf-8")
        except: pass
        return
    default={"version_code":"1","version_name":"1.0","apk_url":"","force":"0","message":"优化体验与修复问题"}
    UPDATE_FILE.write_text(json.dumps(default,ensure_ascii=True),encoding="utf-8")
def read_update_info():
    try:
        if UPDATE_FILE.exists():
            return json.loads(UPDATE_FILE.read_text(encoding="utf-8"))
        if LEGACY_UPDATE_FILE.exists():
            return json.loads(LEGACY_UPDATE_FILE.read_text(encoding="utf-8"))
    except: pass
    return {}
def build_apk_url(info):
    url=str(info.get("apk_url","")).strip()
    if not url:
        apk_file=str(info.get("apk_file","")).strip()
        if apk_file: url=f"/update/{apk_file.lstrip('/')}"
    if url and not url.startswith(('http','/')):
        url=f"/update/{url}"
    if url and not url.startswith('http'):
        url=f"http://{request.host}{url}"
    return url
def get_active_ban_until(reports,target_tel):
    now=now_ms()
    active=0
    perm=False
    for r in reports:
        if r.get("target_tel")!=target_tel: continue
        if r.get("status")!="banned": continue
        until=parse_int(r.get("ban_until"),0)
        if until==0: perm=True
        elif until>now and until>active: active=until
    if perm: return 0
    return active if active>0 else None
def ban_message(until):
    if until==0: return "账号已被封禁"
    if until>0: return f"账号已被封禁至 {format_datetime(until)}"
    return "账号已被封禁"
def device_ban_message(until):
    if until==0: return "设备已被封禁"
    if until>0: return f"设备已被封禁至 {format_datetime(until)}"
    return "设备已被封禁"
def find_device_ban(rows,device_id):
    for r in rows:
        if r.get("device_id")==device_id: return r
    return None
def get_active_device_ban_until(rows,device_id):
    now=now_ms()
    for r in rows:
        if r.get("device_id")!=device_id or r.get("status")!="banned": continue
        until=parse_int(r.get("ban_until"),0)
        if until==0: return 0
        if until>now: return until
    return None
def apply_device_ban(rows,device_id,duration,reason,handler):
    device_id=device_id.strip()
    if not device_id: return ""
    now=now_ms()
    target=find_device_ban(rows,device_id)
    if not target:
        target={"id":str(next_id(rows)),"device_id":device_id,"status":"banned","ban_until":"","created_at":str(now),"updated_at":str(now),"reason":"","handler":""}
        rows.append(target)
    target["status"]="banned"
    target["ban_until"]="0" if duration==0 else str(now+duration*1000)
    target["reason"]=reason
    target["updated_at"]=str(now)
    target["handler"]=handler
    return target["ban_until"]
def find_user_device(rows,user_tel):
    for r in rows:
        if r.get("user_tel")==user_tel: return r
    return None
def upsert_user_device(rows,user_tel,device_id,ip):
    now=str(now_ms())
    target=find_user_device(rows,user_tel)
    if target:
        target["device_id"]=device_id
        target["ip"]=ip
        target["updated_at"]=now
        return target
    row={"id":str(next_id(rows)),"user_tel":user_tel,"device_id":device_id,"ip":ip,"created_at":now,"updated_at":now}
    rows.append(row)
    return row
def push_ws(user_tel,payload):
    if not user_tel or not payload: return
    with WS_LOCK:
        clients=WS_CLIENTS.get(user_tel,[])[:]
    for c in clients:
        try: c.send(payload)
        except: pass
def get_old_coins(user_tel):
    """获取用户旧币余额，返回浮点数，若用户不存在返回 None"""
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return None
        val = user.get("old_coins", "0")
        try:
            return float(val) if val else 0.0
        except:
            return 0.0

def set_old_coins(user_tel, amount):
    """设置用户旧币余额（直接覆盖），成功返回 True，失败返回 False"""
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return False
        user["old_coins"] = str(amount)
        write_table("users", users)
        return True

def add_old_coins(user_tel, amount):
    """增加用户旧币，返回布尔值"""
    if amount <= 0:
        return False
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return False
        current = float(user.get("old_coins", "0") or "0")
        new_balance = current + amount
        user["old_coins"] = str(new_balance)
        write_table("users", users)
        return True

def deduct_old_coins(user_tel, amount):
    """扣除用户旧币，余额不足返回 False，成功返回 True"""
    if amount <= 0:
        return False
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return False
        current = float(user.get("old_coins", "0") or "0")
        if current < amount:
            return False
        new_balance = current - amount
        user["old_coins"] = str(new_balance)
        write_table("users", users)
        return True

def daily_reward_if_needed(user_tel):
    """
    检查用户今日是否已领取每日奖励，若未领取则增加10旧币并更新 last_daily_reward
    返回 (是否已奖励, 新余额)
    """
    from datetime import datetime
    today = datetime.now().strftime("%Y-%m-%d")
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return False, None
        last_reward = user.get("last_daily_reward", "")
        if last_reward == today:
            return False, float(user.get("old_coins", "0") or "0")
        # 未奖励，加10
        current = float(user.get("old_coins", "0") or "0")
        new_balance = current + 10
        user["old_coins"] = str(new_balance)
        user["last_daily_reward"] = today
        write_table("users", users)
        return True, new_balance
def build_ws_payload(msg):
    body=json.dumps(msg,ensure_ascii=True)
    return json.dumps({"type":"message","data":encrypt_text(body),"enc":"1"},ensure_ascii=True)
def build_kick_payload(msg):
    body=json.dumps({"message":msg},ensure_ascii=True)
    return json.dumps({"type":"kick","data":encrypt_text(body),"enc":"1"},ensure_ascii=True)
def kick_user(user_tel,message):
    if not user_tel: return
    push_ws(user_tel,build_kick_payload(message))
    with WS_LOCK:
        WS_CLIENTS.pop(user_tel,None)
def append_group_notice_message(messages,group_id,sender_tel,sender_name,sender_head_url,content):
    row={
        "id":str(next_id(messages)),
        "conversation_id":group_id,
        "sender_tel":sender_tel or "",
        "sender_name":sender_name or sender_tel or "",
        "sender_head_url":sender_head_url or "",
        "message_type":"group_notice",
        "media_url":"",
        "receiver_id":"",
        "is_group":"1",
        "content":content,
        "timestamp":str(now_ms()),
    }
    messages.append(row)
    return row
def parse_userlist(value):
    if not value: return []
    return [re.sub(r"\D","",p.strip().strip("'\"")) for p in value.split(",") if re.sub(r"\D","",p.strip().strip("'\""))]
def are_friends(friendships,user_tel,friend_tel):
    return any(r.get("user_tel")==user_tel and r.get("friend_tel")==friend_tel for r in friendships)
def find_group_announcement(rows,group_id):
    candidates=[r for r in rows if r.get("group_id")==group_id and r.get("status")!="deleted"]
    if not candidates: return {}
    candidates.sort(key=lambda r:parse_int(r.get("updated_at") or r.get("created_at")),reverse=True)
    return candidates[0]
def is_announcement_read(rows,announcement_id,user_tel):
    return any(r.get("announcement_id")==announcement_id and r.get("user_tel")==user_tel for r in rows)
def moment_to_dict(row,users):
    if not row: return {}
    user=find_user(users,row.get("user_tel",""))
    urls=parse_json_list(row.get("image_urls",""))
    if not urls and row.get("image_url"): urls=[row.get("image_url")]
    likes=[str(x) for x in parse_json_list(row.get("likes","")) if str(x).strip()]
    comments=[]
    for c in parse_json_list(row.get("comments","")):
        if not isinstance(c,dict): continue
        comment_user=find_user(users,c.get("user_tel",""))
        comments.append({
            "id":str(c.get("id","")),
            "user_tel":c.get("user_tel",""),
            "content":c.get("content",""),
            "created_at":str(c.get("created_at","0")),
            "user":user_to_dict(comment_user),
        })
    return {
        "id":str(row.get("id","")),
        "user_tel":row.get("user_tel",""),
        "content":row.get("content",""),
        "image_url":row.get("image_url",""),
        "image_urls":urls,
        "likes":likes,
        "comments":comments,
        "created_at":str(row.get("created_at","0")),
        "user":user_to_dict(user),
    }
def group_request_to_dict(row,user,group):
    return {
        "id":str(row.get("id","")),
        "group_id":row.get("group_id",""),
        "group_name":group.get("group_name","") if group else "",
        "user_tel":row.get("user_tel",""),
        "user_name":user.get("user_name","") if user else "",
        "user_head_url":user.get("head_url","") if user else "",
        "created_at":str(row.get("created_at","0")),
        "status":row.get("status",""),
    }
def announcement_to_dict(row):
    return {
        "id":str(row.get("id","")),
        "group_id":row.get("group_id",""),
        "content":row.get("content",""),
        "creator":row.get("creator",""),
        "created_at":str(row.get("created_at","0")),
        "updated_at":str(row.get("updated_at","0")),
        "status":row.get("status",""),
    }
def parse_pull_batch_items():
    payload=getattr(g,"payload",None)
    if isinstance(payload,dict) and "items" in payload:
        v=payload.get("items")
        if isinstance(v,list): return v,None
        if v is None: return [],None
        try: return json.loads(str(v)),None
        except: return None,"invalid items"
    raw=get_param("items","").strip()
    if not raw: return [],None
    try: return json.loads(raw),None
    except: return None,"invalid items"

# ---------- 旧币辅助函数 ----------
def daily_reward_for_all_users():
    """每天0点为所有用户增加10旧币（若当天未奖励）"""
    today = datetime.now().strftime("%Y-%m-%d")
    with DATA_LOCK:
        users = read_table("users")
        updated = 0
        for user in users:
            last = user.get("last_daily_reward", "")
            if last != today:
                current = float(user.get("old_coins", "0") or "0")
                new_balance = current + 10
                user["old_coins"] = str(new_balance)
                user["last_daily_reward"] = today
                updated += 1
        if updated > 0:
            write_table("users", users)
            print(f"[DAILY REWARD] {updated} users rewarded +10 old coins")
        else:
            print("[DAILY REWARD] All users already rewarded today")
def add_balance(user_tel, amount, description, trans_type="reward"):
    """增加用户余额并记录交易，amount 可为正数或负数（但推荐正数加 type）"""
    if not user_tel:
        return False
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return False
        balance_str = user.get("balance", "0")
        try:
            balance = float(balance_str) if balance_str else 0.0
        except:
            balance = 0.0
        new_balance = balance + amount
        user["balance"] = str(new_balance)
        write_table("users", users)
        
        trans = read_table("transactions")
        trans.append({
            "id": str(next_id(trans)),
            "from_user": "system",
            "to_user": user_tel,
            "amount": str(amount),
            "type": trans_type,
            "description": description,
            "created_at": str(now_ms())
        })
        write_table("transactions", trans)
        return True

# ---------- WebSocket 路由 ----------
@sock.route("/ws")
def ws_handler(ws):
    user_tel=request.args.get("user_tel","").strip()
    if not user_tel: ws.close(); return
    with DATA_LOCK:
        reports=read_table("reports")
        ban_until=get_active_ban_until(reports,user_tel)
    if ban_until is not None:
        try: ws.send(build_kick_payload(ban_message(ban_until)))
        except: pass
        ws.close(); return
    with WS_LOCK:
        WS_CLIENTS.setdefault(user_tel,[]).append(ws)
    try:
        while ws.receive() is not None: pass
    finally:
        with WS_LOCK:
            clients=WS_CLIENTS.get(user_tel,[])
            if ws in clients: clients.remove(ws)
            if not clients and user_tel in WS_CLIENTS: WS_CLIENTS.pop(user_tel,None)

@sock.route("/ws_call")
def ws_call_handler(ws):
    call_id=request.args.get("call_id","").strip()
    user_tel=request.args.get("user_tel","").strip()
    if not call_id or not user_tel: ws.close(); return
    with CALL_WS_LOCK:
        CALL_WS_CLIENTS.setdefault(call_id,[]).append({"ws":ws,"user_tel":user_tel})
    try:
        while True:
            data=ws.receive()
            if data is None: break
            if isinstance(data,(bytes,bytearray)):
                with CALL_WS_LOCK:
                    targets=CALL_WS_CLIENTS.get(call_id,[])[:]
                for t in targets:
                    if t.get("ws")==ws: continue
                    try: t.get("ws").send(data)
                    except: pass
    finally:
        with CALL_WS_LOCK:
            clients=CALL_WS_CLIENTS.get(call_id,[])
            clients=[c for c in clients if c.get("ws")!=ws]
            if clients: CALL_WS_CLIENTS[call_id]=clients
            elif call_id in CALL_WS_CLIENTS: CALL_WS_CLIENTS.pop(call_id,None)

# ---------- HTTP 路由 ----------
@app.route("/health")
@rate_limit(limit_per_sec=10, exempt_paths=('/health',))
def health(): return json_response("1",{"status":"ok"},"ok")

@app.route("/device/enter", methods=["POST"])
@rate_limit()
def device_enter():
    user_tel=get_param("user_tel","").strip()
    device_id=get_device_id()
    if not user_tel or not device_id: return json_response("0","","missing user_tel or device_id")
    ip=get_client_ip()
    with DATA_LOCK:
        rows=read_table("user_devices")
        upsert_user_device(rows,user_tel,device_id,ip)
        write_table("user_devices",rows)
    return json_response("1","","ok")

@app.route("/admin/login", methods=["GET","POST"])
@rate_limit()
def admin_login():
    if request.method=="GET":
        return render_template_string(ADMIN_HTML, page="login", next=request.args.get("next","/bans"), msg="")
    username=get_param("username","").strip()
    password=get_param("password","").strip()
    next_url=get_param("next","/bans").strip() or "/bans"
    if username==ADMIN_USER and password==ADMIN_PASSWORD:
        session["admin"]=True
        session["admin_user"]=username
        return redirect(next_url)
    return render_template_string(ADMIN_HTML, page="login", next=next_url, msg="账号或密码错误")

@app.route("/admin/logout")
@rate_limit()
def admin_logout():
    session.pop("admin",None)
    session.pop("admin_user",None)
    return redirect("/admin/login")

@app.route("/user/register", methods=["POST"])
@rate_limit()
def register():
    username = get_param("username", "").strip()
    password = get_param("password", "").strip()
    device_id = get_device_id()
    if not username or not password:
        return json_response("0", "", "missing username or password")
    password = normalize_password(password)
    with DATA_LOCK:
        if device_id:
            device_bans = read_table("device_bans")
            ban_until = get_active_device_ban_until(device_bans, device_id)
            if ban_until is not None:
                return json_response("0", "", device_ban_message(ban_until))
        users = read_table("users")
        if find_user(users, username):
            return json_response("0", "", "user already exists")
        for u in users:
            if u.get("oldchat_id") == username or u.get("telephone") == username:
                return json_response("0", "", "oldchat_id already exists")
        
        # 设置初始旧币
        if username == "110":
            initial_coins = "-10000"
        else:
            initial_coins = "15"
        
        row = {
            "id": str(next_id(users)),
            "telephone": username,
            "password": password,
            "oldchat_id": username,
            "user_name": f"WX{username}",
            "head_url": "",
            "cover_url": "",
            "signature": "",
            "sex": "",
            "location": "",
            "birthday": "",
            "type": "N",
            "balance": "0",           # 保留原有 balance 字段，暂未使用
            "old_coins": initial_coins,
            "last_daily_reward": "",
        }
        users.append(row)
        write_table("users", users)
    return json_response("1", user_to_dict(row), "ok")

@app.route("/user/login", methods=["POST"])
@rate_limit()
def login():
    username = get_param("username", "").strip()
    password = get_param("password", "").strip()
    device_id = get_device_id()
    if not username or not password:
        return json_response("0", "", "missing username or password")
    with DATA_LOCK:
        if device_id:
            device_bans = read_table("device_bans")
            ban_until = get_active_device_ban_until(device_bans, device_id)
            if ban_until is not None:
                return json_response("0", "", device_ban_message(ban_until))
        users = read_table("users")
        row = find_user(users, username)
        if not row or row.get("password") != normalize_password(password):
            return json_response("0", "", "invalid username or password")
        reports = read_table("reports")
        ban_until = get_active_ban_until(reports, row.get("telephone", ""))
        if ban_until is not None:
            return json_response("0", "", ban_message(ban_until))
    
    return json_response("1", user_to_dict(row), "ok")

@app.route("/app/update", methods=["GET","POST"])
@rate_limit()
def app_update():
    info=read_update_info()
    if not info: return json_response("1",{},"ok")
    return json_response("1",{
        "version_code":str(info.get("version_code","0")),
        "version_name":str(info.get("version_name","")),
        "apk_url":build_apk_url(info),
        "force":str(info.get("force","0")),
        "message":str(info.get("message","")),
    },"ok")

@app.route("/", methods=["GET"])
def index_page():
    info = read_update_info()
    version_name = html.escape(str(info.get("version_name", "")).strip())
    version_code = html.escape(str(info.get("version_code", "")).strip())
    message = html.escape(str(info.get("message", "")).strip())
    apk_url = build_apk_url(info)
    button_text = "立即下载" if apk_url else "暂无下载"
    disabled_attr = "" if apk_url else "disabled"
    download_href = apk_url if apk_url else "#"
    version_line = ""
    if version_name or version_code:
        version_line = f"最新版本：{version_name}（{version_code}）"
    notice_line = message if message else "支持注册登录、好友、群聊、语音与图片消息。"
    return f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>旧聊 - 轻量聊天应用</title>
  <style>
    :root {{
      color-scheme: light;
      --bg: #f5f5f5;
      --card: #ffffff;
      --text: #1f1f1f;
      --muted: #8c8c8c;
      --accent: #1aad19;
    }}
    body {{
      margin: 0;
      font-family: "PingFang SC", "Microsoft YaHei", "Noto Sans CJK SC", sans-serif;
      background: radial-gradient(1200px 800px at 80% -10%, #eaf8ea, var(--bg));
      color: var(--text);
    }}
    .wrap {{
      max-width: 920px;
      margin: 0 auto;
      padding: 48px 20px 64px;
    }}
    .hero {{
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
      gap: 24px;
      align-items: center;
    }}
    .title {{
      font-size: 36px;
      margin: 0 0 12px;
      letter-spacing: 1px;
    }}
    .desc {{
      font-size: 16px;
      line-height: 1.8;
      color: var(--muted);
      margin: 0 0 20px;
    }}
    .card {{
      background: var(--card);
      border-radius: 16px;
      padding: 24px;
      box-shadow: 0 18px 40px rgba(0, 0, 0, 0.08);
    }}
    .btn {{
      display: inline-block;
      background: var(--accent);
      color: #fff;
      padding: 12px 22px;
      border-radius: 10px;
      text-decoration: none;
      font-weight: 600;
    }}
    .btn[disabled] {{
      opacity: 0.5;
      pointer-events: none;
    }}
    .meta {{
      margin-top: 14px;
      font-size: 13px;
      color: var(--muted);
    }}
    ul {{
      margin: 0;
      padding-left: 18px;
      color: var(--muted);
      line-height: 1.8;
    }}
    .badge {{
      display: inline-block;
      background: #e7f6e7;
      color: #1a7d13;
      padding: 4px 10px;
      border-radius: 999px;
      font-size: 12px;
      margin-bottom: 12px;
    }}
  </style>
</head>
<body>
  <div class="wrap">
    <section class="hero">
      <div>
        <div class="badge">聊天应用</div>
        <h1 class="title">旧聊</h1>
        <p class="desc">轻量 仅3mb大小 {notice_line}</p>
        <a class="btn" href="{download_href}" {disabled_attr}>{button_text}</a>
        <div class="meta">{version_line}</div>
      </div>
    </section>
  </div>
</body>
</html>"""

ADMIN_HTML = open(Path(__file__).parent / "admin.html", "r", encoding="utf-8").read() if (Path(__file__).parent / "admin.html").exists() else "<h1>admin.html not found</h1>"

@app.route("/bugs", methods=["GET","POST"])
@rate_limit()
def bugs():
    if not admin_logged_in(): return render_template_string(ADMIN_HTML, page="login", next="/bugs", msg="")
    if request.method=="POST":
        user_tel=get_param("user_tel","").strip()
        content=get_param("content","").strip()
        device=get_param("device","").strip()
        app_version=get_param("app_version","").strip()
        if not content: return json_response("0","","missing content")
        with DATA_LOCK:
            rows=read_table("bugs")
            rows.append({"id":str(next_id(rows)),"user_tel":user_tel,"content":content,"device":device,"app_version":app_version,"created_at":str(now_ms())})
            write_table("bugs",rows)
        return json_response("1","","ok")
    with DATA_LOCK:
        rows=read_table("bugs")
        users=read_table("users")
    rows.sort(key=lambda r:parse_int(r.get("created_at")),reverse=True)
    items=[{"id":r.get("id",""),"user_tel":r.get("user_tel",""),"name":find_user(users,r.get("user_tel","")).get("user_name",""),"content":r.get("content",""),"device":r.get("device",""),"app_version":r.get("app_version",""),"created_at":format_datetime(parse_int(r.get("created_at")))} for r in rows]
    return render_template_string(ADMIN_HTML, page="bugs", items=items)

@app.route("/report", methods=["POST"])
@rate_limit()
def report_user():
    reporter_tel=get_param("reporter_tel","").strip()
    target_raw=get_param("target_tel","").strip() or get_param("target","").strip()
    reason=get_param("reason","").strip()
    if not reporter_tel or not target_raw: return json_response("0","","missing reporter_tel or target_tel")
    with DATA_LOCK:
        users=read_table("users")
        target_tel=resolve_user_identifier(users,target_raw)
        if not target_tel: return json_response("0","","target not found")
        device_rows=read_table("user_devices")
        device_id=find_user_device(device_rows,target_tel).get("device_id","") if find_user_device(device_rows,target_tel) else ""
        rows=read_table("reports")
        rows.append({"id":str(next_id(rows)),"reporter_tel":reporter_tel,"target_tel":target_tel,"device_id":device_id,"reason":reason,"created_at":str(now_ms()),"status":"pending","ban_until":"","handled_at":"","handler":""})
        write_table("reports",rows)
    return json_response("1","","ok")

@app.route("/bans", methods=["GET","POST"])
@rate_limit()
def bans():
    if not admin_logged_in(): return render_template_string(ADMIN_HTML, page="login", next="/bans", msg="")
    kick_info=None
    if request.method=="POST":
        action=get_param("action","").strip()
        report_id=get_param("report_id","").strip()
        duration=parse_int(get_param("duration","0"),0)
        device_id=get_param("device_id","").strip()
        device_reason=get_param("reason","").strip()
        with DATA_LOCK:
            rows=read_table("reports")
            target=next((r for r in rows if r.get("id")==report_id),None)
            handler=str(session.get("admin_user",""))
            if action=="ban_device":
                if not device_id and target: device_id=target.get("device_id","")
                if not device_id and target:
                    device_rows=read_table("user_devices")
                    dv=find_user_device(device_rows,target.get("target_tel",""))
                    if dv: device_id=dv.get("device_id","")
                if not device_reason and target: device_reason=target.get("reason","")
                if device_id:
                    dev_rows=read_table("device_bans")
                    ban_until=apply_device_ban(dev_rows,device_id,duration,device_reason,handler)
                    write_table("device_bans",dev_rows)
                    if target:
                        target["status"]="device_banned"
                        target["ban_until"]=ban_until
                        target["handled_at"]=str(now_ms())
                        target["handler"]=handler
                        kick_info=(target.get("target_tel",""), device_ban_message(parse_int(ban_until,0)))
            else:
                if target:
                    if action=="ignore":
                        target["status"]="ignored"
                        target["ban_until"]=""
                        target["handled_at"]=str(now_ms())
                        target["handler"]=handler
                    elif action=="ban":
                        ban_until="0" if duration==0 else str(now_ms()+duration*1000)
                        target["status"]="banned"
                        target["ban_until"]=ban_until
                        target["handled_at"]=str(now_ms())
                        target["handler"]=handler
                        kick_info=(target.get("target_tel",""), ban_message(parse_int(ban_until,0)))
                        target_device=target.get("device_id","")
                        if not target_device:
                            dev_rows=read_table("user_devices")
                            dv=find_user_device(dev_rows,target.get("target_tel",""))
                            if dv: target_device=dv.get("device_id","")
                        if target_device:
                            dev_rows=read_table("device_bans")
                            apply_device_ban(dev_rows,target_device,duration,target.get("reason",""),handler)
                            write_table("device_bans",dev_rows)
            write_table("reports",rows)
        if kick_info:
            kick_user(kick_info[0], kick_info[1])
    with DATA_LOCK:
        reports=read_table("reports")
        users=read_table("users")
    reports.sort(key=lambda r:parse_int(r.get("created_at")),reverse=True)
    now_ts=now_ms()
    cards=[]
    for r in reports:
        reporter=find_user(users,r.get("reporter_tel",""))
        target=find_user(users,r.get("target_tel",""))
        status=r.get("status","pending")
        until=parse_int(r.get("ban_until"),0)
        until_text=""
        if status=="banned":
            if until==0: until_text="永久封禁"
            elif until>now_ts: until_text=f"封禁至 {format_datetime(until)}"
            else: until_text="封禁已到期"
        elif status=="device_banned":
            if until==0: until_text="设备永久封禁"
            elif until>now_ts: until_text=f"设备封禁至 {format_datetime(until)}"
            else: until_text="设备封禁已到期"
        cards.append({"id":r.get("id",""),"reporter_name":reporter.get("user_name",""),"reporter_tel":r.get("reporter_tel",""),"target_name":target.get("user_name",""),"target_tel":r.get("target_tel",""),"device_id":r.get("device_id","") or "-","reason":r.get("reason",""),"created_at":format_datetime(parse_int(r.get("created_at"))),"status":status,"until_text":until_text})
    return render_template_string(ADMIN_HTML, page="bans", cards=cards)

@app.route("/device_bans", methods=["GET","POST"])
@rate_limit()
def device_bans():
    if not admin_logged_in(): return render_template_string(ADMIN_HTML, page="login", next="/device_bans", msg="")
    msg=err=""
    if request.method=="POST":
        action=get_param("action","").strip()
        device_id=get_param("device_id","").strip()
        reason=get_param("reason","").strip()
        duration=parse_int(get_param("duration","0"),0)
        if not device_id: err="设备ID不能为空"
        else:
            with DATA_LOCK:
                rows=read_table("device_bans")
                now=now_ms()
                target=find_device_ban(rows,device_id)
                if action=="ban":
                    if not target:
                        target={"id":str(next_id(rows)),"device_id":device_id,"status":"banned","ban_until":"","created_at":str(now),"updated_at":str(now),"reason":"","handler":""}
                        rows.append(target)
                    target["status"]="banned"
                    target["ban_until"]="0" if duration==0 else str(now+duration*1000)
                    target["reason"]=reason
                    target["updated_at"]=str(now)
                    target["handler"]=str(session.get("admin_user",""))
                    msg="已封禁设备"
                elif action=="unban" and target:
                    target["status"]="released"
                    target["ban_until"]=""
                    target["updated_at"]=str(now)
                    target["handler"]=str(session.get("admin_user",""))
                    msg="已解除封禁"
                write_table("device_bans",rows)
    with DATA_LOCK:
        rows=read_table("device_bans")
    rows.sort(key=lambda r:parse_int(r.get("updated_at") or r.get("created_at")),reverse=True)
    now_ts=now_ms()
    items=[]
    for r in rows:
        status=r.get("status","")
        until=parse_int(r.get("ban_until"),0)
        until_text=""
        if status=="banned":
            if until==0: until_text="永久封禁"
            elif until>now_ts: until_text=f"封禁至 {format_datetime(until)}"
            else: until_text="封禁已到期"
        else: until_text="未封禁"
        items.append({"device_id":r.get("device_id",""),"status":status,"until_text":until_text,"reason":r.get("reason",""),"created_at":format_datetime(parse_int(r.get("created_at"))),"updated_at":format_datetime(parse_int(r.get("updated_at"))),"handler":r.get("handler","")})
    return render_template_string(ADMIN_HTML, page="device_bans", items=items, msg=msg, err=err)

@app.route("/user_devices", methods=["GET"])
@rate_limit()
def user_devices():
    if not admin_logged_in(): return render_template_string(ADMIN_HTML, page="login", next="/user_devices", msg="")
    with DATA_LOCK:
        rows=read_table("user_devices")
        users=read_table("users")
    rows.sort(key=lambda r:parse_int(r.get("updated_at") or r.get("created_at")),reverse=True)
    items=[]
    for r in rows:
        user=find_user(users,r.get("user_tel",""))
        items.append({"id":r.get("id",""),"user_name":user.get("user_name","") if user else "","user_tel":r.get("user_tel",""),"device_id":r.get("device_id",""),"ip":r.get("ip",""),"created_at":format_datetime(parse_int(r.get("created_at"))),"updated_at":format_datetime(parse_int(r.get("updated_at")))})
    return render_template_string(ADMIN_HTML, page="user_devices", items=items)

@app.route("/bans/messages", methods=["GET"])
@rate_limit()
def bans_messages():
    if not admin_logged_in(): return render_template_string(ADMIN_HTML, page="login", next="/bans/messages", msg="")
    target_tel=request.args.get("target_tel","").strip()
    if not target_tel: return redirect("/bans")
    with DATA_LOCK:
        messages=read_table("messages")
        users=read_table("users")
    target=find_user(users,target_tel)
    filtered=[r for r in messages if r.get("sender_tel")==target_tel or r.get("receiver_id")==target_tel]
    filtered.sort(key=lambda r:parse_int(r.get("timestamp")),reverse=True)
    items=[]
    for r in filtered:
        msg_type=r.get("message_type","text")
        content=r.get("content","")
        if msg_type!="text": content=f"[{msg_type}] {r.get('media_url','') or content}"
        items.append({"timestamp":format_datetime(parse_int(r.get("timestamp"))),"sender_tel":r.get("sender_tel",""),"receiver_id":r.get("receiver_id",""),"conversation_id":r.get("conversation_id",""),"message_type":msg_type,"content":content})
    return render_template_string(ADMIN_HTML, page="bans_messages", target_tel=target_tel, target_name=target.get("user_name","") if target else "", items=items)

@app.route("/admins", methods=["GET","POST"])
@rate_limit()
def admins():
    if not admin_logged_in(): return render_template_string(ADMIN_HTML, page="login", next="/admins", msg="")
    notice_msg=""
    if request.method=="POST" and get_param("action","")=="notify":
        title=get_param("title","").strip()
        content=get_param("content","").strip()
        file=request.files.get("image") if request.files else None
        if not content and not file: notice_msg="请填写通知内容或选择图片"
        else:
            with DATA_LOCK:
                users=read_table("users")
                messages=read_table("messages")
                if content:
                    now=str(now_ms())
                    notice_content=f"【{title}】{content}" if title else content
                    row={"id":str(next_id(messages)),"conversation_id":"system_notice","sender_tel":"admin","sender_name":"通知服务","sender_head_url":"","message_type":"text","media_url":"","receiver_id":"","is_group":"1","content":notice_content,"timestamp":now}
                    messages.append(row)
                if file and file.filename:
                    ext=os.path.splitext(file.filename)[1].lower()
                    if ext in ('.jpg','.jpeg','.png','.gif','.webp') and validate_file_header(file, ALLOWED_IMAGE_MAGIC):
                        filename=build_upload_filename(ext)
                        file.save(UPLOAD_DIR/filename)
                        url=f"http://{request.host}/uploads/{filename}"
                        now=str(now_ms())
                        row={"id":str(next_id(messages)),"conversation_id":"system_notice","sender_tel":"admin","sender_name":"通知服务","sender_head_url":"","message_type":"image","media_url":url,"receiver_id":"","is_group":"1","content":"","timestamp":now}
                        messages.append(row)
                    else:
                        notice_msg="图片文件格式无效"
                write_table("messages",messages)
                for u in users:
                    push_ws(u.get("telephone",""), build_ws_payload(message_to_dict(row))) if 'row' in locals() else None
                notice_msg="通知已发送" if 'row' in locals() else notice_msg
    query=request.args.get("q","").strip()
    group_filter=request.args.get("group","").strip()
    start_raw=request.args.get("start","").strip()
    end_raw=request.args.get("end","").strip()
    start_ts=parse_datetime(start_raw)
    end_ts=parse_datetime(end_raw,True)
    with DATA_LOCK:
        users=read_table("users")
        friendships=read_table("friendships")
        groups=read_table("groups")
        moments=read_table("moments")
        messages=read_table("messages")
        requests=read_table("friend_requests")
    users.sort(key=lambda r:r.get("telephone",""))
    user_map={u.get("telephone",""):u for u in users if u.get("telephone")}
    friends_map={}
    for f in friendships:
        friends_map.setdefault(f.get("user_tel",""),set()).add(f.get("friend_tel",""))
        friends_map.setdefault(f.get("friend_tel",""),set()).add(f.get("user_tel",""))
    groups_map={}
    for g in groups:
        for m in split_members(g.get("members","")):
            groups_map.setdefault(m,set()).add(g.get("group_id",""))
    q_low=query.lower()
    matched_users=[u for u in users if not query or q_low in u.get("telephone","").lower() or q_low in u.get("oldchat_id","").lower() or q_low in u.get("user_name","").lower()]
    if group_filter: matched_users=[u for u in matched_users if group_filter in groups_map.get(u.get("telephone",""),set())]
    matched_tels={u.get("telephone","") for u in matched_users if u.get("telephone")}
    user_rows=[{"id":u.get("id",""),"telephone":u.get("telephone",""),"oldchat_id":u.get("oldchat_id",""),"user_name":u.get("user_name",""),"signature":u.get("signature",""),"location":u.get("location",""),"birthday":u.get("birthday",""),"type":u.get("type","")} for u in matched_users]
    relation_rows=[]
    for u in matched_users:
        tel=u.get("telephone","")
        friends=[f for f in friends_map.get(tel,set()) if f]
        friend_texts=[f"{f}({user_map.get(f,{}).get('user_name','')})" if user_map.get(f) else f for f in friends]
        groups_text="、".join(sorted(groups_map.get(tel,set())))
        relation_rows.append({"id":u.get("id",""),"telephone":tel,"oldchat_id":u.get("oldchat_id",""),"user_name":u.get("user_name",""),"friends":"、".join(friend_texts),"groups":groups_text})
    group_rows=[]
    for g in groups:
        if group_filter and g.get("group_id")!=group_filter: continue
        if query and q_low not in g.get("group_id","").lower() and q_low not in g.get("group_name","").lower() and not any(m in matched_tels for m in split_members(g.get("members",""))): continue
        group_rows.append({"id":g.get("id",""),"group_id":g.get("group_id",""),"group_name":g.get("group_name",""),"owner_id":g.get("owner_id",""),"members":"、".join(split_members(g.get("members","")))})
    moment_rows=[]
    for m in moments:
        ts=parse_int(m.get("created_at"))
        if start_ts and ts<start_ts: continue
        if end_ts and ts>end_ts: continue
        if query and m.get("user_tel","") not in matched_tels and q_low not in user_map.get(m.get("user_tel",""),{}).get("user_name","").lower(): continue
        urls=parse_json_list(m.get("image_urls",""))
        if not urls and m.get("image_url"): urls=[m.get("image_url")]
        moment_rows.append({"id":m.get("id",""),"user_tel":m.get("user_tel",""),"user_name":user_map.get(m.get("user_tel",""),{}).get("user_name",""),"content":m.get("content",""),"images":"、".join(urls),"likes":m.get("likes",""),"comments":m.get("comments",""),"created_at":format_datetime(ts)})
    message_rows=[]
    for msg in messages:
        ts=parse_int(msg.get("timestamp"))
        if start_ts and ts<start_ts: continue
        if end_ts and ts>end_ts: continue
        if group_filter and msg.get("conversation_id")!=group_filter: continue
        if query and msg.get("sender_tel","") not in matched_tels and msg.get("receiver_id","") not in matched_tels and q_low not in msg.get("conversation_id","").lower(): continue
        msg_type=msg.get("message_type","text")
        content=msg.get("content","")
        if msg_type!="text": content=f"[{msg_type}] {msg.get('media_url','') or content}"
        message_rows.append({"id":msg.get("id",""),"timestamp":format_datetime(ts),"conversation_id":msg.get("conversation_id",""),"sender_tel":msg.get("sender_tel",""),"receiver_id":msg.get("receiver_id",""),"is_group":msg.get("is_group",""),"message_type":msg_type,"content":content})
    request_rows=[]
    for req in requests:
        ts=parse_int(req.get("created_at"))
        if start_ts and ts<start_ts: continue
        if end_ts and ts>end_ts: continue
        if query and req.get("user_tel","") not in matched_tels and req.get("friend_tel","") not in matched_tels and q_low not in req.get("user_tel","").lower() and q_low not in req.get("friend_tel","").lower(): continue
        request_rows.append({"id":req.get("id",""),"user_tel":req.get("user_tel",""),"friend_tel":req.get("friend_tel",""),"status":req.get("status",""),"created_at":format_datetime(ts)})
    filter_parts=[]
    if query: filter_parts.append(f"关键词：{html.escape(query)}")
    if group_filter: filter_parts.append(f"群号：{html.escape(group_filter)}")
    if start_raw or end_raw: filter_parts.append(f"时间：{html.escape(start_raw or '不限')} ~ {html.escape(end_raw or '不限')}")
    filter_line=" | ".join(filter_parts)
    return render_template_string(ADMIN_HTML, page="admins", users=user_rows, relations=relation_rows, groups=group_rows, moments=moment_rows, messages=message_rows, requests=request_rows, filter_line=filter_line, notice_msg=notice_msg, query=query, group_filter=group_filter, start_raw=start_raw, end_raw=end_raw, total_users=len(matched_users), total_friendships=len(friendships), total_groups=len(group_rows), total_moments=len(moment_rows), total_messages=len(message_rows), total_requests=len(request_rows))

# ---------- 违禁词管理 ----------
@app.route("/admin/banned_words", methods=["GET", "POST"])
@rate_limit()
def admin_banned_words():
    if not admin_logged_in():
        return render_template_string(ADMIN_HTML, page="login", next="/admin/banned_words", msg="")
    msg = ""
    err = ""
    if request.method == "POST" and request.form.get("action") == "add":
        word = request.form.get("word", "").strip()
        if not word:
            err = "违禁词不能为空"
        else:
            with DATA_LOCK:
                rows = read_table("banned_words")
                if any(r.get("word") == word for r in rows):
                    err = "违禁词已存在"
                else:
                    rows.append({
                        "id": str(next_id(rows)),
                        "word": word,
                        "created_at": str(now_ms())
                    })
                    write_table("banned_words", rows)
                    msg = "添加成功"
    if request.method == "POST" and request.form.get("action") == "delete":
        word_id = request.form.get("id", "").strip()
        if word_id:
            import pymysql
            conn = pymysql.connect(**DB_CONFIG)
            try:
                with conn.cursor() as cur:
                    cur.execute("DELETE FROM `banned_words` WHERE `id` = %s", (word_id,))
                    conn.commit()
                    msg = "删除成功"
            except Exception as e:
                err = f"删除失败: {e}"
            finally:
                conn.close()
    with DATA_LOCK:
        words = read_table("banned_words")
    for w in words:
        w["created_at"] = format_datetime(parse_int(w.get("created_at", 0)))
    words.sort(key=lambda r: r.get("id", ""), reverse=True)
    return render_template_string(ADMIN_HTML, page="banned_words", words=words, msg=msg, err=err)

# ---------- 用户相关 ----------
@app.route("/user/update_userinfo", methods=["POST"])
@rate_limit()
def update_userinfo():
    tel=get_param("telphone") or get_param("telephone")
    if not tel: return json_response("0","","missing telphone")
    updates={k:get_optional_param_any(*v) for k,v in {"user_name":["username"],"oldchat_id":["oldchat_id","oldChatId","oldchatId"],"head_url":["headUrl","head_url"],"cover_url":["coverUrl","cover_url"],"signature":["signature"],"sex":["sex"],"location":["location"],"birthday":["birthday"],"type":["type"]}.items()}
    set_parts={k:v for k,v in updates.items() if v is not None}
    if not set_parts: return json_response("0","","no fields to update")
    with DATA_LOCK:
        users=read_table("users")
        row=find_user(users,tel)
        if not row:
            row={"id":str(next_id(users)),"telephone":tel,"password":"","oldchat_id":tel,"user_name":updates.get("user_name",""),"head_url":"","cover_url":"","signature":"","sex":"","location":"","birthday":"","type":"N"}
            users.append(row)
        if "oldchat_id" in set_parts:
            if not set_parts["oldchat_id"]: return json_response("0","","invalid oldchat_id")
            for u in users:
                if u.get("telephone")!=tel and (u.get("oldchat_id")==set_parts["oldchat_id"] or u.get("telephone")==set_parts["oldchat_id"]):
                    return json_response("0","","oldchat_id already exists")
        for k,v in set_parts.items(): row[k]=v
        write_table("users",users)
    return json_response("1",user_to_dict(row),"ok")

@app.route("/user/get_balance", methods=["POST"])
@rate_limit()
def get_balance():
    user_tel = get_param("user_tel", "").strip()
    if not user_tel:
        return json_response("0", "", "missing user_tel")
    with DATA_LOCK:
        users = read_table("users")
        user = find_user(users, user_tel)
        if not user:
            return json_response("0", "", "user not found")
        balance = float(user.get("old_coins", "0") or "0")
    return json_response("1", {"balance": balance}, "ok")

@app.route("/user/get_user_list", methods=["GET","POST"])
@rate_limit()
def get_user_list():
    tel=get_param("telphone") or get_param("telephone")
    group_id=get_param("group_id")
    if group_id: return get_group_info()
    with DATA_LOCK:
        users=read_table("users")
        if tel:
            row=find_user(users,tel)
            if not row: return json_response("0","","user not found")
            return json_response("1",user_to_dict(row),"ok")
        return json_response("1",[user_to_dict(u) for u in users],"ok")

@app.route("/user/get_contact_list", methods=["GET","POST"])
@rate_limit()
def get_contact_list():
    userlist=get_param("userlist","")
    numbers=parse_userlist(userlist)
    if not numbers: return json_response("1",[],"ok")
    with DATA_LOCK:
        users=read_table("users")
        resolved=set()
        for n in numbers:
            t=resolve_user_identifier(users,n)
            if t: resolved.add(t)
        rows=[user_to_dict(u) for u in users if u.get("telephone") in resolved]
    return json_response("1",rows,"ok")

@app.route("/user/add_friend", methods=["POST"])
@rate_limit()
def add_friend():
    user_tel=get_param("user_tel","").strip()
    friend_tel=get_param("friend_tel","").strip()
    if not user_tel or not friend_tel: return json_response("0","","missing user_tel or friend_tel")
    with DATA_LOCK:
        users=read_table("users")
        friendships=read_table("friendships")
        requests=read_table("friend_requests")
        resolved=resolve_user_identifier(users,friend_tel)
        if not resolved: return json_response("0","","friend user not found")
        if user_tel==resolved: return json_response("0","","cannot add yourself")
        if are_friends(friendships,user_tel,resolved): return json_response("0","","already friends")
        if any(r.get("user_tel")==user_tel and r.get("friend_tel")==resolved and r.get("status")=="pending" for r in requests): return json_response("1","","request already sent")
        requests.append({"id":str(next_id(requests)),"user_tel":user_tel,"friend_tel":resolved,"status":"pending","created_at":str(now_ms())})
        write_table("friend_requests",requests)
    return json_response("1","","request sent")

@app.route("/user/get_friends", methods=["GET","POST"])
@rate_limit()
def get_friends():
    user_tel=get_param("user_tel","").strip()
    if not user_tel: return json_response("0","","missing user_tel")
    with DATA_LOCK:
        friendships=read_table("friendships")
        users=read_table("users")
        friends=[f.get("friend_tel") for f in friendships if f.get("user_tel")==user_tel]
        rows=[user_to_dict(u) for u in users if u.get("telephone") in friends]
    return json_response("1",rows,"ok")

@app.route("/user/delete_friend", methods=["POST"])
@rate_limit()
def delete_friend():
    user_tel=get_param("user_tel","").strip()
    friend_tel=get_param("friend_tel","").strip()
    if not user_tel or not friend_tel: return json_response("0","","missing user_tel or friend_tel")
    with DATA_LOCK:
        friendships=read_table("friendships")
        requests=read_table("friend_requests")
        friendships=[r for r in friendships if not ((r.get("user_tel")==user_tel and r.get("friend_tel")==friend_tel) or (r.get("user_tel")==friend_tel and r.get("friend_tel")==user_tel))]
        requests=[r for r in requests if not ((r.get("user_tel")==user_tel and r.get("friend_tel")==friend_tel) or (r.get("user_tel")==friend_tel and r.get("friend_tel")==user_tel))]
        write_table("friendships",friendships)
        write_table("friend_requests",requests)
    return json_response("1","","ok")

# ---------- 朋友圈 ----------
@app.route("/moment/add", methods=["POST"])
@rate_limit()
def add_moment():
    user_tel=get_param("user_tel","").strip()
    content=get_param("content","").strip()
    image_url=get_param("image_url","").strip()
    raw_urls=get_optional_param_any("image_urls","imageUrls")
    image_urls=parse_json_list(raw_urls) if raw_urls is not None else []
    if not image_urls and image_url: image_urls=[image_url]
    if not user_tel: return json_response("0","","missing user_tel")
    if not content and not image_urls: return json_response("0","","missing content or image_url")
    with DATA_LOCK:
        users=read_table("users")
        if not find_user(users,user_tel): return json_response("0","","user not found")
        moments=read_table("moments")
        row={
            "id":str(next_id(moments)),
            "user_tel":user_tel,
            "content":content,
            "image_url":image_url or (image_urls[0] if image_urls else ""),
            "image_urls":json.dumps(image_urls,ensure_ascii=True) if image_urls else "",
            "likes":"[]",
            "comments":"[]",
            "created_at":str(now_ms()),
        }
        moments.append(row)
        write_table("moments",moments)
    return json_response("1",moment_to_dict(row,users),"ok")

@app.route("/moment/list", methods=["GET","POST"])
@rate_limit()
def list_moments():
    user_tel=get_param("user_tel","").strip()
    target_ident=get_optional_param_any("target_tel","target_id","targetId","target")
    if not user_tel: return json_response("0","","missing user_tel")
    limit=max(1, min(200, parse_int(get_param("limit","10"))))
    offset=max(0, parse_int(get_param("offset","0")))
    with DATA_LOCK:
        users=read_table("users")
        moments=read_table("moments")
        target_tel=""
        if target_ident:
            target_tel=resolve_user_identifier(users,target_ident.strip())
            if not target_tel: return json_response("0","","user not found")
        if target_tel:
            rows=[r for r in moments if r.get("user_tel")==target_tel]
        else:
            friendships=read_table("friendships")
            friends=[f.get("friend_tel") for f in friendships if f.get("user_tel")==user_tel]
            allow=set(friends+[user_tel])
            rows=[r for r in moments if r.get("user_tel") in allow]
        rows.sort(key=lambda r:parse_int(r.get("created_at")),reverse=True)
        sliced=rows[offset:offset+limit]
        result=[moment_to_dict(r,users) for r in sliced]
    return json_response("1",result,"ok")

@app.route("/moment/like", methods=["POST"])
@rate_limit()
def like_moment():
    user_tel=get_param("user_tel","").strip()
    moment_id=get_param("moment_id","").strip()
    action=get_param("action","like").strip().lower()
    if not user_tel or not moment_id: return json_response("0","","missing user_tel or moment_id")
    with DATA_LOCK:
        moments=read_table("moments")
        row=next((r for r in moments if r.get("id")==moment_id),None)
        if not row: return json_response("0","","moment not found")
        likes=[str(x) for x in parse_json_list(row.get("likes","")) if str(x).strip()]
        if action=="unlike": likes=[x for x in likes if x!=user_tel]
        elif user_tel not in likes: likes.append(user_tel)
        row["likes"]=json.dumps(likes,ensure_ascii=True)
        write_table("moments",moments)
        users=read_table("users")
    return json_response("1",moment_to_dict(row,users),"ok")

@app.route("/moment/comment", methods=["POST"])
@rate_limit()
def comment_moment():
    user_tel=get_param("user_tel","").strip()
    moment_id=get_param("moment_id","").strip()
    content=get_param("content","").strip()
    if not user_tel or not moment_id: return json_response("0","","missing user_tel or moment_id")
    if not content: return json_response("0","","missing content")
    with DATA_LOCK:
        moments=read_table("moments")
        row=next((r for r in moments if r.get("id")==moment_id),None)
        if not row: return json_response("0","","moment not found")
        comments=parse_json_list(row.get("comments",""))
        if not isinstance(comments,list): comments=[]
        comments.append({"id":str(now_ms()),"user_tel":user_tel,"content":content,"created_at":str(now_ms())})
        row["comments"]=json.dumps(comments,ensure_ascii=True)
        write_table("moments",moments)
        users=read_table("users")
    return json_response("1",moment_to_dict(row,users),"ok")

@app.route("/moment/delete", methods=["POST"])
@rate_limit()
def delete_moment():
    user_tel=get_param("user_tel","").strip()
    moment_id=get_param("moment_id","").strip()
    if not user_tel or not moment_id: return json_response("0","","missing user_tel or moment_id")
    with DATA_LOCK:
        moments=read_table("moments")
        row=next((r for r in moments if r.get("id")==moment_id),None)
        if not row: return json_response("0","","moment not found")
        if row.get("user_tel")!=user_tel: return json_response("0","","only owner can delete")
        moments=[r for r in moments if r.get("id")!=moment_id]
        write_table("moments",moments)
    return json_response("1","","ok")

# ---------- 好友请求 ----------
@app.route("/friend/requests", methods=["GET","POST"])
@rate_limit()
def get_friend_requests():
    friend_tel=get_param("friend_tel","").strip()
    if not friend_tel: return json_response("0","","missing friend_tel")
    with DATA_LOCK:
        requests=read_table("friend_requests")
        users=read_table("users")
        pending=[r for r in requests if r.get("friend_tel")==friend_tel and r.get("status")=="pending"]
        pending.sort(key=lambda r:parse_int(r.get("created_at")),reverse=True)
        result=[]
        for r in pending:
            user=find_user(users,r.get("user_tel",""))
            result.append({"request_id":str(r.get("id","")),"user_tel":r.get("user_tel",""),"created_at":str(r.get("created_at") or 0),"user":user_to_dict(user)})
    return json_response("1",result,"ok")

@app.route("/friend/respond", methods=["POST"])
@rate_limit()
def respond_friend_request():
    request_id=get_param("request_id","").strip()
    action=get_param("action","").strip()
    if not request_id or action not in ("accept","reject"): return json_response("0","","missing request_id or action")
    with DATA_LOCK:
        requests=read_table("friend_requests")
        friendships=read_table("friendships")
        row=next((r for r in requests if r.get("id")==request_id),None)
        if not row or row.get("status")!="pending": return json_response("0","","request not found or already handled")
        if action=="accept":
            row["status"]="accepted"
            if not are_friends(friendships,row.get("user_tel"),row.get("friend_tel")):
                friendships.append({"id":str(next_id(friendships)),"user_tel":row.get("user_tel",""),"friend_tel":row.get("friend_tel","")})
                friendships.append({"id":str(next_id(friendships)),"user_tel":row.get("friend_tel",""),"friend_tel":row.get("user_tel","")})
        else: row["status"]="rejected"
        write_table("friend_requests",requests)
        write_table("friendships",friendships)
    return json_response("1","","ok")

# ---------- 群组 ----------
@app.route("/group/add_group", methods=["POST"])
@rate_limit()
def add_group():
    group_id=get_param("group_id","").strip()
    group_name=get_param("group_name","").strip()
    owner_ident=get_param("owner_id","").strip()
    members_raw=get_param("members","").strip()
    if not group_id: return json_response("0","","missing group_id")
    with DATA_LOCK:
        users=read_table("users")
        owner_id=resolve_user_identifier(users,owner_ident) if owner_ident else ""
        resolved_members=[]
        for m in split_members(members_raw):
            rm=resolve_user_identifier(users,m)
            if not rm: return json_response("0","","invalid member")
            resolved_members.append(rm)
        if owner_id and owner_id not in resolved_members: resolved_members.insert(0,owner_id)
        groups=read_table("groups")
        if find_group(groups,group_id): return json_response("0","","group already exists")
        row={
            "id":str(next_id(groups)),
            "group_id":group_id,
            "group_name":group_name,
            "owner_id":owner_id,
            "members":join_members(resolved_members),
            "description":get_param("description",""),
            "image_path":get_param("image_path",""),
            "maxusers":get_param("maxusers",""),
            "authority":get_param("authority",""),
            "affiliations":get_param("affiliations",""),
            "receive":get_param("receive","0"),
            "is_common":get_param("is_common","1"),
            "is_in":get_param("is_in","1"),
            "share_location":get_param("share_location",""),
            "type":get_param("type",""),
        }
        groups.append(row)
        write_table("groups",groups)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/get_group_list", methods=["GET","POST"])
@rate_limit()
def get_group_list():
    with DATA_LOCK:
        groups=read_table("groups")
    return json_response("1",[group_to_dict(g) for g in groups],"ok")

@app.route("/group/get_group_info", methods=["GET","POST"])
@rate_limit()
def get_group_info():
    group_id=get_param("group_id","").strip()
    if not group_id: return json_response("0","","missing group_id")
    with DATA_LOCK:
        row=find_group(read_table("groups"),group_id)
        if not row: return json_response("0","","group not found")
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/exit_group", methods=["POST"])
@rate_limit()
def exit_group():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip()
    if not group_id or not user_ident: return json_response("0","","missing group_id or user_id")
    with DATA_LOCK:
        users=read_table("users")
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row: return json_response("0","","group not found")
        members=split_members(row.get("members",""))
        user_id=user_ident if user_ident in members or user_ident==row.get("owner_id") else resolve_user_identifier(users,user_ident)
        if not user_id: return json_response("0","","invalid user_id")
        if user_id not in members and user_id!=row.get("owner_id"): return json_response("0","","not in group")
        row["members"]=join_members([m for m in members if m!=user_id])
        admins=split_members(row.get("authority",""))
        if user_id in admins: row["authority"]=join_members([a for a in admins if a!=user_id])
        write_table("groups",groups)
        messages=read_table("messages")
        display=resolve_user_identifier(users,user_id) or user_id
        head=find_user(users,user_id).get("head_url","") if find_user(users,user_id) else ""
        notice=append_group_notice_message(messages,group_id,user_id,display,head,f"{display}退出群聊")
        if notice: write_table("messages",messages)
        targets=split_members(row.get("members",""))
    if notice and targets:
        p=build_ws_payload(message_to_dict(notice))
        for t in targets: push_ws(t,p)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/dissolve", methods=["POST"])
@rate_limit()
def group_dissolve():
    group_id=get_param("group_id","").strip()
    owner_ident=get_param("owner_id","").strip()
    if not group_id or not owner_ident: return json_response("0","","missing group_id or owner_id")
    with DATA_LOCK:
        users=read_table("users")
        owner_id=resolve_user_identifier(users,owner_ident)
        if not owner_id: return json_response("0","","invalid owner_id")
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row or (row.get("owner_id") and row.get("owner_id")!=owner_id): return json_response("0","","only owner can dissolve")
        groups=[g for g in groups if g.get("group_id")!=group_id]
        write_table("groups",groups)
    return json_response("1","","ok")

@app.route("/group/add_member", methods=["POST"])
@rate_limit()
def group_add_member():
    group_id=get_param("group_id","").strip()
    owner_ident=get_param("owner_id","").strip()
    members_raw=get_param("members","").strip()
    single_member=get_param("member_tel","").strip()
    new_members=split_members(members_raw)
    if single_member: new_members.append(single_member)
    if not group_id or not owner_ident or not new_members: return json_response("0","","missing params")
    with DATA_LOCK:
        users=read_table("users")
        owner_id=resolve_user_identifier(users,owner_ident)
        if not owner_id: return json_response("0","","invalid owner_id")
        resolved=[]
        for m in new_members:
            rm=resolve_user_identifier(users,m)
            if not rm: return json_response("0","","invalid member")
            resolved.append(rm)
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row: return json_response("0","","group not found")
        if not is_group_admin(row,owner_id): return json_response("0","","no permission")
        existing=split_members(row.get("members",""))
        added=[]
        for rm in resolved:
            if rm not in existing:
                existing.append(rm)
                added.append(rm)
        row["members"]=join_members(existing)
        write_table("groups",groups)
        if added:
            messages=read_table("messages")
            notices=[]
            for m in added:
                display=resolve_user_identifier(users,m) or m
                head=find_user(users,m).get("head_url","") if find_user(users,m) else ""
                notice=append_group_notice_message(messages,group_id,m,display,head,f"{display}加入群聊")
                if notice: notices.append(notice)
            if notices:
                write_table("messages",messages)
                targets=split_members(row.get("members",""))
                for notice in notices:
                    p=build_ws_payload(message_to_dict(notice))
                    for t in targets: push_ws(t,p)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/remove_member", methods=["POST"])
@rate_limit()
def group_remove_member():
    group_id=get_param("group_id","").strip()
    owner_ident=get_param("owner_id","").strip()
    member_ident=get_param("member_tel","").strip()
    if not group_id or not owner_ident or not member_ident: return json_response("0","","missing params")
    with DATA_LOCK:
        users=read_table("users")
        owner_id=resolve_user_identifier(users,owner_ident)
        if not owner_id: return json_response("0","","invalid owner_id")
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row: return json_response("0","","group not found")
        if not is_group_admin(row,owner_id): return json_response("0","","no permission")
        members=split_members(row.get("members",""))
        member_tel=member_ident if member_ident in members or member_ident==row.get("owner_id") else resolve_user_identifier(users,member_ident)
        if not member_tel: return json_response("0","","invalid member")
        if member_tel==row.get("owner_id"): return json_response("0","","cannot remove owner")
        admins=split_members(row.get("authority",""))
        if row.get("owner_id")!=owner_id and member_tel in admins: return json_response("0","","only owner can remove admin")
        row["members"]=join_members([m for m in members if m!=member_tel])
        if member_tel in admins: row["authority"]=join_members([a for a in admins if a!=member_tel])
        write_table("groups",groups)
        messages=read_table("messages")
        display=resolve_user_identifier(users,member_tel) or member_tel
        head=find_user(users,member_tel).get("head_url","") if find_user(users,member_tel) else ""
        notice=append_group_notice_message(messages,group_id,member_tel,display,head,f"{display}被移出群聊")
        if notice: write_table("messages",messages)
        targets=split_members(row.get("members",""))
    if notice and targets:
        p=build_ws_payload(message_to_dict(notice))
        for t in targets: push_ws(t,p)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/update_group", methods=["POST"])
@rate_limit()
def group_update():
    group_id=get_param("group_id","").strip()
    owner_id=get_param("owner_id","").strip()
    if not group_id or not owner_id: return json_response("0","","missing group_id or owner_id")
    updates={}
    for k in ["group_name","image_path"]:
        v=get_optional_param(k)
        if v is not None: updates[k]=v
    if not updates: return json_response("0","","no fields to update")
    with DATA_LOCK:
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row or (row.get("owner_id") and row.get("owner_id")!=owner_id): return json_response("0","","only owner can update")
        for k,v in updates.items(): row[k]=v
        write_table("groups",groups)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/announcement/get", methods=["POST"])
@rate_limit()
def group_announcement_get():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip() or get_param("user_tel","").strip()
    if not group_id or not user_ident: return json_response("0","","missing group_id or user_id")
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","invalid user_id")
        groups=read_table("groups")
        group=find_group(groups,group_id)
        if not group or not is_group_member(group,user_tel): return json_response("0","","not in group")
        announcements=read_table("group_announcements")
        ann=find_group_announcement(announcements,group_id)
        if not ann: return json_response("1",{"exists":"0"},"ok")
        reads=read_table("group_announcement_reads")
        read_flag=is_announcement_read(reads,ann.get("id",""),user_tel)
    data=announcement_to_dict(ann)
    data["exists"]="1"
    data["is_read"]="1" if read_flag else "0"
    return json_response("1",data,"ok")

@app.route("/group/announcement/set", methods=["POST"])
@rate_limit()
def group_announcement_set():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip() or get_param("user_tel","").strip()
    content=get_param("content","").strip()
    if not group_id or not user_ident or not content: return json_response("0","","missing params")
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","invalid user_id")
        groups=read_table("groups")
        group=find_group(groups,group_id)
        if not group or not is_group_admin(group,user_tel): return json_response("0","","only owner or admin can update")
        announcements=read_table("group_announcements")
        ann=None
        for a in announcements:
            if a.get("group_id")==group_id:
                ann=a
                break
        now=str(now_ms())
        if ann:
            ann["content"]=content
            ann["creator"]=user_tel
            if not ann.get("created_at"): ann["created_at"]=now
            ann["updated_at"]=now
            ann["status"]="active"
        else:
            ann={"id":str(next_id(announcements)),"group_id":group_id,"content":content,"creator":user_tel,"created_at":now,"updated_at":now,"status":"active"}
            announcements.append(ann)
        write_table("group_announcements",announcements)
    return json_response("1",announcement_to_dict(ann),"ok")

@app.route("/group/announcement/delete", methods=["POST"])
@rate_limit()
def group_announcement_delete():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip() or get_param("user_tel","").strip()
    if not group_id or not user_ident: return json_response("0","","missing group_id or user_id")
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","invalid user_id")
        groups=read_table("groups")
        group=find_group(groups,group_id)
        if not group or not is_group_admin(group,user_tel): return json_response("0","","only owner or admin can update")
        announcements=read_table("group_announcements")
        for a in announcements:
            if a.get("group_id")==group_id and a.get("status")!="deleted":
                a["content"]=""
                a["status"]="deleted"
                a["updated_at"]=str(now_ms())
                write_table("group_announcements",announcements)
                break
    return json_response("1","","ok")

@app.route("/group/announcement/read", methods=["POST"])
@rate_limit()
def group_announcement_read():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip() or get_param("user_tel","").strip()
    if not group_id or not user_ident: return json_response("0","","missing group_id or user_id")
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","invalid user_id")
        groups=read_table("groups")
        group=find_group(groups,group_id)
        if not group or not is_group_member(group,user_tel): return json_response("0","","not in group")
        announcements=read_table("group_announcements")
        ann=find_group_announcement(announcements,group_id)
        if not ann: return json_response("1","","ok")
        reads=read_table("group_announcement_reads")
        if not is_announcement_read(reads,ann.get("id",""),user_tel):
            reads.append({"id":str(next_id(reads)),"announcement_id":ann.get("id",""),"group_id":group_id,"user_tel":user_tel,"read_at":str(now_ms())})
            write_table("group_announcement_reads",reads)
    return json_response("1","","ok")

@app.route("/group/set_admins", methods=["POST"])
@rate_limit()
def group_set_admins():
    group_id=get_param("group_id","").strip()
    owner_ident=get_param("owner_id","").strip()
    admins_raw=get_param("admins","").strip()
    if not group_id or not owner_ident: return json_response("0","","missing group_id or owner_id")
    with DATA_LOCK:
        users=read_table("users")
        owner_id=resolve_user_identifier(users,owner_ident)
        if not owner_id: return json_response("0","","invalid owner_id")
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row or (row.get("owner_id") and row.get("owner_id")!=owner_id): return json_response("0","","only owner can set admins")
        members=split_members(row.get("members",""))
        resolved=[]
        for a in split_members(admins_raw):
            ra=resolve_user_identifier(users,a)
            if ra and ra!=row.get("owner_id") and ra in members and ra not in resolved:
                resolved.append(ra)
        row["authority"]=join_members(resolved)
        write_table("groups",groups)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/set_join_approval", methods=["POST"])
@rate_limit()
def group_set_join_approval():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip()
    if not group_id or not user_ident: return json_response("0","","missing group_id or user_id")
    enabled=parse_bool(get_param("enabled","0"))
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","invalid user_id")
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row or not is_group_admin(row,user_tel): return json_response("0","","only owner or admin can update")
        row["receive"]="1" if enabled else "0"
        write_table("groups",groups)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/join", methods=["POST"])
@rate_limit()
def group_join():
    group_id=get_param("group_id","").strip()
    user_ident=get_param("user_id","").strip() or get_param("user_tel","").strip()
    if not group_id or not user_ident: return json_response("0","","missing group_id or user_id")
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","user not found")
        groups=read_table("groups")
        row=find_group(groups,group_id)
        if not row: return json_response("0","","group not found")
        if row.get("owner_id")==user_tel: return json_response("1",group_to_dict(row),"ok")
        members=split_members(row.get("members",""))
        if user_tel in members: return json_response("1",group_to_dict(row),"ok")
        if parse_bool(row.get("receive","0")):
            reqs=read_table("group_requests")
            if not any(r.get("group_id")==group_id and r.get("user_tel")==user_tel and r.get("status")=="pending" for r in reqs):
                reqs.append({"id":str(next_id(reqs)),"group_id":group_id,"user_tel":user_tel,"created_at":str(now_ms()),"status":"pending","handled_at":"","handler":""})
                write_table("group_requests",reqs)
            return json_response("0","","pending")
        members.append(user_tel)
        row["members"]=join_members(members)
        write_table("groups",groups)
        messages=read_table("messages")
        display=resolve_user_identifier(users,user_tel) or user_tel
        head=find_user(users,user_tel).get("head_url","") if find_user(users,user_tel) else ""
        notice=append_group_notice_message(messages,group_id,user_tel,display,head,f"{display}加入群聊")
        if notice: write_table("messages",messages)
        targets=split_members(row.get("members",""))
    if notice and targets:
        p=build_ws_payload(message_to_dict(notice))
        for t in targets: push_ws(t,p)
    return json_response("1",group_to_dict(row),"ok")

@app.route("/group/requests/list", methods=["POST"])
@rate_limit()
def group_request_list():
    user_ident=get_param("user_id","").strip()
    if not user_ident: return json_response("0","","missing user_id")
    with DATA_LOCK:
        users=read_table("users")
        user_tel=resolve_user_identifier(users,user_ident)
        if not user_tel: return json_response("0","","user not found")
        groups=read_table("groups")
        group_map={g.get("group_id",""):g for g in groups if g.get("group_id")}
        allowed={g.get("group_id","") for g in groups if g.get("group_id") and is_group_admin(g,user_tel)}
        reqs=read_table("group_requests")
        rows=[]
        for r in reqs:
            if r.get("status")!="pending": continue
            gid=r.get("group_id","")
            if gid not in allowed: continue
            applicant=find_user(users,r.get("user_tel",""))
            rows.append(group_request_to_dict(r,applicant,group_map.get(gid)))
    return json_response("1",rows,"ok")

@app.route("/group/requests/respond", methods=["POST"])
@rate_limit()
def group_request_respond():
    request_id=get_param("request_id","").strip()
    action=get_param("action","").strip()
    user_ident=get_param("user_id","").strip()
    if not request_id or not action or not user_ident: return json_response("0","","missing params")
    if action not in ("accept","reject"): return json_response("0","","invalid action")
    with DATA_LOCK:
        users=read_table("users")
        operator=resolve_user_identifier(users,user_ident)
        if not operator: return json_response("0","","user not found")
        groups=read_table("groups")
        reqs=read_table("group_requests")
        target=next((r for r in reqs if r.get("id")==request_id),None)
        if not target: return json_response("0","","request not found")
        gid=target.get("group_id","")
        group=find_group(groups,gid)
        if not group or not is_group_admin(group,operator): return json_response("0","","no permission")
        now_str=str(now_ms())
        applicant=target.get("user_tel","")
        added=False
        if action=="accept":
            members=split_members(group.get("members",""))
            if applicant and applicant not in members:
                members.append(applicant)
                group["members"]=join_members(members)
                added=True
        target["status"]="approved" if action=="accept" else "rejected"
        target["handled_at"]=now_str
        target["handler"]=operator
        write_table("groups",groups)
        write_table("group_requests",reqs)
        if added:
            messages=read_table("messages")
            display=resolve_user_identifier(users,applicant) or applicant
            head=find_user(users,applicant).get("head_url","") if find_user(users,applicant) else ""
            notice=append_group_notice_message(messages,gid,applicant,display,head,f"{display}加入群聊")
            if notice:
                write_table("messages",messages)
                targets=split_members(group.get("members",""))
                p=build_ws_payload(message_to_dict(notice))
                for t in targets: push_ws(t,p)
    return json_response("1","","ok")

# ---------- 消息 ----------
@app.route("/message/send", methods=["POST"])
@message_rate_limit
def message_send():
    conversation_id = get_param("conversation_id", "").strip()
    sender_tel = get_param("sender_tel", "").strip()
    sender_name = get_param("sender_name", "").strip()
    receiver_id = get_param("receiver_id", "").strip()
    is_group_raw = get_param("is_group", "0").strip()
    content = get_param("content", "").strip()
    message_type = get_param("message_type", "text").strip()
    media_url = get_param("media_url", "").strip()
    device_id = get_device_id()

    if not conversation_id or not sender_tel:
        return json_response("0", "", "missing conversation_id or sender_tel")
    if message_type == "text" and not content:
        return json_response("0", "", "missing content")
    if message_type in ("image", "voice", "emoji", "video", "file") and not media_url:
        return json_response("0", "", "missing media_url")

    is_group = "1" if is_group_raw in ("1", "true", "True") else "0"
    timestamp = str(now_ms())
    targets = []

    with DATA_LOCK:
        # ----- 违禁词检测（封账号10分钟） -----
        if content:
            banned_rows = read_table("banned_words")
            for bw in banned_rows:
                word = bw.get("word", "").strip()
                if word and word in content:
                    reports = read_table("reports")
                    existing_ban = None
                    for r in reports:
                        if r.get("target_tel") == sender_tel and r.get("status") == "banned":
                            existing_ban = r
                            break
                    if existing_ban:
                        return json_response("0", "", "账号已被封禁，无法发送消息")
                    else:
                        ban_until = str(now_ms() + 600 * 1000)  # 10分钟
                        reports.append({
                            "id": str(next_id(reports)),
                            "reporter_tel": "system",
                            "target_tel": sender_tel,
                            "device_id": device_id or "",
                            "reason": f"发送违禁词: {word}",
                            "created_at": str(now_ms()),
                            "status": "banned",
                            "ban_until": ban_until,
                            "handled_at": str(now_ms()),
                            "handler": "system"
                        })
                        write_table("reports", reports)
                        kick_user(sender_tel, f"账号已被封禁10分钟（原因：发送违禁词“{word}”）")
                        return json_response("0", "", f"消息包含违禁词“{word}”，账号已被封禁10分钟")
        # ------------------

        if device_id:
            dev_bans = read_table("device_bans")
            ban_until = get_active_device_ban_until(dev_bans, device_id)
            if ban_until is not None:
                return json_response("0", "", device_ban_message(ban_until))

        reports = read_table("reports")
        ban_until = get_active_ban_until(reports, sender_tel)
        if ban_until is not None:
            return json_response("0", "", ban_message(ban_until))

        groups = read_table("groups")
        friendships = read_table("friendships")
        users = read_table("users")
        messages = read_table("messages")

        if is_group == "1":
            group = find_group(groups, conversation_id)
            if not group:
                return json_response("0", "", "group not found")
            members = split_members(group.get("members", ""))
            if sender_tel not in members:
                return json_response("0", "", "not in group")
            targets = [m for m in members if m and m != sender_tel]
        else:
            if not receiver_id:
                return json_response("0", "", "missing receiver_id")
            computed = build_conversation_id(sender_tel, receiver_id)
            if computed:
                conversation_id = computed
            if sender_tel == receiver_id:
                targets = []
            else:
                if not are_friends(friendships, sender_tel, receiver_id):
                    return json_response("0", "", "not friends")
                targets = [receiver_id]

        sender = find_user(users, sender_tel)
        row = {
            "id": str(next_id(messages)),
            "conversation_id": conversation_id,
            "sender_tel": sender_tel,
            "sender_name": sender_name,
            "sender_head_url": sender.get("head_url", "") if sender else "",
            "message_type": message_type,
            "media_url": media_url,
            "receiver_id": receiver_id,
            "is_group": is_group,
            "content": content,
            "timestamp": timestamp,
        }
        messages.append(row)
        write_table("messages", messages)

    # 消息发送成功，奖励 0.1 旧币
    add_balance(sender_tel, 0.1, "发送消息奖励")

    message_dict = message_to_dict(row)
    payload = build_ws_payload(message_dict)
    for t in targets:
        push_ws(t, payload)

    return json_response("1", message_dict, "ok")

# ---------- 通话 ----------
@app.route("/call/start", methods=["POST"])
@rate_limit()
def call_start():
    caller=get_param("caller_tel","").strip()
    callee=get_param("callee_tel","").strip()
    if not caller or not callee or caller==callee: return json_response("0","","invalid")
    with DATA_LOCK:
        if not are_friends(read_table("friendships"),caller,callee): return json_response("0","","not friends")
        users=read_table("users")
    caller_name=find_user(users,caller).get("user_name","") or caller
    call_id=f"{now_ms()}_{random.randint(1000,9999)}"
    push_ws(callee, build_call_payload({"action":"invite","call_id":call_id,"from_tel":caller,"from_name":caller_name,"to_tel":callee}))
    return json_response("1",{"call_id":call_id},"ok")

@app.route("/call/accept", methods=["POST"])
@rate_limit()
def call_accept():
    call_id=get_param("call_id","").strip()
    caller=get_param("caller_tel","").strip()
    callee=get_param("callee_tel","").strip()
    if not call_id or not caller or not callee: return json_response("0","","missing params")
    push_ws(caller, build_call_payload({"action":"accept","call_id":call_id,"from_tel":callee,"to_tel":caller}))
    return json_response("1","","ok")

@app.route("/call/reject", methods=["POST"])
@rate_limit()
def call_reject():
    call_id=get_param("call_id","").strip()
    caller=get_param("caller_tel","").strip()
    callee=get_param("callee_tel","").strip()
    if not call_id or not caller or not callee: return json_response("0","","missing params")
    push_ws(caller, build_call_payload({"action":"reject","call_id":call_id,"from_tel":callee,"to_tel":caller}))
    return json_response("1","","ok")

@app.route("/call/end", methods=["POST"])
@rate_limit()
def call_end():
    call_id=get_param("call_id","").strip()
    from_tel=get_param("from_tel","").strip()
    to_tel=get_param("to_tel","").strip()
    if not call_id or not from_tel or not to_tel: return json_response("0","","missing params")
    push_ws(to_tel, build_call_payload({"action":"end","call_id":call_id,"from_tel":from_tel,"to_tel":to_tel}))
    return json_response("1","","ok")

def build_call_payload(payload):
    return json.dumps({"type":"call","data":encrypt_text(json.dumps(payload,ensure_ascii=True)),"enc":"1"},ensure_ascii=True)

# ---------- 消息撤回 ----------
@app.route("/message/revoke", methods=["POST"])
@rate_limit()
def message_revoke():
    message_id = get_optional_param_any("message_id", "msg_id", "msgId", "id")
    user_tel = get_optional_param_any("user_tel", "sender_tel", "userId", "senderId")
    if not message_id or not user_tel:
        print("[REVOKE] 参数缺失", message_id, user_tel)
        return json_response("0", "", "missing message_id or user_tel")
    message_id = str(message_id).strip()
    user_tel = str(user_tel).strip()
    print(f"[REVOKE] 收到: msg_id={message_id}, user_tel={user_tel}")
    with DATA_LOCK:
        messages = read_table("messages")
        target = None
        for row in messages:
            rid = str(row.get("id", ""))
            if rid == message_id or (message_id.isdigit() and int(rid) == int(message_id)):
                target = row
                break
        if not target:
            print(f"[REVOKE] 未找到消息 id={message_id}")
            return json_response("0", "", "message not found")
        if target.get("sender_tel") != user_tel:
            print(f"[REVOKE] 权限错误: 发送者={target.get('sender_tel')}, 操作者={user_tel}")
            return json_response("0", "", "no permission")
        target["message_type"] = "revoke"
        target["content"] = "消息已撤回"
        target["media_url"] = ""
        write_table("messages", messages)
        print(f"[REVOKE] 消息 {message_id} 撤回成功")
        targets = []
        if target.get("is_group") == "1":
            groups = read_table("groups")
            group = find_group(groups, target.get("conversation_id", ""))
            if group:
                targets = split_members(group.get("members", ""))
        else:
            if target.get("sender_tel"):
                targets.append(target.get("sender_tel"))
            if target.get("receiver_id") and target.get("receiver_id") != target.get("sender_tel"):
                targets.append(target.get("receiver_id"))
        msg_dict = message_to_dict(target)
        payload = build_ws_payload(msg_dict)
        for t in targets:
            push_ws(t, payload)
    return json_response("1", msg_dict, "ok")

# ---------- 消息拉取 ----------
@app.route("/message/pull", methods=["GET", "POST"])
@rate_limit()
def message_pull():
    conversation_id = get_param("conversation_id", "").strip()
    if not conversation_id:
        return json_response("0", "", "missing conversation_id")
    is_group_raw = get_param("is_group", "").strip()
    with DATA_LOCK:
        all_messages = read_table("messages")
        filtered = []
        for row in all_messages:
            if is_group_raw in ("1", "true") and row.get("is_group") != "1":
                continue
            if is_group_raw in ("0", "false") and row.get("is_group") == "1":
                continue
            if row.get("is_group") == "1":
                if row.get("conversation_id") != conversation_id:
                    continue
            else:
                computed = build_conversation_id(row.get("sender_tel", ""), row.get("receiver_id", ""))
                if computed and computed != conversation_id:
                    continue
                elif not computed and row.get("conversation_id") != conversation_id:
                    continue
            filtered.append(row)
        filtered.sort(key=lambda r: int(r.get("timestamp") or 0), reverse=True)
        filtered = filtered[:200]
        filtered.reverse()
        rows = [message_to_dict(r) for r in filtered]
        for r in rows:
            if r.get("is_group") != "1":
                computed = build_conversation_id(r.get("sender_tel", ""), r.get("receiver_id", ""))
                if computed:
                    r["conversation_id"] = computed
        if rows:
            t_min = min(int(r.get("timestamp", 0)) for r in rows)
            t_max = max(int(r.get("timestamp", 0)) for r in rows)
            print(f"[PULL] 会话 {conversation_id} 返回 {len(rows)} 条，时间范围 {t_min} -> {t_max} (升序)")
    return json_response("1", rows, "ok")

@app.route("/message/pull_batch", methods=["GET", "POST"])
@rate_limit()
def message_pull_batch():
    items, err = parse_pull_batch_items()
    if err:
        return json_response("0", "", err)
    if not items:
        return json_response("1", [], "ok")
    results = []
    with DATA_LOCK:
        all_messages = read_table("messages")
        for entry in items:
            if not isinstance(entry, dict):
                continue
            conv_id = str(entry.get("conversation_id") or "").strip()
            if not conv_id:
                continue
            is_group_raw = str(entry.get("is_group") or "").strip()
            filtered = []
            for row in all_messages:
                if is_group_raw in ("1", "true") and row.get("is_group") != "1":
                    continue
                if is_group_raw in ("0", "false") and row.get("is_group") == "1":
                    continue
                if row.get("is_group") == "1":
                    if row.get("conversation_id") != conv_id:
                        continue
                else:
                    computed = build_conversation_id(row.get("sender_tel", ""), row.get("receiver_id", ""))
                    if computed and computed != conv_id:
                        continue
                    elif not computed and row.get("conversation_id") != conv_id:
                        continue
                filtered.append(row)
            filtered.sort(key=lambda r: int(r.get("timestamp") or 0), reverse=True)
            filtered = filtered[:200]
            filtered.reverse()
            batch_rows = [message_to_dict(r) for r in filtered]
            for r in batch_rows:
                if r.get("is_group") != "1":
                    computed = build_conversation_id(r.get("sender_tel", ""), r.get("receiver_id", ""))
                    if computed:
                        r["conversation_id"] = computed
            results.append({
                "conversation_id": conv_id,
                "is_group": is_group_raw,
                "messages": batch_rows,
            })
    return json_response("1", results, "ok")

# ---------- 头像/媒体上传 ----------
@app.route("/user/upload_avatar", methods=["POST"])
@rate_limit()
def upload_avatar():
    file = request.files.get("file") or request.files.get("image")
    if not file:
        return json_response("0", "", "no file")
    ext = os.path.splitext(file.filename)[1].lower()
    allowed_exts = {'.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp'}
    if ext not in allowed_exts:
        return json_response("0", "", "不支持的头像格式，仅限 jpg/png/gif/webp/bmp")
    file.seek(0, os.SEEK_END)
    size = file.tell()
    file.seek(0)
    if size > 10 * 1024 * 1024:
        return json_response("0", "", "头像图片不能超过10MB")
    filename = build_upload_filename(ext)
    file.save(UPLOAD_DIR / filename)
    url = f"http://{request.host}/uploads/{filename}"
    return json_response("1", {"url": url}, "ok")
@app.route("/admin/old_coins", methods=["GET", "POST"])
@rate_limit()
def admin_old_coins():
    if not admin_logged_in():
        return render_template_string(ADMIN_HTML, page="login", next="/admin/old_coins", msg="")
    
    msg = ""
    err = ""
    
    if request.method == "POST":
        action = request.form.get("action", "").strip()
        target_tel = request.form.get("target_tel", "").strip()
        amount_str = request.form.get("amount", "").strip()
        
        if not target_tel:
            err = "请填写用户手机号"
        elif action not in ("add", "deduct", "set"):
            err = "无效操作"
        else:
            try:
                amount = float(amount_str)
                if action in ("add", "set") and amount < 0:
                    err = "金额不能为负数"
                elif action == "deduct" and amount <= 0:
                    err = "扣除金额必须为正数"
                else:
                    # 直接使用 SQL 更新
                    import pymysql
                    conn = pymysql.connect(**DB_CONFIG)
                    try:
                        with conn.cursor() as cur:
                            if action == "add":
                                # 增加：old_coins = old_coins + amount
                                sql = "UPDATE users SET old_coins = old_coins + %s WHERE telephone = %s"
                                cur.execute(sql, (str(amount), target_tel))
                            elif action == "deduct":
                                # 先查询当前余额检查是否足够
                                cur.execute("SELECT old_coins FROM users WHERE telephone = %s", (target_tel,))
                                row = cur.fetchone()
                                if not row:
                                    err = f"用户 {target_tel} 不存在"
                                else:
                                    current = float(row[0] or 0)
                                    if current < amount:
                                        err = f"用户余额不足 (当前 {current}, 需扣除 {amount})"
                                    else:
                                        sql = "UPDATE users SET old_coins = old_coins - %s WHERE telephone = %s"
                                        cur.execute(sql, (str(amount), target_tel))
                            else:  # set
                                sql = "UPDATE users SET old_coins = %s WHERE telephone = %s"
                                cur.execute(sql, (str(amount), target_tel))
                                addm = 0
                                sql2 = "UPDATE users SET old_coins = old_coins + %s WHERE telephone = %s"
                                cur.execute(sql2, (str(addm), target_tel))
                            if not err:
                                conn.commit()
                                # 获取更新后的值
                                cur.execute("SELECT old_coins FROM users WHERE telephone = %s", (target_tel,))
                                new_row = cur.fetchone()
                                new_balance = new_row[0] if new_row else None
                                msg = f"用户 {target_tel} 旧币已更新，当前余额: {new_balance}"
                    except Exception as e:
                        conn.rollback()
                        err = f"数据库错误: {str(e)}"
                    finally:
                        conn.close()
            except ValueError:
                err = "金额格式无效"
    
    with DATA_LOCK:
        users = read_table("users")
    users.sort(key=lambda u: int(u.get("id", 0)))
    total_old_coins = sum(float(u.get("old_coins", "0") or "0") for u in users)
    
    return render_template_string(ADMIN_HTML, page="old_coins", users=users, msg=msg, err=err, total_old_coins=total_old_coins)
@app.route("/message/upload_media", methods=["POST"])
@rate_limit()
def upload_media():
    file = request.files.get("file") or request.files.get("image") or request.files.get("audio") or request.files.get("video")
    if not file:
        return json_response("0", "", "no file")
    ext = os.path.splitext(file.filename)[1].lower()
    allowed_exts = {
        '.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp', '.ico', '.tiff',
        '.mp4', '.avi', '.mov', '.mkv', '.3gp', '.flv', '.wmv', '.m4v', '.mpg', '.mpeg',
        '.mp3', '.aac', '.ogg', '.wav', '.flac', '.m4a',
        '.pdf', '.doc', '.docx', '.xls', '.xlsx', '.ppt', '.pptx', '.txt', '.md',
        '.csv', '.rtf', '.odt', '.ods', '.odp',
        '.zip', '.rar', '.7z', '.tar', '.gz', '.bz2'
    }
    if ext not in allowed_exts:
        return json_response("0", "", f"不支持的文件类型: {ext}")
    file.seek(0)
    header = file.read(20)
    file.seek(0)
    if header.startswith(b'\x7fELF') or header.startswith(b'#!'):
        return json_response("0", "", "可执行文件被禁止")
    file.seek(0, os.SEEK_END)
    size = file.tell()
    file.seek(0)
    if ext in ('.jpg','.jpeg','.png','.gif','.webp','.bmp','.ico','.tiff'):
        max_size = 10 * 1024 * 1024
        type_name = "图片"
    elif ext in ('.mp4','.avi','.mov','.mkv','.3gp','.flv','.wmv','.m4v','.mpg','.mpeg'):
        max_size = 200 * 1024 * 1024
        type_name = "视频"
    elif ext in ('.mp3','.aac','.ogg','.wav','.flac','.m4a'):
        max_size = 50 * 1024 * 1024
        type_name = "音频"
    else:
        max_size = 100 * 1024 * 1024
        type_name = "文件"
    if size > max_size:
        return json_response("0", "", f"{type_name}文件过大，最大{max_size // (1024*1024)}MB")
    filename = build_upload_filename(ext)
    file.save(UPLOAD_DIR / filename)
    url = f"http://{request.host}/uploads/{filename}"
    return json_response("1", {"url": url}, "ok")

@app.route("/uploads/<path:filename>")
def uploaded_file(filename):
    return send_from_directory(UPLOAD_DIR, filename)

@app.route("/update/<path:filename>")
def update_file(filename):
    return send_from_directory(UPDATE_DIR, filename)

DATA_LOCK = threading.RLock()
if __name__=="__main__":
    init_storage()
    host=os.environ.get("OLDCHAT_HOST","0.0.0.0")
    port=int(os.environ.get("OLDCHAT_PORT","8880"))
    processes=int(os.environ.get("OLDCHAT_PROCESSES","1"))
    threads=int(os.environ.get("OLDCHAT_THREADS","4"))
    if processes>1 and threads>1: threads=1
    app.run(host=host,port=port,debug=False,threaded=threads>1,processes=processes)