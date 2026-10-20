# ═══════════════════════════════════════════════════════════════════════════
#  app.py — XONUS API  •  WEB DASHBOARD EDITION
# ═══════════════════════════════════════════════════════════════════════════

from flask import Flask, request, jsonify, render_template_string
import hmac
import hashlib
import requests
import string
import random
import secrets
import json
import base64
import re
import os
import time
import threading
import uuid
import concurrent.futures
from datetime import datetime, timezone
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
import urllib3

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

app = Flask(__name__)
app.config["JSON_SORT_KEYS"] = False
app.config["PROPAGATE_EXCEPTIONS"] = False

# ═══════════════════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════════════════
APP_ID         = 100067
RELEASE_VER    = "OB55"
GAME_VERSION   = "2.132.4"
HEX_KEY        = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"

URL_GUEST_REGISTER = "https://100067.connect.garena.com/api/v2/oauth/guest:register"
URL_TOKEN_GRANT    = "https://100067.connect.garena.com/api/v2/oauth/guest/token:grant"
URL_MAJOR_LOGIN    = "https://loginbp.ppmainecoonghj.com/MajorLogin"
URL_MAJOR_REGISTER = "https://loginbp.ppmainecoonghj.com/MajorRegister"
URL_NEWBIE_CHOICE  = "https://loginbp.ppmainecoonghj.com/ChooseNewbieChoice"

FORCE_REGION       = "ID"
FORCE_NAME_PREFIX  = "XNS"
MAX_COUNT          = 15
WORKER_CAP         = 10
SESSION_POOL       = 8
IP_POOL_INITIAL    = 100
IP_POOL_BG_MAX     = 5_000

TIMEOUT_TIERS = [
    (3,  (0.8, 2.5)),
    (7,  (0.8, 2.0)),
    (15, (0.6, 1.5)),
]

def pick_timeout(count):
    for max_c, t in TIMEOUT_TIERS:
        if count <= max_c: return t
    return (0.6, 1.5)

REGION_LANG = {
    "ME": "ar", "IND": "hi", "ID": "id", "JP": "ja",
    "VN": "vi", "TH": "th", "BD": "bn", "PK": "ur",
    "TW": "zh", "CIS": "ru", "SAC": "es", "BR": "pt",
    "SG": "en", "US": "en", "EU": "en", "LK": "en",
}

_AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
_AES_IV  = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])

FIELD_22 = bytes.fromhex(
    "4747524501010100620200001052aa0d669c6a368f08338060d2ee0690053af84a41edcd3558556ec10f24f4"
    "6c93ac64ca41a16732c46a2cb071246a79b8929032f9e1b6f4ef331bd53cabf29b09b97349a46e9863c0314e"
    "1a0d80819fef8aabf03876b3d037db354a7ccb5c1bce96411fb3753f6f50e44c69c4ed617fa30efb8ffc0517"
    "ff2f636739be1f304d999cfd6fd48bf69454199794c3dc88f55a4bdbd66534d5a061359cdfd1fb680cd37918"
    "df9fdb3cf7d80067b0a3506c90063cf62b2ccec11e23913a2fd7c4ef091331967bb518a5ad1e551146b90821"
    "be800883abadde39d6c80a5d798611466c748f075481806c5842ce45e6bd4e3368ec08fe2ec41ceb880cd862"
    "49eb71693f79f0bccf9e590c3fae12519fe08c7a1905d0927690109e0df28574bb14847225db1a59230e6662"
    "ed7730e15ff9a6c815cb41b420edeada735a4b03e181037c37c2c850257311df2f07b0a56e759372cbd0268e"
    "3f13a292ee4373e38ab5096e0342a5e0d7fec6da2bbc265d74baadd2b24ee4f74862f82c21d6694bac53f8ce"
    "80312a30068a6276a641c19b11d0305c6fe2f531ac7de578b29f543697f5c73663e6f23aa15277b6122dcd4d"
    "4171e38f9ac0b173f39c58416a16c5c1f4a35acd065ce78f449cf538a249339e763272d458e4ed86c976591a"
    "9c066b3a37111e44091eb6b5a795249f3e5145db022a6055f2cc675936391312f688f89627845df222a91156"
    "555225be36f9714a0ba50246d0f003bda3c9c1292ab73b4f79635ddd023218eda93a302d79e023404c143965"
    "44a930b98ed54771aca7fec10d095587685b473e81a9619764fad9256529dcd6e911f4f4629612287d4ee3ec"
    "5389f6ec4ec020b0e2aac017232a9197be9e46239ce690fe5d4872b2e98e651510c971667f3aca8b59f3e9d5"
    "0e43"
)

def _gen_ip(rng):
    public_first = [o for o in range(1, 224) if o not in (10, 127, 169, 172, 192)]
    a = rng.choice(public_first)
    return f"{a}.{rng.randint(0,255)}.{rng.randint(0,255)}.{rng.randint(1,254)}"

def _build_ip_pool(target, seed=1337):
    rng = random.Random(seed)
    pool = set()
    safety = target * 3
    while len(pool) < target and safety > 0:
        pool.add(_gen_ip(rng))
        safety -= 1
    pl = list(pool)
    rng.shuffle(pl)
    return pl

IP_POOL = _build_ip_pool(IP_POOL_INITIAL, seed=1337)
IP_COUNT = len(IP_POOL)
IP_LOCK = threading.Lock()

def _bg_expand_ip():
    global IP_POOL, IP_COUNT
    try:
        bigger = _build_ip_pool(IP_POOL_BG_MAX, seed=4242)
        with IP_LOCK:
            IP_POOL = bigger
            IP_COUNT = len(bigger)
    except: pass

threading.Thread(target=_bg_expand_ip, daemon=True).start()

def ip_headers():
    real = IP_POOL[random.randrange(IP_COUNT)]
    chain = [real] + [IP_POOL[random.randrange(IP_COUNT)] for _ in range(random.randint(1, 2))]
    return {
        "X-Forwarded-For": ", ".join(chain), "X-Real-IP": real, "X-Client-IP": real,
        "X-Originating-IP": real, "X-Remote-IP": real, "X-Remote-Addr": real,
        "Forwarded": f"for={real};proto=https", "CF-Connecting-IP": real,
    }

_SAMSUNG_MODELS = [("SM-A325M","13"),("SM-A525F","13"),("SM-A725F","13"),("SM-A127F","12"),("SM-A546E","14"),("SM-S918B","14"),("SM-G998B","13")]
_XIAOMI_MODELS = ["Poco X3","Poco F3","Poco F5","Xiaomi 12","Xiaomi 13 Pro","Redmi Note 10","Redmi Note 12"]
_REGS = ["HK","ID","SG","MY","PH","TH","VN"]

USER_AGENTS_POOL = []
for m, o in _SAMSUNG_MODELS:
    for r in _REGS: USER_AGENTS_POOL.append(f"GarenaMSDK/4.0.39({m};Android {o};en;{r};)")
for m in _XIAOMI_MODELS:
    for o in ["12","13","14"]:
        for r in _REGS: USER_AGENTS_POOL.append(f"GarenaMSDK/4.0.40({m};Android {o};en;{r};)")
USER_AGENTS_POOL = list(set(USER_AGENTS_POOL))
UA_COUNT = len(USER_AGENTS_POOL)

def random_ua(): return USER_AGENTS_POOL[random.randrange(UA_COUNT)]

DEVICE_MODELS = [
    ("Asus ASUS_AI2501_B","Android OS 12 / API-31 (SP1A.210812.016.C2)","Adreno (TM) 640"),
    ("Redmi Note 12 Pro","Android OS 13 / API-33 (TP1A.220624.014)","Adreno (TM) 618"),
    ("Samsung SM-M135F","Android OS 13 / API-33 (TP1A.220624.014)","Mali-G68"),
    ("Realme RMX3630","Android OS 12 / API-31 (SP1A.210812.016)","Adreno (TM) 610"),
    ("Vivo V2149","Android OS 13 / API-33 (TP1A.220624.014)","Adreno (TM) 642L"),
]
DEVICE_COUNT = len(DEVICE_MODELS)

def generate_device_info():
    m, o, g = DEVICE_MODELS[random.randrange(DEVICE_COUNT)]
    u = uuid.uuid4()
    return {"model": m, "os_string": o, "gpu": g, "device_id": f"Google|{u}"}

def _new_session():
    s = requests.Session()
    adapter = requests.adapters.HTTPAdapter(pool_connections=SESSION_POOL, pool_maxsize=SESSION_POOL, max_retries=0)
    s.mount("https://", adapter); s.mount("http://", adapter)
    s.verify = False
    s.headers.update({"Accept": "application/json", "Accept-Encoding": "gzip, deflate", "Connection": "keep-alive"})
    return s

STATS = {"total_requests": 0, "total_success": 0, "total_fail": 0, "fail_register": 0, "fail_token": 0, "fail_major": 0}
STATS_LOCK = threading.Lock()

def record_success():
    with STATS_LOCK:
        STATS["total_requests"] += 1; STATS["total_success"] += 1

def record_fail(kind="major"):
    with STATS_LOCK:
        STATS["total_requests"] += 1; STATS["total_fail"] += 1
        key = "fail_register" if kind == "reg" else "fail_token" if kind == "tok" else "fail_major"
        STATS[key] += 1

_ALNUM = string.ascii_letters + string.digits
def generate_random_name(base): return f"{base[:4]}{''.join(random.choices(_ALNUM, k=8))}"

def encode_varint(n):
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def create_proto_field(field_num, value):
    if isinstance(value, int): return encode_varint((field_num << 3) | 0) + encode_varint(value)
    if isinstance(value, str):
        v = value.encode(); return encode_varint((field_num << 3) | 2) + encode_varint(len(v)) + v
    if isinstance(value, bytes): return encode_varint((field_num << 3) | 2) + encode_varint(len(value)) + value
    return b""

def build_proto(fields): return b"".join(create_proto_field(k, v) for k, v in fields.items())
def aes_encrypt_bytes(plain_bytes): return AES.new(_AES_KEY, AES.MODE_CBC, _AES_IV).encrypt(pad(plain_bytes, AES.block_size))

_KS14 = bytes([0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30])
def _make_field_f14(open_id):
    ob = open_id.encode("latin1", errors="ignore") if isinstance(open_id, str) else open_id
    return bytes((ob[i] ^ _KS14[i % 32]) for i in range(len(ob)))

JWT_RE = re.compile(r"eyJ[A-Za-z0-9_\-]+\.[A-Za-z0-9_\-]+\.[A-Za-z0-9_\-]+")
def extract_jwt(content):
    try:
        m = JWT_RE.search(content.decode("utf-8", errors="ignore"))
        return m.group(0) if m else None
    except: return None

def is_valid_jwt(tok): return bool(tok) and tok.startswith("eyJ") and tok.count(".") >= 2 and len(tok) > 50
def _ga_sv(): return str(int(time.time()) - random.randint(0, 60))

def guest_register(session, password, timeout):
    try:
        body = json.dumps({"app_id": APP_ID, "client_type": 2, "password": password, "source": 2}, separators=(",", ":"))
        sig = hmac.new(HEX_KEY.encode(), body.encode(), hashlib.sha256).hexdigest()
        headers = {"User-Agent": random_ua(), "Connection": "Keep-Alive", "Accept": "application/json", "Accept-Encoding": "gzip", "Authorization": f"Signature {sig}", "Content-Type": "application/json; charset=utf-8", "Host": "100067.connect.garena.com"}
        headers.update(ip_headers())
        r = session.post(URL_GUEST_REGISTER, headers=headers, data=body, timeout=timeout, verify=False)
        if r.status_code == 200:
            j = r.json()
            if j.get("code") == 0: return j["data"]["uid"]
    except: pass
    return None

def token_grant(session, uid, password, timeout):
    try:
        body = json.dumps({"client_id": APP_ID, "client_secret": HEX_KEY, "client_type": 2, "device_id": f"02-{uuid.uuid4()}", "password": password, "response_type": "token", "uid": uid}, separators=(",", ":"))
        headers = {"User-Agent": random_ua(), "Connection": "Keep-Alive", "Accept": "application/json", "Accept-Encoding": "gzip", "Content-Type": "application/json; charset=utf-8", "Host": "100067.connect.garena.com"}
        headers.update(ip_headers())
        r = session.post(URL_TOKEN_GRANT, headers=headers, data=body, timeout=timeout, verify=False)
        if r.status_code == 200:
            j = r.json()
            if j.get("code") == 0: return j["data"]["access_token"], j["data"]["open_id"]
    except: pass
    return None

def build_majorlogin_proto(open_id, access_token, lang="en"):
    device = generate_device_info()
    now_ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    fields = {3: now_ts, 4: "free fire", 5: 4, 7: "1.132.1", 8: "2019116753", 9: device["os_string"], 10: "Handheld", 11: device["model"], 12: 1280, 13: 720, 14: "240", 15: "x86-64", 16: 6000, 17: device["gpu"], 18: "OpenGL", 19: device["device_id"], 20: "127.0.0.1", 21: lang, 22: open_id, 23: "4", 24: "Handheld", 25: device["model"], 26: "IND", 29: access_token, 30: 1, 41: "Jio", 42: "WIFI", 92: 20000, 93: "max", 97: 1, 98: 1, 99: "4", 100: "4", 104: 77149, 105: 1}
    return aes_encrypt_bytes(build_proto(fields))

def major_login(session, access_token, open_id, lang, timeout):
    try:
        payload = build_majorlogin_proto(open_id, access_token, lang)
        headers = {"User-Agent": random_ua(), "Accept-Encoding": "deflate, gzip", "X-GA-SV": _ga_sv(), "Authorization": f"Bearer {access_token}", "X-GA": "v1 1", "ReleaseVersion": RELEASE_VER, "Content-Type": "application/octet-stream", "X-Unity-Version": "2018.4.12f1", "Host": "loginbp.ppmainecoonghj.com"}
        headers.update(ip_headers())
        r = session.post(URL_MAJOR_LOGIN, headers=headers, data=payload, verify=False, timeout=timeout)
        if r.status_code == 200 and len(r.content) >= 20:
            jwt = extract_jwt(r.content)
            account_id = None
            if jwt and is_valid_jwt(jwt):
                try:
                    p = jwt.split(".")[1]; p += "=" * (4 - len(p) % 4)
                    dec = json.loads(base64.urlsafe_b64decode(p))
                    account_id = dec.get("account_id") or dec.get("external_id")
                except: pass
            if not account_id:
                nums = re.findall(r"\b\d{10,12}\b", r.content.decode("utf-8", errors="ignore"))
                if nums: account_id = nums[0]
            if account_id: return {"account_id": str(account_id), "jwt_token": jwt or ""}
    except: pass
    return None

def major_register(session, access_token, open_id, uid, password, region, nick, lang, timeout):
    try:
        payload = {1: nick, 2: access_token, 3: open_id, 5: 102000007, 6: 4, 7: 1, 13: 1, 14: _make_field_f14(open_id), 15: lang, 16: 1, 17: 1, 22: FIELD_22}
        enc = aes_encrypt_bytes(build_proto(payload))
        headers = {"User-Agent": random_ua(), "Accept-Encoding": "deflate, gzip", "X-GA-SV": _ga_sv(), "Authorization": "Bearer", "X-GA": "v1 1", "ReleaseVersion": RELEASE_VER, "Content-Type": "application/x-www-form-urlencoded", "X-Unity-Version": "2018.4.12f1", "Host": "loginbp.ppmainecoonghj.com"}
        headers.update(ip_headers())
        session.post(URL_MAJOR_REGISTER, headers=headers, data=enc, verify=False, timeout=timeout)
        return major_login(session, access_token, open_id, lang, timeout)
    except: return None

def _fire_and_forget_bind(region, jwt, timeout):
    if not jwt or region.upper() == "BR": return
    def _run():
        try:
            s = _new_session()
            rc = "RU" if region.upper() == "CIS" else region.upper()
            payload = aes_encrypt_bytes(build_proto({1: rc}))
            headers = {"X-GA-SV": _ga_sv(), "Authorization": f"Bearer {jwt}", "ReleaseVersion": RELEASE_VER, "Content-Type": "application/x-www-form-urlencoded"}
            s.post(URL_NEWBIE_CHOICE, data=payload, headers=headers, timeout=timeout, verify=False)
            s.close()
        except: pass
    threading.Thread(target=_run, daemon=True).start()

def get_rarity_info(account_id):
    return {"rarity": "COMMON"}

def create_account(region, account_name, password_prefix, is_ghost=False, skip_bind=False, timeout=(0.8, 2.2)):
    session = _new_session()
    try:
        password = secrets.token_hex(16)
        uid = guest_register(session, password, timeout)
        if not uid: record_fail("reg"); return None
        tok = token_grant(session, uid, password, timeout)
        if not tok: record_fail("tok"); return None
        access_token, open_id = tok
        lang = "pt" if is_ghost else REGION_LANG.get(region.upper(), "en")
        nick = generate_random_name(account_name)
        login = major_register(session, access_token, open_id, uid, password, region, nick, lang, timeout)
        if not login: record_fail("major"); return None
        if not skip_bind: _fire_and_forget_bind(region, login.get("jwt_token", ""), timeout)
        record_success()
        return {
            "uid": str(uid), "password": password, "account_id": str(login["account_id"]),
            "name": nick, "region": "GHOST" if is_ghost else region.upper(),
            "jwt_token": login.get("jwt_token", ""), "status": "success"
        }
    except: record_fail("major"); return None
    finally: 
        try: session.close()
        except: pass

def create_single_account(args):
    r = create_account(*args)
    return r if (r and r.get("uid")) else None

# ═══════════════════════════════════════════════════════════════════════════
#  WEB UI HTML TEMPLATE (DASHBOARD)
# ═══════════════════════════════════════════════════════════════════════════
HTML_TEMPLATE = """
<!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>XONUS Dashboard - Auto Create Account</title>
    <link href="https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700&display=swap" rel="stylesheet">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <style>
        :root {
            --bg: #0f172a; --card: #1e293b; --text: #f8fafc; --text-muted: #94a3b8;
            --primary: #3b82f6; --primary-hover: #2563eb; --border: #334155;
            --success: #10b981; --danger: #ef4444;
        }
        [data-theme="light"] {
            --bg: #f1f5f9; --card: #ffffff; --text: #0f172a; --text-muted: #64748b;
            --primary: #3b82f6; --primary-hover: #2563eb; --border: #e2e8f0;
        }
        * { box-sizing: border-box; margin: 0; padding: 0; font-family: 'Plus Jakarta Sans', sans-serif; transition: background 0.3s, color 0.3s; }
        body { background: var(--bg); color: var(--text); min-height: 100vh; display: flex; flex-direction: column; align-items: center; padding: 20px; }
        
        .header { width: 100%; max-width: 800px; display: flex; justify-content: space-between; align-items: center; margin-bottom: 30px; }
        .logo { font-size: 24px; font-weight: 700; color: var(--primary); display: flex; align-items: center; gap: 10px; }
        .theme-toggle { background: var(--card); border: 1px solid var(--border); color: var(--text); padding: 10px 15px; border-radius: 50px; cursor: pointer; transition: 0.3s; }
        .theme-toggle:hover { border-color: var(--primary); }

        .container { width: 100%; max-width: 800px; background: var(--card); border: 1px solid var(--border); border-radius: 16px; padding: 30px; box-shadow: 0 10px 30px rgba(0,0,0,0.1); }
        
        .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 20px; margin-bottom: 20px; }
        @media (max-width: 600px) { .grid { grid-template-columns: 1fr; } }
        
        .form-group { display: flex; flex-direction: column; gap: 8px; }
        label { font-size: 14px; font-weight: 600; color: var(--text-muted); }
        input, select { padding: 12px 16px; border-radius: 10px; border: 1px solid var(--border); background: var(--bg); color: var(--text); font-size: 15px; outline: none; transition: 0.2s; }
        input:focus, select:focus { border-color: var(--primary); box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.2); }
        
        .btn-generate { width: 100%; padding: 16px; background: var(--primary); color: white; border: none; border-radius: 10px; font-size: 16px; font-weight: 700; cursor: pointer; display: flex; justify-content: center; align-items: center; gap: 10px; margin-top: 10px; transition: 0.3s; }
        .btn-generate:hover { background: var(--primary-hover); transform: translateY(-2px); }
        .btn-generate:disabled { background: var(--text-muted); cursor: not-allowed; transform: none; }

        .loading-container { display: none; text-align: center; margin-top: 30px; }
        .spinner { width: 40px; height: 40px; border: 4px solid var(--border); border-top-color: var(--primary); border-radius: 50%; animation: spin 1s linear infinite; margin: 0 auto 15px; }
        @keyframes spin { 100% { transform: rotate(360deg); } }

        .results-container { display: none; margin-top: 30px; }
        .results-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 15px; border-bottom: 1px solid var(--border); padding-bottom: 10px; }
        .results-header h3 { font-size: 18px; }
        
        .account-card { background: var(--bg); border: 1px solid var(--border); border-radius: 12px; padding: 20px; margin-bottom: 15px; position: relative; animation: fadeIn 0.5s ease; }
        @keyframes fadeIn { from { opacity: 0; transform: translateY(10px); } to { opacity: 1; transform: translateY(0); } }
        .account-card .badge { position: absolute; top: 15px; right: 15px; background: rgba(16, 185, 129, 0.1); color: var(--success); padding: 5px 10px; border-radius: 20px; font-size: 12px; fon
