#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Netflix EPR Telegram V22.14 — Signup-Only Proxy + Self-Healing + Railway + Telegram OTP + Membership Confirmation + Password/PIN Full Manager

Main flow
---------
1. Arabic-Iraq locale is forced for Netflix requests and Chromium sessions.
2. Existing-account login is available from Telegram using email + OTP, with a Password alternative; credentials remain ephemeral.
   Existing-account login always uses direct Railway networking. The saved proxy is reserved for new-account signup only.
3. EPR bootstrap (Requests first, Chromium fallback only when live state is needed).
4. Plan selection -> mobile billing -> phone verification.
5. Carrier-billing OTP is requested automatically from the owner as soon as the OTP screen is reached. On the direct CLCS path it stays only in memory until approval.
6. Before Start Membership, Telegram shows an explicit owner confirmation with Approve/Reject buttons. Only Approve submits the OTP + Start Membership action in the same live Netflix session; Reject discards the OTP and leaves membership unstarted.
7. The selected proxy is used only from new-account EPR/signup through Terms/phone verification/OTP and the explicitly approved Start Membership action. Immediately after membership becomes active, V22.14 detaches the proxy before password/profile/PIN management.
8. Password is entered through the private Telegram bot, used only in memory, and never written
   to accounts.json. The incoming Telegram password message is deleted best-effort.
9. Profile names/PINs can be managed in bulk or one-by-one. PIN updates use direct GraphQL first.
   If Netflix asks for fresh profile-lock verification, V22 deliberately chooses the Password
   verification branch (not SMS/email), asks for the current account password, resumes the PIN
   change, refreshes the saved Netflix session, and continues.
10. Saved Netflix sessions survive bot restarts. Password values themselves are never persisted.

Safety boundary
---------------
Carrier-billing/payment OTP may be accepted only from the owner chat and is never persisted.
The bot never starts membership without an explicit owner confirmation in Telegram. It does not bypass OTP/CAPTCHA; on the direct CLCS path the approved action is the same OTP/Start Membership screen update from the current Netflix session.
Account-password and profile-lock password verification are non-payment account authentication and can be handled by this private owner-only bot.
"""

from __future__ import annotations

import html as html_lib
import base64
import json
import os
import re
import secrets
import shutil
import socket
import socketserver
import select
import threading
import time
import uuid
from pathlib import Path
from typing import Any, Optional
from urllib.parse import parse_qs, urlparse, quote

import requests

NETFLIX = "https://www.netflix.com"
GRAPHQL = f"{NETFLIX}/graphql"

def _writable_dir_from_env(env_name: str, fallback: Path) -> Path:
    """Use the configured directory only when the current host allows writing to it."""
    raw = (os.environ.get(env_name) or "").strip()
    candidate = Path(raw).expanduser() if raw else fallback
    try:
        candidate.mkdir(parents=True, exist_ok=True)
        # Verify that the directory is actually writable.
        probe = candidate / ".write_test"
        probe.write_text("ok", encoding="utf-8")
        probe.unlink(missing_ok=True)
        return candidate
    except (OSError, PermissionError):
        fallback.mkdir(parents=True, exist_ok=True)
        return fallback

# PythonAnywhere does not allow normal users to create/write /data.
# If NETFLIX_STORE_DIR points there (or to another unwritable location),
# automatically fall back to the user's home directory.
BASE_STORE_DIR = _writable_dir_from_env(
    "NETFLIX_STORE_DIR",
    Path.home() / ".netflix_epr_v18",
)

if os.environ.get("NETFLIX_OWNER_FILE"):
    requested_owner_file = Path(os.environ["NETFLIX_OWNER_FILE"]).expanduser()
    try:
        requested_owner_file.parent.mkdir(parents=True, exist_ok=True)
        OWNER_FILE = requested_owner_file
    except (OSError, PermissionError):
        OWNER_FILE = BASE_STORE_DIR / "owner.json"
elif os.environ.get("NETFLIX_STORE_DIR"):
    OWNER_FILE = BASE_STORE_DIR / "owner.json"
else:
    OWNER_FILE = Path.home() / ".netflix_epr_bot_owner.json"

TMPDIR = _writable_dir_from_env(
    "TMPDIR",
    Path.home() / ".netflix_tmp",
)

# Railway: keep the Telegram bot token only in the BOT_TOKEN secret variable.
BOT_TOKEN = os.environ.get("BOT_TOKEN", "7744831171:AAGMyFUGRg2BrU1BdmNKTvFRWLdgXm7EVl8").strip()
if not BOT_TOKEN:
    raise SystemExit("BOT_TOKEN missing")

TG_BASE = f"https://api.telegram.org/bot{BOT_TOKEN}"
TG = requests.Session()

# Persisted-query IDs learned from the validated trace.
PQ_MEMBERSHIP = "3f50f3b3-fff8-48c0-bbd3-5fa2cb04b3c1"
PQ_INIT_SIGNUP = "59134b11-7416-42ca-abb7-6d1f318975fe"
PQ_PRELOAD = "2eceeacc-e2fe-4157-82c2-6fcbec108525"
PQ_SCREEN_UPDATE = "bf08eba4-da1b-4e3b-92e4-ceb2b7c1c27d"
PQ_VERSION = 102

# Profile-management persisted queries captured from the user's own Netflix session.
PQ_ADD_PROFILE = "cca89a76-1986-49a9-9c8f-afaa2c098ead"
PQ_UPDATE_PROFILE_INFO = "cfd14150-9a88-4075-8278-e9fb8ce4baa0"
PQ_UPDATE_PROFILE_PIN = "d1528f2f-ed01-4dc1-b870-ee91bb2c3850"
PQ_REMOVE_PROFILE = "be35fe7f-2b59-4169-9c75-474474831d09"

STORE_DIR = BASE_STORE_DIR  # Same default store, but Railway can mount /data via NETFLIX_STORE_DIR.
STORE_DIR.mkdir(parents=True, exist_ok=True)
ACCOUNTS_FILE = STORE_DIR / "accounts.json"
PROXIES_FILE = STORE_DIR / "proxies.json"

# Trace-observed versions. They are used as headers only; the GraphQL payload itself is driven
# by live serverState/serverScreenUpdate values parsed from the current session.
DEFAULT_APP_VERSION = "v622e5d08"
DEFAULT_HAWKINS_VERSION = "5.26.0"
DEFAULT_UA = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) HeadlessChrome/149.0.0.0 Safari/537.36"
)
DEFAULT_LOCALE = "ar-IQ"
DEFAULT_LOCALE_HEADER = "ar-iq"
DEFAULT_ACCEPT_LANGUAGE = "ar-IQ,ar;q=0.9,en-US;q=0.6,en;q=0.5"
NETFLIX_IQ = f"{NETFLIX}/iq"

STATE_LOCK = threading.RLock()
WAIT_COND = threading.Condition(STATE_LOCK)
CHAT_STATE: dict[int, dict] = {}
ACTIVE_JOBS: dict[int, threading.Thread] = {}
CHANGE_PHONE_JOBS: dict[int, threading.Thread] = {}
PIN_JOBS: dict[int, threading.Thread] = {}
PASSWORD_JOBS: dict[int, threading.Thread] = {}
MANUAL_BROWSER_JOBS: dict[int, threading.Thread] = {}
LOGIN_JOBS: dict[int, threading.Thread] = {}
LOGIN_CANCEL_EVENTS: dict[int, threading.Event] = {}
# Cooperative cancellation for the long-running signup worker.  A cancelled worker may still
# be inside one short network request, but it is prevented from resurrecting deleted sessions.
JOB_CANCEL_EVENTS: dict[int, threading.Event] = {}
ACTIVE_JOB_ACCOUNTS: dict[int, str] = {}
DELETED_ACCOUNT_IDS: set[str] = set()
EPHEMERAL_PASSWORDS: dict[str, tuple[str, float]] = {}
PASSWORD_CACHE_TTL = 15 * 60


def _job_cancelled(chat_id: int) -> bool:
    with STATE_LOCK:
        ev = JOB_CANCEL_EVENTS.get(chat_id)
        return bool(ev and ev.is_set())


def _account_deleted(account_id: str) -> bool:
    with STATE_LOCK:
        return bool(account_id and account_id in DELETED_ACCOUNT_IDS)


def request_main_job_cancel(chat_id: int) -> bool:
    """Cooperatively cancel the active signup and wake every Telegram wait immediately."""
    with WAIT_COND:
        ev = JOB_CANCEL_EVENTS.get(chat_id)
        active = ACTIVE_JOBS.get(chat_id)
        had_job = bool(active and active.is_alive())
        if ev is not None:
            ev.set()
        st = CHAT_STATE.setdefault(chat_id, {})
        if st.get("awaiting_phone"):
            st["phone_value"] = "__CANCEL__"
        if st.get("awaiting_payment_otp"):
            st["payment_otp_value"] = "__CANCEL__"
        if st.get("awaiting_membership_confirmation"):
            st["membership_confirm_value"] = "NO"
        st["awaiting_phone"] = False
        st["awaiting_payment_otp"] = False
        st["awaiting_membership_confirmation"] = False
        WAIT_COND.notify_all()
        return had_job


def _join_cancelled_main_job(chat_id: int, timeout: float = 2.5) -> bool:
    """Give a cancelled worker a short chance to leave its wait loop before accepting a new job."""
    with STATE_LOCK:
        th = ACTIVE_JOBS.get(chat_id)
    if th is None or not th.is_alive():
        return True
    if th is threading.current_thread():
        return False
    if not _job_cancelled(chat_id):
        return False
    th.join(timeout=max(0.0, timeout))
    return not th.is_alive()


def _login_cancelled(chat_id: int) -> bool:
    with STATE_LOCK:
        ev = LOGIN_CANCEL_EVENTS.get(chat_id)
        return bool(ev and ev.is_set())


def request_login_cancel(chat_id: int) -> bool:
    """Cancel the owner-only login worker and wake Telegram credential waits."""
    with WAIT_COND:
        ev = LOGIN_CANCEL_EVENTS.get(chat_id)
        th = LOGIN_JOBS.get(chat_id)
        had_job = bool(th and th.is_alive())
        if ev is not None:
            ev.set()
        st = CHAT_STATE.setdefault(chat_id, {})
        if st.get("awaiting_login_email"):
            st["login_email_value"] = "__CANCEL__"
        if st.get("awaiting_login_otp"):
            st["login_otp_value"] = "__CANCEL__"
        if st.get("awaiting_login_password"):
            st["login_password_value"] = "__CANCEL__"
        st["login_method_value"] = "__CANCEL__"
        st["awaiting_login_email"] = False
        st["awaiting_login_otp"] = False
        st["awaiting_login_password"] = False
        WAIT_COND.notify_all()
        return had_job


def _join_cancelled_login_job(chat_id: int, timeout: float = 2.5) -> bool:
    with STATE_LOCK:
        th = LOGIN_JOBS.get(chat_id)
    if th is None or not th.is_alive():
        return True
    if th is threading.current_thread():
        return False
    if not _login_cancelled(chat_id):
        return False
    th.join(timeout=max(0.0, timeout))
    return not th.is_alive()


def busy_job_name(chat_id: int) -> Optional[str]:
    with STATE_LOCK:
        checks = (
            (ACTIVE_JOBS, "إنشاء الحساب"),
            (CHANGE_PHONE_JOBS, "تغيير الرقم"),
            (PASSWORD_JOBS, "كلمة المرور"),
            (PIN_JOBS, "تعديل PIN"),
            (LOGIN_JOBS, "تسجيل الدخول"),
        )
        for jobs, label in checks:
            t = jobs.get(chat_id)
            if t is not None and t.is_alive():
                return label
    return None



# ---------------- Proxy manager ----------------

PROXY_LOCK = threading.RLock()
PROXY_RELAY_SERVER = None
PROXY_RELAY_THREAD = None
PROXY_RELAY_FINGERPRINT = None


def _default_proxy_config() -> dict:
    return {"enabled": False, "active_id": None, "items": {}}


def _atomic_proxy_write(obj: dict) -> None:
    tmp = PROXIES_FILE.with_suffix('.json.tmp')
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2), encoding='utf-8')
    try:
        os.chmod(tmp, 0o600)
    except Exception:
        pass
    tmp.replace(PROXIES_FILE)
    try:
        os.chmod(PROXIES_FILE, 0o600)
    except Exception:
        pass


def load_proxy_config() -> dict:
    with PROXY_LOCK:
        cfg = _default_proxy_config()
        if PROXIES_FILE.exists():
            try:
                raw = json.loads(PROXIES_FILE.read_text(encoding='utf-8'))
                if isinstance(raw, dict):
                    cfg.update({k: raw.get(k, cfg[k]) for k in cfg})
            except Exception:
                pass
        if not isinstance(cfg.get('items'), dict):
            cfg['items'] = {}
        # Optional first-boot import from Railway/Termux env without hardcoding secrets in source.
        env_proxy = (os.environ.get('DEFAULT_PROXY') or '').strip()
        if env_proxy and not cfg['items']:
            try:
                p = parse_proxy_string(env_proxy)
                pid = 'px_' + secrets.token_hex(4)
                p['id'] = pid
                cfg['items'][pid] = p
                cfg['active_id'] = pid
                cfg['enabled'] = True
                _atomic_proxy_write(cfg)
            except Exception:
                pass
        return cfg


def save_proxy_config(cfg: dict) -> None:
    with PROXY_LOCK:
        _atomic_proxy_write(cfg)
        _stop_proxy_relay_locked()


def parse_proxy_string(value: str) -> dict:
    value = (value or '').strip()
    if not value:
        raise RuntimeError('البروكسي فارغ')
    # Supported: host:port:user:pass and http://user:pass@host:port
    if '://' in value:
        u = urlparse(value)
        if not u.hostname or not u.port:
            raise RuntimeError('صيغة البروكسي غير صحيحة')
        user = u.username or ''
        password = u.password or ''
        host = u.hostname
        port = int(u.port)
    else:
        parts = value.split(':', 3)
        if len(parts) != 4:
            raise RuntimeError('استخدم الصيغة host:port:user:pass')
        host, port_s, user, password = [x.strip() for x in parts]
        if not host or not port_s.isdigit():
            raise RuntimeError('host أو port غير صحيح')
        port = int(port_s)
    if port < 1 or port > 65535:
        raise RuntimeError('port خارج النطاق')
    if not user or not password:
        raise RuntimeError('اسم المستخدم أو كلمة مرور البروكسي ناقصة')
    return {"host": host, "port": port, "username": user, "password": password, "created_at": time.time()}


def proxy_mask(p: Optional[dict]) -> str:
    if not p:
        return 'غير مضاف'
    return f"{p.get('host','?')}:{p.get('port','?')}"


def scrub_sensitive_text(value: str) -> str:
    text = str(value or '')
    try:
        cfg = load_proxy_config()
        for p in (cfg.get('items') or {}).values():
            if not isinstance(p, dict):
                continue
            for secret in (p.get('password'), proxy_url(p)):
                if secret:
                    text = text.replace(str(secret), '<redacted>')
    except Exception:
        pass
    return text


def active_proxy(proxy_id: Optional[str] = None, require_enabled: bool = True) -> tuple[Optional[str], Optional[dict]]:
    cfg = load_proxy_config()
    if require_enabled and not cfg.get('enabled'):
        return None, None
    items = cfg.get('items') or {}
    pid = proxy_id if proxy_id in items else cfg.get('active_id')
    p = items.get(pid) if pid else None
    if not isinstance(p, dict):
        return None, None
    return str(pid), p


def proxy_url(p: dict) -> str:
    user = quote(str(p.get('username') or ''), safe='')
    password = quote(str(p.get('password') or ''), safe='')
    return f"http://{user}:{password}@{p['host']}:{int(p['port'])}"


def apply_proxy_to_session(session: requests.Session, proxy_id: Optional[str] = None) -> Optional[str]:
    session.trust_env = False
    session.proxies.clear()
    pid, p = active_proxy(proxy_id=proxy_id, require_enabled=True)
    if p:
        url = proxy_url(p)
        session.proxies.update({'http': url, 'https': url})
    return pid


def apply_saved_proxy_temporarily(session: requests.Session, proxy_id: Optional[str]) -> Optional[str]:
    """Use a saved proxy for this session only, ignoring the global ON/OFF toggle.

    This is intentionally used by the existing-account login flow so the proxy can
    be OFF for normal operation while still protecting the short authentication
    handshake. It does not change the global proxy configuration.
    """
    session.trust_env = False
    session.proxies.clear()
    pid, p = active_proxy(proxy_id=proxy_id, require_enabled=False)
    if p:
        url = proxy_url(p)
        session.proxies.update({'http': url, 'https': url})
        return pid
    return None


class _ProxyRelayHandler(socketserver.BaseRequestHandler):
    timeout = 30

    def _read_headers(self) -> bytes:
        data = b''
        while b'\r\n\r\n' not in data and len(data) < 131072:
            try:
                chunk = self.request.recv(8192)
            except (ConnectionResetError, ConnectionAbortedError, TimeoutError, OSError):
                return b''
            if not chunk:
                break
            data += chunk
        return data

    @staticmethod
    def _tunnel(a, b):
        """Bidirectional relay that treats normal peer disconnects as a clean exit.

        Chromium/proxy peers can close either side while a CONNECT tunnel is
        being established.  The previous implementation let recv()/sendall()
        propagate ConnectionResetError/ BrokenPipeError into socketserver,
        producing a traceback and making the request look like a server crash.
        """
        sockets = [a, b]
        for sock in sockets:
            try:
                sock.settimeout(60)
            except OSError:
                pass

        while True:
            try:
                readable, _, _ = select.select(sockets, [], [], 60)
            except (OSError, ValueError):
                return
            if not readable:
                return

            for src in readable:
                dst = b if src is a else a
                try:
                    chunk = src.recv(65536)
                    if not chunk:
                        return
                    dst.sendall(chunk)
                except (
                    ConnectionResetError,
                    ConnectionAbortedError,
                    BrokenPipeError,
                    ConnectionError,
                    TimeoutError,
                    OSError,
                ):
                    return

    def handle(self):
        upstream = getattr(self.server, 'upstream', None)
        if not upstream:
            return
        first = self._read_headers()
        if not first:
            return
        line = first.split(b'\r\n', 1)[0].decode('latin1', 'replace')
        parts = line.split(' ')
        if len(parts) < 3:
            return
        method, target = parts[0].upper(), parts[1]
        auth = base64.b64encode(f"{upstream['username']}:{upstream['password']}".encode()).decode()
        try:
            remote = socket.create_connection(
                (str(upstream['host']), int(upstream['port'])),
                timeout=20,
            )
            remote.settimeout(60)
            try:
                remote.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
            except OSError:
                pass
        except (OSError, TimeoutError, ConnectionError):
            return

        try:
            if method == 'CONNECT':
                req = (
                    f"CONNECT {target} HTTP/1.1\r\n"
                    f"Host: {target}\r\n"
                    f"Proxy-Authorization: Basic {auth}\r\n"
                    "Proxy-Connection: Keep-Alive\r\n\r\n"
                ).encode('latin1')
                remote.sendall(req)
                resp = b''
                while b'\r\n\r\n' not in resp and len(resp) < 65536:
                    c = remote.recv(8192)
                    if not c:
                        break
                    resp += c
                try:
                    self.request.sendall(resp)
                except (ConnectionResetError, ConnectionAbortedError, BrokenPipeError, ConnectionError, OSError):
                    return
                status_line = resp.split(b'\r\n', 1)[0] if resp else b''
                if b' 200 ' not in status_line:
                    return
                self._tunnel(self.request, remote)
            else:
                head, sep, tail = first.partition(b'\r\n\r\n')
                lines = head.split(b'\r\n')
                filtered = [lines[0]] + [x for x in lines[1:] if not x.lower().startswith(b'proxy-authorization:')]
                filtered.append(f"Proxy-Authorization: Basic {auth}".encode('latin1'))
                try:
                    remote.sendall(b'\r\n'.join(filtered) + b'\r\n\r\n' + tail)
                except (ConnectionResetError, ConnectionAbortedError, BrokenPipeError, ConnectionError, OSError):
                    return
                self._tunnel(self.request, remote)
        finally:
            try:
                remote.close()
            except Exception:
                pass


class _ThreadingProxyRelay(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


def _stop_proxy_relay_locked() -> None:
    global PROXY_RELAY_SERVER, PROXY_RELAY_THREAD, PROXY_RELAY_FINGERPRINT
    srv = PROXY_RELAY_SERVER
    PROXY_RELAY_SERVER = None
    PROXY_RELAY_THREAD = None
    PROXY_RELAY_FINGERPRINT = None
    if srv is not None:
        try:
            srv.shutdown()
            srv.server_close()
        except Exception:
            pass


def chrome_proxy_server(proxy_id: Optional[str] = None, *, require_enabled: bool = True) -> Optional[str]:
    global PROXY_RELAY_SERVER, PROXY_RELAY_THREAD, PROXY_RELAY_FINGERPRINT
    pid, p = active_proxy(proxy_id=proxy_id, require_enabled=require_enabled)
    if not p:
        return None
    fp = (pid, p.get('host'), int(p.get('port')), p.get('username'), p.get('password'))
    with PROXY_LOCK:
        if PROXY_RELAY_SERVER is not None and PROXY_RELAY_FINGERPRINT == fp:
            host, port = PROXY_RELAY_SERVER.server_address
            return f"http://127.0.0.1:{port}"
        _stop_proxy_relay_locked()
        srv = _ThreadingProxyRelay(('127.0.0.1', 0), _ProxyRelayHandler)
        srv.upstream = dict(p)
        th = threading.Thread(target=srv.serve_forever, daemon=True)
        th.start()
        PROXY_RELAY_SERVER = srv
        PROXY_RELAY_THREAD = th
        PROXY_RELAY_FINGERPRINT = fp
        return f"http://127.0.0.1:{srv.server_address[1]}"


def test_proxy(proxy_id: Optional[str] = None) -> dict:
    pid, p = active_proxy(proxy_id=proxy_id, require_enabled=False)
    if not p:
        raise RuntimeError('ماكو بروكسي مختار')
    ses = requests.Session()
    ses.trust_env = False
    u = proxy_url(p)
    ses.proxies.update({'http': u, 'https': u})
    result = {'proxy_id': pid, 'proxy': proxy_mask(p), 'ip': None, 'netflix_status': None}
    try:
        r = ses.get('https://api.ipify.org?format=json', timeout=20)
        if r.ok:
            try:
                result['ip'] = str(r.json().get('ip') or '')
            except Exception:
                result['ip'] = (r.text or '').strip()[:80]
    except Exception:
        pass
    r2 = ses.get(f'{NETFLIX}/robots.txt', timeout=25, allow_redirects=True)
    result['netflix_status'] = int(r2.status_code)
    return result


# ---------------- Telegram ----------------

def tg_call(method: str, data: Optional[dict] = None, files: Optional[dict] = None, timeout: int = 45):
    r = TG.post(f"{TG_BASE}/{method}", data=data or {}, files=files, timeout=timeout)
    r.raise_for_status()
    obj = r.json()
    if not obj.get("ok"):
        raise RuntimeError(f"Telegram API error: {obj}")
    return obj.get("result")


def send_message(chat_id: int, text: str, keyboard: bool = False) -> None:
    payload: dict[str, str] = {
        "chat_id": str(chat_id),
        "text": text,
        "disable_web_page_preview": "true",
    }
    if keyboard:
        payload["reply_markup"] = json.dumps({
            "keyboard": [
                [{"text": "إنشاء حساب"}, {"text": "تسجيل دخول"}],
                [{"text": "📂 حساباتي"}, {"text": "🌐 البروكسي"}],
                [{"text": "🧹 تنضيف الجلسات"}, {"text": "❌ إلغاء"}],
            ],
            "resize_keyboard": True,
            "is_persistent": True,
        }, ensure_ascii=False)
    tg_call("sendMessage", payload)


def send_document(chat_id: int, path: str, caption: str = "") -> None:
    try:
        with open(path, "rb") as fh:
            tg_call("sendDocument", {"chat_id": str(chat_id), "caption": caption[:1000]}, {"document": fh}, timeout=90)
    except Exception as exc:
        send_message(chat_id, f"[!] تعذر إرسال ملف التشخيص: {exc}")


def delete_telegram_message(chat_id: int, message_id: int) -> None:
    """Best-effort deletion for sensitive password/OTP messages in the private bot chat."""
    try:
        tg_call("deleteMessage", {"chat_id": str(chat_id), "message_id": str(message_id)})
    except Exception:
        pass


def load_owner() -> Optional[int]:
    try:
        return int(json.loads(OWNER_FILE.read_text(encoding="utf-8")).get("owner_id"))
    except Exception:
        return None


def save_owner(uid: int) -> None:
    OWNER_FILE.write_text(json.dumps({"owner_id": uid}), encoding="utf-8")
    try:
        os.chmod(OWNER_FILE, 0o600)
    except Exception:
        pass


def ensure_owner(uid: int) -> bool:
    owner = load_owner()
    if owner is None:
        save_owner(uid)
        return True
    return owner == uid


# ---------------- Helpers ----------------

def deep_walk(obj: Any):
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from deep_walk(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from deep_walk(v)


def nested_get(obj: Any, *keys: str):
    cur = obj
    for k in keys:
        if not isinstance(cur, dict):
            return None
        cur = cur.get(k)
    return cur


def find_screen_by_logging(screens: list[dict], logging_name: str) -> Optional[dict]:
    for s in screens:
        if isinstance(s, dict) and str(s.get("loggingViewName") or "").lower() == logging_name.lower():
            return s
    return None


def screen_contains_type(screen: dict, typename: str) -> bool:
    return any(d.get("__typename") == typename or d.get("componentType") == typename for d in deep_walk(screen))


def find_node(screen: dict, *, test_id: Optional[str] = None, logging_view: Optional[str] = None,
              label: Optional[str] = None, typename: Optional[str] = None) -> Optional[dict]:
    for d in deep_walk(screen):
        if test_id is not None and str(d.get("testId") or "").lower() != test_id.lower():
            continue
        if logging_view is not None and str(d.get("loggingViewName") or "").lower() != logging_view.lower():
            continue
        if typename is not None and d.get("__typename") != typename and d.get("componentType") != typename:
            continue
        if label is not None:
            lbl = nested_get(d, "label", "value")
            if str(lbl or "").lower() != label.lower():
                continue
        return d
    return None


def action_server_update(node: dict) -> Optional[str]:
    on_press = node.get("onPress") if isinstance(node, dict) else None
    if not on_press:
        return None
    # Prefer the actual request-screen-update effect.
    candidates = []
    for d in deep_walk(on_press):
        ssu = d.get("serverScreenUpdate")
        if isinstance(ssu, str) and ssu:
            score = 0
            if d.get("effectType") == "CLCSRequestScreenUpdate" or d.get("__typename") == "CLCSRequestScreenUpdate":
                score += 10
            if d.get("loggingAction") == "Submitted":
                score += 5
            candidates.append((score, ssu))
    if not candidates:
        return None
    candidates.sort(key=lambda x: x[0], reverse=True)
    return candidates[0][1]


def extract_screen(resp: dict) -> Optional[dict]:
    # CLCSWebInitSignup
    s = nested_get(resp, "data", "clcsWebInitSignup", "screen")
    if isinstance(s, dict):
        return s
    # CLCSScreenUpdate transition
    s = nested_get(resp, "data", "result", "screen")
    if isinstance(s, dict):
        return s
    return None


def extract_preload_screens(resp: dict) -> list[dict]:
    v = nested_get(resp, "data", "clcsPreloadScreens")
    return [x for x in (v or []) if isinstance(x, dict)]


def extract_plan_value(screen: dict) -> str:
    node = find_node(screen, typename="CLCSPlanSelection")
    if node:
        v = nested_get(node, "planField", "initialStringValue")
        if isinstance(v, str) and v:
            return v
        v = nested_get(node, "planField", "initialSensitiveValue", "value")
        if isinstance(v, str) and v:
            return v
    # Keep the validated trace's selected value as a fallback only.
    return "3108"


def extract_text_values(obj: Any) -> list[str]:
    out: list[str] = []
    for d in deep_walk(obj):
        for key in ("value", "loggingViewName", "testId", "screenName"):
            v = d.get(key)
            if isinstance(v, str):
                out.append(v)
    return out


def looks_like_phone_entry(screen: dict) -> bool:
    if screen_contains_type(screen, "CLCSPaymentFormPhoneEntry") or screen_contains_type(screen, "CLCSPhoneInput"):
        return True
    vals = "\n".join(extract_text_values(screen)).lower()
    return any(x in vals for x in (
        "verify phone number", "mobile number", "phone number", "enter_dcb", "paymentdcb"
    ))


def looks_like_payment_otp(screen: dict) -> bool:
    if screen_contains_type(screen, "CLCSPinEntry"):
        return True
    vals = "\n".join(extract_text_values(screen)).lower()
    return any(x in vals for x in (
        "otp", "verification code", "enter code", "security code", "mfa", "one-time"
    ))


def extract_poll_update(resp: dict) -> tuple[Optional[str], int]:
    for d in deep_walk(resp):
        if d.get("__typename") == "CLCSPollForScreenUpdate" or d.get("effectType") == "CLCSPollForScreenUpdate":
            ssu = d.get("serverScreenUpdate")
            if isinstance(ssu, str) and ssu:
                try:
                    interval = int(d.get("intervalMs") or 1000)
                except Exception:
                    interval = 1000
                return ssu, max(250, min(interval, 3000))
    return None, 1000


def normalize_iq_phone(text: str) -> Optional[str]:
    digits = re.sub(r"\D+", "", text or "")
    if digits.startswith("00964"):
        digits = digits[2:]
    if digits.startswith("0") and len(digits) == 11:
        digits = "964" + digits[1:]
    if digits.startswith("964") and len(digits) == 13:
        return digits
    return None


def cache_account_password(account_id: str, password: str) -> None:
    password = validate_account_password(password)
    with STATE_LOCK:
        EPHEMERAL_PASSWORDS[account_id] = (password, time.time() + PASSWORD_CACHE_TTL)


def get_cached_account_password(account_id: str) -> Optional[str]:
    with STATE_LOCK:
        item = EPHEMERAL_PASSWORDS.get(account_id)
        if not item:
            return None
        password, expires = item
        if time.time() >= expires:
            EPHEMERAL_PASSWORDS.pop(account_id, None)
            return None
        return password


def clear_cached_account_password(account_id: str) -> None:
    with STATE_LOCK:
        EPHEMERAL_PASSWORDS.pop(account_id, None)


def validate_account_password(value: str) -> str:
    value = str(value or "")
    if value != value.strip():
        raise RuntimeError("كلمة المرور ما لازم تبدأ أو تنتهي بمسافة")
    if len(value) < 4 or len(value) > 60:
        raise RuntimeError("كلمة المرور لازم تكون بين 4 و60 حرف")
    if "\n" in value or "\r" in value:
        raise RuntimeError("كلمة المرور غير صالحة")
    return value


def wait_for_secret(chat_id: int, account_id: str, kind: str, prompt: str,
                    timeout: int = 300, back_callback: Optional[str] = None) -> Optional[str]:
    """Wait for a sensitive text value without persisting it to disk.

    The Telegram message is deleted best-effort as soon as it is received.
    """
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_secret"] = True
        st["secret_kind"] = kind
        st["secret_account"] = account_id
        st.pop("secret_value", None)
    rows = [[("❌ إلغاء", f"cancelsecret:{account_id}")]]
    send_inline(chat_id, prompt, rows)
    deadline = time.time() + timeout
    try:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            while time.time() < deadline:
                value = st.pop("secret_value", None)
                if value is not None:
                    st["awaiting_secret"] = False
                    st.pop("secret_kind", None)
                    st.pop("secret_account", None)
                    if value == "__CANCEL__":
                        return None
                    return str(value)
                WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
            st["awaiting_secret"] = False
            st.pop("secret_kind", None)
            st.pop("secret_account", None)
            return None
    finally:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            if st.get("secret_account") == account_id:
                st["awaiting_secret"] = False
                st.pop("secret_kind", None)
                st.pop("secret_account", None)
                st.pop("secret_value", None)


# ---------------- Owner-only Netflix login via Telegram ----------------

def validate_login_email(value: str) -> str:
    email = str(value or "").strip()
    if len(email) < 3 or len(email) > 254 or not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email):
        raise RuntimeError("الإيميل غير صالح")
    return email


def wait_for_login_email(chat_id: int, timeout: int = 300) -> Optional[str]:
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_login_email"] = True
        st.pop("login_email_value", None)
    send_inline(
        chat_id,
        "📧 دز إيميل حساب Netflix اللي تريد تسجل دخوله.\n\n"
        "🌐 تسجيل الدخول يستخدم البروكسي المحفوظ مؤقتاً فقط، وبعد نجاح الدخول ينفصل عن الحساب وتكمل الإدارة على Railway مباشر.\n"
        "الرسالة تنحذف من تيليجرام قدر الإمكان، وما أخزن الإيميل داخل ملف الجلسة.",
        [[("❌ إلغاء", "login_cancel")]],
    )
    deadline = time.time() + timeout
    try:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            while time.time() < deadline:
                if _login_cancelled(chat_id):
                    return None
                value = st.pop("login_email_value", None)
                if value is not None:
                    st["awaiting_login_email"] = False
                    if value == "__CANCEL__":
                        return None
                    return str(value)
                WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
            return None
    finally:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            st["awaiting_login_email"] = False
            st.pop("login_email_value", None)


def wait_for_login_otp_or_password(chat_id: int, timeout: int = 300) -> Optional[str]:
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_login_otp"] = True
        st.pop("login_otp_value", None)
        st.pop("login_method_value", None)
    send_inline(
        chat_id,
        "📩 Netflix طلب رمز تسجيل الدخول. دز رمز OTP هنا.\n\n"
        "إذا تريد تدخل بكلمة المرور بدل الرمز، اضغط الزر أدناه.",
        [[("🔑 استخدام كلمة المرور بدلاً من ذلك", "login_use_password")], [("❌ إلغاء", "login_cancel")]],
    )
    deadline = time.time() + timeout
    try:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            while time.time() < deadline:
                if _login_cancelled(chat_id):
                    return None
                method = st.pop("login_method_value", None)
                if method == "PASSWORD":
                    st["awaiting_login_otp"] = False
                    return "__PASSWORD__"
                if method == "__CANCEL__":
                    return None
                value = st.pop("login_otp_value", None)
                if value is not None:
                    st["awaiting_login_otp"] = False
                    if value == "__CANCEL__":
                        return None
                    return str(value)
                WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
            return None
    finally:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            st["awaiting_login_otp"] = False
            st.pop("login_otp_value", None)
            st.pop("login_method_value", None)


def wait_for_login_password(chat_id: int, timeout: int = 300) -> Optional[str]:
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_login_password"] = True
        st.pop("login_password_value", None)
    send_inline(
        chat_id,
        "🔑 دز كلمة مرور Netflix الحالية.\n\n"
        "تُستخدم بالذاكرة فقط، وتنحذف رسالتها من تيليجرام قدر الإمكان، وما تنخزن داخل accounts.json.",
        [[("❌ إلغاء", "login_cancel")]],
    )
    deadline = time.time() + timeout
    try:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            while time.time() < deadline:
                if _login_cancelled(chat_id):
                    return None
                value = st.pop("login_password_value", None)
                if value is not None:
                    st["awaiting_login_password"] = False
                    if value == "__CANCEL__":
                        return None
                    return str(value)
                WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
            return None
    finally:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            st["awaiting_login_password"] = False
            st.pop("login_password_value", None)


# ---------------- Owner-only payment OTP autofill ----------------

_OTP_DIGIT_TRANSLATION = str.maketrans(
    "٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹",
    "01234567890123456789",
)


def validate_payment_otp(value: str) -> str:
    """Validate and normalize a carrier-billing OTP without storing it persistently.

    Python's ``\\d`` accepts Arabic-Indic/Persian digits.  Netflix's DCB endpoint is much
    more reliable with ASCII digits, so normalize ٠١٢٣ / ۰۱۲۳ before submission and then
    validate strictly as [0-9].
    """
    otp = re.sub(r"\s+", "", str(value or "")).translate(_OTP_DIGIT_TRANSLATION)
    if not re.fullmatch(r"[0-9]{4,8}", otp):
        raise RuntimeError("رمز OTP لازم يكون من 4 إلى 8 أرقام")
    return otp


def wait_for_payment_otp(chat_id: int, account_id: str, timeout: int = 300) -> Optional[str]:
    """Wait for an OTP from the owner chat, only for browser autofill.

    The OTP is kept in CHAT_STATE only long enough to transfer it to the live browser field.
    It is never written to accounts.json/debug files and this function never submits the
    Start Membership/payment action.
    """
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_payment_otp"] = True
        st["otp_account"] = account_id
        st.pop("payment_otp_value", None)
    send_inline(
        chat_id,
        "📩 وصلنا تلقائياً لمرحلة OTP. دز كود Netflix اللي وصلك بالـSMS هسه.\n\n"
        "راح أعبّيه مباشرة داخل خانة OTP بنفس جلسة Netflix، بدون ما تحتاج تضغط زر تعبئة OTP.\n"
        "✅ بعد تعبئة OTP راح يظهر تأكيد Start Membership داخل Telegram: موافق / رفض.",
        [[("❌ إلغاء OTP", f"cancelotp:{account_id}")]],
    )
    deadline = time.time() + timeout
    try:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            while time.time() < deadline:
                if _job_cancelled(chat_id) or _account_deleted(account_id):
                    st["awaiting_payment_otp"] = False
                    st.pop("otp_account", None)
                    return None
                value = st.pop("payment_otp_value", None)
                if value is not None:
                    st["awaiting_payment_otp"] = False
                    st.pop("otp_account", None)
                    if value == "__CANCEL__":
                        return None
                    return str(value)
                WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
            st["awaiting_payment_otp"] = False
            st.pop("otp_account", None)
            return None
    finally:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            if st.get("otp_account") == account_id:
                st["awaiting_payment_otp"] = False
                st.pop("otp_account", None)
                st.pop("payment_otp_value", None)


def wait_for_membership_confirmation(chat_id: int, account_id: str, timeout: int = 300) -> Optional[bool]:
    """Ask the owner for an explicit Start Membership decision.

    Returns True for approval, False for rejection, and None for timeout/cancel.
    The decision is ephemeral and scoped to the active account/job only.
    """
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_membership_confirmation"] = True
        st["membership_confirm_account"] = account_id
        st.pop("membership_confirm_value", None)

    send_inline(
        chat_id,
        "▶️ Start Membership\n\n"
        "هل أنت موافق على بدء العضوية الآن؟\n\n"
        "إذا ضغطت موافق، البوت راح ينفذ Start Membership داخل نفس جلسة Netflix ويكمل الخطوات.\n"
        "إذا ضغطت رفض، ما راح يبدأ الاشتراك.",
        [[("✅ موافق", f"membership_yes:{account_id}"), ("❌ رفض", f"membership_no:{account_id}")]],
    )

    deadline = time.time() + timeout
    try:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            while time.time() < deadline:
                if _job_cancelled(chat_id) or _account_deleted(account_id):
                    st["awaiting_membership_confirmation"] = False
                    st.pop("membership_confirm_account", None)
                    return None
                value = st.pop("membership_confirm_value", None)
                if value is not None:
                    st["awaiting_membership_confirmation"] = False
                    st.pop("membership_confirm_account", None)
                    if value == "YES":
                        return True
                    if value == "NO":
                        return False
                    return None
                WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
            st["awaiting_membership_confirmation"] = False
            st.pop("membership_confirm_account", None)
            return None
    finally:
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            if st.get("membership_confirm_account") == account_id:
                st["awaiting_membership_confirmation"] = False
                st.pop("membership_confirm_account", None)
                st.pop("membership_confirm_value", None)


def click_start_membership_after_confirmation(driver, chat_id: int, account_id: str) -> bool:
    """Require explicit Telegram approval, then click the visible Start Membership CTA."""
    approved = wait_for_membership_confirmation(chat_id, account_id, timeout=300)
    if approved is False:
        send_message(chat_id, "❌ تم رفض Start Membership. ما تم بدء العضوية أو إرسال تأكيد الدفع.")
        return False
    if approved is None:
        send_message(chat_id, "⏳ انتهى/أُلغي انتظار الموافقة. ما تم بدء العضوية.")
        return False

    clicked = _click_button_like(driver, (
        "start membership", "start your membership", "start my membership",
        "ابدأ العضوية", "بدء العضوية", "ابدأ اشتراكك", "بدء الاشتراك",
    ))
    if not clicked:
        raise RuntimeError("تمت الموافقة، لكن زر Start Membership مو ظاهر أو مو قابل للضغط")

    send_message(chat_id, "✅ تمت الموافقة. ضغطت Start Membership داخل نفس جلسة Netflix، وجاري انتظار نتيجة التفعيل...")
    return True


# ---------------- Direct Telegram OTP -> approved Start Membership ----------------

def _all_response_text_lower(obj: Any) -> str:
    """Flatten response strings for classification only; nothing is persisted."""
    vals: list[str] = []
    for d in deep_walk(obj):
        for v in d.values():
            if isinstance(v, str):
                vals.append(v)
    return "\n".join(vals).lower()


def _membership_action_server_update(screen: dict) -> str:
    """Find the approved Start Membership CLCS action from the live OTP screen.

    Netflix localizes the visible CTA.  V22.10 only scored the English text, so an
    ar-IQ OTP screen could expose several onPress actions (start/resend/change method)
    while none scored high enough.  Keep the selection conservative: recognize both
    English and Arabic membership CTAs, reward the CLCS Submitted action, and heavily
    penalize resend/change-payment controls.  If the result is still ambiguous, fail
    closed instead of guessing which action bills the account.
    """
    candidates: list[tuple[int, str]] = []
    all_updates: list[str] = []

    for d in deep_walk(screen):
        if not isinstance(d, dict) or not d.get("onPress"):
            continue
        update = action_server_update(d)
        if not update:
            continue
        all_updates.append(update)

        hay = " ".join(extract_text_values(d)).lower()
        label = str(nested_get(d, "label", "value") or "").lower()

        meta_vals: list[str] = []
        for part in deep_walk(d.get("onPress")):
            if not isinstance(part, dict):
                continue
            for key in (
                "loggingAction", "action", "eventName", "loggingViewName",
                "testId", "name", "effectType", "__typename",
            ):
                value = part.get(key)
                if isinstance(value, str) and value:
                    meta_vals.append(value)
        meta = " ".join(meta_vals).lower()
        joined = f"{hay} {label} {meta}"

        score = 0

        # English variants / internal identifiers.
        if "start membership" in joined:
            score += 240
        if "startmembership" in joined:
            score += 220
        if "start" in joined and "membership" in joined:
            score += 170
        if "activate" in joined and "membership" in joined:
            score += 170

        # Arabic ar-IQ variants used by localized signup screens.
        ar_membership = any(x in joined for x in (
            "عضوية", "العضوية", "عضويتك", "اشتراك", "الاشتراك",
        ))
        ar_start = any(x in joined for x in (
            "بدء", "البدء", "ابدأ", "إبدأ", "ابدء", "تفعيل", "فعّل", "فعل",
        ))
        if ar_membership and ar_start:
            score += 240
        if any(x in joined for x in (
            "بدء العضوية", "ابدأ العضوية", "ابدأ عضويتك", "تفعيل العضوية",
            "بدء الاشتراك", "ابدأ الاشتراك", "تفعيل الاشتراك",
        )):
            score += 120

        # The billing CTA is the submitted CLCS form action on the OTP screen.
        if "submitted" in meta:
            score += 55
        if any(x in joined for x in ("otp", "mfa", "verification code", "رمز التحقق")) and "submitted" in meta:
            score += 25
        if "cta" in joined:
            score += 5

        # Do not confuse secondary OTP/payment links with Start Membership.
        if any(x in joined for x in (
            "text me again", "resend", "send again", "different payment",
            "change payment", "use a different payment method",
            "إعادة إرسال", "اعادة ارسال", "إرسال مجدد", "ارسال مجدد",
            "إرسال الرمز مرة أخرى", "طريقة دفع مختلفة", "تغيير طريقة الدفع",
            "استخدام طريقة دفع مختلفة",
        )):
            score -= 300
        if any(x in joined for x in ("cancel", "back", "إلغاء", "رجوع")):
            score -= 220

        candidates.append((score, update))

    candidates.sort(key=lambda x: x[0], reverse=True)
    if candidates and candidates[0][0] >= 120:
        # Avoid a tie between two different high-confidence billing actions.
        if len(candidates) == 1 or candidates[0][0] > candidates[1][0] or candidates[0][1] == candidates[1][1]:
            return candidates[0][1]

    unique: list[str] = []
    for u in all_updates:
        if u not in unique:
            unique.append(u)
    if len(unique) == 1:
        return unique[0]

    raise RuntimeError(
        "ما قدرت أحدد Start Membership action من شاشة OTP الحالية بأمان. "
        "الشاشة غالباً مترجمة/متغيرة وفيها أكثر من إجراء، لذلك ما راح أخمّن زر التفعيل."
    )


def _otp_error_phrase_kind(text: str) -> Optional[str]:
    text = str(text or "").lower()
    if any(x in text for x in (
        "incorrect code", "invalid code", "code is incorrect", "code isn't correct",
        "code is not correct", "wrong code", "رمز غير صحيح", "الكود غير صحيح",
        "الرمز غير صحيح",
    )):
        return "INVALID_OTP"
    if any(x in text for x in (
        "code has expired", "code expired", "expired code", "request a new code",
        "انتهت صلاحية الرمز", "انتهت صلاحية الكود",
    )):
        return "OTP_EXPIRED"
    return None


def _explicit_otp_error_kind(body: dict) -> Optional[str]:
    """Return INVALID/EXPIRED only when the response contains real error evidence.

    Older V22 builds flattened *every* string in the CLCS response.  Netflix responses can
    contain hidden/preloaded/generic copy such as "invalid code" even when that text is not
    the active field error.  That made the bot claim "Netflix says your code is wrong" without
    enough evidence.  V22.14 only trusts top-level GraphQL errors or error/validation-shaped
    subtrees.  Ambiguous OTP screens are reported honestly as unconfirmed instead.
    """
    if not isinstance(body, dict):
        return None

    # Top-level GraphQL errors are authoritative error containers.
    top_errors = body.get("errors")
    if isinstance(top_errors, list):
        for err in top_errors:
            if isinstance(err, dict):
                kind = _otp_error_phrase_kind(_all_response_text_lower(err))
                if kind:
                    return kind
            elif isinstance(err, str):
                kind = _otp_error_phrase_kind(err)
                if kind:
                    return kind

    # Inline CLCS validation/error nodes.  Require an error-shaped key/type before trusting text.
    for d in deep_walk(body):
        if not isinstance(d, dict):
            continue
        keys = " ".join(str(k).lower() for k in d.keys())
        typename = " ".join(str(d.get(k) or "").lower() for k in (
            "__typename", "componentType", "effectType", "type", "name", "testId"
        ))
        errorish = (
            any(x in keys for x in ("error", "validation", "invalid", "feedback"))
            or any(x in typename for x in ("error", "validation", "invalid"))
            or d.get("isValid") is False
            or d.get("valid") is False
        )
        if not errorish:
            continue
        local = _all_response_text_lower(d)
        kind = _otp_error_phrase_kind(local)
        if kind:
            return kind
    return None


def _classify_payment_otp_response(body: dict) -> tuple[str, Optional[dict]]:
    screen = extract_screen(body) if isinstance(body, dict) else None

    explicit_otp_error = _explicit_otp_error_kind(body)
    if explicit_otp_error:
        return explicit_otp_error, screen

    # These remain conservative blockers.  They do not make a claim about the OTP itself.
    text = _all_response_text_lower(body)
    if any(x in text for x in (
        "captcha", "verify you are human", "security check", "unusual activity",
        "تحقق من أنك إنسان", "نشاط غير معتاد",
    )):
        return "SECURITY_CHALLENGE", screen
    if any(x in text for x in (
        "too many", "rate limit", "try again later", "محاولات كثيرة", "حاول لاحقاً",
    )):
        return "RATE_LIMIT", screen
    if any(x in text for x in (
        "session expired", "sign in again", "session has expired", "انتهت الجلسة",
    )):
        return "SESSION_EXPIRED", screen

    if screen is not None:
        if looks_like_payment_otp(screen):
            return "OTP_UNCONFIRMED", screen
        return "SCREEN_CHANGED", screen
    if extract_poll_update(body)[0]:
        return "POLL", None
    if isinstance(body, dict) and body.get("errors"):
        return "GRAPHQL_ERROR", None
    return "UNKNOWN", None


def _submit_payment_otp_direct(eng: "NetflixDirect", otp_screen: dict, otp: str) -> tuple[dict, str]:
    """Submit the exact approved OTP+Start Membership CLCS action in the current session."""
    otp = validate_payment_otp(otp)
    state = str(otp_screen.get("serverState") or "")
    if not state:
        raise RuntimeError("شاشة OTP ناقصها serverState")
    update = _membership_action_server_update(otp_screen)
    body = eng.gql(
        "CLCSScreenUpdate",
        {
            "format": "HTML",
            "imageFormat": "PNG",
            "locale": DEFAULT_LOCALE,
            "serverState": state,
            "serverScreenUpdate": update,
            "inputFields": [
                {"name": "mfaCode", "value": {"stringValue": otp}},
            ],
        },
        PQ_SCREEN_UPDATE,
        client_context={"appView": "otpCodeEntry", "action": "Submitted", "appstate": "foreground"},
        referer=f"{NETFLIX}/signup?serverState={quote(state, safe='')}",
        clcs=True,
    )
    return body, state


def _follow_direct_clcs_poll(eng: "NetflixDirect", body: dict, server_state: str,
                             timeout: float = 25.0) -> tuple[dict, Optional[dict]]:
    """Follow CLCSPollForScreenUpdate without resubmitting OTP/payment input."""
    current = body
    deadline = time.time() + timeout
    while time.time() < deadline:
        screen = extract_screen(current)
        if screen is not None:
            return current, screen
        poll_update, interval_ms = extract_poll_update(current)
        if not poll_update:
            return current, None
        time.sleep(interval_ms / 1000.0)
        current = eng.gql(
            "CLCSScreenUpdate",
            {
                "format": "HTML",
                "imageFormat": "PNG",
                "locale": DEFAULT_LOCALE,
                "serverState": server_state,
                "serverScreenUpdate": poll_update,
                "inputFields": [],
            },
            PQ_SCREEN_UPDATE,
            client_context={"appView": "otpCodeEntry", "appstate": "foreground"},
            referer=f"{NETFLIX}/signup?serverState={quote(server_state, safe='')}",
            clcs=True,
        )
    return current, extract_screen(current)


def _finalize_membership_activation(chat_id: int, account_id: str, eng: "NetflixDirect",
                                    membership_status: str, inline_password: bool = True) -> None:
    before = load_accounts().get(account_id, {})
    prior_pstatus = str(before.get("password_status") or "unknown")
    save_engine_account(eng, account_id=account_id, status="active", profiles=before.get("profiles") or [])
    update_account_record(account_id, membership_status=membership_status)
    old_proxy = detach_proxy_after_activation(eng, account_id)
    proxy_note = "\n🌐 تم فصل بروكسي التسجيل عن هذا الحساب؛ العمليات التالية تستخدم اتصال Railway المباشر." if old_proxy else ""
    send_message(
        chat_id,
        f"✅ تم تفعيل العضوية. MembershipStatus={membership_status}\n"
        f"الجلسة انحفظت. هسه نكمل للخطوة التالية.{proxy_note}",
    )

    if prior_pstatus not in {"set", "unknown"}:
        set_account_password_state(account_id, "required")
        if inline_password:
            # We are already inside the owner job thread, so run the existing password
            # workflow inline instead of trying to start a second job that busy_job_name blocks.
            password_job_worker(chat_id, account_id, initial=True)
            return
    show_account_menu(chat_id, account_id)


def direct_payment_otp_membership_flow(chat_id: int, account_id: str,
                                       eng: "NetflixDirect", otp_screen: dict) -> bool:
    """All-bot path: ask OTP -> explicit approval -> CLCS submit -> continue automatically."""
    current_screen = otp_screen
    for attempt in range(1, 6):
        if _job_cancelled(chat_id) or _account_deleted(account_id):
            return False
        otp = wait_for_payment_otp(chat_id, account_id, timeout=300)
        if otp == "__CHANGE_PHONE__":
            with STATE_LOCK:
                CHAT_STATE.setdefault(chat_id, {})["deferred_change_phone"] = account_id
            send_message(chat_id, "📱 تمام. أوقف انتظار الكود الحالي وأنتقل لتغيير رقم الهاتف بنفس الحساب والجلسة المحفوظة...")
            return False
        if otp is None:
            send_message(chat_id, "⏸ تم إلغاء/انتهاء انتظار OTP. ما تم بدء العضوية.")
            show_account_menu(chat_id, account_id)
            return False

        otp_received_at = time.time()
        approved = wait_for_membership_confirmation(chat_id, account_id, timeout=300)
        if approved is False:
            otp = None
            send_message(chat_id, "❌ تم الرفض. تم تجاهل OTP وما تم بدء العضوية.")
            show_account_menu(chat_id, account_id)
            return False
        if approved is None:
            otp = None
            send_message(chat_id, "⏳ انتهى انتظار الموافقة. تم تجاهل OTP وما تم بدء العضوية.")
            show_account_menu(chat_id, account_id)
            return False

        # If approval was delayed for several minutes, do not submit a code that may have expired
        # while sitting only in Telegram memory.  Ask for a fresh code instead of blaming the user.
        if time.time() - otp_received_at > 180:
            otp = None
            send_message(chat_id, "⌛ مر وقت طويل بين استلام OTP والموافقة. ما راح أرسل رمز قديم وأعتبره غلط؛ دز أحدث رمز وصلك بعد آخر Verify.")
            continue

        if _job_cancelled(chat_id) or _account_deleted(account_id):
            otp = None
            return False
        send_message(chat_id, "✅ وصلت موافقتك. جاري إرسال OTP وتنفيذ Start Membership بنفس جلسة Netflix الحالية...")
        try:
            body, state = _submit_payment_otp_direct(eng, current_screen, otp)
        finally:
            # Never retain the OTP longer than the request call.
            otp = None

        if _job_cancelled(chat_id) or _account_deleted(account_id):
            return False
        body, next_screen = _follow_direct_clcs_poll(eng, body, state, timeout=25.0)
        if _job_cancelled(chat_id) or _account_deleted(account_id):
            return False
        acct = load_accounts().get(account_id, {})
        save_engine_account(eng, account_id=account_id, status=acct.get("status") or "pending_otp", profiles=acct.get("profiles") or [])

        response_state, parsed_screen = _classify_payment_otp_response(body)
        if parsed_screen is not None:
            next_screen = parsed_screen

        # MembershipStatus is the source of truth.  Do not stop after a single text classifier hit:
        # some CLCS responses carry generic/hidden validation copy while activation is still settling.
        ms = None
        settle_started = time.time()
        settle_deadline = settle_started + 24
        terminal_grace = settle_started + 4
        while time.time() < settle_deadline:
            if _job_cancelled(chat_id) or _account_deleted(account_id):
                return False
            ms = eng.membership_status()
            if is_active_membership(ms):
                _finalize_membership_activation(chat_id, account_id, eng, str(ms), inline_password=True)
                return True
            if (
                response_state in {"INVALID_OTP", "OTP_EXPIRED", "SECURITY_CHALLENGE", "RATE_LIMIT", "SESSION_EXPIRED"}
                and time.time() >= terminal_grace
            ):
                break
            time.sleep(1.0)

        # Keep a sanitized audit breadcrumb.  No OTP/serverState is written by eng.note/safe_summary.
        eng.note(
            "otp_outcome_truth_check",
            classification=response_state,
            membership_status=ms,
            has_screen=bool(next_screen),
            otp_screen=bool(next_screen is not None and looks_like_payment_otp(next_screen)),
        )

        if response_state in {"INVALID_OTP", "OTP_EXPIRED", "OTP_UNCONFIRMED"} or (next_screen is not None and looks_like_payment_otp(next_screen)):
            if next_screen is not None and looks_like_payment_otp(next_screen):
                current_screen = next_screen
            if response_state == "OTP_EXPIRED":
                send_inline(
                    chat_id,
                    "⌛ Netflix رجع خطأ صريح مرتبط بحقل OTP يفيد بأن صلاحية الرمز انتهت، والعضوية ما صارت Active. دز أحدث كود وصلك بعد آخر Verify.",
                    [[("📱 تغيير رقم الهاتف", f"otp_cp:{account_id}")]],
                )
            elif response_state == "INVALID_OTP":
                send_inline(
                    chat_id,
                    "❌ Netflix رجع خطأ تحقق صريح مرتبط بالـOTP، والعضوية بقيت غير فعالة. هذا يثبت أن Netflix لم يقبل هذا الرمز لهذه الجلسة، لكنه لا يثبت أنك كتبته غلط؛ ممكن يكون الرمز تابع لطلب Verify أقدم. دز أحدث كود وصلك بعد آخر Verify.",
                    [[("📱 تغيير رقم الهاتف", f"otp_cp:{account_id}")]],
                )
            else:
                send_inline(
                    chat_id,
                    "⚠️ التفعيل ما تأكد وبقيت شاشة OTP، لكن رد Netflix ما يحتوي دليلاً صريحاً يثبت أن الكود خطأ. لذلك ما راح أقول لك إن الكود غلط. إذا وصلك كود أحدث بعد آخر Verify دزه؛ أو غيّر رقم الهاتف.",
                    [[("📱 تغيير رقم الهاتف", f"otp_cp:{account_id}")]],
                )
            continue

        if response_state == "SECURITY_CHALLENGE":
            send_message(chat_id, "⚠️ Netflix طلب تحققاً أمنياً إضافياً. ما راح أحاول أتجاوزه.")
        elif response_state == "RATE_LIMIT":
            send_message(chat_id, "⏳ Netflix طلب الانتظار بسبب كثرة المحاولات. ما راح أعيد الطلب تلقائياً.")
        elif response_state == "SESSION_EXPIRED":
            send_message(chat_id, "⌛ انتهت جلسة Netflix قبل إكمال التفعيل.")
        else:
            send_message(chat_id, f"⚠️ Netflix ما أكد التفعيل بعد الموافقة. الحالة={response_state} MembershipStatus={ms!r}")

        dbg = eng.write_debug(f"direct_otp_membership_{response_state.lower()}")
        send_document(chat_id, dbg, "V22.14 تشخيص OTP/Start Membership (بدون OTP أو بيانات جلسة حساسة)")
        show_account_menu(chat_id, account_id)
        return False

    send_message(chat_id, "⛔ توقفت بعد 5 محاولات OTP حتى ما تتكرر المحاولات بدون حد.")
    show_account_menu(chat_id, account_id)
    return False


def set_account_password_state(account_id: str, status: str, **extra) -> dict:
    changes = {"password_status": status, **extra}
    return update_account_record(account_id, **changes)


def assert_profile_management_allowed(account_id: str) -> None:
    acct = load_accounts().get(account_id) or {}
    if not acct:
        raise RuntimeError("الحساب المحفوظ غير موجود")
    if str(acct.get("status") or "") != "active":
        raise RuntimeError("الحساب بعده مو Active")
    if str(acct.get("password_status") or "unknown") in {"pending_activation", "required", "failed", "not_set"}:
        raise RuntimeError("لازم تنشئ كلمة مرور الحساب أولاً")


def safe_summary(obj: Any) -> Any:
    """Return a compact, secret-free structure for diagnostics."""
    if isinstance(obj, dict):
        # Netflix CLCS stores secrets as generic value/stringValue fields next to a
        # semantic name (for example name=mfaCode). Redact the whole value branch
        # before the generic recursive walk so OTP can never leak into debug files.
        semantic_name = str(obj.get("name") or "").strip().lower()
        if semantic_name in {"mfacode", "otp", "verificationcode", "securitycode"}:
            redacted = {}
            for k, v in obj.items():
                redacted[k] = v if k == "name" else "<redacted>"
            return redacted
        out = {}
        for k, v in obj.items():
            kl = k.lower()
            if any(x in kl for x in ("cookie", "token", "password", "phone", "email", "otp", "mfacode", "serverstate", "serverscreenupdate", "authorization", "flwssn", "gsid", "proxy")):
                out[k] = "<redacted>"
            elif k in ("componentTree", "preload"):
                # avoid giant reports
                out[k] = "<omitted>"
            else:
                out[k] = safe_summary(v)
        return out
    if isinstance(obj, list):
        return [safe_summary(x) for x in obj[:20]]
    if isinstance(obj, str):
        obj = scrub_sensitive_text(obj)
        if len(obj) > 500:
            return obj[:500] + "..."
        return obj
    return obj


# ---------------- Netflix direct engine ----------------

class NetflixDirect:
    def __init__(self, *, use_signup_proxy: bool = False, proxy_id: Optional[str] = None):
        self.s = requests.Session()
        self.s.trust_env = False
        self.s.proxies.clear()
        # V22.14 policy: proxy is opt-in and reserved for NEW-ACCOUNT SIGNUP only.
        # Login and all post-activation account management stay on direct Railway.
        self.proxy_id = apply_proxy_to_session(self.s, proxy_id) if use_signup_proxy else None
        self.s.headers.update({
            "User-Agent": DEFAULT_UA,
            "Accept-Language": DEFAULT_ACCEPT_LANGUAGE,
            "Accept": "*/*",
        })
        self.app_version = DEFAULT_APP_VERSION
        self.hawkins = DEFAULT_HAWKINS_VERSION
        self.referer = f"{NETFLIX}/"
        self.debug: list[dict] = []

    def note(self, name: str, **meta):
        self.debug.append({"ts": time.time(), "event": name, "meta": safe_summary(meta)})

    def gql(self, operation: str, variables: dict, persisted_id: str,
            client_context: Optional[dict] = None, referer: Optional[str] = None,
            clcs: bool = False) -> dict:
        effective_referer = referer or self.referer
        headers = {
            "content-type": "application/json",
            "Origin": NETFLIX,
            "x-netflix.context.operation-name": operation,
            "x-netflix.context.ui-flavor": "akira",
            "x-netflix.context.locales": DEFAULT_LOCALE_HEADER,
            "x-netflix.context.form-factor": "phone",
            "x-netflix.context.is-inapp-browser": "false",
            "x-netflix.context.app-version": self.app_version,
            "x-netflix.context.hawkins-version": self.hawkins,
            "x-netflix.request.attempt": "1",
            "x-netflix.request.id": secrets.token_hex(16),
            "x-netflix.request.originating.url": effective_referer,
            "x-netflix.request.toplevel.uuid": str(uuid.uuid4()),
            "Referer": effective_referer,
        }
        if client_context is not None:
            headers["x-netflix.request.client.context"] = json.dumps(client_context, separators=(",", ":"))
        if clcs:
            headers["x-netflix.request.clcs.bucket"] = "high"
        payload = {
            "operationName": operation,
            "variables": variables,
            "extensions": {"persistedQuery": {"id": persisted_id, "version": PQ_VERSION}},
        }
        t0 = time.time()
        # Refresh proxy binding before each GraphQL call. Existing accounts keep their pinned proxy when enabled.
        self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
        r = self.s.post(GRAPHQL, headers=headers, json=payload, timeout=30)
        elapsed = round(time.time() - t0, 3)
        try:
            body = r.json()
        except Exception:
            body = {"_non_json": (r.text or "")[:1000]}
        self.note("graphql", operation=operation, status=r.status_code, elapsed=elapsed,
                  variables=variables, response=body)
        r.raise_for_status()
        return body

    def membership_status(self) -> Optional[str]:
        try:
            body = self.gql("MembershipStatus", {}, PQ_MEMBERSHIP,
                            client_context={"appstate": "foreground"}, referer=self.referer)
            return nested_get(body, "data", "growthAccount", "membershipStatus")
        except Exception as exc:
            self.note("membership_error", error=f"{type(exc).__name__}: {exc}")
            return None

    def discover_versions(self, text: str):
        for pat in (r'"appVersion"\s*:\s*"(v[0-9A-Za-z]+)"', r'x-netflix\.context\.app-version[^v]*(v[0-9A-Za-z]+)'):
            m = re.search(pat, text or "", re.I)
            if m:
                self.app_version = m.group(1)
                break
        m = re.search(r'"hawkinsVersion"\s*:\s*"([0-9.]+)"', text or "", re.I)
        if m:
            self.hawkins = m.group(1)

    @staticmethod
    def _decode_jsonish(s: str) -> str:
        s = html_lib.unescape(s)
        try:
            return json.loads('"' + s.replace('"', '\\"') + '"')
        except Exception:
            return s.replace("\\/", "/").replace("\\u002B", "+")

    def extract_bootstrap_state(self, text: str, url: str) -> tuple[Optional[str], Optional[str]]:
        state = None
        update = None
        try:
            q = parse_qs(urlparse(url).query)
            vals = q.get("serverState") or []
            if vals:
                state = vals[0]
        except Exception:
            pass

        patterns_state = [
            r'"serverState"\s*:\s*"([^"<>]{80,})"',
            r'\\"serverState\\"\s*:\s*\\"(.{80,}?)\\"',
            r'serverState=([^&#"\']{80,})',
        ]
        patterns_update = [
            r'"serverScreenUpdate"\s*:\s*"([^"<>]{80,})"',
            r'\\"serverScreenUpdate\\"\s*:\s*\\"(.{80,}?)\\"',
        ]
        if not state:
            for p in patterns_state:
                m = re.search(p, text or "", re.S)
                if m:
                    state = html_lib.unescape(m.group(1))
                    break
        for p in patterns_update:
            m = re.search(p, text or "", re.S)
            if m:
                update = html_lib.unescape(m.group(1))
                break
        return state, update

    def extract_bootstrap_state(self, text: str, url: str) -> tuple[Optional[str], Optional[str]]:
        state = None
        update = None
        try:
            q = parse_qs(urlparse(url).query)
            vals = q.get("serverState") or []
            if vals:
                state = vals[0]
        except Exception:
            pass

        patterns_state = [
            r'"serverState"\s*:\s*"([^"<>]{80,})"',
            r'\\"serverState\\"\s*:\s*\\"(.{80,}?)\\"',
            r'serverState=([^&#"\']{80,})',
        ]
        patterns_update = [
            r'"serverScreenUpdate"\s*:\s*"([^"<>]{80,})"',
            r'\\"serverScreenUpdate\\"\s*:\s*\\"(.{80,}?)\\"',
        ]
        if not state:
            for p in patterns_state:
                m = re.search(p, text or "", re.S)
                if m:
                    state = html_lib.unescape(m.group(1))
                    break
        for p in patterns_update:
            m = re.search(p, text or "", re.S)
            if m:
                update = html_lib.unescape(m.group(1))
                break
        return state, update

    def open_epr_direct(self, epr_url: str) -> tuple[bool, str]:
        if "netflix.com/epr" in epr_url.lower():
            epr_url = re.sub(r"netflix\.com/epr", "netflix.com/iq/epr", epr_url, flags=re.IGNORECASE)
            sep = "&" if "?" in epr_url else "?"
            if "ui_langs=" not in epr_url.lower():
                epr_url += f"{sep}ui_langs=ar-IQ"

        t0 = time.time()

        # V22.14: the upstream proxy may occasionally close the very first EPR socket without
        # returning an HTTP response (RemoteDisconnected / connection aborted).  That is a
        # transport failure, not a bad Netflix session. Retry the tiny EPR GET on a fresh Requests
        # connection, then hand off to the existing Chromium fallback on the SAME signup proxy.
        # Never fall back to direct Railway while a signup proxy is selected.
        r = None
        last_transport_exc = None
        for attempt in range(1, 3):
            try:
                self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
                r = self.s.get(epr_url, timeout=30, allow_redirects=True)
                break
            except (requests.ConnectionError, requests.Timeout) as exc:
                last_transport_exc = exc
                self.note(
                    "epr_transport_error",
                    attempt=attempt,
                    proxy=bool(self.proxy_id),
                    error=f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}",
                )
                # Drop urllib3 connection pools so the retry cannot reuse the dead proxy socket.
                old_headers = dict(self.s.headers)
                old_cookies = self.s.cookies.copy()
                try:
                    self.s.close()
                except Exception:
                    pass
                self.s = requests.Session()
                self.s.trust_env = False
                self.s.headers.update(old_headers)
                try:
                    self.s.cookies.update(old_cookies)
                except Exception:
                    pass
                self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
                if attempt < 2:
                    time.sleep(0.35)

        if r is None:
            self.note(
                "epr_transport_fallback_to_chromium",
                proxy=bool(self.proxy_id),
                error=f"{type(last_transport_exc).__name__}: {scrub_sensitive_text(str(last_transport_exc))}" if last_transport_exc else "unknown",
            )
            return False, "proxy_transport_retry_exhausted" if self.proxy_id else "direct_transport_retry_exhausted"

        self.referer = r.url
        self.discover_versions(r.text or "")
        self.note("epr_get", status=r.status_code, final_url=r.url, elapsed=round(time.time()-t0, 3))
        r.raise_for_status()

        # Sometimes the account/session is already established after the GET/redirect chain.
        try:
            ms = self.membership_status()
        except (requests.ConnectionError, requests.Timeout) as exc:
            self.note("membership_after_epr_transport_error", error=f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}")
            return False, "proxy_transport_after_epr" if self.proxy_id else "direct_transport_after_epr"
        if ms == "NEVER_MEMBER":
            return True, "requests_get_only"

        state, update = self.extract_bootstrap_state(r.text or "", r.url)
        if not (state and update):
            self.note("direct_bootstrap_missing_state", have_state=bool(state), have_update=bool(update))
            return False, "missing_epr_bootstrap_state"

        try:
            body = self.gql(
                "CLCSScreenUpdate",
                {
                    "format": "HTML",
                    "imageFormat": "PNG",
                    "locale": DEFAULT_LOCALE,
                    "serverState": state,
                    "serverScreenUpdate": update,
                    "inputFields": [],
                },
                PQ_SCREEN_UPDATE,
                client_context={"appView": "PASSWORDLESS_REGISTRATION", "action": "Submitted", "appstate": "foreground"},
                referer=r.url,
                clcs=True,
            )
            # Response may tell the web app to navigate. The cookies are the important part for us.
            self.note("direct_epr_bootstrap_response", response=body)
            self.referer = f"{NETFLIX}/?accountCreated=success"
            ms = self.membership_status()
            if ms == "NEVER_MEMBER":
                return True, "requests_graphql_bootstrap"
        except Exception as exc:
            self.note("direct_epr_bootstrap_error", error=f"{type(exc).__name__}: {exc}")
        return False, "direct_bootstrap_not_confirmed"



        # V22.14: the upstream proxy may occasionally close the very first EPR socket without
        # returning an HTTP response (RemoteDisconnected / connection aborted).  That is a
        # transport failure, not a bad Netflix session. Retry the tiny EPR GET on a fresh Requests
        # connection, then hand off to the existing Chromium fallback on the SAME signup proxy.
        # Never fall back to direct Railway while a signup proxy is selected.
        r = None
        last_transport_exc = None
        for attempt in range(1, 3):
            try:
                self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
                r = self.s.get(epr_url, timeout=30, allow_redirects=True)
                break
            except (requests.ConnectionError, requests.Timeout) as exc:
                last_transport_exc = exc
                self.note(
                    "epr_transport_error",
                    attempt=attempt,
                    proxy=bool(self.proxy_id),
                    error=f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}",
                )
                # Drop urllib3 connection pools so the retry cannot reuse the dead proxy socket.
                old_headers = dict(self.s.headers)
                old_cookies = self.s.cookies.copy()
                try:
                    self.s.close()
                except Exception:
                    pass
                self.s = requests.Session()
                self.s.trust_env = False
                self.s.headers.update(old_headers)
                try:
                    self.s.cookies.update(old_cookies)
                except Exception:
                    pass
                self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
                if attempt < 2:
                    time.sleep(0.35)

        if r is None:
            self.note(
                "epr_transport_fallback_to_chromium",
                proxy=bool(self.proxy_id),
                error=f"{type(last_transport_exc).__name__}: {scrub_sensitive_text(str(last_transport_exc))}" if last_transport_exc else "unknown",
            )
            return False, "proxy_transport_retry_exhausted" if self.proxy_id else "direct_transport_retry_exhausted"

        self.referer = r.url
        self.discover_versions(r.text or "")
        self.note("epr_get", status=r.status_code, final_url=r.url, elapsed=round(time.time()-t0, 3))
        r.raise_for_status()

        # Sometimes the account/session is already established after the GET/redirect chain.
        try:
            ms = self.membership_status()
        except (requests.ConnectionError, requests.Timeout) as exc:
            self.note("membership_after_epr_transport_error", error=f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}")
            return False, "proxy_transport_after_epr" if self.proxy_id else "direct_transport_after_epr"
        if ms == "NEVER_MEMBER":
            return True, "requests_get_only"

        state, update = self.extract_bootstrap_state(r.text or "", r.url)
        if not (state and update):
            self.note("direct_bootstrap_missing_state", have_state=bool(state), have_update=bool(update))
            return False, "missing_epr_bootstrap_state"

        try:
            body = self.gql(
                "CLCSScreenUpdate",
                {
                    "format": "HTML",
                    "imageFormat": "PNG",
                    "locale": DEFAULT_LOCALE,
                    "serverState": state,
                    "serverScreenUpdate": update,
                    "inputFields": [],
                },
                PQ_SCREEN_UPDATE,
                client_context={"appView": "PASSWORDLESS_REGISTRATION", "action": "Submitted", "appstate": "foreground"},
                referer=r.url,
                clcs=True,
            )
            # Response may tell the web app to navigate. The cookies are the important part for us.
            self.note("direct_epr_bootstrap_response", response=body)
            self.referer = f"{NETFLIX}/?accountCreated=success"
            ms = self.membership_status()
            if ms == "NEVER_MEMBER":
                return True, "requests_graphql_bootstrap"
        except Exception as exc:
            self.note("direct_epr_bootstrap_error", error=f"{type(exc).__name__}: {exc}")
        return False, "direct_bootstrap_not_confirmed"

        # V22.14: the upstream proxy may occasionally close the very first EPR socket without
        # returning an HTTP response (RemoteDisconnected / connection aborted).  That is a
        # transport failure, not a bad Netflix session. Retry the tiny EPR GET on a fresh Requests
        # connection, then hand off to the existing Chromium fallback on the SAME signup proxy.
        # Never fall back to direct Railway while a signup proxy is selected.
        r = None
        last_transport_exc = None
        for attempt in range(1, 3):
            try:
                self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
                r = self.s.get(epr_url, timeout=30, allow_redirects=True)
                break
            except (requests.ConnectionError, requests.Timeout) as exc:
                last_transport_exc = exc
                self.note(
                    "epr_transport_error",
                    attempt=attempt,
                    proxy=bool(self.proxy_id),
                    error=f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}",
                )
                # Drop urllib3 connection pools so the retry cannot reuse the dead proxy socket.
                old_headers = dict(self.s.headers)
                old_cookies = self.s.cookies.copy()
                try:
                    self.s.close()
                except Exception:
                    pass
                self.s = requests.Session()
                self.s.trust_env = False
                self.s.headers.update(old_headers)
                try:
                    self.s.cookies.update(old_cookies)
                except Exception:
                    pass
                self.proxy_id = apply_proxy_to_session(self.s, self.proxy_id)
                if attempt < 2:
                    time.sleep(0.35)

        if r is None:
            self.note(
                "epr_transport_fallback_to_chromium",
                proxy=bool(self.proxy_id),
                error=f"{type(last_transport_exc).__name__}: {scrub_sensitive_text(str(last_transport_exc))}" if last_transport_exc else "unknown",
            )
            return False, "proxy_transport_retry_exhausted" if self.proxy_id else "direct_transport_retry_exhausted"

        self.referer = r.url
        self.discover_versions(r.text or "")
        self.note("epr_get", status=r.status_code, final_url=r.url, elapsed=round(time.time()-t0, 3))
        r.raise_for_status()

        # Sometimes the account/session is already established after the GET/redirect chain.
        try:
            ms = self.membership_status()
        except (requests.ConnectionError, requests.Timeout) as exc:
            self.note("membership_after_epr_transport_error", error=f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}")
            return False, "proxy_transport_after_epr" if self.proxy_id else "direct_transport_after_epr"
        if ms == "NEVER_MEMBER":
            return True, "requests_get_only"

        state, update = self.extract_bootstrap_state(r.text or "", r.url)
        if not (state and update):
            self.note("direct_bootstrap_missing_state", have_state=bool(state), have_update=bool(update))
            return False, "missing_epr_bootstrap_state"

        try:
            body = self.gql(
                "CLCSScreenUpdate",
                {
                    "format": "HTML",
                    "imageFormat": "PNG",
                    "locale": DEFAULT_LOCALE,
                    "serverState": state,
                    "serverScreenUpdate": update,
                    "inputFields": [],
                },
                PQ_SCREEN_UPDATE,
                client_context={"appView": "PASSWORDLESS_REGISTRATION", "action": "Submitted", "appstate": "foreground"},
                referer=r.url,
                clcs=True,
            )
            # Response may tell the web app to navigate. The cookies are the important part for us.
            self.note("direct_epr_bootstrap_response", response=body)
            self.referer = f"{NETFLIX}/?accountCreated=success"
            ms = self.membership_status()
            if ms == "NEVER_MEMBER":
                return True, "requests_graphql_bootstrap"
        except Exception as exc:
            self.note("direct_epr_bootstrap_error", error=f"{type(exc).__name__}: {exc}")
        return False, "direct_bootstrap_not_confirmed"

    def import_selenium_cookies(self, cookies: list[dict], current_url: str):
        for c in cookies:
            name = c.get("name")
            value = c.get("value")
            if not name or value is None:
                continue
            kwargs = {}
            if c.get("domain"):
                kwargs["domain"] = c["domain"]
            if c.get("path"):
                kwargs["path"] = c["path"]
            try:
                self.s.cookies.set(name, value, **kwargs)
            except Exception:
                self.s.cookies.set(name, value)
        self.referer = current_url or f"{NETFLIX}/?accountCreated=success"
        self.note("imported_browser_cookies", cookie_count=len(cookies), current_url=current_url)

    def preload_from_screen(self, screen: dict) -> list[dict]:
        preload_states = screen.get("preload") or []
        if not preload_states:
            return []
        pre = self.gql(
            "CLCSPreloadScreens",
            {"serverStates": preload_states},
            PQ_PRELOAD,
            client_context={"appstate": "foreground"},
            referer=f"{NETFLIX}/signup",
            clcs=True,
        )
        return extract_preload_screens(pre)

    def init_signup(self) -> tuple[dict, list[dict]]:
        flwssn = None
        try:
            flwssn = self.s.cookies.get("flwssn")
        except Exception:
            pass
        if not flwssn:
            matches = [c.value for c in self.s.cookies if c.name == "flwssn" and c.value]
            if matches:
                flwssn = matches[-1]
        if not flwssn:
            raise RuntimeError("ما لكيت flwssn بالجلسة بعد إنشاء الحساب")

        init = self.gql(
            "CLCSWebInitSignup",
            {
                "inputNode": "WELCOME",
                "locale": DEFAULT_LOCALE,
                "inputFields": [{"name": "flwssn", "value": {"stringValue": flwssn}}],
            },
            PQ_INIT_SIGNUP,
            client_context={"appstate": "foreground"},
            referer=f"{NETFLIX}/?accountCreated=success",
            clcs=True,
        )
        screen = extract_screen(init)
        if not screen:
            typename = nested_get(init, "data", "clcsWebInitSignup", "__typename")
            location = nested_get(init, "data", "clcsWebInitSignup", "location")
            self.note("init_without_screen", typename=typename, location=location, response=init)
            raise RuntimeError("CLCSWebInitSignup رجع بدون screen")
        return screen, self.preload_from_screen(screen)

    def select_plan(self, plan_screen: dict) -> dict:
        plan_value = extract_plan_value(plan_screen)
        button = find_node(plan_screen, test_id="cta-plan-selection") or find_node(plan_screen, label="Next")
        if not button:
            raise RuntimeError("ما لكيت زر Next الخاص بالخطة داخل CLCS")
        update = action_server_update(button)
        state = plan_screen.get("serverState")
        if not (state and update):
            raise RuntimeError("خطة Netflix ناقصها serverState/serverScreenUpdate")
        body = self.gql(
            "CLCSScreenUpdate",
            {
                "format": "HTML",
                "imageFormat": "PNG",
                "locale": DEFAULT_LOCALE,
                "serverState": state,
                "serverScreenUpdate": update,
                "inputFields": [{"name": "planChoice", "value": {"stringValue": plan_value}}],
            },
            PQ_SCREEN_UPDATE,
            client_context={"appView": "planSelection", "action": "Submitted", "appstate": "foreground"},
            referer=f"{NETFLIX}/signup",
            clcs=True,
        )
        screen = extract_screen(body)
        if not screen:
            raise RuntimeError("اختيار الخطة ما رجع payment screen")
        return screen

    def choose_mobile_bill(self, payment_screen: dict) -> dict:
        dcb = find_node(payment_screen, test_id="DCB") or find_node(payment_screen, logging_view="paymentDcb")
        if not dcb:
            raise RuntimeError("ما لكيت DCB/paymentDcb داخل paymentPicker")
        update = action_server_update(dcb)
        state = payment_screen.get("serverState")
        if not (state and update):
            raise RuntimeError("paymentPicker ناقص serverState/serverScreenUpdate")
        body = self.gql(
            "CLCSScreenUpdate",
            {
                "format": "HTML",
                "imageFormat": "PNG",
                "locale": DEFAULT_LOCALE,
                "serverState": state,
                "serverScreenUpdate": update,
                "inputFields": [],
            },
            PQ_SCREEN_UPDATE,
            client_context={"appView": "paymentPicker", "action": "Submitted", "appstate": "foreground"},
            referer=f"{NETFLIX}/signup",
            clcs=True,
        )
        screen = extract_screen(body)
        if not screen:
            raise RuntimeError("اختيار Add to mobile bill ما رجع screen")
        return screen

    def submit_phone_for_dcb(self, phone_screen: dict, phone: str) -> tuple[Optional[dict], str]:
        button = (
            find_node(phone_screen, logging_view="submitPaymentButton")
            or find_node(phone_screen, label="Verify Phone Number")
            or find_node(phone_screen, test_id="cta-button")
        )
        if not button:
            raise RuntimeError("ما لكيت زر Verify Phone Number داخل ENTER_DCB")
        update = action_server_update(button)
        state = phone_screen.get("serverState")
        if not (state and update):
            raise RuntimeError("ENTER_DCB ناقص serverState/serverScreenUpdate")

        body = self.gql(
            "CLCSScreenUpdate",
            {
                "format": "HTML",
                "imageFormat": "PNG",
                "locale": DEFAULT_LOCALE,
                "serverState": state,
                "serverScreenUpdate": update,
                "inputFields": [
                    {"name": "phoneNumber", "value": {"stringValue": phone}},
                    {"name": "countryCode", "value": {"stringValue": "IQ"}},
                    {"name": "paymentSubtype", "value": {"stringValue": "NA"}},
                    {"name": "partnerIntegrationUrl", "value": {"stringValue": "https://www.netflix.com/signup?serverCallback={serverCallback}"}},
                    {"name": "iAgree", "value": {"booleanValue": True}},
                ],
            },
            PQ_SCREEN_UPDATE,
            client_context={"appView": "ENTER_DCB", "action": "Submitted", "appstate": "foreground"},
            referer=f"{NETFLIX}/signup",
            clcs=True,
        )

        screen = extract_screen(body)
        if screen:
            return screen, "screen"

        poll_update, interval_ms = extract_poll_update(body)
        if not poll_update:
            return None, "submitted_no_screen"

        deadline = time.time() + 15
        while time.time() < deadline:
            time.sleep(interval_ms / 1000.0)
            polled = self.gql(
                "CLCSScreenUpdate",
                {
                    "format": "HTML",
                    "imageFormat": "PNG",
                    "locale": DEFAULT_LOCALE,
                    "serverState": state,
                    "serverScreenUpdate": poll_update,
                    "inputFields": [],
                },
                PQ_SCREEN_UPDATE,
                client_context={"appView": "ENTER_DCB", "appstate": "foreground"},
                referer=f"{NETFLIX}/signup",
                clcs=True,
            )
            screen = extract_screen(polled)
            if screen:
                return screen, "poll_screen"
            next_update, next_interval = extract_poll_update(polled)
            if next_update:
                poll_update, interval_ms = next_update, next_interval
            else:
                return None, "submitted_poll_complete_without_screen"
        return None, "submitted_poll_timeout"

    def write_debug(self, reason: str) -> str:
        p = TMPDIR / f"netflix_fast_v22_debug_{int(time.time())}.json"
        p.write_text(json.dumps({
            "format": "netflix_fast_v22_debug",
            "reason": reason,
            "created_at": time.time(),
            "privacy": "sanitized; no cookies/session state/phone/email/password/OTP",
            "events": self.debug,
        }, ensure_ascii=False, indent=2), encoding="utf-8")
        return str(p)


# ---------------- Optional Chromium fallback for live CLCS state ----------------

def _configure_driver_arabic(driver) -> None:
    """Force Arabic-Iraq locale for both headless and visible Chromium sessions."""
    try:
        driver.execute_cdp_cmd("Network.enable", {})
        driver.execute_cdp_cmd("Network.setExtraHTTPHeaders", {"headers": {"Accept-Language": DEFAULT_ACCEPT_LANGUAGE}})
    except Exception:
        pass
    try:
        driver.execute_cdp_cmd("Emulation.setLocaleOverride", {"locale": DEFAULT_LOCALE})
    except Exception:
        pass


def _new_chromium_driver(performance: bool = False, proxy_id: Optional[str] = None, *, arabic: bool = True, force_proxy: bool = False):
    try:
        from selenium import webdriver
        from selenium.webdriver.chrome.options import Options
        from selenium.webdriver.chrome.service import Service
    except Exception as exc:
        raise RuntimeError(f"Selenium غير متوفر للـbootstrap الاحتياطي: {exc}")

    chromium = shutil.which("chromium-browser") or shutil.which("chromium")
    chromedriver = shutil.which("chromedriver")
    if not chromium or not chromedriver:
        raise RuntimeError("Chromium/chromedriver غير موجودين للـbootstrap الاحتياطي")

    opts = Options()
    opts.binary_location = chromium
    # Speed without changing the workflow: return after DOMContentLoaded, then our existing
    # state-pollers wait for the exact Netflix state. This avoids waiting for cosmetic assets.
    try:
        opts.page_load_strategy = "eager"
    except Exception:
        pass
    # Keep the invisible EPR bootstrap on the legacy locale that was stable
    # before V22.7. Visible/manual Netflix sessions remain Arabic-Iraq.
    browser_lang = "ar-IQ" if arabic else "en-US"
    for arg in (
        "--headless=new", "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
        "--window-size=430,900", f"--lang={browser_lang}", "--disable-extensions",
        "--disable-sync", "--no-first-run", "--no-default-browser-check",
        "--blink-settings=imagesEnabled=false",
    ):
        opts.add_argument(arg)
    opts.add_experimental_option("prefs", {
        "profile.managed_default_content_settings.images": 2,
        "profile.default_content_setting_values.images": 2,
        "profile.default_content_setting_values.notifications": 2,
        "intl.accept_languages": "ar-IQ,ar,en-US,en" if arabic else "en-US,en",
    })
    chrome_proxy = chrome_proxy_server(proxy_id, require_enabled=not force_proxy)
    if chrome_proxy:
        opts.add_argument(f"--proxy-server={chrome_proxy}")
    if performance:
        opts.set_capability("goog:loggingPrefs", {"performance": "ALL"})
    driver = webdriver.Chrome(service=Service(chromedriver), options=opts)
    # Keep JavaScript/CSS/XHR untouched. Only heavy cosmetic/media resources are blocked,
    # which cuts proxy traffic and lets the form/CLCS state arrive sooner.
    try:
        driver.execute_cdp_cmd("Network.enable", {})
        driver.execute_cdp_cmd("Network.setBlockedURLs", {"urls": [
            "*.jpg", "*.jpeg", "*.png", "*.gif", "*.webp",
            "*.woff", "*.woff2", "*.ttf", "*.mp4", "*.webm", "*.m3u8", "*.mp3"
        ]})
    except Exception:
        pass
    if arabic:
        _configure_driver_arabic(driver)
    return driver


def _seed_browser_from_requests(driver, session: requests.Session) -> None:
    driver.get(f"{NETFLIX}/robots.txt")
    try:
        driver.delete_all_cookies()
    except Exception:
        pass
    for c in session.cookies:
        if not c.name or c.value is None:
            continue
        item = {"name": c.name, "value": c.value, "path": c.path or "/"}
        dom = c.domain or ".netflix.com"
        if "netflix.com" in dom:
            item["domain"] = dom
        try:
            driver.add_cookie(item)
        except Exception:
            try:
                item.pop("domain", None)
                driver.add_cookie(item)
            except Exception:
                pass

def bootstrap_with_chromium(epr_url: str, chat_id: int, seed_session: Optional[requests.Session] = None, proxy_id: Optional[str] = None) -> tuple[list[dict], str]:
    if "netflix.com/epr" in epr_url.lower():
        epr_url = re.sub(r"netflix\.com/epr", "netflix.com/iq/epr", epr_url, flags=re.IGNORECASE)
        sep = "&" if "?" in epr_url else "?"
        if "ui_langs=" not in epr_url.lower():
            epr_url += f"{sep}ui_langs=ar-IQ"

    driver = _new_chromium_driver(performance=False, proxy_id=proxy_id, arabic=True, force_proxy=bool(proxy_id))

    # EPR is an invisible bootstrap. Keep it on the old en-US locale because
    # forcing ar-IQ changed the redirect behavior on some Netflix variants.
    # All visible/manual browser sessions remain ar-IQ.
    driver = _new_chromium_driver(performance=False, proxy_id=proxy_id, arabic=False, force_proxy=bool(proxy_id))
    try:
        send_message(chat_id, "⚡ Direct EPR bootstrap ما اكتمل؛ أشغل Chromium بالخلفية لتثبيت جلسة EPR، وبعدها أكمل بالكود المباشر.")
        if seed_session is not None and len(seed_session.cookies):
            _seed_browser_from_requests(driver, seed_session)
        driver.get(epr_url)

        deadline = time.time() + 50
        last = ""
        server_state_seen_at = None
        last_membership_check = 0.0
        explicit_advance_attempts = 0

        while time.time() < deadline:
            u = str(driver.current_url or "")
            last = u
            ul = u.lower()

            if "accountcreated=success" in ul:
                return driver.get_cookies(), u

            body = _body_text_lower(driver)
            if any(x in body for x in (
                "link has expired", "link expired", "code has expired", "invalid link",
                "انتهت صلاحية الرابط", "انتهت صلاحية الرمز", "الرابط غير صالح",
            )):
                raise RuntimeError("رابط EPR منتهي/مستخدم. أنشئ رابط EPR جديد وجربه مرة واحدة فقط")

            try:
                qs = parse_qs(urlparse(u).query)
                live_state = bool((qs.get("serverState") or [None])[0])
            except Exception:
                live_state = False

            if live_state:
                if server_state_seen_at is None:
                    server_state_seen_at = time.time()

                # Some Netflix variants render a small intermediate EPR screen
                # instead of auto-navigating. Advance only explicit safe signup CTAs.
                if explicit_advance_attempts < 2 and _click_button_like(driver, (
                    "finish sign-up", "finish signup", "complete sign-up", "complete signup",
                    "continue", "next", "إكمال التسجيل", "إنهاء التسجيل", "متابعة", "التالي",
                )):
                    explicit_advance_attempts += 1
                    time.sleep(0.25)
                    continue

                # URL is not the only source of truth. Verify the same browser
                # cookies through MembershipStatus. NEVER_MEMBER is the normal
                # pre-membership state and confirms the EPR session exists.
                if time.time() - last_membership_check >= 1.0:
                    last_membership_check = time.time()
                    try:
                        tmp = NetflixDirect()
                        tmp.proxy_id = apply_saved_proxy_temporarily(tmp.s, proxy_id) if proxy_id else None
                        tmp.import_selenium_cookies(driver.get_cookies(), u)
                        ms = tmp.membership_status()
                        if ms == "NEVER_MEMBER":
                            return driver.get_cookies(), u
                    except Exception:
                        pass

                # Compatibility fallback for the exact V22.7 regression: when a
                # live serverState + flwssn stay stable, hand the session to
                # init_signup(), which performs the next authoritative CLCS check.
                if server_state_seen_at and time.time() - server_state_seen_at >= 1.5:
                    try:
                        names = {str(c.get("name") or "") for c in driver.get_cookies()}
                    except Exception:
                        names = set()
                    if "flwssn" in names:
                        return driver.get_cookies(), u

            time.sleep(0.10)

        try:
            _send_v22_browser_diagnostic(
                chat_id, driver, "epr_bootstrap_timeout",
                "EPR ما أعطى accountCreated=success ولا جلسة CLCS قابلة للتسليم. استخدم رابط EPR جديد بعد التأكد من البروكسي."
            )
        except Exception:
            pass
        raise RuntimeError(f"EPR bootstrap ما اكتمل. آخر رابط: {_redact_browser_url(last)}")
    finally:
        try:
            driver.quit()
        except Exception:
            pass


def _decode_perf_body(driver, request_id: str) -> Optional[dict]:
    try:
        body_obj = driver.execute_cdp_cmd("Network.getResponseBody", {"requestId": request_id})
        raw = body_obj.get("body") or ""
        if body_obj.get("base64Encoded"):
            raw = base64.b64decode(raw).decode("utf-8", "replace")
        obj = json.loads(raw)
        return obj if isinstance(obj, dict) else None
    except Exception:
        return None


def capture_live_init_with_chromium(eng: NetflixDirect, chat_id: int) -> tuple[dict, list[dict]]:
    driver = _new_chromium_driver(performance=True, proxy_id=eng.proxy_id, force_proxy=bool(eng.proxy_id))
    init_body = None
    preload_body = None
    request_ops: dict[str, str] = {}
    try:
        send_message(chat_id, "⚡ CLCSWebInitSignup المباشر رجع بدون screen. آخذ الـlive init من Chromium مرة وحدة، أغلقه، وبعدها أكمل Requests بسرعة.")
        _seed_browser_from_requests(driver, eng.s)
        driver.get(f"{NETFLIX}/?accountCreated=success")
        time.sleep(0.30)
        try:
            driver.get_log("performance")
        except Exception:
            pass

        clicked = False
        js = "const els=[...document.querySelectorAll('a,button,[role=\"button\"]')];const el=els.find(e=>/finish\\s*sign[- ]?up/i.test((e.innerText||e.textContent||'').trim()));if(el){el.click();return true;}return false;"
        try:
            clicked = bool(driver.execute_script(js))
        except Exception:
            clicked = False
        if not clicked:
            driver.get(f"{NETFLIX}/signup")

        deadline = time.time() + 18
        while time.time() < deadline:
            try:
                logs = driver.get_log("performance")
            except Exception:
                logs = []
            for entry in logs:
                try:
                    msg = json.loads(entry.get("message") or "{}").get("message") or {}
                    method = msg.get("method")
                    params = msg.get("params") or {}
                    if method == "Network.requestWillBeSent":
                        rid = params.get("requestId")
                        req = params.get("request") or {}
                        if not rid or "/graphql" not in str(req.get("url") or ""):
                            continue
                        op = ""
                        headers = req.get("headers") or {}
                        for hk, hv in headers.items():
                            if str(hk).lower() == "x-netflix.context.operation-name":
                                op = str(hv)
                                break
                        if not op:
                            pd = req.get("postData")
                            if pd:
                                try:
                                    op = str(json.loads(pd).get("operationName") or "")
                                except Exception:
                                    pass
                        if op:
                            request_ops[rid] = op
                    elif method in ("Network.responseReceived", "Network.loadingFinished"):
                        rid = params.get("requestId")
                        op = request_ops.get(rid or "", "")
                        if rid and op in ("CLCSWebInitSignup", "CLCSPreloadScreens"):
                            obj = _decode_perf_body(driver, rid)
                            if obj:
                                if op == "CLCSWebInitSignup" and init_body is None:
                                    init_body = obj
                                elif op == "CLCSPreloadScreens" and preload_body is None:
                                    preload_body = obj
                except Exception:
                    continue
            if init_body is not None and preload_body is not None:
                break
            time.sleep(0.12)

        eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or f"{NETFLIX}/signup")
        if not init_body:
            raise RuntimeError("ما قدرت ألتقط CLCSWebInitSignup الحي من Chromium")
        init_screen = extract_screen(init_body)
        if not init_screen:
            raise RuntimeError("حتى CLCSWebInitSignup الحي رجع بدون screen")
        screens = extract_preload_screens(preload_body or {})
        if not screens:
            screens = eng.preload_from_screen(init_screen)
        eng.note("live_init_captured", preload_count=len(screens), current_url=driver.current_url)
        return init_screen, screens
    finally:
        try:
            driver.quit()
        except Exception:
            pass


# ---------------- Persistent sessions + profile manager ----------------

def send_inline(chat_id: int, text: str, rows: list[list[tuple[str, str]]]) -> None:
    markup = {
        "inline_keyboard": [
            [{"text": label, "callback_data": data} for label, data in row]
            for row in rows
        ]
    }
    tg_call("sendMessage", {
        "chat_id": str(chat_id),
        "text": text,
        "disable_web_page_preview": "true",
        "reply_markup": json.dumps(markup, ensure_ascii=False),
    })


def send_url_inline(chat_id: int, text: str, label: str, url: str) -> None:
    tg_call("sendMessage", {
        "chat_id": str(chat_id),
        "text": text,
        "disable_web_page_preview": "true",
        "reply_markup": json.dumps({"inline_keyboard": [[{"text": label, "url": url}]]}, ensure_ascii=False),
    })


def show_proxy_menu(chat_id: int) -> None:
    cfg = load_proxy_config()
    items = cfg.get('items') or {}
    active_id = cfg.get('active_id')
    active = items.get(active_id) if active_id else None
    enabled = bool(cfg.get('enabled') and active)
    rows = [
        [("➕ إضافة بروكسي", "proxy_add"), ("🧪 فحص البروكسي", "proxy_test")],
        [("⏹ إيقاف البروكسي" if enabled else "▶️ تشغيل البروكسي", "proxy_toggle"), ("🗑 حذف الحالي", "proxy_delete")],
    ]
    for pid, p in list(items.items())[:8]:
        mark = '✅' if pid == active_id else '▫️'
        rows.append([(f"{mark} {proxy_mask(p)}", f"proxy_sel:{pid}")])
    rows.append([("⬅️ رجوع", "proxy_back")])
    state = '✅ جاهز لإنشاء الحساب' if enabled else '⏸ غير مستخدم بإنشاء الحساب'
    send_inline(chat_id, f"🌐 إدارة البروكسي\nالحالة: {state}\nالحالي: {proxy_mask(active)}\nالعدد: {len(items)}\n\nالبروكسي مخصص لإنشاء الحساب فقط: EPR → الخطة → الشروط/الهاتف → OTP → Start Membership. بعد التفعيل ينفصل فوراً. تسجيل الدخول وإدارة الحساب Direct Railway.", rows)


def proxy_test_worker(chat_id: int) -> None:
    try:
        r = test_proxy()
        ip = r.get('ip') or 'غير متاح'
        send_inline(chat_id, f"✅ فحص البروكسي نجح\nProxy: {r.get('proxy')}\nIP: {ip}\nNetflix HTTP: {r.get('netflix_status')}", [[("⬅️ البروكسي", "proxy")]])
    except Exception as exc:
        send_inline(chat_id, f"❌ فحص البروكسي فشل: {type(exc).__name__}: {scrub_sensitive_text(str(exc))}", [[("🔄 إعادة الفحص", "proxy_test"), ("⬅️ البروكسي", "proxy")]])


def railway_browser_url() -> Optional[str]:
    explicit = (os.environ.get('PUBLIC_BROWSER_URL') or '').strip()
    if explicit:
        return explicit.rstrip('/') + '/vnc.html?autoconnect=true&resize=scale&path=websockify'
    domain = (os.environ.get('RAILWAY_PUBLIC_DOMAIN') or '').strip()
    if domain:
        return f"https://{domain}/vnc.html?autoconnect=true&resize=scale&path=websockify"
    return None


def answer_callback(callback_id: str, text: str = "") -> None:
    try:
        tg_call("answerCallbackQuery", {"callback_query_id": callback_id, "text": text[:180]})
    except Exception:
        pass


def _atomic_write_json(path: Path, obj: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2), encoding="utf-8")
    try:
        os.chmod(tmp, 0o600)
    except Exception:
        pass
    tmp.replace(path)
    try:
        os.chmod(path, 0o600)
    except Exception:
        pass


def load_accounts() -> dict[str, dict]:
    with STATE_LOCK:
        try:
            obj = json.loads(ACCOUNTS_FILE.read_text(encoding="utf-8"))
            if isinstance(obj, dict):
                return {str(k): v for k, v in obj.items() if isinstance(v, dict)}
        except Exception:
            pass
        return {}


def save_accounts(accounts: dict[str, dict]) -> None:
    with STATE_LOCK:
        _atomic_write_json(ACCOUNTS_FILE, accounts)


def cookiejar_to_list(session: requests.Session) -> list[dict]:
    out = []
    for c in session.cookies:
        out.append({
            "name": c.name,
            "value": c.value,
            "domain": c.domain or ".netflix.com",
            "path": c.path or "/",
            "secure": bool(getattr(c, "secure", False)),
        })
    return out


def restore_cookies(session: requests.Session, cookies: list[dict]) -> None:
    session.cookies.clear()
    for c in cookies or []:
        if not isinstance(c, dict) or not c.get("name"):
            continue
        kwargs = {}
        if c.get("domain"):
            kwargs["domain"] = str(c["domain"])
        if c.get("path"):
            kwargs["path"] = str(c["path"])
        try:
            session.cookies.set(str(c["name"]), str(c.get("value") or ""), **kwargs)
        except Exception:
            session.cookies.set(str(c["name"]), str(c.get("value") or ""))


def _next_account_id(accounts: dict[str, dict]) -> str:
    nums = []
    for k in list(accounts) + list(DELETED_ACCOUNT_IDS):
        m = re.fullmatch(r"acc(\d+)", str(k))
        if m:
            nums.append(int(m.group(1)))
    # Do not reuse a tombstoned id until process restart; an old worker may still hold that id.
    return f"acc{(max(nums) if nums else 0) + 1}"


def save_engine_account(eng: NetflixDirect, account_id: Optional[str] = None,
                        status: str = "pending_otp", profiles: Optional[list[dict]] = None) -> str:
    # Hold the state lock across the full read-modify-write transaction. This closes a race where
    # a stale browser/signup worker could load accounts.json just before deletion and write the
    # deleted account back a moment later. RLock makes nested load/save helpers safe here.
    with STATE_LOCK:
        accounts = load_accounts()
        now = time.time()
        if not account_id:
            account_id = _next_account_id(accounts)
        elif account_id in DELETED_ACCOUNT_IDS:
            return account_id

        old = accounts.get(account_id, {})
        label = old.get("label") or f"حساب {account_id[3:] if account_id.startswith('acc') else account_id}"
        proxy_detached = bool(old.get("proxy_detached_after_activation") or old.get("proxy_detached_after_login"))
        saved_proxy_id = None if proxy_detached else (getattr(eng, "proxy_id", None) or old.get("proxy_id"))
        accounts[account_id] = {
            **old,
            "id": account_id,
            "label": label,
            "status": status,
            "created_at": old.get("created_at") or now,
            "updated_at": now,
            "app_version": eng.app_version,
            "hawkins": eng.hawkins,
            "referer": eng.referer,
            "proxy_id": saved_proxy_id,
            "cookies": cookiejar_to_list(eng.s),
            "profiles": profiles if profiles is not None else old.get("profiles", []),
        }
        # Re-check under the same lock immediately before the write.
        if account_id in DELETED_ACCOUNT_IDS:
            return account_id
        save_accounts(accounts)
        return account_id


def update_account_record(account_id: str, **changes) -> dict:
    with STATE_LOCK:
        if account_id in DELETED_ACCOUNT_IDS:
            return {}
        accounts = load_accounts()
        if account_id not in accounts:
            raise RuntimeError("الجلسة المحفوظة غير موجودة")
        accounts[account_id].update(changes)
        accounts[account_id]["updated_at"] = time.time()
        if account_id in DELETED_ACCOUNT_IDS:
            return {}
        save_accounts(accounts)
        return accounts[account_id]


def delete_account_record(account_id: str) -> None:
    with STATE_LOCK:
        # Tombstone and delete atomically with respect to all account writers.
        DELETED_ACCOUNT_IDS.add(account_id)
        accounts = load_accounts()
        accounts.pop(account_id, None)
        save_accounts(accounts)
        clear_cached_account_password(account_id)


def engine_from_account(account_id: str) -> NetflixDirect:
    accounts = load_accounts()
    acct = accounts.get(account_id)
    if not acct:
        raise RuntimeError("ما لكيت الحساب المحفوظ")
    eng = NetflixDirect()
    status = str(acct.get("status") or "").lower()
    detached = bool(acct.get("proxy_detached_after_activation") or acct.get("proxy_detached_after_login"))
    if status == "active" or detached:
        # Activated/logged-in accounts never spend proxy traffic.
        eng.s.trust_env = False
        eng.s.proxies.clear()
        eng.proxy_id = None
    else:
        # A pending signup keeps the exact signup proxy until membership activation,
        # even if the global toggle is changed while the OTP flow is still pending.
        eng.proxy_id = apply_saved_proxy_temporarily(eng.s, acct.get("proxy_id"))
    restore_cookies(eng.s, acct.get("cookies") or [])
    eng.app_version = str(acct.get("app_version") or DEFAULT_APP_VERSION)
    eng.hawkins = str(acct.get("hawkins") or DEFAULT_HAWKINS_VERSION)
    eng.referer = str(acct.get("referer") or f"{NETFLIX}/account")
    return eng


def detach_proxy_after_activation(eng: NetflixDirect, account_id: str) -> Optional[str]:
    """Detach only this activated account from the limited signup proxy.

    The proxy definition/global enable state is left untouched for future signups.
    This Requests engine is cleared immediately and the account is persistently
    marked so future Requests/Chromium operations for it use direct Railway.
    """
    acct = load_accounts().get(account_id) or {}
    previous = acct.get("proxy_id") or getattr(eng, "proxy_id", None)
    eng.s.trust_env = False
    eng.s.proxies.clear()
    eng.proxy_id = None
    update_account_record(
        account_id,
        proxy_id=None,
        proxy_detached_after_activation=True,
        proxy_detached_at=time.time(),
        last_signup_proxy_id=previous,
    )
    return str(previous) if previous else None


def detach_proxy_after_login(eng: NetflixDirect, account_id: str) -> Optional[str]:
    """Detach the short-lived login proxy from this saved account immediately.

    The global proxy config is not changed. The login browser/request session may use
    the selected saved proxy just for authentication, but every later operation for
    this account is forced to direct Railway networking.
    """
    acct = load_accounts().get(account_id) or {}
    previous = acct.get("proxy_id") or getattr(eng, "proxy_id", None)
    eng.s.trust_env = False
    eng.s.proxies.clear()
    eng.proxy_id = None
    update_account_record(
        account_id,
        proxy_id=None,
        proxy_detached_after_login=True,
        proxy_detached_at=time.time(),
        last_login_proxy_id=previous,
    )
    return str(previous) if previous else None


def is_active_membership(status: Optional[str]) -> bool:
    s = str(status or "").upper()
    if not s or "NEVER" in s or "FORMER" in s or "CANCEL" in s:
        return False
    return s in {"CURRENT_MEMBER", "MEMBER", "ACTIVE", "CURRENT"} or ("MEMBER" in s and "NEVER" not in s)


def graphql_ok(body: dict, operation: str) -> None:
    errors = body.get("errors") if isinstance(body, dict) else None
    if errors:
        raise RuntimeError(f"{operation} رجع GraphQL errors: {safe_summary(errors)}")
    if not isinstance(body, dict) or "data" not in body:
        raise RuntimeError(f"{operation} رجع رد غير متوقع")


def profile_guid_from_obj(obj: Any) -> Optional[str]:
    guid_re = re.compile(r"^[A-Za-z0-9]{20,40}$")
    for d in deep_walk(obj):
        for key in ("profileGuid", "guid", "id"):
            v = d.get(key)
            if isinstance(v, str) and guid_re.fullmatch(v):
                return v
    return None


def add_profile(eng: NetflixDirect, name: str) -> Optional[str]:
    body = eng.gql(
        "AddProfile",
        {"name": name, "avatarKey": "icon26", "isKids": False},
        PQ_ADD_PROFILE,
        client_context={"appstate": "foreground"},
        referer=f"{NETFLIX}/ManageProfiles",
    )
    graphql_ok(body, "AddProfile")
    return profile_guid_from_obj(body)


def update_profile_name(eng: NetflixDirect, profile: dict, name: str) -> None:
    guid = str(profile.get("guid") or "")
    if not guid:
        raise RuntimeError("البروفايل ناقص GUID")
    avatar = str(profile.get("avatarKey") or "icon26")
    body = eng.gql(
        "updateProfileInfo",
        {"id": guid, "name": name, "gender": "UNSPECIFIED", "avatarKey": avatar},
        PQ_UPDATE_PROFILE_INFO,
        client_context={"appstate": "foreground"},
        referer=f"{NETFLIX}/ManageProfiles",
    )
    graphql_ok(body, "updateProfileInfo")


def update_profile_pin(eng: NetflixDirect, guid: str, pin: str) -> None:
    if not re.fullmatch(r"\d{4}", pin or ""):
        raise RuntimeError("PIN لازم يكون 4 أرقام")
    body = eng.gql(
        "UpdateProfileAccessPin",
        {"profileGuid": guid, "profilePin": pin, "requirePinToCreateProfiles": False},
        PQ_UPDATE_PROFILE_PIN,
        client_context={"appstate": "foreground"},
        referer=f"{NETFLIX}/settings/lock/{guid}",
    )
    graphql_ok(body, "UpdateProfileAccessPin")


def remove_profile(eng: NetflixDirect, guid: str) -> None:
    body = eng.gql(
        "RemoveProfile",
        {"id": guid},
        PQ_REMOVE_PROFILE,
        client_context={"appstate": "foreground"},
        referer=f"{NETFLIX}/ManageProfiles",
    )
    graphql_ok(body, "RemoveProfile")


def _candidate_profile(d: dict) -> Optional[dict]:
    guid_re = re.compile(r"^[A-Za-z0-9]{20,40}$")
    guid = None
    for key in ("profileGuid", "guid", "id"):
        v = d.get(key)
        if isinstance(v, str) and guid_re.fullmatch(v):
            guid = v
            break
    if not guid:
        return None
    name = d.get("name") or d.get("profileName") or d.get("displayName")
    avatar = d.get("avatarKey") or nested_get(d, "avatar", "name") or nested_get(d, "avatar", "key")
    return {
        "guid": guid,
        "name": str(name or "").strip(),
        "avatarKey": str(avatar or "").strip() or None,
    }


def collect_profile_candidates(obj: Any) -> list[dict]:
    out: list[dict] = []
    seen = set()
    for d in deep_walk(obj):
        p = _candidate_profile(d)
        if p and p["guid"] not in seen:
            seen.add(p["guid"])
            out.append(p)
    return out


def _merge_profiles(base: list[dict], extra: list[dict]) -> list[dict]:
    order: list[str] = []
    data: dict[str, dict] = {}
    for p in list(base) + list(extra):
        if not isinstance(p, dict) or not p.get("guid"):
            continue
        g = str(p["guid"])
        if g not in data:
            order.append(g)
            data[g] = {"guid": g, "name": "", "avatarKey": None}
        if p.get("name"):
            data[g]["name"] = str(p["name"])
        if p.get("avatarKey"):
            data[g]["avatarKey"] = str(p["avatarKey"])
    result = [data[g] for g in order]
    for i, p in enumerate(result, 1):
        if not p.get("name"):
            p["name"] = f"Profile {i}"
    return result[:5]


def _profiles_from_html(text: str) -> list[dict]:
    profiles: list[dict] = []
    for m in re.finditer(r"/settings/([A-Za-z0-9]{20,40})", text or ""):
        guid = m.group(1)
        chunk = (text or "")[max(0, m.start()-500):m.end()+500]
        nm = re.search(r'"(?:name|profileName|displayName)"\s*:\s*"([^"\\]{1,80})"', chunk)
        profiles.append({"guid": guid, "name": html_lib.unescape(nm.group(1)) if nm else "", "avatarKey": None})
    for m in re.finditer(r'"profileGuid"\s*:\s*"([A-Za-z0-9]{20,40})"', text or ""):
        guid = m.group(1)
        chunk = (text or "")[max(0, m.start()-500):m.end()+500]
        nm = re.search(r'"(?:name|profileName|displayName)"\s*:\s*"([^"\\]{1,80})"', chunk)
        profiles.append({"guid": guid, "name": html_lib.unescape(nm.group(1)) if nm else "", "avatarKey": None})
    return _merge_profiles([], profiles)


def discover_profiles(eng: NetflixDirect) -> list[dict]:
    profiles: list[dict] = []
    try:
        r = eng.s.get(f"{NETFLIX}/ManageProfiles", headers={"Referer": f"{NETFLIX}/account"}, timeout=25, allow_redirects=True)
        eng.referer = r.url
        profiles = _merge_profiles(profiles, _profiles_from_html(r.text or ""))
        for hk, hv in r.headers.items():
            if hk.lower() == "x-netflix-passport.fromorigin.profileguid" and re.fullmatch(r"[A-Za-z0-9]{20,40}", hv or ""):
                profiles = _merge_profiles(profiles, [{"guid": hv, "name": "", "avatarKey": None}])
    except Exception as exc:
        eng.note("profile_http_discovery_error", error=f"{type(exc).__name__}: {exc}")

    if len(profiles) < 2:
        try:
            driver = _new_chromium_driver(performance=True, proxy_id=eng.proxy_id)
            request_ids: set[str] = set()
            try:
                _seed_browser_from_requests(driver, eng.s)
                driver.get(f"{NETFLIX}/ManageProfiles")
                time.sleep(2.2)
                try:
                    dom = driver.execute_script(r'''
                        const out=[]; const seen=new Set();
                        const els=[...document.querySelectorAll('[data-profile-guid],[data-guid],a[href*="/settings/"],a[href*="/profiles/"]')];
                        for(const el of els){
                          const attrs=[el.getAttribute('data-profile-guid'),el.getAttribute('data-guid'),el.getAttribute('href')||''];
                          const joined=attrs.filter(Boolean).join(' ');
                          const m=joined.match(/[A-Za-z0-9]{20,40}/); if(!m||seen.has(m[0])) continue;
                          seen.add(m[0]);
                          const box=el.closest('li,div')||el;
                          const name=(el.innerText||box.innerText||'').trim().split('\n')[0].slice(0,80);
                          out.push({guid:m[0],name:name});
                        }
                        return out;
                    ''') or []
                    profiles = _merge_profiles(profiles, [x for x in dom if isinstance(x, dict)])
                except Exception:
                    pass

                deadline = time.time() + 5
                while time.time() < deadline:
                    try:
                        logs = driver.get_log("performance")
                    except Exception:
                        logs = []
                    for entry in logs:
                        try:
                            msg = json.loads(entry.get("message") or "{}").get("message") or {}
                            method = msg.get("method")
                            params = msg.get("params") or {}
                            if method == "Network.responseReceived":
                                rid = params.get("requestId")
                                response = params.get("response") or {}
                                if rid and "/graphql" in str(response.get("url") or ""):
                                    request_ids.add(rid)
                            elif method == "Network.loadingFinished":
                                rid = params.get("requestId")
                                if rid in request_ids:
                                    obj = _decode_perf_body(driver, rid)
                                    if obj:
                                        profiles = _merge_profiles(profiles, collect_profile_candidates(obj))
                        except Exception:
                            continue
                    time.sleep(0.15)
                profiles = _merge_profiles(profiles, _profiles_from_html(driver.page_source or ""))
                eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or eng.referer)
            finally:
                try:
                    driver.quit()
                except Exception:
                    pass
        except Exception as exc:
            eng.note("profile_browser_discovery_error", error=f"{type(exc).__name__}: {exc}")

    return _merge_profiles([], profiles)


def sync_account_profiles(account_id: str, force: bool = True) -> list[dict]:
    accounts = load_accounts()
    acct = accounts.get(account_id)
    if not acct:
        raise RuntimeError("الحساب المحفوظ غير موجود")
    cached = [x for x in (acct.get("profiles") or []) if isinstance(x, dict)]
    if cached and not force:
        return cached
    eng = engine_from_account(account_id)
    discovered = discover_profiles(eng)
    # Discovery sometimes returns GUIDs without display names. Preserve the known cached name
    # for the same GUID instead of replacing a freshly-created name with "Profile N".
    if discovered:
        cached_by_guid = {str(p.get("guid") or ""): p for p in cached if p.get("guid")}
        repaired = []
        for p in discovered:
            item = dict(p)
            oldp = cached_by_guid.get(str(item.get("guid") or "")) or {}
            if not str(item.get("name") or "").strip() and str(oldp.get("name") or "").strip():
                item["name"] = str(oldp.get("name"))
            if not item.get("avatarKey") and oldp.get("avatarKey"):
                item["avatarKey"] = oldp.get("avatarKey")
            repaired.append(item)
        profiles = _merge_profiles([], repaired)
    else:
        # A temporary discovery failure must not wipe a valid local profile cache.
        profiles = _merge_profiles([], cached)
    save_engine_account(eng, account_id=account_id, status=acct.get("status") or "unknown", profiles=profiles)
    return profiles


def parse_indexed_lines(text: str, pins: bool = False) -> dict[int, str]:
    out: dict[int, str] = {}
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line:
            continue
        m = re.match(r"^([1-5])\s*[-–—:.)]\s*(.+?)\s*$", line)
        if not m:
            raise RuntimeError("اكتب كل سطر مثل: 1- القيمة")
        idx = int(m.group(1))
        val = m.group(2).strip()
        if pins and not re.fullmatch(r"\d{4}", val):
            raise RuntimeError(f"PIN رقم {idx} لازم 4 أرقام")
        if not pins and (not val or len(val) > 50):
            raise RuntimeError(f"اسم البروفايل رقم {idx} غير صالح")
        out[idx] = val
    if not out:
        raise RuntimeError("ما استلمت قيم")
    max_i = max(out)
    if set(out) != set(range(1, max_i + 1)):
        raise RuntimeError("الأرقام لازم تكون متسلسلة من 1 بدون فراغات")
    return out


def batch_profile_names(account_id: str, mapping: dict[int, str]) -> list[dict]:
    eng = engine_from_account(account_id)
    ms = eng.membership_status()
    if not is_active_membership(ms):
        raise RuntimeError(f"الحساب بعده مو Active. MembershipStatus={ms!r}")
    profiles = sync_account_profiles(account_id, force=True)
    target_n = max(mapping)
    while len(profiles) < target_n:
        idx = len(profiles) + 1
        name = mapping[idx]
        guid = add_profile(eng, name)
        profiles.append({"guid": guid or "", "name": name, "avatarKey": "icon26"})
        if not guid:
            save_engine_account(eng, account_id=account_id, status="active", profiles=[p for p in profiles if p.get("guid")])
            profiles = sync_account_profiles(account_id, force=True)
            if len(profiles) < idx:
                raise RuntimeError(f"تم إنشاء البروفايل {idx} لكن ما قدرت أستخرج GUID مالتَه")
    for idx in range(1, target_n + 1):
        p = profiles[idx-1]
        update_profile_name(eng, p, mapping[idx])
        p["name"] = mapping[idx]
    save_engine_account(eng, account_id=account_id, status="active", profiles=profiles)
    return profiles


def single_profile_rename(account_id: str, guid: str, name: str) -> None:
    eng = engine_from_account(account_id)
    profiles = sync_account_profiles(account_id, force=False)
    p = next((x for x in profiles if str(x.get("guid")) == guid), None)
    if not p:
        profiles = sync_account_profiles(account_id, force=True)
        p = next((x for x in profiles if str(x.get("guid")) == guid), None)
    if not p:
        raise RuntimeError("البروفايل ما عاد موجود")
    update_profile_name(eng, p, name)
    p["name"] = name
    save_engine_account(eng, account_id=account_id, status="active", profiles=profiles)


def batch_profile_pins_resilient(chat_id: int, account_id: str, mapping: dict[int, str]) -> list[dict]:
    eng = engine_from_account(account_id)
    ms = eng.membership_status()
    if not is_active_membership(ms):
        raise RuntimeError(f"الحساب بعده مو Active. MembershipStatus={ms!r}")
    acct = load_accounts().get(account_id) or {}
    if str(acct.get("password_status") or "unknown") in {"required", "failed", "pending_activation", "not_set"}:
        raise RuntimeError("لازم تنشئ كلمة مرور الحساب أولاً")
    profiles = sync_account_profiles(account_id, force=False)
    if len(profiles) < max(mapping):
        profiles = sync_account_profiles(account_id, force=True)
    if len(profiles) < max(mapping):
        raise RuntimeError(f"الحساب بي {len(profiles)} بروفايل فقط")
    password_cache: dict[str, str] = {}
    try:
        for idx, pin in mapping.items():
            set_profile_pin_resilient(chat_id, account_id, str(profiles[idx-1]["guid"]), pin, password_cache=password_cache)
    finally:
        password_cache.clear()
    # Refresh cookies/session written by any browser fallback and preserve profile cache.
    eng = engine_from_account(account_id)
    save_engine_account(eng, account_id=account_id, status="active", profiles=profiles)
    return profiles


def single_profile_pin_resilient(chat_id: int, account_id: str, guid: str, pin: str) -> None:
    acct = load_accounts().get(account_id) or {}
    if str(acct.get("password_status") or "unknown") in {"required", "failed", "pending_activation", "not_set"}:
        raise RuntimeError("لازم تنشئ كلمة مرور الحساب أولاً")
    set_profile_pin_resilient(chat_id, account_id, guid, pin)


def pin_batch_worker(chat_id: int, account_id: str, mapping: dict[int, str]) -> None:
    try:
        send_message(chat_id, "🔐 جاري تطبيق PINات البروفايلات...")
        profiles = batch_profile_pins_resilient(chat_id, account_id, mapping)
        send_message(chat_id, f"✅ تم تحديث {len(mapping)} PIN بنجاح.\n" + profile_summary(profiles))
        show_account_menu(chat_id, account_id)
    except Exception as exc:
        send_inline(chat_id, f"❌ تحديث PINات البروفايلات ما كمل: {type(exc).__name__}: {exc}", [[("🔄 حاول مرة ثانية", f"bp:{account_id}"), ("⬅️ الحساب", f"acct:{account_id}")]])
    finally:
        with STATE_LOCK:
            PIN_JOBS.pop(chat_id, None)


def pin_single_worker(chat_id: int, account_id: str, guid: str, pin: str) -> None:
    try:
        send_message(chat_id, "🔐 جاري تحديث PIN...")
        single_profile_pin_resilient(chat_id, account_id, guid, pin)
        send_message(chat_id, "✅ تم تغيير PIN.")
        show_profile_manager(chat_id, account_id, force=False)
    except Exception as exc:
        send_inline(chat_id, f"❌ تغيير PIN ما كمل: {type(exc).__name__}: {exc}", [[("🔄 حاول مرة ثانية", f"sp:{account_id}:{guid}"), ("⬅️ البروفايلات", f"pm:{account_id}")]])
    finally:
        with STATE_LOCK:
            PIN_JOBS.pop(chat_id, None)


def launch_pin_batch(chat_id: int, account_id: str, mapping: dict[int, str]) -> None:
    busy = busy_job_name(chat_id)
    if busy and busy != "تعديل PIN":
        raise RuntimeError(f"أكمل عملية {busy} أولاً")
    with STATE_LOCK:
        old = PIN_JOBS.get(chat_id)
        if old is not None and old.is_alive():
            raise RuntimeError("عملية PIN شغالة حالياً")
        t = threading.Thread(target=pin_batch_worker, args=(chat_id, account_id, mapping), daemon=True)
        PIN_JOBS[chat_id] = t
        t.start()


def launch_pin_single(chat_id: int, account_id: str, guid: str, pin: str) -> None:
    busy = busy_job_name(chat_id)
    if busy and busy != "تعديل PIN":
        raise RuntimeError(f"أكمل عملية {busy} أولاً")
    with STATE_LOCK:
        old = PIN_JOBS.get(chat_id)
        if old is not None and old.is_alive():
            raise RuntimeError("عملية PIN شغالة حالياً")
        t = threading.Thread(target=pin_single_worker, args=(chat_id, account_id, guid, pin), daemon=True)
        PIN_JOBS[chat_id] = t
        t.start()


def single_profile_delete(account_id: str, guid: str) -> None:
    eng = engine_from_account(account_id)
    remove_profile(eng, guid)
    profiles = [p for p in (load_accounts().get(account_id, {}).get("profiles") or []) if str(p.get("guid")) != guid]
    save_engine_account(eng, account_id=account_id, status="active", profiles=profiles)


def profile_summary(profiles: list[dict]) -> str:
    if not profiles:
        return "ما حصلت بروفايلات بعد."
    return "\n".join(f"{i}- {p.get('name') or 'بدون اسم'}" for i, p in enumerate(profiles, 1))


def show_accounts(chat_id: int) -> None:
    accounts = load_accounts()
    if not accounts:
        send_message(chat_id, "ماكو جلسات محفوظة حالياً. اضغط «إنشاء حساب» أو «تسجيل دخول».", keyboard=True)
        return
    rows = []
    for aid, acct in sorted(accounts.items(), key=lambda kv: kv[1].get("created_at", 0)):
        status = str(acct.get("status") or "unknown")
        pstatus = str(acct.get("password_status") or "unknown")
        if status == "active" and pstatus in {"pending_activation", "required", "failed", "not_set"}:
            icon = "🔑"
        else:
            icon = "✅" if status == "active" else ("⏳" if "pending" in status else "⚠️")
        rows.append([(f"{icon} {acct.get('label') or aid}", f"acct:{aid}")])
    send_inline(chat_id, "📂 الجلسات المحفوظة — اختار حساب:", rows)


def show_account_menu(chat_id: int, account_id: str) -> None:
    acct = load_accounts().get(account_id)
    if not acct:
        send_message(chat_id, "الجلسة مو موجودة.")
        return
    with STATE_LOCK:
        CHAT_STATE.setdefault(chat_id, {})["selected_account"] = account_id
    profiles = [p for p in (acct.get("profiles") or []) if isinstance(p, dict)]
    status = str(acct.get("status") or "unknown")
    password_status = str(acct.get("password_status") or "unknown")
    account_proxy_id = acct.get("proxy_id")
    detached_after_activation = bool(acct.get("proxy_detached_after_activation"))
    detached_after_login = bool(acct.get("proxy_detached_after_login"))
    account_proxy_detached = detached_after_activation or detached_after_login
    _cfg = load_proxy_config()
    account_proxy = (_cfg.get("items") or {}).get(account_proxy_id) if account_proxy_id else None
    if detached_after_login:
        account_proxy_text = "استُخدم للتسجيل فقط ثم انفصل ✅ (Direct Railway)"
    elif detached_after_activation:
        account_proxy_text = "مفصول بعد التفعيل ✅ (Direct Railway)"
    else:
        account_proxy_text = proxy_mask(account_proxy) if account_proxy else "مباشر/غير مربوط"

    if status == "logged_in":
        rows = [
            [("🔄 فحص الجلسة", f"check:{account_id}"), ("🗑 حذف الجلسة المحلية", f"ds:{account_id}")],
            [("⬅️ حساباتي", "accounts")],
        ]
        send_inline(
            chat_id,
            f"📁 {acct.get('label') or account_id}\nالحالة: مسجل دخول / العضوية غير Active\n"
            f"MembershipStatus: {acct.get('membership_status')!r}\n\n"
            "الجلسة محفوظة، لكن إدارة البروفايلات تحتاج عضوية Active.",
            rows,
        )
        return

    if status == "active" and password_status in {"pending_activation", "required", "failed", "not_set"}:
        rows = [
            [("🔑 إنشاء كلمة المرور", f"setpw:{account_id}"), ("🔄 فحص الجلسة", f"check:{account_id}")],
            [("🗑 حذف الجلسة المحلية", f"ds:{account_id}"), ("⬅️ حساباتي", "accounts")],
        ]
        send_inline(
            chat_id,
            f"📁 {acct.get('label') or account_id}\nالحالة: {status}\n"
            "🔐 كلمة المرور: مطلوبة قبل إدارة البروفايلات\n\n"
            "بعد إنشائها راح تظهر أزرار الأسماء والـPIN وإدارة البروفايلات.",
            rows,
        )
        return

    # Pending signup sessions must not expose profile/password actions that are guaranteed to fail.
    # This also prevents the owner from accidentally opening a second OTP browser while the direct
    # Telegram OTP worker is still alive.
    if status != "active":
        with STATE_LOCK:
            main_th = ACTIVE_JOBS.get(chat_id)
            direct_waiting = bool(
                main_th and main_th.is_alive()
                and ACTIVE_JOB_ACCOUNTS.get(chat_id) == account_id
                and not _job_cancelled(chat_id)
            )
        rows = [[("✅ فحص التفعيل", f"verified:{account_id}")]]
        if direct_waiting:
            rows.append([("🛑 إلغاء عملية التسجيل", f"cancelacct:{account_id}")])
        else:
            rows.append([("🖥 فتح Netflix يدوياً", f"otpview:{account_id}"), ("📱 تغيير الرقم", f"cp:{account_id}")])
        rows.append([("🗑 حذف الجلسة المحلية", f"ds:{account_id}"), ("⬅️ حساباتي", "accounts")])
        pw_label = "مضافة" if password_status == "set" else ("غير معروف/حساب قديم" if password_status == "unknown" else password_status)
        note = "\n⏳ التسجيل الحالي ينتظر OTP/الموافقة داخل Telegram." if direct_waiting else ""
        send_inline(
            chat_id,
            f"📁 {acct.get('label') or account_id}\nالحالة: {status}\n🔐 كلمة المرور: {pw_label}\n🌐 البروكسي: {account_proxy_text}\nالبروفايلات المحفوظة: {len(profiles)}{note}",
            rows,
        )
        return

    rows = [
        [("👤 أسماء البروفايلات", f"bn:{account_id}"), ("🔐 رموز البروفايلات", f"bp:{account_id}")],
        [("⚙️ إدارة البروفايلات", f"pm:{account_id}"), ("➕ إضافة بروفايل", f"ap:{account_id}")],
        [("🔄 تحديث البروفايلات", f"rp:{account_id}"), ("🔄 فحص الجلسة", f"check:{account_id}")],
        [("🔑 تغيير كلمة المرور", f"pw:{account_id}"), ("🗑 حذف الجلسة المحلية", f"ds:{account_id}")],
        [("⬅️ حساباتي", "accounts")],
    ]
    pw_label = "مضافة" if password_status == "set" else ("غير معروف/حساب قديم" if password_status == "unknown" else password_status)
    send_inline(
        chat_id,
        f"📁 {acct.get('label') or account_id}\nالحالة: {status}\n🔐 كلمة المرور: {pw_label}\n🌐 البروكسي: {account_proxy_text}\nالبروفايلات المحفوظة: {len(profiles)}",
        rows,
    )


def show_profile_manager(chat_id: int, account_id: str, force: bool = False) -> None:
    profiles = sync_account_profiles(account_id, force=force)
    if not profiles:
        send_inline(chat_id, "ما قدرت أستخرج البروفايلات من الجلسة بعد. تكدر تحدث أو تنشئ بروفايل جديد.", [
            [("🔄 تحديث", f"rp:{account_id}"), ("➕ إضافة بروفايل", f"ap:{account_id}")],
            [("⬅️ رجوع للحساب", f"acct:{account_id}")],
        ])
        return
    rows = [[(f"{i}️⃣ {p.get('name') or 'Profile'}", f"p:{account_id}:{i-1}")] for i, p in enumerate(profiles, 1)]
    rows.append([("➕ إضافة بروفايل", f"ap:{account_id}"), ("🔄 تحديث", f"rp:{account_id}")])
    rows.append([("⬅️ رجوع للحساب", f"acct:{account_id}")])
    send_inline(chat_id, "⚙️ اختار البروفايل:", rows)


def show_one_profile(chat_id: int, account_id: str, index: int) -> None:
    profiles = sync_account_profiles(account_id, force=False)
    if index < 0 or index >= len(profiles):
        send_message(chat_id, "رقم البروفايل تغير، اضغط تحديث.")
        return
    p = profiles[index]
    guid = str(p.get("guid") or "")
    rows = [
        [("✏️ تغيير الاسم", f"rn:{account_id}:{guid}"), ("🔐 تغيير PIN", f"sp:{account_id}:{guid}")],
        [("🗑 حذف البروفايل", f"dp:{account_id}:{guid}"), ("⬅️ رجوع", f"pm:{account_id}")],
    ]
    send_inline(chat_id, f"👤 {p.get('name') or 'Profile'}\nرقم البروفايل: {index+1}", rows)


def clear_input_state(chat_id: int) -> None:
    with STATE_LOCK:
        st = CHAT_STATE.setdefault(chat_id, {})
        for k in list(st.keys()):
            if k.startswith("awaiting_") or k in (
                "target_account", "target_guid", "otp_account", "payment_otp_value",
                "login_email_value", "login_otp_value", "login_password_value", "login_method_value"
            ):
                st.pop(k, None)


def cleanup_transient_sessions(chat_id: int) -> None:
    """Reset only transient/local signup state; preserve active Netflix accounts and proxy settings.

    This is intentionally stronger than the normal Cancel button: it cancels waits, tombstones
    pending account sessions so an old worker cannot resurrect them, restarts the local proxy
    relay, clears ephemeral password cache, and removes only our temporary diagnostics.
    """
    with STATE_LOCK:
        active_pending_id = str(ACTIVE_JOB_ACCOUNTS.get(chat_id) or "")
        if active_pending_id:
            DELETED_ACCOUNT_IDS.add(active_pending_id)

    request_main_job_cancel(chat_id)
    request_login_cancel(chat_id)
    with WAIT_COND:
        live = CHAT_STATE.setdefault(chat_id, {})
        if live.get("awaiting_change_phone") or (chat_id in CHANGE_PHONE_JOBS and CHANGE_PHONE_JOBS[chat_id].is_alive()):
            live["change_phone_value"] = "__CANCEL__"
        if live.get("awaiting_secret"):
            live["secret_value"] = "__CANCEL__"
        if live.get("awaiting_payment_otp"):
            live["payment_otp_value"] = "__CANCEL__"
        if live.get("awaiting_membership_confirmation"):
            live["membership_confirm_value"] = "NO"
        for key in list(live.keys()):
            if key.startswith("awaiting_"):
                live[key] = False
        live.pop("deferred_change_phone", None)
        WAIT_COND.notify_all()

    main_done = _join_cancelled_main_job(chat_id, timeout=2.0)
    login_done = _join_cancelled_login_job(chat_id, timeout=2.0)

    accounts = load_accounts()
    removed_pending: list[str] = []
    for aid, acct in list(accounts.items()):
        if str((acct or {}).get("status") or "").lower() != "active":
            removed_pending.append(aid)
            with STATE_LOCK:
                DELETED_ACCOUNT_IDS.add(aid)
            accounts.pop(aid, None)
            clear_cached_account_password(aid)
    if removed_pending:
        save_accounts(accounts)

    with STATE_LOCK:
        CHAT_STATE[chat_id] = {}
        EPHEMERAL_PASSWORDS.clear()
        # Drop only completed thread registrations. Alive workers remain registered until their
        # own finally blocks exit, so cleanup never lies about a still-closing network call.
        for jobs in (CHANGE_PHONE_JOBS, PASSWORD_JOBS, PIN_JOBS, MANUAL_BROWSER_JOBS, LOGIN_JOBS):
            th = jobs.get(chat_id)
            if th is not None and not th.is_alive():
                jobs.pop(chat_id, None)

    # Force the next Chromium proxy use to create a fresh local relay/tunnel while keeping the
    # user's saved upstream proxy credentials/configuration untouched.
    with PROXY_LOCK:
        _stop_proxy_relay_locked()

    removed_tmp = 0
    for pattern in ("netflix_fast_v22_*", "v22_page_diag_*"):
        for p in TMPDIR.glob(pattern):
            try:
                if p.is_file():
                    p.unlink()
                    removed_tmp += 1
            except Exception:
                pass

    active_left = sum(1 for a in accounts.values() if str((a or {}).get("status") or "").lower() == "active")
    closing_note = "" if (main_done and login_done) else "\n⏳ أكو طلب شبكة قديم قيد الإغلاق؛ تم إلغاؤه ومنعه من إعادة الجلسة، وقد يحتاج ثوانٍ قليلة حتى ينتهي فعلياً."
    send_message(
        chat_id,
        "🧹 تم تنضيف الجلسات المؤقتة.\n"
        f"• حذفت جلسات pending/الفاشلة: {len(removed_pending)}\n"
        f"• الحسابات Active المحفوظة بقيت بدون حذف: {active_left}\n"
        "• صفّرت حالات OTP/رقم/تسجيل الدخول المؤقتة وكاش كلمات المرور\n"
        "• أعدت تهيئة نفق البروكسي المحلي للمحاولة القادمة\n"
        f"• حذفت ملفات تشخيص مؤقتة: {removed_tmp}\n"
        "✅ إعداد البروكسي نفسه ما انحذف." + closing_note,
        keyboard=True,
    )


def _arabic_netflix_url(url: str) -> str:
    """Route known visible Netflix UI pages through /iq, preserving query/fragment."""
    try:
        u = urlparse(str(url or ""))
        if u.netloc.lower() not in {"netflix.com", "www.netflix.com"}:
            return str(url or "")
        path = u.path or "/"
        if path.lower().startswith("/epr") or path.lower().startswith("/iq/") or path.lower() == "/iq":
            return str(url or "")
        visible_roots = ("/signup", "/login", "/password", "/manageprofiles", "/settings", "/account", "/browse", "/profiles")
        if not any(path.lower().startswith(root) for root in visible_roots):
            return str(url or "")
        from urllib.parse import urlunparse
        return urlunparse((u.scheme or "https", u.netloc or "www.netflix.com", "/iq" + path, u.params, u.query, u.fragment))
    except Exception:
        return str(url or "")


def _new_chromium_driver_interactive(proxy_id: Optional[str] = None, *, force_proxy: bool = False):
    try:
        from selenium import webdriver
        from selenium.webdriver.chrome.options import Options
        from selenium.webdriver.chrome.service import Service
    except Exception as exc:
        raise RuntimeError(f"Selenium غير متوفر: {exc}")
    if not os.environ.get("DISPLAY"):
        raise RuntimeError("ماكو DISPLAY. شغل VNC/X11 واضبط DISPLAY أولاً حتى تفتح صفحة Netflix اليدوية.")
    chromium = shutil.which("chromium-browser") or shutil.which("chromium")
    chromedriver = shutil.which("chromedriver")
    if not chromium or not chromedriver:
        raise RuntimeError("Chromium/chromedriver غير موجودين")
    opts = Options()
    opts.binary_location = chromium
    for arg in (
        "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
        "--window-size=430,900", "--lang=ar-IQ", "--disable-extensions",
        "--disable-sync", "--no-first-run", "--no-default-browser-check",
    ):
        opts.add_argument(arg)
    opts.add_experimental_option("prefs", {"intl.accept_languages": "ar-IQ,ar,en-US,en"})
    chrome_proxy = chrome_proxy_server(proxy_id, require_enabled=not force_proxy)
    if chrome_proxy:
        opts.add_argument(f"--proxy-server={chrome_proxy}")
    driver = webdriver.Chrome(service=Service(chromedriver), options=opts)
    _configure_driver_arabic(driver)
    return driver


def manual_browser_worker(chat_id: int, account_id: str, target_url: str, purpose: str) -> None:
    driver = None
    try:
        eng = engine_from_account(account_id)
        driver = _new_chromium_driver_interactive(proxy_id=eng.proxy_id, force_proxy=bool(eng.proxy_id))
        try:
            driver.set_page_load_timeout(45)
        except Exception:
            pass

        # Browser is alive on Railway Xvfb. Send noVNC before slow Netflix navigation.
        remote = railway_browser_url()
        if purpose == "otp":
            if remote:
                send_url_inline(
                    chat_id,
                    "🌐 المتصفح صار جاهز على Railway. جاري تحميل نفس جلسة Netflix بالداخل.",
                    "🌐 فتح المتصفح",
                    remote,
                )
            else:
                send_message(chat_id, "⚠️ المتصفح اشتغل، لكن رابط Railway العام غير متوفر داخل الخدمة.")
        else:
            if remote:
                send_url_inline(chat_id, "🌐 افتح نافذة تغيير كلمة المرور من هنا.", "🌐 فتح المتصفح", remote)

        try:
            _seed_browser_from_requests(driver, eng.s)
        except Exception as exc:
            send_message(chat_id, f"⚠️ المتصفح فتح، لكن تهيئة كوكيز الجلسة تأخرت/فشلت: {scrub_sensitive_text(str(exc))}")

        try:
            driver.get(_arabic_netflix_url(target_url))
        except Exception as exc:
            # Keep browser alive so the user can still inspect/retry from noVNC.
            send_message(chat_id, f"⚠️ صفحة Netflix ما اكتمل تحميلها تلقائياً، لكن نافذة المتصفح باقية مفتوحة: {scrub_sensitive_text(str(exc))}")

        otp_prompted_once = False
        otp_last_error = None

        if purpose == "otp":
            body_now = _body_text_lower(driver)
            if any(x in body_now for x in ("choose any plan", "choose a plan", "most popular", "premium", "standard")):
                send_inline(
                    chat_id,
                    "⚠️ Netflix رجع الجلسة إلى اختيار الخطة بدل شاشة OTP. اضغط تغيير رقم الهاتف وأرسل الرقم (حتى نفس الرقم إذا تريد)؛ V22.14 راح يعيد المسار تلقائياً إلى شاشة OTP، وبعدها استخدم تعبئة OTP عبر البوت.",
                    [[("📱 تغيير رقم الهاتف", f"cp:{account_id}")], [("⬅️ الحساب", f"acct:{account_id}")]],
                )
            elif _visible_otp_input(driver) is not None:
                otp = wait_for_payment_otp(chat_id, account_id, timeout=300)
                otp_prompted_once = True
                if otp is None:
                    send_message(chat_id, "⏸ تم إلغاء/انتهاء انتظار OTP. المتصفح راح ينغلق بدون إرسال أي عملية دفع.")
                    return
                _fill_visible_payment_otp_only(driver, otp)
                # Drop the local reference as soon as the browser field is filled.
                otp = None
                send_message(chat_id, "✅ تم تعبئة كود OTP داخل خانة Netflix بنفس الجلسة.")
                if not click_start_membership_after_confirmation(driver, chat_id, account_id):
                    show_account_menu(chat_id, account_id)
                    return
            else:
                send_message(chat_id, "🖥 نافذة Netflix مفتوحة بنفس الجلسة، لكن خانة OTP مو ظاهرة حالياً. افتح المتصفح وتأكد من الصفحة؛ البوت يراقب التفعيل.")
        else:
            send_message(chat_id, "🖥 نافذة تغيير كلمة المرور مفتوحة بنفس الجلسة. كملها يدوياً؛ البوت ما يخزن كلمة المرور.")

        deadline = time.time() + 900
        last_check = 0.0
        while time.time() < deadline:
            time.sleep(1.5)
            if _account_deleted(account_id):
                return
            try:
                eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or target_url)
                acct = load_accounts().get(account_id, {})
                save_engine_account(eng, account_id=account_id, status=acct.get("status") or "pending_otp", profiles=acct.get("profiles") or [])
            except Exception:
                break

            if purpose == "otp":
                # If Start Membership was approved but Netflix rejects/expires the OTP,
                # ask for a fresh OTP and require a fresh explicit approval before retrying.
                err_state = _otp_error_state(driver)
                if err_state and err_state != otp_last_error and _visible_otp_input(driver) is not None:
                    otp_last_error = err_state
                    msg = "❌ Netflix يقول إن الكود غير صحيح." if err_state == "invalid" else "⌛ Netflix يقول إن صلاحية الكود انتهت."
                    send_message(chat_id, msg + " دز الكود الجديد حتى أعبّيه بالخانة.")
                    otp = wait_for_payment_otp(chat_id, account_id, timeout=300)
                    if otp is not None:
                        _fill_visible_payment_otp_only(driver, otp)
                        otp = None
                        send_message(chat_id, "✅ تم تحديث خانة OTP بالكود الجديد.")
                        if not click_start_membership_after_confirmation(driver, chat_id, account_id):
                            show_account_menu(chat_id, account_id)
                            return
                        otp_last_error = None
                    else:
                        send_message(chat_id, "⏸ ما استلمت OTP جديد؛ ما تم تنفيذ أي تأكيد دفع.")
                        return

                if time.time() - last_check >= 3:
                    last_check = time.time()
                    ms = eng.membership_status()
                    if is_active_membership(ms):
                        before = load_accounts().get(account_id, {})
                        prior_status = str(before.get("status") or "unknown")
                        prior_pstatus = str(before.get("password_status") or "unknown")
                        save_engine_account(eng, account_id=account_id, status="active", profiles=before.get("profiles") or [])
                        changes = {"membership_status": ms}
                        if prior_pstatus == "unknown" and prior_status != "active":
                            changes["password_status"] = "required"
                        update_account_record(account_id, **changes)
                        old_proxy = detach_proxy_after_activation(eng, account_id)
                        proxy_note = "\n🌐 تم فصل بروكسي التسجيل عن هذا الحساب؛ العمليات التالية تستخدم اتصال Railway المباشر." if old_proxy else ""
                        send_message(chat_id, f"✅ تم تفعيل العضوية بعد موافقتك من Telegram. MembershipStatus={ms}\nالجلسة انحفظت. الخطوة التالية الإلزامية: إنشاء كلمة مرور الحساب.{proxy_note}")
                        if not require_password_after_activation(chat_id, account_id):
                            show_account_menu(chat_id, account_id)
                        break
    except Exception as exc:
        send_message(chat_id, f"⚠️ ما قدرت أفتح/أعبّي نافذة OTP: {scrub_sensitive_text(str(exc))}")
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            st["awaiting_payment_otp"] = False
            st.pop("otp_account", None)
            st.pop("payment_otp_value", None)
            st["awaiting_membership_confirmation"] = False
            st.pop("membership_confirm_account", None)
            st.pop("membership_confirm_value", None)
            WAIT_COND.notify_all()
        with STATE_LOCK:
            MANUAL_BROWSER_JOBS.pop(chat_id, None)


def launch_manual_browser(chat_id: int, account_id: str, target_url: str, purpose: str) -> None:
    # Immediate acknowledgement: Selenium/Netflix can take several seconds on Railway.
    with STATE_LOCK:
        old = MANUAL_BROWSER_JOBS.get(chat_id)
        if old is not None and old.is_alive():
            send_message(chat_id, "⏳ نافذة المتصفح اليدوية قيد التجهيز/مفتوحة حالياً. انتظر زر 🌐 فتح المتصفح بدل الضغط مرة ثانية.")
            return
        th = threading.Thread(
            target=manual_browser_worker,
            args=(chat_id, account_id, target_url, purpose),
            daemon=True,
        )
        MANUAL_BROWSER_JOBS[chat_id] = th
    if purpose == "otp":
        send_message(chat_id, "⏳ وصلت مرحلة OTP. جاري تجهيز نفس جلسة Netflix... أول ما تظهر الخانة راح أطلب منك الكود تلقائياً، وبعدها أعرض موافق/رفض قبل Start Membership.")
    else:
        send_message(chat_id, "⏳ جاري تجهيز نافذة المتصفح على Railway...")
    th.start()



def _browser_element_text(el) -> str:
    parts = []
    for attr in ("innerText", "textContent", "value", "aria-label", "data-uia", "name", "id"):
        try:
            value = el.get_attribute(attr)
        except Exception:
            value = None
        if value:
            parts.append(str(value))
    try:
        if el.text:
            parts.append(str(el.text))
    except Exception:
        pass
    return " ".join(parts).strip().lower()


def _find_visible_phone_input(driver):
    selectors = (
        'input[type="tel"]',
        'input[name="phoneNumber"]',
        'input[name*="phone"]',
        'input[id*="phone"]',
        'input[data-uia*="phone"]',
    )
    for selector in selectors:
        try:
            for el in driver.find_elements("css selector", selector):
                if el.is_displayed() and el.is_enabled():
                    return el
        except Exception:
            continue
    return None


def _click_button_like(driver, needles: tuple[str, ...]) -> bool:
    try:
        els = driver.find_elements("css selector", 'button,a,[role="button"],input[type="button"],input[type="submit"]')
    except Exception:
        els = []
    for el in els:
        try:
            if not el.is_displayed() or not el.is_enabled():
                continue
            hay = _browser_element_text(el)
            if not any(n in hay for n in needles):
                continue
            driver.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
            time.sleep(0.15)
            try:
                el.click()
            except Exception:
                driver.execute_script("arguments[0].click();", el)
            return True
        except Exception:
            continue
    return False


def _visible_elements(driver, selector: str):
    out = []
    try:
        for el in driver.find_elements("css selector", selector):
            try:
                if el.is_displayed() and el.is_enabled():
                    out.append(el)
            except Exception:
                continue
    except Exception:
        pass
    return out


def _body_text_lower(driver) -> str:
    try:
        return str(driver.find_element("tag name", "body").text or "").strip().lower()
    except Exception:
        try:
            return str(driver.page_source or "").lower()
        except Exception:
            return ""


def _find_visible_password_inputs(driver):
    return _visible_elements(driver, 'input[type="password"]')


def _has_current_password_field(driver) -> bool:
    """Detect the change-password form without reading any password value."""
    for el in _find_visible_password_inputs(driver):
        meta = _input_meta(el)
        if any(x in meta for x in ("current", "old", "existing", "current-password")):
            return True
    return False


def _input_meta(el) -> str:
    vals = []
    for attr in ("name", "id", "autocomplete", "placeholder", "aria-label", "data-uia", "maxlength"):
        try:
            v = el.get_attribute(attr)
        except Exception:
            v = None
        if v:
            vals.append(str(v))
    return " ".join(vals).lower()


def _safe_fill(el, value: str) -> None:
    try:
        el.clear()
    except Exception:
        pass
    try:
        el.send_keys(value)
    except Exception as exc:
        raise RuntimeError(f"تعذر تعبئة الحقل: {exc}")


def _wait_page(driver, predicate, timeout: float = 15.0, step: float = 0.12) -> bool:
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            if predicate():
                return True
        except Exception:
            pass
        time.sleep(step)
    return False


def _password_form_fill(driver, new_password: str, old_password: Optional[str] = None) -> None:
    pw = _find_visible_password_inputs(driver)
    if not pw:
        raise RuntimeError("ما حصلت حقول كلمة المرور بصفحة Netflix")

    current = []
    new_fields = []
    confirm = []
    unknown = []
    for el in pw:
        meta = _input_meta(el)
        if any(x in meta for x in ("current", "old", "existing", "current-password")):
            current.append(el)
        elif any(x in meta for x in ("confirm", "reenter", "re-enter", "repeat", "verify")):
            confirm.append(el)
        elif any(x in meta for x in ("new", "new-password")):
            new_fields.append(el)
        else:
            unknown.append(el)

    # Netflix page variants differ. Infer only when metadata is missing.
    if current and not old_password:
        raise RuntimeError("CURRENT_PASSWORD_REQUIRED")
    for el in current:
        _safe_fill(el, str(old_password or ""))
    for el in new_fields:
        _safe_fill(el, new_password)
    for el in confirm:
        _safe_fill(el, new_password)

    if unknown:
        if old_password and not current and not new_fields and not confirm and len(unknown) >= 2:
            # Metadata-free change-password form: first=current, remaining=new/confirm.
            _safe_fill(unknown[0], old_password)
            for el in unknown[1:]:
                _safe_fill(el, new_password)
        else:
            # Passwordless/add-password pages commonly expose one or two new-password fields.
            for el in unknown:
                _safe_fill(el, new_password)


def set_or_change_password_browser(account_id: str, new_password: str,
                                   old_password: Optional[str] = None) -> None:
    new_password = validate_account_password(new_password)
    if old_password is not None:
        old_password = validate_account_password(old_password)
    eng = engine_from_account(account_id)
    driver = _new_chromium_driver(performance=False, proxy_id=eng.proxy_id)
    try:
        _seed_browser_from_requests(driver, eng.s)
        driver.get(f"{NETFLIX}/password")
        _wait_page(driver, lambda: bool(_find_visible_password_inputs(driver)) or "sign in" in _body_text_lower(driver), timeout=15)
        body0 = _body_text_lower(driver)
        if "/login" in str(driver.current_url or "").lower() or ("sign in" in body0 and not _find_visible_password_inputs(driver)):
            raise RuntimeError("جلسة Netflix انتهت وتحتاج تسجيل دخول جديد")

        _password_form_fill(driver, new_password, old_password)
        clicked = _click_button_like(driver, (
            "save", "change password", "update password", "set password", "create password",
            "next", "continue", "submit", "حفظ", "تغيير كلمة المرور", "تعيين كلمة المرور", "متابعة"
        ))
        if not clicked:
            try:
                clicked = bool(driver.execute_script(
                    "const f=document.querySelector('form'); "
                    "if(f){f.requestSubmit?f.requestSubmit():f.submit(); return true;} return false;"
                ))
            except Exception:
                clicked = False
        if not clicked:
            raise RuntimeError("ما حصلت زر حفظ كلمة المرور")

        def explicit_error() -> Optional[str]:
            body = _body_text_lower(driver)
            if any(x in body for x in (
                "incorrect password", "wrong password", "current password is incorrect",
                "كلمة المرور غير صحيحة", "كلمة السر غير صحيحة"
            )):
                return "كلمة المرور الحالية غير صحيحة"
            if any(x in body for x in (
                "password must", "password should", "too short", "too long",
                "كلمة المرور يجب", "كلمة السر يجب"
            )):
                return "Netflix رفض صيغة كلمة المرور"
            if any(x in body for x in ("something went wrong", "try again", "حدث خطأ", "حاول مرة أخرى")) and _find_visible_password_inputs(driver):
                return "Netflix رفض تغيير كلمة المرور؛ الصفحة ما زالت تعرض خطأ"
            return None

        def done() -> bool:
            url = str(driver.current_url or "").lower()
            body = _body_text_lower(driver)
            if any(x in body for x in (
                "password updated", "password changed", "password has been changed", "password saved",
                "password created", "password set",
                "تم تغيير كلمة المرور", "تم تحديث كلمة المرور", "تم حفظ كلمة المرور", "تم تعيين كلمة المرور"
            )):
                return True
            if "/password" not in url and "/login" not in url:
                return True
            if not _find_visible_password_inputs(driver):
                return True
            # On initial password creation, Netflix can keep /password but switch the form
            # to a normal change-password page.  That transition itself confirms creation.
            if old_password is None and _has_current_password_field(driver):
                return True
            return False

        confirmed = _wait_page(driver, done, timeout=24)
        err = explicit_error()
        if err:
            raise RuntimeError(err)

        if not confirmed and old_password is None:
            # Some Netflix variants do not render a success toast/redirect. Verify by navigating
            # away and reopening /password: a visible current-password field means the first
            # password was accepted. This avoids asking the owner to submit the same password twice.
            try:
                driver.get(f"{NETFLIX}/account")
                _wait_page(driver, lambda: "/login" in str(driver.current_url or "").lower() or bool(_body_text_lower(driver)), timeout=8)
                if "/login" not in str(driver.current_url or "").lower():
                    driver.get(f"{NETFLIX}/password")
                    _wait_page(driver, lambda: bool(_find_visible_password_inputs(driver)), timeout=12)
                    confirmed = _has_current_password_field(driver)
            except Exception:
                confirmed = False

        if not confirmed:
            err = explicit_error()
            if err:
                raise RuntimeError(err)
            raise RuntimeError("Netflix ما أكد حفظ كلمة المرور")

        eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or f"{NETFLIX}/account")
        acct = load_accounts().get(account_id) or {}
        save_engine_account(eng, account_id=account_id, status=acct.get("status") or "active", profiles=acct.get("profiles") or [])
        update_account_record(account_id, password_status="set", password_set_at=time.time(), password_error=None)
    finally:
        try:
            driver.quit()
        except Exception:
            pass


def _choose_password_verification(driver) -> bool:
    # Strongly prefer the password branch and deliberately never click SMS/email choices.
    return _click_button_like(driver, (
        "use password", "password", "enter password", "verify with password",
        "كلمة المرور", "استخدام كلمة المرور", "أدخل كلمة المرور"
    ))


def _find_pin_inputs(driver):
    candidates = []
    selectors = (
        'input[name*="pin" i]', 'input[id*="pin" i]', 'input[data-uia*="pin" i]',
        'input[inputmode="numeric"]', 'input[type="tel"]',
        'input[type="password"][maxlength="4"]', 'input[type="password"][maxlength="1"]'
    )
    seen = set()
    for selector in selectors:
        for el in _visible_elements(driver, selector):
            key = id(el)
            if key in seen:
                continue
            seen.add(key)
            meta = _input_meta(el)
            try:
                ml = int(el.get_attribute("maxlength") or 0)
            except Exception:
                ml = 0
            if "phone" in meta or "otp" in meta or "code" in meta and "pin" not in meta:
                continue
            if "pin" in meta or ml in (1, 4) or "numeric" in meta:
                candidates.append(el)
    return candidates


def _fill_pin_fields(driver, pin: str) -> bool:
    fields = _find_pin_inputs(driver)
    if not fields:
        return False
    if len(fields) >= 4:
        one_char = []
        for el in fields:
            try:
                ml = int(el.get_attribute("maxlength") or 0)
            except Exception:
                ml = 0
            if ml == 1:
                one_char.append(el)
        if len(one_char) >= 4:
            for el, digit in zip(one_char[:4], pin):
                _safe_fill(el, digit)
            return True
    _safe_fill(fields[0], pin)
    # Some variants show a confirmation field.
    if len(fields) >= 2:
        try:
            meta2 = _input_meta(fields[1])
            if any(x in meta2 for x in ("confirm", "repeat", "reenter", "re-enter")):
                _safe_fill(fields[1], pin)
        except Exception:
            pass
    return True


def profile_pin_browser_fallback(chat_id: int, account_id: str, guid: str, pin: str,
                                 password_cache: Optional[dict[str, str]] = None) -> None:
    if not re.fullmatch(r"\d{4}", pin or ""):
        raise RuntimeError("PIN لازم يكون 4 أرقام")
    eng = engine_from_account(account_id)
    driver = _new_chromium_driver(performance=False, proxy_id=eng.proxy_id)
    session_password: Optional[str] = None

    def wrong_password_visible() -> bool:
        body = _body_text_lower(driver)
        return any(x in body for x in (
            "incorrect password", "wrong password", "current password is incorrect",
            "كلمة المرور غير صحيحة", "كلمة السر غير صحيحة"
        ))

    def refresh_engine_from_browser() -> None:
        eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or f"{NETFLIX}/settings/lock/{guid}")

    def try_direct_after_browser_auth() -> bool:
        """Fresh password verification can authorize the GraphQL PIN mutation even when UI routing changes."""
        try:
            refresh_engine_from_browser()
            update_profile_pin(eng, guid, pin)
            acct = load_accounts().get(account_id) or {}
            save_engine_account(eng, account_id=account_id, status=acct.get("status") or "active", profiles=acct.get("profiles") or [])
            update_account_record(account_id, pin_password_auth_at=time.time())
            return True
        except Exception:
            return False

    try:
        _seed_browser_from_requests(driver, eng.s)
        driver.get(f"{NETFLIX}/settings/lock/{guid}")
        _wait_page(driver, lambda: bool(_body_text_lower(driver)) or bool(_find_pin_inputs(driver)) or bool(_find_visible_password_inputs(driver)), timeout=10)

        # Netflix has used both /settings/lock/<guid> and /settings/lock/pinentry/<guid>.
        # Walk only explicit profile-lock/password states; never choose SMS/email verification.
        pinentry_visits = 0
        password_verified = False
        for _ in range(10):
            if _find_pin_inputs(driver):
                break

            pw_inputs = _find_visible_password_inputs(driver)
            if pw_inputs:
                password = session_password or (password_cache or {}).get("value") or get_cached_account_password(account_id)
                if not password:
                    password = wait_for_secret(
                        chat_id, account_id, "profile_auth_password",
                        "🔐 Netflix طلب تحقق قبل تعديل PIN. دز كلمة مرور الحساب الحالية.\n\nالبوت يحذف رسالة كلمة المرور مباشرة وما يخزنها بملف.",
                        timeout=300, back_callback=f"acct:{account_id}"
                    )
                    if password is None:
                        raise RuntimeError("تم إلغاء تحقق كلمة المرور")
                    password = validate_account_password(password)
                session_password = password
                if password_cache is not None:
                    password_cache["value"] = password

                for el in pw_inputs:
                    _safe_fill(el, password)
                clicked = _click_button_like(driver, (
                    "continue", "next", "verify", "submit", "done",
                    "متابعة", "التالي", "تحقق", "تأكيد"
                ))
                if not clicked:
                    try:
                        clicked = bool(driver.execute_script(
                            "const f=document.querySelector('form'); "
                            "if(f){f.requestSubmit?f.requestSubmit():f.submit(); return true;} return false;"
                        ))
                    except Exception:
                        clicked = False
                if not clicked:
                    raise RuntimeError("ما حصلت زر متابعة تحقق كلمة المرور")

                _wait_page(
                    driver,
                    lambda: wrong_password_visible() or bool(_find_pin_inputs(driver)) or not bool(_find_visible_password_inputs(driver)),
                    timeout=12,
                )
                if wrong_password_visible():
                    session_password = None
                    clear_cached_account_password(account_id)
                    if password_cache is not None:
                        password_cache.pop("value", None)
                    send_message(chat_id, "⚠️ كلمة المرور ما انقبلت. راح أطلب الحالية مرة ثانية بدل ما أفشل العملية.")
                    time.sleep(0.5)
                    continue

                password_verified = True
                refresh_engine_from_browser()
                if _find_pin_inputs(driver):
                    break

                # V22.14 fix: after password verification Netflix can leave us on the verifier
                # instead of automatically routing to the PIN form. Explicitly open pinentry now.
                try:
                    driver.get(f"{NETFLIX}/settings/lock/pinentry/{guid}")
                    pinentry_visits += 1
                    _wait_page(driver, lambda: bool(_find_pin_inputs(driver)) or bool(_find_visible_password_inputs(driver)) or bool(_body_text_lower(driver)), timeout=10)
                except Exception:
                    pass
                continue

            body = _body_text_lower(driver)
            if any(x in body for x in ("email", "sms", "text message", "البريد", "رسالة نصية", "رقم الهاتف")):
                if not _choose_password_verification(driver):
                    # If password verification just succeeded, the fresh auth cookies may already
                    # be enough for the direct mutation even if Netflix rendered a stale chooser.
                    if password_verified and try_direct_after_browser_auth():
                        return
                    raise RuntimeError("Netflix طلب تحقق، لكن خيار كلمة المرور ما ظهر بهذه الجلسة")
                time.sleep(0.8)
                continue

            if _choose_password_verification(driver):
                time.sleep(0.8)
                continue

            if pinentry_visits < 2:
                try:
                    driver.get(f"{NETFLIX}/settings/lock/pinentry/{guid}")
                    pinentry_visits += 1
                    time.sleep(0.9)
                    continue
                except Exception:
                    pass
            time.sleep(0.5)

        if not _find_pin_inputs(driver):
            # Last recovery: password auth may have succeeded even though the new Netflix UI no
            # longer exposes the PIN input at the captured route. Reuse that authenticated session
            # for the same GraphQL mutation before declaring failure.
            if password_verified and try_direct_after_browser_auth():
                return
            _send_v22_browser_diagnostic(chat_id, driver, "pin_entry_not_found_after_password")
            raise RuntimeError("ما حصلت حقل PIN بعد تحقق كلمة المرور")

        if not _fill_pin_fields(driver, pin):
            raise RuntimeError("ما حصلت حقل PIN بعد تحقق كلمة المرور")
        clicked = _click_button_like(driver, (
            "save", "continue", "next", "submit", "done", "set pin", "change pin",
            "حفظ", "متابعة", "التالي", "تأكيد", "حفظ الرمز"
        ))
        if not clicked:
            try:
                clicked = bool(driver.execute_script(
                    "const f=document.querySelector('form'); "
                    "if(f){f.requestSubmit?f.requestSubmit():f.submit(); return true;} return false;"
                ))
            except Exception:
                clicked = False
        if not clicked:
            raise RuntimeError("ما حصلت زر حفظ PIN")

        success = _wait_page(driver, lambda: (
            "profilepinadded=success" in str(driver.current_url or "").lower()
            or any(x in _body_text_lower(driver) for x in (
                "pin updated", "pin saved", "profile lock updated", "تم حفظ", "تم تحديث"
            ))
            or (not _find_pin_inputs(driver) and "/settings/lock" not in str(driver.current_url or "").lower())
        ), timeout=20)
        if not success:
            if wrong_password_visible():
                raise RuntimeError("كلمة المرور الحالية غير صحيحة")
            # UI confirmation is occasionally missing; use the freshly authenticated cookies once.
            if password_verified and try_direct_after_browser_auth():
                return
            _send_v22_browser_diagnostic(chat_id, driver, "pin_save_not_confirmed")
            raise RuntimeError("Netflix ما أكد حفظ PIN")

        refresh_engine_from_browser()
        acct = load_accounts().get(account_id) or {}
        save_engine_account(eng, account_id=account_id, status=acct.get("status") or "active", profiles=acct.get("profiles") or [])
        update_account_record(account_id, pin_password_auth_at=time.time())
        clear_cached_account_password(account_id)
    finally:
        session_password = None
        try:
            driver.quit()
        except Exception:
            pass


def set_profile_pin_resilient(chat_id: int, account_id: str, guid: str, pin: str,
                              password_cache: Optional[dict[str, str]] = None) -> None:
    """Prefer the fast GraphQL update; if Netflix requires fresh auth, recover through Password."""
    eng = engine_from_account(account_id)
    try:
        update_profile_pin(eng, guid, pin)
        acct = load_accounts().get(account_id) or {}
        save_engine_account(eng, account_id=account_id, status=acct.get("status") or "active", profiles=acct.get("profiles") or [])
        return
    except Exception as direct_exc:
        # A verification requirement is normal. The browser fallback always prefers Password and
        # never chooses SMS/email verification. Keep the direct exception only for diagnostics.
        try:
            profile_pin_browser_fallback(chat_id, account_id, guid, pin, password_cache=password_cache)
            return
        except Exception as browser_exc:
            raise RuntimeError(f"PIN direct+browser فشل: {browser_exc}") from direct_exc


def password_job_worker(chat_id: int, account_id: str, initial: bool) -> None:
    try:
        acct = load_accounts().get(account_id) or {}
        if initial and str(acct.get("password_status") or "") == "set":
            send_message(chat_id, "✅ كلمة مرور الحساب مضافة مسبقاً.")
            show_account_menu(chat_id, account_id)
            return

        if initial:
            new_password = wait_for_secret(
                chat_id, account_id, "new_account_password",
                "🔑 الحساب صار Active. هسه دز كلمة المرور اللي تريدها للحساب.\n\n"
                "• من 4 إلى 60 حرف\n• الرسالة تنحذف مباشرة من تيليجرام قدر الإمكان\n• كلمة المرور ما تنخزن داخل accounts.json",
                timeout=300, back_callback=f"acct:{account_id}"
            )
            if new_password is None:
                set_account_password_state(account_id, "required")
                send_inline(chat_id, "⏸ ما تم إنشاء كلمة المرور بعد. إدارة البروفايلات تبقى متوقفة إلى أن تضيفها.", [[("🔑 إنشاء كلمة المرور", f"setpw:{account_id}"), ("⬅️ الحساب", f"acct:{account_id}")]])
                return
            new_password = validate_account_password(new_password)
            try:
                set_or_change_password_browser(account_id, new_password, old_password=None)
            except RuntimeError as exc:
                if "CURRENT_PASSWORD_REQUIRED" not in str(exc):
                    raise
                current = wait_for_secret(
                    chat_id, account_id, "current_account_password",
                    "🔐 Netflix طلب كلمة مرور حالية بهذه الجلسة. دزها حتى أكمل تعيين كلمة المرور الجديدة.",
                    timeout=300, back_callback=f"acct:{account_id}"
                )
                if current is None:
                    raise RuntimeError("تم إلغاء إدخال كلمة المرور الحالية")
                set_or_change_password_browser(account_id, new_password, old_password=current)
            set_account_password_state(account_id, "set", password_set_at=time.time())
            cache_account_password(account_id, new_password)
            send_message(chat_id, "✅ تم إنشاء كلمة مرور الحساب بنجاح. هسه إدارة البروفايلات والـPIN جاهزة.")
            try:
                profiles = sync_account_profiles(account_id, force=True)
                send_message(chat_id, "👤 البروفايلات الحالية:\n" + profile_summary(profiles))
            except Exception as exc:
                send_message(chat_id, f"✅ كلمة المرور جاهزة. تحديث قائمة البروفايلات نأجله للزر «تحديث»: {exc}")
            show_account_menu(chat_id, account_id)
            return

        old_password = wait_for_secret(
            chat_id, account_id, "current_account_password",
            "🔐 دز كلمة المرور الحالية للحساب:",
            timeout=300, back_callback=f"acct:{account_id}"
        )
        if old_password is None:
            send_message(chat_id, "❌ تم إلغاء تغيير كلمة المرور.")
            show_account_menu(chat_id, account_id)
            return
        old_password = validate_account_password(old_password)
        new_password = wait_for_secret(
            chat_id, account_id, "new_account_password",
            "🆕 دز كلمة المرور الجديدة:",
            timeout=300, back_callback=f"acct:{account_id}"
        )
        if new_password is None:
            send_message(chat_id, "❌ تم إلغاء تغيير كلمة المرور.")
            show_account_menu(chat_id, account_id)
            return
        new_password = validate_account_password(new_password)
        if old_password == new_password:
            raise RuntimeError("كلمة المرور الجديدة نفس الحالية")
        set_or_change_password_browser(account_id, new_password, old_password=old_password)
        set_account_password_state(account_id, "set", password_set_at=time.time())
        cache_account_password(account_id, new_password)
        send_message(chat_id, "✅ تم تغيير كلمة مرور الحساب بنجاح.")
        show_account_menu(chat_id, account_id)
    except Exception as exc:
        if initial:
            try:
                set_account_password_state(account_id, "failed", password_error=str(exc)[:250])
            except Exception:
                pass
        send_inline(chat_id, f"❌ عملية كلمة المرور ما كملت: {type(exc).__name__}: {exc}", [[("🔄 حاول مرة ثانية", f"setpw:{account_id}" if initial else f"pw:{account_id}"), ("⬅️ الحساب", f"acct:{account_id}")]])
    finally:
        with STATE_LOCK:
            PASSWORD_JOBS.pop(chat_id, None)


def launch_password_job(chat_id: int, account_id: str, initial: bool) -> None:
    busy = busy_job_name(chat_id)
    if busy and busy != "كلمة المرور":
        send_message(chat_id, f"⏳ أكمل عملية {busy} أولاً.")
        return
    with STATE_LOCK:
        old = PASSWORD_JOBS.get(chat_id)
        if old is not None and old.is_alive():
            send_message(chat_id, "⏳ عملية كلمة المرور شغالة حالياً.")
            return
        t = threading.Thread(target=password_job_worker, args=(chat_id, account_id, initial), daemon=True)
        PASSWORD_JOBS[chat_id] = t
        t.start()


def require_password_after_activation(chat_id: int, account_id: str) -> bool:
    acct = load_accounts().get(account_id) or {}
    pstatus = str(acct.get("password_status") or "unknown")
    if pstatus == "set":
        return False
    # Older imported sessions may already have a password. Do not falsely lock them.
    if pstatus == "unknown":
        return False
    set_account_password_state(account_id, "required")
    launch_password_job(chat_id, account_id, initial=True)
    return True




def _driver_url(driver) -> str:
    try:
        return str(driver.current_url or "")
    except Exception:
        return ""


def _driver_title(driver) -> str:
    try:
        return str(driver.title or "")
    except Exception:
        return ""


def _redact_browser_url(url: str) -> str:
    """Keep diagnostics useful without leaking opaque signup/session state."""
    try:
        u = urlparse(str(url or ""))
        if not u.scheme or not u.netloc:
            return scrub_sensitive_text(str(url or ""))[:500]
        qs = parse_qs(u.query, keep_blank_values=True)
        safe = []
        for k in sorted(qs):
            kl = k.lower()
            if any(x in kl for x in ("state", "token", "code", "session", "flwssn", "gsid", "auth")):
                safe.append(f"{k}=<redacted>")
            else:
                vals = qs.get(k) or [""]
                safe.append(f"{k}={scrub_sensitive_text(str(vals[0]))[:120]}")
        q = "&".join(safe)
        return f"{u.scheme}://{u.netloc}{u.path}" + (f"?{q}" if q else "")
    except Exception:
        return "<unavailable>"


def _visible_input_descriptors(driver) -> list[dict]:
    out = []
    try:
        els = driver.find_elements("css selector", "input,select,textarea")
    except Exception:
        els = []
    for el in els[:80]:
        try:
            if not el.is_displayed():
                continue
            item = {}
            for attr in ("type", "name", "id", "autocomplete", "aria-label", "data-uia", "placeholder"):
                try:
                    v = el.get_attribute(attr)
                except Exception:
                    v = None
                if v:
                    item[attr] = scrub_sensitive_text(str(v))[:180]
            # Never record field values.
            out.append(item)
        except Exception:
            continue
    return out[:30]


def _visible_action_labels(driver) -> list[str]:
    labels = []
    try:
        els = driver.find_elements("css selector", "button,a,[role='button'],input[type='submit']")
    except Exception:
        els = []
    for el in els[:160]:
        try:
            if not el.is_displayed() or not el.is_enabled():
                continue
            parts = []
            for attr in ("innerText", "textContent", "value", "aria-label", "data-uia", "name", "id"):
                try:
                    v = el.get_attribute(attr)
                except Exception:
                    v = None
                if v:
                    parts.append(str(v))
            s = re.sub(r"\s+", " ", " | ".join(parts)).strip()
            if s:
                labels.append(scrub_sensitive_text(s)[:240])
        except Exception:
            continue
    # stable dedupe
    seen, out = set(), []
    for x in labels:
        k = x.lower()
        if k in seen:
            continue
        seen.add(k)
        out.append(x)
    return out[:35]


def _find_visible_login_id_input(driver):
    selectors = (
        'input[name="userLoginId"]', 'input[type="email"]', 'input[autocomplete="username"]',
        'input[name*="email" i]', 'input[id*="email" i]', 'input[name*="login" i]'
    )
    for selector in selectors:
        for el in _visible_elements(driver, selector):
            if "password" not in _input_meta(el):
                return el
    return None


def _visible_login_otp_fields(driver):
    selectors = (
        'input[autocomplete="one-time-code"]', 'input[name*="otp" i]', 'input[id*="otp" i]',
        'input[name*="code" i]', 'input[id*="code" i]', 'input[inputmode="numeric"]'
    )
    out = []
    seen = set()
    for selector in selectors:
        for el in _visible_elements(driver, selector):
            try:
                key = el.id
            except Exception:
                key = id(el)
            if key in seen:
                continue
            seen.add(key)
            meta = _input_meta(el)
            if "phone" in meta or "pin" in meta:
                continue
            out.append(el)
    return out


def _find_visible_login_otp_input(driver):
    fields = _visible_login_otp_fields(driver)
    return fields[0] if fields else None


def _fill_login_otp(driver, otp: str) -> None:
    otp = validate_payment_otp(otp)
    fields = _visible_login_otp_fields(driver)
    if not fields:
        raise RuntimeError("خانة OTP مو ظاهرة")
    one_char = []
    for el in fields:
        try:
            maxlength = int(el.get_attribute("maxlength") or 0)
        except Exception:
            maxlength = 0
        if maxlength == 1:
            one_char.append(el)
    if len(one_char) >= len(otp):
        for el, digit in zip(one_char, otp):
            _safe_fill(el, digit)
        return
    _safe_fill(fields[0], otp)


def _login_error_kind(driver) -> Optional[str]:
    body = _body_text_lower(driver)
    if any(x in body for x in (
        "err_empty_response", "this page isn't working", "didn't send any data",
        "لم ترسل أي بيانات", "لم ترسل بيانات",
    )):
        return "NETWORK"
    if any(x in body for x in (
        "captcha", "verify you are human", "security challenge", "unusual activity",
        "تحقق من أنك إنسان", "التحقق الأمني", "نشاط غير معتاد"
    )):
        return "SECURITY"
    if any(x in body for x in (
        "incorrect password", "wrong password", "password is incorrect",
        "كلمة المرور غير صحيحة", "كلمة السر غير صحيحة"
    )):
        return "INVALID_PASSWORD"
    if any(x in body for x in (
        "invalid code", "incorrect code", "code is incorrect", "wrong code",
        "الرمز غير صحيح", "الكود غير صحيح", "رمز غير صحيح"
    )):
        return "INVALID_OTP"
    if any(x in body for x in (
        "code has expired", "code expired", "expired code",
        "انتهت صلاحية الرمز", "انتهت صلاحية الكود"
    )):
        return "OTP_EXPIRED"
    if any(x in body for x in (
        "can't find an account", "cannot find an account", "account not found",
        "لا يمكن العثور على حساب", "لم نعثر على حساب", "الحساب غير موجود"
    )):
        return "ACCOUNT_NOT_FOUND"
    return None


def _login_stage(driver) -> str:
    err = _login_error_kind(driver)
    if err:
        return err
    if _find_visible_password_inputs(driver):
        return "PASSWORD"
    if _find_visible_login_otp_input(driver) is not None:
        return "OTP"
    url = str(getattr(driver, "current_url", "") or "").lower()
    body = _body_text_lower(driver)
    if "/login" not in url and any(x in url for x in ("/browse", "/profiles", "/manageprofiles", "/account")):
        return "SUCCESS"
    if any(x in body for x in ("who's watching", "من يشاهد", "إدارة الملفات الشخصية", "manage profiles")):
        return "SUCCESS"
    return "UNKNOWN"


def _wait_login_stage(driver, timeout: float = 18.0) -> str:
    deadline = time.time() + timeout
    last = "UNKNOWN"
    while time.time() < deadline:
        last = _login_stage(driver)
        if last != "UNKNOWN":
            return last
        time.sleep(0.25)
    return last


def _submit_visible_login_form(driver, source_field=None) -> bool:
    """Submit the current Netflix login step without depending on one button label."""
    if _click_button_like(driver, (
        "تسجيل الدخول", "متابعة", "التالي", "إرسال الرمز", "إرسال رمز",
        "إرسال رمز تسجيل الدخول", "إرسال رمز لتسجيل الدخول", "رمز تسجيل الدخول",
        "تحقق", "تأكيد", "sign in", "continue", "next", "send code",
        "send sign-in code", "sign-in code", "verify", "submit"
    )):
        return True

    # Prefer the form that owns the field we just filled. This avoids submitting
    # unrelated footer/help forms.
    if source_field is not None:
        try:
            submitted = bool(driver.execute_script(r'''
                const el=arguments[0];
                const f=el && el.closest ? el.closest('form') : null;
                if(!f) return false;
                const b=f.querySelector('button[type="submit"],input[type="submit"],[data-uia*="submit" i],[data-uia*="login" i]');
                if(b && !b.disabled){ b.click(); return true; }
                if(f.requestSubmit){ f.requestSubmit(); return true; }
                f.submit(); return true;
            ''', source_field))
            if submitted:
                return True
        except Exception:
            pass

        # Current identification variants can bind CLCS submission to Enter on
        # userLoginId even when no normal button is exposed to Selenium.
        try:
            from selenium.webdriver.common.keys import Keys
            source_field.send_keys(Keys.ENTER)
            return True
        except Exception:
            pass

    try:
        return bool(driver.execute_script(r'''
            const fs=[...document.querySelectorAll('form')].filter(f=>{
              const r=f.getBoundingClientRect(); const st=getComputedStyle(f);
              return r.width>0 && r.height>0 && st.display!=='none' && st.visibility!=='hidden';
            });
            if(fs.length!==1) return false;
            const f=fs[0];
            if(f.requestSubmit){f.requestSubmit();}else{f.submit();}
            return true;
        '''))
    except Exception:
        return False


def _switch_login_to_password(driver) -> bool:
    if _find_visible_password_inputs(driver):
        return True
    if _click_button_like(driver, (
        "استخدام كلمة المرور بدلاً من ذلك", "استخدم كلمة المرور بدلاً من ذلك",
        "الدخول بكلمة المرور", "تسجيل الدخول بكلمة المرور",
        "use password instead", "sign in with password", "password instead"
    )):
        return _wait_page(driver, lambda: bool(_find_visible_password_inputs(driver)), timeout=10)
    _click_button_like(driver, (
        "طلب المساعدة", "الحصول على مساعدة", "هل تحتاج إلى مساعدة",
        "get help", "need help", "help"
    ))
    time.sleep(0.7)
    if _click_button_like(driver, (
        "استخدام كلمة المرور بدلاً من ذلك", "استخدم كلمة المرور بدلاً من ذلك",
        "الدخول بكلمة المرور", "تسجيل الدخول بكلمة المرور",
        "use password instead", "sign in with password", "password instead"
    )):
        return _wait_page(driver, lambda: bool(_find_visible_password_inputs(driver)), timeout=10)
    return bool(_find_visible_password_inputs(driver))


def _finalize_login_session(driver, chat_id: int, proxy_id: Optional[str], used_password: bool) -> str:
    # V22.14: existing-account login is direct Railway only. proxy_id is retained
    # in the signature for compatibility with older call sites but is intentionally ignored.
    eng = NetflixDirect()
    eng.import_selenium_cookies(driver.get_cookies(), str(driver.current_url or f"{NETFLIX_IQ}/"))
    ms = eng.membership_status()
    url = str(driver.current_url or "").lower()
    stage = _login_stage(driver)
    authenticated = stage == "SUCCESS" or "/login" not in url
    if not authenticated and not is_active_membership(ms):
        raise RuntimeError("Netflix ما أكد تسجيل الدخول")

    status = "active" if is_active_membership(ms) else "logged_in"
    account_id = save_engine_account(eng, status=status, profiles=[])
    update_account_record(
        account_id,
        membership_status=ms,
        password_status="set" if used_password else "unknown",
        login_source="telegram_login",
        login_at=time.time(),
    )
    with STATE_LOCK:
        CHAT_STATE.setdefault(chat_id, {})["selected_account"] = account_id

    if status == "active":
        send_message(chat_id, f"✅ تم تسجيل الدخول بنجاح. MembershipStatus={ms}\n💾 انحفظت الجلسة باسم حساب {account_id[3:]}.\n🌐 تسجيل الدخول تم Direct Railway؛ البروكسي محفوظ لإنشاء الحساب فقط.")
    else:
        send_message(chat_id, f"✅ تم تسجيل الدخول، لكن العضوية مو Active حالياً. MembershipStatus={ms!r}\n💾 انحفظت الجلسة باسم حساب {account_id[3:]}.\n🌐 تسجيل الدخول تم Direct Railway؛ البروكسي محفوظ لإنشاء الحساب فقط.")
    show_account_menu(chat_id, account_id)
    return account_id


def login_worker(chat_id: int) -> None:
    me = threading.current_thread()
    driver = None
    try:
        email = wait_for_login_email(chat_id, timeout=300)
        if not email or _login_cancelled(chat_id):
            send_message(chat_id, "⏸ تم إلغاء تسجيل الدخول.", keyboard=True)
            return

        # V22.14 policy: the proxy is reserved exclusively for NEW ACCOUNT signup.
        # Existing-account login never consumes proxy traffic.
        proxy_id = None
        send_message(chat_id, "🌐 جاري فتح Netflix بالعربي عبر Direct Railway. البروكسي ما راح يُستخدم بتسجيل الدخول؛ هو مخصص لإنشاء الحساب فقط.")
        driver = _new_chromium_driver(performance=False, proxy_id=None)
        try:
            driver.set_page_load_timeout(45)
        except Exception:
            pass
        driver.get(f"{NETFLIX_IQ}/login")

        first_error = _login_error_kind(driver)
        if first_error == "NETWORK":
            raise RuntimeError("اتصال Railway المباشر ما رجع بيانات من Netflix (ERR_EMPTY_RESPONSE). جرّب مرة ثانية لاحقاً")
        if first_error == "SECURITY":
            raise RuntimeError("Netflix عرض CAPTCHA/تحقق أمني أثناء تسجيل الدخول المباشر. ما راح أحاول أتجاوز التحقق")

        _wait_page(driver, lambda: _find_visible_login_id_input(driver) is not None or bool(_find_visible_password_inputs(driver)), timeout=22)
        field = _find_visible_login_id_input(driver)

        # Password-first A/B variant: continue through the existing password flow.
        if field is None and _find_visible_password_inputs(driver):
            stage = "PASSWORD"
        else:
            if field is None:
                try:
                    _send_v22_browser_diagnostic(chat_id, driver, "login_identification_missing", "ما ظهرت خانة userLoginId بعد انتظار الصفحة.")
                except Exception:
                    pass
                raise RuntimeError("صفحة تسجيل الدخول فتحت، لكن خانة الإيميل ما ظهرت")
            _safe_fill(field, email)
            if not _submit_visible_login_form(driver, source_field=field):
                try:
                    _send_v22_browser_diagnostic(chat_id, driver, "login_identification_submit", "تعذر تشغيل Submit من زر/فورم/Enter.")
                except Exception:
                    pass
                raise RuntimeError("تعذر إرسال الإيميل من صفحة تسجيل الدخول")
            stage = _wait_login_stage(driver, timeout=25)

        if stage in ("OTP", "UNKNOWN"):
            for _attempt in range(4):
                if _login_cancelled(chat_id):
                    return
                value = wait_for_login_otp_or_password(chat_id, timeout=300)
                if value is None:
                    send_message(chat_id, "⏸ تم إلغاء تسجيل الدخول.", keyboard=True)
                    return
                if value == "__PASSWORD__":
                    if not _switch_login_to_password(driver):
                        raise RuntimeError("Netflix ما أظهر خيار كلمة المرور بهذه الجلسة")
                    stage = "PASSWORD"
                    break
                otp = validate_payment_otp(value)
                otp_field = _find_visible_login_otp_input(driver)
                if otp_field is None:
                    stage = _wait_login_stage(driver, timeout=3)
                    if stage == "PASSWORD":
                        break
                    raise RuntimeError("خانة OTP اختفت قبل تعبئة الرمز")
                _fill_login_otp(driver, otp)
                otp = None
                if not _submit_visible_login_form(driver, source_field=otp_field):
                    raise RuntimeError("ما قدرت أرسل رمز تسجيل الدخول من الصفحة")
                stage = _wait_login_stage(driver, timeout=15)
                if stage == "SUCCESS":
                    _finalize_login_session(driver, chat_id, proxy_id, used_password=False)
                    return
                if stage in ("INVALID_OTP", "OTP_EXPIRED"):
                    send_message(chat_id, "❌ رمز تسجيل الدخول غير صحيح أو انتهت صلاحيته. دز الرمز الجديد.")
                    continue
                if stage == "PASSWORD":
                    break
                if stage == "SECURITY":
                    raise RuntimeError("Netflix عرض CAPTCHA/تحقق أمني أثناء تسجيل الدخول المباشر؛ ما راح أحاول أتجاوزه")
                if stage == "ACCOUNT_NOT_FOUND":
                    raise RuntimeError("Netflix ما لقى حساب بهذا الإيميل")
                time.sleep(1.0)
                stage = _wait_login_stage(driver, timeout=5)
                if stage == "SUCCESS":
                    _finalize_login_session(driver, chat_id, proxy_id, used_password=False)
                    return
            else:
                raise RuntimeError("تم تجاوز عدد محاولات OTP")

        if stage == "ACCOUNT_NOT_FOUND":
            raise RuntimeError("Netflix ما لقى حساب بهذا الإيميل")
        if stage == "SECURITY":
            raise RuntimeError("Netflix عرض CAPTCHA/تحقق أمني أثناء تسجيل الدخول المباشر؛ ما راح أحاول أتجاوزه")
        if stage == "SUCCESS":
            _finalize_login_session(driver, chat_id, proxy_id, used_password=False)
            return
        if stage != "PASSWORD":
            if not _switch_login_to_password(driver):
                raise RuntimeError("صفحة تسجيل الدخول تغيرت وما قدرت أوصل لخانة كلمة المرور")

        for _attempt in range(3):
            password = wait_for_login_password(chat_id, timeout=300)
            if password is None or _login_cancelled(chat_id):
                send_message(chat_id, "⏸ تم إلغاء تسجيل الدخول.", keyboard=True)
                return
            id_field = _find_visible_login_id_input(driver)
            if id_field is not None:
                _safe_fill(id_field, email)
            pw_fields = _find_visible_password_inputs(driver)
            if not pw_fields:
                raise RuntimeError("خانة كلمة المرور مو ظاهرة")
            for pw_field in pw_fields:
                _safe_fill(pw_field, password)
            password = None
            if not _submit_visible_login_form(driver, source_field=pw_fields[0]):
                raise RuntimeError("ما قدرت أرسل نموذج تسجيل الدخول بكلمة المرور")
            stage = _wait_login_stage(driver, timeout=18)
            if stage == "SUCCESS":
                _finalize_login_session(driver, chat_id, proxy_id, used_password=True)
                return
            if stage == "INVALID_PASSWORD":
                send_message(chat_id, "❌ كلمة المرور غير صحيحة. دز كلمة المرور الصحيحة.")
                continue
            if stage == "SECURITY":
                raise RuntimeError("Netflix عرض CAPTCHA/تحقق أمني أثناء تسجيل الدخول المباشر؛ ما راح أحاول أتجاوزه")
            time.sleep(1.0)
            stage = _wait_login_stage(driver, timeout=5)
            if stage == "SUCCESS":
                _finalize_login_session(driver, chat_id, proxy_id, used_password=True)
                return
        raise RuntimeError("Netflix ما أكد تسجيل الدخول بعد محاولات كلمة المرور")
    except Exception as exc:
        if not _login_cancelled(chat_id):
            send_message(chat_id, f"❌ تسجيل الدخول ما كمل: {type(exc).__name__}: {scrub_sensitive_text(str(exc))}", keyboard=True)
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass
        with WAIT_COND:
            st = CHAT_STATE.setdefault(chat_id, {})
            for key in (
                "awaiting_login_email", "awaiting_login_otp", "awaiting_login_password",
                "login_email_value", "login_otp_value", "login_password_value", "login_method_value"
            ):
                st.pop(key, None)
            WAIT_COND.notify_all()
        with STATE_LOCK:
            if LOGIN_JOBS.get(chat_id) is me:
                LOGIN_JOBS.pop(chat_id, None)
                LOGIN_CANCEL_EVENTS.pop(chat_id, None)


def launch_login_job(chat_id: int) -> None:
    _join_cancelled_login_job(chat_id, timeout=1.0)
    busy = busy_job_name(chat_id)
    if busy:
        raise RuntimeError(f"عندك عملية شغالة حالياً: {busy}")
    clear_input_state(chat_id)
    with STATE_LOCK:
        LOGIN_CANCEL_EVENTS[chat_id] = threading.Event()
        th = threading.Thread(target=login_worker, args=(chat_id,), daemon=True)
        LOGIN_JOBS[chat_id] = th
        th.start()


def _visible_otp_input(driver):
    sels = (
        'input[autocomplete="one-time-code"]',
        'input[name*="otp" i]', 'input[id*="otp" i]',
        'input[name*="code" i]', 'input[id*="code" i]',
    )
    for sel in sels:
        try:
            for el in driver.find_elements("css selector", sel):
                if el.is_displayed() and el.is_enabled():
                    return el
        except Exception:
            continue
    return None


def _fill_visible_payment_otp_only(driver, otp: str) -> None:
    """Fill the visible OTP input and deliberately do not submit/click anything."""
    otp = validate_payment_otp(otp)
    field = _visible_otp_input(driver)
    if field is None:
        raise RuntimeError("ما حصلت خانة OTP ظاهرة داخل صفحة Netflix")
    try:
        driver.execute_script("arguments[0].scrollIntoView({block:'center'});", field)
    except Exception:
        pass
    _safe_fill(field, otp)
    # Confirm that the browser field actually received the code. Do not log the value.
    try:
        current = str(field.get_attribute("value") or "")
    except Exception:
        current = ""
    if current and current != otp:
        raise RuntimeError("خانة OTP ما احتفظت بالكود كاملاً")


def _otp_error_state(driver) -> Optional[str]:
    """Classify visible post-submit OTP errors without reading/storing the OTP itself."""
    body = _body_text_lower(driver)
    if any(x in body for x in (
        "code has expired", "code expired", "expired code", "request a new code",
        "انتهت صلاحية الرمز", "انتهت صلاحية الكود", "اطلب رمزاً جديداً", "اطلب رمز جديد",
    )):
        return "expired"
    if any(x in body for x in (
        "incorrect code", "invalid code", "code is incorrect", "code isn't correct", "code is not correct",
        "wrong code", "رمز غير صحيح", "الكود غير صحيح", "الرمز غير صحيح",
    )):
        return "invalid"
    return None



def run_live_browser_payment_otp_flow(driver, chat_id: int, account_id: str,
                                      eng: "NetflixDirect", target_url: str) -> bool:
    """Browser fallback that NEVER reopens the signup URL after OTP was reached.

    This fixes the plan-selection regression: the exact driver that reached otpCodeEntry stays
    alive while Telegram receives OTP and membership confirmation.
    """
    for attempt in range(1, 6):
        if _visible_otp_input(driver) is None:
            _send_v22_browser_diagnostic(chat_id, driver, "otp_field_disappeared_same_driver")
            raise RuntimeError("وصلنا OTP لكن الخانة اختفت من نفس المتصفح قبل استلام الكود")

        otp = wait_for_payment_otp(chat_id, account_id, timeout=300)
        if otp == "__CHANGE_PHONE__":
            with STATE_LOCK:
                CHAT_STATE.setdefault(chat_id, {})["deferred_change_phone"] = account_id
            send_message(chat_id, "📱 تمام. أوقف انتظار الكود الحالي وأنتقل لتغيير رقم الهاتف بنفس الحساب والجلسة المحفوظة...")
            return False
        if otp is None:
            send_message(chat_id, "⏸ تم إلغاء/انتهاء انتظار OTP. ما تم بدء العضوية.")
            return False
        _fill_visible_payment_otp_only(driver, otp)
        otp = None
        send_message(chat_id, "✅ تم تعبئة OTP داخل نفس نافذة Netflix التي وصلت فعلياً لشاشة الكود.")

        if not click_start_membership_after_confirmation(driver, chat_id, account_id):
            return False

        deadline = time.time() + 50
        last_ms_check = 0.0
        retry_reason = None
        while time.time() < deadline:
            time.sleep(0.55)
            try:
                eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or target_url)
                acct = load_accounts().get(account_id, {})
                save_engine_account(eng, account_id=account_id, status=acct.get("status") or "pending_otp", profiles=acct.get("profiles") or [])
            except Exception:
                pass

            err = _otp_error_state(driver)
            if err:
                retry_reason = err
                break

            state, _ = _browser_page_state(driver)
            if state == "security":
                _send_v22_browser_diagnostic(chat_id, driver, "security_after_approved_membership")
                send_message(chat_id, "⚠️ Netflix طلب تحققاً أمنياً إضافياً. ما راح أحاول أتجاوزه.")
                return False

            if time.time() - last_ms_check >= 3:
                last_ms_check = time.time()
                ms = eng.membership_status()
                if is_active_membership(ms):
                    _finalize_membership_activation(chat_id, account_id, eng, str(ms), inline_password=True)
                    return True

        if retry_reason:
            if retry_reason == "expired":
                send_message(chat_id, "⌛ الكود انتهت صلاحيته. دز الكود الجديد؛ نفس نافذة OTP باقية مفتوحة.")
            else:
                send_inline(
                    chat_id,
                    "❌ الكود غير صحيح. دز الكود الصحيح؛ نفس نافذة OTP باقية مفتوحة.",
                    [[("📱 تغيير رقم الهاتف", f"otp_cp:{account_id}")]],
                )
            continue

        _send_v22_browser_diagnostic(chat_id, driver, "membership_not_confirmed_same_driver")
        send_message(chat_id, "⚠️ Netflix ما أكد التفعيل ضمن المهلة. أوقفت المحاولة بدل إعادة أي خطوة دفع تلقائياً.")
        return False

    send_message(chat_id, "⛔ توقفت بعد 5 محاولات OTP.")
    return False


def _browser_page_state(driver) -> tuple[str, str]:
    body = _body_text_lower(driver)
    url = _driver_url(driver).lower()

    if any(x in body for x in (
        "captcha", "verify you are human", "security check", "unusual activity",
        "تحقق من أنك إنسان", "اختبار أمني", "نشاط غير معتاد",
    )):
        return "security", "security/captcha text"

    if _visible_otp_input(driver) is not None or any(x in body for x in (
        "verification code", "enter code", "one-time code", "one time code", "otp",
        "رمز التحقق", "أدخل الرمز", "رمز لمرة واحدة",
    )):
        return "payment_otp", "otp input/text"

    if _find_visible_phone_input(driver) is not None:
        return "phone_entry", "visible phone input"

    if any(x in body for x in (
        "choose how to pay", "add to mobile bill", "mobile bill", "carrier billing",
        "اختر طريقة الدفع", "فاتورة الهاتف", "الدفع عبر الهاتف",
    )):
        return "payment_picker", "payment picker text"

    if any(x in body for x in (
        "choose any plan", "choose a plan", "select a plan", "most popular",
        "اختر أي خطة", "اختر خطة", "حدد خطة",
    )):
        return "plan_selection", "plan selection text"

    if any(x in body for x in ("finish sign-up", "finish signup", "complete sign-up", "complete signup")):
        return "finish_signup", "finish signup CTA"

    if any(x in body for x in (
        "something went wrong", "try again", "we're having trouble", "we are having trouble",
        "حدث خطأ", "حاول مرة أخرى",
    )):
        return "error", "error text"

    try:
        pw = driver.find_elements("css selector", 'input[type="password"]')
        if any(el.is_displayed() for el in pw):
            return "password", "visible password input"
    except Exception:
        pass

    if "/manageprofiles" in url or "manage profiles" in body or "إدارة الملفات الشخصية" in body:
        return "profiles", "profile manager"

    return "unknown", "no known signature"


def _write_v22_browser_diagnostic(driver, context: str, state: str | None = None) -> tuple[str | None, str]:
    ts = int(time.time())
    state = state or _browser_page_state(driver)[0]
    base = TMPDIR / f"v22_page_diag_{ts}_{re.sub(r'[^a-zA-Z0-9_-]+', '_', context)[:45]}"
    png = str(base.with_suffix('.png'))
    jsn = str(base.with_suffix('.json'))
    screenshot_ok = False
    try:
        screenshot_ok = bool(driver.save_screenshot(png))
    except Exception:
        screenshot_ok = False
    body = _body_text_lower(driver)
    payload = {
        "format": "netflix_v22_page_diagnostic",
        "context": context,
        "state": state,
        "url": _redact_browser_url(_driver_url(driver)),
        "title": scrub_sensitive_text(_driver_title(driver))[:300],
        "body_preview": scrub_sensitive_text(re.sub(r"\s+", " ", body))[:1800],
        "actions": _visible_action_labels(driver),
        "inputs": _visible_input_descriptors(driver),
        "created_at": time.time(),
        "privacy": "No cookies, form values, OTP, phone, password, email, serverState, or proxy credentials are recorded.",
    }
    Path(jsn).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding='utf-8')
    return (png if screenshot_ok and Path(png).exists() else None), jsn


def _send_v22_browser_diagnostic(chat_id: int, driver, context: str, note: str = "") -> None:
    try:
        state, why = _browser_page_state(driver)
        png, jsn = _write_v22_browser_diagnostic(driver, context, state)
        send_message(chat_id, f"🧭 V22 شخّص صفحة غير متوقعة. الحالة={state} ({why})" + (f"\n{note}" if note else ""))
        if png:
            send_document(chat_id, png, f"V22 screenshot — {context}")
        send_document(chat_id, jsn, f"V22 diagnostic — {context}")
    except Exception as exc:
        send_message(chat_id, f"⚠️ تعذر تجهيز تشخيص V22: {scrub_sensitive_text(str(exc))}")


def _recover_phone_entry_from_signup_ui(driver, chat_id: int | None = None):
    """V22 self-healing browser state machine.

    It recognizes the currently rendered signup page instead of assuming a fixed route.
    It can recover planSelection -> paymentPicker -> DCB phone entry and can step back from
    the payment-OTP page to the phone page. Security/CAPTCHA stays manual. Payment OTP may be autofilled later, but payment submission remains manual.
    Unknown pages are not blindly clicked; they are diagnosed for a targeted update.
    """
    announced = set()
    deadline = time.time() + 95
    unknown_rounds = 0
    error_retries = 0
    otp_back_attempted = False
    last_signature = None

    while time.time() < deadline:
        state, why = _browser_page_state(driver)
        url = _driver_url(driver)
        sig = (state, _redact_browser_url(url), tuple(_visible_action_labels(driver)[:5]))
        if sig != last_signature:
            last_signature = sig
            unknown_rounds = 0

        if state == "phone_entry":
            return _find_visible_phone_input(driver)

        if state == "security":
            if chat_id is not None:
                _send_v22_browser_diagnostic(chat_id, driver, "security_challenge", "التحقق الأمني يبقى يدوي وما راح أحاول أتجاوزه.")
            raise RuntimeError("Netflix عرض تحقق أمني/CAPTCHA؛ افتحه يدوياً")

        if state == "payment_otp":
            # Changing the phone from OTP is a normal navigation action, not OTP automation.
            if _click_button_like(driver, (
                "change phone", "change number", "edit phone", "use another number",
                "تغيير الرقم", "تغيير رقم", "تعديل الرقم", "استخدام رقم آخر",
            )):
                time.sleep(0.9)
                continue
            if not otp_back_attempted:
                otp_back_attempted = True
                try:
                    driver.back()
                    time.sleep(1.0)
                    continue
                except Exception:
                    pass
            # A saved opaque CLCS state may reopen somewhere else; fall back to /signup and
            # classify from there rather than pretending this page has a Change phone control.
            try:
                driver.get(f"{NETFLIX}/signup")
                time.sleep(0.9)
                continue
            except Exception:
                pass

        if state == "payment_picker":
            if chat_id is not None and state not in announced:
                send_message(chat_id, "🧭 V22: وصلت صفحة الدفع؛ أختار Add to mobile bill وأرجع لخانة الرقم.")
                announced.add(state)
            if _click_button_like(driver, (
                "add to mobile bill", "mobile bill", "carrier billing",
                "فاتورة الهاتف", "الدفع عبر الهاتف", "إضافة إلى فاتورة الهاتف",
            )):
                time.sleep(1.0)
                continue

        if state == "plan_selection":
            if chat_id is not None and state not in announced:
                send_message(chat_id, "🧭 V22: Netflix رجع لاختيار الخطة؛ أحافظ على الاختيار الحالي وأكمل للمسار التالي.")
                announced.add(state)
            if _click_button_like(driver, ("next", "continue", "التالي", "متابعة", "استمرار")):
                time.sleep(1.0)
                continue

        if state == "finish_signup":
            if _click_button_like(driver, ("finish sign-up", "finish signup", "complete sign-up", "complete signup")):
                time.sleep(1.0)
                continue

        if state == "error":
            if error_retries < 1 and _click_button_like(driver, ("try again", "retry", "حاول مرة أخرى", "إعادة المحاولة")):
                error_retries += 1
                time.sleep(1.2)
                continue
            if chat_id is not None:
                _send_v22_browser_diagnostic(chat_id, driver, "netflix_error_page")
            return None

        if state in ("password", "profiles"):
            if chat_id is not None:
                _send_v22_browser_diagnostic(chat_id, driver, f"unexpected_{state}")
            return None

        # Unknown-page policy: V22 never blindly clicks arbitrary actions.  It may advance only
        # through an explicit generic Next/Continue control, and only twice before diagnosing.
        if state == "unknown":
            unknown_rounds += 1
            if unknown_rounds <= 2 and _click_button_like(driver, ("next", "continue", "التالي", "متابعة")):
                if chat_id is not None and "unknown_continue" not in announced:
                    send_message(chat_id, "🧭 V22: ظهرت صفحة وسيطة جديدة وبها Continue/Next واضح؛ أجرب الانتقال الآمن وأفحص الصفحة التالية.")
                    announced.add("unknown_continue")
                time.sleep(1.0)
                continue
            if unknown_rounds >= 5:
                if chat_id is not None:
                    _send_v22_browser_diagnostic(chat_id, driver, "unknown_signup_page", "ما ضغطت أي زر غير معروف؛ أرسلت التشخيص حتى ما نخرب الجلسة.")
                return None

        time.sleep(0.45)

    if chat_id is not None:
        _send_v22_browser_diagnostic(chat_id, driver, "recovery_timeout")
    return None

def _check_agreement_if_present(driver) -> None:
    selectors = ('input[name="iAgree"]', 'input[id="iAgree"]', 'input[type="checkbox"]')
    for selector in selectors:
        try:
            for el in driver.find_elements("css selector", selector):
                if not el.is_displayed() or not el.is_enabled():
                    continue
                if not el.is_selected():
                    try:
                        el.click()
                    except Exception:
                        driver.execute_script("arguments[0].click();", el)
                return
        except Exception:
            continue


def _wait_for_changed_phone(chat_id: int, timeout: int = 300) -> Optional[str]:
    deadline = time.time() + timeout
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_change_phone"] = True
        while time.time() < deadline:
            value = st.pop("change_phone_value", None)
            if value:
                st["awaiting_change_phone"] = False
                return str(value)
            WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
        st["awaiting_change_phone"] = False
    return None


def change_phone_worker(chat_id: int, account_id: str) -> None:
    driver = None
    try:
        acct = load_accounts().get(account_id) or {}
        if not acct:
            raise RuntimeError("saved account not found")
        if str(acct.get("status") or "") == "active":
            raise RuntimeError("account is already active")

        eng = engine_from_account(account_id)
        target = str(acct.get("otp_url") or f"{NETFLIX}/signup")
        send_inline(
            chat_id,
            "\U0001f4f1 \u062c\u0627\u0631\u064a \u0641\u062a\u062d \u0645\u0631\u062d\u0644\u0629 \u0627\u0644\u0631\u0642\u0645 \u0645\u0646 \u0646\u0641\u0633 \u0627\u0644\u062c\u0644\u0633\u0629...",
            [[("\u274c \u0625\u0644\u063a\u0627\u0621", f"cp_cancel:{account_id}")]],
        )
        driver = _new_chromium_driver(performance=False, proxy_id=eng.proxy_id, force_proxy=bool(eng.proxy_id))
        _seed_browser_from_requests(driver, eng.s)
        driver.get(target)

        deadline = time.time() + 20
        phone_input = None
        while time.time() < deadline:
            phone_input = _find_visible_phone_input(driver)
            if phone_input is not None:
                break
            time.sleep(0.15)

        if phone_input is None:
            changed = _click_button_like(driver, (
                "change phone", "change number", "edit phone", "use another number",
                "\u062a\u063a\u064a\u064a\u0631 \u0627\u0644\u0631\u0642\u0645", "\u062a\u063a\u064a\u064a\u0631 \u0631\u0642\u0645", "\u062a\u0639\u062f\u064a\u0644 \u0627\u0644\u0631\u0642\u0645",
            ))
            if changed:
                deadline = time.time() + 20
                while time.time() < deadline:
                    phone_input = _find_visible_phone_input(driver)
                    if phone_input is not None:
                        break
                    time.sleep(0.15)

        # A pending CLCS state is not a durable browser URL.  On Railway Netflix
        # may reopen this saved session at planSelection (as seen in the user's
        # screenshot) instead of showing a literal "Change phone" link.  Recover
        # through the normal signup UI and stop at the phone field.
        if phone_input is None:
            phone_input = _recover_phone_entry_from_signup_ui(driver, chat_id=chat_id)

        if phone_input is None:
            body = _body_text_lower(driver).replace("\n", " ")[:220]
            raise RuntimeError(f"تعذر الرجوع إلى خانة الرقم من صفحة Netflix الحالية: {body}")

        send_inline(
            chat_id,
            "\U0001f4f2 \u062f\u0632 \u0627\u0644\u0631\u0642\u0645 \u0627\u0644\u0639\u0631\u0627\u0642\u064a \u0627\u0644\u062c\u062f\u064a\u062f. \u0627\u0644\u0628\u0648\u062a \u0631\u0627\u062d \u064a\u0631\u0633\u0644 Verify Phone Number \u0648\u064a\u0631\u062c\u0639\u0643 \u0644\u0634\u0627\u0634\u0629 OTP.",
            [[("\u274c \u0625\u0644\u063a\u0627\u0621", f"cp_cancel:{account_id}"), ("\u2b05\ufe0f \u0627\u0644\u062d\u0633\u0627\u0628", f"acct:{account_id}")]],
        )
        phone = _wait_for_changed_phone(chat_id)
        if phone == "__CANCEL__":
            send_message(chat_id, "\u274c \u062a\u0645 \u0625\u0644\u063a\u0627\u0621 \u062a\u063a\u064a\u064a\u0631 \u0627\u0644\u0631\u0642\u0645.")
            show_account_menu(chat_id, account_id)
            return
        if not phone:
            raise RuntimeError("phone change timed out")

        phone_input = _find_visible_phone_input(driver)
        if phone_input is None:
            raise RuntimeError("phone field disappeared before submit")
        try:
            phone_input.clear()
        except Exception:
            pass
        phone_input.send_keys(phone)
        _check_agreement_if_present(driver)

        verified = _click_button_like(driver, (
            "verify phone number", "verify number", "verify phone", "send code", "continue",
            "\u062a\u062d\u0642\u0642 \u0645\u0646 \u0631\u0642\u0645 \u0627\u0644\u0647\u0627\u062a\u0641", "\u062a\u062d\u0642\u0642", "\u0625\u0631\u0633\u0627\u0644 \u0627\u0644\u0631\u0645\u0632",
        ))
        if not verified:
            raise RuntimeError("Verify Phone Number button not found")

        deadline = time.time() + 30
        reached_otp = False
        while time.time() < deadline:
            time.sleep(0.20)
            try:
                body = (driver.find_element("tag name", "body").text or "").lower()
            except Exception:
                body = ""
            try:
                otp_inputs = driver.find_elements("css selector", 'input[autocomplete="one-time-code"],input[name*="otp"],input[id*="otp"],input[name*="code"],input[id*="code"]')
                otp_visible = any(x.is_displayed() for x in otp_inputs)
            except Exception:
                otp_visible = False
            if otp_visible or any(x in body for x in ("verification code", "enter code", "one-time", "otp", "\u0631\u0645\u0632 \u0627\u0644\u062a\u062d\u0642\u0642", "\u0623\u062f\u062e\u0644 \u0627\u0644\u0631\u0645\u0632")):
                reached_otp = True
                break
            if any(x in body for x in ("something went wrong", "try again", "\u062d\u062f\u062b \u062e\u0637\u0623", "\u062d\u0627\u0648\u0644 \u0645\u0631\u0629 \u0623\u062e\u0631\u0649")):
                raise RuntimeError("Netflix returned an error after Verify Phone Number")

        eng.import_selenium_cookies(driver.get_cookies(), driver.current_url or target)
        profiles = (load_accounts().get(account_id, {}) or {}).get("profiles") or []
        save_engine_account(eng, account_id=account_id, status="pending_otp", profiles=profiles)
        update_account_record(account_id, otp_url=str(driver.current_url or target))

        msg = "\U0001f4e9 \u062a\u0645 \u062a\u063a\u064a\u064a\u0631 \u0627\u0644\u0631\u0642\u0645 \u0648\u0625\u0631\u0633\u0627\u0644 Verify Phone Number."
        if reached_otp:
            msg += "\n\u2705 \u0631\u062c\u0639\u0646\u0627 \u0644\u0645\u0631\u062d\u0644\u0629 OTP \u0628\u0646\u062c\u0627\u062d."
        else:
            msg += "\n\u23f3 \u0627\u0644\u0637\u0644\u0628 \u0627\u0646\u0631\u0633\u0644\u061b \u0627\u0633\u062a\u062e\u062f\u0645 \u0641\u062d\u0635 \u0627\u0644\u062a\u0641\u0639\u064a\u0644 \u0623\u0648 \u0641\u062a\u062d OTP."
        if reached_otp:
            send_message(chat_id, msg + "\n📩 راح أطلب منك الكود تلقائياً هسه على نفس النافذة؛ ما راح أعيد فتح signup.")
            run_live_browser_payment_otp_flow(driver, chat_id, account_id, eng, str(driver.current_url or target))
        else:
            send_inline(chat_id, msg, [
                [("🖥 فتح OTP يدوياً", f"otpview:{account_id}"), ("📱 تغيير الرقم", f"cp:{account_id}")],
                [("✅ فحص التفعيل", f"verified:{account_id}"), ("⬅️ الحساب", f"acct:{account_id}")],
            ])
    except Exception as exc:
        send_inline(chat_id, f"\u274c \u062a\u063a\u064a\u064a\u0631 \u0627\u0644\u0631\u0642\u0645 \u0645\u0627 \u0643\u0645\u0644: {type(exc).__name__}: {exc}", [[("\U0001f504 \u062d\u0627\u0648\u0644 \u0645\u0631\u0629 \u062b\u0627\u0646\u064a\u0629", f"cp:{account_id}"), ("\u2b05\ufe0f \u0627\u0644\u062d\u0633\u0627\u0628", f"acct:{account_id}")]])
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass
        with STATE_LOCK:
            CHANGE_PHONE_JOBS.pop(chat_id, None)


def launch_change_phone(chat_id: int, account_id: str) -> None:
    busy = busy_job_name(chat_id)
    if busy and busy != "تغيير الرقم":
        send_message(chat_id, f"⏳ أكمل عملية {busy} أولاً.")
        return
    with STATE_LOCK:
        old = CHANGE_PHONE_JOBS.get(chat_id)
        if old is not None and old.is_alive():
            send_message(chat_id, "\u23f3 \u0639\u0645\u0644\u064a\u0629 \u062a\u063a\u064a\u064a\u0631 \u0627\u0644\u0631\u0642\u0645 \u0634\u063a\u0627\u0644\u0629 \u062d\u0627\u0644\u064a\u0627\u064b.")
            return
        st = CHAT_STATE.setdefault(chat_id, {})
        st.pop("change_phone_value", None)
        st["awaiting_change_phone"] = False
        t = threading.Thread(target=change_phone_worker, args=(chat_id, account_id), daemon=True)
        CHANGE_PHONE_JOBS[chat_id] = t
        t.start()


def check_activation(chat_id: int, account_id: str) -> bool:
    eng = engine_from_account(account_id)
    ms = eng.membership_status()
    if is_active_membership(ms):
        acct = load_accounts().get(account_id, {})
        prior_status = str(acct.get("status") or "unknown")
        prior_pstatus = str(acct.get("password_status") or "unknown")
        save_engine_account(eng, account_id=account_id, status="active", profiles=acct.get("profiles") or [])
        changes = {"membership_status": ms}
        if prior_pstatus == "unknown" and prior_status != "active":
            # Migration path for a V19 pending-OTP account completed under V21.
            changes["password_status"] = "required"
        acct = update_account_record(account_id, **changes)
        old_proxy = detach_proxy_after_activation(eng, account_id)
        proxy_note = "\n🌐 تم فصل بروكسي التسجيل عن هذا الحساب؛ بقية الإدارة تستخدم اتصال Railway المباشر." if old_proxy else ""
        send_message(chat_id, f"✅ التفعيل ناجح. MembershipStatus={ms}{proxy_note}")
        if require_password_after_activation(chat_id, account_id):
            return True
        try:
            profiles = sync_account_profiles(account_id, force=True)
            send_message(chat_id, "👤 البروفايلات الحالية:\n" + profile_summary(profiles))
        except Exception as exc:
            send_message(chat_id, f"✅ الحساب Active، لكن اكتشاف البروفايلات يحتاج تحديث لاحق: {exc}")
        show_account_menu(chat_id, account_id)
        return True
    send_inline(chat_id, f"⏳ بعده ما ظهر التفعيل على الجلسة. MembershipStatus={ms!r}", [
        [("🖥 فتح Netflix يدوياً", f"otpview:{account_id}"), ("📱 تغيير الرقم", f"cp:{account_id}")],
        [("🔄 أعد الفحص", f"verified:{account_id}"), ("⬅️ الحساب", f"acct:{account_id}")],
    ])
    return False


# ---------------- Fast signup job ----------------

def wait_for_phone(chat_id: int, timeout: int = 300) -> Optional[str]:
    deadline = time.time() + timeout
    with WAIT_COND:
        st = CHAT_STATE.setdefault(chat_id, {})
        st["awaiting_phone"] = True
        st.pop("phone_value", None)
        while time.time() < deadline:
            if _job_cancelled(chat_id):
                st["awaiting_phone"] = False
                return "__CANCEL__"
            value = st.pop("phone_value", None)
            if value:
                st["awaiting_phone"] = False
                return value
            WAIT_COND.wait(timeout=min(5, max(0.1, deadline - time.time())))
        st["awaiting_phone"] = False
    return None



def _v22_browser_signup_fallback_to_otp(chat_id: int, eng: NetflixDirect, t_all: float, direct_reason: str) -> bool:
    """Fallback when Netflix changes CLCS screen names/trees or persisted signup behavior.

    Uses the ordinary rendered signup UI, preserves the same cookies/proxy, and stops at payment OTP.
    OTP autofill and Start Membership confirmation are handled later by the owner-only live browser flow.
    """
    driver = None
    try:
        send_message(chat_id, "🧭 V22 Self-Healing: المسار المباشر تغيّر أو ظهرت شاشة جديدة. أحوّل لنفس الجلسة داخل Chromium وأتعرف على الصفحة الحالية بدل ما أفشل.\nسبب التحويل: " + scrub_sensitive_text(str(direct_reason))[:350])
        driver = _new_chromium_driver(performance=False, proxy_id=eng.proxy_id, force_proxy=bool(eng.proxy_id))
        try:
            driver.set_page_load_timeout(45)
        except Exception:
            pass
        _seed_browser_from_requests(driver, eng.s)
        try:
            driver.get(f"{NETFLIX}/signup")
        except Exception as exc:
            send_message(chat_id, "⚠️ تحميل /signup تأخر؛ V22 راح يفحص الصفحة الموجودة حالياً.")

        phone_input = _recover_phone_entry_from_signup_ui(driver, chat_id=chat_id)
        if phone_input is None:
            _send_v22_browser_diagnostic(chat_id, driver, "direct_to_browser_fallback_failed")
            raise RuntimeError("V22 ما قدر يوصل لخانة الرقم من الصفحة الجديدة بدون تخمين")

        send_inline(chat_id, "✅ V22 استعاد مسار التسجيل ووصل لخانة رقم الهاتف.\n\n📱 دز رقمك العراقي هسه، مثلاً 07xxxxxxxxx أو +9647xxxxxxxxx", [[("❌ إلغاء العملية", "canceljob")]])
        phone = wait_for_phone(chat_id)
        if phone == "__CANCEL__":
            send_message(chat_id, "❌ تم إلغاء العملية.", keyboard=True)
            return False
        if not phone:
            raise RuntimeError("انتهى وقت انتظار رقم الهاتف")

        phone_input = _find_visible_phone_input(driver)
        if phone_input is None:
            raise RuntimeError("خانة الرقم اختفت قبل الإرسال")
        try:
            phone_input.clear()
        except Exception:
            pass
        phone_input.send_keys(phone)
        _check_agreement_if_present(driver)

        if not _click_button_like(driver, (
            "verify phone number", "verify number", "verify phone", "send code", "continue",
            "تحقق من رقم الهاتف", "تحقق", "إرسال الرمز",
        )):
            _send_v22_browser_diagnostic(chat_id, driver, "verify_phone_button_changed")
            raise RuntimeError("V22 ما تعرّف على زر Verify Phone Number الجديد")

        reached_otp = False
        deadline = time.time() + 35
        final_state = "unknown"
        while time.time() < deadline:
            time.sleep(0.20)
            final_state, _ = _browser_page_state(driver)
            if final_state == "payment_otp":
                reached_otp = True
                break
            if final_state == "security":
                _send_v22_browser_diagnostic(chat_id, driver, "security_after_phone_submit")
                raise RuntimeError("ظهر تحقق أمني بعد إرسال الرقم؛ يحتاج تدخل يدوي")
            if final_state == "error":
                _send_v22_browser_diagnostic(chat_id, driver, "error_after_phone_submit")
                raise RuntimeError("Netflix رجع صفحة خطأ بعد Verify Phone Number")

        eng.import_selenium_cookies(driver.get_cookies(), _driver_url(driver) or f"{NETFLIX}/signup")
        account_id = save_engine_account(eng, status="pending_otp", profiles=[])
        with STATE_LOCK:
            ACTIVE_JOB_ACCOUNTS[chat_id] = account_id
        update_account_record(account_id, password_status="pending_activation", otp_url=str(_driver_url(driver) or f"{NETFLIX}/signup"))
        with STATE_LOCK:
            CHAT_STATE.setdefault(chat_id, {})["selected_account"] = account_id

        total = time.time() - t_all
        detail = "وصلت شاشة رمز التحقق." if reached_otp else f"تم Verify؛ V22 صنّف الصفحة الحالية: {final_state}"
        send_message(
            chat_id,
            "📩 تم تنفيذ Verify Phone Number عبر Browser fallback.\n"
            f"{detail}\n"
            f"⏱ الزمن الكلي: {total:.1f} ثانية\n\n"
            f"💾 الجلسة انحفظت باسم: حساب {account_id[3:]}\n"
            "✅ إذا ظهرت شاشة OTP، راح أطلب منك الكود تلقائياً هسه بدون أي زر إضافي.\n"
            "✅ بعد OTP راح يطلع لك تأكيد Start Membership داخل Telegram (موافق/رفض)."
        )
        if reached_otp:
            send_message(chat_id, "🤖 راح أكمل من Telegram على نفس نافذة Chromium الحالية؛ ما راح أعيد فتح /signup حتى ما نرجع لاختيار الخطة.")
            run_live_browser_payment_otp_flow(driver, chat_id, account_id, eng, str(_driver_url(driver) or f"{NETFLIX}/signup"))
        else:
            show_account_menu(chat_id, account_id)
        return True
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass


def fast_flow(chat_id: int, epr_url: str) -> bool:
    # A new signup always starts with a fresh local proxy relay/tunnel. The upstream proxy
    # configuration is preserved; only stale local transport state from a previous run is reset.
    with PROXY_LOCK:
        _stop_proxy_relay_locked()
    # V22.14: this is the ONLY automatic flow allowed to attach the selected proxy.
    # The same proxy stays on EPR -> plan -> terms/phone -> OTP -> approved Start Membership.
    # detach_proxy_after_activation() clears it immediately after MembershipStatus becomes active.
    eng = NetflixDirect(use_signup_proxy=True)
    t_all = time.time()
    if eng.proxy_id:
        send_message(chat_id, "🌐 بروكسي التسجيل مفعّل لهذه العملية فقط. يبقى إلى نجاح Start Membership ثم ينفصل فوراً قبل كلمة المرور/البروفايلات.")
    else:
        send_message(chat_id, "⚠️ بروكسي التسجيل غير مفعّل؛ إنشاء الحساب راح يستخدم اتصال Railway المباشر.")
    send_message(chat_id, "🛡️ V22 Self-Healing بدأ.\nالأولوية للمحرك المباشر السريع؛ وإذا تغيّرت صفحة/CLCS أحوّل تلقائياً إلى Browser fallback وأرسل تشخيصاً عند الصفحة المجهولة.")

    t = time.time()
    ok, mode = eng.open_epr_direct(epr_url)
    if not ok:
        if mode in {"proxy_transport_retry_exhausted", "proxy_transport_after_epr"}:
            send_message(
                chat_id,
                "⚡ اتصال البروكسي انقطع أثناء الطلب المباشر. ما راح أستخدم Railway المباشر؛ "
                "أحوّل تلقائياً إلى Chromium بنفس بروكسي التسجيل وبجلسة جديدة.",
            )
        cookies, current = bootstrap_with_chromium(epr_url, chat_id, eng.s, proxy_id=eng.proxy_id)
        eng.import_selenium_cookies(cookies, current)
        # Membership GraphQL may itself change in the future.  Keep the validated check when
        # available, but do not discard a browser-confirmed accountCreated=success session merely
        # because a query changed; the next signup-page classifier is the second source of truth.
        try:
            ms = eng.membership_status()
        except Exception as exc:
            ms = None
            eng.note("membership_check_after_bootstrap_failed", error=str(exc))
        if ms not in (None, "NEVER_MEMBER"):
            raise RuntimeError(f"بعد bootstrap ما تأكد إنشاء الحساب. MembershipStatus={ms!r}")
        mode = "chromium_bootstrap_then_direct"
    send_message(chat_id, f"✅ 1/4 تم إنشاء/تثبيت جلسة الحساب ({time.time()-t:.1f}s)\nالمحرك: {mode}")

    # Direct path stays fastest. Any structural change before the phone prompt switches to the
    # rendered browser state machine instead of crashing the whole job.
    try:
        t = time.time()
        init_mode = "direct"
        try:
            init_screen, preloaded = eng.init_signup()
        except RuntimeError as exc:
            if "CLCSWebInitSignup رجع بدون screen" not in str(exc):
                raise
            init_screen, preloaded = capture_live_init_with_chromium(eng, chat_id)
            init_mode = "live-init-fallback"

        # Semantic search first: exact loggingViewName, then component/text signatures.
        plan_screen = find_screen_by_logging(preloaded, "planSelection")
        if not plan_screen:
            candidates = [init_screen] + list(preloaded or [])
            for s in candidates:
                if not isinstance(s, dict):
                    continue
                vals = " ".join(extract_text_values(s)).lower()
                if screen_contains_type(s, "CLCSPlanSelection") or "choose any plan" in vals or "choose a plan" in vals:
                    plan_screen = s
                    break
        if not plan_screen:
            raise RuntimeError("V22_DIRECT_STRUCTURE_CHANGED: ما حصلت شاشة اختيار الخطة بالمعنى أو النوع")
        send_message(chat_id, f"✅ 2/4 تم فتح اختيار الخطة ({time.time()-t:.1f}s)\nالمسار: {init_mode}")

        t = time.time()
        payment_screen = eng.select_plan(plan_screen)
        vals = " ".join(extract_text_values(payment_screen)).lower()
        if str(payment_screen.get("loggingViewName") or "").lower() != "paymentpicker" and not any(x in vals for x in ("choose how to pay", "add to mobile bill", "mobile bill")):
            raise RuntimeError(f"V22_DIRECT_STRUCTURE_CHANGED: شاشة بعد الخطة غير معروفة ({payment_screen.get('loggingViewName')!r})")
        send_message(chat_id, f"✅ 3/4 تم الوصول إلى Choose how to pay ({time.time()-t:.1f}s)")

        t = time.time()
        phone_screen = eng.choose_mobile_bill(payment_screen)
        if not looks_like_phone_entry(phone_screen):
            raise RuntimeError(f"V22_DIRECT_STRUCTURE_CHANGED: DCB رجع شاشة غير متوقعة ({phone_screen.get('loggingViewName')!r})")
        send_inline(chat_id, f"✅ 4/4 وصلنا إلى صفحة رقم الهاتف ({time.time()-t:.1f}s)\n\n📱 دز رقمك العراقي هسه، مثلاً 07xxxxxxxxx أو +9647xxxxxxxxx", [[("❌ إلغاء العملية", "canceljob")]])
    except Exception as direct_exc:
        return _v22_browser_signup_fallback_to_otp(chat_id, eng, t_all, str(direct_exc))

    phone = wait_for_phone(chat_id)
    if phone == "__CANCEL__":
        send_message(chat_id, "❌ تم إلغاء العملية.", keyboard=True)
        return False
    if not phone:
        raise RuntimeError("انتهى وقت انتظار رقم الهاتف")
    send_message(chat_id, "✅ استلمت الرقم. أرسل Verify Phone Number هسه...")

    # Do not silently resubmit a payment-verification phone if this request changes/fails; repeated
    # submits could send multiple OTPs.  Instead preserve the session and emit sanitized diagnostics.
    try:
        otp_screen, status = eng.submit_phone_for_dcb(phone_screen, phone)
    except Exception as exc:
        dbg = eng.write_debug("submit_phone_for_dcb_changed")
        send_document(chat_id, dbg, "V22 direct diagnostic بعد Verify")
        raise RuntimeError(f"Verify Phone Number تغيّر/فشل، ما أعدت الإرسال تلقائياً: {scrub_sensitive_text(str(exc))}")

    account_id = save_engine_account(eng, status="pending_otp", profiles=[])
    with STATE_LOCK:
        ACTIVE_JOB_ACCOUNTS[chat_id] = account_id
    update_account_record(account_id, password_status="pending_activation")
    with STATE_LOCK:
        CHAT_STATE.setdefault(chat_id, {})["selected_account"] = account_id
    target = f"{NETFLIX}/signup"
    if otp_screen and isinstance(otp_screen.get("serverState"), str) and otp_screen.get("serverState"):
        target = f"{NETFLIX}/signup?serverState={quote(str(otp_screen['serverState']), safe='')}"
    update_account_record(account_id, otp_url=target)

    total = time.time() - t_all
    if otp_screen and looks_like_payment_otp(otp_screen):
        detail = "وصلت شاشة رمز التحقق."
    elif otp_screen:
        detail = f"Netflix رجع شاشة جديدة: {otp_screen.get('loggingViewName') or 'unknown'}"
    else:
        detail = f"تم إرسال Verify؛ الحالة: {status}"

    send_message(
        chat_id,
        "📩 تم تنفيذ Verify Phone Number.\n"
        f"{detail}\n"
        f"⏱ الزمن الكلي: {total:.1f} ثانية\n\n"
        f"💾 الجلسة انحفظت محلياً باسم: حساب {account_id[3:]}\n"
        "✅ إذا وصلنا شاشة OTP، راح أطلب منك الكود تلقائياً هسه بدون زر إضافي.\n"
        "✅ بعد OTP راح يطلب منك Telegram موافق/رفض على Start Membership؛ إذا وافقت يضغطه ويكمل تلقائياً."
    )
    if otp_screen and looks_like_payment_otp(otp_screen):
        send_message(chat_id, "🤖 ما تحتاج تفتح المتصفح. راح أكمل OTP + موافقة Start Membership بالكامل من Telegram وبنفس CLCS session الحالية.")
        direct_payment_otp_membership_flow(chat_id, account_id, eng, otp_screen)
    else:
        show_account_menu(chat_id, account_id)
    return True

def run_job(chat_id: int, epr_url: str) -> None:
    me = threading.current_thread()
    try:
        fast_flow(chat_id, epr_url)
    except Exception as exc:
        # A cooperative owner cancel is a normal exit, not an error report.
        if _job_cancelled(chat_id):
            return
        p = TMPDIR / f"netflix_fast_v22_error_{int(time.time())}.txt"
        p.write_text(f"{type(exc).__name__}: {scrub_sensitive_text(str(exc))}\n", encoding="utf-8")
        send_message(chat_id, f"❌ V22 توقف:\n{type(exc).__name__}: {scrub_sensitive_text(str(exc))}")
        send_document(chat_id, str(p), "تشخيص V22 المختصر")
    finally:
        deferred_change = None
        with STATE_LOCK:
            # Never let an older worker remove a newer job registration.
            if ACTIVE_JOBS.get(chat_id) is me:
                ACTIVE_JOBS.pop(chat_id, None)
                JOB_CANCEL_EVENTS.pop(chat_id, None)
                ACTIVE_JOB_ACCOUNTS.pop(chat_id, None)
            st = CHAT_STATE.setdefault(chat_id, {})
            deferred_change = st.pop("deferred_change_phone", None)
            st["awaiting_epr"] = False
            st["awaiting_phone"] = False
            st["awaiting_payment_otp"] = False
            st["awaiting_membership_confirmation"] = False
            st.pop("phone_value", None)
            st.pop("payment_otp_value", None)
            st.pop("membership_confirm_value", None)
        # The old signup thread is no longer registered, so this can safely reuse the saved
        # pending account without opening two competing Netflix sessions at the same time.
        if deferred_change and not _account_deleted(str(deferred_change)):
            try:
                launch_change_phone(chat_id, str(deferred_change))
            except Exception as exc:
                send_message(chat_id, f"❌ ما قدرت أبدأ تغيير الرقم: {type(exc).__name__}: {scrub_sensitive_text(str(exc))}")


def start_job(chat_id: int, epr_url: str) -> None:
    # If the owner just cancelled a waiting OTP job, give it a short chance to unwind now.
    _join_cancelled_main_job(chat_id, timeout=2.5)
    with STATE_LOCK:
        old = ACTIVE_JOBS.get(chat_id)
        if old and old.is_alive():
            if _job_cancelled(chat_id):
                send_message(chat_id, "⏳ العملية السابقة ملغاة فعلاً لكن عندها طلب شبكة قيد الإغلاق. جرّب إنشاء الحساب بعد ثوانٍ قليلة.")
            else:
                send_message(chat_id, "عندك عملية شغالة حالياً.")
            return
        ev = threading.Event()
        JOB_CANCEL_EVENTS[chat_id] = ev
        ACTIVE_JOB_ACCOUNTS.pop(chat_id, None)
        th = threading.Thread(target=run_job, args=(chat_id, epr_url), daemon=True)
        ACTIVE_JOBS[chat_id] = th
        th.start()


def _set_text_wait(chat_id: int, key: str, account_id: str, guid: Optional[str] = None) -> None:
    clear_input_state(chat_id)
    with STATE_LOCK:
        st = CHAT_STATE.setdefault(chat_id, {})
        st[key] = True
        st["target_account"] = account_id
        if guid:
            st["target_guid"] = guid


def handle_callback(cb: dict) -> None:
    cid = str(cb.get("id") or "")
    user_id = int((cb.get("from") or {}).get("id", 0) or 0)
    msg = cb.get("message") or {}
    chat_id = int((msg.get("chat") or {}).get("id", 0) or 0)
    data = str(cb.get("data") or "")
    if not user_id or not chat_id:
        return
    if not ensure_owner(user_id):
        answer_callback(cid, "هذا البوت خاص")
        return
    answer_callback(cid)
    try:
        parts = data.split(":")
        cmd = parts[0]
        aid = parts[1] if len(parts) > 1 else ""
        if cmd == "login_cancel":
            request_login_cancel(chat_id)
            _join_cancelled_login_job(chat_id, timeout=1.0)
            send_message(chat_id, "✅ تم إلغاء تسجيل الدخول.", keyboard=True)
        elif cmd == "login_use_password":
            with WAIT_COND:
                live = CHAT_STATE.setdefault(chat_id, {})
                if not live.get("awaiting_login_otp"):
                    send_message(chat_id, "⚠️ خيار كلمة المرور قديم أو تسجيل الدخول مو منتظر OTP حالياً.")
                else:
                    live["login_method_value"] = "PASSWORD"
                    live["awaiting_login_otp"] = False
                    WAIT_COND.notify_all()
                    send_message(chat_id, "🔑 تمام، أحول Netflix إلى استخدام كلمة المرور بدلاً من OTP...")
        elif cmd == "proxy":
            clear_input_state(chat_id)
            show_proxy_menu(chat_id)
        elif cmd == "proxy_back":
            clear_input_state(chat_id)
            send_message(chat_id, "اختار من الأزرار.", keyboard=True)
        elif cmd == "proxy_add":
            clear_input_state(chat_id)
            with STATE_LOCK:
                CHAT_STATE.setdefault(chat_id, {})["awaiting_proxy_add"] = True
            send_inline(chat_id, "➕ دز البروكسي بصيغة:\nhost:port:user:pass\n\nراح أحذف الرسالة من تيليجرام بعد حفظها قدر الإمكان.", [[("❌ إلغاء", "proxy")]])
        elif cmd == "proxy_toggle":
            cfg = load_proxy_config()
            if not cfg.get("active_id") or cfg.get("active_id") not in (cfg.get("items") or {}):
                raise RuntimeError("أضف بروكسي أولاً")
            cfg["enabled"] = not bool(cfg.get("enabled"))
            save_proxy_config(cfg)
            show_proxy_menu(chat_id)
        elif cmd == "proxy_test":
            threading.Thread(target=proxy_test_worker, args=(chat_id,), daemon=True).start()
        elif cmd == "proxy_sel":
            pid = aid
            cfg = load_proxy_config()
            if pid not in (cfg.get("items") or {}):
                raise RuntimeError("البروكسي غير موجود")
            cfg["active_id"] = pid
            save_proxy_config(cfg)
            show_proxy_menu(chat_id)
        elif cmd == "proxy_delete":
            cfg = load_proxy_config()
            pid = cfg.get("active_id")
            if not pid:
                raise RuntimeError("ماكو بروكسي حالي")
            send_inline(chat_id, f"🗑 حذف {proxy_mask((cfg.get('items') or {}).get(pid))}؟", [[("✅ حذف", f"proxy_delete2:{pid}"), ("❌ إلغاء", "proxy")]])
        elif cmd == "proxy_delete2":
            pid = aid
            cfg = load_proxy_config()
            (cfg.get("items") or {}).pop(pid, None)
            if cfg.get("active_id") == pid:
                cfg["active_id"] = next(iter(cfg.get("items") or {}), None)
            if not cfg.get("active_id"):
                cfg["enabled"] = False
            save_proxy_config(cfg)
            show_proxy_menu(chat_id)
        elif cmd == "acct":
            show_account_menu(chat_id, aid)
        elif cmd == "accounts":
            show_accounts(chat_id)
        elif cmd == "cp":
            launch_change_phone(chat_id, aid)
        elif cmd == "otp_cp":
            with WAIT_COND:
                live = CHAT_STATE.setdefault(chat_id, {})
                if not live.get("awaiting_payment_otp") or str(live.get("otp_account") or "") != aid:
                    send_message(chat_id, "⚠️ زر تغيير الرقم قديم أو العملية ما عادت تنتظر OTP. افتح الحساب واضغط تغيير الرقم من هناك.")
                else:
                    live["payment_otp_value"] = "__CHANGE_PHONE__"
                    live["awaiting_payment_otp"] = False
                    WAIT_COND.notify_all()
        elif cmd == "cp_cancel":
            with WAIT_COND:
                live = CHAT_STATE.setdefault(chat_id, {})
                live["change_phone_value"] = "__CANCEL__"
                live["awaiting_change_phone"] = False
                WAIT_COND.notify_all()
            show_account_menu(chat_id, aid)
        elif cmd == "canceljob":
            request_main_job_cancel(chat_id)
            _join_cancelled_main_job(chat_id, timeout=1.5)
            send_message(chat_id, "✅ تم إلغاء عملية التسجيل.", keyboard=True)
        elif cmd == "cancelacct":
            with STATE_LOCK:
                matches = ACTIVE_JOB_ACCOUNTS.get(chat_id) == aid
            if matches:
                request_main_job_cancel(chat_id)
                _join_cancelled_main_job(chat_id, timeout=1.5)
            send_message(chat_id, "✅ تم إلغاء عملية التسجيل لهذا الحساب. الجلسة المحلية تبقى موجودة لحد ما تحذفها إذا تريد.")
            if load_accounts().get(aid):
                show_account_menu(chat_id, aid)
        elif cmd == "cancelinput":
            clear_input_state(chat_id)
            if aid:
                show_account_menu(chat_id, aid)
            else:
                send_message(chat_id, "✅ تم الإلغاء.", keyboard=True)
        elif cmd == "cancelotp":
            with STATE_LOCK:
                matches = ACTIVE_JOB_ACCOUNTS.get(chat_id) == aid
            if matches:
                request_main_job_cancel(chat_id)
                _join_cancelled_main_job(chat_id, timeout=1.5)
            else:
                with WAIT_COND:
                    live = CHAT_STATE.setdefault(chat_id, {})
                    live["payment_otp_value"] = "__CANCEL__"
                    live["awaiting_payment_otp"] = False
                    WAIT_COND.notify_all()
            if aid and load_accounts().get(aid):
                show_account_menu(chat_id, aid)
        elif cmd in ("membership_yes", "membership_no"):
            with WAIT_COND:
                live = CHAT_STATE.setdefault(chat_id, {})
                expected = str(live.get("membership_confirm_account") or "")
                if not live.get("awaiting_membership_confirmation") or expected != aid:
                    send_message(chat_id, "⚠️ هذا التأكيد قديم أو ماكو عملية Start Membership تنتظر موافقة حالياً.")
                else:
                    live["membership_confirm_value"] = "YES" if cmd == "membership_yes" else "NO"
                    live["awaiting_membership_confirmation"] = False
                    WAIT_COND.notify_all()
                    if cmd == "membership_yes":
                        send_message(chat_id, "👍 وصلت الموافقة. جاري تنفيذ Start Membership داخل الجلسة الحالية...")
                    else:
                        send_message(chat_id, "👎 وصلت الرفض. لن يتم بدء العضوية.")
        elif cmd == "cancelsecret":
            with WAIT_COND:
                live = CHAT_STATE.setdefault(chat_id, {})
                live["secret_value"] = "__CANCEL__"
                live["awaiting_secret"] = False
                WAIT_COND.notify_all()
            if aid:
                show_account_menu(chat_id, aid)
        elif cmd == "setpw":
            launch_password_job(chat_id, aid, initial=True)
        elif cmd == "bn":
            assert_profile_management_allowed(aid)
            _set_text_wait(chat_id, "awaiting_batch_names", aid)
            profiles = sync_account_profiles(aid, force=False)
            send_inline(chat_id, "👤 دز الأسماء دفعة وحدة بهالشكل:\n1- بروفايل 1\n2- بروفايل 2\n... لحد 5\n\nالحالي:\n" + profile_summary(profiles), [[("❌ إلغاء", f"cancelinput:{aid}"), ("⬅️ الحساب", f"acct:{aid}")]])
        elif cmd == "bp":
            assert_profile_management_allowed(aid)
            _set_text_wait(chat_id, "awaiting_batch_pins", aid)
            profiles = sync_account_profiles(aid, force=False)
            send_inline(chat_id, "🔐 دز الرموز دفعة وحدة، كل PIN أربع أرقام:\n1- 1111\n2- 2222\n...\n\nالحالي:\n" + profile_summary(profiles), [[("❌ إلغاء", f"cancelinput:{aid}"), ("⬅️ الحساب", f"acct:{aid}")]])
        elif cmd == "pm":
            assert_profile_management_allowed(aid)
            show_profile_manager(chat_id, aid, force=False)
        elif cmd == "rp":
            assert_profile_management_allowed(aid)
            profiles = sync_account_profiles(aid, force=True)
            send_message(chat_id, "🔄 تم تحديث البروفايلات:\n" + profile_summary(profiles))
            show_profile_manager(chat_id, aid, force=False)
        elif cmd == "p":
            assert_profile_management_allowed(aid)
            show_one_profile(chat_id, aid, int(parts[2]))
        elif cmd == "rn":
            assert_profile_management_allowed(aid)
            guid = parts[2]
            _set_text_wait(chat_id, "awaiting_single_name", aid, guid)
            send_inline(chat_id, "✏️ دز الاسم الجديد لهذا البروفايل:", [[("❌ إلغاء", f"cancelinput:{aid}"), ("⬅️ رجوع", f"pm:{aid}")]])
        elif cmd == "sp":
            assert_profile_management_allowed(aid)
            guid = parts[2]
            _set_text_wait(chat_id, "awaiting_single_pin", aid, guid)
            send_inline(chat_id, "🔐 دز PIN جديد من 4 أرقام:", [[("❌ إلغاء", f"cancelinput:{aid}"), ("⬅️ رجوع", f"pm:{aid}")]])
        elif cmd == "dp":
            assert_profile_management_allowed(aid)
            guid = parts[2]
            send_inline(chat_id, "⚠️ متأكد تريد تحذف هذا البروفايل؟", [[("✅ نعم احذف", f"dp2:{aid}:{guid}"), ("❌ إلغاء", f"pm:{aid}")]])
        elif cmd == "dp2":
            assert_profile_management_allowed(aid)
            guid = parts[2]
            single_profile_delete(aid, guid)
            send_message(chat_id, "🗑 تم حذف البروفايل.")
            show_profile_manager(chat_id, aid, force=True)
        elif cmd == "ap":
            assert_profile_management_allowed(aid)
            _set_text_wait(chat_id, "awaiting_add_profile", aid)
            send_inline(chat_id, "➕ دز اسم البروفايل الجديد:", [[("❌ إلغاء", f"cancelinput:{aid}"), ("⬅️ الحساب", f"acct:{aid}")]])
        elif cmd in ("verified", "check"):
            check_activation(chat_id, aid)
        elif cmd == "otpview":
            with STATE_LOCK:
                main_th = ACTIVE_JOBS.get(chat_id)
                direct_waiting = bool(
                    main_th and main_th.is_alive()
                    and ACTIVE_JOB_ACCOUNTS.get(chat_id) == aid
                    and not _job_cancelled(chat_id)
                )
            if direct_waiting:
                send_message(chat_id, "⏳ نفس عملية التسجيل بعدَها تنتظر OTP داخل Telegram. ما راح أفتح متصفح ثاني حتى ما تتعارض الجلسات.")
            else:
                acct = load_accounts().get(aid) or {}
                target = str(acct.get("otp_url") or f"{NETFLIX}/signup")
                launch_manual_browser(chat_id, aid, target, "otp")
        elif cmd == "pw":
            launch_password_job(chat_id, aid, initial=False)
        elif cmd == "ds":
            send_inline(chat_id, "🗑 حذف الجلسة من الجهاز فقط؟ حساب Netflix نفسه ما ينحذف.", [[("✅ احذف الجلسة", f"ds2:{aid}"), ("❌ إلغاء", f"acct:{aid}")]])
        elif cmd == "ds2":
            with STATE_LOCK:
                matches = ACTIVE_JOB_ACCOUNTS.get(chat_id) == aid
            if matches:
                request_main_job_cancel(chat_id)
            delete_account_record(aid)
            _join_cancelled_main_job(chat_id, timeout=1.5)
            send_message(chat_id, "🗑 تم حذف الجلسة المحلية فقط، وأوقفت أي عملية تسجيل مرتبطة بها.", keyboard=True)
            show_accounts(chat_id)
    except Exception as exc:
        send_message(chat_id, f"❌ العملية ما كملت: {type(exc).__name__}: {exc}")


def handle_message(msg: dict) -> None:
    chat_id = int((msg.get("chat") or {}).get("id", 0) or 0)
    user_id = int((msg.get("from") or {}).get("id", 0) or 0)
    raw_text = str(msg.get("text") or "")
    text = raw_text.strip()
    if not chat_id or not user_id:
        return
    if not ensure_owner(user_id):
        send_message(chat_id, "⛔ هذا البوت خاص بصاحبه فقط.")
        return
    if text == "/start":
        send_message(chat_id, "✅ V22.14 جاهز. البروكسي لإنشاء الحساب فقط. OTP صار Truthful: تطبيع الأرقام العربية إلى ASCII، وعدم اتهام الكود بالخطأ إلا بدليل تحقق صريح، مع مهلة MembershipStatus قبل الحكم.", keyboard=True)
        return
    if text == "❌ إلغاء":
        request_main_job_cancel(chat_id)
        request_login_cancel(chat_id)
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            if live.get("awaiting_change_phone") or (chat_id in CHANGE_PHONE_JOBS and CHANGE_PHONE_JOBS[chat_id].is_alive()):
                live["change_phone_value"] = "__CANCEL__"
            if live.get("awaiting_secret"):
                live["secret_value"] = "__CANCEL__"
            for key in list(live.keys()):
                if key.startswith("awaiting_"):
                    live[key] = False
            WAIT_COND.notify_all()
        clear_input_state(chat_id)
        ended = _join_cancelled_main_job(chat_id, timeout=1.5)
        login_ended = _join_cancelled_login_job(chat_id, timeout=1.5)
        ended = ended and login_ended
        if ended:
            send_message(chat_id, "✅ تم الإلغاء وانتهت العملية. اختار من الأزرار.", keyboard=True)
        else:
            send_message(chat_id, "✅ تم طلب الإلغاء. إذا أكو طلب Netflix بالشبكة قيد التنفيذ راح ينغلق أول ما يرجع، بدون إعادة إحياء الجلسة المحذوفة.", keyboard=True)
        return
    if text in ("تسجيل دخول", "/login"):
        _join_cancelled_login_job(chat_id, timeout=1.0)
        busy = busy_job_name(chat_id)
        if busy:
            send_message(chat_id, f"⏳ عندك عملية شغالة حالياً: {busy}. كملها أو الغها أولاً.")
            return
        try:
            launch_login_job(chat_id)
        except Exception as exc:
            send_message(chat_id, f"❌ ما قدرت أبدأ تسجيل الدخول: {type(exc).__name__}: {exc}")
        return

    if text == "🧹 تنضيف الجلسات":
        cleanup_transient_sessions(chat_id)
        return
    if text == "📂 حساباتي":
        show_accounts(chat_id)
        return
    if text == "🌐 البروكسي":
        show_proxy_menu(chat_id)
        return
    if text in ("إنشاء حساب", "/new", "/create"):
        # A just-cancelled OTP wait normally exits immediately; clean it up before reporting busy.
        _join_cancelled_main_job(chat_id, timeout=1.5)
        busy = busy_job_name(chat_id)
        if busy:
            if busy == "إنشاء الحساب" and _job_cancelled(chat_id):
                send_message(chat_id, "⏳ العملية السابقة ملغاة لكنها بعدَها تغلق طلب شبكة. انتظر ثوانٍ قليلة واضغط إنشاء حساب مرة ثانية.")
            else:
                send_message(chat_id, f"⏳ عندك عملية شغالة حالياً: {busy}. كملها أو الغها أولاً.")
            return
        clear_input_state(chat_id)
        with STATE_LOCK:
            st = CHAT_STATE.setdefault(chat_id, {})
            st["awaiting_epr"] = True
            st["awaiting_phone"] = False
            st.pop("phone_value", None)
        send_message(chat_id, "🔗 دز رابط Netflix EPR فقط:")
        return

    with STATE_LOCK:
        st = dict(CHAT_STATE.setdefault(chat_id, {}))

    if st.get("awaiting_proxy_add"):
        message_id = int(msg.get("message_id", 0) or 0)
        try:
            p = parse_proxy_string(raw_text)
            cfg = load_proxy_config()
            pid = 'px_' + secrets.token_hex(4)
            p['id'] = pid
            cfg.setdefault('items', {})[pid] = p
            cfg['active_id'] = pid
            cfg['enabled'] = True
            save_proxy_config(cfg)
            clear_input_state(chat_id)
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"✅ تم حفظ وتشغيل البروكسي: {proxy_mask(p)}")
            show_proxy_menu(chat_id)
        except Exception as exc:
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"❌ {exc}. دز البروكسي مرة ثانية بصيغة host:port:user:pass")
        return

    if st.get("awaiting_login_email"):
        message_id = int(msg.get("message_id", 0) or 0)
        try:
            email = validate_login_email(raw_text)
        except Exception as exc:
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"❌ {exc}. دز إيميل Netflix الصحيح.")
            return
        if message_id:
            delete_telegram_message(chat_id, message_id)
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["login_email_value"] = email
            live["awaiting_login_email"] = False
            WAIT_COND.notify_all()
        email = None
        send_message(chat_id, "✅ استلمت الإيميل مؤقتاً. جاري فتح تسجيل الدخول...")
        return

    if st.get("awaiting_login_otp"):
        message_id = int(msg.get("message_id", 0) or 0)
        try:
            otp = validate_payment_otp(raw_text)
        except Exception as exc:
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"❌ {exc}. دز رمز تسجيل الدخول بالأرقام فقط، أو اضغط استخدام كلمة المرور.")
            return
        if message_id:
            delete_telegram_message(chat_id, message_id)
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["login_otp_value"] = otp
            live["awaiting_login_otp"] = False
            WAIT_COND.notify_all()
        otp = None
        send_message(chat_id, "✅ استلمت رمز تسجيل الدخول مؤقتاً. جاري التحقق...")
        return

    if st.get("awaiting_login_password"):
        message_id = int(msg.get("message_id", 0) or 0)
        try:
            password = validate_account_password(raw_text)
        except Exception as exc:
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"❌ {exc}. دز كلمة المرور الصحيحة أو اضغط إلغاء.")
            return
        if message_id:
            delete_telegram_message(chat_id, message_id)
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["login_password_value"] = password
            live["awaiting_login_password"] = False
            WAIT_COND.notify_all()
        password = None
        send_message(chat_id, "✅ استلمت كلمة المرور مؤقتاً. جاري تسجيل الدخول...")
        return

    if st.get("awaiting_payment_otp"):
        message_id = int(msg.get("message_id", 0) or 0)
        try:
            otp = validate_payment_otp(raw_text)
        except Exception as exc:
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"❌ {exc}. دز الكود بالأرقام فقط أو اضغط إلغاء OTP.")
            return
        if message_id:
            delete_telegram_message(chat_id, message_id)
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["payment_otp_value"] = otp
            live["awaiting_payment_otp"] = False
            WAIT_COND.notify_all()
        # Do not echo the OTP back to Telegram.
        otp = None
        send_message(chat_id, "✅ استلمت OTP بشكل مؤقت. جاري تعبئته داخل خانة Netflix فقط...")
        return

    if st.get("awaiting_secret"):
        message_id = int(msg.get("message_id", 0) or 0)
        try:
            secret = validate_account_password(raw_text)
        except Exception as exc:
            if message_id:
                delete_telegram_message(chat_id, message_id)
            send_message(chat_id, f"❌ {exc}. دز كلمة مرور ثانية أو اضغط إلغاء.")
            return
        if message_id:
            delete_telegram_message(chat_id, message_id)
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["secret_value"] = secret
            live["awaiting_secret"] = False
            WAIT_COND.notify_all()
        send_message(chat_id, "✅ استلمت كلمة المرور بشكل مؤقت. جاري إكمال العملية...")
        return

    if st.get("awaiting_change_phone"):
        phone = normalize_iq_phone(text)
        if not phone:
            send_message(chat_id, "📱 الرقم الجديد مو بصيغة عراقية واضحة. دزه مثل 07xxxxxxxxx أو +9647xxxxxxxxx")
            return
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["change_phone_value"] = phone
            live["awaiting_change_phone"] = False
            WAIT_COND.notify_all()
        send_message(chat_id, "📲 تم استلام الرقم الجديد. جاري إرسال Verify...")
        return

    if st.get("awaiting_phone"):
        phone = normalize_iq_phone(text)
        if not phone:
            send_message(chat_id, "📱 الرقم مو بصيغة عراقية واضحة. دزه مثل 07xxxxxxxxx أو +9647xxxxxxxxx")
            return
        with WAIT_COND:
            live = CHAT_STATE.setdefault(chat_id, {})
            live["phone_value"] = phone
            live["awaiting_phone"] = False
            WAIT_COND.notify_all()
        send_message(chat_id, "📲 تم استلام الرقم. أكمل هسه...")
        return

    if st.get("awaiting_epr"):
        if not text.startswith("https://www.netflix.com/epr?"):
            send_message(chat_id, "الرابط مو EPR واضح. دز رابط يبدأ بـ https://www.netflix.com/epr?")
            return
        with STATE_LOCK:
            CHAT_STATE[chat_id]["awaiting_epr"] = False
        start_job(chat_id, text)
        return

    aid = str(st.get("target_account") or st.get("selected_account") or "")
    guid = str(st.get("target_guid") or "")
    try:
        if st.get("awaiting_batch_names"):
            mapping = parse_indexed_lines(text, pins=False)
            profiles = batch_profile_names(aid, mapping)
            clear_input_state(chat_id)
            send_message(chat_id, "✅ تم تطبيق أسماء البروفايلات دفعة وحدة:\n" + profile_summary(profiles))
            show_account_menu(chat_id, aid)
            return
        if st.get("awaiting_batch_pins"):
            mapping = parse_indexed_lines(text, pins=True)
            clear_input_state(chat_id)
            launch_pin_batch(chat_id, aid, mapping)
            return
        if st.get("awaiting_single_name"):
            if not text or len(text) > 50:
                raise RuntimeError("الاسم غير صالح")
            single_profile_rename(aid, guid, text)
            clear_input_state(chat_id)
            send_message(chat_id, "✅ تم تغيير اسم البروفايل.")
            show_profile_manager(chat_id, aid, force=True)
            return
        if st.get("awaiting_single_pin"):
            if not re.fullmatch(r"\d{4}", text):
                raise RuntimeError("PIN لازم 4 أرقام")
            clear_input_state(chat_id)
            launch_pin_single(chat_id, aid, guid, text)
            return
        if st.get("awaiting_add_profile"):
            if not text or len(text) > 50:
                raise RuntimeError("اسم البروفايل غير صالح")
            eng = engine_from_account(aid)
            profiles = sync_account_profiles(aid, force=False)
            if len(profiles) >= 5:
                raise RuntimeError("وصلت حد 5 بروفايلات")
            before_guids = {str(p.get("guid") or "") for p in profiles if p.get("guid")}
            guid_new = add_profile(eng, text)
            if guid_new and str(guid_new) not in before_guids:
                profiles.append({"guid": guid_new, "name": text, "avatarKey": "icon26"})
                save_engine_account(eng, account_id=aid, status="active", profiles=profiles)
            else:
                # Some AddProfile responses do not expose the new GUID in the generic id fields.
                # Refresh once, identify the single new GUID, and attach the exact name the owner sent.
                save_engine_account(eng, account_id=aid, status="active", profiles=profiles)
                refreshed = sync_account_profiles(aid, force=True)
                newcomers = [p for p in refreshed if str(p.get("guid") or "") and str(p.get("guid")) not in before_guids]
                if len(newcomers) == 1:
                    newcomers[0]["name"] = text
                    profiles = refreshed
                    save_engine_account(eng, account_id=aid, status="active", profiles=profiles)
                else:
                    profiles = refreshed
            clear_input_state(chat_id)
            send_message(chat_id, "✅ تم إنشاء البروفايل.")
            show_profile_manager(chat_id, aid, force=True)
            return
    except Exception as exc:
        send_message(chat_id, f"❌ {type(exc).__name__}: {exc}")
        return

    send_message(chat_id, "اختار «إنشاء حساب» أو «تسجيل دخول» أو «📂 حساباتي».", keyboard=True)


def poll_forever() -> None:
    print("\nNetflix EPR Telegram V22.14 SIGNUP-ONLY PROXY + ARABIC + EPR RECOVERY + TELEGRAM OTP")
    print("[+] Signup-only proxy through activation; direct Railway login/post-activation management; Arabic-IQ visible sessions + resilient EPR/OTP/password/profiles.")
    offset = 0
    while True:
        try:
            updates = tg_call("getUpdates", {
                "offset": str(offset),
                "timeout": "30",
                "allowed_updates": json.dumps(["message", "callback_query"]),
            }, timeout=40)
            for upd in updates or []:
                offset = max(offset, int(upd.get("update_id", 0)) + 1)
                if upd.get("message"):
                    handle_message(upd["message"])
                elif upd.get("callback_query"):
                    handle_callback(upd["callback_query"])
        except requests.RequestException as exc:
            print(f"[!] Telegram network error: {exc}", flush=True)
            time.sleep(2)
        except KeyboardInterrupt:
            print("\n[+] stopped")
            break
        except Exception as exc:
            print(f"[!] loop error: {type(exc).__name__}: {exc}", flush=True)
            time.sleep(2)


if __name__ == "__main__":
    poll_forever()
