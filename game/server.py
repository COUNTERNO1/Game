#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
幸存者 · 局域网服务器
==================================================================
纯 Python 标准库实现，不需要 Node.js，不需要 pip install 任何东西。

用途：同时提供
  1) 静态文件（index.html 游戏本体）
  2) /api/* 接口（注册、登录、排行榜、进度同步）

启动：
    cd ~/H5Project/game
    python3 server.py            # 默认 8000 端口
    python3 server.py 8080       # 指定端口

然后浏览器 / 手机访问：
    http://localhost:8000
    http://<本机局域网IP>:8000
"""

import base64
import hashlib
import hmac
import json
import mimetypes
import os
import re
import secrets
import socket
import sqlite3
import sys
import threading
import time
import unicodedata
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# =====================================================================
# 路径与常量
# =====================================================================
ROOT = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(ROOT, 'data')
DB_PATH = os.path.join(DATA_DIR, 'survivor.db')

NICK_MIN, NICK_MAX = 1, 12
PASS_MIN, PASS_MAX = 6, 32

SESSION_MS = 90 * 24 * 60 * 60 * 1000      # 90 天

LOCK_FAIL_COUNT = 5                        # 连错 5 次
LOCK_MS = 15 * 60 * 1000                   # 锁 15 分钟

LOGIN_RATE_WINDOW = 10 * 60 * 1000
LOGIN_RATE_MAX = 20

REGISTER_RATE_WINDOW = 60 * 60 * 1000
REGISTER_RATE_MAX = 10

SCORE_MIN_TIME = 0                         # 不再要求通关，任何一局 Hell 都可上榜
SCORE_MAX_TIME = 1800
SCORE_MAX_KILLS = 20000
SCORE_COOLDOWN_MS = 30 * 1000

# 计分权重（与前端 CONFIG.score 一致，服务端才是权威）
SCORE_NORMAL_KILL = 10
SCORE_GREEN_KILL = 30
SCORE_BLUE_KILL = 50
SCORE_ELITE_KILL = 100
SCORE_BOSS_KILL = 200
SCORE_PER_SECOND = 1

MAX_BODY = 64 * 1024

SCRYPT_N = 16384
SCRYPT_R = 8
SCRYPT_P = 1
SCRYPT_KEYLEN = 64
SCRYPT_MAXMEM = 64 * 1024 * 1024

DIFFS = ('easy', 'hard', 'hell')

# =====================================================================
# 数据库
# =====================================================================
SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
  id              INTEGER PRIMARY KEY AUTOINCREMENT,
  nickname        TEXT NOT NULL,
  nickname_norm   TEXT NOT NULL UNIQUE,
  password_hash   TEXT NOT NULL,
  created_at      INTEGER NOT NULL,
  fail_count      INTEGER NOT NULL DEFAULT 0,
  locked_until    INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS sessions (
  id            INTEGER PRIMARY KEY AUTOINCREMENT,
  user_id       INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
  token_hash    TEXT NOT NULL UNIQUE,
  created_at    INTEGER NOT NULL,
  expires_at    INTEGER NOT NULL,
  last_used_at  INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_sessions_user    ON sessions(user_id);
CREATE INDEX IF NOT EXISTS idx_sessions_expires ON sessions(expires_at);

CREATE TABLE IF NOT EXISTS scores (
  id           INTEGER PRIMARY KEY AUTOINCREMENT,
  user_id      INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
  difficulty   TEXT NOT NULL,
  score        REAL NOT NULL DEFAULT 0,
  time         REAL NOT NULL,
  kills        INTEGER NOT NULL,
  normal_kills INTEGER NOT NULL DEFAULT 0,
  elite_kills  INTEGER NOT NULL DEFAULT 0,
  updated_at   INTEGER NOT NULL,
  UNIQUE(user_id, difficulty)
);
CREATE INDEX IF NOT EXISTS idx_scores_diff ON scores(difficulty, score DESC);

CREATE TABLE IF NOT EXISTS progress (
  user_id     INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
  difficulty  TEXT NOT NULL,
  best_time   REAL NOT NULL DEFAULT 0,
  best_kills  INTEGER NOT NULL DEFAULT 0,
  cleared     INTEGER NOT NULL DEFAULT 0,
  updated_at  INTEGER NOT NULL,
  PRIMARY KEY(user_id, difficulty)
);

CREATE TABLE IF NOT EXISTS login_attempts (
  id  INTEGER PRIMARY KEY AUTOINCREMENT,
  ip  TEXT NOT NULL,
  ts  INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_login_ip_ts ON login_attempts(ip, ts);

CREATE TABLE IF NOT EXISTS register_attempts (
  id  INTEGER PRIMARY KEY AUTOINCREMENT,
  ip  TEXT NOT NULL,
  ts  INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_register_ip_ts ON register_attempts(ip, ts);

CREATE TABLE IF NOT EXISTS score_submits (
  user_id  INTEGER NOT NULL,
  ts       INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_score_user ON score_submits(user_id, ts);
"""

_init_lock = threading.Lock()
_initialized = False


def db_connect():
    conn = sqlite3.connect(DB_PATH, timeout=10.0)
    conn.row_factory = sqlite3.Row
    conn.execute('PRAGMA foreign_keys = ON')
    return conn


def _migrate(conn):
    """老数据库补列：scores 表从「时间榜」升级为「分数榜」"""
    cols = {row['name'] for row in conn.execute('PRAGMA table_info(scores)')}
    additions = {
        'score': 'REAL NOT NULL DEFAULT 0',
        'normal_kills': 'INTEGER NOT NULL DEFAULT 0',
        'elite_kills': 'INTEGER NOT NULL DEFAULT 0',
    }
    for name, decl in additions.items():
        if name not in cols:
            conn.execute('ALTER TABLE scores ADD COLUMN %s %s' % (name, decl))


def init_db():
    global _initialized
    with _init_lock:
        if _initialized:
            return
        os.makedirs(DATA_DIR, exist_ok=True)
        conn = db_connect()
        try:
            conn.execute('PRAGMA journal_mode = WAL')
            conn.execute('PRAGMA synchronous = NORMAL')
            conn.executescript(SCHEMA)
            _migrate(conn)
            conn.commit()
        finally:
            conn.close()
        _initialized = True


# =====================================================================
# 工具函数
# =====================================================================
def now_ms():
    return int(time.time() * 1000)


def normalize_nickname(raw):
    if not isinstance(raw, str):
        return ''
    return unicodedata.normalize('NFKC', raw.strip())


def nickname_key(nickname):
    return unicodedata.normalize('NFKC', nickname).lower()


def is_valid_nickname(nickname):
    if not isinstance(nickname, str):
        return False
    if not (NICK_MIN <= len(nickname) <= NICK_MAX):
        return False
    if not nickname.strip():
        return False
    for ch in nickname:
        code = ord(ch)
        if code < 0x20 or code == 0x7F:          # C0 控制符 + DEL
            return False
        if 0x80 <= code <= 0x9F:                 # C1 控制符
            return False
    return True


def is_valid_password(password, nickname=None):
    if not isinstance(password, str):
        return False
    if not (PASS_MIN <= len(password) <= PASS_MAX):
        return False
    if not password.strip():
        return False
    if nickname and password == nickname:
        return False
    return True


def hash_password(password):
    salt = secrets.token_bytes(16)
    dk = hashlib.scrypt(password.encode('utf-8'), salt=salt,
                        n=SCRYPT_N, r=SCRYPT_R, p=SCRYPT_P,
                        dklen=SCRYPT_KEYLEN, maxmem=SCRYPT_MAXMEM)
    return 'scrypt${}${}${}${}${}'.format(
        SCRYPT_N, SCRYPT_R, SCRYPT_P,
        base64.b64encode(salt).decode('ascii'),
        base64.b64encode(dk).decode('ascii'))


def verify_password(password, stored):
    try:
        parts = (stored or '').split('$')
        if len(parts) != 6 or parts[0] != 'scrypt':
            return False
        n, r, p = int(parts[1]), int(parts[2]), int(parts[3])
        salt = base64.b64decode(parts[4])
        expected = base64.b64decode(parts[5])
        test = hashlib.scrypt(password.encode('utf-8'), salt=salt,
                              n=n, r=r, p=p, dklen=len(expected),
                              maxmem=SCRYPT_MAXMEM)
        return hmac.compare_digest(test, expected)
    except Exception:
        return False


def new_token():
    return secrets.token_urlsafe(32)


def hash_token(token):
    return hashlib.sha256(token.encode('utf-8')).hexdigest()


def build_progress(conn, user_id):
    out = {d: {'bestTime': 0, 'bestKills': 0, 'cleared': False} for d in DIFFS}
    rows = conn.execute(
        'SELECT difficulty, best_time, best_kills, cleared FROM progress WHERE user_id = ?',
        (user_id,)).fetchall()
    for row in rows:
        d = row['difficulty']
        if d not in out:
            continue
        out[d] = {
            'bestTime': row['best_time'],
            'bestKills': row['best_kills'],
            'cleared': bool(row['cleared']),
        }
    return out


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


# =====================================================================
# 接口实现
# =====================================================================
def api_nickname_available(ctx):
    name = normalize_nickname((ctx['query'].get('name') or [''])[0])
    if not is_valid_nickname(name):
        return {'available': False, 'reason': 'invalid'}
    conn = ctx['conn']
    row = conn.execute('SELECT 1 FROM users WHERE nickname_norm = ?',
                       (nickname_key(name),)).fetchone()
    return {'available': row is None}


def api_register(ctx):
    ip, t = ctx['ip'], now_ms()
    conn = ctx['conn']

    conn.execute('DELETE FROM register_attempts WHERE ts < ?',
                 (t - REGISTER_RATE_WINDOW * 2,))
    cnt = conn.execute(
        'SELECT COUNT(*) AS c FROM register_attempts WHERE ip = ? AND ts > ?',
        (ip, t - REGISTER_RATE_WINDOW)).fetchone()['c']
    if cnt >= REGISTER_RATE_MAX:
        raise ApiError(429, '注册过于频繁，请稍后再试')

    body = ctx['body']
    nickname = normalize_nickname(body.get('nickname'))
    password = body.get('password') if isinstance(body.get('password'), str) else ''

    if not is_valid_nickname(nickname):
        raise ApiError(400, '昵称需为 1–12 个字符，不能含控制字符')
    if not is_valid_password(password, nickname):
        raise ApiError(400, '密码需为 6–32 个字符，不能与昵称相同')

    key = nickname_key(nickname)
    if conn.execute('SELECT 1 FROM users WHERE nickname_norm = ?', (key,)).fetchone():
        raise ApiError(409, '昵称已被占用')

    try:
        cur = conn.execute(
            'INSERT INTO users (nickname, nickname_norm, password_hash, created_at,'
            ' fail_count, locked_until) VALUES (?, ?, ?, ?, 0, 0)',
            (nickname, key, hash_password(password), t))
    except sqlite3.IntegrityError:
        raise ApiError(409, '昵称已被占用')
    user_id = cur.lastrowid

    conn.execute('INSERT INTO register_attempts (ip, ts) VALUES (?, ?)', (ip, t))

    token = new_token()
    conn.execute(
        'INSERT INTO sessions (user_id, token_hash, created_at, expires_at, last_used_at)'
        ' VALUES (?, ?, ?, ?, ?)',
        (user_id, hash_token(token), t, t + SESSION_MS, t))
    conn.commit()

    return {'nickname': nickname, 'token': token}


def api_login(ctx):
    ip, t = ctx['ip'], now_ms()
    conn = ctx['conn']

    conn.execute('DELETE FROM login_attempts WHERE ts < ?',
                 (t - LOGIN_RATE_WINDOW * 2,))
    cnt = conn.execute(
        'SELECT COUNT(*) AS c FROM login_attempts WHERE ip = ? AND ts > ?',
        (ip, t - LOGIN_RATE_WINDOW)).fetchone()['c']
    if cnt >= LOGIN_RATE_MAX:
        raise ApiError(429, '尝试过于频繁，请稍后再试')

    conn.execute('INSERT INTO login_attempts (ip, ts) VALUES (?, ?)', (ip, t))

    body = ctx['body']
    nickname = normalize_nickname(body.get('nickname'))
    password = body.get('password') if isinstance(body.get('password'), str) else ''

    if not is_valid_nickname(nickname) or not password:
        conn.commit()
        raise ApiError(401, '昵称或密码错误')

    row = conn.execute('SELECT * FROM users WHERE nickname_norm = ?',
                       (nickname_key(nickname),)).fetchone()
    if row is None:
        conn.commit()
        raise ApiError(401, '昵称或密码错误')

    if row['locked_until'] > t:
        conn.commit()
        mins = max(1, (row['locked_until'] - t) // 60000)
        raise ApiError(401, '尝试次数过多，请 %d 分钟后再试' % mins)

    if not verify_password(password, row['password_hash']):
        fails = row['fail_count'] + 1
        locked_until = t + LOCK_MS if fails >= LOCK_FAIL_COUNT else 0
        conn.execute('UPDATE users SET fail_count = ?, locked_until = ? WHERE id = ?',
                     (0 if locked_until else fails, locked_until, row['id']))
        conn.commit()
        if locked_until:
            raise ApiError(401, '尝试次数过多，请 15 分钟后再试')
        raise ApiError(401, '昵称或密码错误')

    conn.execute('UPDATE users SET fail_count = 0, locked_until = 0 WHERE id = ?',
                 (row['id'],))

    token = new_token()
    conn.execute(
        'INSERT INTO sessions (user_id, token_hash, created_at, expires_at, last_used_at)'
        ' VALUES (?, ?, ?, ?, ?)',
        (row['id'], hash_token(token), t, t + SESSION_MS, t))
    conn.commit()

    return {'nickname': row['nickname'], 'token': token,
            'progress': build_progress(conn, row['id'])}


def api_logout(ctx):
    ctx['conn'].execute('DELETE FROM sessions WHERE id = ?', (ctx['session_id'],))
    ctx['conn'].commit()
    return {'ok': True}


def api_me(ctx):
    return {'nickname': ctx['user']['nickname']}


def api_rename(ctx):
    user = ctx['user']
    conn = ctx['conn']
    nickname = normalize_nickname(ctx['body'].get('nickname'))
    if not is_valid_nickname(nickname):
        raise ApiError(400, '昵称需为 1–12 个字符，不能含控制字符')

    key = nickname_key(nickname)
    if key == user['nickname_norm']:
        return {'nickname': user['nickname']}

    if conn.execute('SELECT 1 FROM users WHERE nickname_norm = ? AND id != ?',
                    (key, user['id'])).fetchone():
        raise ApiError(409, '昵称已被占用')

    try:
        conn.execute('UPDATE users SET nickname = ?, nickname_norm = ? WHERE id = ?',
                     (nickname, key, user['id']))
        conn.commit()
    except sqlite3.IntegrityError:
        raise ApiError(409, '昵称已被占用')
    return {'nickname': nickname}


def api_change_password(ctx):
    user = ctx['user']
    conn = ctx['conn']
    old = ctx['body'].get('oldPassword') or ''
    new = ctx['body'].get('newPassword') or ''

    if not verify_password(old, user['password_hash']):
        raise ApiError(401, '旧密码错误')
    if not is_valid_password(new, user['nickname']):
        raise ApiError(400, '新密码需为 6–32 个字符，不能与昵称相同')

    conn.execute('UPDATE users SET password_hash = ? WHERE id = ?',
                 (hash_password(new), user['id']))
    conn.execute('DELETE FROM sessions WHERE user_id = ? AND id != ?',
                 (user['id'], ctx['session_id']))
    conn.commit()
    return {'ok': True}


def api_score(ctx):
    body = ctx['body']
    difficulty = str(body.get('difficulty') or '')

    if difficulty != 'hell':
        raise ApiError(400, '当前只有 hell 难度进入排行榜')

    try:
        time_val = float(body.get('time'))
        normal = int(body.get('normalKills') or 0)
        green = int(body.get('greenKills') or 0)
        blue = int(body.get('blueKills') or 0)
        elite = int(body.get('eliteKills') or 0)
        boss = int(body.get('bossKills') or 0)
    except (TypeError, ValueError):
        raise ApiError(400, '成绩参数不合法')

    if not (SCORE_MIN_TIME <= time_val <= SCORE_MAX_TIME):
        raise ApiError(400, '成绩时间超出合法范围')
    if min(normal, green, blue, elite, boss) < 0:
        raise ApiError(400, '击杀数超出合法范围')
    kills = normal + green + blue + elite + boss
    if kills > SCORE_MAX_KILLS:
        raise ApiError(400, '击杀数超出合法范围')

    # 服务端自己算分，不信任客户端传来的分数
    score = (normal * SCORE_NORMAL_KILL
             + green * SCORE_GREEN_KILL
             + blue * SCORE_BLUE_KILL
             + elite * SCORE_ELITE_KILL
             + boss * SCORE_BOSS_KILL
             + int(time_val) * SCORE_PER_SECOND)

    conn, t, uid = ctx['conn'], now_ms(), ctx['user']['id']

    conn.execute('DELETE FROM score_submits WHERE ts < ?', (t - SCORE_COOLDOWN_MS * 2,))
    last = conn.execute('SELECT MAX(ts) AS last FROM score_submits WHERE user_id = ?',
                        (uid,)).fetchone()['last'] or 0
    if t - last < SCORE_COOLDOWN_MS:
        raise ApiError(429, '提交过于频繁，请稍后再试')
    conn.execute('INSERT INTO score_submits (user_id, ts) VALUES (?, ?)', (uid, t))

    existing = conn.execute('SELECT * FROM scores WHERE user_id = ? AND difficulty = ?',
                            (uid, 'hell')).fetchone()
    improved = existing is None or score > existing['score']

    if improved:
        conn.execute(
            'INSERT INTO scores (user_id, difficulty, score, time, kills,'
            ' normal_kills, elite_kills, updated_at)'
            ' VALUES (?, ?, ?, ?, ?, ?, ?, ?)'
            ' ON CONFLICT(user_id, difficulty) DO UPDATE SET'
            '   score = excluded.score, time = excluded.time, kills = excluded.kills,'
            '   normal_kills = excluded.normal_kills, elite_kills = excluded.elite_kills,'
            '   updated_at = excluded.updated_at',
            (uid, 'hell', score, time_val, kills, normal, elite, t))
    conn.commit()

    best = conn.execute('SELECT * FROM scores WHERE user_id = ? AND difficulty = ?',
                        (uid, 'hell')).fetchone()
    better = conn.execute(
        'SELECT COUNT(*) AS c FROM scores WHERE difficulty = ? AND score > ?',
        ('hell', best['score'])).fetchone()['c']

    return {'rank': better + 1,
            'score': score,
            'best': {'score': best['score'], 'time': best['time'], 'kills': best['kills']},
            'improved': improved}


def api_leaderboard(ctx):
    query = ctx['query']
    difficulty = str((query.get('difficulty') or ['hell'])[0])
    try:
        limit = int((query.get('limit') or ['20'])[0])
    except ValueError:
        limit = 20
    if limit <= 0:
        limit = 20
    limit = min(limit, 100)

    conn = ctx['conn']
    rows = conn.execute(
        'SELECT s.user_id, s.score, s.time, s.kills, u.nickname FROM scores s'
        ' JOIN users u ON u.id = s.user_id'
        ' WHERE s.difficulty = ? ORDER BY s.score DESC, s.updated_at ASC LIMIT ?',
        (difficulty, limit)).fetchall()

    user = ctx['user']
    lst = [{
        'rank': i + 1,
        'name': r['nickname'],
        'score': r['score'],
        'time': r['time'],
        'kills': r['kills'],
        'mine': bool(user and r['user_id'] == user['id']),
    } for i, r in enumerate(rows)]

    me = None
    if user:
        s = conn.execute('SELECT * FROM scores WHERE user_id = ? AND difficulty = ?',
                         (user['id'], difficulty)).fetchone()
        if s:
            better = conn.execute(
                'SELECT COUNT(*) AS c FROM scores WHERE difficulty = ? AND score > ?',
                (difficulty, s['score'])).fetchone()['c']
            me = {'rank': better + 1, 'score': s['score'],
                  'time': s['time'], 'kills': s['kills']}

    return {'list': lst, 'me': me}


def api_progress_get(ctx):
    return build_progress(ctx['conn'], ctx['user']['id'])


def api_progress_put(ctx):
    body = ctx['body'].get('progress')
    if not isinstance(body, dict):
        raise ApiError(400, '参数错误')

    conn, t, uid = ctx['conn'], now_ms(), ctx['user']['id']
    for d in DIFFS:
        p = body.get(d)
        if not isinstance(p, dict):
            continue
        try:
            bt = max(0.0, float(p.get('bestTime') or 0))
            bk = max(0, int(p.get('bestKills') or 0))
        except (TypeError, ValueError):
            continue
        cl = 1 if p.get('cleared') else 0
        conn.execute(
            'INSERT INTO progress (user_id, difficulty, best_time, best_kills,'
            ' cleared, updated_at) VALUES (?, ?, ?, ?, ?, ?)'
            ' ON CONFLICT(user_id, difficulty) DO UPDATE SET'
            '   best_time  = MAX(best_time,  excluded.best_time),'
            '   best_kills = MAX(best_kills, excluded.best_kills),'
            '   cleared    = MAX(cleared,    excluded.cleared),'
            '   updated_at = excluded.updated_at',
            (uid, d, bt, bk, cl, t))
    conn.commit()
    return build_progress(conn, uid)


# 路由表：(method, path) -> (处理函数, 是否必须登录)
ROUTES = {
    ('GET', '/api/health'): (lambda ctx: {'ok': True, 'time': now_ms()}, False),
    ('GET', '/api/nickname-available'): (api_nickname_available, False),
    ('POST', '/api/register'): (api_register, False),
    ('POST', '/api/login'): (api_login, False),
    ('POST', '/api/logout'): (api_logout, True),
    ('GET', '/api/me'): (api_me, True),
    ('POST', '/api/rename'): (api_rename, True),
    ('POST', '/api/change-password'): (api_change_password, True),
    ('POST', '/api/score'): (api_score, True),
    ('GET', '/api/leaderboard'): (api_leaderboard, False),
    ('GET', '/api/progress'): (api_progress_get, True),
    ('PUT', '/api/progress'): (api_progress_put, True),
}


# =====================================================================
# HTTP 处理
# =====================================================================
class Handler(BaseHTTPRequestHandler):
    server_version = 'SurvivorServer/1.0'
    protocol_version = 'HTTP/1.1'

    # ---------- 基础 ----------
    def log_message(self, fmt, *args):
        sys.stderr.write('[%s] %s\n' % (self.log_date_time_string(), fmt % args))

    def _send_json(self, status, obj):
        payload = json.dumps(obj, ensure_ascii=False).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(payload)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(payload)

    def _read_json_body(self):
        try:
            length = int(self.headers.get('Content-Length') or 0)
        except ValueError:
            length = 0
        if length <= 0:
            return {}
        if length > MAX_BODY:
            raise ApiError(413, '请求体过大')
        raw = self.rfile.read(length)
        if not raw:
            return {}
        try:
            data = json.loads(raw.decode('utf-8'))
        except (ValueError, UnicodeDecodeError):
            raise ApiError(400, '请求体不是合法 JSON')
        return data if isinstance(data, dict) else {}

    def _client_ip(self):
        fwd = self.headers.get('X-Forwarded-For')
        if fwd:
            return fwd.split(',')[0].strip()
        return self.client_address[0] if self.client_address else 'unknown'

    def _bearer(self):
        header = self.headers.get('Authorization') or ''
        match = re.match(r'^Bearer\s+(.+)$', header, re.I)
        return match.group(1).strip() if match else None

    # ---------- 分发 ----------
    def do_GET(self):
        self._dispatch('GET')

    def do_POST(self):
        self._dispatch('POST')

    def do_PUT(self):
        self._dispatch('PUT')

    def do_HEAD(self):
        self._dispatch('GET', head=True)

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header('Allow', 'GET, POST, PUT, OPTIONS')
        self.send_header('Content-Length', '0')
        self.end_headers()

    def _dispatch(self, method, head=False):
        parsed = urlparse(self.path)
        path = unquote(parsed.path)
        if path.startswith('/api/') or path == '/api':
            return self._handle_api(method, path, parsed.query)
        return self._serve_static(path, head=head)

    # ---------- API ----------
    def _handle_api(self, method, path, query_string):
        entry = ROUTES.get((method, path))
        if entry is None:
            # 路径存在但方法不对 → 405
            if any(p == path for (_, p) in ROUTES):
                return self._send_json(405, {'error': '方法不被允许'})
            return self._send_json(404, {'error': '接口不存在'})

        func, need_auth = entry
        conn = None
        try:
            body = self._read_json_body() if method in ('POST', 'PUT') else {}
            query = parse_qs(query_string)

            user = None
            session_id = None
            conn = db_connect()

            token = self._bearer()
            if token:
                session = conn.execute(
                    'SELECT * FROM sessions WHERE token_hash = ?',
                    (hash_token(token),)).fetchone()
                if session and session['expires_at'] >= now_ms():
                    user = conn.execute('SELECT * FROM users WHERE id = ?',
                                        (session['user_id'],)).fetchone()
                    if user is not None:
                        session_id = session['id']
                        conn.execute(
                            'UPDATE sessions SET expires_at = ?, last_used_at = ? WHERE id = ?',
                            (now_ms() + SESSION_MS, now_ms(), session_id))

            if need_auth and user is None:
                raise ApiError(401, '登录已过期，请重新登录')

            ctx = {
                'body': body,
                'query': query,
                'ip': self._client_ip(),
                'conn': conn,
                'user': user,
                'session_id': session_id,
            }
            result = func(ctx)
            self._send_json(200, result)
        except ApiError as e:
            self._send_json(e.status, {'error': e.message})
        except Exception as e:  # noqa: BLE001
            sys.stderr.write('[server error] %r\n' % (e,))
            self._send_json(500, {'error': '服务器内部错误'})
        finally:
            if conn is not None:
                conn.close()

    # ---------- 静态文件 ----------
    def _serve_static(self, path, head=False):
        if path in ('/', ''):
            path = '/index.html'

        rel = path.lstrip('/')
        full = os.path.abspath(os.path.join(ROOT, rel))

        # 防目录穿越 & 禁止下载数据库/源码
        if not full.startswith(ROOT + os.sep):
            return self._send_text(403, '403 Forbidden')
        if full.startswith(DATA_DIR + os.sep) or full == DATA_DIR:
            return self._send_text(403, '403 Forbidden')
        if rel.startswith('.') or os.path.basename(full) in ('server.py', 'survivor.db'):
            return self._send_text(403, '403 Forbidden')

        if os.path.isdir(full):
            full = os.path.join(full, 'index.html')

        if not os.path.isfile(full):
            return self._send_text(404, '404 Not Found')

        ctype = mimetypes.guess_type(full)[0] or 'application/octet-stream'
        if ctype.startswith('text/') or ctype in ('application/javascript', 'application/json'):
            ctype += '; charset=utf-8'

        try:
            with open(full, 'rb') as fh:
                data = fh.read()
        except OSError:
            return self._send_text(500, '500 Internal Server Error')

        self.send_response(200)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store, must-revalidate')
        self.end_headers()
        if not head:
            self.wfile.write(data)

    def _send_text(self, status, text):
        payload = text.encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'text/plain; charset=utf-8')
        self.send_header('Content-Length', str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)


# =====================================================================
# 清理线程 & 启动
# =====================================================================
def cleanup_loop():
    while True:
        time.sleep(6 * 60 * 60)
        try:
            conn = db_connect()
            t = now_ms()
            conn.execute('DELETE FROM sessions WHERE expires_at < ?', (t,))
            conn.execute('DELETE FROM login_attempts WHERE ts < ?',
                         (t - 24 * 3600 * 1000,))
            conn.execute('DELETE FROM register_attempts WHERE ts < ?',
                         (t - 24 * 3600 * 1000,))
            conn.execute('DELETE FROM score_submits WHERE ts < ?',
                         (t - 24 * 3600 * 1000,))
            conn.commit()
            conn.close()
        except Exception as e:  # noqa: BLE001
            sys.stderr.write('[cleanup] %r\n' % (e,))


def lan_ip():
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.connect(('8.8.8.8', 80))
        ip = sock.getsockname()[0]
        sock.close()
        return ip
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
        except OSError:
            return '127.0.0.1'


def main():
    port = 8000
    if len(sys.argv) > 1:
        try:
            port = int(sys.argv[1])
        except ValueError:
            print('端口号不合法，用法：python3 server.py [端口]')
            sys.exit(1)
    port = int(os.environ.get('PORT', port))

    init_db()
    threading.Thread(target=cleanup_loop, daemon=True).start()

    mimetypes.add_type('application/javascript', '.js')
    mimetypes.add_type('text/css', '.css')

    try:
        httpd = ThreadingHTTPServer(('0.0.0.0', port), Handler)
    except OSError as e:
        if e.errno in (48, 98):  # macOS / Linux 的 “Address already in use”
            print('启动失败：端口 %d 已被占用。' % port)
            print('  1) 先看是谁占着：lsof -nP -iTCP:%d -sTCP:LISTEN' % port)
            print('  2) 或者换个端口：python3 server.py %d' % (port + 1))
        else:
            print('启动失败：%r' % (e,))
        sys.exit(1)

    httpd.daemon_threads = True
    ip = lan_ip()

    print('=' * 45)
    print(' 幸存者服务器已启动（Python 版）')
    print(' 监听：0.0.0.0:%d' % port)
    print(' 本机访问：http://localhost:%d' % port)
    print(' 手机访问：http://%s:%d' % (ip, port))
    print(' 数据库：%s' % DB_PATH)
    print(' 停止服务：Ctrl+C')
    print('=' * 45)

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print('\n正在关闭…')
    finally:
        httpd.shutdown()
        httpd.server_close()


if __name__ == '__main__':
    main()
