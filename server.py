import hashlib, hmac, io, json, math, os, random, secrets, threading, time, urllib.parse, urllib.request
import psycopg
from contextlib import contextmanager
from fastapi import FastAPI, Header, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, HTMLResponse, Response
from fastapi.staticfiles import StaticFiles
import telebot
from telebot.types import InlineKeyboardButton as IBtn, InlineKeyboardMarkup as IKB, KeyboardButton as KBtn, ReplyKeyboardMarkup as RKB, ReplyKeyboardRemove, WebAppInfo, BotCommand, BotCommandScopeChat

TOKEN = os.environ.get('BOT_TOKEN', '').strip().strip("'\"")
try: ADMIN_ID = int(os.environ.get('ADMIN_ID', '0').strip().strip("'\"") or '0')
except Exception: ADMIN_ID = 0

DEFAULT_URL = 'https://jano-bingo-e8m6.onrender.com'
APP_URL = (os.environ.get('APP_URL') or DEFAULT_URL).strip().strip("'\"").rstrip('/')
APP_URL = ('https://' + APP_URL[8:]) if APP_URL.lower().startswith('https://') else DEFAULT_URL

SUPPORT = '@janobingosupport1'
TB_NAME = os.environ.get('TELEBIRR_NAME', 'SINSHAW JEMANEH ESHETE')
TB_PHONE = os.environ.get('TELEBIRR_PHONE', '0941882333')
DATABASE_URL = os.environ.get('DATABASE_URL', '').strip().strip("'\"")
HOUSE_CUT, CD_SEC, CALL_SEC, WIN_SEC = 0.20, 60, 3.0, 10
MIN_PLAYERS = int(os.environ.get('MIN_PLAYERS', '2') or '2')
db_lock, room_lock = threading.RLock(), threading.RLock()

class HybridRow:
  def __init__(self, names, values):
    self._names, self._values = names, values
    self._map = dict(zip(names, values))
  def __getitem__(self, key):
    return self._map[key] if isinstance(key, str) else self._values[key]
  def __iter__(self):
    return iter(self._values)
  def __len__(self):
    return len(self._values)
  def keys(self):
    return self._names

class PGCursor:
  def __init__(self, cursor, lastrowid=None):
    self._cursor, self.lastrowid = cursor, lastrowid
    self._names = [d.name for d in cursor.description] if cursor.description else []
  @property
  def rowcount(self):
    return self._cursor.rowcount
  def fetchone(self):
    row = self._cursor.fetchone()
    return HybridRow(self._names, row) if row is not None else None
  def fetchall(self):
    return [HybridRow(self._names, row) for row in self._cursor.fetchall()]

class PGConnection:
  def __init__(self, conn):
    self._conn = conn
  def execute(self, sql, params=()):
    statement = sql.strip().replace('BEGIN IMMEDIATE', 'BEGIN')
    ignore = statement.upper().startswith('INSERT OR IGNORE INTO')
    if ignore:
      statement = statement.replace('INSERT OR IGNORE INTO', 'INSERT INTO', 1)
      statement += ' ON CONFLICT DO NOTHING'
    wants_id = statement.upper().startswith('INSERT INTO REQUESTS ')
    if wants_id:
      statement += ' RETURNING id'
    statement = statement.replace('?', '%s')
    cur = self._conn.execute(statement, params)
    lastrowid = None
    if wants_id:
      inserted = cur.fetchone()
      if inserted is not None:
        lastrowid = inserted[0]
    return PGCursor(cur, lastrowid)

@contextmanager
def get_db():
  if not DATABASE_URL:
    raise RuntimeError('DATABASE_URL is not configured. Add your Neon connection string in Render environment variables.')
  with db_lock:
    conn = psycopg.connect(DATABASE_URL)
    c = PGConnection(conn)
    try:
      yield c
      conn.commit()
    except Exception:
      conn.rollback()
      raise
    finally:
      conn.close()

def init_db():
  with get_db() as c:
    c.execute("""CREATE TABLE IF NOT EXISTS users (
      uid BIGINT PRIMARY KEY, name TEXT DEFAULT 'Player', phone TEXT,
      play_wallet DOUBLE PRECISION DEFAULT 0, win_wallet DOUBLE PRECISION DEFAULT 0,
      matches_played INTEGER DEFAULT 0, wins INTEGER DEFAULT 0,
      total_won DOUBLE PRECISION DEFAULT 0, referred_by BIGINT, created_at BIGINT)""")
    # Merge legacy Play + Win balances into one balance; safe on every restart.
    c.execute("UPDATE users SET play_wallet=COALESCE(play_wallet,0)+COALESCE(win_wallet,0), win_wallet=0 WHERE COALESCE(win_wallet,0)<>0")
    c.execute("""CREATE TABLE IF NOT EXISTS transactions (
      id BIGSERIAL PRIMARY KEY, uid BIGINT, icon TEXT, title TEXT,
      amount DOUBLE PRECISION, created_at BIGINT)""")
    c.execute("""CREATE TABLE IF NOT EXISTS requests (
      id BIGSERIAL PRIMARY KEY, req_type TEXT, uid BIGINT, amount DOUBLE PRECISION,
      method TEXT, details TEXT, status TEXT DEFAULT 'pending',
      created_at BIGINT, reference TEXT)""")
    c.execute("""CREATE TABLE IF NOT EXISTS house_stats (
      id INTEGER PRIMARY KEY CHECK (id=1),
      total_commission DOUBLE PRECISION DEFAULT 0,
      total_rounds INTEGER DEFAULT 0)""")
    # Bot leaderboard is separate from user wallets: virtual winnings affect rank only.
    c.execute("""CREATE TABLE IF NOT EXISTS bot_rankings (
      name TEXT PRIMARY KEY,
      wins INTEGER DEFAULT 0,
      total_won DOUBLE PRECISION DEFAULT 0)""")
    c.execute("""CREATE TABLE IF NOT EXISTS room_cards (
      stake INTEGER NOT NULL, card_no INTEGER NOT NULL, uid BIGINT NOT NULL,
      name TEXT NOT NULL, grid TEXT NOT NULL,
      PRIMARY KEY (stake, card_no))""")
    c.execute('INSERT INTO house_stats (id,total_commission,total_rounds) VALUES (1,0,0) ON CONFLICT (id) DO NOTHING')
    c.execute("CREATE UNIQUE INDEX IF NOT EXISTS uq_requests_reference ON requests(reference) WHERE reference IS NOT NULL AND reference <> ''")

def recover_interrupted_games():
  # Any cards still recorded at startup belong to an unfinished round.
  # Refund them atomically, then clear the persisted round-card records.
  with get_db() as c:
    rows = c.execute('SELECT stake,card_no,uid FROM room_cards').fetchall()
    for row in rows:
      cur = c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (row['stake'], row['uid']))
      if cur.rowcount == 1:
        add_tx(c, row['uid'], '↩️', f'የተቋረጠ ጨዋታ ካርድ #{row["card_no"]} ተመላሽ', row['stake'])
    c.execute('DELETE FROM room_cards')
  return len(rows)

def ensure_user(uid, name='Player', ref=None):
  with get_db() as c:
    r = c.execute('SELECT * FROM users WHERE uid=?', (uid,)).fetchone()
    if not r:
      c.execute('INSERT INTO users (uid,name,play_wallet,win_wallet,referred_by,created_at) VALUES (?,?,0,0,?,?)', (uid, name or 'Player', ref, int(time.time())))
      r = c.execute('SELECT * FROM users WHERE uid=?', (uid,)).fetchone()
    elif name and name != 'Player' and r['name'] != name:
      c.execute('UPDATE users SET name=? WHERE uid=?', (name, uid))
      r = c.execute('SELECT * FROM users WHERE uid=?', (uid,)).fetchone()
    return dict(r)

def add_tx(c, uid, ic, title, amt):
  c.execute('INSERT INTO transactions (uid,icon,title,amount,created_at) VALUES (?,?,?,?,?)', (uid, ic, title, float(amt), int(time.time())))

def gen_card(no):
  rng = random.SystemRandom()
  cols = [rng.sample(range(a, b + 1), 5) for a, b in [(1,15),(16,30),(31,45),(46,60),(61,75)]]
  return ['FREE' if (r == 2 and c == 2) else cols[c][r] for r in range(5) for c in range(5)]

WIN_LINES = [[0,1,2,3,4],[5,6,7,8,9],[10,11,12,13,14],[15,16,17,18,19],[20,21,22,23,24],
             [0,5,10,15,20],[1,6,11,16,21],[2,7,12,17,22],[3,8,13,18,23],[4,9,14,19,24],
             [0,6,12,18,24],[4,8,12,16,20],[0,4,20,24]]
check_win = lambda g, cs: next((ln for ln in WIN_LINES if all(g[i] == 'FREE' or g[i] in cs for i in ln)), None)
mk_room = lambda s: {'stake': s, 'phase': 'WAITING', 'countdown': CD_SEC, 'cards': {}, 'called': [], 'deck': [], 'tick': time.time(), 'winner': None, 'win_until': 0.0, 'last_bot_count': 0, 'bot_queue': [], 'bot_start_at': None, 'bot_index': 0}
rooms = {10: mk_room(10), 20: mk_room(20), 50: mk_room(50)}
BOT_NAMES = ['Abel','Hana','Dawit','Selam','Meron','Natnael','Liya','Bereket','Rahel','Yonatan','Eden','Sami','Tigist','Mikiyas','Meseret','Amanuel','Hirut','Fitsum','Biniam','Martha','Robel','Saron','Henok','Bethlehem','Yared']
def seed_bots(r):
  rng = random.SystemRandom()
  counts = [n for n in range(15, 21) if n != r.get('last_bot_count')]
  bot_count = rng.choice(counts)
  r['last_bot_count'] = bot_count
  # Bots are queued, not preloaded. Each gets a unique random second in the 55-second selection window.
  offsets = sorted(rng.sample(range(1, 56), bot_count))
  names = rng.sample(BOT_NAMES, bot_count)
  r['bot_queue'] = [{'name': name, 'at': offset} for name, offset in zip(names, offsets)]
  # Begin the staggered bot selection immediately when this round is seeded.
  r['bot_start_at'] = time.time()
  r['bot_index'] = 0
for room in rooms.values():
  if room['stake'] == 10:
    seed_bots(room)
real_players = lambda r: len({v['uid'] for v in r['cards'].values() if v['uid'] > 0})
bot_players = lambda r: sum(1 for v in r['cards'].values() if v.get('is_bot'))
n_players = lambda r: real_players(r) + bot_players(r)
# Every reserved card contributes its room stake, including bot cards paid with virtual credits.
paid_cards = lambda r: len(r['cards'])
derash = lambda r: round(paid_cards(r) * r['stake'] * (1.0 - HOUSE_CUT), 2)

def finish_round(r, uid, name, cno, wl):
  prize = derash(r)
  is_bot = uid < 0
  if is_bot:
    # Bots receive the same virtual derash for ranking, but never a wallet credit or payout.
    comm = round(paid_cards(r) * r['stake'] - prize, 2)
    with get_db() as c:
      c.execute('''INSERT INTO bot_rankings (name,wins,total_won) VALUES (?,1,?)
                   ON CONFLICT (name) DO UPDATE SET wins=bot_rankings.wins+1,
                   total_won=bot_rankings.total_won+EXCLUDED.total_won''', (name, prize))
      c.execute('UPDATE house_stats SET total_commission=total_commission+?, total_rounds=total_rounds+1 WHERE id=1', (comm,))
      c.execute('DELETE FROM room_cards WHERE stake=?', (r['stake'],))
    r['phase'], r['win_until'] = 'WINNER', time.time() + WIN_SEC
    r['winner'] = {'uid': uid, 'name': name, 'card_no': cno, 'prize': prize, 'grid': r['cards'][cno]['grid'], 'win_line': wl, 'is_bot': True}
    return
  comm = round(paid_cards(r) * r['stake'] - prize, 2)
  with get_db() as c:
    c.execute('UPDATE users SET play_wallet=play_wallet+?, wins=wins+1, total_won=total_won+? WHERE uid=?', (prize, prize, uid))
    add_tx(c, uid, '🏆', f'BINGO አሸነፉ! (Card #{cno})', prize)
    c.execute('UPDATE house_stats SET total_commission=total_commission+?, total_rounds=total_rounds+1 WHERE id=1', (comm,))
    # Remove all cards in this completed round in the same transaction as payout.
    c.execute('DELETE FROM room_cards WHERE stake=?', (r['stake'],))
  r['phase'], r['win_until'] = 'WINNER', time.time() + WIN_SEC
  r['winner'] = {'uid': uid, 'name': name, 'card_no': cno, 'prize': prize, 'grid': r['cards'][cno]['grid'], 'win_line': wl, 'is_bot': False}

def reset_room(r):
  # Clear completed round cards. Bot cards are memory-only and never enter the wallet database.
  with get_db() as c:
    c.execute('DELETE FROM room_cards WHERE stake=?', (r['stake'],))
  r.update({'phase': 'WAITING', 'countdown': CD_SEC, 'cards': {}, 'called': [], 'deck': [], 'winner': None, 'tick': time.time()})
  if r['stake'] == 10:
    seed_bots(r)
  else:
    r.update({'bot_queue': [], 'bot_start_at': None, 'bot_index': 0})

def game_loop():
  while True:
    now = time.time()
    with room_lock:
      for r in rooms.values():
        # Bots begin selecting cards automatically as soon as a round is seeded,
        # even when no real player has joined yet.
        if r['stake'] == 10 and r['bot_start_at'] is not None and r['phase'] in ('WAITING', 'COUNTDOWN'):
          elapsed = now - r['bot_start_at']
          while r['bot_index'] < len(r['bot_queue']) and elapsed >= r['bot_queue'][r['bot_index']]['at']:
            used = set(r['cards'])
            available = [n for n in range(1, 401) if n not in used]
            if not available: break
            i = r['bot_index']
            cno = random.SystemRandom().choice(available)
            name = r['bot_queue'][i]['name']
            r['cards'][cno] = {'uid': -(i + 1), 'name': name, 'grid': gen_card(cno), 'is_bot': True}
            r['bot_index'] += 1
        pc = n_players(r)
        # The first reserved card (bot or real player) starts the 60-second countdown.
        # Bots may play a complete round without any real players.
        if r['phase'] == 'WAITING' and pc >= 1:
          r.update({'phase': 'COUNTDOWN', 'countdown': CD_SEC, 'tick': now})
        elif r['phase'] == 'COUNTDOWN':
          if now - r['tick'] >= 1.0:
            r['tick'], r['countdown'] = now, r['countdown'] - 1
            if r['countdown'] <= 0:
              r.update({'phase': 'PLAYING', 'called': [], 'deck': list(range(1, 76)), 'tick': now})
              secrets.SystemRandom().shuffle(r['deck'])
              with get_db() as c:
                for uid in {v['uid'] for v in r['cards'].values() if v['uid'] > 0}:
                  c.execute('UPDATE users SET matches_played=matches_played+1 WHERE uid=?', (uid,))
        elif r['phase'] == 'PLAYING' and now - r['tick'] >= CALL_SEC:
          r['tick'] = now
          if r['deck']:
            r['called'].insert(0, r['deck'].pop())
            # Check every card immediately after each called number.
            # The first completed card ends the round; bots receive no payout.
            cs, won = set(r['called']), False
            candidates = list(r['cards'].items())
            random.SystemRandom().shuffle(candidates)
            for cno, info in candidates:
              wl = check_win(info['grid'], cs)
              if wl:
                finish_round(r, info['uid'], info['name'], cno, wl)
                won = True
                break
          else:
            reset_room(r)
        elif r['phase'] == 'WINNER' and now >= r['win_until']:
          reset_room(r)
    time.sleep(0.35)

def auth_user(init_data: str):
  if not init_data or not TOKEN:
    raise HTTPException(401, 'እባክዎ አፑን በቴሌግራም ቦት ውስጥ ብቻ ይክፈቱ!')
  try:
    pairs = urllib.parse.parse_qsl(init_data, keep_blank_values=True)
    if len(dict(pairs)) != len(pairs):
      raise ValueError('duplicate fields')
    p = dict(pairs)
    rh = p.pop('hash', None)
    dc = '\n'.join(f'{k}={v}' for k, v in sorted(p.items()))
    sec = hmac.new(b'WebAppData', TOKEN.encode(), hashlib.sha256).digest()
    expected = hmac.new(sec, dc.encode(), hashlib.sha256).hexdigest()
    if not rh or not hmac.compare_digest(expected, rh):
      raise ValueError('invalid hash')
    auth_date = int(p.get('auth_date', '0'))
    now = int(time.time())
    if auth_date <= 0 or auth_date > now + 30 or now - auth_date > 86400:
      raise ValueError('expired initData')
    uo = json.loads(p.get('user', '{}'))
    uid = int(uo['id'])
    if uid <= 0:
      raise ValueError('invalid user')
    nm = ' '.join(x for x in [uo.get('first_name'), uo.get('last_name')] if x) or 'Player'
    return ensure_user(uid, nm)
  except Exception:
    raise HTTPException(401, 'የTelegram መግቢያ መረጃ ተሳስቷል ወይም ጊዜው አልፎበታል። እባክዎ አፑን እንደገና ይክፈቱ!')

bot = telebot.TeleBot(TOKEN) if TOKEN else None
is_adm = lambda uid: ADMIN_ID != 0 and int(uid) == int(ADMIN_ID)

def ensure_welcome_banner():
  os.makedirs('static', exist_ok=True)
  path = 'static/jano-bingo-welcome.jpg'
  if os.path.exists(path): return path
  w, h = 960, 600
  im = Image.new('RGB', (w, h))
  px = im.load()
  for y in range(h):
    for x in range(w):
      glow = max(0, 1 - (((x-w/2)/(w*.8))**2 + ((y-h/2)/(h*.9))**2)**.5)
      px[x,y] = (int(18+38*glow), int(4+5*glow), int(48+105*glow))
  d = ImageDraw.Draw(im)
  d.rounded_rectangle((14,14,w-14,h-14), radius=54, outline=(255,190,35), width=12)
  d.rounded_rectangle((30,30,w-30,h-30), radius=42, outline=(176,70,255), width=5)
  font_path = '/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf'
  def font(size):
    try: return ImageFont.truetype(font_path, size)
    except Exception: return ImageFont.load_default()
  # Crown above the JANO wordmark
  cx = w//2
  d.polygon([(cx-120,155),(cx-88,78),(cx-38,122),(cx,48),(cx+38,122),(cx+88,78),(cx+120,155)], fill=(255,190,30), outline=(255,235,130))
  d.rounded_rectangle((cx-124,145,cx+124,174), radius=10, fill=(255,190,30), outline=(255,235,130), width=5)
  def centered(txt, y, f, color, stroke=(20,0,35), sw=9):
    b=d.textbbox((0,0),txt,font=f,stroke_width=sw)
    d.text(((w-(b[2]-b[0]))//2,y),txt,font=f,fill=color,stroke_width=sw,stroke_fill=stroke)
  centered('JANO',170,font(142),(255,207,48))
  centered('BINGO',320,font(126),(220,62,255))
  for x,y,n,c in [(115,300,'7',(40,125,255)),(845,300,'5',(240,65,80)),(155,465,'12',(40,200,110)),(805,465,'36',(155,80,255))]:
    d.ellipse((x-52,y-52,x+52,y+52),fill=c,outline='white',width=7)
    f=font(42); b=d.textbbox((0,0),n,font=f)
    d.text((x-(b[2]-b[0])/2,y-(b[3]-b[1])/2-5),n,font=f,fill='white')
  centered('PLAY  •  WIN  •  ENJOY',510,font(34),(255,220,100),sw=2)
  im.save(path, 'JPEG', quality=88, optimize=True)
  return path

def menu_kb(uid=None):
  kb = IKB()
  kb.row(IBtn('🎮 Play JANO BINGO', web_app=WebAppInfo(url=APP_URL)))
  kb.row(IBtn('💰 Deposit', callback_data='home_deposit'), IBtn('💸 Withdraw', callback_data='home_withdraw'))
  kb.row(IBtn('💳 Balance', callback_data='home_balance'), IBtn('👥 Invite Friends', callback_data='home_invite'))
  kb.row(IBtn('🎯 Game Patterns', web_app=WebAppInfo(url=APP_URL)), IBtn('📖 Instructions', callback_data='home_rules'))
  kb.row(IBtn('📝 Register', callback_data='home_register'), IBtn('🎧 Support', url=f'https://t.me/{SUPPORT.lstrip("@")}'))
  if uid and is_adm(uid):
    kb.row(IBtn('👑 Admin Panel', callback_data='home_admin'))
  return kb

def play_kb(lbl='🎲 Play JANO BINGO'):
  kb = IKB(); kb.add(IBtn(lbl, web_app=WebAppInfo(url=APP_URL))); return kb

def adm_kb():
  kb = IKB()
  kb.row(IBtn('📊 ሪፖርትና ትርፍ', callback_data='adm_stats'), IBtn('👥 ተጫዋቾች', callback_data='adm_users'))
  kb.row(IBtn('➕ ብር ጨምር', callback_data='adm_add'), IBtn('➖ ብር ቀንስ', callback_data='adm_sub'))
  kb.row(IBtn(f'⚙️ ዝቅተኛ ተጫዋች: {MIN_PLAYERS}', callback_data='adm_minp'), IBtn('💾 DB Backup', callback_data='adm_backup'))
  kb.row(IBtn('📢 ለሁሉም መልዕክት ላክ', callback_data='adm_bcast'))
  return kb

def notify_req(rtype, uid, amt, md, det, reference=None):
  u = ensure_user(uid)
  with get_db() as c:
    rid = c.execute('INSERT INTO requests (req_type,uid,amount,method,details,status,created_at,reference) VALUES (?,?,?,?,?,?,?,?)',
                    (rtype, uid, float(amt), md, det, 'pending', int(time.time()), reference)).lastrowid
  if not bot or ADMIN_ID == 0: return rid
  kb = IKB()
  if rtype == 'deposit':
    hdr = '🔔 አዲስ የገቢ (DEPOSIT) ጥያቄ!'
    kb.row(IBtn('✅ ፍቀድ', callback_data=f'ap_dep_{rid}'), IBtn('❌ ሰርዝ', callback_data=f'rj_dep_{rid}'))
  else:
    hdr = '🔔 አዲስ የወጪ (WITHDRAW) ጥያቄ!'
    kb.row(IBtn('✅ ተልኳል', callback_data=f'ap_wd_{rid}'), IBtn('❌ ሰርዝና መልስ', callback_data=f'rj_wd_{rid}'))
  try: bot.send_message(ADMIN_ID, f'{hdr}\n\n🆔 #{rid}\n👤 {u["name"]} (ID: {uid})\n📞 {u["phone"] or "-"}\n💵 {float(amt):.2f} ETB\n🏦 {md}\n📝 {det}', reply_markup=kb)
  except Exception: pass
  return rid


def addis_voice_sample():
  api_key = os.environ.get('ADDIS_API_KEY', '').strip()
  if not api_key:
    raise RuntimeError('ADDIS_API_KEY is not configured on this service.')
  base = 'https://api.addisassistant.com'
  headers = {'x-api-key': api_key, 'Content-Type': 'application/json'}
  text = 'ሰላም፣ የጃኖ ቢንጎ ተጫዋቾች። ቢ አስራ ሁለት።'
  payload = {'text': text, 'voice_id': 'am-yohanes-calm', 'language': 'am', 'output_format': 'mp3_44100'}
  def post_json(path, body):
    req = urllib.request.Request(base + '/api/v1' + path, data=json.dumps(body).encode('utf-8'), headers=headers, method='POST')
    try:
      with urllib.request.urlopen(req, timeout=45) as response:
        return json.loads(response.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
      detail = e.read().decode('utf-8', errors='replace')
      raise RuntimeError(f'Addis AI HTTP {e.code}: {detail[:500]}') from None
  estimate = post_json('/voice/estimate', payload)
  est = estimate.get('data', estimate)
  if est.get('can_generate') is False:
    raise RuntimeError('Addis AI reports insufficient voice-generation balance.')
  request_id = 'jano-voice-sample-' + secrets.token_hex(12)
  generated = post_json('/voice/generations', dict(payload, client_request_id=request_id))
  data = generated.get('data', generated)
  audio_url = data.get('audio_url')
  if not audio_url:
    raise RuntimeError('Addis AI did not return an audio URL.')
  req = urllib.request.Request(audio_url, headers={'User-Agent': 'JANO-BINGO/1.0'})
  with urllib.request.urlopen(req, timeout=45) as response:
    audio = io.BytesIO(response.read())
  audio.name = 'jano-bingo-amharic-male-sample.mp3'
  audio.seek(0)
  return audio, est.get('estimated_cost'), data.get('id')


if bot:

  @bot.message_handler(commands=['voicesample'])
  def c_voice_sample(m):
    if not is_adm(m.from_user.id):
      return bot.reply_to(m, '⛔ ለአድሚን ብቻ!')
    if not os.environ.get('ADDIS_API_KEY', '').strip():
      return bot.reply_to(m, '❌ ADDIS_API_KEY በ Neon test Render ላይ አልተገኘም።')
    status = bot.reply_to(m, '🎙️ የአማርኛ የወንድ ድምፅ ናሙና እየተዘጋጀ ነው...')
    try:
      audio, cost, clip_id = addis_voice_sample()
      bot.send_audio(m.chat.id, audio, caption='🎙️ JANO BINGO — Yohannes የአማርኛ ድምፅ ናሙና')
      note = '✅ ናሙናው ተልኳል። ድምፁን ያዳምጡና ይወስኑ።'
      if cost is not None: note += f'\nየተገመተ ወጪ: {cost} ETB'
      bot.send_message(m.chat.id, note)
    except Exception as e:
      print('Addis voice sample error:', type(e).__name__, str(e)[:300])
      bot.send_message(m.chat.id, '❌ የድምፅ ናሙና ማዘጋጀት አልተሳካም። Render logs ይፈትሹ።')

  @bot.message_handler(commands=['myid'])
  def c_myid(m): bot.reply_to(m, f'🆔 የአንተ Telegram ID፦ `{m.from_user.id}`', parse_mode='Markdown')

  @bot.message_handler(commands=['admin'])
  @bot.message_handler(func=lambda m: m.text == '👑 Admin Panel')
  def c_admin(m):
    if not is_adm(m.from_user.id): return bot.reply_to(m, '⛔ ለአድሚን ብቻ!')
    bot.send_message(m.chat.id, '👑 JANO BINGO — የአድሚን መቆጣጠሪያ', reply_markup=adm_kb())

  @bot.message_handler(commands=['menu'])
  def c_menu(m):
    with open(ensure_welcome_banner(), 'rb') as photo:
      bot.send_photo(m.chat.id, photo, caption=f'👋 ሰላም {m.from_user.first_name or "Player"}!\n\n🎉 Welcome to JANO BINGO!\nYour exciting bingo game starts here. Choose an option below 👇', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(commands=['start'])
  def c_start(m):
    ps = (m.text or '').split()
    ref = int(ps[1]) if len(ps) > 1 and ps[1].isdigit() and int(ps[1]) != m.from_user.id else None
    u = ensure_user(m.from_user.id, m.from_user.first_name or 'Player', ref)
    if not u['phone']:
      kb = RKB(resize_keyboard=True, one_time_keyboard=True); kb.add(KBtn('📱 ስልክ ቁጥር አጋራ', request_contact=True))
      return bot.send_message(m.chat.id, '👑 እንኳን ወደ JANO BINGO በደህና መጡ!\n\nለመመዝገብ ስልክ ቁጥርዎን ያጋሩ 👇', reply_markup=kb)
    with open(ensure_welcome_banner(), 'rb') as photo:
      bot.send_photo(m.chat.id, photo, caption=f'👋 ሰላም {m.from_user.first_name or "Player"}!\n\n🎉 Welcome to JANO BINGO!\nYour exciting bingo game starts here. Choose an option below 👇', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(content_types=['contact'])
  def c_contact(m):
    ensure_user(m.from_user.id, m.from_user.first_name or 'Player')
    with get_db() as c: c.execute('UPDATE users SET phone=? WHERE uid=?', (m.contact.phone_number, m.from_user.id))
    bot.send_message(m.chat.id, f'✅ ተመዝግበዋል! ({m.contact.phone_number})', reply_markup=ReplyKeyboardRemove())
    bot.send_message(m.chat.id, '👋 Welcome to JANO BINGO! Choose an option below 👇', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(commands=['play'])
  @bot.message_handler(func=lambda m: m.text == '🎮 Play JANO BINGO')
  def c_play(m): bot.send_message(m.chat.id, 'Good luck JANO BINGO 🍀', reply_markup=play_kb('🎲 Play JANO BINGO'))

  @bot.message_handler(commands=['balance'])
  @bot.message_handler(func=lambda m: m.text == '💳 ባላንስ (Balance)')
  def c_bal(m):
    u = ensure_user(m.from_user.id, m.from_user.first_name or 'Player')
    bot.send_message(m.chat.id, f'💰 ጠቅላላ ባላንስ: {u["play_wallet"]:.2f} ETB', reply_markup=play_kb('🎲 Play'))

  @bot.message_handler(commands=['deposit'])
  @bot.message_handler(func=lambda m: m.text == '💰 ገቢ (Deposit)')
  def c_dep(m):
    kb = IKB(); kb.row(IBtn('📲 TeleBirr', callback_data='dep_TeleBirr'), IBtn('🏦 CBE Birr', callback_data='dep_CBE'))
    bot.send_message(m.chat.id, '💳 የክፍያ አማራጭ ይምረጡ፦', reply_markup=kb)

  @bot.callback_query_handler(func=lambda c: c.data in ('dep_TeleBirr', 'dep_CBE'))
  def cb_dep(call):
    bot.answer_callback_query(call.id); md = 'CBE Birr' if call.data.endswith('_CBE') else 'TeleBirr'
    bot.register_next_step_handler(bot.send_message(call.message.chat.id, f'💵 በ {md} የሚያስገቡትን መጠን ይጻፉ (ዝቅተኛ 20 ETB)፦'), s_dep_amt, md)

  def s_dep_amt(m, md):
    try:
      amt = float((m.text or '').strip())
      if not math.isfinite(amt) or amt < 20 or amt > 1000000:
        return bot.reply_to(m, '❌ 20 ETB እስከ 1,000,000 ETB ያለ ትክክለኛ መጠን ያስገቡ።')
    except Exception: return bot.reply_to(m, '❌ ትክክለኛ ቁጥር ያስገቡ።')
    bot.register_next_step_handler(bot.send_message(m.chat.id, f'🏦 {md}\n👤 {TB_NAME}\n📱 {TB_PHONE}\n💵 {amt:.2f} ETB\n\nከላኩ በኋላ የSMS Transaction ID ይላኩ 👇'), s_dep_tx, amt, md)

  def s_dep_tx(m, amt, md):
    tx = (m.text or '').strip()
    if len(tx) < 4 or len(tx) > 120: return bot.reply_to(m, '❌ ትክክለኛ Transaction ID ያስገቡ።')
    try: notify_req('deposit', m.from_user.id, amt, md, f'TX: {tx}', reference=tx)
    except psycopg.IntegrityError: return bot.reply_to(m, '❌ ይህ Transaction ID ቀድሞ ተጠቅሟል።')
    bot.reply_to(m, f'✅ የ {amt:.2f} ETB ገቢ ጥያቄዎ ለአድሚን ተልኳል!', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(commands=['withdraw'])
  @bot.message_handler(func=lambda m: m.text == '💸 ወጪ (Withdraw)')
  def c_wd(m):
    kb = IKB(); kb.row(IBtn('📲 TeleBirr', callback_data='wd_TeleBirr'), IBtn('🏦 CBE Birr', callback_data='wd_CBE'))
    bot.send_message(m.chat.id, '💸 ወደ የትኛው አካውንት ማውጣት ይፈልጋሉ?', reply_markup=kb)

  @bot.callback_query_handler(func=lambda c: c.data in ('wd_TeleBirr', 'wd_CBE'))
  def cb_wd(call):
    bot.answer_callback_query(call.id); md = 'CBE Birr' if call.data.endswith('_CBE') else 'TeleBirr'
    bot.register_next_step_handler(bot.send_message(call.message.chat.id, f'💸 በ {md} የሚወጣውን መጠን ይጻፉ (ዝቅተኛ 100 ETB)፦'), s_wd_amt, md)

  def s_wd_amt(m, md):
    u = ensure_user(m.from_user.id)
    try: amt = float((m.text or '').strip())
    except Exception: return bot.reply_to(m, '❌ ትክክለኛ ቁጥር ያስገቡ።')
    if not math.isfinite(amt) or amt < 100 or amt > 1000000 or u['play_wallet'] < amt:
      return bot.reply_to(m, f'❌ 100–1,000,000 ETB ያስገቡ እና በቂ ባላንስ እንዳለ ያረጋግጡ ({u["play_wallet"]:.2f} ETB)።')
    bot.register_next_step_handler(bot.reply_to(m, f'📱 የ {md} ስልክ/አካውንት ቁጥርዎን ያስገቡ፦'), s_wd_acc, amt, md)

  def s_wd_acc(m, amt, md):
    acc = (m.text or '').strip()
    if len(acc) < 6 or len(acc) > 64:
      return bot.reply_to(m, '❌ ትክክለኛ የስልክ/አካውንት ቁጥር ያስገቡ።')
    try:
      with get_db() as c:
        c.execute('BEGIN IMMEDIATE')
        u = c.execute('SELECT play_wallet FROM users WHERE uid=?', (m.from_user.id,)).fetchone()
        if not u or not math.isfinite(float(amt)) or amt < 100 or u['play_wallet'] < amt:
          return bot.reply_to(m, '❌ በቂ ባላንስ የለዎትም ወይም የገንዘብ መጠኑ ትክክል አይደለም!')
        cur = c.execute('UPDATE users SET play_wallet=play_wallet-? WHERE uid=? AND play_wallet>=?', (amt, m.from_user.id, amt))
        if cur.rowcount != 1:
          return bot.reply_to(m, '❌ በቂ ባላንስ የለዎትም!')
        add_tx(c, m.from_user.id, '💸', f'የወጪ ጥያቄ ({md})', -amt)
        rid = c.execute('INSERT INTO requests (req_type,uid,amount,method,details,status,created_at) VALUES (?,?,?,?,?,?,?)',
                        ('withdraw', m.from_user.id, amt, md, f'Acc: {acc}', 'pending', int(time.time()))).lastrowid
      if bot and ADMIN_ID:
        kb = IKB(); kb.row(IBtn('✅ ተልኳል', callback_data=f'ap_wd_{rid}'), IBtn('❌ ሰርዝና መልስ', callback_data=f'rj_wd_{rid}'))
        try: bot.send_message(ADMIN_ID, f'🔔 አዲስ የወጪ ጥያቄ!\n\n🆔 #{rid}\n👤 {m.from_user.first_name or "Player"} (ID: {m.from_user.id})\n💵 {amt:.2f} ETB\n🏦 {md}\n📱 {acc}', reply_markup=kb)
        except Exception: pass
      bot.reply_to(m, f'✅ የ {amt:.2f} ETB የወጪ ጥያቄዎ ተመዝግቧል።', reply_markup=menu_kb(m.from_user.id))
    except psycopg.Error:
      bot.reply_to(m, '❌ ጥያቄውን ማስመዝገብ አልተቻለም። እባክዎ እንደገና ይሞክሩ።')

  @bot.callback_query_handler(func=lambda c: c.data.startswith(('adm_', 'ap_', 'rj_')))
  def cb_adm(call):
    global MIN_PLAYERS
    if not is_adm(call.from_user.id): return bot.answer_callback_query(call.id, '⛔ ለአድሚን ብቻ!', show_alert=True)
    d = call.data; bot.answer_callback_query(call.id)
    if d == 'adm_stats':
      with get_db() as c:
        uc = c.execute('SELECT COUNT(*) FROM users').fetchone()[0]
        pw = c.execute('SELECT COALESCE(SUM(play_wallet),0) FROM users').fetchone()[0]
        
        pn = c.execute("SELECT COUNT(*) FROM requests WHERE status='pending'").fetchone()[0]
        hs = c.execute('SELECT total_commission,total_rounds FROM house_stats WHERE id=1').fetchone()
      with room_lock: lv = ' | '.join(f'{k}ብር:{n_players(r)}ሰው({r["phase"]})' for k, r in rooms.items())
      bot.send_message(call.message.chat.id, f'📊 ሪፖርት\n👥 ተጫዋቾች: {uc}\n💰 Player balances: {pw:.2f} ETB\n💰 ትርፍ(20%): {hs["total_commission"]:.2f} ETB\n🎲 ዙሮች: {hs["total_rounds"]}\n⏳ ጥያቄዎች: {pn}\n🔴 {lv}')
    elif d == 'adm_users':
      with get_db() as c: rows = c.execute('SELECT * FROM users ORDER BY created_at DESC LIMIT 20').fetchall()
      bot.send_message(call.message.chat.id, '\n'.join(f'• {r["name"]} (`{r["uid"]}`) | Balance:{r["play_wallet"]:.1f} ETB' for r in rows) or 'ምንም ተጫዋች የለም።', parse_mode='Markdown')
    elif d in ('adm_add', 'adm_sub'):
      act = 'add' if d == 'adm_add' else 'sub'
      bot.register_next_step_handler(bot.send_message(call.message.chat.id, '✏️ ID እና መጠን ይላኩ (ምሳሌ፦ `528672685 100`)', parse_mode='Markdown'), s_adm_bal, act)
    elif d == 'adm_minp':
      MIN_PLAYERS = 1 if MIN_PLAYERS >= 3 else MIN_PLAYERS + 1
      bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=adm_kb())
      bot.send_message(call.message.chat.id, f'⚙️ ዝቅተኛ ተጫዋች ወደ {MIN_PLAYERS} ተቀይሯል።')
    elif d == 'adm_backup':
      bot.send_message(call.message.chat.id, '💾 Database is hosted on Neon PostgreSQL. Use Neon backup/restore tools for database backups.')
    elif d == 'adm_bcast':
      bot.register_next_step_handler(bot.send_message(call.message.chat.id, '📢 ለሁሉም የሚላከውን መልዕክት ይጻፉ፦'), s_bcast)
    elif d.startswith(('ap_', 'rj_')):
      act, rt, rid = d.split('_')
      with get_db() as c:
        c.execute('BEGIN IMMEDIATE')
        rq = c.execute('SELECT * FROM requests WHERE id=? FOR UPDATE', (int(rid),)).fetchone()
        if not rq or rq['status'] != 'pending': return bot.send_message(call.message.chat.id, '⚠️ ቀድሞ ተወስኗል።')
        uid, amt = rq['uid'], rq['amount']
        if rt == 'dep' and act == 'ap':
          c.execute("UPDATE requests SET status='approved' WHERE id=?", (int(rid),))
          c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (amt, uid))
          add_tx(c, uid, '💰', f'ገቢ ጸድቋል ({rq["method"]})', amt)
          u = c.execute('SELECT referred_by FROM users WHERE uid=?', (uid,)).fetchone()
          if u and u['referred_by']:
            c.execute('UPDATE users SET play_wallet=play_wallet+15 WHERE uid=?', (u['referred_by'],))
            c.execute('UPDATE users SET referred_by=NULL WHERE uid=?', (uid,))
            add_tx(c, u['referred_by'], '🎁', 'የግብዣ ሽልማት', 15.0)
          bot.edit_message_text(call.message.text + f'\n\n✅ ጸድቋል (+{amt:.2f} ETB)', call.message.chat.id, call.message.message_id)
          try: bot.send_message(uid, f'🎉 የ {amt:.2f} ETB ገቢዎ ጸድቋል!')
          except Exception: pass
        elif rt == 'dep':
          c.execute("UPDATE requests SET status='rejected' WHERE id=?", (int(rid),))
          bot.edit_message_text(call.message.text + '\n\n❌ ተሰርዟል', call.message.chat.id, call.message.message_id)
          try: bot.send_message(uid, f'❌ የ {amt:.2f} ETB ገቢ ጥያቄዎ ተቀባይነት አላገኘም። እባክዎ አድሚንን ያነጋግሩ።')
          except Exception: pass
        elif rt == 'wd' and act == 'ap':
          c.execute("UPDATE requests SET status='paid' WHERE id=?", (int(rid),))
          bot.edit_message_text(call.message.text + f'\n\n✅ ተልኳል ({amt:.2f} ETB)', call.message.chat.id, call.message.message_id)
          try: bot.send_message(uid, f'✅ የ {amt:.2f} ETB ወጪዎ ተልኳል!')
          except Exception: pass
        else:
          c.execute("UPDATE requests SET status='rejected' WHERE id=?", (int(rid),))
          c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (amt, uid))
          add_tx(c, uid, '↩️', 'ወጪ ተመልሷል', amt)
          bot.edit_message_text(call.message.text + '\n\n❌ ተሰርዞ ተመልሷል', call.message.chat.id, call.message.message_id)

  def s_adm_bal(m, act):
    if not is_adm(m.from_user.id): return
    try:
      u_s, a_s = (m.text or '').strip().split()
      uid, amt = int(u_s), float(a_s)
      if uid <= 0 or not math.isfinite(amt) or amt <= 0 or amt > 1000000: raise ValueError()
      ensure_user(uid)
      with get_db() as c:
        if act == 'add': c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (amt, uid)); add_tx(c, uid, '🎁', 'አድሚን ጨምሯል', amt)
        else: c.execute('UPDATE users SET play_wallet=GREATEST(0,play_wallet-?) WHERE uid=?', (amt, uid)); add_tx(c, uid, '➖', 'አድሚን ቀንሷል', -amt)
        pw = c.execute('SELECT play_wallet FROM users WHERE uid=?', (uid,)).fetchone()[0]
      bot.reply_to(m, f'✅ ተስተካክሏል! ID `{uid}` Play: {pw:.2f} ETB', parse_mode='Markdown')
    except Exception: bot.reply_to(m, '❌ ምሳሌ፦ `528672685 100`', parse_mode='Markdown')

  def s_bcast(m):
    if not is_adm(m.from_user.id): return
    with get_db() as c: uids = [r[0] for r in c.execute('SELECT uid FROM users').fetchall()]
    s = 0
    for u in uids:
      try: bot.send_message(u, f'📢 ማስታወቂያ\n\n{m.text}'); s += 1
      except Exception: pass
    bot.reply_to(m, f'✅ ለ {s} ተጫዋቾች ተልኳል።')

  @bot.message_handler(commands=['invite'])
  @bot.message_handler(func=lambda m: m.text == '👥 ግብዣ (Invite)')
  def c_inv(m):
    me = bot.get_me()
    bot.send_message(m.chat.id, f'🎁 ለእያንዳንዱ ስኬታማ ግብዣ 15 ETB ይሸለሙ!\n🔗 https://t.me/{me.username}?start={m.from_user.id}')

  @bot.message_handler(commands=['register'])
  @bot.message_handler(func=lambda m: m.text == '📝 ምዝገባ (Register)')
  def c_reg(m):
    kb = RKB(resize_keyboard=True, one_time_keyboard=True); kb.add(KBtn('📱 ስልክ ቁጥር አጋራ', request_contact=True))
    bot.send_message(m.chat.id, '📱 ስልክ ቁጥርዎን ያጋሩ 👇', reply_markup=kb)

  @bot.message_handler(commands=['support'])
  @bot.message_handler(func=lambda m: m.text == '🎧 ድጋፍ (Support)')
  def c_sup(m):
    support_url = f"https://t.me/{SUPPORT.lstrip('@')}"
    kb = IKB(); kb.add(IBtn('💬 የድጋፍ ቡድንን ያነጋግሩ / Contact Support', url=support_url))
    bot.send_message(m.chat.id, f'🎧 የJANO BINGO ድጋፍ\n\nለእርዳታ ከዚህ ይጻፉ፦ {SUPPORT}\n\nContact our support account:', reply_markup=kb, disable_web_page_preview=True)

  @bot.callback_query_handler(func=lambda c: c.data and c.data.startswith('home_'))
  def cb_home_menu(call):
    bot.answer_callback_query(call.id)
    uid = call.from_user.id
    if call.data == 'home_deposit':
      c_dep(call.message)
    elif call.data == 'home_withdraw':
      c_wd(call.message)
    elif call.data == 'home_balance':
      u = ensure_user(uid, call.from_user.first_name or 'Player')
      bot.send_message(call.message.chat.id, f'💰 ጠቅላላ ባላንስ: {u["play_wallet"]:.2f} ETB')
    elif call.data == 'home_invite':
      me = bot.get_me()
      bot.send_message(call.message.chat.id, f'🎁 ለእያንዳንዱ ስኬታማ ግብዣ 15 ETB ይሸለሙ!\n🔗 https://t.me/{me.username}?start={uid}')
    elif call.data == 'home_register':
      kb = RKB(resize_keyboard=True, one_time_keyboard=True)
      kb.add(KBtn('📱 ስልክ ቁጥር አጋራ', request_contact=True))
      bot.send_message(call.message.chat.id, '📱 ለመመዝገብ ስልክ ቁጥርዎን ያጋሩ 👇', reply_markup=kb)
    elif call.data == 'home_rules':
      c_rules(call.message)
    elif call.data == 'home_admin':
      if is_adm(uid): bot.send_message(call.message.chat.id, '👑 JANO BINGO — የአድሚን መቆጣጠሪያ', reply_markup=adm_kb())

  @bot.message_handler(commands=['rules'])
  @bot.message_handler(func=lambda m: m.text == '📜 ህግና መመሪያ')
  def c_rules(m): bot.send_message(m.chat.id, '📜 ህግና መመሪያ\n• ቢያንስ 2 ተጫዋቾች ካርድ ሲገዙ ይጀምራል።\n• ካርድ: 10/20/50 ብር (እስከ 4)።\n• ደራሽ: 80% ለአሸናፊው።\n• ዝቅተኛ ወጪ: 100 ETB።')

def run_bot():
  if not bot: return print('WARNING: BOT_TOKEN not set; bot polling skipped.')
  try:
    # Telegram's native Menu button will show these slash commands.
    public_commands = [
      BotCommand('start', 'Start JANO BINGO'),
      BotCommand('menu', 'Open the main menu'),
      BotCommand('play', 'Play JANO BINGO'),
      BotCommand('balance', 'Check your balance'),
      BotCommand('deposit', 'Deposit funds'),
      BotCommand('withdraw', 'Withdraw funds'),
      BotCommand('invite', 'Invite friends'),
      BotCommand('register', 'Register your phone number'),
      BotCommand('support', 'Contact support'),
      BotCommand('rules', 'Game rules')
    ]
    bot.set_my_commands(public_commands)
    if ADMIN_ID:
      bot.set_my_commands(public_commands + [BotCommand('admin', 'Open admin panel'), BotCommand('myid', 'Show Telegram ID'), BotCommand('voicesample', 'Generate Amharic voice sample')], scope=BotCommandScopeChat(ADMIN_ID))
    print('Telegram command menu configured.')
  except Exception as e:
    print('Telegram command menu setup error:', e)
  while True:
    try: bot.infinity_polling(timeout=20, long_polling_timeout=15)
    except Exception as e: print('Bot error:', e); time.sleep(5)

app = FastAPI(title='JANO BINGO Live')
allowed_origins = [x.strip().rstrip('/') for x in os.environ.get('CORS_ORIGINS', APP_URL).split(',') if x.strip()]
app.add_middleware(CORSMiddleware, allow_origins=allowed_origins, allow_methods=['GET', 'POST'], allow_headers=['Content-Type', 'X-Tg-Init-Data'])
if os.path.isdir('sounds'): app.mount('/sounds', StaticFiles(directory='sounds'), name='sounds')
if os.path.isdir('static'): app.mount('/static', StaticFiles(directory='static'), name='static')

@app.on_event('startup')
def on_startup():
  init_db()
  refunded = recover_interrupted_games()
  if refunded: print(f'Recovered interrupted game: refunded {refunded} card(s).')
  threading.Thread(target=game_loop, daemon=True).start()
  threading.Thread(target=run_bot, daemon=True).start()

@app.get('/health')
def health(): return {'ok': True, 'time': int(time.time())}

@app.head('/')
def head_root(): return Response(status_code=200)

@app.get('/', response_class=HTMLResponse)
def serve_app(): return FileResponse('index.html') if os.path.exists('index.html') else HTMLResponse('index.html missing', 404)

@app.get('/api/state')
def api_state(stake: int = 10, x_tg_init_data: str = Header(default='')):
  u = auth_user(x_tg_init_data)
  if stake not in rooms: raise HTTPException(400, 'ልክ ያልሆነ የጨዋታ ክፍል!')
  r = rooms[stake]
  with room_lock:
    my_c = sorted([k for k, v in r['cards'].items() if v['uid'] == u['uid']])
    tk_c = sorted([k for k, v in r['cards'].items() if v['uid'] != u['uid']])
    snap = {'stake': r['stake'], 'phase': r['phase'], 'countdown': r['countdown'], 'players': n_players(r),
            'min_players': max(3, MIN_PLAYERS),
            'total_cards': len(r['cards']), 'derash': derash(r),
            'taken_cards': tk_c, 'my_cards': my_c, 'my_boards': {str(n): r['cards'][n]['grid'] for n in my_c},
            'called': r['called'], 'winner': r['winner'],  # Bot winner details are exposed only during the winner screen.
            'winner_left': max(0, int(r['win_until'] - time.time())) if r['phase'] == 'WINNER' else 0}
  with get_db() as c:
    txs = [dict(x) for x in c.execute('SELECT icon,title,amount,created_at FROM transactions WHERE uid=? ORDER BY id DESC LIMIT 25', (u['uid'],)).fetchall()]
    top = [dict(x) for x in c.execute("""SELECT name,total_won FROM (
      SELECT name,total_won FROM users WHERE total_won>0
      UNION ALL
      SELECT name,total_won FROM bot_rankings WHERE total_won>0
    ) winners ORDER BY total_won DESC LIMIT 10""").fetchall()]
  return {'user': {'uid': u['uid'], 'name': u['name'], 'play_wallet': round(u['play_wallet'],2), 'matches_played': u['matches_played'], 'wins': u['wins']},
          'config': {'telebirr_name': TB_NAME, 'telebirr_phone': TB_PHONE, 'support': SUPPORT}, 'room': snap, 'history': txs, 'rank': top}

@app.post('/api/buy_card')
async def api_buy(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  try: st, cno = int(b.get('stake', 10)), int(b.get('card_no', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'ልክ ያልሆነ ካርድ!')
  if st not in rooms or not (1 <= cno <= 400): raise HTTPException(400, 'ልክ ያልሆነ ካርድ!')
  with room_lock:
    r = rooms[st]
    if r['phase'] not in ('WAITING', 'COUNTDOWN'): raise HTTPException(400, 'ጨዋታው ተጀምሯል!')
    if cno in r['cards']:
      if r['cards'][cno]['uid'] == u['uid']:
        with get_db() as c:
          c.execute('BEGIN IMMEDIATE')
          c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (st, u['uid']))
          add_tx(c, u['uid'], '↩️', f'ካርድ #{cno} ተሰርዟል', st)
          c.execute('DELETE FROM room_cards WHERE stake=? AND card_no=? AND uid=?', (st, cno, u['uid']))
        del r['cards'][cno]
        return {'ok': True, 'action': 'removed'}
      raise HTTPException(400, f'ካርድ #{cno} ተይዟል!')
    if sum(1 for v in r['cards'].values() if v['uid'] == u['uid']) >= 4: raise HTTPException(400, 'እስከ 4 ካርድ ብቻ!')
    grid = gen_card(cno)
    with get_db() as c:
      c.execute('BEGIN IMMEDIATE')
      wallet = c.execute('SELECT play_wallet FROM users WHERE uid=?', (u['uid'],)).fetchone()
      if not wallet or wallet['play_wallet'] < st: raise HTTPException(400, 'በቂ ባላንስ የለዎትም! ገቢ ያድርጉ።')
      c.execute('UPDATE users SET play_wallet=play_wallet-? WHERE uid=?', (st, u['uid']))
      add_tx(c, u['uid'], '🎴', f'ካርድ #{cno} ({st} ብር)', -st)
      c.execute('INSERT INTO room_cards (stake,card_no,uid,name,grid) VALUES (?,?,?,?,?)',
                (st, cno, u['uid'], u['name'], json.dumps(grid)))
    r['cards'][cno] = {'uid': u['uid'], 'name': u['name'], 'grid': grid}
    return {'ok': True, 'action': 'bought'}

@app.post('/api/claim_bingo')
async def api_claim(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  try: st, cno = int(b.get('stake', 10)), int(b.get('card_no', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'ልክ ያልሆነ ክፍል/ካርድ!')
  if st not in rooms or not (1 <= cno <= 400): raise HTTPException(400, 'ልክ ያልሆነ ክፍል/ካርድ!')
  with room_lock:
    r = rooms[st]
    if r['phase'] != 'PLAYING': raise HTTPException(400, 'ጨዋታው አልተጀመረም!')
    own = r['cards'].get(cno)
    if not own or own['uid'] != u['uid']: raise HTTPException(403, 'ይህ ካርድ የእርስዎ አይደለም!')
    wl = check_win(own['grid'], set(r['called']))
    if not wl: raise HTTPException(400, 'ገና BINGO አልተሟላም!')
    finish_round(r, u['uid'], u['name'], cno, wl)
    return {'ok': True, 'prize': r['winner']['prize']}

@app.post('/api/deposit')
async def api_dep(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  try: amt = float(b.get('amount', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'የገንዘብ መጠኑ ትክክል አይደለም!')
  tx = str(b.get('tx_id', '')).strip()
  if not math.isfinite(amt) or amt < 20 or amt > 1000000 or len(tx) < 4 or len(tx) > 120:
    raise HTTPException(400, 'ዝቅተኛ 20 ETB፣ ትክክለኛ Transaction ID እና ተገቢ መጠን ያስገቡ!')
  try: notify_req('deposit', u['uid'], amt, 'TeleBirr/CBE Birr', f'App TX: {tx}', reference=tx)
  except psycopg.IntegrityError: raise HTTPException(409, 'ይህ Transaction ID ቀድሞ ተጠቅሟል!')
  return {'ok': True}

@app.post('/api/withdraw')
async def api_wd(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  try: amt = float(b.get('amount', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'የገንዘብ መጠኑ ትክክል አይደለም!')
  ph = str(b.get('phone', '')).strip()
  method = str(b.get('method', '')).strip()
  if method not in ('TeleBirr', 'CBE Birr'):
    raise HTTPException(400, 'የክፍያ ዘዴ ይምረጡ!')
  if not math.isfinite(amt) or amt < 100 or amt > 1000000 or len(ph) < 9 or len(ph) > 32:
    raise HTTPException(400, 'ዝቅተኛ 100 ETB እና ትክክለኛ ስልክ ያስገቡ!')
  with get_db() as c:
    c.execute('BEGIN IMMEDIATE')
    row = c.execute('SELECT play_wallet FROM users WHERE uid=?', (u['uid'],)).fetchone()
    if not row or row['play_wallet'] < amt: raise HTTPException(400, 'በቂ ባላንስ የለዎትም!')
    cur = c.execute('UPDATE users SET play_wallet=play_wallet-? WHERE uid=? AND play_wallet>=?', (amt, u['uid'], amt))
    if cur.rowcount != 1: raise HTTPException(409, 'ባላንሱ ተቀይሯል፤ እንደገና ይሞክሩ።')
    add_tx(c, u['uid'], '💸', f'የወጪ ጥያቄ ({ph})', -amt)
    rid = c.execute('INSERT INTO requests (req_type,uid,amount,method,details,status,created_at) VALUES (?,?,?,?,?,?,?)',
                    ('withdraw', u['uid'], amt, method, f'App Phone: {ph}', 'pending', int(time.time()))).lastrowid
  try:
    if bot and ADMIN_ID:
      kb = IKB()
      kb.row(IBtn('✅ ተልኳል', callback_data=f'ap_wd_{rid}'), IBtn('❌ ሰርዝና መልስ', callback_data=f'rj_wd_{rid}'))
      bot.send_message(ADMIN_ID, f'🔔 አዲስ የወጪ ጥያቄ!\n\n🆔 #{rid}\n👤 {u["name"]} (ID: {u["uid"]})\n💵 {amt:.2f} ETB\n📱 {ph}', reply_markup=kb)
  except Exception:
    pass
  return {'ok': True}
