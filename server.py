import hashlib, hmac, io, json, math, os, random, secrets, threading, time, urllib.parse, urllib.request
from zoneinfo import ZoneInfo
import psycopg
from contextlib import contextmanager
from fastapi import FastAPI, Header, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, HTMLResponse, Response
from fastapi.staticfiles import StaticFiles
import telebot
from PIL import Image, ImageDraw, ImageFont
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
HOUSE_CUT, CD_SEC, CALL_SEC, WIN_SEC = 0.20, 40, 3.0, 10
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
    c.execute("CREATE TABLE IF NOT EXISTS bot_settings (setting_key TEXT PRIMARY KEY, image_data BYTEA, updated_at BIGINT)")
    c.execute("CREATE TABLE IF NOT EXISTS daily_promo_sends (send_date TEXT NOT NULL, slot TEXT NOT NULL, sent_at BIGINT NOT NULL, PRIMARY KEY (send_date,slot))")
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
# Short-lived card previews are not reservations and never deduct wallet funds.
pending_previews = {}
BOT_NAMES = ['Abel','Hana','Dawit','Selam','Meron','Natnael','Liya','Bereket','Rahel','Yonatan','Eden','Sami','Tigist','Mikiyas','Meseret','Amanuel','Hirut','Fitsum','Biniam','Martha','Robel','Saron','Henok','Bethlehem','Yared']
def seed_bots(r):
  rng = random.SystemRandom()
  counts = [n for n in range(15, 21) if n != r.get('last_bot_count')]
  bot_count = rng.choice(counts)
  r['last_bot_count'] = bot_count
  # Bots are queued, not preloaded. Each gets a unique random second in the 55-second selection window.
  offsets = sorted(rng.sample(range(1, 37), bot_count))
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
    add_tx(c, uid, '🏆', f'Bingo አሸነፉ! (Card #{cno})', prize)
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
  try:
    with get_db() as c:
      row = c.execute("SELECT image_data FROM bot_settings WHERE setting_key='welcome_image'").fetchone()
    if row and row['image_data']:
      with open(path, 'wb') as f: f.write(bytes(row['image_data']))
      return path
  except Exception as e:
    print('Welcome image database read error:', type(e).__name__)
  w, h = 1280, 720
  im = Image.new('RGB', (w, h))
  px = im.load()
  for y in range(h):
    for x in range(w):
      dx=(x-w/2)/(w*.78); dy=(y-h/2)/(h*.95)
      glow=max(0,1-(dx*dx+dy*dy)**0.5)
      px[x,y]=(int(9+31*glow),int(2+5*glow),int(36+104*glow))
  d=ImageDraw.Draw(im)
  # Layered gold and violet frame
  d.rounded_rectangle((16,16,w-16,h-16),radius=74,outline=(255,184,25),width=18)
  d.rounded_rectangle((36,36,w-36,h-36),radius=60,outline=(255,222,91),width=5)
  d.rounded_rectangle((48,48,w-48,h-48),radius=52,outline=(177,54,255),width=8)
  font_path='/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf'
  def font(sz):
    try: return ImageFont.truetype(font_path,sz)
    except Exception: return ImageFont.load_default()
  # Crown
  cx=w//2
  d.polygon([(cx-145,218),(cx-111,110),(cx-49,174),(cx,62),(cx+49,174),(cx+111,110),(cx+145,218)],
            fill=(255,188,20),outline=(255,229,111),width=7)
  d.rounded_rectangle((cx-151,203,cx+151,239),radius=15,fill=(255,195,25),outline=(255,230,120),width=6)
  # Text with shadow, thick dark outline, and warm gradient fill
  def gradient_word(word, top, size, c1, c2):
    f=font(size)
    mask=Image.new('L',(w,h),0); md=ImageDraw.Draw(mask)
    box=md.textbbox((0,0),word,font=f,stroke_width=0)
    tw,th=box[2]-box[0],box[3]-box[1]
    x=(w-tw)//2-box[0]
    md.text((x,top),word,font=f,fill=255)
    shadow=Image.new('RGBA',(w,h),(0,0,0,0)); sd=ImageDraw.Draw(shadow)
    sd.text((x+7,top+13),word,font=f,fill=(0,0,0,170),stroke_width=19,stroke_fill=(0,0,0,210))
    im.paste(shadow,(0,0),shadow)
    outline=Image.new('RGBA',(w,h),(0,0,0,0)); od=ImageDraw.Draw(outline)
    od.text((x,top),word,font=f,fill=(255,255,255,0),stroke_width=18,stroke_fill=(15,0,28,255))
    im.paste(outline,(0,0),outline)
    grad=Image.new('RGB',(w,h),c1); gp=grad.load()
    for yy in range(max(0,top),min(h,top+size+40)):
      t=max(0,min(1,(yy-top)/max(1,size+20)))
      col=tuple(int(c1[i]*(1-t)+c2[i]*t) for i in range(3))
      for xx in range(w): gp[xx,yy]=col
    im.paste(grad,(0,0),mask)
    d2=ImageDraw.Draw(im)
    d2.text((x,top),word,font=f,fill=(255,255,255,0),stroke_width=5,stroke_fill=(255,225,150,190))
  gradient_word('JANO',250,166,(255,225,82),(255,155,20))
  gradient_word('BINGO',410,150,(255,87,241),(174,30,239))
  d=ImageDraw.Draw(im)
  # Bingo balls framing the wordmark
  balls=[(145,345,'7',(39,128,255)),(1135,345,'5',(239,61,88)),(200,535,'12',(35,195,112)),(1080,535,'36',(154,76,245))]
  for x,y,n,c in balls:
    d.ellipse((x-61,y-61,x+61,y+61),fill=(245,245,255),outline=(255,255,255),width=5)
    d.ellipse((x-53,y-53,x+53,y+53),fill=c)
    f=font(48); bb=d.textbbox((0,0),n,font=f)
    d.text((x-(bb[2]-bb[0])/2,y-(bb[3]-bb[1])/2-8),n,font=f,fill='white',stroke_width=1,stroke_fill=(255,255,255))
  slogan='PLAY  •  WIN  •  ENJOY'
  f=font(42); bb=d.textbbox((0,0),slogan,font=f)
  d.text(((w-(bb[2]-bb[0]))//2,615),slogan,font=f,fill=(255,214,87),stroke_width=2,stroke_fill=(35,8,35))
  im.save(path,'JPEG',quality=94,optimize=True,progressive=True)
  return path


DAILY_PROMO_SLOTS = {
  'morning': {'hour': 9, 'caption': '🌅 ጃኖ ቢንጎ! ዛሬስ ማን ያሸንፋል? 🔥\n\nአዲስ ቀን፣ አዲስ እድል! አሁኑኑ ይግቡና ይጫወቱ።'},
  'afternoon': {'hour': 13, 'caption': '🏆 እድልህን ሞክር፤ የድል ቀንህ ዛሬ ይሁን!\n\nየምትወደውን ካርድ ምረጥ፤ ጨዋታህን ጀምር! 🎯'},
  'evening': {'hour': 19, 'caption': '🌙 ጓደኞችህ እየተጫወቱ ነው፤ አንተስ?\n\nየምሽቱን ጨዋታ አትዘግይ! አሁኑኑ ጃኖ ቢንጎን ክፈት። ✨'}
}
PROMO_LOCK = threading.Lock()

def ensure_daily_promo_images():
  os.makedirs('static', exist_ok=True)
  palettes = {
    'morning': ((16, 35, 91), (111, 43, 170), (255, 190, 45), (255, 91, 130)),
    'afternoon': ((6, 69, 83), (15, 133, 133), (255, 205, 65), (255, 121, 47)),
    'evening': ((13, 8, 42), (65, 24, 115), (255, 190, 45), (215, 75, 255))
  }
  for slot, (top, bottom, gold, accent) in palettes.items():
    path = f'static/jano-bingo-{slot}.jpg'
    if os.path.exists(path):
      continue
    w, h = 720, 1280
    im = Image.new('RGB', (w, h))
    px = im.load()
    for y in range(h):
      t = y / max(1, h - 1)
      base = tuple(int(top[i] * (1-t) + bottom[i] * t) for i in range(3))
      for x in range(w):
        glow = max(0, 1 - (((x-w*.5)/(w*.8))**2 + ((y-h*.43)/(h*.8))**2)**.5)
        px[x,y] = tuple(min(255, int(base[i] + glow * (gold[i]-base[i]) * .18)) for i in range(3))
    d = ImageDraw.Draw(im)
    d.rounded_rectangle((18,18,w-18,h-18), radius=54, outline=gold, width=12)
    d.rounded_rectangle((37,37,w-37,h-37), radius=42, outline=accent, width=5)
    font_path = '/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf'
    def f(sz):
      try: return ImageFont.truetype(font_path, sz)
      except Exception: return ImageFont.load_default()
    # Decorative bingo balls, with a different composition for each posting time.
    positions = ([(115,340),(605,520),(145,820),(575,990)] if slot == 'morning'
                 else [(110,460),(610,350),(120,900),(590,800)] if slot == 'afternoon'
                 else [(115,360),(600,430),(140,920),(580,1000)])
    ballcols = [(53,135,255),(232,62,98),(36,190,125),(153,75,245)]
    for i, (x,y) in enumerate(positions):
      rad = 66 if i % 2 == 0 else 54
      d.ellipse((x-rad,y-rad,x+rad,y+rad), fill=(248,247,255), outline=gold, width=6)
      d.ellipse((x-rad+8,y-rad+8,x+rad-8,y+rad-8), fill=ballcols[i])
      num = str([7,18,42,63][i])
      bb = d.textbbox((0,0), num, font=f(42))
      d.text((x-(bb[2]-bb[0])/2,y-(bb[3]-bb[1])/2-5), num, font=f(42), fill='white')
    # Central crown and strong wordmark.
    cx = w//2
    d.polygon([(cx-105,250),(cx-80,165),(cx-32,225),(cx,125),(cx+32,225),(cx+80,165),(cx+105,250)],
              fill=gold, outline=(255,239,170))
    d.rounded_rectangle((cx-110,238,cx+110,270), radius=12, fill=gold)
    for word, y, size, color in [('JANO', 490, 105, gold), ('BINGO', 605, 100, (255,225,255))]:
      ft = f(size)
      bb = d.textbbox((0,0), word, font=ft, stroke_width=5)
      x = (w-(bb[2]-bb[0]))//2
      d.text((x+5,y+8), word, font=ft, fill=(0,0,0), stroke_width=8, stroke_fill=(0,0,0))
      d.text((x,y), word, font=ft, fill=color, stroke_width=5, stroke_fill=(38,10,54))
    slogan = {'morning':'A NEW DAY • A NEW CHANCE','afternoon':'PICK YOUR CARD • PLAY NOW','evening':'TONIGHT COULD BE YOUR NIGHT'}[slot]
    ft=f(25); bb=d.textbbox((0,0),slogan,font=ft)
    d.text(((w-(bb[2]-bb[0]))//2,760),slogan,font=ft,fill=(255,245,210),stroke_width=2,stroke_fill=(25,8,40))
    d.rounded_rectangle((115,1080,605,1170), radius=34, fill=gold, outline=(255,245,190), width=4)
    cta='PLAY Jano Bingo'
    ft=f(34); bb=d.textbbox((0,0),cta,font=ft)
    d.text(((w-(bb[2]-bb[0]))//2,1098),cta,font=ft,fill=(35,12,48))
    im.save(path,'JPEG',quality=92,optimize=True)
  return True

def daily_promo_loop():
  if not bot:
    print('Daily promo scheduler skipped: BOT_TOKEN is not configured.')
    return
  try:
    ensure_daily_promo_images()
  except Exception as e:
    print('Daily promo image generation error:', type(e).__name__, e)
  tz = ZoneInfo('Africa/Addis_Ababa')
  while True:
    try:
      now = time.time()
      local = __import__('datetime').datetime.fromtimestamp(now, tz)
      for slot, cfg in DAILY_PROMO_SLOTS.items():
        if local.hour != cfg['hour'] or local.minute != 0:
          continue
        date_key = local.strftime('%Y-%m-%d')
        with PROMO_LOCK:
          with get_db() as c:
            already = c.execute('SELECT 1 FROM daily_promo_sends WHERE send_date=? AND slot=?', (date_key, slot)).fetchone()
            uids = [] if already else [int(r[0]) for r in c.execute('SELECT uid FROM users').fetchall()]
          if already:
            continue
          path = f'static/jano-bingo-{slot}.jpg'
          if not os.path.exists(path):
            ensure_daily_promo_images()
          sent = 0
          for uid in uids:
            try:
              with open(path, 'rb') as photo:
                bot.send_photo(uid, photo, caption=cfg['caption'], reply_markup=play_kb('🎮 PLAY Jano Bingo'))
              sent += 1
            except Exception as e:
              print(f'Daily promo failed for {uid}:', type(e).__name__)
          with get_db() as c:
            c.execute('INSERT INTO daily_promo_sends (send_date,slot,sent_at) VALUES (?,?,?) ON CONFLICT (send_date,slot) DO NOTHING',
                      (date_key, slot, int(time.time())))
          print(f'Daily promo {slot}: sent to {sent}/{len(uids)} users on {date_key}.')
    except Exception as e:
      print('Daily promo scheduler error:', type(e).__name__, e)
    time.sleep(25)


def menu_kb(uid=None):
  kb = IKB()
  kb.row(IBtn('🎮 Play Jano Bingo', web_app=WebAppInfo(url=APP_URL)))
  kb.row(IBtn('💰 Deposit', callback_data='home_deposit'), IBtn('💸 Withdraw', callback_data='home_withdraw'))
  kb.row(IBtn('💳 Balance', callback_data='home_balance'), IBtn('👥 Invite Friends', callback_data='home_invite'))
  kb.row(IBtn('🎯 Game Patterns', web_app=WebAppInfo(url=APP_URL)), IBtn('📖 Instructions', callback_data='home_rules'))
  kb.row(IBtn('📝 Register', callback_data='home_register'), IBtn('🎧 Support', url=f'https://t.me/{SUPPORT.lstrip("@")}'))
  if uid and is_adm(uid):
    kb.row(IBtn('👑 Admin Panel', callback_data='home_admin'))
  return kb

def play_kb(lbl='🎲 Play Jano Bingo'):
  kb = IKB(); kb.add(IBtn(lbl, web_app=WebAppInfo(url=APP_URL))); return kb

def adm_kb():
  kb = IKB()
  kb.row(IBtn('📊 ሪፖርትና ትርፍ', callback_data='adm_stats'), IBtn('👥 ተጫዋቾች', callback_data='adm_users'))
  kb.row(IBtn('🔎 ተጫዋች መፈለጊያ', callback_data='adm_player_info'))
  kb.row(IBtn('💸 Pending Payout Requests', callback_data='adm_pending_payouts'))
  kb.row(IBtn('➕ ብር ጨምር', callback_data='adm_add'), IBtn('➖ ብር ቀንስ', callback_data='adm_sub'))
  kb.row(IBtn(f'⚙️ ዝቅተኛ ተጫዋች: {MIN_PLAYERS}', callback_data='adm_minp'), IBtn('💾 DB Backup', callback_data='adm_backup'))
  kb.row(IBtn('📢 ለሁሉም መልዕክት ላክ', callback_data='adm_bcast'))
  kb.row(IBtn('🧹 Reset Rankings', callback_data='adm_reset_rank'))
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
  try: bot.send_message(ADMIN_ID, f'{hdr}\n\n🆔 #{rid}\n👤 {u["name"]}\n📱 Player ID: {u["phone"] or "Not registered"}\n💵 {float(amt):.2f} ETB\n🏦 {md}\n📝 {det}', reply_markup=kb)
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
  req = urllib.request.Request(audio_url, headers={'User-Agent': 'Jano-Bingo/1.0'})
  with urllib.request.urlopen(req, timeout=45) as response:
    audio = io.BytesIO(response.read())
  audio.name = 'jano-bingo-amharic-male-sample.mp3'
  audio.seek(0)
  return audio, est.get('estimated_cost'), data.get('id')


if bot:

  @bot.message_handler(content_types=['photo'])
  def c_set_welcome_photo(m):
    if not is_adm(m.from_user.id):
      return
    try:
      file_info = bot.get_file(m.photo[-1].file_id)
      image_bytes = bot.download_file(file_info.file_path)
      from PIL import Image
      import io
      with Image.open(io.BytesIO(image_bytes)) as img:
        img = img.convert('RGB')
        out = io.BytesIO()
        img.save(out, format='JPEG', quality=92, optimize=True)
        data = out.getvalue()
      with get_db() as c:
        c.execute("INSERT INTO bot_settings (setting_key,image_data,updated_at) VALUES ('welcome_image',?,?) ON CONFLICT (setting_key) DO UPDATE SET image_data=EXCLUDED.image_data, updated_at=EXCLUDED.updated_at", (data, int(time.time())))
      with open('static/jano-bingo-welcome.jpg', 'wb') as f:
        f.write(data)
      bot.reply_to(m, '✅ Welcome image updated! It will now appear above the Jano Bingo menu whenever players open /start.')
    except Exception as e:
      print('Welcome image upload error:', type(e).__name__, str(e)[:250])
      bot.reply_to(m, '❌ I could not save that image. Please send it again as a photo.')

  @bot.message_handler(commands=['voicesample'])
  def c_voice_sample(m):
    if not is_adm(m.from_user.id):
      return bot.reply_to(m, '⛔ ለአድሚን ብቻ!')
    if not os.environ.get('ADDIS_API_KEY', '').strip():
      return bot.reply_to(m, '❌ ADDIS_API_KEY በ Neon test Render ላይ አልተገኘም።')
    status = bot.reply_to(m, '🎙️ የአማርኛ የወንድ ድምፅ ናሙና እየተዘጋጀ ነው...')
    try:
      audio, cost, clip_id = addis_voice_sample()
      bot.send_audio(m.chat.id, audio, caption='🎙️ Jano Bingo — Yohannes የአማርኛ ድምፅ ናሙና')
      note = '✅ ናሙናው ተልኳል። ድምፁን ያዳምጡና ይወስኑ።'
      if cost is not None: note += f'\nየተገመተ ወጪ: {cost} ETB'
      bot.send_message(m.chat.id, note)
    except Exception as e:
      print('Addis voice sample error:', type(e).__name__, str(e)[:300])
      bot.send_message(m.chat.id, '❌ የድምፅ ናሙና ማዘጋጀት አልተሳካም። Render logs ይፈትሹ።')

  @bot.message_handler(commands=['myid'])
  def c_myid(m):
    u = ensure_user(m.from_user.id, m.from_user.first_name or 'Player')
    if not u.get('phone'):
      return bot.reply_to(m, '📱 መጀመሪያ /register በመጫን ስልክ ቁጥርዎን ያስመዝግቡ።')
    bot.reply_to(m, f'🆔 የተጫዋች መለያዎ (Player ID): {u["phone"]}')

  @bot.message_handler(commands=['admin'])
  @bot.message_handler(func=lambda m: m.text == '👑 Admin Panel')
  def c_admin(m):
    if not is_adm(m.from_user.id): return bot.reply_to(m, '⛔ ለአድሚን ብቻ!')
    bot.send_message(m.chat.id, '👑 Jano Bingo — የአድሚን መቆጣጠሪያ', reply_markup=adm_kb())

  @bot.message_handler(commands=['resetplayers'])
  def c_resetplayers(m):
    if not is_adm(m.from_user.id): return bot.reply_to(m, '⛔ ለአድሚን ብቻ!')
    kb = IKB()
    kb.row(IBtn('🗑️ Confirm full player reset', callback_data='adm_reset_players_confirm'),
           IBtn('❌ Cancel', callback_data='adm_reset_players_cancel'))
    bot.send_message(m.chat.id, '⚠️ This will permanently delete every player account except the admin account, all player balances, transactions, deposit/withdraw requests, referral records, player and bot rankings, and cards in progress. Game settings and house statistics will remain. Continue?', reply_markup=kb)

  @bot.message_handler(commands=['menu'])
  def c_menu(m):
    with open(ensure_welcome_banner(), 'rb') as photo:
      bot.send_photo(m.chat.id, photo, caption=f'👋 ሰላም {m.from_user.first_name or "Player"}!\n\n🎉 Welcome to Jano Bingo!\nYour exciting bingo game starts here. Choose an option below 👇', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(commands=['start'])
  def c_start(m):
    ps = (m.text or '').split()
    ref = int(ps[1]) if len(ps) > 1 and ps[1].isdigit() and int(ps[1]) != m.from_user.id else None
    u = ensure_user(m.from_user.id, m.from_user.first_name or 'Player', ref)
    if not u['phone']:
      kb = RKB(resize_keyboard=True, one_time_keyboard=True); kb.add(KBtn('📱 ስልክ ቁጥር አጋራ', request_contact=True))
      return bot.send_message(m.chat.id, '👑 እንኳን ወደ Jano Bingo በደህና መጡ!\n\nለመመዝገብ ስልክ ቁጥርዎን ያጋሩ 👇', reply_markup=kb)
    with open(ensure_welcome_banner(), 'rb') as photo:
      bot.send_photo(m.chat.id, photo, caption=f'👋 ሰላም {m.from_user.first_name or "Player"}!\n\n🎉 Welcome to Jano Bingo!\nYour exciting bingo game starts here. Choose an option below 👇', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(content_types=['contact'])
  def c_contact(m):
    # Only accept the Telegram user's own shared contact, and award the signup
    # bonus once when their phone number is first registered.
    if not m.contact or (m.contact.user_id and int(m.contact.user_id) != int(m.from_user.id)):
      return bot.reply_to(m, '❌ እባክዎ የራስዎን ስልክ ቁጥር ብቻ ያጋሩ።')
    ensure_user(m.from_user.id, m.from_user.first_name or 'Player')
    phone = (m.contact.phone_number or '').strip()
    if not phone:
      return bot.reply_to(m, '❌ ትክክለኛ ስልክ ቁጥር አልተገኘም። እንደገና ይሞክሩ።')
    awarded = False
    with get_db() as c:
      row = c.execute('SELECT phone FROM users WHERE uid=? FOR UPDATE', (m.from_user.id,)).fetchone()
      if row and not row['phone']:
        c.execute('UPDATE users SET phone=?,play_wallet=play_wallet+10 WHERE uid=?', (phone, m.from_user.id))
        add_tx(c, m.from_user.id, '🎁', 'የአዲስ ምዝገባ ቦነስ', 10.0)
        awarded = True
    if awarded:
      bot.send_message(m.chat.id, f'✅ በተሳካ ሁኔታ ተመዝግበዋል! ({phone})\n\n🎁 የምዝገባ ቦነስ: +10 ETB\n💰 10 ብር ወደ ባላንስዎ ተጨምሯል።', reply_markup=ReplyKeyboardRemove())
    else:
      bot.send_message(m.chat.id, f'✅ አስቀድመው ተመዝግበዋል! ({phone})\n🎁 የ10 ETB የምዝገባ ቦነስ አንድ ጊዜ ብቻ ይሰጣል።', reply_markup=ReplyKeyboardRemove())
    with open(ensure_welcome_banner(), 'rb') as photo:
      bot.send_photo(m.chat.id, photo, caption='👋 Welcome to Jano Bingo! Choose an option below 👇', reply_markup=menu_kb(m.from_user.id))

  @bot.message_handler(commands=['play'])
  @bot.message_handler(func=lambda m: (m.text or '').strip().casefold() in {'🎮 play jano bingo', '🎮 play jano bingo'.casefold(), '🎮 play jano bingo'.upper().casefold(), '🎮 play jano bingo'.replace('jano','JANO').casefold()})
  def c_play(m): bot.send_message(m.chat.id, '🎮 ጨዋታውን ለመክፈት ከታች ይጫኑ፦', reply_markup=play_kb('🎮 OPEN Jano Bingo'))

  @bot.message_handler(commands=['transfer'])
  def c_transfer(m):
    u = ensure_user(m.from_user.id, m.from_user.first_name or 'Player')
    if not u.get('phone'):
      return bot.reply_to(m, '📱 ለማስተላለፍ መጀመሪያ /register በመጫን ይመዝገቡ።')
    bot.register_next_step_handler(bot.send_message(m.chat.id, '📱 ገንዘብ የሚቀበለውን ተጫዋች የተመዘገበ ስልክ ቁጥር ያስገቡ፦'), s_transfer_phone)

  def s_transfer_phone(m):
    phone = ''.join(ch for ch in (m.text or '').strip() if ch.isdigit() or ch == '+')
    if len(phone) < 9 or len(phone) > 16:
      return bot.reply_to(m, '❌ ትክክለኛ ስልክ ቁጥር ያስገቡ። እንደገና /transfer ይጻፉ።')
    digits = ''.join(ch for ch in phone if ch.isdigit())
    last9 = digits[-9:]
    variants = list({digits, last9, '0' + last9, '251' + last9})
    with get_db() as c:
      matches = c.execute("SELECT uid,name,phone FROM users WHERE phone IS NOT NULL AND regexp_replace(phone, '[^0-9]', '', 'g') = ANY(?)", (variants,)).fetchall()
    if len(matches) == 0:
      return bot.reply_to(m, '❌ ይህ ስልክ ቁጥር የተመዘገበ ተጫዋች አይደለም።')
    if len(matches) > 1:
      return bot.reply_to(m, '⚠️ ይህ ስልክ ቁጥር ከአንድ ተጫዋች ጋር ተያይዟል። እባክዎ ድጋፍን ያነጋግሩ።')
    recipient = matches[0]
    if int(recipient['uid']) == int(m.from_user.id):
      return bot.reply_to(m, '❌ ወደ ራስዎ ገንዘብ ማስተላለፍ አይችሉም።')
    bot.register_next_step_handler(bot.send_message(m.chat.id, f'👤 ተቀባይ: {recipient["name"]}\n📱 {recipient["phone"]}\n💵 ምን ያህል ETB ማስተላለፍ ይፈልጋሉ? (ክፍያ 0 ETB)'), s_transfer_amount, int(recipient['uid']), recipient['name'])

  def s_transfer_amount(m, recipient_uid, recipient_name):
    try:
      amt = float((m.text or '').strip())
      if not math.isfinite(amt) or amt <= 0 or amt > 1000000: raise ValueError()
      with get_db() as c:
        c.execute('BEGIN')
        sender = c.execute('SELECT name,phone FROM users WHERE uid=? FOR UPDATE', (m.from_user.id,)).fetchone()
        recipient = c.execute('SELECT uid FROM users WHERE uid=? FOR UPDATE', (recipient_uid,)).fetchone()
        if not sender or not sender['phone'] or not recipient:
          return bot.reply_to(m, '❌ ተጫዋቹ አልተገኘም ወይም አልተመዘገበም።')
        cur = c.execute('UPDATE users SET play_wallet=play_wallet-? WHERE uid=? AND play_wallet>=?', (amt, m.from_user.id, amt))
        if cur.rowcount != 1:
          return bot.reply_to(m, '❌ በቂ ባላንስ የለዎትም።')
        c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (amt, recipient_uid))
        add_tx(c, m.from_user.id, '↗️', f'ለ {recipient_name} የተላከ ገንዘብ', -amt)
        add_tx(c, recipient_uid, '↙️', f'ከ {sender["name"]} የተቀበሉት ገንዘብ', amt)
      bot.reply_to(m, f'✅ {amt:.2f} ETB ወደ {recipient_name} ተልኳል።\n💸 ክፍያ: 0 ETB')
      try: bot.send_message(recipient_uid, f'💰 {sender["name"]}  {amt:.2f} ETB ልከውልዎታል።')
      except Exception: pass
    except Exception:
      bot.reply_to(m, '❌ መጠኑ ትክክል አይደለም። እንደገና /transfer ይጻፉ።')

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
        try: bot.send_message(ADMIN_ID, f'🔔 አዲስ የወጪ ጥያቄ!\n\n🆔 #{rid}\n👤 {m.from_user.first_name or "Player"}\n📱 {ensure_user(m.from_user.id).get('phone') or 'Not registered'}\n💵 {amt:.2f} ETB\n🏦 {md}\n📱 {acc}', reply_markup=kb)
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
      bot.send_message(call.message.chat.id, '\n'.join(f'• {r["name"]} | 📱 {r["phone"] or "Not registered"} | Balance:{r["play_wallet"]:.1f} ETB' for r in rows) or 'ምንም ተጫዋች የለም።')
    elif d == 'adm_player_info':
      bot.register_next_step_handler(bot.send_message(call.message.chat.id, '🔎 የተጫዋቹን የተመዘገበ ስልክ ቁጥር ያስገቡ፦'), s_adm_player_info)
    elif d == 'adm_pending_payouts':
      with get_db() as c:
        payouts = c.execute("""
          SELECT r.id,r.uid,r.amount,r.method,r.details,r.created_at,u.name,u.phone
          FROM requests r LEFT JOIN users u ON u.uid=r.uid
          WHERE r.req_type='withdraw' AND r.status='pending'
          ORDER BY r.created_at ASC LIMIT 30
        """).fetchall()
      if not payouts:
        bot.send_message(call.message.chat.id, '✅ ምንም በመጠባበቅ ላይ ያለ የወጪ ክፍያ ጥያቄ የለም።', reply_markup=adm_kb())
      else:
        bot.send_message(call.message.chat.id, f'💸 <b>PENDING PAYOUT REQUESTS</b> — {len(payouts)}', parse_mode='HTML')
        for p in payouts:
          stamp = time.strftime('%Y-%m-%d %H:%M', time.localtime(p['created_at'])) if p['created_at'] else 'Unknown'
          details = (p['details'] or '').replace('<','&lt;').replace('>','&gt;').replace('&','&amp;')
          phone = p['phone'] or 'Not registered'
          name = p['name'] or 'Player'
          msg = (
            f'💸 <b>PAYOUT #{p["id"]}</b>\\n'
            f'👤 {name}\\n'
            f'📱 <code>{phone}</code>\\n'
            f'💵 <b>{float(p["amount"] or 0):.2f} ETB</b>\\n'
            f'🏦 {p["method"] or "Unknown"}\\n'
            f'📄 {details}\\n'
            f'🕒 {stamp}'
          )
          kb = IKB()
          kb.row(IBtn('✅ Mark as paid', callback_data=f'ap_wd_{p["id"]}'),
                 IBtn('❌ Reject & refund', callback_data=f'rj_wd_{p["id"]}'))
          bot.send_message(call.message.chat.id, msg, parse_mode='HTML', reply_markup=kb)
    elif d in ('adm_add', 'adm_sub'):
      act = 'add' if d == 'adm_add' else 'sub'
      bot.register_next_step_handler(bot.send_message(call.message.chat.id, '📱 የተጫዋቹን የተመዘገበ ስልክ ቁጥር እና መጠን ይላኩ (ምሳሌ፦ `0912345678 100`)', parse_mode='Markdown'), s_adm_bal, act)
    elif d == 'adm_minp':
      MIN_PLAYERS = 1 if MIN_PLAYERS >= 3 else MIN_PLAYERS + 1
      bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=adm_kb())
      bot.send_message(call.message.chat.id, f'⚙️ ዝቅተኛ ተጫዋች ወደ {MIN_PLAYERS} ተቀይሯል።')
    elif d == 'adm_backup':
      bot.send_message(call.message.chat.id, '💾 Database is hosted on Neon PostgreSQL. Use Neon backup/restore tools for database backups.')
    elif d == 'adm_reset_rank':
      kb = IKB()
      kb.row(IBtn('✅ Confirm reset', callback_data='adm_reset_rank_confirm'), IBtn('❌ Cancel', callback_data='adm_reset_rank_cancel'))
      bot.send_message(call.message.chat.id, '⚠️ Reset leaderboard totals for all real players and clear bot rankings? Wallets, deposits, withdrawals, transactions, match counts and win counts will remain unchanged.', reply_markup=kb)
    elif d == 'adm_reset_rank_cancel':
      bot.send_message(call.message.chat.id, 'Reset cancelled. No ranking data was changed.')
    elif d == 'adm_reset_players_cancel':
      bot.send_message(call.message.chat.id, 'Full player reset cancelled. No data was changed.')
    elif d == 'adm_reset_players_confirm':
      with get_db() as c:
        c.execute('BEGIN')
        c.execute('DELETE FROM requests')
        c.execute('DELETE FROM transactions')
        c.execute('DELETE FROM room_cards')
        c.execute('DELETE FROM bot_rankings')
        c.execute('DELETE FROM users WHERE uid<>?', (ADMIN_ID,))
        if ADMIN_ID:
          c.execute('UPDATE users SET play_wallet=0,win_wallet=0,matches_played=0,wins=0,total_won=0,referred_by=NULL WHERE uid=?', (ADMIN_ID,))
      with room_lock:
        for room in rooms.values():
          room.update({'phase':'WAITING','countdown':CD_SEC,'cards':{},'called':[],'deck':[],'winner':None,'win_until':0.0,'tick':time.time()})
          if room['stake'] == 10: seed_bots(room)
          else: room.update({'bot_queue':[],'bot_start_at':None,'bot_index':0})
      bot.send_message(call.message.chat.id, '✅ Full player reset completed. All player accounts and related records were deleted. The admin account, game settings, and house statistics were preserved.')
    elif d == 'adm_reset_rank_confirm':
      with get_db() as c:
        c.execute('BEGIN')
        c.execute('UPDATE users SET total_won=0')
        c.execute('DELETE FROM bot_rankings')
      bot.send_message(call.message.chat.id, '✅ Test leaderboard reset complete. Player wallets, transactions, deposits, withdrawals, match counts and win counts were preserved.')
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

  def s_adm_player_info(m):
    if not is_adm(m.from_user.id): return
    if (m.text or '').strip().lower() in ('/cancel', 'cancel', 'stop', '/admin'):
      bot.send_message(m.chat.id, '✅ የተጫዋች ፍለጋ ተዘግቷል።', reply_markup=adm_kb())
      return
    phone = ''.join(ch for ch in (m.text or '') if ch.isdigit())
    if len(phone) < 9:
      bot.send_message(m.chat.id, '❌ ትክክለኛ የስልክ ቁጥር ያስገቡ።')
      bot.send_message(m.chat.id, '📱 ሌላ ስልክ ቁጥር ይላኩ፤ ለመውጣት /cancel ይጻፉ።')
      bot.register_next_step_handler_by_chat_id(m.chat.id, s_adm_player_info)
      return
    last9 = phone[-9:]
    variants = list({phone, last9, '0' + last9, '251' + last9})
    with get_db() as c:
      rows = c.execute("SELECT * FROM users WHERE phone IS NOT NULL AND regexp_replace(phone, '[^0-9]', '', 'g') = ANY(?)", (variants,)).fetchall()
      if len(rows) != 1:
        error = '❌ ተጫዋቹ አልተገኘም። የተመዘገበውን ስልክ ቁጥር ያረጋግጡ።' if not rows else '⚠️ ከአንድ በላይ ተጫዋች ተገኝቷል። ሙሉ ስልክ ቁጥሩን ያስገቡ።'
        bot.send_message(m.chat.id, error)
        bot.send_message(m.chat.id, '📱 ሌላ ስልክ ቁጥር ይላኩ፤ ለመውጣት /cancel ይጻፉ።')
        bot.register_next_step_handler_by_chat_id(m.chat.id, s_adm_player_info)
        return
      u = rows[0]
      losses = max(0, int(u['matches_played'] or 0) - int(u['wins'] or 0))
      tx = c.execute('SELECT icon,title,amount,created_at FROM transactions WHERE uid=? ORDER BY created_at DESC LIMIT 10', (u['uid'],)).fetchall()
      req = c.execute("SELECT req_type,COALESCE(SUM(amount),0) AS total FROM requests WHERE uid=? AND status IN ('approved','paid') GROUP BY req_type", (u['uid'],)).fetchall()
    req_totals = {r['req_type']: float(r['total'] or 0) for r in req}
    joined = time.strftime('%Y-%m-%d', time.localtime(u['created_at'])) if u['created_at'] else 'Unknown'
    msg = (
      "👤 <b>PLAYER PROFILE</b>\n"
      "━━━━━━━━━━━━━━━━━━\n"
      f"👤 Name       : <b>{u['name']}</b>\n"
      f"📱 Phone      : <code>{u['phone']}</code>\n"
      f"🆔 Player ID  : <code>{u['phone']}</code>\n"
      f"📅 Joined     : {joined}\n"
      "━━━━━━━━━━━━━━━━━━\n"
      f"💰 Balance    : <b>{float(u['play_wallet'] or 0):.2f} ETB</b>\n"
      f"🏆 Wins       : {int(u['wins'] or 0)}\n"
      f"❌ Losses     : {losses}\n"
      f"🎮 Matches    : {int(u['matches_played'] or 0)}\n"
      f"💵 Total won  : {float(u['total_won'] or 0):.2f} ETB\n"
      f"📥 Deposits   : {req_totals.get('deposit',0):.2f} ETB\n"
      f"📤 Withdrawals: {req_totals.get('withdraw',0):.2f} ETB\n"
      "━━━━━━━━━━━━━━━━━━"
    )
    if tx:
      msg += "\n🧾 <b>RECENT TRANSACTIONS</b>\n"
      for t in tx:
        stamp = time.strftime('%m-%d %H:%M', time.localtime(t['created_at'])) if t['created_at'] else ''
        msg += f"\n{stamp}  {t['icon'] or ''} {t['title']}  |  {float(t['amount'] or 0):+.2f} ETB"
    bot.send_message(m.chat.id, msg, parse_mode='HTML')
    bot.send_message(m.chat.id, '📱 ሌላ ስልክ ቁጥር ይላኩ፤ ለመውጣት /cancel ይጻፉ።')
    bot.register_next_step_handler_by_chat_id(m.chat.id, s_adm_player_info)

  def s_adm_bal(m, act):
    if not is_adm(m.from_user.id): return
    try:
      phone_s, a_s = (m.text or '').strip().rsplit(None, 1)
      phone = ''.join(ch for ch in phone_s if ch.isdigit())
      amt = float(a_s)
      if len(phone) < 9 or not math.isfinite(amt) or amt <= 0 or amt > 1000000: raise ValueError()
      last9 = phone[-9:]
      variants = list({phone, last9, '0' + last9, '251' + last9})
      with get_db() as c:
        matches = c.execute("SELECT uid,name,phone FROM users WHERE phone IS NOT NULL AND regexp_replace(phone, '[^0-9]', '', 'g') = ANY(?)", (variants,)).fetchall()
        if len(matches) != 1:
          return bot.reply_to(m, '❌ ይህ ስልክ ቁጥር የተመዘገበ አንድ ተጫዋች ብቻ መሆን አለበት።')
        target = matches[0]
        uid = target['uid']
        if act == 'add': c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (amt, uid)); add_tx(c, uid, '🎁', 'አድሚን ጨምሯል', amt)
        else: c.execute('UPDATE users SET play_wallet=GREATEST(0,play_wallet-?) WHERE uid=?', (amt, uid)); add_tx(c, uid, '➖', 'አድሚን ቀንሷል', -amt)
        pw = c.execute('SELECT play_wallet FROM users WHERE uid=?', (uid,)).fetchone()[0]
      bot.reply_to(m, f'✅ {target["name"]} ({target["phone"]}) ተስተካክሏል። Play: {pw:.2f} ETB')
    except Exception: bot.reply_to(m, '❌ ምሳሌ፦ `0912345678 100`', parse_mode='Markdown')

  def s_bcast(m):
    if not is_adm(m.from_user.id): return
    if m.content_type == 'text' and not (m.text or '').strip():
      return bot.reply_to(m, '❌ ባዶ መልዕክት መላክ አይቻልም።')
    if m.content_type != 'text' and m.content_type not in ('photo', 'video', 'document', 'animation', 'audio', 'voice', 'video_note', 'sticker'):
      return bot.reply_to(m, '❌ ይህ የመልዕክት አይነት ገና አይደገፍም።')
    with get_db() as c: uids = [r[0] for r in c.execute('SELECT uid FROM users').fetchall()]
    s = 0
    for u in uids:
      try:
        if m.content_type == 'text':
          bot.send_message(u, f'📢 ማስታወቂያ\\n\\n{m.text}', reply_markup=play_kb('🎮 PLAY Jano Bingo'))
        else:
          bot.copy_message(u, m.chat.id, m.message_id, reply_markup=play_kb('🎮 PLAY Jano Bingo'))
        s += 1
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
    u = ensure_user(m.from_user.id, m.from_user.first_name or 'Player')
    if u.get('phone'):
      return bot.send_message(m.chat.id, f'✅ አስቀድመው ተመዝግበዋል! (Already registered)\n📱 {u["phone"]}')
    kb = RKB(resize_keyboard=True, one_time_keyboard=True); kb.add(KBtn('📱 ስልክ ቁጥር አጋራ', request_contact=True))
    bot.send_message(m.chat.id, '📱 ለመመዝገብ ስልክ ቁጥርዎን ያጋሩ 👇', reply_markup=kb)

  @bot.message_handler(commands=['support'])
  @bot.message_handler(func=lambda m: m.text == '🎧 ድጋፍ (Support)')
  def c_sup(m):
    support_url = f"https://t.me/{SUPPORT.lstrip('@')}"
    kb = IKB(); kb.add(IBtn('💬 የድጋፍ ቡድንን ያነጋግሩ / Contact Support', url=support_url))
    bot.send_message(m.chat.id, f'🎧 የJano Bingo ድጋፍ\n\nለእርዳታ ከዚህ ይጻፉ፦ {SUPPORT}\n\nContact our support account:', reply_markup=kb, disable_web_page_preview=True)

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
      u = ensure_user(uid, call.from_user.first_name or 'Player')
      if u.get('phone'):
        bot.send_message(call.message.chat.id, f'✅ አስቀድመው ተመዝግበዋል! (Already registered)\n📱 {u["phone"]}')
      else:
        kb = RKB(resize_keyboard=True, one_time_keyboard=True)
        kb.add(KBtn('📱 ስልክ ቁጥር አጋራ', request_contact=True))
        bot.send_message(call.message.chat.id, '📱 ለመመዝገብ ስልክ ቁጥርዎን ያጋሩ 👇', reply_markup=kb)
    elif call.data == 'home_rules':
      c_rules(call.message)
    elif call.data == 'home_admin':
      if is_adm(uid): bot.send_message(call.message.chat.id, '👑 Jano Bingo — የአድሚን መቆጣጠሪያ', reply_markup=adm_kb())

  @bot.message_handler(commands=['rules'])
  @bot.message_handler(func=lambda m: m.text == '📜 ህግና መመሪያ')
  def c_rules(m): bot.send_message(m.chat.id, '📜 ህግና መመሪያ\n• ቢያንስ 2 ተጫዋቾች ካርድ ሲገዙ ይጀምራል።\n• ካርድ: 10/20/50 ብር (እስከ 4)።\n• ደራሽ: 80% ለአሸናፊው።\n• ዝቅተኛ ወጪ: 100 ETB።')

def run_bot():
  if not bot: return print('WARNING: BOT_TOKEN not set; bot polling skipped.')
  try:
    # Telegram's native Menu button will show these slash commands.
    public_commands = [
      BotCommand('start', 'Start Jano Bingo'),
      BotCommand('menu', 'Open the main menu'),
      BotCommand('play', 'Play Jano Bingo'),
      BotCommand('balance', 'Check your balance'),
      BotCommand('deposit', 'Deposit funds'),
      BotCommand('withdraw', 'Withdraw funds'),
      BotCommand('invite', 'Invite friends'),
      BotCommand('register', 'Register your phone number'),
      BotCommand('transfer', 'Transfer ETB to a registered player'),
      BotCommand('support', 'Contact support'),
      BotCommand('rules', 'Game rules')
    ]
    bot.set_my_commands(public_commands)
    if ADMIN_ID:
      bot.set_my_commands(public_commands + [BotCommand('admin', 'Open admin panel'), BotCommand('myid', 'Show your Player ID (phone number)'), BotCommand('voicesample', 'Generate Amharic voice sample')], scope=BotCommandScopeChat(ADMIN_ID))
    print('Telegram command menu configured.')
  except Exception as e:
    print('Telegram command menu setup error:', e)
  while True:
    try: bot.infinity_polling(timeout=20, long_polling_timeout=15)
    except Exception as e: print('Bot error:', e); time.sleep(5)

app = FastAPI(title='Jano Bingo Live')
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
  # Daily promotional broadcasts are disabled; do not start daily_promo_loop().

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
  return {'user': {'phone': u.get('phone') or 'Not registered', 'name': u['name'], 'play_wallet': round(u['play_wallet'],2), 'matches_played': u['matches_played'], 'wins': u['wins']},
          'config': {'telebirr_name': TB_NAME, 'telebirr_phone': TB_PHONE, 'support': SUPPORT}, 'room': snap, 'history': txs, 'rank': top}

@app.post('/api/preview_card')
async def api_preview_card(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  try: st, cno = int(b.get('stake', 10)), int(b.get('card_no', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'ልክ ያልሆነ ካርድ!')
  if st not in rooms or not (1 <= cno <= 400): raise HTTPException(400, 'ልክ ያልሆነ ካርድ!')
  with room_lock:
    r = rooms[st]
    if r['phase'] not in ('WAITING', 'COUNTDOWN'): raise HTTPException(400, 'ጨዋታው ተጀምሯል!')
    if cno in r['cards']: raise HTTPException(400, f'ካርድ #{cno} ተይዟል!')
    if sum(1 for v in r['cards'].values() if v['uid'] == u['uid']) >= 4: raise HTTPException(400, 'እስከ 4 ካርድ ብቻ!')
    with get_db() as c:
      wallet = c.execute('SELECT play_wallet FROM users WHERE uid=?', (u['uid'],)).fetchone()
    if not wallet or wallet['play_wallet'] < st: raise HTTPException(400, 'በቂ ባላንስ የለዎትም! ገቢ ያድርጉ።')
    now = time.time()
    for token in [k for k,v in pending_previews.items() if v['expires'] < now]:
      pending_previews.pop(token, None)
    token = secrets.token_urlsafe(24)
    grid = gen_card(cno)
    pending_previews[token] = {'uid':u['uid'],'stake':st,'card_no':cno,'grid':grid,'expires':now+180}
    return {'ok':True,'preview_token':token,'grid':grid,'stake':st,'card_no':cno}

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
    token = str(b.get('preview_token') or '')
    preview = pending_previews.get(token)
    if not preview or preview['expires'] < time.time() or preview['uid'] != u['uid'] or preview['stake'] != st or preview['card_no'] != cno:
      raise HTTPException(400, 'እባክዎ ካርዱን እንደገና ይምረጡና ያረጋግጡ።')
    grid = preview['grid']
    with get_db() as c:
      c.execute('BEGIN IMMEDIATE')
      wallet = c.execute('SELECT play_wallet FROM users WHERE uid=?', (u['uid'],)).fetchone()
      if not wallet or wallet['play_wallet'] < st: raise HTTPException(400, 'በቂ ባላንስ የለዎትም! ገቢ ያድርጉ።')
      c.execute('UPDATE users SET play_wallet=play_wallet-? WHERE uid=?', (st, u['uid']))
      add_tx(c, u['uid'], '🎴', f'ካርድ #{cno} ({st} ብር)', -st)
      c.execute('INSERT INTO room_cards (stake,card_no,uid,name,grid) VALUES (?,?,?,?,?)',
                (st, cno, u['uid'], u['name'], json.dumps(grid)))
    r['cards'][cno] = {'uid': u['uid'], 'name': u['name'], 'grid': grid}
    pending_previews.pop(token, None)
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
    if not wl: raise HTTPException(400, 'ገና Bingo አልተሟላም!')
    finish_round(r, u['uid'], u['name'], cno, wl)
    return {'ok': True, 'prize': r['winner']['prize']}

@app.post('/api/deposit')
async def api_dep(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  try: amt = float(b.get('amount', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'የገንዘብ መጠኑ ትክክል አይደለም!')
  tx = str(b.get('tx_id', '')).strip()
  method = str(b.get('method', '')).strip()
  if method not in ('TeleBirr', 'CBE Birr'):
    raise HTTPException(400, 'የክፍያ ዘዴ ይምረጡ!')
  if not math.isfinite(amt) or amt < 20 or amt > 1000000 or len(tx) < 4 or len(tx) > 120:
    raise HTTPException(400, 'ዝቅተኛ 20 ETB፣ ትክክለኛ Transaction ID እና ተገቢ መጠን ያስገቡ!')
  try: notify_req('deposit', u['uid'], amt, method, f'App TX: {tx}', reference=tx)
  except psycopg.IntegrityError: raise HTTPException(409, 'ይህ Transaction ID ቀድሞ ተጠቅሟል!')
  return {'ok': True}

@app.post('/api/transfer')
async def api_transfer(req: Request, x_tg_init_data: str = Header(default='')):
  u, b = auth_user(x_tg_init_data), await req.json()
  phone = ''.join(ch for ch in str(b.get('phone', '')).strip() if ch.isdigit() or ch == '+')
  try: amt = float(b.get('amount', 0))
  except (TypeError, ValueError): raise HTTPException(400, 'የገንዘብ መጠኑ ትክክል አይደለም!')
  if not math.isfinite(amt) or amt <= 0 or amt > 1000000:
    raise HTTPException(400, 'ትክክለኛ የማስተላለፊያ መጠን ያስገቡ!')
  if len(phone) < 9 or len(phone) > 16: raise HTTPException(400, 'ትክክለኛ የተመዘገበ ስልክ ቁጥር ያስገቡ!')
  digits = phone.lstrip('+')
  variants = {phone, digits, '0' + digits[-9:] if len(digits) >= 9 else digits, '+251' + digits[-9:] if len(digits) >= 9 else digits}
  with get_db() as c:
    c.execute('BEGIN IMMEDIATE')
    recipient = c.execute('SELECT uid,name,phone FROM users WHERE phone IS NOT NULL AND regexp_replace(phone, \'[^0-9]\', \'\', \'g\') = ANY(?)', (list({''.join(ch for ch in v if ch.isdigit()) for v in variants}),)).fetchone()
    if not recipient: raise HTTPException(404, 'ይህ ስልክ ቁጥር የተመዘገበ ተጫዋች አይደለም!')
    if int(recipient['uid']) == int(u['uid']): raise HTTPException(400, 'ወደ ራስዎ ገንዘብ ማስተላለፍ አይችሉም!')
    sender = c.execute('SELECT play_wallet,phone FROM users WHERE uid=?', (u['uid'],)).fetchone()
    if not sender or not sender['phone']: raise HTTPException(403, 'ለማስተላለፍ መጀመሪያ ይመዝገቡ!')
    cur = c.execute('UPDATE users SET play_wallet=play_wallet-? WHERE uid=? AND play_wallet>=?', (amt, u['uid'], amt))
    if cur.rowcount != 1: raise HTTPException(400, 'በቂ ባላንስ የለዎትም!')
    c.execute('UPDATE users SET play_wallet=play_wallet+? WHERE uid=?', (amt, recipient['uid']))
    add_tx(c, u['uid'], '↗️', f'ለ {recipient["name"]} የተላከ ገንዘብ', -amt)
    add_tx(c, recipient['uid'], '↙️', f'ከ {u["name"]} የተቀበሉት ገንዘብ', amt)
  return {'ok': True, 'recipient': recipient['name'], 'amount': round(amt, 2), 'fee': 0}

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
      bot.send_message(ADMIN_ID, f'🔔 አዲስ የወጪ ጥያቄ!\n\n🆔 #{rid}\n👤 {u["name"]}\n📱 {u["phone"] or 'Not registered'}\n💵 {amt:.2f} ETB\n🏦 {method}\n📱 {ph}', reply_markup=kb)
  except Exception:
    pass
  return {'ok': True}
