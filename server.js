'use strict';
// Белка онлайн: сервер без внешних зависимостей (Node.js 18+).
// HTTP API + Server-Sent Events. Все правила, карты и таймеры — на сервере.

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const E = require('./engine');
const { S_ } = E;

const PORT = +process.env.PORT || 3000;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const PUBLIC = path.join(__dirname, 'public');
const ADMIN_LOGIN = (process.env.ADMIN_LOGIN || 'belka').trim();
const ADMIN_PASSWORD = process.env.ADMIN_PASSWORD || '';

const TURN_MS = +process.env.TURN_MS || 20000, TRICK_MS = +process.env.TRICK_MS || 1200, BOT_MS = +process.env.BOT_MS || 800, DEAL_PAUSE = +process.env.DEAL_PAUSE || 6000, MAX_MISSES = 3;
const PTS_WIN = 10, PTS_EGGS = 15, PTS_GOLAYA = 25, PTS_LEAVE = -5, LEVEL_PTS = 100;
const WAIT_GRACE_MS = 60000;
const CLOSE_AFTER_MS = +process.env.CLOSE_AFTER_MS || 15000; // приватный стол закрывается после партии // сколько ждём отключившегося игрока до начала партии
const BOT_NAMES = ['Бот Ёж', 'Бот Лиса', 'Бот Сова', 'Бот Барсук'];
// Во время игры — только эти эмодзи; до начала — обычный чат.
const EMOJI = ['👌', '🤣', '🤦‍♀️', '🤦‍♂️', '😎', '😢', '😍', '🤔', '😑', '😴', '🤬', '💩', '💪', '🤜'];
const BUBBLE_MS = 3500, CHAT_MAX = 60, CHAT_LEN = 200;

// Сервер не должен падать из-за одной ошибки: пишем её в журнал и работаем дальше.
process.on('uncaughtException', e => console.error('Необработанная ошибка:', e));
process.on('unhandledRejection', e => console.error('Необработанный промис:', e));

/* ================= хранилище ================= */
fs.mkdirSync(DATA_DIR, { recursive: true });
const DB_FILE = path.join(DATA_DIR, 'db.json');
let db = { users: {}, sessions: {} };
try { db = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch (e) { /* первый запуск */ }
db.users = db.users || {}; db.sessions = db.sessions || {}; db.dms = db.dms || {};
let saveT = null;
function saveNow() { try { const tmp = DB_FILE + '.tmp'; fs.writeFileSync(tmp, JSON.stringify(db)); fs.renameSync(tmp, DB_FILE); } catch (e) { console.error('Не удалось сохранить базу:', e.message); } }
for (const sig of ['SIGTERM', 'SIGINT']) process.on(sig, () => { clearTimeout(saveT); saveNow(); try { saveRoomsNow(); } catch (e) {} process.exit(0); });
function save() {
  clearTimeout(saveT);
  saveT = setTimeout(saveNow, 300);
}

/* ================= пароли и сессии ================= */
function hashPw(pw, salt) { return crypto.scryptSync(pw, salt, 64).toString('hex'); }
function checkPw(pw, u) {
  const a = Buffer.from(hashPw(pw, u.salt), 'hex'), b = Buffer.from(u.hash, 'hex');
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
function setPw(u, pw) { u.salt = crypto.randomBytes(16).toString('hex'); u.hash = hashPw(pw, u.salt); }
const validLogin = l => /^[\p{L}\p{N}_\-.]{3,16}$/u.test(l);
const userByLogin = l => Object.values(db.users).find(u => u.loginLower === l.trim().toLowerCase());
function newSession(uid) { const t = crypto.randomBytes(24).toString('hex'); db.sessions[t] = { uid, at: Date.now() }; save(); return t; }
function newUser(login, pw, extra) {
  const id = 'u' + crypto.randomBytes(6).toString('hex');
  const u = Object.assign({ id, login, loginLower: login.toLowerCase(), avatar: '', points: 0, games: 0, wins: 0, left: 0, createdAt: Date.now() }, extra || {});
  setPw(u, pw); db.users[id] = u; save(); return u;
}
if (ADMIN_PASSWORD) {
  let a = userByLogin(ADMIN_LOGIN);
  if (!a) a = newUser(ADMIN_LOGIN, ADMIN_PASSWORD, { admin: true });
  else { a.admin = true; setPw(a, ADMIN_PASSWORD); }
  save();
}
const levelOf = p => Math.floor(Math.max(0, p || 0) / LEVEL_PTS) + 1;
function publicUser(u) {
  if (!u) return null;
  return { id: u.id, login: u.login, avatar: u.avatar ? '/avatar/' + u.id + '?v=' + (u.avatarV || 0) : '', points: u.points, level: levelOf(u.points), games: u.games, wins: u.wins, left: u.left, admin: !!u.admin };
}
/* ---- жалобы ----
   Каждый игрок может пожаловаться на другого один раз. 10 жалоб — бан на час:
   нельзя садиться за столы. После часа бан снимается, жалобы обнуляются. */
const COMPLAINTS_LIMIT = +process.env.COMPLAINTS_LIMIT || 10, BAN_MS = +process.env.BAN_MS || 60 * 60 * 1000;
function banLeft(u) {
  if (!u || !u.banUntil) return 0;
  if (u.banUntil <= Date.now()) { u.banUntil = 0; u.complaints = []; save(); return 0; }
  return u.banUntil - Date.now();
}
function meView(u) { const p = publicUser(u); if (p) p.banUntil = banLeft(u) ? u.banUntil : 0; return p; }
function needNotBanned(uid) {
  const u = db.users[uid], left = banLeft(u);
  if (left) throw new Err(`Вы получили ${COMPLAINTS_LIMIT} жалоб и не можете играть ещё ${Math.ceil(left / 60000)} мин.`);
}
setInterval(() => { for (const u of Object.values(db.users)) if (u.banUntil && u.banUntil <= Date.now()) { banLeft(u); pushMe(u.id); } }, 30000);
function addPoints(uid, delta, opts) {
  const u = db.users[uid]; if (!u) return;
  u.points = Math.max(0, (u.points || 0) + delta);
  if (opts && opts.game) { u.games = (u.games || 0) + 1; if (opts.win) u.wins = (u.wins || 0) + 1; }
  if (opts && opts.left) u.left = (u.left || 0) + 1;
  save(); pushMe(uid); scheduleLobby();
}

/* ================= защита от перебора ================= */
const attempts = new Map();
setInterval(() => { const now = Date.now(); for (const [k, v] of attempts) if (!v.some(t => now - t < 60000)) attempts.delete(k); }, 60000);
function limited(ip) {
  const now = Date.now(), a = (attempts.get(ip) || []).filter(t => now - t < 60000);
  a.push(now); attempts.set(ip, a);
  return a.length > 30;
}

/* ================= подключения (SSE) ================= */
const conns = new Map(); // cid -> {res, uid, view}
function send(res, ev, data) { try { res.write(`event: ${ev}\ndata: ${JSON.stringify(data)}\n\n`); } catch (e) { /* закрыто */ } }
/* ---- одна Wi-Fi сеть за столом ----
   Значок «IP» показываем, только если игроки за одним столом выходят в интернет
   с одного адреса И это не мобильный интернет (там операторы часто сажают
   тысячи незнакомых людей на один общий адрес).
   Мобильный интернет узнаём двумя способами:
   1) браузер сам сообщает тип сети (navigator.connection.type: wifi / cellular) — Chrome на Android;
   2) по IP-адресу спрашиваем справочник, мобильный ли это оператор (поле mobile у ip-api.com).
   Сам адрес никому не показываем. */
const IP_LOOKUP = (process.env.IP_LOOKUP || 'on') !== 'off';
const lastIp = new Map();   // uid -> адрес (как пришёл)
const netType = new Map();  // uid -> 'wifi' | 'cellular' | 'ethernet' | ''
const ipInfo = new Map();   // адрес -> { mobile: bool } | 'pending'
function normIp(ip) {
  ip = String(ip || '').replace(/^::ffff:/, '');
  if (ip.includes(':')) return ip.split(':').slice(0, 4).join(':'); // IPv6: сеть /64 — один роутер
  return ip;
}
const isPrivateIp = ip => /^(127\.|10\.|192\.168\.|172\.(1[6-9]|2\d|3[01])\.|::1$|f[cd]|fe80)/i.test(ip);
function lookupIp(ip) {
  if (!IP_LOOKUP || !ip || isPrivateIp(ip) || ipInfo.has(ip) || typeof fetch !== 'function') return;
  ipInfo.set(ip, 'pending');
  fetch(`http://ip-api.com/json/${encodeURIComponent(ip)}?fields=status,mobile`, { signal: AbortSignal.timeout(4000) })
    .then(r => r.json())
    .then(j => { ipInfo.set(ip, { mobile: j.status === 'success' && !!j.mobile, at: Date.now() }); for (const r of rooms.values()) broadcast(r); scheduleLobby(); })
    .catch(() => ipInfo.delete(ip));
}
function noteIp(uid, ip, net) {
  if (!uid) return;
  if (ip) { ip = String(ip).replace(/^::ffff:/, ''); lastIp.set(uid, ip); lookupIp(ip); }
  if (net !== undefined) netType.set(uid, ['wifi', 'cellular', 'ethernet'].includes(net) ? net : '');
}
function onMobileNet(uid) {
  if (netType.get(uid) === 'cellular') return true;
  const info = ipInfo.get(lastIp.get(uid));
  return !!(info && info !== 'pending' && info.mobile);
}
// Возвращает массив из 4 чисел: 0 — нет совпадений, 1, 2… — номер группы с одной Wi-Fi сетью.
function ipGroups(seats) {
  const by = new Map();
  seats.forEach((v, i) => {
    if (!isHuman(v) || !lastIp.has(v) || onMobileNet(v)) return;
    const k = normIp(lastIp.get(v));
    (by.get(k) || by.set(k, []).get(k)).push(i);
  });
  const out = [0, 0, 0, 0]; let n = 0;
  for (const idx of by.values()) if (new Set(idx.map(i => seats[i])).size > 1) { n++; idx.forEach(i => { out[i] = n; }); }
  return out;
}
function ipGroupsKey(uid) { return (lastIp.get(uid) || '') + '|' + (netType.get(uid) || ''); }
function connsOf(uid) { return [...conns.values()].filter(c => c.uid === uid); }
function isOnline(uid) { return connsOf(uid).length > 0; }
function pushMe(uid) { const u = db.users[uid]; connsOf(uid).forEach(c => send(c.res, 'me', meView(u))); }
function toastTo(uid, text) { connsOf(uid).forEach(c => send(c.res, 'toast', text)); }
// «пульс» каждые 15 с: браузер понимает, что живая связь есть (на некоторых хостингах поток режется — тогда браузер переходит на опрос)
setInterval(() => conns.forEach(c => send(c.res, 'ping', Date.now())), 15000);

/* ================= столы ================= */
const rooms = new Map();
// Номер стола — наименьший свободный среди открытых столов: Стол №1, Стол №2…
function nextTableNo() { const used = new Set([...rooms.values()].map(r => r.no)); let n = 1; while (used.has(n)) n++; return n; }
function makeCode() { let c; do { c = String(crypto.randomInt(1000, 10000)); } while ([...rooms.values()].some(r => r.code === c)); return c; }

function createRoom(uid, opts) {
  leaveWaitingSeats(uid);
  const id = 'r' + crypto.randomBytes(5).toString('hex');
  const r = {
    id, no: 0, name: '',
    private: !!opts.private || !!opts.training, training: !!opts.training, code: '', host: uid, createdAt: Date.now(),
    seats: [uid, null, null, null], ready: {}, misses: [0, 0, 0, 0], g: E.freshGame(), timer: null, deadline: 0, rev: 0,
    offlineSince: {}, chat: [], bubbles: [null, null, null, null], lastMsg: {},
  };
  r.no = opts.training ? 0 : nextTableNo();
  r.name = opts.training ? 'Тренировка' : 'Стол №' + r.no;
  if (r.private) r.code = makeCode();
  if (r.training) { r.seats = [uid, 'bot', 'bot', 'bot']; r.ready[uid] = true; }
  rooms.set(id, r);
  setView(uid, id);
  if (r.training) E.newDeal(r.g);
  advance(r);
  return r;
}
const isBot = v => v === 'bot';
const isHuman = v => !!v && v !== 'bot';
const humans = r => r.seats.filter(isHuman);
const seatOf = (r, uid) => r.seats.indexOf(uid);
function roomOfPlayer(uid) {
  for (const r of rooms.values()) if (r.seats.includes(uid)) return r;
  return null;
}
function deleteRoom(r, reason) {
  clearTimeout(r.timer);
  rooms.delete(r.id);
  conns.forEach(c => { if (c.view === r.id) { c.view = null; send(c.res, 'room', null); if (reason) send(c.res, 'toast', reason); } });
  scheduleLobby();
}
// Стол удаляется, если за ним не осталось живых игроков.
function checkEmpty(r) {
  if (!rooms.has(r.id)) return true;
  if (humans(r).length === 0) { deleteRoom(r, 'За столом не осталось игроков — стол закрыт.'); return true; }
  if (!humans(r).includes(r.host)) { r.host = humans(r)[0]; toastTo(r.host, 'Вы теперь создатель этого стола.'); }
  return false;
}
function leaveWaitingSeats(uid) {
  for (const r of rooms.values()) {
    const i = seatOf(r, uid);
    if (i >= 0 && (r.g.phase === 'waiting' || r.g.phase === 'over')) {
      r.seats[i] = null; delete r.ready[uid];
      if (!checkEmpty(r)) touch(r);
    }
  }
}
function setView(uid, roomId) { connsOf(uid).forEach(c => { c.view = roomId; }); }

/* ---- ход игры ---- */
function touch(r) { r.rev++; broadcast(r); scheduleLobby(); saveRooms(); }
// Столы и партии тоже сохраняются на диск: после перезапуска сервера игра продолжится.
const ROOMS_FILE = path.join(DATA_DIR, 'rooms.json');
let roomsT = null;
function roomsSnapshot() { return [...rooms.values()].map(r => { const { timer, ...rest } = r; return rest; }); }
function saveRoomsNow() {
  try { const tmp = ROOMS_FILE + '.tmp'; fs.writeFileSync(tmp, JSON.stringify(roomsSnapshot())); fs.renameSync(tmp, ROOMS_FILE); }
  catch (e) { console.error('Не удалось сохранить столы:', e.message); }
}
function saveRooms() { if (!roomsT) roomsT = setTimeout(() => { roomsT = null; saveRoomsNow(); }, 1000); }
function loadRooms() {
  let list = [];
  try { list = JSON.parse(fs.readFileSync(ROOMS_FILE, 'utf8')); } catch (e) { return; }
  for (const r of list) {
    if (!r || !r.id || !r.g) continue;
    r.timer = null; r.deadline = 0; r.offlineSince = {}; r.lastMsg = {};
    r.seats = r.seats.map(v => (isHuman(v) && !db.users[v]) ? (r.g.phase === 'waiting' ? null : 'bot') : v);
    if (!r.seats.some(isHuman)) continue;
    rooms.set(r.id, r);
  }
  for (const r of rooms.values()) { try { advance(r); } catch (e) { console.error('Стол не восстановлен', r.id, e); rooms.delete(r.id); } }
  console.log('Восстановлено столов:', rooms.size);
}
function schedule(r, ms, fn) {
  clearTimeout(r.timer); r.deadline = Date.now() + ms;
  r.timer = setTimeout(() => { r.timer = null; try { fn(); } catch (e) { console.error('Ошибка за столом', r.id, e); try { advance(r); } catch (e2) {} } }, ms);
}
function allReady(r) { return r.seats.every(Boolean) && humans(r).length > 0 && humans(r).every(u => r.ready[u]); }

function advance(r) {
  if (!rooms.has(r.id)) return;
  const g = r.g;
  clearTimeout(r.timer); r.timer = null; r.deadline = 0;
  if (g.phase === 'waiting') {
    if (allReady(r)) { E.newDeal(g); r.misses = [0, 0, 0, 0]; return advance(r); }
  } else if (g.phase === 'dealEnd') {
    schedule(r, DEAL_PAUSE, () => { E.newDeal(g); advance(r); });
  } else if (g.phase === 'over') {
    award(r);
    // После партии итог виден несколько секунд, потом стол снова собирает игроков.
    // Стол закрывается, только когда за ним не останется живых игроков.
    if (!r.training) schedule(r, CLOSE_AFTER_MS, () => { resetToWaiting(r); advance(r); });
  } else if (g.phase === 'playing') {
    if (g.trick.length === 4) schedule(r, TRICK_MS, () => { E.resolveTrick(g); advance(r); });
    else if (isBot(r.seats[g.turn])) schedule(r, BOT_MS, () => { E.playCardOn(g, g.turn, E.botCard(g, g.turn)); advance(r); });
    else if (!r.training) schedule(r, TURN_MS, () => timeout(r));
  }
  touch(r);
}
// Игрок не успел сходить за 20 секунд — за него ходит бот.
// После третьего такого хода подряд игрока сразу выводят из-за стола (−5),
// его место до конца партии занимает бот, остальные играют дальше.
function timeout(r) {
  const g = r.g, s = g.turn, uid = r.seats[s];
  if (g.phase !== 'playing' || !isHuman(uid)) return advance(r);
  r.misses[s] += 1;
  E.playCardOn(g, s, E.botCard(g, s));
  if (r.misses[s] >= MAX_MISSES) {
    r.seats[s] = 'bot'; r.misses[s] = 0; delete r.ready[uid];
    addPoints(uid, PTS_LEAVE, { left: true });
    setView(uid, null); connsOf(uid).forEach(c => send(c.res, 'room', null));
    toastTo(uid, `Бот сходил за вас ${MAX_MISSES} раза подряд — вас вывели из-за стола: ${PTS_LEAVE} очков.`);
    if (checkEmpty(r)) return;
  } else {
    toastTo(uid, `Время вышло — за вас сходил бот (${r.misses[s]} из ${MAX_MISSES}). После ${MAX_MISSES}-го раза вас выведут из-за стола.`);
  }
  advance(r);
}
function resetToWaiting(r) {
  const dealer = r.g.dealer;
  r.g = E.freshGame(); r.g.dealer = dealer; r.ready = {}; r.misses = [0, 0, 0, 0]; r.bubbles = [null, null, null, null];
}
function matchPoints(g, team) {
  if (g.winner !== team) return 0;
  if (g.result && g.result.kind === 'golaya') return PTS_GOLAYA;
  return g.hadEggs ? PTS_EGGS : PTS_WIN;
}
function award(r) {
  const g = r.g;
  if (g.awarded) return;
  g.awarded = true;
  if (r.training) return;
  r.seats.forEach((v, i) => { if (isHuman(v)) addPoints(v, matchPoints(g, i % 2), { game: true, win: g.winner === i % 2 }); });
}

/* ---- что видит конкретный игрок ---- */
function roomView(r, uid) {
  const g = r.g, me = seatOf(r, uid);
  const ipg = ipGroups(r.seats);
  const seats = r.seats.map((v, i) => {
    if (!v) return null;
    if (isBot(v)) return { bot: true, name: BOT_NAMES[i], ready: true };
    const u = publicUser(db.users[v]) || { login: 'Игрок' };
    return { id: v, name: u.login, avatar: u.avatar, level: u.level, ready: !!r.ready[v], online: isOnline(v), host: r.host === v, ipGroup: ipg[i], complained: !!(db.users[v] && (db.users[v].complaints || []).includes(uid)) };
  });
  const view = {
    id: r.id, name: r.name, private: r.private, training: r.training, code: (r.host === uid || me >= 0) ? r.code : '', host: r.host === uid,
    seats, mySeat: me, rev: r.rev,
    phase: g.phase, dealNo: g.dealNo, dealer: g.dealer, trump: g.trump, trumpTeam: g.trumpTeam, owner: g.owner, suitOwner: g.suitOwner,
    trick: g.trick, lastTrick: g.lastTrick, eyes: g.eyes, mult: g.mult, eggs: !!g.eggs, taken: g.taken, tricks: g.tricks, result: g.result,
    winner: g.winner, turn: g.turn, hadEggs: g.hadEggs, awarded: g.awarded,
    counts: [0, 1, 2, 3].map(i => g.hands[S_(i)].length),
    chat: g.phase === 'waiting' ? r.chat.slice(-40) : [],
    bubbles: r.bubbles.map(b => b && Date.now() - b.at < BUBBLE_MS ? { e: b.e, id: b.id, age: Date.now() - b.at } : null),
    left: r.deadline ? Math.max(0, r.deadline - Date.now()) : 0,
    turnMs: TURN_MS, dealPause: DEAL_PAUSE, misses: me >= 0 ? r.misses[me] : 0,
  };
  if (me >= 0) {
    view.hand = g.hands[S_(me)];
    view.legal = g.phase === 'playing' && g.turn === me && g.trick.length < 4 ? E.legalCards(view.hand, g.trick, g.trump, g.played) : [];
    if (g.phase === 'over' && !r.training) view.gain = matchPoints(g, me % 2);
  }
  return view;
}
function broadcast(r) { conns.forEach(c => { if (c.view === r.id) send(c.res, 'room', roomView(r, c.uid)); }); }

/* ---- лобби ---- */
let lobbyT = null;
function lobbyFor(uid) {
  const list = [...rooms.values()]
    // В списке только столы, которые собирают игроков. Приватные тоже видны — с замком, войти можно по коду.
    .filter(r => !r.training && r.g.phase === 'waiting')
    .sort((a, b) => b.createdAt - a.createdAt)
    .map(r => ({
      id: r.id, name: r.name, private: r.private, mine: r.host === uid, code: r.host === uid ? r.code : '',
      access: !r.private || r.seats.includes(uid) || !!(r.invited && r.invited[uid]),
      phase: r.g.phase, eyes: r.g.eyes,
      seats: (ipg => r.seats.map((v, i) => !v ? null : isBot(v) ? { bot: true, name: BOT_NAMES[i] } : (u => ({ id: v, name: u ? u.login : 'Игрок', avatar: u ? u.avatar : '', level: u ? u.level : 1, ipGroup: ipg[i] }))(publicUser(db.users[v]))))(ipGroups(r.seats)),
    }));
  const playing = [...rooms.values()].filter(r => r.g.phase === 'playing' || r.g.phase === 'dealEnd').length;
  const mine = roomOfPlayer(uid);
  const online = new Set([...conns.values()].map(c => c.uid)).size;
  return { rooms: list, playing, online, myRoom: mine && mine.g.phase !== 'over' ? mine.id : null };
}
function scheduleLobby() {
  if (lobbyT) return;
  lobbyT = setTimeout(() => { lobbyT = null; conns.forEach(c => send(c.res, 'lobby', lobbyFor(c.uid))); }, 150);
}
// Рейтинг всех игроков: очки, затем победы, затем кто раньше зарегистрировался.
function leaders() {
  return Object.values(db.users).filter(u => !u.admin)
    .sort((a, b) => (b.points || 0) - (a.points || 0) || (b.wins || 0) - (a.wins || 0) || a.createdAt - b.createdAt)
    .map(publicUser);
}

// Отключившийся игрок до начала партии освобождает место через минуту.
setInterval(() => {
  const now = Date.now();
  for (const r of [...rooms.values()]) {
    if (r.g.phase !== 'waiting' && r.g.phase !== 'over') continue;
    for (let i = 0; i < 4; i++) {
      const v = r.seats[i];
      if (!isHuman(v)) continue;
      if (isOnline(v)) { delete r.offlineSince[v]; continue; }
      r.offlineSince[v] = r.offlineSince[v] || now;
      if (now - r.offlineSince[v] > WAIT_GRACE_MS) {
        r.seats[i] = null; delete r.ready[v]; delete r.offlineSince[v];
      }
    }
    if (rooms.has(r.id) && !checkEmpty(r)) advance(r);
  }
}, 10000);

/* ================= друзья, личные сообщения, приглашения ================= */
const DM_MAX = 100, DM_LEN = 500;
function soc(u) { u.friends = u.friends || []; u.reqIn = u.reqIn || []; u.reqOut = u.reqOut || []; u.unread = u.unread || {}; return u; }
const dmKey = (a, b) => (a < b ? a + '|' + b : b + '|' + a);
const areFriends = (a, b) => !!db.users[a] && soc(db.users[a]).friends.includes(b);
function whereIs(uid) {
  if (!isOnline(uid)) return { online: false, text: 'не в сети' };
  const r = roomOfPlayer(uid);
  if (!r) return { online: true, text: 'в лобби' };
  if (r.training) return { online: true, text: 'на тренировке' };
  return { online: true, text: r.g.phase === 'waiting' ? 'собирает ' + r.name.replace('Стол', 'стол') : 'играет за ' + r.name.replace('Стол', 'столом'), room: r.private ? null : r.id };
}
function socialSummary(uid) {
  const u = soc(db.users[uid]);
  return { requests: u.reqIn.filter(id => db.users[id]).length, unread: Object.values(u.unread).reduce((a, b) => a + b, 0) };
}
function pushSocial(uid) { if (db.users[uid]) connsOf(uid).forEach(c => send(c.res, 'social', socialSummary(uid))); }
function friendsView(uid) {
  const u = soc(db.users[uid]);
  const card = id => { const p = publicUser(db.users[id]); return p && Object.assign(p, { where: whereIs(id), unread: u.unread[id] || 0 }); };
  const friends = u.friends.map(card).filter(Boolean).sort((a, b) => (b.where.online - a.where.online) || (b.unread - a.unread) || a.login.localeCompare(b.login));
  return { friends, incoming: u.reqIn.map(card).filter(Boolean), outgoing: u.reqOut.map(card).filter(Boolean), summary: socialSummary(uid) };
}
function notify(uid, n) { connsOf(uid).forEach(c => send(c.res, 'notify', n)); }
function removeFrom(arr, x) { const i = arr.indexOf(x); if (i >= 0) arr.splice(i, 1); }

function social(uid, a) {
  const me = soc(db.users[uid]);
  const t = a.type;
  const other = () => { const o = db.users[a.uid]; need(o && o.id !== uid, 'Нет такого игрока.'); return soc(o); };
  if (t === 'friends') return friendsView(uid);
  if (t === 'playerCard') {
    const o = db.users[a.uid]; need(o && !o.admin, 'Нет такого игрока.');
    const all = leaders(); const pos = all.findIndex(x => x.id === o.id);
    soc(o);
    return { player: Object.assign(publicUser(o), { rank: pos + 1, total: all.length, isMe: o.id === uid,
      friend: me.friends.includes(o.id), sent: me.reqOut.includes(o.id), got: me.reqIn.includes(o.id), where: whereIs(o.id), complained: (o.complaints || []).includes(uid) }) };
  }
  if (t === 'friendSearch') {
    const q = String(a.q || '').trim().toLowerCase();
    if (q.length < 2) return { users: [] };
    return { users: Object.values(db.users).filter(u => !u.admin && u.id !== uid && u.loginLower.includes(q)).slice(0, 20)
      .map(u => Object.assign(publicUser(u), { friend: me.friends.includes(u.id), sent: me.reqOut.includes(u.id), got: me.reqIn.includes(u.id), where: whereIs(u.id) })) };
  }
  if (t === 'friendAdd') {
    const o = other();
    need(!me.friends.includes(o.id), 'Вы уже друзья.');
    if (me.reqIn.includes(o.id)) return social(uid, { type: 'friendAccept', uid: o.id }); // встречная заявка — сразу дружба
    need(!me.reqOut.includes(o.id), 'Заявка уже отправлена.');
    need(me.reqOut.length < 200, 'Слишком много отправленных заявок.');
    me.reqOut.push(o.id); o.reqIn.push(uid); save();
    notify(o.id, { kind: 'friendReq', from: publicUser(me), text: `${me.login} хочет добавить вас в друзья` });
    pushSocial(o.id);
    return friendsView(uid);
  }
  if (t === 'friendAccept') {
    const o = other();
    need(me.reqIn.includes(o.id), 'Заявки нет.');
    removeFrom(me.reqIn, o.id); removeFrom(o.reqOut, uid);
    if (!me.friends.includes(o.id)) me.friends.push(o.id);
    if (!o.friends.includes(uid)) o.friends.push(uid);
    save(); pushSocial(uid);
    notify(o.id, { kind: 'info', from: publicUser(me), text: `${me.login} принял(а) вашу заявку в друзья` });
    return friendsView(uid);
  }
  if (t === 'friendDecline') { const o = other(); removeFrom(me.reqIn, o.id); removeFrom(o.reqOut, uid); save(); pushSocial(uid); return friendsView(uid); }
  if (t === 'friendCancel') { const o = other(); removeFrom(me.reqOut, o.id); removeFrom(o.reqIn, uid); save(); pushSocial(o.id); return friendsView(uid); }
  if (t === 'friendRemove') {
    const o = other(); removeFrom(me.friends, o.id); removeFrom(o.friends, uid);
    delete me.unread[o.id]; delete o.unread[uid]; save(); pushSocial(uid); pushSocial(o.id);
    return friendsView(uid);
  }
  if (t === 'dmHistory') {
    const o = other();
    const msgs = db.dms[dmKey(uid, o.id)] || [];
    if (me.unread[o.id]) { delete me.unread[o.id]; save(); pushSocial(uid); }
    return { with: Object.assign(publicUser(o), { where: whereIs(o.id), friend: me.friends.includes(o.id) }), messages: msgs.slice(-60) };
  }
  if (t === 'dmSend') {
    const o = other();
    need(me.friends.includes(o.id), 'Писать можно только друзьям.');
    const text = String(a.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, DM_LEN);
    need(text, 'Пустое сообщение.');
    const now = Date.now();
    need(now - (me.lastDm || 0) > 500, 'Не так быстро.');
    me.lastDm = now;
    const k = dmKey(uid, o.id), list = db.dms[k] = db.dms[k] || [];
    const m = { id: crypto.randomBytes(4).toString('hex'), from: uid, text, at: now };
    list.push(m); if (list.length > DM_MAX) list.splice(0, list.length - DM_MAX);
    o.unread[uid] = (o.unread[uid] || 0) + 1; save();
    connsOf(o.id).forEach(c => send(c.res, 'dm', { from: publicUser(me), msg: m }));
    pushSocial(o.id);
    return { msg: m };
  }
  if (t === 'invite') {
    const o = other();
    need(me.friends.includes(o.id), 'Пригласить можно только друга.');
    const r = rooms.get(a.room); need(r && !r.training, 'Стол уже закрыт.');
    need(r.seats.includes(uid), 'Сначала сядьте за стол.');
    need(r.g.phase === 'waiting', 'Приглашать можно, пока стол собирается.');
    need(r.seats.some(v => !v || isBot(v)), 'За столом нет свободных мест.');
    need(!r.seats.includes(o.id), 'Друг уже за этим столом.');
    need(isOnline(o.id), 'Друг сейчас не в сети.');
    r.invited = r.invited || {}; r.invited[o.id] = Date.now();
    notify(o.id, { kind: 'invite', from: publicUser(me), room: r.id, roomName: r.name, text: `${me.login} приглашает вас за ${r.name.replace('Стол', 'стол')}` });
    return { ok: true };
  }
  if (t === 'inviteAccept') {
    needNotBanned(uid);
    const r = rooms.get(a.room); need(r, 'Стол уже закрыт.');
    need(r.invited && r.invited[uid], 'Приглашение устарело.');
    need(r.g.phase === 'waiting', 'Игра за этим столом уже началась.');
    const other = roomOfPlayer(uid);
    need(!other || other.id === r.id || other.g.phase === 'waiting' || other.g.phase === 'over', 'Сначала доиграйте текущую партию.');
    if (!r.seats.includes(uid)) {
      let i = r.seats.findIndex(v => !v); if (i < 0) i = r.seats.findIndex(isBot);
      need(i >= 0, 'За столом уже нет свободных мест.');
      leaveWaitingSeats(uid);
      if (!rooms.has(r.id)) throw new Err('Стол уже закрыт.');
      r.seats[i] = uid; r.misses[i] = 0;
    }
    delete r.invited[uid];
    setView(uid, r.id); advance(r);
    return { room: roomView(r, uid) };
  }
  return null;
}

/* ================= действия ================= */
class Err extends Error {}
const need = (c, msg) => { if (!c) throw new Err(msg); };

function action(uid, a) {
  const u = db.users[uid];
  const t = a.type;
  if (t === 'avatar') {
    need(typeof a.data === 'string' && /^data:image\/(jpeg|png|webp);base64,/.test(a.data) && a.data.length < 200000, 'Картинка слишком большая или не того формата.');
    u.avatar = a.data; u.avatarV = (u.avatarV || 0) + 1; save(); pushMe(uid); scheduleLobby();
    const r = roomOfPlayer(uid); if (r) touch(r);
    return {};
  }
  if (t === 'leaders') return { leaders: leaders() };
  if (/^(friend|dm|invite)/.test(t) || t === 'friends' || t === 'playerCard') { const res = social(uid, a); if (res) return res; }
  if (t === 'lobby') { setView(uid, null); return { lobby: lobbyFor(uid) }; }
  // Игрок сам вернулся в лобби: пока игра не началась, он освобождает место
  // (если это создатель — стол закрывается). Идущую партию можно продолжить через «Возврат в игру».
  if (t === 'toLobby') {
    setView(uid, null);
    for (const r of [...rooms.values()]) if (r.training && r.seats.includes(uid)) deleteRoom(r);
    leaveWaitingSeats(uid);
    return { lobby: lobbyFor(uid) };
  }
  if (t === 'complain') {
    const x = db.users[a.uid]; need(x && x.id !== uid, 'Нет такого игрока.');
    need(!x.admin, 'На администратора жаловаться нельзя.');
    x.complaints = x.complaints || [];
    need(!x.complaints.includes(uid), 'Вы уже пожаловались на этого игрока.');
    x.complaints.push(uid);
    if (x.complaints.length >= COMPLAINTS_LIMIT) {
      x.banUntil = Date.now() + BAN_MS; x.complaints = [];
      for (const r of [...rooms.values()]) { const i = seatOf(r, x.id); if (i < 0) continue; r.seats[i] = (r.g.phase === 'waiting' || r.g.phase === 'over') ? null : 'bot'; delete r.ready[x.id]; if (!checkEmpty(r)) advance(r); }
      connsOf(x.id).forEach(c => { c.view = null; send(c.res, 'room', null); });
      toastTo(x.id, `На вас пожаловались ${COMPLAINTS_LIMIT} игроков. Вы не можете играть 1 час.`);
      pushMe(x.id); scheduleLobby();
    }
    save();
    for (const r of rooms.values()) if (r.seats.includes(x.id) || r.seats.includes(uid)) broadcast(r);
    return { ok: true };
  }
  if (t === 'create') { if (!a.training) needNotBanned(uid); const r = createRoom(uid, a); return { room: roomView(r, uid) }; }
  if (t === 'open') {
    const r = rooms.get(a.id); need(r, 'Стол уже закрыт.');
    need(!r.private || r.seats.includes(uid) || (r.allowed && r.allowed[uid]) || (a.code && String(a.code).trim() === r.code) || (r.invited && r.invited[uid]), a.code ? 'Неверный код стола.' : 'Это приватный стол. Нужен код.');
    if (r.private){ r.allowed = r.allowed || {}; r.allowed[uid] = true; }
    setView(uid, r.id); return { room: roomView(r, uid) };
  }
  if (t === 'findPrivate') {
    const r = [...rooms.values()].find(x => x.private && !x.training && x.code === String(a.code || '').trim());
    need(r, 'Стол с таким кодом не найден.');
    r.allowed = r.allowed || {}; r.allowed[uid] = true;
    setView(uid, r.id); return { room: roomView(r, uid), code: r.code };
  }
  if (t === 'adminUsers') { need(u.admin, 'Нет доступа.'); return { users: Object.values(db.users).map(x => Object.assign(publicUser(x), { createdAt: x.createdAt, complaints: (x.complaints || []).length, banUntil: banLeft(x) ? x.banUntil : 0 })) }; }
  if (t === 'adminResetPw') {
    need(u.admin, 'Нет доступа.'); const x = db.users[a.uid]; need(x, 'Нет такого игрока.');
    need(typeof a.password === 'string' && a.password.length >= 6, 'Новый пароль — от 6 символов.');
    setPw(x, a.password);
    for (const [k, s] of Object.entries(db.sessions)) if (s.uid === x.id) delete db.sessions[k];
    save(); return {};
  }
  if (t === 'adminSetPoints') {
    need(u.admin, 'Нет доступа.'); const x = db.users[a.uid]; need(x, 'Нет такого игрока.');
    x.points = Math.max(0, Math.floor(+a.points || 0)); save(); pushMe(x.id); scheduleLobby(); return {};
  }
  if (t === 'adminDeleteUser') {
    need(u.admin, 'Нет доступа.'); const x = db.users[a.uid]; need(x && !x.admin, 'Этого игрока удалить нельзя.');
    for (const r of [...rooms.values()]) { const i = seatOf(r, x.id); if (i >= 0) { r.seats[i] = r.g.phase === 'waiting' ? null : 'bot'; if (!checkEmpty(r)) advance(r); } }
    for (const [k, s] of Object.entries(db.sessions)) if (s.uid === x.id) delete db.sessions[k];
    connsOf(x.id).forEach(c => { send(c.res, 'logout', 'Ваш аккаунт удалён администратором.'); c.res.end(); });
    for (const o of Object.values(db.users)) { soc(o); removeFrom(o.friends, x.id); removeFrom(o.reqIn, x.id); removeFrom(o.reqOut, x.id); delete o.unread[x.id]; }
    for (const k of Object.keys(db.dms)) if (k.split('|').includes(x.id)) delete db.dms[k];
    delete db.users[x.id]; save(); return {};
  }
  if (t === 'adminRooms') {
    need(u.admin, 'Нет доступа.');
    return { rooms: [...rooms.values()].map(r => ({ id: r.id, name: r.name, private: r.private, training: r.training, code: r.code, phase: r.g.phase, eyes: r.g.eyes, dealNo: r.g.dealNo, createdAt: r.createdAt,
      seats: r.seats.map((v, i) => !v ? null : isBot(v) ? BOT_NAMES[i] : (db.users[v] ? db.users[v].login : '?')) })) };
  }
  if (t === 'adminBan') {
    need(u.admin, 'Нет доступа.'); const x = db.users[a.uid]; need(x && !x.admin, 'Нет такого игрока.');
    const min = Math.max(1, Math.min(60 * 24 * 30, Math.floor(+a.minutes || 60)));
    x.banUntil = Date.now() + min * 60000;
    for (const r of [...rooms.values()]) { const i = seatOf(r, x.id); if (i < 0) continue; r.seats[i] = (r.g.phase === 'waiting' || r.g.phase === 'over') ? null : 'bot'; delete r.ready[x.id]; if (!checkEmpty(r)) advance(r); }
    connsOf(x.id).forEach(c => { c.view = null; send(c.res, 'room', null); });
    toastTo(x.id, `Администратор ограничил вам игру на ${min} мин.`);
    save(); pushMe(x.id); scheduleLobby(); return {};
  }
  if (t === 'adminUnban') {
    need(u.admin, 'Нет доступа.'); const x = db.users[a.uid]; need(x, 'Нет такого игрока.');
    x.banUntil = 0; x.complaints = []; save(); pushMe(x.id); toastTo(x.id, 'Ограничение снято, можно играть.'); return {};
  }
  if (t === 'adminAnnounce') {
    need(u.admin, 'Нет доступа.');
    const text = String(a.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, 300); need(text, 'Пустое сообщение.');
    const ids = new Set([...conns.values()].map(c => c.uid));
    ids.forEach(id => notify(id, { kind: 'info', text: '📢 ' + text }));
    return { sent: ids.size };
  }
  if (t === 'adminCloseRoom') { need(u.admin, 'Нет доступа.'); const r = rooms.get(a.id); if (r) deleteRoom(r, 'Администратор закрыл стол.'); return {}; }
  if (t === 'deleteRoom') {
    const r = rooms.get(a.id); need(r, 'Стол уже закрыт.');
    need(r.host === uid || u.admin, 'Убрать стол может только его создатель.');
    need(r.g.phase === 'waiting' || r.g.phase === 'over' || u.admin, 'Нельзя убрать стол во время партии.');
    deleteRoom(r, 'Создатель убрал стол.'); return {};
  }

  // Дальше — действия за конкретным столом.
  const r = rooms.get(a.room); need(r, 'Стол уже закрыт.');
  const g = r.g, me = seatOf(r, uid);
  // Чат и эмодзи не трогают ход игры и таймер.
  if (t === 'chat' || t === 'emoji') {
    need(me >= 0, 'Писать могут только игроки за столом.');
    const now = Date.now();
    need(now - (r.lastMsg[uid] || 0) > 700, 'Не так быстро.');
    r.lastMsg[uid] = now;
    if (t === 'chat') {
      need(g.phase === 'waiting', 'Во время игры доступны только эмодзи.');
      const text = String(a.text || '').replace(/[\u0000-\u001f\u007f]/g, ' ').trim().slice(0, CHAT_LEN);
      need(text, 'Пустое сообщение.');
      r.chat.push({ id: crypto.randomBytes(4).toString('hex'), uid, name: db.users[uid].login, seat: me, text, at: now });
      if (r.chat.length > CHAT_MAX) r.chat.splice(0, r.chat.length - CHAT_MAX);
    } else {
      need(EMOJI.includes(a.e), 'Такого эмодзи нет.');
      need(g.phase !== 'waiting', 'До начала игры пишите в чат.');
      r.bubbles[me] = { e: a.e, at: now, id: crypto.randomBytes(3).toString('hex') };
    }
    r.rev++; broadcast(r);
    return { room: roomView(r, uid) };
  }
  switch (t) {
    case 'sit': {
      needNotBanned(uid);
      const i = +a.seat; need(i >= 0 && i < 4, 'Нет такого места.');
      need(!r.private || (r.allowed && r.allowed[uid]) || (r.invited && r.invited[uid]), 'Это приватный стол. Нужен код.');
      need(!isHuman(r.seats[i]), 'Место уже занято.');
      need(me < 0, 'Вы уже сидите за этим столом.');
      need(g.phase === 'waiting' || isBot(r.seats[i]), 'Во время партии можно сесть только вместо бота.');
      const other = roomOfPlayer(uid);
      need(!other || other.g.phase === 'waiting' || other.g.phase === 'over', 'Сначала доиграйте или выйдите из другой партии.');
      leaveWaitingSeats(uid);
      if (!rooms.has(r.id)) throw new Err('Стол уже закрыт.');
      r.seats[i] = uid; r.misses[i] = 0; setView(uid, r.id);
      break;
    }
    case 'stand': {
      need(me >= 0, 'Вы не за столом.');
      // Создатель ушёл до начала игры — стол закрывается, очки никто не теряет.
      // До начала игры и после её конца уйти можно без штрафа.
      if (g.phase === 'waiting' || g.phase === 'over') { r.seats[me] = null; delete r.ready[uid]; }
      // Игра уже идёт: за игрока доигрывает бот, −5 очков.
      else { r.seats[me] = 'bot'; delete r.ready[uid]; addPoints(uid, PTS_LEAVE, { left: true }); }
      if (checkEmpty(r)) return { closed: true };
      break;
    }
    case 'addBot': {
      const i = +a.seat; need(me >= 0 && g.phase === 'waiting', 'Добавить бота можно до начала партии.');
      need(!r.seats[i], 'Место занято.'); r.seats[i] = 'bot'; break;
    }
    case 'kick': {
      const i = +a.seat; need(r.host === uid, 'Убирать игроков может только создатель стола.');
      need(g.phase === 'waiting', 'Убирать игроков можно только до начала игры.');
      need(i !== me && r.seats[i], 'Некого убирать.');
      const v = r.seats[i]; r.seats[i] = null; delete r.ready[v];
      if (isHuman(v)) { toastTo(v, 'Создатель стола убрал вас с места.'); }
      break;
    }
    case 'ready': { need(me >= 0 && g.phase === 'waiting', 'Сейчас это не нужно.'); r.ready[uid] = !r.ready[uid]; break; }
    case 'play': {
      need(me >= 0 && g.phase === 'playing' && g.turn === me && g.trick.length < 4, 'Сейчас не ваш ход.');
      const hand = g.hands[S_(me)];
      need(hand.includes(a.card), 'У вас нет этой карты.');
      if (!E.legalCards(hand, g.trick, g.trump, g.played).includes(a.card)) {
        const noSuit = !hand.some(c => E.eff(c, g.trump) === E.eff(g.trick[0].card, g.trump));
        throw new Err(noSuit && E.isUnplayedAce(a.card, g.trump, g.played) ? 'Нельзя сбрасывать неигранного туза — в эту масть ещё не заходили.' : 'Нужно ходить в масть хода.');
      }
      r.misses[me] = 0; E.playCardOn(g, me, a.card); break;
    }
    case 'next': { need(me >= 0 && g.phase === 'dealEnd', 'Сейчас это не нужно.'); E.newDeal(g); break; }
    case 'newMatch': {
      need(me >= 0 && g.phase === 'over' && g.awarded, 'Партия ещё не закончена.');
      resetToWaiting(r);
      if (r.training) { r.ready[uid] = true; E.newDeal(r.g); }
      break;
    }
    default: throw new Err('Неизвестное действие.');
  }
  if (!checkEmpty(r)) advance(r);
  return rooms.has(r.id) ? { room: roomView(r, uid) } : { closed: true };
}

/* ================= статистика для админа ================= */
function stats() {
  const now = Date.now(), day = 24 * 3600 * 1000;
  const users = Object.values(db.users).filter(u => !u.admin);
  const onlineIds = new Set([...conns.values()].map(c => c.uid));
  const rs = [...rooms.values()].filter(r => !r.training);
  const playingRooms = rs.filter(r => r.g.phase === 'playing' || r.g.phase === 'dealEnd');
  const inGame = new Set(); playingRooms.forEach(r => r.seats.filter(isHuman).forEach(v => inGame.add(v)));
  const waiting = new Set(); rs.filter(r => r.g.phase === 'waiting').forEach(r => r.seats.filter(isHuman).forEach(v => waiting.add(v)));
  const training = [...rooms.values()].filter(r => r.training).length;
  const recent = users.slice().sort((a, b) => b.createdAt - a.createdAt).slice(0, 10).map(u => ({ login: u.login, at: u.createdAt, level: levelOf(u.points) }));
  return {
    at: now,
    registered: users.length,
    newToday: users.filter(u => now - u.createdAt < day).length,
    newWeek: users.filter(u => now - u.createdAt < 7 * day).length,
    online: onlineIds.size,
    inGame: inGame.size,
    atTables: waiting.size,
    inLobby: [...onlineIds].filter(id => !inGame.has(id) && !waiting.has(id)).length,
    tablesPlaying: playingRooms.length,
    tablesWaiting: rs.length - playingRooms.length,
    training,
    banned: users.filter(u => banLeft(u)).length,
    pro: users.filter(u => levelOf(u.points) >= 20 && levelOf(u.points) < 40).length,
    crown: users.filter(u => levelOf(u.points) >= 40).length,
    history: onlineHistory,
    recent,
  };
}
// раз в минуту запоминаем, сколько людей онлайн (последние 24 часа)
const onlineHistory = [];
setInterval(() => {
  onlineHistory.push([Date.now(), new Set([...conns.values()].map(c => c.uid)).size]);
  if (onlineHistory.length > 1440) onlineHistory.shift();
}, +process.env.STATS_EVERY || 60000);

/* ================= HTTP ================= */
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.webp': 'image/webp', '.png': 'image/png', '.svg': 'image/svg+xml', '.ico': 'image/x-icon', '.json': 'application/json' };
function json(res, code, obj) { res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(JSON.stringify(obj)); }
function body(req) {
  return new Promise((ok, fail) => {
    let size = 0; const chunks = [];
    req.on('data', c => { size += c.length; if (size > 300000) { fail(new Err('Слишком большой запрос.')); req.destroy(); } else chunks.push(c); });
    req.on('end', () => { try { ok(JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}')); } catch (e) { fail(new Err('Неверный запрос.')); } });
  });
}
function auth(req, url) {
  const h = req.headers.authorization || '';
  const t = h.startsWith('Bearer ') ? h.slice(7) : url.searchParams.get('t');
  const s = t && db.sessions[t];
  return s && db.users[s.uid] ? { token: t, uid: s.uid } : null;
}
const ipOf = req => (req.headers['x-forwarded-for'] || '').split(',')[0].trim() || req.socket.remoteAddress;

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  const p = url.pathname;
  // Программа-монитор открывается как отдельный файл, поэтому вход и статистике разрешаем чужой источник
  if (p === '/api/login' || p === '/api/stats' || p === '/api/logout') {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
    res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
    if (req.method === 'OPTIONS') { res.writeHead(204); return res.end(); }
  }
  try {
    if (p === '/api/register' && req.method === 'POST') {
      if (limited(ipOf(req))) return json(res, 429, { error: 'Слишком много попыток. Подождите минуту.' });
      const b = await body(req);
      const login = String(b.login || '').trim(), pw = String(b.password || '');
      need(validLogin(login), 'Логин: от 3 до 16 символов — буквы, цифры, точка, _ или -.');
      need(pw.length >= 6 && pw.length <= 100, 'Пароль — от 6 символов.');
      need(!userByLogin(login) && login.toLowerCase() !== ADMIN_LOGIN.toLowerCase(), 'Такой логин уже занят.');
      const u = newUser(login, pw);
      if (typeof b.avatar === 'string' && /^data:image\/(jpeg|png|webp);base64,/.test(b.avatar) && b.avatar.length < 200000) { u.avatar = b.avatar; u.avatarV = 1; save(); }
      return json(res, 200, { token: newSession(u.id), me: publicUser(u) });
    }
    if (p === '/api/login' && req.method === 'POST') {
      if (limited(ipOf(req))) return json(res, 429, { error: 'Слишком много попыток. Подождите минуту.' });
      const b = await body(req);
      const u = userByLogin(String(b.login || ''));
      need(u && checkPw(String(b.password || ''), u), 'Неверный логин или пароль.');
      return json(res, 200, { token: newSession(u.id), me: publicUser(u) });
    }
    if (p === '/api/stats') {
      const a2 = auth(req, url); if (!a2) return json(res, 401, { error: 'Войдите заново.' });
      if (!db.users[a2.uid].admin) return json(res, 403, { error: 'Только для администратора.' });
      return json(res, 200, stats());
    }
    if (p === '/api/logout' && req.method === 'POST') {
      const a = auth(req, url); if (a) { delete db.sessions[a.token]; save(); }
      return json(res, 200, {});
    }
    if (p === '/api/action' && req.method === 'POST') {
      const a = auth(req, url); if (!a) return json(res, 401, { error: 'Войдите заново.' });
      const b = await body(req);
      const before = ipGroupsKey(a.uid);
      noteIp(a.uid, ipOf(req), typeof b.net === 'string' ? b.net : undefined);
      if (b.type === 'net') { if (before !== ipGroupsKey(a.uid)) { const r = roomOfPlayer(a.uid); if (r) broadcast(r); } return json(res, 200, {}); }
      return json(res, 200, action(a.uid, b) || {});
    }
    if (p === '/events') {
      const a = auth(req, url); if (!a) return json(res, 401, { error: 'Войдите заново.' });
      res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-store', Connection: 'keep-alive', 'X-Accel-Buffering': 'no' });
      res.write('retry: 2000\n\n');
      const cid = crypto.randomBytes(6).toString('hex');
      const mine = roomOfPlayer(a.uid);
      noteIp(a.uid, ipOf(req), url.searchParams.get('net') || '');
      const c = { res, uid: a.uid, view: mine ? mine.id : null };
      conns.set(cid, c);
      scheduleLobby(); // обновить счётчик «онлайн» у всех
      send(res, 'me', meView(db.users[a.uid]));
      send(res, 'lobby', lobbyFor(a.uid));
      send(res, 'social', socialSummary(a.uid));
      if (mine) { send(res, 'room', roomView(mine, a.uid)); broadcast(mine); }
      req.on('close', () => { conns.delete(cid); scheduleLobby(); const r = roomOfPlayer(a.uid); if (r) broadcast(r); });
      return;
    }
    if (p.startsWith('/avatar/')) {
      const u = db.users[p.slice(8)];
      if (!u || !u.avatar) { res.writeHead(404); return res.end(); }
      const m = u.avatar.match(/^data:(image\/\w+);base64,(.*)$/);
      res.writeHead(200, { 'Content-Type': m[1], 'Cache-Control': 'public, max-age=31536000, immutable' });
      return res.end(Buffer.from(m[2], 'base64'));
    }
    // статика
    let f = path.normalize(path.join(PUBLIC, p === '/' ? 'index.html' : (p === '/stats' || p === '/admin') ? 'admin.html' : decodeURIComponent(p)));
    if (!f.startsWith(PUBLIC)) { res.writeHead(403); return res.end(); }
    fs.readFile(f, (err, data) => {
      if (err) { res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' }); return res.end('Не найдено'); }
      const ext = path.extname(f);
      res.writeHead(200, { 'Content-Type': MIME[ext] || 'application/octet-stream', 'Cache-Control': ext === '.html' ? 'no-cache' : 'public, max-age=86400' });
      res.end(data);
    });
  } catch (e) {
    if (e instanceof Err) return json(res, 400, { error: e.message });
    console.error(e);
    json(res, 500, { error: 'Ошибка сервера. Попробуйте ещё раз.' });
  }
});
loadRooms();
server.listen(PORT, () => console.log(`Белка работает: http://localhost:${PORT}` + (ADMIN_PASSWORD ? '' : '  (ADMIN_PASSWORD не задан — админ-панель выключена)')));
