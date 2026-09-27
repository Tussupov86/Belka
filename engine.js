'use strict';
// Правила Белки: колода 32 карты, валеты всегда козыри, счёт до 12 глаз.

const SUITS = ['C', 'S', 'H', 'D'];
const RANKS = ['7', '8', '9', 'T', 'J', 'Q', 'K', 'A'];
const PTS = { A: 11, T: 10, K: 4, Q: 3, J: 2 };
const RORD = { '7': 1, '8': 2, '9': 3, Q: 4, K: 5, T: 6, A: 7 };
const JORD = { C: 4, S: 3, H: 2, D: 1 };
const S_ = i => 's' + i;

const pts = c => PTS[c[0]] || 0;
const isTrump = (c, t) => c[0] === 'J' || c[1] === t;
const eff = (c, t) => (isTrump(c, t) ? 'T' : c[1]);
const power = (c, t) => (c[0] === 'J' ? 100 + JORD[c[1]] : (c[1] === t ? 50 : 0) + RORD[c[0]]);

function trickWinner(trick, t) {
  let best = trick[0];
  for (const p of trick.slice(1)) {
    const pe = eff(p.card, t), be = eff(best.card, t);
    if (pe === 'T' && be !== 'T') best = p;
    else if (pe === be && power(p.card, t) > power(best.card, t)) best = p;
  }
  return best.seat;
}
// Какими картами можно ходить.
// played — масти, в которые уже заходили в этой раздаче.
// Правило: нельзя сбрасывать туза масти, в которую ещё не заходили (неигранного туза),
// если есть чем ещё сходить. Заходить с такого туза можно.
const isUnplayedAce = (c, t, played) => c[0] === 'A' && !isTrump(c, t) && !(played || []).includes(c[1]);
function legalCards(hand, trick, t, played) {
  if (!trick.length) return hand.slice();
  const led = eff(trick[0].card, t);
  const f = hand.filter(c => eff(c, t) === led);
  if (f.length) return f;
  const ok = hand.filter(c => !isUnplayedAce(c, t, played));
  return ok.length ? ok : hand.slice();
}
function shuffle(a) {
  const crypto = require('crypto');
  for (let i = a.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}
function freshGame() {
  return {
    phase: 'waiting', dealNo: 0, dealer: 3, trump: 'C', trumpTeam: 0, owner: -1, suitOwner: null,
    hands: { s0: [], s1: [], s2: [], s3: [] }, trick: [], leader: 0, turn: -1, taken: [0, 0], tricks: [0, 0],
    lastTrick: null, played: [], eyes: [0, 0], mult: 1, eggs: false, result: null, winner: -1, hadEggs: false, awarded: false,
  };
}
function newDeal(g) {
  g.dealNo += 1;
  g.dealer = (g.dealer + 1) % 4;
  const deck = shuffle(SUITS.flatMap(s => RANKS.map(r => r + s)));
  for (let i = 0; i < 4; i++) g.hands[S_(i)] = deck.slice(i * 8, i * 8 + 8);
  const h = [0, 1, 2, 3].find(i => g.hands[S_(i)].includes('JC'));
  g.owner = h;
  if (g.dealNo === 1 || !g.suitOwner) {
    g.suitOwner = {};
    g.suitOwner[S_(h)] = 'C'; g.suitOwner[S_((h + 2) % 4)] = 'S';
    g.suitOwner[S_((h + 1) % 4)] = 'H'; g.suitOwner[S_((h + 3) % 4)] = 'D';
    g.trump = 'C';
  } else {
    g.trump = g.suitOwner[S_(h)];
  }
  g.trumpTeam = h % 2;
  g.leader = g.turn = (g.dealer + 1) % 4;
  g.trick = []; g.taken = [0, 0]; g.tricks = [0, 0]; g.lastTrick = null; g.result = null; g.played = [];
  g.phase = 'playing';
  return g;
}
function playCardOn(g, seat, card) {
  const k = S_(seat);
  g.hands[k] = g.hands[k].filter(c => c !== card);
  g.trick = g.trick.concat([{ seat, card }]);
  if (g.trick.length === 1) { const s = eff(card, g.trump); if (s !== 'T' && !(g.played || (g.played = [])).includes(s)) g.played.push(s); }
  g.turn = g.trick.length < 4 ? (seat + 1) % 4 : -1;
  return g;
}
function resolveTrick(g) {
  const w = trickWinner(g.trick, g.trump);
  const p = g.trick.reduce((s, x) => s + pts(x.card), 0);
  const tm = w % 2;
  g.taken[tm] += p; g.tricks[tm] += 1;
  g.lastTrick = { cards: g.trick, winner: w };
  g.trick = []; g.leader = g.turn = w;
  if (g.tricks[0] + g.tricks[1] === 8) scoreDeal(g);
  return g;
}
// Подсчёт глаз за раздачу:
//  • голая (все 8 взяток) — партия окончена;
//  • 60:60 — яйца: глаза не открываются, следующая раздача разыгрывается «на яйца» — победитель открывает 4 глаза;
//  • первая раздача — победитель всегда открывает 2 глаза;
//  • выиграла пара с козырем — 1 глаз;
//  • выиграла пара без козыря — 2 глаза, если козырная пара набрала спас (31+), иначе 3.
const SPAS = 31, EGGS_EYES = 4;
function scoreDeal(g) {
  const [a, b] = g.taken;
  const r = { pts: [a, b], tricks: g.tricks.slice(), team: -1, eyes: 0, kind: '', trumpTeam: g.trumpTeam, dealNo: g.dealNo, onEggs: !!g.eggs };
  if (g.tricks[0] === 8 || g.tricks[1] === 8) {
    r.team = g.tricks[0] === 8 ? 0 : 1; r.kind = 'golaya';
    g.eyes[r.team] = Math.max(12, g.eyes[r.team]);
    g.eggs = false;
  } else if (a === 60) {
    r.kind = 'eggs'; g.eggs = true; g.hadEggs = true;
  } else {
    const w = a > 60 ? 0 : 1, l = 1 - w;
    let e;
    if (g.eggs) { e = EGGS_EYES; r.why = 'eggs'; }
    else if (g.dealNo === 1) { e = 2; r.why = 'first'; } // первая раздача — всегда 2 глаза
    else if (w === g.trumpTeam) { e = 1; r.why = 'own'; }
    else if (g.taken[l] >= SPAS) { e = 2; r.why = 'spas'; }
    else { e = 3; r.why = 'nospas'; }
    g.eggs = false;
    r.team = w; r.eyes = e; r.kind = 'win';
    g.eyes[w] = Math.min(12, g.eyes[w] + e);
  }
  g.result = r;
  if (g.eyes[0] >= 12 || g.eyes[1] >= 12) { g.phase = 'over'; g.winner = g.eyes[0] >= 12 ? 0 : 1; }
  else g.phase = 'dealEnd';
  g.turn = -1;
}

function botCard(g, seat) {
  const t = g.trump, hand = g.hands[S_(seat)], trick = g.trick;
  const legal = legalCards(hand, trick, t, g.played);
  const cheap = (x, y) => (pts(x) - pts(y)) || ((isTrump(x, t) ? 1 : 0) - (isTrump(y, t) ? 1 : 0)) || (power(x, t) - power(y, t));
  const lowest = arr => arr.slice().sort(cheap)[0];
  if (!trick.length) {
    const trumps = hand.filter(c => isTrump(c, t));
    const plain = legal.filter(c => !isTrump(c, t));
    const aces = plain.filter(c => c[0] === 'A');
    if (aces.length) return aces[0];
    if (trumps.length >= 4) {
      const top = trumps.slice().sort((x, y) => power(y, t) - power(x, t))[0];
      if (top === 'JC' || top === 'JS') return top;
    }
    return plain.length ? lowest(plain) : lowest(legal);
  }
  const cur = trickWinner(trick, t);
  const partnerWins = cur % 2 === seat % 2;
  const last = trick.length === 3;
  const curCard = trick.find(x => x.seat === cur).card;
  const winners = legal.filter(c => trickWinner(trick.concat([{ seat, card: c }]), t) === seat);
  const onTable = trick.reduce((s, x) => s + pts(x.card), 0);
  if (partnerWins) {
    const safe = last || power(curCard, t) >= 104 || (eff(curCard, t) !== 'T' && curCard[0] === 'A' && trick.length === 2);
    if (safe) {
      const plain = legal.filter(c => !isTrump(c, t));
      const pool = plain.length ? plain : legal.filter(c => c[0] !== 'J');
      const src = pool.length ? pool : legal;
      return src.slice().sort((x, y) => pts(y) - pts(x) || power(x, t) - power(y, t))[0];
    }
    return lowest(legal);
  }
  if (winners.length) {
    const cheapestWin = winners.slice().sort((x, y) => power(x, t) - power(y, t))[0];
    if (last || onTable >= 3 || !isTrump(cheapestWin, t)) return cheapestWin;
    return lowest(legal);
  }
  return lowest(legal);
}

module.exports = { SUITS, RANKS, S_, pts, isTrump, eff, power, trickWinner, legalCards, isUnplayedAce, freshGame, newDeal, playCardOn, resolveTrick, scoreDeal, botCard };
