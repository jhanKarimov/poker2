const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const crypto = require('crypto');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' } });

app.use(express.static(path.join(__dirname)));
app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'index.html')));

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Royal Flush Casino running on port ${PORT}`));

// ─── Constants ───────────────────────────────────────────────────────────────
const STARTING_CHIPS = 1000;
const SB = 5;
const BB = 10;
const ACTION_TIMEOUT_MS = 35000;

const SUITS = ['♠', '♥', '♦', '♣'];
const VALUES = ['2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A'];
const EMOJIS = ['🦁', '🐺', '🦊', '🐻', '🐯', '🦅', '🐲', '🦝', '🎭', '🃏', '🤠', '👑'];
const BOT_NAMES = ['Viper', 'Stone', 'Joker', 'Goldie', 'Ace', 'Nova', 'Blaze', 'Ghost', 'Sable', 'Rex'];
let botIdCounter = 0;

const sleep = ms => new Promise(r => setTimeout(r, ms));
const uid = () => crypto.randomBytes(4).toString('hex');

// ─── Deck ─────────────────────────────────────────────────────────────────────
function buildDeck() {
  const d = [];
  SUITS.forEach(s => VALUES.forEach((v, i) =>
    d.push({ val: v, suit: s, rank: i, id: `${v}${s}`, red: s === '♥' || s === '♦' })
  ));
  for (let i = d.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [d[i], d[j]] = [d[j], d[i]];
  }
  return d;
}

// ─── Hand Evaluation (same logic as client) ───────────────────────────────────
function combos(arr, k) {
  const out = [];
  function go(s, c) {
    if (c.length === k) { out.push([...c]); return; }
    for (let i = s; i < arr.length; i++) { c.push(arr[i]); go(i + 1, c); c.pop(); }
  }
  go(0, []);
  return out;
}

function eval5(hand) {
  const s = [...hand].sort((a, b) => b.rank - a.rank);
  const rk = s.map(c => c.rank), su = s.map(c => c.suit);
  const isF = su.every(v => v === su[0]);
  const cnt = rk.reduce((a, r) => { a[r] = (a[r] || 0) + 1; return a; }, {});
  const byCnt = Object.entries(cnt).sort((a, b) => b[1] - a[1] || b[0] - a[0]).map(e => +e[0]);
  const uniq = [...new Set(rk)];
  const isStr = uniq.length >= 5 && (uniq[0] - uniq[4] === 4);
  const isW = JSON.stringify([...uniq].sort((a, b) => a - b).slice(0, 5)) === '[0,1,2,3,12]';
  const st = isStr || isW;
  if (st && isF) return { type: 8, ranks: rk, name: rk[0] === 12 && isF ? 'Royal Flush' : 'Straight Flush', hand: s };
  if (cnt[byCnt[0]] === 4) return { type: 7, ranks: byCnt, name: 'Four of a Kind', hand: s };
  if (cnt[byCnt[0]] === 3 && cnt[byCnt[1]] === 2) return { type: 6, ranks: byCnt, name: 'Full House', hand: s };
  if (isF) return { type: 5, ranks: rk, name: 'Flush', hand: s };
  if (st) return { type: 4, ranks: rk, name: 'Straight', hand: s };
  if (cnt[byCnt[0]] === 3) return { type: 3, ranks: byCnt, name: 'Three of a Kind', hand: s };
  if (cnt[byCnt[0]] === 2 && cnt[byCnt[1]] === 2) return { type: 2, ranks: byCnt, name: 'Two Pair', hand: s };
  if (cnt[byCnt[0]] === 2) return { type: 1, ranks: byCnt, name: `Pair of ${VALUES[byCnt[0]]}s`, hand: s };
  return { type: 0, ranks: byCnt, name: `High Card ${VALUES[byCnt[0]]}`, hand: s };
}

function cmpH(h1, h2) {
  if (h1.type !== h2.type) return h1.type - h2.type;
  for (let i = 0; i < Math.min(h1.ranks.length, h2.ranks.length); i++)
    if (h1.ranks[i] !== h2.ranks[i]) return h1.ranks[i] - h2.ranks[i];
  return 0;
}

function bestOf(cards) {
  const cs = cards.length <= 5 ? [cards] : combos(cards, 5);
  let best = { type: -1, ranks: [], name: '', hand: [] };
  for (const c of cs) { const h = eval5(c); if (cmpH(h, best) > 0) best = h; }
  return best;
}

// ─── Table management ─────────────────────────────────────────────────────────
const tables = new Map();

function createTable(name) {
  return {
    id: uid(),
    name: name || `Table ${tables.size + 1}`,
    seats: Array(6).fill(null),
    phase: 'waiting',
    community: [],
    pot: 0,
    currentBet: 0,
    dealerSeat: -1,
    activeSeat: -1,
    deck: [],
    hands: {},        // socketId -> Card[]
    log: [],
    pendingAction: null,
    gameRunning: false,
    startTimer: null,
  };
}

function findPlayerSeat(socketId) {
  for (const table of tables.values()) {
    const si = table.seats.findIndex(s => s?.socketId === socketId);
    if (si !== -1) return { table, seatIndex: si };
  }
  return null;
}

function getPublicState(table) {
  return {
    id: table.id,
    name: table.name,
    seats: table.seats.map(s => s ? {
      name: s.name,
      emoji: s.emoji,
      chips: s.chips,
      bet: s.bet,
      folded: s.folded,
      isAllIn: s.isAllIn,
      status: s.status,
      hasCards: !!(table.hands[s.socketId]?.length),
      socketId: s.socketId,
    } : null),
    community: table.community,
    pot: table.pot,
    currentBet: table.currentBet,
    phase: table.phase,
    dealerSeat: table.dealerSeat,
    activeSeat: table.activeSeat,
    log: table.log.slice(-40),
  };
}

function broadcastState(table) {
  io.to(table.id).emit('table_state', getPublicState(table));
}

function tableLog(table, msg, cls = '') {
  table.log.push({ msg, cls });
  if (table.log.length > 120) table.log.shift();
}

function getTablesList() {
  return [...tables.values()].map(t => ({
    id: t.id,
    name: t.name,
    seated: t.seats.filter(s => s !== null).length,
    max: t.seats.length,
    phase: t.phase,
  }));
}

// ─── Game helpers ─────────────────────────────────────────────────────────────
function seatedPlayers(table) { return table.seats.filter(s => s !== null); }
function activePlayers(table)  { return table.seats.filter(s => s && !s.folded); }
function bettingPlayers(table) { return table.seats.filter(s => s && !s.folded && !s.isAllIn); }
function oneLeft(table)        { return activePlayers(table).length <= 1; }

function nextSeat(table, from, requireActive = false) {
  const n = table.seats.length;
  for (let i = 1; i <= n; i++) {
    const si = (from + i) % n;
    const s = table.seats[si];
    if (!s) continue;
    if (requireActive && (s.folded || s.isAllIn)) continue;
    return si;
  }
  return from;
}

function postBlind(table, si, amount, label) {
  const s = table.seats[si];
  if (!s) return;
  const actual = Math.min(s.chips, amount);
  s.chips -= actual;
  s.bet = actual;
  table.pot += actual;
  if (s.chips === 0) s.isAllIn = true;
  s.status = label;
  tableLog(table, `${s.emoji} ${s.name} posts ${label} $${actual}`, 'le-sys');
}

function resetBets(table) {
  table.currentBet = 0;
  table.seats.forEach(s => { if (s) s.bet = 0; });
}

// ─── Bot AI ───────────────────────────────────────────────────────────────────
function addBot(table) {
  const emptyIdx = table.seats.findIndex(s => s === null);
  if (emptyIdx === -1) return false;
  const name = BOT_NAMES[botIdCounter % BOT_NAMES.length];
  const emoji = EMOJIS[botIdCounter % EMOJIS.length];
  const botId = `bot_${++botIdCounter}`;
  table.seats[emptyIdx] = {
    socketId: botId, name, emoji,
    chips: STARTING_CHIPS, bet: 0,
    folded: false, isAllIn: false, status: '',
    isBot: true,
  };
  tableLog(table, `${emoji} ${name} (bot) joined seat ${emptyIdx + 1}`, 'le-sys');
  return true;
}

function botDecideServer(table, seatIndex, callAmt) {
  const seat = table.seats[seatIndex];
  const hand = table.hands[seat.socketId] || [];
  let strength = 0.4;
  if (hand.length >= 2) {
    if (table.community.length > 0) {
      strength = Math.min(1, bestOf([...hand, ...table.community]).type / 8 + 0.08);
    } else {
      const r1 = hand[0].rank, r2 = hand[1].rank;
      strength = Math.min(1, (r1 + r2) / 24 + (r1 === r2 ? 0.35 : 0) + (hand[0].suit === hand[1].suit ? 0.1 : 0));
    }
  }
  // Occasional bluff
  if (Math.random() < 0.12) strength = 0.35 + Math.random() * 0.5;

  if (callAmt > 0 && strength < 0.28 && Math.random() < 0.75) return { type: 'fold' };
  if (strength > 0.68 && Math.random() < 0.45 && seat.chips > callAmt + BB * 2) {
    const raiseTo = Math.min(seat.chips + seat.bet, table.currentBet + BB * (2 + Math.floor(Math.random() * 3)));
    return { type: 'raise', amount: raiseTo };
  }
  if (callAmt > 0) return { type: 'call' };
  return { type: 'check' };
}

// ─── Betting loop ─────────────────────────────────────────────────────────────
async function doBetting(table, startSeat) {
  const n = table.seats.length;
  const acted = new Set();
  let currentSeat = startSeat;
  let guard = 0;

  while (guard++ < 80) {
    const bp = bettingPlayers(table);
    if (bp.length <= 1) break;
    if (bp.every(s => acted.has(s.socketId)) && bp.every(s => s.bet === table.currentBet)) break;

    const seat = table.seats[currentSeat];
    currentSeat = (currentSeat + 1) % n;

    if (!seat || seat.folded || seat.isAllIn) continue;
    if (acted.has(seat.socketId) && seat.bet === table.currentBet) continue;

    table.activeSeat = table.seats.indexOf(seat);
    broadcastState(table);

    const callAmt = Math.min(seat.chips, table.currentBet - seat.bet);
    const action = await waitForAction(table, table.activeSeat, callAmt);
    applyAction(table, table.activeSeat, action);
    acted.add(seat.socketId);
    broadcastState(table);
  }

  table.activeSeat = -1;
}

function waitForAction(table, seatIndex, callAmt) {
  const seat = table.seats[seatIndex];
  // Bot: decide automatically after a short delay
  if (seat?.isBot) {
    return new Promise(resolve => {
      setTimeout(() => {
        const action = botDecideServer(table, seatIndex, callAmt);
        const verb = action.type === 'raise' ? `raises to $${action.amount}` : action.type === 'call' ? `calls $${callAmt}` : action.type;
        tableLog(table, `${seat.emoji} ${seat.name} ${verb}`, `le-${action.type === 'raise' ? 'raise' : 'call'}`);
        broadcastState(table);
        resolve(action);
      }, 700 + Math.random() * 800);
    });
  }
  return new Promise(resolve => {
    let timer;

    const resolveOnce = (action) => {
      clearTimeout(timer);
      if (table.pendingAction?.resolve === resolveOnce) table.pendingAction = null;
      resolve(action);
    };

    table.pendingAction = { seatIndex, resolve: resolveOnce };

    if (seat) {
      io.to(seat.socketId).emit('your_turn', {
        callAmount: callAmt,
        minRaise: Math.min(seat.chips + seat.bet, table.currentBet + BB),
        maxRaise: seat.chips + seat.bet,
        pot: table.pot,
        timeLimit: Math.floor(ACTION_TIMEOUT_MS / 1000),
      });
    }

    // Auto-fold on timeout
    timer = setTimeout(() => resolveOnce({ type: 'fold' }), ACTION_TIMEOUT_MS);
  });
}

function applyAction(table, seatIndex, action) {
  const seat = table.seats[seatIndex];
  if (!seat) return;
  const { type, amount } = action;
  const callAmt = Math.min(seat.chips, table.currentBet - seat.bet);

  if (type === 'fold') {
    seat.folded = true;
    seat.status = 'FOLD';
    tableLog(table, `${seat.emoji} ${seat.name} folds`, 'le-fold');
  } else if (type === 'check') {
    seat.status = 'CHECK';
    tableLog(table, `${seat.emoji} ${seat.name} checks`, 'le-call');
  } else if (type === 'call') {
    seat.chips -= callAmt;
    seat.bet += callAmt;
    table.pot += callAmt;
    if (seat.chips === 0) seat.isAllIn = true;
    seat.status = 'CALL';
    tableLog(table, `${seat.emoji} ${seat.name} calls $${callAmt}`, 'le-call');
  } else if (type === 'raise') {
    const raiseTo = Math.min(seat.chips + seat.bet, Math.max(+amount || 0, table.currentBet + BB));
    const cost = raiseTo - seat.bet;
    if (cost <= 0) { applyAction(table, seatIndex, { type: 'call' }); return; }
    seat.chips -= cost;
    seat.bet = raiseTo;
    table.pot += cost;
    if (raiseTo > table.currentBet) table.currentBet = raiseTo;
    if (seat.chips === 0) seat.isAllIn = true;
    seat.status = `RAISE $${raiseTo}`;
    tableLog(table, `${seat.emoji} ${seat.name} raises to $${raiseTo}`, 'le-raise');
  }
}

// ─── Showdown ─────────────────────────────────────────────────────────────────
async function doShowdown(table) {
  table.phase = 'showdown';
  table.activeSeat = -1;
  broadcastState(table);

  const alive = table.seats.filter(s => s && !s.folded);
  if (alive.length === 0) { finishHand(table); return; }

  if (alive.length === 1) {
    const w = alive[0];
    w.chips += table.pot;
    w.status = `WIN $${table.pot}`;
    tableLog(table, `🏆 ${w.emoji} ${w.name} wins $${table.pot} (everyone folded)`, 'le-win');
    table.pot = 0;
    broadcastState(table);
    await sleep(3000);
    finishHand(table);
    return;
  }

  // Evaluate hands
  const evaluated = alive.map(s => {
    const hand = table.hands[s.socketId] || [];
    const best = bestOf([...hand, ...table.community]);
    return { seat: s, hand, best };
  });
  evaluated.sort((a, b) => cmpH(b.best, a.best));
  const topScore = evaluated[0].best;
  const winners = evaluated.filter(e => cmpH(e.best, topScore) === 0);

  // Reveal all hands to everyone
  const revealData = {};
  evaluated.forEach(e => {
    revealData[e.seat.socketId] = { hand: e.hand, handName: e.best.name };
  });
  io.to(table.id).emit('showdown_reveal', { revealData, community: table.community });

  tableLog(table, '─── Showdown ───', 'le-ph');
  evaluated.forEach(e => tableLog(table, `${e.seat.emoji} ${e.seat.name}: ${e.best.name}`, 'le-sys'));

  const prize = Math.floor(table.pot / winners.length);
  const rem = table.pot % winners.length;
  winners.forEach((w, i) => {
    const won = prize + (i === 0 ? rem : 0);
    w.seat.chips += won;
    w.seat.status = `WIN $${won}`;
    tableLog(table, `🏆 ${w.seat.emoji} ${w.seat.name} wins $${won} — ${w.best.name}`, 'le-win');
  });
  table.pot = 0;

  broadcastState(table);
  await sleep(4500);
  finishHand(table);
}

// ─── Finish hand ──────────────────────────────────────────────────────────────
function finishHand(table) {
  // Remove busted players
  table.seats.forEach((s, i) => {
    if (s && s.chips <= 0) {
      tableLog(table, `${s.emoji} ${s.name} is out of chips`, 'le-sys');
      if (s.isBot) {
        // Rebuy bot automatically
        s.chips = STARTING_CHIPS;
        s.folded = false; s.isAllIn = false; s.bet = 0; s.status = '';
      } else {
        io.to(s.socketId).emit('busted', { msg: 'Out of chips! Refresh to rejoin.' });
        table.seats[i] = null;
      }
    }
  });

  table.phase = 'waiting';
  table.community = [];
  table.hands = {};
  table.activeSeat = -1;
  table.gameRunning = false;
  table.seats.forEach(s => {
    if (s) { s.bet = 0; s.folded = false; s.isAllIn = false; s.status = ''; }
  });

  broadcastState(table);
  io.emit('tables_list', getTablesList());

  const still = seatedPlayers(table);
  if (still.length >= 2) {
    table.startTimer = setTimeout(() => {
      if (!table.gameRunning && seatedPlayers(table).length >= 2) startHand(table);
    }, 3000);
    io.to(table.id).emit('next_hand_soon', { seconds: 3 });
  }
}

// ─── Start hand ───────────────────────────────────────────────────────────────
async function startHand(table) {
  if (table.gameRunning) return;
  const seated = seatedPlayers(table);
  if (seated.length < 2) return;

  table.gameRunning = true;
  table.deck = buildDeck();
  table.community = [];
  table.pot = 0;
  table.hands = {};
  table.log = table.log.slice(-10);
  table.seats.forEach(s => {
    if (s) { s.folded = false; s.isAllIn = false; s.bet = 0; s.status = ''; }
  });

  // Advance dealer
  const n = table.seats.length;
  if (table.dealerSeat === -1) {
    table.dealerSeat = table.seats.findIndex(s => s !== null);
  } else {
    table.dealerSeat = nextSeat(table, table.dealerSeat);
  }

  // Find SB (next after dealer) and BB (next after SB)
  const sbIdx = nextSeat(table, table.dealerSeat);
  const bbIdx = nextSeat(table, sbIdx);

  table.currentBet = BB;
  tableLog(table, '─── New Hand ───', 'le-ph');
  postBlind(table, sbIdx, SB, 'SB');
  postBlind(table, bbIdx, BB, 'BB');

  // Deal hole cards
  table.seats.forEach(s => {
    if (s) {
      const hand = [table.deck.pop(), table.deck.pop()];
      table.hands[s.socketId] = hand;
      if (!s.isBot) io.to(s.socketId).emit('your_hand', { hand });
    }
  });

  table.phase = 'preflop';
  tableLog(table, '🃏 Hole cards dealt — Pre-Flop', 'le-comm');
  broadcastState(table);

  // Preflop: first to act is seat after BB
  const preflopStart = nextSeat(table, bbIdx);
  await doBetting(table, preflopStart);
  if (oneLeft(table)) { await doShowdown(table); return; }

  // Flop
  table.community.push(table.deck.pop(), table.deck.pop(), table.deck.pop());
  table.phase = 'flop';
  resetBets(table);
  tableLog(table, `🃏 Flop: ${table.community.map(c => c.val + c.suit).join(' ')}`, 'le-comm');
  broadcastState(table);
  await sleep(600);
  await doBetting(table, nextSeat(table, table.dealerSeat));
  if (oneLeft(table)) { await doShowdown(table); return; }

  // Turn
  table.community.push(table.deck.pop());
  table.phase = 'turn';
  resetBets(table);
  tableLog(table, `🃏 Turn: ${table.community[3].val + table.community[3].suit}`, 'le-comm');
  broadcastState(table);
  await sleep(500);
  await doBetting(table, nextSeat(table, table.dealerSeat));
  if (oneLeft(table)) { await doShowdown(table); return; }

  // River
  table.community.push(table.deck.pop());
  table.phase = 'river';
  resetBets(table);
  tableLog(table, `🃏 River: ${table.community[4].val + table.community[4].suit}`, 'le-comm');
  broadcastState(table);
  await sleep(500);
  await doBetting(table, nextSeat(table, table.dealerSeat));

  await doShowdown(table);
}

// ─── Socket handlers ──────────────────────────────────────────────────────────
io.on('connection', socket => {
  console.log('+ Connected:', socket.id);
  socket.emit('tables_list', getTablesList());

  socket.on('get_tables', () => socket.emit('tables_list', getTablesList()));

  socket.on('create_table', ({ name } = {}) => {
    const table = createTable(name);
    tables.set(table.id, table);
    socket.join(table.id);
    socket.emit('joined_table', { tableId: table.id });
    socket.emit('table_state', getPublicState(table));
    io.emit('tables_list', getTablesList());
    console.log(`Table created: ${table.id} "${table.name}"`);
  });

  socket.on('join_table', ({ tableId } = {}) => {
    const table = tables.get(tableId);
    if (!table) { socket.emit('error_msg', { msg: 'Table not found' }); return; }
    socket.join(tableId);
    socket.emit('joined_table', { tableId });
    socket.emit('table_state', getPublicState(table));
    // Re-send hand if player is already seated (e.g. reconnect)
    const si = table.seats.findIndex(s => s?.socketId === socket.id);
    if (si !== -1 && table.hands[socket.id]) {
      socket.emit('your_hand', { hand: table.hands[socket.id] });
    }
  });

  socket.on('sit_down', ({ seatIndex, name, emoji } = {}) => {
    const tableId = [...socket.rooms].find(r => r !== socket.id && tables.has(r));
    if (!tableId) return;
    const table = tables.get(tableId);
    if (!table) return;

    if (seatIndex < 0 || seatIndex >= table.seats.length) return;
    if (table.seats[seatIndex] !== null) {
      socket.emit('error_msg', { msg: 'Seat taken — pick another' }); return;
    }
    if (table.seats.some(s => s?.socketId === socket.id)) {
      socket.emit('error_msg', { msg: 'Already seated' }); return;
    }

    const playerName = (name || 'Guest').replace(/[<>&"]/g, '').slice(0, 20);
    const playerEmoji = emoji || EMOJIS[Math.floor(Math.random() * EMOJIS.length)];

    table.seats[seatIndex] = {
      socketId: socket.id,
      name: playerName,
      emoji: playerEmoji,
      chips: STARTING_CHIPS,
      bet: 0,
      folded: false,
      isAllIn: false,
      status: '',
    };

    tableLog(table, `${playerEmoji} ${playerName} sat at seat ${seatIndex + 1}`, 'le-sys');
    broadcastState(table);
    io.emit('tables_list', getTablesList());

    const seated = seatedPlayers(table);
    if (seated.length >= 2 && !table.gameRunning) {
      if (table.startTimer) clearTimeout(table.startTimer);
      table.startTimer = setTimeout(() => {
        if (!table.gameRunning && seatedPlayers(table).length >= 2) startHand(table);
      }, 3000);
      io.to(tableId).emit('game_starting', { countdown: 3 });
    }
  });

  socket.on('action', ({ type, amount } = {}) => {
    const info = findPlayerSeat(socket.id);
    if (!info) return;
    const { table, seatIndex } = info;
    if (!table.pendingAction || table.pendingAction.seatIndex !== seatIndex) return;
    table.pendingAction.resolve({ type, amount: +amount || 0 });
  });

  socket.on('add_bot', () => {
    const tableId = [...socket.rooms].find(r => r !== socket.id && tables.has(r));
    if (!tableId) return;
    const table = tables.get(tableId);
    if (!table || table.gameRunning) { socket.emit('error_msg', { msg: 'Cannot add bot during a hand' }); return; }
    const added = addBot(table);
    if (!added) { socket.emit('error_msg', { msg: 'Table is full' }); return; }
    broadcastState(table);
    io.emit('tables_list', getTablesList());
    const seated = seatedPlayers(table);
    if (seated.length >= 2 && !table.gameRunning) {
      if (table.startTimer) clearTimeout(table.startTimer);
      table.startTimer = setTimeout(() => {
        if (!table.gameRunning && seatedPlayers(table).length >= 2) startHand(table);
      }, 3000);
      io.to(tableId).emit('game_starting', { countdown: 3 });
    }
  });

  socket.on('chat', ({ msg } = {}) => {
    const info = findPlayerSeat(socket.id);
    if (!info) return;
    const seat = info.table.seats[info.seatIndex];
    const clean = (msg || '').replace(/[<>&"]/g, '').slice(0, 120);
    if (!clean) return;
    const tableId = [...socket.rooms].find(r => r !== socket.id && tables.has(r));
    if (tableId) io.to(tableId).emit('chat_msg', { from: `${seat.emoji} ${seat.name}`, msg: clean });
  });

  socket.on('disconnect', () => {
    console.log('- Disconnected:', socket.id);
    const info = findPlayerSeat(socket.id);
    if (!info) return;
    const { table, seatIndex } = info;
    const seat = table.seats[seatIndex];
    if (seat) {
      tableLog(table, `${seat.emoji} ${seat.name} disconnected`, 'le-sys');
      // Auto-fold if it was their turn
      if (table.pendingAction?.seatIndex === seatIndex) {
        table.pendingAction.resolve({ type: 'fold' });
      }
      table.seats[seatIndex] = null;
    }
    broadcastState(table);
    io.emit('tables_list', getTablesList());
    // Clean up empty tables after a delay
    if (seatedPlayers(table).length === 0) {
      setTimeout(() => {
        if (seatedPlayers(table).length === 0) {
          tables.delete(table.id);
          console.log(`Table removed: ${table.id}`);
        }
      }, 60000);
    }
  });
});
