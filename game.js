'use strict';

/* ============ 基本定数 ============ */
const N = 15;                 // 盤面サイズ
const CELL = 36;              // 1マスのピクセル数
const MARGIN = 42;            // 盤面の余白(座標表示用)
const BOARD_PX = MARGIN * 2 + CELL * (N - 1);
const EMPTY = 0, BLACK = 1, WHITE = 2;   // BLACK=先手(ホスト/AI戦では自分), WHITE=後手
const COLS = 'ABCDEFGHIJKLMNO';
const PEER_PREFIX = 'pentoren-';

// 12種のペントミノ。カードに描かれる向き=有効な鏡像(回転のみ可・裏返し不可)
const PENTOMINOES = {
  F: [[1,0],[2,0],[0,1],[1,1],[1,2]],
  I: [[0,0],[1,0],[2,0],[3,0],[4,0]],
  L: [[0,0],[0,1],[0,2],[0,3],[1,3]],
  P: [[0,0],[1,0],[0,1],[1,1],[0,2]],
  N: [[1,0],[1,1],[0,2],[1,2],[0,3]],
  T: [[0,0],[1,0],[2,0],[1,1],[1,2]],
  U: [[0,0],[2,0],[0,1],[1,1],[2,1]],
  V: [[0,0],[0,1],[0,2],[1,2],[2,2]],
  W: [[0,0],[0,1],[1,1],[1,2],[2,2]],
  X: [[1,0],[0,1],[1,1],[2,1],[1,2]],
  Y: [[1,0],[0,1],[1,1],[1,2],[1,3]],
  Z: [[0,0],[1,0],[1,1],[1,2],[2,2]],
};
const LETTERS = Object.keys(PENTOMINOES);

/* ============ 形の前計算 ============ */
function normalize(cells) {
  const mx = Math.min(...cells.map(c => c[0]));
  const my = Math.min(...cells.map(c => c[1]));
  return cells.map(([x, y]) => [x - mx, y - my])
              .sort((a, b) => a[1] - b[1] || a[0] - b[0]);
}
const shapeKey = cells => cells.map(c => c.join(',')).join(';');
const rot90 = cells => cells.map(([x, y]) => [-y, x]);

// 文字ごとの回転バリエーション(重複除去)
const ORIENTS = {};
for (const L of LETTERS) {
  const seen = new Set();
  let cur = normalize(PENTOMINOES[L]);
  for (let i = 0; i < 4; i++) {
    seen.add(shapeKey(cur));
    cur = normalize(rot90(cur));
  }
  ORIENTS[L] = [...seen].map(s => s.split(';').map(p => p.split(',').map(Number)));
}

// 盤面上の全配置パターン: PLACEMENTS[L] = [ [idx5つ], ... ]
const PLACEMENTS = {};
const CELL_PATTERNS = {}; // CELL_PATTERNS[L][cellIdx] = パターンindex配列
for (const L of LETTERS) {
  const pats = [];
  for (const o of ORIENTS[L]) {
    const w = Math.max(...o.map(c => c[0])) + 1;
    const h = Math.max(...o.map(c => c[1])) + 1;
    for (let dy = 0; dy <= N - h; dy++)
      for (let dx = 0; dx <= N - w; dx++)
        pats.push(o.map(([x, y]) => (y + dy) * N + (x + dx)));
  }
  PLACEMENTS[L] = pats;
  const m = Array.from({ length: N * N }, () => []);
  pats.forEach((p, i) => p.forEach(idx => m[idx].push(i)));
  CELL_PATTERNS[L] = m;
}

/* ============ 状態 ============ */
let board, blackSet, whiteSet;      // 石は色(BLACK/WHITE)で管理
const targets = { [BLACK]: null, [WHITE]: null }; // 色→ターゲット文字(null=不明)
let mode = 'ai';          // 'ai' | 'net'
let myColor = BLACK;
let phase = 'menu';       // menu | draw | net | play | over
let turn = BLACK;
let hover = -1, lastMove = -1;
let winPattern = null;
let thinking = false;
let peer = null, conn = null;

const oppColor = () => (myColor === BLACK ? WHITE : BLACK);
const myStones = () => (myColor === BLACK ? blackSet : whiteSet);
const stonesOf = who => (who === BLACK ? blackSet : whiteSet);
const oppName = () => (mode === 'ai' ? 'AI' : '相手');

/* ============ DOM ============ */
const boardCv = document.getElementById('board');
const ctx = boardCv.getContext('2d');
const statusEl = document.getElementById('status');
const logEl = document.getElementById('log');
const candEl = document.getElementById('candidates');
const candCountEl = document.getElementById('cand-count');
const overlayEl = document.getElementById('overlay');
const ovModeEl = document.getElementById('ov-mode');
const ovNetEl = document.getElementById('ov-net');
const ovDrawEl = document.getElementById('ov-draw');
const netSetupEl = document.getElementById('net-setup');
const netWaitEl = document.getElementById('net-wait');
const netMsgEl = document.getElementById('net-msg');
const roomCodeEl = document.getElementById('room-code');
const joinCodeEl = document.getElementById('join-code');
const drawCardsEl = document.getElementById('draw-cards');
const cardPlayerCv = document.getElementById('card-player');
const cardAiCv = document.getElementById('card-ai');
const playerTargetNameEl = document.getElementById('player-target-name');
const difficultyEl = document.getElementById('difficulty');
const aiOptionsEl = document.getElementById('ai-options');

const dpr = window.devicePixelRatio || 1;
boardCv.width = BOARD_PX * dpr;
boardCv.height = BOARD_PX * dpr;
boardCv.style.width = BOARD_PX + 'px';
boardCv.style.height = BOARD_PX + 'px';
ctx.scale(dpr, dpr);

/* ============ ユーティリティ ============ */
const idx2xy = i => [i % N, (i / N) | 0];
const xy2idx = (x, y) => y * N + x;
const coordName = i => { const [x, y] = idx2xy(i); return COLS[x] + (y + 1); };
const shuffle = a => { const r = [...a]; for (let i = r.length - 1; i > 0; i--) { const j = (Math.random() * (i + 1)) | 0; [r[i], r[j]] = [r[j], r[i]]; } return r; };

function setStatus(text, cls) {
  statusEl.textContent = text;
  statusEl.className = 'status' + (cls ? ' ' + cls : '');
}
function addLog(text, cls) {
  const div = document.createElement('div');
  if (cls) div.className = cls;
  div.textContent = text;
  logEl.appendChild(div);
  while (logEl.children.length > 40) logEl.removeChild(logEl.firstChild);
  logEl.scrollTop = logEl.scrollHeight;
}

/* ============ 形判定 ============ */
// ownSet の中に letter の形(回転可)が含まれていればそのパターンを返す
function findWinningPattern(letter, ownSet) {
  for (const p of PLACEMENTS[letter]) {
    let ok = true;
    for (const i of p) if (!ownSet.has(i)) { ok = false; break; }
    if (ok) return p;
  }
  return null;
}

// letter の形が「あと1手で完成」する空きマス → Map<cellIdx, 完成するパターン数>
function completionCells(letter, ownSet, oppSet) {
  const res = new Map();
  for (const p of PLACEMENTS[letter]) {
    let missing = 0, missIdx = -1, blocked = false;
    for (const i of p) {
      if (oppSet.has(i)) { blocked = true; break; }
      if (!ownSet.has(i)) { missing++; missIdx = i; }
    }
    if (!blocked && missing === 1) res.set(missIdx, (res.get(missIdx) || 0) + 1);
  }
  return res;
}

// 「あと2個必要」なパターンから、m に置くと残り other が即勝セルになる対応表を作る
// 返り値: Map<置くマス, Set<新たに生じる即勝セル>> (Set が2以上ならダブルスレッド)
function threatMap(letter, ownSet, oppSet) {
  const map = new Map();
  for (const p of PLACEMENTS[letter]) {
    const miss = [];
    let blocked = false;
    for (const i of p) {
      if (oppSet.has(i)) { blocked = true; break; }
      if (!ownSet.has(i)) miss.push(i);
    }
    if (blocked || miss.length !== 2) continue;
    const [a, b] = miss;
    if (!map.has(a)) map.set(a, new Set());
    if (!map.has(b)) map.set(b, new Set());
    map.get(a).add(b); map.get(b).add(a);
  }
  return map;
}

// letter の形がまだ完成可能か(自分+空きマスだけで作れるパターンがあるか)
function isFeasible(letter, oppSet) {
  for (const p of PLACEMENTS[letter]) {
    let ok = true;
    for (const i of p) if (oppSet.has(i)) { ok = false; break; }
    if (ok) return true;
  }
  return false;
}

/* ============ AI ============ */
// AIは常に WHITE(後手)。黒=プレイヤー
const aiCandidates = new Set(); // AI目線で消去法により残っている相手ターゲット候補

function updateAiCandidates() {
  for (const L of [...aiCandidates]) {
    if (!isFeasible(L, whiteSet)) aiCandidates.delete(L); // 白が全パターンを塞いだ
  }
}

// セル idx に置いた時のスコア(攻め + 守り)
function scoreCell(idx, defend, myThreatMap, oppThreatMaps) {
  let score = Math.random() * 3;

  // 攻め:自分のターゲットに近づく
  const ownW = [100000, 800, 70, 9, 1, 0]; // idx を置く前の残り必要数(idx含む) → 重み
  for (const pi of CELL_PATTERNS[targets[WHITE]][idx]) {
    const p = PLACEMENTS[targets[WHITE]][pi];
    let miss = 0, bad = false;
    for (const i of p) {
      if (blackSet.has(i)) { bad = true; break; }
      if (!whiteSet.has(i)) miss++;
    }
    if (!bad) score += ownW[miss];
  }

  // 守り:相手の候補のうち最も完成に近い形を優先して潰す
  if (defend) {
    let defMax = 0;
    for (const L of aiCandidates) {
      let d = 0;
      for (const pi of CELL_PATTERNS[L][idx]) {
        const p = PLACEMENTS[L][pi];
        let oppHas = 0, bad = false;
        for (const i of p) {
          if (whiteSet.has(i)) { bad = true; break; }
          if (blackSet.has(i)) oppHas++;
        }
        if (bad) continue;
        const need = 5 - oppHas;
        d += [0, 400, 50, 7, 0, 0][need];
      }
      if (d > defMax) defMax = d;
    }
    score += defMax;
  }

  // つよい:強制手(次に即勝セルを作る手)の創出・相手の強制手の予防を評価
  if (myThreatMap) {
    const t = myThreatMap.get(idx);
    if (t) score += t.size * 150;
  }
  if (oppThreatMaps) {
    for (const m of oppThreatMaps.values()) {
      const t = m.get(idx);
      if (t) score += t.size * 40;
    }
  }
  return score;
}

function aiMove() {
  const difficulty = difficultyEl.value;
  const empties = [];
  for (let i = 0; i < N * N; i++) if (board[i] === EMPTY) empties.push(i);
  if (!empties.length) return -1;

  // 1. 自分が勝てるなら勝つ
  const myWins = completionCells(targets[WHITE], whiteSet, blackSet);
  if (myWins.size) {
    return [...myWins.entries()].sort((a, b) => b[1] - a[1])[0][0];
  }

  const doDefend = difficulty !== 'easy';
  const isHard = difficulty === 'hard';

  // 2. 相手が次に勝てる手を塞ぐ(候補全形について)
  if (doDefend) {
    const threats = new Map();
    for (const L of aiCandidates) {
      for (const [cell, cnt] of completionCells(L, blackSet, whiteSet)) {
        threats.set(cell, (threats.get(cell) || 0) + cnt);
      }
    }
    if (threats.size) {
      return [...threats.entries()].sort((a, b) => b[1] - a[1])[0][0];
    }
  }

  // つよい:フォーク(ダブルスレッド)の判定を先に済ませ、評価にも使う
  let myTMap = null, oppTMaps = null;
  if (isHard) {
    // 3. 自分がダブルスレッドを作れるなら作る(次のターンに確実に勝てる)
    myTMap = threatMap(targets[WHITE], whiteSet, blackSet);
    let forkCell = -1, forkN = 1;
    for (const [cell, others] of myTMap) {
      if (others.size > forkN) { forkN = others.size; forkCell = cell; }
    }
    if (forkCell >= 0) return forkCell;

    // 4. 相手のダブルスレッドを潰す
    oppTMaps = new Map();
    const oppFork = new Map();
    for (const L of aiCandidates) {
      const t = threatMap(L, blackSet, whiteSet);
      oppTMaps.set(L, t);
      for (const [cell, others] of t) {
        if (others.size >= 2) oppFork.set(cell, (oppFork.get(cell) || 0) + others.size);
      }
    }
    if (oppFork.size) {
      return [...oppFork.entries()].sort((a, b) => b[1] - a[1])[0][0];
    }
  }

  // 5. ヒューリスティックで最善手
  let best = -1, bestScore = -Infinity;
  for (const idx of empties) {
    const s = scoreCell(idx, doDefend, myTMap, oppTMaps);
    if (s > bestScore) { bestScore = s; best = idx; }
  }
  return best;
}

/* ============ ゲーム進行 ============ */
function clearBoard() {
  board = new Array(N * N).fill(EMPTY);
  blackSet = new Set(); whiteSet = new Set();
  hover = -1; lastMove = -1; winPattern = null; thinking = false;
  logEl.innerHTML = '';
}

function reset() {
  clearBoard();
  targets[BLACK] = targets[WHITE] = null;
  turn = BLACK;
  aiCandidates.clear();
  buildCandidates();
  drawCardFace(cardPlayerCv.getContext('2d'), null);
  drawCardBack(cardAiCv.getContext('2d'));
  playerTargetNameEl.textContent = '?';
  setStatus('モードを選んでください');
  ovShow('menu');
}

// remoteWin: 通信対戦で相手が勝利を申告した場合 {pat:[idx5つ], card:'L'}
function place(cell, who, remoteWin) {
  board[cell] = who;
  stonesOf(who).add(cell);
  lastMove = cell;
  const mine = who === myColor;
  addLog((mine ? 'あなた' : oppName()) + ' → ' + coordName(cell), mine ? 'you' : 'ai');

  const tgt = targets[who];
  let wp = tgt ? findWinningPattern(tgt, stonesOf(who)) : null;
  if (!wp && remoteWin) { wp = remoteWin.pat; targets[who] = remoteWin.card; }

  // オンライン:自分の手を送信(勝敗に関わらず)
  if (mode === 'net' && mine && conn && conn.open) {
    conn.send({ t: 'mv', c: cell, w: !!wp, pat: wp || undefined, card: wp ? targets[myColor] : undefined });
  }

  if (wp) { gameOver(who, wp); return; }
  if (!board.includes(EMPTY)) {
    phase = 'over';
    setStatus('引き分け(盤面が埋まりました)', 'draw');
    revealOppCard();
    return;
  }

  if (mode === 'ai') updateAiCandidates();
  buildCandidates();

  turn = who === BLACK ? WHITE : BLACK;
  if (mode === 'ai') {
    if (turn === WHITE) {
      thinking = true;
      setStatus('AIが考えています…');
      setTimeout(() => {
        const mv = aiMove();
        thinking = false;
        if (mv >= 0 && phase === 'play') place(mv, WHITE);
        else if (phase === 'play') { turn = BLACK; setStatus('あなたの番です'); }
      }, 450 + Math.random() * 400);
    } else {
      setStatus('あなたの番です');
    }
  } else {
    setStatus(turn === myColor ? 'あなたの番です' : '相手の番です');
  }
}

function gameOver(who, wp) {
  phase = 'over'; winPattern = wp;
  const mine = who === myColor;
  if (mine) setStatus('あなたの勝ち!', 'win');
  else setStatus(oppName() + 'の勝ち… (' + (targets[oppColor()] || '?') + ' でした)', 'lose');
  revealOppCard();
}

function revealOppCard() {
  drawCardFace(cardAiCv.getContext('2d'), targets[oppColor()]);
}

/* ============ 候補パネル ============ */
function buildCandidates() {
  candEl.innerHTML = '';
  let remain = 0;
  const mine = myStones();
  const myT = targets[myColor];
  for (const L of LETTERS) {
    if (L === myT) continue;
    const div = document.createElement('div');
    div.className = 'cand';
    const cv = document.createElement('canvas');
    cv.width = 34; cv.height = 34;
    drawMiniPent(cv.getContext('2d'), L, 34, 34, 6);
    const lb = document.createElement('div');
    lb.className = 'clabel'; lb.textContent = L;
    div.appendChild(cv); div.appendChild(lb);
    // 自分の石が全パターンを塞いだ形は、相手のターゲットであり得ない
    const possible = !myT || isFeasible(L, mine);
    if (!possible) div.classList.add('eliminated'); else remain++;
    candEl.appendChild(div);
  }
  candCountEl.textContent = myT ? `残り ${remain}/11` : '';
}

/* ============ 盤面描画 ============ */
function draw() {
  // 木目調の盤
  const g = ctx.createLinearGradient(0, 0, BOARD_PX, BOARD_PX);
  g.addColorStop(0, '#e7c37e'); g.addColorStop(.5, '#dfb565'); g.addColorStop(1, '#d4a856');
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, BOARD_PX, BOARD_PX);

  // グリッド
  ctx.strokeStyle = '#6d4a1f'; ctx.lineWidth = 1;
  ctx.beginPath();
  for (let i = 0; i < N; i++) {
    const p = MARGIN + i * CELL;
    ctx.moveTo(MARGIN, p); ctx.lineTo(BOARD_PX - MARGIN, p);
    ctx.moveTo(p, MARGIN); ctx.lineTo(p, BOARD_PX - MARGIN);
  }
  ctx.stroke();
  // 外枠を少し太く
  ctx.lineWidth = 2.4;
  ctx.strokeRect(MARGIN, MARGIN, CELL * (N - 1), CELL * (N - 1));

  // 星
  ctx.fillStyle = '#6d4a1f';
  for (const [x, y] of [[3,3],[3,11],[7,7],[11,3],[11,11]]) {
    ctx.beginPath();
    ctx.arc(MARGIN + x * CELL, MARGIN + y * CELL, 4, 0, Math.PI * 2);
    ctx.fill();
  }

  // 座標
  ctx.fillStyle = '#5c3d17';
  ctx.font = '12px Kaname, monospace';
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (let i = 0; i < N; i++) {
    ctx.fillText(COLS[i], MARGIN + i * CELL, MARGIN / 2);
    ctx.fillText(String(i + 1), MARGIN / 2 - 4, MARGIN + i * CELL);
  }

  // 石
  for (let i = 0; i < N * N; i++) {
    if (board[i] !== EMPTY) drawStone(i, board[i]);
  }

  // ホバーゴースト
  if (phase === 'play' && turn === myColor && !thinking && hover >= 0 && board[hover] === EMPTY) {
    drawStone(hover, myColor, 0.45);
  }

  // 最後の手マーカー
  if (lastMove >= 0 && phase === 'play') {
    const [x, y] = idx2xy(lastMove);
    ctx.strokeStyle = board[lastMove] === myColor ? '#4fc3f7' : '#ef5350';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(MARGIN + x * CELL, MARGIN + y * CELL, 6, 0, Math.PI * 2);
    ctx.stroke();
  }

  // 勝利形を強調(点滅)
  if (winPattern) {
    const t = (Math.sin(performance.now() / 200) + 1) / 2;
    ctx.strokeStyle = `rgba(255, 215, 80, ${0.5 + t * 0.5})`;
    ctx.lineWidth = 3;
    for (const i of winPattern) {
      const [x, y] = idx2xy(i);
      ctx.beginPath();
      ctx.arc(MARGIN + x * CELL, MARGIN + y * CELL, CELL * 0.46, 0, Math.PI * 2);
      ctx.stroke();
    }
  }

  requestAnimationFrame(draw);
}

function drawStone(idx, who, alpha = 1) {
  const [x, y] = idx2xy(idx);
  const cx = MARGIN + x * CELL, cy = MARGIN + y * CELL;
  const r = CELL * 0.44;
  ctx.save();
  ctx.globalAlpha = alpha;
  const g = ctx.createRadialGradient(cx - r * .35, cy - r * .4, r * .1, cx, cy, r);
  if (who === BLACK) { g.addColorStop(0, '#666'); g.addColorStop(1, '#0a0a0a'); }
  else { g.addColorStop(0, '#fff'); g.addColorStop(1, '#c9c9c9'); }
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
  ctx.strokeStyle = 'rgba(0,0,0,.4)'; ctx.lineWidth = 1; ctx.stroke();
  ctx.restore();
}

/* ============ カード描画 ============ */
function drawMiniPent(c, letter, w, h, cellSize) {
  const cells = normalize(PENTOMINOES[letter]);
  const bw = Math.max(...cells.map(p => p[0])) + 1;
  const bh = Math.max(...cells.map(p => p[1])) + 1;
  const ox = (w - bw * cellSize) / 2, oy = (h - bh * cellSize) / 2;
  for (const [x, y] of cells) {
    c.fillStyle = '#8f7bd8';
    c.fillRect(ox + x * cellSize, oy + y * cellSize, cellSize, cellSize);
    c.strokeStyle = '#15151f';
    c.strokeRect(ox + x * cellSize + .5, oy + y * cellSize + .5, cellSize - 1, cellSize - 1);
  }
}

function roundRect(c, x, y, w, h, r) {
  c.beginPath();
  c.moveTo(x + r, y);
  c.arcTo(x + w, y, x + w, y + h, r);
  c.arcTo(x + w, y + h, x, y + h, r);
  c.arcTo(x, y + h, x, y, r);
  c.arcTo(x, y, x + w, y, r);
  c.closePath();
}

function drawCardBack(c) {
  const w = c.canvas.width, h = c.canvas.height;
  c.fillStyle = '#2a3a6e';
  roundRect(c, 0, 0, w, h, 8); c.fill();
  c.strokeStyle = '#4a5a9e'; c.lineWidth = 2;
  roundRect(c, 3, 3, w - 6, h - 6, 6); c.stroke();
  c.fillStyle = 'rgba(255,255,255,.08)';
  for (let i = -h; i < w; i += 12) {
    c.beginPath();
    c.moveTo(i, 0); c.lineTo(i + 6, 0); c.lineTo(i + 6 + h, h); c.lineTo(i + h, h);
    c.fill();
  }
  c.fillStyle = '#e0b34f';
  c.font = `${h * 0.3}px Kaname, monospace`;
  c.textAlign = 'center'; c.textBaseline = 'middle';
  c.fillText('?', w / 2, h / 2);
}

function drawCardFace(c, letter) {
  const w = c.canvas.width, h = c.canvas.height;
  c.fillStyle = '#f2e8d0';
  roundRect(c, 0, 0, w, h, 8); c.fill();
  c.strokeStyle = '#8a6d3b'; c.lineWidth = 2;
  roundRect(c, 3, 3, w - 6, h - 6, 6); c.stroke();
  if (!letter) {
    c.fillStyle = '#8a6d3b';
    c.font = `${h * 0.3}px Kaname, monospace`;
    c.textAlign = 'center'; c.textBaseline = 'middle';
    c.fillText('?', w / 2, h / 2);
    return;
  }
  const cells = normalize(PENTOMINOES[letter]);
  const bw = Math.max(...cells.map(p => p[0])) + 1;
  const bh = Math.max(...cells.map(p => p[1])) + 1;
  const cs = Math.min((w - 22) / bw, (h - 34) / bh);
  const ox = (w - bw * cs) / 2, oy = ((h - 16) - bh * cs) / 2;
  for (const [x, y] of cells) {
    c.fillStyle = '#5a4a8a';
    c.fillRect(ox + x * cs, oy + y * cs, cs, cs);
    c.strokeStyle = '#f2e8d0'; c.lineWidth = 1.5;
    c.strokeRect(ox + x * cs + .5, oy + y * cs + .5, cs - 1, cs - 1);
  }
  c.fillStyle = '#3a2f1a';
  c.font = `bold ${Math.min(20, cs)}px Kaname, monospace`;
  c.textAlign = 'center'; c.textBaseline = 'bottom';
  c.fillText(letter, w / 2, h - 6);
}

/* ============ オーバーレイ制御 ============ */
function ovShow(state) {
  overlayEl.classList.remove('hidden');
  ovModeEl.classList.toggle('hidden', state !== 'menu');
  ovNetEl.classList.toggle('hidden', state !== 'net');
  ovDrawEl.classList.toggle('hidden', state !== 'draw');
  phase = state === 'menu' ? 'menu' : state === 'draw' ? 'draw' : 'net';
}

function setNetMsg(t) { netMsgEl.textContent = t; }

/* ============ AI戦 ============ */
function buildDrawCards() {
  drawCardsEl.innerHTML = '';
  for (const L of shuffle(LETTERS)) {
    const div = document.createElement('div');
    div.className = 'dcard';
    const cv = document.createElement('canvas');
    cv.width = 84; cv.height = 108;
    drawCardBack(cv.getContext('2d'));
    div.appendChild(cv);
    div.onclick = () => pickCard(div, cv, L);
    drawCardsEl.appendChild(div);
  }
}

function pickCard(div, cv, letter) {
  if (targets[myColor] || phase !== 'draw') return;
  targets[BLACK] = letter;
  targets[WHITE] = shuffle(LETTERS.filter(l => l !== letter))[0];
  aiCandidates.clear();
  for (const L of LETTERS) if (L !== targets[WHITE]) aiCandidates.add(L);

  div.classList.add('picked');
  drawCardFace(cv.getContext('2d'), letter);
  drawCardFace(cardPlayerCv.getContext('2d'), letter);
  playerTargetNameEl.textContent = letter + ' ピース';

  setTimeout(() => {
    overlayEl.classList.add('hidden');
    phase = 'play';
    setStatus('あなたの番です(先手・黒)');
    addLog('ゲーム開始! あなたのターゲットは ' + letter);
    buildCandidates();
  }, 1100);
}

/* ============ オンライン対戦 ============ */
function newCode() {
  const chars = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
  let s = '';
  for (let i = 0; i < 4; i++) s += chars[(Math.random() * chars.length) | 0];
  return s;
}

function closePeer() {
  try { if (conn) conn.close(); } catch (e) {}
  try { if (peer) peer.destroy(); } catch (e) {}
  conn = null; peer = null;
}

function startHost() {
  if (typeof Peer === 'undefined') {
    setNetMsg('通信ライブラリを読み込めませんでした(インターネット接続が必要です)');
    return;
  }
  myColor = BLACK;
  closePeer();
  peer = new Peer(PEER_PREFIX + newCode());
  peer.on('open', id => {
    roomCodeEl.textContent = id.slice(PEER_PREFIX.length);
    netSetupEl.classList.add('hidden');
    netWaitEl.classList.remove('hidden');
  });
  peer.on('connection', c => {
    conn = c;
    setupConn();
    c.on('open', () => {
      setNetMsg('相手が接続しました。ゲーム開始!');
      hostDeal();
    });
  });
  peer.on('error', e => {
    if (e.type === 'unavailable-id') { closePeer(); startHost(); } // コード衝突→引き直し
    else setNetMsg('エラー: ' + e.type);
  });
}

function joinGame() {
  if (typeof Peer === 'undefined') {
    setNetMsg('通信ライブラリを読み込めませんでした(インターネット接続が必要です)');
    return;
  }
  const code = joinCodeEl.value.trim().toUpperCase();
  if (!code) { setNetMsg('コードを入力してください'); return; }
  myColor = WHITE;
  closePeer();
  peer = new Peer();
  peer.on('open', () => {
    conn = peer.connect(PEER_PREFIX + code);
    setupConn();
    conn.on('open', () => setNetMsg('接続しました。カード配布を待っています…'));
    conn.on('error', () => setNetMsg('接続に失敗しました'));
  });
  peer.on('error', e => setNetMsg('接続できませんでした: ' + e.type));
}

function setupConn() {
  conn.on('data', onNetData);
  conn.on('close', () => {
    conn = null;
    if (phase === 'play' || phase === 'over') {
      phase = 'over';
      setStatus('相手が切断しました', 'lose');
    } else {
      setNetMsg('切断されました');
    }
  });
}

function onNetData(d) {
  if (d.t === 'deal') {           // カード配布(ゲスト側が受信)
    targets[myColor] = d.card;
    targets[oppColor()] = null;
    startNetGame();
  } else if (d.t === 'mv') {      // 相手の手
    const ok = Number.isInteger(d.c) && d.c >= 0 && d.c < N * N;
    if (ok && phase === 'play' && turn === oppColor() && board[d.c] === EMPTY) {
      place(d.c, oppColor(), d.w ? { pat: d.pat, card: d.card } : null);
    }
  } else if (d.t === 'restart') { // 再戦要求(ホストのみ処理)
    if (myColor === BLACK && conn && conn.open) hostDeal();
  }
}

function hostDeal() {
  const [a, b] = shuffle(LETTERS);
  targets[myColor] = a;          // ホスト=BLACK
  targets[oppColor()] = null;    // 相手のカードは保持しない(情報を完全に隠す)
  conn.send({ t: 'deal', card: b });
  startNetGame();
}

function startNetGame() {
  clearBoard();
  phase = 'play';
  turn = BLACK;
  overlayEl.classList.add('hidden');
  drawCardFace(cardPlayerCv.getContext('2d'), targets[myColor]);
  drawCardBack(cardAiCv.getContext('2d'));
  playerTargetNameEl.textContent = targets[myColor] + ' ピース';
  setStatus(myColor === BLACK ? 'あなたの番です(先手・黒)' : '相手の番です(あなたは後手・白)');
  addLog('ゲーム開始! あなたのターゲットは ' + targets[myColor]);
  buildCandidates();
}

/* ============ 入力 ============ */
boardCv.addEventListener('mousemove', e => {
  const r = boardCv.getBoundingClientRect();
  const x = Math.round((e.clientX - r.left - MARGIN) / CELL);
  const y = Math.round((e.clientY - r.top - MARGIN) / CELL);
  hover = (x >= 0 && x < N && y >= 0 && y < N) ? xy2idx(x, y) : -1;
});
boardCv.addEventListener('mouseleave', () => { hover = -1; });
boardCv.addEventListener('click', () => {
  if (phase !== 'play' || turn !== myColor || thinking) return;
  if (hover < 0 || board[hover] !== EMPTY) return;
  place(hover, myColor);
});

document.getElementById('btn-vs-ai').onclick = () => {
  mode = 'ai'; myColor = BLACK;
  aiOptionsEl.classList.remove('hidden');
  buildDrawCards();
  setStatus('カードをひいてください');
  ovShow('draw');
};
document.getElementById('btn-vs-net').onclick = () => {
  mode = 'net';
  aiOptionsEl.classList.add('hidden');
  netSetupEl.classList.remove('hidden');
  netWaitEl.classList.add('hidden');
  setNetMsg('');
  ovShow('net');
};
document.getElementById('btn-host').onclick = startHost;
document.getElementById('btn-join').onclick = joinGame;
document.getElementById('btn-net-back').onclick = () => { closePeer(); ovShow('menu'); };
joinCodeEl.addEventListener('keydown', e => { if (e.key === 'Enter') joinGame(); });

document.getElementById('btn-restart').onclick = () => {
  if (mode === 'net' && conn && conn.open) {
    if (myColor === BLACK) hostDeal();
    else { conn.send({ t: 'restart' }); setStatus('再戦を要求しました'); }
  } else {
    closePeer();
    reset();
  }
};

/* ============ 開始 ============ */
reset();
draw();
