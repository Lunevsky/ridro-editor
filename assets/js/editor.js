/* Редактор схем маршрутов в стиле Ridro (шаблон схем 13 / 40A / Л).
   Координаты остановок и линии хранятся в долях подложки (0..1),
   поэтому схема не съезжает при замене подложки на другую картинку всей карты. */
(() => {
  'use strict';

  // Подложка по умолчанию. credit — подпись, которую требует лицензия источника.
  // Подложка и дороги подключены скриптами (base-opm.js, roads.js), чтобы редактор работал и открытым как файл.
  const BASE = { src: window.RIDRO_BASE, credit: '© Данные OpenProvinceMap' };

  const W = 1920, H = 1080;
  const Y = '#FADB04', Y_DIM = '#968216', BADGE = '#FFDB00', BLACK = '#131313';
  const FONT = 'RidroLD, Montserrat, sans-serif';   // RidroLD — только треугольные Л/Д, как на схемах (editor.css)
  const TYPES = { shot: 'Скриншот', main: 'Обязательная', req: 'По треб.' };
  const KEY = 'ridro-editor-v1';
  const DEFW = 10 / 4096;                // ширина линии там, где дорога неизвестна (доля ширины подложки)

  const $ = (s) => document.querySelector(s);
  const cv = $('#cv'), ctx = cv.getContext('2d');

  // line / back: [[x, y, w], …] — прямой и обратный рейс; w = ширина дороги под точкой (доля ширины подложки).
  // В режиме auto линии строятся по дорогам через остановки и их промежуточные точки stop.via / stop.viaBack.
  const blank = () => ({
    v: 1, number: '', stops: [], line: [], arrows: [],
    view: { cx: 0.5, cy: 0.5, span: 0.45 },
    list: { show: true, x: 40, y: 40 },
    legend: { show: true, x: 40, y: 760 },
    note: '', neutral: true, auto: true, widthScale: 1, returnTrip: true, back: [],
  });

  let S = load() || blank();
  let mode = 'pan';
  let base = new Image(), baseCredit = BASE.credit;
  let hits = { list: null, legend: null, labels: [] };
  let drag = null, selected = -1;

  // ---------- координаты ----------
  const k = () => W / (S.view.span * base.width);           // пикселей схемы на пиксель подложки
  const toOut = ([x, y]) => [(x - S.view.cx) * base.width * k() + W / 2, (y - S.view.cy) * base.height * k() + H / 2];
  const toNorm = ([ox, oy]) => [S.view.cx + (ox - W / 2) / (k() * base.width), S.view.cy + (oy - H / 2) / (k() * base.height)];
  const dist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);
  const inRect = (p, r) => r && p[0] >= r.x && p[0] <= r.x + r.w && p[1] >= r.y && p[1] <= r.y + r.h;

  function nearestOnLine(p, only) {    // p в пикселях схемы → ближайшая точка прямой (line) или обратной (back) линии
    let best = null;
    (only ? [only] : ['line', 'back']).forEach((which) => {
      const L0 = S[which] || [];
      for (let i = 0; i < L0.length - 1; i++) {
        const a = toOut(L0[i]), b = toOut(L0[i + 1]);
        const dx = b[0] - a[0], dy = b[1] - a[1], L = dx * dx + dy * dy || 1;
        const t = Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L));
        const pt = [a[0] + dx * t, a[1] + dy * t], d = dist(p, pt);
        if (!best || d < best.d) best = { i, pt, d, ang: Math.atan2(dy, dx), which };
      }
    });
    return best;
  }

  // ---------- дороги и прокладка ----------
  // roads.js (window.RIDRO_ROADS): граф дорог OpenProvinceMap в пикселях подложки 4096×4096 + ширина каждой дороги.
  let R = null;                          // { X, Y, seg: [[a, b, ширина, oneway, цена класса]], adj: [[to, seg], …] }
  // для каждой точки линии: у какой остановки лежат промежуточные точки перегона и номер участка между ними
  const meta = { line: { legOf: [], subOf: [] }, back: { legOf: [], subOf: [] } };
  const VIA = { line: 'via', back: 'viaBack' };   // промежуточные точки прямого / обратного рейса
  // «Цена» метра по классу дороги OSM: маршрут держится главных улиц и заезжает во дворы, только если иначе никак.
  const ROAD_COST = {
    motorway: 1, motorway_link: 1, trunk: 1, trunk_link: 1, primary: 1, primary_link: 1,
    secondary: 1.1, secondary_link: 1.1, tertiary: 1.5, tertiary_link: 1.5,
    unclassified: 2.2, road: 2.2, residential: 3, living_street: 5, service: 6,
  };
  const SNAP_R = 30 / 4096;              // радиус поиска соседних полос (разделённые дороги)

  async function loadRoads() {
    try {
      const d = window.RIDRO_ROADS;
      if (!d) throw new Error('нет файла assets/editor/roads.js');
      const n = d.nodes.length / 2, X = new Float64Array(n), Yc = new Float64Array(n);
      for (let i = 0; i < n; i++) { X[i] = d.nodes[2 * i] / d.size; Yc[i] = d.nodes[2 * i + 1] / d.size; }
      const seg = [], adj = Array.from({ length: n }, () => []);
      d.ways.forEach(([w, ow, c, ...ids]) => {
        const f = ROAD_COST[d.classes[c]] || 2;
        for (let i = 0; i < ids.length - 1; i++) {
          const s = seg.length, a = ids[i], b = ids[i + 1];
          seg.push([a, b, w / d.size, ow, f]);
          if (ow !== -1) adj[a].push([b, s]);
          if (ow !== 1) adj[b].push([a, s]);
        }
      });
      R = { X, Y: Yc, seg, adj };
      $('#roads-info').textContent = `Дороги загружены: ${d.ways.length}`;
    } catch (err) {
      $('#roads-info').textContent = `Дороги не загрузились (${err.message}) — линию можно рисовать вручную`;
    }
  }

  // Отрезки дорог рядом с точкой: ближайший + все в радиусе SNAP_R (чтобы выбрать полосу нужного направления).
  function snapAll(p) {
    const all = [];
    R.seg.forEach(([a, b], s) => {
      const ax = R.X[a], ay = R.Y[a], dx = R.X[b] - ax, dy = R.Y[b] - ay, L = dx * dx + dy * dy || 1e-12;
      const t = Math.max(0, Math.min(1, ((p[0] - ax) * dx + (p[1] - ay) * dy) / L));
      const pt = [ax + dx * t, ay + dy * t];
      all.push({ s, t, pt, d: dist(p, pt) });
    });
    all.sort((x, y) => x.d - y.d);
    return all.filter((c, i) => i === 0 || c.d <= SNAP_R).slice(0, 8);
  }
  const snap = (p) => snapAll(p)[0];

  // Кратчайший путь по дорогам с учётом одностороннего движения (A*). Возвращает [[x, y, w], …].
  // Старт и финиш — несколько соседних отрезков; отход от точки штрафуется, поэтому берётся ближайшая
  // полоса, по которой можно ехать в нужную сторону.
  function route(p, q) {
    const CA = snapAll(p), CB = snapAll(q), n = R.X.length, S0 = n, T = n + 1;
    const V0 = n + 2, V1 = n + 2 + CA.length;          // виртуальные узлы: старты [V0, V1), финиши [V1, …)
    const fwd = (s) => R.seg[s][3] !== -1, bwd = (s) => R.seg[s][3] !== 1;
    const tgt = new Map();               // узел дороги → финиши, на которые с него можно въехать
    CB.forEach((c, j) => {
      const [a, b] = R.seg[c.s];
      if (fwd(c.s)) tgt.set(a, [...(tgt.get(a) || []), j]);
      if (bwd(c.s)) tgt.set(b, [...(tgt.get(b) || []), j]);
    });
    const pt = (u) => (u === S0 ? p : u === T ? q : u >= V1 ? CB[u - V1].pt : u >= V0 ? CA[u - V0].pt : [R.X[u], R.Y[u]]);
    const edges = (u) => {               // [куда, отрезок, цена (иначе длина)]
      if (u === S0) return CA.map((c, i) => [V0 + i, -1, c.d * 2]);
      if (u === T) return [];
      if (u >= V1) return [[T, -1, CB[u - V1].d * 2]];
      if (u >= V0) {
        const c = CA[u - V0], [a, b] = R.seg[c.s], e = [];
        if (fwd(c.s)) e.push([b, c.s]);
        if (bwd(c.s)) e.push([a, c.s]);
        CB.forEach((cb, j) => { if (cb.s === c.s && ((fwd(c.s) && c.t <= cb.t) || (bwd(c.s) && c.t >= cb.t))) e.push([V1 + j, c.s]); });
        return e;
      }
      const e = R.adj[u].slice();
      (tgt.get(u) || []).forEach((j) => e.push([V1 + j, CB[j].s]));
      return e;
    };
    const g = new Map([[S0, 0]]), prev = new Map(), heap = [[dist(p, q), S0]];
    const push = (it) => { heap.push(it); let i = heap.length - 1; while (i) { const j = (i - 1) >> 1; if (heap[j][0] <= heap[i][0]) break; [heap[i], heap[j]] = [heap[j], heap[i]]; i = j; } };
    const pop = () => { const top = heap[0], last = heap.pop(); if (heap.length) { heap[0] = last; let i = 0; for (;;) { const l = 2 * i + 1, r = l + 1; let m = i; if (l < heap.length && heap[l][0] < heap[m][0]) m = l; if (r < heap.length && heap[r][0] < heap[m][0]) m = r; if (m === i) break; [heap[i], heap[m]] = [heap[m], heap[i]]; i = m; } } return top; };
    while (heap.length) {
      const [, u] = pop();
      if (u === T) break;
      const gu = g.get(u);
      for (const [v, s, cost] of edges(u)) {
        const nv = gu + (cost ?? dist(pt(u), pt(v)) * (s >= 0 ? R.seg[s][4] : 1));
        if (nv < (g.get(v) ?? Infinity)) { g.set(v, nv); prev.set(v, [u, s]); push([nv + dist(pt(v), q), v]); }
      }
    }
    if (!prev.has(T)) return null;
    const out = [];                      // от старта на дороге до финиша на дороге
    let v = prev.get(T)[0], w = DEFW;
    while (v !== S0) {
      const [u, s] = prev.get(v);
      if (s >= 0) w = R.seg[s][2];
      out.unshift([...pt(v), w]);
      v = u;
    }
    // линия доходит до самих точек, даже если подъезд выбран по соседней полосе
    if (out.length) { out.unshift([...p, out[0][2]]); out.push([...q, out[out.length - 1][2]]); }
    return out;
  }

  // Путь через точки seq; промежуточные точки перегона i берутся у остановки holderOf(i).
  function buildPath(seq, holderOf, which) {
    const line = [], m = meta[which];
    m.legOf = []; m.subOf = [];
    let broken = false;
    for (let i = 0; i < seq.length - 1; i++) {
      const holder = holderOf(i), hi = S.stops.indexOf(holder);
      const pts = [seq[i], ...(holder[VIA[which]] || []).map(([x, y]) => ({ x, y })), seq[i + 1]];
      for (let j = 0; j < pts.length - 1; j++) {
        const p = [pts[j].x, pts[j].y], q = [pts[j + 1].x, pts[j + 1].y];
        let r = route(p, q);
        if (!r) { broken = true; r = [[...p, DEFW], [...q, DEFW]]; }
        if (line.length) r = r.slice(1);   // стык участков — одна точка
        r.forEach((pt) => { line.push(pt); m.legOf.push(hi); m.subOf.push(j); });
      }
    }
    return { line, broken };
  }

  function computeLine() {
    if (!S.auto || !R) return;
    const st = S.stops;
    const f = buildPath(st, (i) => st[i], 'line');
    // обратный рейс: те же остановки с конца; точки перегона (i+1)→i лежат у остановки i в viaBack
    const rev = st.slice().reverse();
    const b = S.returnTrip ? buildPath(rev, (i) => rev[i + 1], 'back') : { line: [], broken: false };
    S.line = f.line; S.back = b.line;
    hint(f.broken || b.broken ? 'Между некоторыми точками нет пути по дорогам — там прямая' : '');
  }

  // Одна ширина на всю схему — по самой широкой дороге маршрута, чтобы дорога нигде не выглядывала из-под линии.
  function lineWidth() {
    let w = 0;
    [S.line, S.back || []].forEach((L) => L.forEach((pt) => { w = Math.max(w, pt[2] || 0); }));
    return Math.max(2, (w || DEFW) * base.width * k() * S.widthScale);
  }

  const snapStop = (n) => (S.auto && R ? snap(n).pt : n);   // в авторежиме точка всегда на ближайшей дороге

  // ---------- отрисовка ----------
  function font(w, px) { return `${w} ${px}px ${FONT}`; }

  // Значки на карте — в пропорции шаблона: линия 6 px ↔ кольцо радиусом 10.5 px.
  const markerScale = () => Math.max(0.6, lineWidth() / 6);

  function marker(x, y, type, scale = 1) {
    ctx.save();
    ctx.lineWidth = 4.5 * scale;
    ctx.strokeStyle = Y; ctx.fillStyle = Y;
    if (type === 'req') {
      ctx.beginPath(); ctx.arc(x, y, 6 * scale, 0, 7); ctx.fill();
    } else {
      ctx.beginPath(); ctx.arc(x, y, 10.5 * scale, 0, 7);
      ctx.fillStyle = '#050505'; ctx.fill(); ctx.stroke();
      if (type === 'shot') { ctx.fillStyle = Y; ctx.beginPath(); ctx.arc(x, y, 4.5 * scale, 0, 7); ctx.fill(); }
    }
    ctx.restore();
  }

  function arrowHead(x, y, ang, size = 15) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
    ctx.fillStyle = Y; ctx.beginPath();
    ctx.moveTo(size, 0); ctx.lineTo(-size * 0.7, -size * 0.7); ctx.lineTo(-size * 0.7, size * 0.7);
    ctx.closePath(); ctx.fill(); ctx.restore();
  }

  function box(r) {
    ctx.save();
    ctx.fillStyle = 'rgba(5,5,5,.82)'; ctx.strokeStyle = 'rgba(250,219,4,.45)'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.roundRect(r.x, r.y, r.w, r.h, 14); ctx.fill(); ctx.stroke();
    ctx.restore();
  }

  function draw(forExport = false) {
    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = '#080808'; ctx.fillRect(0, 0, W, H);
    if (!base.width) return;               // подложка ещё грузится
    const [x0, y0] = toOut([0, 0]);
    ctx.save();
    if (S.neutral) ctx.filter = 'grayscale(1)';
    ctx.drawImage(base, x0, y0, base.width * k(), base.height * k());
    ctx.restore();

    // линии прямого и обратного рейса одной ширины — по самой широкой дороге маршрута
    ctx.save();
    ctx.strokeStyle = Y; ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.lineWidth = lineWidth();
    [S.line, S.back || []].forEach((L) => {
      if (L.length < 2) return;
      ctx.beginPath();
      L.forEach((pt, i) => { const o = toOut(pt); i ? ctx.lineTo(...o) : ctx.moveTo(...o); });
      ctx.stroke();
    });
    ctx.restore();
    // стрелки направления: угол берётся от ближайшего отрезка линии
    S.arrows.forEach((a) => {
      const o = toOut(a), n = nearestOnLine(o, a[2] === 'back' ? 'back' : 'line');
      arrowHead(o[0], o[1], n ? n.ang : 0);
    });
    // точки линии (вручную) или промежуточные точки (авто) видны только при редактировании
    if ((mode === 'line' || mode === 'via') && !forExport) {
      ctx.save(); ctx.fillStyle = '#fff'; ctx.strokeStyle = '#000'; ctx.lineWidth = 2;
      const pts = S.auto ? S.stops.flatMap((s) => [...(s.via || []), ...(s.viaBack || [])]) : S.line;
      pts.forEach((p) => { const o = toOut(p); ctx.beginPath(); ctx.arc(o[0], o[1], S.auto ? 7 : 5, 0, 7); ctx.fill(); ctx.stroke(); });
      ctx.restore();
    }

    // остановки и подписи
    hits.labels = [];
    ctx.font = font(600, 25); ctx.textBaseline = 'middle';
    S.stops.forEach((s, i) => {
      const o = toOut([s.x, s.y]);
      marker(o[0], o[1], s.type, markerScale());
      const ms = markerScale();            // отступ подписи растёт вместе со значком
      const lx = o[0] + s.lx * ms, ly = o[1] + s.ly * ms, w = ctx.measureText(s.name).width;
      ctx.save();
      ctx.lineWidth = 5; ctx.strokeStyle = 'rgba(0,0,0,.75)'; ctx.lineJoin = 'round';
      ctx.strokeText(s.name, lx, ly);
      ctx.fillStyle = Y; ctx.fillText(s.name, lx, ly);
      ctx.restore();
      hits.labels.push({ x: lx - 4, y: ly - 18, w: w + 8, h: 36, i });
      if (i === selected && !forExport) {
        ctx.save(); ctx.strokeStyle = '#fff'; ctx.setLineDash([4, 4]); ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.arc(o[0], o[1], 18, 0, 7); ctx.stroke(); ctx.restore();
      }
    });

    hits.list = S.list.show ? drawList() : null;
    hits.legend = S.legend.show ? drawLegend() : null;
    drawBadge();
    if (baseCredit) {
      ctx.save(); ctx.font = font(500, 15); ctx.fillStyle = 'rgba(232,232,232,.5)'; ctx.textBaseline = 'alphabetic';
      ctx.textAlign = 'right'; ctx.fillText(baseCredit, W - 196 - 14, H - 12); ctx.restore();
    }
  }

  function drawList() {
    const pad = 28, step = 58, titleH = 90;
    ctx.font = font(700, 45);
    const tW = ctx.measureText('Маршрут').width;
    const num = S.number || '—';
    const nW = ctx.measureText(num).width + 24;
    ctx.font = font(600, 33);
    const itemsW = Math.max(0, ...S.stops.map((s) => ctx.measureText(s.name).width)) + 66;
    const r = { x: S.list.x, y: S.list.y, w: Math.max(tW + nW + 14, itemsW) + pad * 2, h: titleH + S.stops.length * step + pad - 6 };
    box(r);
    // заголовок с номером на плашке
    const ty = r.y + pad + 26;
    ctx.save();
    ctx.textBaseline = 'middle'; ctx.font = font(700, 45);
    const tx = r.x + (r.w - (tW + 14 + nW)) / 2;
    ctx.fillStyle = Y; ctx.fillText('Маршрут', tx, ty);
    ctx.fillStyle = '#403810'; ctx.fillRect(tx + tW + 14, ty - 28, nW, 56);
    ctx.fillStyle = Y; ctx.fillText(num, tx + tW + 26, ty + 1);
    // пунктир между значками
    const mx = r.x + pad + 8, y0 = r.y + titleH + 18;
    if (S.stops.length > 1) {
      ctx.strokeStyle = Y; ctx.lineWidth = 3; ctx.setLineDash([6, 8]);
      ctx.beginPath(); ctx.moveTo(mx, y0); ctx.lineTo(mx, y0 + (S.stops.length - 1) * step); ctx.stroke(); ctx.setLineDash([]);
    }
    ctx.font = font(600, 33);
    S.stops.forEach((s, i) => {
      const y = y0 + i * step;
      marker(mx, y, s.type, 0.95);
      ctx.fillStyle = s.type === 'req' ? Y_DIM : Y;
      ctx.fillText(s.name, mx + 38, y + 1);
    });
    ctx.restore();
    return r;
  }

  function wrap(text, maxW) {
    const out = [];
    text.split('\n').forEach((para) => {
      let line = '';
      para.split(/\s+/).forEach((word) => {
        const t = line ? line + ' ' + word : word;
        if (ctx.measureText(t).width > maxW && line) { out.push(line); line = word; } else line = t;
      });
      out.push(line);
    });
    return out;
  }

  function drawLegend() {
    const pad = 24, step = 55, w = 560;
    ctx.save();
    ctx.font = font(600, 24);
    const note = S.note.trim() ? wrap(S.note.trim(), w - pad * 2) : [];
    const r = { x: S.legend.x, y: S.legend.y, w, h: pad * 2 + step * 3 + 34 + (note.length ? 22 + note.length * 34 : 0) };
    box(r);
    ctx.fillStyle = Y; ctx.textBaseline = 'middle';
    let y = r.y + pad + 16;
    const x = r.x + pad;
    // строка 1: линия и направление
    ctx.strokeStyle = Y; ctx.lineWidth = 5; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(x + 4, y); ctx.lineTo(x + 44, y); ctx.stroke();
    ctx.fillText('Маршрут', x + 64, y);
    const ax = x + 260;
    ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(ax, y); ctx.lineTo(ax + 40, y); ctx.stroke();
    arrowHead(ax + 46, y, 0, 10);
    ctx.fillText('Направление', ax + 66, y);
    [['shot', 'Скриншот'], ['main', 'Обязательная остановка'], ['req', 'По требованию']].forEach(([t, label]) => {
      y += step;
      marker(x + 24, y, t, 0.9);
      ctx.fillStyle = Y; ctx.fillText(label, x + 64, y);
    });
    if (note.length) {
      y += step - 4;
      note.forEach((ln) => { ctx.fillText(ln, x, y); y += 34; });
    }
    ctx.restore();
    return r;
  }

  function drawBadge() {
    const w = 196, h = 84, x = W - w, y = H - h;
    ctx.save();
    ctx.fillStyle = BADGE;
    ctx.beginPath(); ctx.roundRect(x, y, w, h, [18, 0, 0, 0]); ctx.fill();
    ctx.fillStyle = BLACK; ctx.font = font(700, 45); ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('Ridro', x + w / 2, y + h / 2 + 2);
    ctx.restore();
  }

  // ---------- мышь ----------
  function pos(e) {
    const r = cv.getBoundingClientRect();
    return [(e.clientX - r.left) * W / r.width, (e.clientY - r.top) * H / r.height];
  }

  function hitTest(p) {
    const rs = Math.max(16, 12 * markerScale());
    for (let i = S.stops.length - 1; i >= 0; i--) if (dist(p, toOut([S.stops[i].x, S.stops[i].y])) < rs) return { t: 'stop', i };
    for (let i = S.arrows.length - 1; i >= 0; i--) if (dist(p, toOut(S.arrows[i])) < 14) return { t: 'arrow', i };
    if ((mode === 'line' || mode === 'via') && S.auto) {
      for (let i = 0; i < S.stops.length; i++) {
        for (const key of ['via', 'viaBack']) {
          const via = S.stops[i][key] || [];
          for (let j = 0; j < via.length; j++) if (dist(p, toOut(via[j])) < 12) return { t: 'via', i, j, key };
        }
      }
    }
    if (mode === 'line' && !S.auto) for (let i = S.line.length - 1; i >= 0; i--) if (dist(p, toOut(S.line[i])) < 10) return { t: 'vertex', i };
    for (const l of hits.labels) if (inRect(p, l)) return { t: 'label', i: l.i };
    if (inRect(p, hits.list)) return { t: 'list' };
    if (inRect(p, hits.legend)) return { t: 'legend' };
    return null;
  }

  function removeStop(i) {
    S.stops.splice(i, 1);
    if (S.stops[i - 1]) { S.stops[i - 1].via = []; S.stops[i - 1].viaBack = []; }   // перегон изменился — его ручные точки больше не к месту
  }

  let raf = 0;                                     // перестройка линии не чаще кадра
  function relayout() {
    if (raf) return;
    raf = requestAnimationFrame(() => { raf = 0; computeLine(); draw(); });
  }

  cv.addEventListener('pointerdown', (e) => {
    if (!base.width) return;
    const p = pos(e), h = hitTest(p);
    cv.setPointerCapture(e.pointerId);
    if (h && e.altKey) {                       // удаление
      if (h.t === 'stop') removeStop(h.i);
      if (h.t === 'arrow') S.arrows.splice(h.i, 1);
      if (h.t === 'vertex') S.line.splice(h.i, 1);
      if (h.t === 'via') S.stops[h.i][h.key].splice(h.j, 1);
      selected = -1; computeLine(); changed(true); return;
    }
    if (h && (h.t === 'stop' || h.t === 'label')) { selected = h.i; renderStops(); }
    drag = { h, start: p, last: p, moved: false };
  });

  cv.addEventListener('pointermove', (e) => {
    if (!drag) return;
    const p = pos(e), dx = p[0] - drag.last[0], dy = p[1] - drag.last[1];
    if (dist(p, drag.start) > 8) drag.moved = true;   // дрожание мыши при клике — не перетаскивание
    drag.last = p;
    if (!drag.moved) return;
    const h = drag.h;
    if (!h) {
      if (mode !== 'pan') return;
      S.view.cx -= dx / (k() * base.width); S.view.cy -= dy / (k() * base.height);
    } else if (h.t === 'stop') {
      let q;
      if (S.auto) q = snapStop(toNorm(p));
      else { const n = nearestOnLine(p); q = toNorm(n && n.d < 14 ? n.pt : p); }
      [S.stops[h.i].x, S.stops[h.i].y] = q;
      if (S.auto) { relayout(); return; }
    } else if (h.t === 'via') { S.stops[h.i][h.key][h.j] = snapStop(toNorm(p)); relayout(); return; }
    else if (h.t === 'label') { S.stops[h.i].lx += dx / markerScale(); S.stops[h.i].ly += dy / markerScale(); }
    else if (h.t === 'arrow') { const n = nearestOnLine(p); S.arrows[h.i] = n ? [...toNorm(n.pt), n.which] : toNorm(p); }
    else if (h.t === 'vertex') S.line[h.i] = [...toNorm(p), S.line[h.i][2] || DEFW];
    else if (h.t === 'list' || h.t === 'legend') { S[h.t].x += dx; S[h.t].y += dy; }
    draw();
  });

  cv.addEventListener('pointerup', (e) => {
    if (!drag) return;
    const { h, moved } = drag, p = pos(e);
    drag = null;
    if (moved) { changed(); return; }
    if (h) return;
    if (mode === 'line') {
      const n = nearestOnLine(p);
      if (S.auto) {                            // клик по линии — промежуточная точка перегона
        if (!n || n.d > 20) { hint('Кликните по линии, чтобы добавить промежуточную точку'); return; }
        const m = meta[n.which], st = S.stops[m.legOf[n.i]], key = VIA[n.which];
        (st[key] = st[key] || []).splice(m.subOf[n.i], 0, toNorm(n.pt));
        computeLine();
      } else if (n && n.d < 10 && n.which === 'line') S.line.splice(n.i + 1, 0, [...toNorm(n.pt), S.line[n.i][2] || DEFW]);
      else S.line.push([...toNorm(p), S.line.length ? S.line[S.line.length - 1][2] || DEFW : DEFW]);
    } else if (mode === 'stop') {
      let q;
      if (S.auto) q = snapStop(toNorm(p));
      else { const n = nearestOnLine(p); q = toNorm(n && n.d < 20 ? n.pt : p); }
      S.stops.push({ name: `Остановка ${S.stops.length + 1}`, type: 'main', x: q[0], y: q[1], lx: 18, ly: -24, via: [] });
      selected = S.stops.length - 1;
      computeLine();
      changed(true);
      const inputs = document.querySelectorAll('#stops .name');
      inputs[selected]?.select();
      return;
    } else if (mode === 'via') {
      if (!S.auto) { hint('Промежуточные точки работают, когда включена «Линия по дорогам»'); return; }
      if (S.stops.length < 2) { hint('Сначала поставьте хотя бы две остановки'); return; }
      addVia(snapStop(toNorm(p)));
    } else if (mode === 'arrow') {
      const n = nearestOnLine(p);
      if (!n || n.d > 20) { hint('Стрелку ставьте на линию маршрута'); return; }
      S.arrows.push([...toNorm(n.pt), n.which]);   // стрелка помнит свой рейс — на общем участке не перевернётся
    } else return;
    changed();
  });

  // Точка прямого рейса там, где она меньше всего удлиняет путь: перебираем все участки
  // «остановка → промежуточные точки → следующая остановка». Для обратного рейса — клик по его линии в режиме «Линия».
  function addVia(q) {
    let best = null;
    for (let i = 0; i < S.stops.length - 1; i++) {
      const via = S.stops[i].via || [];
      const pts = [[S.stops[i].x, S.stops[i].y], ...via, [S.stops[i + 1].x, S.stops[i + 1].y]];
      for (let j = 0; j < pts.length - 1; j++) {
        const cost = dist(pts[j], q) + dist(q, pts[j + 1]) - dist(pts[j], pts[j + 1]);
        if (!best || cost < best.cost) best = { cost, i, j };
      }
    }
    const st = S.stops[best.i];
    (st.via = st.via || []).splice(best.j, 0, q);
    computeLine();
  }

  cv.addEventListener('wheel', (e) => {
    e.preventDefault();
    if (!base.width) return;
    const p = pos(e), n = toNorm(p);
    S.view.span = Math.min(1.6, Math.max(0.05, S.view.span * (e.deltaY > 0 ? 1.12 : 1 / 1.12)));
    S.view.cx = n[0] - (p[0] - W / 2) / (k() * base.width);
    S.view.cy = n[1] - (p[1] - H / 2) / (k() * base.height);
    draw(); saveSoon();
  }, { passive: false });

  // ---------- боковая панель ----------
  const HINTS = {
    pan: 'Тяните карту, чтобы выбрать кадр',
    line: () => (S.auto ? 'Клик по линии — промежуточная точка; тяните её, чтобы пустить маршрут другой дорогой'
      : 'Клик — точка линии по ходу движения; клик по линии — вставить точку'),
    stop: () => (S.auto ? 'Клик — новая остановка в конец списка, линия построится по дорогам' : 'Клик — новая остановка (в конец списка)'),
    arrow: 'Клик по линии — стрелка направления',
    via: 'Клик по дороге — маршрут пройдёт через эту точку; точки можно тянуть, Alt+клик — удалить',
  };
  function hint(t) { const h = HINTS[mode]; $('#hint').textContent = t || (typeof h === 'function' ? h() : h); }
  function setMode(m) {
    mode = m;
    document.querySelectorAll('[data-mode]').forEach((b) => b.classList.toggle('on', b.dataset.mode === m));
    cv.style.cursor = m === 'pan' ? 'grab' : 'crosshair';
    hint(); draw();
  }
  document.querySelectorAll('[data-mode]').forEach((b) => b.addEventListener('click', () => setMode(b.dataset.mode)));

  function esc(s) { return String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])); }

  function renderStops() {
    const ol = $('#stops');
    ol.innerHTML = S.stops.map((s, i) => `
      <li class="${i === selected ? 'sel' : ''}" data-i="${i}">
        <input class="input name" value="${esc(s.name)}">
        <select class="input type">${Object.entries(TYPES).map(([v, t]) => `<option value="${v}"${v === s.type ? ' selected' : ''}>${t}</option>`).join('')}</select>
        <span class="btns"><button data-a="up" title="Выше">↑</button><button data-a="down" title="Ниже">↓</button><button data-a="del" title="Удалить">✕</button></span>
      </li>`).join('');
    $('#stops-empty').hidden = S.stops.length > 0;
  }
  $('#stops').addEventListener('input', (e) => {
    const i = +e.target.closest('li').dataset.i;
    if (e.target.classList.contains('name')) S.stops[i].name = e.target.value;
    if (e.target.classList.contains('type')) S.stops[i].type = e.target.value;
    changed();
  });
  $('#stops').addEventListener('focusin', (e) => {
    const li = e.target.closest('li'); if (!li) return;
    selected = +li.dataset.i; draw();
  });
  $('#stops').addEventListener('click', (e) => {
    const a = e.target.dataset.a; if (!a) return;
    const i = +e.target.closest('li').dataset.i, st = S.stops;
    const clearVia = (...js) => js.forEach((j) => { if (st[j]) { st[j].via = []; st[j].viaBack = []; } });
    if (a === 'del') removeStop(i);
    if (a === 'up' && i > 0) { [st[i - 1], st[i]] = [st[i], st[i - 1]]; clearVia(i - 2, i - 1, i); }
    if (a === 'down' && i < st.length - 1) { [st[i + 1], st[i]] = [st[i], st[i + 1]]; clearVia(i - 1, i, i + 1); }
    selected = -1; computeLine(); changed(true);
  });

  $('#num').addEventListener('input', (e) => { S.number = e.target.value.trim(); changed(); });
  $('#note').addEventListener('input', (e) => { S.note = e.target.value; changed(); });
  $('#show-list').addEventListener('change', (e) => { S.list.show = e.target.checked; changed(); });
  $('#show-legend').addEventListener('change', (e) => { S.legend.show = e.target.checked; changed(); });
  $('#neutral').addEventListener('change', (e) => { S.neutral = e.target.checked; changed(); });
  $('#line-undo').addEventListener('click', () => { S.line.pop(); changed(); });
  $('#via-clear').addEventListener('click', () => { S.stops.forEach((st) => { st.via = []; st.viaBack = []; }); computeLine(); changed(); });
  $('#return-trip').addEventListener('change', (e) => { S.returnTrip = e.target.checked; if (!S.returnTrip) S.back = []; computeLine(); changed(); });
  $('#auto').addEventListener('change', (e) => {
    if (e.target.checked && S.line.length && !confirm('Линия будет заново построена по дорогам, ручные правки линии пропадут. Продолжить?')) { e.target.checked = false; return; }
    S.auto = e.target.checked; computeLine(); syncForm(); hint(); changed();
  });
  $('#width').addEventListener('input', (e) => { S.widthScale = +e.target.value; syncForm(); changed(); });
  $('#line-clear').addEventListener('click', () => { if (confirm('Удалить всю линию маршрута?')) { S.line = []; S.arrows = []; changed(); } });

  $('#base-file').addEventListener('change', (e) => {
    const f = e.target.files[0]; if (!f) return;
    setBase(URL.createObjectURL(f), null, f.name);
    e.target.value = '';
  });

  $('#export').addEventListener('click', () => {
    draw(true);
    cv.toBlob((b) => {
      download(b, `marshrut-${S.number || 'bez-nomera'}.png`);
      draw();
    }, 'image/png');
  });
  $('#save').addEventListener('click', () => {
    download(new Blob([JSON.stringify(S, null, 1)], { type: 'application/json' }), `marshrut-${S.number || 'bez-nomera'}.json`);
  });
  $('#open').addEventListener('change', async (e) => {
    const f = e.target.files[0]; if (!f) return;
    try {
      const d = JSON.parse(await f.text());
      if (d.v !== 1 || !Array.isArray(d.stops)) throw new Error();
      S = Object.assign(blank(), d); selected = -1; syncForm(); computeLine(); changed(true);
    } catch { alert('Это не файл схемы Ridro'); }
    e.target.value = '';
  });
  $('#reset').addEventListener('click', () => {
    if (!confirm('Начать новую схему? Текущая будет стёрта (сохраните .json, если нужна).')) return;
    S = blank(); selected = -1; syncForm(); changed(true);
  });

  function download(blob, name) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob); a.download = name; a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  }

  function syncForm() {
    $('#num').value = S.number; $('#note').value = S.note;
    $('#show-list').checked = S.list.show; $('#show-legend').checked = S.legend.show; $('#neutral').checked = S.neutral;
    $('#auto').checked = S.auto; $('#return-trip').checked = S.returnTrip; $('#return-trip').disabled = !S.auto; $('#width').value = S.widthScale; $('#width-val').textContent = `×${(+S.widthScale).toFixed(2)}`;
    $('#manual-btns').hidden = S.auto; $('#via-clear').hidden = !S.auto;
  }

  // ---------- хранение ----------
  let timer;
  function persist() { snapshot(); try { localStorage.setItem(KEY, JSON.stringify(S)); } catch { /* нет хранилища */ } }
  function saveSoon() { clearTimeout(timer); timer = setTimeout(persist, 300); }

  // ---------- отмена (Ctrl+Z) и возврат (Ctrl+Y, Ctrl+Shift+Z) ----------
  const past = [], future = [];
  const shot = () => JSON.stringify({ ...S, view: undefined });
  function snapshot() {
    const j = shot();
    if (past[past.length - 1] === j) return;
    past.push(j); future.length = 0;
    if (past.length > 100) past.shift();
  }
  function restore(j) {
    S = Object.assign(blank(), JSON.parse(j), { view: S.view });   // кадр карты не откатываем
    selected = -1; syncForm(); renderStops(); computeLine(); draw();
    try { localStorage.setItem(KEY, JSON.stringify(S)); } catch { /* нет хранилища */ }
  }
  function undo() {
    clearTimeout(timer); snapshot();     // зафиксировать изменение, которое ещё не успело сохраниться
    if (past.length < 2) return;
    future.push(past.pop()); restore(past[past.length - 1]);
  }
  function redo() {
    if (!future.length) return;
    const j = future.pop(); past.push(j); restore(j);
  }
  // В поле, которое уже правили, Ctrl+Z отменяет набор текста; в нетронутом (например, имя только что
  // поставленной остановки) — действие на карте.
  let fieldEdited = false;
  document.addEventListener('focusin', () => { fieldEdited = false; });
  document.addEventListener('input', () => { fieldEdited = true; });
  document.addEventListener('keydown', (e) => {
    if (!(e.ctrlKey || e.metaKey) || (e.code !== 'KeyZ' && e.code !== 'KeyY')) return;
    if (e.target.closest?.('input, textarea, select')) { if (fieldEdited) return; e.target.blur(); }
    // e.code, а не e.key: на русской раскладке Z — это «я»
    if (e.code === 'KeyZ' && !e.shiftKey) { e.preventDefault(); undo(); }
    else if (e.code === 'KeyY' || (e.code === 'KeyZ' && e.shiftKey)) { e.preventDefault(); redo(); }
  });
  function load() { try { const d = JSON.parse(localStorage.getItem(KEY)); return d && d.v === 1 ? Object.assign(blank(), d) : null; } catch { return null; } }
  function changed(list) { if (list) renderStops(); draw(); saveSoon(); }

  function setBase(src, credit, label) {
    const img = new Image();
    img.onload = () => {
      base = img; baseCredit = credit;
      $('#base-info').textContent = `Подложка: ${label} (${img.width}×${img.height})`;
      draw();
    };
    img.onerror = () => alert('Не удалось открыть картинку подложки');
    img.src = src;
  }

  // ---------- старт ----------
  syncForm(); renderStops(); setMode('pan');
  loadRoads().then(() => { computeLine(); draw(); snapshot(); });
  Promise.all(['600 25px', '700 45px', '600 33px', '600 24px', '500 15px'].map((f) => document.fonts.load(`${f} ${FONT}`, 'Маршрут Лд'))).finally(() => {
    setBase(BASE.src, BASE.credit, 'карта MTA Province');
  });
})();
