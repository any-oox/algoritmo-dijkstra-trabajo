"use strict";
/* =====================================================================================
   SCRIPT.JS = el "cerebro" de la página (traducción del programa en Python).
   Las funciones conservan los MISMOS NOMBRES que en Python para poder compararlas.
   Python -> JavaScript:  def f(x): -> function f(x){ }   |   lista [] y dict {} -> igual
   $ = atajo para buscar un elemento del HTML por su id.
   ===================================================================================== */

// ---------- CONSTANTES (igual que en Python) ----------
const INFINITO = Infinity;                 // número "más grande que todos"
const N_MIN = 7, N_MAX = 16;               // mínimo y máximo de nodos
const PESO_MAX_DEFECTO = 30, PESO_MAX_LIMITE = 999;
const COL = { card: "#ffffff", ink: "#14213d", mut: "#5b6b7c", acc: "#0f766e", accl: "#cdeee9",
              cur: "#d98e04", curl: "#fdecc4", dist: "#1d4ed8", pred: "#7c3aed", itr: "#15803d" };
// Colores que se reparten entre las flechas (se repiten al acabarse).
const PALETA_ARISTAS = ["#2563eb", "#d97706", "#059669", "#7c3aed", "#db2777", "#0891b2", "#ca8a04", "#4f46e5", "#e11d48", "#65a30d"];
const FUENTE = "bold 12px sans-serif";     // letra de pesos y etiquetas (sube el 12 para letras más grandes)
const FUENTE_ETI = "12px sans-serif";    // letra normal para etiquetas de nodos aún pendientes

// ---------- VARIABLES GLOBALES (la "memoria" del programa) ----------
let n = 8;                                 // cantidad de nodos
let aristas = [];                          // [[desde, hasta, peso], ...]  (0 = A, 1 = B...)
let columnas = {}, nivel_max = 1;          // qué nodos van en cada columna
let nodo_sel = null, nodo_segundo_sel = null;   // nodos marcados con clic (modo manual)
let P_px = {}, etiquetas_px = {};          // posiciones en pantalla de nodos y pesos
let ultimo_peso = "1";
let zoom_grafo = 1, pan_x = 0, pan_y = 0;  // zoom y desplazamiento de la vista
let pasos = [], paso_actual = 0;           // "fotografías" de cada paso de Dijkstra
let mov_nodos = {};                        // cuánto movió el usuario cada nodo
let forma_auto = {}, clave_guardada = null;// curvatura automática de cada flecha y su "huella"
let tam_dibujo = [900, 450];
let arrastre = null;                       // arrastre de la vista con el botón DEL MEDIO (como en Python)
let forma_manual = {};                     // curvatura que el usuario dio a una flecha arrastrando su peso
let pos_peso = {}, tam_peso = {};          // punto de la curva (0-40) y tamaño/texto del recuadro de cada peso
let arrastre_peso = null, arrastre_nodo = null, arrastre_fondo = null;   // arrastres con el botón izquierdo
let editor_peso = null, editor_arista = -1;                              // cajita para editar un peso
let panel_sup_colapsado = false, panel_inf_colapsado = false;            // paneles ocultos o no

// ---------- ATAJOS ----------
const $ = id => document.getElementById(id);
const lienzo = $("lienzo"), ctx = lienzo.getContext("2d");   // ctx = el "pincel" para dibujar
const modo = () => document.querySelector('input[name="modo"]:checked').value;  // "rand" o "man"
const origen_actual = () => +$("origen").value;     // el + convierte texto a número
const destino_actual = () => +$("destino").value;
const letra = i => String.fromCharCode(65 + i);     // 0 -> A, 1 -> B...
const radio_nodo = () => (n <= 9 ? 17 : (n <= 12 ? 15 : 14));   // círculos más chicos si hay más nodos
const texto_distancia = x => (x === INFINITO ? "∞" : String(x));
const entero = (a, b) => a + Math.floor(Math.random() * (b - a + 1));  // = random.randint(a, b)
const ids = P => Object.keys(P).map(Number);        // lista de números de nodo de un diccionario

// ---------- GRAFO ----------
// Crea aristas al azar. Siempre van de un nodo menor a uno mayor => nunca hay ciclos.
function generar_aleatorio(cantidad, peso_max) {
  const lista = [];
  for (let j = 1; j < cantidad; j++) {
    const a = Math.max(0, j - 4);                   // solo mira los 4 nodos anteriores (más = más enredo)
    const k = entero(a, j - 1);                     // un "padre" obligatorio
    lista.push([k, j, entero(1, peso_max)]);
    for (let i = a; i < j; i++)
      if (i !== k && Math.random() < 0.35)          // 35% de flechas extra (sube para un grafo más denso)
        lista.push([i, j, entero(1, peso_max)]);
  }
  return lista;
}

// ¿Se puede llegar de a a b siguiendo flechas? (para prohibir ciclos)
function hay_camino(a, b) {
  const vis = [a], pila = [a];
  while (pila.length) {
    const x = pila.pop();
    if (x === b) return true;
    for (const ar of aristas)
      if (ar[0] === x && !vis.includes(ar[1])) { vis.push(ar[1]); pila.push(ar[1]); }
  }
  return false;
}

// Devuelve el motivo del rechazo, o "" si la arista es válida.
function validar_arista(u, v, w) {
  if (u === v) return "Una arista no puede unir un vértice consigo mismo.";
  if (!(w > 0)) return "El peso debe ser un número positivo.";
  if (aristas.some(a => a[0] === u && a[1] === v)) return `La arista ${letra(u)}→${letra(v)} ya existe.`;
  if (hay_camino(v, u)) return `No se añadió ${letra(u)}→${letra(v)}: formaría un ciclo y el grafo debe ser acíclico.`;
  return "";
}

// ---------- ORDEN DE NODOS EN COLUMNAS (reduce cruces de flechas) ----------
// Altura relativa (0 a 1) de cada nodo dentro de su columna.
function actualizar_rangos(cols, rango) {
  for (const l in cols) cols[l].forEach((x, k) => { rango[x] = (k + 1) / (cols[l].length + 1); });
}
// Reordena una columna según el promedio de altura de los vecinos de cada nodo.
function ordenar_columna(cols, rango, l, vecinos) {
  const pares = cols[l].map((i, k) => {
    const v = vecinos[i];
    const clave = v.length ? v.reduce((s, x) => s + rango[x], 0) / v.length : rango[i];
    return [clave, k, i];
  });
  pares.sort((x, y) => x[0] - y[0] || x[1] - y[1]);
  cols[l] = pares.map(p => p[2]);
}

// Decide en qué columna va cada nodo (todavía sin píxeles).
function calcular_posiciones() {
  columnas = {}; nivel_max = 1;
  if (n === 0) return;
  if (modo() === "man") {                           // manual: origen | intermedios | destino
    const o = origen_actual(), d = destino_actual(), inter = [];
    for (let i = 0; i < n; i++) if (i !== o && i !== d) inter.push(i);
    columnas[0] = [o]; let nv = 1;
    const tam = Math.max(1, Math.ceil(inter.length / Math.max(1, n - 3)));   // nodos por columna
    for (let i = 0; i < inter.length; i += tam) columnas[nv++] = inter.slice(i, i + tam);
    columnas[nv] = [d]; nivel_max = nv;
    return;
  }
  if (aristas.length === 0) { columnas = { 0: [...Array(n).keys()] }; return; }
  // Nivel = cantidad máxima de flechas para llegar a cada nodo.
  const nivel = Array(n).fill(0);
  for (let r = 0; r < n; r++) for (const a of aristas) if (nivel[a[0]] + 1 > nivel[a[1]]) nivel[a[1]] = nivel[a[0]] + 1;
  const M = Math.max(1, ...nivel), cols = {};
  for (let i = 0; i < n; i++) (cols[nivel[i]] = cols[nivel[i]] || []).push(i);
  const pred = [], succ = [];
  for (let i = 0; i < n; i++) { pred.push([]); succ.push([]); }
  for (const a of aristas) { pred[a[1]].push(a[0]); succ[a[0]].push(a[1]); }
  const rango = {}; actualizar_rangos(cols, rango);
  const niveles = Object.keys(cols).map(Number).sort((a, b) => a - b);
  for (let r = 0; r < 8; r++) {                     // 8 pasadas de reordenamiento (más = menos cruces)
    for (let k = 1; k < niveles.length; k++) { ordenar_columna(cols, rango, niveles[k], pred); actualizar_rangos(cols, rango); }
    for (let k = niveles.length - 2; k >= 0; k--) { ordenar_columna(cols, rango, niveles[k], succ); actualizar_rangos(cols, rango); }
  }
  columnas = cols; nivel_max = M;
}

// Convierte columnas en coordenadas (x, y) en píxeles.
function posiciones_pixel(W, H) {
  const R = radio_nodo(), izq = 52, arriba = R + 34, abajo = R + 28;   // márgenes
  const ancho = W - 5 * izq, alto = H - arriba - abajo, P = {};        // el 5: más grande = grafo más estrecho
  const ls = Object.keys(columnas).map(Number).sort((a, b) => a - b);
  if (!ls.length) {                                 // sin columnas: nodos en círculo
    for (let i = 0; i < n; i++) { const ang = 2 * Math.PI * i / n - Math.PI / 2; P[i] = [W / 2 + ancho / 2 * Math.cos(ang), arriba + alto / 2 + alto / 2 * Math.sin(ang)]; }
    return P;
  }
  let escalonar = false;                            // columnas muy llenas: nodos alternados a la derecha
  for (const l of ls) { const c = columnas[l].length; if (c > 2 && alto / c < 2 * R + 26) escalonar = true; }
  const desp = escalonar ? 0.45 : 0, paso = ancho / Math.max(1, nivel_max + desp);   // paso = distancia entre columnas
  const ys = {};
  for (const l of ls) columnas[l].forEach((i, k) => { ys[i] = (k + 0.5) / columnas[l].length; });
  const carriles = [0.5, 0.12, 0.88, 0.31, 0.69];  // alturas en zigzag para columnas de 1 solo nodo
  let cont = 0;
  for (const l of ls) { if (columnas[l].length === 1) { ys[columnas[l][0]] = carriles[cont % carriles.length]; cont++; } else cont = 0; }
  const vals = Object.values(ys), ymin = Math.min(...vals), ymax = Math.max(...vals);
  for (const l of ls) columnas[l].forEach((i, k) => {
    const fy = ymax - ymin < 1e-9 ? 0.5 : (ys[i] - ymin) / (ymax - ymin);
    let x = izq + l * paso;                         // para mover todo a la derecha: suma un número aquí
    if (escalonar && columnas[l].length > 2 && k % 2 === 1) x += desp * paso;
    P[i] = [x, arriba + fy * alto];
  });
  return P;
}

// ---------- ALGORITMO DE DIJKSTRA ----------
// Guarda una "fotografía" (copias) del estado para poder avanzar y retroceder.
function guardar_paso(d, p, vis, it, actual, rel, log, fin) {
  pasos.push({ d: [...d], p: p.map(x => [...x]), vis: [...vis], it: [...it], cur: actual, rel: [...rel], log: [...log], fin });
}

function dijkstra(s, t) {
  pasos = [];
  const d = Array(n).fill(INFINITO);                // distancias (todas ∞ al inicio)
  const p = Array.from({ length: n }, () => []);    // predecesores (lista: puede haber varios caminos iguales)
  const vis = Array(n).fill(false), it = Array(n).fill(0);
  let turno = 0; d[s] = 0;
  guardar_paso(d, p, vis, it, -1, [], [`Inicio: d(${letra(s)}) = 0 y el resto de vértices tiene distancia ∞.`], false);
  while (true) {
    let u = -1;                                     // u = no visitado con la menor distancia
    for (let i = 0; i < n; i++) if (!vis[i] && d[i] < INFINITO && (u < 0 || d[i] < d[u])) u = i;
    if (u < 0) break;
    vis[u] = true; it[u] = ++turno;
    const log = [`Se elige ${letra(u)}: es el vértice no visitado con menor distancia (${d[u]}).`], rel = [];
    aristas.forEach(([a, v, w], k) => {             // revisa las flechas que salen de u
      if (a !== u || vis[v]) return;
      rel.push(k);
      const nd = d[u] + w, base = `${letra(u)}→${letra(v)}: ${d[u]}+${w}=${nd}`;
      if (nd < d[v]) { log.push(`${base} < ${texto_distancia(d[v])}. Se actualiza d(${letra(v)})=${nd}.`); d[v] = nd; p[v] = [u]; }
      else if (nd === d[v]) { log.push(`${base}, igual a d(${letra(v)}). Se suma otro camino mínimo.`); p[v].push(u); }
      else log.push(`${base} > ${texto_distancia(d[v])}. No mejora.`);
    });
    if (log.length === 1) log.push(`${letra(u)} no tiene aristas hacia vértices pendientes.`);
    guardar_paso(d, p, vis, it, u, rel, log, false);
    if (u === t) break;                             // ya llegamos al destino
  }
  guardar_paso(d, p, vis, it, -1, [], [d[t] < INFINITO
    ? `Fin: el destino ${letra(t)} quedó fijado con distancia mínima ${d[t]}.`
    : `Fin: ${letra(t)} no es alcanzable desde ${letra(s)}.`], true);
}

// Reconstruye TODOS los caminos mínimos yendo hacia atrás por los predecesores (recursión).
function buscar_caminos(v, p, s) {
  if (v === s) return [[s]];
  const lista = [];
  for (const u of p[v]) for (const q of buscar_caminos(u, p, s)) lista.push([...q, v]);
  return lista;
}

// ---------- GEOMETRÍA: CURVAS DE BÉZIER ----------
// Punto de la curva: t=0 inicio, t=1 final, c = "imán" que curva la línea.
const bezier = (p0, c, p1, t) => { const a = (1 - t) ** 2, b = 2 * t * (1 - t), d = t * t; return [a * p0[0] + b * c[0] + d * p1[0], a * p0[1] + b * c[1] + d * p1[1]]; };
// Guarda el punto de control en coordenadas relativas (a lo largo, a un costado) para que la curva se adapte si mueves nodos.
function forma_de_control(p0, p1, c) {
  const dx = p1[0] - p0[0], dy = p1[1] - p0[1], L2 = Math.max(dx * dx + dy * dy, 1), qx = c[0] - p0[0], qy = c[1] - p0[1];
  return [(qx * dx + qy * dy) / L2, (-qx * dy + qy * dx) / L2];
}
const control_de_forma = (p0, p1, a, b) => { const dx = p1[0] - p0[0], dy = p1[1] - p0[1]; return [p0[0] + a * dx - b * dy, p0[1] + a * dy + b * dx]; };
// Distancia de un punto a un segmento (para saber si una flecha roza un nodo).
function dist_segmento(p, a, b) {
  const dx = b[0] - a[0], dy = b[1] - a[1], l2 = dx * dx + dy * dy;
  if (l2 === 0) return Math.hypot(p[0] - a[0], p[1] - a[1]);
  const t = Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / l2));
  return Math.hypot(p[0] - (a[0] + t * dx), p[1] - (a[1] + t * dy));
}
const orientacion = (p, q, r) => (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0]);
const se_cruzan = (a, b, c, d) => orientacion(a, b, c) * orientacion(a, b, d) < 0 && orientacion(c, d, a) * orientacion(c, d, b) < 0;

// ---- Rectángulos ("cajas") y nombres de aristas ----
const caja = pts => { const xs = pts.map(p => p[0]), ys = pts.map(p => p[1]); return [Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)]; };
const cajas_solapan = (a, b) => !(a[2] < b[0] || b[2] < a[0] || a[3] < b[1] || b[3] < a[1]);   // ¿se superponen dos rectángulos?
const punto_en_caja = (x, y, r) => r[0] <= x && x <= r[2] && r[1] <= y && y <= r[3];
const nombre_arista = (u, v) => u + "-" + v;       // clave tipo "0-3" para recordar la curvatura manual

// FUNCIÓN MÁS COMPLEJA: hace que las flechas se curven solas. Para cada flecha PRUEBA varias curvaturas
// y le pone "multas" por cada problema; gana la de menor multa. Luego busca dónde poner el recuadro del peso.
// Devuelve [curvas, etiquetas].
function calcular_rutas(P, W, H) {
  const R = radio_nodo(), NS = 14, n_ar = aristas.length;   // NS = tramos para analizar cada curva
  const largos = aristas.map((a, k) => [Math.hypot(P[a[0]][0] - P[a[1]][0], P[a[0]][1] - P[a[1]][1]), k]);
  largos.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  const orden = largos.map(p => p[1]);              // primero las flechas cortas
  const ctrls = {}, burdas = {}, cajas = {};
  // reservas: zona sobre cada nodo donde irá su etiqueta [distancia, predecesor]
  const reservas = ids(P).map(j => [P[j][0] - 44, P[j][1] - R - 21, P[j][0] + 44, P[j][1] - R - 3]);

  for (const k of orden) {
    const [u, v] = aristas[k], p0 = P[u], p1 = P[v];
    const mx = (p0[0] + p1[0]) / 2, my = (p0[1] + p1[1]) / 2, dx = p1[0] - p0[0], dy = p1[1] - p0[1];
    const ln = Math.max(Math.hypot(dx, dy), 1), nx = -dy / ln, ny = dx / ln;   // (nx, ny) = dirección perpendicular
    let mejor = null;
    const separacion = n_ar < 20 ? 36 : 46;                  // salto entre curvaturas candidatas
    const max_curva = Math.min(360, 100 + n_ar * 10);        // cuánto puede alejarse de la recta
    const candidatos = [0];
    for (let nc = 1; nc <= Math.floor(max_curva / separacion); nc++) candidatos.push(nc * separacion, -nc * separacion);

    for (const off of candidatos) {
      const ctrl = [mx + nx * 2 * off, my + ny * 2 * off], pts = [];
      for (let i = 0; i <= NS; i++) pts.push(bezier(p0, ctrl, p1, i / NS));
      let pen = Math.abs(off) * 0.3;                         // MULTA 1: curvarse mucho
      if (off === 0 && n_ar > 3) pen += 300;                 // MULTA 2: ir recta (si hay más de 3 flechas)
      for (const j of ids(P)) {                              // MULTA 3: pasar cerca de otro nodo
        if (j === u || j === v) continue;
        let dmin = 999999;
        for (let i = 0; i < NS; i++) dmin = Math.min(dmin, dist_segmento(P[j], pts[i], pts[i + 1]));
        if (dmin < R + 12) pen += 900 + (R + 12 - dmin) * 35;
      }
      for (const q of pts) if (reservas.some(r => punto_en_caja(q[0], q[1], r))) pen += 50;   // MULTA 4: zonas reservadas
      if (pts.some(q => q[0] < 6 || q[1] < 6 || q[0] > W - 6 || q[1] > H - 6)) pen += 500;    // MULTA 5: salirse del lienzo
      const bb = caja(pts);
      for (const m in burdas) {                              // MULTA 6: llevarse mal con flechas ya colocadas
        const [u2, v2] = aristas[m], pts2 = burdas[m];
        if (u === u2 || v === v2) {                          // mismo nodo de salida/llegada: abrirse en abanico
          const dist_medio = Math.hypot(pts[7][0] - pts2[7][0], pts[7][1] - pts2[7][1]);   // pts[7] = punto medio (la mitad de 14)
          if (dist_medio < 38) pen += 3000 / Math.max(dist_medio, 1);
        }
        if (u === u2 || u === v2 || v === u2 || v === v2) continue;   // comparten nodo: es normal que se toquen
        if (!cajas_solapan(bb, cajas[m])) continue;                   // cajas lejanas: no hace falta comparar
        for (let i = 0; i < NS; i++) for (let j = 0; j < NS; j++) {
          if (Math.hypot(pts[i][0] - pts2[j][0], pts[i][1] - pts2[j][1]) < 18) pen += 250;   // casi pegadas
          if (se_cruzan(pts[i], pts[i + 1], pts2[j], pts2[j + 1])) pen += 60;                // se cruzan
        }
      }
      if (!mejor || pen < mejor[0]) mejor = [pen, ctrl, pts];
    }
    ctrls[k] = mejor[1]; burdas[k] = mejor[2]; cajas[k] = caja(mejor[2]);
  }

  // Curvas finales con 41 puntos (de t=0 a t=1 en saltos de 1/40).
  const resultado_curvas = {};
  aristas.forEach(([u, v], k) => { resultado_curvas[k] = Array.from({ length: 41 }, (_, i) => bezier(P[u], ctrls[k], P[v], i / 40)); });

  // Recuadro del peso de cada flecha: se prueban 9 posiciones a lo largo de la curva.
  ctx.font = FUENTE;
  const resultado_etiquetas = {}, rects = [];
  for (const k of orden) {
    const texto = String(aristas[k][2]), ew = ctx.measureText(texto).width + 12, eh = 18;   // tamaño del recuadro
    let mejor = null;
    for (const t of [0.5, 0.4, 0.6, 0.32, 0.68, 0.25, 0.75, 0.2, 0.8]) {
      const idx = Math.round(t * 40), cx = resultado_curvas[k][idx][0], cy = resultado_curvas[k][idx][1];
      const r = [cx - ew / 2, cy - eh / 2, cx + ew / 2, cy + eh / 2];
      let pen = Math.abs(t - 0.5) * 20;                      // se prefiere el centro
      for (const j of ids(P)) {                              // +1200 si tapa un nodo
        const qx = Math.min(Math.max(P[j][0], r[0]), r[2]), qy = Math.min(Math.max(P[j][1], r[1]), r[3]);
        if (Math.hypot(P[j][0] - qx, P[j][1] - qy) < R + 4) pen += 1200;
      }
      for (const r2 of rects.concat(reservas))               // +1200 si se encima con otro peso o una etiqueta
        if (!(r[2] + 3 < r2[0] || r2[2] + 3 < r[0] || r[3] + 3 < r2[1] || r2[3] + 3 < r[1])) pen += 1200;
      for (const m in resultado_curvas) {                    // +100 si tapa otra flecha
        if (+m === k) continue;
        const lista = resultado_curvas[m];
        for (let q = 0; q < lista.length; q += 2) if (punto_en_caja(lista[q][0], lista[q][1], r)) { pen += 100; break; }
      }
      if (!mejor || pen < mejor[0]) mejor = [pen, r, cx, cy, texto];
    }
    rects.push(mejor[1]);
    resultado_etiquetas[k] = [mejor[2], mejor[3], mejor[1], mejor[4]];
  }
  return [resultado_curvas, resultado_etiquetas];
}

// Guarda el resultado de calcular_rutas en forma "relativa" (forma_auto) y la posición/tamaño de cada peso.
function guardar_formas_automaticas(P, W, H) {
  const [curvas, etiquetas] = calcular_rutas(P, W, H);
  forma_auto = {}; pos_peso = {}; tam_peso = {};
  for (const k in curvas) {
    const [u, v] = aristas[k], p0 = P[u], p1 = P[v], medio = curvas[k][20];
    // Se "deduce" el punto de control a partir del punto medio de la curva (fórmula de Bézier despejada).
    forma_auto[k] = forma_de_control(p0, p1, [2 * medio[0] - 0.5 * (p0[0] + p1[0]), 2 * medio[1] - 0.5 * (p0[1] + p1[1])]);
    const [ex, ey, rect] = etiquetas[k];
    let mejor_i = 20, mejor_d = 1e18;                        // punto de la curva más cercano al recuadro
    for (let idx = 0; idx < 41; idx++) {
      const dd = (curvas[k][idx][0] - ex) ** 2 + (curvas[k][idx][1] - ey) ** 2;
      if (dd < mejor_d) { mejor_d = dd; mejor_i = idx; }
    }
    pos_peso[k] = mejor_i;
    tam_peso[k] = [(rect[2] - rect[0]) / 2, (rect[3] - rect[1]) / 2, etiquetas[k][3]];   // [mitad ancho, mitad alto, texto]
  }
}

// ---------- ZOOM / DESPLAZAMIENTO (mundo del grafo <-> pantalla) ----------
const x_pantalla = (x, W) => W / 2 + (x - W / 2) * zoom_grafo + pan_x;
const y_pantalla = (y, H) => H / 2 + (y - H / 2) * zoom_grafo + pan_y;
const x_grafo = (x, W) => (x - pan_x - W / 2) / zoom_grafo + W / 2;
const y_grafo = (y, H) => (y - pan_y - H / 2) / zoom_grafo + H / 2;

// Posición automática + lo que el usuario movió a mano.
function posiciones_actuales(W, H) {
  const base = posiciones_pixel(W, H), P = {};
  for (const i of ids(base)) { const m = mov_nodos[i] || [0, 0]; P[i] = [base[i][0] + m[0], base[i][1] + m[1]]; }
  return P;
}
// Recalcula las curvas solo si cambió el tamaño o las aristas (es una operación lenta).
function asegurar_formas(P_base, W, H) {
  const clave = W + "|" + H + "|" + JSON.stringify(aristas);
  if (clave !== clave_guardada) { guardar_formas_automaticas(P_base, W, H); clave_guardada = clave; }
}

// ---------- DIBUJO ----------
// Texto de varios colores dentro de un recuadro, ej: [distancia, predecesor](turno).
function texto_color(x, y, segs, fondo, borde, centrado = true, fuente = FUENTE) {
  ctx.font = fuente; ctx.textAlign = "left"; ctx.textBaseline = "middle";
  const anchos = segs.map(s => ctx.measureText(s[0]).width), total = anchos.reduce((a, b) => a + b, 0);
  let x0 = centrado ? x - total / 2 : x;
  ctx.fillStyle = fondo; ctx.strokeStyle = borde; ctx.lineWidth = 1;
  ctx.fillRect(x0 - 3, y - 9, total + 6, 18); ctx.strokeRect(x0 - 3, y - 9, total + 6, 18);
  segs.forEach((s, k) => { ctx.fillStyle = s[1]; ctx.fillText(s[0], x0, y); x0 += anchos[k]; });
}
function circulo(x, y, r, relleno, borde, grosor, dash = []) {
  ctx.beginPath(); ctx.arc(x, y, r, 0, 2 * Math.PI);
  if (relleno) { ctx.fillStyle = relleno; ctx.fill(); }
  ctx.setLineDash(dash); ctx.strokeStyle = borde; ctx.lineWidth = grosor; ctx.stroke(); ctx.setLineDash([]);
}

// Pinta TODO desde cero: flechas -> nodos -> etiquetas -> pesos (lo último queda encima).
function dibujar() {
  lienzo.width = lienzo.clientWidth; lienzo.height = lienzo.clientHeight;   // también borra el lienzo
  if (n === 0) return;
  const W = Math.max(lienzo.width, 900), H = Math.max(lienzo.height, 450);  // tamaño mínimo virtual
  tam_dibujo = [W, H];
  const P_base = posiciones_actuales(W, H), P = {};
  for (const i of ids(P_base)) P[i] = [x_pantalla(P_base[i][0], W), y_pantalla(P_base[i][1], H)];
  P_px = P;
  const st = pasos.length ? pasos[paso_actual] : null, R = radio_nodo(), s = origen_actual(), t = destino_actual();
  const en_camino = [];                              // flechas del camino mínimo (solo en el paso final)
  if (st && st.fin && st.d[t] < INFINITO)
    for (const q of buscar_caminos(t, st.p, s)) for (let i = 0; i < q.length - 1; i++) en_camino.push(q[i] + "-" + q[i + 1]);
  asegurar_formas(P_base, W, H);

  // Curva y estilo [color, grosor, fondo del peso, prioridad] de cada flecha.
  const curvas = {}, etiquetas = {}, estilo = {};
  aristas.forEach(([u, v, w], k) => {
    const nombre = nombre_arista(u, v);
    let a, b, punto_peso;
    if (nombre in forma_manual) { [a, b] = forma_manual[nombre]; punto_peso = 20; }   // curvatura dada por el usuario
    else { [a, b] = forma_auto[k]; punto_peso = pos_peso[k]; }                         // curvatura automática
    const ctrl = control_de_forma(P_base[u], P_base[v], a, b);
    curvas[k] = Array.from({ length: 41 }, (_, i) => { const q = bezier(P_base[u], ctrl, P_base[v], i / 40); return [x_pantalla(q[0], W), y_pantalla(q[1], H)]; });
    const [mw, mh] = tam_peso[k], cx = curvas[k][punto_peso][0], cy = curvas[k][punto_peso][1];
    etiquetas[k] = [cx, cy, [cx - mw, cy - mh, cx + mw, cy + mh], tam_peso[k][2]];   // [centro x, centro y, rectángulo, texto]
    estilo[k] = en_camino.includes(u + "-" + v) ? [COL.acc, 4, COL.accl, 2]            // camino final: verde y grueso
              : (st && st.rel.includes(k)) ? ["#000000", 3, "#e5e7eb", 1]              // revisada en este paso: negra
              : [PALETA_ARISTAS[k % PALETA_ARISTAS.length], 2, COL.card, 0];           // normal
  });
  etiquetas_px = etiquetas;

  // Flechas, en 3 tandas para que las resaltadas queden encima.
  for (const prio of [0, 1, 2]) aristas.forEach(([u, v], k) => {
    if (estilo[k][3] !== prio) return;
    const pts = [...curvas[k]];
    while (pts.length > 2 && Math.hypot(pts[0][0] - P[u][0], pts[0][1] - P[u][1]) < R) pts.shift();               // recorta dentro del nodo origen
    while (pts.length > 2 && Math.hypot(pts[pts.length - 1][0] - P[v][0], pts[pts.length - 1][1] - P[v][1]) < R + 3) pts.pop();
    ctx.strokeStyle = ctx.fillStyle = estilo[k][0]; ctx.lineWidth = estilo[k][1]; ctx.lineCap = ctx.lineJoin = "round";
    ctx.beginPath(); pts.forEach((q, i) => (i ? ctx.lineTo(q[0], q[1]) : ctx.moveTo(q[0], q[1]))); ctx.stroke();
    const f = pts[pts.length - 1], g = pts[Math.max(0, pts.length - 4)], ang = Math.atan2(f[1] - g[1], f[0] - g[0]);
    ctx.beginPath(); ctx.moveTo(f[0], f[1]);        // punta de flecha (12 = tamaño; 0.4 = apertura)
    ctx.lineTo(f[0] - 12 * Math.cos(ang - 0.4), f[1] - 12 * Math.sin(ang - 0.4));
    ctx.lineTo(f[0] - 12 * Math.cos(ang + 0.4), f[1] - 12 * Math.sin(ang + 0.4));
    ctx.closePath(); ctx.fill();
  });

  // Nodos.
  for (const i of ids(P)) {
    const [x, y] = P[i], sel = modo() === "man" && (nodo_sel === i || nodo_segundo_sel === i);
    if (sel) circulo(x, y, R + 9, null, COL.cur, 3.5, [3, 2]);          // aro naranja punteado: seleccionado
    if (i === s) circulo(x, y, R + 5, null, COL.acc, 2);                // aro verde: origen
    if (i === t) circulo(x, y, R + 5, null, COL.ink, 1.5, [4, 3]);      // aro oscuro punteado: destino
    const actual = st && st.cur === i;
    circulo(x, y, R, (sel || actual) ? COL.curl : (st && st.vis[i] ? COL.accl : COL.card),
            (sel || actual) ? COL.cur : COL.ink, (sel || actual) ? 3 : 1.5);
    ctx.fillStyle = COL.ink; ctx.font = "bold 14px sans-serif"; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.fillText(letra(i), x, y);
  }

  // Etiquetas [distancia, predecesor](turno) encima de cada nodo.
  if (st) {
    for (const i of ids(P)) {
      const pr = st.p[i].map(letra).join("/") || "–";
      const segs = [["[", COL.mut], [texto_distancia(st.d[i]), COL.dist], [", ", COL.mut], [pr, COL.pred], ["]", COL.mut]];
      if (st.it[i]) segs.push(["(", COL.mut], [String(st.it[i]), COL.itr], [")", COL.mut]);
      const fondo = st.cur === i ? COL.curl : (st.vis[i] ? COL.accl : COL.card);
      const borde = st.cur === i ? COL.cur : (st.vis[i] ? COL.acc : "#cfd8df");
      texto_color(P[i][0], P[i][1] - R - 12, segs, fondo, borde, true, (st.cur === i || st.vis[i]) ? FUENTE : FUENTE_ETI);        // R + 12 = altura sobre el nodo
    }
    texto_color(8, lienzo.height - 14, [["Etiqueta: [", COL.mut], ["distancia", COL.dist], [", ", COL.mut], ["predecesor", COL.pred], ["](", COL.mut], ["iteración", COL.itr], [")", COL.mut]], COL.card, COL.card, false);
  }

  // Pesos (recuadros con el número de cada flecha).
  ctx.font = FUENTE;
  for (const prio of [0, 1, 2]) aristas.forEach((_, k) => {
    if (estilo[k][3] !== prio) return;
    const [cx, cy, r, texto] = etiquetas[k];
    ctx.fillStyle = estilo[k][2]; ctx.strokeStyle = estilo[k][0]; ctx.lineWidth = 1.5;
    ctx.fillRect(r[0], r[1], r[2] - r[0], r[3] - r[1]); ctx.strokeRect(r[0], r[1], r[2] - r[0], r[3] - r[1]);
    ctx.fillStyle = estilo[k][3] === 0 ? estilo[k][0] : COL.ink; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.fillText(texto, cx, cy);
  });
}

// Actualiza tabla, registro y resultado para el paso actual y redibuja.
function mostrar_paso() {
  const st = pasos[paso_actual], s = origen_actual(), t = destino_actual();
  $("etiqueta_paso").textContent = `Paso ${paso_actual + 1} de ${pasos.length}`;
  let filas = "";
  for (let v = 0; v < n; v++) {
    const cls = st.cur === v ? "cur" : (st.vis[v] ? "vis" : ""), estado = st.cur === v ? "actual" : (st.vis[v] ? "visitado" : "pendiente");
    filas += `<tr class="${cls}"><td>${letra(v)}</td><td>${texto_distancia(st.d[v])}</td><td>${st.p[v].map(letra).join(", ") || "–"}</td><td>${estado}</td></tr>`;
  }
  $("tabla").innerHTML = filas;
  const fila_actual = $("tabla").querySelector("tr.cur"); if (fila_actual) fila_actual.scrollIntoView({ block: "nearest" });   // = tabla.see(): desplaza hasta el nodo actual
  $("log").innerHTML = st.log.map(l => "• " + l).join("<br>");
  let res = "";
  if (st.fin) {
    if (st.d[t] < INFINITO) {
      const lista = buscar_caminos(t, st.p, s);
      res = `<b>Distancia mínima ${letra(s)}→${letra(t)}: ${st.d[t]}</b><br>Caminos mínimos: ${lista.length}<br>` + lista.map(q => q.map(letra).join(" → ")).join("<br>");
    } else res = `<b>No existe camino de ${letra(s)} a ${letra(t)}.</b>`;
  }
  $("res").innerHTML = res;
  dibujar();
}

// ---------- CONTROLES Y MENSAJES ----------
function estado_controles(activar) { document.querySelectorAll(".nav").forEach(b => { b.disabled = !activar; }); }
function mensaje(texto = "", info = false) { $("msg").textContent = texto; $("msg").className = info ? "info" : ""; }

function leer_peso_maximo() {
  const t = $("var_peso_max").value.trim();
  if (t === "") return PESO_MAX_DEFECTO;
  const v = parseInt(t, 10);
  if (!/^\d+$/.test(t) || v < 1 || v > PESO_MAX_LIMITE) {
    $("var_peso_max").value = "";
    mensaje(`El peso máximo debe ser un entero entre 1 y ${PESO_MAX_LIMITE}. Se usó ${PESO_MAX_DEFECTO}.`);
    return PESO_MAX_DEFECTO;
  }
  return v;
}

// Botón "Generar grafo": lee la cantidad de nodos, valida y crea el grafo.
function generar() {
  mov_nodos = {}; forma_manual = {};
  let cantidad = parseInt($("var_n").value, 10);
  if (!(cantidad >= N_MIN && cantidad <= N_MAX)) {
    cantidad = 8; $("var_n").value = 8;
    mensaje(`El numero de nodos debe ser un entero entre ${N_MIN} y ${N_MAX}.`);
  } else mensaje();
  n = cantidad;
  aristas = modo() === "rand" ? generar_aleatorio(n, leer_peso_maximo()) : [];
  const o0 = $("origen").value === "" ? 0 : +$("origen").value, d0 = $("destino").value === "" ? 7 : +$("destino").value;
  const opciones = Array.from({ length: n }, (_, i) => `<option value="${i}">${letra(i)}</option>`).join("");
  $("origen").innerHTML = opciones; $("destino").innerHTML = opciones;
  $("origen").value = Math.min(o0, n - 1); $("destino").value = Math.min(d0, n - 1);
  reiniciar_ejecucion();
}

// Limpia pasos, tabla y resultado. rearmar=true recalcula columnas y ajusta la vista.
function reiniciar_ejecucion(rearmar = true) {
  nodo_sel = nodo_segundo_sel = null; pasos = []; paso_actual = 0; estado_controles(false);
  $("etiqueta_paso").textContent = ""; $("tabla").innerHTML = ""; $("log").textContent = ""; $("res").textContent = "";
  $("etiqueta_aristas").textContent = "Aristas: " + (aristas.length ? aristas.map(a => `${letra(a[0])}→${letra(a[1])} (${a[2]})`).join(", ") : "ninguna. Añade aristas para empezar.");
  if (rearmar) { calcular_posiciones(); clave_guardada = null; ajustar_a_ventana(); } else dibujar();
}

// Elige "Aleatorio" o "Manual": muestra u oculta las herramientas de cada modo.
function cambiar_modo() {
  const man = modo() === "man";
  $("panel_manual").hidden = !man; $("marco_peso_max").hidden = man;
  lienzo.style.cursor = man ? "pointer" : "grab";
  generar();
}

function ejecutar() {
  const s = origen_actual(), t = destino_actual();
  if (s === t) return mensaje("El origen y el destino deben ser distintos.");
  if (!aristas.length) return mensaje("Primero construye el grafo.");
  mensaje(); dijkstra(s, t); paso_actual = 0; estado_controles(true); mostrar_paso();
}
function ir_a_paso(nuevo) {
  if (!pasos.length) return;
  paso_actual = Math.max(0, Math.min(pasos.length - 1, nuevo)); mostrar_paso();
}

// ---------- ARISTAS ESCRITAS A MANO ----------
// Entiende "A B 5", "AB5", "A->B:5", "a,b,2.5"... (misma expresión regular que en Python)
const PATRON_ARISTA = /([A-Za-z])\s*(?:->|→|=>|>|-|,|:)?\s*([A-Za-z])\s*[:=,]?\s*(\d+(?:\.\d+)?)/g;
function leer_aristas(texto) {
  const nuevas = [], errores = [];
  for (const m of texto.matchAll(PATRON_ARISTA)) {
    const u = m[1].toUpperCase().charCodeAt(0) - 65, v = m[2].toUpperCase().charCodeAt(0) - 65;   // letra -> número
    if (u >= n || v >= n) { errores.push(`El vértice ${(u >= n ? m[1] : m[2]).toUpperCase()} no existe (los vértices son ${letra(0)}–${letra(n - 1)}).`); continue; }
    nuevas.push([u, v, parseFloat(m[3])]);
  }
  const resto = texto.replace(PATRON_ARISTA, " ").replace(/[\s,;]+/g, " ").trim();   // lo que no se entendió
  if (resto) errores.push(`No se entendió: "${resto}".`);
  return [nuevas, errores];
}
function anadir() {
  const texto = $("entrada").value.trim();
  if (!texto) return mensaje("Escribe una arista, por ejemplo:  A B 5   (o  AB5).", true);
  const [nuevas, errores] = leer_aristas(texto);
  let agregadas = 0;
  for (const a of nuevas) {
    const e = validar_arista(a[0], a[1], a[2]);
    if (e) errores.push(e); else { aristas.push(a); ultimo_peso = String(a[2]); agregadas++; }
  }
  if (agregadas) { reiniciar_ejecucion(); $("entrada").value = ""; }
  if (errores.length) mensaje(errores.slice(0, 2).join("  ") + (errores.length > 2 ? `  (+${errores.length - 2} más)` : ""));
  else if (agregadas) mensaje(`${agregadas} arista(s) añadida(s).`, true);
  $("entrada").focus();
}
function quitar() {
  if (aristas.length) { const u = aristas.pop(); delete forma_manual[nombre_arista(u[0], u[1])]; reiniciar_ejecucion(); mensaje(); }
}
function limpiar() { aristas = []; forma_manual = {}; reiniciar_ejecucion(); mensaje(); }

// ---------- RATÓN / DEDO ----------
const pos = e => { const r = lienzo.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
const nodo_en = (x, y) => ids(P_px).find(i => Math.hypot(x - P_px[i][0], y - P_px[i][1]) <= radio_nodo() + 5);   // +5 = tolerancia del clic
// ¿Qué recuadro de peso está bajo (x, y)? Se revisa al revés para elegir el que está encima.
function etiqueta_en(x, y) {
  for (const k of Object.keys(etiquetas_px).map(Number).reverse()) {
    const r = etiquetas_px[k][2];
    if (x >= r[0] - 2 && x <= r[2] + 2 && y >= r[1] - 2 && y <= r[3] + 2) return k;
  }
  return null;
}

// Clic sobre un nodo en modo manual: 1.º = salida, 2.º = llegada (autocompleta la caja).
function al_click(x, y) {
  if (modo() !== "man") return;
  const e = nodo_en(x, y);
  if (e === undefined) { nodo_sel = nodo_segundo_sel = null; mensaje(); }
  else if (nodo_sel === null) { nodo_sel = e; nodo_segundo_sel = null; mensaje(`Salida: ${letra(e)} seleccionado. Haz clic en el vértice de llegada.`, true); }
  else if (nodo_sel === e) { nodo_sel = nodo_segundo_sel = null; mensaje("Selección cancelada.", true); }
  else {
    nodo_segundo_sel = e; const prefijo = `${letra(nodo_sel)} ${letra(e)} `;
    $("entrada").value = prefijo + ultimo_peso; $("entrada").focus(); $("entrada").setSelectionRange(prefijo.length, $("entrada").value.length);
    mensaje(`Arista ${letra(nodo_sel)}${letra(e)} preparada. Escribe el peso y pulsa Enter.`, true);
  }
  dibujar();
}

// Presionar el botón izquierdo: decide QUÉ se va a arrastrar: 1) un peso, 2) un nodo, 3) el fondo (toda la vista).
//   arrastre_peso  = [flecha, desfase x, desfase y]
//   arrastre_nodo  = [nodo, desfase x, desfase y, x inicial, y inicial, ¿ya se movió?]
//   arrastre_fondo = [x inicial, y inicial, pan_x inicial, pan_y inicial, ¿ya se movió?]
function al_presionar(e) {
  const [x, y] = pos(e);
  cerrar_editor_peso(); arrastre_fondo = null;
  const k = etiqueta_en(x, y);
  if (k !== null && k < aristas.length) { arrastre_peso = [k, x - etiquetas_px[k][0], y - etiquetas_px[k][1]]; lienzo.style.cursor = "move"; return; }
  arrastre_peso = null;
  const i = nodo_en(x, y);
  if (i !== undefined) { arrastre_nodo = [i, x - P_px[i][0], y - P_px[i][1], x, y, false]; return; }
  arrastre_nodo = null;
  arrastre_fondo = [x, y, pan_x, pan_y, false];
}

// Mover con el botón presionado.
function al_arrastrar(e) {
  const [x, y] = pos(e);
  if (arrastre_fondo !== null) {                     // caso 1: mover toda la vista
    if (!arrastre_fondo[4] && Math.hypot(x - arrastre_fondo[0], y - arrastre_fondo[1]) < 4) return;   // umbral de 4 px: menos = simple clic
    arrastre_fondo[4] = true; lienzo.style.cursor = "move";
    pan_x = arrastre_fondo[2] + x - arrastre_fondo[0]; pan_y = arrastre_fondo[3] + y - arrastre_fondo[1];
    dibujar(); return;
  }
  if (arrastre_nodo !== null) {                      // caso 2: mover un nodo (se guarda cuánto se alejó de su posición automática)
    if (!arrastre_nodo[5] && Math.hypot(x - arrastre_nodo[3], y - arrastre_nodo[4]) < 4) return;
    arrastre_nodo[5] = true; lienzo.style.cursor = "move";
    const [W, H] = tam_dibujo, auto = posiciones_pixel(W, H)[arrastre_nodo[0]];
    mov_nodos[arrastre_nodo[0]] = [x_grafo(x - arrastre_nodo[1], W) - auto[0], y_grafo(y - arrastre_nodo[2], H) - auto[1]];
    dibujar(); return;
  }
  if (arrastre_peso === null) return;                // caso 3: arrastrar un peso = cambiar la curvatura de esa flecha
  const k = arrastre_peso[0]; if (k >= aristas.length) return;
  const [W, H] = tam_dibujo, P_base = posiciones_actuales(W, H), [u, v] = aristas[k], p0 = P_base[u], p1 = P_base[v];
  const mx = x_grafo(x - arrastre_peso[1], W), my = y_grafo(y - arrastre_peso[2], H);
  let [a, b] = forma_de_control(p0, p1, [2 * mx - 0.5 * (p0[0] + p1[0]), 2 * my - 0.5 * (p0[1] + p1[1])]);
  b = Math.max(-3.0, Math.min(3.0, b));              // LÍMITES de la curvatura: b de -3 a 3
  a = Math.max(-1.5, Math.min(2.5, a));              //                          a de -1.5 a 2.5
  forma_manual[nombre_arista(u, v)] = [a, b];
  dibujar();
}

// Soltar el botón. Si no se movió nada, era un clic normal (selecciona nodos en modo manual).
function al_soltar(e) {
  if (arrastre_fondo !== null) { const movido = arrastre_fondo[4]; arrastre_fondo = null; lienzo.style.cursor = modo() === "man" ? "pointer" : "grab"; if (!movido) al_click(...pos(e)); return; }
  if (arrastre_nodo !== null) { const movido = arrastre_nodo[5]; arrastre_nodo = null; lienzo.style.cursor = modo() === "man" ? "pointer" : "grab"; if (!movido) al_click(...pos(e)); return; }
  if (arrastre_peso !== null) { arrastre_peso = null; lienzo.style.cursor = modo() === "man" ? "pointer" : "grab"; }
}

// ---- EDITOR DE PESOS (doble clic sobre un número): cajita de texto encima del recuadro ----
function cerrar_editor_peso() { if (editor_peso !== null) { const viejo = editor_peso; editor_peso = null; viejo.remove(); } }
function abrir_editor_peso(k) {
  cerrar_editor_peso();
  const [x, y] = etiquetas_px[k]; editor_arista = k;
  const inp = document.createElement("input");
  inp.type = "text"; inp.className = "editor_peso"; inp.value = aristas[k][2];
  inp.style.left = (x - 28) + "px"; inp.style.top = (y - 12) + "px"; inp.style.width = "56px";   // 56 de ancho / 2 = 28 para centrarla
  $("marco_lienzo").appendChild(inp); editor_peso = inp; inp.focus(); inp.select();
  inp.addEventListener("keydown", ev => { if (ev.key === "Enter") aceptar_editor_peso(); if (ev.key === "Escape") cerrar_editor_peso(); });
  inp.addEventListener("blur", cerrar_editor_peso);   // clic fuera = cancelar
}
// Valida y guarda el nuevo peso (solo números positivos como 5 o 2.5).
function aceptar_editor_peso() {
  if (editor_peso === null) return;
  const k = editor_arista, texto = editor_peso.value.trim();
  if (!/^\d+(\.\d+)?$/.test(texto)) return mensaje("El peso debe ser un número positivo (por ejemplo 5 o 2.5).");
  const nuevo = parseFloat(texto);
  if (nuevo <= 0) return mensaje("El peso debe ser un número positivo.");
  aristas[k][2] = nuevo;
  if (k in tam_peso) { ctx.font = FUENTE; tam_peso[k][0] = (ctx.measureText(String(nuevo)).width + 12) / 2; tam_peso[k][2] = String(nuevo); }   // ajusta el ancho del recuadro
  cerrar_editor_peso(); reiniciar_ejecucion(false);
  mensaje(`Peso de la arista ${letra(aristas[k][0])}${letra(aristas[k][1])} cambiado a ${nuevo}.`, true);
}

// ---- Eventos del lienzo (pointer = ratón o dedo) ----
lienzo.addEventListener("pointerdown", e => {
  if (e.button === 1) { e.preventDefault(); arrastre = [...pos(e), pan_x, pan_y]; lienzo.setPointerCapture(e.pointerId); return; }   // botón del medio: mover la vista
  if (e.button !== 0) return;
  lienzo.setPointerCapture(e.pointerId); al_presionar(e);
});
lienzo.addEventListener("pointermove", e => {
  if (arrastre !== null) { const [x, y] = pos(e); pan_x = arrastre[2] + x - arrastre[0]; pan_y = arrastre[3] + y - arrastre[1]; dibujar(); return; }
  al_arrastrar(e);
});
lienzo.addEventListener("pointerup", e => { if (e.button === 1) { arrastre = null; return; } al_soltar(e); });
lienzo.addEventListener("dblclick", e => { const k = etiqueta_en(...pos(e)); if (k !== null && k < aristas.length) abrir_editor_peso(k); });
// Rueda: zoom hacia el punto donde está el cursor. 1.12 = cuánto por giro; 0.2 y 4 = zoom mínimo y máximo.
lienzo.addEventListener("wheel", e => {
  e.preventDefault();
  const [x, y] = pos(e), nuevo = Math.max(0.2, Math.min(4, zoom_grafo * (e.deltaY < 0 ? 1.12 : 1 / 1.12)));
  if (nuevo === zoom_grafo) return;
  const cx = tam_dibujo[0] / 2, cy = tam_dibujo[1] / 2;
  pan_x = x - cx - (x - cx - pan_x) * (nuevo / zoom_grafo); pan_y = y - cy - (y - cy - pan_y) * (nuevo / zoom_grafo);
  zoom_grafo = nuevo; dibujar();
}, { passive: false });

// ---- Paneles que se ocultan ----
function alternar_panel_superior() {
  panel_sup_colapsado = !panel_sup_colapsado;
  $("contenido_sup").hidden = panel_sup_colapsado;
  $("btn_colapsar_sup").textContent = panel_sup_colapsado ? "▼ Mostrar herramientas" : "▲ Ocultar herramientas";
  ajustar_a_ventana();
}
function alternar_panel_inferior() {
  panel_inf_colapsado = !panel_inf_colapsado;
  $("cuerpo").hidden = panel_inf_colapsado;
  $("btn_colapsar_inf").textContent = panel_inf_colapsado ? "▲ Mostrar detalle de ejecución" : "▼ Ocultar detalle de ejecución";
  ajustar_a_ventana();
}

function cambiar_zoom(f) { zoom_grafo = Math.max(0.2, Math.min(4, zoom_grafo * f)); dibujar(); }

// "Ajustar a ventana": calcula zoom y desplazamiento para que TODO el grafo quepa y quede centrado.
function ajustar_a_ventana() {
  if (!Object.keys(columnas).length) return;
  const W = Math.max(lienzo.clientWidth, 900), H = Math.max(lienzo.clientHeight, 450);
  const Pb = posiciones_actuales(W, H); asegurar_formas(Pb, W, H);
  const pts = ids(Pb).map(i => Pb[i]);
  aristas.forEach(([u, v], k) => {
    const m = forma_manual[nombre_arista(u, v)] || forma_auto[k], c = control_de_forma(Pb[u], Pb[v], m[0], m[1]);
    for (let i = 0; i <= 40; i += 4) pts.push(bezier(Pb[u], c, Pb[v], i / 40));
  });
  const xs = pts.map(q => q[0]), ys = pts.map(q => q[1]);
  const minx = Math.min(...xs), maxx = Math.max(...xs), miny = Math.min(...ys), maxy = Math.max(...ys);
  const R = radio_nodo(), mi = Math.max(R + 14, 40), ma = R + 34, mb = R + 18;   // márgenes libres alrededor
  const vw = lienzo.clientWidth || W, vh = lienzo.clientHeight || H;
  zoom_grafo = Math.max(0.2, Math.min(4, Math.min((vw - 2 * mi) / Math.max(maxx - minx, 100), (vh - ma - mb) / Math.max(maxy - miny, 100))));
  const ox = mi + (vw - 2 * mi) / 2, oy = ma + (vh - ma - mb) / 2;   // dónde debe quedar el centro (suma un número para moverlo)
  pan_x = ox - W / 2 - ((minx + maxx) / 2 - W / 2) * zoom_grafo;
  pan_y = oy - H / 2 - ((miny + maxy) / 2 - H / 2) * zoom_grafo;
  dibujar();
}

// ---------- CONEXIÓN DE BOTONES (equivale a command= y bind() de tkinter) ----------
$("btn_generar").onclick = generar;
$("var_n").addEventListener("keydown", e => { if (e.key === "Enter") generar(); });
$("var_peso_max").addEventListener("keydown", e => { if (e.key === "Enter") generar(); });
document.querySelectorAll('input[name="modo"]').forEach(r => r.addEventListener("change", cambiar_modo));
$("btn_anadir").onclick = anadir;
$("entrada").addEventListener("keydown", e => {
  if (e.key === "Enter") anadir();
  if (e.key === "Escape") { $("entrada").value = ""; reiniciar_ejecucion(); }
});
$("btn_quitar").onclick = quitar;
$("btn_limpiar").onclick = limpiar;
$("zoom_mas").onclick = () => cambiar_zoom(1.15);
$("zoom_menos").onclick = () => cambiar_zoom(1 / 1.15);
$("btn_ajustar").onclick = ajustar_a_ventana;
// Cambiar Origen/Destino: en modo manual reinicia la ejecución; en aleatorio solo redibuja (igual que en Python).
$("origen").onchange = $("destino").onchange = () => (modo() === "man" ? reiniciar_ejecucion(false) : dibujar());
$("btn_colapsar_sup").onclick = alternar_panel_superior;
$("btn_colapsar_inf").onclick = alternar_panel_inferior;
$("btn_ejecutar").onclick = ejecutar;
$("btn_reiniciar").onclick = () => ir_a_paso(0);
$("btn_anterior").onclick = () => ir_a_paso(paso_actual - 1);
$("btn_siguiente").onclick = () => ir_a_paso(paso_actual + 1);
$("btn_final").onclick = () => ir_a_paso(pasos.length - 1);

// Al cambiar el tamaño de la ventana, redibuja una sola vez tras 50 ms (evita redibujar sin parar).
let temporizador = null;
window.addEventListener("resize", () => { clearTimeout(temporizador); temporizador = setTimeout(dibujar, 50); });

// ---------- ARRANQUE ----------
estado_controles(false);
generar();                                  // crea un primer grafo aleatorio
setTimeout(ajustar_a_ventana, 150);         // y lo ajusta cuando la página ya tiene su tamaño real
