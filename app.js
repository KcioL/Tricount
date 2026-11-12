// Comptes de Potes — partage des dépenses entre amis, stocké dans Firestore.
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import {
  getFirestore, collection, doc, setDoc, updateDoc, deleteDoc,
  onSnapshot, query, orderBy
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";
import { firebaseConfig } from "./firebase-config.js";

const ROOT = "comptesDePotes";          // collection Firestore dédiée à l'appli
const LS_KEY = "comptesDePotes.groupes"; // groupes ouverts sur cet appareil

const app = document.getElementById("app");
const dlg = document.getElementById("dlg");
const dlgBody = document.getElementById("dlgBody");

let db = null;
let fatal = "";
let flashMsg = "";
let flashKind = "err";

// Accueil : groupes mémorisés sur cet appareil
let myGroups = loadMyGroups();   // [{id, name}]
const groupCache = {};           // id -> données du groupe (ou null si supprimé)
const homeSubs = {};             // id -> unsubscribe

// Groupe ouvert
let current = null;
let group = null;
let groupLoaded = false;
let expenses = [];
let expensesLoaded = false;
let unsubGroup = null;
let unsubExp = null;
let tab = "depenses";

// ---------- utilitaires ----------
const esc = (s) => String(s == null ? "" : s).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));

function fmt(cents, cur) {
  const v = (Math.abs(cents) / 100).toLocaleString("fr-FR", { minimumFractionDigits: 2, maximumFractionDigits: 2 });
  return (cents < 0 ? "−" : "") + v + " " + (cur || "€");
}
function parseAmount(str) {
  const s = String(str).replace(/\s/g, "").replace(",", ".");
  if (!/^\d+(\.\d{0,2})?$/.test(s)) return null;
  const c = Math.round(parseFloat(s) * 100);
  return c > 0 ? c : null;
}
function today() {
  const d = new Date();
  return d.getFullYear() + "-" + String(d.getMonth() + 1).padStart(2, "0") + "-" + String(d.getDate()).padStart(2, "0");
}
function dayLabel(iso) {
  try { return new Date(iso + "T12:00:00").toLocaleDateString("fr-FR", { weekday: "long", day: "numeric", month: "long" }); }
  catch (e) { return iso; }
}
function cleanNames(arr) {
  const seen = new Set(); const out = [];
  (arr || []).forEach(n => {
    const t = String(n).trim().slice(0, 30);
    if (t && !seen.has(t.toLowerCase())) { seen.add(t.toLowerCase()); out.push(t); }
  });
  return out;
}
function newId() {
  // identifiant long et aléatoire : c'est lui qui protège l'accès au groupe
  const a = new Uint8Array(15); crypto.getRandomValues(a);
  return Array.from(a, b => "abcdefghijklmnopqrstuvwxyz0123456789"[b % 36]).join("");
}
function shareUrl(id) { return location.origin + location.pathname + "#g-" + id; }

function loadMyGroups() {
  try { const v = JSON.parse(localStorage.getItem(LS_KEY) || "[]"); return Array.isArray(v) ? v : []; }
  catch (e) { return []; }
}
function saveMyGroups() {
  try { localStorage.setItem(LS_KEY, JSON.stringify(myGroups)); } catch (e) { /* stockage indisponible */ }
}
function rememberGroup(id, name) {
  const g = myGroups.find(x => x.id === id);
  if (g) { if (g.name !== name) { g.name = name; saveMyGroups(); } return; }
  myGroups.unshift({ id, name }); saveMyGroups();
}
function forgetGroup(id) {
  myGroups = myGroups.filter(x => x.id !== id); saveMyGroups();
  if (homeSubs[id]) { homeSubs[id](); delete homeSubs[id]; }
  delete groupCache[id];
}

// ---------- calculs ----------
// Partage à parts égales ; les centimes restants vont aux premiers.
function shares(amount, people) {
  const n = people.length; if (!n) return {};
  const base = Math.floor(amount / n); let rest = amount - base * n;
  const out = {};
  people.forEach(p => { out[p] = base + (rest > 0 ? 1 : 0); if (rest > 0) rest--; });
  return out;
}
function computeBalances(members, list) {
  const bal = {}; members.forEach(m => bal[m] = 0);
  list.forEach(e => {
    const parts = (e.participants || []).filter(p => p in bal);
    if (!(e.payer in bal) || !parts.length) return;
    bal[e.payer] += e.amount;
    const s = shares(e.amount, parts);
    for (const p in s) bal[p] -= s[p];
  });
  return bal;
}
// Le plus gros débiteur rembourse le plus gros créancier : n-1 virements au maximum.
function settlements(bal) {
  const cred = [], debt = [];
  for (const k in bal) { if (bal[k] > 0) cred.push([k, bal[k]]); else if (bal[k] < 0) debt.push([k, -bal[k]]); }
  cred.sort((a, b) => b[1] - a[1]); debt.sort((a, b) => b[1] - a[1]);
  const out = []; let i = 0, j = 0;
  while (i < debt.length && j < cred.length) {
    const x = Math.min(debt[i][1], cred[j][1]);
    if (x > 0) out.push({ from: debt[i][0], to: cred[j][0], amount: x });
    debt[i][1] -= x; cred[j][1] -= x;
    if (debt[i][1] === 0) i++;
    if (cred[j][1] === 0) j++;
  }
  return out;
}

// ---------- Firestore ----------
function errText(e) {
  const c = e && e.code;
  if (c === "permission-denied") return "Firestore a refusé l'opération. Vérifie que les règles de sécurité ont bien été publiées.";
  if (c === "unavailable") return "Pas de connexion. Les changements seront envoyés dès que tu seras de nouveau en ligne.";
  if (c === "resource-exhausted") return "Le quota gratuit de Firebase est atteint pour aujourd'hui. Réessaie demain.";
  return "Impossible d'enregistrer pour l'instant. Réessaie dans un instant.";
}
const groupRef = (id) => doc(db, ROOT, id);
const expensesCol = (id) => collection(db, ROOT, id, "expenses");

function init() {
  if (!firebaseConfig || !firebaseConfig.projectId || String(firebaseConfig.apiKey).includes("COLLE_ICI")) {
    fatal = "Configuration Firebase manquante : remplis le fichier firebase-config.js avec les infos de ton projet.";
    render(); return;
  }
  try {
    db = getFirestore(initializeApp(firebaseConfig));
  } catch (e) {
    fatal = "Impossible de se connecter à Firebase. Vérifie le fichier firebase-config.js.";
    render(); return;
  }
  window.addEventListener("hashchange", route);
  route();
}

function watchHomeGroups() {
  myGroups.forEach(g => {
    if (homeSubs[g.id]) return;
    homeSubs[g.id] = onSnapshot(groupRef(g.id), snap => {
      if (!snap.exists()) { forgetGroup(g.id); render(); return; }
      groupCache[g.id] = snap.data();
      rememberGroup(g.id, snap.data().name);
      if (!current) render();
    }, () => { groupCache[g.id] = groupCache[g.id] || null; });
  });
}

function openGroup(id) {
  if (current === id) { render(); return; }
  if (unsubGroup) { unsubGroup(); unsubGroup = null; }
  if (unsubExp) { unsubExp(); unsubExp = null; }
  current = id; group = null; groupLoaded = false; expenses = []; expensesLoaded = false; tab = "depenses";
  if (!id) { watchHomeGroups(); render(); return; }

  unsubGroup = onSnapshot(groupRef(id), snap => {
    groupLoaded = true;
    group = snap.exists() ? snap.data() : null;
    if (group) rememberGroup(id, group.name);
    render();
  }, e => { groupLoaded = true; flash(errText(e)); });

  unsubExp = onSnapshot(query(expensesCol(id), orderBy("date", "desc")), snap => {
    expenses = snap.docs.map(d => Object.assign({ id: d.id }, d.data()));
    expensesLoaded = true;
    syncTotal();
    render();
  }, e => { expensesLoaded = true; flash(errText(e)); });

  render();
}

// garde le total sur le document du groupe pour l'accueil (écrit seulement s'il change)
function syncTotal() {
  if (!group || !current) return;
  const t = expenses.reduce((s, e) => s + (e.amount || 0), 0);
  if (group.total !== t) { group.total = t; updateDoc(groupRef(current), { total: t }).catch(() => {}); }
}

function route() {
  const h = location.hash.replace(/^#/, "");
  const id = h.startsWith("g-") ? h.slice(2) : null;
  openGroup(id && /^[a-z0-9]{6,40}$/i.test(id) ? id : null);
}

function flash(m, kind = "err") {
  flashMsg = m; flashKind = kind; render();
  setTimeout(() => { if (flashMsg === m) { flashMsg = ""; render(); } }, 5000);
}

// ---------- affichage ----------
function header() {
  return `<div class="topbar"><div class="mark">÷</div><div class="grow"><h1>Comptes de Potes</h1></div></div>`;
}
function flashBox() {
  return flashMsg ? `<div class="notice ${flashKind}">${esc(flashMsg)}</div>` : "";
}

function render() {
  if (fatal) { app.innerHTML = header() + `<div class="notice err">${esc(fatal)}</div>`; return; }
  if (current) {
    if (!groupLoaded) { app.innerHTML = `<div class="notice">Chargement du groupe…</div>`; return; }
    if (!group) {
      app.innerHTML = header() + `<div class="notice err">Ce groupe n'existe pas ou a été supprimé. Vérifie le lien qu'on t'a envoyé.</div>
        <div><button class="btn ghost" data-home>← Mes groupes</button></div>`;
      bind(); return;
    }
    app.innerHTML = groupView(group);
  } else {
    app.innerHTML = homeView();
  }
  bind();
}

function homeView() {
  const list = myGroups.length ? myGroups.map(g => {
    const d = groupCache[g.id];
    const ms = d ? (d.members || []) : [];
    return `<button class="group-row" data-open="${esc(g.id)}">
      <div class="grow"><h3>${esc(d ? d.name : g.name)}</h3>
        <div class="who">${d ? `${ms.length} pers. · ${esc(ms.join(", "))}` : "Chargement…"}</div></div>
      <div class="total">${d && typeof d.total === "number" ? fmt(d.total, d.currency) : ""}</div>
    </button>`;
  }).join("") : `<div class="notice">Aucun groupe sur cet appareil. Crée-en un ci-dessous, ou ouvre le lien qu'un pote t'a envoyé pour rejoindre le sien.</div>`;

  return `${header()}
    <p class="muted">Notez qui a payé quoi, l'appli calcule qui doit combien à qui. Partagez le lien d'un groupe avec vos potes pour remplir les comptes ensemble.</p>
    ${flashBox()}
    <section style="display:flex;flex-direction:column;gap:10px">
      <div class="label">Mes groupes</div>
      <div class="groups">${list}</div>
    </section>
    <form class="panel" id="newGroup" autocomplete="off">
      <h2>Nouveau groupe</h2>
      <div class="row">
        <div class="field" style="flex:2 1 220px"><label for="gName">Nom</label><input class="input" id="gName" maxlength="60" placeholder="Week-end à l'île de Ré" required></div>
        <div class="field" style="flex:1 1 100px"><label for="gCur">Devise</label>
          <select class="input" id="gCur"><option value="€">Euro (€)</option><option value="$">Dollar ($)</option><option value="£">Livre (£)</option><option value="CHF">Franc suisse (CHF)</option></select></div>
      </div>
      <div class="field"><label for="gMembers">Participants</label><input class="input" id="gMembers" placeholder="Léa, Hugo, Inès, Tom" required>
        <span class="hint">Sépare les prénoms par des virgules. Tu pourras en ajouter plus tard.</span></div>
      <div class="error-text" id="gErr" hidden></div>
      <div class="actions"><button class="btn" type="submit">Créer le groupe</button></div>
    </form>`;
}

function groupView(g) {
  const members = g.members || [];
  const cur = g.currency || "€";
  const total = expenses.reduce((s, e) => s + e.amount, 0);
  const bal = computeBalances(members, expenses);
  const perHead = members.length ? Math.round(total / members.length) : 0;

  let body;
  if (!expensesLoaded) body = `<div class="notice">Chargement des dépenses…</div>`;
  else if (tab === "depenses") body = expensesTab(g, cur);
  else if (tab === "equilibres") body = balancesTab(bal, cur);
  else body = membersTab(g);

  return `
    <div class="topbar"><button class="link" data-home>← Mes groupes</button></div>
    <div class="topbar"><div class="grow"><div class="label">Groupe</div><h1>${esc(g.name)}</h1></div>
      <button class="btn" data-add ${members.length ? "" : "disabled"}>+ Dépense</button></div>
    ${flashBox()}
    <div class="summary">
      <div class="stat"><div class="label">Total dépensé</div><div class="v">${fmt(total, cur)}</div></div>
      <div class="stat"><div class="label">Par personne</div><div class="v">${fmt(perHead, cur)}</div></div>
      <div class="stat"><div class="label">Dépenses</div><div class="v">${expenses.length}</div></div>
    </div>
    <div class="tabs" role="tablist">
      <button role="tab" data-tab="depenses" aria-selected="${tab === "depenses"}">Dépenses</button>
      <button role="tab" data-tab="equilibres" aria-selected="${tab === "equilibres"}">Équilibres</button>
      <button role="tab" data-tab="membres" aria-selected="${tab === "membres"}">Groupe</button>
    </div>
    ${body}`;
}

function expensesTab(g, cur) {
  if (!expenses.length) return `<div class="notice">Pas encore de dépense. Appuie sur « + Dépense » pour noter la première : les courses, l'essence, le resto…</div>`;
  const byDay = {};
  expenses.forEach(e => { (byDay[e.date] = byDay[e.date] || []).push(e); });
  return Object.keys(byDay).sort().reverse().map(d => `
    <section class="day"><div class="label">${esc(dayLabel(d))}</div>
    ${byDay[d].map(e => {
      const n = (e.participants || []).length;
      const forAll = n === (g.members || []).length;
      return `<article class="expense">
        <div class="t">${esc(e.title)}</div><div class="a">${fmt(e.amount, cur)}</div>
        <div class="m">Payé par <strong>${esc(e.payer)}</strong> · pour ${forAll ? "tout le monde" : esc((e.participants || []).join(", "))}</div>
        <div class="share-each">÷ ${n} = ${fmt(n ? Math.round(e.amount / n) : 0, cur)}</div>
        <div class="ops"><button class="link" data-edit="${esc(e.id)}">Modifier</button><button class="link" style="color:var(--neg)" data-del="${esc(e.id)}">Supprimer</button></div>
      </article>`;
    }).join("")}
    </section>`).join("");
}

function balancesTab(bal, cur) {
  const names = Object.keys(bal);
  if (!names.length) return `<div class="notice">Ajoute des participants pour voir les équilibres.</div>`;
  const max = Math.max(1, ...names.map(n => Math.abs(bal[n])));
  const rows = names.sort((a, b) => bal[b] - bal[a]).map(n => {
    const v = bal[n]; const w = Math.abs(v) / max * 50;
    const style = v >= 0 ? `left:50%;width:${w}%;background:var(--pos)` : `right:50%;width:${w}%;background:var(--neg)`;
    return `<div class="bal"><div class="name">${esc(n)}</div><div class="bar"><span style="${style}"></span></div>
      <div class="v ${v > 0 ? "pos" : v < 0 ? "neg" : "muted"}">${v > 0 ? "+" : ""}${fmt(v, cur)}</div></div>`;
  }).join("");
  const st = settlements(bal);
  const plan = st.length ? st.map((s, i) => `
    <div class="settle-item"><strong>${esc(s.from)}</strong><span class="arrow">doit</span><span class="amt">${fmt(s.amount, cur)}</span><span class="arrow">à</span><strong class="grow">${esc(s.to)}</strong>
      <button class="btn ghost" data-pay="${i}">C'est réglé</button></div>`).join("")
    : `<div class="notice ok">Tout le monde est quitte.</div>`;
  return `
    <section class="panel"><h2>Qui est en positif ?</h2>
      <p class="hint">En vert : a avancé plus que sa part. En rouge : doit encore de l'argent.</p>
      <div class="balances">${rows}</div></section>
    <section class="panel"><h2>Remboursements</h2>
      <p class="hint">Le moins de virements possible pour que tout le monde soit quitte. « C'est réglé » ajoute le remboursement aux dépenses.</p>
      <div class="settle">${plan}</div></section>`;
}

function membersTab(g) {
  const ms = g.members || [];
  const used = new Set();
  expenses.forEach(e => { used.add(e.payer); (e.participants || []).forEach(p => used.add(p)); });
  return `
    <section class="panel"><h2>Inviter des potes</h2>
      <p class="hint">Envoie ce lien : toute personne qui l'a peut voir et modifier les comptes du groupe.</p>
      <div class="share"><input class="input" id="shareLink" readonly value="${esc(shareUrl(current))}"><button class="btn" id="copyLink">Copier le lien</button></div>
    </section>
    <section class="panel"><h2>Participants</h2>
      <div class="chips">${ms.map(m => `<span class="chip">${esc(m)}${used.has(m) ? "" : `<button class="x" title="Retirer ${esc(m)}" aria-label="Retirer ${esc(m)}" data-rm="${esc(m)}">×</button>`}</span>`).join("")}</div>
      <p class="hint">Une personne qui apparaît déjà dans une dépense ne peut pas être retirée.</p>
      <form class="row" id="addMember" autocomplete="off" style="align-items:flex-end">
        <div class="field" style="flex:3 1 180px"><label for="mName">Ajouter quelqu'un</label><input class="input" id="mName" maxlength="30" placeholder="Prénom"></div>
        <div style="flex:1 1 100px"><button class="btn" type="submit" style="width:100%">Ajouter</button></div>
      </form>
    </section>
    <section class="panel"><h2>Retirer de mes groupes</h2>
      <p class="hint">Masque ce groupe sur cet appareil uniquement. Les comptes restent intacts pour les autres.</p>
      <div class="actions"><button class="btn ghost" data-forget>Retirer de mes groupes</button></div>
    </section>
    <section class="panel"><h2>Supprimer le groupe</h2>
      <p class="hint">Efface le groupe et toutes ses dépenses, pour tout le monde. Impossible à annuler.</p>
      <div class="actions"><button class="btn danger" data-delgroup>Supprimer « ${esc(g.name)} »</button></div>
    </section>`;
}

// ---------- interactions ----------
function bind() {
  const ng = document.getElementById("newGroup");
  if (ng) ng.addEventListener("submit", async ev => {
    ev.preventDefault();
    const name = document.getElementById("gName").value.trim().slice(0, 60);
    const members = cleanNames(document.getElementById("gMembers").value.split(","));
    const err = document.getElementById("gErr");
    if (!name || members.length < 2) { err.textContent = "Donne un nom au groupe et au moins deux participants."; err.hidden = false; return; }
    const btn = ng.querySelector("button[type=submit]"); btn.disabled = true;
    const id = newId();
    try {
      await setDoc(groupRef(id), { name, currency: document.getElementById("gCur").value, members, total: 0, createdAt: Date.now() });
      rememberGroup(id, name);
      location.hash = "g-" + id;
    } catch (e) { btn.disabled = false; err.textContent = errText(e); err.hidden = false; }
  });

  app.querySelectorAll("[data-open]").forEach(b => b.addEventListener("click", () => { location.hash = "g-" + b.dataset.open; }));
  app.querySelectorAll("[data-home]").forEach(b => b.addEventListener("click", () => { location.hash = ""; }));
  app.querySelectorAll("[data-tab]").forEach(b => b.addEventListener("click", () => { tab = b.dataset.tab; render(); }));
  app.querySelectorAll("[data-add]").forEach(b => b.addEventListener("click", () => expenseDialog(null)));
  app.querySelectorAll("[data-edit]").forEach(b => b.addEventListener("click", () => expenseDialog(expenses.find(e => e.id === b.dataset.edit))));

  app.querySelectorAll("[data-del]").forEach(b => b.addEventListener("click", () => {
    const e = expenses.find(x => x.id === b.dataset.del); if (!e) return;
    confirmDialog("Supprimer cette dépense ?", `« ${e.title} » (${fmt(e.amount, group.currency)}) sera retirée des comptes de tout le groupe.`, "Supprimer",
      () => deleteDoc(doc(expensesCol(current), e.id)));
  }));

  app.querySelectorAll("[data-pay]").forEach(b => b.addEventListener("click", () => {
    const s = settlements(computeBalances(group.members || [], expenses))[+b.dataset.pay]; if (!s) return;
    confirmDialog("Remboursement effectué ?", `${s.from} a remboursé ${fmt(s.amount, group.currency)} à ${s.to}. On l'ajoute aux comptes.`, "Oui, c'est réglé",
      () => setDoc(doc(expensesCol(current)), {
        title: ("Remboursement " + s.from + " → " + s.to).slice(0, 80), amount: s.amount, payer: s.from,
        participants: [s.to], date: today(), createdAt: Date.now(), kind: "remboursement"
      }), false);
  }));

  const copy = document.getElementById("copyLink");
  if (copy) copy.addEventListener("click", async () => {
    const input = document.getElementById("shareLink");
    try { await navigator.clipboard.writeText(input.value); flash("Lien copié. Envoie-le à tes potes.", "ok"); }
    catch (e) { input.focus(); input.select(); }
  });

  const am = document.getElementById("addMember");
  if (am) am.addEventListener("submit", ev => {
    ev.preventDefault();
    const next = cleanNames((group.members || []).concat([document.getElementById("mName").value]));
    if (next.length === (group.members || []).length) return;
    updateDoc(groupRef(current), { members: next }).catch(e => flash(errText(e)));
  });
  app.querySelectorAll("[data-rm]").forEach(b => b.addEventListener("click", () => {
    updateDoc(groupRef(current), { members: (group.members || []).filter(m => m !== b.dataset.rm) }).catch(e => flash(errText(e)));
  }));

  app.querySelectorAll("[data-forget]").forEach(b => b.addEventListener("click", () => {
    forgetGroup(current); location.hash = "";
  }));

  app.querySelectorAll("[data-delgroup]").forEach(b => b.addEventListener("click", () => {
    confirmDialog("Supprimer le groupe ?", `« ${group.name} » et ses ${expenses.length} dépense(s) seront effacés pour tout le monde. Impossible à annuler.`, "Supprimer définitivement", async () => {
      const id = current;
      for (const e of expenses.slice()) await deleteDoc(doc(expensesCol(id), e.id));
      await deleteDoc(groupRef(id));
      forgetGroup(id);
      location.hash = "";
    });
  }));
}

function showDialog(html) {
  dlgBody.innerHTML = html;
  if (typeof dlg.showModal === "function") dlg.showModal(); else dlg.setAttribute("open", "");
}
function closeDialog() {
  if (typeof dlg.close === "function") dlg.close(); else dlg.removeAttribute("open");
}
dlg.addEventListener("click", ev => { if (ev.target === dlg) closeDialog(); });

function confirmDialog(title, text, okLabel, action, danger = true) {
  showDialog(`<h2>${esc(title)}</h2><p class="muted">${esc(text)}</p><div class="error-text" id="cErr" hidden></div>
    <div class="actions"><button class="btn ghost" id="cNo">Annuler</button><button class="btn ${danger ? "danger" : ""}" id="cOk">${esc(okLabel)}</button></div>`);
  document.getElementById("cNo").onclick = closeDialog;
  document.getElementById("cOk").onclick = async (ev) => {
    ev.target.disabled = true;
    try { await action(); closeDialog(); }
    catch (e) { const x = document.getElementById("cErr"); x.textContent = errText(e); x.hidden = false; ev.target.disabled = false; }
  };
}

function expenseDialog(existing) {
  if (!group) return;
  const ms = group.members || [];
  const sel = new Set(existing ? existing.participants : ms);
  const payer = existing ? existing.payer : ms[0];
  showDialog(`
    <h2>${existing ? "Modifier la dépense" : "Nouvelle dépense"}</h2>
    <form id="expForm" autocomplete="off" style="display:flex;flex-direction:column;gap:14px">
      <div class="field"><label for="eTitle">Pour quoi ?</label><input class="input" id="eTitle" maxlength="80" placeholder="Courses, essence, resto…" value="${esc(existing ? existing.title : "")}" required></div>
      <div class="row">
        <div class="field"><label for="eAmount">Montant (${esc(group.currency || "€")})</label><input class="input num" id="eAmount" inputmode="decimal" placeholder="42,50" value="${existing ? (existing.amount / 100).toFixed(2).replace(".", ",") : ""}" required></div>
        <div class="field"><label for="eDate">Date</label><input class="input" type="date" id="eDate" value="${esc(existing ? existing.date : today())}" required></div>
      </div>
      <div class="field"><label for="ePayer">Payé par</label><select class="input" id="ePayer">${ms.map(m => `<option ${m === payer ? "selected" : ""}>${esc(m)}</option>`).join("")}</select></div>
      <div class="field"><label>Pour qui ? <span class="hint">(partagé à parts égales)</span></label>
        <div class="chips">${ms.map(m => `<button type="button" class="chip toggle" aria-pressed="${sel.has(m)}" data-p="${esc(m)}">${esc(m)}</button>`).join("")}</div>
        <div><button type="button" class="link" id="eAll">Tout le monde</button></div></div>
      <div class="hint num" id="eSplit"></div>
      <div class="error-text" id="eErr" hidden></div>
      <div class="actions"><button type="button" class="btn ghost" id="eCancel">Annuler</button><button class="btn" type="submit">${existing ? "Enregistrer" : "Ajouter"}</button></div>
    </form>`);

  const parts = () => [...dlgBody.querySelectorAll("[data-p]")].filter(b => b.getAttribute("aria-pressed") === "true").map(b => b.dataset.p);
  const upd = () => {
    const a = parseAmount(document.getElementById("eAmount").value); const p = parts();
    document.getElementById("eSplit").textContent = a && p.length ? `Soit ${fmt(Math.round(a / p.length), group.currency)} par personne (${p.length})` : "";
  };
  dlgBody.querySelectorAll("[data-p]").forEach(b => b.onclick = () => {
    b.setAttribute("aria-pressed", b.getAttribute("aria-pressed") === "true" ? "false" : "true"); upd();
  });
  document.getElementById("eAll").onclick = () => { dlgBody.querySelectorAll("[data-p]").forEach(b => b.setAttribute("aria-pressed", "true")); upd(); };
  document.getElementById("eAmount").oninput = upd;
  document.getElementById("eCancel").onclick = closeDialog;
  upd();

  document.getElementById("expForm").onsubmit = async (ev) => {
    ev.preventDefault();
    const err = document.getElementById("eErr");
    const title = document.getElementById("eTitle").value.trim().slice(0, 80);
    const amount = parseAmount(document.getElementById("eAmount").value);
    const p = parts();
    const date = document.getElementById("eDate").value || today();
    if (!title) { err.textContent = "Indique à quoi correspond la dépense."; err.hidden = false; return; }
    if (!amount) { err.textContent = "Montant invalide. Exemple : 42,50"; err.hidden = false; return; }
    if (!p.length) { err.textContent = "Choisis au moins une personne concernée."; err.hidden = false; return; }
    const data = { title, amount, payer: document.getElementById("ePayer").value, participants: p, date };
    const btn = dlgBody.querySelector("button[type=submit]"); btn.disabled = true;
    try {
      if (existing) await updateDoc(doc(expensesCol(current), existing.id), data);
      else await setDoc(doc(expensesCol(current)), Object.assign({ createdAt: Date.now() }, data));
      closeDialog();
    } catch (e) { err.textContent = errText(e); err.hidden = false; btn.disabled = false; }
  };
  setTimeout(() => { const t = document.getElementById("eTitle"); if (t) t.focus(); }, 30);
}

init();
