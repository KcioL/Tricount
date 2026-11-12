// Comptes de Potes — partage des dépenses entre amis, stocké dans Firestore.
// Chacun se connecte avec un compte email + mot de passe (Firebase Auth) : c'est ce qui
// permet aux règles Firestore de garantir que chacun ne gère que ses propres dépenses.
// Le prénom affiché se choisit séparément dans chaque groupe.
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import {
  getAuth, onAuthStateChanged, createUserWithEmailAndPassword,
  signInWithEmailAndPassword, sendPasswordResetEmail, signOut
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js";
import {
  getFirestore, collection, doc, setDoc, updateDoc, deleteDoc, writeBatch, getDocs,
  onSnapshot, query, orderBy, limit
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";
import { firebaseConfig } from "./firebase-config.js";

const ROOT = "comptesDePotes";          // collection Firestore dédiée à l'appli
const USERS = "comptesDePotesUsers";     // liste « Mes groupes » de chaque compte
const LOG_LIMIT = 150;                  // entrées du journal affichées

const app = document.getElementById("app");
const dlg = document.getElementById("dlg");
const dlgBody = document.getElementById("dlgBody");

let db = null;
let auth = null;
let authReady = false;
let me = null;          // uid du compte connecté
let myEmail = "";
let authMode = "login"; // "login" | "signup"
let fatal = "";
let flashMsg = "";
let flashKind = "err";

// Accueil
let myGroups = [];               // [{id, name, addedAt}] depuis Firestore
let myGroupsLoaded = false;
let unsubMyGroups = null;
const groupCache = {};
const homeSubs = {};

// Groupe ouvert
let current = null;
let group = null, groupLoaded = false;
let members = {}, membersLoaded = false;     // uid -> {name, joinedAt}
let expenses = [], expensesLoaded = false;
let logEntries = [];
let subs = [];
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
function timeLabel(ms) {
  const d = new Date(ms);
  const sameDay = d.toDateString() === new Date().toDateString();
  return sameDay
    ? "aujourd'hui à " + d.toLocaleTimeString("fr-FR", { hour: "2-digit", minute: "2-digit" })
    : d.toLocaleDateString("fr-FR", { day: "numeric", month: "short" }) + " à " + d.toLocaleTimeString("fr-FR", { hour: "2-digit", minute: "2-digit" });
}
function cleanName(s) { return String(s || "").trim().replace(/\s+/g, " ").slice(0, 30); }
function newId() {
  // identifiant long et aléatoire : c'est lui qui protège l'accès au groupe
  const a = new Uint8Array(15); crypto.getRandomValues(a);
  return Array.from(a, b => "abcdefghijklmnopqrstuvwxyz0123456789"[b % 36]).join("");
}
function shareUrl(id) { return location.origin + location.pathname + "#g-" + id; }
function nameOf(uid) { return (members[uid] && members[uid].name) || "Ancien membre"; }
function isOwner() { return !!(group && me && group.createdBy === me); }
function isMember() { return !!(me && members[me]); }
function nameTaken(name, exceptUid) {
  const n = name.toLowerCase();
  return Object.keys(members).some(uid => uid !== exceptUid && members[uid].name.toLowerCase() === n);
}

// « Mes groupes » est rangé dans le compte : on le retrouve sur tous ses appareils.
const myGroupRef = (id) => doc(db, USERS, me, "groups", id);
function rememberGroup(id, name, force = false) {
  if (!me || (!myGroupsLoaded && !force)) return;
  const g = myGroups.find(x => x.id === id);
  if (g && g.name === name) return;
  setDoc(myGroupRef(id), { name: String(name).slice(0, 60), addedAt: g ? g.addedAt : Date.now() }).catch(() => {});
}
function forgetGroup(id) {
  if (me) deleteDoc(myGroupRef(id)).catch(() => {});
  myGroups = myGroups.filter(x => x.id !== id);
  if (homeSubs[id]) { homeSubs[id](); delete homeSubs[id]; }
  delete groupCache[id];
}

// ---------- calculs (tout est en centimes, indexé par uid) ----------
function shares(amount, people) {
  const n = people.length; if (!n) return {};
  const base = Math.floor(amount / n); let rest = amount - base * n;
  const out = {};
  people.forEach(p => { out[p] = base + (rest > 0 ? 1 : 0); if (rest > 0) rest--; });
  return out;
}
function computeBalances(memberIds, list) {
  const bal = {}; memberIds.forEach(m => bal[m] = 0);
  list.forEach(e => {
    const parts = (e.participants || []).filter(p => p in bal);
    if (!(e.payer in bal) || !parts.length) return;
    bal[e.payer] += e.amount;
    const s = shares(e.amount, parts);
    for (const p in s) bal[p] -= s[p];
  });
  return bal;
}
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
  if (c === "permission-denied") return "Action refusée. Tu ne peux modifier que tes propres dépenses (ou les règles Firestore ne sont pas à jour).";
  if (c === "unavailable") return "Pas de connexion. Les changements seront envoyés dès que tu seras de nouveau en ligne.";
  if (c === "resource-exhausted") return "Le quota gratuit de Firebase est atteint pour aujourd'hui. Réessaie demain.";
  if (c === "auth/operation-not-allowed" || c === "auth/admin-restricted-operation")
    return "La connexion par email n'est pas activée. Console Firebase › Authentication › Sign-in method › Adresse e-mail/Mot de passe › Activer.";
  if (c === "auth/invalid-email") return "Cette adresse email n'est pas valide.";
  if (c === "auth/missing-password") return "Indique ton mot de passe.";
  if (c === "auth/email-already-in-use") return "Un compte existe déjà avec cet email. Connecte-toi plutôt.";
  if (c === "auth/weak-password") return "Mot de passe trop court : 6 caractères minimum.";
  if (c === "auth/invalid-credential" || c === "auth/wrong-password" || c === "auth/user-not-found" || c === "auth/invalid-login-credentials")
    return "Email ou mot de passe incorrect.";
  if (c === "auth/too-many-requests") return "Trop de tentatives. Attends quelques minutes ou réinitialise ton mot de passe.";
  if (c === "auth/network-request-failed") return "Pas de connexion internet. Vérifie ton réseau et réessaie.";
  if (c === "auth/unauthorized-domain") return "Ce site n'est pas autorisé. Ajoute son domaine dans Authentication › Paramètres › Domaines autorisés.";
  return "Impossible d'enregistrer pour l'instant. Réessaie dans un instant.";
}
const groupRef = (id) => doc(db, ROOT, id);
const sub = (id, name) => collection(db, ROOT, id, name);

// ajoute une entrée au journal dans le même lot d'écritures
function addLog(batch, gid, action, text, expenseId) {
  const entry = { action, by: me, at: Date.now(), text: String(text).slice(0, 200) };
  if (expenseId) entry.expenseId = expenseId;
  batch.set(doc(sub(gid, "log")), entry);
}

function init() {
  if (!firebaseConfig || !firebaseConfig.projectId || String(firebaseConfig.apiKey).includes("COLLE_ICI")) {
    fatal = "Configuration Firebase manquante : remplis le fichier firebase-config.js avec les infos de ton projet.";
    render(); return;
  }
  try {
    const fb = initializeApp(firebaseConfig);
    db = getFirestore(fb);
    auth = getAuth(fb);
  } catch (e) {
    fatal = "Impossible de se connecter à Firebase. Vérifie le fichier firebase-config.js.";
    render(); return;
  }
  render();
  window.addEventListener("hashchange", route);
  onAuthStateChanged(auth, user => {
    authReady = true;
    const uid = user ? user.uid : null;
    if (uid !== me) {
      resetSession();
      me = uid;
      myEmail = user ? (user.email || "") : "";
      if (me) watchMyGroups();
    }
    route();
  });
}

function resetSession() {
  closeGroup();
  Object.keys(homeSubs).forEach(k => { homeSubs[k](); delete homeSubs[k]; });
  Object.keys(groupCache).forEach(k => delete groupCache[k]);
  if (unsubMyGroups) { unsubMyGroups(); unsubMyGroups = null; }
  myGroups = []; myGroupsLoaded = false;
  current = undefined;
}

function watchMyGroups() {
  unsubMyGroups = onSnapshot(query(collection(db, USERS, me, "groups"), orderBy("addedAt", "desc")), snap => {
    myGroups = snap.docs.map(d => Object.assign({ id: d.id }, d.data()));
    myGroupsLoaded = true;
    if (!current) { watchHomeGroups(); render(); }
  }, e => { myGroupsLoaded = true; flash(errText(e)); });
}

function watchHomeGroups() {
  myGroups.forEach(g => {
    if (homeSubs[g.id]) return;
    homeSubs[g.id] = onSnapshot(groupRef(g.id), snap => {
      if (!snap.exists()) { forgetGroup(g.id); if (!current) render(); return; }
      groupCache[g.id] = snap.data();
      rememberGroup(g.id, snap.data().name);
      if (!current) render();
    }, () => {});
  });
}

function closeGroup() {
  subs.forEach(u => u()); subs = [];
  group = null; groupLoaded = false;
  members = {}; membersLoaded = false;
  expenses = []; expensesLoaded = false;
  logEntries = [];
}

function openGroup(id) {
  if (current === id) { render(); return; }
  closeGroup();
  current = id; tab = "depenses";
  if (!id) { watchHomeGroups(); render(); return; }

  subs.push(onSnapshot(groupRef(id), snap => {
    groupLoaded = true;
    group = snap.exists() ? snap.data() : null;
    if (group && isMember()) rememberGroup(id, group.name);
    render();
  }, e => { groupLoaded = true; flash(errText(e)); }));

  subs.push(onSnapshot(sub(id, "members"), snap => {
    members = {};
    snap.docs.forEach(d => { members[d.id] = d.data(); });
    membersLoaded = true;
    if (group && isMember()) rememberGroup(id, group.name);
    render();
  }, e => { membersLoaded = true; flash(errText(e)); }));

  subs.push(onSnapshot(query(sub(id, "expenses"), orderBy("date", "desc")), snap => {
    expenses = snap.docs.map(d => Object.assign({ id: d.id }, d.data()));
    expensesLoaded = true;
    syncTotal();
    render();
  }, e => { expensesLoaded = true; flash(errText(e)); }));

  subs.push(onSnapshot(query(sub(id, "log"), orderBy("at", "desc"), limit(LOG_LIMIT)), snap => {
    logEntries = snap.docs.map(d => d.data());
    if (tab === "journal") render();
  }, () => {}));

  render();
}

// garde le total sur le document du groupe pour l'accueil (écrit seulement s'il change)
function syncTotal() {
  if (!group || !current || !isMember()) return;
  const t = expenses.reduce((s, e) => s + (e.amount || 0), 0);
  if (group.total !== t) { group.total = t; updateDoc(groupRef(current), { total: t }).catch(() => {}); }
}

function route() {
  if (!me) { render(); return; }
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
  const account = me ? `<div class="account"><span class="account-email">${esc(myEmail)}</span><button class="link" data-logout>Déconnexion</button></div>` : "";
  return `<div class="topbar"><div class="mark">÷</div><div class="grow"><h1>Comptes de Potes</h1></div>${account}</div>`;
}
function pendingInvite() { return /^#g-[a-z0-9]{6,40}$/i.test(location.hash); }
function flashBox() {
  return flashMsg ? `<div class="notice ${flashKind}">${esc(flashMsg)}</div>` : "";
}

function render() {
  if (fatal) { app.innerHTML = header() + `<div class="notice err">${esc(fatal)}</div>`; return; }
  if (!authReady) { app.innerHTML = header() + `<div class="notice">Connexion…</div>`; return; }
  if (!me) { app.innerHTML = authView(); bind(); return; }
  if (current) {
    if (!groupLoaded || !membersLoaded) { app.innerHTML = `<div class="notice">Chargement du groupe…</div>`; return; }
    if (!group) {
      app.innerHTML = header() + `<div class="notice err">Ce groupe n'existe pas ou a été supprimé. Vérifie le lien qu'on t'a envoyé.</div>
        <div><button class="btn ghost" data-home>← Mes groupes</button></div>`;
      bind(); return;
    }
    app.innerHTML = isMember() ? groupView(group) : joinView(group);
  } else {
    app.innerHTML = homeView();
  }
  bind();
}

function homeView() {
  const list = !myGroupsLoaded ? `<div class="notice">Chargement de tes groupes…</div>` : myGroups.length ? myGroups.map(g => {
    const d = groupCache[g.id];
    return `<button class="group-row" data-open="${esc(g.id)}">
      <div class="grow"><h3>${esc(d ? d.name : g.name)}</h3>
        <div class="who">${d ? "Créé le " + new Date(d.createdAt).toLocaleDateString("fr-FR") : "Chargement…"}</div></div>
      <div class="total">${d && typeof d.total === "number" ? fmt(d.total, d.currency) : ""}</div>
    </button>`;
  }).join("") : `<div class="notice">Aucun groupe pour l'instant. Crée-en un ci-dessous, ou ouvre le lien qu'un pote t'a envoyé pour rejoindre le sien.</div>`;

  return `${header()}
    <p class="muted">Chacun note ce qu'il a payé, l'appli calcule qui doit combien à qui. Crée un groupe, puis envoie le lien à tes potes : ils créeront leur profil en arrivant.</p>
    ${flashBox()}
    <section class="stack">
      <div class="label">Mes groupes</div>
      <div class="groups">${list}</div>
    </section>
    <form class="panel" id="newGroup" autocomplete="off">
      <h2>Nouveau groupe</h2>
      <div class="row">
        <div class="field" style="flex:2 1 220px"><label for="gName">Nom du groupe</label><input class="input" id="gName" maxlength="60" placeholder="Week-end à l'île de Ré" required></div>
        <div class="field" style="flex:1 1 100px"><label for="gCur">Devise</label>
          <select class="input" id="gCur"><option value="€">Euro (€)</option><option value="$">Dollar ($)</option><option value="£">Livre (£)</option><option value="CHF">Franc suisse (CHF)</option></select></div>
      </div>
      <div class="field"><label for="gMe">Ton prénom</label><input class="input" id="gMe" maxlength="30" placeholder="Comment les autres te voient" required></div>
      <div class="error-text" id="gErr" hidden></div>
      <div class="actions"><button class="btn" type="submit">Créer le groupe</button></div>
    </form>`;
}

function authView() {
  const signup = authMode === "signup";
  return `${header()}
    <p class="muted">Chacun note ce qu'il a payé, l'appli calcule qui doit combien à qui. Un compte te permet de retrouver tes groupes sur tous tes appareils.</p>
    ${pendingInvite() ? `<div class="notice ok">Tu as été invité dans un groupe. Connecte-toi ou crée ton compte pour le rejoindre.</div>` : ""}
    ${flashBox()}
    <section class="panel">
      <div class="tabs" role="tablist">
        <button role="tab" data-auth="login" aria-selected="${!signup}">Se connecter</button>
        <button role="tab" data-auth="signup" aria-selected="${signup}">Créer un compte</button>
      </div>
      <form id="authForm" class="stack">
        <div class="field"><label for="aEmail">Email</label><input class="input" type="email" id="aEmail" autocomplete="email" required></div>
        <div class="field"><label for="aPass">Mot de passe</label><input class="input" type="password" id="aPass" autocomplete="${signup ? "new-password" : "current-password"}" minlength="6" required>
          ${signup ? `<span class="hint">6 caractères minimum.</span>` : ""}</div>
        ${signup ? `<div class="field"><label for="aPass2">Confirme le mot de passe</label><input class="input" type="password" id="aPass2" autocomplete="new-password" minlength="6" required></div>` : ""}
        <div class="error-text" id="aErr" hidden></div>
        <div class="actions">
          ${signup ? "" : `<button type="button" class="link" id="aReset">Mot de passe oublié ?</button><span class="grow"></span>`}
          <button class="btn" type="submit">${signup ? "Créer mon compte" : "Se connecter"}</button>
        </div>
      </form>
    </section>`;
}

function joinView(g) {
  const names = Object.values(members).map(m => m.name);
  return `${header()}
    <section class="panel">
      <div class="label">Invitation</div>
      <h2>Rejoindre « ${esc(g.name)} »</h2>
      <p class="muted">${names.length ? `Déjà dans le groupe : ${esc(names.join(", "))}.` : "Personne n'a encore rejoint ce groupe."}</p>
      <form id="joinForm" class="stack" autocomplete="off">
        <div class="field"><label for="jName">Ton prénom</label><input class="input" id="jName" maxlength="30" placeholder="Comment les autres te voient" required></div>
        <p class="hint">Ce prénom ne vaut que pour ce groupe : tu peux en choisir un autre dans chaque groupe. Tu pourras ajouter et modifier tes propres dépenses ; les autres verront ce que tu fais dans le journal.</p>
        <div class="error-text" id="jErr" hidden></div>
        <div class="actions"><button class="btn ghost" type="button" data-home>Annuler</button><button class="btn" type="submit">Rejoindre le groupe</button></div>
      </form>
    </section>`;
}

function groupView(g) {
  const ids = Object.keys(members);
  const cur = g.currency || "€";
  const total = expenses.reduce((s, e) => s + e.amount, 0);
  const bal = computeBalances(ids, expenses);
  const myBal = bal[me] || 0;

  let body;
  if (!expensesLoaded) body = `<div class="notice">Chargement des dépenses…</div>`;
  else if (tab === "depenses") body = expensesTab(g, cur);
  else if (tab === "equilibres") body = balancesTab(bal, cur);
  else if (tab === "journal") body = journalTab(cur);
  else body = groupTab(g);

  return `
    <div class="topbar"><button class="link" data-home>← Mes groupes</button><span class="grow"></span><span class="me-pill">${esc(nameOf(me))}</span></div>
    <div class="topbar"><div class="grow"><div class="label">Groupe</div><h1>${esc(g.name)}</h1></div>
      <button class="btn" data-add>+ Ma dépense</button></div>
    ${flashBox()}
    <div class="summary">
      <div class="stat"><div class="label">Total du groupe</div><div class="v">${fmt(total, cur)}</div></div>
      <div class="stat"><div class="label">Mon solde</div><div class="v ${myBal > 0 ? "pos" : myBal < 0 ? "neg" : ""}">${myBal > 0 ? "+" : ""}${fmt(myBal, cur)}</div></div>
      <div class="stat"><div class="label">Membres</div><div class="v">${ids.length}</div></div>
    </div>
    <div class="tabs" role="tablist">
      <button role="tab" data-tab="depenses" aria-selected="${tab === "depenses"}">Dépenses</button>
      <button role="tab" data-tab="equilibres" aria-selected="${tab === "equilibres"}">Équilibres</button>
      <button role="tab" data-tab="journal" aria-selected="${tab === "journal"}">Journal</button>
      <button role="tab" data-tab="groupe" aria-selected="${tab === "groupe"}">Groupe</button>
    </div>
    ${body}`;
}

function expensesTab(g, cur) {
  if (!expenses.length) return `<div class="notice">Pas encore de dépense. Appuie sur « + Ma dépense » pour noter ce que tu as payé : les courses, l'essence, le resto…</div>`;
  const byDay = {};
  expenses.forEach(e => { (byDay[e.date] = byDay[e.date] || []).push(e); });
  const total = Object.keys(members).length;
  return Object.keys(byDay).sort().reverse().map(d => `
    <section class="day"><div class="label">${esc(dayLabel(d))}</div>
    ${byDay[d].map(e => {
      const n = (e.participants || []).length;
      const forAll = n === total;
      const mine = e.createdBy === me;
      return `<article class="expense ${mine ? "mine" : ""}">
        <div class="t">${esc(e.title)}</div><div class="a">${fmt(e.amount, cur)}</div>
        <div class="m">Payé par <strong>${mine ? "toi" : esc(nameOf(e.payer))}</strong> · pour ${forAll ? "tout le monde" : esc((e.participants || []).map(p => p === me ? "toi" : nameOf(p)).join(", "))}</div>
        <div class="share-each">÷ ${n} = ${fmt(n ? Math.round(e.amount / n) : 0, cur)}</div>
        ${mine ? `<div class="ops"><button class="link" data-edit="${esc(e.id)}">Modifier</button><button class="link danger-link" data-del="${esc(e.id)}">Supprimer</button></div>` : ""}
      </article>`;
    }).join("")}
    </section>`).join("");
}

function balancesTab(bal, cur) {
  const ids = Object.keys(bal);
  const max = Math.max(1, ...ids.map(n => Math.abs(bal[n])));
  const rows = ids.sort((a, b) => bal[b] - bal[a]).map(uid => {
    const v = bal[uid]; const w = Math.abs(v) / max * 50;
    const style = v >= 0 ? `left:50%;width:${w}%;background:var(--pos)` : `right:50%;width:${w}%;background:var(--neg)`;
    return `<div class="bal"><div class="name">${esc(nameOf(uid))}${uid === me ? " <span class='muted'>(toi)</span>" : ""}</div><div class="bar"><span style="${style}"></span></div>
      <div class="v ${v > 0 ? "pos" : v < 0 ? "neg" : "muted"}">${v > 0 ? "+" : ""}${fmt(v, cur)}</div></div>`;
  }).join("");
  const st = settlements(bal);
  const plan = st.length ? st.map((s, i) => `
    <div class="settle-item"><strong>${s.from === me ? "Toi" : esc(nameOf(s.from))}</strong><span class="arrow">${s.from === me ? "dois" : "doit"}</span><span class="amt">${fmt(s.amount, cur)}</span><span class="arrow">à</span><strong class="grow">${s.to === me ? "toi" : esc(nameOf(s.to))}</strong>
      ${s.from === me ? `<button class="btn ghost" data-pay="${i}">J'ai remboursé</button>` : ""}</div>`).join("")
    : `<div class="notice ok">Tout le monde est quitte.</div>`;
  return `
    <section class="panel"><h2>Qui est en positif ?</h2>
      <p class="hint">En vert : a avancé plus que sa part. En rouge : doit encore de l'argent.</p>
      <div class="balances">${rows}</div></section>
    <section class="panel"><h2>Remboursements</h2>
      <p class="hint">Le moins de virements possible pour que tout le monde soit quitte. Quand tu as remboursé quelqu'un, appuie sur « J'ai remboursé » : c'est ajouté à tes dépenses.</p>
      <div class="settle">${plan}</div></section>`;
}

const LOG_ICON = { join: "＋", add: "€", edit: "✎", delete: "×", rename: "Aa", settle: "⇄" };
function journalTab() {
  if (!logEntries.length) return `<div class="notice">Rien dans le journal pour l'instant.</div>`;
  return `<section class="panel"><h2>Journal</h2>
    <p class="hint">Tout ce qui a été ajouté, modifié ou supprimé, et par qui. Le journal ne peut pas être modifié.</p>
    <ol class="log">${logEntries.map(l => `
      <li class="log-item log-${esc(l.action)}">
        <span class="log-icon" aria-hidden="true">${LOG_ICON[l.action] || "•"}</span>
        <div class="log-body"><div><strong>${l.by === me ? "Toi" : esc(nameOf(l.by))}</strong> ${esc(l.text)}</div>
          <div class="hint">${esc(timeLabel(l.at))}</div></div>
      </li>`).join("")}</ol>
    ${logEntries.length >= LOG_LIMIT ? `<p class="hint">Seules les ${LOG_LIMIT} dernières actions sont affichées.</p>` : ""}
  </section>`;
}

function groupTab(g) {
  const ids = Object.keys(members).sort((a, b) => (members[a].joinedAt || 0) - (members[b].joinedAt || 0));
  return `
    <section class="panel"><h2>Inviter des potes</h2>
      <p class="hint">Envoie ce lien : en l'ouvrant, chacun crée son profil et peut ajouter ses dépenses.</p>
      <div class="share"><input class="input" id="shareLink" readonly value="${esc(shareUrl(current))}"><button class="btn" id="copyLink">Copier le lien</button></div>
    </section>
    <section class="panel"><h2>Membres</h2>
      <div class="chips">${ids.map(uid => `<span class="chip ${uid === me ? "chip-me" : ""}">${esc(members[uid].name)}${uid === g.createdBy ? " <span class='muted'>· créateur</span>" : ""}</span>`).join("")}</div>
      <form class="row" id="renameForm" autocomplete="off" style="align-items:flex-end">
        <div class="field" style="flex:3 1 180px"><label for="rName">Mon prénom dans ce groupe</label><input class="input" id="rName" maxlength="30" value="${esc(nameOf(me))}"></div>
        <div style="flex:1 1 100px"><button class="btn ghost" type="submit" style="width:100%">Renommer</button></div>
      </form>
      <div class="error-text" id="rErr" hidden></div>
    </section>
    <section class="panel"><h2>Retirer de mes groupes</h2>
      <p class="hint">Masque ce groupe dans ta liste. Tu restes membre : rouvre le lien pour le retrouver.</p>
      <div class="actions"><button class="btn ghost" data-forget>Retirer de mes groupes</button></div>
    </section>
    ${isOwner() ? `<section class="panel"><h2>Supprimer le groupe</h2>
      <p class="hint">Réservé au créateur. Efface le groupe, toutes les dépenses et le journal, pour tout le monde. Impossible à annuler.</p>
      <div class="actions"><button class="btn danger" data-delgroup>Supprimer « ${esc(g.name)} »</button></div>
    </section>` : ""}`;
}

// ---------- interactions ----------
function bind() {
  app.querySelectorAll("[data-logout]").forEach(b => b.addEventListener("click", () => {
    location.hash = ""; signOut(auth).catch(e => flash(errText(e)));
  }));
  app.querySelectorAll("[data-auth]").forEach(b => b.addEventListener("click", () => { authMode = b.dataset.auth; render(); }));

  const af = document.getElementById("authForm");
  if (af) {
    const showErr = (m) => { const x = document.getElementById("aErr"); x.textContent = m; x.hidden = false; };
    af.addEventListener("submit", async ev => {
      ev.preventDefault();
      const email = document.getElementById("aEmail").value.trim();
      const pass = document.getElementById("aPass").value;
      const btn = af.querySelector("button[type=submit]");
      if (authMode === "signup" && pass !== document.getElementById("aPass2").value) { showErr("Les deux mots de passe ne sont pas identiques."); return; }
      btn.disabled = true;
      try {
        if (authMode === "signup") await createUserWithEmailAndPassword(auth, email, pass);
        else await signInWithEmailAndPassword(auth, email, pass);
      } catch (e) { btn.disabled = false; showErr(errText(e)); }
    });
    const reset = document.getElementById("aReset");
    if (reset) reset.addEventListener("click", async () => {
      const email = document.getElementById("aEmail").value.trim();
      if (!email) { showErr("Indique ton email, puis appuie à nouveau sur « Mot de passe oublié ? »."); return; }
      try {
        await sendPasswordResetEmail(auth, email);
        flash("Si un compte existe pour cette adresse, un email de réinitialisation vient d'être envoyé. Pense à vérifier les spams.", "ok");
      } catch (e) { showErr(errText(e)); }
    });
  }

  const ng = document.getElementById("newGroup");
  if (ng) ng.addEventListener("submit", async ev => {
    ev.preventDefault();
    const name = document.getElementById("gName").value.trim().slice(0, 60);
    const myName = cleanName(document.getElementById("gMe").value);
    const err = document.getElementById("gErr");
    if (!name || !myName) { err.textContent = "Donne un nom au groupe et ton prénom."; err.hidden = false; return; }
    const btn = ng.querySelector("button[type=submit]"); btn.disabled = true;
    const id = newId(); const now = Date.now();
    const b = writeBatch(db);
    b.set(groupRef(id), { name, currency: document.getElementById("gCur").value, total: 0, createdAt: now, createdBy: me });
    b.set(doc(sub(id, "members"), me), { name: myName, joinedAt: now });
    addLog(b, id, "join", `a créé le groupe « ${name} »`);
    try { await b.commit(); rememberGroup(id, name, true); location.hash = "g-" + id; }
    catch (e) { btn.disabled = false; err.textContent = errText(e); err.hidden = false; }
  });

  const jf = document.getElementById("joinForm");
  if (jf) jf.addEventListener("submit", async ev => {
    ev.preventDefault();
    const myName = cleanName(document.getElementById("jName").value);
    const err = document.getElementById("jErr");
    if (!myName) { err.textContent = "Indique ton prénom."; err.hidden = false; return; }
    if (nameTaken(myName)) { err.textContent = `« ${myName} » est déjà pris dans ce groupe. Ajoute une initiale, par exemple.`; err.hidden = false; return; }
    const btn = jf.querySelector("button[type=submit]"); btn.disabled = true;
    const b = writeBatch(db);
    b.set(doc(sub(current, "members"), me), { name: myName, joinedAt: Date.now() });
    addLog(b, current, "join", "a rejoint le groupe");
    try { await b.commit(); rememberGroup(current, group.name, true); }
    catch (e) { btn.disabled = false; err.textContent = errText(e); err.hidden = false; }
  });

  app.querySelectorAll("[data-open]").forEach(b => b.addEventListener("click", () => { location.hash = "g-" + b.dataset.open; }));
  app.querySelectorAll("[data-home]").forEach(b => b.addEventListener("click", () => { location.hash = ""; }));
  app.querySelectorAll("[data-tab]").forEach(b => b.addEventListener("click", () => { tab = b.dataset.tab; render(); }));
  app.querySelectorAll("[data-add]").forEach(b => b.addEventListener("click", () => expenseDialog(null)));
  app.querySelectorAll("[data-edit]").forEach(b => b.addEventListener("click", () => expenseDialog(expenses.find(e => e.id === b.dataset.edit))));

  app.querySelectorAll("[data-del]").forEach(b => b.addEventListener("click", () => {
    const e = expenses.find(x => x.id === b.dataset.del); if (!e) return;
    confirmDialog("Supprimer cette dépense ?", `« ${e.title} » (${fmt(e.amount, group.currency)}) sera retirée des comptes. La suppression apparaîtra dans le journal.`, "Supprimer", () => {
      const bt = writeBatch(db);
      bt.delete(doc(sub(current, "expenses"), e.id));
      addLog(bt, current, "delete", `a supprimé « ${e.title} » (${fmt(e.amount, group.currency)})`, e.id);
      return bt.commit();
    });
  }));

  app.querySelectorAll("[data-pay]").forEach(b => b.addEventListener("click", () => {
    const s = settlements(computeBalances(Object.keys(members), expenses))[+b.dataset.pay];
    if (!s || s.from !== me) return;
    confirmDialog("Remboursement effectué ?", `Tu as remboursé ${fmt(s.amount, group.currency)} à ${nameOf(s.to)}. On l'ajoute à tes dépenses.`, "Oui, j'ai remboursé", () => {
      const bt = writeBatch(db);
      const ref = doc(sub(current, "expenses"));
      bt.set(ref, {
        title: ("Remboursement à " + nameOf(s.to)).slice(0, 80), amount: s.amount, payer: me, participants: [s.to],
        date: today(), createdAt: Date.now(), createdBy: me, kind: "remboursement"
      });
      addLog(bt, current, "settle", `a remboursé ${fmt(s.amount, group.currency)} à ${nameOf(s.to)}`, ref.id);
      return bt.commit();
    }, false);
  }));

  const copy = document.getElementById("copyLink");
  if (copy) copy.addEventListener("click", async () => {
    const input = document.getElementById("shareLink");
    try { await navigator.clipboard.writeText(input.value); flash("Lien copié. Envoie-le à tes potes.", "ok"); }
    catch (e) { input.focus(); input.select(); }
  });

  const rf = document.getElementById("renameForm");
  if (rf) rf.addEventListener("submit", async ev => {
    ev.preventDefault();
    const err = document.getElementById("rErr");
    const n = cleanName(document.getElementById("rName").value);
    const old = nameOf(me);
    if (!n || n === old) return;
    if (nameTaken(n, me)) { err.textContent = `« ${n} » est déjà pris dans ce groupe.`; err.hidden = false; return; }
    const bt = writeBatch(db);
    bt.update(doc(sub(current, "members"), me), { name: n });
    addLog(bt, current, "rename", `s'appelle maintenant ${n} (avant : ${old})`);
    try { await bt.commit(); flash("Prénom mis à jour.", "ok"); }
    catch (e) { err.textContent = errText(e); err.hidden = false; }
  });

  app.querySelectorAll("[data-forget]").forEach(b => b.addEventListener("click", () => {
    forgetGroup(current); location.hash = "";
  }));

  app.querySelectorAll("[data-delgroup]").forEach(b => b.addEventListener("click", () => {
    confirmDialog("Supprimer le groupe ?", `« ${group.name} », ses ${expenses.length} dépense(s) et tout le journal seront effacés pour tout le monde. Impossible à annuler.`, "Supprimer définitivement", async () => {
      const id = current;
      const refs = [];
      for (const name of ["expenses", "log", "members"]) {
        const snap = await getDocs(sub(id, name));
        snap.docs.forEach(d => refs.push(d.ref));
      }
      // dépenses, journal et membres d'abord, le groupe en dernier : les règles vérifient le créateur sur le groupe
      for (let i = 0; i < refs.length; i += 400) {
        const bt = writeBatch(db);
        refs.slice(i, i + 400).forEach(r => bt.delete(r));
        await bt.commit();
      }
      const last = writeBatch(db); last.delete(groupRef(id)); await last.commit();
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
  if (!group || !isMember()) return;
  if (existing && existing.createdBy !== me) return;
  const ids = Object.keys(members).sort((a, b) => (members[a].joinedAt || 0) - (members[b].joinedAt || 0));
  const sel = new Set(existing ? existing.participants : ids);
  showDialog(`
    <h2>${existing ? "Modifier ma dépense" : "Nouvelle dépense"}</h2>
    <form id="expForm" autocomplete="off" class="stack">
      <div class="field"><label for="eTitle">Pour quoi ?</label><input class="input" id="eTitle" maxlength="80" placeholder="Courses, essence, resto…" value="${esc(existing ? existing.title : "")}" required></div>
      <div class="row">
        <div class="field"><label for="eAmount">Montant payé (${esc(group.currency || "€")})</label><input class="input num" id="eAmount" inputmode="decimal" placeholder="42,50" value="${existing ? (existing.amount / 100).toFixed(2).replace(".", ",") : ""}" required></div>
        <div class="field"><label for="eDate">Date</label><input class="input" type="date" id="eDate" value="${esc(existing ? existing.date : today())}" required></div>
      </div>
      <p class="hint">Payé par <strong>toi</strong> (${esc(nameOf(me))}). Les autres ajoutent leurs propres dépenses.</p>
      <div class="field"><label>Pour qui ? <span class="hint">(partagé à parts égales)</span></label>
        <div class="chips">${ids.map(uid => `<button type="button" class="chip toggle" aria-pressed="${sel.has(uid)}" data-p="${esc(uid)}">${uid === me ? "Moi" : esc(members[uid].name)}</button>`).join("")}</div>
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
    const cur = group.currency;
    const btn = dlgBody.querySelector("button[type=submit]"); btn.disabled = true;
    const bt = writeBatch(db);
    if (existing) {
      bt.update(doc(sub(current, "expenses"), existing.id), { title, amount, participants: p, date });
      const changes = [];
      if (existing.title !== title) changes.push(`titre « ${existing.title} » → « ${title} »`);
      if (existing.amount !== amount) changes.push(`${fmt(existing.amount, cur)} → ${fmt(amount, cur)}`);
      if (existing.date !== date) changes.push("date");
      if (existing.participants.slice().sort().join() !== p.slice().sort().join()) changes.push("participants");
      addLog(bt, current, "edit", `a modifié « ${title} »${changes.length ? " : " + changes.join(", ") : ""}`, existing.id);
    } else {
      const ref = doc(sub(current, "expenses"));
      bt.set(ref, { title, amount, payer: me, participants: p, date, createdAt: Date.now(), createdBy: me });
      addLog(bt, current, "add", `a ajouté « ${title} » (${fmt(amount, cur)})`, ref.id);
    }
    try { await bt.commit(); closeDialog(); }
    catch (e) { err.textContent = errText(e); err.hidden = false; btn.disabled = false; }
  };
  setTimeout(() => { const t = document.getElementById("eTitle"); if (t) t.focus(); }, 30);
}

init();
