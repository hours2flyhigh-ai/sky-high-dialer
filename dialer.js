/* Sky High Dialer — power dialer driving Zoom Phone Smart Embed.
 *
 * Flow per lead:
 *   dial -> (zp-call-ringing-event) ringing -> (zp-call-connected-event) live -> (zp-call-ended-event) talked
 *   dial -> ringing -> ended without connect -> retry (until max attempts) or noanswer
 * While a call is live, or an inbound call is active, the dialer never starts another call.
 * Leads come from one or more sheets (added/removed/switched off in the UI). With several PCs,
 * each phone number is owned by one PC (see ownerOf), so no number is dialed twice.
 * Website version: everything is shared through the online database (cloud.js). The admin
 * login controls sheets, settings and every PC; agent logins only dial, mark sales/DNC and edit details.
 */
(() => {
  "use strict";

  const ZOOM_ORIGIN = "https://applications.zoom.us";
  const ZOOM_URL = ZOOM_ORIGIN + "/integration/phone/embeddablephone/home?originDomain=" + encodeURIComponent(location.origin);
  const DIAL_TIMEOUT_MS = 40000; // no word from Zoom after dialing -> stop and ask the user

  const $ = (id) => document.getElementById(id);
  const iframe = $("zoom-embeddable-phone-iframe");

  // ---------- state ----------
  let leads = [];          // {id, name, phone, display, state, sheet, attempts, status, result, lastCall}
  let sheets = [];         // {id, name, active}  each sheet the dialer pulls leads from
  let dnc = new Set();     // Do Not Call: last 10 digits of numbers that must never be dialed
  const SETTINGS_VERSION = 2;
  let settings = { v: SETTINGS_VERSION, maxAttempts: 2, retryMode: "now", gapSec: 4, hoursGuard: true, pcCount: 1, pcNumber: 1,
    statesOnly: null,      // null = dial every state; otherwise only these state codes
    blankState: true };    // dial customers whose state is unknown
  let running = false;
  let current = null;      // {leadId, callId, connected, startedAt}
  let lastLeadId = null;
  let inboundBusy = false;
  let countdown = null;    // {leadId, endsAt, timer}
  let watchdog = null;
  let zoomSeen = false;
  let focusMode = false;   // customer view: only the current customer + Zoom panel
  // online sync state (see "online sync" below)
  const cloud = { role: null, since: null, serverNow: null, snap: new Map(), dncSnap: new Set(), sheetsSnap: "[]",
    sheetIds: new Set(), configSnap: "", desire: null, lastDesiredAt: undefined, pcs: [], commands: [],
    timer: null, pushTimer: null, busy: false, again: false, started: false };

  // ---------- storage: a local copy per signed-in user (the shared copy is online) ----------
  const storeKey = () => "shd-data:" + ((window.Cloud && Cloud.session && Cloud.session.email) || "local");
  let storeTimer = null;
  const store = {
    async get() { try { return JSON.parse(localStorage.getItem(storeKey()) || "{}"); } catch { return {}; } },
    save() {
      clearTimeout(storeTimer);
      storeTimer = setTimeout(() => {
        try { localStorage.setItem(storeKey(), JSON.stringify({ leads, settings, sheets, dnc: [...dnc] })); } catch { /* full or blocked */ }
      }, 300);
      cloudChanged();
    }
  };

  // ---------- phone helpers ----------
  const digits = (s) => String(s || "").replace(/\D/g, "");
  function toE164(raw) {
    const d = digits(raw);
    if (d.length === 10) return "+1" + d;
    if (d.length === 11 && d[0] === "1") return "+" + d;
    if (d.length > 11) return "+" + d;
    return null;
  }
  function pretty(e164) {
    const d = digits(e164);
    const t = d.length === 11 && d[0] === "1" ? d.slice(1) : d;
    return t.length === 10 ? `(${t.slice(0, 3)}) ${t.slice(3, 6)}-${t.slice(6)}` : e164;
  }
  const last10 = (s) => digits(s).slice(-10);

  // ---------- no-extra-charge guard ----------
  // The plan (US & Canada Unlimited) only covers US and Canada. These +1 area codes are NOT US/Canada
  // (Caribbean countries) or are US territories / premium lines that can be billed per minute.
  const NANP_FOREIGN = new Set(["242","246","264","268","284","345","441","473","649","658","664","721",
    "758","767","784","809","829","849","868","869","876"]);
  const NANP_TERRITORY = new Set(["340","670","671","684","787","939"]);
  const NANP_PREMIUM = /^(900|976|500|52[1-9]|533|544|566|577|588|700|710)$/;
  function blockReason(e164) {
    const d = digits(e164);
    if (d.length !== 11 || d[0] !== "1") return "Not a US/Canada number";
    const area = d.slice(1, 4), exch = d.slice(4, 7);
    if (!/^[2-9]\d\d$/.test(area) || !/^[2-9]\d\d$/.test(exch) || /^\d11$/.test(area)) return "Invalid number";
    if (NANP_FOREIGN.has(area)) return "Caribbean (international, billed)";
    if (NANP_TERRITORY.has(area)) return "US territory (may be billed)";
    if (NANP_PREMIUM.test(area)) return "Premium/special number (may be billed)";
    return "";
  }
  function applyGuard(lead) {
    const why = blockReason(lead.phone);
    if (why && lead.status !== "talked") { lead.status = "blocked"; lead.result = why; }
    return lead;
  }

  // Several PCs: each phone number is owned by exactly one PC, worked out from the number itself
  // (so it doesn't matter what order sheets were added in on each PC).
  function ownerOf(lead) {
    let h = 2166136261;
    const s = last10(lead.phone);
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619) >>> 0; }
    return (h % Math.max(1, settings.pcCount)) + 1;
  }
  const isMine = (l) => ownerOf(l) === settings.pcNumber;
  const sheetOf = (l) => sheets.find((s) => s.id === l.sheet);
  const sheetActive = (l) => { const s = sheetOf(l); return !s || s.active; };
  const isDnc = (l) => dnc.has(last10(l.phone));
  const stateAllowed = (l) => !l.state ? settings.blankState : !settings.statesOnly || settings.statesOnly.includes(l.state);

  function normState(s) {
    const v = String(s || "").trim().toUpperCase();
    if (!v) return "";
    if (window.STATE_TZ[v]) return v;
    return window.STATE_NAMES[v] || "";
  }
  function localHour(lead) {
    const tz = window.STATE_TZ[lead.state];
    if (!tz) return null;
    const h = Number(new Intl.DateTimeFormat("en-US", { timeZone: tz, hour: "numeric", hourCycle: "h23" }).format(new Date()));
    return h;
  }
  function localTimeText(lead) {
    const tz = window.STATE_TZ[lead.state];
    if (!tz) return "—";
    return new Intl.DateTimeFormat("en-US", { timeZone: tz, hour: "numeric", minute: "2-digit" }).format(new Date()) + " " + lead.state;
  }
  function inHours(lead) {
    if (!settings.hoursGuard) return true;
    const h = localHour(lead);
    if (h === null) return true; // no state column: can't check
    return h >= 8 && h < 21;
  }

  // ---------- import ----------
  function parseDelimited(text) {
    const firstLine = text.split(/\r?\n/, 1)[0] || "";
    const delim = firstLine.includes("\t") ? "\t" : ",";
    const rows = [];
    let row = [], field = "", q = false;
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (q) {
        if (c === '"' && text[i + 1] === '"') { field += '"'; i++; }
        else if (c === '"') q = false;
        else field += c;
      } else if (c === '"') q = true;
      else if (c === delim) { row.push(field); field = ""; }
      else if (c === "\n" || c === "\r") {
        if (c === "\r" && text[i + 1] === "\n") i++;
        row.push(field); rows.push(row); row = []; field = "";
      } else field += c;
    }
    if (field || row.length) { row.push(field); rows.push(row); }
    return rows.filter((r) => r.some((v) => String(v).trim()));
  }

  // Full customer details shown on the card, in this order. "re" matches the label in a
  // "Label: value" block or a column header (lower-cased, spaces collapsed).
  const DETAIL_FIELDS = [
    { key: "phone",     label: "Phone Number",      re: /^(phone( number| no\.?| #)?|cell( phone)?|mobile( number)?|tel(ephone)?|number)$/ },
    { key: "name",      label: "Full Name",         re: /^(full name|name|customer( name)?|client( name)?)$/ },
    { key: "dob",       label: "DOB",               re: /^(dob|d\.o\.b\.?|date of birth|birth ?date)$/ },
    { key: "age",       label: "Age",               re: /^age$/ },
    { key: "gender",    label: "Gender",            re: /^(gender|sex)$/ },
    { key: "bornState", label: "Born State",        re: /^(born state|birth ?state|state of birth|place of birth)$/ },
    { key: "height",    label: "Height",            re: /^height$/ },
    { key: "weight",    label: "Weight",            re: /^weight$/ },
    { key: "smoking",   label: "Smoking Status",    re: /^(smok(ing|er)( status)?|tobacco( use| status)?)$/ },
    { key: "health",    label: "Health Issues",     re: /^(health( issues?| conditions?)?|medical( issues?| conditions?)?|conditions?)$/ },
    { key: "meds",      label: "Medications",       re: /^(medications?|medicines?|meds)$/ },
    { key: "address",   label: "Mailing Address",   re: /^(mailing address|address|home address|street( address)?)$/ },
    { key: "plan",      label: "Plan Type",         re: /^(plan( type)?|policy( type)?)$/ },
    { key: "carrier",   label: "Carrier",           re: /^(carrier|insurance( company)?|company)$/ },
    { key: "ssn",       label: "SSN",               re: /^(ssn|ss#|ss ?no\.?|social( security)?( number| no\.?| #)?)$/ },
    { key: "benef",     label: "Beneficiary",       re: /^beneficiar(y|ies)$/ },
    { key: "draft",     label: "Future Draft Date", re: /^((future |next )?draft( date)?)$/ },
    { key: "acctType",  label: "Account Type",      re: /^account type$/ },
    { key: "bank",      label: "Bank Name",         re: /^bank( name)?$/ },
    { key: "routing",   label: "Routing Number",    re: /^(routing( number| no\.?| #)?|aba( number)?)$/ },
    { key: "checking",  label: "Checking Account",  re: /^(checking( account)?( number| no\.?| #)?|account( number| no\.?| #)?|acct( number| no\.?| #)?)$/ }
  ];
  const normLabel = (t) => String(t || "").toLowerCase().replace(/[_\s]+/g, " ").replace(/\s*[:#-]\s*$/, "").trim();
  const fieldFor = (label) => { const n = normLabel(label); return DETAIL_FIELDS.find((f) => f.re.test(n)); };
  const COMMENT_LABEL = /^(comments?|notes?|remarks?)$/;
  const STATE_LABEL = /^(state|mailing state|home state)$/;
  // Mailing address like "12 Main St, Dover, DE 19901" -> "DE" (so calling hours still work without a State column)
  function stateFromAddress(addr) {
    const m = String(addr || "").match(/\b([A-Za-z]{2})\.?[\s,]+\d{5}(?:-\d{4})?\s*$/) || String(addr || "").match(/,\s*([A-Za-z]{2})\b/);
    return m ? normState(m[1]) : "";
  }

  // Sheets where each customer is one cell of "Label: value" lines (Phone Number:, Full Name:, DOB:, ...).
  const BLOCK_PHONE = /(?:^|\n)[ \t]*(?:phone(?:[ \t]*number)?|number|cell|mobile)[ \t]*[:#-][ \t]*([+\d().\-\s]{7,20})/i;
  function parseBlock(cell) {
    const det = {}; const comments = []; let state = ""; let check = ""; let inComments = false;
    for (const raw of String(cell).split(/\r?\n/)) {
      const line = raw.trim();
      if (!line) continue;
      const m = line.match(/^([A-Za-z][A-Za-z .#/()-]{0,40}?)[ \t]*:[ \t]*(.*)$/);
      if (m) {
        const lab = normLabel(m[1]);
        if (COMMENT_LABEL.test(lab)) { inComments = true; if (m[2].trim()) comments.push(m[2].trim()); continue; }
        if (STATE_LABEL.test(lab)) { state = normState(m[2]); inComments = false; continue; }
        const f = fieldFor(lab);
        if (f) { if (!det[f.key]) det[f.key] = m[2].trim(); inComments = false; continue; }
        if (/^(check|verify)\b/.test(lab)) { check = m[2].trim(); inComments = false; continue; }
      } else if (COMMENT_LABEL.test(normLabel(line))) { inComments = true; continue; }
      comments.push(line); // anything that isn't a known field counts as a comment
    }
    return { det, comments: comments.join("\n"), state, check };
  }
  function buildBlockLeads(rows) {
    const out = [];
    const seen = new Set();
    let dup = 0;
    for (const r of rows) {
      for (const cell of r) {
        if (!BLOCK_PHONE.test(cell)) continue;
        const { det, comments, state, check } = parseBlock(cell);
        const phone = toE164(det.phone || String(cell).match(BLOCK_PHONE)[1]);
        if (!phone) continue;
        if (seen.has(phone)) { dup++; continue; }
        seen.add(phone);
        out.push({ id: phone, name: det.name || "", phone, display: pretty(phone),
          state: state || stateFromAddress(det.address), address: det.address || "", age: det.age || "", gender: det.gender || "",
          check, details: det, comments,
          attempts: 0, status: "pending", result: "", lastCall: "" });
      }
    }
    return { out, bad: 0, dup, hasState: out.some((l) => l.state) };
  }

  function buildLeads(rows) {
    if (!rows.length) throw new Error("No rows found.");
    // Notes-style sheet ("Phone Number: ..." inside cells) only when the first row isn't a normal header with a phone column.
    const hasPhoneHeader = (rows[0] || []).some((h) => { const f = fieldFor(h); return f && f.key === "phone"; });
    if (!hasPhoneHeader && rows.slice(0, 50).some((r) => r.some((c) => BLOCK_PHONE.test(c)))) {
      const res = buildBlockLeads(rows);
      if (res.out.length) return res;
    }
    const head = rows[0].map((h) => String(h).trim().toLowerCase());
    const find = (re, not) => head.findIndex((h) => re.test(h) && !(not && not.test(h)));
    const sensitive = /account|routing|social|ssn|bank|eft|beneficiary/;
    let phoneCol = find(/phone|number|cell|mobile|tel/, sensitive);
    let nameCol = find(/^name$|full name|client|customer|lead/, /first|last/);
    const firstCol = find(/first/);
    const lastCol = find(/last/);
    if (nameCol < 0 && firstCol < 0) nameCol = find(/name/);
    const stateCol = find(/state/, /birth|born/);
    // Extra customer details shown on the customer card while dialing (never sensitive columns).
    const addrCol = find(/address|street/, sensitive);
    const ageCol = find(/^age\b/);
    const genderCol = find(/^gender|^sex$/);
    const checkCol = find(/^check|verify/, sensitive);
    // Columns matching the full detail list (Phone Number, Full Name, DOB ... Checking Account) and Comments.
    const detCols = {};
    head.forEach((h, i) => { const f = fieldFor(h); if (f && detCols[f.key] === undefined) detCols[f.key] = i; });
    const commentCol = head.findIndex((h) => COMMENT_LABEL.test(normLabel(h)));
    const cell = (r, c) => (c >= 0 ? String(r[c] || "").trim() : "");
    let body = rows.slice(1);

    if (phoneCol < 0) {
      // No recognisable header: treat every row as data and pick the first column that looks like a phone.
      body = rows;
      const sample = rows.slice(0, 20);
      for (let c = 0; c < (rows[0] || []).length; c++) {
        if (sample.filter((r) => toE164(r[c])).length >= Math.ceil(sample.length / 2)) { phoneCol = c; break; }
      }
      if (phoneCol < 0) throw new Error("Couldn't find a phone column. Add a header row with a column named Phone or Number.");
    }

    const out = [];
    const seen = new Set();
    let bad = 0, dup = 0;
    for (const r of body) {
      const phone = toE164(r[phoneCol]);
      if (!phone) { bad++; continue; }
      if (seen.has(phone)) { dup++; continue; }
      seen.add(phone);
      let name = nameCol >= 0 ? r[nameCol] : [r[firstCol], r[lastCol]].filter(Boolean).join(" ");
      const details = {};
      for (const k in detCols) { const v = cell(r, detCols[k]); if (v) details[k] = v; }
      const address = cell(r, addrCol);
      out.push({
        id: phone, name: String(name || "").trim(), phone, display: pretty(phone),
        state: (stateCol >= 0 ? normState(r[stateCol]) : "") || stateFromAddress(address),
        address, age: cell(r, ageCol), gender: cell(r, genderCol), check: cell(r, checkCol),
        details, comments: cell(r, commentCol),
        attempts: 0, status: "pending", result: "", lastCall: ""
      });
    }
    if (!out.length) throw new Error("No valid US phone numbers found in that data.");
    return { out, bad, dup, hasState: stateCol >= 0 || out.some((l) => l.state) };
  }

  function addSheet(text, name) { addSheetRows(parseDelimited(text), name); }

  async function addFile(f) {
    const msg = $("importMsg");
    if (!f) return;
    msg.className = "msg"; msg.textContent = `Reading ${f.name}…`;
    try {
      const base = f.name.replace(/\.[^.]+$/, "");
      const name = $("sheetName").value.trim() || base;
      if (/\.xlsx$/i.test(f.name)) {
        const { rows } = await window.readXlsx(await f.arrayBuffer());
        addSheetRows(rows, name);
      } else if (/\.(csv|tsv|txt)$/i.test(f.name)) {
        addSheetRows(parseDelimited(await f.text()), name);
      } else {
        throw new Error("Use an Excel (.xlsx) or CSV file. Older .xls files: open in Excel and Save As .xlsx.");
      }
    } catch (err) {
      msg.className = "msg bad"; msg.textContent = err.message;
    }
    $("fileInput").value = "";
  }

  function addSheetRows(rows, name) {
    const msg = $("importMsg");
    try {
      const { out, bad, dup, hasState } = buildLeads(rows);
      const have = new Set(leads.map((l) => l.id));
      const fresh = out.filter((l) => !have.has(l.id)).map(applyGuard);
      const blocked = fresh.filter((l) => l.status === "blocked").length;
      const already = out.length - fresh.length;
      if (!fresh.length) throw new Error("Every number in that sheet is already loaded.");
      const sheet = { id: "s" + Date.now().toString(36), name: (name || "").trim() || `Sheet ${sheets.length + 1}`, active: true };
      sheets.push(sheet);
      fresh.forEach((l) => { l.sheet = sheet.id; leads.push(l); });
      store.save(); render();
      msg.className = "msg good";
      msg.textContent = `Added "${sheet.name}": ${fresh.length} leads.` +
        (bad ? ` Skipped ${bad} rows without a valid number.` : "") +
        (dup + already ? ` Skipped ${dup + already} duplicates.` : "") +
        (blocked ? ` ${blocked} won't be dialed (not US/Canada or could be billed extra).` : "") +
        (hasState ? "" : " No State column, so calling-hours check is off for these leads.");
      $("sheetName").value = ""; $("pasteBox").value = ""; $("sheetUrl").value = "";
      setTimeout(() => { $("importPanel").hidden = true; }, 2500);
    } catch (err) {
      msg.className = "msg bad";
      msg.textContent = err.message;
    }
  }

  let armedRemove = null;
  function removeSheet(id) {
    const sheet = sheets.find((s) => s.id === id);
    if (!sheet) return;
    if (current && (leadById(current.leadId) || {}).sheet === id) {
      setStatus("wait", `Can't remove "${sheet.name}" while a call from it is in progress.`);
      return;
    }
    if (countdown && (leadById(countdown.leadId) || {}).sheet === id) cancelCountdown();
    leads = leads.filter((l) => l.sheet !== id);
    sheets = sheets.filter((s) => s.id !== id);
    armedRemove = null;
    store.save(); render();
    if (running && !current && !inboundBusy && !countdown) scheduleNext();
  }

  async function fetchSheet(url) {
    const msg = $("importMsg");
    const m = String(url).match(/\/spreadsheets\/d\/([a-zA-Z0-9-_]+)/);
    if (!m) { msg.className = "msg bad"; msg.textContent = "That doesn't look like a Google Sheets link."; return; }
    const gid = (String(url).match(/[#&?]gid=(\d+)/) || [])[1] || "0";
    msg.className = "msg"; msg.textContent = "Loading sheet…";
    try {
      const res = await fetch(`https://docs.google.com/spreadsheets/d/${m[1]}/export?format=csv&gid=${gid}`, { credentials: "include" });
      const text = await res.text();
      if (!res.ok || /^\s*<!DOCTYPE html|<html/i.test(text)) {
        throw new Error("Google didn't return the sheet. Make sure you're signed in to Google in this Chrome and can open the sheet, or use Option B.");
      }
      addSheet(text, $("sheetName").value);
    } catch (err) {
      msg.className = "msg bad";
      msg.textContent = err.message.startsWith("Google") ? err.message : "Couldn't load the sheet (" + err.message + "). Use Option B instead.";
    }
  }

  // ---------- Zoom Smart Embed bridge ----------
  function zoomPost(msg) {
    try { iframe.contentWindow.postMessage(msg, ZOOM_ORIGIN); } catch (e) { console.warn("postMessage failed", e); }
  }
  function initZoom() {
    zoomPost({
      type: "zp-init-config",
      data: { enableSavingLog: false, enableAutoLog: false, enableContactSearching: false, enableContactMatching: false }
    });
  }
  iframe.addEventListener("load", () => {
    setTimeout(initZoom, 1500);
    if (!zoomSeen) $("zoomState").textContent = "Loaded · sign in if asked";
  });
  iframe.src = ZOOM_URL;

  window.addEventListener("message", (e) => {
    if (e.origin !== ZOOM_ORIGIN || !e.data || typeof e.data !== "object") return;
    if (!zoomSeen) { zoomSeen = true; $("zoomState").textContent = "Connected"; }
    const type = e.data.type;
    const d = e.data.data || e.data;
    switch (type) {
      case "zp-call-ringing-event": onRinging(d); break;
      case "zp-call-connected-event": onConnected(d); break;
      case "zp-call-ended-event": onEnded(d); break;
      case "zp-call-log-completed-event": onLog(d); break;
    }
  });

  const isInbound = (d) => String(d.direction || "").toLowerCase() === "inbound";
  const calleeMatches = (d, lead) => {
    const n = d.callee && (d.callee.phoneNumber || d.callee.number);
    return !n || last10(n) === last10(lead.phone);
  };
  const leadById = (id) => leads.find((l) => l.id === id);

  function onRinging(d) {
    if (isInbound(d)) { inboundBusy = true; cancelCountdown(); setStatus("wait", "Incoming call. Dialer is holding."); return; }
    const lead = current && leadById(current.leadId);
    if (!lead || !calleeMatches(d, lead)) return;
    clearTimeout(watchdog);
    current.callId = d.callId;
    lead.status = "ringing";
    setStatus("dialing", `Ringing ${lead.name || lead.display} (try ${lead.attempts} of ${settings.maxAttempts})`);
    render();
  }

  function onConnected(d) {
    if (isInbound(d)) { inboundBusy = true; cancelCountdown(); setStatus("live", "On an incoming call. Dialer is holding."); return; }
    const lead = current && leadById(current.leadId);
    if (!lead || !calleeMatches(d, lead)) return;
    clearTimeout(watchdog);
    current.connected = true;
    lead.status = "live";
    setStatus("live", `Connected: ${lead.name || lead.display}. Dialer waits until you hang up.`);
    render();
  }

  function onEnded(d) {
    if (isInbound(d)) {
      inboundBusy = false;
      if (!current) afterCall();
      return;
    }
    const lead = current && leadById(current.leadId);
    if (!lead || !calleeMatches(d, lead)) return;
    clearTimeout(watchdog);
    lead.lastCall = new Date().toLocaleString();
    if (lead.sale) {
      lead.status = "sale"; lead.result = "Sale made";
    } else if (current.connected) {
      lead.status = "talked";
      lead.result = "Answered";
    } else {
      lead.result = d.result === "rejected" ? "Rejected" : "No answer";
      lead.status = lead.attempts >= settings.maxAttempts ? "noanswer" : "retry";
    }
    current = null;
    store.save(); render();
    afterCall();
  }

  function onLog(d) {
    // Richer result (Busy, Voicemail, Wrong Number...) arrives a little later.
    const n = d.callee && (d.callee.number || d.callee.phoneNumber);
    if (!n || isInbound(d)) return;
    const lead = leads.find((l) => last10(l.phone) === last10(n));
    if (lead && d.result && lead.status !== "live") { lead.result = String(d.result); store.save(); render(); }
  }

  // ---------- dialing engine ----------
  function candidates() {
    return leads.filter((l) => (l.status === "pending" || l.status === "retry") && l.attempts < settings.maxAttempts
      && isMine(l) && sheetActive(l) && !isDnc(l) && !l.sale && stateAllowed(l));
  }
  function pickNext() {
    const c = candidates();
    const ok = c.filter(inHours);
    if (!ok.length) return { lead: null, blocked: c.length };
    if (settings.retryMode === "now") {
      const last = ok.find((l) => l.id === lastLeadId && l.status === "retry");
      if (last) return { lead: last };
      return { lead: ok[0] };
    }
    return { lead: ok.find((l) => l.status === "pending") || ok[0] };
  }

  function afterCall() {
    if (!running || current || inboundBusy) { if (!running && !current) setStatus("idle", "Paused."); return; }
    scheduleNext();
  }

  function scheduleNext() {
    cancelCountdown();
    const { lead, blocked } = pickNext();
    if (!lead) {
      running = false; setFocus(false); syncButtons();
      setStatus("idle", blocked
        ? `Stopped: ${blocked} leads left, but it's outside 8am–9pm in their time zones.`
        : "Done. Every lead on your sheets has been called.");
      return;
    }
    const endsAt = Date.now() + settings.gapSec * 1000;
    countdown = { leadId: lead.id, endsAt, timer: null };
    const tick = () => {
      if (!countdown) return;
      const s = Math.max(0, Math.ceil((countdown.endsAt - Date.now()) / 1000));
      setStatus("wait", `Next: ${lead.name || lead.display} in ${s}s`);
      if (s <= 0) { const id = countdown.leadId; countdown = null; dial(leadById(id)); }
      else countdown.timer = setTimeout(tick, 250);
    };
    tick();
    render();
  }
  function cancelCountdown() { if (countdown) { clearTimeout(countdown.timer); countdown = null; } }

  function dial(lead) {
    if (!lead || current || inboundBusy) return;
    if (isDnc(lead)) {
      setStatus("error", `Not dialed: ${lead.display} is on your Do Not Call list.`);
      render();
      if (running) setTimeout(afterCall, 1500);
      return;
    }
    const why = blockReason(lead.phone);
    if (why) {
      lead.status = "blocked"; lead.result = why; store.save(); render();
      setStatus("error", `Not dialed: ${lead.display} is "${why}". Your plan only covers US & Canada.`);
      if (running) setTimeout(afterCall, 1500);
      return;
    }
    lead.attempts += 1;
    lead.status = "dialing";
    lastLeadId = lead.id;
    current = { leadId: lead.id, callId: null, connected: false, startedAt: Date.now() };
    setStatus("dialing", `Dialing ${lead.name || lead.display} (try ${lead.attempts} of ${settings.maxAttempts})`);
    zoomPost({ type: "zp-make-call", number: lead.phone, autoDial: true, data: { number: lead.phone, autoDial: true } });
    clearTimeout(watchdog);
    watchdog = setTimeout(() => {
      if (!current || current.leadId !== lead.id || lead.status !== "dialing") return;
      lead.status = "error"; lead.result = "Zoom didn't start the call";
      current = null; running = false; syncButtons();
      setStatus("error", "Zoom didn't start the call. Check that you're signed in on the right, then press Start.");
      store.save(); render();
    }, DIAL_TIMEOUT_MS);
    store.save(); render();
  }

  function start(fromCloud) {
    if (!leads.length) { if (cloud.role === "admin") $("importPanel").hidden = false; setStatus("idle", cloud.role === "admin" ? "Add a sheet first." : "No customers yet. The admin adds the sheets."); return; }
    running = true; setFocus(true); syncButtons();
    if (fromCloud !== true) cloudDesire("run");
    if (current) { setStatus("live", "On a call. Dialing resumes after it ends."); return; }
    if (inboundBusy) { setStatus("wait", "Incoming call. Dialer is holding."); return; }
    scheduleNext();
  }
  function pause(fromCloud) {
    running = false; syncButtons();
    if (fromCloud !== true) cloudDesire("pause");
    cancelCountdown();
    setStatus(current ? "live" : "idle", current ? "Paused. Finish this call; no new calls will start." : "Paused.");
    render();
  }
  function skip() {
    if (countdown) {
      const lead = leadById(countdown.leadId);
      cancelCountdown();
      if (lead) { lead.status = "skipped"; lead.result = "Skipped"; }
      store.save();
      if (running) scheduleNext(); else render();
      return;
    }
    if (current) {
      const lead = leadById(current.leadId);
      if (lead && lead.status === "live") { setStatus("live", "You're on a live call. Hang up in the Zoom panel to move on."); return; }
      clearTimeout(watchdog);
      if (lead) { lead.status = "skipped"; lead.result = "Skipped"; }
      current = null;
      store.save(); render();
      setStatus("wait", "Skipped. Hang up the ringing call in the Zoom panel if it's still going.");
      if (running) setTimeout(afterCall, 1500);
    }
  }

  // ---------- UI ----------
  function setStatus(state, text) { $("statusBox").dataset.state = state; $("statusText").textContent = text; }
  function syncButtons() { $("btnStart").hidden = running; $("btnPause").hidden = !running; }

  const LABEL = { pending: "Not called", dialing: "Dialing", ringing: "Ringing", live: "On call", talked: "Answered",
    retry: "Will retry", noanswer: "No answer", skipped: "Skipped", error: "Error", blocked: "Not dialed", sale: "Sale made" };

  function render() {
    const tbody = $("rows");
    tbody.textContent = "";
    $("empty").hidden = leads.length > 0;
    renderSheets();
    renderCard();
    renderDnc();
    renderStates();
    const rb = $("btnRestart");
    rb.textContent = armedRestart === "all" ? "Click again: clears all results" : "Start over";
    rb.classList.toggle("armed", armedRestart === "all");
    rb.disabled = !leads.length || !!current;
    const counts = {};
    let shown = 0, others = 0;
    leads.forEach((l) => {
      const theirs = !isMine(l);
      if (theirs && cloud.role !== "admin") { others++; return; }
      shown++;
      counts[l.status] = (counts[l.status] || 0) + 1;
      const tr = document.createElement("tr");
      if ((current && current.leadId === l.id) || (countdown && countdown.leadId === l.id)) tr.className = "current";
      const td = (cls, text) => { const c = document.createElement("td"); if (cls) c.className = cls; c.textContent = text; tr.appendChild(c); return c; };
      td("num", shown);
      td("name", l.name || "—");
      td("tel", l.display);
      const sh = sheetOf(l);
      td("sheetname", (sh ? sh.name : "—") + (settings.pcCount > 1 ? ` · PC ${ownerOf(l)}` : ""));
      const lt = td("", localTimeText(l));
      if (l.state && settings.hoursGuard && !inHours(l)) lt.className = "lt-off";
      td("tries", `${l.attempts}/${settings.maxAttempts}`);
      const res = td("", "");
      const pill = document.createElement("span");
      const waiting = l.status === "pending" || l.status === "retry";
      const dncd = isDnc(l) && (waiting || l.status === "blocked");
      const sheetOff = waiting && !dncd && !sheetActive(l);
      const stateOff = waiting && !dncd && !sheetOff && !stateAllowed(l);
      const outOfHours = waiting && !dncd && !sheetOff && !stateOff && !inHours(l);
      pill.className = "pill " + (dncd ? "blocked" : sheetOff || stateOff || outOfHours ? "later" : l.status);
      pill.textContent = dncd ? "Do not call" : sheetOff ? "Sheet off" : stateOff ? "State off" : outOfHours ? "Outside hours" : (l.status === "noanswer" || l.status === "error" || l.status === "blocked") && l.result ? l.result : LABEL[l.status] || l.status;
      if (l.result && l.status === "retry") pill.title = l.result;
      res.appendChild(pill);
      const act = td("", "");
      const wrap = document.createElement("div"); wrap.className = "row-actions";
      const btn = (label, fn, title) => { const b = document.createElement("button"); b.type = "button"; b.className = "btn tiny"; b.textContent = label; if (title) b.title = title; b.addEventListener("click", fn); wrap.appendChild(b); return b; };
      const busy = !!current || inboundBusy;
      const callBtn = btn("Call", () => { cancelCountdown(); dial(l); }, "Call this lead now");
      callBtn.disabled = busy || theirs;
      if (theirs) callBtn.title = `PC ${ownerOf(l)} dials this customer`;
      if (l.status === "blocked" || isDnc(l)) callBtn.disabled = true;
      if (!["pending", "dialing", "ringing", "live", "blocked"].includes(l.status)) {
        btn("Retry", () => { l.status = "retry"; if (l.attempts >= settings.maxAttempts) l.attempts = settings.maxAttempts - 1; store.save(); render(); }, "Put back in the queue");
      }
      const dncBtn = btn(isDnc(l) ? "Undo DNC" : "DNC", () => toggleDnc(l), isDnc(l) ? "Take this number off Do Not Call" : "Never call this number");
      dncBtn.classList.add("danger");
      const saleBtn = btn(l.sale ? "Undo sale" : "Sale", () => toggleSale(l), l.sale ? "Take the sale mark off" : "Mark this customer as a sale (never auto-dialed again)");
      saleBtn.classList.add("sale");
      act.appendChild(wrap);
      tbody.appendChild(tr);
    });
    const c = $("counts"); c.textContent = "";
    const chip = (t) => { const s = document.createElement("span"); s.className = "chip"; s.textContent = t; c.appendChild(s); };
    if (leads.length) {
      if (settings.pcCount > 1) chip(`PC ${settings.pcNumber} of ${settings.pcCount}`);
      if (settings.statesOnly) chip(`Dialing ${settings.statesOnly.length} state${settings.statesOnly.length === 1 ? "" : "s"}`);
      chip(`${shown} leads`);
      chip(`${candidates().length} to call`);
      chip(`${counts.talked || 0} answered`);
      chip(`${counts.noanswer || 0} no answer`);
      if (counts.blocked) chip(`${counts.blocked} not dialed (would cost extra)`);
      const dncMine = leads.filter((l) => isMine(l) && isDnc(l)).length;
      if (dncMine) chip(`${dncMine} on Do Not Call`);
      if (others) chip(`${others} on other PCs`);
    }
  }

  // ---------- Do Not Call list ----------
  const PHONE_IN_TEXT = /(?:\+?1[\s.\-]?)?\(?\d{3}\)?[\s.\-]?\d{3}[\s.\-]?\d{4}/g;
  function numbersIn(text) {
    const found = [];
    for (const m of String(text || "").match(PHONE_IN_TEXT) || []) { const e = toE164(m); if (e) found.push(last10(e)); }
    return found;
  }
  function addDnc(list, source) {
    let added = 0;
    for (const n of list) if (n.length === 10 && !dnc.has(n)) { dnc.add(n); added++; }
    store.save(); render();
    const msg = $("dncMsg");
    msg.className = added ? "msg good" : "msg";
    msg.textContent = added ? `Added ${added} number${added === 1 ? "" : "s"} to Do Not Call${source ? " from " + source : ""}.` : "Those numbers are already on the list (or none were found).";
    return added;
  }
  function toggleSale(lead) {
    lead.sale = !lead.sale;
    const onLine = current && current.leadId === lead.id;
    if (lead.sale) {
      lead.saleAt = new Date().toLocaleString();
      if (!onLine) { lead.prevStatus = lead.status; lead.status = "sale"; }
      lead.result = "Sale made";
      if (countdown && countdown.leadId === lead.id) { cancelCountdown(); if (running) scheduleNext(); }
    } else {
      lead.saleAt = "";
      if (!onLine) lead.status = lead.prevStatus && lead.prevStatus !== "sale" ? lead.prevStatus : "talked";
      lead.result = lead.status === "talked" ? "Answered" : (LABEL[lead.status] || "");
    }
    store.save(); render();
  }
  function toggleDnc(lead) {
    const n = last10(lead.phone);
    if (dnc.has(n)) dnc.delete(n); else dnc.add(n);
    store.save(); render();
  }
  async function addDncFile(f) {
    if (!f) return;
    const msg = $("dncMsg");
    try {
      let rows;
      if (/\.xlsx$/i.test(f.name)) rows = (await window.readXlsx(await f.arrayBuffer())).rows;
      else if (/\.(csv|tsv|txt)$/i.test(f.name)) rows = parseDelimited(await f.text());
      else throw new Error("Use an Excel (.xlsx) or CSV file.");
      const nums = [];
      for (const r of rows) for (const cell of r) nums.push(...numbersIn(cell));
      addDnc(nums, f.name);
    } catch (err) { msg.className = "msg bad"; msg.textContent = err.message; }
    $("dncFile").value = "";
  }
  function renderDnc() {
    $("dncCount").textContent = dnc.size ? `${dnc.size} number${dnc.size === 1 ? "" : "s"}` : "empty";
    const box = $("dncList"); box.textContent = "";
    const q = digits($("dncSearch").value);
    const list = [...dnc].filter((n) => !q || n.includes(q)).sort();
    for (const n of list.slice(0, 300)) {
      const item = document.createElement("span"); item.className = "dnc-item";
      const t = document.createElement("span"); t.textContent = pretty("+1" + n);
      const x = document.createElement("button"); x.type = "button"; x.className = "dnc-x"; x.textContent = "×";
      x.title = "Remove from Do Not Call"; x.setAttribute("aria-label", "Remove " + pretty("+1" + n) + " from Do Not Call");
      x.addEventListener("click", () => { dnc.delete(n); store.save(); render(); });
      item.append(t, x); box.appendChild(item);
    }
    if (list.length > 300) { const more = document.createElement("span"); more.className = "hint"; more.textContent = `…and ${list.length - 300} more. Search to find one.`; box.appendChild(more); }
  }

  // ---------- start over ----------
  // Puts every customer (or one sheet's customers) back to "Not called" so dialing restarts from the top.
  // Do Not Call numbers, sales and numbers blocked for extra cost stay excluded.
  let armedRestart = null;
  function restart(sheetId) {
    if (current) { setStatus("wait", "Finish the current call first, then Start over."); return; }
    cancelCountdown();
    let n = 0;
    for (const l of leads) {
      if (sheetId && l.sheet !== sheetId) continue;
      if (l.status === "blocked" && blockReason(l.phone)) continue;
      if (l.sale) continue; // sales are never reset or redialed
      l.attempts = 0; l.status = "pending"; l.result = ""; l.lastCall = ""; n++;
    }
    lastLeadId = null; armedRestart = null;
    store.save(); render();
    setStatus(running ? "wait" : "idle", `Started over: ${n} customers set back to "Not called".` + (running ? "" : " Press Start dialing."));
    maybeResume();
  }
  function armRestart(key, btn, label) {
    if (armedRestart === key) { restart(key === "all" ? null : key); return; }
    armedRestart = key; render();
    setTimeout(() => { if (armedRestart === key) { armedRestart = null; render(); } }, 4000);
  }

  // ---------- state filter ----------
  function stateCounts() {
    const m = new Map(); let blank = 0;
    for (const l of leads) {
      if (!isMine(l) || isDnc(l)) continue;
      const waiting = (l.status === "pending" || l.status === "retry") && l.attempts < settings.maxAttempts;
      const k = l.state || "";
      if (!k) { if (waiting) blank++; continue; }
      const e = m.get(k) || { total: 0, left: 0 };
      e.total++; if (waiting) e.left++;
      m.set(k, e);
    }
    return { m, blank };
  }
  function setStates(list) { settings.statesOnly = list; store.save(); render(); maybeResume(); }
  function maybeResume() { if (running && !current && !inboundBusy && !countdown) scheduleNext(); }
  function renderStates() {
    const grid = $("stateGrid"); if (!grid) return;
    grid.textContent = "";
    const { m, blank } = stateCounts();
    // Every US state (plus DC and Puerto Rico), whether or not it's on a loaded sheet.
    const nameOf = {};
    for (const [n, c] of Object.entries(window.STATE_NAMES)) if (!nameOf[c] || n.length > nameOf[c].length) nameOf[c] = n;
    const title = (c) => (nameOf[c] || c).toLowerCase().replace(/\b\w/g, (x) => x.toUpperCase());
    const codes = Object.keys(window.STATE_TZ).sort((a, b) => title(a).localeCompare(title(b)));
    $("stateSummary").textContent = settings.statesOnly
      ? `${settings.statesOnly.length} of ${codes.length} selected` : `All ${codes.length} selected`;
    for (const code of codes) {
      const e = m.get(code) || { total: 0, left: 0 };
      const lab = document.createElement("label");
      const on = !settings.statesOnly || settings.statesOnly.includes(code);
      lab.className = "state-opt" + (on ? "" : " off");
      const cb = document.createElement("input"); cb.type = "checkbox"; cb.checked = on;
      cb.addEventListener("change", () => {
        const cur = new Set(settings.statesOnly || codes);
        if (cb.checked) cur.add(code); else cur.delete(code);
        setStates(codes.every((c) => cur.has(c)) ? null : [...cur]);
      });
      const tz = window.STATE_TZ[code];
      const h = tz ? Number(new Intl.DateTimeFormat("en-US", { timeZone: tz, hour: "numeric", hourCycle: "h23" }).format(new Date())) : null;
      const time = tz ? new Intl.DateTimeFormat("en-US", { timeZone: tz, hour: "numeric", minute: "2-digit" }).format(new Date()) : "";
      const name = document.createElement("b"); name.textContent = code;
      const full = document.createElement("span"); full.className = "state-name"; full.textContent = title(code);
      const meta = document.createElement("span"); meta.className = "state-meta";
      meta.textContent = `${e.left} · ${time}`;
      meta.title = `${e.left} customers left to call in ${title(code)}; local time ${time}`;
      if (!e.total) lab.classList.add("nolead");
      if (h !== null && (h < 8 || h >= 21)) { meta.classList.add("lt-off"); meta.title = "Outside 8am–9pm there right now"; }
      lab.append(cb, name, full, meta);
      grid.appendChild(lab);
    }
    $("blankState").checked = settings.blankState;
    $("blankStateCount").textContent = `${blank} left`;
  }

  function setFocus(on) {
    focusMode = on;
    document.body.classList.toggle("focus-mode", on);
    $("btnView").textContent = on ? "Show all options" : "Customer view";
    $("btnView").title = on ? "Show sheets, settings and the full list" : "Show only the customer and the Zoom panel";
    renderCard();
  }

  // Which customer the card shows: the one on the line, else the one about to be dialed, else the last one called.
  let shownLeadId = null; // the customer on the card stays there (also while paused) until another call starts
  function cardLead() {
    if (current) return leadById(current.leadId);
    if (countdown) return leadById(countdown.leadId);
    return (shownLeadId && leadById(shownLeadId)) || (lastLeadId ? leadById(lastLeadId) : null);
  }
  // ---------- editable customer details ----------
  // Every field on the card can be changed; changes are saved right away and kept (also after pause or a reload).
  const MULTI = new Set(["health", "meds", "address", "benef"]);
  let editorFor = null;
  function detailsOf(l) {
    const det = l.details || (l.details = {});
    if (!det.phone) det.phone = l.display;
    if (!det.name && l.name) det.name = l.name;
    if (!det.address && l.address) det.address = l.address;
    if (!det.age && l.age) det.age = l.age;
    if (!det.gender && l.gender) det.gender = l.gender;
    return det;
  }
  let saveTimer = null;
  const saveSoon = () => { clearTimeout(saveTimer); saveTimer = setTimeout(() => store.save(), 400); };
  function applyEdit(l, key, val) {
    const det = detailsOf(l);
    det[key] = val;
    if (key === "name") l.name = val.trim();
    if (key === "age") l.age = val.trim();
    if (key === "gender") l.gender = val.trim();
    if (key === "address") { l.address = val.trim(); if (!l.stateManual) { const st = stateFromAddress(val); if (st) l.state = st; } }
    if (key === "phone") {
      const e = toE164(val);
      if (e) { l.phone = e; l.display = pretty(e); $("cPhone").textContent = l.display; }
    }
    if (key === "comments") l.comments = val;
    if (key === "state") { const st = normState(val); l.state = st; l.stateManual = true; }
    saveSoon();
  }
  function grow(t) { t.style.height = "auto"; t.style.height = t.scrollHeight + 2 + "px"; }
  function makeInput(l, key, value, multi, placeholder) {
    const el = document.createElement(multi ? "textarea" : "input");
    if (!multi) el.type = "text"; else el.rows = 1;
    el.className = "edit"; el.value = value || ""; el.dataset.key = key; el.spellcheck = false;
    if (placeholder) el.placeholder = placeholder;
    el.addEventListener("input", () => { applyEdit(l, key, el.value); if (multi) grow(el); });
    el.addEventListener("change", () => {
      if (key === "phone" && el.value && !toE164(el.value)) { el.classList.add("bad"); setStatus("error", "That phone number doesn't look right. The dialer keeps using the old one."); }
      else el.classList.remove("bad");
      store.save(); render();
    });
    if (multi) requestAnimationFrame(() => grow(el));
    return el;
  }
  function buildEditor(l) {
    const dl = $("cFacts");
    if (editorFor === l.id && dl.childElementCount) {
      // Same customer: refresh only fields nobody is typing in.
      for (const el of dl.querySelectorAll(".edit")) {
        if (el === document.activeElement) continue;
        const v = (detailsOf(l)[el.dataset.key] || "");
        if (el.value !== v) { el.value = v; if (el.tagName === "TEXTAREA") grow(el); }
      }
      const c = $("cComments");
      if (c !== document.activeElement && c.value !== (l.comments || "")) { c.value = l.comments || ""; grow(c); }
      return;
    }
    editorFor = l.id;
    dl.textContent = "";
    const det = detailsOf(l);
    for (const f of DETAIL_FIELDS) {
      const dt = document.createElement("dt"); dt.textContent = f.label;
      const dd = document.createElement("dd");
      dd.appendChild(makeInput(l, f.key, det[f.key], MULTI.has(f.key), "—"));
      dl.append(dt, dd);
    }
    const old = $("cComments");
    const c = makeInput(l, "comments", l.comments, true, "Add a comment…");
    c.id = "cComments"; c.classList.add("comments");
    old.replaceWith(c);
    $("cCommentsWrap").hidden = false;
  }
  function renderCard() {
    const l = cardLead();
    $("cardEmpty").hidden = !!l;
    $("card").hidden = !l;
    if (!l) return;
    $("cName").textContent = l.name || "No name on sheet";
    $("cPhone").textContent = l.display;
    const pill = $("cStatus");
    pill.className = "pill " + l.status;
    pill.textContent = countdown && countdown.leadId === l.id ? "Up next" : (LABEL[l.status] || l.status);
    shownLeadId = l.id;
    buildEditor(l);
    const addRow = (box, k, v) => {
      const dt = document.createElement("dt"); dt.textContent = k;
      const dd = document.createElement("dd"); dd.textContent = v || "—";
      box.append(dt, dd);
    };
    const meta = $("cMeta"); meta.textContent = "";
    const metaRows = [
      ["Local time", localTimeText(l)],
      ["State (for calling hours)", l.state],
      ["Sheet", (sheetOf(l) || {}).name],
      ["Try", `${Math.max(l.attempts, 1)} of ${settings.maxAttempts}`]
    ];
    for (const [k, v] of metaRows) {
      if (k.startsWith("State")) {
        const dt = document.createElement("dt"); dt.textContent = k;
        const dd = document.createElement("dd");
        const inp = makeInput(l, "state", l.state, false, "e.g. TX");
        inp.classList.add("short"); inp.maxLength = 20;
        dd.appendChild(inp); meta.append(dt, dd); continue;
      }
      if (v && v !== "—") addRow(meta, k, v);
    }
    $("cCheckWrap").hidden = !l.check;
    $("cCheck").textContent = l.check || "";
    // Who comes after this one
    const rest = candidates().filter((x) => x.id !== l.id && inHours(x));
    const nxt = rest.find((x) => x.status === "pending") || rest[0];
    $("cNext").textContent = nxt ? `After this: ${nxt.name || nxt.display}` : "";
    $("cLeft").textContent = `${candidates().length} left to call on this PC`;
    const onDnc = isDnc(l);
    $("cDnc").textContent = onDnc ? "On Do Not Call (undo)" : "Do not call again";
    $("cDnc").classList.toggle("armed", onDnc);
    $("cDnc").onclick = () => toggleDnc(l);
    $("cSale").textContent = l.sale ? "Sale made ✓ (undo)" : "Sale made";
    $("cSale").classList.toggle("armed", !!l.sale);
    $("cSale").onclick = () => toggleSale(l);
  }

  function renderSheets() {
    const box = $("sheets");
    box.textContent = "";
    for (const sh of sheets) {
      const mine = leads.filter((l) => l.sheet === sh.id && isMine(l));
      const done = mine.filter((l) => l.status === "talked" || l.status === "noanswer").length;
      const el = document.createElement("div");
      el.className = "sheet" + (sh.active ? "" : " off");
      const lab = document.createElement("label");
      lab.title = "Untick to stop dialing from this sheet without removing it";
      const cb = document.createElement("input");
      cb.type = "checkbox"; cb.checked = sh.active;
      cb.addEventListener("change", () => {
        sh.active = cb.checked; store.save(); render();
        if (running && !current && !inboundBusy && !countdown) scheduleNext();
      });
      lab.append(cb, document.createTextNode(sh.name));
      const meta = document.createElement("span");
      meta.className = "sheet-meta";
      meta.textContent = `${done}/${mine.length} done`;
      const rm = document.createElement("button");
      rm.type = "button"; rm.className = "btn tiny danger" + (armedRemove === sh.id ? " armed" : "");
      rm.textContent = armedRemove === sh.id ? "Click again to remove" : "Remove";
      rm.title = "Remove this sheet and its leads from the dialer";
      rm.addEventListener("click", () => {
        if (armedRemove === sh.id) { removeSheet(sh.id); return; }
        armedRemove = sh.id; render();
        setTimeout(() => { if (armedRemove === sh.id) { armedRemove = null; render(); } }, 4000);
      });
      const rs = document.createElement("button");
      rs.type = "button"; rs.className = "btn tiny" + (armedRestart === sh.id ? " danger armed" : "");
      rs.textContent = armedRestart === sh.id ? "Click again to restart" : "Restart";
      rs.title = "Set this sheet's customers back to Not called and dial them again from the top";
      rs.disabled = !!current;
      rs.addEventListener("click", () => armRestart(sh.id));
      el.append(lab, meta, rs, rm);
      box.appendChild(el);
    }
  }

  function resultsRows() {
    const head = ["Name", "Phone", "State", "Sheet", "Tries", "Result", "Last call"];
    head.splice(4, 0, "PC");
    return [head, ...leads.filter((l) => cloud.role === "admin" || isMine(l)).map((l) => [l.name, l.display, l.state, (sheetOf(l) || {}).name || "", String(ownerOf(l)), String(l.attempts),
      l.status === "talked" ? "Answered" : isDnc(l) && l.status !== "talked" && l.attempts === 0 ? "Do not call" : (l.result || LABEL[l.status] || l.status), l.lastCall])];
  }

  // ---------- wire up ----------
  $("btnStart").addEventListener("click", start);
  $("btnRestart").addEventListener("click", () => armRestart("all"));
  $("btnView").addEventListener("click", () => setFocus(!focusMode));
  $("btnPause").addEventListener("click", pause);
  $("btnSkip").addEventListener("click", skip);
  const PANELS = ["importPanel", "settingsPanel", "dncPanel", "statePanel"];
  $("btnStates").addEventListener("click", () => togglePanel("statePanel"));
  $("btnStatesAll").addEventListener("click", () => { settings.blankState = true; setStates(null); });
  $("btnStatesNone").addEventListener("click", () => { settings.blankState = false; setStates([]); });
  $("blankState").addEventListener("change", () => { settings.blankState = $("blankState").checked; store.save(); render(); maybeResume(); });
  const togglePanel = (id) => { const open = $(id).hidden; PANELS.forEach((p) => { $(p).hidden = true; }); $(id).hidden = !open; };
  $("btnImport").addEventListener("click", () => togglePanel("importPanel"));
  $("btnSettings").addEventListener("click", () => togglePanel("settingsPanel"));
  $("btnDnc").addEventListener("click", () => togglePanel("dncPanel"));
  $("btnDncAdd").addEventListener("click", () => { if (addDnc(numbersIn($("dncBox").value))) $("dncBox").value = ""; });
  $("dncFile").addEventListener("change", () => addDncFile($("dncFile").files[0]));
  $("dncSearch").addEventListener("input", renderDnc);
  $("btnDncCsv").addEventListener("click", () => {
    const csv = ["Phone", ...[...dnc].sort().map((n) => pretty("+1" + n))].join("\r\n");
    const a = document.createElement("a");
    a.href = URL.createObjectURL(new Blob([csv], { type: "text/csv" }));
    a.download = `do-not-call-${new Date().toISOString().slice(0, 10)}.csv`;
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  });
  $("btnPaste").addEventListener("click", () => addSheet($("pasteBox").value, $("sheetName").value));
  $("btnFetch").addEventListener("click", () => fetchSheet($("sheetUrl").value.trim()));
  $("fileInput").addEventListener("change", () => addFile($("fileInput").files[0]));
  $("btnCopy").addEventListener("click", async () => {
    const tsv = resultsRows().map((r) => r.map((v) => String(v || "").replace(/\t|\n/g, " ")).join("\t")).join("\n");
    try { await navigator.clipboard.writeText(tsv); setStatus($("statusBox").dataset.state, "Results copied. Paste into Google Sheets."); }
    catch { setStatus("error", "Couldn't copy. Use Download CSV instead."); }
  });
  $("btnCsv").addEventListener("click", () => {
    const csv = resultsRows().map((r) => r.map((v) => `"${String(v || "").replace(/"/g, '""')}"`).join(",")).join("\r\n");
    const a = document.createElement("a");
    a.href = URL.createObjectURL(new Blob([csv], { type: "text/csv" }));
    a.download = `dialer-results-${new Date().toISOString().slice(0, 10)}.csv`;
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 5000);
  });
  const clamp = (v, lo, hi, dflt) => { v = Math.round(Number(v)); return Number.isFinite(v) ? Math.min(hi, Math.max(lo, v)) : dflt; };
  function readSettings() {
    settings.maxAttempts = clamp($("maxAttempts").value, 1, 5, 2);
    settings.retryMode = $("retryMode").value;
    settings.gapSec = clamp($("gapSec").value, 1, 600, 4);
    settings.hoursGuard = $("hoursGuard").checked;
    settings.pcCount = clamp($("pcCount").value, 1, 20, 1);
    settings.pcNumber = clamp($("pcNumber").value, 1, settings.pcCount, 1);
    $("gapSec").value = String(settings.gapSec);
    $("pcCount").value = String(settings.pcCount);
    $("pcNumber").value = String(settings.pcNumber);
    $("pcNumber").max = String(settings.pcCount);
    try { localStorage.setItem("shd-pc", String(settings.pcNumber)); } catch { /* ignore */ }
    $("whoPc").textContent = "PC " + settings.pcNumber;
    store.save(); render(); renderAdmin();
  }
  for (const id of ["maxAttempts", "retryMode", "gapSec", "hoursGuard", "pcCount", "pcNumber"]) $(id).addEventListener("change", readSettings);

  // ---------- theme ----------
  const darkQuery = window.matchMedia("(prefers-color-scheme: dark)");
  const isDark = () => (document.documentElement.dataset.theme || (darkQuery.matches ? "dark" : "light")) === "dark";
  function syncThemeBtn() { $("btnTheme").textContent = isDark() ? "Light mode" : "Dark mode"; }
  $("btnTheme").addEventListener("click", () => {
    const next = isDark() ? "light" : "dark";
    document.documentElement.dataset.theme = next;
    try { localStorage.setItem("shd-theme", next); } catch { /* ignore */ }
    syncThemeBtn();
  });
  darkQuery.addEventListener("change", syncThemeBtn);
  syncThemeBtn();

  window.addEventListener("beforeunload", (e) => { if (running || current) { e.preventDefault(); e.returnValue = ""; } });
  setInterval(() => { if (!current) render(); }, 60000); // keep local times fresh

  // ---------- boot ----------
  function applySaved(saved) {
    if (saved && saved.settings) {
      settings = { ...settings, ...saved.settings };
      // Older versions defaulted to 3 tries; the new default is 2.
      if (saved.settings.v !== SETTINGS_VERSION) settings.maxAttempts = 2;
      settings.v = SETTINGS_VERSION;
    }
    if (saved && Array.isArray(saved.sheets)) sheets = saved.sheets;
    if (saved && Array.isArray(saved.dnc)) dnc = new Set(saved.dnc);
    if (saved && Array.isArray(saved.leads)) {
      // Anything mid-call when the tab closed goes back in the queue.
      leads = saved.leads.map((l) => ["dialing", "ringing", "live"].includes(l.status)
        ? { ...l, status: l.attempts >= settings.maxAttempts ? "noanswer" : "retry" } : l);
      leads.forEach((l) => { if (l.status === "pending" || l.status === "retry") applyGuard(l); });
      // Leads saved by the older single-list version go into a sheet of their own.
      if (leads.some((l) => !l.sheet)) {
        if (!sheets.some((s) => s.id === "s0")) sheets.unshift({ id: "s0", name: "Sheet 1", active: true });
        leads.forEach((l) => { if (!l.sheet) l.sheet = "s0"; });
      }
    }
    fillSettingsForm();
    render(); syncButtons();
  }
  function fillSettingsForm() {
    $("maxAttempts").value = String(settings.maxAttempts);
    $("retryMode").value = settings.retryMode;
    $("gapSec").value = String(settings.gapSec);
    $("hoursGuard").checked = settings.hoursGuard;
    $("pcCount").value = String(settings.pcCount);
    $("pcNumber").value = String(settings.pcNumber);
    $("pcNumber").max = String(settings.pcCount);
    }

  // ---------- online sync (admin + agent PCs) ----------
  // Light on usage: one small request every 5 s (15 s when this PC is paused, 30 s if the tab is hidden),
  // and only customers that changed are sent or received. The full list downloads once at sign-in.
  function stable(v) {
    if (Array.isArray(v)) return "[" + v.map(stable).join(",") + "]";
    if (v && typeof v === "object") return "{" + Object.keys(v).sort().filter((k) => v[k] !== undefined).map((k) => JSON.stringify(k) + ":" + stable(v[k])).join(",") + "}";
    return JSON.stringify(v === undefined ? null : v);
  }
  const sheetsJson = (list) => stable(list.map((x) => ({ id: x.id, name: x.name, active: x.active !== false })));
  function configOf() { const c = { ...settings }; delete c.pcNumber; return c; }
  function cloudDesire(d) { if (cloud.started) { cloud.desire = d; cloudSoon(200, true); } }
  function cloudChanged() { if (cloud.started) cloudSoon(600, false); }
  function cloudSoon(ms, pull) { clearTimeout(cloud.pushTimer); cloud.pushTimer = setTimeout(() => cloudCycle(pull), ms); }
  function statusObj() {
    const mine = leads.filter(isMine);
    const l = current ? leadById(current.leadId) : null;
    return { running, state: $("statusBox").dataset.state, text: $("statusText").textContent.slice(0, 120),
      lead: l ? (l.name || l.display) : "", called: mine.filter((x) => x.attempts > 0).length,
      sales: mine.filter((x) => x.sale).length, left: candidates().length, v: "1.4.0" };
  }
  function setOnline(ok, err) {
    const el = $("syncState");
    el.textContent = ok ? "Synced" : "Offline · retrying";
    el.dataset.ok = ok ? "1" : "0";
    el.title = ok ? "Shared with all PCs" : ("Changes are kept on this PC and sent when the connection is back. " + (err ? err.message : ""));
  }
  function nextDelay() {
    if (document.hidden && !running && !current) return 30000;
    return (cloud.role === "admin" || running || current) ? 5000 : 15000;
  }

  async function cloudCycle(pull = true) {
    if (!cloud.started) return;
    if (cloud.busy) { cloud.again = true; return; }
    cloud.busy = true; clearTimeout(cloud.timer);
    let stop = false;
    try {
      await cloudPush();
      if (pull) await cloudPull();
      setOnline(true);
    } catch (err) {
      if (err.signedOut || err.notAllowed) { stop = true; authLost(err); }
      else setOnline(false, err);
    } finally {
      cloud.busy = false;
      if (cloud.started && !stop) {
        const again = cloud.again; cloud.again = false;
        cloud.timer = setTimeout(() => cloudCycle(true), again ? 300 : nextDelay());
      }
    }
  }

  async function cloudPush() {
    const admin = cloud.role === "admin";
    const changed = [];
    for (const l of leads) {
      const j = stable(l);
      if (cloud.snap.get(l.id) === j) continue;
      if (!admin && !cloud.snap.has(l.id)) continue; // agents can't add customers
      changed.push([l.id, j]);
    }
    const dAdd = [...dnc].filter((n) => !cloud.dncSnap.has(n));
    const dRem = [...cloud.dncSnap].filter((n) => !dnc.has(n));
    let sj = null, delSheets = [], cj = null;
    if (admin) {
      const now = sheetsJson(sheets);
      if (now !== cloud.sheetsSnap) { sj = now; delSheets = [...cloud.sheetIds].filter((id) => !sheets.some((x) => x.id === id)); }
      const c = stable(configOf());
      if (c !== cloud.configSnap) cj = c;
    }
    const cmds = cloud.commands.splice(0);
    if (!changed.length && !dAdd.length && !dRem.length && sj === null && cj === null && !cmds.length) return;
    try {
      let first = true;
      do {
        const chunk = changed.splice(0, 200);
        const args = { p_leads: chunk.map(([, j]) => JSON.parse(j)) };
        if (first) Object.assign(args, { p_dnc_add: dAdd, p_dnc_remove: dRem, p_sheets: sj ? JSON.parse(sj) : null,
          p_delete_sheets: delSheets, p_config: cj ? JSON.parse(cj) : null, p_commands: cmds.length ? cmds : null });
        await Cloud.rpc("dialer_push", args);
        chunk.forEach(([id, j]) => cloud.snap.set(id, j));
        if (first) {
          dAdd.forEach((n) => cloud.dncSnap.add(n)); dRem.forEach((n) => cloud.dncSnap.delete(n));
          if (sj !== null) { cloud.sheetsSnap = sj; cloud.sheetIds = new Set(JSON.parse(sj).map((x) => x.id)); }
          if (cj !== null) cloud.configSnap = cj;
          cmds.length = 0;
        }
        first = false;
      } while (changed.length);
    } catch (err) {
      if (cmds.length) cloud.commands.unshift(...cmds);
      throw err;
    }
  }

  function applyConfig(cfg) {
    if (!cfg || !Object.keys(cfg).length) return false;
    const pc = settings.pcNumber;
    settings = { ...settings, ...cfg, pcNumber: pc };
    cloud.configSnap = stable(configOf());
    fillSettingsForm();
    return true;
  }
  function obeyAdmin(pcs, initial) {
    cloud.pcs = pcs || [];
    const me = cloud.pcs.find((x) => x.pc === settings.pcNumber);
    const at = me && me.desired_at ? me.desired_at : null;
    if (initial || cloud.lastDesiredAt === undefined) { cloud.lastDesiredAt = at; return; }
    if (!at || at === cloud.lastDesiredAt) return;
    cloud.lastDesiredAt = at;
    if (me.desired === "run" && !running) { start(true); setStatus($("statusBox").dataset.state, "Started by the admin. " + $("statusText").textContent); }
    else if (me.desired === "pause" && running) { pause(true); setStatus("idle", "Paused by the admin."); }
  }

  async function cloudPull() {
    const since = cloud.since ? new Date(new Date(cloud.since).getTime() - 3000).toISOString() : null;
    const desire = cloud.desire; cloud.desire = null;
    let res;
    try { res = await Cloud.rpc("dialer_sync", { p_since: since, p_pc: settings.pcNumber, p_status: statusObj(), p_desired: desire }); }
    catch (err) { if (desire && !cloud.desire) cloud.desire = desire; throw err; }
    if (res.role !== cloud.role) { cloud.role = res.role; applyRole(); }
    cloud.serverNow = res.now;
    let changed = false;

    const sj = sheetsJson(res.sheets || []);
    if (sj !== sheetsJson(sheets)) {
      const keepIds = new Set((res.sheets || []).map((x) => x.id));
      sheets = (res.sheets || []).map((x) => ({ id: x.id, name: x.name, active: x.active !== false }));
      const before = leads.length;
      leads = leads.filter((l) => keepIds.has(l.sheet) || (current && current.leadId === l.id));
      if (leads.length !== before && countdown && !leadById(countdown.leadId)) cancelCountdown();
      changed = true;
    }
    cloud.sheetsSnap = sj; cloud.sheetIds = new Set((res.sheets || []).map((x) => x.id));

    const byId = new Map(leads.map((l) => [l.id, l]));
    for (const d of res.leads || []) {
      if (!d || !d.id) continue;
      const dj = stable(d);
      const loc = byId.get(d.id);
      if (loc) {
        const lj = stable(loc);
        if (lj === dj) { cloud.snap.set(d.id, dj); continue; }
        if (cloud.snap.has(d.id) && lj !== cloud.snap.get(d.id)) continue; // this PC has newer changes waiting to be sent
        for (const k of Object.keys(loc)) delete loc[k];
        Object.assign(loc, d);
      } else {
        leads.push(d); byId.set(d.id, d);
      }
      cloud.snap.set(d.id, dj);
      changed = true;
    }
    for (const x of res.dnc || []) {
      if (x.x) { if (dnc.delete(x.p)) changed = true; cloud.dncSnap.delete(x.p); }
      else { if (!dnc.has(x.p)) { dnc.add(x.p); changed = true; } cloud.dncSnap.add(x.p); }
    }
    if (applyConfig(res.config)) changed = true;
    obeyAdmin(res.pcs, false);
    cloud.since = res.now;
    if (changed) {
      try { localStorage.setItem(storeKey(), JSON.stringify({ leads, settings, sheets, dnc: [...dnc] })); } catch { /* ignore */ }
      render(); maybeResume();
    }
    renderAdmin();
  }

  async function cloudStart() {
    setOnline(true); $("syncState").textContent = "Connecting…";
    let res;
    try { res = await Cloud.rpc("dialer_sync", { p_since: null, p_pc: settings.pcNumber, p_status: statusObj(), p_desired: null }); }
    catch (err) {
      if (err.signedOut || err.notAllowed) return authLost(err);
      setOnline(false, err); setTimeout(cloudStart, 10000); return;
    }
    cloud.role = res.role; cloud.serverNow = res.now; applyRole();
    const srvSheets = res.sheets || [];
    const keepLocal = cloud.role === "admin" && !srvSheets.length && leads.length > 0; // first time: upload this PC's list
    const srvDnc = new Set((res.dnc || []).filter((x) => !x.x).map((x) => x.p));
    if (!keepLocal) {
      sheets = srvSheets.map((x) => ({ id: x.id, name: x.name, active: x.active !== false }));
      leads = res.leads || [];
      cloud.snap = new Map(leads.map((l) => [l.id, stable(l)]));
      cloud.sheetsSnap = sheetsJson(sheets);
      cloud.sheetIds = new Set(sheets.map((x) => x.id));
    } else {
      cloud.snap = new Map(); cloud.sheetsSnap = "[]"; cloud.sheetIds = new Set();
    }
    dnc = new Set([...dnc, ...srvDnc]); // numbers marked DNC on this PC are shared too
    cloud.dncSnap = srvDnc;
    if (!applyConfig(res.config)) cloud.configSnap = cloud.role === "admin" ? "" : stable(configOf());
    obeyAdmin(res.pcs, true);
    // Anything this PC was mid-call on when it closed goes back in the queue.
    leads.forEach((l) => { if (isMine(l) && ["dialing", "ringing", "live"].includes(l.status)) l.status = l.attempts >= settings.maxAttempts ? "noanswer" : "retry"; });
    cloud.since = res.now; cloud.started = true;
    setOnline(true);
    fillSettingsForm(); render(); renderAdmin(); syncButtons();
    if (settings.pcNumber > settings.pcCount) setStatus("error", `This PC is number ${settings.pcNumber}, but the admin set ${settings.pcCount} PC${settings.pcCount === 1 ? "" : "s"}. Sign out and pick a number from 1 to ${settings.pcCount}.`);
    else setStatus("idle", cloud.role === "admin" ? (leads.length ? "Ready. Press Start dialing, or start PCs from the admin panel." : "Press Add sheet to load customers for all PCs.") : (leads.length ? "Ready. Press Start dialing." : "Waiting for the admin to add customers."));
    cloudCycle(true);
  }

  function authLost(err) {
    cloud.started = false;
    clearTimeout(cloud.timer); clearTimeout(cloud.pushTimer);
    if (running) pause(true);
    Cloud.signOut();
    showLogin(err && err.notAllowed ? "This login isn't allowed to use the dialer. Ask the admin." : "Please sign in again.");
  }

  // ---------- roles ----------
  function applyRole() {
    const admin = cloud.role === "admin";
    document.body.classList.toggle("role-admin", admin);
    document.body.classList.toggle("role-agent", !admin);
    $("whoRole").textContent = admin ? "Admin" : "Agent";
    $("whoPc").textContent = "PC " + settings.pcNumber;
    $("pcNumber").disabled = !admin;
    if (!admin) setFocus(true);
  }

  // ---------- admin panel: every PC at a glance, start/pause any of them ----------
  function adminCommand(pc, desired) {
    if (cloud.role !== "admin") return;
    if (pc === settings.pcNumber) { if (desired === "run") start(true); else pause(true); }
    cloud.commands = cloud.commands.filter((c) => c.pc !== pc);
    cloud.commands.push({ pc, desired });
    const row = cloud.pcs.find((x) => x.pc === pc);
    if (row) row.pending = desired;
    renderAdmin();
    cloudSoon(100, true);
  }
  function renderAdmin() {
    if (cloud.role !== "admin") return;
    const now = cloud.serverNow ? new Date(cloud.serverNow).getTime() : Date.now();
    const max = Math.max(settings.pcCount, ...cloud.pcs.map((x) => x.pc), 1);
    const body = $("adminRows"); body.textContent = "";
    let online = 0, dialing = 0;
    for (let pc = 1; pc <= max; pc++) {
      const row = cloud.pcs.find((x) => x.pc === pc) || { pc, status: {} };
      const st = row.status || {};
      const isMe = pc === settings.pcNumber;
      const seen = row.last_seen ? new Date(row.last_seen).getTime() : 0;
      const on = isMe || (seen && now - seen < 45000);
      const runningNow = isMe ? running : !!st.running;
      if (on) online++;
      if (on && runningNow) dialing++;
      const tr = document.createElement("tr");
      const td = (t, cls) => { const c = document.createElement("td"); c.textContent = t; if (cls) c.className = cls; tr.appendChild(c); return c; };
      td(isMe ? `PC ${pc} (this PC)` : `PC ${pc}`);
      const onCell = td(on ? "Online" : (seen ? "Offline" : "Not signed in yet"), on ? "on" : "off");
      onCell.title = seen ? "Last seen " + new Date(seen).toLocaleTimeString() : "";
      const want = row.pending || null;
      td(want ? (want === "run" ? "Starting…" : "Pausing…") : (on ? (runningNow ? "Dialing" : "Paused") : "—"), runningNow && on ? "run" : "");
      const live = isMe ? statusObj() : st;
      td(on ? (live.lead ? "On the line: " + live.lead : (live.text || "")) : "", "admin-now");
      td(String(live.called ?? "—")); td(String(live.sales ?? "—")); td(String(live.left ?? "—"));
      const act = document.createElement("td"); act.className = "row-actions";
      const b1 = document.createElement("button"); b1.type = "button"; b1.className = "btn tiny primary"; b1.textContent = "Start";
      b1.disabled = runningNow && on; b1.addEventListener("click", () => adminCommand(pc, "run"));
      const b2 = document.createElement("button"); b2.type = "button"; b2.className = "btn tiny"; b2.textContent = "Pause";
      b2.disabled = !runningNow; b2.addEventListener("click", () => adminCommand(pc, "pause"));
      act.append(b1, b2); tr.appendChild(act);
      body.appendChild(tr);
    }
    const sales = leads.filter((l) => l.sale).length;
    const called = leads.filter((l) => l.attempts > 0).length;
    $("adminSum").textContent = `${online} online · ${dialing} dialing · ${called} called · ${sales} sale${sales === 1 ? "" : "s"}`;
  }
  $("btnAllStart").addEventListener("click", () => { for (let pc = 1; pc <= settings.pcCount; pc++) adminCommand(pc, "run"); });
  $("btnAllPause").addEventListener("click", () => { for (let pc = 1; pc <= Math.max(settings.pcCount, ...cloud.pcs.map((x) => x.pc)); pc++) adminCommand(pc, "pause"); });

  // ---------- sign in ----------
  function showLogin(msg) {
    $("login").hidden = false;
    document.body.classList.add("signed-out");
    let pc = "1"; try { pc = localStorage.getItem("shd-pc") || "1"; } catch { /* ignore */ }
    $("loginPc").value = pc;
    $("loginMsg").textContent = msg || "";
    $("loginMsg").className = msg ? "msg bad" : "msg";
    setTimeout(() => $("loginEmail").focus(), 50);
  }
  $("loginForm").addEventListener("submit", async (e) => {
    e.preventDefault();
    const btn = $("loginBtn"); btn.disabled = true;
    $("loginMsg").className = "msg"; $("loginMsg").textContent = "Signing in…";
    try {
      await Cloud.signIn($("loginEmail").value, $("loginPw").value);
      const pc = clamp($("loginPc").value, 1, 50, 1);
      try { localStorage.setItem("shd-pc", String(pc)); } catch { /* ignore */ }
      $("loginPw").value = "";
      $("login").hidden = true; document.body.classList.remove("signed-out");
      await bootApp();
    } catch (err) {
      $("loginMsg").className = "msg bad"; $("loginMsg").textContent = err.message;
    } finally { btn.disabled = false; }
  });
  $("btnSignOut").addEventListener("click", () => {
    if (current) { setStatus("wait", "Finish the call first, then sign out."); return; }
    if (running) pause();
    const go = () => { cloud.started = false; Cloud.signOut(); location.reload(); };
    // send the pause/heartbeat first so the admin sees this PC stop
    cloudCycle(true).finally(go);
  });

  async function bootApp() {
    applySaved(await store.get());
    let pc = settings.pcNumber;
    try { pc = clamp(localStorage.getItem("shd-pc") || pc, 1, 50, 1); } catch { /* ignore */ }
    settings.pcNumber = pc;
    $("whoEmail").textContent = (Cloud.session && Cloud.session.email) || "";
    fillSettingsForm();
    await cloudStart();
  }
  document.addEventListener("visibilitychange", () => { if (!document.hidden && cloud.started) cloudSoon(100, true); });
  if (window.Cloud && Cloud.session) bootApp(); else showLogin();

})();
