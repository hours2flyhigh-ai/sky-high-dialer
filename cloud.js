/* Sky High Dialer — sign-in and calls to the online database (Supabase).
 * The publishable key below is meant to be public: the database only answers
 * signed-in users that are on the dialer's allowed list (admin or agent). */
window.Cloud = (() => {
  "use strict";
  const BASE = "https://bnyucdybespguuvjlttk.supabase.co";
  const KEY = "sb_publishable_zfjL-9m3OiwYa8C4K3R5-Q_TLaw-V-7";
  const SKEY = "shd-session";

  let session = null;
  try { session = JSON.parse(localStorage.getItem(SKEY) || "null"); } catch { session = null; }
  function keep(s) {
    session = s;
    try { if (s) localStorage.setItem(SKEY, JSON.stringify(s)); else localStorage.removeItem(SKEY); } catch { /* ignore */ }
  }
  const fromAuth = (j) => ({ access: j.access_token, refresh: j.refresh_token,
    exp: Date.now() + (j.expires_in || 3600) * 1000, email: (j.user && j.user.email) || (session && session.email) || "" });

  async function signIn(email, password) {
    const r = await fetch(`${BASE}/auth/v1/token?grant_type=password`, {
      method: "POST", headers: { apikey: KEY, "Content-Type": "application/json" },
      body: JSON.stringify({ email: String(email).trim(), password })
    });
    const j = await r.json().catch(() => ({}));
    if (!r.ok) throw new Error(/invalid/i.test(j.error_description || j.msg || "") ? "Wrong username or password." : (j.error_description || j.msg || "Sign-in failed."));
    keep(fromAuth(j));
    return session;
  }

  let refreshing = null;
  function refresh() {
    if (!session) return Promise.reject(new Error("Signed out"));
    if (!refreshing) {
      refreshing = (async () => {
        const r = await fetch(`${BASE}/auth/v1/token?grant_type=refresh_token`, {
          method: "POST", headers: { apikey: KEY, "Content-Type": "application/json" },
          body: JSON.stringify({ refresh_token: session.refresh })
        });
        const j = await r.json().catch(() => ({}));
        if (!r.ok) {
          if (r.status === 400 || r.status === 401) { keep(null); const e = new Error("Please sign in again."); e.signedOut = true; throw e; }
          throw new Error("Couldn't reach the server.");
        }
        keep(fromAuth(j));
      })().finally(() => { refreshing = null; });
    }
    return refreshing;
  }

  async function rpc(fn, args, retried) {
    if (!session) { const e = new Error("Signed out"); e.signedOut = true; throw e; }
    if (Date.now() > session.exp - 60000) await refresh();
    const r = await fetch(`${BASE}/rest/v1/rpc/${fn}`, {
      method: "POST",
      headers: { apikey: KEY, Authorization: "Bearer " + session.access, "Content-Type": "application/json" },
      body: JSON.stringify(args || {})
    });
    if (r.status === 401 && !retried) { await refresh(); return rpc(fn, args, true); }
    const text = await r.text();
    if (!r.ok) {
      let msg = text; try { const j = JSON.parse(text); msg = j.message || j.msg || text; } catch { /* keep text */ }
      const e = new Error(msg || ("Server error " + r.status));
      e.status = r.status;
      if (/not allowed/i.test(msg)) e.notAllowed = true;
      throw e;
    }
    return text ? JSON.parse(text) : null;
  }

  function signOut() {
    const s = session;
    keep(null);
    if (s) fetch(`${BASE}/auth/v1/logout`, { method: "POST", headers: { apikey: KEY, Authorization: "Bearer " + s.access } }).catch(() => {});
  }

  return { signIn, signOut, rpc, get session() { return session; } };
})();
