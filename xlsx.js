/* Minimal .xlsx reader (no external code): unzips with the browser's DecompressionStream and
 * reads the cell values of one worksheet into an array of rows. Prefers a tab named "Dial List",
 * otherwise the first tab. Handles shared strings, inline strings, numbers and booleans. */
window.readXlsx = async function (arrayBuffer) {
  const buf = arrayBuffer, dv = new DataView(buf);
  let eocd = -1;
  for (let i = buf.byteLength - 22; i >= Math.max(0, buf.byteLength - 65557); i--) {
    if (dv.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
  }
  if (eocd < 0) throw new Error("That file isn't a valid Excel (.xlsx) file.");
  const count = dv.getUint16(eocd + 10, true);
  let p = dv.getUint32(eocd + 16, true);
  const entries = {};
  const dec = new TextDecoder();
  for (let n = 0; n < count && dv.getUint32(p, true) === 0x02014b50; n++) {
    const method = dv.getUint16(p + 10, true), csize = dv.getUint32(p + 20, true);
    const nlen = dv.getUint16(p + 28, true), elen = dv.getUint16(p + 30, true), clen = dv.getUint16(p + 32, true);
    const local = dv.getUint32(p + 42, true);
    entries[dec.decode(new Uint8Array(buf, p + 46, nlen))] = { method, csize, local };
    p += 46 + nlen + elen + clen;
  }
  async function file(name) {
    const e = entries[name.replace(/^\//, "")];
    if (!e) return null;
    const off = e.local + 30 + dv.getUint16(e.local + 26, true) + dv.getUint16(e.local + 28, true);
    const data = new Uint8Array(buf, off, e.csize);
    if (e.method === 0) return dec.decode(data);
    if (e.method !== 8) throw new Error("Unsupported compression in this Excel file.");
    const stream = new Blob([data]).stream().pipeThrough(new DecompressionStream("deflate-raw"));
    return await new Response(stream).text();
  }
  const xml = (s) => new DOMParser().parseFromString(s, "application/xml");
  const wb = xml(await file("xl/workbook.xml") || "");
  const sheets = [...wb.getElementsByTagName("sheet")];
  if (!sheets.length) throw new Error("No tabs found in that Excel file.");
  const pick = sheets.find((s) => /^dial\s*list$/i.test(s.getAttribute("name") || "")) || sheets[0];
  const rid = pick.getAttribute("r:id");
  const rels = xml(await file("xl/_rels/workbook.xml.rels") || "<x/>");
  let target = "worksheets/sheet1.xml";
  for (const r of rels.getElementsByTagName("Relationship")) if (r.getAttribute("Id") === rid) target = r.getAttribute("Target");
  const path = target.startsWith("/") ? target.slice(1) : "xl/" + target.replace(/^\.\//, "");
  const shared = [];
  const ss = await file("xl/sharedStrings.xml");
  if (ss) for (const si of xml(ss).getElementsByTagName("si")) {
    shared.push([...si.getElementsByTagName("t")].map((t) => t.textContent).join(""));
  }
  const sheetXml = await file(path);
  if (!sheetXml) throw new Error("Couldn't read the tab in that Excel file.");
  const colIdx = (ref) => { let c = 0; for (const ch of ref.replace(/\d+/g, "")) c = c * 26 + ch.charCodeAt(0) - 64; return c - 1; };
  const rows = [];
  for (const row of xml(sheetXml).getElementsByTagName("row")) {
    const out = [];
    let next = 0;
    for (const c of row.getElementsByTagName("c")) {
      const ref = c.getAttribute("r");
      const ci = ref ? colIdx(ref) : next;
      next = ci + 1;
      const t = c.getAttribute("t");
      const v = c.getElementsByTagName("v")[0];
      let val = "";
      if (t === "s") val = shared[Number(v && v.textContent)] || "";
      else if (t === "inlineStr") val = [...c.getElementsByTagName("t")].map((x) => x.textContent).join("");
      else if (t === "b") val = v && v.textContent === "1" ? "TRUE" : "FALSE";
      else val = v ? v.textContent : "";
      out[ci] = val;
    }
    for (let i = 0; i < out.length; i++) if (out[i] === undefined) out[i] = "";
    rows.push(out);
  }
  return { rows: rows.filter((r) => r.some((v) => String(v).trim())), tab: pick.getAttribute("name") || "" };
};
