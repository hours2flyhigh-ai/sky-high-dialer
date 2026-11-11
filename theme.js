/* Applies the saved theme and menu size before the page paints (no flash). No saved theme = follow the PC (light or dark). */
(function () {
  try {
    var t = localStorage.getItem("shd-theme");
    if (/^(light|dark|sunrise|mint|ocean|plum)$/.test(t || "")) document.documentElement.setAttribute("data-theme", t);
  } catch (e) { /* storage unavailable: follow the system setting */ }
  try {
    var s = localStorage.getItem("shd-side");
    // small menu (icons only) when picked on this PC, or by itself on a narrow window
    if (s === "rail" || (s !== "full" && window.innerWidth < 1000)) document.documentElement.setAttribute("data-side", "rail");
  } catch (e) { /* storage unavailable: full menu */ }
})();
