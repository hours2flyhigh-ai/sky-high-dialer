/* Applies the saved theme before the page paints (no flash). No saved theme = follow the PC (light or dark). */
(function () {
  try {
    var t = localStorage.getItem("shd-theme");
    if (/^(light|dark|sunrise|mint|ocean|plum)$/.test(t || "")) document.documentElement.setAttribute("data-theme", t);
  } catch (e) { /* storage unavailable: follow the system setting */ }
})();
