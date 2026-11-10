/* Applies the saved light/dark choice before the page paints (no flash). */
(function () {
  try {
    var t = localStorage.getItem("shd-theme");
    if (t === "light" || t === "dark") document.documentElement.setAttribute("data-theme", t);
  } catch (e) { /* storage unavailable: follow the system setting */ }
})();
