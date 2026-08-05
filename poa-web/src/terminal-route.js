const ROUTE_ALIASES = Object.freeze({ watch: "overview" });

/** Resolve one terminal section. A non-empty hash is authoritative, including
 * an invalid one (which fails to the default). `?view=` is consulted only when
 * there is no hash route, preserving signed companion links without ambiguity. */
export function resolveTerminalRoute({ hash = "", search = "" } = {}, knownRoutes = []) {
  const known = new Set(knownRoutes);
  const hashRoute = hash.startsWith("#") ? hash.slice(1) : hash;
  let requested = hashRoute;
  if (requested.length === 0) {
    const queryRoute = new URLSearchParams(search).get("view") ?? "";
    requested = ROUTE_ALIASES[queryRoute] ?? queryRoute;
  }
  return known.has(requested) ? requested : known.has("overview") ? "overview" : knownRoutes[0] ?? null;
}
