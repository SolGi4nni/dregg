import { createReadStream, statSync } from "node:fs";
import { createServer } from "node:http";
import { extname, join, normalize, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("./", import.meta.url));
/**
 * `public/` is OVERLAID at the web root, which is how the deployed terminal is
 * laid out: `sync-artifacts.mjs` writes `public/artifacts/poag1/` and
 * `public/poa-curator-key.json`, and the client fetches them at `/artifacts/…`
 * and `/poa-curator-key.json`.
 *
 * ⚠ Serving only the package directory made `npm run serve` unable to serve the
 * app AT ALL: every artifact 404'd, `loadPOAG1` refused with "manifest returned
 * HTTP 404", and the terminal rendered its sealed state. Nothing caught it
 * because the suite loads artifacts off disk and never through this server.
 */
const overlays = [root, fileURLToPath(new URL("./public/", import.meta.url))];
const port = Number.parseInt(process.env.POA_WEB_PORT ?? "4173", 10);
const host = process.env.POA_WEB_HOST ?? "127.0.0.1";
const mimes = new Map([
  [".html", "text/html; charset=utf-8"], [".css", "text/css; charset=utf-8"],
  [".js", "text/javascript; charset=utf-8"], [".json", "application/json; charset=utf-8"],
  [".svg", "image/svg+xml"], [".png", "image/png"], [".ico", "image/x-icon"],
]);

createServer((request, response) => {
  const requestUrl = new URL(request.url ?? "/", "http://localhost");
  let pathname;
  try { pathname = decodeURIComponent(requestUrl.pathname); } catch { pathname = "/__invalid__"; }
  const local = pathname === "/" ? "index.html" : pathname.replace(/^\/+/, "");
  const file = overlays
    .map((base) => ({ base, absolute: normalize(join(base, local)) }))
    .filter(({ base, absolute }) => !relative(base, absolute).startsWith(".."))
    .map(({ absolute }) => absolute)
    .find((candidate) => { try { return statSync(candidate).isFile(); } catch { return false; } });
  if (!file) {
    response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
    response.end("Not found\n");
    return;
  }
  response.writeHead(200, {
    "Content-Type": mimes.get(extname(file)) ?? "application/octet-stream",
    // ⚠ `no-store` for EVERYTHING, not just artifacts. This is a development
    // server; the previous `max-age=300` on scripts meant an edit to src/ was
    // invisible for five minutes, and the first thing that happened was a fix
    // being reviewed against the old bundle and read as not working. A dev
    // server that lies about what it is serving is worse than a slow one.
    "Cache-Control": "no-store",
    "Content-Security-Policy": "default-src 'self'; img-src 'self' data:; style-src 'self'; script-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'self'",
    "Referrer-Policy": "no-referrer",
    "X-Content-Type-Options": "nosniff",
    "Cross-Origin-Opener-Policy": "same-origin",
  });
  createReadStream(file).pipe(response);
}).listen(port, host, () => {
  process.stdout.write(`Path of Angels beta terminal: http://${host}:${port}\n`);
});
