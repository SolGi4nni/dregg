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
const nodeUpstream = process.env.POA_NODE_UPSTREAM
  ? new URL(process.env.POA_NODE_UPSTREAM)
  : null;
if (nodeUpstream && !["http:", "https:"].includes(nodeUpstream.protocol)) {
  throw new Error("POA_NODE_UPSTREAM must be an http(s) origin");
}
const mimes = new Map([
  [".html", "text/html; charset=utf-8"], [".css", "text/css; charset=utf-8"],
  [".js", "text/javascript; charset=utf-8"], [".json", "application/json; charset=utf-8"],
  [".svg", "image/svg+xml"], [".png", "image/png"], [".ico", "image/x-icon"],
]);

function readBody(request, limit = 64 * 1024) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let bytes = 0;
    let refused = false;
    request.on("data", (chunk) => {
      if (refused) return;
      bytes += chunk.byteLength;
      if (bytes > limit) {
        refused = true;
        reject(Object.assign(new Error("request body exceeds development proxy limit"), { code: "body-too-large" }));
        return;
      }
      chunks.push(chunk);
    });
    request.on("end", () => {
      if (!refused) resolve(chunks.length === 0 ? undefined : Buffer.concat(chunks));
    });
    request.on("error", reject);
  });
}

/**
 * Development-only same-origin carrier for the exact `/node/*` paths the
 * terminal uses in production.
 *
 * This is deliberately opt-in: setting `POA_NODE_UPSTREAM` is an operator act,
 * and the destination is fixed at process start rather than accepted from a
 * request. It exists for a browser integration check against a real node when a
 * browser or privacy extension blocks that node's public hostname. It does not
 * add a proxy route to deployed static releases.
 */
async function proxyNode(request, response, requestUrl) {
  const path = requestUrl.pathname.slice("/node".length) || "/";
  // Assign path/query onto the fixed origin. `new URL(path, origin)` would
  // interpret `/node//attacker.example` as a scheme-relative URL after slicing
  // the prefix, turning an operator-fixed proxy into an SSRF primitive.
  const target = new URL(nodeUpstream);
  target.pathname = path;
  target.search = requestUrl.search;
  try {
    const body = request.method === "GET" || request.method === "HEAD"
      ? undefined
      : await readBody(request);
    const upstream = await fetch(target, {
      method: request.method,
      headers: {
        accept: request.headers.accept ?? "application/json",
        ...(request.headers["content-type"] ? { "content-type": request.headers["content-type"] } : {}),
      },
      body,
      redirect: "manual",
    });
    response.writeHead(upstream.status, {
      "Content-Type": upstream.headers.get("content-type") ?? "application/octet-stream",
      "Cache-Control": "no-store",
      "X-Content-Type-Options": "nosniff",
    });
    if (request.method === "HEAD" || upstream.body === null) {
      response.end();
      return;
    }
    for await (const chunk of upstream.body) response.write(chunk);
    response.end();
  } catch (error) {
    const tooLarge = error?.code === "body-too-large";
    if (!response.headersSent) {
      response.writeHead(tooLarge ? 413 : 502, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store" });
    }
    response.end(JSON.stringify({ reason: tooLarge ? "proxy-body-too-large" : "proxy-upstream-unanswered" }));
  }
}

createServer(async (request, response) => {
  const requestUrl = new URL(request.url ?? "/", "http://localhost");
  if (nodeUpstream && (requestUrl.pathname === "/node" || requestUrl.pathname.startsWith("/node/"))) {
    await proxyNode(request, response, requestUrl);
    return;
  }
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
