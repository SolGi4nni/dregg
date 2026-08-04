import { createReadStream, statSync } from "node:fs";
import { createServer } from "node:http";
import { extname, join, normalize, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("./", import.meta.url));
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
  const absolute = normalize(join(root, local));
  const escaped = relative(root, absolute).startsWith("..");
  let file = absolute;
  try {
    if (escaped || !statSync(file).isFile()) throw new Error("not found");
  } catch {
    response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
    response.end("Not found\n");
    return;
  }
  response.writeHead(200, {
    "Content-Type": mimes.get(extname(file)) ?? "application/octet-stream",
    "Cache-Control": file.endsWith("manifest.json") || file.includes("/artifacts/") ? "no-store" : "public, max-age=300",
    "Content-Security-Policy": "default-src 'self'; img-src 'self' data:; style-src 'self'; script-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'self'",
    "Referrer-Policy": "no-referrer",
    "X-Content-Type-Options": "nosniff",
    "Cross-Origin-Opener-Policy": "same-origin",
  });
  createReadStream(file).pipe(response);
}).listen(port, host, () => {
  process.stdout.write(`Path of Angels beta terminal: http://${host}:${port}\n`);
});
