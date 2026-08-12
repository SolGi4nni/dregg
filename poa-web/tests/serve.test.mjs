import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { once } from "node:events";
import { createServer } from "node:http";
import { test } from "node:test";

/**
 * ⚠ `npm run serve` could not serve the terminal AT ALL, and no test noticed.
 *
 * `sync-artifacts.mjs` writes the bundle to `public/artifacts/poag1/` and the
 * curator key to `public/poa-curator-key.json`; the client fetches them at
 * `/artifacts/…` and `/poa-curator-key.json`, because `public/` is overlaid at
 * the web root in the deployed layout. The dev server served only the package
 * directory, so every artifact 404'd, `loadPOAG1` refused with "manifest
 * returned HTTP 404", and the page rendered THIS TERMINAL REFUSED THE RULES.
 *
 * The whole suite reads artifacts off disk and never through this server, so it
 * stayed green while the thing a human would actually open was broken. This runs
 * the real server and asks it for the files the real client asks for.
 */

const server = new URL("../serve.mjs", import.meta.url);
const sync = new URL("../scripts/sync-artifacts.mjs", import.meta.url);

/**
 * `public/artifacts/` is generated and gitignored, so this test SYNCS it first
 * rather than passing when it happens to be there and failing when it is not. A
 * gate whose colour depends on a leftover directory is not a gate.
 */
async function syncArtifacts() {
  const child = spawn(process.execPath, [sync.pathname], { stdio: ["ignore", "pipe", "pipe"] });
  const stderr = [];
  child.stderr.on("data", (chunk) => stderr.push(chunk));
  const [code] = await once(child, "exit");
  assert.equal(code, 0, `sync-artifacts refused: ${Buffer.concat(stderr).toString()}`);
}

async function withServer(callback, extraEnv = {}) {
  await syncArtifacts();
  const port = 40000 + Math.floor(Math.random() * 20000);
  const child = spawn(process.execPath, [server.pathname], {
    env: { ...process.env, ...extraEnv, POA_WEB_PORT: String(port), POA_WEB_HOST: "127.0.0.1" },
    stdio: ["ignore", "pipe", "pipe"],
  });
  try {
    await once(child.stdout, "data");
    return await callback(`http://127.0.0.1:${port}`);
  } finally {
    child.kill("SIGKILL");
  }
}

async function withUpstream(callback) {
  const requests = [];
  const upstream = createServer(async (request, response) => {
    const chunks = [];
    for await (const chunk of request) chunks.push(chunk);
    const record = {
      method: request.method,
      url: request.url,
      contentType: request.headers["content-type"] ?? null,
      body: Buffer.concat(chunks).toString(),
    };
    requests.push(record);
    response.writeHead(request.method === "POST" ? 201 : 200, { "content-type": "application/json" });
    response.end(JSON.stringify(record));
  });
  upstream.listen(0, "127.0.0.1");
  await once(upstream, "listening");
  const address = upstream.address();
  try {
    return await callback(`http://127.0.0.1:${address.port}`, requests);
  } finally {
    upstream.close();
    await once(upstream, "close");
  }
}

test("the dev server serves everything the client actually fetches", async () => {
  await withServer(async (origin) => {
    const index = await fetch(`${origin}/`);
    assert.equal(index.status, 200);
    assert.match(index.headers.get("content-type"), /text\/html/);

    // The entry module and its transitive imports must be reachable, or the
    // browser fails to link and renders nothing.
    for (const path of ["/src/app.js", "/src/signal-runtime.js", "/src/hidden-instance.js", "/styles.css"]) {
      const response = await fetch(`${origin}${path}`);
      assert.equal(response.status, 200, `${path} must be served`);
      // ⚠ A dev server must not cache source: a five-minute max-age here made an
      // edit invisible and got a working fix read as broken.
      assert.equal(response.headers.get("cache-control"), "no-store", `${path} must not be cached in development`);
    }

    // The overlay: these live under public/ and are requested at the root.
    const manifest = await fetch(`${origin}/artifacts/poag1/manifest.json`);
    assert.equal(manifest.status, 200, "the POAG1 manifest must be served at /artifacts/poag1/");
    assert.equal(manifest.headers.get("cache-control"), "no-store");
    assert.equal((await manifest.json()).format, "POAG1");

    for (const path of [
      "/artifacts/poag1/catalog.json",
      "/artifacts/poag1/manifest.sig.json",
      "/artifacts/poag1/games/black-box-reconstruction.json",
      "/artifacts/poag1/games/relay-repair.json",
      "/artifacts/poag1/games/salvage-lock.json",
      "/artifacts/poag1/games/signal-triangulation.json",
      "/poa-curator-key.json",
    ]) {
      assert.equal((await fetch(`${origin}${path}`)).status, 200, `${path} must be served`);
    }
  });
});

test("the dev server refuses to escape its roots", async () => {
  await withServer(async (origin) => {
    for (const path of ["/..%2f..%2fCLAUDE.md", "/public/../../CLAUDE.md", "/src/../../AGENTS.md"]) {
      const response = await fetch(`${origin}${path}`);
      assert.equal(response.status, 404, `${path} must not escape the served roots`);
    }
    assert.equal((await fetch(`${origin}/definitely-not-here.json`)).status, 404);
  });
});

test("the served headers keep the page self-contained", async () => {
  await withServer(async (origin) => {
    const headers = (await fetch(`${origin}/`)).headers;
    const csp = headers.get("content-security-policy");
    assert.match(csp, /default-src 'self'/);
    assert.match(csp, /object-src 'none'/);
    assert.match(csp, /base-uri 'none'/);
    assert.ok(!csp.includes("unsafe-inline"), "the terminal must not permit inline script or style");
    assert.equal(headers.get("x-content-type-options"), "nosniff");
    assert.equal(headers.get("referrer-policy"), "no-referrer");
  });
});

test("the opt-in development proxy carries exact node paths and session bodies", async () => {
  await withUpstream(async (upstream, requests) => {
    await withServer(async (origin) => {
      const read = await fetch(`${origin}/node/api/poa/signal/abcd/slot?at=1`);
      assert.equal(read.status, 200);
      assert.equal(read.headers.get("cache-control"), "no-store");
      assert.deepEqual(await read.json(), {
        method: "GET", url: "/api/poa/signal/abcd/slot?at=1", contentType: null, body: "",
      });

      const write = await fetch(`${origin}/node/api/poa/signal/abcd/session/open`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ player_key: "11" }),
      });
      assert.equal(write.status, 201);
      assert.deepEqual(await write.json(), {
        method: "POST", url: "/api/poa/signal/abcd/session/open",
        contentType: "application/json", body: '{"player_key":"11"}',
      });

      const doubleSlash = await fetch(`${origin}/node//attacker.invalid/status`);
      assert.equal(doubleSlash.status, 200);
      assert.equal((await doubleSlash.json()).url, "//attacker.invalid/status");
      assert.equal(requests.length, 3, "a scheme-relative path must still reach the fixed upstream");
    }, { POA_NODE_UPSTREAM: upstream });
  });
});

test("the node-shaped path remains absent unless the development proxy is explicitly enabled", async () => {
  await withServer(async (origin) => {
    assert.equal((await fetch(`${origin}/node/status`)).status, 404);
  });
});
