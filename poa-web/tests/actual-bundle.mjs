import { readFile } from "node:fs/promises";

const canonical = new URL("../../poa/artifacts/poag1/", import.meta.url);
const curatorKey = new URL("../../poa/config/curator-key.json", import.meta.url);

export async function actualBytes(path) {
  return new Uint8Array(await readFile(new URL(path, canonical)));
}
export async function actualBundleFiles() {
  return {
    manifest: await actualBytes("manifest.json"),
    signature: await actualBytes("manifest.sig.json"),
    key: new Uint8Array(await readFile(curatorKey)),
    schema: await actualBytes("schema.json"),
    catalog: await actualBytes("catalog.json"),
    relay: await actualBytes("games/relay-repair.json"),
    salvage: await actualBytes("games/salvage-lock.json"),
    signal: await actualBytes("games/signal-triangulation.json"),
  };
}

export function fetchMap(entries) {
  const map = new Map(Object.entries(entries));
  return async (url) => {
    const pathname = new URL(url).pathname;
    const match = [...map.entries()].find(([suffix]) => pathname.endsWith(suffix));
    if (!match) return { ok: false, status: 404, arrayBuffer: async () => new ArrayBuffer(0) };
    const bytes = match[1];
    return {
      ok: true,
      status: 200,
      arrayBuffer: async () => bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength),
    };
  };
}

export async function actualFetch(overrides = {}) {
  const files = await actualBundleFiles();
  return fetchMap({
    "manifest.json": files.manifest,
    "manifest.sig.json": files.signature,
    "poa-curator-key.json": files.key,
    "schema.json": files.schema,
    "catalog.json": files.catalog,
    "games/relay-repair.json": files.relay,
    "games/salvage-lock.json": files.salvage,
    "games/signal-triangulation.json": files.signal,
    ...overrides,
  });
}
