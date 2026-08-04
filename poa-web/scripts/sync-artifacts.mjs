import { mkdir, readFile, rename, rm, writeFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { fnv1a64, POAG1_EXPECTED_ARTIFACTS, sha256Hex, validateManifest } from "../src/poag1.js";
import { authenticateContentEpoch } from "../src/content-epoch.js";
import { POA_EXPECTED_CONTENT_EPOCH, POA_EXPECTED_CURATOR_COUNTER } from "../src/trust-config.js";

const here = dirname(fileURLToPath(import.meta.url));
const source = resolve(here, "../../poa/artifacts/poag1");
const parent = resolve(here, "../public/artifacts");
const destination = resolve(parent, "poag1");
const staging = resolve(parent, `.poag1-${process.pid}`);
const curatorKeySource = resolve(here, "../../poa/config/curator-key.json");
const curatorKeyDestination = resolve(here, "../public/poa-curator-key.json");

function refuse(condition, message) {
  if (!condition) throw new Error(`POAG1 sync refused: ${message}`);
}

await rm(staging, { recursive: true, force: true });
await mkdir(staging, { recursive: true });

try {
  const manifestBytes = new Uint8Array(await readFile(resolve(source, "manifest.json")));
  let raw;
  try { raw = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(manifestBytes)); }
  catch (cause) { throw new Error("canonical manifest is not valid UTF-8 JSON", { cause }); }
  const manifest = validateManifest(raw, POAG1_EXPECTED_ARTIFACTS);

  for (const entry of manifest.artifacts) {
    const bytes = new Uint8Array(await readFile(resolve(source, entry.path)));
    refuse(bytes.byteLength === entry.bytes, `${entry.path} byte length is not the manifest length`);
    refuse(`sha256:${await sha256Hex(bytes)}` === entry.sha256, `${entry.path} does not match the manifest SHA-256`);
    refuse(fnv1a64(bytes) === entry.fnv1a64, `${entry.path} does not match the manifest pin`);
    await mkdir(dirname(resolve(staging, entry.path)), { recursive: true });
    await writeFile(resolve(staging, entry.path), bytes);
  }
  const signatureBytes = new Uint8Array(await readFile(resolve(source, "manifest.sig.json")));
  const curatorKeyBytes = new Uint8Array(await readFile(curatorKeySource));
  await authenticateContentEpoch({
    manifestBytes,
    signatureBytes,
    keyBytes: curatorKeyBytes,
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
  });
  await writeFile(resolve(staging, "manifest.sig.json"), signatureBytes);
  await writeFile(resolve(staging, "manifest.json"), manifestBytes);
  await rm(destination, { recursive: true, force: true });
  await rename(staging, destination);
  await writeFile(curatorKeyDestination, curatorKeyBytes);
  process.stdout.write(`synced POAG1 ${manifest.sourceDigest.slice(0, 16)} to ${destination}\n`);
} catch (error) {
  await rm(staging, { recursive: true, force: true });
  throw error;
}
