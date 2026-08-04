import { ArtifactRefusal, sha256Hex } from "./poag1.js";

const SIGNATURE_SCHEMA = "POA-CONTENT-EPOCH-SIGNATURE-V1";
const KEY_SCHEMA = "POA-CURATOR-KEY-V1";
const DOMAIN = new TextEncoder().encode("pathofangels.network/content-epoch/v1\0");
const ACTIVATION_DOMAIN = new TextEncoder().encode("pathofangels.network/activation-digest/v1\0");
const HEX_32 = /^[0-9a-f]{64}$/;
const HEX_64 = /^[0-9a-f]{128}$/;
const SHA256 = /^sha256:[0-9a-f]{64}$/;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}
function object(value) { return value !== null && typeof value === "object" && !Array.isArray(value); }
function exactKeys(value, keys, at) {
  refuse(object(value), "signature-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  refuse(actual.length === expected.length && actual.every((key, i) => key === expected[i]), "signature-field", `${at} has an unknown or missing field`);
}
function parseJson(bytes, at) {
  try { return JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch (cause) { throw new ArtifactRefusal("signature-json", `${at} is not strict UTF-8 JSON`, cause); }
}
function hexBytes(hex) {
  return Uint8Array.from(hex.match(/../g) ?? [], (pair) => Number.parseInt(pair, 16));
}
function u64be(value) {
  refuse(Number.isSafeInteger(value) && value >= 0, "signature-u64", "content epoch integers must be exact nonnegative JSON integers");
  const bytes = new Uint8Array(8);
  new DataView(bytes.buffer).setBigUint64(0, BigInt(value), false);
  return bytes;
}
function join(parts) {
  const length = parts.reduce((sum, part) => sum + part.byteLength, 0);
  const out = new Uint8Array(length);
  let offset = 0;
  for (const part of parts) { out.set(part, offset); offset += part.byteLength; }
  return out;
}

export function parseCuratorKey(bytes) {
  const key = parseJson(bytes, "curator key pin");
  exactKeys(key, ["schema", "curator_pubkey"], "curator key pin");
  refuse(key.schema === KEY_SCHEMA, "key-schema", "unsupported curator key schema");
  refuse(typeof key.curator_pubkey === "string" && HEX_32.test(key.curator_pubkey), "key-format", "curator key must be 32-byte lowercase Ed25519 hex");
  return Object.freeze({ schema: key.schema, curatorPublicKey: key.curator_pubkey });
}

export function parseContentEpochSignature(bytes) {
  const envelope = parseJson(bytes, "content epoch signature");
  exactKeys(envelope, ["schema", "manifest_sha256", "curator_pubkey", "content_epoch", "counter", "signature"], "content epoch signature");
  refuse(envelope.schema === SIGNATURE_SCHEMA, "signature-schema", "unsupported content epoch signature schema");
  refuse(typeof envelope.manifest_sha256 === "string" && SHA256.test(envelope.manifest_sha256), "signature-digest", "content epoch manifest digest is invalid");
  refuse(typeof envelope.curator_pubkey === "string" && HEX_32.test(envelope.curator_pubkey), "signature-key", "content epoch curator key is invalid");
  refuse(Number.isSafeInteger(envelope.content_epoch) && envelope.content_epoch >= 0, "signature-epoch", "content_epoch must be an exact nonnegative JSON integer");
  refuse(Number.isSafeInteger(envelope.counter) && envelope.counter >= 0, "signature-counter", "counter must be an exact nonnegative JSON integer");
  refuse(typeof envelope.signature === "string" && HEX_64.test(envelope.signature), "signature-format", "content epoch Ed25519 signature is invalid");
  return Object.freeze({
    schema: envelope.schema,
    manifestDigest: envelope.manifest_sha256,
    curatorPublicKey: envelope.curator_pubkey,
    contentEpoch: envelope.content_epoch,
    counter: envelope.counter,
    signature: envelope.signature,
  });
}

export function contentEpochSigningBytes(envelope, manifestBytes) {
  return join([DOMAIN, u64be(envelope.contentEpoch), u64be(envelope.counter), u64be(manifestBytes.byteLength), manifestBytes]);
}

/** Exact activation-digest preimage shared with poa-curator. */
export function activationDigestBytes(envelope) {
  const schema = new TextEncoder().encode(envelope.schema);
  return join([
    ACTIVATION_DOMAIN,
    u64be(schema.byteLength), schema,
    hexBytes(envelope.manifestDigest.slice(7)),
    hexBytes(envelope.curatorPublicKey),
    u64be(envelope.contentEpoch),
    u64be(envelope.counter),
    hexBytes(envelope.signature),
  ]);
}

/** Authenticate exact manifest bytes against the external curator key pin. */
export async function authenticateContentEpoch({ manifestBytes, signatureBytes, keyBytes, expectedContentEpoch, expectedCounter }) {
  const envelope = parseContentEpochSignature(signatureBytes);
  const key = parseCuratorKey(keyBytes);
  refuse(Number.isSafeInteger(expectedContentEpoch) && expectedContentEpoch >= 0, "epoch-pin-missing", "deployment must pin the expected content epoch outside POAG1");
  refuse(Number.isSafeInteger(expectedCounter) && expectedCounter >= 0, "counter-pin-missing", "deployment must pin the expected curator counter outside POAG1");
  refuse(envelope.contentEpoch === expectedContentEpoch, "epoch-rollback", "content epoch does not equal the deployment pin");
  refuse(envelope.counter === expectedCounter, "counter-rollback", "curator counter does not equal the deployment pin");
  refuse(envelope.curatorPublicKey === key.curatorPublicKey, "key-mismatch", "content epoch key does not equal the external curator key pin");
  const actualDigest = `sha256:${await sha256Hex(manifestBytes)}`;
  refuse(actualDigest === envelope.manifestDigest, "manifest-digest", "content epoch signature names different manifest bytes");
  const subtle = globalThis.crypto?.subtle;
  refuse(subtle, "crypto-unavailable", "Web Crypto Ed25519 is required for curator authentication");
  let publicKey;
  try { publicKey = await subtle.importKey("raw", hexBytes(key.curatorPublicKey), { name: "Ed25519" }, false, ["verify"]); }
  catch (cause) { throw new ArtifactRefusal("ed25519-unavailable", "curator Ed25519 key could not be imported", cause); }
  const valid = await subtle.verify({ name: "Ed25519" }, publicKey, hexBytes(envelope.signature), contentEpochSigningBytes(envelope, manifestBytes));
  refuse(valid, "bad-signature", "content epoch signature does not authenticate the manifest");
  const verified = { ...envelope, manifestDigest: actualDigest };
  const activationDigest = `sha256:${await sha256Hex(activationDigestBytes(verified))}`;
  return Object.freeze({ ...verified, activationDigest });
}
