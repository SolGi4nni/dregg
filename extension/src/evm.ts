/**
 * The EVM signing leg — secp256k1 ECDSA + keccak256 over the wallet's seed.
 *
 * The cipherclerk's native identity is Ed25519 (+ ML-DSA-65); an on-chain
 * launchpad escrow (`DreggLaunchpad.commitBid`) lives on an EVM chain and needs
 * a secp256k1 signature the chain can `ecrecover`. Rather than hold a SECOND,
 * disjoint wallet, the EVM key is derived DETERMINISTICALLY from the same
 * 32-byte wallet seed the Ed25519 identity expands from, under a domain
 * separation tag — so one recovery phrase restores BOTH identities and the two
 * never need an out-of-band binding.
 *
 * Everything here is real, audited crypto: `secp256k1` + `keccak_256` are the
 * vendored @noble primitives (the same ones ethers/viem build on). Signatures
 * are EIP-191 `personal_sign`, EIP-712 typed-data, and raw 32-byte digests,
 * each producing a canonical `r‖s‖v` (v ∈ {27,28}) an EVM verifier recovers.
 */
import { secp256k1, keccak_256, bytesToHex, hexToBytes } from "../vendor/noble-crypto.js";

/** Domain-separation tag: the wallet seed → the EVM secp256k1 scalar. */
const EVM_DERIVATION_TAG = "dregg-evm-secp256k1-v1";

const SECP256K1_N = BigInt(
  "0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
);

function utf8(s: string): Uint8Array {
  return new TextEncoder().encode(s);
}

function concat(...parts: Uint8Array[]): Uint8Array {
  const total = parts.reduce((n, p) => n + p.length, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}

function bytesToBigIntBE(b: Uint8Array): bigint {
  let x = 0n;
  for (const byte of b) x = (x << 8n) | BigInt(byte);
  return x;
}

function bigIntTo32BE(x: bigint): Uint8Array {
  const out = new Uint8Array(32);
  for (let i = 31; i >= 0; i--) {
    out[i] = Number(x & 0xffn);
    x >>= 8n;
  }
  return out;
}

/** `0x`-prefixed lowercase hex. */
export function hex0x(b: Uint8Array): string {
  return "0x" + bytesToHex(b);
}

/** Parse `0x…` (or bare) hex into bytes. */
export function fromHex0x(s: string): Uint8Array {
  return hexToBytes(s.startsWith("0x") ? s.slice(2) : s);
}

/** keccak256 of the concatenated inputs. */
export function keccak256(...parts: Uint8Array[]): Uint8Array {
  return keccak_256(parts.length === 1 ? parts[0] : concat(...parts));
}

export interface EvmIdentity {
  /** 32-byte secp256k1 private scalar. */
  privateKey: Uint8Array;
  /** 65-byte uncompressed public key (0x04‖X‖Y). */
  publicKey: Uint8Array;
  /** EIP-55 checksummed `0x…` address. */
  address: string;
}

/**
 * Derive the wallet's EVM identity from its 32-byte seed. The scalar is
 * `keccak256(tag ‖ seed) mod (n-1) + 1` (a uniform, nonzero secp256k1 scalar),
 * fully determined by the seed — the same mnemonic always yields the same
 * EVM address.
 */
export function deriveEvmIdentity(seed: Uint8Array): EvmIdentity {
  if (seed.length < 32) {
    throw new Error("deriveEvmIdentity: seed must be at least 32 bytes");
  }
  const material = keccak256(utf8(EVM_DERIVATION_TAG), seed);
  const scalar = (bytesToBigIntBE(material) % (SECP256K1_N - 1n)) + 1n;
  const privateKey = bigIntTo32BE(scalar);
  const publicKey = secp256k1.getPublicKey(privateKey, false); // uncompressed
  return { privateKey, publicKey, address: addressFromPublicKey(publicKey) };
}

/** EIP-55 checksummed address from a 65-byte uncompressed public key. */
export function addressFromPublicKey(publicKey: Uint8Array): string {
  // Drop the 0x04 tag; address = last 20 bytes of keccak256(X‖Y).
  const body = publicKey.length === 65 ? publicKey.slice(1) : publicKey;
  const hashed = keccak256(body);
  const addr = hashed.slice(12); // 20 bytes
  return toChecksumAddress(bytesToHex(addr));
}

/** EIP-55 mixed-case checksum. `lowerHex` is 40 chars, no `0x`. */
export function toChecksumAddress(lowerHex: string): string {
  const lower = lowerHex.toLowerCase();
  const hash = bytesToHex(keccak256(utf8(lower)));
  let out = "0x";
  for (let i = 0; i < lower.length; i++) {
    out += parseInt(hash[i], 16) >= 8 ? lower[i].toUpperCase() : lower[i];
  }
  return out;
}

export interface EvmSignature {
  /** 65-byte `r‖s‖v` signature, `0x…`. */
  signature: string;
  r: string;
  s: string;
  /** Recovery-adjusted v (27 or 28). */
  v: number;
  /** The 32-byte digest that was signed, `0x…`. */
  digest: string;
}

/**
 * Sign a raw 32-byte digest with the EVM key. Produces a canonical
 * (low-`s`) signature plus the `ecrecover` `v` (27/28). Callers that already
 * have an EIP-712 or EIP-191 digest use this directly.
 */
export function signDigest(privateKey: Uint8Array, digest: Uint8Array): EvmSignature {
  if (digest.length !== 32) throw new Error("signDigest: digest must be 32 bytes");
  const sig = secp256k1.sign(digest, privateKey); // low-s by default
  const r = bigIntTo32BE(sig.r);
  const s = bigIntTo32BE(sig.s);
  const v = 27 + sig.recovery;
  const signature = concat(r, s, Uint8Array.of(v));
  return { signature: hex0x(signature), r: hex0x(r), s: hex0x(s), v, digest: hex0x(digest) };
}

/** The EIP-191 `personal_sign` prefixed digest for a message. */
export function personalSignDigest(message: Uint8Array): Uint8Array {
  const prefix = utf8(`\x19Ethereum Signed Message:\n${message.length}`);
  return keccak256(prefix, message);
}

/**
 * EIP-191 `personal_sign`. `message` is a UTF-8 string or raw bytes; the
 * `\x19Ethereum Signed Message:\n<len>` prefix is applied before hashing, so
 * the signature matches what MetaMask/ethers `signMessage` produce.
 */
export function personalSign(privateKey: Uint8Array, message: string | Uint8Array): EvmSignature {
  const msg = typeof message === "string" ? utf8(message) : message;
  return signDigest(privateKey, personalSignDigest(msg));
}

/**
 * Recover the signer's checksummed address from a digest + `r‖s‖v` signature.
 * The verification counterpart to `signDigest` — an EVM `ecrecover` in JS.
 */
export function recoverAddress(digest: Uint8Array, signature: Uint8Array): string {
  if (signature.length !== 65) throw new Error("recoverAddress: signature must be 65 bytes");
  const r = bytesToBigIntBE(signature.slice(0, 32));
  const s = bytesToBigIntBE(signature.slice(32, 64));
  const recovery = signature[64] - 27;
  const sig = new secp256k1.Signature(r, s).addRecoveryBit(recovery);
  const pub = sig.recoverPublicKey(digest).toRawBytes(false); // uncompressed
  return addressFromPublicKey(pub);
}

// ---------------------------------------------------------------------------
// EIP-712 typed structured data (the shape the on-chain launchpad verifies).
// ---------------------------------------------------------------------------

export interface Eip712Domain {
  name?: string;
  version?: string;
  chainId?: number;
  verifyingContract?: string; // 0x address
  salt?: string; // 0x32
}

export type Eip712Types = Record<string, Array<{ name: string; type: string }>>;

/** ABI-encode + keccak the EIP-712 domain separator. */
function hashDomain(domain: Eip712Domain): Uint8Array {
  const fields: Array<{ name: string; type: string }> = [];
  const values: Record<string, unknown> = {};
  if (domain.name !== undefined) { fields.push({ name: "name", type: "string" }); values.name = domain.name; }
  if (domain.version !== undefined) { fields.push({ name: "version", type: "string" }); values.version = domain.version; }
  if (domain.chainId !== undefined) { fields.push({ name: "chainId", type: "uint256" }); values.chainId = domain.chainId; }
  if (domain.verifyingContract !== undefined) { fields.push({ name: "verifyingContract", type: "address" }); values.verifyingContract = domain.verifyingContract; }
  if (domain.salt !== undefined) { fields.push({ name: "salt", type: "bytes32" }); values.salt = domain.salt; }
  return hashStruct("EIP712Domain", { EIP712Domain: fields }, values);
}

function encodeType(primary: string, types: Eip712Types): string {
  // Collect referenced struct types (alphabetical, per EIP-712), then encode.
  const deps = new Set<string>();
  const visit = (t: string) => {
    if (deps.has(t) || !types[t]) return;
    deps.add(t);
    for (const f of types[t]) {
      const base = f.type.replace(/\[\d*\]$/, "");
      if (types[base]) visit(base);
    }
  };
  visit(primary);
  deps.delete(primary);
  const ordered = [primary, ...Array.from(deps).sort()];
  return ordered.map(t => `${t}(${types[t].map(f => `${f.type} ${f.name}`).join(",")})`).join("");
}

function typeHash(primary: string, types: Eip712Types): Uint8Array {
  return keccak256(utf8(encodeType(primary, types)));
}

function encodeField(type: string, value: unknown, types: Eip712Types): Uint8Array {
  if (types[type]) {
    // A struct-typed field encodes to its hashStruct (already a 32-byte hash) —
    // do NOT keccak it again.
    return hashStruct(type, types, value as Record<string, unknown>);
  }
  if (type === "string") return keccak256(utf8(String(value)));
  if (type === "bytes") return keccak256(fromHex0x(String(value)));
  if (type === "bytes32") {
    const b = fromHex0x(String(value));
    const out = new Uint8Array(32);
    out.set(b.slice(0, 32));
    return out;
  }
  if (type === "address") {
    const b = fromHex0x(String(value));
    const out = new Uint8Array(32);
    out.set(b.slice(0, 20), 12);
    return out;
  }
  if (type === "bool") return bigIntTo32BE(value ? 1n : 0n);
  if (type.startsWith("uint") || type.startsWith("int")) {
    return bigIntTo32BE(BigInt(value as string | number | bigint));
  }
  throw new Error(`EIP-712: unsupported field type ${type}`);
}

/** keccak(typeHash ‖ encoded-fields) for one struct. */
function hashStruct(primary: string, types: Eip712Types, value: Record<string, unknown>): Uint8Array {
  const parts = [typeHash(primary, types)];
  for (const f of types[primary]) {
    parts.push(encodeField(f.type, value[f.name], types));
  }
  return keccak256(...parts);
}

/** The EIP-712 signing digest: keccak(`\x19\x01` ‖ domainSep ‖ hashStruct). */
export function eip712Digest(
  domain: Eip712Domain,
  types: Eip712Types,
  primaryType: string,
  message: Record<string, unknown>,
): Uint8Array {
  return keccak256(
    Uint8Array.of(0x19, 0x01),
    hashDomain(domain),
    hashStruct(primaryType, types, message),
  );
}

/** Sign EIP-712 typed structured data — the on-chain sealed-bid signature. */
export function signTypedData(
  privateKey: Uint8Array,
  domain: Eip712Domain,
  types: Eip712Types,
  primaryType: string,
  message: Record<string, unknown>,
): EvmSignature {
  return signDigest(privateKey, eip712Digest(domain, types, primaryType, message));
}
