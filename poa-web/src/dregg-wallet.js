/**
 * Provider-neutral Solana wallet ownership challenge for Path of Angels.
 *
 * This module proves control of a wallet key only. Token holdings are always
 * verified by the server against finalized Solana RPC state.
 */

export const DREGG_MINT = "XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump";
/** Exact SPL Token-2022 program id owning this mint and its token accounts. */
export const DREGG_TOKEN_PROGRAM = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb";
export const DREGG_PROOF_PROTOCOL = "poa-dregg-proof-v1";
export const DREGG_CHALLENGE_DOMAIN = "pathofangels.network/dregg-proof";
export const DREGG_OWNER_BIND_DOMAIN = "dregg-holding-weight-bind-v1";

const encoder = new TextEncoder();

function requiredText(name, value) {
  if (typeof value !== "string" || value.length === 0) {
    throw new TypeError(`${name} must be a non-empty string`);
  }
  if (/\r|\n|[\u0000-\u001f]/u.test(value)) {
    throw new TypeError(`${name} contains control characters`);
  }
  return value;
}

function requiredInteger(name, value) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new TypeError(`${name} must be a non-negative safe integer`);
  }
  return value;
}

function publicKeyText(publicKey) {
  if (typeof publicKey === "string") return normalizeSolanaPublicKey("walletAddress", publicKey);
  if (publicKey && typeof publicKey.toBase58 === "function") {
    return normalizeSolanaPublicKey("walletAddress", publicKey.toBase58());
  }
  if (publicKey && typeof publicKey.toString === "function") {
    return normalizeSolanaPublicKey("walletAddress", publicKey.toString());
  }
  throw new TypeError("wallet did not expose a Solana public key");
}

function asBytes(value, name) {
  if (value instanceof Uint8Array) return value;
  if (ArrayBuffer.isView(value)) {
    return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  }
  if (value instanceof ArrayBuffer) return new Uint8Array(value);
  if (Array.isArray(value)) return Uint8Array.from(value);
  throw new TypeError(`${name} must be bytes`);
}

export function bytesToBase64(bytesLike) {
  const bytes = asBytes(bytesLike, "signature");
  const alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  let output = "";
  for (let index = 0; index < bytes.length; index += 3) {
    const a = bytes[index];
    const b = index + 1 < bytes.length ? bytes[index + 1] : 0;
    const c = index + 2 < bytes.length ? bytes[index + 2] : 0;
    const word = (a << 16) | (b << 8) | c;
    output += alphabet[(word >>> 18) & 63];
    output += alphabet[(word >>> 12) & 63];
    output += index + 1 < bytes.length ? alphabet[(word >>> 6) & 63] : "=";
    output += index + 2 < bytes.length ? alphabet[word & 63] : "=";
  }
  return output;
}

/** Strict, canonical standard-base64 decoder for backend-provided signing bytes. */
export function base64ToBytes(text) {
  requiredText("base64", text);
  if (!/^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$/u.test(text)) {
    throw new TypeError("invalid standard base64");
  }
  const alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  const output = [];
  for (let index = 0; index < text.length; index += 4) {
    const a = alphabet.indexOf(text[index]);
    const b = alphabet.indexOf(text[index + 1]);
    const c = text[index + 2] === "=" ? 0 : alphabet.indexOf(text[index + 2]);
    const d = text[index + 3] === "=" ? 0 : alphabet.indexOf(text[index + 3]);
    const word = (a << 18) | (b << 12) | (c << 6) | d;
    output.push((word >>> 16) & 255);
    if (text[index + 2] !== "=") output.push((word >>> 8) & 255);
    if (text[index + 3] !== "=") output.push(word & 255);
  }
  const bytes = Uint8Array.from(output);
  if (bytesToBase64(bytes) !== text) throw new TypeError("non-canonical standard base64");
  return bytes;
}

export function base58ToBytes(text) {
  requiredText("base58", text);
  const alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
  const bytes = [0];
  for (const character of text) {
    const value = alphabet.indexOf(character);
    if (value < 0) throw new TypeError("invalid base58 character");
    let carry = value;
    for (let index = 0; index < bytes.length; index += 1) {
      carry += bytes[index] * 58;
      bytes[index] = carry & 255;
      carry >>= 8;
    }
    while (carry > 0) {
      bytes.push(carry & 255);
      carry >>= 8;
    }
  }
  for (let index = 0; index < text.length - 1 && text[index] === "1"; index += 1) bytes.push(0);
  return Uint8Array.from(bytes.reverse());
}

/** Refuse malformed or non-32-byte Solana/Ed25519 public keys at the boundary. */
export function normalizeSolanaPublicKey(name, value) {
  const text = requiredText(name, value);
  if (base58ToBytes(text).length !== 32) {
    throw new TypeError(`${name} must be a base58-encoded 32-byte public key`);
  }
  return text;
}

/** Exact Rust `binding_message`: BIND_DOMAIN || owner(32) || voter(32). */
export function buildDreggOwnerBindingMessage(ownerAddress, voterId) {
  const owner = base58ToBytes(normalizeSolanaPublicKey("ownerAddress", ownerAddress));
  const voter = base58ToBytes(normalizeSolanaPublicKey("voterId", voterId));
  const domain = encoder.encode(DREGG_OWNER_BIND_DOMAIN);
  const message = new Uint8Array(domain.length + 64);
  message.set(domain, 0);
  message.set(owner, domain.length);
  message.set(voter, domain.length + 32);
  return message;
}

export function normalizeDreggChallenge(challenge) {
  if (!challenge || typeof challenge !== "object") {
    throw new TypeError("challenge is required");
  }
  const normalized = {
    protocol: requiredText("protocol", challenge.protocol),
    domain: requiredText("domain", challenge.domain),
    origin: requiredText("origin", challenge.origin),
    federationId: requiredText("federationId", challenge.federationId),
    cluster: requiredText("cluster", challenge.cluster),
    nonce: requiredText("nonce", challenge.nonce),
    issuedAt: requiredText("issuedAt", challenge.issuedAt),
    expiresAt: requiredText("expiresAt", challenge.expiresAt),
    slot: requiredInteger("slot", challenge.slot),
    mint: requiredText("mint", challenge.mint),
    voterId: normalizeSolanaPublicKey("voterId", challenge.voterId),
  };
  if (normalized.protocol !== DREGG_PROOF_PROTOCOL) throw new Error("wrong proof protocol");
  if (normalized.domain !== DREGG_CHALLENGE_DOMAIN) throw new Error("wrong proof domain");
  if (normalized.mint !== DREGG_MINT) throw new Error("wrong $DREGG mint");
  if (!normalized.cluster.startsWith("solana:")) throw new Error("cluster must be CAIP-like solana:* text");
  const issued = Date.parse(normalized.issuedAt);
  const expires = Date.parse(normalized.expiresAt);
  if (!Number.isFinite(issued) || !Number.isFinite(expires) || expires <= issued) {
    throw new Error("invalid challenge time window");
  }
  return Object.freeze(normalized);
}

export function formatDreggChallenge(challenge, walletAddress) {
  const c = normalizeDreggChallenge(challenge);
  const wallet = normalizeSolanaPublicKey("walletAddress", walletAddress);
  return [
    "Path of Angels $DREGG Proof of Holding",
    `Protocol: ${c.protocol}`,
    `Domain: ${c.domain}`,
    `Origin: ${c.origin}`,
    `Federation: ${c.federationId}`,
    `Wallet: ${wallet}`,
    `Dregg Voter: ${c.voterId}`,
    `Cluster: ${c.cluster}`,
    `Mint: ${c.mint}`,
    `Reference Slot: ${c.slot}`,
    `Nonce: ${c.nonce}`,
    `Issued At: ${c.issuedAt}`,
    `Expires At: ${c.expiresAt}`,
    "Purpose: authenticate this wallet for a server-verified $DREGG holding check.",
    "This signature does not authorize a transaction or transfer.",
  ].join("\n");
}

function chooseStandardAccount(wallet, connectResult, cluster) {
  const accounts = connectResult?.accounts ?? wallet.accounts ?? [];
  const account = accounts.find((candidate) =>
    (!candidate.chains || candidate.chains.includes(cluster)) &&
    (!candidate.features || candidate.features.includes("solana:signMessage"))
  );
  if (!account) throw new Error(`wallet has no ${cluster} account with solana:signMessage`);
  return account;
}

/** Normalize Wallet Standard wallets and deliberately injected classic providers. */
export async function connectDreggWallet(wallet, { cluster = "solana:mainnet" } = {}) {
  if (!wallet || typeof wallet !== "object") throw new TypeError("wallet is required");
  const standardConnect = wallet.features?.["standard:connect"]?.connect;
  const standardSign = wallet.features?.["solana:signMessage"]?.signMessage;
  if (typeof standardConnect === "function" && typeof standardSign === "function") {
    const connected = await standardConnect();
    const account = chooseStandardAccount(wallet, connected, cluster);
    return Object.freeze({
      kind: "wallet-standard",
      name: wallet.name ?? "Wallet Standard",
      address: publicKeyText(account.address),
      account,
      async signMessage(message) {
        const result = await standardSign({ account, message });
        const first = Array.isArray(result) ? result[0] : result;
        return asBytes(first?.signature ?? first, "wallet signature");
      },
    });
  }

  if (typeof wallet.connect !== "function" || typeof wallet.signMessage !== "function") {
    throw new Error("wallet lacks a supported connect + signMessage interface");
  }
  const connected = await wallet.connect();
  const address = publicKeyText(connected?.publicKey ?? wallet.publicKey);
  return Object.freeze({
    kind: "wallet-adapter",
    name: wallet.name ?? "Solana wallet",
    address,
    async signMessage(message) {
      const result = await wallet.signMessage(message);
      return asBytes(result?.signature ?? result, "wallet signature");
    },
  });
}

export async function createDreggVerificationRequest(walletSession, challenge) {
  if (!walletSession || typeof walletSession.signMessage !== "function") {
    throw new TypeError("connected wallet session is required");
  }
  const normalized = normalizeDreggChallenge(challenge);
  const message = formatDreggChallenge(normalized, walletSession.address);
  const messageBytes = encoder.encode(message);
  const signature = await walletSession.signMessage(messageBytes);
  const ownerBindingMessage = buildDreggOwnerBindingMessage(
    walletSession.address,
    normalized.voterId,
  );
  const ownerBindingSignature = await walletSession.signMessage(ownerBindingMessage);
  return Object.freeze({
    protocol: DREGG_PROOF_PROTOCOL,
    walletAddress: walletSession.address,
    challenge: normalized,
    signedMessage: Object.freeze({ encoding: "utf8", value: message }),
    signature: Object.freeze({ encoding: "base64", value: bytesToBase64(signature) }),
    ownerBinding: Object.freeze({
      voterId: normalized.voterId,
      message: Object.freeze({
        encoding: "base64",
        value: bytesToBase64(ownerBindingMessage),
      }),
      signature: Object.freeze({
        encoding: "base64",
        value: bytesToBase64(ownerBindingSignature),
      }),
    }),
    wallet: Object.freeze({ kind: walletSession.kind, name: walletSession.name }),
  });
}

/**
 * Discover Wallet Standard wallets plus an explicit caller-owned classic source.
 * The classic source may be an array or a function returning one; this module
 * never guesses vendor globals such as `window.solana`.
 */
export function discoverDreggWallets(walletsRegistry, classicProviderSource = []) {
  if (!walletsRegistry || typeof walletsRegistry.get !== "function") {
    throw new TypeError("Wallet Standard registry with get() is required");
  }
  const standard = walletsRegistry.get().filter((wallet) =>
    typeof wallet.features?.["standard:connect"]?.connect === "function" &&
    typeof wallet.features?.["solana:signMessage"]?.signMessage === "function"
  );
  const supplied = typeof classicProviderSource === "function"
    ? classicProviderSource()
    : classicProviderSource;
  if (!Array.isArray(supplied)) throw new TypeError("classic provider source must yield an array");
  const classic = supplied.filter((wallet) => wallet && typeof wallet === "object" &&
    typeof wallet.connect === "function" && typeof wallet.signMessage === "function");
  return [...new Set([...standard, ...classic])];
}
