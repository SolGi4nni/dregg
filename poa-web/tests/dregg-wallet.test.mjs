import test from "node:test";
import assert from "node:assert/strict";
import {
  DREGG_CHALLENGE_DOMAIN,
  DREGG_MINT,
  DREGG_PROOF_PROTOCOL,
  DREGG_TOKEN_PROGRAM,
  connectDreggWallet,
  createDreggVerificationRequest,
  discoverDreggWallets,
  formatDreggChallenge,
  buildDreggOwnerBindingMessage,
  base58ToBytes,
  bytesToBase58,
  normalizeSolanaPublicKey,
} from "../src/dregg-wallet.js";
import { buildDreggServerVerificationPlan } from "../src/dregg-wallet-verification.js";

const challenge = Object.freeze({
  protocol: DREGG_PROOF_PROTOCOL,
  domain: DREGG_CHALLENGE_DOMAIN,
  origin: "https://beta.pathofangels.network",
  federationId: "poa-devnet-1",
  cluster: "solana:mainnet",
  nonce: "server-nonce-9Yk3",
  issuedAt: "2026-08-04T13:00:00.000Z",
  expiresAt: "2026-08-04T13:05:00.000Z",
  slot: 420000000,
  mint: DREGG_MINT,
  voterId: "11111111111111111111111111111111",
});

test("classic Wallet Adapter/Phantom-style provider signs exact domain-separated bytes", async () => {
  const signed = [];
  const wallet = {
    name: "Fixture adapter",
    publicKey: { toBase58: () => "11111111111111111111111111111111" },
    async connect() {},
    async signMessage(message) {
      signed.push(message);
      return Uint8Array.of(1, 2, 3, 4);
    },
  };
  const session = await connectDreggWallet(wallet);
  const request = await createDreggVerificationRequest(session, challenge);
  assert.equal(new TextDecoder().decode(signed[0]), formatDreggChallenge(challenge, session.address));
  assert.deepEqual(signed[1], buildDreggOwnerBindingMessage(session.address, challenge.voterId));
  assert.equal(request.signature.value, "AQIDBA==");
  assert.equal(request.challenge.mint, DREGG_MINT);
  assert.equal("balance" in request, false);
  assert.equal("tokenAccounts" in request, false);
});

test("Wallet Standard standard:connect + solana:signMessage is supported", async () => {
  const account = {
    address: "11111111111111111111111111111111",
    chains: ["solana:mainnet"],
    features: ["solana:signMessage"],
  };
  const wallet = {
    name: "Fixture standard wallet",
    accounts: [account],
    features: {
      "standard:connect": { connect: async () => ({ accounts: [account] }) },
      "solana:signMessage": {
        signMessage: async ({ account: actual, message }) => {
          assert.equal(actual, account);
          assert.ok(message instanceof Uint8Array);
          return [{ signature: Uint8Array.of(255, 0) }];
        },
      },
    },
  };
  const session = await connectDreggWallet(wallet);
  const request = await createDreggVerificationRequest(session, challenge);
  assert.equal(session.kind, "wallet-standard");
  assert.equal(request.signature.value, "/wA=");
});

test("challenge binds nonce, wallet, origin, federation, mint, cluster, slot, and expiry", () => {
  const first = formatDreggChallenge(challenge, challenge.voterId);
  assert.notEqual(first, formatDreggChallenge(challenge, DREGG_MINT));
  assert.notEqual(first, formatDreggChallenge({ ...challenge, nonce: "different" }, challenge.voterId));
  assert.notEqual(first, formatDreggChallenge({ ...challenge, slot: challenge.slot + 1 }, challenge.voterId));
  assert.throws(() => formatDreggChallenge({ ...challenge, mint: "fake" }, challenge.voterId), /mint/u);
  assert.throws(() => formatDreggChallenge({ ...challenge, origin: "https://evil\n.test" }, challenge.voterId), /control/u);
});

test("durable owner binding bytes exactly match Rust domain || owner(32) || voter(32)", () => {
  const message = buildDreggOwnerBindingMessage(
    "11111111111111111111111111111111",
    "11111111111111111111111111111111",
  );
  const domain = new TextEncoder().encode("dregg-holding-weight-bind-v1");
  assert.equal(message.length, domain.length + 64);
  assert.deepEqual(message.slice(0, domain.length), domain);
  assert.deepEqual(message.slice(domain.length), new Uint8Array(64));
});

test("canonical base58 encoder round-trips Ed25519 keys including zero prefixes", () => {
  for (const bytes of [
    new Uint8Array(32),
    Uint8Array.from({ length: 32 }, (_, index) => index),
    Uint8Array.from({ length: 32 }, (_, index) => 255 - index),
  ]) {
    const encoded = bytesToBase58(bytes);
    assert.deepEqual(base58ToBytes(encoded), bytes);
    assert.equal(bytesToBase58(base58ToBytes(encoded)), encoded);
  }
});

test("server plan requires exact mint/owner and finalized fresh RPC context", async () => {
  const wallet = {
    publicKey: "11111111111111111111111111111111",
    async connect() {},
    async signMessage() { return Uint8Array.of(9); },
  };
  const request = await createDreggVerificationRequest(await connectDreggWallet(wallet), challenge);
  const plan = buildDreggServerVerificationPlan(request, {
    origin: challenge.origin,
    federationId: challenge.federationId,
    cluster: challenge.cluster,
    maxClockSkewMs: 5_000,
    maxSlotLag: 150,
    minimumRawAmount: "1",
  }, Date.parse("2026-08-04T13:02:00.000Z"));
  assert.equal(plan.rpcRead.filter.mint, DREGG_MINT);
  assert.equal(plan.rpcRead.owner, request.walletAddress);
  assert.equal(plan.rpcRead.commitment, "finalized");
  assert.equal(plan.rpcRead.minContextSlot, challenge.slot);
  assert.equal(plan.acceptance.exactTokenProgramId, DREGG_TOKEN_PROGRAM);
  assert.equal(plan.acceptance.trustGrade, "rpcAttested");
  assert.equal(plan.acceptance.admissionScope, "poa:beta:game-admission");
  assert.equal(plan.acceptance.credentialKind, "short-lived");
  assert.equal(plan.acceptance.governanceWeightBearing, false);
  assert.equal(plan.acceptance.balanceClaimBearing, false);
  assert.equal(plan.acceptance.accountsProofAnchored, false);
  assert.equal(plan.acceptance.evidenceBoundary, "configured-server-finalized-solana-rpc-only");
  assert.equal(plan.rpcRead.purpose, "rpc-attested-beta-game-admission-only");
  assert.equal(plan.nonceCheck.operation, "consume-once");
  assert.equal(plan.durableOwnerBindingCheck.rustFunction,
    "dregg_governance::holding_weight::binding_message");
});

test("server preflight rejects expiry and domain/origin substitution", async () => {
  const wallet = {
    publicKey: "11111111111111111111111111111111",
    async connect() {},
    async signMessage() { return Uint8Array.of(9); },
  };
  const request = await createDreggVerificationRequest(await connectDreggWallet(wallet), challenge);
  const policy = {
    origin: challenge.origin,
    federationId: challenge.federationId,
    cluster: challenge.cluster,
    maxClockSkewMs: 0,
    maxSlotLag: 150,
  };
  assert.throws(() => buildDreggServerVerificationPlan(request, policy,
    Date.parse("2026-08-04T13:06:00.000Z")), /expired/u);
  assert.throws(() => buildDreggServerVerificationPlan(request,
    { ...policy, origin: "https://evil.test" }, Date.parse("2026-08-04T13:02:00.000Z")), /origin/u);
});

test("Wallet Standard discovery is feature-based, not Phantom-specific", () => {
  const compatible = {
    features: {
      "standard:connect": { connect() {} },
      "solana:signMessage": { signMessage() {} },
    },
  };
  const incompatible = { features: {} };
  assert.deepEqual(discoverDreggWallets({ get: () => [incompatible, compatible] }), [compatible]);
});

test("classic providers are discoverable only through an explicit injected source", () => {
  const classic = {
    name: "Explicit classic provider",
    async connect() {},
    async signMessage() {},
  };
  const registry = { get: () => [] };
  assert.deepEqual(discoverDreggWallets(registry), []);
  assert.deepEqual(discoverDreggWallets(registry, [classic]), [classic]);
  assert.deepEqual(discoverDreggWallets(registry, () => [classic]), [classic]);
  assert.throws(() => discoverDreggWallets(registry, () => classic), /yield an array/u);
});

test("wallet and voter bindings refuse malformed or non-32-byte base58 keys before signing", async () => {
  assert.throws(() => normalizeSolanaPublicKey("walletAddress", "not a key"), /base58/u);
  assert.throws(() => normalizeSolanaPublicKey("walletAddress", "111"), /32-byte/u);
  assert.throws(() => formatDreggChallenge(challenge, "111"), /32-byte/u);
  assert.throws(() => formatDreggChallenge({ ...challenge, voterId: "111" }, challenge.voterId), /32-byte/u);

  let signs = 0;
  const wallet = {
    publicKey: "111",
    async connect() {},
    async signMessage() { signs += 1; return Uint8Array.of(1); },
  };
  await assert.rejects(() => connectDreggWallet(wallet), /32-byte/u);
  assert.equal(signs, 0);
});

test("server policy numeric fields and clock are fail-closed", async () => {
  const wallet = {
    publicKey: "11111111111111111111111111111111",
    async connect() {},
    async signMessage() { return Uint8Array.of(9); },
  };
  const request = await createDreggVerificationRequest(await connectDreggWallet(wallet), challenge);
  const basePolicy = {
    origin: challenge.origin,
    federationId: challenge.federationId,
    cluster: challenge.cluster,
    maxClockSkewMs: 0,
    maxSlotLag: 150,
    minimumRawAmount: "1",
  };
  assert.throws(() => buildDreggServerVerificationPlan(request,
    { ...basePolicy, maxClockSkewMs: 0.5 }, Date.parse("2026-08-04T13:02:00.000Z")), /maxClockSkewMs/u);
  assert.throws(() => buildDreggServerVerificationPlan(request,
    { ...basePolicy, maxSlotLag: -1 }, Date.parse("2026-08-04T13:02:00.000Z")), /maxSlotLag/u);
  assert.throws(() => buildDreggServerVerificationPlan(request,
    { ...basePolicy, minimumRawAmount: "1.5" }, Date.parse("2026-08-04T13:02:00.000Z")), /minimumRawAmount/u);
  assert.throws(() => buildDreggServerVerificationPlan(request, basePolicy, Number.NaN), /nowMs/u);
});
