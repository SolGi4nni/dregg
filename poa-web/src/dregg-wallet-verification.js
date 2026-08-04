import {
  DREGG_CHALLENGE_DOMAIN,
  DREGG_MINT,
  DREGG_PROOF_PROTOCOL,
  DREGG_TOKEN_PROGRAM,
  buildDreggOwnerBindingMessage,
  bytesToBase64,
  formatDreggChallenge,
  normalizeDreggChallenge,
} from "./dregg-wallet.js";

/**
 * Pure server-side preflight. Signature verification, nonce consumption and
 * Solana RPC reads are integration seams, deliberately not faked here.
 */
export function buildDreggServerVerificationPlan(request, policy, nowMs = Date.now()) {
  if (!policy || typeof policy !== "object") throw new TypeError("verification policy is required");
  if (!Number.isSafeInteger(nowMs) || nowMs < 0) throw new Error("nowMs must be a non-negative safe integer");
  if (!request || request.protocol !== DREGG_PROOF_PROTOCOL) throw new Error("wrong request protocol");
  const challenge = normalizeDreggChallenge(request.challenge);
  if (challenge.domain !== DREGG_CHALLENGE_DOMAIN) throw new Error("wrong challenge domain");
  if (challenge.mint !== DREGG_MINT) throw new Error("wrong $DREGG mint");
  if (challenge.origin !== policy.origin) throw new Error("wrong origin");
  if (challenge.federationId !== policy.federationId) throw new Error("wrong federation");
  if (challenge.cluster !== policy.cluster) throw new Error("wrong cluster");
  if (!Number.isSafeInteger(policy.maxClockSkewMs) || policy.maxClockSkewMs < 0) {
    throw new Error("maxClockSkewMs must be a non-negative safe integer");
  }
  if (!Number.isSafeInteger(policy.maxSlotLag) || policy.maxSlotLag < 0) {
    throw new Error("maxSlotLag must be a non-negative safe integer");
  }
  if (nowMs < Date.parse(challenge.issuedAt) - policy.maxClockSkewMs) throw new Error("challenge not yet valid");
  if (nowMs > Date.parse(challenge.expiresAt) + policy.maxClockSkewMs) throw new Error("challenge expired");
  if (request.signedMessage?.encoding !== "utf8" ||
      request.signedMessage.value !== formatDreggChallenge(challenge, request.walletAddress)) {
    throw new Error("signed message does not exactly match challenge");
  }
  if (request.signature?.encoding !== "base64" || typeof request.signature.value !== "string") {
    throw new Error("missing Ed25519 signature");
  }
  const exactOwnerBindingMessage = buildDreggOwnerBindingMessage(
    request.walletAddress,
    challenge.voterId,
  );
  if (request.ownerBinding?.voterId !== challenge.voterId ||
      request.ownerBinding?.message?.encoding !== "base64" ||
      request.ownerBinding.message.value !== bytesToBase64(exactOwnerBindingMessage) ||
      request.ownerBinding?.signature?.encoding !== "base64" ||
      typeof request.ownerBinding.signature.value !== "string") {
    throw new Error("owner binding does not match canonical dregg binding_message bytes");
  }
  const minimumRawAmount = String(policy.minimumRawAmount ?? "1");
  if (!/^[1-9][0-9]*$/u.test(minimumRawAmount)) throw new Error("minimumRawAmount must be positive raw units");

  return Object.freeze({
    signatureCheck: Object.freeze({
      algorithm: "Ed25519",
      publicKeyBase58: request.walletAddress,
      messageUtf8: request.signedMessage.value,
      signatureBase64: request.signature.value,
    }),
    durableOwnerBindingCheck: Object.freeze({
      algorithm: "Ed25519",
      rustFunction: "dregg_governance::holding_weight::binding_message",
      publicKeyBase58: request.walletAddress,
      voterIdBase58: challenge.voterId,
      messageBase64: request.ownerBinding.message.value,
      signatureBase64: request.ownerBinding.signature.value,
    }),
    nonceCheck: Object.freeze({ nonce: challenge.nonce, operation: "consume-once" }),
    rpcRead: Object.freeze({
      method: "getTokenAccountsByOwner",
      cluster: challenge.cluster,
      commitment: "finalized",
      minContextSlot: challenge.slot,
      owner: request.walletAddress,
      filter: Object.freeze({ mint: DREGG_MINT }),
      purpose: "rpc-attested-beta-game-admission-only",
    }),
    acceptance: Object.freeze({
      exactMint: DREGG_MINT,
      exactTokenAccountOwner: request.walletAddress,
      exactTokenProgramId: DREGG_TOKEN_PROGRAM,
      requireInitializedAccount: true,
      sumRawBalancesAtLeast: minimumRawAmount,
      responseContextSlotAtLeast: challenge.slot,
      maxSlotLag: policy.maxSlotLag,
      trustGrade: "rpcAttested",
      admissionScope: "poa:beta:game-admission",
      credentialKind: "short-lived",
      governanceWeightBearing: false,
      balanceClaimBearing: false,
      accountsProofAnchored: false,
      evidenceBoundary: "configured-server-finalized-solana-rpc-only",
      upgradeRequirement: "dregg-consensus-accepted-anchored-accounts-proof",
    }),
  });
}
