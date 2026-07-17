/**
 * # `raw` — UNAUTHORIZED turn construction. Genesis / plumbing ONLY.
 *
 * ## ⚠ READ THIS BEFORE IMPORTING ANYTHING FROM HERE
 *
 * This module is the SDK's **sealed escape hatch**: the raw `Action` /
 * `Turn` vocabulary, including [`unsignedAction`] — the one constructor that
 * expresses *an act carrying no credential at all*
 * (`Authorization::Unchecked`).
 *
 * It exists for exactly two legitimate reasons on the TS surface:
 *
 * 1. **The signing flow itself** — the canonical signing message is computed
 *    over the action *with the authorization field zeroed*
 *    ([`unsignedAction`] is that zeroing step, used internally by
 *    `Identity.signAction` and the `TurnBuilder.sign()` path before the
 *    real signature is attached).
 * 2. **Test fixtures / genesis tooling** that need the wire vocabulary
 *    (postcard encoders, canonical hashes) directly.
 *
 * **Everything else goes through the authorized surface**: an
 * [`Identity`](./identity) building a turn via `runtime.turn()` → typed verb
 * builders → `.sign()` → `.submit()`. On that surface an unauthorized act is
 * **inexpressible** — the authorization field is private to the flow and
 * always a real credential by the time anything executes.
 *
 * If you find yourself importing from `@dregg/sdk/raw` in application code,
 * you are almost certainly building something the executor will reject. The
 * executor's posture: `Unchecked` means "no credential presented; ownership
 * / cell-permission checks decide", and any cell with real permissions
 * rejects it.
 *
 * This is the TS twin of the Rust SDK's quarantined `sdk/src/raw.rs` — same
 * seal, same documentation posture, same wire format.
 */

export type {
  Action,
  ArchivalAttestation,
  AttestedRoot,
  AuthRequired,
  Authorization,
  Bytes32,
  CallTree,
  CapabilityRef,
  CapGrant,
  CapTarget,
  CellId,
  CellMode,
  CellProgram,
  ConditionProof,
  ConservationProof,
  DeathCertificate,
  DeathReason,
  Effect,
  EventualRef,
  FactoryCreationParams,
  HybridQuorumSig,
  Permissions,
  PortableNoteProof,
  ProofCondition,
  RefusalReason,
  ResolutionCondition,
  ShieldedInputPayload,
  ShieldedLeg,
  ShieldedTransferPayload,
  Turn,
  VerificationKey,
} from "./internal/wire";

export {
  actionHash,
  actionSigningMessage,
  archivalCheckpointHash,
  deathCertificateHash,
  defaultTokenId,
  deriveCellId,
  EFFECT_KIND_COUNT,
  effectHash,
  encodeSignedTurn,
  encodeTurn,
  fieldFromU64,
  forestHash,
  symbol,
  turnHash,
  turnHashHex,
  UnmodeledWireError,
  unsignedAction,
  unsignedActionNamed,
} from "./internal/wire";

export { blake3, blake3DeriveKey, Blake3Hasher } from "./internal/blake3";
export { ed25519PublicKey, ed25519Sign, ed25519Verify } from "./internal/ed25519";
/**
 * The ML-DSA-65 (FIPS 204) post-quantum half of a HYBRID authorization —
 * mirrors `dregg-pq` / `turn/src/pq.rs`. The key derives from the SAME 32-byte
 * ed25519 seed the classical identity uses, so a hybrid identity needs no new
 * key material.
 */
export {
  HYBRID_TURN_PQ_CTX,
  ML_DSA_PK_LEN,
  ML_DSA_SIG_LEN,
  ML_DSA_SK_LEN,
  mlDsaKeypairFromEd25519Seed,
  mlDsaSign,
  mlDsaVerify,
} from "./internal/mldsa";
export type { MlDsaKeypair } from "./internal/mldsa";
export {
  bytesEqual,
  concatBytes,
  hexDecode,
  hexDecodeExact,
  hexEncode,
} from "./internal/bytes";
