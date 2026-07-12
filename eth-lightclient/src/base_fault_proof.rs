//! **Live-Base fault-proof anchor verifier** — the honest completion of
//! [`crate::base`]. That module verifies the LEGACY `L2OutputOracle` honest-oracle
//! model (exact for pre-fault-proof OP-stack chains; Base's last legacy output is
//! 12086). LIVE Base's anchor is a resolved **dispute game**: a `DisputeGameFactory`
//! (DGF) creates games, an `AnchorStateRegistry` (ASR) decides which resolved game
//! is a valid anchor (`isGameClaimValid`). This module verifies THAT — the
//! slot-level trust chain grounded and live-validated in
//! `docs/deos/BASE-FAULT-PROOF-ANCHOR.md` (raw `eth_getStorageAt`/`eth_call`
//! against Ethereum mainnet, 2026-07-12).
//!
//! ## The trust chain (each arrow fail-closed)
//!
//! ```text
//! FinalizedExecution (finality.rs, unforgeable)
//!   ├─(L1 acct proof)→ ASR.storage_hash ─→ slot 6: respectedGameType, retirementTs [1,2]
//!   │                                  └→ slot 5 mapping: blacklist[game] ABSENT    [7]
//!   │                                  └→ slot 1: disputeGameFactory == DGF         [3]
//!   ├─(L1 acct proof)→ DGF.storage_hash ─→ slot keccak(UUID‖103): GameId            [4]
//!   │                     where UUID = keccak(abi.encode(type, rootClaim, extraData))
//!   ├─(L1 acct proof)→ game.storage_hash (+CWIA code-hash recompute) ─→ slot 0:     [5,6]
//!   │                     status==DEFENDER_WINS ∧ resolvedAt≠0 ∧ respected@creation
//!   │                     ∧ createdAt > retirementTs
//!   ├─ l1_time > resolvedAt + max(asr_delay, policy_delay)                          [8]
//!   └─→ (rootClaim, l2BlockNumber from extraData) = L1CommittedOutput
//!         └→ verify_op_output_root → l2_state_root → verify_erc20_holding          [9]
//! ```
//!
//! Link 4 is the keystone: the DGF `_disputeGames` mapping KEY is
//! `keccak256(abi.encode(gameType, rootClaim, extraData))`, so ONE storage proof
//! binds the entire claim content (type + root + extraData→l2BlockNumber) to the
//! unique game proxy the factory created for exactly that claim. Tamper any byte of
//! the claim and the mapping slot itself moves — the proof cannot open.
//!
//! ## The honest trust delta (do not launder)
//!
//! What accepting a `DEFENDER_WINS` game asks you to believe, beyond L1 finality +
//! keccak/MPT (all named, none removable by this verifier):
//!
//! * **Validity-at-creation soundness** (Base's live game type 621,
//!   `AggregateVerifier`): a game initializes only WITH a TEE attestation (AWS
//!   Nitro, `TEE_IMAGE_HASH`) or a ZK proof (`ZK_RANGE/AGGREGATE_HASH`), and a wrong
//!   single-proof proposal still needs a counter-proof challenge inside its in-game
//!   5-day window. The cryptographic floor is **TEE-or-ZK soundness + challenger
//!   liveness for single-proof games** — named primitive trust, same class as
//!   BLS/keccak elsewhere in this crate.
//! * **Game/ASR code semantics** are inherited via the Link-5 `code_hash` pin —
//!   RECOMPUTED, not a fixture constant (Residual R3 closed): the proven game
//!   account's `code_hash` must equal `keccak256` of the Solady CWIA proxy
//!   runtime rebuilt from the PINNED AggregateVerifier implementation address +
//!   the game's creation immutable args (`creator ‖ rootClaim ‖ l1Head ‖
//!   extraData`, see [`cwia_proxy_code_hash`]). A look-alike contract with the
//!   same slot-0 layout but different bytecode — or a game cloned from a
//!   different implementation — is refused. What remains pinned as constants:
//!   the impl ADDRESS ([`BASE_AGGREGATE_VERIFIER_IMPL`]) and the CWIA template
//!   bytes — both change only on an OP-stack contracts upgrade (the correct
//!   failure mode is fail-closed + explicit re-pin). The impl account's own
//!   bytecode at that address is not separately proven; post-Cancun an
//!   account's code is immutable (`SELFDESTRUCT` only in the creating tx), so
//!   the address IS the semantics, the same way [`crate::base`] inherits
//!   `L2OutputOracle` semantics from its address.
//! * **Governance keys**: the guardian can blacklist/retire/rotate and the
//!   ProxyAdmin can swap implementations. Fail-closed here (pins refuse after an
//!   upgrade), but irreducible.
//! * **The registry airgap on live Base is ZERO** (`disputeGameFinalityDelaySeconds
//!   == 0`, an ASR-impl immutable — live-read fact). The real anti-fraud windows
//!   run INSIDE the game before `resolve()`. [`FaultProofAnchorParams::
//!   policy_finality_delay`] is therefore **OUR conservatism knob, set by the
//!   caller — NOT a protocol guarantee**; the predicate is
//!   `l1_time > resolvedAt + max(asr_delay, policy_delay)` and the two delays must
//!   never be conflated: `asr_delay` mirrors what the CHAIN enforces (0 on Base),
//!   `policy_delay` is a local liveness/soundness assumption (e.g. "the guardian
//!   would blacklist a bad game within N seconds and we give it N").
//! * **Deliberately not mirrored:** `SystemConfig.paused()` (unpinned Base-fork
//!   slot — a pause only makes the chain MORE conservative than us at time T),
//!   bond amounts (incentive lubricant, nothing cryptographic), and the parent
//!   game chain (enforced by game code — `resolve()` propagates parent
//!   `CHALLENGER_WINS` — inherited via the code-hash pin, not re-verified).

use crate::base::{verify_op_output_root, BaseProofError, L1CommittedOutput, L2StateCommitment};
use crate::evm::{
    verify_erc20_holding, verify_evm_account_proof, verify_evm_storage_slot,
    verify_evm_storage_slot_absent, AccountClaim, Erc20ProofError, HoldingTrust,
    ProvenErc20Holding,
};
use crate::finality::FinalizedExecution;
use alloy_primitives::{hex, keccak256, U256};

/// Declared slot of `mapping(Hash => GameId) _disputeGames` in the canonical
/// contracts-bedrock `DisputeGameFactory` (slot **103**; `gameImpls` 101,
/// `initBonds` 102, `_disputeGameList` 104 — stable op-contracts v1.x → develop,
/// validated live against Base's DGF on 2026-07-12).
pub const DGF_DISPUTE_GAMES_SLOT: u64 = 103;
/// Declared slot of `IDisputeGameFactory disputeGameFactory` in the
/// `AnchorStateRegistry` (slot **1**, validated live).
pub const ASR_DISPUTE_GAME_FACTORY_SLOT: u64 = 1;
/// Declared slot of `mapping(IDisputeGame => bool) disputeGameBlacklist` in the
/// `AnchorStateRegistry` (slot **5**, validated live: the anchor game's key reads
/// zero, i.e. ABSENT).
pub const ASR_BLACKLIST_SLOT: u64 = 5;
/// Declared slot packing `GameType respectedGameType (u32 @0)` ‖
/// `uint64 retirementTimestamp (@4)` in the `AnchorStateRegistry` (slot **6**,
/// validated live: `0x…6a15fbbf0000026d` = (1779825599, 621)).
pub const ASR_RESPECTED_GAME_TYPE_SLOT: u64 = 6;
/// The dispute game's slot 0 packs `createdAt(u64 @0) ‖ resolvedAt(u64 @8) ‖
/// status(u8 @16) ‖ initialized(bool @17) ‖ wasRespectedGameTypeWhenCreated(bool
/// @18)` (AggregateVerifier verified source, byte-exact live match; classic
/// FaultDisputeGame shares the first four fields but keeps
/// `wasRespectedGameTypeWhenCreated` elsewhere and version-dependent — re-pin per
/// deployment before building an FDG profile).
pub const GAME_RESOLUTION_SLOT: u64 = 0;

/// `GameStatus.IN_PROGRESS` — the game has not resolved.
pub const GAME_STATUS_IN_PROGRESS: u8 = 0;
/// `GameStatus.CHALLENGER_WINS` — the root claim was successfully challenged.
pub const GAME_STATUS_CHALLENGER_WINS: u8 = 1;
/// `GameStatus.DEFENDER_WINS` — the root claim stands. The ONLY status this
/// verifier accepts.
pub const GAME_STATUS_DEFENDER_WINS: u8 = 2;

/// Base mainnet's live respected game type: **621** (`AggregateVerifier` v0.1.0,
/// the dual-attestation TEE/ZK validity game — live-read 2026-07-12).
pub const BASE_AGGREGATE_VERIFIER_GAME_TYPE: u32 = 621;

/// Base mainnet's live game-type-621 implementation — `DGF.gameImpls(621)` =
/// **`AggregateVerifier` v0.1.0** at `0x1bd8db5139Ba7aC9277684650c15e6E341761919`
/// (live-read 2026-07-12; docs/deos/BASE-FAULT-PROOF-ANCHOR.md §0). This is the
/// DELEGATECALL target baked into every type-621 game proxy's CWIA runtime
/// bytecode — the semantics pin Link 5 recomputes the code hash against.
/// Changes only on an OP-stack/Base contracts upgrade (re-pin explicitly).
pub const BASE_AGGREGATE_VERIFIER_IMPL: [u8; 20] = hex!("1bd8db5139ba7ac9277684650c15e6e341761919");

// ---------------------------------------------------------------------------
// The Solady CWIA proxy runtime template — Residual R3's closure.
//
// The DisputeGameFactory creates every game as a Clones-With-Immutable-Args
// proxy: contracts-bedrock `DisputeGameFactory.create` calls Solady
// `LibClone.cloneDeterministic(impl, abi.encodePacked(msg.sender, _rootClaim,
// parentHash, _extraData), uuid)` where `parentHash = blockhash(block.number-1)`
// (ethereum-optimism/optimism `packages/contracts-bedrock/src/dispute/
// DisputeGameFactory.sol`, `create()`; the salt only affects the CREATE2
// address, never the runtime bytes). The deployed RUNTIME bytecode is Solady
// LibClone's documented "RUNTIME (98 bytes + extraLength)" CWIA layout —
// byte-identical across Solady v0.0.123 → v0.0.200, the range contracts-bedrock
// has vendored (`src/utils/LibClone.sol`, the `ReceiveETH(uint256)`-logging
// clone-with-immutable-args section):
//
//   36 602c 57                        calldatasize-nonzero? jump to 0x2c
//   34 3d 52 7f <topic32>  59 3d a1   empty call: LOG1 ReceiveETH(callvalue)
//   00 5b                             STOP; JUMPDEST(0x2c)
//   36 3d 3d 37 3d 3d 3d 3d           copy calldata
//   61 <extraLength:2> 80             PUSH2 extraLength = argLen + 2
//   60 62 36 39 36 01 3d              CODECOPY args after calldata (0x62 = 98)
//   73 <impl:20> 5a f4                DELEGATECALL the implementation
//   3d 3d 93 80 3e 6060 57 fd 5b f3   bubble returndata
//   ‖ immutable args ‖ extraLength(2 bytes, big-endian)
//
// Everything below was additionally byte-matched against the LIVE fixture
// game's `eth_getCode` (0x15F3…3626, fetched 2026-07-12): template ‖ impl ‖
// creator ‖ rootClaim ‖ l1Head ‖ extraData ‖ 0x030a, whose keccak256 is exactly
// the account-proof-proven code hash. That KAT (tests/base_fault_proof.rs
// `kat_cwia_code_hash_reconstructs`) is what pins this layout.
// ---------------------------------------------------------------------------

/// CWIA runtime bytes 0..8: dispatch + the start of the ReceiveETH log.
const CWIA_RUNTIME_0_8: [u8; 8] = hex!("36602c57343d527f");
/// CWIA runtime bytes 8..40: the `ReceiveETH(uint256)` event topic
/// (`keccak256("ReceiveETH(uint256)")`), PUSH32 immediate.
const CWIA_RECEIVE_ETH_TOPIC: [u8; 32] =
    hex!("9e4ac34f21c619cefc926c8bd93b54bf5a39c7ab2127a895af1cc0691d7e3dff");
/// CWIA runtime bytes 40..54: log + calldata copy, ending in the PUSH2 opcode
/// whose immediate is `extraLength` (bytes 54..56).
const CWIA_RUNTIME_40_54: [u8; 14] = hex!("593da1005b363d3d373d3d3d3d61");
/// CWIA runtime bytes 56..65: args CODECOPY (offset 0x62 = 98 = template size),
/// ending in the PUSH20 opcode whose immediate is the impl address (65..85).
const CWIA_RUNTIME_56_65: [u8; 9] = hex!("806062363936013d73");
/// CWIA runtime bytes 85..98: DELEGATECALL + returndata bubbling.
const CWIA_RUNTIME_85_98: [u8; 13] = hex!("5af43d3d93803e606057fd5bf3");

/// Recompute the runtime `code_hash` of a Solady CWIA proxy cloned from
/// `impl_addr` with `immutable_args`: `keccak256(template(extraLength, impl) ‖
/// immutable_args ‖ extraLength_be16)` where `extraLength = len(args) + 2`.
/// Returns `None` when the args cannot fit the 2-byte length field (no such
/// proxy can exist on chain — EIP-170 caps runtime code well below that
/// anyway); the caller must refuse, never truncate.
pub fn cwia_proxy_code_hash(impl_addr: &[u8; 20], immutable_args: &[u8]) -> Option<[u8; 32]> {
    let extra_length = u16::try_from(immutable_args.len().checked_add(2)?).ok()?;
    let mut code = Vec::with_capacity(98 + immutable_args.len() + 2);
    code.extend_from_slice(&CWIA_RUNTIME_0_8);
    code.extend_from_slice(&CWIA_RECEIVE_ETH_TOPIC);
    code.extend_from_slice(&CWIA_RUNTIME_40_54);
    code.extend_from_slice(&extra_length.to_be_bytes());
    code.extend_from_slice(&CWIA_RUNTIME_56_65);
    code.extend_from_slice(impl_addr);
    code.extend_from_slice(&CWIA_RUNTIME_85_98);
    code.extend_from_slice(immutable_args);
    code.extend_from_slice(&extra_length.to_be_bytes());
    debug_assert_eq!(code.len(), 98 + immutable_args.len() + 2);
    Some(keccak256(code).0)
}

/// Pack a dispute game's CWIA immutable args exactly as
/// `DisputeGameFactory.create` does: `abi.encodePacked(msg.sender, _rootClaim,
/// parentHash, _extraData)` — `creator(20) ‖ rootClaim(32) ‖ l1Head(32) ‖
/// extraData`. (`l1Head` is the game's name for the factory's
/// `blockhash(block.number - 1)`.)
pub fn fault_dispute_game_immutable_args(
    creator: &[u8; 20],
    root_claim: &[u8; 32],
    l1_head: &[u8; 32],
    extra_data: &[u8],
) -> Vec<u8> {
    let mut args = Vec::with_capacity(84 + extra_data.len());
    args.extend_from_slice(creator);
    args.extend_from_slice(root_claim);
    args.extend_from_slice(l1_head);
    args.extend_from_slice(extra_data);
    args
}

/// Why a fault-proof anchor observation was refused. One variant per trust-chain
/// link; a refusal NEVER yields an output root or a holding (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaultProofAnchorError {
    /// The claimed root claim is all-zero (an unset mapping value reads as zero;
    /// a keccak preimage for zero is unknown anyway).
    ZeroRootClaim,
    /// The claimed game type is not the one this verifier is configured to
    /// respect. A stale/rotated `respectedGameType` fails here (or at the slot-6
    /// proof) — the correct failure mode is an explicit re-pin, never silent
    /// acceptance of a different game's semantics.
    GameTypeMismatch { got: u32, expected: u32 },
    /// `status != DEFENDER_WINS`: an `IN_PROGRESS` or `CHALLENGER_WINS` game is
    /// not a commitment — accepting one would trust a challengeable or REFUTED
    /// output root.
    GameNotDefenderWins { status: u8 },
    /// `resolvedAt == 0`: the game never resolved on L1 (also implied by
    /// `IN_PROGRESS`, checked independently — prove the whole word, trust nothing).
    GameNotResolved,
    /// `createdAt <= retirementTimestamp`: the game was created at or before the
    /// ASR retirement boundary — retired games are not anchors regardless of
    /// status (the guardian's mass-invalidation lever).
    GameRetired {
        created_at: u64,
        retirement_timestamp: u64,
    },
    /// `extraData` is too short to carry the leading `uint256 l2BlockNumber` word.
    ExtraDataTooShort { len: usize },
    /// The leading `extraData` word does not fit `u64` — refused, never truncated.
    L2BlockNumberOverflow,
    /// The L1 account proof does not open the AnchorStateRegistry under the
    /// finalized L1 state root.
    AsrAccountProofInvalid,
    /// The storage proof does not open ASR slot 6 to the claimed
    /// `retirementTimestamp ‖ respectedGameType` word (wrong retirement claim, or
    /// the chain's respected type is not the expected one).
    RespectedGameTypeSlotProofInvalid,
    /// The storage proof does not open ASR slot 1 to the expected
    /// DisputeGameFactory address — the factory identity must be L1-anchored,
    /// not configuration.
    DgfBindingSlotProofInvalid,
    /// The L1 account proof does not open the DisputeGameFactory under the
    /// finalized L1 state root.
    DgfAccountProofInvalid,
    /// THE KEYSTONE: the storage proof does not open
    /// `_disputeGames[keccak(abi.encode(gameType, rootClaim, extraData))]` to the
    /// packed GameId `(gameType ‖ createdAt ‖ gameProxy)`. Any tampered byte of
    /// the claim moves the mapping slot itself; a forged proxy address or
    /// createdAt changes the packed word. Either way: refused.
    GameIdSlotProofInvalid,
    /// The L1 account proof does not open the game proxy account under the
    /// finalized L1 state root.
    GameAccountProofInvalid,
    /// The game account's proven `code_hash` does not RECOMPUTE as the Solady
    /// CWIA proxy of the pinned AggregateVerifier implementation with this
    /// game's immutable args (`creator ‖ rootClaim ‖ l1Head ‖ extraData`) — the
    /// proxy bytecode defines the game's SEMANTICS, and the recomputation
    /// re-binds the claim from the bytecode itself (Residual R3 closed). A
    /// look-alike contract with the same slot-0 layout, a clone of a different
    /// impl, or a lied-about creator/l1Head all land here. Refused.
    GameCodeHashMismatch { got: [u8; 32], expected: [u8; 32] },
    /// The claimed CWIA immutable args cannot fit the proxy's 2-byte length
    /// field — no such clone can exist on chain. Refused, never truncated.
    CwiaImmutableArgsTooLong { len: usize },
    /// The storage proof does not open game slot 0 to the required resolution
    /// word: `createdAt ‖ resolvedAt ‖ DEFENDER_WINS ‖ initialized=1 ‖
    /// wasRespectedGameTypeWhenCreated=1`. A `CHALLENGER_WINS`/`IN_PROGRESS`
    /// status byte, a lied-about resolvedAt, an uninitialized game, or a
    /// not-respected-at-creation game all land here — the WHOLE packed word is
    /// proven, nothing is parsed off-proof.
    GameResolutionSlotProofInvalid,
    /// The blacklist EXCLUSION proof failed: either the proof is invalid or the
    /// game IS present in `disputeGameBlacklist` (a guardian-blacklisted game
    /// must never be an anchor — this is the negative the guardian's safety
    /// valve depends on).
    GameBlacklistNotExcluded,
    /// The finality window has not elapsed:
    /// `l1_time <= resolvedAt + max(asr_delay, policy_delay)` (or the sum
    /// overflows). The airgap is the guardian's post-resolution reaction window;
    /// on live Base the on-chain component is ZERO and `policy_delay` is the
    /// caller's own conservatism — see the module docs.
    AirgapNotElapsed {
        l1_time: u64,
        resolved_at: u64,
        required_delay: u64,
    },
    /// The root claim opened fine but the OP output-root binding refused
    /// (non-v0 version, or the claimed L2 preimage does not recompute it).
    OutputRoot(BaseProofError),
    /// The L2 (Base) EIP-1186 holding proof failed against the bound L2 state root.
    L2Holding(Erc20ProofError),
}

impl core::fmt::Display for FaultProofAnchorError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ZeroRootClaim => write!(f, "claimed root claim is zero (unset slot) — refused"),
            Self::GameTypeMismatch { got, expected } => write!(
                f,
                "game type {got} is not the expected respected game type {expected} — re-pin explicitly, never accept silently"
            ),
            Self::GameNotDefenderWins { status } => write!(
                f,
                "game status {status} is not DEFENDER_WINS(2) — a challengeable or refuted root is not a commitment"
            ),
            Self::GameNotResolved => write!(f, "game resolvedAt is zero — the game never resolved"),
            Self::GameRetired { created_at, retirement_timestamp } => write!(
                f,
                "game createdAt {created_at} <= retirementTimestamp {retirement_timestamp} — retired games are not anchors"
            ),
            Self::ExtraDataTooShort { len } => write!(
                f,
                "extraData ({len} bytes) is too short to carry the leading l2BlockNumber word"
            ),
            Self::L2BlockNumberOverflow => {
                write!(f, "extraData l2BlockNumber word exceeds u64 — refused, never truncated")
            }
            Self::AsrAccountProofInvalid => write!(
                f,
                "L1 account proof does not open the AnchorStateRegistry under the finalized L1 state root"
            ),
            Self::RespectedGameTypeSlotProofInvalid => write!(
                f,
                "storage proof does not open ASR slot 6 to the claimed retirementTimestamp ‖ respectedGameType word"
            ),
            Self::DgfBindingSlotProofInvalid => write!(
                f,
                "storage proof does not open ASR slot 1 to the expected DisputeGameFactory address"
            ),
            Self::DgfAccountProofInvalid => write!(
                f,
                "L1 account proof does not open the DisputeGameFactory under the finalized L1 state root"
            ),
            Self::GameIdSlotProofInvalid => write!(
                f,
                "storage proof does not open _disputeGames[uuid] to the packed GameId — the claim (type, rootClaim, extraData) is not bound to this game"
            ),
            Self::GameAccountProofInvalid => write!(
                f,
                "L1 account proof does not open the game proxy account under the finalized L1 state root"
            ),
            Self::GameCodeHashMismatch { .. } => write!(
                f,
                "game proxy code hash does not recompute as the CWIA clone of the pinned implementation with this game's immutable args — unknown bytecode means unknown game semantics"
            ),
            Self::CwiaImmutableArgsTooLong { len } => write!(
                f,
                "claimed CWIA immutable args ({len} bytes) cannot fit the proxy's 2-byte length field — no such clone exists on chain"
            ),
            Self::GameResolutionSlotProofInvalid => write!(
                f,
                "storage proof does not open game slot 0 to createdAt ‖ resolvedAt ‖ DEFENDER_WINS ‖ initialized ‖ respected-at-creation"
            ),
            Self::GameBlacklistNotExcluded => write!(
                f,
                "blacklist exclusion proof failed — the game may be guardian-blacklisted, refused"
            ),
            Self::AirgapNotElapsed { l1_time, resolved_at, required_delay } => write!(
                f,
                "finality window not elapsed: l1_time {l1_time} <= resolvedAt {resolved_at} + delay {required_delay}"
            ),
            Self::OutputRoot(e) => write!(f, "output-root binding failed: {e}"),
            Self::L2Holding(e) => write!(f, "L2 holding proof failed: {e}"),
        }
    }
}

impl std::error::Error for FaultProofAnchorError {}

/// 32-byte big-endian encoding of a u64 slot number (Solidity `uint256` slot).
fn u64_slot_be32(slot: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&slot.to_be_bytes());
    b
}

/// Left-pad a 20-byte address into a 32-byte ABI word.
fn pad32_address(addr: &[u8; 20]) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[12..].copy_from_slice(addr);
    b
}

/// The DisputeGameFactory game UUID:
/// `keccak256(abi.encode(uint32 gameType, bytes32 rootClaim, bytes extraData))`.
/// The dynamic `bytes` head/tail encoding is load-bearing: `pad32(gameType) ‖
/// rootClaim ‖ 0x…60 (tail offset) ‖ pad32(len(extraData)) ‖ extraData ‖ zero-pad
/// to a 32-byte boundary`. Validated live: reproduces the on-chain
/// `DGF.getGameUUID` for the fixture game byte-exactly.
pub fn game_uuid(game_type: u32, root_claim: &[u8; 32], extra_data: &[u8]) -> [u8; 32] {
    let padded_len = extra_data.len().div_ceil(32) * 32;
    let mut preimage = Vec::with_capacity(128 + padded_len);
    preimage.extend_from_slice(&u64_slot_be32(game_type as u64)); // pad32(gameType)
    preimage.extend_from_slice(root_claim);
    preimage.extend_from_slice(&u64_slot_be32(0x60)); // tail offset of `bytes`
    preimage.extend_from_slice(&u64_slot_be32(extra_data.len() as u64));
    preimage.extend_from_slice(extra_data);
    preimage.resize(128 + padded_len, 0); // zero-pad the tail
    keccak256(preimage).0
}

/// The `_disputeGames[uuid]` mapping value slot:
/// `keccak256(uuid ‖ pad32(DGF_DISPUTE_GAMES_SLOT = 103))`.
pub fn dispute_games_mapping_slot(uuid: &[u8; 32]) -> [u8; 32] {
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(uuid);
    preimage[32..].copy_from_slice(&u64_slot_be32(DGF_DISPUTE_GAMES_SLOT));
    keccak256(preimage).0
}

/// The `disputeGameBlacklist[game]` mapping slot:
/// `keccak256(pad32(game) ‖ pad32(ASR_BLACKLIST_SLOT = 5))`. The verifier proves
/// this slot ABSENT (exclusion), never a value.
pub fn blacklist_mapping_slot(game: &[u8; 20]) -> [u8; 32] {
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(&pad32_address(game));
    preimage[32..].copy_from_slice(&u64_slot_be32(ASR_BLACKLIST_SLOT));
    keccak256(preimage).0
}

/// Pack a `GameId` exactly as `LibGameId.pack` does:
/// `uint256(gameType) << 224 | uint256(createdAt) << 160 | uint160(gameProxy)` —
/// the raw 32-byte word is `gameType(4) ‖ createdAt(8) ‖ proxy(20)`.
pub fn pack_game_id(game_type: u32, created_at: u64, game_proxy: &[u8; 20]) -> U256 {
    (U256::from(game_type) << 224)
        | (U256::from(created_at) << 160)
        | U256::from_be_bytes(pad32_address(game_proxy))
}

/// Unpack a `GameId` word into `(game_type, created_at, game_proxy)` — the exact
/// inverse of [`pack_game_id`] (all 32 bytes are used; there are no spare bits).
pub fn unpack_game_id(word: U256) -> (u32, u64, [u8; 20]) {
    let bytes = word.to_be_bytes::<32>();
    let game_type = u32::from_be_bytes(bytes[0..4].try_into().expect("4 bytes"));
    let created_at = u64::from_be_bytes(bytes[4..12].try_into().expect("8 bytes"));
    let mut proxy = [0u8; 20];
    proxy.copy_from_slice(&bytes[12..32]);
    (game_type, created_at, proxy)
}

/// Pack the game's slot-0 resolution word as Solidity stores it (declaration
/// order packs from the LOW bytes up): `createdAt (u64 @byte 0) | resolvedAt
/// (u64 @8) | status (u8 @16) | initialized (bool @17) |
/// wasRespectedGameTypeWhenCreated (bool @18)`.
pub fn pack_game_resolution_word(
    created_at: u64,
    resolved_at: u64,
    status: u8,
    initialized: bool,
    was_respected_game_type_when_created: bool,
) -> U256 {
    U256::from(created_at)
        | (U256::from(resolved_at) << 64)
        | (U256::from(status) << 128)
        | (U256::from(initialized as u8) << 136)
        | (U256::from(was_respected_game_type_when_created as u8) << 144)
}

/// Pack ASR slot 6 as Solidity stores it: `respectedGameType (u32 @byte 0) |
/// retirementTimestamp (u64 @4)`.
pub fn pack_asr_respected_word(retirement_timestamp: u64, respected_game_type: u32) -> U256 {
    U256::from(respected_game_type) | (U256::from(retirement_timestamp) << 32)
}

/// Parse the L1-anchored L2 block number out of the PROVEN `extraData`: the first
/// 32-byte word as `uint256` (both the classic-FDG `abi.encode(uint256)` layout
/// and AggregateVerifier's `pad32(l2BlockNumber) ‖ parentGame ‖ intermediate
/// roots` CWIA layout put it first). The remaining bytes are NOT interpreted —
/// they are bound by the UUID (Link 4), which is all the anchor needs.
pub fn parse_extra_data_l2_block_number(extra_data: &[u8]) -> Result<u64, FaultProofAnchorError> {
    if extra_data.len() < 32 {
        return Err(FaultProofAnchorError::ExtraDataTooShort {
            len: extra_data.len(),
        });
    }
    let word = U256::from_be_slice(&extra_data[..32]);
    u64::try_from(word).map_err(|_| FaultProofAnchorError::L2BlockNumberOverflow)
}

/// The verifier's PINNED expectations — the analog of "which oracle address do I
/// trust" in [`crate::base`], extended with the fault-proof pins. Everything here
/// is configuration the caller vouches for once (and must explicitly re-pin after
/// a governance upgrade — the checks fail closed until then).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaultProofAnchorParams {
    /// The L1 address of the `AnchorStateRegistry` proxy
    /// (`0x909f6CF47ED12f010A796527F562BFc26c7F4e72` on live Base).
    pub asr_address: [u8; 20],
    /// The L1 address of the `DisputeGameFactory`
    /// (`0x43edB88C4B80fDD2AdFF2412A7BebF9dF42cB40e` on live Base) — additionally
    /// proven equal to ASR slot 1, so the factory identity is L1-anchored too.
    pub dgf_address: [u8; 20],
    /// The game type this verifier accepts ([`BASE_AGGREGATE_VERIFIER_GAME_TYPE`]
    /// = 621 on live Base). Proven equal to the ASR's CURRENT `respectedGameType`
    /// (slot 6) and to the game's own type (GameId word).
    pub expected_game_type: u32,
    /// The pinned game IMPLEMENTATION address the proxy must delegate to
    /// ([`BASE_AGGREGATE_VERIFIER_IMPL`] = `gameImpls[621]` on live Base). The
    /// game account's proven `code_hash` must recompute as
    /// [`cwia_proxy_code_hash`] of THIS address + the game's immutable args —
    /// a proxy of any other implementation (or non-CWIA bytecode entirely) is
    /// refused. Changes only on an OP-stack contracts upgrade: fail-closed
    /// until explicitly re-pinned.
    pub game_impl_address: [u8; 20],
    /// The ASR-impl `DISPUTE_GAME_FINALITY_DELAY_SECONDS` immutable — what the
    /// CHAIN enforces after `resolvedAt`. **0 on live Base** (live-read fact).
    pub dispute_game_finality_delay: u64,
    /// **The caller's OWN conservatism — NOT a protocol parameter.** Because the
    /// on-chain registry airgap is zero on live Base, a caller wanting a
    /// guardian-reaction window (or extra reorg margin) sets it here; the
    /// predicate takes `max(dispute_game_finality_delay, policy_finality_delay)`.
    /// Setting 0 means "accept exactly what the chain accepts". Documented as a
    /// liveness/soundness ASSUMPTION, never laundered as a guarantee.
    pub policy_finality_delay: u64,
}

/// Everything needed to open the fault-proof anchor: account claims + EIP-1186
/// proofs for the three L1 accounts, the per-link storage proofs, and the claimed
/// game facts (every one verified against L1 storage, never trusted bare).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaultProofAnchor {
    // --- Links 1,2,3(slot 1),7: the AnchorStateRegistry ---
    /// ASR account fields from `eth_getProof` on L1.
    pub asr_account: AccountClaim,
    /// EIP-1186 `accountProof` for the ASR under the finalized L1 state root.
    pub asr_account_proof: Vec<Vec<u8>>,
    /// The claimed `retirementTimestamp` (verified via the slot-6 word, which
    /// also pins `respectedGameType == expected_game_type`).
    pub retirement_timestamp: u64,
    /// EIP-1186 storage proof for ASR slot 6.
    pub respected_game_type_slot_proof: Vec<Vec<u8>>,
    /// EIP-1186 storage proof for ASR slot 1 (must open to `dgf_address`).
    pub dgf_binding_slot_proof: Vec<Vec<u8>>,
    /// EIP-1186 EXCLUSION proof: `disputeGameBlacklist[game]` is ABSENT.
    pub blacklist_absence_proof: Vec<Vec<u8>>,
    // --- Links 3,4: the DisputeGameFactory ---
    /// DGF account fields from `eth_getProof` on L1.
    pub dgf_account: AccountClaim,
    /// EIP-1186 `accountProof` for the DGF under the finalized L1 state root.
    pub dgf_account_proof: Vec<Vec<u8>>,
    /// EIP-1186 storage proof for `_disputeGames[uuid]` → the packed GameId.
    pub game_id_slot_proof: Vec<Vec<u8>>,
    // --- Links 5,6: the game proxy ---
    /// The game proxy address (bound by the GameId word — a wrong claim refuses).
    pub game_address: [u8; 20],
    /// The claimed `createdAt` (bound TWICE: the GameId word and slot 0 — the
    /// same field feeds both packings, so the cross-tooth is by construction).
    pub game_created_at: u64,
    /// The claimed `resolvedAt` (bound by the slot-0 word; must be nonzero).
    pub game_resolved_at: u64,
    /// The claimed `GameStatus` (must be [`GAME_STATUS_DEFENDER_WINS`]; bound by
    /// the slot-0 word — lying about a `CHALLENGER_WINS` game fails the proof).
    pub game_status: u8,
    /// The game's creator (`msg.sender` of `DGF.create`) — CWIA immutable arg 0.
    /// Bound by the code-hash recomputation: a wrong creator changes the
    /// reconstructed proxy bytecode, so the proven `code_hash` cannot match.
    pub game_creator: [u8; 20],
    /// The game's `l1Head` (the factory's `blockhash(block.number - 1)` at
    /// creation) — CWIA immutable arg 2, bound the same way as `game_creator`.
    pub game_l1_head: [u8; 32],
    /// Game proxy account fields from `eth_getProof` (binds storage_hash AND
    /// code_hash — the semantics pin).
    pub game_account: AccountClaim,
    /// EIP-1186 `accountProof` for the game proxy.
    pub game_account_proof: Vec<Vec<u8>>,
    /// EIP-1186 storage proof for game slot 0.
    pub game_slot0_proof: Vec<Vec<u8>>,
    // --- The claim being opened (the UUID preimage) ---
    /// The game type (must equal `params.expected_game_type`; feeds the UUID and
    /// both packed words).
    pub game_type: u32,
    /// The root claim — the OP output root this game vouches for.
    pub root_claim: [u8; 32],
    /// The factory-creation `extraData` (leading word = L2 block number). Bound
    /// byte-for-byte by the UUID mapping key.
    pub extra_data: Vec<u8>,
}

/// **Open the live-Base fault-proof anchor out of finalized L1 state** — the
/// fault-proof analog of [`crate::base::verify_l1_committed_output_root`].
/// Verifies Links 1–8 of the module trust chain and returns the trusted
/// [`L1CommittedOutput`]: the game's `rootClaim` plus the L2 block number proven
/// out of the UUID-bound `extraData` (`timestamp` carries `resolvedAt`).
///
/// Ordering: cheap fail-closed predicate checks first (zero root, wrong type,
/// wrong status, unresolved, retired, malformed extraData), then the three
/// account proofs + five storage proofs, then the airgap predicate over the
/// PROVEN `resolvedAt` and the light-client execution timestamp.
pub fn verify_l1_fault_proof_output_root(
    l1_finalized: &FinalizedExecution,
    params: &FaultProofAnchorParams,
    anchor: &FaultProofAnchor,
) -> Result<L1CommittedOutput, FaultProofAnchorError> {
    // --- Cheap predicate floor (each also enforced by a proof below where a
    //     chain value exists; these refuse honest-but-invalid claims early and
    //     make every gate independently visible). ---
    if anchor.root_claim == [0u8; 32] {
        return Err(FaultProofAnchorError::ZeroRootClaim);
    }
    if anchor.game_type != params.expected_game_type {
        return Err(FaultProofAnchorError::GameTypeMismatch {
            got: anchor.game_type,
            expected: params.expected_game_type,
        });
    }
    if anchor.game_status != GAME_STATUS_DEFENDER_WINS {
        return Err(FaultProofAnchorError::GameNotDefenderWins {
            status: anchor.game_status,
        });
    }
    if anchor.game_resolved_at == 0 {
        return Err(FaultProofAnchorError::GameNotResolved);
    }
    if anchor.game_created_at <= anchor.retirement_timestamp {
        return Err(FaultProofAnchorError::GameRetired {
            created_at: anchor.game_created_at,
            retirement_timestamp: anchor.retirement_timestamp,
        });
    }
    let l2_block_number = parse_extra_data_l2_block_number(&anchor.extra_data)?;

    let l1_state_root = l1_finalized.execution_state_root();

    // --- Link 1: ASR account proof (binds asr_account.storage_hash). ---
    verify_evm_account_proof(
        l1_state_root,
        params.asr_address,
        &anchor.asr_account,
        &anchor.asr_account_proof,
    )
    .map_err(|_| FaultProofAnchorError::AsrAccountProofInvalid)?;

    // --- Link 2: ASR slot 6 = retirementTimestamp ‖ respectedGameType. The
    //     expected word bakes in anchor.game_type (== expected_game_type), so a
    //     chain whose respected type rotated away refuses HERE. ---
    verify_evm_storage_slot(
        anchor.asr_account.storage_hash,
        u64_slot_be32(ASR_RESPECTED_GAME_TYPE_SLOT),
        pack_asr_respected_word(anchor.retirement_timestamp, anchor.game_type),
        &anchor.respected_game_type_slot_proof,
    )
    .map_err(|_| FaultProofAnchorError::RespectedGameTypeSlotProofInvalid)?;

    // --- Link 3a: ASR slot 1 must hold the pinned DGF address — the factory
    //     identity is L1-anchored, not configuration. ---
    verify_evm_storage_slot(
        anchor.asr_account.storage_hash,
        u64_slot_be32(ASR_DISPUTE_GAME_FACTORY_SLOT),
        U256::from_be_bytes(pad32_address(&params.dgf_address)),
        &anchor.dgf_binding_slot_proof,
    )
    .map_err(|_| FaultProofAnchorError::DgfBindingSlotProofInvalid)?;

    // --- Link 3b: DGF account proof (binds dgf_account.storage_hash). ---
    verify_evm_account_proof(
        l1_state_root,
        params.dgf_address,
        &anchor.dgf_account,
        &anchor.dgf_account_proof,
    )
    .map_err(|_| FaultProofAnchorError::DgfAccountProofInvalid)?;

    // --- Link 4, THE KEYSTONE: _disputeGames[keccak(abi.encode(type, rootClaim,
    //     extraData))] = GameId(type, createdAt, gameProxy). The mapping KEY
    //     commits the whole claim; the VALUE binds the proxy + creation time. ---
    let uuid = game_uuid(anchor.game_type, &anchor.root_claim, &anchor.extra_data);
    verify_evm_storage_slot(
        anchor.dgf_account.storage_hash,
        dispute_games_mapping_slot(&uuid),
        pack_game_id(
            anchor.game_type,
            anchor.game_created_at,
            &anchor.game_address,
        ),
        &anchor.game_id_slot_proof,
    )
    .map_err(|_| FaultProofAnchorError::GameIdSlotProofInvalid)?;

    // --- Link 5: game account proof (binds storage_hash AND code_hash), then
    //     the semantics pin (Residual R3, closed): the proven code_hash must
    //     RECOMPUTE as the Solady CWIA clone of the pinned implementation with
    //     THIS game's immutable args. rootClaim/extraData are already
    //     UUID-bound by Link 4; creator/l1Head are bound HERE — any lie changes
    //     the reconstructed bytecode, and a look-alike contract (same slot-0
    //     layout, different code) cannot produce the hash at all. ---
    verify_evm_account_proof(
        l1_state_root,
        anchor.game_address,
        &anchor.game_account,
        &anchor.game_account_proof,
    )
    .map_err(|_| FaultProofAnchorError::GameAccountProofInvalid)?;
    let immutable_args = fault_dispute_game_immutable_args(
        &anchor.game_creator,
        &anchor.root_claim,
        &anchor.game_l1_head,
        &anchor.extra_data,
    );
    let expected_code_hash = cwia_proxy_code_hash(&params.game_impl_address, &immutable_args)
        .ok_or(FaultProofAnchorError::CwiaImmutableArgsTooLong {
            len: immutable_args.len(),
        })?;
    if anchor.game_account.code_hash != expected_code_hash {
        return Err(FaultProofAnchorError::GameCodeHashMismatch {
            got: anchor.game_account.code_hash,
            expected: expected_code_hash,
        });
    }

    // --- Link 6: game slot 0 = createdAt ‖ resolvedAt ‖ DEFENDER_WINS ‖
    //     initialized ‖ wasRespectedGameTypeWhenCreated. The whole word is
    //     recomputed from the (already-gated) claims with status/flags REQUIRED —
    //     nothing is parsed off-proof. createdAt here is the SAME field the
    //     GameId word proved: the cross-tooth is by construction. ---
    verify_evm_storage_slot(
        anchor.game_account.storage_hash,
        u64_slot_be32(GAME_RESOLUTION_SLOT),
        pack_game_resolution_word(
            anchor.game_created_at,
            anchor.game_resolved_at,
            GAME_STATUS_DEFENDER_WINS,
            true,
            true,
        ),
        &anchor.game_slot0_proof,
    )
    .map_err(|_| FaultProofAnchorError::GameResolutionSlotProofInvalid)?;

    // --- Link 7: the game must NOT be blacklisted — an EXCLUSION proof of the
    //     blacklist mapping slot under the ASR's PROVEN storage hash. ---
    verify_evm_storage_slot_absent(
        anchor.asr_account.storage_hash,
        blacklist_mapping_slot(&anchor.game_address),
        &anchor.blacklist_absence_proof,
    )
    .map_err(|_| FaultProofAnchorError::GameBlacklistNotExcluded)?;

    // --- Link 8: the finality window. l1_time is the light-client-verified
    //     execution timestamp; resolvedAt was proven by Link 6. Strict `>`
    //     (mirrors isGameFinalized's `<=`-reject); checked add refuses overflow. ---
    let required_delay = params
        .dispute_game_finality_delay
        .max(params.policy_finality_delay);
    let l1_time = l1_finalized.execution_timestamp();
    let deadline = anchor.game_resolved_at.checked_add(required_delay).ok_or(
        FaultProofAnchorError::AirgapNotElapsed {
            l1_time,
            resolved_at: anchor.game_resolved_at,
            required_delay,
        },
    )?;
    if l1_time <= deadline {
        return Err(FaultProofAnchorError::AirgapNotElapsed {
            l1_time,
            resolved_at: anchor.game_resolved_at,
            required_delay,
        });
    }

    Ok(L1CommittedOutput {
        output_root: anchor.root_claim,
        l2_block_number,
        timestamp: anchor.game_resolved_at as u128,
    })
}

/// **The live-Base fault-proof proof-of-holdings composition** — the fault-proof
/// analog of [`crate::base::verify_base_erc20_holding`]: L1 finality →
/// resolved-game anchor (Links 1–8) → v0 output-root binding (Link 9) → L2
/// ERC-20 MPT proof. Mints [`HoldingTrust::ConsensusProven`] ONLY when every
/// link verifies; the minted holding's `state_root`/`block_number` are the
/// **L2** ones (the block number L1-anchored via the UUID-bound `extraData`),
/// and `to_foreign_fields()` yields `chain_tag = 1` (EVM family — Base is
/// `ChainId::Evm(8453)` at the governance edge).
#[allow(clippy::too_many_arguments)]
pub fn verify_base_fault_proof_erc20_holding(
    l1_finalized: &FinalizedExecution,
    params: &FaultProofAnchorParams,
    anchor: &FaultProofAnchor,
    l2_commitment: &L2StateCommitment,
    l2_account_proof: &[Vec<u8>],
    l2_storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    balances_slot: u64,
    token_account: &AccountClaim,
    claimed_balance: U256,
) -> Result<ProvenErc20Holding, FaultProofAnchorError> {
    // Links 1-8: open the resolved-game anchor out of finalized L1 state.
    let committed = verify_l1_fault_proof_output_root(l1_finalized, params, anchor)?;

    // Link 9a: bind the claimed L2 state root to the game's root claim (the v0
    // output-root preimage — live-validated to hold for type-621 games).
    verify_op_output_root(
        l2_commitment.version,
        l2_commitment.l2_state_root,
        l2_commitment.l2_withdrawal_storage_root,
        l2_commitment.l2_block_hash,
        committed.output_root,
    )
    .map_err(FaultProofAnchorError::OutputRoot)?;

    // Link 9b: the ordinary EVM holding proof against the now-trusted L2 state
    // root, at the L1-proven L2 block number. The StructureOnly it mints is
    // upgraded to ConsensusProven, justified by Links 1-9a.
    let mut holding = verify_erc20_holding(
        l2_commitment.l2_state_root,
        l2_account_proof,
        l2_storage_proof,
        token,
        holder,
        balances_slot,
        token_account,
        claimed_balance,
        committed.l2_block_number,
    )
    .map_err(FaultProofAnchorError::L2Holding)?;
    holding.trust = HoldingTrust::ConsensusProven;
    Ok(holding)
}
