//! Live-Base fault-proof anchor — the dispute-game trust chain of
//! `src/base_fault_proof.rs` (plan: docs/deos/BASE-FAULT-PROOF-ANCHOR.md).
//!
//! ## Evidence classes (named honestly)
//!
//! * **REAL-EXTERNAL (live L1 + Base mainnet, captured 2026-07-12):** the whole
//!   accept chain in tests/fixtures/base_fault_proof_mainnet.rs — game index
//!   17049 (type 621 AggregateVerifier, the CURRENT `ASR.anchorGame`), every
//!   `eth_getProof` a real node answer under a real finalized L1 block, the
//!   UUID cross-checked against the on-chain `DGF.getGameUUID`, the packed
//!   GameId/slot-0/slot-6 words raw `eth_getStorageAt` values, the rootClaim
//!   recomputing from Base block 48306960's real header + message-passer root,
//!   and a real WETH holding on Base at that block. The `FinalizedExecution`
//!   carrier is `new_unchecked` with the real block's values (the sync-committee
//!   path has its own KATs in finality_kat.rs).
//! * **SELF-CONSISTENT SYNTHESIS (≠ external conformance):** the hostile worlds
//!   no honest chain can serve — a blacklist entry that IS present, a game whose
//!   slot 0 says CHALLENGER_WINS while the caller claims DEFENDER_WINS, a
//!   not-respected-at-creation flag — built with the same pinned alloy-trie
//!   `HashBuilder` and named as synthesis wherever used.
//!
//! REJECT coverage (all default-run): wrong/rotated respectedGameType, a GameId
//! that does not bind the (type, rootClaim, extraData) claim (tampered extraData
//! byte, forged rootClaim, forged proxy address, forged createdAt), status
//! IN_PROGRESS / CHALLENGER_WINS (both honest-claim and lying-claim forms),
//! resolvedAt == 0, a retired game, a BLACKLISTED game (present where exclusion
//! is required — synthetic world), the airgap not yet elapsed (strict-boundary
//! checked), a rootClaim whose v0 preimage does not recompute, tampered proofs at
//! every link, a wrong pinned code hash, and the measured alloy-trie 0.9.5
//! exclusion hole: a TRUNCATED inclusion-proof prefix passed off as an absence
//! proof must refuse.

#[path = "fixtures/base_fault_proof_mainnet.rs"]
mod fx;

use eth_lightclient::base::{
    compute_op_output_root_v0, BaseProofError, L2StateCommitment, OUTPUT_ROOT_VERSION_V0,
};
use eth_lightclient::base_fault_proof::{
    blacklist_mapping_slot, dispute_games_mapping_slot, game_uuid, pack_asr_respected_word,
    pack_game_id, pack_game_resolution_word, parse_extra_data_l2_block_number, unpack_game_id,
    verify_base_fault_proof_erc20_holding, verify_l1_fault_proof_output_root, FaultProofAnchor,
    FaultProofAnchorError, FaultProofAnchorParams, BASE_AGGREGATE_VERIFIER_GAME_TYPE,
    GAME_STATUS_CHALLENGER_WINS, GAME_STATUS_DEFENDER_WINS, GAME_STATUS_IN_PROGRESS,
};
use eth_lightclient::evm::{
    verify_evm_storage_slot_absent, AccountClaim, Erc20ProofError, HoldingTrust, Uint256,
    CHAIN_TAG_EVM,
};
use eth_lightclient::finality::FinalizedExecution;

fn h32(s: &str) -> [u8; 32] {
    let v = hex::decode(s).expect("hex32");
    let mut a = [0u8; 32];
    a.copy_from_slice(&v);
    a
}
fn h20(s: &str) -> [u8; 20] {
    let v = hex::decode(s).expect("hex20");
    let mut a = [0u8; 20];
    a.copy_from_slice(&v);
    a
}
fn nodes(list: &[&str]) -> Vec<Vec<u8>> {
    list.iter()
        .map(|s| hex::decode(s).expect("hex node"))
        .collect()
}
fn u256(s: &str) -> Uint256 {
    Uint256::from_str_radix(s, 16).expect("u256 hex")
}
fn slot_be32(slot: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&slot.to_be_bytes());
    b
}

/// The accept-path policy delay: 600 s < the fixture's real airgap margin
/// (l1_time − resolvedAt = 1224 s at capture). OUR conservatism knob, not a
/// protocol parameter — see `FaultProofAnchorParams::policy_finality_delay`.
const POLICY_DELAY_ACCEPT: u64 = 600;
/// The fixture's exact margin, for the strict-boundary airgap tests.
const FIXTURE_AIRGAP_MARGIN: u64 = fx::L1_TIMESTAMP - fx::GAME_RESOLVED_AT;

/// The real finalized-L1 carrier (real block 25514711 state root + timestamp).
fn l1_finalized() -> FinalizedExecution {
    FinalizedExecution::new_unchecked(
        0,         // beacon slot: not exercised by this composition
        [0u8; 32], // beacon root: not exercised by this composition
        fx::L1_BLOCK_NUMBER,
        h32(fx::L1_BLOCK_HASH),
        h32(fx::L1_STATE_ROOT),
        fx::L1_TIMESTAMP,
    )
}

fn params() -> FaultProofAnchorParams {
    FaultProofAnchorParams {
        asr_address: h20(fx::ASR_ADDRESS),
        dgf_address: h20(fx::DGF_ADDRESS),
        expected_game_type: BASE_AGGREGATE_VERIFIER_GAME_TYPE,
        game_code_hash: h32(fx::GAME_CODE_HASH),
        dispute_game_finality_delay: 0, // live-read fact: the ASR airgap is ZERO
        policy_finality_delay: POLICY_DELAY_ACCEPT,
    }
}

fn asr_account() -> AccountClaim {
    AccountClaim {
        nonce: fx::ASR_NONCE,
        balance: u256(fx::ASR_BALANCE_HEX),
        storage_hash: h32(fx::ASR_STORAGE_HASH),
        code_hash: h32(fx::ASR_CODE_HASH),
    }
}

fn anchor() -> FaultProofAnchor {
    FaultProofAnchor {
        asr_account: asr_account(),
        asr_account_proof: nodes(fx::ASR_ACCOUNT_PROOF),
        retirement_timestamp: fx::RETIREMENT_TIMESTAMP,
        respected_game_type_slot_proof: nodes(fx::ASR_SLOT6_PROOF),
        dgf_binding_slot_proof: nodes(fx::ASR_SLOT1_PROOF),
        blacklist_absence_proof: nodes(fx::BLACKLIST_ABSENCE_PROOF),
        dgf_account: AccountClaim {
            nonce: fx::DGF_NONCE,
            balance: u256(fx::DGF_BALANCE_HEX),
            storage_hash: h32(fx::DGF_STORAGE_HASH),
            code_hash: h32(fx::DGF_CODE_HASH),
        },
        dgf_account_proof: nodes(fx::DGF_ACCOUNT_PROOF),
        game_id_slot_proof: nodes(fx::GAME_ID_SLOT_PROOF),
        game_address: h20(fx::GAME_ADDRESS),
        game_created_at: fx::GAME_CREATED_AT,
        game_resolved_at: fx::GAME_RESOLVED_AT,
        game_status: GAME_STATUS_DEFENDER_WINS,
        game_account: AccountClaim {
            nonce: fx::GAME_NONCE,
            balance: u256(fx::GAME_BALANCE_HEX),
            storage_hash: h32(fx::GAME_STORAGE_HASH),
            code_hash: h32(fx::GAME_CODE_HASH),
        },
        game_account_proof: nodes(fx::GAME_ACCOUNT_PROOF),
        game_slot0_proof: nodes(fx::GAME_SLOT0_PROOF),
        game_type: fx::GAME_TYPE,
        root_claim: h32(fx::ROOT_CLAIM),
        extra_data: hex::decode(fx::EXTRA_DATA).expect("extra data hex"),
    }
}

fn l2_commitment() -> L2StateCommitment {
    L2StateCommitment {
        version: OUTPUT_ROOT_VERSION_V0,
        l2_state_root: h32(fx::L2_STATE_ROOT),
        l2_withdrawal_storage_root: h32(fx::L2_WITHDRAWAL_STORAGE_ROOT),
        l2_block_hash: h32(fx::L2_BLOCK_HASH),
    }
}

fn token_account() -> AccountClaim {
    AccountClaim {
        nonce: fx::TOKEN_NONCE,
        balance: u256(fx::TOKEN_BALANCE_HEX),
        storage_hash: h32(fx::TOKEN_STORAGE_HASH),
        code_hash: h32(fx::TOKEN_CODE_HASH),
    }
}

fn run_anchor(
    l1: &FinalizedExecution,
    p: &FaultProofAnchorParams,
    a: &FaultProofAnchor,
) -> Result<eth_lightclient::base::L1CommittedOutput, FaultProofAnchorError> {
    verify_l1_fault_proof_output_root(l1, p, a)
}

fn run_full(
    p: &FaultProofAnchorParams,
    a: &FaultProofAnchor,
    c: &L2StateCommitment,
    balance: Uint256,
) -> Result<eth_lightclient::evm::ProvenErc20Holding, FaultProofAnchorError> {
    verify_base_fault_proof_erc20_holding(
        &l1_finalized(),
        p,
        a,
        c,
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        h20(fx::TOKEN),
        h20(fx::HOLDER),
        fx::BALANCES_SLOT,
        &token_account(),
        balance,
    )
}

// ---------------------------------------------------------------------------
// KATs — the slot math and packed words, pinned against RAW live chain values
// ---------------------------------------------------------------------------

/// EXTERNAL KAT: our abi.encode(uint32, bytes32, bytes) UUID reproduces the
/// on-chain `DGF.getGameUUID` (cross-checked live at capture), and the mapping
/// slot is the one the L1 node actually served the GameId proof for.
#[test]
fn kat_game_uuid_and_mapping_slots() {
    let extra = hex::decode(fx::EXTRA_DATA).unwrap();
    assert_eq!(extra.len(), 692, "AggregateVerifier extraData layout");
    let uuid = game_uuid(fx::GAME_TYPE, &h32(fx::ROOT_CLAIM), &extra);
    assert_eq!(uuid, h32(fx::GAME_UUID));
    assert_eq!(dispute_games_mapping_slot(&uuid), h32(fx::GAME_ID_SLOT));
    assert_eq!(
        blacklist_mapping_slot(&h20(fx::GAME_ADDRESS)),
        h32(fx::BLACKLIST_SLOT)
    );
}

/// EXTERNAL KAT: GameId packing vs the raw `eth_getStorageAt` word (LibGameId).
#[test]
fn kat_game_id_packing() {
    let word = Uint256::from_be_bytes(h32(fx::GAME_ID_WORD));
    assert_eq!(
        pack_game_id(fx::GAME_TYPE, fx::GAME_CREATED_AT, &h20(fx::GAME_ADDRESS)),
        word
    );
    assert_eq!(
        unpack_game_id(word),
        (fx::GAME_TYPE, fx::GAME_CREATED_AT, h20(fx::GAME_ADDRESS))
    );
}

/// EXTERNAL KAT: game slot-0 packing vs the raw live word (createdAt ‖
/// resolvedAt ‖ status=DEFENDER_WINS ‖ initialized ‖ respected-at-creation).
#[test]
fn kat_game_slot0_packing() {
    assert_eq!(
        pack_game_resolution_word(
            fx::GAME_CREATED_AT,
            fx::GAME_RESOLVED_AT,
            GAME_STATUS_DEFENDER_WINS,
            true,
            true,
        ),
        Uint256::from_be_bytes(h32(fx::GAME_SLOT0_WORD))
    );
    // A flipped status/flag byte changes the word (the packing is not vacuous).
    assert_ne!(
        pack_game_resolution_word(
            fx::GAME_CREATED_AT,
            fx::GAME_RESOLVED_AT,
            GAME_STATUS_CHALLENGER_WINS,
            true,
            true,
        ),
        Uint256::from_be_bytes(h32(fx::GAME_SLOT0_WORD))
    );
}

/// EXTERNAL KAT: ASR slot-6 packing vs the raw live word
/// (retirementTimestamp ‖ respectedGameType = 621).
#[test]
fn kat_asr_slot6_packing() {
    assert_eq!(
        pack_asr_respected_word(fx::RETIREMENT_TIMESTAMP, fx::RESPECTED_GAME_TYPE),
        Uint256::from_be_bytes(h32(fx::ASR_SLOT6_WORD))
    );
}

/// EXTERNAL KAT (the decisive reuse fact): the type-621 game's rootClaim is a
/// v0 OP output root — it recomputes from Base block 48306960's REAL
/// (stateRoot, messagePasserStorageRoot, blockHash).
#[test]
fn kat_root_claim_recomputes_as_v0_output_root() {
    assert_eq!(
        compute_op_output_root_v0(
            h32(fx::L2_STATE_ROOT),
            h32(fx::L2_WITHDRAWAL_STORAGE_ROOT),
            h32(fx::L2_BLOCK_HASH),
        ),
        h32(fx::ROOT_CLAIM)
    );
}

#[test]
fn extra_data_l2_block_number_parses_and_fails_closed() {
    let extra = hex::decode(fx::EXTRA_DATA).unwrap();
    assert_eq!(
        parse_extra_data_l2_block_number(&extra),
        Ok(fx::L2_BLOCK_NUMBER)
    );
    // Too short to carry the leading uint256 word.
    assert_eq!(
        parse_extra_data_l2_block_number(&extra[..31]),
        Err(FaultProofAnchorError::ExtraDataTooShort { len: 31 })
    );
    // A leading word above u64::MAX refuses — never truncated.
    let mut big = extra.clone();
    big[0] = 0x01;
    assert_eq!(
        parse_extra_data_l2_block_number(&big),
        Err(FaultProofAnchorError::L2BlockNumberOverflow)
    );
}

// ---------------------------------------------------------------------------
// The exclusion-proof helper: both polarities + the measured alloy-trie hole
// ---------------------------------------------------------------------------

/// ACCEPT: the REAL exclusion proof — the live ASR storage trie does not
/// contain `disputeGameBlacklist[game]`.
#[test]
fn blacklist_exclusion_proof_accepts() {
    assert!(verify_evm_storage_slot_absent(
        h32(fx::ASR_STORAGE_HASH),
        h32(fx::BLACKLIST_SLOT),
        &nodes(fx::BLACKLIST_ABSENCE_PROOF),
    )
    .is_ok());
}

/// REJECT: an absence claim for a PRESENT key. ASR slot 6 IS in the trie; its
/// (valid!) inclusion proof must not pass as an exclusion proof.
#[test]
fn absence_of_present_key_rejects() {
    assert!(verify_evm_storage_slot_absent(
        h32(fx::ASR_STORAGE_HASH),
        slot_be32(6),
        &nodes(fx::ASR_SLOT6_PROOF),
    )
    .is_err());
}

/// REJECT (the measured alloy-trie 0.9.5 hole, pinned): every TRUNCATED PREFIX
/// of a valid INCLUSION proof must refuse as an absence proof. alloy's
/// `verify_proof(…, None, …)` alone ACCEPTS these (a pending hash-continuation
/// and a real absence terminal both collapse to `None`); the strict-termination
/// re-walk in `verify_evm_storage_slot_absent` is what refuses. Without it, an
/// attacker whose game IS blacklisted truncates the blacklist entry's inclusion
/// proof and "proves" absence.
#[test]
fn truncated_inclusion_prefix_rejects_as_absence() {
    let full = nodes(fx::ASR_SLOT6_PROOF);
    assert!(full.len() >= 2, "fixture proof must have interior nodes");
    for cut in 1..full.len() {
        assert!(
            verify_evm_storage_slot_absent(h32(fx::ASR_STORAGE_HASH), slot_be32(6), &full[..cut],)
                .is_err(),
            "a {cut}-node prefix of the slot-6 inclusion proof must not prove absence"
        );
    }
}

/// REJECT: truncated prefixes of the REAL absence proof also refuse — the
/// terminal node is what carries the absence evidence.
#[test]
fn truncated_absence_proof_rejects() {
    let full = nodes(fx::BLACKLIST_ABSENCE_PROOF);
    for cut in 1..full.len() {
        assert!(
            verify_evm_storage_slot_absent(
                h32(fx::ASR_STORAGE_HASH),
                h32(fx::BLACKLIST_SLOT),
                &full[..cut],
            )
            .is_err(),
            "a {cut}-node prefix of the absence proof must refuse"
        );
    }
    // And the empty proof refuses (the storage root is not the empty-trie root).
    assert!(verify_evm_storage_slot_absent(
        h32(fx::ASR_STORAGE_HASH),
        h32(fx::BLACKLIST_SLOT),
        &[],
    )
    .is_err());
}

/// REJECT: a tampered absence-proof node fails the hash linkage.
#[test]
fn tampered_absence_proof_rejects() {
    let mut p = nodes(fx::BLACKLIST_ABSENCE_PROOF);
    let last = p.len() - 1;
    p[last][7] ^= 0x01;
    assert!(
        verify_evm_storage_slot_absent(h32(fx::ASR_STORAGE_HASH), h32(fx::BLACKLIST_SLOT), &p,)
            .is_err()
    );
}

// ---------------------------------------------------------------------------
// The anchor opening: accept (REAL external fixture)
// ---------------------------------------------------------------------------

#[test]
fn fault_proof_anchor_accepts() {
    let committed = run_anchor(&l1_finalized(), &params(), &anchor())
        .expect("the real live-Base dispute-game anchor must verify");
    assert_eq!(committed.output_root, h32(fx::ROOT_CLAIM));
    assert_eq!(committed.l2_block_number, fx::L2_BLOCK_NUMBER);
    assert_eq!(committed.timestamp, fx::GAME_RESOLVED_AT as u128);
}

#[test]
fn full_fault_proof_holding_accepts_consensus_proven() {
    let proven = run_full(
        &params(),
        &anchor(),
        &l2_commitment(),
        u256(fx::EXPECTED_BALANCE_HEX),
    )
    .expect("the full real live-Base fault-proof chain must verify");
    assert_eq!(proven.trust, HoldingTrust::ConsensusProven);
    assert_eq!(proven.balance, u256(fx::EXPECTED_BALANCE_HEX));
    assert_eq!(proven.token, h20(fx::TOKEN));
    assert_eq!(proven.holder, h20(fx::HOLDER));
    // Anchored at the L2 state root and the L1-PROVEN L2 block number (parsed
    // from the UUID-bound extraData, never caller-claimed).
    assert_eq!(proven.state_root, h32(fx::L2_STATE_ROOT));
    assert_eq!(proven.block_number, fx::L2_BLOCK_NUMBER);

    // The governance edge: EVM family tag (Base = ChainId::Evm(8453) downstream).
    let fields = proven.to_foreign_fields().expect("fits u128");
    assert_eq!(fields.chain_tag, CHAIN_TAG_EVM);
    assert!(fields.consensus_proven);
    assert_eq!(fields.snapshot, fx::L2_BLOCK_NUMBER);
}

// ---------------------------------------------------------------------------
// Rejects: the respected-game-type gate
// ---------------------------------------------------------------------------

/// A claim for a game type other than the configured one refuses outright.
#[test]
fn wrong_game_type_rejects() {
    let mut a = anchor();
    a.game_type = 0; // classic permissionless CANNON — deregistered on live Base
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameTypeMismatch {
            got: 0,
            expected: BASE_AGGREGATE_VERIFIER_GAME_TYPE
        })
    );
}

/// A verifier re-pinned to a DIFFERENT expected type (as after a governance
/// rotation we have not validated) must refuse against the real chain: the
/// slot-6 word no longer opens.
#[test]
fn rotated_respected_game_type_rejects_at_slot6() {
    let mut p = params();
    p.expected_game_type = 622;
    let mut a = anchor();
    a.game_type = 622; // passes the cheap equality gate; the CHAIN refuses
    assert_eq!(
        run_anchor(&l1_finalized(), &p, &a),
        Err(FaultProofAnchorError::RespectedGameTypeSlotProofInvalid)
    );
}

// ---------------------------------------------------------------------------
// Rejects: THE KEYSTONE — the GameId binding
// ---------------------------------------------------------------------------

/// Tampering ONE BYTE of extraData moves the UUID, hence the mapping slot: the
/// proof cannot open. (extraData carries the L2 block number — this is what
/// stops a forged snapshot height.)
#[test]
fn tampered_extra_data_rejects() {
    let mut a = anchor();
    a.extra_data[40] ^= 0x01; // inside the parentGame field
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameIdSlotProofInvalid)
    );
    // The leading l2BlockNumber word specifically:
    let mut a = anchor();
    a.extra_data[31] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameIdSlotProofInvalid)
    );
}

/// A forged rootClaim refuses AT THE BINDING (not merely downstream at the
/// output-root recompute): the UUID moves. An attacker cannot detach the claim
/// from the game.
#[test]
fn forged_root_claim_rejects_at_game_id_binding() {
    let mut a = anchor();
    a.root_claim[5] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameIdSlotProofInvalid)
    );
}

/// A forged game proxy address changes the packed GameId word: refused. (This
/// is what stops pointing the resolution checks at a DIFFERENT, attacker-chosen
/// contract that resolved DEFENDER_WINS for some other claim.)
#[test]
fn forged_game_address_rejects() {
    let mut a = anchor();
    a.game_address[19] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameIdSlotProofInvalid)
    );
}

/// A forged createdAt changes the packed GameId word: refused (and the same
/// field feeds the slot-0 word — the cross-tooth is by construction).
#[test]
fn forged_created_at_rejects() {
    let mut a = anchor();
    a.game_created_at += 1;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameIdSlotProofInvalid)
    );
}

// ---------------------------------------------------------------------------
// Rejects: resolution status / retirement / resolvedAt
// ---------------------------------------------------------------------------

/// An honest claim of a non-DEFENDER_WINS status refuses outright.
#[test]
fn non_defender_wins_status_rejects() {
    for status in [GAME_STATUS_IN_PROGRESS, GAME_STATUS_CHALLENGER_WINS, 3u8] {
        let mut a = anchor();
        a.game_status = status;
        assert_eq!(
            run_anchor(&l1_finalized(), &params(), &a),
            Err(FaultProofAnchorError::GameNotDefenderWins { status }),
            "status {status} must refuse"
        );
    }
}

#[test]
fn zero_resolved_at_rejects() {
    let mut a = anchor();
    a.game_resolved_at = 0;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameNotResolved)
    );
}

/// A forged resolvedAt (e.g. back-dated to fake out the airgap) changes the
/// slot-0 word: refused by the proof.
#[test]
fn forged_resolved_at_rejects() {
    let mut a = anchor();
    a.game_resolved_at -= 7200; // pretend it resolved two hours earlier
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameResolutionSlotProofInvalid)
    );
}

/// A game created at/before the retirement boundary is not an anchor.
#[test]
fn retired_game_rejects() {
    let mut a = anchor();
    a.retirement_timestamp = fx::GAME_CREATED_AT; // createdAt <= retirement
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameRetired {
            created_at: fx::GAME_CREATED_AT,
            retirement_timestamp: fx::GAME_CREATED_AT,
        })
    );
}

/// A LIED retirement timestamp (to smuggle a retired game past the predicate)
/// fails the slot-6 proof — the retirement bound is L1-anchored.
#[test]
fn forged_retirement_timestamp_rejects() {
    let mut a = anchor();
    a.retirement_timestamp = 0; // claim "nothing is retired"
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::RespectedGameTypeSlotProofInvalid)
    );
}

#[test]
fn zero_root_claim_rejects() {
    let mut a = anchor();
    a.root_claim = [0u8; 32];
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::ZeroRootClaim)
    );
}

// ---------------------------------------------------------------------------
// Rejects: the airgap / finality window (strict boundary)
// ---------------------------------------------------------------------------

#[test]
fn airgap_not_elapsed_rejects() {
    let mut p = params();
    p.policy_finality_delay = 86_400; // a day of guardian window — not elapsed yet
    assert_eq!(
        run_anchor(&l1_finalized(), &p, &anchor()),
        Err(FaultProofAnchorError::AirgapNotElapsed {
            l1_time: fx::L1_TIMESTAMP,
            resolved_at: fx::GAME_RESOLVED_AT,
            required_delay: 86_400,
        })
    );
}

/// The boundary is STRICT: `l1_time == resolvedAt + delay` refuses;
/// one second less accepts. (Mirrors the live ASR's `isGameFinalized`
/// `<=`-reject.)
#[test]
fn airgap_boundary_is_strict() {
    let mut p = params();
    p.policy_finality_delay = FIXTURE_AIRGAP_MARGIN; // deadline == l1_time
    assert!(matches!(
        run_anchor(&l1_finalized(), &p, &anchor()),
        Err(FaultProofAnchorError::AirgapNotElapsed { .. })
    ));
    p.policy_finality_delay = FIXTURE_AIRGAP_MARGIN - 1; // deadline == l1_time - 1
    assert!(run_anchor(&l1_finalized(), &p, &anchor()).is_ok());
}

/// The ON-CHAIN delay component is enforced through the same max():
/// a counterfactual nonzero ASR delay refuses identically.
#[test]
fn asr_delay_component_enforced() {
    let mut p = params();
    p.dispute_game_finality_delay = 86_400;
    p.policy_finality_delay = 0;
    assert!(matches!(
        run_anchor(&l1_finalized(), &p, &anchor()),
        Err(FaultProofAnchorError::AirgapNotElapsed { .. })
    ));
}

/// resolvedAt + delay overflowing u64 refuses (never wraps into the past).
#[test]
fn airgap_overflow_rejects() {
    let mut p = params();
    p.policy_finality_delay = u64::MAX;
    assert!(matches!(
        run_anchor(&l1_finalized(), &p, &anchor()),
        Err(FaultProofAnchorError::AirgapNotElapsed { .. })
    ));
}

// ---------------------------------------------------------------------------
// Rejects: tampered proofs / wrong roots / code-hash pin
// ---------------------------------------------------------------------------

#[test]
fn wrong_l1_state_root_rejects() {
    let mut sr = h32(fx::L1_STATE_ROOT);
    sr[0] ^= 0x01;
    let l1 = FinalizedExecution::new_unchecked(
        0,
        [0u8; 32],
        fx::L1_BLOCK_NUMBER,
        h32(fx::L1_BLOCK_HASH),
        sr,
        fx::L1_TIMESTAMP,
    );
    assert_eq!(
        run_anchor(&l1, &params(), &anchor()),
        Err(FaultProofAnchorError::AsrAccountProofInvalid)
    );
}

#[test]
fn tampered_asr_account_proof_rejects() {
    let mut a = anchor();
    let last = a.asr_account_proof.len() - 1;
    a.asr_account_proof[last][11] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::AsrAccountProofInvalid)
    );
}

/// A wrong DGF address in params fails the ASR slot-1 binding — the factory
/// identity is L1-anchored, not configuration.
#[test]
fn wrong_dgf_address_rejects_at_slot1_binding() {
    let mut p = params();
    p.dgf_address[10] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &p, &anchor()),
        Err(FaultProofAnchorError::DgfBindingSlotProofInvalid)
    );
}

#[test]
fn tampered_dgf_account_proof_rejects() {
    let mut a = anchor();
    let last = a.dgf_account_proof.len() - 1;
    a.dgf_account_proof[last][9] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::DgfAccountProofInvalid)
    );
}

#[test]
fn tampered_game_id_slot_proof_rejects() {
    let mut a = anchor();
    let last = a.game_id_slot_proof.len() - 1;
    a.game_id_slot_proof[last][13] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameIdSlotProofInvalid)
    );
}

#[test]
fn tampered_game_account_proof_rejects() {
    let mut a = anchor();
    let last = a.game_account_proof.len() - 1;
    a.game_account_proof[last][15] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameAccountProofInvalid)
    );
}

#[test]
fn tampered_game_slot0_proof_rejects() {
    let mut a = anchor();
    let last = a.game_slot0_proof.len() - 1;
    a.game_slot0_proof[last][10] ^= 0x01;
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameResolutionSlotProofInvalid)
    );
}

/// An unknown game bytecode (a different clone / an upgraded impl we have not
/// re-pinned) refuses — unknown code hash means unknown game semantics.
#[test]
fn wrong_game_code_hash_rejects() {
    let mut p = params();
    p.game_code_hash[0] ^= 0x01;
    assert!(matches!(
        run_anchor(&l1_finalized(), &p, &anchor()),
        Err(FaultProofAnchorError::GameCodeHashMismatch { .. })
    ));
}

/// Swapping the blacklist ABSENCE proof for a proof of a different (present)
/// key refuses — presence evidence is not absence evidence.
#[test]
fn wrong_proof_for_blacklist_exclusion_rejects() {
    let mut a = anchor();
    a.blacklist_absence_proof = nodes(fx::ASR_SLOT6_PROOF);
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameBlacklistNotExcluded)
    );
}

/// A TRUNCATED blacklist absence proof refuses through the composition (the
/// alloy-trie exclusion hole must not be reachable from the anchor entry).
#[test]
fn truncated_blacklist_proof_rejects_through_composition() {
    let mut a = anchor();
    a.blacklist_absence_proof.pop();
    assert_eq!(
        run_anchor(&l1_finalized(), &params(), &a),
        Err(FaultProofAnchorError::GameBlacklistNotExcluded)
    );
}

// ---------------------------------------------------------------------------
// Rejects: the L2 tail (output-root binding + holding)
// ---------------------------------------------------------------------------

/// The attack this composition exists to stop: a VALID-LOOKING L2 state root
/// the resolved game never committed.
#[test]
fn forged_l2_state_root_rejects() {
    let mut c = l2_commitment();
    c.l2_state_root[7] ^= 0x01;
    assert!(matches!(
        run_full(&params(), &anchor(), &c, u256(fx::EXPECTED_BALANCE_HEX)),
        Err(FaultProofAnchorError::OutputRoot(
            BaseProofError::OutputRootMismatch { .. }
        ))
    ));
}

#[test]
fn wrong_output_root_version_rejects() {
    let mut c = l2_commitment();
    c.version[31] = 1;
    assert!(matches!(
        run_full(&params(), &anchor(), &c, u256(fx::EXPECTED_BALANCE_HEX)),
        Err(FaultProofAnchorError::OutputRoot(
            BaseProofError::UnsupportedOutputRootVersion { .. }
        ))
    ));
}

#[test]
fn wrong_l2_balance_rejects() {
    let bad = u256(fx::EXPECTED_BALANCE_HEX) + Uint256::from(1u8);
    assert_eq!(
        run_full(&params(), &anchor(), &l2_commitment(), bad),
        Err(FaultProofAnchorError::L2Holding(
            Erc20ProofError::StorageProofInvalid
        ))
    );
}

// ---------------------------------------------------------------------------
// SELF-CONSISTENT SYNTHESIS — hostile worlds no honest chain can serve.
// Named honestly: these tries are built locally with the same pinned
// alloy-trie HashBuilder (synthesis ≠ external conformance); the point is the
// GATE, not the fixture.
// ---------------------------------------------------------------------------

mod synthetic {
    use super::*;
    use alloy_primitives::{keccak256, Bytes, B256};
    use alloy_trie::{proof::ProofRetainer, HashBuilder, Nibbles, TrieAccount};

    /// Build a trie from (raw_key, rlp_value) pairs, returning the root and,
    /// for each requested target key, its proof node list.
    fn build_trie(
        entries: &[([u8; 32], Vec<u8>)],
        targets: &[[u8; 32]],
    ) -> ([u8; 32], Vec<Vec<Vec<u8>>>) {
        let target_nibbles: Vec<Nibbles> = targets
            .iter()
            .map(|k| Nibbles::unpack(keccak256(k)))
            .collect();
        let retainer = ProofRetainer::new(target_nibbles.clone());
        let mut hb = HashBuilder::default().with_proof_retainer(retainer);
        let mut sorted: Vec<(Nibbles, &Vec<u8>)> = entries
            .iter()
            .map(|(k, v)| (Nibbles::unpack(keccak256(k)), v))
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        for (path, value) in sorted {
            hb.add_leaf(path, value);
        }
        let root: B256 = hb.root();
        let retained: Vec<(Nibbles, Bytes)> = hb.take_proof_nodes().into_nodes_sorted();
        let proofs = target_nibbles
            .iter()
            .map(|t| {
                retained
                    .iter()
                    .filter(|(p, _)| t.starts_with(p))
                    .map(|(_, n)| n.to_vec())
                    .collect::<Vec<_>>()
            })
            .collect();
        (root.0, proofs)
    }

    fn rlp_u256(v: Uint256) -> Vec<u8> {
        alloy_rlp::encode(v)
    }

    fn rlp_account(a: &AccountClaim) -> Vec<u8> {
        alloy_rlp::encode(TrieAccount {
            nonce: a.nonce,
            balance: a.balance,
            storage_root: a.storage_hash.into(),
            code_hash: a.code_hash.into(),
        })
    }

    /// A synthetic L1 world that mirrors the real fixture EXCEPT for the
    /// requested hostility: `blacklisted` plants the game in the ASR blacklist;
    /// `chain_status`/`chain_respected_flag` control the game's REAL slot-0
    /// word. The DGF storage (GameId binding) and game-storage layout reuse the
    /// real fixture where unchanged.
    struct World {
        state_root: [u8; 32],
        anchor: FaultProofAnchor,
    }

    fn build_world(blacklisted: bool, chain_status: u8, chain_respected_flag: bool) -> World {
        // --- ASR storage trie: slot 6 + slot 1 (+ blacklist entry if hostile).
        let slot6_val = rlp_u256(pack_asr_respected_word(
            fx::RETIREMENT_TIMESTAMP,
            fx::RESPECTED_GAME_TYPE,
        ));
        let mut asr_dgf_word = [0u8; 32];
        asr_dgf_word[12..].copy_from_slice(&h20(fx::DGF_ADDRESS));
        let slot1_val = rlp_u256(Uint256::from_be_bytes(asr_dgf_word));
        let blacklist_key = h32(fx::BLACKLIST_SLOT);
        let mut asr_entries = vec![(slot_be32(6), slot6_val), (slot_be32(1), slot1_val)];
        if blacklisted {
            asr_entries.push((blacklist_key, rlp_u256(Uint256::from(1u8))));
        }
        let (asr_storage_root, asr_storage_proofs) =
            build_trie(&asr_entries, &[slot_be32(6), slot_be32(1), blacklist_key]);

        // --- Game storage trie: slot 0 with the CHAIN's actual status/flags.
        let slot0_val = rlp_u256(pack_game_resolution_word(
            fx::GAME_CREATED_AT,
            fx::GAME_RESOLVED_AT,
            chain_status,
            true,
            chain_respected_flag,
        ));
        let (game_storage_root, game_storage_proofs) =
            build_trie(&[(slot_be32(0), slot0_val)], &[slot_be32(0)]);

        // --- Account trie: ASR (synthetic storage), DGF (REAL storage hash, so
        //     the real GameId proof still opens), game (synthetic storage).
        let asr_acct = AccountClaim {
            storage_hash: asr_storage_root,
            ..super::asr_account()
        };
        let dgf_acct = AccountClaim {
            nonce: fx::DGF_NONCE,
            balance: u256(fx::DGF_BALANCE_HEX),
            storage_hash: h32(fx::DGF_STORAGE_HASH),
            code_hash: h32(fx::DGF_CODE_HASH),
        };
        let game_acct = AccountClaim {
            nonce: fx::GAME_NONCE,
            balance: u256(fx::GAME_BALANCE_HEX),
            storage_hash: game_storage_root,
            code_hash: h32(fx::GAME_CODE_HASH),
        };
        let (state_root, account_proofs) = build_account_trie(&[
            (h20(fx::ASR_ADDRESS), rlp_account(&asr_acct)),
            (h20(fx::DGF_ADDRESS), rlp_account(&dgf_acct)),
            (h20(fx::GAME_ADDRESS), rlp_account(&game_acct)),
        ]);

        let anchor = FaultProofAnchor {
            asr_account: asr_acct,
            asr_account_proof: account_proofs[0].clone(),
            retirement_timestamp: fx::RETIREMENT_TIMESTAMP,
            respected_game_type_slot_proof: asr_storage_proofs[0].clone(),
            dgf_binding_slot_proof: asr_storage_proofs[1].clone(),
            blacklist_absence_proof: asr_storage_proofs[2].clone(),
            dgf_account: dgf_acct,
            dgf_account_proof: account_proofs[1].clone(),
            game_id_slot_proof: nodes(fx::GAME_ID_SLOT_PROOF), // REAL binding
            game_address: h20(fx::GAME_ADDRESS),
            game_created_at: fx::GAME_CREATED_AT,
            game_resolved_at: fx::GAME_RESOLVED_AT,
            game_status: GAME_STATUS_DEFENDER_WINS, // the CLAIM (may be a lie)
            game_account: game_acct,
            game_account_proof: account_proofs[2].clone(),
            game_slot0_proof: game_storage_proofs[0].clone(),
            game_type: fx::GAME_TYPE,
            root_claim: h32(fx::ROOT_CLAIM),
            extra_data: hex::decode(fx::EXTRA_DATA).unwrap(),
        };
        World { state_root, anchor }
    }

    /// Account trie: keys are keccak256(address) (20-byte preimage).
    fn build_account_trie(entries: &[([u8; 20], Vec<u8>)]) -> ([u8; 32], Vec<Vec<Vec<u8>>>) {
        let target_nibbles: Vec<Nibbles> = entries
            .iter()
            .map(|(a, _)| Nibbles::unpack(keccak256(a)))
            .collect();
        let retainer = ProofRetainer::new(target_nibbles.clone());
        let mut hb = HashBuilder::default().with_proof_retainer(retainer);
        let mut sorted: Vec<(Nibbles, &Vec<u8>)> = entries
            .iter()
            .map(|(a, v)| (Nibbles::unpack(keccak256(a)), v))
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        for (path, value) in sorted {
            hb.add_leaf(path, value);
        }
        let root: B256 = hb.root();
        let retained: Vec<(Nibbles, Bytes)> = hb.take_proof_nodes().into_nodes_sorted();
        let proofs = target_nibbles
            .iter()
            .map(|t| {
                retained
                    .iter()
                    .filter(|(p, _)| t.starts_with(p))
                    .map(|(_, n)| n.to_vec())
                    .collect::<Vec<_>>()
            })
            .collect();
        (root.0, proofs)
    }

    fn l1_at(state_root: [u8; 32]) -> FinalizedExecution {
        FinalizedExecution::new_unchecked(
            0,
            [0u8; 32],
            fx::L1_BLOCK_NUMBER,
            [0u8; 32],
            state_root,
            fx::L1_TIMESTAMP,
        )
    }

    /// Harness validity: the benign synthetic world (not blacklisted,
    /// DEFENDER_WINS, respected-at-creation) verifies end-to-end — so the
    /// refusals below are attributable to the ONE hostile difference, not to a
    /// broken harness. SELF-CONSISTENT, not external conformance.
    #[test]
    fn benign_synthetic_world_accepts() {
        let w = build_world(false, GAME_STATUS_DEFENDER_WINS, true);
        let committed =
            verify_l1_fault_proof_output_root(&l1_at(w.state_root), &super::params(), &w.anchor)
                .expect("benign synthetic world must verify");
        assert_eq!(committed.output_root, h32(fx::ROOT_CLAIM));
        assert_eq!(committed.l2_block_number, fx::L2_BLOCK_NUMBER);
    }

    /// THE BLACKLIST GATE: identical world, except the guardian blacklisted the
    /// game. Every other link passes; the exclusion link must refuse. (The
    /// attacker here even submits the VALID inclusion proof of the blacklist
    /// entry as their "absence proof".)
    #[test]
    fn blacklisted_game_rejects() {
        let w = build_world(true, GAME_STATUS_DEFENDER_WINS, true);
        assert_eq!(
            verify_l1_fault_proof_output_root(&l1_at(w.state_root), &super::params(), &w.anchor,),
            Err(FaultProofAnchorError::GameBlacklistNotExcluded)
        );
    }

    /// A LYING claim: the chain's slot 0 says CHALLENGER_WINS (or IN_PROGRESS)
    /// but the caller claims DEFENDER_WINS. The recomputed slot-0 word cannot
    /// open against the game's storage: refused.
    #[test]
    fn lying_defender_wins_claim_rejects() {
        for chain_status in [GAME_STATUS_IN_PROGRESS, GAME_STATUS_CHALLENGER_WINS] {
            let w = build_world(false, chain_status, true);
            assert_eq!(
                verify_l1_fault_proof_output_root(
                    &l1_at(w.state_root),
                    &super::params(),
                    &w.anchor,
                ),
                Err(FaultProofAnchorError::GameResolutionSlotProofInvalid),
                "chain status {chain_status} with a DEFENDER_WINS claim must refuse"
            );
        }
    }

    /// A game that was NOT the respected type when created (the flag the ASR's
    /// `isGameRespected` reads) refuses even with DEFENDER_WINS status.
    #[test]
    fn not_respected_at_creation_rejects() {
        let w = build_world(false, GAME_STATUS_DEFENDER_WINS, false);
        assert_eq!(
            verify_l1_fault_proof_output_root(&l1_at(w.state_root), &super::params(), &w.anchor,),
            Err(FaultProofAnchorError::GameResolutionSlotProofInvalid)
        );
    }
}
