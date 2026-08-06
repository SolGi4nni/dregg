//! **THE RECEIPT-CHAIN HEAD IS A NODE, SO IT NEEDS COLLISION RESISTANCE — AND IT HAD 64 BITS.**
//!
//! The verified kernel's `admissible` ChainHead leg is a `Nat` equality,
//! `h.prevReceipt = ctx.storedHead` (`Dregg2/Exec/Admission.lean`). Both operands are unbounded
//! `Nat`s in Lean. Until this file's flag day, **Rust folded both to their low 64 bits** before
//! they crossed:
//!
//! * `lean_shadow.rs`'s `stored_head_nat = bytes32_to_nat(&head)` — bytes `[24..32]` of the host's
//!   real 32-byte head;
//! * `lean_shadow.rs`'s `prev_hash = Digest::from_u64(bytes32_to_nat(&h))` — the turn's CLAIMED
//!   32-byte prev, narrowed to the same 8 bytes.
//!
//! The comment defending it said the two paths "compare like-for-like", which is TRUE and is a
//! statement about *path agreement*, not about *fidelity*. What the verified leg actually decided
//! was `low64(claimed) = low64(stored)` — an equivalence whose fibers hold `2^192` values each.
//!
//! ## The cost, derived — and it is NOT a birthday bound
//!
//! `Turn::previous_receipt_hash : Option<[u8; 32]>` is agent-supplied and carries no structural
//! obligation: nothing anywhere requires it to be the hash of anything. So the adversary is not
//! searching for a collision, they are **naming a member of a known fiber**. Given the true head
//! `H` (which an honest agent must already know to build an honest turn), every `X` with
//! `X[24..32] == H[24..32]` is accepted, and `X = H ^ (1 << 255)` is one XOR away.
//!
//! * **2^0** — one operation, zero hash evaluations. This is the deployed cost, and the number
//!   that belongs in the finding.
//! * 2^64 would be the cost if the claimed prev had to be a GENUINE receipt hash the adversary can
//!   produce (grind receipts until one folds onto a target head) — a targeted second-preimage on
//!   the fold.
//! * 2^32 would be the birthday cost of two genuine receipts of the adversary's own colliding
//!   under the fold, with no target.
//!
//! Neither of the last two applies here. Quoting one of them would be the flattering-number sin.
//!
//! ## Why it was not merely "instrumented"
//!
//! Producer mode (`produce_via_lean`, default-ON via `DREGG_LEAN_PRODUCER`) makes the Lean verdict
//! AUTHORITATIVE: on a covered turn, `lean_committed` installs the Lean post-state **and overrides
//! a Rust rejection**. The Rust reference does compare all 32 bytes
//! (`TurnExecutor::check_previous_receipt_hash`), and its refusal did surface — as
//! `ProducerDivergence::CommitBit` on an `error!` log line labelled *"the Rust path is BUGGY"*.
//! The turn still committed. `build_producer_committed_result` then minted a receipt carrying
//! `previous_receipt_hash: turn.previous_receipt_hash` — the adversary's value verbatim — SIGNED
//! it, and **advanced the executor's stored head onto it** (`finalize.rs`'s `record_receipt_hash`).
//!
//! ⚑ That is the consequence in the kernel's own vocabulary. `Admission.admissible_append_wellLinked`
//! preserves `wellLinked` across an admitted turn *given* `(head of chain) = headDigest ctx`. Under
//! the fold, `headDigest ctx` was `low64(H)` while the chain's real head hash was `H`, so the
//! hypothesis was false on the deployed path and the tamper-evidence conclusion did not transfer.
//! The chain could accept — and permanently keep — a node whose `prevHash` is the hash of nothing.
//!
//! So the fold was a reachable authority hole on the default production path, not a gap held shut
//! by a cross-check.
//!
//! ## What this file pins
//!
//! * NON-VACUITY — the demoted Rust reference, alone, refuses the fold sibling (so the refusal
//!   below is not one Rust would have made for some other reason).
//! * COMPLETENESS — an honest head still crosses the shadow and both executors still agree.
//! * THE TOOTH — the fold sibling is REFUSED by the authoritative verified verdict, on a turn the
//!   verified producer genuinely decides (`LeanAuthoritative`, never a `Fallback`).
//!
//! Run:
//!   DREGG_TEST_REQUIRE_LEAN=1 cargo nextest run -p dregg-exec-lean \
//!       --test chain_head_fold_collision

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

/// The executor a native node builds (`node::executor_setup::new_submit_executor`).
fn node_shaped_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc())
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn one_cell_ledger(bal: i64) -> (Ledger, CellId) {
    let mut pk = [0u8; 32];
    pk[0] = 1;
    pk[31] = 37;
    let mut cell = Cell::with_balance(pk, [0u8; 32], bal);
    cell.permissions = open_permissions();
    let id = cell.id();
    let mut l = Ledger::new();
    l.insert_cell(cell).unwrap();
    (l, id)
}

/// A field write the marshaller carries at full width — the simplest turn in the COVERED
/// (root-agreeing) set, so the verified producer genuinely decides it.
const WRITTEN: [u8; 32] = {
    let mut v = [0u8; 32];
    v[31] = 0xcd;
    v
};

fn set_field(agent: CellId, nonce: u64, prev: Option<[u8; 32]>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: agent,
            index: 3,
            value: WRITTEN,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000_000),
        previous_receipt_hash: prev,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// A REAL 32-byte receipt-chain head with a non-zero low lane (a low lane of zero would fold onto
/// `prevReceiptOf`'s genesis sentinel on both sides and make the exhibit test something else).
const TRUE_HEAD: [u8; 32] = [
    0xd2, 0x50, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
    0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69, 0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2, 0xe1, 0xf0,
];

/// THE EXHIBIT, in one operation: flip the top bit. The low 8 bytes — the entire content of the
/// old `bytes32_to_nat` fold — are untouched, so the two heads were INDISTINGUISHABLE to the
/// verified ChainHead leg. No search, no hashing, no grinding.
fn fold_sibling(h: [u8; 32]) -> [u8; 32] {
    let mut x = h;
    x[0] ^= 0x80;
    x
}

fn require_lean() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "verified Turn executor archive (lean_available)",
    )
}

/// THE EXHIBIT IS WHAT IT CLAIMS TO BE — and it costs one operation.
///
/// ⚑ "the digests differ" is NOT the property. The property is that they differ *while agreeing on
/// every bit the old projection kept*, which is what made the verified leg unable to tell them
/// apart. Asserting only `!=` would pass for any two distinct hashes and prove nothing.
#[test]
fn the_exhibit_is_a_fold_sibling_built_in_one_operation() {
    let x = fold_sibling(TRUE_HEAD);
    assert_ne!(x, TRUE_HEAD, "the sibling must be a DIFFERENT 256-bit head");
    assert_eq!(
        x[24..32],
        TRUE_HEAD[24..32],
        "the sibling must agree on the low 8 bytes — the ENTIRE content of the retired \
         `bytes32_to_nat` projection. This equality is the collision; the inequality above is what \
         makes it an attack."
    );
    assert_ne!(
        x[0..24],
        TRUE_HEAD[0..24],
        "…and it must differ somewhere in the 192 bits the old projection discarded"
    );
    // Derived, not asserted: the fiber of `low64` over a known head has 2^192 members and the
    // adversary names one with a single XOR. Not 2^32 (birthday, no target), not 2^64 (targeted
    // second-preimage on the fold with a GENUINE receipt) — those bounds require the claimed prev
    // to be a real receipt hash, and `Turn::previous_receipt_hash` carries no such obligation.
}

/// NON-VACUITY — the demoted Rust reference, on its own, REFUSES the fold sibling with the
/// chain-head error. Without this, the refusal the tooth asserts could be any other gate firing.
#[test]
fn the_rust_reference_alone_refuses_the_fold_sibling() {
    let (mut ledger, agent) = one_cell_ledger(100);
    let rust_only = TurnExecutor::new(ComputronCosts::zero());
    rust_only.set_last_receipt_hash(agent, TRUE_HEAD);

    let sibling = fold_sibling(TRUE_HEAD);
    let r = rust_only.execute(&set_field(agent, 0, Some(sibling)), &mut ledger);
    match &r {
        dregg_turn::turn::TurnResult::Rejected {
            reason: dregg_turn::TurnError::ReceiptChainMismatch { expected, got },
            ..
        } => {
            assert_eq!(*expected, Some(TRUE_HEAD));
            assert_eq!(*got, Some(sibling));
        }
        other => panic!(
            "the Rust reference compares all 32 bytes and must refuse the fold sibling as \
             ReceiptChainMismatch, got {other:?}"
        ),
    }

    // …and it COMMITS the honest head, so the refusal above is about the head and nothing else.
    let (mut ledger2, agent2) = one_cell_ledger(100);
    let rust_only2 = TurnExecutor::new(ComputronCosts::zero());
    rust_only2.set_last_receipt_hash(agent2, TRUE_HEAD);
    let ok = rust_only2.execute(&set_field(agent2, 0, Some(TRUE_HEAD)), &mut ledger2);
    assert!(
        ok.is_committed(),
        "PRECONDITION: the same turn with the TRUE head must commit on the Rust reference, \
         got {ok:?}"
    );
}

/// COMPLETENESS — an honest chain head still crosses the shadow, the verified producer still
/// decides the turn, and the two executors still AGREE. A fix that refused honest chains would
/// satisfy the tooth below and be worthless.
#[test]
fn an_honest_chain_head_still_commits_and_both_executors_agree() {
    if !require_lean() {
        return;
    }
    let (mut ledger, agent) = one_cell_ledger(100);
    let executor = node_shaped_executor();
    executor.set_last_receipt_hash(agent, TRUE_HEAD);

    let (result, outcome) = dregg_exec_lean::produce_via_lean(
        &executor,
        &set_field(agent, 0, Some(TRUE_HEAD)),
        &mut ledger,
    );

    assert!(
        matches!(
            outcome,
            dregg_exec_lean::ProducerOutcome::LeanAuthoritative { .. }
        ),
        "the turn must be COVERED (the verified producer decides it), not fenced onto Rust — a \
         Fallback would make every other assertion here vacuous. got {outcome:?}"
    );
    assert!(
        result.is_committed(),
        "an honest chain-head turn must COMMIT through the authoritative producer, got {result:?}"
    );
    assert!(
        !outcome.rust_bug_surfaced(),
        "the two executors must AGREE on an honest chain head; a disagreement is a real finding: \
         {outcome:?}"
    );
    assert_eq!(
        ledger
            .get(&agent)
            .and_then(|c| c.state.get_field(3).copied()),
        Some(WRITTEN),
        "the committed write must be on the authoritative ledger"
    );
}

/// ⚑ **THE TOOTH — OLD ADMITS, NEW REJECTS.**
///
/// Before the flag day this turn COMMITTED: the verified ChainHead leg saw
/// `low64(sibling) = low64(TRUE_HEAD)` and admitted; the Rust reference refused on all 32 bytes;
/// `produce_via_lean` installed the Lean verdict and logged the Rust refusal as a *Rust bug*. The
/// receipt `build_producer_committed_result` then minted carried the adversary's `sibling` as its
/// `previous_receipt_hash`, signed.
///
/// After the flag day the whole 256-bit head crosses and the verified leg refuses it — with the
/// Rust reference now AGREEING, so no spurious "Rust bug" is surfaced either.
#[test]
fn a_fold_sibling_chain_head_is_refused_by_the_authoritative_verdict() {
    if !require_lean() {
        return;
    }
    let (mut ledger, agent) = one_cell_ledger(100);
    let executor = node_shaped_executor();
    executor.set_last_receipt_hash(agent, TRUE_HEAD);

    let sibling = fold_sibling(TRUE_HEAD);
    let (result, outcome) = dregg_exec_lean::produce_via_lean(
        &executor,
        &set_field(agent, 0, Some(sibling)),
        &mut ledger,
    );

    assert!(
        matches!(
            outcome,
            dregg_exec_lean::ProducerOutcome::LeanAuthoritative { .. }
        ),
        "the fold sibling must be REFUSED BY THE VERIFIED PRODUCER, not fenced onto Rust — a \
         Fallback here would mean the verified leg never ran and this tooth proves nothing. \
         got {outcome:?}"
    );
    assert!(
        !result.is_committed(),
        "OLD-ADMITS/NEW-REJECTS: a chain head that agrees with the stored head only on its low 64 \
         bits must NOT commit. It did before the head crossed at full width. got {result:?}"
    );
    assert_eq!(
        ledger
            .get(&agent)
            .and_then(|c| c.state.get_field(3).copied()),
        Some([0u8; 32]),
        "a refused turn is NO state edit — the field must still be its pre-state zero"
    );
    assert!(
        !outcome.rust_bug_surfaced(),
        "with the head crossing at full width the Rust reference AGREES with the verified refusal; \
         a surfaced 'Rust bug' here means the verified leg is still deciding on the fold. \
         got {outcome:?}"
    );
    match &result {
        dregg_turn::turn::TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                dregg_turn::TurnError::LeanShadowVeto
                    | dregg_turn::TurnError::AdmissionRefused { .. }
                    | dregg_turn::TurnError::ReceiptChainMismatch { .. }
            ),
            "the refusal must name a chain-head/verified-refusal shape, got {reason:?}"
        ),
        other => panic!("expected Rejected, got {other:?}"),
    }

    // …and the agent is not bricked: its next turn, claiming the TRUE head, still commits.
    let (next, next_outcome) = dregg_exec_lean::produce_via_lean(
        &executor,
        &set_field(agent, 0, Some(TRUE_HEAD)),
        &mut ledger,
    );
    assert!(
        next.is_committed(),
        "a refused fold sibling must leave the agent able to take its next honest turn, \
         got {next:?} / {next_outcome:?}"
    );
}

// ===================================================================
// ⚑ THE SAME TOOTH AT THE GATE ITSELF — the OLD projection and the NEW one, side by side, in one
// run, against the SAME verified kernel.
//
// The producer-level tooth above says what the system does TODAY. It cannot, on its own, show that
// the retired projection was the thing that admitted — a reader six weeks out has to take the
// commit archaeology on faith. These two drive the verified `admissible` gate directly through the
// JSON boundary (`shadow_exec_full_forest_auth`, the standing byte-exact oracle) with the two wire
// encodings EXPLICIT, so the fold is exhibited as a property of the encoding rather than of a
// past commit. The pair also cannot rot into agreement: re-narrowing the carrier turns the
// NEW-REJECTS half red while the OLD-ADMITS half stays green.
// ===================================================================

use dregg_lean_ffi::marshal::{
    Digest, WForest, WideInt, WireAction, WireAuth, WireHostCtx, WireState, WireTurn, WireValue,
    marshal_turn_hosted,
};

/// The low 64 bits, big-endian — `lean_shadow::bytes32_to_nat`, the RETIRED projection, reproduced
/// here so the exhibit carries the thing it accuses rather than a description of it.
fn retired_low64_fold(bytes: &[u8; 32]) -> u64 {
    u64::from_be_bytes(bytes[24..32].try_into().unwrap())
}

/// A one-cell state the verified kernel admits: cell `0` live, balance 100, nonce 7.
fn gate_state() -> WireState {
    WireState {
        cells: vec![(
            0,
            WireValue::Record(vec![
                ("balance".to_string(), WireValue::int(100i128)),
                ("nonce".to_string(), WireValue::int(7i128)),
            ]),
        )],
        bal: vec![(0, 0, 100)],
        ..WireState::default()
    }
}

/// A self-`SetField` turn under the `Unchecked`→`breadstuff` credential (the WHO leg passes; the
/// authority decision is `authorizedB`'s ownership disjunct, `actor = src`). Every admission leg
/// but ChainHead is satisfied, so ChainHead is the ONLY thing the two runs below differ on.
fn gate_turn(prev: Digest) -> WireTurn {
    WireTurn {
        agent: 0,
        nonce: 7,
        fee: 0,
        valid_until: 1000,
        block_height: 0,
        prev_hash: prev,
        root: WForest {
            auth: WireAuth::Breadstuff { token: 0 },
            caveats: vec![],
            action: WireAction::SetField {
                actor: 0,
                cell: 0,
                field: "owner".to_string(),
                v: WideInt::from(0xcdi128),
            },
            children: vec![],
        },
    }
}

fn run_gate(host: WireHostCtx, prev: Digest) -> dregg_lean_ffi::ShadowVerdict {
    run_gate_auth(host, prev, WireAuth::Breadstuff { token: 0 })
}

fn run_gate_auth(host: WireHostCtx, prev: Digest, auth: WireAuth) -> dregg_lean_ffi::ShadowVerdict {
    let mut turn = gate_turn(prev);
    turn.root.auth = auth;
    let wire = marshal_turn_hosted(&host, &gate_state(), &turn).expect("the fixture must marshal");
    let out = dregg_lean_ffi::shadow_exec_full_forest_auth(&wire).expect("the verified gate runs");
    dregg_lean_ffi::decode_shadow_verdict(&out).expect("the verdict decodes")
}

/// ⚑ **OLD ADMITS.** Feed the verified gate exactly what the retired marshaller fed it: both the
/// stored head and the claimed prev folded to their low 64 bits. The fold sibling — a DIFFERENT
/// 256-bit head — is ADMITTED and the turn COMMITS.
///
/// This is the wound, held in place so it stays legible: the kernel is not at fault (its ChainHead
/// leg is `Option Nat` structural equality on unbounded `Nat`s), the CARRIER was.
#[test]
fn the_retired_low64_projection_admits_the_fold_sibling() {
    if !require_lean() {
        return;
    }
    let sibling = fold_sibling(TRUE_HEAD);

    // The retired encoding, verbatim: `WireHostCtx.stored_head = bytes32_to_nat(head)` and
    // `prev = Digest::from_u64(bytes32_to_nat(claimed))`.
    let folded_head = {
        let mut h = [0u8; 32];
        h[24..32].copy_from_slice(&retired_low64_fold(&TRUE_HEAD).to_be_bytes());
        h
    };
    let host = WireHostCtx {
        stored_head: folded_head,
        ..WireHostCtx::diag()
    };
    let verdict = run_gate(host, Digest::from_u64(retired_low64_fold(&sibling)));

    assert!(
        verdict.committed,
        "under the RETIRED projection the verified gate could not distinguish the fold sibling \
         from the true head, so it admitted the turn. If this is no longer true the exhibit has \
         stopped exhibiting and the pair below proves nothing. verdict = {verdict:?}"
    );
}

/// ⚑ **NEW REJECTS.** The same turn, the same kernel, the same gate — with both operands crossing
/// at their full 256 bits. Refused, and the refusal NAMES the ChainHead leg (wire code 10), which
/// is what distinguishes "the head was wrong" from "some other gate happened to fire".
#[test]
fn the_full_width_head_refuses_the_fold_sibling_and_names_the_chain_head_gate() {
    if !require_lean() {
        return;
    }
    let sibling = fold_sibling(TRUE_HEAD);
    let host = WireHostCtx {
        stored_head: TRUE_HEAD,
        ..WireHostCtx::diag()
    };
    let verdict = run_gate(host, Digest::from_bytes(sibling));

    assert!(
        !verdict.committed,
        "at full width the fold sibling is a DIFFERENT head and must be refused, got {verdict:?}"
    );
    assert_eq!(
        verdict.reason,
        Some(dregg_lean_ffi::marshal::AdmissionReason::ChainHeadMismatch),
        "the refusal must be the CHAIN-HEAD gate — a refusal from any other leg would mean the \
         fixture is failing for an unrelated reason and the tooth is vacuous. got {verdict:?}"
    );
}

/// COMPLETENESS AT THE GATE — the true head, at full width, still ADMITS. Without this the
/// rejection above is satisfied by a carrier that refuses everything.
#[test]
fn the_full_width_head_still_admits_the_true_head() {
    if !require_lean() {
        return;
    }
    let host = WireHostCtx {
        stored_head: TRUE_HEAD,
        ..WireHostCtx::diag()
    };
    let verdict = run_gate(host, Digest::from_bytes(TRUE_HEAD));
    assert!(
        verdict.committed,
        "an honest full-width head must still cross the gate and commit, got {verdict:?}"
    );

    // …and genesis is unmoved: no stored head, no claimed prev, both the all-zero sentinel.
    let genesis = run_gate(WireHostCtx::diag(), Digest::default());
    assert!(
        genesis.committed,
        "the genesis sentinel (all-zero head, all-zero prev) must still admit — `prevReceiptOf` \
         maps 0 to `none` on both sides. got {genesis:?}"
    );
}

/// ⓘ **AN ADJACENT MEASUREMENT, NOT A FIX — the SAME width class, one credential arm over.**
///
/// `sig_echo_wire` narrows its `Signature` statement to 64 bits on purpose, and says why: *"the
/// kernel's `Crypto.Reference` portal compares the FULL Nats; a 256-bit statement could never equal
/// a 64-bit proof — the exact stuck-veto bug this closes."* Every OTHER credential arm still
/// presents exactly that shape. `auth_to_wire`'s bearer arm emits
/// `WireAuth::Bearer { deleg_msg: Digest, deleg_sig: u64 }`, and
/// `FullForestAuth.portalVerify (.bearer msg sig _) = CryptoKernel.verify msg sig` is `msg == sig`
/// under the reference portal — so a real delegator pubkey (256 bits) can never echo a 64-bit
/// `deleg_sig`. `Token`, `Custom`, `Stealth` and `CapTpDelivered` have the same `Digest`-vs-`u64`
/// pairing.
///
/// This test does not assert that is WRONG — the direction is fail-CLOSED, which is the safe one.
/// It exists so the claim is MEASURED rather than derived from the types, because bearer roots are
/// deliberately inside `produce_via_lean`'s covered set (`forest_agent_reaches_roots` admits them)
/// and a permanently-refusing WHO leg there is an availability fact someone should own. Reported,
/// not repaired: widening those arms is the credential-portal lane's call, not this one's.
#[test]
fn adjacent_the_bearer_who_leg_cannot_echo_a_256_bit_statement_at_64_bit_width() {
    if !require_lean() {
        return;
    }
    let host = WireHostCtx {
        stored_head: TRUE_HEAD,
        ..WireHostCtx::diag()
    };
    // A bearer credential shaped exactly as `auth_to_wire` emits one: a full-width delegator
    // commitment against a 64-bit folded signature hash.
    let verdict = run_gate_auth(
        host,
        Digest::from_bytes(TRUE_HEAD),
        WireAuth::Bearer {
            deleg_msg: Digest::from_bytes([0x9au8; 32]),
            deleg_sig: 0x0123_4567_89ab_cdef,
            stark: false,
        },
    );
    assert!(
        !verdict.committed,
        "MEASURED: the bearer WHO leg compares a 256-bit statement against a 64-bit proof, so it \
         cannot admit. If this ever commits, the portal or the carrier changed and the note above \
         is stale — reread it rather than deleting this test. verdict = {verdict:?}"
    );
    // …and it is the BODY/WHO leg that refused, not admission: every admission gate passes here
    // (same fixture as the honest pole), so the reason must be `Admitted` with a non-committed
    // status — the prologue-only shape.
    assert_eq!(
        verdict.reason,
        Some(dregg_lean_ffi::marshal::AdmissionReason::Admitted),
        "the turn must clear ADMISSION and fail at the credential leg — a refusal from an \
         admission gate would mean the fixture is wrong and this measures nothing. \
         verdict = {verdict:?}"
    );
}
