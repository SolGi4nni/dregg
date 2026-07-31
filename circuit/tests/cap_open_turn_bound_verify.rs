//! # THE TURN-IDENTITY WELD (#225) — the LEDGERLESS LIGHT CLIENT'S forcing tooth.
//!
//! The Lean keystone `Dregg2.Circuit.Emit.CapOpenTurnPins.effCapOpenV3TB` (descriptor
//! `transferCapOpenTBVmDescriptor2R24`) is the LIVE transfer cap-open plus ONE appended
//! `.piBinding .first` gate welding the cap-open `src` column to a NEW public-input slot
//! (`src -> PI[46]`). It adds NO column: `src` is the column `targetBindGate` already pins to the
//! opened leaf's `target`, and the depth-16 membership open chains that leaf to the committed cap
//! root. The verifier ANCHORS that PI to the TRUSTED turn it holds (`anchor_cap_open_turn_pins`,
//! the deployment realization of the named `TurnIdentityAnchored` predicate), exactly as the
//! record-pin family anchors `dpis[46]` from the trusted post-cell.
//!
//! THE FORCING (the light-client-relevant tooth): a ledgerless light client, holding only the
//! trusted turn, can conclude the published turn's `src` MATCHES the proven transition. This test
//! realizes that END-TO-END in Rust:
//!
//!   * an HONEST transfer TB cap-open proof verifies when the verifier anchors the turn-identity PI
//!     to the SAME `src` the prover published;
//!   * a proof whose published `src` does NOT match the trusted turn is REJECTED by
//!     `verify_vm_descriptor2` ALONE (the verifier overrides the PI from the trusted turn; the
//!     appended `.piBinding` gate then disagrees with the proof's bound column -> UNSAT).
//!
//! This is `CapOpenTurnPins.effCapOpenV3TB_rejects_mismatched_src` made good on the deployed prover +
//! verifier: the gate is LOAD-BEARING for a ledgerless client.
//!
//! ## FLAG DAY 2026-07-31 — and the two teeth this file used to carry were NOT teeth
//!
//! Until the re-emit, the member declared `public_input_count 49` and this file asserted three
//! forcing teeth: a forged published `src`, `actor` or `dst` is rejected by the verifier alone.
//! Only the `src` one meant anything. `actor` and `dst` were welded to two columns
//! `CapOpenTurnPins` itself introduced and NO other constraint in the member read — so the prover
//! chose the column and the published felt together, the pin held by construction, and the
//! "rejection" this file measured was only the rejection of a forger who moved the PI and forgot to
//! move its column. A prover who moves both is accepted, publishing any actor it likes. That is the
//! shape `UnforcedPiPins.unforcedPins` censuses and `unforced_pin_row_admits_any_value` proves a
//! no-op; the two pins are gone at the Lean source and the member now carries
//! `public_input_count 47`.
//!
//! The teeth are therefore REPLACED, not renumbered: `src` keeps its end-to-end forcing test, and a
//! new assertion reads the committed bytes and requires that NOTHING else is pinned in the
//! turn-identity window. The successor that publishes `actor`/`dst` and can also FORCE them (they
//! become `turnIn` of the Lamport turn-digest lookup whose output the signed message recomposes) is
//! Lean `Dregg2/Circuit/Emit/TurnAuthCapOpenWeld.lean`, staged.
//!
//! LAW #1: this test fills COLUMNS only; every constraint is the Lean-declared chip lookup / base gate
//! / pi_binding the IR-v2 interpreter realizes generically. No hand-authored Rust constraint semantics.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover cap_open_turn_bound -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::VmConstraint2;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_TB_PI_COUNT, CAP_OPEN_TB_PI_SRC, CAP_OPEN_TB_WIDTH, CapOpenWitness, FACET_MASK_HI,
    RotatedBlockWitness, SIGNATURE_AUTH_TAG, WRITE_MASK_LO, anchor_cap_open_turn_pins,
    avail_pad_for_descriptor_name, cap_open_tb_dpis, generate_rotated_effect_vm_trace_avail,
    transfer_caveat_manifest, widen_to_cap_open_tb_avail,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_turn::rotation_witness as rw;

/// The LIVE turn-bound transfer cap-open descriptor (the #225 weld).
const CAP_OPEN_TB_KEY: &str = "transferCapOpenTBVmDescriptor2R24";

fn reg_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Build a proven rotated TRANSFER base trace + 46 PIs (a debit transfer — `direction = 1`), the live
/// rotated cohort path the deployed transfer cap-open widens. NO attenuate phase-B patch (transfer is
/// directly valid), the two-domain transfer caveat manifest (matching the live route).
///
/// `avail_pad` is the AVAILABILITY-WELD face the TARGET DESCRIPTOR was emitted at, derived by the
/// caller from the committed member's own name — the committed TB member is the hardened
/// `…-transfer-v1-avail-…` one, so a `0` here would lay the BARE v1 face and every appendix base
/// (cap-open columns, turn-identity columns, the pinned last-row reads) would sit `pad` columns
/// below where the descriptor's gates read them.
fn build_transfer_base(avail_pad: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount: 1_000,
        direction: 1,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    // A debit transfer ticks the nonce and debits the balance on the after-cell.
    let after_cell = producer_cell(before_balance - 1_000, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let caveat = transfer_caveat_manifest();
    let (trace, pis) = generate_rotated_effect_vm_trace_avail(
        avail_pad,
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated Transfer base trace must generate");
    (trace, pis)
}

/// The cap-membership witness: a transfer-conferring leaf (genuine two-axis facet × tier — `mask_lo ==
/// EFFECT_TRANSFER`, `mask_hi == 0`, `auth_tag == Signature`) whose `target` IS the turn's `src` felt.
const SRC_FELT: u32 = 7_777;

fn cap_open_witness() -> CapOpenWitness {
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),            // slot_hash
        BabyBear::new(SRC_FELT),           // target (== src)
        BabyBear::new(SIGNATURE_AUTH_TAG), // auth_tag (== 1, Signature tier)
        BabyBear::new(WRITE_MASK_LO),      // mask_lo (== EFFECT_TRANSFER = 2)
        BabyBear::new(FACET_MASK_HI),      // mask_hi (== 0)
        BabyBear::new(0x00FF_FFFF),        // expiry
        BabyBear::new(42),                 // breadstuff
    ];
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(123),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds")
}

/// **THE DEPLOYMENT FORCING TEST (#225).** An honest transfer TB cap-open proof verifies under the
/// trusted-turn anchor; a proof whose published `src` disagrees with the trusted turn is REJECTED by
/// `verify_vm_descriptor2` ALONE (the verifier override realizes `TurnIdentityAnchored`). And the
/// committed member pins NOTHING ELSE in the turn-identity window — see the file header for the two
/// pins that lived there and refused nothing.
#[test]
fn cap_open_turn_bound_verifier_forces_published_identity() {
    let desc =
        parse_vm_descriptor2(reg_json(CAP_OPEN_TB_KEY)).expect("TB cap-open descriptor parses");
    // THE FACE, DERIVED FROM THE COMMITTED MEMBER'S OWN NAME. The deployed TB member is the
    // AVAILABILITY-HARDENED transfer face (`…-transfer-v1-avail-…-capopen-eff-tb`), so its width is
    // the bare turn-bound cap-open host PLUS that pad, and every column below rides the same shift.
    // Pinning the bare `CAP_OPEN_TB_WIDTH` here (and laying the bare face) was the avail-shift trap:
    // the honest prover cannot produce the committed member's row at all.
    let pad = avail_pad_for_descriptor_name(&desc.name);
    if desc.name.contains("-v1-avail") {
        assert!(
            pad > 0,
            "the hardened TB member must derive a NONZERO availability pad from its own name"
        );
    }
    assert_eq!(
        desc.trace_width,
        CAP_OPEN_TB_WIDTH + pad,
        "TB width = the bare turn-bound cap-open host + this member's own availability pad"
    );
    assert_eq!(
        desc.public_input_count, CAP_OPEN_TB_PI_COUNT,
        "TB carries {CAP_OPEN_TB_PI_COUNT} PIs (46 rotated + the ONE turn-identity `src`) \
         regardless of the pad — the pad shifts COLUMNS, never PI indices"
    );

    // ⚑ THE WITHDRAWAL, READ OFF THE COMMITTED BYTES. Exactly one `pi_binding` lands at or past the
    // rotated 46, it is at `CAP_OPEN_TB_PI_SRC`, and its column is one the member reads elsewhere.
    // That last clause is the whole difference between a binding and a publication, so it is
    // asserted, not assumed: `actor`/`dst` failed exactly it.
    {
        let tail: Vec<(usize, usize)> = desc
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
                    if *pi_index >= CAP_OPEN_TB_PI_SRC =>
                {
                    Some((*pi_index, *col))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            tail.len(),
            1,
            "the TB weld appends EXACTLY ONE pin past the rotated 46; found {tail:?}. Two more sat \
             at PI 47/48 until 2026-07-31 publishing prover-chosen `actor`/`dst` felts."
        );
        let (pi, col) = tail[0];
        assert_eq!(
            pi, CAP_OPEN_TB_PI_SRC,
            "…and it is the turn-identity `src` slot"
        );
        // ⚠ `window_gate`, NOT `gate`. The 2026-07-30 last-row hardening flag day (`81ee5492d`)
        // lowered EVERY row-local `.base (.gate …)` as a whole-domain
        // `windowGate { on_transition: false }` over `WindowExpr::loc` — 6923 of them, registry
        // wide — so a reader that only looks at `Gate` now sees zero gates and concludes every
        // column is unread. That is precisely how `bare_floor_refuse_weld` went red one commit
        // before the nine-lane epoch and was mistaken for flag-day noise. This reader was written
        // with the same blind spot and caught by its own assertion; both arms are here now.
        let read_elsewhere = desc.constraints.iter().any(|c| match c {
            VmConstraint2::Base(VmConstraint::Gate(b))
            | VmConstraint2::Base(VmConstraint::Boundary { body: b, .. }) => expr_reads(b, col),
            VmConstraint2::Lookup(l) => l.tuple.iter().any(|e| expr_reads(e, col)),
            VmConstraint2::WindowGate(w) => window_reads(&w.body, col),
            _ => false,
        });
        assert!(
            read_elsewhere,
            "the pinned `src` column {col} must be READ by some non-pin constraint of the member \
             (`targetBindGate` pins `leaf.target == src`, and the depth-16 open chains that leaf to \
             the committed cap root). A pin on a column nothing else reads is `local[c] == pi[k]` \
             with the prover choosing both sides — it publishes, it does not bind."
        );
        eprintln!(
            "TURN-IDENTITY WINDOW: one pin, PI {pi} -> col {col}, and col {col} IS read elsewhere."
        );
    }

    // The TRUSTED turn the light client holds. `src` IS the cap-leaf target the targetBind roots.
    let trusted_src = BabyBear::new(SRC_FELT);

    // The HONEST prover: build the transfer base, widen with the TB cap-open, publish the 47-PI
    // vector with the prover's OWN (honest) source.
    let (mut trace, base_pis) = build_transfer_base(pad);
    let w = cap_open_witness();
    widen_to_cap_open_tb_avail(&mut trace, &w, pad).expect("TB widen");
    let honest_pis = cap_open_tb_dpis(&base_pis, trusted_src);
    assert_eq!(honest_pis.len(), CAP_OPEN_TB_PI_COUNT);
    assert_eq!(
        trace[0].len(),
        desc.trace_width,
        "the widened row must equal the committed member's width — a shortfall of exactly the pad \
         means the bare v1 face was laid for the AVAIL-hardened committed member"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &honest_pis, &mem_boundary, &map_heaps)
        .expect("honest transfer TB cap-open proves (and self-verifies)");

    // (A) THE VERIFIER ANCHOR — ACCEPT. The light client recomputes the turn-identity PI from the
    //     TRUSTED turn it holds and verifies. It matches the honest proof → ACCEPT.
    let mut anchored_pis = honest_pis.clone();
    anchor_cap_open_turn_pins(&mut anchored_pis, trusted_src);
    verify_vm_descriptor2(&desc, &proof, &anchored_pis)
        .expect("honest TB cap-open verifies under the trusted-turn anchor");
    eprintln!(
        "TURN-IDENTITY ANCHOR ACCEPT: honest transfer TB cap-open verified; the verifier recomputed \
         the src PI (46) from the trusted turn and it MATCHES the proven transition."
    );

    // (B) THE NEGATIVE TOOTH — a FORGED published SRC is rejected by the VERIFIER ALONE. The trusted
    //     turn's src is `trusted_src`; the verifier anchors PI[46] to it. The proof was bound to the
    //     honest src column (== trusted_src). We now anchor PI[46] to a DIFFERENT (forged) src the
    //     trusted turn does NOT carry → the first-row src pin disagrees with the bound column → UNSAT.
    //
    //     This tooth is REAL where the deleted actor/dst ones were not, and the reason is the
    //     assertion above: a prover cannot escape by moving the column to match, because the column
    //     is `targetBindGate`'s and moving it breaks the depth-16 membership open.
    {
        let mut forged = honest_pis.clone();
        let forged_src = BabyBear::new(SRC_FELT + 1);
        anchor_cap_open_turn_pins(&mut forged, forged_src);
        assert_ne!(forged[CAP_OPEN_TB_PI_SRC], honest_pis[CAP_OPEN_TB_PI_SRC]);
        let rejected = verify_vm_descriptor2(&desc, &proof, &forged).is_err();
        assert!(
            rejected,
            "a published src that does NOT match the trusted turn MUST be rejected by the verifier alone"
        );
    }

    eprintln!(
        "TURN-IDENTITY NEGATIVE TOOTH GREEN: a forged published src (one the trusted turn does NOT \
         carry) is REJECTED by verify_vm_descriptor2 alone — the #225 gate is load-bearing for a \
         ledgerless light client."
    );
}

/// Does `e` read trace column `col`? (The census's `expr_cols`, specialised to one column.)
fn expr_reads(e: &dregg_circuit::lean_descriptor_air::LeanExpr, col: usize) -> bool {
    use dregg_circuit::lean_descriptor_air::LeanExpr;
    match e {
        LeanExpr::Var(v) => *v == col,
        LeanExpr::Const(_) => false,
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => expr_reads(a, col) || expr_reads(b, col),
    }
}

/// The `WindowExpr` twin — the shape every row-local gate is emitted as since the last-row
/// hardening flag day. A reader that omits this arm sees an empty descriptor.
fn window_reads(e: &dregg_circuit::descriptor_ir2::WindowExpr, col: usize) -> bool {
    use dregg_circuit::descriptor_ir2::WindowExpr;
    match e {
        WindowExpr::Loc(c) | WindowExpr::Nxt(c) => *c == col,
        WindowExpr::Const(_) => false,
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
            window_reads(a, col) || window_reads(b, col)
        }
    }
}
