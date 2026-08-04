//! ⚑ **THE ETH/BASE SYNC-COMMITTEE LIGHT CLIENT, PROVED ON THE DEPLOYED PROVER — THE FIFTH AND
//! LAST.**
//!
//! # What had never happened, and why this one was different
//!
//! Five peer chains have a Lean-authored light-client verify AIR routed through `EmitByName.lean`
//! into `circuit/src/descriptor_by_name.rs`. As of 2026-08-03 four had been proved — Mina
//! (`turn/tests/mina_anchored_head_lands.rs`), Tendermint, Solana, Midnight. ETH was the last one
//! served by name that no prover had ever run.
//!
//! ⚑ **And unlike the other three, nothing was wrong with it.** The width census that found three
//! vacuous range tables (`tm` at 64, `solana` and `midnight` at 128 — every one of them ≥ 31 and
//! therefore containing the whole BabyBear field, `RangeFieldContainment
//! .range_vacuous_at_or_above_31`) left this descriptor UNTOUCHED. `dregg-eth-lightclient-verify::v1`
//! declares `bits: 11`, and 11 is:
//!
//!  * **inside the field** — `2^11 = 2048 < p = 2013265921`, so the interval refuses something;
//!  * **wrap-free** — `2^12 = 4096 ≤ p`, so a negative slack of any magnitude the interval can
//!    itself reach lands outside it (`RangeFieldContainment.wrap_free_iff_le_29`, of which 11 is
//!    comfortably a member);
//!  * **complete for the real domain** — the quorum slack `QDIFF = 3·PC − 1024` maxes at
//!    `3·512 − 1024 = 512` for a full sync committee, and `512 < 2048`.
//!
//! So this file was not a width repair. It is the missing measurement: the deployed prover PROVES
//! an honest finalized update and REFUSES the Nomad-class sub-quorum, on the served object — and,
//! since 2026-08-03, refuses an over-committee participation count too (below).
//!
//! # The tooth: the 342 / 341 boundary
//!
//! The sync committee is 512 keys. Altair's threshold is `2/3` of it, and the multiply-form the AIR
//! carries is `2·512 ≤ 3·pc`, i.e. `1024 ≤ 3·pc`, i.e. `pc ≥ 342` (`341.33…` rounded up). The
//! quorum slack `QDIFF = 3·pc − 1024` is range-checked into `[0, 2^11)`:
//!
//!  * `pc = 342` ⇒ `QDIFF = 2` — accepted, and it PROVES here;
//!  * `pc = 341` ⇒ `QDIFF = −1`, which in the deployed mod-`p` reading is `p − 1 = 2013265920`,
//!    nearly a million times the interval ceiling — refused, and the literal refusal text is
//!    reported below.
//!
//! The `0 < pc` floor is SUBSUMED rather than separately gated: `1024 ≤ 3·pc` already forces
//! `pc ≥ 342 > 0`, so the empty-committee case rides the same tooth (`the_empty_participation_set_
//! is_refused` measures it as its own row anyway, because "subsumed" is a claim worth checking).
//!
//! # ⚑⚑ THE RESIDUAL THIS FILE FOUND IS NOW CLOSED (2026-08-03), AND BOTH POLARITIES ARE HERE
//!
//! The first version of this harness MEASURED a hole: the AIR forced `CL = 512` and `BL = 512` and
//! the quorum slack, but **no gate related `PC` to either**, so `PC = 1023` against a 512-key
//! committee PROVED AND VERIFIED. The only bound was incidental — `3·PC − 1024 < 2^11` capping `PC`
//! at `1023`, i.e. 2× the committee. No stated theorem broke (`ethLcAir_sound` takes
//! `hpc : a PC = (pc : ℤ)` as a WITNESS RELATION, so `PC` sat inside the named boundary), which is
//! exactly why it survived: it was undone work wearing a residual's clothes.
//!
//! The closure is Lean-side, in `LightClientEthAir` — House Law #1, the AIR is Lean-authored, and
//! as of this revision it is COMPILER-authored (`EffectLower.lowerAir` of the `EffectAir` source
//! `ethHeadAir`; no hand-written `VmConstraint2` in the module). One new column `PC_SLACK`, one new
//! gate `PC_SLACK + PC = BL`, one new lookup on the SAME 11-bit table. Non-negativity of the slack
//! IS `PC ≤ BL`.
//!
//! `an_over_committee_participation_count_proved_before_the_bound_and_is_refused_after` runs BOTH
//! halves on the deployed prover: the identical row PROVES with the two new constraints removed and
//! is REFUSED with them present, `row 0: range wire 9 value 2013265410 >= 2^11`. The Lean statement
//! it cashes is `ethLcAir_forces_participation_bounded` — `342 ≤ PC ≤ BL = 512` from the trace, no
//! hypothesis about the update.
//!
//! ⚠ **AND THE SAME OMISSION IS IN THE DECISION.** `LightClientEthGate.syncDecision` does not check
//! `pc ≤ bitsLen` either, so the AIR is now strictly STRONGER than the object it refines on this
//! conjunct. Its three peers are worse off: `signed ≤ total` is forced by no gate in the Tendermint,
//! Solana or Midnight AIRs, and by no conjunct of their scalar decisions.
//!
//! # Scope, said plainly
//!
//! `BLS_OK` / `FIN_OK` / `EXEC_OK` are witnessed carrier bits, not in-AIR BLS12-381 aggregate
//! verify and SHA-256 SSZ Merkle folds; the dregg-side STARK inherits the undischarged FRI floor.
//! This is a prover running the served object. It is **not** "Ethereum-valid", and it is not
//! "machine-checked" — the machine-checked statements are the Lean ones this file names, and a
//! Rust case-test quantifies over nothing.
//!
//! ⚠ **PROFILE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]` panics under
//! `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`; RANGE refusals are `Err`
//! in both. Every refusal here goes through `dregg_circuit::refusal`.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal;

const ETH_LC_VERIFY_DESCRIPTOR: &str = "dregg-eth-lightclient-verify::v1";

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Trace column layout — pinned to `LightClientEthAir`'s Lean `def`s (§1).
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// Committee length (the sync committee's key count); structural, forced `= 512`.
const CL: usize = 0;
/// Bitfield length (the participation bitfield's bit count); structural, forced `= 512`.
const BL: usize = 1;
/// Participant popcount (`SyncAggregate::count`); bounded only through the quorum slack.
const PC: usize = 2;
/// The quorum SLACK `3·PC − 1024`; the range tooth forces it into `[0, 2^11)`.
const QDIFF: usize = 3;
/// CARRIER — the `blst` aggregate-verify result over the participating subset + signing root.
const BLS_OK: usize = 4;
/// Finality-branch depth; forced `∈ {6, 7}` (Altair..Deneb | Electra+).
const FL: usize = 5;
/// CARRIER — the SHA-256 finality-branch reconstruction compare (subtree index 41).
const FIN_OK: usize = 6;
/// Execution-branch depth; forced `= 4`.
const EL: usize = 7;
/// CARRIER — the SHA-256 execution-branch reconstruction compare (subtree index 9).
const EXEC_OK: usize = 8;
/// ⚑ The PARTICIPATION slack `BL − PC`, range-checked into `[0, 2^11)` — the column that closes the
/// unbounded-count residual this file MEASURED on 2026-08-03 and that `LightClientEthAir` now gates.
const PC_SLACK: usize = 9;
/// PUBLIC ANCHOR — the TRUSTED sync-committee root (the WS-checkpoint trust anchor).
const COMMITTEE_ROOT: usize = 10;
/// PUBLIC ANCHOR limb 0 — the finalized execution state root as nine radix-`2^31` MSB-first limbs.
const FIN_STATE_ROOT_0: usize = 11;
const FIN_STATE_ROOT_LIMBS: usize = 9;
/// PUBLIC ANCHOR — the fork/domain (genesis-validators-root-derived signing domain).
const DOMAIN_GVR: usize = 20;

const ETH_LC_WIDTH: usize = 21;
const ETH_PI_COUNT: usize = 11;

/// The declared quorum-slack width. ⚑ **UNCHANGED by the width census** — genuinely inside the
/// field, genuinely wrap-free, genuinely complete for a 512-key committee.
const Q_BITS: usize = 11;

/// Declared wire id of the shared `range` table (`TableId.range`).
const TID_RANGE: usize = 2;

/// Altair's sync-committee size (`SYNC_COMMITTEE_SIZE`).
const COMMITTEE_SIZE: u32 = 512;

/// The smallest participant count satisfying `2·512 ≤ 3·pc`. **This is the Nomad boundary.**
const MIN_QUORUM_PC: u32 = 342;

/// The smallest FULLY VACUOUS width (`2^32 > p`), the control the 11 is measured against.
const VACUOUS_BITS: usize = 32;

const TRACE_ROWS: usize = 8;

const P: i64 = 2_013_265_921;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(ETH_LC_VERIFY_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{ETH_LC_VERIFY_DESCRIPTOR} must dispatch: the Lean-emitted descriptor is routed \
             through EmitByName.lean and included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// The SAME served descriptor with the quorum table's declared width set to `bits`.
///
/// ⚑ This is the control for the quorum tooth. A tooth that only shows the CURRENT width refusing a
/// value has not shown the value would ever be admitted; this hands the identical trace to the
/// identical AIR under the identical prover, differing in exactly one integer.
fn desc_with_range_width(bits: usize) -> EffectVmDescriptor2 {
    let mut d = desc();
    let mut touched = 0usize;
    for t in d.tables.iter_mut() {
        if t.id == TID_RANGE {
            if let TableSem::Range { bits: b } = &mut t.sem {
                *b = bits;
                touched += 1;
            }
        }
    }
    assert_eq!(
        touched, 1,
        "exactly the quorum range table must be re-declared"
    );
    d
}

/// Field-encode a possibly-negative integer: in BabyBear a negative value IS `p − k`, which is the
/// element the range tooth must refuse. This is where a sub-quorum's `QDIFF` lands.
fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// One logical row of the ETH finalized-update verify decision
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy)]
struct Update {
    committee_len: u32,
    bitfield_len: u32,
    participants: u32,
    bls_ok: u32,
    finality_depth: u32,
    fin_ok: u32,
    exec_depth: u32,
    exec_ok: u32,
    committee_root: u32,
    fin_state_root: [u32; FIN_STATE_ROOT_LIMBS],
    domain: u32,
}

/// An HONEST finalized update: the quorum slack is COMPUTED from the identity its gate forces
/// (`QDIFF = 3·PC − 1024`), never claimed. A caller cannot hand this a slack; it can only hand it
/// the participant count the slack derives from.
fn honest(participants: u32) -> Update {
    Update {
        committee_len: COMMITTEE_SIZE,
        bitfield_len: COMMITTEE_SIZE,
        participants,
        bls_ok: 1,
        // 6 is Altair..Deneb; `a_deneb_and_an_electra_finality_depth_both_prove` runs 7 too.
        finality_depth: 6,
        fin_ok: 1,
        exec_depth: 4,
        exec_ok: 1,
        committee_root: 0xc0_11_ee_01,
        fin_state_root: [1, 2, 3, 4, 5, 6, 7, 8, 9],
        domain: 0x01_00_00_00,
    }
}

/// The 21 cells of one logical row, as integers — kept in `i64` so a sub-quorum's NEGATIVE slack
/// (and an over-claimed count's negative PARTICIPATION slack) survives to `felt` unaltered, which is
/// the value the tooth must refuse.
fn row_cells(u: Update) -> Vec<i64> {
    let mut r = vec![0i64; ETH_LC_WIDTH];
    r[CL] = u.committee_len as i64;
    r[BL] = u.bitfield_len as i64;
    r[PC] = u.participants as i64;
    // §2, verbatim: `QDIFF + 1024 = 3·PC`.
    r[QDIFF] = 3 * u.participants as i64 - 1024;
    // ⚑ §2 G4, verbatim: `PC_SLACK + PC = BL`. COMPUTED from the identity its gate forces, never
    // claimed — a caller cannot hand this a slack, only the count the slack derives from.
    r[PC_SLACK] = u.bitfield_len as i64 - u.participants as i64;
    r[BLS_OK] = u.bls_ok as i64;
    r[FL] = u.finality_depth as i64;
    r[FIN_OK] = u.fin_ok as i64;
    r[EL] = u.exec_depth as i64;
    r[EXEC_OK] = u.exec_ok as i64;
    r[COMMITTEE_ROOT] = u.committee_root as i64;
    for (i, l) in u.fin_state_root.iter().enumerate() {
        r[FIN_STATE_ROOT_0 + i] = *l as i64;
    }
    r[DOMAIN_GVR] = u.domain as i64;
    r
}

/// The eleven published anchors, in PI order.
fn pis_of(u: Update) -> Vec<BabyBear> {
    let mut pis = vec![BabyBear::new(0); ETH_PI_COUNT];
    pis[0] = BabyBear::new(u.committee_root);
    for (i, l) in u.fin_state_root.iter().enumerate() {
        pis[1 + i] = BabyBear::new(*l);
    }
    pis[10] = BabyBear::new(u.domain);
    pis
}

fn trace_of(cells: &[i64]) -> Vec<Vec<BabyBear>> {
    let row: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![row; TRACE_ROWS]
}

fn prove_and_verify(
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> Result<(), String> {
    let trace = trace_of(cells);
    refusal::assert_committed_shape("eth lightclient", d, &trace, pis);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(d, &trace, pis, &mem, &heaps)
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, pis).map_err(|e| format!("verifier refused: {e:?}"))
}

fn must_prove(what: &str, u: Update) {
    must_prove_under(what, &desc(), u);
}

fn must_prove_under(what: &str, d: &EffectVmDescriptor2, u: Update) {
    let cells = row_cells(u);
    let pis = pis_of(u);
    refusal::must_accept(what, || prove_and_verify(d, &cells, &pis));
}

/// A RANGE refusal — an `Err` in EVERY profile, never a panic, never debug-only.
fn must_refuse_out_of_range(
    what: &str,
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> String {
    let e: String = refusal::must_refuse(what, || prove_and_verify(d, cells, pis));
    assert!(
        e.contains("range wire"),
        "{what}: expected the RANGE tooth (`row R: range wire N value V >= 2^b`), got: {e}"
    );
    e
}

/// An ALGEBRAIC refusal — a p3 unsat panic under `cargo test`, `OodEvaluationMismatch` under
/// `--release`. The load-bearing half is the NEGATIVE clause: a tooth whose subject is a specific
/// gate must not be satisfied by the lookup bus failing instead.
fn must_refuse_violated_gate(
    what: &str,
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> String {
    let r = refusal::must_refuse_or_unsat_panic(what, || prove_and_verify(d, cells, pis));
    let reason = r.reason();
    refusal::assert_violated_constraint_not_bus(what, &reason);
    reason
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The served object — and the width that was ALREADY RIGHT
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The descriptor this tree serves is the one the Lean module declares, and its declared width
/// passes all three tests the census applied to its three siblings.
#[test]
fn the_served_descriptor_is_the_lean_emitted_one_and_its_width_is_sound() {
    let d = desc();
    assert_eq!(d.name, ETH_LC_VERIFY_DESCRIPTOR);
    assert_eq!(d.trace_width, ETH_LC_WIDTH);
    assert_eq!(d.public_input_count, ETH_PI_COUNT);
    // 9 gates + 2 slack lookups + 11 PI pins = 22 (`ethLcVerifyDesc_constraint_count`).
    assert_eq!(d.constraints.len(), 22);
    assert_eq!(d.tables.len(), 1);

    // ⚠ Read the width OUT OF THE SERVED DESCRIPTOR, not out of this file's `Q_BITS`. A constant
    // compared against its own definition is decoration; this is the emitted object measured
    // against the field it is evaluated in.
    let served_bits = match d.tables.iter().find(|t| t.id == TID_RANGE).map(|t| &t.sem) {
        Some(TableSem::Range { bits }) => *bits,
        other => panic!("the quorum table must be a range table, got {other:?}"),
    };
    assert_eq!(served_bits, Q_BITS);

    // ⚑ THE THREE TESTS THE CENSUS APPLIED. `tm` at 64, `solana`/`midnight` at 128 failed the first
    // one outright — their intervals contained the whole field.
    assert!(
        (1i64 << served_bits) < P,
        "INSIDE THE FIELD: the declared interval must not contain every element. FALSE at 64, \
         FALSE at 128 — this is the leg the three siblings failed."
    );
    assert!(
        (1i64 << (served_bits + 1)) <= P,
        "WRAP-FREE: `p − 2^bits ≥ 2^bits`, so a negative slack of any magnitude the interval can \
         itself reach lands outside it. False at 30; true with enormous margin at 11."
    );
    assert!(
        3 * COMMITTEE_SIZE as i64 - 1024 < (1i64 << served_bits),
        "COMPLETE: a FULL sync committee's slack (3·512 − 1024 = 512) must fit, or the honest \
         maximum would be refused"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE MEASUREMENT — a prover has run this descriptor
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE DELIVERABLE: AN HONEST ETH FINALIZED UPDATE PROVES AND VERIFIES ON THE DEPLOYED RUST
/// PROVER.** A comfortable supermajority — 400 of 512 signing keys — through the served,
/// Lean-emitted AIR.
#[test]
fn an_honest_finalized_update_proves_and_verifies() {
    let u = honest(400);
    assert!(2 * COMMITTEE_SIZE as u64 <= 3 * u.participants as u64);
    assert_eq!(row_cells(u)[QDIFF], 176);

    let t0 = std::time::Instant::now();
    must_prove("⚑ an honest ETH finalized update (400 of 512)", u);
    eprintln!(
        "⚑ ETH HONEST UPDATE: participants={} of {COMMITTEE_SIZE} QDIFF={} PROVED AND VERIFIED in \
         {:?} ({TRACE_ROWS} trace rows, {ETH_LC_WIDTH} base columns)",
        u.participants,
        row_cells(u)[QDIFF],
        t0.elapsed()
    );
}

/// ⚑ **THE ACCEPTING SIDE OF THE NOMAD BOUNDARY.** `pc = 342` is the SMALLEST participant count
/// satisfying `2·512 ≤ 3·pc`; its slack is `2`, the tightest accepting row there is.
#[test]
fn the_minimal_quorum_at_342_proves() {
    let u = honest(MIN_QUORUM_PC);
    assert!(2 * COMMITTEE_SIZE as u64 <= 3 * u.participants as u64);
    assert!(2 * COMMITTEE_SIZE as u64 > 3 * (u.participants - 1) as u64);
    assert_eq!(row_cells(u)[QDIFF], 2);
    must_prove("⚑ the minimal quorum, 342 of 512", u);
}

/// …and the FULL committee proves, which is the completeness end of the declared width: `pc = 512`
/// gives the largest honest slack, `512`, and `512 < 2^11 = 2048`.
#[test]
fn a_full_committee_proves() {
    let u = honest(COMMITTEE_SIZE);
    assert_eq!(row_cells(u)[QDIFF], 512);
    assert!(row_cells(u)[QDIFF] < (1 << Q_BITS));
    must_prove("a FULL 512-key sync committee", u);
}

/// Both legal finality depths prove: `6` (Altair through Deneb) and `7` (Electra onwards). The gate
/// is `(FL − 6)·(FL − 7)`, so this is the disjunction's two satisfying assignments, both run.
#[test]
fn a_deneb_and_an_electra_finality_depth_both_prove() {
    for depth in [6u32, 7u32] {
        let mut u = honest(400);
        u.finality_depth = depth;
        must_prove(&format!("an honest update at finality depth {depth}"), u);
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE TOOTH — the 341 sub-quorum, the Nomad-class boundary
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **ONE SIGNATURE BELOW THE THRESHOLD IS REFUSED.** `pc = 341` fails `2·512 ≤ 3·pc` by exactly
/// one: `3·341 = 1023 < 1024`. The slack fills to `−1`, which in the deployed mod-`p` reading is
/// `p − 1 = 2013265920` — 983 thousand times the interval ceiling — and the 11-bit tooth has no row
/// for it.
///
/// This is the boundary a light client exists to hold. The refusal's literal text is reported
/// because the NUMBER is the evidence: `2013265920` is `p − 1`, a WRAPPED NEGATIVE slack, and the
/// only reason it lands outside `[0, 2^11)` is that the declared width is wrap-free. At the 64 and
/// 128 its three siblings shipped, that same element sat comfortably INSIDE.
#[test]
fn the_341_sub_quorum_is_refused() {
    let u = honest(MIN_QUORUM_PC - 1);
    assert!(
        2 * COMMITTEE_SIZE as u64 > 3 * u.participants as u64,
        "341 of 512 is BELOW Altair's 2/3 threshold and must not finalize"
    );

    let cells = row_cells(u);
    assert_eq!(cells[QDIFF], -1, "the sub-quorum's slack is −1");
    assert_eq!(
        felt(cells[QDIFF]).as_u32() as i64,
        P - 1,
        "…which on the wire is p − 1, an element with no row in [0, 2^11)"
    );

    let e = must_refuse_out_of_range(
        "⚑ the 341-of-512 sub-quorum (the Nomad boundary)",
        &desc(),
        &cells,
        &pis_of(u),
    );
    eprintln!("⚑ ETH 341-of-512 sub-quorum refused: {e}");
    assert!(
        e.contains(&format!("range wire {QDIFF}")),
        "the QUORUM tooth is what must bite: {e}"
    );
}

/// ⚑ **THE CONTROL: THE SAME SUB-QUORUM IS ADMITTED WHEN THE WIDTH IS VACUOUS.**
///
/// One integer moves — the quorum table's declared width, 11 → 32, an interval covering the whole
/// field exactly as its three siblings' 64 and 128 did. `p − 1 = 2013265920 < 2^32` is then IN
/// range, the `QDIFF` identity gate is satisfied over `𝔽_p` (it is a ℤ identity, so it holds mod
/// `p`), and **the sub-quorum PROVES**.
///
/// That pairing is what makes the 11 a CHECK rather than a number, and it is measured on the
/// running prover rather than asserted. It is also the exact shape the other three shipped in.
#[test]
fn the_341_sub_quorum_is_admitted_when_the_width_is_vacuous() {
    assert!(
        (1u64 << VACUOUS_BITS) > P as u64,
        "the control width must actually be vacuous — its interval must cover the field"
    );
    must_prove_under(
        "⚑ the SAME 341-of-512 sub-quorum at a VACUOUS range width",
        &desc_with_range_width(VACUOUS_BITS),
        honest(MIN_QUORUM_PC - 1),
    );
    eprintln!(
        "⚑ ETH 341-of-512 sub-quorum ADMITTED at a vacuous 32-bit width — the 11-bit declaration is \
         what refuses it, and that is the leg tm/solana/midnight were missing"
    );
}

/// ⚑ **THE EMPTY PARTICIPATION SET IS REFUSED**, on the same tooth. The AIR has no separate
/// `0 < pc` gate — the module claims it is SUBSUMED by `1024 ≤ 3·pc` — so this row checks the
/// claim rather than trusting it: `pc = 0` gives `QDIFF = −1024`, i.e. `p − 1024 = 2013264897`,
/// far outside `[0, 2^11)`.
#[test]
fn the_empty_participation_set_is_refused() {
    let u = honest(0);
    let cells = row_cells(u);
    assert_eq!(cells[QDIFF], -1024);
    assert_eq!(felt(cells[QDIFF]).as_u32() as i64, P - 1024);

    let e = must_refuse_out_of_range(
        "⚑ a finalized update signed by NOBODY",
        &desc(),
        &cells,
        &pis_of(u),
    );
    eprintln!("⚑ ETH empty participation set refused: {e}");
    assert!(e.contains(&format!("range wire {QDIFF}")));
}

/// ⚑ **A FORGED SLACK IS REFUSED.** The obvious repair for the sub-quorum is to claim a slack the
/// range tooth admits while leaving `PC` at 341. That breaks the `QDIFF = 3·PC − 1024` identity
/// gate, so the refusal is a VIOLATED CONSTRAINT rather than a range complaint — the two teeth are
/// paired, and neither alone would hold the boundary.
#[test]
fn a_forged_quorum_slack_is_refused() {
    let u = honest(MIN_QUORUM_PC - 1);
    let mut forged = row_cells(u);
    forged[QDIFF] = 2; // the slack an honest `pc = 342` would have
    assert!(forged[QDIFF] >= 0 && forged[QDIFF] < (1 << Q_BITS));
    let reason = must_refuse_violated_gate(
        "⚑ a sub-quorum with the slack forged into range",
        &desc(),
        &forged,
        &pis_of(u),
    );
    eprintln!("⚑ ETH forged quorum slack: {reason}");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE CLOSED RESIDUAL — `PC ≤ BL`, ACCEPTED BEFORE / REFUSED AFTER, ON THE SAME PROVER
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The served descriptor with the PARTICIPATION-BOUND leg REMOVED — the exact shape this descriptor
/// had before 2026-08-03.
///
/// ⚑ This is the control that makes the closure a measurement rather than an assertion. Removing a
/// constraint from an AIR makes it accept STRICTLY MORE (`TableAirIR.rowHolds_of_sublist`), and no
/// byte-golden and no denotation can see the loss — so the only honest way to show the new leg BITES
/// is to hand the identical trace to the identical prover with and without it.
///
/// The two constraints removed are the `PC_SLACK + PC = BL` gate and its range lookup, at emission
/// indices 4 and 5 — pinned Lean-side by `ethLcVerifyDesc_slack_lookups` and re-derived here off the
/// SERVED bytes rather than transcribed, so a re-emission that moves them fails here loudly.
fn desc_without_participation_bound() -> EffectVmDescriptor2 {
    let mut d = desc();
    let at = d
        .constraints
        .iter()
        .position(|k| {
            matches!(k, VmConstraint2::Lookup(l)
                if l.table == TID_RANGE && l.tuple == vec![LeanExpr::Var(PC_SLACK)])
        })
        .expect("the served descriptor must carry a range lookup on PC_SLACK");
    assert_eq!(
        at, 5,
        "the participation lookup must be emission index 5 (Lean: ethLcVerifyDesc_slack_lookups)"
    );
    // The identity gate is the leg immediately before its lookup, exactly as the quorum pair is.
    d.constraints.remove(at);
    d.constraints.remove(at - 1);
    assert_eq!(
        d.constraints.len(),
        20,
        "the pre-2026-08-03 shape is 20 constraints"
    );
    d
}

/// ⚑⚑ **THE DELIVERABLE: THE UNBOUNDED PARTICIPATION COUNT PROVED, AND NOW IT DOES NOT.**
///
/// `CL` and `BL` are both forced to `512`. Before this revision `PC` was forced by NOTHING except
/// the quorum slack, so a prover could claim more participants than the committee has keys and the
/// descriptor ACCEPTED: `pc = 1023` gives `QDIFF = 2045 < 2048`, in range, every gate satisfied.
/// The only bound was incidental — the range width capping `3·PC − 1024 < 2^11`, hence `PC ≤ 1023`,
/// i.e. 2× the committee. Nothing in the AIR knew that `PC` counts bits of a 512-bit field.
///
/// This test runs BOTH halves on the deployed prover, in one place, differing in exactly two
/// constraints:
///
///  * **BEFORE** (`desc_without_participation_bound`) — `PC = 1023` PROVES AND VERIFIES.
///  * **AFTER** (the served descriptor) — the SAME row is REFUSED, on the RANGE tooth, because
///    `PC_SLACK = 512 − 1023 = −511` is the field element `p − 511 = 2013265410`, six orders of
///    magnitude above the interval ceiling (Lean: `eth_wrapped_slack_is_outside_the_range`).
///
/// The Lean statement this cashes is `ethLcAir_forces_participation_bounded`, which concludes
/// `342 ≤ PC ≤ BL = 512` from the trace with NO hypothesis about the update — the bound that was
/// previously available only through the witness relation `hpc`.
#[test]
fn an_over_committee_participation_count_proved_before_the_bound_and_is_refused_after() {
    let over = honest(1023);
    let cells = row_cells(over);
    let pis = pis_of(over);
    assert_eq!(cells[QDIFF], 2045);
    assert!(
        cells[QDIFF] < (1 << Q_BITS),
        "the QUORUM tooth does NOT catch this"
    );
    assert_eq!(cells[PC_SLACK], -511);
    assert_eq!(felt(cells[PC_SLACK]).as_u32() as i64, P - 511);
    assert!(
        over.participants > over.bitfield_len,
        "the whole point: PC exceeds the bitfield length"
    );

    // ── BEFORE: the pre-2026-08-03 AIR accepts it. The `PC_SLACK` column is present in the trace
    //    but no constraint reads it, which is precisely the state the residual described.
    must_prove_under(
        "⚑ BEFORE the bound: an over-claimed participant count (1023 of a 512-key committee)",
        &desc_without_participation_bound(),
        over,
    );
    eprintln!(
        "⚑ ETH BEFORE: PC={} against BL={} PROVED AND VERIFIED with the participation leg removed",
        over.participants, over.bitfield_len
    );

    // ── AFTER: the served descriptor refuses the identical row, on the participation tooth.
    let e = must_refuse_out_of_range(
        "⚑ AFTER the bound: the SAME over-claimed participant count",
        &desc(),
        &cells,
        &pis,
    );
    assert!(
        e.contains(&format!("range wire {PC_SLACK}")),
        "the PARTICIPATION tooth is what must bite (not the quorum one): {e}"
    );
    eprintln!("⚑ ETH AFTER: {e}");
}

/// ⚑ The bound is not a single-value coincidence: EVERY count above the bitfield length is refused,
/// and every count at or below it (down to the quorum floor) still proves. The two teeth together
/// pin `PC` to exactly `[342, 512]`, which is what a 512-key sync committee can actually produce.
#[test]
fn the_participation_bound_holds_across_the_whole_boundary() {
    let d = desc();
    for pc in [342u32, 400, 511, 512] {
        must_prove_under(&format!("⚑ an honest {pc} of 512"), &d, honest(pc));
    }
    for pc in [513u32, 600, 1023] {
        let u = honest(pc);
        let e = must_refuse_out_of_range(
            &format!("⚑ an over-committee count {pc} of 512"),
            &d,
            &row_cells(u),
            &pis_of(u),
        );
        assert!(e.contains(&format!("range wire {PC_SLACK}")));
    }
    eprintln!(
        "⚑ ETH PARTICIPATION BOUND: [342, 512] proves, 513+ refused on the PC_SLACK tooth — the \
         interval a 512-key committee can actually produce"
    );
}

/// ⚑ **THE CONTROL FOR THE NEW TOOTH.** The same over-committee row at a VACUOUS 32-bit table
/// PROVES, so the refusal above is the DECLARED WIDTH doing work and not the trace being malformed.
/// One integer moves.
#[test]
fn the_over_committee_count_is_admitted_when_the_width_is_vacuous() {
    must_prove_under(
        "⚑ the SAME 1023-of-512 over-claim at a VACUOUS range width",
        &desc_with_range_width(VACUOUS_BITS),
        honest(1023),
    );
    eprintln!(
        "⚑ ETH 1023-of-512 ADMITTED at a vacuous 32-bit width — the 11-bit declaration is what \
         refuses it"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The structural and carrier teeth
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A structural length that is not 512, or a branch depth outside its legal set, is refused by its
/// own gate. These never depended on any range table, and the test says so by running each one.
#[test]
fn a_structural_violation_is_refused() {
    for (name, col, bad) in [
        ("committee length (CL ≠ 512)", CL, 511i64),
        ("bitfield length (BL ≠ 512)", BL, 513i64),
        ("finality-branch depth (FL ∉ {6,7})", FL, 5i64),
        ("finality-branch depth (FL ∉ {6,7})", FL, 8i64),
        ("execution-branch depth (EL ≠ 4)", EL, 3i64),
    ] {
        let u = honest(400);
        let mut cells = row_cells(u);
        cells[col] = bad;
        let reason =
            must_refuse_violated_gate(&format!("{name} = {bad}"), &desc(), &cells, &pis_of(u));
        eprintln!("{name} = {bad}: {reason}");
    }
}

/// A forged CARRIER — the BLS aggregate-verify result, the finality-branch reconstruction, or the
/// execution-branch reconstruction, cleared to `0` — is refused by its own gate.
///
/// ⚠ These are witnessed bits, not in-AIR BLS12-381 and SHA-256. What the AIR enforces is that a
/// prover claiming acceptance must ASSERT all three; the crypto soundness behind them is consumed
/// one layer up, inside `ethLcAir_no_forgery`.
#[test]
fn a_cleared_crypto_carrier_is_refused() {
    for (name, col) in [
        ("BLS_OK (blst aggregate verify)", BLS_OK),
        ("FIN_OK (finality-branch SHA-256 reconstruct)", FIN_OK),
        ("EXEC_OK (execution-branch SHA-256 reconstruct)", EXEC_OK),
    ] {
        let u = honest(400);
        let mut cells = row_cells(u);
        assert_eq!(cells[col], 1, "the honest carrier is set");
        cells[col] = 0;
        let reason = must_refuse_violated_gate(
            &format!("a cleared carrier {name}"),
            &desc(),
            &cells,
            &pis_of(u),
        );
        eprintln!("cleared carrier {name}: {reason}");
    }
}

/// A forged PUBLIC ANCHOR: a finalized-state-root limb on the wire disagreeing with the published
/// PI. The nine `.piBinding` pins bind the WHOLE 256-bit EVM `state_root` — a SINGLE anchor felt
/// bound only a 31-bit PROJECTION, so two roots agreeing in 31 bits both verified. Perturbing any
/// ONE of the nine is refused, which is the observable half of that repair.
#[test]
fn a_finalized_state_root_limb_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(400);
    let d = desc();
    for i in 0..FIN_STATE_ROOT_LIMBS {
        let mut cells = row_cells(u);
        cells[FIN_STATE_ROOT_0 + i] += 1;
        let reason = must_refuse_violated_gate(
            &format!("a finalized-state-root limb {i} disagreeing with its PI pin"),
            &d,
            &cells,
            &pis_of(u),
        );
        eprintln!("forged finalized-state-root limb {i}: {reason}");
    }
}

/// The committee root and the signing domain are PI-pinned too: a proof relative to a different
/// trust anchor, or under a different fork's signing domain, must say so publicly. A trace that
/// disagrees with its own public statement does not verify.
#[test]
fn a_committee_root_or_domain_that_disagrees_with_its_public_input_is_refused() {
    for (name, col) in [
        ("trusted committee root", COMMITTEE_ROOT),
        ("signing domain (fork / gvr)", DOMAIN_GVR),
    ] {
        let u = honest(400);
        let mut cells = row_cells(u);
        cells[col] += 1;
        let reason = must_refuse_violated_gate(
            &format!("a {name} disagreeing with its PI pin"),
            &desc(),
            &cells,
            &pis_of(u),
        );
        eprintln!("forged {name}: {reason}");
    }
}
