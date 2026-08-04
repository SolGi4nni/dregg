//! # `dregg-solana-stake-table-fold::v1` on the DEPLOYED PROVER — the SAME-TALLY forgery, refused.
//!
//! ⚑ SUBSTRATE: the descriptor under test is Lean-authored and, more precisely, LEAN-COMPILED —
//! `Dregg2.Circuit.Emit.LightClientSolStakeFoldAir.solStakeFoldDesc` is `EffectLower.lowerAir`
//! applied to the `EffectAir` source `solStakeFoldAir`, and that module contains no hand-written
//! `VmConstraint2`. This file writes NO constraints. It builds traces and asks the deployed prover.
//!
//! ## The hole this closes, in the words of the descriptor that has it
//!
//! `dregg-solana-lightclient-verify::v1` PINS the active-stake denominator (`totalStakePins`,
//! 2026-08-04) and bounds its own claim in the same docblock:
//!
//! > ⚠ **Bound the claim.** This pins the DENOMINATOR, not the TABLE. … **a swap to a different
//! > validator set with the SAME total active stake is NOT refused by this.**
//!
//! `solana_lightclient_proves.rs::a_swapped_stake_table_is_arithmetically_perfect` exhibits exactly
//! that: a forged validator set that satisfies EVERY gate of the served verify descriptor.
//!
//! This rung refuses it. Both numbers the Solana light client's trust story hangs from — the stake
//! table's commitment and the `u64` denominator — are derived from the SAME exhibited rows, so a
//! table whose lamports sum identically but whose MEMBERSHIP differs clears every tally pin and
//! moves the root.
//!
//! ## The pair this file delivers
//!
//! * `the_honest_stake_table_proves_and_verifies` — the honest table, its derived root, its derived
//!   denominator.
//! * `the_same_tally_swap_is_arithmetically_perfect` — the forged table PROVES against its OWN root:
//!   every carry, every range lookup, every accumulator gate, every chip absorb is satisfied. This
//!   is the control that makes the next test mean something.
//! * ⚑ `the_same_tally_swap_is_refused_against_the_pinned_root` — the SAME forged table against the
//!   light client's PINNED anchor root, with the IDENTICAL published denominator. Refused.
//! * `a_reordered_stake_table_is_refused` — same multiset, same tally, different order.
//! * `an_extra_zero_stake_validator_is_refused` — same tally, one more member.
//!
//! ## ⚑ RUN IN RELEASE
//!
//! In a DEBUG build plonky3's own constraint check is a debug assertion, so an algebraic refusal
//! arrives as a PANIC; in RELEASE it arrives as a clean `Err(OodEvaluationMismatch)` from the
//! verifier. `dregg_circuit::refusal` discriminates both, and
//! `the_refusal_is_a_violated_gate_not_the_bus` records which one fired.
//!
//!     cargo nextest run --release -p dregg-circuit --test solana_stake_table_fold

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::refusal;

const FOLD_DESCRIPTOR: &str = "dregg-solana-stake-table-fold::v1";

// ── Column layout, mirroring `LightClientSolStakeFoldAir` §1. A drift here is caught by
//    `the_served_descriptor_matches_the_lean_shape`.
const ROOT_IN_0: usize = 0;
const VOTER_0: usize = 8;
const STAKE_0: usize = 17;
const MID_0: usize = 21;
const ROOT_OUT_0: usize = 29;
const ACC_0: usize = 37;
const CARRY_0: usize = 41;
const FOLD_WIDTH: usize = 44;

const PI_TABLE_ROOT_0: usize = 0;
const PI_TOTAL_STAKE_0: usize = 8;
const FOLD_PI_COUNT: usize = 12;

/// `LightClientSolStakeFoldAir.FOLD_TAG` — ASCII `SSTF`, lane 0 of the pinned initial state.
const FOLD_TAG: u32 = 0x5353_5446;

/// The committed trace must be a power of two. Six of the eight rows are the canonical ZERO ENTRY,
/// which is how a table shorter than the height is padded: a zero row adds nothing to the tally and
/// is part of what the anchor root commits to.
const TRACE_ROWS: usize = 8;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(FOLD_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{FOLD_DESCRIPTOR} is not in the by-name registry — it is emitted from \
             Dregg2/Circuit/Emit/LightClientSolStakeFoldAir.lean through EmitByName.lean and \
             included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// One stake-table entry: a 32-byte vote pubkey as nine radix-`2^29` lanes, and a `u64` of lamports.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Entry {
    voter: [u32; 9],
    stake: u64,
}

/// The canonical padding entry.
const ZERO_ENTRY: Entry = Entry {
    voter: [0; 9],
    stake: 0,
};

/// Validator A. (Any canonical nonet does: the fold binds the ROWS, not what they mean on Solana.)
const PK_A: [u32; 9] = [11, 22, 33, 44, 55, 66, 77, 88, 99];
/// Validator B — the 40%-stake member that wants to be the 60%-stake member.
const PK_B: [u32; 9] = [111, 222, 333, 444, 555, 666, 777, 888, 999];
/// A third member, for the "one more validator at the same tally" case.
const PK_C: [u32; 9] = [7, 7, 7, 7, 7, 7, 7, 7, 7];

fn limbs4(v: u64) -> [u32; 4] {
    [
        (v & 0xFFFF) as u32,
        ((v >> 16) & 0xFFFF) as u32,
        ((v >> 32) & 0xFFFF) as u32,
        ((v >> 48) & 0xFFFF) as u32,
    ]
}

fn f(v: u32) -> BabyBear {
    BabyBear::new(v)
}

/// The fold's pinned initial state: `[SSTF, 0, 0, 0, 0, 0, 0, 0]`.
fn init_state() -> [BabyBear; 8] {
    let mut st = [BabyBear::new(0); 8];
    st[0] = f(FOLD_TAG);
    st
}

/// ⚑ THE PRODUCER. One row per entry; two arity-16 absorbs of the SAME `state8 ‖ block8` shape, a
/// four-limb `u64` accumulator with boolean carries. Returns the trace and the DERIVED
/// `(table_root, total_stake_limbs)` this table commits to.
fn fold(entries: &[Entry]) -> (Vec<Vec<BabyBear>>, [BabyBear; 8], [u32; 4]) {
    assert!(entries.len() <= TRACE_ROWS);
    let mut st = init_state();
    let mut acc = [0u32; 4];
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(TRACE_ROWS);

    for r in 0..TRACE_ROWS {
        let e = entries.get(r).copied().unwrap_or(ZERO_ENTRY);
        let stk = limbs4(e.stake);

        // Block A: the running state and the eight LOW pubkey lanes.
        let mut ins_a = [BabyBear::new(0); 16];
        ins_a[..8].copy_from_slice(&st);
        for j in 0..8 {
            ins_a[8 + j] = f(e.voter[j]);
        }
        let mid = chip_absorb_all_lanes(16, &ins_a);

        // Block B: the intermediate state, the top pubkey lane, the four stake limbs, three zeros.
        let mut ins_b = [BabyBear::new(0); 16];
        ins_b[..8].copy_from_slice(&mid);
        ins_b[8] = f(e.voter[8]);
        for i in 0..4 {
            ins_b[9 + i] = f(stk[i]);
        }
        let root_out = chip_absorb_all_lanes(16, &ins_b);

        // The u64 limb addition, with the three boolean carries the AIR pins.
        let mut new_acc = [0u32; 4];
        let mut carry = 0u32;
        let mut carries = [0u32; 3];
        for i in 0..4 {
            let s = acc[i] + stk[i] + carry;
            new_acc[i] = s & 0xFFFF;
            carry = s >> 16;
            if i < 3 {
                carries[i] = carry;
            }
        }
        assert_eq!(
            carry, 0,
            "the running total overflowed a u64 — no honest fill exists"
        );

        let mut row = vec![BabyBear::new(0); FOLD_WIDTH];
        for j in 0..8 {
            row[ROOT_IN_0 + j] = st[j];
            row[MID_0 + j] = mid[j];
            row[ROOT_OUT_0 + j] = root_out[j];
        }
        for j in 0..9 {
            row[VOTER_0 + j] = f(e.voter[j]);
        }
        for i in 0..4 {
            row[STAKE_0 + i] = f(stk[i]);
            row[ACC_0 + i] = f(new_acc[i]);
        }
        for i in 0..3 {
            row[CARRY_0 + i] = f(carries[i]);
        }
        rows.push(row);

        st = root_out;
        acc = new_acc;
    }

    (rows, st, acc)
}

/// The twelve public inputs: eight root lanes, four denominator limbs.
fn pis_of(root: [BabyBear; 8], total: [u32; 4]) -> Vec<BabyBear> {
    let mut pis = vec![BabyBear::new(0); FOLD_PI_COUNT];
    for j in 0..8 {
        pis[PI_TABLE_ROOT_0 + j] = root[j];
    }
    for i in 0..4 {
        pis[PI_TOTAL_STAKE_0 + i] = f(total[i]);
    }
    pis
}

/// PROVE and VERIFY, both legs, exactly as a deployed consumer would.
fn prove_and_verify(
    d: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    refusal::assert_committed_shape("solana stake-table fold", d, trace, pis);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(d, trace, pis, &mem, &heaps)
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, pis).map_err(|e| format!("verifier refused: {e:?}"))
}

/// The honest table: A holds 60 lamports, B holds 40. Total 100.
fn honest_table() -> Vec<Entry> {
    vec![
        Entry {
            voter: PK_A,
            stake: 60,
        },
        Entry {
            voter: PK_B,
            stake: 40,
        },
    ]
}

/// ⚑ THE FORGERY: the SAME two validators, the SAME 100 lamports, the shares SWAPPED. B — a
/// minority holder under the honest table — now claims the majority share.
fn same_tally_swap() -> Vec<Entry> {
    vec![
        Entry {
            voter: PK_A,
            stake: 40,
        },
        Entry {
            voter: PK_B,
            stake: 60,
        },
    ]
}

// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn the_served_descriptor_matches_the_lean_shape() {
    let d = desc();
    assert_eq!(d.name, FOLD_DESCRIPTOR);
    // `solStakeFoldDesc_width` / `_piCount` / `_constraint_count` / `_tables`, in Lean.
    assert_eq!(
        d.trace_width, FOLD_WIDTH,
        "trace width drifted from the Lean emission"
    );
    assert_eq!(d.public_input_count, FOLD_PI_COUNT, "PI count drifted");
    assert_eq!(
        d.constraints.len(),
        58,
        "constraint count drifted (solStakeFoldDesc_constraint_count)"
    );
    assert_eq!(
        d.tables.len(),
        3,
        "declared tables drifted: range_w29 + range_w24 + range_w16"
    );
    assert!(
        d.hash_sites.is_empty(),
        "v2 descriptors carry no v1 hash sites; the hashing is chip LOOKUPS"
    );
}

/// The honest pole. An honest pole that fails makes every paired refusal vacuous, so it is asserted
/// rather than assumed.
#[test]
fn the_honest_stake_table_proves_and_verifies() {
    let d = desc();
    let (trace, root, total) = fold(&honest_table());
    let pis = pis_of(root, total);
    assert_eq!(
        total,
        limbs4(100),
        "the derived denominator is 100 lamports"
    );
    refusal::must_accept("honest stake table", || prove_and_verify(&d, &trace, &pis));
}

/// ⚑ **THE TALLIES ARE IDENTICAL AND THE ROOTS ARE NOT.** This is the measurement the whole rung
/// exists for, made before any prover runs: the forged table's accumulator lands on the same four
/// felts, and its eight-lane commitment does not.
#[test]
fn the_swap_preserves_the_tally_and_moves_the_root() {
    let (_, honest_root, honest_total) = fold(&honest_table());
    let (_, forged_root, forged_total) = fold(&same_tally_swap());
    assert_eq!(
        honest_total, forged_total,
        "the swap must preserve the denominator — otherwise `totalStakePins` already refuses it \
         and this rung proves nothing new"
    );
    assert_ne!(
        honest_root, forged_root,
        "the eight-lane Poseidon2 commitment must move; if it did not, the fold would be blind to \
         exactly the forgery it exists to catch"
    );
}

/// ⚑ **THE CONTROL.** The forged table PROVES against its OWN root: every range lookup, every
/// boolean carry, every accumulator gate and both chip absorbs are satisfied on every row. The
/// forgery is not caught by arithmetic — it is caught by the anchor, and this is what makes the next
/// test mean something. (`a_swapped_stake_table_is_arithmetically_perfect`'s analog, one rung down.)
#[test]
fn the_same_tally_swap_is_arithmetically_perfect() {
    let d = desc();
    let (trace, root, total) = fold(&same_tally_swap());
    let pis = pis_of(root, total);
    refusal::must_accept("same-tally swap against its own root", || {
        prove_and_verify(&d, &trace, &pis)
    });
}

/// ⚑⚑ **THE DELIVERABLE. A SWAPPED VALIDATOR SET WITH THE SAME TALLY IS REFUSED.**
///
/// The light client supplies its governance-pinned anchor root in `PI[0..8]` and the denominator it
/// believes in `PI[8..12]`. The forger's table clears the denominator — the four felts are
/// bit-identical — and the LAST-row root pins do not vanish.
///
/// This is the exact forgery `LightClientSolanaAir.totalStakePins` names as outside its scope.
#[test]
fn the_same_tally_swap_is_refused_against_the_pinned_root() {
    let d = desc();
    let (honest_trace, honest_root, honest_total) = fold(&honest_table());
    let (forged_trace, _forged_root, forged_total) = fold(&same_tally_swap());

    // The light client's PINNED public statement — the honest table's root, the honest denominator.
    let pinned = pis_of(honest_root, honest_total);
    assert_eq!(
        forged_total, honest_total,
        "the published denominator is the same object in both proofs"
    );
    assert_ne!(
        honest_trace, forged_trace,
        "the two traces must differ, or there is nothing to refuse"
    );

    let r =
        refusal::must_refuse_or_unsat_panic("same-tally swap vs the pinned anchor root", || {
            prove_and_verify(&d, &forged_trace, &pinned)
        });
    refusal::assert_violated_constraint_not_bus(
        "same-tally swap vs the pinned anchor root",
        &r.reason(),
    );
}

/// A REORDERING: the same two members, the same lamports each, listed the other way round. Same
/// multiset, same tally — and the fold is order-sensitive by construction, so the root moves.
#[test]
fn a_reordered_stake_table_is_refused() {
    let d = desc();
    let (_, honest_root, honest_total) = fold(&honest_table());
    let mut reordered = honest_table();
    reordered.reverse();
    let (trace, _, total) = fold(&reordered);
    assert_eq!(total, honest_total, "a reorder preserves the tally");

    let pinned = pis_of(honest_root, honest_total);
    let r = refusal::must_refuse_or_unsat_panic("reordered stake table", || {
        prove_and_verify(&d, &trace, &pinned)
    });
    refusal::assert_violated_constraint_not_bus("reordered stake table", &r.reason());
}

/// ⚑ AN EXTRA MEMBER AT ZERO STAKE. The tally is untouched — the padding rows this table displaces
/// are themselves zero entries — and the root still moves, because the message frame moved. This is
/// the case a tally-only pin is structurally blind to.
#[test]
fn an_extra_zero_stake_validator_is_refused() {
    let d = desc();
    let (_, honest_root, honest_total) = fold(&honest_table());
    let mut padded = honest_table();
    padded.push(Entry {
        voter: PK_C,
        stake: 0,
    });
    let (trace, _, total) = fold(&padded);
    assert_eq!(
        total, honest_total,
        "a zero-stake member preserves the tally"
    );

    let pinned = pis_of(honest_root, honest_total);
    let r = refusal::must_refuse_or_unsat_panic("extra zero-stake validator", || {
        prove_and_verify(&d, &trace, &pinned)
    });
    refusal::assert_violated_constraint_not_bus("extra zero-stake validator", &r.reason());
}

/// A FORGED CHIP DIGEST: keep the honest table, but write a different value into a site's `out0` —
/// the ONE output column the producer owns. The chip table is served by the genuine permutation, so
/// the lookup names no serving row and the proof dies on the bus.
#[test]
fn a_forged_chip_digest_is_refused() {
    let d = desc();
    let (mut trace, root, total) = fold(&honest_table());
    let pis = pis_of(root, total);
    trace[0][MID_0] += BabyBear::new(1);
    refusal::must_refuse_or_unsat_panic("forged chip digest (out0)", || {
        prove_and_verify(&d, &trace, &pis)
    });
}

/// ⚑ **MEASURED, NOT ASSUMED: OUTPUT LANES 1..7 ARE WELD-OWNED, SO TAMPERING THEM IS CORRECTED
/// RATHER THAN REFUSED.**
///
/// This test was first written as "bump `MID` lane 3 and expect a refusal" and it FAILED — the
/// forgery was ACCEPTED. The reason is not a hole, and writing it down is cheaper than someone
/// rediscovering it: `descriptor_ir2::fill_chip_lanes` requires a chip lookup's lane slots
/// (tuple indices `CHIP_RATE + 2 + j`, i.e. output lanes 1..7) to be bare `Var` columns and
/// **writes the genuine permutation lanes into them** before proving. `out0` (tuple index
/// `CHIP_RATE + 1`) is explicitly NOT in that set — *"the producer's hash chain owns it"*.
///
/// So a producer has exactly ONE forgeable output column per site, `out0`, and
/// `a_forged_chip_digest_is_refused` is the tooth for it. A tamper on lanes 1..7 is overwritten, and
/// the proof that results is a proof about the CORRECTED trace — which is why this test asserts
/// ACCEPTANCE and asserts that the trace was rewritten under it.
///
/// ⚠ The consequence that matters for this descriptor: `ROOT_OUT` lanes 1..7 are weld-owned, so the
/// LAST-row PI pins on them compare the GENUINE lanes against the light client's anchor. That is
/// what makes `the_same_tally_swap_is_refused_against_the_pinned_root` a refusal of the FOLD and not
/// of a number the prover happened to write.
#[test]
fn chip_output_lanes_1_to_7_are_weld_owned_not_producer_owned() {
    let d = desc();
    let (honest_trace, root, total) = fold(&honest_table());
    let pis = pis_of(root, total);

    let mut tampered = honest_trace.clone();
    tampered[0][MID_0 + 3] += BabyBear::new(1);
    assert_ne!(
        tampered[0][MID_0 + 3],
        honest_trace[0][MID_0 + 3],
        "the tamper must actually change the submitted cell"
    );

    // ACCEPTED — the weld rewrote the cell before any constraint saw it.
    refusal::must_accept("tampered chip lane 3 (weld-owned)", || {
        prove_and_verify(&d, &tampered, &pis)
    });

    // …and the same tamper on `out0`, the producer-owned column, is refused. Both poles, so the
    // acceptance above reads as "this column is not the producer's" and not as "the chip is blind".
    let mut out0_tampered = honest_trace.clone();
    out0_tampered[0][MID_0] += BabyBear::new(1);
    refusal::must_refuse_or_unsat_panic("tampered chip out0 (producer-owned)", || {
        prove_and_verify(&d, &out0_tampered, &pis)
    });
}

/// A FORGED CARRY: flip one accumulator carry to a non-boolean value. The `.all`-scoped boolean pin
/// fires on EVERY row including the last, which is exactly where a padded trace would hide it.
#[test]
fn a_non_boolean_carry_is_refused() {
    let d = desc();
    let (mut trace, root, total) = fold(&honest_table());
    let pis = pis_of(root, total);
    trace[TRACE_ROWS - 1][CARRY_0] = BabyBear::new(2);
    refusal::must_refuse_or_unsat_panic("non-boolean carry on the last row", || {
        prove_and_verify(&d, &trace, &pis)
    });
}

/// ⚑ THE PROFILE RECORD. Under `--release` an algebraic refusal is the deployed VERIFIER's
/// `OodEvaluationMismatch`; under `cargo test` it is p3's debug constraint check panicking. Both are
/// refusals and both are meaningful, but only the first is the one a deployed light client sees.
#[test]
fn the_refusal_is_a_violated_gate_not_the_bus() {
    let d = desc();
    let (_, honest_root, honest_total) = fold(&honest_table());
    let (forged_trace, _, _) = fold(&same_tally_swap());
    let pinned = pis_of(honest_root, honest_total);
    let r = refusal::must_refuse_or_unsat_panic("release-profile record", || {
        prove_and_verify(&d, &forged_trace, &pinned)
    });
    let reason = r.reason();
    refusal::assert_violated_constraint_not_bus("release-profile record", &reason);
    if cfg!(debug_assertions) {
        eprintln!("debug profile: refusal arrived as {reason}");
    } else {
        assert!(
            reason.contains("OodEvaluationMismatch"),
            "in RELEASE the refusal must be the deployed verifier's, got: {reason}"
        );
    }
}
