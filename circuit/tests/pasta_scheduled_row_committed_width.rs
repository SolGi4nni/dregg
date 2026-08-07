//! # The SCHEDULED Pasta RCB row, priced on the EMITTED BYTES.
//!
//! ## ⚑ What this measures and why it is not a restatement
//!
//! `PastaCurveScheduled.the_scheduled_row_commits_1499` computes the committed width in **Lean**,
//! over the Lean `EffectAir`, through `AirColumnAlloc.decompCols` — a transcription of
//! `descriptor_ir2.rs`'s `decomp_cols`. This test computes it in **Rust**, over the **emitted
//! JSON**, through the deployed `decomp_cols_pub` itself. Two independent routes to the same
//! number: a transcription slip in either one is a red here.
//!
//! ⚠ **`trace_width` is the WRONG denominator and this test exists to say so with numbers.**
//! `MainLayout::build` (`circuit/src/descriptor_ir2.rs:2008`, cursor at `:2038`) allocates a nibble
//! aux block per declared range lookup on top of `desc.trace_width`, and `Ir2Air::Main` is
//! `width()`d at the sum (`:3758-3762`). The wrap cost is `Q · W` in that sum, so a declared-width
//! ratio over-promises.
//!
//! ## ⚑ The two objects
//!
//! | row | declared | committed | aux | range lookups |
//! |---|---|---|---|---|
//! | one-row (`pasta-pallas-complete-add-sound`, DEPLOYED, routed by name) | 3 048 | 10 756 | 7 708 | 3 048 |
//! | scheduled (`pasta-pallas-complete-add-scheduled`, MEASUREMENT ONLY) | 481 | 1 499 | 1 018 | 447 |
//!
//! ⚑ **The aux block is the bigger half of the win: 7 708 → 1 018, against 2 567 declared columns
//! recovered.** One op per row is what turns 3 048 per-op range lookups into 447 per-POOL ones;
//! register allocation alone does not touch the aux block at all. That is the sentence the
//! `LIMB_BITS`-vs-schedule accounting turns on.
//!
//! ## ⚠ The scheduled row is NOT routed by name
//!
//! Its JSON lives in `tests/fixtures/`, not `descriptors/by-name/`. No `byNameDescriptors` row, no
//! `PROVENANCE.json` stamp, no VK rotation, nothing re-emits. Routing it is a separate deliberate
//! act. Re-emit the fixtures with:
//!
//! ```text
//! cd metatheory
//! lake env lean --run EmitPastaCurveScheduled.lean pallas \
//!   > ../circuit/tests/fixtures/pasta-pallas-complete-add-scheduled.json
//! lake env lean --run EmitPastaCurveScheduled.lean vesta \
//!   > ../circuit/tests/fixtures/pasta-vesta-complete-add-scheduled.json
//! ```
//!
//! ## ⚠ WHAT THIS TEST DOES NOT SAY
//!
//! It prices a SHAPE. It says nothing about whether the scheduled row FORCES the RCB formula —
//! that is `Dregg2.Circuit.Emit.AirCrossRow.scheduledRows_force_the_rcb_formula`, in Lean, and it
//! still carries two selector premises (`PhaseIndicator`, `RowsSat`). A narrow row that forced
//! nothing would pass every assertion below.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, TableSem, VmConstraint2, decomp_cols_pub, parse_vm_descriptor2,
};

const SCHED_PALLAS: &str = include_str!("fixtures/pasta-pallas-complete-add-scheduled.json");
const SCHED_VESTA: &str = include_str!("fixtures/pasta-vesta-complete-add-scheduled.json");
const ONEROW_PALLAS: &str =
    include_str!("../descriptors/by-name/pasta-pallas-complete-add-sound.json");

/// `(declared, committed, aux, n_range_lookups)`, read off the descriptor's OWN tables through the
/// deployed `decomp_cols_pub`. This is `MainLayout::build`'s cursor arithmetic, nothing else.
fn price(desc: &EffectVmDescriptor2) -> (usize, usize, usize, usize) {
    let mut aux = 0usize;
    let mut nlk = 0usize;
    for c in &desc.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                desc.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
                nlk += 1;
            }
        }
    }
    (desc.trace_width, desc.trace_width + aux, aux, nlk)
}

/// `log2 |D^(0)| = max(degree_bits) + log_blowup`, the formula
/// `circuit-prove/tests/fri_trace_height_measure.rs:172` states. FRI batches every committed
/// polynomial onto the LARGEST evaluation domain, so the tallest table sets it for the whole proof.
fn log_d0(log_rows: usize, log_blowup: usize) -> usize {
    log_rows + log_blowup
}

#[test]
fn the_scheduled_row_commits_1499_on_the_emitted_bytes() {
    let sched = parse_vm_descriptor2(SCHED_PALLAS).expect("the deployed checker parses the row");
    let onerow = parse_vm_descriptor2(ONEROW_PALLAS).expect("the deployed checker parses the row");

    let (sd, sc, sa, sl) = price(&sched);
    let (od, oc, oa, ol) = price(&onerow);

    println!("\n=== THE PASTA RCB COMPLETE ADDITION, PRICED ON THE EMITTED BYTES ===");
    println!("                              declared  committed      aux   lookups   constraints");
    println!(
        "one-row (deployed)            {od:>8} {oc:>10} {oa:>8} {ol:>9} {:>13}",
        onerow.constraints.len()
    );
    println!(
        "scheduled (1 op / row)        {sd:>8} {sc:>10} {sa:>8} {sl:>9} {:>13}",
        sched.constraints.len()
    );
    println!(
        "\ndeclared ratio  {:.2}x   COMMITTED ratio  {:.2}x   aux ratio  {:.2}x",
        od as f64 / sd as f64,
        oc as f64 / sc as f64,
        oa as f64 / sa as f64
    );
    println!(
        "aux share of committed:  one-row {:.1}%   scheduled {:.1}%",
        100.0 * oa as f64 / oc as f64,
        100.0 * sa as f64 / sc as f64
    );

    // ⚑ The four numbers, against Lean's independently-computed ones.
    assert_eq!(od, 3048, "PastaCurveSound.rcb_width_eq");
    assert_eq!(oc, 10756, "PastaCurveScheduled.the_sound_row_commits_10756");
    assert_eq!(oa, 7708, "PastaCurveScheduled.the_two_aux_blocks (left)");
    assert_eq!(
        ol, 3048,
        "AirSchedule.the_model_reproduces_the_lookup_count (right)"
    );

    assert_eq!(sd, 481, "PastaCurveScheduled.pallasScheduledDesc_width");
    assert_eq!(
        sc, 1499,
        "PastaCurveScheduled.the_scheduled_row_commits_1499"
    );
    assert_eq!(sa, 1018, "PastaCurveScheduled.the_two_aux_blocks (right)");
    assert_eq!(
        sl, 447,
        "PastaCurveScheduled.pallasScheduledAir_range_lookups"
    );
    assert_eq!(
        sched.constraints.len(),
        2297,
        "PastaCurveScheduled.pallasScheduledDesc_constraint_count"
    );

    // ⚑ WHERE THE WIN LIVES. The aux block falls 7.57x; declared falls 6.34x. Committed — the one
    // the wrap is linear in — falls 7.18x, i.e. BETTER than declared, and the reason is entirely
    // the lookup collapse. A `LIMB_BITS` change would move `aux` and NOT `declared`; this pass
    // moves both, and moves aux more.
    assert!(
        oa - sa > od - sd,
        "the AUX recovery ({}) is larger than the DECLARED recovery ({}) — if this flips, the \
         headline sentence about where the win lives is wrong",
        oa - sa,
        od - sd
    );
    assert!(sc * 7 < oc, "committed ratio clears 7x");
    assert!(
        sc * 8 > oc,
        "…and does NOT clear 8x — stating the flattering integer is how a 7.18 becomes an '8x'"
    );

    // ⚠ The aux block is STILL the majority of what the narrowed row commits. Register allocation
    // does not touch it; `LIMB_BITS` does, and `LIMB_BITS` 4->8 is REFUSED on soundness
    // (`descriptor_ir2.rs:400-467`). So this is the floor this pass can reach, not a way station.
    assert!(
        2 * sa > sc,
        "range decomposition is still over half the scheduled row's committed width"
    );
}

#[test]
fn the_vesta_twin_prices_identically() {
    let p = parse_vm_descriptor2(SCHED_PALLAS).expect("pallas");
    let v = parse_vm_descriptor2(SCHED_VESTA).expect("vesta");
    assert_eq!(price(&p), price(&v), "the two curves differ only in `pl`");
    assert_ne!(p.name, v.name, "…and they are not the same descriptor");
    // The accumulator leg is Step/Tick on Vesta: a Pallas-only narrowing would halve the win.
    assert_eq!(price(&v).1, 1499);
}

#[test]
fn the_narrowing_raises_the_lde_domain_and_that_must_be_said() {
    // ⚑ THE COST IS `Q · W` PLUS AN O(log rows) MERKLE TERM — NOT TRACE SIZE. So a narrowing that
    // BUYS width by SPENDING rows is still a win, but the row spend is not free and it lands
    // somewhere visible: |D^(0)|.
    //
    // one-row:   1 op-block per row, so ONE row for a complete addition -> padded to 2^0.
    // scheduled: 33 ops on 33 rows, plus the idle phase -> padded to 2^6 = 64 rows.
    const IR2_INNER_LOG_BLOWUP: usize = 6; // recursion-verify/src/config.rs:88

    let one_row_log = 0usize;
    let sched_log = 6usize; // 33 ops + idle, padded to the next power of two

    let d0_one = log_d0(one_row_log, IR2_INNER_LOG_BLOWUP);
    let d0_sched = log_d0(sched_log, IR2_INNER_LOG_BLOWUP);

    println!("\n=== THE LDE DOMAIN, WHICH A WIDTH TABLE DOES NOT SHOW ===");
    println!("one-row    : 2^{one_row_log} rows -> log2|D^0| = {d0_one}");
    println!(
        "scheduled  : 2^{sched_log} rows -> log2|D^0| = {d0_sched}   (+{} bits)",
        d0_sched - d0_one
    );
    println!(
        "deployed wrap worst case: log2|D^0| = 22 (FriDeployedHeightPairing.deployedWrapLogD0), \
         so a 2^6-row leaf sits far under the ceiling"
    );

    assert_eq!(d0_one, 6);
    assert_eq!(d0_sched, 12);
    // ⚠ SIX BITS. The domain grows; it is the Merkle depth term, not the `Q · W` term, and it is
    // logarithmic against a linear 7.18x. Recorded so the win is quoted with its cost attached.
    assert_eq!(d0_sched - d0_one, 6);
    assert!(
        d0_sched < 22,
        "the scheduled leaf stays under the deployed wrap ceiling of 2^22"
    );
}
