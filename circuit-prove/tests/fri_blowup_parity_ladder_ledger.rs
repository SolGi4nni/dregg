//! # THE `log_blowup` PARITY LADDER, ON ALL FOUR LEAN COLUMNS — not just the two it is named for.
//!
//! `ir2_config`'s docblock names `(lb 6, q 19)`, `(lb 2, q 57)` and `(lb 1, q 114)` as
//! "security-parity" points. They are parity on the two QUERY ledgers (`q·lb + pow` conjectured,
//! `q·lb/2 + pow` proven/Johnson) — and that is all "parity" has ever meant here. The FRI ledger
//! has FOUR columns, and the other two are functions of `log_blowup`:
//!
//!   * **per-fold** (`FriLedgerSound.ledger_perFold_soundness`) — `|Good| ≤ (m−1)·C(2^lb, 2)`, so a
//!     SMALLER folded domain has FEWER good challenges and the posture RISES as `lb` FALLS.
//!   * **commit / `ε_C`** (BCIKS20 Thm 8.3) — carries `1/(2ρ^{3/2}) = 2^(3·lb/2 − 1)`, so a SMALLER
//!     blowup makes it BETTER, and at the deployed wrap this is the column that binds BELOW Johnson
//!     (`COMMIT_FLOOR_BITS`'s own derivation says so).
//!
//! So the sweep the sibling `dregg-circuit` file measures on the wire has a soundness half, and it
//! does not point the same way as the size half. This file reports it, from Lean, for every rung.
//! Rust computes NO soundness number here — every column arrives from
//! `@[export] dregg_fri_ledger` over the compiled `Dregg2.Circuit.FriLedger.friLedger`, exactly as
//! `fri_params_soundness_budget.rs` does. It changes no deployed constant and gates nothing new;
//! the deployed-config floors stay that file's job.
//!
//! Run: `cargo test -p dregg-circuit-prove --test fri_blowup_parity_ladder_ledger -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    IR2_EXT_DEGREE, IR2_FRI_COMMIT_POW_BITS, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN,
    IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS,
};
use dregg_lean_ffi::{FriKnobs, fri_ledger, fri_ledger_available};

/// The rungs. `q` is chosen so `q·lb` is constant at `114` — i.e. both query ledgers are held fixed
/// at the deployed config's `130` conjectured / `73` proven. `(6,19)` is `ir2_config` itself.
const PARITY: &[(usize, usize)] = &[(6, 19), (4, 29), (3, 39), (2, 57), (1, 114)];

/// The same fixture height `fri_params_soundness_budget.rs` reads `ε_C` at — a `2^6`-row trace at
/// the wrap's `2^6` blowup. ⚑ It is a FIXTURE, not production: `ε_C ∝ |D⁽⁰⁾|²`, and the deployed
/// wrap runs at `2^22` where Lean reads 51. Held CONSTANT across the ladder so the column compares
/// like with like; a real ladder would move `log_d0` with `lb` too, and that is called out below.
const FIXTURE_LOG_D0: usize = 12;
/// BCIKS20's proximity parameter (Thm 8.3). Not a prover knob.
const BCIKS_M: usize = 7;

fn knobs_at(lb: usize, q: usize) -> FriKnobs {
    FriKnobs {
        log_blowup: lb,
        num_queries: q,
        query_pow_bits: IR2_FRI_QUERY_POW_BITS,
        max_log_arity: IR2_FRI_MAX_LOG_ARITY,
        log_final_poly_len: IR2_FRI_LOG_FINAL_POLY_LEN,
        ext_deg: IR2_EXT_DEGREE,
        log_d0: FIXTURE_LOG_D0,
        bciks_m: BCIKS_M,
        commit_pow: IR2_FRI_COMMIT_POW_BITS,
    }
}

/// ⚑ **THE LADDER, FROM LEAN.** A missing archive is a REFUSAL, never a fall-back to Rust
/// arithmetic — a hand-written twin of the metatheory is exactly what the sibling gate had deleted.
#[test]
fn the_parity_ladder_reported_on_every_lean_column() {
    assert!(
        fri_ledger_available(),
        "the VERIFIED Lean FRI ledger (`@[export] dregg_fri_ledger`) is NOT in the linked archive, \
         so this file has nothing to report and must NOT compute the numbers itself. Rebuild: \
         `lake build Dregg2.Circuit.FriLedger` in metatheory/, then `cargo build -p dregg-lean-ffi`."
    );

    // The deployed point must be ON the ladder, or the ladder is about some other config.
    assert_eq!(
        (IR2_FRI_LOG_BLOWUP, IR2_FRI_NUM_QUERIES),
        PARITY[0],
        "PARITY[0] must be the DEPLOYED `ir2_config` point; if the deployed knobs moved, this \
         ladder's baseline moved with them and every 'vs deployed' column below is meaningless"
    );

    println!(
        "\n═══ THE (log_blowup, num_queries) PARITY LADDER — ALL FOUR LEAN COLUMNS ═══\n\
         arity {} (2^{IR2_FRI_MAX_LOG_ARITY}) · ext_deg {IR2_EXT_DEGREE} · query_pow \
         {IR2_FRI_QUERY_POW_BITS} · commit_pow {IR2_FRI_COMMIT_POW_BITS} · \
         ε_C read at log_d0={FIXTURE_LOG_D0} (A FIXTURE HEIGHT, not production) · bciks_m={BCIKS_M}",
        1usize << IR2_FRI_MAX_LOG_ARITY,
    );
    println!(
        "\n{:>3}{:>6}{:>8}{:>12}{:>12}{:>12}{:>12}",
        "lb", "q", "|Good|", "capacity", "Johnson", "per-fold", "commit ε_C"
    );

    let mut rows = Vec::new();
    for &(lb, q) in PARITY {
        let l = fri_ledger(knobs_at(lb, q))
            .unwrap_or_else(|e| panic!("Lean ledger at (lb {lb}, q {q}): {e}"));
        assert_eq!(
            l.folded_domain,
            1usize << lb,
            "Lean's folded-domain column must be 2^log_blowup — otherwise the ledger that came \
             back is not about the config we asked about"
        );
        println!(
            "{lb:>3}{q:>6}{:>8}{:>12}{:>12}{:>12}{:>12}",
            l.good_count, l.capacity_bits, l.johnson_bits, l.per_fold_bits, l.commit_bits
        );
        rows.push((lb, q, l));
    }

    let deployed = rows[0].2;
    let lb2 = rows
        .iter()
        .find(|(lb, _, _)| *lb == 2)
        .expect("the (2,57) rung")
        .2;

    // ── ⚑ THE FINDING THE WORD "PARITY" HIDES.
    assert_eq!(
        (deployed.capacity_bits, deployed.johnson_bits),
        (lb2.capacity_bits, lb2.johnson_bits),
        "(6,19) and (2,57) must agree on BOTH query ledgers — that is the entire content of the \
         word 'parity' in `ir2_config`'s docblock, and if it stops holding the ladder is not a \
         controlled experiment"
    );
    assert!(
        lb2.per_fold_bits > deployed.per_fold_bits,
        "dropping log_blowup must IMPROVE the per-fold posture (|Good| ≤ (m−1)·C(2^lb,2) shrinks). \
         Lean read {} at (6,19) and {} at (2,57).",
        deployed.per_fold_bits,
        lb2.per_fold_bits
    );
    assert!(
        lb2.commit_bits > deployed.commit_bits,
        "dropping log_blowup must IMPROVE the commit column (ε_C carries 1/(2ρ^{{3/2}})). Lean \
         read {} at (6,19) and {} at (2,57).",
        deployed.commit_bits,
        lb2.commit_bits
    );

    println!(
        "\n⚑ 'PARITY' IS PARITY ON THE TWO QUERY COLUMNS ONLY.\n  \
         capacity  {} → {} (unchanged, by construction)\n  \
         Johnson   {} → {} (unchanged, by construction)\n  \
         per-fold  {} → {} ({:+} bits — lb=2 is BETTER)\n  \
         commit εC {} → {} ({:+} bits — lb=2 is BETTER)\n\
         At the deployed wrap the commit column BINDS BELOW Johnson ({} < {}), so on the column \
         that actually binds, the (2,57) rung is the STRONGER point — the opposite direction from \
         the wire cost.",
        deployed.capacity_bits,
        lb2.capacity_bits,
        deployed.johnson_bits,
        lb2.johnson_bits,
        deployed.per_fold_bits,
        lb2.per_fold_bits,
        lb2.per_fold_bits as i64 - deployed.per_fold_bits as i64,
        deployed.commit_bits,
        lb2.commit_bits,
        lb2.commit_bits as i64 - deployed.commit_bits as i64,
        deployed.commit_bits,
        deployed.johnson_bits,
    );

    // ── ⚑ AND THE ε_C COLUMN IS NOT TRACE-INVARIANT, so the comparison above is at ONE height.
    // `ε_C ∝ |D⁽⁰⁾|²`, and every rung's MAXIMUM |D⁽⁰⁾| is the same `2^27` (BabyBear two-adicity),
    // reached at a different trace height: `2^21` rows at lb=6, `2^25` at lb=2. Report the column
    // at that shared ceiling so nobody quotes the fixture-height reading as the system's.
    println!(
        "\n{:>3}{:>6}{:>16}{:>16}{:>14}",
        "lb", "q", "max log_rows", "log_d0 at max", "commit ε_C"
    );
    let mut ceiling: Vec<(usize, usize)> = Vec::new();
    for &(lb, q) in PARITY {
        let max_log_rows = 27 - lb; // BabyBear two-adicity 27; `log_h + lb ≤ 27`.
        let mut k = knobs_at(lb, q);
        k.log_d0 = 27; // the LDE domain at the ceiling is 2^27 at EVERY rung, by definition
        let l = fri_ledger(k).unwrap_or_else(|e| panic!("Lean ledger at ceiling (lb {lb}): {e}"));
        println!(
            "{lb:>3}{q:>6}{max_log_rows:>16}{:>16}{:>14}",
            27, l.commit_bits
        );
        ceiling.push((lb, l.commit_bits));
    }
    let c6 = ceiling.iter().find(|(lb, _)| *lb == 6).expect("lb 6").1;
    let c2 = ceiling.iter().find(|(lb, _)| *lb == 2).expect("lb 2").1;
    // ⚑ The obvious guess — "same domain, so same ε_C" — is FALSE, and the ladder refutes it.
    // `ε_C`'s first term carries `1/(2ρ^{3/2}) = 2^(3·lb/2 − 1)`, which has no `|D⁽⁰⁾|` in it at
    // all, so the blowup gap SURVIVES the shared ceiling. Asserted, because it was written the
    // other way first and the printed numbers were the thing that caught it.
    assert!(
        c2 > c6,
        "at the shared 2^27 ceiling the low-blowup rung must STILL read better on ε_C — the \
         1/(2ρ^{{3/2}}) term is height-free. Lean read {c6} at lb=6 and {c2} at lb=2."
    );
    println!(
        "\n⚑ THE CEILING DOES NOT ERASE THE GAP. Every rung runs the same 2^27 FRI domain there, \
         but ε_C's `1/(2ρ^(3/2))` term is HEIGHT-FREE, so lb=2 still reads {c2} against lb=6's \
         {c6} — the same {} -bit spread as at the fixture. What the ceiling DOES do is cost every \
         rung ~30 bits against its fixture-height reading ({} → {c6} at lb=6). So the honest \
         summary is: a lower blowup is better on this column at every height AND reaches 16x the \
         trace rows; the fixture-height numbers above are the flattering ones for BOTH rungs, and \
         neither is a claim about a production turn.",
        c2 as i64 - c6 as i64,
        deployed.commit_bits,
    );
}
