//! # THE DEPLOYED TRACE-HEIGHT MEASUREMENT — the input `ε_C` needs and nobody had measured.
//!
//! ## Why this file exists
//!
//! `docs/reference/FRI-SOUNDNESS-FRONTIER-RESEARCH.md` §3.2 names one number as *"the single input
//! that moves the proven posture most and nobody has measured it"*: the **deployed trace height**.
//! The reason is BCIKS20's commit-phase error, read verbatim from the paper
//! (`~/dev/gh/forks/IACR-eprint-mirror/2020/654.pdf`, Lemma 8.2 p.40 / Thm 8.3 pp.40-41):
//!
//! ```text
//! ε_FRI = ε_C + α^s ,   α = √ρ·(1 + 1/2m) ,   m ≥ 3
//! ε_C   = (m+½)⁷·|D⁽⁰⁾|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁽⁰⁾|+1)·Σᵢ l⁽ⁱ⁾ / (√ρ·|F|)
//! ```
//!
//! **`ε_C ∝ |D⁽⁰⁾|²`.** So the proven posture is NOT trace-invariant — it falls ~2 bits per trace
//! doubling. The shipped ledger (`fri_params_soundness_budget.rs`, `q·lb/2 + pow`) is the `m → ∞`
//! idealisation of the QUERY column ONLY: it drops ε_C entirely and therefore reports the same
//! number at every trace height. **`FriKnobs` carries no height field at all.** That is the gap this
//! file measures into.
//!
//! ## What this file does, and the one thing it deliberately does NOT do
//!
//! It MEASURES. It runs real deployed workloads, reads `BatchProof::degree_bits` **off the proofs
//! they actually produce**, and pins the envelope. It computes **no soundness bound** — the
//! predecessor twin that re-derived that arithmetic in hand-written Rust is exactly what
//! `fri_params_soundness_budget.rs` exists to have deleted, and this file does not resurrect it.
//! `ε_C` is being mechanized as a real column in `Dregg2.Circuit.FriLedger` (a sibling lane); this
//! file supplies the **`|D⁽⁰⁾|` that column consumes**, measured rather than assumed.
//!
//! The research report is explicit that its own `|D⁽⁰⁾|` was **assumed, not measured** (2^12 from the
//! `degree_bits [6,3,4]` fixture; 2^20 as a hypothetical tall anchor). Both are now measured, and
//! **both were wrong in the same direction** — see the findings.
//!
//! ## `|D⁽⁰⁾| = height · 2^log_blowup` — CONFIRMED IN THE DEPLOYED CODE, not assumed
//!
//! Traced through the pinned plonky3 (`Cargo.toml:238`, rev `82cfad73`):
//!   * `uni-stark/src/prover.rs:43-44` — `let degree = trace.height(); log2_strict_usize(degree)`
//!     (a non-power-of-two trace PANICS — heights are exactly powers of two);
//!   * `fri/src/two_adic_pcs.rs:285` — `natural_domain_for_degree` ⇒ the trace domain `H` has
//!     `|H| = height` exactly;
//!   * `fri/src/two_adic_pcs.rs:314-318` — commit does `coset_lde_batch(evals, log_blowup, shift)`;
//!   * `dft/src/traits.rs:253-261` — the LDE is literally a left-shift by `log_blowup`;
//!   * the read side inverts it: `two_adic_pcs.rs:380` `lde.height() >> self.fri.log_blowup`.
//! BCIKS20 defines `ρ = (k⁽⁰⁾+1)/|D⁽⁰⁾|` (Lemma 8.2), and ethSTARK's own worked example
//! (eprint 2021/582 §5.10.2: `|H₀| = 2^20`, `ρ = 1/4`, `|D| = 2^22`) is the same relation.
//!
//! ## ⚑ THE FINDINGS — three, and each contradicts an assumption the report had to make
//!
//! **1. The tall trace is not hypothetical. It is DEPLOYED, on every fold, by construction.**
//! `accumulator.rs:238` sets `WRAP_LOG_CEIL = 16` and `wrap_params()` applies it as a
//! `min_trace_height` FLOOR (live, and ON BY DEFAULT — `accumulator.rs:660`, `:427`), forcing every
//! running-proof table to `degree_bits ≥ 16` so the FRI phase count cannot grow with fold depth. That
//! knob — added to make the VK depth-invariant — is also the system's **tallest committed trace**,
//! and at `log_blowup = 3` it lands `|D⁽⁰⁾| = 2^19`. Measured natural fold heights are
//! `degree_bits [9, 9, 15, 14, 15]` (`apex_shrink_trace_anatomy`, re-measured for this file;
//! independently recorded at `accumulator.rs:227`) — so the ceiling pads 2^15 → 2^16. **The worst
//! case is also the typical case: no workload is small enough to escape it.**
//!
//! **2. The leaf height is NOT the effect-VM trace height — it is the CHIP table, and it overtakes.**
//! `MIN_TRACE_HEIGHT = 64` (`circuit/src/effect_vm/trace.rs:508`) floors the MAIN table at 2^6, which
//! is where the report's `[6,3,4]` fixture comes from. But the deployed IR-v2 batch commits five
//! tables and FRI batches them onto the LARGEST domain. The Poseidon2 CHIP table is sized ~4 rows per
//! transfer (`descriptor_ir2.rs:3874`, `next_pow2`), so it **passes the main table at 32 effects**.
//! Measured, one deployed `transferVmDescriptor2` per row:
//!
//! | effects | trace rows | `degree_bits` | max | `\|D⁽⁰⁾\|` |
//! |---:|---:|---|---:|---:|
//! | 1 | 64 | `[6, 3, 4]` | 2^6 | 2^12 |
//! | 16 | 64 | `[6, 6, 4]` | 2^6 | 2^12 |
//! | 32 | 64 | `[6, 7, 4]` | **2^7** | 2^13 |
//! | 64 | 64 | `[6, 8, 4]` | **2^8** | 2^14 |
//! | 128 | 128 | `[7, 9, 4]` | 2^9 | 2^15 |
//! | 512 | 512 | `[9, 11, 4]` | 2^11 | 2^17 |
//!
//! A gate reading the effect-VM trace height would report 2^6 for the 32-effect turn and be wrong by
//! a factor of 2 in `|D⁽⁰⁾|` — i.e. by ~2 proven bits. **Height must be read off the PROOF, which is
//! why this file reads `BatchProof::degree_bits` and never the witness.**
//!
//! **3. Nothing caps effects-per-turn**, so the leaf `|D⁽⁰⁾|` is UNBOUNDED ABOVE (a census of
//! `turn/`, `intent/`, `circuit/src/effect_vm/` found no `MAX_EFFECTS`-class bound). The leaf is
//! small in practice — a real multi-verb turn through the production `TurnExecutor` measures
//! `degree_bits [3,4,3,3]` (`circuit/tests/effect_vm_umem_real_turn.rs`), i.e. `2^4` — but there is
//! no structural reason it stays there, and every doubling costs ~2 proven bits. That is a real
//! open residual, named here rather than papered over: the envelope below is pinned at a MEASURED
//! turn size, not at a proven bound.
//!
//! ⚑ `create_recursion_config` was ALREADY the named weakest link on the query column (pow 14 ⇒
//! Johnson 71, `fri_params_soundness_budget.rs:906`). It is ALSO the tallest-trace config. The two
//! weaknesses compound on the same object, and the query ledger cannot see the second one.
//!
//! ## What this file asserts
//!
//! The ENVELOPE, not a bound: every measured deployed height stays inside a pinned window, and the
//! recursion ceiling is that window's top. A regression that makes a trace TALLER reds this file —
//! which is the point, because a taller trace silently lowers the proven number and NO existing gate
//! can see it (`FriKnobs` has no height field, so the ledger reports the same bits either way).
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test fri_trace_height_measure -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_BLOWUP, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::PROD_FRI_LOG_BLOWUP;
use dregg_circuit_prove::accumulator::WRAP_LOG_CEIL;
use dregg_circuit_prove::dregg_outer_config::OUTER_FRI_LOG_BLOWUP;
use dregg_circuit_prove::ivc_turn_chain::IR2_INNER_LOG_BLOWUP;

// ─────────────────────────────────────────────────────────────────────────────
// THE PINS. Each is a MEASURED value with its measurement named — not a guess, and not a target.
// ─────────────────────────────────────────────────────────────────────────────

/// The largest effect count this file measures the leaf envelope AT. Not a system limit — **no such
/// limit exists** (finding 3). It is the turn size the envelope below is honest about.
const ENVELOPE_TURN_EFFECTS: usize = 64;

/// The leaf `|D⁽⁰⁾|` (as `log₂`) for a turn of up to [`ENVELOPE_TURN_EFFECTS`] effects, MEASURED.
///
/// `2^14` = the chip table's `2^8` at 64 effects, times the deployed `log_blowup = 6`. Note this is
/// **4× the `2^12` the report's fixture implies** — the fixture is a 1-effect turn, and the report's
/// own cost grid inherits that. It is NOT a proven ceiling: a 128-effect turn measures `2^15` and a
/// 512-effect turn `2^17`. Repin it, naming the workload, if a bigger turn family ships — and re-read
/// the ε_C column at the new `|D⁽⁰⁾|` when you do.
const LEAF_ENVELOPE_LOG_D0: usize = 14;

/// **THE WORST CASE THE DEPLOYED SYSTEM PRODUCES**, as `log₂|D⁽⁰⁾|`: the recursion wrap.
///
/// `WRAP_LOG_CEIL` (2^16 rows, FORCED on every running fold) + `IR2_INNER_LOG_BLOWUP` (6) — the
/// blowup of the config that same `prove` call binds. This is the number the proven posture is set
/// by: not the leaf's, and not the fixture's.
///
/// ⚑ **REPAIRED 2026-07-28. It was `WRAP_LOG_CEIL + RECURSION_FRI_LOG_BLOWUP` (the recursion config's blowup) = 19**, which adds one
/// path's trace floor to the OTHER path's blowup: `Accumulator::accumulate` applies `wrap_params()`'s
/// `min_trace_height` floor AND binds `config = ir2_leaf_wrap_config()` in the SAME call, and that
/// config's blowup is `IR2_INNER_LOG_BLOWUP = 6`; `create_recursion_config` (`lb = 3`) is never
/// constructed on the wrap path. Lean proved the correct pairing in 2026-07
/// (`Dregg2.Circuit.FriDeployedHeightPairing.deployedWrapLogD0 = 22`, `deployed_wrap_commitBits = 51`,
/// `deployed_wrap_is_not_61`) and this constant was left wrong anyway, with a doc comment saying so —
/// *"moving it is a posture change to be argued, not a constant to edit quietly"*.
///
/// It is not an argument any more, because it is now MEASURED rather than derived. The leaf-wrap
/// output proof's own `degree_bits` at the deployed knobs read **`[10, 9, 16, 14, 16]`**
/// (`circuit-prove/tests/fri_hundred_bit_cutover.rs`, real prove + real verify): the wrap trace is
/// `2^16` **naturally**, and at `lb = 6` that is `|D⁽⁰⁾| = 2^22` off a proof, agreeing with Lean
/// exactly. ⚠ Note what that also settles: `WRAP_LOG_CEIL` is a FLOOR, and at the leaf wrap it is
/// not padding anything — lowering it does not shrink this domain.
///
/// The posture change this repair makes explicit: the deployed commit column reads **51**, not 61.
const DEPLOYED_WORST_LOG_D0: usize = WRAP_LOG_CEIL + IR2_INNER_LOG_BLOWUP;

/// One measured workload: what ran, and the heights the proof it produced actually carries.
#[derive(Debug)]
struct Measured {
    label: String,
    /// `log₂(rows)` per committed table — read off `BatchProof::degree_bits`, i.e. off a REAL proof.
    /// Never off the witness: finding 2 is that the witness height is not the committed max.
    degree_bits: Vec<usize>,
    /// The deployed `log_blowup` the proof was produced under.
    log_blowup: usize,
}

impl Measured {
    fn max_log_height(&self) -> usize {
        self.degree_bits.iter().copied().max().unwrap_or(0)
    }
    /// `|D⁽⁰⁾| = max_height · 2^log_blowup`, as `log₂`. FRI batches every committed poly onto the
    /// LARGEST evaluation domain, so the tallest table sets `|D⁽⁰⁾|` for the whole proof.
    fn log_d0(&self) -> usize {
        self.max_log_height() + self.log_blowup
    }
}

/// **THE MEASUREMENT.** A real deployed workload, proven through the production
/// `transferVmDescriptor2` at `ir2_config`, its heights read off the proof. The proof is VERIFIED
/// before it is measured — a proof that does not verify is not evidence of anything.
fn measure_turn(n_effects: usize) -> Measured {
    let json = descriptor2_for_key("transferVmDescriptor2").expect("deployed transfer descriptor");
    let desc = parse_vm_descriptor2(json).expect("transfer descriptor parses");
    let state = CellState::new(100_000_000, 0);
    let effects: Vec<Effect> = (0..n_effects)
        .map(|_| Effect::Transfer {
            amount: 1,
            direction: 1,
        })
        .collect();
    let (trace, pis) = generate_effect_vm_trace(&state, &effects);
    let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .expect("the deployed transfer must prove — a workload that cannot prove measures nothing");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("the measured proof must verify");
    Measured {
        label: format!("ir2 transfer x{n_effects} (deployed transferVmDescriptor2, real witness)"),
        degree_bits: proof.degree_bits.clone(),
        log_blowup: IR2_FRI_LOG_BLOWUP,
    }
}

/// **THE LIVE MEASUREMENT — real workloads, real proofs, heights read off the wire.**
///
/// Reports the distribution rather than collapsing it to a comfortable median, and asserts the
/// envelope. Non-vacuous by construction: it requires that workloads were actually measured and that
/// each carries a non-empty `degree_bits`.
#[test]
fn deployed_leaf_heights_are_measured_and_within_the_envelope() {
    let measured: Vec<Measured> = [1usize, 4, 16, 32, ENVELOPE_TURN_EFFECTS]
        .iter()
        .map(|&n| measure_turn(n))
        .collect();
    assert!(
        !measured.is_empty(),
        "no workload was measured — every envelope assertion below would be vacuous"
    );

    for m in &measured {
        assert!(
            !m.degree_bits.is_empty(),
            "[{}] the proof carries no degree_bits — nothing was measured",
            m.label
        );
        println!(
            "[{}]\n    degree_bits {:?} → max height 2^{} · log_blowup {} → |D⁽⁰⁾| = 2^{}",
            m.label,
            m.degree_bits,
            m.max_log_height(),
            m.log_blowup,
            m.log_d0(),
        );
        assert!(
            m.log_d0() <= LEAF_ENVELOPE_LOG_D0,
            "[{}] measured |D⁽⁰⁾| = 2^{}, ABOVE the pinned leaf envelope 2^{LEAF_ENVELOPE_LOG_D0}. \
             This is not necessarily a bug — a bigger turn legitimately grows the trace — but \
             ε_C ∝ |D⁽⁰⁾|² means it LOWERS the proven soundness (~2 bits per doubling, BCIKS20 \
             Thm 8.3), and NO other gate in this tree can see it: `FriKnobs` carries no height, so \
             `fri_params_soundness_budget.rs` reports the same bits at any height. Re-read the ε_C \
             column in `Dregg2.Circuit.FriLedger` at the new |D⁽⁰⁾| and land the number, then repin \
             LEAF_ENVELOPE_LOG_D0 here naming the workload that forced it.",
            m.label,
            m.log_d0(),
        );
    }

    // ⚑ THE DISTRIBUTION, reported as min/median/max. The MAX is the posture; the median is not.
    let mut d0s: Vec<usize> = measured.iter().map(|m| m.log_d0()).collect();
    d0s.sort_unstable();
    println!(
        "== LEAF |D⁽⁰⁾| DISTRIBUTION (n = {}, turns of 1..={ENVELOPE_TURN_EFFECTS} effects) ==\n  \
         min 2^{} | median 2^{} | max 2^{}  ← the max is what sets the proven number",
        d0s.len(),
        d0s[0],
        d0s[d0s.len() / 2],
        d0s[d0s.len() - 1],
    );

    // The chip table, not the main trace, is the tallest at the envelope size — finding 2, gated so
    // a future reader cannot re-derive the posture from the effect-VM height and be wrong by 2 bits.
    let big = measured.last().expect("measured");
    assert!(
        big.degree_bits[1] > big.degree_bits[0],
        "at {ENVELOPE_TURN_EFFECTS} effects the CHIP table (degree_bits[1] = 2^{}) must exceed the \
         MAIN effect-VM table (degree_bits[0] = 2^{}) — that is finding 2, and the reason this file \
         reads heights off the PROOF rather than off the witness trace. If this inverts, the chip \
         sizing changed and the leaf posture must be re-measured, not re-derived.",
        big.degree_bits[1],
        big.degree_bits[0],
    );
}

/// **⚑ THE WORST CASE IS THE RECURSION, AND IT IS THE TYPICAL CASE TOO.**
///
/// The finding, gated so it cannot be re-forgotten: the tallest deployed trace is not a big workload,
/// it is `WRAP_LOG_CEIL` — a FLOOR the wrap applies to every running-proof table on every fold, so
/// the system's worst-case `|D⁽⁰⁾|` is paid unconditionally.
///
/// This test computes no soundness bound (that is Lean's column, not Rust's). It pins the INPUT: the
/// worst-case `|D⁽⁰⁾|` the deployed system produces, and the fact that the recursion — already the
/// named weakest link on the query column at pow 14 — is also the tallest.
#[test]
fn the_recursion_ceiling_is_the_systems_worst_case_domain() {
    let leaf_max_d0 = measure_turn(ENVELOPE_TURN_EFFECTS).log_d0();
    // The outer/gnark shrink: `apex_shrink.rs:140-146` records — and `apex_shrink_trace_anatomy`
    // re-measures — the two 2^15-row tables.
    let outer_d0 = 15 + OUTER_FRI_LOG_BLOWUP;

    println!(
        "== DEPLOYED |D⁽⁰⁾| CENSUS ==\n  \
         leaf ir2 @ {ENVELOPE_TURN_EFFECTS} effects (lb={IR2_FRI_LOG_BLOWUP})   |D⁽⁰⁾| = \
         2^{leaf_max_d0}   (MEASURED)\n  \
         v1 per-turn (lb={PROD_FRI_LOG_BLOWUP})                    |D⁽⁰⁾| = 2^{}   (2^6 main table)\n  \
         outer/gnark shrink (lb={OUTER_FRI_LOG_BLOWUP})             |D⁽⁰⁾| = 2^{outer_d0}   \
         (MEASURED 2^15 tables)\n  \
         ir2 leaf WRAP (lb={IR2_INNER_LOG_BLOWUP})               |D⁽⁰⁾| = \
         2^{DEPLOYED_WORST_LOG_D0}   (WRAP_LOG_CEIL = 2^{WRAP_LOG_CEIL}, FORCED every fold; the \
         wrap trace is 2^16 NATURALLY — MEASURED degree_bits [10,9,16,14,16])\n  \
         ⚑ WORST CASE = 2^{DEPLOYED_WORST_LOG_D0} — {}× the 2^12 the cost grid and the ~70-bit \
         headline are measured at.",
        6 + PROD_FRI_LOG_BLOWUP,
        1usize << (DEPLOYED_WORST_LOG_D0 - 12),
    );

    assert!(
        DEPLOYED_WORST_LOG_D0 > leaf_max_d0,
        "the recursion's |D⁽⁰⁾| (2^{DEPLOYED_WORST_LOG_D0}) must exceed the leaf's \
         (2^{leaf_max_d0}) — if this ever inverts, the worst case moved to the leaf and the posture \
         must be re-read there instead. The whole point of this file is that the number is set by \
         the WORST case, not by the fixture and not by the median."
    );

    // ⚑ The wrap is the worst case on the HEIGHT column; `fri_params_soundness_budget.rs`'s
    //   `recursion_config_is_the_weakest_link` pins the QUERY half on a different config (pow 14 ⇒
    //   Johnson 71). Two columns, two weakest links — which is why they stay separate.
    assert_eq!(
        DEPLOYED_WORST_LOG_D0, 22,
        "the deployed wrap commits |D⁽⁰⁾| = 2^(WRAP_LOG_CEIL + IR2_INNER_LOG_BLOWUP) = 2^(16 + 6) = \
         2^22 — MEASURED off a real leaf-wrap proof's degree_bits [10,9,16,14,16] \
         (`fri_hundred_bit_cutover.rs`), and equal to Lean's \
         `FriDeployedHeightPairing.deployedWrapLogD0`. ⚑ It read 2^19 until 2026-07-28, adding this \
         path's trace floor to the OTHER path's blowup (`create_recursion_config`, lb 3, is never \
         constructed on the wrap path). If either knob moved, the ε_C input moved with it and the \
         proven number changed — re-read `Dregg2.Circuit.FriLedger`'s ε_C column at the new |D⁽⁰⁾| \
         before repinning this. ⚠ And note lowering WRAP_LOG_CEIL does NOT help: the wrap trace is \
         2^16 naturally, and the ceiling is a FLOOR."
    );
    assert!(
        outer_d0 < DEPLOYED_WORST_LOG_D0,
        "sanity: the gnark-verified outer shrink (2^{outer_d0}) sits below the recursion wrap \
         (2^{DEPLOYED_WORST_LOG_D0})"
    );
}

/// **THE CANARY — a height regression MUST red, and the envelope must not be slack.**
///
/// The honest pole runs first (the real deployed heights clear the envelope), so the regression
/// assertion cannot be satisfied by a check that reds on everything. Then a REAL taller workload —
/// not a synthetic matrix — must break it, proving the envelope is live rather than decorative.
///
/// This is the tooth that makes the measurement non-rotting: `FriKnobs` has no height field, so a
/// trace that doubles is invisible to every other gate in the tree while quietly costing ~2 proven
/// bits. Here it reds.
#[test]
fn a_taller_trace_reds_the_envelope() {
    let within = |m: &Measured| m.log_d0() <= LEAF_ENVELOPE_LOG_D0;

    // ── HONEST POLE FIRST. The real deployed heights must PASS, or the canary below asserts nothing.
    for n in [1usize, 16, ENVELOPE_TURN_EFFECTS] {
        let m = measure_turn(n);
        assert!(
            within(&m),
            "[{}] the DEPLOYED |D⁽⁰⁾| 2^{} must clear the envelope 2^{LEAF_ENVELOPE_LOG_D0} — \
             otherwise the regression canary below is vacuous (a check that reds on everything reds \
             on a regressed workload too)",
            m.label,
            m.log_d0(),
        );
    }

    // ── THE REGRESSION. A REAL 128-effect turn, proven through the REAL deployed descriptor: double
    //    the envelope's turn size, which the measurement says doubles |D⁽⁰⁾| (2^14 → 2^15). This is a
    //    regression a workload can actually cause, not a hand-built matrix.
    let regressed = measure_turn(2 * ENVELOPE_TURN_EFFECTS);
    println!(
        "[canary] {} → degree_bits {:?} → |D⁽⁰⁾| = 2^{}",
        regressed.label,
        regressed.degree_bits,
        regressed.log_d0(),
    );
    assert!(
        !within(&regressed),
        "a {}-effect turn measures |D⁽⁰⁾| = 2^{} and MUST break the pinned envelope \
         2^{LEAF_ENVELOPE_LOG_D0}. It does not, so this file is not protecting the input it names: a \
         |D⁽⁰⁾| doubling would slip through, and because ε_C ∝ |D⁽⁰⁾|² it would silently cost ~2 \
         proven bits that no other gate in this tree can see.",
        2 * ENVELOPE_TURN_EFFECTS,
        regressed.log_d0(),
    );
    // …and the break must be a genuine |D⁽⁰⁾| MOVE — the quantity ε_C actually reads — not a row
    // count that the blowup happens to absorb.
    let base = measure_turn(ENVELOPE_TURN_EFFECTS);
    assert!(
        regressed.log_d0() > base.log_d0(),
        "the regression must move |D⁽⁰⁾| itself (2^{} → 2^{}), not merely a witness row count — \
         |D⁽⁰⁾| is what ε_C reads",
        base.log_d0(),
        regressed.log_d0(),
    );
}
