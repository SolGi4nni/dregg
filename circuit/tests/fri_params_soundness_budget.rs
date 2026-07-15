//! # THE FRI PARAMS→BITS BUDGET GATE — the knob-drift floor, computed and enforced.
//!
//! The deployed FRI configs carry a soundness budget that lived ONLY in comments
//! (`plonky3_prover::create_config`, `descriptor_ir2::ir2_config`) — a knob edit could silently
//! drop it with no red anywhere. This file computes the budget FROM the exported production knobs
//! and enforces the floors against knob drift.
//!
//! ## The ledger — and what the numbers actually mean (post-audit, 2026-07-13)
//!
//!   * **capacity ledger (REFUTED as a security claim)**: `num_queries × log_blowup +
//!     query_pow_bits`. This is the FRI capacity / up-to-capacity (`1−ρ`) per-query figure every
//!     production STARK historically quoted. **The capacity conjecture is REFUTED** for coset
//!     Reed–Solomon at rates covering our `ρ = 1/64` (Kambiré, arXiv 2604.09724 / eprint
//!     2025/2046). So this column is NOT a proven, nor even conjecturally-safe, security number —
//!     it is retained ONLY as the historical arithmetic and as a stable knob-drift baseline.
//!   * **proven (Johnson bound)**: `num_queries × log_blowup / 2 + query_pow_bits` — the
//!     list-decoding-to-√rate figure that IS proven for any code (`73` at deployed). FLOORED at
//!     `73` (`PROVEN_JOHNSON_FLOOR_BITS`) — see "what changed" below.
//!   * **the number we actually stand behind (~112.6)**: for the deployed dim-2 constant-fold
//!     recursion code, the FIELD-INDEPENDENT counting bound `|Good| ≤ C(64,2) = 2016` over the
//!     quartic-extension challenge field (`|F| ≈ 2^123.6`) proves `2016/|F| < 2⁻¹¹²`, i.e.
//!     **~112.6 proven bits** (`wrap_perFold_soundness_capacity`,
//!     `metatheory/Dregg2/Circuit/FriCorrelatedAgreementSharp.lean` §8). This — not the refuted
//!     capacity 130 — is the accepted standing security posture (ember, 2026-07-13). Sound against
//!     Kambiré: his blow-up needs `n → ∞`, `r > 2`; at our fixed `r = 2`, `n = 64` his own
//!     construction caps at `C(64,2)`.
//!   * **caps**: all figures are additionally capped by the degree-4 BabyBear extension (~2^124
//!     challenge space) and the Poseidon2 commitment hash. The ~112.6 already sits under this cap.
//!
//! ## ⚑ Where the ~112.6 COMES FROM — and therefore which knobs it depends on
//!
//! Read `BabyBearFriDeployedInstance.lean` §2 and `FriCorrelatedAgreementSharp.lean` §8 before
//! touching the pins below. The Lean soundness object is
//! `friSetupWrapRate : FriSetup BabyBear (Fin (2^7)) (Fin (2^6)) := friSetupParam 6 omega128 …` —
//! it is built from **`log_blowup = 6` ALONE**:
//!
//!   * `|L| = 2^7 = 128` (the coset), `|κ| = 2^6 = 64` (the FOLDED domain), RS dimension `r = 2`,
//!     giving rate `2/128 = 1/64` — EXACTLY the deployed `log_blowup = 6`.
//!   * The counting bound is `|Good| ≤ C(|κ|, 2) = C(64, 2) = 2016`, and the per-fold error is
//!     `2016 / babyBearP⁴ ≈ 2⁻¹¹²·⁶⁵` (`wrap_perFold_soundness_capacity_interval`).
//!
//! So **`n = 64` and `r = 2` are both consequences of `log_blowup = 6`** (`|κ| = 2^log_blowup`;
//! `r = 2` is the code dimension), and `extDeg = 4` supplies `|F|`. The ~112.6 is a function of
//! `(log_blowup, extDeg)` — it is NOT a function of `max_log_arity` or `log_final_poly_len`.
//!
//! ⚠ **`max_log_arity` and `log_final_poly_len` do NOT enter any soundness formula in this tree,
//! and no Lean theorem consumes them.** `FriVerifier.FriParams` carries `maxLogArity` /
//! `logFinalPolyLen` fields and `ir2LeafWrapConfig` pins them to `3` / `0`
//! (`FriVerifier.lean:373-375`), but they are INERT — grep the metatheory: nothing reads them.
//! `docs/reference/FRI-PARAM-FRONTIER.md` §1a states the same ("Neither is a security lever").
//! **Therefore this file does NOT invent a numeric bound for them.** It pins them by EQUALITY to
//! the modeled config, which is the honest and derivable gate — see below.
//!
//! ⚑ **RESIDUAL RESOLVED (2026-07-15) — and the answer LOWERS the deployed posture to ~109.84.**
//! The residual read: the Lean per-fold model folds **2-to-1** (`Fin (2^7) → Fin (2^6)`,
//! `Fold geom α f = E f + α·O f`) while the deployed config folds at arity **8**
//! (`max_log_arity = 3`), and the transfer was NOT mechanized. It is now derived and mechanized in
//! `metatheory/Dregg2/Circuit/FriArityTransfer.lean` (Lake-green, `sorry`-free, in the `Dregg2`
//! build target). The finding, reported unmassaged:
//!
//!   * The deployed fold really IS arity-8 and really IS a degree-7 **moment curve**: the pinned
//!     plonky3 rev (`82cfad73`, `fri/src/two_adic_pcs.rs:109-131`) computes
//!     `lagrange_interpolate_at(xs, evals, beta)` ⇒ `Fold_β f (y) = Σ_{i<8} β^i · g_i(y)`. §8's
//!     `2×2` Vandermonde (which pins PAIRWISE intersections to `≤ 1`, and is the whole engine of the
//!     `C(64,2)` count) does NOT survive: two challenges give only 2 equations in 8 unknowns.
//!   * The arity-generic count (`good_card_le_of_phase_injective`) replaces it: for `y ≠ z`,
//!     `H y − H z` is a nonzero degree-`≤ m−1` polynomial whose roots are exactly the good
//!     challenges folding both fibres to the same constant, so each PAIR lies in `≤ m−1` agreement
//!     sets ⇒ `|Good| · C(s,2) ≤ (m−1) · C(|κ|,2)`. It **recovers §8's `2016` EXACTLY at `m = 2`**
//!     (`arity2_recovers_capacity_count`) — the check that it is the right generalization.
//!   * At the deployed `m = 8`: `|Good| ≤ 7 · C(64,2) = 14112`, so the per-fold error is
//!     `14112 / babyBearP⁴ < 2⁻¹⁰⁹` — **~109.84 proven bits, `log₂ 7 ≈ 2.807` BELOW the ~112.6**,
//!     and ~112.6 provably does NOT hold at arity 8 by this method (`arity8_error_not_lt_2e112`).
//!
//! So `max_log_arity` **IS** a security lever (contra the older "not a security lever" note, now
//! corrected in `docs/reference/FRI-PARAM-FRONTIER.md` §1a) — worth `2.807` bits, the price of the
//! measured +9% proof-size saving arity-8 buys. (The gnark ETH-wrap verifier runs arity-2 —
//! `circuit-prove/tests/apex_shrink_blowup_sweep.rs:186` — so ~112.6 is the right figure THERE.)
//! NAMED OBLIGATION (open): the `M = 1` fiber bound is carried as the HYPOTHESIS `hΦ`
//! (`Arity8FiberBound`); discharging it needs the `|L| = 512`, dim-`8`, rate-`1/64` arity-8 setup
//! the metatheory does not build. The `ModelDrift` pin below still exists so that moving arity
//! cannot happen silently — it now pins a knob with a KNOWN bit price.
//!
//! ## What this gate is (and is NOT)
//!
//! The `≥ 128` check below is a CONSERVATIVE ENGINEERING MARGIN on the capacity arithmetic — a
//! knob-drift tooth that reddens when a config edit lowers the (refuted) capacity number. **It is
//! NOT a claim that 128 is proven or conjecturally-safe.** It is KEPT, unchanged, as the labeled
//! drift canary it honestly is. Retargeting the numeric gate off the capacity metric is an ember
//! decision, not this test's to make; the margin is left at 128 (which the deployed capacity 130
//! clears) purely as drift detection.
//!
//! ## Teeth
//!
//!   1. Both deployed configs (v1 `create_config`, IR-v2 `ir2_config`) satisfy `capacity ≥ 128`
//!      and `proven(Johnson) ≥ 73` — and their two ledgers agree (security parity, the invariant
//!      the `(6, 19)` pin was measured against).
//!   2. Both deployed configs carry the modeled structural pair (`max_log_arity = 3`,
//!      `log_final_poly_len = 0`), and the IR-v2 WRAP config equals the Lean-modeled
//!      `ir2LeafWrapConfig` on ALL FIVE knobs — the config every ~112.6 theorem is stated about.
//!   3. NON-VACUITY: `budget_gate_reds_each_degraded_knob` PERTURBS THE DEPLOYED CONSTS — it
//!      degrades each of the **5** gated knobs on each config in turn — and requires `check_budget`,
//!      the same function tooth 1 calls, to refuse with a typed reason NAMING that knob.
//!   4. `proven_floor_is_not_shadowed_by_the_capacity_check` and
//!      `lean_model_pin_reds_wrap_drift_that_clears_both_floors` prove the two NEW floors are
//!      load-bearing rather than redundant: each exhibits a knob set the OTHER gates accept.
//!
//! ## What changed (2026-07-15) — closing CRATE-EXCELLENCE-PLAN Move 5
//!
//! Previously the gate covered 3 of the 5 knobs, and `proven_bits` was computed and printed but
//! never floored. Now: all 5 knobs are gated, and `proven_bits` is floored.
//!
//! ⚑ **Move 5 said "a `proven_bits` floor at ~112". That is arithmetically WRONG and is NOT what
//! landed.** `proven_bits` computes the **Johnson** ledger, which is **73** at the deployed knobs
//! (`19·6/2 + 16`) — flooring it at 112 would red the deployed config instantly. The ~112.6 is a
//! DIFFERENT quantity (the per-fold proximity-gap error over the quartic extension) that this
//! formula does not compute and that these two knobs do not move. So `proven_bits` is floored at
//! its REAL posture (`73`), and the ~112.6 posture is protected the only way it is derivable —
//! by pinning the wrap config to the Lean-modeled knob set the theorem quantifies over.
//!
//! Run: `cargo test -p dregg-circuit --test fri_params_soundness_budget -- --nocapture`.

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES,
    IR2_FRI_QUERY_POW_BITS,
};
use dregg_circuit::plonky3_prover::{
    PROD_FRI_LOG_BLOWUP, PROD_FRI_LOG_FINAL_POLY_LEN, PROD_FRI_MAX_LOG_ARITY, PROD_FRI_NUM_QUERIES,
    PROD_FRI_QUERY_POW_BITS,
};

/// The conservative knob-drift MARGIN the deployed knobs must clear on the capacity arithmetic.
/// NOTE: 128 here is an engineering drift-detection margin, NOT a proven or conjecturally-safe
/// security level — the capacity conjecture is refuted (Kambiré). The proven floor is ~112.6
/// (structure-specific) / 73 (general Johnson), carried in the Lean tree. See the module header.
const CONJECTURED_FLOOR_BITS: usize = 128;

/// The floor on the PROVEN (Johnson / list-decoding-to-√rate) ledger — the figure that is proven
/// for ANY code, with no structure assumption and no refuted conjecture behind it.
///
/// **Derivation, not a guess:** `73` is exactly the deployed reading of `proven_bits` on BOTH
/// configs — IR-v2 `19·6/2 + 16 = 73`, v1 `38·3/2 + 16 = 73` — i.e. the security-parity point the
/// `(6, 19)` pin was measured at (`descriptor_ir2.rs::ir2_config`, `docs/PROOF-ECONOMICS.md` §2c,
/// `docs/reference/FRI-PARAM-FRONTIER.md` §1a). It is the general proven floor the system stands on
/// beneath the structure-specific ~112.6. Any drift BELOW it is a real reduction in the
/// no-assumptions guarantee and must be a named decision.
///
/// This floor is NOT redundant with `CONJECTURED_FLOOR_BITS`: `proven_floor_is_not_shadowed_by_
/// the_capacity_check` exhibits a knob set that clears capacity `128` and still fails this floor.
const PROVEN_JOHNSON_FLOOR_BITS: usize = 73;

/// **The Lean-MODELED wrap config** — `ir2LeafWrapConfig`
/// (`metatheory/Dregg2/Circuit/FriVerifier.lean:373-375`:
/// `{ logBlowup := 6, numQueries := 19, powBits := 16, maxLogArity := 3, logFinalPolyLen := 0,
/// extDeg := 4 }`), the config EVERY ~112.6 theorem is stated about.
///
/// The Lean pins its own three arithmetic knobs to these literals by `rfl` (`wrap_numQueries`,
/// `wrap_logBlowup`, `wrap_powBits` — `BabyBearFriDeployedInstance.lean` §1), and their doc-comments
/// claim they are "the shipped `IR2_FRI_*`" — but **nothing mechanically tied the Rust consts to the
/// Lean literals.** That claim was a doc-comment, not a proof. This const, plus the `ModelDrift`
/// arm of `check_budget`, is what makes it a checked fact: if a Rust knob drifts, the ~112.6
/// theorem is about a DIFFERENT object than the deployed prover, and this reds.
///
/// `extDeg = 4` is the remaining un-pinned modeled parameter: it lives in Rust as a TYPE
/// (`plonky3_prover.rs:63`, `type EF = BinomialExtensionField<P3BabyBear, 4>`), not an exported
/// `usize`, so there is no const to compare. NAMED, not silently dropped.
const LEAN_WRAP_MODEL: FriKnobs = FriKnobs {
    name: IR2_CONFIG_NAME,
    log_blowup: 6,
    log_final_poly_len: 0,
    max_log_arity: 3,
    num_queries: 19,
    query_pow_bits: 16,
};

/// The name identifying the IR-v2 wrap config — the one the Lean models.
const IR2_CONFIG_NAME: &str = "ir2_config";

/// The modeled structural pair, required of BOTH deployed configs.
///
/// **Honest derivation.** These are NOT derived from a soundness formula — no formula in this tree
/// or in the Lean uses them (module header). They are pinned by EQUALITY to the values the Lean
/// wrap model declares (`ir2LeafWrapConfig`) and that both deployed configs already carry. The pin
/// is a DRIFT CANARY with a specific job: while the arity-8-vs-arity-2 model residual (header) is
/// open, a move of these knobs must be a deliberate decision that revisits the Lean model — not a
/// silent edit. Inventing a numeric bound for them would be dishonest; this is what is justified.
const MODELED_MAX_LOG_ARITY: usize = 3;
const MODELED_LOG_FINAL_POLY_LEN: usize = 0;

/// The five deployed FRI knobs of one config — the whole surface a config edit can move.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FriKnobs {
    name: &'static str,
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    query_pow_bits: usize,
}

/// Capacity-ledger FRI arithmetic: `~log_blowup` bits per query, plus query-PoW. The capacity
/// conjecture this rests on is REFUTED (Kambiré) — this is a knob-drift baseline, not a security
/// claim; the proven number is `wrap_perFold_soundness_capacity`'s ~112.6.
fn conjectured_bits(log_blowup: usize, num_queries: usize, pow_bits: usize) -> usize {
    num_queries * log_blowup + pow_bits
}

/// Proven (Johnson / list-decoding-to-√rate) FRI soundness: `~log_blowup/2` bits per query,
/// plus query-PoW (integer floor — the reported figure rounds down, never up).
fn proven_bits(log_blowup: usize, num_queries: usize, pow_bits: usize) -> usize {
    num_queries * log_blowup / 2 + pow_bits
}

/// Why a knob set was refused — the typed reason, so a caller (and the non-vacuity gates below) can
/// assert WHICH tooth fired rather than that something went wrong.
#[derive(Debug, PartialEq, Eq)]
enum BudgetRefusal {
    /// The capacity ledger fell under the drift margin.
    BelowFloor {
        name: &'static str,
        got: usize,
        floor: usize,
    },
    /// The PROVEN (Johnson) ledger fell under its floor — a real reduction in the
    /// no-assumptions guarantee, independent of the refuted capacity column.
    ProvenBelowFloor {
        name: &'static str,
        got: usize,
        floor: usize,
    },
    /// A knob drifted off the Lean-MODELED config the ~112.6 soundness chain is stated about.
    /// Carries the knob NAME so a canary can assert the right tooth fired.
    ModelDrift {
        name: &'static str,
        knob: &'static str,
        got: usize,
        modeled: usize,
    },
    /// The two deployed configs disagree on `(conjectured, proven)` — a security-parity break.
    ParityBreak {
        left: (usize, usize),
        right: (usize, usize),
    },
}

/// **THE GATE ITSELF**, over the knobs it is handed rather than over the consts it closes on.
///
/// This is a plain function, not a `#[test]` body, for one reason: a `const` cannot be perturbed, so
/// a gate that reads `PROD_FRI_*` inline is unfalsifiable by any test — which is exactly how
/// `budget_gate_reds_a_degraded_config` came to assert `20 < 128` and never invoke the gate at all
/// (CRATE-EXCELLENCE-PLAN S8). With the knobs as parameters, `budget_gate_reds_each_degraded_knob`
/// can hand it PERTURBED DEPLOYED values and require the real gate to red.
///
/// Check ORDER is load-bearing and deliberate: the two arithmetic floors run BEFORE the model pin,
/// so a halved `log_blowup`/`num_queries`/`query_pow_bits` still reports the floor it broke (the
/// sharpest available reason) rather than the model pin it also breaks.
fn check_budget(configs: [FriKnobs; 2]) -> Result<(), BudgetRefusal> {
    let mut ledgers = Vec::new();
    for cfg in configs {
        let conj = conjectured_bits(cfg.log_blowup, cfg.num_queries, cfg.query_pow_bits);
        let prov = proven_bits(cfg.log_blowup, cfg.num_queries, cfg.query_pow_bits);

        // ── The capacity drift canary (KEPT, unchanged, honestly labeled — see the header).
        if conj < CONJECTURED_FLOOR_BITS {
            return Err(BudgetRefusal::BelowFloor {
                name: cfg.name,
                got: conj,
                floor: CONJECTURED_FLOOR_BITS,
            });
        }

        // ── The PROVEN (Johnson) floor. Not implied by the capacity floor: at `pow = 16`, capacity
        //    `128` only forces `q·lb ≥ 112`, i.e. proven `≥ 72` — one bit under this floor.
        if prov < PROVEN_JOHNSON_FLOOR_BITS {
            return Err(BudgetRefusal::ProvenBelowFloor {
                name: cfg.name,
                got: prov,
                floor: PROVEN_JOHNSON_FLOOR_BITS,
            });
        }

        // ── The structural pin, on BOTH configs. Equality, not an inequality: these knobs enter no
        //    soundness formula, so there is no bound to compare against — only the modeled value.
        if cfg.max_log_arity != MODELED_MAX_LOG_ARITY {
            return Err(BudgetRefusal::ModelDrift {
                name: cfg.name,
                knob: "max_log_arity",
                got: cfg.max_log_arity,
                modeled: MODELED_MAX_LOG_ARITY,
            });
        }
        if cfg.log_final_poly_len != MODELED_LOG_FINAL_POLY_LEN {
            return Err(BudgetRefusal::ModelDrift {
                name: cfg.name,
                knob: "log_final_poly_len",
                got: cfg.log_final_poly_len,
                modeled: MODELED_LOG_FINAL_POLY_LEN,
            });
        }

        // ── The WRAP config additionally equals the Lean-modeled config on its arithmetic knobs.
        //    This is what protects the ~112.6 posture: `|κ| = 2^log_blowup = 64` and `r = 2` (hence
        //    `C(64,2) = 2016`) are consequences of `log_blowup = 6`, so a `log_blowup` move that
        //    still clears both floors silently invalidates `wrap_perFold_soundness_capacity`.
        if cfg.name == LEAN_WRAP_MODEL.name {
            for (knob, got, modeled) in [
                ("log_blowup", cfg.log_blowup, LEAN_WRAP_MODEL.log_blowup),
                ("num_queries", cfg.num_queries, LEAN_WRAP_MODEL.num_queries),
                (
                    "query_pow_bits",
                    cfg.query_pow_bits,
                    LEAN_WRAP_MODEL.query_pow_bits,
                ),
            ] {
                if got != modeled {
                    return Err(BudgetRefusal::ModelDrift {
                        name: cfg.name,
                        knob,
                        got,
                        modeled,
                    });
                }
            }
        }

        ledgers.push((conj, prov));
    }
    if ledgers[0] != ledgers[1] {
        return Err(BudgetRefusal::ParityBreak {
            left: ledgers[0],
            right: ledgers[1],
        });
    }
    Ok(())
}

/// The DEPLOYED knob set, read from the production exports — the only input the live gate judges.
fn deployed() -> [FriKnobs; 2] {
    [
        FriKnobs {
            name: "v1 create_config",
            log_blowup: PROD_FRI_LOG_BLOWUP,
            log_final_poly_len: PROD_FRI_LOG_FINAL_POLY_LEN,
            max_log_arity: PROD_FRI_MAX_LOG_ARITY,
            num_queries: PROD_FRI_NUM_QUERIES,
            query_pow_bits: PROD_FRI_QUERY_POW_BITS,
        },
        FriKnobs {
            name: IR2_CONFIG_NAME,
            log_blowup: IR2_FRI_LOG_BLOWUP,
            log_final_poly_len: IR2_FRI_LOG_FINAL_POLY_LEN,
            max_log_arity: IR2_FRI_MAX_LOG_ARITY,
            num_queries: IR2_FRI_NUM_QUERIES,
            query_pow_bits: IR2_FRI_QUERY_POW_BITS,
        },
    ]
}

#[test]
fn deployed_fri_configs_clear_the_conjectured_floor() {
    for cfg in deployed() {
        eprintln!(
            "[{}] log_blowup={} queries={} query_pow={} max_log_arity={} log_final_poly_len={} \
             → conjectured {} bits, proven (Johnson) {} bits (both capped by the ~124-bit degree-4 \
             extension; the standing posture is the structure-specific ~112.6 of \
             wrap_perFold_soundness_capacity)",
            cfg.name,
            cfg.log_blowup,
            cfg.num_queries,
            cfg.query_pow_bits,
            cfg.max_log_arity,
            cfg.log_final_poly_len,
            conjectured_bits(cfg.log_blowup, cfg.num_queries, cfg.query_pow_bits),
            proven_bits(cfg.log_blowup, cfg.num_queries, cfg.query_pow_bits)
        );
    }
    if let Err(e) = check_budget(deployed()) {
        panic!(
            "DEPLOYED FRI KNOB DRIFT: {e:?}. A knob change dropped the deployed soundness floor, \
             broke security parity between the two configs, or moved the deployed config OFF the \
             Lean-modeled `ir2LeafWrapConfig` that `wrap_perFold_soundness_capacity`'s ~112.6-bit \
             posture is stated about — this must land as a deliberate, named decision, never a \
             silent downgrade. Re-run the FRI grid (`effect_vm_ir2_size_measure::ir2_fri_grid`) and \
             revisit `metatheory/Dregg2/Circuit/FriCorrelatedAgreementSharp.lean` §8 before \
             accepting it."
        );
    }
}

/// **PROOF THE GATE BITES — perturb the DEPLOYED consts and require the REAL gate to red.**
///
/// The predecessor (`budget_gate_reds_a_degraded_config`) asserted `conjectured_bits(1, 20, 0) < 128`
/// — i.e. that `20 < 128`. It evaluated the formula on a synthetic point it invented, never called
/// the gate it was named for, and would have passed unchanged if the gate's `assert!` had been
/// DELETED OUTRIGHT. It could not distinguish an armed gate from an absent one.
///
/// This walks each of the **5** gated knobs on each of the 2 deployed configs, degrades that ONE
/// knob from its real deployed value, and requires `check_budget` — the same function the live gate
/// calls — to refuse with a typed reason NAMING that knob. So it measures the gate's margin against
/// reality: if a deployed knob could be moved without a red, this test says so.
#[test]
fn budget_gate_reds_each_degraded_knob() {
    // ── HONEST POLE FIRST. The unperturbed deployed knobs must PASS. Without this every "the
    //    degraded config reds" assertion below is satisfied by a gate that refuses everything.
    assert_eq!(
        check_budget(deployed()),
        Ok(()),
        "the DEPLOYED knobs must clear the gate — otherwise the degradation assertions below are \
         vacuous (a gate that reds on everything reds on a degraded config too)"
    );

    // ── Degrade one knob at a time, from the DEPLOYED value, and require the real gate to red.
    for ci in 0..2 {
        for knob in 0..5 {
            let mut cfgs = deployed();
            let base = cfgs[ci];
            let name = base.name;

            // The perturbation per knob. Halving is the plausible "small edit" for the arithmetic
            // knobs. `log_final_poly_len` is DEPLOYED AT 0, so halving is a NO-OP and would make the
            // canary vacuous — it is raised to 4 instead, which is the real alternative the cost
            // grid measured (`docs/reference/FRI-PARAM-FRONTIER.md` §1a: "~-3% at 2⁴").
            let knob_name = match knob {
                0 => "log_blowup",
                1 => "num_queries",
                2 => "query_pow_bits",
                3 => "max_log_arity",
                _ => "log_final_poly_len",
            };
            match knob {
                0 => cfgs[ci].log_blowup = base.log_blowup / 2,
                1 => cfgs[ci].num_queries = base.num_queries / 2,
                2 => cfgs[ci].query_pow_bits = 0,
                3 => cfgs[ci].max_log_arity = base.max_log_arity / 2,
                _ => cfgs[ci].log_final_poly_len = 4,
            }
            assert_ne!(
                cfgs[ci], base,
                "the {knob_name} perturbation on [{name}] was a NO-OP — the canary below would be \
                 vacuous (it would be asserting that the DEPLOYED config reds)"
            );
            let d = cfgs[ci];
            let got_cap = conjectured_bits(d.log_blowup, d.num_queries, d.query_pow_bits);

            let refusal = match check_budget(cfgs) {
                Ok(()) => panic!(
                    "the gate ACCEPTED [{name}] with {knob_name} degraded — it does not red on a \
                     degraded deployed knob, so it is not protecting the floor it names. \
                     (capacity {}→{got_cap} bits)",
                    conjectured_bits(base.log_blowup, base.num_queries, base.query_pow_bits)
                ),
                Err(e) => e,
            };

            match knob {
                // ── The three ARITHMETIC knobs must trip the CAPACITY floor: they are the knobs
                //    that formula reads, and it is the sharpest tooth that sees them.
                0..=2 => match refusal {
                    BudgetRefusal::BelowFloor {
                        name: n,
                        got: g,
                        floor,
                    } => {
                        // Assert WHICH config and WHICH number — not merely that it refused. A
                        // refusal naming the other config, or a parity break, would mean the
                        // perturbation fired the wrong tooth and the knob under test is still
                        // ungated.
                        assert_eq!(n, name, "the floor tooth fired on the wrong config");
                        assert_eq!(
                            g, got_cap,
                            "the floor tooth reported a capacity it did not compute"
                        );
                        assert_eq!(floor, CONJECTURED_FLOOR_BITS);
                    }
                    other => panic!(
                        "degrading [{name}]'s {knob_name} to capacity {got_cap} bits did NOT trip \
                         the capacity floor ({CONJECTURED_FLOOR_BITS} bits) — it fired {other:?} \
                         instead. The floor is blind to this knob; another tooth caught it, and \
                         that tooth may not catch the same edit applied to BOTH configs."
                    ),
                },
                // ── The two STRUCTURAL knobs must trip the MODEL PIN, naming that knob. They enter
                //    no formula, so no floor can see them — this is the tooth that closes Move 5.
                _ => match refusal {
                    BudgetRefusal::ModelDrift {
                        name: n,
                        knob: k,
                        got,
                        modeled,
                    } => {
                        assert_eq!(n, name, "the model pin fired on the wrong config");
                        assert_eq!(
                            k, knob_name,
                            "the model pin fired, but naming the WRONG knob — a canary that cannot \
                             say which knob drifted cannot show {knob_name} is gated"
                        );
                        assert_eq!(got, if knob == 3 { d.max_log_arity } else { 4 });
                        assert_eq!(
                            modeled,
                            if knob == 3 {
                                MODELED_MAX_LOG_ARITY
                            } else {
                                MODELED_LOG_FINAL_POLY_LEN
                            }
                        );
                    }
                    other => panic!(
                        "moving [{name}]'s {knob_name} off the modeled value did NOT trip the model \
                         pin — it fired {other:?} instead. {knob_name} enters no soundness formula, \
                         so if the model pin does not see it, NOTHING does: it can drift silently."
                    ),
                },
            }
        }
    }
}

/// **THE PROVEN FLOOR IS LOAD-BEARING, NOT SHADOWED BY THE CAPACITY CHECK.**
///
/// A floor that only ever fires when a louder floor has already fired is decorative. This exhibits
/// the gap explicitly: at `pow = 16`, capacity `≥ 128` only forces `q·lb ≥ 112`, hence proven
/// `≥ 72` — ONE BIT under `PROVEN_JOHNSON_FLOOR_BITS`. So `(lb, q) = (8, 14)` reads capacity `128`
/// (CLEARS the capacity floor) and proven `72` (FAILS this one), and only `ProvenBelowFloor` can
/// catch it. Without this test the new floor could be deleted with every other test still green.
#[test]
fn proven_floor_is_not_shadowed_by_the_capacity_check() {
    // The witness: clears capacity, fails proven.
    let (lb, q, pow) = (8usize, 14usize, 16usize);
    assert_eq!(
        conjectured_bits(lb, q, pow),
        CONJECTURED_FLOOR_BITS,
        "the witness must CLEAR the capacity floor — otherwise it proves nothing about the proven \
         floor being independently load-bearing"
    );
    assert_eq!(proven_bits(lb, q, pow), PROVEN_JOHNSON_FLOOR_BITS - 1);

    // Apply it to the WRAP config's peer (v1), so the wrap model pin is not what fires.
    let mut cfgs = deployed();
    cfgs[0].log_blowup = lb;
    cfgs[0].num_queries = q;
    cfgs[0].query_pow_bits = pow;

    match check_budget(cfgs) {
        Err(BudgetRefusal::ProvenBelowFloor { name, got, floor }) => {
            assert_eq!(name, "v1 create_config");
            assert_eq!(got, PROVEN_JOHNSON_FLOOR_BITS - 1);
            assert_eq!(floor, PROVEN_JOHNSON_FLOOR_BITS);
        }
        other => panic!(
            "a config reading capacity {CONJECTURED_FLOOR_BITS} (clears) / proven {} (fails) did \
             not trip the PROVEN floor — got {other:?}. The proven floor is not doing any work: \
             delete it or arm it.",
            PROVEN_JOHNSON_FLOOR_BITS - 1
        ),
    }
}

/// **THE MODEL PIN CATCHES ~112.6-BREAKING DRIFT THAT BOTH FLOORS ACCEPT.**
///
/// This is the sharp half of Move 5. `wrap_perFold_soundness_capacity` proves `|Good| ≤ C(|κ|,2)`
/// with `|κ| = 2^log_blowup = 64` — the ~112.6 is a function of `log_blowup`, and RAISING
/// `log_blowup` GROWS the count (`C(128,2) = 8128`, ~3 bits worse) while IMPROVING both ledgers.
/// So `log_blowup: 6 → 8` on the wrap makes capacity (152) and proven (92) look BETTER while
/// silently taking the deployed prover off the config the Lean theorem is about. Only the model pin
/// sees it. Parity is also broken by this edit, so the pin must be checked BEFORE parity to name the
/// knob — this test proves it is.
#[test]
fn lean_model_pin_reds_wrap_drift_that_clears_both_floors() {
    let mut cfgs = deployed();
    let wrap = cfgs[1];
    assert_eq!(wrap.name, LEAN_WRAP_MODEL.name);
    cfgs[1].log_blowup = 8;
    let d = cfgs[1];

    // The perturbation must IMPROVE both ledgers — that is what makes the pin the only tooth.
    assert!(
        conjectured_bits(d.log_blowup, d.num_queries, d.query_pow_bits) >= CONJECTURED_FLOOR_BITS,
        "the witness must clear the capacity floor"
    );
    assert!(
        proven_bits(d.log_blowup, d.num_queries, d.query_pow_bits) >= PROVEN_JOHNSON_FLOOR_BITS,
        "the witness must clear the proven floor"
    );

    match check_budget(cfgs) {
        Err(BudgetRefusal::ModelDrift {
            name,
            knob,
            got,
            modeled,
        }) => {
            assert_eq!(name, IR2_CONFIG_NAME);
            assert_eq!(
                knob, "log_blowup",
                "the pin must name log_blowup — it is the knob the ~112.6 counting bound reads \
                 (|κ| = 2^log_blowup)"
            );
            assert_eq!(got, 8);
            assert_eq!(modeled, 6);
        }
        other => panic!(
            "moving the WRAP's log_blowup 6→8 — which IMPROVES both ledgers and so clears every \
             numeric floor — did not trip the Lean model pin; got {other:?}. The ~112.6 posture \
             (`wrap_perFold_soundness_capacity`, |Good| ≤ C(2^log_blowup, 2)) is then unprotected \
             against exactly the edit that looks like an upgrade."
        ),
    }
}

/// The deployed Rust consts EQUAL the Lean-modeled `ir2LeafWrapConfig` — the fact the Lean's
/// `wrap_numQueries` / `wrap_logBlowup` / `wrap_powBits` doc-comments ASSERT ("the shipped
/// `IR2_FRI_*`") but do not check. Lean pins its side by `rfl`; this pins ours. Without both, the
/// two literals can drift apart and every ~112.6 theorem quietly becomes a statement about a config
/// nobody runs.
#[test]
fn deployed_wrap_consts_equal_the_lean_modeled_config() {
    let wrap = deployed()[1];
    assert_eq!(wrap.name, LEAN_WRAP_MODEL.name);
    assert_eq!(
        wrap, LEAN_WRAP_MODEL,
        "the deployed IR-v2 knobs have drifted off `ir2LeafWrapConfig` \
         (metatheory/Dregg2/Circuit/FriVerifier.lean:373-375). Either revert the Rust knob or move \
         the Lean model AND re-derive `wrap_perFold_soundness_capacity` (§8 of \
         FriCorrelatedAgreementSharp.lean) at the new parameters — the ~112.6-bit posture is stated \
         about the Lean literals, not about whatever Rust ships."
    );
}
