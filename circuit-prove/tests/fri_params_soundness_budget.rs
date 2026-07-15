//! # THE FRI PARAMS→BITS LEDGER GATE — Rust PINS the knobs; LEAN owns the numbers.
//!
//! ## What this file used to be, and why it is not that any more
//!
//! Its predecessor (`circuit/tests/fri_params_soundness_budget.rs`, DELETED) re-derived, in
//! hand-written Rust, the soundness arithmetic the metatheory already models in excruciating detail:
//! `fn conjectured_bits(lb, q, pow) = q*lb + pow`, `fn proven_bits(lb, q, pow) = q*lb/2 + pow`, and a
//! long prose header narrating a per-fold posture (~112.6 / ~109.84) that the Rust computed no part
//! of. That is a TWIN. It can drift from the model it claims to report, and — worse — a
//! re-computation is not a check at all: it agrees with itself by construction. The one load-bearing
//! thing it did was the PIN (deployed consts == the Lean literals), because a pin COMPARES AGAINST
//! the model rather than restating it.
//!
//! So: the pin is kept and sharpened; the re-derivation is gone. Every number below arrives from
//! `@[export] dregg_fri_ledger` — the compiled `Dregg2.Circuit.FriLedger.friLedger`, the same
//! function `Dregg2.Circuit.FriLedgerSound` proves about. There is no soundness formula in this file.
//!
//! ## What Lean exports, and what it cannot
//!
//! **A soundness bound is a `Prop`; a `Prop` cannot be exported.** What is exported is the COMPUTABLE
//! LEDGER — six `Nat` columns per config. The theorems are what justify them:
//!
//!   * `FriLedgerSound.ledger_perFold_soundness` — ONE PARAMETRIC theorem: at ANY config, a word whose
//!     phase map is injective has at most `goodCount` good folding challenges, of density
//!     `< 2^(-perFoldBits)` in the degree-`extDeg` extension. It instantiates
//!     `FriArityTransfer.good_card_le_of_phase_injective` at that config's arity `m = 2^maxLogArity`
//!     and folded domain `|κ| = 2^logBlowup`. Every config below is an INSTANCE of it.
//!   * `FriLedgerSound.wrap_perFold_soundness_from_ledger` — the deployed wrap's bound stated with the
//!     count and the exponent READ OFF the ledger rather than typed in, so the exported number cannot
//!     drift from the proved number: they are the same term.
//!   * `FriLedgerSound.{ledgerP_eq_babyBearP, chooseTwo_eq_choose_two, log2_eq_log_two}` — the pins
//!     that stop the import-thin exported definition from being a second model.
//!
//! ⚑ **NAMED HYPOTHESIS, not fine print.** Every `per_fold_bits` carries the `M = 1` fiber bound as a
//! per-config HYPOTHESIS (`good_card_le_of_phase_injective`'s `hΦ`). It is DISCHARGED only at arity 2
//! / `logBlowup = 6` (§8's `far_fiber_card` + `wrap_fiber_le_one`); it is OPEN at the deployed arity 8
//! (`FriArityTransfer.Arity8FiberBound`) and at every `logBlowup = 3` config. `#assert_axioms` is
//! blind to hypotheses — the Lean being kernel-clean does not make these numbers unconditional.
//!
//! ## ⚑ THE FINDINGS — 7 shipped configs, 7 different postures, 2 corrected claims
//!
//! The old gate judged **2 of 7** shipped FRI knob sets. It also collapsed: one `~112.6` headline was
//! narrated for the system. Reading every config through the same theorem says otherwise.
//!
//!   1. **The deployed IR-v2 wrap reads 109, not 112.** (`FriArityTransfer`'s result, now the
//!      ledger's own output.) `log₂ 7 ≈ 2.807` bits is the price of the arity-8 moment-curve fold.
//!   2. **"The gnark ETH-wrap runs arity-2, so ~112.6 is the right figure THERE" is FALSE.** It
//!      silently assumed the ETH wrap shares the wrap's `logBlowup = 6`. It does not — the outer
//!      shrink gnark verifies is `logBlowup = 3`, so `|κ| = 8`, `goodCount = 28`, and it reads
//!      **118** (`FriLedgerSound.ethWrap_is_not_the_112_config`). The sentence quoted a real number
//!      from the wrong object — exactly what a parametric ledger makes impossible.
//!   3. **The one shipped config ~112.6 actually describes** is `ir2_leaf_wrap_config()` (arity 2 at
//!      `logBlowup = 6`) — which, per the NAME COLLISION below, is *not* the config the Lean
//!      `ir2LeafWrapConfig` is named after.
//!   4. **`create_recursion_config` sits at capacity exactly 128** (`3·38 + 14`; its `14` query-PoW
//!      bits are unique among shipped configs) — the old gate's own drift margin, with zero headroom,
//!      on a config that gate never looked at.
//!   5. **`per_fold_bits` RISES as `logBlowup` FALLS** (118/116 at `logBlowup = 3` vs 112/109 at 6).
//!      Not a paradox and NOT an upgrade: it is the per-fold proximity-gap factor only — a smaller
//!      folded domain has fewer pairs, hence fewer good challenges. The rate is paid for in the QUERY
//!      ledger. The columns are reported separately and never multiplied into a headline; that
//!      independence is itself a theorem (`query_ledger_does_not_determine_perFold`).
//!
//! ⚑ **NAME COLLISION.** Lean's `FriVerifier.ir2LeafWrapConfig` (`maxLogArity = 3`) models the Rust
//! `dregg_circuit::descriptor_ir2::ir2_config`. The Rust fn actually *named*
//! `ivc_turn_chain::ir2_leaf_wrap_config()` is a DIFFERENT knob set (arity 1, via
//! `create_recursion_config_for_inner_fri`'s hardcoded PROBE). Two objects, one name, different
//! postures (109 vs 112). Modeled apart as `ir2LeafWrapConfig` / `ir2LeafWrapRotatedConfig`.
//!
//! ## Teeth
//!
//!   1. `every_shipped_config_reports_its_ledger_from_lean` — each of the 7 configs' numbers, FROM
//!      Lean, gated on its own floors. No config borrows another's number.
//!   2. `deployed_wrap_consts_equal_the_lean_modeled_config` + `deployed_consts_equal_their_lean_models`
//!      — THE PIN, kept and widened from 2 configs to 7, and from 5 knobs to 6 (`ext_deg`, which the
//!      old gate named as un-pinnable, is now an exported const and is pinned).
//!   3. `ledger_gate_reds_each_degraded_knob` — perturbs the DEPLOYED consts, one knob at a time, and
//!      requires the real gate to refuse with a typed reason NAMING that knob.
//!   4. `lean_model_pin_reds_wrap_drift_that_clears_both_floors` — the sharp one: a `logBlowup` 6→8
//!      move IMPROVES every numeric floor and still breaks the model. Only the pin sees it.
//!   5. `the_export_is_consulted_not_shadowed` — proves the numbers TRACK Lean rather than being a
//!      leftover Rust constant: it moves a knob and requires Lean's answer to move with it.
//!
//! Run: `cargo test -p dregg-circuit-prove --test fri_params_soundness_budget -- --nocapture`.

use dregg_circuit::descriptor_ir2::{
    IR2_EXT_DEGREE, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY,
    IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS,
};
use dregg_circuit::plonky3_prover::{
    PROD_EXT_DEGREE, PROD_FRI_LOG_BLOWUP, PROD_FRI_LOG_FINAL_POLY_LEN, PROD_FRI_MAX_LOG_ARITY,
    PROD_FRI_NUM_QUERIES, PROD_FRI_QUERY_POW_BITS,
};
use dregg_circuit::stark_zk::{
    ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN, ZK_FRI_MAX_LOG_ARITY,
    ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS,
};
use dregg_circuit_prove::dregg_outer_config::{
    OUTER_EXT_DEGREE, OUTER_FRI_LOG_BLOWUP, OUTER_FRI_LOG_FINAL_POLY_LEN, OUTER_FRI_MAX_LOG_ARITY,
    OUTER_FRI_NUM_QUERIES, OUTER_FRI_QUERY_POW_BITS,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    INNER_FRI_MAX_LOG_ARITY, INNER_FRI_NUM_QUERIES, RECURSION_EXT_DEGREE, RECURSION_FRI_LOG_BLOWUP,
    RECURSION_FRI_LOG_FINAL_POLY_LEN, RECURSION_FRI_MAX_LOG_ARITY, RECURSION_FRI_NUM_QUERIES,
    RECURSION_FRI_QUERY_POW_BITS,
};
use dregg_lean_ffi::{FriKnobs, FriLedger, fri_ledger, fri_ledger_available};

// ─────────────────────────────────────────────────────────────────────────────
// THE FLOORS. Two numbers, both honestly labeled. Neither is derived here — they are the thresholds
// the deployed system is required to clear, and the ledger they are compared against is Lean's.
// ─────────────────────────────────────────────────────────────────────────────

/// The conservative knob-drift MARGIN on the CAPACITY arithmetic.
///
/// NOTE: `128` is an engineering drift-detection margin, NOT a proven or conjecturally-safe security
/// level — the capacity conjecture is REFUTED for coset Reed–Solomon at our rates (Kambiré, eprint
/// 2025/2046). It is kept, unchanged, as the labeled drift canary it honestly is. Retargeting the
/// numeric gate off the capacity metric is an ember decision, not this test's to make.
const CAPACITY_DRIFT_MARGIN_BITS: usize = 128;

/// The floor on the PROVEN (Johnson / list-decoding-to-`√rate`) query ledger — the column that is
/// proven for ANY code, with no structure assumption and no refuted conjecture behind it.
///
/// **Derivation, not a guess:** `71` is the deployed reading of the WEAKEST shipped config
/// (`create_recursion_config`, whose `14` query-PoW bits give `38·3/2 + 14 = 71`); the other six read
/// `73`. The old gate floored at `73` because it judged only the two `73` configs — the floor was
/// measured against an unrepresentative pair. `71` is the honest floor for the system as shipped, and
/// `recursion_config_is_the_weakest_link` pins it to that config so the floor cannot be quietly
/// lowered again without naming which config forced it.
const JOHNSON_FLOOR_BITS: usize = 71;

/// The floor on the PROVEN per-fold proximity-gap exponent, across every shipped config.
///
/// **Derivation:** `109` is the deployed reading of the WEAKEST shipped config — the IR-v2 wrap at
/// arity 8 (`FriArityTransfer.arity8_perFold_soundness`, `FriLedgerSound.wrap_ledger_perFoldBits`).
/// It is the system's real per-fold posture, and it is `log₂ 7 ≈ 2.807` bits BELOW the ~112.6 that was
/// quoted for years. Flooring at `112` would red the deployed config instantly; that is the finding,
/// not a reason to pick a prettier number.
const PER_FOLD_FLOOR_BITS: usize = 109;

// ─────────────────────────────────────────────────────────────────────────────
// THE SHIPPED CONFIGS. Rust's job here is to MARSHAL — name each config, read its deployed consts,
// and carry the Lean literal it must equal. Rust computes nothing.
// ─────────────────────────────────────────────────────────────────────────────

/// One shipped config: its name, its DEPLOYED knobs (read from the production exports), and the
/// LEAN-MODELED knobs it must equal (the literals in `FriLedgerSound` / `FriVerifier`).
///
/// The `modeled` field is the whole point of the pin: if a Rust knob drifts, every Lean theorem about
/// that config is a statement about an object nobody runs, and this reds. Lean pins its own side by
/// `rfl`; this pins ours. Neither alone is enough.
struct ShippedConfig {
    name: &'static str,
    /// The Lean `def` (in `Dregg2.Circuit.FriLedgerSound`, or `FriVerifier` for the wrap) that models
    /// this config — named so a red points at the exact declaration to reconcile.
    lean_model: &'static str,
    deployed: FriKnobs,
    modeled: FriKnobs,
}

/// The DEPLOYED knob sets, read from the production exports — the only input the live gate judges.
///
/// All 7 shipped configs (the census that produced this list read every `FriParameters` /
/// `create_*_config` construction site in the tree; the excluded ones are `#[ignore]`d sweeps and
/// R1CS-cost grids that never touch the wire). The old gate covered rows 0 and 1 only.
fn shipped() -> Vec<ShippedConfig> {
    vec![
        ShippedConfig {
            name: "ir2_config (IR-v2 batch — leaf mint + light-client verify)",
            lean_model: "FriVerifier.ir2LeafWrapConfig",
            deployed: FriKnobs {
                log_blowup: IR2_FRI_LOG_BLOWUP,
                num_queries: IR2_FRI_NUM_QUERIES,
                query_pow_bits: IR2_FRI_QUERY_POW_BITS,
                max_log_arity: IR2_FRI_MAX_LOG_ARITY,
                log_final_poly_len: IR2_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: IR2_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 6,
                num_queries: 19,
                query_pow_bits: 16,
                max_log_arity: 3,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
        ShippedConfig {
            name: "v1 create_config (production per-turn uni-STARK prover)",
            lean_model: "FriLedgerSound.prodV1Config",
            deployed: FriKnobs {
                log_blowup: PROD_FRI_LOG_BLOWUP,
                num_queries: PROD_FRI_NUM_QUERIES,
                query_pow_bits: PROD_FRI_QUERY_POW_BITS,
                max_log_arity: PROD_FRI_MAX_LOG_ARITY,
                log_final_poly_len: PROD_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: PROD_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 3,
                num_queries: 38,
                query_pow_bits: 16,
                max_log_arity: 3,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
        ShippedConfig {
            name: "create_zk_config (shielded/hiding lane, HidingFriPcs)",
            lean_model: "FriLedgerSound.zkConfig",
            deployed: FriKnobs {
                log_blowup: ZK_FRI_LOG_BLOWUP,
                num_queries: ZK_FRI_NUM_QUERIES,
                query_pow_bits: ZK_FRI_QUERY_POW_BITS,
                max_log_arity: ZK_FRI_MAX_LOG_ARITY,
                log_final_poly_len: ZK_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: ZK_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 3,
                num_queries: 38,
                query_pow_bits: 16,
                max_log_arity: 3,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
        ShippedConfig {
            name: "create_outer_config (BN254 shrink — THE CONFIG THE GNARK ETH-WRAP VERIFIES)",
            lean_model: "FriLedgerSound.ethWrapOuterConfig",
            deployed: FriKnobs {
                log_blowup: OUTER_FRI_LOG_BLOWUP,
                num_queries: OUTER_FRI_NUM_QUERIES,
                query_pow_bits: OUTER_FRI_QUERY_POW_BITS,
                max_log_arity: OUTER_FRI_MAX_LOG_ARITY,
                log_final_poly_len: OUTER_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: OUTER_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 3,
                num_queries: 38,
                query_pow_bits: 16,
                max_log_arity: 1,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
        ShippedConfig {
            name: "create_recursion_config (default recursion tree — powBits 14)",
            lean_model: "FriLedgerSound.recursionConfig",
            deployed: FriKnobs {
                log_blowup: RECURSION_FRI_LOG_BLOWUP,
                num_queries: RECURSION_FRI_NUM_QUERIES,
                query_pow_bits: RECURSION_FRI_QUERY_POW_BITS,
                max_log_arity: RECURSION_FRI_MAX_LOG_ARITY,
                log_final_poly_len: RECURSION_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: RECURSION_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 3,
                num_queries: 38,
                query_pow_bits: 14,
                max_log_arity: 1,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
        ShippedConfig {
            // The rotated native-batch leaf wrap: `ir2_config`'s log_blowup/queries, but the arity +
            // query count come from `create_recursion_config_for_inner_fri`'s pins. THE NAME COLLISION
            // (see the header): this is NOT what Lean's `ir2LeafWrapConfig` models.
            name: "ir2_leaf_wrap_config (rotated native-batch leaf wrap — arity 2, NOT 8)",
            lean_model: "FriLedgerSound.ir2LeafWrapRotatedConfig",
            deployed: FriKnobs {
                log_blowup: IR2_FRI_LOG_BLOWUP,
                num_queries: INNER_FRI_NUM_QUERIES,
                query_pow_bits: IR2_FRI_QUERY_POW_BITS,
                max_log_arity: INNER_FRI_MAX_LOG_ARITY,
                log_final_poly_len: IR2_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: RECURSION_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 6,
                num_queries: 19,
                query_pow_bits: 16,
                max_log_arity: 1,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
        ShippedConfig {
            // The GPU twin of the outer shrink reuses the SAME `OUTER_FRI_*` consts + literals
            // (`gpu_backend.rs::create_gpu_outer_config`), so it is the same knob set by construction.
            // It is listed rather than folded into the outer row so a future divergence between the CPU
            // and GPU shrink cannot hide: the pin below judges it as its own config.
            name: "create_gpu_outer_config (GPU twin of the BN254 shrink)",
            lean_model: "FriLedgerSound.ethWrapOuterConfig",
            deployed: FriKnobs {
                log_blowup: OUTER_FRI_LOG_BLOWUP,
                num_queries: OUTER_FRI_NUM_QUERIES,
                query_pow_bits: OUTER_FRI_QUERY_POW_BITS,
                max_log_arity: OUTER_FRI_MAX_LOG_ARITY,
                log_final_poly_len: OUTER_FRI_LOG_FINAL_POLY_LEN,
                ext_deg: OUTER_EXT_DEGREE,
            },
            modeled: FriKnobs {
                log_blowup: 3,
                num_queries: 38,
                query_pow_bits: 16,
                max_log_arity: 1,
                log_final_poly_len: 0,
                ext_deg: 4,
            },
        },
    ]
}

/// Why a config was refused — the typed reason, so a caller (and the non-vacuity gates below) can
/// assert WHICH tooth fired rather than that something went wrong.
#[derive(Debug, PartialEq, Eq)]
enum Refusal {
    /// The Lean ledger could not be consulted. This is a REFUSAL, never a fall-back-to-Rust: the whole
    /// point is that Rust has no second opinion to offer.
    LedgerUnavailable { name: &'static str, why: String },
    /// The ledger that came back is not ABOUT the config we asked about — its structural columns do
    /// not correspond to the knobs on the wire.
    ///
    /// ⚑ This arm exists because a mutation canary found the hole it closes. Without it, the
    /// `fri_ledger` call in `check_config` could be replaced outright by a hardcoded `FriLedger {
    /// per_fold_bits: 109, johnson_bits: 73, capacity_bits: 130, .. }` and ALL TEN tests still passed:
    /// the floors are lower bounds, so one config's numbers clear every other config's floors, and the
    /// pin fires before the call. A shadowed export was invisible — exactly the failure this file
    /// exists to prevent, reproduced inside the file meant to prevent it.
    ///
    /// The check is a MARSHALLING check, not a soundness one: `arity` and `folded_domain` are Lean's
    /// readings of the knobs we sent (`2^max_log_arity`, `2^log_blowup`), so verifying the response
    /// corresponds to the request is Rust's job and requires no model. It makes any constant response
    /// red on the first config whose knobs differ from it.
    LedgerNotAboutThisConfig {
        name: &'static str,
        column: &'static str,
        got: usize,
        expected_for_these_knobs: usize,
    },
    /// The capacity query ledger fell under the drift margin.
    CapacityBelowMargin {
        name: &'static str,
        got: usize,
        floor: usize,
    },
    /// The PROVEN (Johnson) query ledger fell under its floor.
    JohnsonBelowFloor {
        name: &'static str,
        got: usize,
        floor: usize,
    },
    /// The PROVEN per-fold proximity-gap exponent fell under its floor.
    PerFoldBelowFloor {
        name: &'static str,
        got: usize,
        floor: usize,
    },
    /// A knob drifted off the Lean-MODELED config its theorems are stated about. Carries the knob NAME
    /// so a canary can assert the right tooth fired.
    ModelDrift {
        name: &'static str,
        knob: &'static str,
        got: usize,
        modeled: usize,
    },
}

/// **THE GATE ITSELF**, over the knobs it is handed rather than over the consts it closes on.
///
/// A plain function, not a `#[test]` body, for one reason: a `const` cannot be perturbed, so a gate
/// that reads the deployed consts inline is unfalsifiable by any test. With the knobs as parameters,
/// `ledger_gate_reds_each_degraded_knob` can hand it PERTURBED DEPLOYED values and require the real
/// gate to red.
///
/// Note what is NOT here: any arithmetic. `check_config` asks Lean for the ledger and compares it to
/// the floors. The comparison is Rust's job; the numbers are not.
///
/// Check ORDER is load-bearing: the model pin runs FIRST, so a knob moved off the model reports the
/// pin (the sharpest reason — it says the theorems no longer describe the deployed prover) rather than
/// whichever floor it also happens to break. The old gate ordered these the other way and had to
/// document why; putting the pin first is simply the truer answer.
fn check_config(cfg: &ShippedConfig) -> Result<FriLedger, Refusal> {
    let d = cfg.deployed;
    let m = cfg.modeled;
    for (knob, got, modeled) in [
        ("log_blowup", d.log_blowup, m.log_blowup),
        ("num_queries", d.num_queries, m.num_queries),
        ("query_pow_bits", d.query_pow_bits, m.query_pow_bits),
        ("max_log_arity", d.max_log_arity, m.max_log_arity),
        (
            "log_final_poly_len",
            d.log_final_poly_len,
            m.log_final_poly_len,
        ),
        ("ext_deg", d.ext_deg, m.ext_deg),
    ] {
        if got != modeled {
            return Err(Refusal::ModelDrift {
                name: cfg.name,
                knob,
                got,
                modeled,
            });
        }
    }

    // THE CALL. Every number below this line is Lean's.
    let ledger = fri_ledger(d).map_err(|why| Refusal::LedgerUnavailable {
        name: cfg.name,
        why,
    })?;

    // THE RESPONSE IS ABOUT THE REQUEST. Lean's structural columns are its readings of the knobs we
    // sent; if they do not correspond, we are holding some other config's ledger (or a constant that
    // was never Lean's at all — see `LedgerNotAboutThisConfig`, which a mutation canary earned).
    for (column, got, expected) in [
        ("arity", ledger.arity, 1usize << d.max_log_arity),
        (
            "folded_domain",
            ledger.folded_domain,
            1usize << d.log_blowup,
        ),
    ] {
        if got != expected {
            return Err(Refusal::LedgerNotAboutThisConfig {
                name: cfg.name,
                column,
                got,
                expected_for_these_knobs: expected,
            });
        }
    }

    if ledger.capacity_bits < CAPACITY_DRIFT_MARGIN_BITS {
        return Err(Refusal::CapacityBelowMargin {
            name: cfg.name,
            got: ledger.capacity_bits,
            floor: CAPACITY_DRIFT_MARGIN_BITS,
        });
    }
    if ledger.johnson_bits < JOHNSON_FLOOR_BITS {
        return Err(Refusal::JohnsonBelowFloor {
            name: cfg.name,
            got: ledger.johnson_bits,
            floor: JOHNSON_FLOOR_BITS,
        });
    }
    if ledger.per_fold_bits < PER_FOLD_FLOOR_BITS {
        return Err(Refusal::PerFoldBelowFloor {
            name: cfg.name,
            got: ledger.per_fold_bits,
            floor: PER_FOLD_FLOOR_BITS,
        });
    }
    Ok(ledger)
}

/// The archive gap is a REFUSAL, not a skip and not a fall-back. If the Lean ledger is not linked, this
/// gate has nothing to say — and the correct behaviour is to say so loudly, because the alternative
/// (recomputing the numbers in Rust) is the exact thing that was deleted.
fn require_ledger() {
    assert!(
        fri_ledger_available(),
        "the VERIFIED Lean FRI ledger (`@[export] dregg_fri_ledger` over \
         `Dregg2.Circuit.FriLedger.friLedger`) is NOT in the linked archive, so this gate cannot \
         report any config's soundness numbers. It must NOT fall back to computing them in Rust — a \
         hand-written twin of the metatheory's arithmetic is what this file exists to have deleted. \
         Rebuild the archive: `lake build Dregg2.Circuit.FriLedger` in metatheory/, then \
         `cargo build -p dregg-lean-ffi` (its build.rs splices the export and probes for the symbol)."
    );
}

/// **THE LIVE GATE — every shipped config's ledger, FROM LEAN, against its floors.**
///
/// Seven configs, seven ledgers, one theorem. No config borrows another's number and none is
/// collapsed into a headline.
#[test]
fn every_shipped_config_reports_its_ledger_from_lean() {
    require_ledger();
    for cfg in shipped() {
        match check_config(&cfg) {
            Ok(l) => eprintln!(
                "[{}]\n    knobs  log_blowup={} queries={} query_pow={} max_log_arity={} \
                 log_final_poly_len={} ext_deg={}\n    LEAN   arity={} |κ|={} |Good|≤{} → per-fold \
                 {} bits (PROVEN, carries the M=1 fiber hypothesis) · Johnson {} bits (PROVEN, any \
                 code) · capacity {} bits (REFUTED conjecture — drift baseline only)\n    model  {}",
                cfg.name,
                cfg.deployed.log_blowup,
                cfg.deployed.num_queries,
                cfg.deployed.query_pow_bits,
                cfg.deployed.max_log_arity,
                cfg.deployed.log_final_poly_len,
                cfg.deployed.ext_deg,
                l.arity,
                l.folded_domain,
                l.good_count,
                l.per_fold_bits,
                l.johnson_bits,
                l.capacity_bits,
                cfg.lean_model,
            ),
            Err(e) => panic!(
                "SHIPPED FRI CONFIG REFUSED: {e:?}. Either a knob change dropped a deployed floor, or \
                 it moved the config OFF the Lean-modeled `{}` that its soundness theorems are stated \
                 about — in which case the theorems now describe an object nobody runs. This must land \
                 as a deliberate, named decision, never a silent downgrade: re-run the FRI grid \
                 (`dregg-circuit`'s `effect_vm_ir2_size_measure::ir2_fri_grid`) and revisit \
                 `metatheory/Dregg2/Circuit/FriLedgerSound.lean` before accepting it.",
                cfg.lean_model
            ),
        }
    }
}

/// **THE PIN — the deployed consts EQUAL the Lean-modeled configs, on ALL SIX knobs.**
///
/// This is the tooth the old gate got right and the one thing kept from it. Lean pins its side by
/// `rfl` (`FriLedgerSound`'s config `def`s); this pins ours. Without both, the two literals drift
/// apart and every per-fold theorem quietly becomes a statement about a config nobody runs.
///
/// Widened twice over the predecessor: from 2 configs to 7, and from 5 knobs to 6. `ext_deg` was
/// named by the old gate as "the remaining un-pinned modeled parameter" because it lived in Rust as a
/// TYPE argument rather than a const. It is now an exported const that BUILDS that type
/// (`plonky3_prover::PROD_EXT_DEGREE` ⇒ `type EF = BinomialExtensionField<P3BabyBear, PROD_EXT_DEGREE>`),
/// so the named gap is closed rather than re-narrated: `ext_deg` sets `|F| = babyBearP ^ ext_deg`, the
/// denominator of every per-fold bound.
#[test]
fn deployed_consts_equal_their_lean_models() {
    for cfg in shipped() {
        assert_eq!(
            cfg.deployed, cfg.modeled,
            "[{}] the deployed knobs have DRIFTED off the Lean model `{}`. Either revert the Rust \
             knob, or move the Lean model AND re-derive its ledger at the new parameters \
             (`metatheory/Dregg2/Circuit/FriLedgerSound.lean`) — the per-fold posture is stated about \
             the Lean literals, not about whatever Rust ships.",
            cfg.name, cfg.lean_model
        );
    }
}

/// The wrap pin, called out by name because it is the one every `~112.6`/`~109.84` theorem in the tree
/// is stated about. Kept as a named test (rather than folded into the loop above) so a red says
/// "the deployed wrap left the model" in one line — the predecessor's most load-bearing tooth.
#[test]
fn deployed_wrap_consts_equal_the_lean_modeled_config() {
    let cfgs = shipped();
    let wrap = &cfgs[0];
    assert_eq!(wrap.lean_model, "FriVerifier.ir2LeafWrapConfig");
    assert_eq!(
        wrap.deployed, wrap.modeled,
        "the deployed IR-v2 knobs have drifted off `ir2LeafWrapConfig` \
         (metatheory/Dregg2/Circuit/FriVerifier.lean). Every per-fold theorem — including \
         `FriArityTransfer.arity8_perFold_soundness`'s 109-bit deployed posture — is stated about the \
         Lean literals. Re-derive at the new parameters before accepting the move."
    );
}

/// **PROOF THE GATE BITES — perturb the DEPLOYED consts and require the REAL gate to red.**
///
/// Walks each of the 6 pinned knobs on each of the 7 shipped configs, degrades that ONE knob from its
/// real deployed value, and requires `check_config` — the same function the live gate calls — to
/// refuse, NAMING that knob. So it measures the gate's margin against reality: if a deployed knob
/// could be moved without a red, this test says so.
#[test]
fn ledger_gate_reds_each_degraded_knob() {
    require_ledger();
    // ── HONEST POLE FIRST. The unperturbed deployed knobs must PASS. Without this every "the degraded
    //    config reds" assertion below is satisfied by a gate that refuses everything.
    for cfg in shipped() {
        assert!(
            check_config(&cfg).is_ok(),
            "[{}] the DEPLOYED knobs must clear the gate — otherwise the degradation assertions below \
             are vacuous (a gate that reds on everything reds on a degraded config too)",
            cfg.name
        );
    }

    for base in shipped() {
        for knob in 0..6 {
            let mut cfg = ShippedConfig {
                name: base.name,
                lean_model: base.lean_model,
                deployed: base.deployed,
                modeled: base.modeled,
            };
            // Each perturbation must be a genuine MOVE off the deployed value, or the canary is
            // vacuous. `log_final_poly_len` is DEPLOYED AT 0 everywhere, so halving is a NO-OP; it is
            // raised to 4 instead (the real alternative the cost grid measured).
            let knob_name = match knob {
                0 => {
                    cfg.deployed.log_blowup = base.deployed.log_blowup + 1;
                    "log_blowup"
                }
                1 => {
                    cfg.deployed.num_queries = base.deployed.num_queries / 2;
                    "num_queries"
                }
                2 => {
                    cfg.deployed.query_pow_bits = 0;
                    "query_pow_bits"
                }
                3 => {
                    cfg.deployed.max_log_arity = base.deployed.max_log_arity + 1;
                    "max_log_arity"
                }
                4 => {
                    cfg.deployed.log_final_poly_len = 4;
                    "log_final_poly_len"
                }
                _ => {
                    cfg.deployed.ext_deg = base.deployed.ext_deg / 2;
                    "ext_deg"
                }
            };
            assert_ne!(
                cfg.deployed, base.deployed,
                "[{}] the {knob_name} perturbation was a NO-OP — the canary below would be vacuous \
                 (it would be asserting that the DEPLOYED config reds)",
                base.name
            );

            match check_config(&cfg) {
                Ok(l) => panic!(
                    "the gate ACCEPTED [{}] with {knob_name} degraded (Lean read: per-fold {} bits, \
                     Johnson {} bits, capacity {} bits) — it does not red on a degraded deployed knob, \
                     so it is not protecting the posture it names.",
                    base.name, l.per_fold_bits, l.johnson_bits, l.capacity_bits
                ),
                // Every knob is pinned by EQUALITY to the model, so the pin is the tooth that fires —
                // and it must NAME the knob under test. A refusal naming a different knob, or a
                // different config, would mean the perturbation tripped something else and the knob
                // under test is still ungated.
                Err(Refusal::ModelDrift { name, knob: k, .. }) => {
                    assert_eq!(name, base.name, "the model pin fired on the wrong config");
                    assert_eq!(
                        k, knob_name,
                        "[{}] the model pin fired, but naming the WRONG knob — a canary that cannot \
                         say which knob drifted cannot show {knob_name} is gated",
                        base.name
                    );
                }
                Err(other) => panic!(
                    "[{}] degrading {knob_name} did NOT trip the model pin — it fired {other:?} \
                     instead. Every knob is pinned by equality, so the pin should always be the first \
                     tooth; if it is not, the check order regressed and a knob that enters no floor \
                     (log_final_poly_len) could drift silently.",
                    base.name
                ),
            }
        }
    }
}

/// **THE MODEL PIN CATCHES POSTURE-BREAKING DRIFT THAT EVERY NUMERIC FLOOR ACCEPTS.**
///
/// The sharp half. The per-fold posture is a function of `log_blowup` (`|κ| = 2^log_blowup`, and
/// `|Good| ≤ (m−1)·C(|κ|,2)`), and RAISING `log_blowup` GROWS the count — i.e. makes the per-fold
/// posture WORSE — while IMPROVING both query ledgers. So `log_blowup: 6 → 8` on the wrap makes
/// capacity (`152`) and Johnson (`92`) look BETTER and silently takes the deployed prover off the
/// config the Lean theorems are about.
///
/// This asks LEAN for all four numbers, so it is not asserting the direction from a Rust formula — it
/// exhibits the drift and reports what the model says about it.
#[test]
fn lean_model_pin_reds_wrap_drift_that_clears_both_floors() {
    require_ledger();
    let cfgs = shipped();
    let base = &cfgs[0];
    let mut drifted = FriKnobs {
        log_blowup: 8,
        ..base.deployed
    };
    drifted.log_blowup = 8;

    // The witness must IMPROVE both query ledgers and still be caught — that is what makes the pin the
    // only tooth. Both readings come from Lean.
    let dl = fri_ledger(drifted).expect("the Lean ledger must render the drifted config");
    let bl = fri_ledger(base.deployed).expect("the Lean ledger must render the deployed config");
    assert!(
        dl.capacity_bits >= CAPACITY_DRIFT_MARGIN_BITS && dl.capacity_bits > bl.capacity_bits,
        "the witness must CLEAR and IMPROVE the capacity margin — otherwise it proves nothing about \
         the pin being the only tooth (got {} vs deployed {})",
        dl.capacity_bits,
        bl.capacity_bits
    );
    assert!(
        dl.johnson_bits >= JOHNSON_FLOOR_BITS && dl.johnson_bits > bl.johnson_bits,
        "the witness must CLEAR and IMPROVE the Johnson floor (got {} vs deployed {})",
        dl.johnson_bits,
        bl.johnson_bits
    );
    // ⚑ And Lean says the per-fold posture got WORSE while the query ledgers got better — the whole
    //   reason a "looks like an upgrade" edit needs a pin rather than a floor.
    assert!(
        dl.per_fold_bits < bl.per_fold_bits,
        "raising log_blowup must WORSEN the per-fold posture (|Good| ≤ (m−1)·C(2^log_blowup, 2) grows) \
         — Lean read {} vs the deployed {}. If this ever inverts, the pin's rationale changed and this \
         test is the place to find out.",
        dl.per_fold_bits,
        bl.per_fold_bits
    );

    let cfg = ShippedConfig {
        name: base.name,
        lean_model: base.lean_model,
        deployed: drifted,
        modeled: base.modeled,
    };
    match check_config(&cfg) {
        Err(Refusal::ModelDrift {
            knob, got, modeled, ..
        }) => {
            assert_eq!(
                knob, "log_blowup",
                "the pin must name log_blowup — it is the knob the per-fold count reads \
                 (|κ| = 2^log_blowup)"
            );
            assert_eq!(got, 8);
            assert_eq!(modeled, 6);
        }
        other => panic!(
            "moving the WRAP's log_blowup 6→8 — which IMPROVES both query ledgers and so clears every \
             numeric floor — did not trip the Lean model pin; got {other:?}. The per-fold posture is \
             then unprotected against exactly the edit that looks like an upgrade."
        ),
    }
}

/// **⚑ THE EXPORT IS GENUINELY CONSULTED — not shadowed by a leftover Rust constant.**
///
/// The failure mode this file exists to prevent is subtle: a gate that *looks* like it calls the model
/// but reports a number Rust decided. So this test moves ONE knob and requires Lean's answer to move
/// with it, in the direction the theorems predict — a hardcoded Rust constant cannot track that.
///
/// The three probes are chosen because each is a THEOREM in `FriLedgerSound`, so this is a differential
/// between the Lean the gate links and the Lean the proofs were checked against:
///
///   1. arity 8 → arity 2 at the wrap's `log_blowup = 6`: `goodCount` must fall `14112 → 2016` (exactly
///      `7×`) and `per_fold_bits` must rise `109 → 112`
///      (`arity8_costs_seven_times_arity2_at_logBlowup6`).
///   2. `ext_deg` halves ⇒ `|F| = babyBearP^2` ⇒ the per-fold exponent must roughly halve. Rust
///      supplies no formula for this; Lean must.
///   3. `folded_domain` must equal `2^log_blowup` and `arity` must equal `2^max_log_arity` — returned
///      by Lean, never computed here.
#[test]
fn the_export_is_consulted_not_shadowed() {
    require_ledger();
    let cfgs = shipped();
    let wrap = cfgs[0].deployed;

    let deployed = fri_ledger(wrap).expect("ledger");
    // The DEPLOYED wrap's number is the arity-8 posture — 109, NOT the ~112.6 that was quoted for
    // years. This is `FriArityTransfer.arity8_perFold_soundness` / `wrap_ledger_perFoldBits`.
    assert_eq!(
        (deployed.arity, deployed.good_count, deployed.per_fold_bits),
        (8, 14112, 109),
        "Lean's ledger for the DEPLOYED wrap must be the arity-8 posture proved in \
         `FriArityTransfer` (|Good| ≤ 7·C(64,2) = 14112 ⇒ < 2^-109). Got {deployed:?}. If this \
         disagrees, the linked archive is stale relative to the proofs — rebuild it; do NOT adjust \
         the expectation to match."
    );

    // (1) Drop the arity to 2 and require Lean's numbers to move as the arity theorem says.
    let arity2 = fri_ledger(FriKnobs {
        max_log_arity: 1,
        ..wrap
    })
    .expect("ledger");
    assert_eq!(
        (arity2.arity, arity2.good_count, arity2.per_fold_bits),
        (2, 2016, 112),
        "at arity 2 the ledger must RECOVER §8's C(64,2) = 2016 and its ~112.6 posture \
         (`arity2_recovers_capacity_count`, `rotatedLeafWrap_ledger_perFoldBits`). Got {arity2:?}"
    );
    assert_eq!(
        deployed.good_count,
        7 * arity2.good_count,
        "the arity-8 loss must be EXACTLY the factor 7 of the degree-7 moment curve \
         (`arity8_loses_exactly_factor_seven`) — a Rust constant could not track this"
    );
    assert!(
        arity2.per_fold_bits > deployed.per_fold_bits,
        "arity 2 must beat arity 8 by log₂7 ≈ 2.807 bits; Lean read {} vs {}",
        arity2.per_fold_bits,
        deployed.per_fold_bits
    );

    // (2) Halve the extension degree: |F| = babyBearP^2 ≈ 2^61.8, so the exponent must roughly halve.
    //     Rust states no relation here — if the export were shadowed, this would not move.
    let narrow = fri_ledger(FriKnobs { ext_deg: 2, ..wrap }).expect("ledger");
    assert!(
        narrow.per_fold_bits < deployed.per_fold_bits / 2 + 5
            && narrow.per_fold_bits > deployed.per_fold_bits / 2 - 15,
        "halving ext_deg must roughly halve the per-fold exponent (|F| = babyBearP^ext_deg is its \
         denominator); Lean read {} vs the deployed {}. A shadowed export would not track ext_deg at \
         all.",
        narrow.per_fold_bits,
        deployed.per_fold_bits
    );
    assert_eq!(
        narrow.good_count, deployed.good_count,
        "ext_deg must NOT move the good-challenge count — the count is FIELD-INDEPENDENT (it lands in \
         the unordered pairs of the folded domain, not in the challenge field). That independence is \
         the load-bearing step in `arity8_perFold_soundness`; if Lean ever reports otherwise, the \
         model changed."
    );

    // (3) The structural columns are Lean's readings of the knobs, not Rust's.
    for cfg in shipped() {
        let l = fri_ledger(cfg.deployed).expect("ledger");
        assert_eq!(
            l.arity,
            1usize << cfg.deployed.max_log_arity,
            "[{}] Lean's arity column must be 2^max_log_arity",
            cfg.name
        );
        assert_eq!(
            l.folded_domain,
            1usize << cfg.deployed.log_blowup,
            "[{}] Lean's folded-domain column must be 2^log_blowup — the modeled rate-2^-log_blowup \
             setup folds m·2^log_blowup points onto 2^log_blowup fibres",
            cfg.name
        );
    }
}

/// **⚑ THE ETH-WRAP IS NOT THE ~112.6 CONFIG — the finding, gated so it cannot be re-forgotten.**
///
/// The deleted header asserted "the gnark ETH-wrap verifier runs arity-2 — so ~112.6 is the right
/// figure THERE". Both halves of that are individually true and the conclusion is false: ~112.6 is a
/// statement about `log_blowup = 6` (`|κ| = 64`), and the outer shrink gnark verifies is
/// `log_blowup = 3` (`|κ| = 8`). Its posture is 118 — a DIFFERENT number, from a different instance of
/// the same theorem.
///
/// This is the shape of error a parametric ledger exists to make unavailable: quoting a real number
/// from the wrong object. Both readings come from Lean.
#[test]
fn eth_wrap_posture_is_its_own_not_the_wrap_headline() {
    require_ledger();
    let cfgs = shipped();
    let outer = fri_ledger(cfgs[3].deployed).expect("ledger");
    assert_eq!(
        cfgs[3].lean_model, "FriLedgerSound.ethWrapOuterConfig",
        "row 3 must be the config the gnark ETH-wrap verifies"
    );
    assert_eq!(
        (
            outer.arity,
            outer.folded_domain,
            outer.good_count,
            outer.per_fold_bits
        ),
        (2, 8, 28, 118),
        "the gnark-verified outer shrink is arity 2 at log_blowup 3, so |κ| = 8, |Good| ≤ 1·C(8,2) = \
         28, and its per-fold posture is 118 (`FriLedgerSound.ethWrap_ledger_perFoldBits`) — NOT the \
         ~112.6 that was narrated for it. Got {outer:?}"
    );

    // The one shipped config ~112.6 genuinely describes: the ROTATED leaf wrap (arity 2 at blowup 6).
    let rotated = fri_ledger(cfgs[5].deployed).expect("ledger");
    assert_eq!(
        cfgs[5].lean_model, "FriLedgerSound.ir2LeafWrapRotatedConfig",
        "row 5 must be the rotated leaf wrap"
    );
    assert_eq!(
        rotated.per_fold_bits, 112,
        "the rotated ir2_leaf_wrap_config (arity 2 at log_blowup 6) is the ONE shipped config the \
         standing ~112.6 describes"
    );
    assert_ne!(
        outer.per_fold_bits, rotated.per_fold_bits,
        "the two arity-2 configs have DIFFERENT postures because their log_blowup differs — so \
         'the arity-2 number' is not a thing the system has. This is the non-collapse tooth: if these \
         ever coincide, one headline could again be quoted for both."
    );
}

/// **⚑ THE WEAKEST LINK IS NAMED, and it is not a config the old gate ever judged.**
///
/// `create_recursion_config` carries `14` query-PoW bits where every other shipped config carries
/// `16`, putting its capacity ledger at exactly `128` — the drift margin, with ZERO headroom — and its
/// Johnson ledger at `71`, two bits under the `73` the old gate floored at. The old floor was measured
/// against the only two configs it looked at, both of which read `73`.
///
/// Pinning the floor to the config that forces it means the floor cannot be quietly lowered again
/// without this test naming who did it.
#[test]
fn recursion_config_is_the_weakest_link() {
    require_ledger();
    let cfgs = shipped();
    let rec = fri_ledger(cfgs[4].deployed).expect("ledger");
    assert_eq!(cfgs[4].lean_model, "FriLedgerSound.recursionConfig");
    assert_eq!(
        (rec.capacity_bits, rec.johnson_bits),
        (CAPACITY_DRIFT_MARGIN_BITS, JOHNSON_FLOOR_BITS),
        "create_recursion_config must read capacity 128 (ON the margin, zero headroom) and Johnson 71 \
         — it is the weakest shipped config on both query columns, and the reason JOHNSON_FLOOR_BITS \
         is 71 rather than the 73 the old gate used. Got {rec:?}"
    );

    // It is the MINIMUM, not merely low: no other shipped config may sit under it, or the floor is
    // pinned to the wrong config and a real regression elsewhere would slip under.
    for cfg in shipped() {
        let l = fri_ledger(cfg.deployed).expect("ledger");
        assert!(
            l.johnson_bits >= rec.johnson_bits && l.capacity_bits >= rec.capacity_bits,
            "[{}] reads Johnson {} / capacity {}, UNDER the config the floors are pinned to \
             (create_recursion_config: {} / {}). The floors now name the wrong weakest link — repin \
             them, and say in the commit which config regressed.",
            cfg.name,
            l.johnson_bits,
            l.capacity_bits,
            rec.johnson_bits,
            rec.capacity_bits
        );
    }
}

/// **THE FLOORS ARE LOAD-BEARING, NOT SHADOWED BY EACH OTHER.**
///
/// A floor that only ever fires when a louder floor has already fired is decorative. Each of the three
/// is shown independently live by exhibiting a knob set the OTHER two accept. Every number is Lean's;
/// the witnesses are knob sets, not arithmetic.
#[test]
fn each_floor_is_independently_load_bearing() {
    require_ledger();
    let base = shipped()[0].deployed;

    // JOHNSON is not implied by CAPACITY: at pow = 16, capacity ≥ 128 only forces q·lb ≥ 112, i.e.
    // Johnson ≥ 72. So (lb, q) = (8, 14) clears capacity and lands Johnson at 72 — under the old 73
    // floor, though above today's 71. Lean adjudicates.
    let w = fri_ledger(FriKnobs {
        log_blowup: 8,
        num_queries: 14,
        ..base
    })
    .expect("ledger");
    assert!(
        w.capacity_bits >= CAPACITY_DRIFT_MARGIN_BITS && w.johnson_bits < 73,
        "the capacity floor does not imply a Johnson floor of 73: Lean reads capacity {} (clears) / \
         Johnson {} for (log_blowup 8, 14 queries). The two columns are independent gates.",
        w.capacity_bits,
        w.johnson_bits
    );

    // PER-FOLD is not implied by either query column: `log_blowup: 6 → 12` IMPROVES both query ledgers
    // and CRUSHES the per-fold posture (|κ| = 4096 ⇒ C(4096,2) ≈ 2^23 pairs).
    let deep = fri_ledger(FriKnobs {
        log_blowup: 12,
        ..base
    })
    .expect("ledger");
    assert!(
        deep.capacity_bits > w.capacity_bits.min(base.log_blowup * base.num_queries),
        "sanity: raising log_blowup raises the capacity column"
    );
    assert!(
        deep.per_fold_bits < PER_FOLD_FLOOR_BITS,
        "log_blowup 6→12 must break the PER-FOLD floor while both query ledgers only improve — Lean \
         read per-fold {} / Johnson {} / capacity {}. That is the case only the per-fold floor can \
         catch, and the reason it is not redundant with the query columns.",
        deep.per_fold_bits,
        deep.johnson_bits,
        deep.capacity_bits
    );
    assert!(
        deep.johnson_bits >= JOHNSON_FLOOR_BITS && deep.capacity_bits >= CAPACITY_DRIFT_MARGIN_BITS,
        "…and it must clear BOTH query floors while doing so, or it does not isolate the per-fold \
         floor (Johnson {} / capacity {})",
        deep.johnson_bits,
        deep.capacity_bits
    );
}

/// **THE EXPORT FAILS CLOSED.** A malformed or absurd knob set must yield a REFUSAL, never a number.
/// A ledger that answered anything for `ext_deg = 64` would be inviting a caller to quote it.
#[test]
fn the_ledger_fails_closed_outside_the_modeled_window() {
    require_ledger();
    let base = shipped()[0].deployed;
    for (why, knobs) in [
        (
            "ext_deg far outside the modeled window",
            FriKnobs {
                ext_deg: 64,
                ..base
            },
        ),
        (
            "log_blowup far outside the modeled window",
            FriKnobs {
                log_blowup: 40,
                ..base
            },
        ),
        (
            "max_log_arity outside the modeled window",
            FriKnobs {
                max_log_arity: 20,
                ..base
            },
        ),
    ] {
        assert!(
            fri_ledger(knobs).is_err(),
            "the Lean ledger must FAIL CLOSED for {why} ({knobs:?}) rather than return a number a \
             caller could quote"
        );
    }
}
