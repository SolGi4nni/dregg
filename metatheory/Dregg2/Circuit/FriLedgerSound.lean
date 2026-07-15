import Dregg2.Circuit.FriLedger
import Dregg2.Circuit.FriArityTransfer

/-!
# `FriLedgerSound` — why the `@[export]`ed `friLedger` numbers are TRUE

`Dregg2/Circuit/FriLedger.lean` carries the COMPUTABLE ledger and its `@[export]`; it is import-thin
so the FFI archive splice stays cheap. This file carries the PROOFS. It is deliberately NOT in the
splice set (it exports nothing) and so may import Mathlib freely.

Three jobs, in order:

1. **PIN the thin definitions to the modeled ones.** `ledgerP = babyBearP`, `chooseTwo n =
   Nat.choose n 2`, `Nat.log2 = Nat.log 2`. Without these the ledger would be a SECOND model wearing
   the first one's name — exactly the twin this whole exercise deleted from Rust. Each is `rfl` or a
   one-line Mathlib bridge, and each is CHECKED, not asserted in a comment.

2. **Prove the PARAMETRIC theorem.** `ledger_perFold_soundness` says: at ANY config, a word whose
   phase map is injective has at most `(friLedger cfg).goodCount` good folding challenges, and their
   density in the challenge field is `< 2 ^ (−(friLedger cfg).perFoldBits)`. This is ONE theorem,
   stated over the same `friLedger` the C-ABI runs — so the exported number cannot drift from the
   proved number: they are the same term.

3. **INSTANTIATE at every shipped config**, and report what comes out — including where it
   contradicts what we have said in prose.

## ⚑ THE FINDINGS, reported unmassaged

* **The deployed IR-v2 wrap (`logBlowup = 6`, arity `8`) reads `109`, not `112`.** This is
  `FriArityTransfer`'s ~109.84 result, now the ledger's own output rather than a prose paragraph
  beside it (`wrap_ledger_perFoldBits`, and `wrap_ledger_agrees_with_arity8_theorem` pins the
  ledger's `goodCount` to the `14112` that `arity8_perFold_soundness` is literally stated about).

* **"The gnark ETH-wrap runs arity 2, so ~112.6 is the right figure THERE" is FALSE.** That claim
  (`circuit/tests/fri_params_soundness_budget.rs`'s old header) silently assumed the ETH wrap shares
  the wrap's `logBlowup = 6`. It does not: the BN254-native shrink the gnark circuit verifies is
  `create_outer_config` at `logBlowup = 3` (`circuit-prove/src/dregg_outer_config.rs`), and the
  ~112.6 is a statement about `|κ| = 2^6 = 64`. At arity 2 AND `logBlowup = 3` the folded domain is
  `|κ| = 8`, so `goodCount = 1 · C(8,2) = 28` and the ledger reads **118**
  (`ethWrap_ledger_perFoldBits`). The old sentence quoted a number from the wrong config — which is
  precisely the failure mode a parametric ledger makes impossible.

* **`perFoldBits` RISES as `logBlowup` FALLS, and that is not a paradox.** It is the per-fold
  proximity-gap factor ONLY: a smaller folded domain has fewer pairs, hence fewer good challenges.
  The rate is paid for in the QUERY ledger (`johnsonBits` / `capacityBits`), which is where a worse
  rate shows up. The ledger reports the columns SEPARATELY and never multiplies them into a headline;
  any reader who wants "the" soundness of a config must read both columns and the query count.

## ⚑ THE NAMED HYPOTHESIS (this file does not discharge it, and does not pretend to)

Every per-fold number here carries `hΦ` — the `M = 1` fiber bound — as a HYPOTHESIS, inherited from
`FriArityTransfer.good_card_le_of_phase_injective`. It is DISCHARGED at `m = 2, logBlowup = 6` from
farness (`FriCorrelatedAgreementSharp` §8's `far_fiber_card` + `wrap_fiber_le_one` over the concrete
`friSetupWrapRate`) and is OPEN at every other config, including the deployed arity-8 wrap
(`FriArityTransfer.Arity8FiberBound`) and the `logBlowup = 3` configs (whose analogue needs the
`|L| = m·8`, `|κ| = 8` setup this tree does not build).

`#assert_axioms` is BLIND TO HYPOTHESES. The theorems below are kernel-clean; that is not the same as
hypothesis-free, and the `#assert_axioms` block at the bottom must not be read as if it were.
-/

namespace Dregg2.Circuit.FriLedgerSound

open Dregg2.Circuit.FriLedger
open Dregg2.Circuit.FriArityTransfer (H good_card_le_of_phase_injective)
open Dregg2.Circuit.BabyBearFriField (babyBearP)
open Dregg2.Circuit.FriVerifier (FriParams ir2LeafWrapConfig)

/-! ## §1. THE PINS — the thin core definitions ARE the modeled ones.

The `@[export]`ed `friLedger` uses core `Nat` operations so the archive splice stays cheap. That is a
build-cost decision and must not become a semantic one: each core operation is pinned here to the
Mathlib/metatheory object the theorems are stated over. If a pin ever breaks, the ledger is reporting
about a different model and this file goes red. -/

/-- **THE FIELD PIN.** The ledger's `ledgerP` literal IS `BabyBearFriField.babyBearP` — the modulus
every per-fold theorem in the tree is stated over. `rfl`, so a drift is a build error. -/
theorem ledgerP_eq_babyBearP : ledgerP = babyBearP := rfl

/-- **THE COUNT PIN.** The ledger's core-`Nat` `chooseTwo` IS `Nat.choose · 2` — the binomial the
arity-generic count (`good_card_le_of_phase_injective`) bounds by. -/
theorem chooseTwo_eq_choose_two (n : ℕ) : chooseTwo n = Nat.choose n 2 := by
  rw [Nat.choose_two_right]; rfl

/-- **THE LOG PIN.** Core `Nat.log2` IS Mathlib's `Nat.log 2`, so the `perFoldBits` the C-ABI returns
is the quantity §2's lemmas reason about. -/
theorem log2_eq_log_two (n : ℕ) : Nat.log2 n = Nat.log 2 n := Nat.log2_eq_log_two

/-- The ledger's `goodCount` in the arity theorem's own vocabulary: `(m − 1) · C(|κ|, 2)` with
`m = 2 ^ maxLogArity` the fold arity and `|κ| = 2 ^ logBlowup` the folded domain. -/
theorem ledger_goodCount_eq (cfg : FriParams) :
    (friLedger cfg).goodCount
      = (2 ^ cfg.maxLogArity - 1) * Nat.choose (2 ^ cfg.logBlowup) 2 := by
  simp [friLedger, chooseTwo_eq_choose_two]

/-! ## §2. THE PARAMETRIC PER-FOLD BOUND — `perFoldBits` is a REAL error exponent.

`perFoldBits := Nat.log2 ((|F| − 1) / goodCount)` is a *definition*; on its own it is just an
arithmetic expression, and quoting it as a security figure would be exactly the "a name is not a
proof" move. This section proves the reading: it is the greatest `b` with `goodCount · 2^b < |F|`,
hence a genuine bound on the good-challenge DENSITY. -/

/-- **THE LEDGER'S `perFoldBits` IS A SOUND EXPONENT.** `goodCount · 2 ^ perFoldBits < |F|`.

*Proof.* Write `g = goodCount`, `N = |F|`. `2 ^ log₂((N−1)/g) ≤ (N−1)/g` (`Nat.pow_log_le_self`,
which needs `(N−1)/g ≠ 0` — supplied by `g ≤ N−1`), and `g · ((N−1)/g) ≤ N−1 < N`
(`Nat.div_mul_le_self`). ∎

The two hypotheses are the honest non-degeneracy conditions, not fine print: at `goodCount = 0` the
model says nothing (`maxLogArity = 0`, arity 1 — there is no fold), and at `goodCount ≥ |F|` the count
is vacuous (every challenge could be good). Both hold with enormous room at every shipped config. -/
theorem ledger_perFoldBits_sound (cfg : FriParams)
    (hg : 0 < (friLedger cfg).goodCount)
    (hlt : (friLedger cfg).goodCount < ledgerP ^ cfg.extDeg) :
    (friLedger cfg).goodCount * 2 ^ (friLedger cfg).perFoldBits < ledgerP ^ cfg.extDeg := by
  set g := (friLedger cfg).goodCount with hgdef
  set N := ledgerP ^ cfg.extDeg with hNdef
  have hbits : (friLedger cfg).perFoldBits = Nat.log 2 ((N - 1) / g) := by
    rw [hgdef, hNdef]; simp only [friLedger]; rw [log2_eq_log_two]
  rw [hbits]
  -- `(N−1)/g ≠ 0`: from `g ≤ N−1` (i.e. `g < N`) and `0 < g`.
  have hgN : g ≤ N - 1 := by omega
  have hq : (N - 1) / g ≠ 0 := by
    have := Nat.one_le_div_iff hg |>.mpr hgN
    omega
  -- `2 ^ log₂ q ≤ q`, so `g · 2 ^ log₂ q ≤ g · q ≤ N − 1 < N`.
  have hpow : 2 ^ Nat.log 2 ((N - 1) / g) ≤ (N - 1) / g := Nat.pow_log_le_self 2 hq
  have hmul : g * ((N - 1) / g) ≤ N - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self (N - 1) g
  calc g * 2 ^ Nat.log 2 ((N - 1) / g)
      ≤ g * ((N - 1) / g) := Nat.mul_le_mul_left g hpow
    _ ≤ N - 1 := hmul
    _ < N := by omega

/-- **THE REAL-VALUED ERROR** — the shape `wrap_perFold_soundness_capacity` and
`arity8_perFold_soundness` state, now PARAMETRIC over the config and stated through the ledger:
a good-challenge set no larger than the ledger's count has density `< 2 ^ (−perFoldBits)` in the
degree-`extDeg` extension. -/
theorem ledger_perFold_error {F : Type*} [Fintype F] (cfg : FriParams)
    (hg : 0 < (friLedger cfg).goodCount)
    (hlt : (friLedger cfg).goodCount < ledgerP ^ cfg.extDeg)
    (Good : Finset F) (hGood : Good.card ≤ (friLedger cfg).goodCount) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ cfg.extDeg < 1 / 2 ^ (friLedger cfg).perFoldBits := by
  have hnat := ledger_perFoldBits_sound cfg hg hlt
  rw [← ledgerP_eq_babyBearP]
  have hP : (0 : ℝ) < (ledgerP : ℝ) ^ cfg.extDeg := by
    have : (0 : ℝ) < (ledgerP : ℝ) := by norm_num [ledgerP]
    positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (friLedger cfg).perFoldBits := by positivity
  rw [div_lt_div_iff₀ hP h2, one_mul]
  -- `|Good| · 2^b ≤ goodCount · 2^b < |F|`, cast to ℝ.
  have hcast : ((friLedger cfg).goodCount * 2 ^ (friLedger cfg).perFoldBits : ℝ)
      < ((ledgerP : ℝ) ^ cfg.extDeg) := by
    exact_mod_cast hnat
  have hGR : (Good.card : ℝ) ≤ ((friLedger cfg).goodCount : ℝ) := by exact_mod_cast hGood
  nlinarith [hGR, h2, hcast]

/-! ## §3. THE APEX — the ledger's number, from the arity theorem, at ANY config.

This is the one theorem the whole ledger stands on. `good_card_le_of_phase_injective` supplies the
count; §2 turns the count into the exponent; together they say the `@[export]`ed `perFoldBits` bounds
the good-challenge density at the config the caller handed in. -/

/-- **THE LEDGER'S `goodCount` IS THE ARITY THEOREM'S BOUND**, at any config. Instantiates
`good_card_le_of_phase_injective` at `m = 2 ^ maxLogArity`, `|κ| = 2 ^ logBlowup`, `s = 2` — the
deployed inner radius (`dIn = |κ| − 2`, the non-vacuous edge §8 also sits on, where `C(2,2) = 1`). -/
theorem ledger_good_card_le {F : Type*} [Field F] [DecidableEq F] (cfg : FriParams)
    {Φ : ℕ → Fin (2 ^ cfg.logBlowup) → F}
    (hΦ : ∀ y z : Fin (2 ^ cfg.logBlowup), y ≠ z → ∃ i < 2 ^ cfg.maxLogArity, Φ i y ≠ Φ i z)
    (Good : Finset F) (c : F → F)
    (hS : ∀ β ∈ Good, 2 ≤ (Finset.univ.filter (fun y : Fin (2 ^ cfg.logBlowup) =>
        (H (2 ^ cfg.maxLogArity) Φ y).eval β = c β)).card) :
    Good.card ≤ (friLedger cfg).goodCount := by
  have h := good_card_le_of_phase_injective hΦ Good c (s := 2) hS
  have hc : Fintype.card (Fin (2 ^ cfg.logBlowup)) = 2 ^ cfg.logBlowup := by simp
  rw [hc] at h
  rw [ledger_goodCount_eq]
  simpa using h

/-- **⚑ THE PARAMETRIC PER-FOLD SOUNDNESS — the theorem the exported ledger reports.**

At ANY config `cfg`: if the word's phase map is injective (the `M = 1` fiber bound — the NAMED,
per-config HYPOTHESIS `hΦ`, discharged only at `m = 2, logBlowup = 6` in this tree), and every good
challenge folds to a constant on `≥ 2` fibres (the deployed inner radius), then the good challenges'
density in the degree-`extDeg` extension is below `2 ^ (−(friLedger cfg).perFoldBits)`.

`arity8_perFold_soundness` (`109` at the deployed wrap) and `wrap_perFold_soundness_capacity` (`112`
at the arity-2 model) are INSTANCES of this — not separate results, and not one headline reused. -/
theorem ledger_perFold_soundness (cfg : FriParams)
    {Φ : ℕ → Fin (2 ^ cfg.logBlowup) → BabyBearFriField.BabyBear}
    (hg : 0 < (friLedger cfg).goodCount)
    (hlt : (friLedger cfg).goodCount < ledgerP ^ cfg.extDeg)
    (hΦ : ∀ y z : Fin (2 ^ cfg.logBlowup), y ≠ z → ∃ i < 2 ^ cfg.maxLogArity, Φ i y ≠ Φ i z)
    (Good : Finset BabyBearFriField.BabyBear) (c : BabyBearFriField.BabyBear → BabyBearFriField.BabyBear)
    (hS : ∀ β ∈ Good, 2 ≤ (Finset.univ.filter (fun y : Fin (2 ^ cfg.logBlowup) =>
        (H (2 ^ cfg.maxLogArity) Φ y).eval β = c β)).card) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ cfg.extDeg < 1 / 2 ^ (friLedger cfg).perFoldBits :=
  ledger_perFold_error cfg hg hlt Good (ledger_good_card_le cfg hΦ Good c hS)

/-! ## §4. THE SHIPPED CONFIGS — the Lean-modeled knob sets, one per Rust config.

Each `def` below MODELS one shipped Rust knob set. The Rust gate
(`circuit-prove/tests/fri_params_soundness_budget.rs`) PINS its deployed consts against these
literals; nothing here reads Rust, and nothing in Rust recomputes what is here.

`ir2LeafWrapConfig` (the IR-v2 batch config) already lives in `FriVerifier.lean` and is reused. -/

/-- **v1 `create_config`** — the production per-turn uni-STARK prover
(`circuit/src/plonky3_prover.rs:98-102`): `logBlowup = 3`, `38` queries, `16` query-PoW bits,
`maxLogArity = 3`, `logFinalPolyLen = 0`, degree-4 extension. -/
def prodV1Config : FriParams :=
  { logBlowup := 3, numQueries := 38, powBits := 16, maxLogArity := 3,
    logFinalPolyLen := 0, extDeg := 4 }

/-- **`create_outer_config`** — the BN254-native shrink the gnark ETH-wrap circuit verifies
(`circuit-prove/src/dregg_outer_config.rs:127-131` + the `max_log_arity: 1` / `log_final_poly_len: 0`
literals at `:404-405`): `logBlowup = 3`, `38` queries, `16` query-PoW bits, `maxLogArity = 1`
(**arity 2** — the gnark verifier hardcodes the arity-2 fold, `chain/gnark/fri_verify_native.go`),
degree-4 extension.

⚑ This is the config the "~112.6 applies at the ETH wrap" claim was about, and it is NOT the config
~112.6 is proved for: `logBlowup = 3`, not `6`. See `ethWrap_ledger_perFoldBits`. -/
def ethWrapOuterConfig : FriParams :=
  { logBlowup := 3, numQueries := 38, powBits := 16, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 4 }

/-- **`create_recursion_config`** — the default recursion-tree config
(`circuit-prove/src/plonky3_recursion_impl.rs:284-290`): `logBlowup = 3`, `38` queries, **`14`**
query-PoW bits, `maxLogArity = 1`, `logFinalPolyLen = 0`, degree-4 extension.

⚑ Its capacity column reads `3·38 + 14 = 128` — EXACTLY the old Rust gate's drift margin, with zero
headroom, and it was one of the five configs that gate never looked at. -/
def recursionConfig : FriParams :=
  { logBlowup := 3, numQueries := 38, powBits := 14, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 4 }

/-- **`create_zk_config`** — the shielded/hiding lane (`circuit/src/stark_zk.rs:118-126`), the v1
knobs over a `HidingFriPcs`: identical FRI knob set to `prodV1Config`. -/
def zkConfig : FriParams :=
  { logBlowup := 3, numQueries := 38, powBits := 16, maxLogArity := 3,
    logFinalPolyLen := 0, extDeg := 4 }

/-- **`ir2_leaf_wrap_config`** — the rotated native-batch leaf wrap
(`circuit-prove/src/ivc_turn_chain.rs:1132-1135`), whose FRI knobs are supplied by
`create_recursion_config_for_inner_fri` (`plonky3_recursion_impl.rs:339,343`): `ir2LeafWrapConfig`'s
`logBlowup = 6` / `19` queries, but arity **2**, not 8 — the arity is a hardcoded `1` there.

⚑ NAME COLLISION, reported: the Lean `FriVerifier.ir2LeafWrapConfig` (`maxLogArity = 3`) and the Rust
`ir2_leaf_wrap_config()` (`max_log_arity = 1`) are DIFFERENT knob sets sharing a name. The Lean
`ir2LeafWrapConfig` models the Rust `ir2_config` (`descriptor_ir2.rs`), which is what the old gate
pinned it against. This `def` is the Rust `ir2_leaf_wrap_config()`'s actual knobs — and, being
arity-2 at `logBlowup = 6`, it is the ONE shipped config the ~112.6 genuinely describes. -/
def ir2LeafWrapRotatedConfig : FriParams :=
  { logBlowup := 6, numQueries := 19, powBits := 16, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 4 }

/-! ## §5. THE INSTANCES — every shipped config's number, from the one function.

`Nat.log2` is well-founded-recursive, so it does not reduce in the kernel: `decide` cannot see these.
Each `perFoldBits` is instead proved through the `Nat.log` bridge and
`Nat.log_eq_of_pow_le_of_lt_pow` — i.e. by EXHIBITING the bracket `2^b ≤ (|F|−1)/goodCount < 2^(b+1)`,
which is the honest form: it states what the number means. -/

/-- Prove `(friLedger cfg).perFoldBits = b` by exhibiting the defining bracket. -/
private theorem perFoldBits_eq_of_bracket (cfg : FriParams) (b : ℕ)
    (h₁ : 2 ^ b ≤ (ledgerP ^ cfg.extDeg - 1) / (friLedger cfg).goodCount)
    (h₂ : (ledgerP ^ cfg.extDeg - 1) / (friLedger cfg).goodCount < 2 ^ (b + 1)) :
    (friLedger cfg).perFoldBits = b := by
  show Nat.log2 _ = b
  rw [log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂

/-- **THE DEPLOYED IR-v2 WRAP (arity 8, `logBlowup = 6`): `goodCount = 14112`, `perFoldBits = 109`.**
The ~109.84 posture — the ledger's own output, not a number quoted beside it. -/
theorem wrap_ledger_goodCount : (friLedger ir2LeafWrapConfig).goodCount = 14112 := by
  norm_num [friLedger, chooseTwo, ir2LeafWrapConfig]

theorem wrap_ledger_perFoldBits : (friLedger ir2LeafWrapConfig).perFoldBits = 109 := by
  refine perFoldBits_eq_of_bracket _ 109 ?_ ?_ <;>
    rw [wrap_ledger_goodCount] <;> norm_num [ledgerP, ir2LeafWrapConfig]

/-- **THE LEDGER AGREES WITH `arity8_perFold_soundness`** — the check that the exported number is the
PROVED number. `arity8_perFold_soundness` is stated at the literal `14112` and bounds the error by
`1/2^109`; the ledger computes exactly those two numbers at the deployed wrap config. If either the
theorem or the ledger moved, this goes red. -/
theorem wrap_ledger_agrees_with_arity8_theorem :
    (friLedger ir2LeafWrapConfig).goodCount = 14112 ∧
      (friLedger ir2LeafWrapConfig).perFoldBits = 109 :=
  ⟨wrap_ledger_goodCount, wrap_ledger_perFoldBits⟩

/-- **THE DEPLOYED WRAP'S PER-FOLD SOUNDNESS, THROUGH THE LEDGER.** The same statement
`arity8_perFold_soundness` makes, but with the `14112` and the `109` READ OFF the exported ledger
instead of typed in. This is what makes the export non-decorative: the number the C-ABI returns is
the number this theorem bounds by. -/
theorem wrap_perFold_soundness_from_ledger
    (Good : Finset BabyBearFriField.BabyBear)
    (hGood : Good.card ≤ (friLedger ir2LeafWrapConfig).goodCount) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ ir2LeafWrapConfig.extDeg
      < 1 / 2 ^ (friLedger ir2LeafWrapConfig).perFoldBits := by
  refine ledger_perFold_error ir2LeafWrapConfig ?_ ?_ Good hGood
  · rw [wrap_ledger_goodCount]; norm_num
  · rw [wrap_ledger_goodCount]; norm_num [ledgerP, ir2LeafWrapConfig]

/-- **THE ROTATED LEAF WRAP (arity 2, `logBlowup = 6`): `goodCount = 2016`, `perFoldBits = 112`.**
This — NOT the gnark ETH-wrap — is the shipped config the standing ~112.6 actually describes, and the
ledger RECOVERS §8's `C(64,2) = 2016` at it (`arity2_recovers_capacity_count`). -/
theorem rotatedLeafWrap_ledger_goodCount : (friLedger ir2LeafWrapRotatedConfig).goodCount = 2016 := by
  norm_num [friLedger, chooseTwo, ir2LeafWrapRotatedConfig]

theorem rotatedLeafWrap_ledger_perFoldBits :
    (friLedger ir2LeafWrapRotatedConfig).perFoldBits = 112 := by
  refine perFoldBits_eq_of_bracket _ 112 ?_ ?_ <;>
    rw [rotatedLeafWrap_ledger_goodCount] <;> norm_num [ledgerP, ir2LeafWrapRotatedConfig]

/-- **THE ARITY-8 LOSS IS EXACTLY `log₂ 7`, read off the two ledgers.** Same `logBlowup = 6`, same
field; arity `8` vs arity `2` gives `14112` vs `2016` — a factor of `7` — and `109` vs `112`.
`FriArityTransfer.arity8_loses_exactly_factor_seven` is the same fact stated on the literals. -/
theorem arity8_costs_seven_times_arity2_at_logBlowup6 :
    (friLedger ir2LeafWrapConfig).goodCount
        = 7 * (friLedger ir2LeafWrapRotatedConfig).goodCount ∧
      (friLedger ir2LeafWrapConfig).perFoldBits + 3
        = (friLedger ir2LeafWrapRotatedConfig).perFoldBits := by
  rw [wrap_ledger_goodCount, rotatedLeafWrap_ledger_goodCount, wrap_ledger_perFoldBits,
    rotatedLeafWrap_ledger_perFoldBits]
  norm_num

/-- **⚑ THE ETH-WRAP FINDING: `goodCount = 28`, `perFoldBits = 118` — NOT `112`.**
The BN254-native shrink the gnark circuit verifies is arity 2 at `logBlowup = 3`, so `|κ| = 8` and
`goodCount = 1 · C(8,2) = 28`. The old Rust header's "the gnark ETH-wrap verifier runs arity-2 — so
~112.6 is the right figure THERE" quoted the arity-2 number from the `logBlowup = 6` config. Both
numbers are true; the sentence attached one to the wrong object. -/
theorem ethWrap_ledger_goodCount : (friLedger ethWrapOuterConfig).goodCount = 28 := by
  norm_num [friLedger, chooseTwo, ethWrapOuterConfig]

theorem ethWrap_ledger_perFoldBits : (friLedger ethWrapOuterConfig).perFoldBits = 118 := by
  refine perFoldBits_eq_of_bracket _ 118 ?_ ?_ <;>
    rw [ethWrap_ledger_goodCount] <;> norm_num [ledgerP, ethWrapOuterConfig]

/-- **THE ETH-WRAP POSTURE IS NOT THE ~112.6 — a BOTH-TRUTH tooth.** The ledgers of the ETH-wrap
outer config and of the arity-2 `logBlowup = 6` leaf wrap DIFFER, so no single figure covers both.
This is the falsifier for "one headline number per system". -/
theorem ethWrap_is_not_the_112_config :
    (friLedger ethWrapOuterConfig).perFoldBits ≠ (friLedger ir2LeafWrapRotatedConfig).perFoldBits := by
  rw [ethWrap_ledger_perFoldBits, rotatedLeafWrap_ledger_perFoldBits]; norm_num

/-- **v1 PRODUCTION (arity 8, `logBlowup = 3`): `goodCount = 196`, `perFoldBits = 116`.** -/
theorem prodV1_ledger_goodCount : (friLedger prodV1Config).goodCount = 196 := by
  norm_num [friLedger, chooseTwo, prodV1Config]

theorem prodV1_ledger_perFoldBits : (friLedger prodV1Config).perFoldBits = 116 := by
  refine perFoldBits_eq_of_bracket _ 116 ?_ ?_ <;>
    rw [prodV1_ledger_goodCount] <;> norm_num [ledgerP, prodV1Config]

/-- **The shielded/hiding lane carries the v1 knob set EXACTLY** — so its ledger is v1's, and the
hiding PCS costs nothing in this column. Stated as an equality of LEDGERS, not of headline numbers. -/
theorem zk_ledger_eq_prodV1 : friLedger zkConfig = friLedger prodV1Config := rfl

/-- **The recursion default's capacity column reads `128` — on the nose.** `3·38 + 14 = 128`: the old
gate's `CONJECTURED_FLOOR_BITS` margin with ZERO headroom, on a config that gate never judged. Its
`14` query-PoW bits (vs `16` everywhere else) is the whole difference. -/
theorem recursion_ledger_capacityBits : (friLedger recursionConfig).capacityBits = 128 := by
  norm_num [friLedger, recursionConfig]

theorem recursion_ledger_johnsonBits : (friLedger recursionConfig).johnsonBits = 71 := by
  norm_num [friLedger, recursionConfig]

/-- The recursion default is arity 2 at `logBlowup = 3` — the ETH-wrap outer's fold shape — so it
shares that per-fold count. Its query ledger is what differs (`powBits = 14`). -/
theorem recursion_ledger_perFold_eq_ethWrap :
    (friLedger recursionConfig).goodCount = (friLedger ethWrapOuterConfig).goodCount ∧
      (friLedger recursionConfig).perFoldBits = (friLedger ethWrapOuterConfig).perFoldBits := by
  constructor <;> rfl

/-! ## §6. THE QUERY LEDGERS — the two columns, per config, and the parity fact.

The `(6, 19)` pin was measured against `(3, 38)` at EQUAL Johnson bits — that is the invariant, and
it is a THEOREM here rather than an assertion in a Rust comment. -/

/-- **SECURITY PARITY, PROVED: the IR-v2 wrap and the v1 prod config have IDENTICAL query ledgers.**
`19·6 + 16 = 130 = 38·3 + 16` and `19·6/2 + 16 = 73 = 38·3/2 + 16`. This is the fact the `(6, 19)`
pin was chosen to preserve (`docs/reference/FRI-PARAM-FRONTIER.md` §1a); the old Rust gate CHECKED it
by recomputing both sides in Rust. Now it is proved once, here, of the modeled configs. -/
theorem wrap_prodV1_query_ledger_parity :
    (friLedger ir2LeafWrapConfig).capacityBits = (friLedger prodV1Config).capacityBits ∧
      (friLedger ir2LeafWrapConfig).johnsonBits = (friLedger prodV1Config).johnsonBits := by
  constructor <;> rfl

theorem wrap_ledger_capacityBits : (friLedger ir2LeafWrapConfig).capacityBits = 130 := by
  norm_num [friLedger, ir2LeafWrapConfig]

theorem wrap_ledger_johnsonBits : (friLedger ir2LeafWrapConfig).johnsonBits = 73 := by
  norm_num [friLedger, ir2LeafWrapConfig]

/-- **THE QUERY LEDGER AND THE PER-FOLD LEDGER ARE INDEPENDENT COLUMNS — a non-collapse tooth.**
The v1 prod config has the SAME query ledger as the IR-v2 wrap (`wrap_prodV1_query_ledger_parity`)
but a DIFFERENT per-fold posture (`116` vs `109`). So neither column determines the other, and
quoting one number as "the config's soundness" is not available. -/
theorem query_ledger_does_not_determine_perFold :
    (friLedger ir2LeafWrapConfig).johnsonBits = (friLedger prodV1Config).johnsonBits ∧
      (friLedger ir2LeafWrapConfig).perFoldBits ≠ (friLedger prodV1Config).perFoldBits := by
  refine ⟨rfl, ?_⟩
  rw [wrap_ledger_perFoldBits, prodV1_ledger_perFoldBits]; norm_num

/-! ## §7. THE EXPORT IS THE LEDGER — the `@[export]`ed wire is not a separate path.

`friLedgerFFI` is the C-ABI entry the Rust gate calls. These `#guard`s check it renders the SAME
`friLedger` the theorems above are about, at the shipped configs — so a Rust caller reading the wire
reads the proved numbers, and a wire-format edit that dropped a column would go red HERE, in Lean,
before the Rust test ever ran. -/

-- The deployed IR-v2 wrap: arity 8, |κ| = 64, |Good| ≤ 14112, 109 per-fold bits, 73 Johnson, 130 capacity.
#guard friLedgerFFI "6 19 16 3 0 4" == "8 64 14112 109 73 130"
-- The rotated leaf wrap (arity 2 at logBlowup 6) — the one config the ~112.6 describes.
#guard friLedgerFFI "6 19 16 1 0 4" == "2 64 2016 112 73 130"
-- The gnark ETH-wrap's outer shrink: arity 2 at logBlowup 3 ⇒ |κ| = 8, |Good| ≤ 28, 118 bits.
#guard friLedgerFFI "3 38 16 1 0 4" == "2 8 28 118 73 130"
-- v1 production: arity 8 at logBlowup 3.
#guard friLedgerFFI "3 38 16 3 0 4" == "8 8 196 116 73 130"
-- The recursion default: powBits 14 ⇒ capacity exactly 128.
#guard friLedgerFFI "3 38 14 1 0 4" == "2 8 28 118 71 128"
-- FAIL-CLOSED: a malformed wire and an out-of-window knob set both refuse.
#guard friLedgerFFI "6 19 16" == ""
#guard friLedgerFFI "not a config" == ""
#guard friLedgerFFI "6 19 16 3 0 64" == ""

/-! ## §8. Axiom hygiene.

⚑ `#assert_axioms` is BLIND TO HYPOTHESES. Every theorem below is kernel-clean; the per-fold results
(`ledger_good_card_le`, `ledger_perFold_soundness`, and every instance that routes through them) carry
the `M = 1` phase-injectivity hypothesis `hΦ` — `FriArityTransfer.Arity8FiberBound` at the deployed
arity, and its unbuilt `logBlowup = 3` analogue at the outer/recursion configs. Kernel-clean is not
hypothesis-free, and this block does not claim it is. -/

#assert_axioms ledgerP_eq_babyBearP
#assert_axioms chooseTwo_eq_choose_two
#assert_axioms log2_eq_log_two
#assert_axioms ledger_goodCount_eq
#assert_axioms ledger_perFoldBits_sound
#assert_axioms ledger_perFold_error
#assert_axioms ledger_good_card_le
#assert_axioms ledger_perFold_soundness
#assert_axioms wrap_ledger_goodCount
#assert_axioms wrap_ledger_perFoldBits
#assert_axioms wrap_ledger_agrees_with_arity8_theorem
#assert_axioms wrap_perFold_soundness_from_ledger
#assert_axioms rotatedLeafWrap_ledger_goodCount
#assert_axioms rotatedLeafWrap_ledger_perFoldBits
#assert_axioms arity8_costs_seven_times_arity2_at_logBlowup6
#assert_axioms ethWrap_ledger_goodCount
#assert_axioms ethWrap_ledger_perFoldBits
#assert_axioms ethWrap_is_not_the_112_config
#assert_axioms prodV1_ledger_goodCount
#assert_axioms prodV1_ledger_perFoldBits
#assert_axioms zk_ledger_eq_prodV1
#assert_axioms recursion_ledger_capacityBits
#assert_axioms recursion_ledger_johnsonBits
#assert_axioms recursion_ledger_perFold_eq_ethWrap
#assert_axioms wrap_prodV1_query_ledger_parity
#assert_axioms wrap_ledger_capacityBits
#assert_axioms wrap_ledger_johnsonBits
#assert_axioms query_ledger_does_not_determine_perFold

end Dregg2.Circuit.FriLedgerSound
