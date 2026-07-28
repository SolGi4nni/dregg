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

## ⚑ THE `hΦ` HYPOTHESIS — DISCHARGED AT EVERY SHIPPED CONFIG (2026-07-15)

Every per-fold number here carries `hΦ` — the `M = 1` fiber bound — as a HYPOTHESIS, inherited from
`FriArityTransfer.good_card_le_of_phase_injective`. It was DISCHARGED at `m = 2, logBlowup = 6` from
farness (`FriCorrelatedAgreementSharp` §8's `far_fiber_card` + `wrap_fiber_le_one` over the concrete
`friSetupWrapRate`) and OPEN at every other config, including the deployed arity-8 wrap and the
`logBlowup = 3` configs — for want of the RS setups this tree did not build.

`Dregg2.Circuit.FriArityFiberDischarge` now builds those setups PARAMETRICALLY (`friSetupK` at
`|L| = 2^(k+b)`, `|κ| = 2^b`, dimension `2^k`, rate `2^(−b)`), generalizes `far_fiber_card` to arity
`n` (`far_fiber_card_arity`), and PROVES `hΦ` from farness at every one of the six configs below —
four `(k, b)` instances of ONE theorem (`phase_injective_of_far`):

| config                      | arity | logBlowup | `|L|` | `dOut` ⟹ `M = 1` | discharge |
|-----------------------------|-------|-----------|-------|-------------------|-----------|
| `ir2LeafWrapConfig`         | 8     | 6         | 512   | `≥ 496`           | `arity8_phase_injective` |
| `ir2LeafWrapRotatedConfig`  | 2     | 6         | 128   | `≥ 124`           | `arity2Lb6_phase_injective` |
| `ethWrapOuterConfig`        | 2     | 3         | 16    | `≥ 12`            | `arity2Lb3_phase_injective` |
| `recursionConfig`           | 2     | 3         | 16    | `≥ 12`            | (same instance) |
| `prodV1Config`              | 8     | 3         | 64    | `≥ 48`            | `arity8Lb3_phase_injective` |
| `zkConfig`                  | 8     | 3         | 64    | `≥ 48`            | (same instance) |

It is not vacuous: `phase_injective_fires` exhibits, at EVERY `(k, b)`, a concrete far word the
discharge fires on. ⚠ Also found there: the `Prop` that NAMED the arity-8 obligation
(`FriArityTransfer.Arity8FiberBoundNaive`) was **FALSE**, not open — it omitted the farness link, so
the constant map refutes it. It had no consumers; nothing here was contaminated.

The theorems below still take `hΦ` as a hypothesis, correctly: they are PARAMETRIC in the config and
mention no setup, so they cannot discharge it — the discharge is per-setup and lives where the setups
live. `FriArityFiberDischarge.arity8_good_card_le_unconditional` is the deployed composite with no
`hΦ` left.

`#assert_axioms` is BLIND TO HYPOTHESES. The theorems below are kernel-clean; that is not the same as
hypothesis-free, and the `#assert_axioms` block at the bottom must not be read as if it were — the
`hΦ` discharge is a theorem elsewhere, not something the axiom check could ever have told you.
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

/-! ## §6b. ⚑ THE COMMIT-PHASE COLUMN — `commitBits` IS a bound on BCIKS20's `ε_C`.

`johnsonBits` is `numQueries·logBlowup/2 + powBits`. That is `−s·log₂ α + powBits` for BCIKS20's
`α = √ρ(1 + 1/2m)` **in the limit `m → ∞`** — the bottom row of Thm 8.3 with the commit-phase term
`ε_C` DROPPED. This section proves that `friCommitLedger`'s `commitBits` really is a lower bound on
`−log₂ ε_C` for `ε_C` as the paper defines it, so the number the C-ABI returns is the paper's term
and not an arithmetic expression that resembles it.

**Transcribed from BCIKS20 (eprint 2020/654), Lemma 8.2 / Theorem 8.3, printed pp. 40–41:**

```
ε_C = (m+½)⁷·|D⁽⁰⁾|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁽⁰⁾|+1)/√ρ · (Σᵢ l⁽ⁱ⁾)/|F|
```

⚑ The bound goes ONE WAY on purpose: `epsCNum` OVER-estimates `ε_C`, so `commitBits`
UNDER-estimates `−log₂ ε_C`. A ledger that rounded the other way would report bits it has not got. -/

/-- BCIKS20's rate `ρ = 2^(−logBlowup)`. -/
noncomputable def rate (lb : ℕ) : ℝ := 1 / 2 ^ lb

theorem rate_pos (lb : ℕ) : 0 < rate lb := by unfold rate; positivity

/-- **FAITHFULNESS — `ρ · √ρ` IS the paper's `ρ^{3/2}`.** `epsC` writes the denominator as
`2·(ρ·√ρ)·|F|`; the paper writes `2ρ^{3/2}|F|`. This is the check that they are the same number and
not a convenient re-spelling. -/
theorem rate_rpow_three_halves (lb : ℕ) :
    (rate lb) ^ ((3 : ℝ) / 2) = rate lb * Real.sqrt (rate lb) := by
  have hpos := rate_pos lb
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (le_of_lt hpos) (by norm_num)]
  norm_num

/-- **BCIKS20 Lemma 8.2's `ε_C`, transcribed** — `|F| = ledgerP ^ extDeg`, `|D⁽⁰⁾| = d0`,
`Σᵢ l⁽ⁱ⁾ = sumL`, `m = bciksM`. -/
noncomputable def epsC (lb d0 bciksM sumL extDeg : ℕ) : ℝ :=
  ((bciksM : ℝ) + 1 / 2) ^ 7 * (d0 : ℝ) ^ 2
      / (2 * (rate lb * Real.sqrt (rate lb)) * (ledgerP : ℝ) ^ extDeg)
    + (2 * (bciksM : ℝ) + 1) * ((d0 : ℝ) + 1) / Real.sqrt (rate lb) * (sumL : ℝ)
      / (ledgerP : ℝ) ^ extDeg

/-- **THE ROUNDING PIN** — `⌈3·lb/2⌉ = lb + ⌈lb/2⌉`. The ledger writes the first; the proof needs the
second (so `ρ^{3/2} = ρ·√ρ` factors as `2^(−lb)·2^(−⌈lb/2⌉)`). Equal at every `lb`, so the ledger's
exponent is exactly the one the bound below earns — no slack is being hidden in the spelling. -/
theorem ceilDiv_two (a : ℕ) : ceilDiv a 2 = (a + 1) / 2 := by
  simp only [ceilDiv]
  norm_num

theorem ceilDiv_three_mul_two (lb : ℕ) : ceilDiv (3 * lb) 2 = lb + ceilDiv lb 2 := by
  rw [ceilDiv_two, ceilDiv_two]
  omega

/-- **`√ρ ≥ 2^(−⌈lb/2⌉)`** — the one inequality the whole column rests on. `√ρ` sits in a
DENOMINATOR, so a LOWER bound on it is what upper-bounds `ε_C`. At even `lb` it is an equality
(`√2^(−6) = 2^(−3)` exactly, the deployed case); at odd `lb` the `⌈·⌉` is the conservative side. -/
theorem sqrt_rate_ge (lb : ℕ) : (1 : ℝ) / 2 ^ (ceilDiv lb 2) ≤ Real.sqrt (rate lb) := by
  have hle : lb ≤ ceilDiv lb 2 * 2 := by rw [ceilDiv_two]; omega
  refine Real.le_sqrt' (by positivity) |>.mpr ?_
  rw [rate, div_pow, one_pow, ← pow_mul]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  exact pow_le_pow_right₀ (by norm_num) hle

/-- `1/√ρ ≤ 2^⌈lb/2⌉` — the second `ε_C` term's factor. -/
theorem one_div_sqrt_rate_le (lb : ℕ) : 1 / Real.sqrt (rate lb) ≤ 2 ^ (ceilDiv lb 2) := by
  have h := sqrt_rate_ge lb
  have hpos : (0 : ℝ) < 1 / 2 ^ (ceilDiv lb 2) := by positivity
  have hs : (0 : ℝ) < Real.sqrt (rate lb) := lt_of_lt_of_le hpos h
  rw [div_le_iff₀ hs]
  calc (1 : ℝ) = 2 ^ (ceilDiv lb 2) * (1 / 2 ^ (ceilDiv lb 2)) := by field_simp
    _ ≤ 2 ^ (ceilDiv lb 2) * Real.sqrt (rate lb) := by
        exact mul_le_mul_of_nonneg_left h (by positivity)

/-- `1/(ρ·√ρ) ≤ 2^(lb + ⌈lb/2⌉) = 2^⌈3lb/2⌉` — the first `ε_C` term's factor. -/
theorem one_div_rate_three_halves_le (lb : ℕ) :
    1 / (rate lb * Real.sqrt (rate lb)) ≤ 2 ^ (ceilDiv (3 * lb) 2) := by
  have hs : (0 : ℝ) < Real.sqrt (rate lb) :=
    lt_of_lt_of_le (by positivity) (sqrt_rate_ge lb)
  rw [ceilDiv_three_mul_two, pow_add, one_div, mul_inv, rate]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · rw [one_div, inv_inv]
  · rw [← one_div]; exact one_div_sqrt_rate_le lb

/-- **⚑ THE COLUMN IS THE PAPER'S TERM — `ε_C ≤ epsCNum / (2^8·|F|)`.**

*Proof.* `(m+½)⁷ = (2m+1)⁷/2⁷`, so term₁ `= (2m+1)⁷·d0²·(1/(ρ√ρ))/(2⁸·|F|) ≤ A₁/(2⁸·|F|)` by
`one_div_rate_three_halves_le`; term₂ `= (2m+1)(d0+1)·(1/√ρ)·Σl/|F| ≤ A₂/|F| = 2⁸·A₂/(2⁸·|F|)` by
`one_div_sqrt_rate_le`. Sum. ∎ -/
theorem ledger_epsC_le (cfg : FriParams) (logD0 bciksM : ℕ) :
    epsC cfg.logBlowup (2 ^ logD0) bciksM (friCommitLedger cfg logD0 bciksM).sumArities cfg.extDeg
      ≤ ((friCommitLedger cfg logD0 bciksM).epsCNum : ℝ)
          / (2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg) := by
  have hPp : (0 : ℝ) < (ledgerP : ℝ) := by norm_num [ledgerP]
  have hP : (0 : ℝ) < (ledgerP : ℝ) ^ cfg.extDeg := by positivity
  have hs : (0 : ℝ) < Real.sqrt (rate cfg.logBlowup) :=
    lt_of_lt_of_le (by positivity) (sqrt_rate_ge cfg.logBlowup)
  have hrs : (0 : ℝ) < rate cfg.logBlowup * Real.sqrt (rate cfg.logBlowup) :=
    mul_pos (rate_pos _) hs
  -- The ledger's numerator, in ℝ.
  have hnum : ((friCommitLedger cfg logD0 bciksM).epsCNum : ℝ)
      = (2 * (bciksM : ℝ) + 1) ^ 7 * ((2 : ℝ) ^ logD0 * (2 : ℝ) ^ logD0)
          * 2 ^ (ceilDiv (3 * cfg.logBlowup) 2)
        + 2 ^ 8 * ((2 * (bciksM : ℝ) + 1) * ((2 : ℝ) ^ logD0 + 1)
          * ((friCommitLedger cfg logD0 bciksM).sumArities : ℝ)
          * 2 ^ (ceilDiv cfg.logBlowup 2)) := by
    simp only [friCommitLedger]
    push_cast
    ring
  rw [epsC]
  push_cast
  rw [hnum, add_div]
  refine add_le_add ?_ ?_
  · -- TERM 1: `(m+½)⁷ = (2m+1)⁷/2⁷`, then the only content is `1/(ρ√ρ) ≤ 2^⌈3lb/2⌉`.
    have hC : (0 : ℝ) ≤ (2 * (bciksM : ℝ) + 1) ^ 7
        * ((2 : ℝ) ^ logD0 * (2 : ℝ) ^ logD0) / (2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg) := by
      positivity
    have key := mul_le_mul_of_nonneg_left (one_div_rate_three_halves_le cfg.logBlowup) hC
    calc ((bciksM : ℝ) + 1 / 2) ^ 7 * ((2 : ℝ) ^ logD0) ^ 2
            / (2 * (rate cfg.logBlowup * Real.sqrt (rate cfg.logBlowup))
                * (ledgerP : ℝ) ^ cfg.extDeg)
        = (2 * (bciksM : ℝ) + 1) ^ 7 * ((2 : ℝ) ^ logD0 * (2 : ℝ) ^ logD0)
            / (2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg)
            * (1 / (rate cfg.logBlowup * Real.sqrt (rate cfg.logBlowup))) := by
          field_simp
      _ ≤ (2 * (bciksM : ℝ) + 1) ^ 7 * ((2 : ℝ) ^ logD0 * (2 : ℝ) ^ logD0)
            / (2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg)
            * 2 ^ (ceilDiv (3 * cfg.logBlowup) 2) := key
      _ = (2 * (bciksM : ℝ) + 1) ^ 7 * ((2 : ℝ) ^ logD0 * (2 : ℝ) ^ logD0)
            * 2 ^ (ceilDiv (3 * cfg.logBlowup) 2) / (2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg) := by
          ring
  · -- TERM 2: the only content is `1/√ρ ≤ 2^⌈lb/2⌉`; the `2^8` cancels exactly.
    have hD : (0 : ℝ) ≤ (2 * (bciksM : ℝ) + 1) * ((2 : ℝ) ^ logD0 + 1)
        * ((friCommitLedger cfg logD0 bciksM).sumArities : ℝ)
        / (ledgerP : ℝ) ^ cfg.extDeg := by positivity
    have key := mul_le_mul_of_nonneg_left (one_div_sqrt_rate_le cfg.logBlowup) hD
    calc (2 * (bciksM : ℝ) + 1) * ((2 : ℝ) ^ logD0 + 1) / Real.sqrt (rate cfg.logBlowup)
            * ((friCommitLedger cfg logD0 bciksM).sumArities : ℝ)
            / (ledgerP : ℝ) ^ cfg.extDeg
        = (2 * (bciksM : ℝ) + 1) * ((2 : ℝ) ^ logD0 + 1)
            * ((friCommitLedger cfg logD0 bciksM).sumArities : ℝ)
            / (ledgerP : ℝ) ^ cfg.extDeg * (1 / Real.sqrt (rate cfg.logBlowup)) := by
          field_simp
      _ ≤ (2 * (bciksM : ℝ) + 1) * ((2 : ℝ) ^ logD0 + 1)
            * ((friCommitLedger cfg logD0 bciksM).sumArities : ℝ)
            / (ledgerP : ℝ) ^ cfg.extDeg * 2 ^ (ceilDiv cfg.logBlowup 2) := key
      _ = 2 ^ 8 * ((2 * (bciksM : ℝ) + 1) * ((2 : ℝ) ^ logD0 + 1)
            * ((friCommitLedger cfg logD0 bciksM).sumArities : ℝ)
            * 2 ^ (ceilDiv cfg.logBlowup 2)) / (2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg) := by
          field_simp

/-- **`commitBits` IS A SOUND EXPONENT** — `epsCNum · 2^commitBits < 2^8·|F|`, the same reading
`ledger_perFoldBits_sound` establishes for `perFoldBits`, at the same `Nat.log2` shape. -/
theorem ledger_commitBits_sound (cfg : FriParams) (logD0 bciksM : ℕ)
    (hg : 0 < (friCommitLedger cfg logD0 bciksM).epsCNum)
    (hlt : (friCommitLedger cfg logD0 bciksM).epsCNum < 2 ^ 8 * ledgerP ^ cfg.extDeg) :
    (friCommitLedger cfg logD0 bciksM).epsCNum * 2 ^ (friCommitLedger cfg logD0 bciksM).commitBits
      < 2 ^ 8 * ledgerP ^ cfg.extDeg := by
  set g := (friCommitLedger cfg logD0 bciksM).epsCNum with hgdef
  set N := 2 ^ 8 * ledgerP ^ cfg.extDeg with hNdef
  have hbits : (friCommitLedger cfg logD0 bciksM).commitBits = Nat.log 2 ((N - 1) / g) := by
    rw [hgdef, hNdef]; simp only [friCommitLedger]; rw [log2_eq_log_two]
  rw [hbits]
  have hgN : g ≤ N - 1 := by omega
  have hq : (N - 1) / g ≠ 0 := by
    have := Nat.one_le_div_iff hg |>.mpr hgN
    omega
  have hpow : 2 ^ Nat.log 2 ((N - 1) / g) ≤ (N - 1) / g := Nat.pow_log_le_self 2 hq
  have hmul : g * ((N - 1) / g) ≤ N - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self (N - 1) g
  calc g * 2 ^ Nat.log 2 ((N - 1) / g)
      ≤ g * ((N - 1) / g) := Nat.mul_le_mul_left g hpow
    _ ≤ N - 1 := hmul
    _ < N := by omega

/-- **⚑ THE COMMIT-PHASE APEX — `ε_C ≤ 2^(−commitBits)`, for BCIKS20's `ε_C`.**

This is the theorem that makes `commitBits` a soundness number rather than an arithmetic
expression: the paper's `ε_C` (`epsC`, transcribed from Lemma 8.2) is bounded by two to the minus
the column the C-ABI returns. Compose `ledger_epsC_le` (the column over-estimates `ε_C`) with
`ledger_commitBits_sound` (the `Nat.log2` reading is a real exponent). -/
theorem ledger_epsC_soundness (cfg : FriParams) (logD0 bciksM : ℕ)
    (hg : 0 < (friCommitLedger cfg logD0 bciksM).epsCNum)
    (hlt : (friCommitLedger cfg logD0 bciksM).epsCNum < 2 ^ 8 * ledgerP ^ cfg.extDeg) :
    epsC cfg.logBlowup (2 ^ logD0) bciksM (friCommitLedger cfg logD0 bciksM).sumArities cfg.extDeg
      < 1 / 2 ^ (friCommitLedger cfg logD0 bciksM).commitBits := by
  have hle := ledger_epsC_le cfg logD0 bciksM
  have hnat := ledger_commitBits_sound cfg logD0 bciksM hg hlt
  have hPp : (0 : ℝ) < (ledgerP : ℝ) := by norm_num [ledgerP]
  have hP : (0 : ℝ) < 2 ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (friCommitLedger cfg logD0 bciksM).commitBits := by positivity
  refine lt_of_le_of_lt hle ?_
  rw [div_lt_div_iff₀ hP h2, one_mul]
  have hcast : (((friCommitLedger cfg logD0 bciksM).epsCNum : ℝ)
      * 2 ^ (friCommitLedger cfg logD0 bciksM).commitBits)
      < ((2 : ℝ) ^ 8 * (ledgerP : ℝ) ^ cfg.extDeg) := by
    exact_mod_cast hnat
  nlinarith [hcast, h2]

/-! ## §6c. THE DEPLOYED COMMIT COLUMN — the numbers, reported unmassaged.

⚑ The numbers immediately below are quoted at `logD0 = 12` — the FRI domain of the MEASURED COST
FIXTURE, which is a **1-effect turn** and is smaller than a production turn. They are the fixture's
numbers, not the deployment's, and they are labelled as such.

⚑ The DEPLOYED heights ARE measured — `circuit-prove/tests/fri_trace_height_measure.rs` reads them
off real verified proofs — and `ledger_commitBits_at_measured_heights` reports the column at each
config's own. **The deployed worst case is `61`** (the recursion wrap at `|D⁽⁰⁾| = 2^19`), not the
fixture's `71`. -/

/-- The `commitBits` analogue of `perFoldBits_eq_of_bracket` — so the per-config numbers below are
kernel `Nat` arithmetic, NOT `native_decide`. `native_decide` would put `Lean.ofReduceBool` (and the
compiler) in the trust base of a soundness column; a ledger is exactly the wrong place for that. -/
private theorem commitBits_eq_of_bracket (cfg : FriParams) (logD0 bciksM b : ℕ)
    (h₁ : 2 ^ b ≤ (2 ^ 8 * ledgerP ^ cfg.extDeg - 1) / (friCommitLedger cfg logD0 bciksM).epsCNum)
    (h₂ : (2 ^ 8 * ledgerP ^ cfg.extDeg - 1) / (friCommitLedger cfg logD0 bciksM).epsCNum
        < 2 ^ (b + 1)) :
    (friCommitLedger cfg logD0 bciksM).commitBits = b := by
  show Nat.log2 _ = b
  rw [log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂

/-- **THE DEPLOYED COMMIT COLUMN READS `71`** at the fixture height and `m = 7`. -/
theorem wrap_ledger_commitBits : (friCommitLedger ir2LeafWrapConfig 12 7).commitBits = 71 := by
  refine commitBits_eq_of_bracket _ _ _ 71 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapConfig]

/-- **⚑ THE COMMIT COLUMN IS NOT TRACE-INVARIANT — and this is why it is a REAL column.**
Same config, an `8×`-taller trace: the commit column falls `71 → 55`, ~2 bits per doubling, because
`ε_C ∝ |D⁽⁰⁾|²`. Neither `perFoldBits` nor `johnsonBits` moves at all — they cannot see the trace.
So the proven posture is a function of the STATEMENT being proved, not of the FRI knobs alone. -/
theorem commit_column_is_not_trace_invariant :
    (friCommitLedger ir2LeafWrapConfig 12 7).commitBits = 71 ∧
      (friCommitLedger ir2LeafWrapConfig 20 7).commitBits = 55 ∧
      (friLedger ir2LeafWrapConfig).perFoldBits = (friLedger ir2LeafWrapConfig).perFoldBits ∧
      (friLedger ir2LeafWrapConfig).johnsonBits = 73 := by
  refine ⟨wrap_ledger_commitBits, ?_, rfl, wrap_ledger_johnsonBits⟩
  refine commitBits_eq_of_bracket _ _ _ 55 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapConfig]

/-- **⚑ THE COLUMN AT THE MEASURED TRACE HEIGHTS — the honest deployed numbers.**

The `71` above is the FIXTURE's number, and the fixture is a **1-effect turn**. The real heights are
MEASURED — off real verified proofs' `BatchProof::degree_bits`, not off a witness — in
`circuit-prove/tests/fri_trace_height_measure.rs`. Each config is paired with **its own** measured
`|D⁽⁰⁾|`, because pairing a config with another config's height is exactly the error a parametric
ledger exists to prevent:

| config (its `logBlowup`)          | measured `|D⁽⁰⁾|` | source                                    | `commitBits` |
|-----------------------------------|-------------------|-------------------------------------------|--------------|
| `prodV1Config` (3)                | `2^9`             | `2^6` main table + blowup                 | **81** |
| `ir2LeafWrapConfig` (6)           | `2^14`            | `2^8` chip table at 64 effects + blowup   | **67** |
| `ethWrapOuterConfig` (3)          | `2^18`            | the measured `2^15` shrink tables + blowup| **63** |
| `recursionConfig` (3)             | `2^19`            | `WRAP_LOG_CEIL = 2^16`, FORCED every fold | **61** |

**⚑ `61` is the deployed posture** — the recursion wrap's `2^16`-row ceiling is applied to every
running-proof table on every fold, so the system's worst case is paid unconditionally, and the
recursion is ALSO the named weakest link on the query column (`pow = 14`). Not `71`, and not the
`73` the Johnson column reads.

⚑ **This is the whole point of making `ε_C` a parametric column rather than a scratch-script
footnote.** The fixture flattered us by 10 bits, and no FRI knob could have revealed it: `perFoldBits`
and `johnsonBits` read exactly the same at every one of these heights. The proven posture is a
function of the STATEMENT being proved, and only a column that takes the height as an input can say so.

⚠ The heights are the measurement lane's, not this file's. This file is parametric in `logD0`
precisely so that it CONSUMES a measurement rather than asserting one; re-read it at the new
`|D⁽⁰⁾|` if a bigger turn family ships (a 128-effect turn measures `2^15`, a 512-effect turn `2^17`). -/
theorem ledger_commitBits_at_measured_heights :
    (friCommitLedger prodV1Config 9 7).commitBits = 81 ∧
      (friCommitLedger ir2LeafWrapConfig 14 7).commitBits = 67 ∧
      (friCommitLedger ethWrapOuterConfig 18 7).commitBits = 63 ∧
      (friCommitLedger recursionConfig 19 7).commitBits = 61 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine commitBits_eq_of_bracket _ _ _ 81 ?_ ?_ <;>
      norm_num [friCommitLedger, ceilDiv, ledgerP, prodV1Config]
  · refine commitBits_eq_of_bracket _ _ _ 67 ?_ ?_ <;>
      norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapConfig]
  · refine commitBits_eq_of_bracket _ _ _ 63 ?_ ?_ <;>
      norm_num [friCommitLedger, ceilDiv, ledgerP, ethWrapOuterConfig]
  · refine commitBits_eq_of_bracket _ _ _ 61 ?_ ?_ <;>
      norm_num [friCommitLedger, ceilDiv, ledgerP, recursionConfig]

/-- ⚠ **CORRECTED 2026-07-20 — THE RECURSION WRAP IS NOT THE DEPLOYED PAIR.** See
`Dregg2.Circuit.FriDeployedHeightPairing`. `Accumulator::accumulate` binds `ir2_leaf_wrap_config()`
(`logBlowup = 6`) and `wrap_params()`'s `2^16` floor in ONE prove call, so the deployed domain is
`2^22` at the arity-2 `logBlowup = 6` knob set — `create_recursion_config` (`lb = 3`) is not on that
path. The statement below is TRUE (`recursionConfig` at `2^19` really does read `61`); what is wrong
is calling that pair "the deployed worst case". The deployed reading is **51**
(`FriDeployedHeightPairing.deployed_wrap_commitBits`), and `61` is refuted as the deployed number by
`FriDeployedHeightPairing.deployed_wrap_is_not_61`.

**⚑ THE RECURSION WRAP IS THE WEAKEST SHIPPED CONFIG ON BOTH COLUMNS AT ITS OWN HEIGHT.**
`recursionConfig` is already the tree's named weakest link on the query ledger (`johnsonBits = 71`
at `pow = 14`); at its MEASURED `|D⁽⁰⁾| = 2^19` it is also the weakest on the commit column (`61`).
⚑ And the two weakest-link facts are independent: on the FIXTURE height the commit column's weakest
configs are the `logBlowup = 6` ones (`71`), because `ε_C` carries `1/(2ρ^{3/2})` — a bigger blowup
HURTS `ε_C` while helping every query ledger. "The weakest config" is a property of a COLUMN, not of
the system. -/
theorem recursion_is_weakest_on_the_commit_column_too :
    (friLedger recursionConfig).johnsonBits = 71 ∧
      (friCommitLedger recursionConfig 19 7).commitBits = 61 ∧
      (friCommitLedger ir2LeafWrapConfig 12 7).commitBits = 71 := by
  refine ⟨recursion_ledger_johnsonBits, ?_, wrap_ledger_commitBits⟩
  refine commitBits_eq_of_bracket _ _ _ 61 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, recursionConfig]

/-- **⚑ THE CEILING — no `numQueries` and no `powBits` can pass `ε_C`.** `q = 200` and `pow = 27`
(plonky3's practical maximum) balloon the query columns to `627`/`1227` and leave the commit column
exactly where `q = 19`, `pow = 16` left it. `ε_C`'s formula contains neither knob. The only lever
is `extDeg`, worth exactly `log₂ p ≈ 30.91` bits per degree (`ε_C ∝ 1/p^extDeg`).

⚑ **This is what withdraws "proven Johnson 128 at ext-degree 4".** The query ledger's monotone
`q·lb/2` reading is what made `128` look purchasable; under the term BCIKS20 actually carries, no
`(q, pow)` at ext-degree `4` reaches it.

⚠ **Scope, exactly as stated.** This theorem is about `numQueries` and `powBits` — the two knobs
`FriParams` carries. plonky3 has a THIRD: `commit_proof_of_work_bits` (`fri/src/config.rs:18`),
ground per fold round BEFORE `β` (`prover.rs:224`), i.e. against exactly the commit phase `ε_C`
bounds, and absent from plonky3's own `conjectured_soundness_bits`. Every dregg config sets it to
`0`, so the ceiling holds for what ships; it is not a theorem about the protocol, and this statement
does not claim to be one. -/
theorem query_and_pow_cannot_pass_epsC :
    (friCommitLedger ir2LeafWrapConfig 12 7).commitBits
        = (friCommitLedger { ir2LeafWrapConfig with numQueries := 200, powBits := 27 } 12 7).commitBits
      ∧ (friLedger { ir2LeafWrapConfig with numQueries := 200, powBits := 27 }).johnsonBits = 627 := by
  refine ⟨?_, by norm_num [friLedger, ir2LeafWrapConfig]⟩
  -- `epsCNum` does not mention `numQueries` or `powBits`, so the two terms are literally equal.
  rfl

/-- **⚑ THE TWO-COLUMN LAW, QUANTITATIVELY VINDICATED.** `query_ledger_does_not_determine_perFold`
already showed the query and per-fold columns are independent. The commit column makes the point
sharper: it moves under a parameter (`logD0`) that BOTH other columns are blind to, and does not
move under the parameters (`numQueries`, `powBits`) that drive the query column. Three columns, three
different dependencies — no single product could track them, and any headline that multiplied them
would be tracking none. -/
theorem three_columns_three_dependencies :
    -- the trace moves `commitBits` and NOTHING else
    (friCommitLedger ir2LeafWrapConfig 12 7).commitBits
        ≠ (friCommitLedger ir2LeafWrapConfig 20 7).commitBits ∧
    -- the queries move `johnsonBits` and NOT `commitBits`
    (friLedger ir2LeafWrapConfig).johnsonBits
        ≠ (friLedger { ir2LeafWrapConfig with numQueries := 200, powBits := 27 }).johnsonBits ∧
    (friCommitLedger ir2LeafWrapConfig 12 7).commitBits
        = (friCommitLedger { ir2LeafWrapConfig with numQueries := 200, powBits := 27 } 12 7).commitBits := by
  refine ⟨?_, ?_, rfl⟩
  · rw [wrap_ledger_commitBits]
    rw [show (friCommitLedger ir2LeafWrapConfig 20 7).commitBits = 55 from by
      refine commitBits_eq_of_bracket _ _ _ 55 ?_ ?_ <;>
        norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapConfig]]
    norm_num
  · norm_num [friLedger, ir2LeafWrapConfig]

/-! ## §7. THE EXPORT IS THE LEDGER — the `@[export]`ed wire is not a separate path.

`friLedgerFFI` is the C-ABI entry the Rust gate calls. These `#guard`s check it renders the SAME
`friLedger` the theorems above are about, at the shipped configs — so a Rust caller reading the wire
reads the proved numbers, and a wire-format edit that dropped a column would go red HERE, in Lean,
before the Rust test ever ran. -/

-- ⚑ The wire carries NINE inputs (the six knobs + `logD0` + BCIKS20's `m` + `commitPow`) and TEN
-- columns (the six + `commitBits` + the three eq.-(20) columns `commitPowBranch`, `johnsonBitsAtM`,
-- `compositeBits`). `logD0 = 12` is the COST FIXTURE's FRI domain — a 1-effect turn — and is used
-- below only to exercise the wire against a known reading. It is NOT the deployed height: those are
-- measured in `circuit-prove/tests/fri_trace_height_measure.rs` and read out per config by
-- `ledger_commitBits_at_measured_heights` (the recursion wrap's 2^19 gives 61, not 71). `m = 7` is
-- the proximity parameter that happens to optimise the deployed composite; it is an input, not a fact.
--
-- ⚑ EVERY VECTOR BELOW PASSES `commitPow = 0`, and that is not padding — it is the DEPLOYED VALUE at
-- all ten shipped construction sites, now readable as `IR2_FRI_COMMIT_POW_BITS`,
-- `IR2_INNER_COMMIT_POW_BITS`, `PROD_FRI_COMMIT_POW_BITS`, `ZK_FRI_COMMIT_POW_BITS`,
-- `RECURSION_FRI_COMMIT_POW_BITS`, `OUTER_FRI_COMMIT_POW_BITS`. At `0` the `commitPowBranch` column
-- IS `commitBits`, which is why adding it moved no number the tree already published.

-- The deployed IR-v2 wrap: arity 8, |κ| = 64, |Good| ≤ 14112, 109 per-fold, 73 Johnson, 130 capacity,
-- and commit-phase 71 — the term the 73 drops. ⚑ The composite reads 70, not 73: at ONE m = 7 the
-- honest Johnson branch is 71, not the m → ∞ 73, and min{71, 71} − 1 = 70.
#guard friLedgerFFI "6 19 16 3 0 4 12 7 0" == "8 64 14112 109 73 130 71 71 71 70"
-- The rotated leaf wrap (arity 2 at logBlowup 6) — the one config the ~112.6 describes.
#guard friLedgerFFI "6 19 16 1 0 4 12 7 0" == "2 64 2016 112 73 130 71 71 71 70"
-- The gnark ETH-wrap's outer shrink: arity 2 at logBlowup 3 ⇒ |κ| = 8, |Good| ≤ 28, 118 bits.
#guard friLedgerFFI "3 38 16 1 0 4 12 7 0" == "2 8 28 118 73 130 75 75 69 68"
-- v1 production: arity 8 at logBlowup 3.
#guard friLedgerFFI "3 38 16 3 0 4 12 7 0" == "8 8 196 116 73 130 75 75 69 68"
-- The recursion default: powBits 14 ⇒ capacity exactly 128.
#guard friLedgerFFI "3 38 14 1 0 4 12 7 0" == "2 8 28 118 71 128 75 75 67 66"

-- ⚑ THE COMMIT COLUMN IS NOT TRACE-INVARIANT — the mutation canary, on the wire. Same config, a
-- 2^20 FRI domain instead of 2^12: the per-fold and query columns do not move at all, and the
-- commit column falls 71 → 55 (~2 bits per trace doubling, because ε_C ∝ |D⁽⁰⁾|²). The COMPOSITE
-- follows it down (70 → 54) while `johnsonBitsAtM` stands still at 71 — the whole content of the
-- eq.-(20) `min` in one pair of vectors.
#guard friLedgerFFI "6 19 16 3 0 4 20 7 0" == "8 64 14112 109 73 130 55 55 71 54"
#guard friLedgerFFI "6 19 16 3 0 4 13 7 0" == "8 64 14112 109 73 130 69 69 71 68"

-- ⚑ THE CEILING, AND THE SHARPEST READING IN THIS FILE. `ε_C` contains no `numQueries` and no
-- `powBits`. Buy queries to `200` and PoW to the practical maximum `27` and the query columns
-- balloon — Johnson `73 → 627`, capacity `130 → 1227`, `johnsonBitsAtM` `71 → 607` — while the
-- commit column does not move one bit off `71` AND THE COMPOSITE DOES NOT MOVE OFF `70`. The query
-- ledger's monotone `q·lb/2` reading is what makes "proven 128" look purchasable; ε_C is what says
-- it is not. No `(q, pow)` passes this.
#guard friLedgerFFI "6 200 27 3 0 4 12 7 0" == "8 64 14112 109 627 1227 71 71 607 70"

-- ⚑ …AND `commitPow` IS THE KNOB THAT DOES MOVE IT — but ONLY once the queries have been bought
-- first, which is the whole shape of the eq.-(20) `min` and the reason neither column alone is a
-- posture. At the DEPLOYED query count grinding is worth NOTHING: `commitPow = 1` lifts the commit
-- branch 71 → 72 and the composite does not move off 70, because `johnsonBitsAtM` (71) has already
-- taken over the `min`. Buy the queries (`q = 200`, `pow = 27`) and the Johnson branch goes to 607
-- — and only THEN does grinding buy bits one-for-one: 70 → 86 at `commitPow = 16`, 70 → 100 at the
-- `30`-bit grind cap. A caller cannot read either knob alone as a free ride.
#guard friLedgerFFI "6 19 16 3 0 4 12 7 1" == "8 64 14112 109 73 130 71 72 71 70"
#guard friLedgerFFI "6 200 27 3 0 4 12 7 16" == "8 64 14112 109 627 1227 71 87 607 86"
#guard friLedgerFFI "6 200 27 3 0 4 12 7 30" == "8 64 14112 109 627 1227 71 101 607 100"

-- FAIL-CLOSED: a malformed wire, the OLD EIGHT-field wire (the shape this replaced — it is REFUSED,
-- not reinterpreted as nine with a defaulted `commitPow`, because a defaulted grinding knob is this
-- export choosing a soundness number on the caller's behalf), the older six-field wire, `m < 3`
-- (BCIKS20 Thm 8.3's own hypothesis — outside it the formula is not the paper's), and a `commitPow`
-- above the BabyBear single-witness grind cap (where plonky3's `grind` asserts out, so the number
-- would describe an object no prover can produce) all refuse rather than answer.
#guard friLedgerFFI "6 19 16" == ""
#guard friLedgerFFI "6 19 16 3 0 4" == ""
#guard friLedgerFFI "6 19 16 3 0 4 12 7" == ""
#guard friLedgerFFI "6 19 16 3 0 4 12 2 0" == ""
#guard friLedgerFFI "not a config" == ""
#guard friLedgerFFI "6 19 16 3 0 64 12 7 0" == ""
#guard friLedgerFFI "6 19 16 3 0 4 12 7 31" == ""

/-! ## §8. Axiom hygiene.

⚑ `#assert_axioms` is BLIND TO HYPOTHESES. Every theorem below is kernel-clean; the per-fold results
(`ledger_good_card_le`, `ledger_perFold_soundness`, and every instance that routes through them) carry
the `M = 1` phase-injectivity hypothesis `hΦ`, because they are PARAMETRIC in the config and mention
no setup. `hΦ` is DISCHARGED from farness at every shipped config in
`Dregg2.Circuit.FriArityFiberDischarge` (`phase_injective_of_far`; `arity8_phase_injective` at the
deployed arity 8) — a theorem there, not something this block could ever have told you. Kernel-clean
is not hypothesis-free, and this block does not claim it is. -/

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
#assert_axioms rate_pos
#assert_axioms rate_rpow_three_halves
#assert_axioms ceilDiv_two
#assert_axioms ceilDiv_three_mul_two
#assert_axioms sqrt_rate_ge
#assert_axioms one_div_sqrt_rate_le
#assert_axioms one_div_rate_three_halves_le
#assert_axioms ledger_epsC_le
#assert_axioms ledger_commitBits_sound
#assert_axioms ledger_epsC_soundness
#assert_axioms wrap_ledger_commitBits
#assert_axioms ledger_commitBits_at_measured_heights
#assert_axioms recursion_is_weakest_on_the_commit_column_too
#assert_axioms commit_column_is_not_trace_invariant
#assert_axioms query_and_pow_cannot_pass_epsC
#assert_axioms three_columns_three_dependencies

end Dregg2.Circuit.FriLedgerSound
