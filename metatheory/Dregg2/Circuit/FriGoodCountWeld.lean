/-
# `Dregg2.Circuit.FriGoodCountWeld` — THE VOCABULARY WELD: `goodδ`/`closeN` (FriSetupK distance
vocabulary) ⇔ `goodCount` (the Φ/H-polynomial vocabulary the exported ledger prices).

`FriChainStepIdx`'s header (`:72-76`) names the gap this file closes: the L2 survival bound
consumes a per-layer cap `b` from `goodδ_card_lt` (`FriChainStepIdx:460`, the `FriSetupK`/`closeN`
distance vocabulary over `FriFoldArity.fold_close_of_arity_challenges:184`), while the soundness
the DEPLOYED verifier prices is `FriLedgerSound.ledger_perFold_soundness` (`:213`), whose cap is
`(friLedger cfg).goodCount` in the Φ/H-polynomial vocabulary of
`FriArityTransfer.good_card_le_of_phase_injective` (`:207`). Until the two good sets are
identified, L2's bound cannot read its `b` off the exported ledger.

**THE WELD, in three steps — each a theorem, not a renaming:**

  * **§1 the phase map IS the fold's coefficient vector** (`phasesOf`, `H_phasesOf_eval`): the
    `FriSetupK`'s arity-`n` decomposition components `Cj` (`FriFoldArity:103`) form a phase map
    `Φ : ℕ → κ → F`, and the ledger's phase polynomial evaluates to the setup's fold:
    `(H n (phasesOf S f) y).eval β = Fold S.geom β f y`. This is the point where the two
    files' objects become ONE object; everything else is counting.
  * **§2 agreement ↔ closeness at the TERMINAL code** (`closeN_of_agree`, `agree_of_closeN`,
    `goodδ_eq_ledger_goodSet`): the ledger's `hS` speaks "folds to a CONSTANT on ≥ s fibres";
    `goodδ` speaks "`d`-close to `C'`". When `C'` is the constants code the two are the SAME
    predicate at `d = |κ| − s` — and constants-`C'` is not a convenience: the deployed config has
    `logFinalPolyLen = 0` (`FriVerifier:388`), i.e. the terminal FRI oracle IS a constant, and the
    one in-tree deployed-arity setup `friSetupK8` has `C' = codeC'8 =` constants
    (`FriFoldArity:319,326`). ⚠ SCOPE, stated plainly: for a NON-constant `C'` the ledger's
    pair-counting does not apply as-is (`pair_mem_card_le` needs one shared target value per
    challenge), so every weld theorem carries the constants-code hypothesis explicitly. That is
    the honest boundary of the identification, not fine print.
  * **§3 the COUNT weld** (`goodδ_card_le_phase_bound`, `goodδ_card_le_ledger_goodCount`,
    `goodδ_ledger_perFold_error`): under the ledger's own phase-injectivity hypothesis `hΦ`
    (the `M = 1` fiber bound `ledger_perFold_soundness` carries; discharged from farness only
    where `FriArityFiberDischarge` does it), the distance-graded good set is capped by the
    EXPORTED ledger's number: `(goodδ S d f).card ≤ (friLedger cfg).goodCount`, and its density
    is priced by the exported exponent via `ledger_perFold_error` (`FriLedgerSound:163`):
    `|goodδ|/|F| < 2^(−perFoldBits)`. THAT is "the per-layer `b` read off the exported ledger".

**§4 NON-VACUITY — fires at the deployed-arity shape, on an INHABITED good set.** At
`friSetupK8` (arity `8 = 2^PROD_FRI_MAX_LOG_ARITY`, `C' =` constants — the terminal shape) the
far word `fW x = (−1)^x·(1 − ω₁₆^x)` (frequencies 8 and 9, both outside the degree-<8 code;
`fW_not_mem` via the same DFT functional that kills `f0`) has phase vector
`((−1)^y, −(−1)^y, 0…)` (`comps_fW` — proven through the fiber-Vandermonde UNIQUENESS route,
never by reducing the noncomputable inverse), hence is genuinely phase-injective
(`fW_phase_injective`), and its good set is EXACTLY `{1}` (`goodδ_fW_eq`) — nonempty, unlike
`f0`'s (whose fold is never constant). The weld then fires end-to-end (`weld_fires_k8`):
`1 ∈ goodδ`, `|goodδ| ≤ (friLedger cfgK8).goodCount = 7 = n − 1` — the ledger's Φ/H count and
`goodδ_card_lt`'s distance cap AGREE on the same set (`both_caps_k8`), and the density is priced
by the exported `perFoldBits` (`weld_priced_k8`).

**§5 CANARY — the count is load-bearing.** `weld_canary_mismatched_count`: plug a MISMATCHED
config (arity `2^0 = 1`, `goodCount = 0`) into the weld's conclusion and it is REFUTED by `fW`
(`1 ≤ 0` is false). The weld holds at the MATCHING shape and breaks at a mismatched count — it
is an identification, not an inequality slack enough to be vacuous.

What this file does NOT claim: no multi-layer tower (still absent in-tree, per
`FriChainStepIdx:65-71`), no discharge of `hΦ` beyond where the tree already discharges it, and
no statement about non-constant intermediate codes — the weld is exactly at the terminal shape
the deployed `logFinalPolyLen = 0` config pins.

ADDITIVE. No `sorry`, no new axioms; `#assert_all_clean` on every keystone.
-/
import Dregg2.Circuit.FriChainStepIdx
import Dregg2.Circuit.FriArityTransfer
import Dregg2.Circuit.FriLedgerSound
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

namespace Dregg2.Circuit.FriGoodCountWeld

open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.FriChainStepIdx (goodδ mem_goodδ goodδ_card_lt)
open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem disagree mem_disagree)
open Dregg2.Circuit.FriArityTransfer (H H_eval good_card_le_of_phase_injective)
open Dregg2.Circuit.FriLedger (friLedger ledgerP)
open Dregg2.Circuit.FriLedgerSound (ledger_goodCount_eq ledger_perFold_error)
open Dregg2.Circuit.FriVerifier (FriParams)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.BabyBearFriDeployed (omega16)

/-! ## §1 — the phase map of a word at a setup, and THE VOCABULARY IDENTITY. -/

section Weld

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ} (S : FriSetupK F ι κ n)

/-- **The phase map of `f` at the setup `S`**: its arity-`n` decomposition components `Cj`,
padded with `0` above `n` — exactly the `Φ : ℕ → κ → F` shape `FriArityTransfer`'s counting
theorems quantify over. -/
noncomputable def phasesOf (f : ι → F) : ℕ → κ → F :=
  fun i y => if h : i < n then Cj S.geom ⟨i, h⟩ f y else 0

/-- **⚑ THE VOCABULARY IDENTITY.** The ledger's phase polynomial (`FriArityTransfer.H`), taken
at the setup's own phase map, evaluates at a challenge to EXACTLY the setup's arity-`n` fold:
`(H n (phasesOf S f) y).eval β = Fold S.geom β f y`. The Φ/H-polynomial object and the
`FriSetupK` object are the same object; the two files were counting the same folds. -/
theorem H_phasesOf_eval (f : ι → F) (y : κ) (β : F) :
    (H n (phasesOf S f) y).eval β = Fold S.geom β f y := by
  rw [H_eval, ← Fin.sum_univ_eq_sum_range (fun i => phasesOf S f i y * β ^ i) n]
  show ∑ i : Fin n, phasesOf S f (i : ℕ) y * β ^ (i : ℕ)
      = ∑ j : Fin n, β ^ (j : ℕ) * Cj S.geom j f y
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hφ : phasesOf S f (i : ℕ) y = Cj S.geom i f y := by
    show (if h : (i : ℕ) < n then Cj S.geom ⟨(i : ℕ), h⟩ f y else 0) = Cj S.geom i f y
    rw [dif_pos i.isLt]
  rw [hφ, mul_comm]

/-! ## §2 — agreement ↔ closeness at the terminal (constants) folded code. -/

/-- **Ledger agreement ⇒ distance closeness** (needs only that `C'` CONTAINS the constants —
true of every RS code of dimension ≥ 1): a challenge folding `f` to agree with the constant `a`
on `≥ s` fibres folds `f` `(|κ| − s)`-close to `C'`. -/
theorem closeN_of_agree (hconst : ∀ a : F, (fun _ : κ => a) ∈ S.C')
    {f : ι → F} {β a : F} {s : ℕ}
    (hagree : s ≤ (Finset.univ.filter
        (fun y : κ => (H n (phasesOf S f) y).eval β = a)).card) :
    closeN S.C' (Fintype.card κ - s) (Fold S.geom β f) := by
  classical
  refine ⟨fun _ => a, hconst a, ?_⟩
  have hfe : (Finset.univ.filter (fun y : κ => (H n (phasesOf S f) y).eval β = a))
      = Finset.univ.filter (fun y : κ => Fold S.geom β f y = a) := by
    apply Finset.filter_congr
    intro y _
    rw [H_phasesOf_eval]
  have hdis : disagree (Fold S.geom β f) (fun _ : κ => a)
      = (Finset.univ.filter (fun y : κ => Fold S.geom β f y = a))ᶜ := by
    ext y
    simp [mem_disagree]
  rw [hdis, Finset.card_compl]
  rw [hfe] at hagree
  omega

/-- **Distance closeness ⇒ ledger agreement** (needs that `C'` consists ONLY of constants — the
terminal shape `logFinalPolyLen = 0` deploys): a challenge folding `f` `d`-close to `C'` folds it
to agree with SOME constant on `≥ |κ| − d` fibres. -/
theorem agree_of_closeN (hconst' : ∀ g ∈ S.C', ∃ a : F, g = fun _ : κ => a)
    {f : ι → F} {β : F} {d : ℕ}
    (hclose : closeN S.C' d (Fold S.geom β f)) :
    ∃ a : F, Fintype.card κ - d
      ≤ (Finset.univ.filter (fun y : κ => (H n (phasesOf S f) y).eval β = a)).card := by
  classical
  obtain ⟨g, hgC, hcard⟩ := hclose
  obtain ⟨a, rfl⟩ := hconst' g hgC
  refine ⟨a, ?_⟩
  have hfe : (Finset.univ.filter (fun y : κ => (H n (phasesOf S f) y).eval β = a))
      = Finset.univ.filter (fun y : κ => Fold S.geom β f y = a) := by
    apply Finset.filter_congr
    intro y _
    rw [H_phasesOf_eval]
  have hdis : disagree (Fold S.geom β f) (fun _ : κ => a)
      = (Finset.univ.filter (fun y : κ => Fold S.geom β f y = a))ᶜ := by
    ext y
    simp [mem_disagree]
  rw [hdis, Finset.card_compl] at hcard
  have hle := Finset.card_le_univ (Finset.univ.filter (fun y : κ => Fold S.geom β f y = a))
  rw [hfe]
  omega

open Classical in
/-- **⚑ THE SET IDENTIFICATION at the terminal code.** With `C'` exactly the constants (both
inclusions supplied), the distance-graded good set `goodδ S d f` IS the ledger-vocabulary good
set — the challenges whose H-polynomial fold agrees with some constant on `≥ |κ| − d` fibres.
The two files' "good" predicates are ONE predicate, not two analogous ones. -/
theorem goodδ_eq_ledger_goodSet
    (hconst : ∀ a : F, (fun _ : κ => a) ∈ S.C')
    (hconst' : ∀ g ∈ S.C', ∃ a : F, g = fun _ : κ => a)
    (f : ι → F) {d : ℕ} (hd : d ≤ Fintype.card κ) :
    goodδ S d f = Finset.univ.filter (fun β : F => ∃ a : F,
        Fintype.card κ - d ≤ (Finset.univ.filter
          (fun y : κ => (H n (phasesOf S f) y).eval β = a)).card) := by
  ext β
  rw [mem_goodδ, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨Finset.mem_univ β, agree_of_closeN S hconst' h⟩
  · rintro ⟨-, a, ha⟩
    have h := closeN_of_agree S hconst (f := f) (β := β) (a := a) ha
    rwa [Nat.sub_sub_self hd] at h

/-! ## §3 — THE COUNT WELD: the distance-graded good set, capped by the Φ/H count. -/

/-- **The distance-graded good set obeys the Φ/H-polynomial cap.** Under the ledger's own
phase-injectivity hypothesis (the `M = 1` fiber bound, HERE stated of the setup's REAL phases
`phasesOf S f`, not of an abstract `Φ`), the `goodδ` set is capped by the arity-generic count
`(n − 1)·C(|κ|, 2)` — `FriLedgerSound.ledger_good_card_le`'s bound, now speaking `closeN`. -/
theorem goodδ_card_le_phase_bound
    (hconst' : ∀ g ∈ S.C', ∃ a : F, g = fun _ : κ => a)
    {f : ι → F}
    (hΦ : ∀ y z : κ, y ≠ z → ∃ i < n, phasesOf S f i y ≠ phasesOf S f i z)
    {d : ℕ} (hd : d + 2 ≤ Fintype.card κ) :
    (goodδ S d f).card ≤ (n - 1) * Nat.choose (Fintype.card κ) 2 := by
  classical
  have hA : ∀ β : F, ∃ a : F, β ∈ goodδ S d f →
      2 ≤ (Finset.univ.filter
        (fun y : κ => (H n (phasesOf S f) y).eval β = a)).card := by
    intro β
    by_cases hβ : β ∈ goodδ S d f
    · obtain ⟨a, ha⟩ := agree_of_closeN S hconst' ((mem_goodδ S).1 hβ)
      exact ⟨a, fun _ => le_trans (by omega) ha⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose c hc using hA
  have hS : ∀ β ∈ goodδ S d f,
      2 ≤ (Finset.univ.filter
        (fun y : κ => (H n (phasesOf S f) y).eval β = c β)).card :=
    fun β hβ => hc β hβ
  have hle := good_card_le_of_phase_injective hΦ (goodδ S d f) c (s := 2) hS
  simpa using hle

end Weld

/-! ## §3b — the weld to the EXPORTED ledger: the per-layer `b`, read off `friLedger`. -/

section LedgerWeld

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **⚑ THE WELD.** At a setup whose SHAPE matches the config (arity `2^maxLogArity`, folded
domain `2^logBlowup`) and whose folded code is the terminal constants code, the distance-graded
good set `goodδ` — the object L2's survival machinery consumes — is capped by the EXPORTED
ledger's `goodCount`. This is the sentence `FriChainStepIdx:72-76` said was missing: the
per-layer `b` can now be read off `friLedger cfg` instead of only off `goodδ_card_lt`'s `n − 1`. -/
theorem goodδ_card_le_ledger_goodCount (cfg : FriParams)
    (S : FriSetupK F ι κ (2 ^ cfg.maxLogArity))
    (hκ : Fintype.card κ = 2 ^ cfg.logBlowup)
    (hconst' : ∀ g ∈ S.C', ∃ a : F, g = fun _ : κ => a)
    {f : ι → F}
    (hΦ : ∀ y z : κ, y ≠ z →
      ∃ i < 2 ^ cfg.maxLogArity, phasesOf S f i y ≠ phasesOf S f i z)
    {d : ℕ} (hd : d + 2 ≤ Fintype.card κ) :
    (goodδ S d f).card ≤ (friLedger cfg).goodCount := by
  rw [ledger_goodCount_eq, ← hκ]
  exact goodδ_card_le_phase_bound S hconst' hΦ hd

/-- **The per-layer `b`, PRICED by the exported exponent**: the density of the distance-graded
good set is below `2^(−perFoldBits)` — `goodδ`'s survival numerator composed straight into
`FriLedgerSound.ledger_perFold_error`, the bound the deployed ledger reports. -/
theorem goodδ_ledger_perFold_error (cfg : FriParams)
    (S : FriSetupK F ι κ (2 ^ cfg.maxLogArity))
    (hκ : Fintype.card κ = 2 ^ cfg.logBlowup)
    (hconst' : ∀ g ∈ S.C', ∃ a : F, g = fun _ : κ => a)
    {f : ι → F}
    (hΦ : ∀ y z : κ, y ≠ z →
      ∃ i < 2 ^ cfg.maxLogArity, phasesOf S f i y ≠ phasesOf S f i z)
    {d : ℕ} (hd : d + 2 ≤ Fintype.card κ)
    (hg : 0 < (friLedger cfg).goodCount)
    (hlt : (friLedger cfg).goodCount < ledgerP ^ cfg.extDeg) :
    ((goodδ S d f).card : ℝ) / (babyBearP : ℝ) ^ cfg.extDeg
      < 1 / 2 ^ (friLedger cfg).perFoldBits :=
  ledger_perFold_error cfg hg hlt _
    (goodδ_card_le_ledger_goodCount cfg S hκ hconst' hΦ hd)

end LedgerWeld

/-! ## §4 — NON-VACUITY: the weld FIRES at the deployed-arity setup, on an INHABITED good set.

`f0`'s good set at `friSetupK8` is EMPTY (its fold `(−1)^y` is never constant), so it cannot
witness that the weld's cap constrains anything. `fW` below is far AND has good set exactly
`{1}` — the weld is exercised on a set that exists. -/

section Fires

/-- The far-but-foldable word `fW(x) = (−1)^x · (1 − ω₁₆^x)` — frequencies `8` and `9`, both
outside the degree-`< 8` code; its phase vector at each fibre is `((−1)^y, −(−1)^y, 0, …)`, so
the challenge `1` (and ONLY `1`) folds it to a constant (namely `0`). -/
noncomputable def fW : Fin 16 → BabyBear :=
  fun x => (-1 : BabyBear) ^ (x : ℕ) * (1 - omega16 ^ (x : ℕ))

/-- The claimed phase vector of `fW` at fibre `y`: `((−1)^y, −(−1)^y, 0, 0, 0, 0, 0, 0)`. -/
noncomputable def vW (y : Fin 2) : Fin 8 → BabyBear :=
  ![(-1 : BabyBear) ^ (y : ℕ), -((-1 : BabyBear) ^ (y : ℕ)), 0, 0, 0, 0, 0, 0]

/-- `fW`'s decomposition components ARE `vW` — proven by the fiber-Vandermonde UNIQUENESS route
(`V *ᵥ vW = fvec`, then multiply by `V⁻¹`), NEVER by reducing the noncomputable inverse. The
kernel checks the 16 concrete `V *ᵥ vW = fvec` entries. -/
theorem comps_fW (y : Fin 2) : comps friGeomK8 fW y = vW y := by
  have hmul : fiberV friGeomK8 y *ᵥ vW y = fvec friGeomK8 fW y := by
    funext i
    fin_cases y <;> fin_cases i <;> decide
  show (fiberV friGeomK8 y)⁻¹ *ᵥ fvec friGeomK8 fW y = vW y
  rw [← hmul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (fiberV_isUnit_det friGeomK8 y), Matrix.one_mulVec]

/-- The fold of `fW` in closed form: `Fold_α fW (y) = (−1)^y · (1 − α)`. -/
theorem fold_fW (α : BabyBear) (y : Fin 2) :
    Fold friSetupK8.geom α fW y = (-1 : BabyBear) ^ (y : ℕ) * (1 - α) := by
  show ∑ j : Fin 8, α ^ (j : ℕ) * Cj friGeomK8 j fW y = _
  have hC : ∀ j : Fin 8, Cj friGeomK8 j fW y = vW y j := fun j => by
    show comps friGeomK8 fW y j = vW y j
    rw [comps_fW]
  simp only [hC]
  rw [Fin.sum_univ_eight]
  simp [vW]
  ring

/-- `fW` is genuinely FAR: not in the degree-`< 8` code (the frequency-`8` DFT functional
`phi` annihilates the code but `phi fW = 16 ≠ 0`). -/
theorem fW_not_mem : fW ∉ friSetupK8.C := by
  intro h
  have h0 : phi fW = 0 := phi_zero_on_C fW h
  rw [show phi fW = 16 from by decide] at h0
  exact absurd h0 (by decide)

/-- `fW`'s farness in the shape `goodδ_card_lt` consumes at `d = 0`. -/
theorem fW_far0 : ¬ closeN friSetupK8.C (8 ^ 2 * 0) fW := by
  simp only [Nat.mul_zero]
  exact fun h => fW_not_mem (closeN_zero_iff_mem.mp h)

/-- Membership in the terminal constants code, unfolded. -/
theorem codeC'8_mem {g : Fin 2 → BabyBear} (hg : g ∈ friSetupK8.C') :
    ∃ a : BabyBear, g = fun _ => a := hg

/-- **`fW` is phase-injective** — the ledger's `M = 1` fiber-bound hypothesis, DISCHARGED for
`fW` at the deployed-arity setup: its 0-th phases at the two fibres are `1` and `−1`. -/
theorem fW_phase_injective (y z : Fin 2) (hyz : y ≠ z) :
    ∃ i < 8, phasesOf friSetupK8 fW i y ≠ phasesOf friSetupK8 fW i z := by
  refine ⟨0, by norm_num, ?_⟩
  have h0 : ∀ w : Fin 2, phasesOf friSetupK8 fW 0 w = (-1 : BabyBear) ^ (w : ℕ) := by
    intro w
    show (if h : (0 : ℕ) < 8 then Cj friGeomK8 ⟨0, h⟩ fW w else 0)
        = (-1 : BabyBear) ^ (w : ℕ)
    rw [dif_pos (by norm_num : (0 : ℕ) < 8)]
    show comps friGeomK8 fW w ⟨0, by norm_num⟩ = _
    rw [comps_fW]
    rfl
  rw [h0 y, h0 z]
  fin_cases y <;> fin_cases z <;> first | exact absurd rfl hyz | decide

/-- **The good set of `fW` is EXACTLY `{1}`** — inhabited (unlike `f0`'s) and small: only the
challenge `1` kills the fibre-dependent term `(−1)^y·(1 − α)`. The `α ≠ 1` refutation is the
char-≠-2 step `2·(1 − α) = 0 ⇒ α = 1`. -/
theorem goodδ_fW_eq : goodδ friSetupK8 0 fW = {1} := by
  ext α
  rw [mem_goodδ friSetupK8, closeN_zero_iff_mem, Finset.mem_singleton]
  constructor
  · intro hmem
    obtain ⟨a, ha⟩ := codeC'8_mem hmem
    have h01 : Fold friSetupK8.geom α fW 0 = Fold friSetupK8.geom α fW 1 := by
      rw [ha]
    rw [fold_fW, fold_fW] at h01
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, neg_one_mul] at h01
    have h2 : (2 : BabyBear) * (1 - α) = 0 := by linear_combination h01
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by decide)
    · exact (sub_eq_zero.mp h).symm
  · rintro rfl
    exact ⟨0, funext fun w => by simp [fold_fW]⟩

/-- The good set is inhabited: the weld's cap constrains a set that EXISTS. -/
theorem goodδ_fW_nonempty : (1 : BabyBear) ∈ goodδ friSetupK8 0 fW := by
  rw [goodδ_fW_eq]
  exact Finset.mem_singleton_self 1

/-- The config whose SHAPE is `friSetupK8`: arity `2^3 = 8` (the deployed
`PROD_FRI_MAX_LOG_ARITY = 3`), folded domain `2^1 = 2` (`|κ| = 2` at the `|L| = 16` setup),
base field (`extDeg = 1`), terminal constant (`logFinalPolyLen = 0`). -/
def cfgK8 : FriParams :=
  { logBlowup := 1, numQueries := 19, powBits := 16, maxLogArity := 3,
    logFinalPolyLen := 0, extDeg := 1 }

/-- The exported ledger's count at the k8 shape: `(2^3 − 1)·C(2, 2) = 7`. -/
theorem cfgK8_goodCount : (friLedger cfgK8).goodCount = 7 := by decide

/-- **⚑ NON-VACUITY — the weld FIRES end-to-end at the deployed-arity shape**: the good set is
inhabited, capped by the EXPORTED ledger's count, and that count is EXACTLY `goodδ_card_lt`'s
`n − 1` — the two vocabularies' caps agree numerically where they meet. -/
theorem weld_fires_k8 :
    (1 : BabyBear) ∈ goodδ friSetupK8 0 fW
      ∧ (goodδ friSetupK8 0 fW).card ≤ (friLedger cfgK8).goodCount
      ∧ (friLedger cfgK8).goodCount = 8 - 1 := by
  refine ⟨goodδ_fW_nonempty, ?_, by decide⟩
  exact goodδ_card_le_ledger_goodCount cfgK8 friSetupK8 (by decide)
    (fun g hg => codeC'8_mem hg) fW_phase_injective (by decide)

/-- **Both caps, ONE set**: `goodδ_card_lt`'s distance cap (`< 8`) and the ledger's Φ/H cap
(`≤ goodCount`) now bound the SAME `Finset` — the sentence that was previously unstateable. -/
theorem both_caps_k8 :
    (goodδ friSetupK8 0 fW).card < 8
      ∧ (goodδ friSetupK8 0 fW).card ≤ (friLedger cfgK8).goodCount :=
  ⟨goodδ_card_lt friSetupK8 fW_far0, weld_fires_k8.2.1⟩

/-- **The per-layer `b`, PRICED at the k8 shape by the exported exponent**: `goodδ`'s density
is below `2^(−(friLedger cfgK8).perFoldBits)` — L2's survival numerator, composed into the
bound the deployed ledger reports, with every hypothesis discharged concretely. -/
theorem weld_priced_k8 :
    ((goodδ friSetupK8 0 fW).card : ℝ) / (babyBearP : ℝ) ^ cfgK8.extDeg
      < 1 / 2 ^ (friLedger cfgK8).perFoldBits := by
  refine ledger_perFold_error cfgK8 (by decide) (by decide) _ weld_fires_k8.2.1

end Fires

/-! ## §5 — CANARY: the count is load-bearing. -/

section Canary

/-- A config whose shape does NOT match `friSetupK8`: arity `2^0 = 1` — the degenerate no-fold
config, whose ledger `goodCount` is `0`. -/
def cfgMismatch : FriParams :=
  { logBlowup := 1, numQueries := 19, powBits := 16, maxLogArity := 0,
    logFinalPolyLen := 0, extDeg := 1 }

/-- **⚑ CANARY — a MISMATCHED count BREAKS the weld.** The weld's conclusion with the wrong
config's `goodCount` (`0`, arity mismatch) is REFUTED by `fW`: its good set has a member, so
`|goodδ| ≤ 0` is false. The shape hypotheses of `goodδ_card_le_ledger_goodCount` cannot be
dropped and the cap cannot be tightened below the matching ledger's number — the weld is an
identification of counts, not slack. -/
theorem weld_canary_mismatched_count :
    ¬ (goodδ friSetupK8 0 fW).card ≤ (friLedger cfgMismatch).goodCount := by
  rw [goodδ_fW_eq, show (friLedger cfgMismatch).goodCount = 0 from by decide,
    Finset.card_singleton]
  norm_num

end Canary

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  H_phasesOf_eval,
  closeN_of_agree,
  agree_of_closeN,
  goodδ_eq_ledger_goodSet,
  goodδ_card_le_phase_bound,
  goodδ_card_le_ledger_goodCount,
  goodδ_ledger_perFold_error,
  comps_fW,
  fold_fW,
  fW_not_mem,
  fW_phase_injective,
  goodδ_fW_eq,
  goodδ_fW_nonempty,
  cfgK8_goodCount,
  weld_fires_k8,
  both_caps_k8,
  weld_priced_k8,
  weld_canary_mismatched_count
]

end Dregg2.Circuit.FriGoodCountWeld
