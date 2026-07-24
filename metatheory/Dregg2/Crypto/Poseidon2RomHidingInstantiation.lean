/-
# `Dregg2.Crypto.Poseidon2RomHidingInstantiation` — the DEPLOYED `BlindedSpanCommitment` welded to
the PROVED keyed-ROM hiding floor through ONE NAMED, PER-ADVERSARY ROM-instantiation assumption —
reduced-to, never axiomatized, with the UNIVERSAL form of the assumption REFUTED in-file.

## The ceiling this addresses

`KeyedRomHidingFloor.blindedSpanRomFamily` (§9 there) is a fresh keyed-ROM family whose
cardinalities MIRROR the deployed shape (`Fin (2^l)` blinding, `Fin (2^(8l+8))` digest), connected
to the real `Metatheory.Open.BlindedSpanHiding.BlindedSpanCommitment` — the deployed
`hash(span_digest8 ‖ C_T ‖ BLINDING ‖ 0)` wide-Poseidon2 leaf — by PROSE ONLY ("the named residual
is the ROM-modeling of Poseidon2"). TWO distinct gaps hid under that one sentence:

  1. **the asymptotic-shape gap**: `card (Fin (2^l)) = 2^l` equals the deployed blinding-felt count
     at NO `l` (`babyBearP = 2013265921` is odd — `mirrorFamily_card_never_deployed` pins it); the
     exact trap `RomCarrierSites` names on the collision side ("no `l` at which `Fin (2^l)` IS the
     deployed 31-bit BabyBear felt"); and
  2. **the ROM-instantiation gap proper**: a FIXED public sponge is not a SAMPLED oracle.

This file CLOSES gap 1 outright — `KeyedRomHidingFloor.hidingAdv_le` is parametric in the spaces,
so it is applied AT THE EXACT DEPLOYED CARDINALITIES (blinding space literally `Fin 2013265921`,
8-felt spans and digests), with no asymptotic mirror in the chain — and NAMES gap 2 as the single
honest assumption the deployed statement rests on, REDUCED TO, never assumed away.

## The construction

  * **§1 `fixedAcceptProb` / `fixedHidingAdv`** — the two-world hiding experiment AT A FIXED oracle
    `H₀ : Msg × B → R`: the challenger samples ONLY the hidden blinding `r` uniformly (the deployed
    fresh-felt distribution); the adversary is the SAME raw `HidingDistinguisher` the ROM floor
    quantifies over, so there is no transport map to get wrong — the two experiments differ in
    EXACTLY one place, whether the oracle is fixed or sampled.
  * **§2 `RomFaithfulHiding H₀ A`** — ⚑ THE NAMED ROM-INSTANTIATION ASSUMPTION, per adversary:
    `fixedHidingAdv H₀ A ≤ hidingAdv A` — "the fixed hash serves this adversary no better than a
    freshly sampled oracle would". This is the standard ROM heuristic stated as the inequality it
    actually is. A `def`/hypothesis, NEVER an `axiom` ([[feedback-no-named-carrier-laundering]]).
  * **§2 `fixedHidingAdv_le_of_romFaithful`** — the generic reduction: ROM-faithful + `Q`-query
    (`QueryHiding Q A`) ⟹ `fixedHidingAdv H₀ A ≤ 2Q/|B|`. One `le_trans` deep BY DESIGN: the whole
    proved content is the ROM floor (`hidingAdv_le`, information-theoretic counting), and the
    assumption is EXACTLY the one remaining step, visibly.
  * **§3 the deployed weld** — `deployedSpongeOracle D : Span × Blind → Digest` IS the deployed
    commitment map: `deployedSpongeOracle_spec` shows it is definitionally
    `decodeDigest (D.wideHash (tagCode ‖ span_digest8 ‖ C_T ‖ BLINDING ‖ 0))` — the very
    `BlindedSpanCommitment.commitAt` of `BlindedSpanHiding`, felts encoded/decoded faithfully
    (`spanList_injective`, `decodeDigest_spanList`). `Poseidon2RandomOracleInstantiation D A :=
    RomFaithfulHiding (deployedSpongeOracle D) A` is the named assumption AT the deployed object.
  * **§3 `deployed_blindedSpan_hiding_of_romInstantiation`** — ⚑⚑ THE DELIVERABLE: under the named
    instantiation, every `Q`-query adversary's two-world span-distinguishing advantage against the
    DEPLOYED blinded commitment is `≤ 2·Q / 2013265921` (`≤ 2·Q / 2^30` in the crude form). The
    deployed `BlindedSpanCommitment` inherits `hidingAdv_le` — CONCRETE numbers, not asymptotics.
  * **§4 BOTH POLES OF THE ASSUMPTION.** Satisfiable (`poseidon2RomInstantiation_satisfiable`) and
    — the load-bearing tooth — the UNIVERSAL (∀-adversary) form is FALSE at a structured sponge:
    `poseidon2RomInstantiation_not_universal` cooks a `BlindedSpanCommitment` whose `wideHash`
    leaks its input and exhibits a 0-QUERY adversary with fixed advantage `1` but ROM advantage `0`
    (`zeroQuery_hidingAdv_eq_zero`). A fixed hash is PUBLIC — its entire table is available at
    adversary-DESIGN time, so a `.pure`-leaf adversary can bake it in without one query. Hence the
    honest assumption is PER-ADVERSARY ("adversaries that use the sponge generically"), and any
    lane upgrading it to `∀ A` is asserting something REFUTED here. This is the hiding-side
    transplant of `RomBindingReduction`'s own verdict on fixed public hashes.

## HONEST HEADER — what is PROVED vs what is ASSUMED

PROVED (kernel-clean, no assumption): the reduction; the ROM floor under it (`hidingAdv_le`,
counting); the encoding faithfulness; the concrete-cardinality arithmetic; both poles of the named
assumption; the mirror-family cardinality mismatch. ASSUMED (the ONE named residual):
`Poseidon2RandomOracleInstantiation D A` — that the deployed wide Poseidon2 serves the given
query-bounded adversary no better than a sampled oracle. NOT dischargeable without idealization
(Canetti–Goldreich–Halevi: no fixed function realizes a random oracle against all adversaries —
and our §4 tooth is the finitary shadow of exactly that), so it is carried NAMED and per-adversary.

MODELING SCOPE, disclosed: (i) the adversary's oracle queries range over the CHALLENGE-SHAPED
domain `Span × Blind` — sponge calls at assembled preimages `tagCode ‖ span ‖ C_T ‖ blinding ‖ 0`
at the deployed tag; queries at other `List ℤ` points are outside the model (under a true ROM they
are independent of the challenge; at the fixed sponge that independence is part of the named
assumption). (ii) Digests are compared after `decodeDigest` (felt-wise `% p` into 8 limbs), which
is the identity on in-range deployed digests. (iii) The blinding is sampled uniformly from
`Fin babyBearP` — the deployed "fresh hidden blinding FELT", exactly.

## ⚑ SHARED WITH COLLISION-RESISTANCE? — the audit answer, stated plainly

Collision-resistance does NOT name this assumption in Lean. Its keyed-ROM tower
(`KeyedRomFloor.keyedRom_hard` → `RomBindingReduction` → `RomCarrierSites` → the re-pointed
`_binds_rom` sites) carries the SAME residual as a PROSE "modelling caveat" only
(`RomCarrierSites` header: "a deliberate, labelled idealisation … NOT a derivation"), and
`Poseidon2KeyedBridge`'s non-ROM route rests on `DomainSeparatedCREff` (a computational floor at
`IsPolyTime`), not on a ROM instantiation. So before this file the whole ROM tower shared ONE
UNNAMED gap. `RomFaithfulHiding` is its FIRST Lean-named form, and it is deliberately stated
GENERICALLY (any fixed `H₀` vs the sampled oracle, per adversary) so the collision face can adopt
the same discipline. It cannot literally REUSE this predicate: at a fixed sponge the collision
game has NO residual randomness at all (the tag is folded into the domain and the oracle is the
only sample — `RomBindingReduction`'s point that fixed-hash CR is a conjecture, not a game with a
sampled coordinate), whereas hiding retains the blinding sample, which is why a fixed-oracle
hiding advantage is even definable. Naming the collision face centrally, on this file's pattern,
is surfaced as follow-up work — not smuggled in here.

## The number this exposes (felt-width campaign adjacency)

The deployed blinding is ONE felt. The inherited bound is `2Q/2013265921 ≈ Q/2^30` — a ~31-bit
hiding budget: ~2^30 challenge-shaped sponge queries defeat span hiding OUTRIGHT (enumerate the
blinding). The asymptotic mirror family (`B = Fin (2^l)`) made this invisible; the deployed-
cardinality statement says it out loud. Same class as `docs/WOUND-felt-width-boundaries-2026-07-19`.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, NO new `axiom`,
no `native_decide`. The named instantiation is a `def` reduced-to. NEW ADDITIVE file; imports
read-only.
-/
import Dregg2.Crypto.KeyedRomHidingFloor
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace Dregg2.Crypto.Poseidon2RomHidingInstantiation

open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_nonneg winProb_le_one)
open Dregg2.Crypto.KeyedRomHidingFloor
open Dregg2.Crypto.RomCarrierSites (babyBearP babyBearP_pos one_lt_babyBearP)
open Metatheory.Open.BlindedSpanHiding (BlindedSpanCommitment)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1 — the two-world hiding experiment at a FIXED oracle.

The adversary type is the SAME raw `HidingDistinguisher` the ROM floor quantifies over — no
transport map, so nothing to get wrong in one. The ONLY difference from
`KeyedRomHidingFloor.acceptProb` is that the oracle is a fixed `H₀` instead of a sample: the
probability is over the hidden blinding alone, which is exactly the deployed experiment (the
sponge is public and fixed; the fresh blinding felt is the secret). -/

section FixedOracle

variable {Msg B R : Type}
variable [Fintype Msg] [DecidableEq Msg] [Fintype B] [DecidableEq B]
variable [Fintype R] [DecidableEq R] [Nonempty B] [Nonempty R]

/-- **The accept probability in world `b`, at the FIXED oracle `H₀`.** The challenger samples ONLY
the blinding `r : B` uniformly and hands the adversary the challenge `H₀ (msgAt b, r)` — the
deployed blinded-commitment experiment, where the hash is a fixed public function. -/
noncomputable def fixedAcceptProb (H₀ : Msg × B → R) (A : HidingDistinguisher Msg B R)
    (b : Bool) : ℝ :=
  (∑ r : B, if A.accept H₀ r (H₀ (A.msgAt b, r)) then (1 : ℝ) else 0) / (Fintype.card B : ℝ)

/-- **The two-world hiding advantage at the FIXED oracle** — the deployed hiding quantity. -/
noncomputable def fixedHidingAdv (H₀ : Msg × B → R) (A : HidingDistinguisher Msg B R) : ℝ :=
  |fixedAcceptProb H₀ A false - fixedAcceptProb H₀ A true|

theorem fixedAcceptProb_mem_unit (H₀ : Msg × B → R) (A : HidingDistinguisher Msg B R) (b : Bool) :
    0 ≤ fixedAcceptProb H₀ A b ∧ fixedAcceptProb H₀ A b ≤ 1 := by
  have hB : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · apply div_nonneg _ hB.le
    exact Finset.sum_nonneg fun r _ => by split <;> norm_num
  · rw [fixedAcceptProb, div_le_one hB]
    calc (∑ r : B, if A.accept H₀ r (H₀ (A.msgAt b, r)) then (1 : ℝ) else 0)
        ≤ ∑ _r : B, (1 : ℝ) := Finset.sum_le_sum fun r _ => by split <;> norm_num
      _ = (Fintype.card B : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem fixedHidingAdv_mem_unit (H₀ : Msg × B → R) (A : HidingDistinguisher Msg B R) :
    0 ≤ fixedHidingAdv H₀ A ∧ fixedHidingAdv H₀ A ≤ 1 := by
  refine ⟨abs_nonneg _, ?_⟩
  have h0 := fixedAcceptProb_mem_unit H₀ A false
  have h1 := fixedAcceptProb_mem_unit H₀ A true
  rw [fixedHidingAdv, abs_sub_le_iff]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-! ## §2 — ⚑ THE NAMED ROM-INSTANTIATION ASSUMPTION, and the reduction through it. -/

/-- **⚑⚑ `RomFaithfulHiding H₀ A` — THE named ROM-instantiation assumption, per adversary.** The
fixed hash `H₀` serves the adversary `A` no better than a freshly sampled oracle would:
`A`'s two-world advantage at the fixed `H₀` is at most its advantage in the keyed-ROM hiding
experiment (`KeyedRomHidingFloor.hidingAdv`, oracle sampled AFTER `A` is fixed).

This is the random-oracle heuristic stated as the inequality it actually is — a HYPOTHESIS
(`def`, never an `axiom`), the one thing the deployed hiding statement rests on. It is stated
PER-ADVERSARY deliberately: `romFaithful_universal_refuted`/`poseidon2RomInstantiation_not_universal`
prove the `∀ A` form FALSE at a structured fixed hash — a fixed function is public, so a 0-query
adversary can bake its table in at design time. The honest reading is a class restriction
("adversaries that use the sponge generically"), exactly parallel to how `KeyedRomEff` is a class
restriction on the collision side. -/
def RomFaithfulHiding (H₀ : Msg × B → R) (A : HidingDistinguisher Msg B R) : Prop :=
  fixedHidingAdv H₀ A ≤ hidingAdv A

/-- **⚑ THE GENERIC REDUCTION.** ROM-faithful + `Q`-query ⟹ the fixed-oracle two-world advantage
is at most `2·Q/|B|`. ONE `le_trans` deep BY DESIGN: everything under it is the PROVED
information-theoretic ROM floor (`hidingAdv_le`), and the named assumption is exactly and only the
remaining step — visible, not smuggled. -/
theorem fixedHidingAdv_le_of_romFaithful (H₀ : Msg × B → R) (A : HidingDistinguisher Msg B R)
    (Q : ℕ) (hA : QueryHiding Q A) (hfaith : RomFaithfulHiding H₀ A) :
    fixedHidingAdv H₀ A ≤ 2 * (Q : ℝ) / (Fintype.card B : ℝ) :=
  le_trans hfaith (hidingAdv_le A Q hA)

/-! ### The satisfiable pole: the assumption is not empty. -/

/-- The constant-accept distinguisher — advantage `0` in BOTH experiments, hence ROM-faithful at
EVERY fixed oracle. (Satisfiability witness; teeth are in §4.) -/
def constAdv (m0 m1 : Msg) : HidingDistinguisher Msg B R where
  msg0 := m0
  msg1 := m1
  accept := fun _ _ _ => true

theorem constAdv_queryHiding (m0 m1 : Msg) (Q : ℕ) :
    QueryHiding Q (constAdv (B := B) (R := R) m0 m1) :=
  ⟨fun _c => .pure true, fun _c => QueryBounded.pure Q _, fun _ _ _ => rfl⟩

theorem constAdv_fixedHidingAdv (H₀ : Msg × B → R) (m0 m1 : Msg) :
    fixedHidingAdv H₀ (constAdv m0 m1) = 0 := by
  have hB : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have h : ∀ b, fixedAcceptProb H₀ (constAdv (B := B) (R := R) m0 m1) b = 1 := by
    intro b
    rw [fixedAcceptProb]
    have hterm : ∀ r : B,
        (if (constAdv (B := B) (R := R) m0 m1).accept H₀ r
            (H₀ ((constAdv (B := B) (R := R) m0 m1).msgAt b, r)) then (1 : ℝ) else 0) = 1 := by
      intro r
      show (if True then (1 : ℝ) else 0) = 1
      simp
    rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, div_self (ne_of_gt hB)]
  rw [fixedHidingAdv, h false, h true, sub_self, abs_zero]

theorem constAdv_hidingAdv (m0 m1 : Msg) :
    hidingAdv (constAdv (B := B) (R := R) m0 m1) = 0 := by
  have hB : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have h : ∀ b, acceptProb (constAdv (B := B) (R := R) m0 m1) b = 1 := by
    intro b
    rw [acceptProb]
    have hterm : ∀ r : B, winProb (fun H : (Msg × B) → R =>
        (constAdv (B := B) (R := R) m0 m1).accept H r
          (H ((constAdv (B := B) (R := R) m0 m1).msgAt b, r))) = 1 := by
      intro r
      have hpred : (fun H : (Msg × B) → R =>
          (constAdv (B := B) (R := R) m0 m1).accept H r
            (H ((constAdv (B := B) (R := R) m0 m1).msgAt b, r))) = fun _ => true := rfl
      rw [hpred]
      exact winProb_top
    rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, div_self (ne_of_gt hB)]
  rw [hidingAdv, h false, h true, sub_self, abs_zero]

/-- **(SATISFIABILITY.)** The named assumption holds — at every fixed oracle — for the constant
distinguisher: both advantages are `0`. So `RomFaithfulHiding` is not the empty class. -/
theorem constAdv_romFaithful (H₀ : Msg × B → R) (m0 m1 : Msg) :
    RomFaithfulHiding H₀ (constAdv m0 m1) := by
  show fixedHidingAdv H₀ (constAdv m0 m1) ≤ hidingAdv (constAdv m0 m1)
  rw [constAdv_fixedHidingAdv, constAdv_hidingAdv]

set_option linter.unusedVariables false in
/-- **(CANARY — faithfulness of ONE adversary does not discharge the bound for ANOTHER.)** Only
`A`'s own named instantiation connects `A`'s fixed-oracle advantage to the ROM floor; the
hypothesis is PER-ADVERSARY by construction. If this stops failing, the reduction has degenerated
into a floor-at-an-unrelated-adversary discharge. (Stated here at abstract spaces; at the deployed
`Fin babyBearP` spaces the same mismatch is still a type-level failure, but the unifier's
delta-descent through the huge `Fintype` instances overflows before reporting it cleanly.) -/
example (H₀ : Msg × B → R) (A A' : HidingDistinguisher Msg B R) (Q : ℕ)
    (hA : QueryHiding Q A) (hfaith' : RomFaithfulHiding H₀ A') : True := by
  fail_if_success
    (have : fixedHidingAdv H₀ A ≤ 2 * (Q : ℝ) / (Fintype.card B : ℝ) :=
      fixedHidingAdv_le_of_romFaithful H₀ A Q hA hfaith')
  trivial

end FixedOracle

/-! ## §3 — the DEPLOYED instantiation: the exact commitment, the exact cardinalities.

`Felt` is the deployed BabyBear felt (`RomCarrierSites.babyBearP` — the SAME constant the
collision-side kit uses, not a re-mint). Spans and digests are 8 felts (the deployed
`span_digest8` and the wide 8-felt output — the class-D "kept wide" lesson); the blinding is ONE
felt, which is what the concrete bound below makes visible. -/

/-- The deployed BabyBear felt. -/
abbrev Felt : Type := Fin babyBearP

/-- An 8-felt span digest — the deployed `span_digest8`, equal width BY TYPE. -/
abbrev Span : Type := Fin 8 → Felt

/-- The deployed one-felt blinding space. -/
abbrev Blind : Type := Felt

/-- The deployed 8-felt wide digest. -/
abbrev Digest : Type := Fin 8 → Felt

instance : Nonempty Felt := ⟨⟨0, babyBearP_pos⟩⟩
instance : Nonempty Span := ⟨fun _ => ⟨0, babyBearP_pos⟩⟩

/-- A span encoded as the deployed felt list (the `List ℤ` the sponge absorbs). -/
def spanList (m : Span) : List ℤ := List.ofFn fun i => ((m i : ℕ) : ℤ)

@[simp] theorem spanList_length (m : Span) : (spanList m).length = 8 := by
  simp [spanList]

/-- The blinding as the deployed felt. -/
def blindInt (r : Blind) : ℤ := ((r : ℕ) : ℤ)

/-- Decode a deployed digest list into 8 felts (felt-wise `% p`; the identity on in-range deployed
digests — `decodeDigest_spanList` is the round-trip tooth). -/
def decodeDigest (xs : List ℤ) : Digest := fun i =>
  ⟨((xs.getD (i : ℕ) 0) % (babyBearP : ℤ)).toNat, by
    have hp : (0 : ℤ) < (babyBearP : ℤ) := by exact_mod_cast babyBearP_pos
    have h1 := Int.emod_nonneg (xs.getD (i : ℕ) 0) hp.ne'
    have h2 := Int.emod_lt_of_pos (xs.getD (i : ℕ) 0) hp
    omega⟩

/-- The span encoding is injective — the game's message space is FAITHFULLY the deployed 8-felt
span space, not a quotient of it. -/
theorem spanList_injective : Function.Injective spanList := by
  intro m m' h
  funext i
  have hi : (i : ℕ) < (spanList m).length := by rw [spanList_length]; exact i.isLt
  have hi' : (i : ℕ) < (spanList m').length := by rw [spanList_length]; exact i.isLt
  have h1 : (spanList m).getD (i : ℕ) 0 = (spanList m').getD (i : ℕ) 0 := by rw [h]
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at h1
  simp only [spanList, List.getElem_ofFn, Fin.eta] at h1
  exact Fin.ext (by exact_mod_cast h1)

theorem blindInt_injective : Function.Injective blindInt := by
  intro r r' h
  simp only [blindInt] at h
  exact Fin.ext (by exact_mod_cast h)

/-- **The encode/decode round-trip** — decoding any list that starts with an encoded span recovers
the span exactly (deployed digests are in-range felts, so `% p` is the identity limb-wise). -/
@[simp] theorem decodeDigest_spanList (m : Span) (rest : List ℤ) :
    decodeDigest (spanList m ++ rest) = m := by
  funext i
  apply Fin.ext
  show (((spanList m ++ rest).getD (i : ℕ) 0) % (babyBearP : ℤ)).toNat = ((m i : ℕ))
  have hi8 : (i : ℕ) < (spanList m).length := by rw [spanList_length]; exact i.isLt
  have hlen : (i : ℕ) < (spanList m ++ rest).length := by
    rw [List.length_append]; omega
  have hget : (spanList m ++ rest).getD (i : ℕ) 0 = ((m i : ℕ) : ℤ) := by
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_append_left hi8]
    simp only [spanList, List.getElem_ofFn, Fin.eta]
  rw [hget]
  have h0 : (0 : ℤ) ≤ ((m i : ℕ) : ℤ) := by positivity
  have hlt : ((m i : ℕ) : ℤ) < (babyBearP : ℤ) := by exact_mod_cast (m i).isLt
  rw [Int.emod_eq_of_lt h0 hlt]
  simp

/-- **THE DEPLOYED SPONGE, AS THE GAME'S FIXED ORACLE.** At `(m, r)` this is — definitionally
(`deployedSpongeOracle_spec`) — the deployed `BlindedSpanCommitment.commitAt` at the deployed tag:
the wide Poseidon2 over `tagCode ‖ span_digest8 ‖ C_T ‖ BLINDING ‖ 0`, decoded to 8 felts. The
SAME object `BlindedSpanHiding` reasons about; no re-authored mirror. -/
def deployedSpongeOracle (D : BlindedSpanCommitment) : Span × Blind → Digest :=
  fun p => decodeDigest (D.commitAt D.deployedTag (spanList p.1) (blindInt p.2))

/-- **THE WELD, PINNED `rfl`-TIGHT**: the game's oracle IS the deployed wide hash over the deployed
assembled preimage — `wideHash (tagCode(deployedTag) ++ (span ++ [C_T, blinding, 0]))`, decoded. -/
theorem deployedSpongeOracle_spec (D : BlindedSpanCommitment) (m : Span) (r : Blind) :
    deployedSpongeOracle D (m, r)
      = decodeDigest (D.wideHash
          (D.tagCode D.deployedTag ++ (spanList m ++ [D.CT, blindInt r, 0]))) := rfl

theorem card_Blind : Fintype.card Blind = babyBearP := Fintype.card_fin _

/-- **⚑⚑ `Poseidon2RandomOracleInstantiation D A` — THE named assumption, at the deployed object.**
The deployed wide Poseidon2 (as the blinded-span commitment map) serves the adversary `A` no
better than a sampled keyed random oracle. The ONE residual the deployed hiding bound rests on;
per-adversary (the `∀ A` strengthening is REFUTED in §4); never an `axiom`. -/
def Poseidon2RandomOracleInstantiation (D : BlindedSpanCommitment)
    (A : HidingDistinguisher Span Blind Digest) : Prop :=
  RomFaithfulHiding (deployedSpongeOracle D) A

/-- **⚑⚑⚑ THE DELIVERABLE — the DEPLOYED blinded span commitment inherits `hidingAdv_le`.** Under
the ONE named ROM-instantiation assumption, every `Q`-query adversary's two-world
span-distinguishing advantage against the deployed `BlindedSpanCommitment` is at most
`2·Q / 2013265921` — the keyed-ROM hiding floor, AT the deployed cardinalities (one-felt BabyBear
blinding, 8-felt spans and digests), with no asymptotic mirror in the chain.

What is PROVED: the reduction and everything under it (the ROM floor is information-theoretic
counting). What is ASSUMED: exactly `hRom`. Note the number: a ~31-bit hiding budget — ~2^30
challenge-shaped sponge queries enumerate the one-felt blinding and win outright. -/
theorem deployed_blindedSpan_hiding_of_romInstantiation (D : BlindedSpanCommitment)
    (A : HidingDistinguisher Span Blind Digest) (Q : ℕ) (hA : QueryHiding Q A)
    (hRom : Poseidon2RandomOracleInstantiation D A) :
    fixedHidingAdv (deployedSpongeOracle D) A ≤ 2 * (Q : ℝ) / 2013265921 := by
  have h := fixedHidingAdv_le_of_romFaithful (deployedSpongeOracle D) A Q hA hRom
  have hc : ((Fintype.card Blind : ℕ) : ℝ) = 2013265921 := by
    rw [card_Blind]; norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP]
  rwa [hc] at h

/-- The crude power-of-two form: `≤ 2·Q / 2^30` (since `2^30 ≤ babyBearP`). -/
theorem deployed_blindedSpan_hiding_pow2 (D : BlindedSpanCommitment)
    (A : HidingDistinguisher Span Blind Digest) (Q : ℕ) (hA : QueryHiding Q A)
    (hRom : Poseidon2RandomOracleInstantiation D A) :
    fixedHidingAdv (deployedSpongeOracle D) A ≤ 2 * (Q : ℝ) / 2 ^ 30 := by
  refine (deployed_blindedSpan_hiding_of_romInstantiation D A Q hA hRom).trans ?_
  have h1 : (0 : ℝ) ≤ 2 * (Q : ℝ) := by positivity
  have h2 : (2 : ℝ) ^ 30 ≤ 2013265921 := by norm_num
  gcongr

/-- **(THE MIRROR FAMILY NEVER HITS THE DEPLOYED CARDINALITY.)** At NO parameter does
`blindedSpanRomFamily`'s `2^l`-element blinding space equal the deployed one-felt space —
`babyBearP` is odd. The asymptotic-shape half of the old prose gap, pinned; it is why this file
applies the floor at the exact deployed cardinalities instead of through the mirror family. -/
theorem mirrorFamily_card_never_deployed (l : ℕ) : (2 : ℕ) ^ l ≠ Fintype.card Blind := by
  rw [card_Blind]
  intro h
  rcases l with _ | l
  · norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP] at h
  · have h2 : (2 : ℕ) ∣ 2 ^ (l + 1) := dvd_pow_self 2 (Nat.succ_ne_zero l)
    rw [h] at h2
    norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP] at h2

/-! ## §4 — ⚑ BOTH POLES OF THE NAMED ASSUMPTION (so it cannot be read as stronger than it is).

The satisfiable pole is §2's `constAdv_romFaithful`, transported below. The load-bearing pole: the
UNIVERSAL (∀-adversary) form of the instantiation is FALSE at a structured sponge — a fixed hash
is PUBLIC, so its table is available at adversary-design time, and a 0-query `.pure`-leaf
adversary can exploit it with fixed-oracle advantage `1` while its ROM advantage is EXACTLY `0`
(`zeroQuery_hidingAdv_eq_zero`: against a sampled oracle, hardcoding is worthless). This is the
hiding-side twin of `KeyedRomFloor.fixedPairAdv_negl`'s moral, run in the OTHER direction — and
the reason `Poseidon2RandomOracleInstantiation` is per-adversary, never `∀ A`. -/

/-- The all-zeros span. -/
def spanZero : Span := fun _ => ⟨0, babyBearP_pos⟩

/-- The all-ones span. -/
def spanOne : Span := fun _ => ⟨1, one_lt_babyBearP⟩

theorem spanZero_ne_spanOne : spanZero ≠ spanOne := by
  intro h
  have h0 := congrFun h 0
  have hval : (0 : ℕ) = 1 := congrArg Fin.val h0
  exact absurd hval (by norm_num)

/-- **(SATISFIABILITY, at the deployed oracle.)** The named assumption is inhabited at EVERY
deployed commitment — the constant distinguisher is ROM-faithful (both advantages `0`). -/
theorem poseidon2RomInstantiation_satisfiable (D : BlindedSpanCommitment) :
    Poseidon2RandomOracleInstantiation D (constAdv spanZero spanOne) :=
  constAdv_romFaithful (deployedSpongeOracle D) spanZero spanOne

/-- A `BlindedSpanCommitment` whose "sponge" LEAKS its input (`wideHash = id`, empty tag): the
commitment at `(span, r)` decodes back to `span` itself. A legal inhabitant of the deployed
STRUCTURE — which is exactly the point: nothing in the structure forbids a sponge whose fixed
table is trivially exploitable, so no theorem can hold at ALL `(D, A)` pairs. -/
def leakCommitment : BlindedSpanCommitment where
  wideHash := id
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  tagCode := fun _ => []
  deployedTag := ()
  CT := 0
  honestSpan := fun _ => List.replicate 8 0
  honestSpanLen := fun _ => by simp
  honestBlinding := fun _ => 0

/-- The leaky commitment's oracle is the first projection: it hands the committed span back. -/
theorem leakOracle_eq : deployedSpongeOracle leakCommitment = fun p => p.1 := by
  funext p
  show decodeDigest (leakCommitment.commitAt () (spanList p.1) (blindInt p.2)) = p.1
  have hc : leakCommitment.commitAt () (spanList p.1) (blindInt p.2)
      = spanList p.1 ++ [(0 : ℤ), blindInt p.2, 0] := rfl
  rw [hc, decodeDigest_spanList]

/-- The table-baking adversary: ZERO queries, verdict "is the challenge the `spanOne` table row".
Legal because the sponge's table is public at design time. -/
def leakAdv : HidingDistinguisher Span Blind Digest where
  msg0 := spanZero
  msg1 := spanOne
  accept := fun _H _r c => decide (c = spanOne)

/-- The table-baker is a 0-QUERY class member — the exact shape the keyed-ROM class ADMITS (and
defangs, in the ROM). -/
theorem leakAdv_zeroQuery : QueryHiding 0 leakAdv :=
  ⟨fun c => .pure (decide (c = spanOne)), fun _c => QueryBounded.pure 0 _, fun _ _ _ => rfl⟩

theorem leakAdv_fixed_false :
    fixedAcceptProb (deployedSpongeOracle leakCommitment) leakAdv false = 0 := by
  rw [fixedAcceptProb, leakOracle_eq]
  have hterm : ∀ r : Blind,
      (if leakAdv.accept (fun p : Span × Blind => p.1) r
          ((fun p : Span × Blind => p.1) (leakAdv.msgAt false, r)) then (1 : ℝ) else 0) = 0 := by
    intro r
    have hacc : leakAdv.accept (fun p : Span × Blind => p.1) r
        ((fun p : Span × Blind => p.1) (leakAdv.msgAt false, r)) = false := by
      show decide (spanZero = spanOne) = false
      exact decide_eq_false spanZero_ne_spanOne
    rw [hacc]
    simp
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  simp

theorem leakAdv_fixed_true :
    fixedAcceptProb (deployedSpongeOracle leakCommitment) leakAdv true = 1 := by
  have hB : (0 : ℝ) < (Fintype.card Blind : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [fixedAcceptProb, leakOracle_eq]
  have hterm : ∀ r : Blind,
      (if leakAdv.accept (fun p : Span × Blind => p.1) r
          ((fun p : Span × Blind => p.1) (leakAdv.msgAt true, r)) then (1 : ℝ) else 0) = 1 := by
    intro r
    have hacc : leakAdv.accept (fun p : Span × Blind => p.1) r
        ((fun p : Span × Blind => p.1) (leakAdv.msgAt true, r)) = true := by
      show decide (spanOne = spanOne) = true
      simp
    rw [hacc]
    simp
  rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, div_self (ne_of_gt hB)]

/-- The table-baker's FIXED-oracle advantage is EXACTLY `1` — it reads the span straight out of
the leaky commitment, with zero queries. -/
theorem leakAdv_fixedHidingAdv :
    fixedHidingAdv (deployedSpongeOracle leakCommitment) leakAdv = 1 := by
  rw [fixedHidingAdv, leakAdv_fixed_false, leakAdv_fixed_true]
  norm_num

/-- **⚑ (THE LOAD-BEARING POLE.) THE UNIVERSAL INSTANTIATION IS REFUTED.** There is a (structured)
deployed-shape commitment and a 0-query adversary at which `Poseidon2RandomOracleInstantiation`
FAILS: fixed-oracle advantage `1`, ROM advantage `0`. A fixed public hash cannot be a random
oracle against ALL adversaries — the finitary CGH shadow, in-tree. Hence the named assumption is
PER-ADVERSARY; any `∀ A` upgrade of it at the real sponge is asserting a refuted shape. -/
theorem poseidon2RomInstantiation_not_universal :
    ∃ (D : BlindedSpanCommitment) (A : HidingDistinguisher Span Blind Digest),
      QueryHiding 0 A ∧ ¬ Poseidon2RandomOracleInstantiation D A := by
  refine ⟨leakCommitment, leakAdv, leakAdv_zeroQuery, fun h => ?_⟩
  have h' : fixedHidingAdv (deployedSpongeOracle leakCommitment) leakAdv ≤ hidingAdv leakAdv := h
  rw [leakAdv_fixedHidingAdv, zeroQuery_hidingAdv_eq_zero leakAdv leakAdv_zeroQuery] at h'
  norm_num at h'

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  fixedAcceptProb_mem_unit,
  fixedHidingAdv_mem_unit,
  fixedHidingAdv_le_of_romFaithful,
  constAdv_queryHiding,
  constAdv_fixedHidingAdv,
  constAdv_hidingAdv,
  constAdv_romFaithful,
  spanList_injective,
  blindInt_injective,
  decodeDigest_spanList,
  deployedSpongeOracle_spec,
  card_Blind,
  deployed_blindedSpan_hiding_of_romInstantiation,
  deployed_blindedSpan_hiding_pow2,
  mirrorFamily_card_never_deployed,
  poseidon2RomInstantiation_satisfiable,
  leakOracle_eq,
  leakAdv_zeroQuery,
  leakAdv_fixedHidingAdv,
  poseidon2RomInstantiation_not_universal
]

end Dregg2.Crypto.Poseidon2RomHidingInstantiation
