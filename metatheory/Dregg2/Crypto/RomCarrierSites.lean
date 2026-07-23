/-
# `Dregg2.Crypto.RomCarrierSites` — the per-site instantiation kit for the keyed-ROM binding.

## What this is

`Crypto.RomBindingReduction` proved the carrier PATTERN once: an oracle-program forger
(`RomCarrierComp`, `Q`-query-bounded), an extractor that is a post-map (`OracleComp.mapOut`, budget
preserved), and the binding closed from the PROVED keyed floor (`KeyedRomFloor.keyedRom_hard`, the
birthday bound) with NO false `IsPolyTime` hypothesis. What each deployed `_binds_from_polyTime` site
still needs to consume it is MECHANICAL but repetitive:

  1. a `KeyedRomFamily` whose digest space is the `λ`-growing `Fin (2 ^ l)` — so the floor's
     `hw : card (R l) = 2 ^ l` obligation is discharged ONCE (`flatFamily_card_R`), never restated;
  2. a `RomCarrier` built from the site's structural encoding, with the domain-separation tag carried
     in the CONTEXT (`taggedCarrier`) — so per-site content is exactly the encoder and its
     payload-injectivity, the same two facts `SpongeCarrier.ofFlatEncoding` took;
  3. for CHAINED sites (commitment absorbs digest absorbs sub-block), sequential composition of oracle
     programs (`OracleComp.bindComp`) with ADDITIVE query accounting, and the union bound over two
     carriers of ONE family (`chained_rom_binds`) — the ROM successor of
     `EncodedBindingReduction.chained_binding_advantage_bound`, with the floor PROVED instead of
     parametric.

This module supplies those pieces once. It creates NO new collision-resistance claim: every binding
below is `romCarrier_binds` (hence `keyedRom_hard`, hence the birthday bound) applied.

## ⚑ The modelling caveat every consumer inherits (say it, do not smuggle it)

A site landing here has taken the standard RANDOM-ORACLE IDEALISATION of the deployed domain-separated
Poseidon2 sponge at an ASYMPTOTIC digest width: the sampled `H : Key × Msg → Fin (2 ^ l)` replaces the
fixed public `sponge (tagCode t ++ ·)`, and there is NO `l` at which `Fin (2 ^ l)` IS the deployed
31-bit BabyBear felt. That is a MODELLING step — a deliberate, labelled idealisation, exactly as
`DomainSeparatedCREffRegrounded` §5 demands — NOT a derivation. What it buys over the deleted
`IsPolyTime` discharge: the floor under the reduction is a THEOREM about the model instead of a
hypothesis that is FALSE at the deployed object. What it does not buy: any statement about the fixed
deployed sponge itself — collision resistance of a fixed public function is a conjecture, not a Lean
theorem (`RomBindingReduction` header, proved reasoning).

## Non-fake

Both generic poles are priced at the floor (`KeyedRomFloor` §3–§5). Here: the query class at any
carrier is INHABITED by the `0`-query constant answerer (`constTriple_in_eff`) whose advantage is
POSITIVE at every parameter (`constTriple_gameAdv_pos`) yet NEGLIGIBLE (`constTriple_binds`) — the
admitted-but-defanged pole, the exact transplant of the `shortCollAdv` shape that refutes the
`IsPolyTime` floor.

No `sorry`, no `axiom`, no `native_decide`. `#assert_all_clean` ⊆ {propext, Classical.choice,
Quot.sound}.
-/
import Dregg2.Crypto.RomBindingReduction
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomCarrierSites

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded negl_add)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (RomFamily romCollisionGame)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff)
open Dregg2.Crypto.RomBindingReduction

set_option autoImplicit false

/-! ## §0 — shared facts: the deployed felt bound, a winnable game has positive advantage, and a
`+2` query budget stays polynomial. -/

/-- The BabyBear prime — the range of every deployed felt limb; the truncated message shapes the
per-site families absorb are tuples over `Fin babyBearP`. -/
def babyBearP : ℕ := 2013265921

theorem babyBearP_pos : 0 < babyBearP := by norm_num [babyBearP]

theorem one_lt_babyBearP : 1 < babyBearP := by norm_num [babyBearP]

/-- **A WITNESSED WIN MAKES `winProb` POSITIVE.** One instance on which the predicate fires puts at
least one point in the filter, so the uniform count is `> 0`. This is what turns "the constant
answerer sometimes wins" into the non-vacuity tooth `constTriple_gameAdv_pos`. -/
theorem winProb_pos_of_witness {Ω : Type} [Fintype Ω] (win : Ω → Bool) (o : Ω)
    (ho : win o = true) : 0 < winProb win := by
  have hnum : 0 < ((Finset.univ.filter (fun x : Ω => win x = true)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ o, ho⟩⟩
  have hden : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨o⟩
  unfold Dregg2.Crypto.ProbCrypto.winProb
  exact div_pos hnum hden

/-- **A `Q + 2` BUDGET IS STILL POLYNOMIAL** — the accounting fact a two-hop chained reduction needs:
the layer that re-queries the two inner digests spends two extra queries, and
`(Q + 2)² + 1 ≤ 7 · (Q² + 1)`, so the floor's polynomial-budget obligation transfers. -/
theorem polyBounded_sq_add_two (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    PolyBounded (fun l => (((Q l + 2 : ℕ) : ℝ) * ((Q l + 2 : ℕ) : ℝ) + 1)) := by
  obtain ⟨d, C, h⟩ := hQ
  refine ⟨d, 7 * C, ?_⟩
  filter_upwards [h] with n hn
  have hq : (0 : ℝ) ≤ (Q n : ℝ) := Nat.cast_nonneg _
  have h1 : |((Q n : ℝ) * (Q n : ℝ) + 1)| = (Q n : ℝ) * (Q n : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  have h2 : |(((Q n + 2 : ℕ) : ℝ) * ((Q n + 2 : ℕ) : ℝ) + 1)|
      = ((Q n : ℝ) + 2) * ((Q n : ℝ) + 2) + 1 := by
    push_cast
    exact abs_of_nonneg (by positivity)
  rw [h2]
  rw [h1] at hn
  nlinarith [hn, hq, sq_nonneg ((Q n : ℝ) - 1)]

/-! ## §1 — SEQUENTIAL COMPOSITION of oracle programs, with additive query accounting.

`RomBindingReduction.OracleComp.mapOut` post-maps a program's ANSWER without touching its queries.
A chained extractor must do more: run the forger's program, then make FURTHER queries that depend on
its answer (re-query the two inner digests). That is monadic `bind`, and its budget is the SUM. -/

/-- **RUN `M`, THEN CONTINUE WITH `k` ON ITS ANSWER** — graft `k a` onto every `pure a` leaf. -/
def OracleComp.bindComp {D R A B : Type} :
    OracleComp D R A → (A → OracleComp D R B) → OracleComp D R B
  | .pure a, k => k a
  | .query d f, k => .query d (fun r => OracleComp.bindComp (f r) k)

/-- Sequencing evaluates as expected: run `M`, feed its answer to `k`, run that. -/
theorem OracleComp.bindComp_eval {D R A B : Type} (M : OracleComp D R A)
    (k : A → OracleComp D R B) (H : D → R) :
    (OracleComp.bindComp M k).eval H = (k (M.eval H)).eval H := by
  induction M with
  | pure a => rfl
  | query d f ih =>
      show (OracleComp.bindComp (f (H d)) k).eval H = _
      exact ih (H d)

/-- **QUERY BUDGETS ADD UNDER SEQUENCING** — a `Q`-query program continued by an `n`-query program is
`Q + n`-query. This is why a chained extractor stays in the query-counted class with an explicit,
polynomial overhead, instead of pricing answer size. -/
theorem OracleComp.bindComp_queryBounded {D R A B : Type} {Q n : ℕ}
    {M : OracleComp D R A} {k : A → OracleComp D R B}
    (hM : QueryBounded Q M) (hk : ∀ a, QueryBounded n (k a)) :
    QueryBounded (Q + n) (OracleComp.bindComp M k) := by
  induction hM with
  | pure m a => exact (hk a).mono (Nat.le_add_left n m)
  | query m d f _ ih =>
      exact (QueryBounded.query (m + n) d _ (fun r => ih r)).mono (by omega)

/-! ## §2 — the FLAT FAMILY: any finite deployed message shape, under the `λ`-bit ideal digest. -/

/-- **A KEYED ROM FAMILY FROM A DEPLOYED MESSAGE SHAPE.** The key is the site's own domain-separation
tag space; the message domain is the site's (finite, possibly `λ`-indexed) absorbed shape; the digest
space is the ideal `Fin (2 ^ l)`. ⚑ The digest space is the MODELLING step (header): `λ`-growing where
the deployed felt is fixed ~31-bit. It is what lets `keyedRom_hard`'s `hw` close by computation. -/
def flatFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (Msg : ℕ → Type) (mF : ∀ l, Fintype (Msg l)) (mD : ∀ l, DecidableEq (Msg l))
    (mN : ∀ l, Nonempty (Msg l)) : KeyedRomFamily where
  Key := fun _ => Key
  D := Msg
  R := fun l => Fin (2 ^ l)
  keyFin := fun _ => kF
  keyDec := fun _ => kD
  keyNe := fun _ => kN
  dFin := mF
  dDec := mD
  dNe := mN
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun _ => ⟨⟨0, by positivity⟩⟩

/-- **THE `hw` OBLIGATION, DISCHARGED ONCE.** Every flat family has a `2 ^ l`-element digest space by
construction, so no site restates the floor's width obligation — the single biggest per-site trap
(`card BabyBear ≠ 2 ^ l` for any `l`) is closed at the constructor. -/
theorem flatFamily_card_R (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (Msg : ℕ → Type) (mF : ∀ l, Fintype (Msg l)) (mD : ∀ l, DecidableEq (Msg l))
    (mN : ∀ l, Nonempty (Msg l)) (l : ℕ) :
    letI := (flatFamily Key kF kD kN Msg mF mD mN).rFin l
    Fintype.card ((flatFamily Key kF kD kN Msg mF mD mN).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-! ## §3 — the TAGGED CARRIER: the site's structural encoding, tag in the context. -/

/-- **A CARRIER FROM A STRUCTURAL EMBEDDING, TAG-IN-CONTEXT.** The context is a domain-separation tag
together with the site's own fixed opening data; the commitment is one oracle query at
`(tag, emb ctx val)`. The ONLY per-site obligations are the embedding into the message shape and its
injectivity in the payload — the same two facts `SpongeCarrier.ofFlatEncoding` took, with the width
obligation absorbed into the finiteness of `Msg`. -/
def taggedCarrier (F : KeyedRomFamily) (Ctx' Val : ℕ → Type)
    (valDec : ∀ l, DecidableEq (Val l))
    (emb : ∀ l, Ctx' l → Val l → F.D l)
    (emb_inj : ∀ l (c : Ctx' l) (a b : Val l), emb l c a = emb l c b → a = b) :
    RomCarrier F where
  Ctx := fun l => F.Key l × Ctx' l
  Val := Val
  valDec := valDec
  encode := fun l c v => (c.1, emb l c.2 v)
  encode_inj := fun l c a b h => emb_inj l c.2 a b (congrArg Prod.snd h)

/-- **⚑ THE FLAT-SITE BINDING — NO width obligation, NO floor hypothesis.** Any carrier over a flat
family binds against every query-bounded forger: `romCarrier_binds` with `hw` closed by
`flatFamily_card_R`. The hypotheses that remain — a polynomial query budget and the forger's
membership in the query class — are the honest ones; nothing refutable is carried. -/
theorem flatSite_binds (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (Msg : ℕ → Type) (mF : ∀ l, Fintype (Msg l)) (mD : ∀ l, DecidableEq (Msg l))
    (mN : ∀ l, Nonempty (Msg l))
    (C : RomCarrier (flatFamily Key kF kD kN Msg mF mD mN))
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (flatFamily Key kF kD kN Msg mF mD mN) C))
    (hA : RomCarrierEff (flatFamily Key kF kD kN Msg mF mD mN) C Q A) :
    Negl (gameAdv (romCarrierGame (flatFamily Key kF kD kN Msg mF mD mN) C) A) :=
  romCarrier_binds _ C Q hQ (flatFamily_card_R Key kF kD kN Msg mF mD mN) A hA

/-! ## §4 — non-vacuity teeth, generic: the class is inhabited by an answerer with POSITIVE
advantage, and that answerer is DEFANGED (its advantage is negligible), not excluded. -/

/-- **THE CONSTANT ANSWERER** — the `0`-query program returning a fixed context and two fixed
payloads: the random-oracle transplant of the `shortCollAdv` shape that refutes the `IsPolyTime`
floor. The class ADMITS it; §4 shows why that is fine. -/
def constTripleComp (F : KeyedRomFamily) (C : RomCarrier F)
    (c : ∀ l, C.Ctx l) (v w : ∀ l, C.Val l) : RomCarrierComp F C :=
  fun l => OracleComp.pure (c l, v l, w l)

/-- The constant answerer is `0`-query, hence in the class at EVERY budget. -/
theorem constTriple_in_eff (F : KeyedRomFamily) (C : RomCarrier F)
    (c : ∀ l, C.Ctx l) (v w : ∀ l, C.Val l) (Q : ℕ → ℕ) :
    RomCarrierEff F C Q (romCarrierAdv F C (constTripleComp F C c v w)) :=
  ⟨constTripleComp F C c v w, fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩

/-- **THE GAME IS WINNABLE — the advantage is POSITIVE at every parameter.** The constant oracle maps
both encodings to one digest, so on distinct payloads the constant answerer wins somewhere; hence the
binding theorems bound something that is genuinely nonzero, not the advantage of an unwinnable game. -/
theorem constTriple_gameAdv_pos (F : KeyedRomFamily) (C : RomCarrier F)
    (c : ∀ l, C.Ctx l) (v w : ∀ l, C.Val l) (l : ℕ) (hne : v l ≠ w l) :
    0 < gameAdv (romCarrierGame F C) (romCarrierAdv F C (constTripleComp F C c v w)) l := by
  obtain ⟨r₀⟩ := F.rNe l
  refine @winProb_pos_of_witness _ ((romCarrierGame F C).instFin l) _ (fun _ => r₀) ?_
  exact ((romCarrierAdv F C (constTripleComp F C c v w)).hit_eq_true l _).mpr ⟨hne, rfl⟩

/-- **⚑ THE ADMITTED SHAPE IS DEFANGED, NOT EXCLUDED.** The binding applies to the constant answerer
itself: admitted by the class, positive advantage, NEGLIGIBLE advantage. Against the fixed sponge this
shape wins with probability `1` and refutes the `IsPolyTime` floor; against the sampled oracle its
advantage collapses. This is the counterexample dying at the carrier layer, per carrier. -/
theorem constTriple_binds (F : KeyedRomFamily) (C : RomCarrier F)
    (c : ∀ l, C.Ctx l) (v w : ∀ l, C.Val l) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l) :
    Negl (gameAdv (romCarrierGame F C) (romCarrierAdv F C (constTripleComp F C c v w))) :=
  romCarrier_binds F C Q hQ hw _ (constTriple_in_eff F C c v w Q)

/-! ## §5 — CHAINED bindings over ONE sampled oracle: the union bound, ROM edition.

The ROM successor of `EncodedBindingReduction` §6. Both layers of a chain (commitment ⟸ digest)
live over ONE family — one oracle domain with the two message shapes domain-separated inside it — so
both carrier games share the sampled-instance space and the union bound is a `winProb` fact. -/

/-- **A COMPOSED FORGERY over `F`'s own sampled oracle** — the chained break, before it is a `Game`.
Its win relation may apply the ORACLE ITSELF (e.g. re-absorb an inner digest), which is exactly what a
single carrier cannot express. -/
structure RomForgery (F : KeyedRomFamily) where
  /-- What the composed forger outputs. -/
  Ans : ℕ → Type
  /-- **THE PROBLEM** — the composed equivocation, checked against the sampled oracle. -/
  wins : ∀ l, (F.toRomFamily.D l → F.toRomFamily.R l) → Ans l → Prop
  /-- The win event is counted, so it is decidable. -/
  winsDec : ∀ l (H : F.toRomFamily.D l → F.toRomFamily.R l) (a : Ans l), Decidable (wins l H a)

/-- The composed forgery, as a first-class `Game` over the family's sampled oracle space. -/
def RomForgery.game {F : KeyedRomFamily} (P : RomForgery F) : Game where
  Inst := fun l => F.toRomFamily.D l → F.toRomFamily.R l
  Ans := P.Ans
  instFin := fun l => (romCollisionGame F.toRomFamily).instFin l
  instNe := fun l => (romCollisionGame F.toRomFamily).instNe l
  wins := P.wins
  winsDec := P.winsDec

/-- **THE QUERY-BOUNDED COMPOSED-FORGER CLASS** — same shape as `RomCarrierEff`, at the composed
answer type: the forger factors through a `Q`-query tree fixed before the oracle is sampled. -/
def RomForgeryEff (F : KeyedRomFamily) (P : RomForgery F) (Q : ℕ → ℕ)
    (A : Adversary P.game) : Prop :=
  ∃ M : ∀ l, OracleComp (F.toRomFamily.D l) (F.toRomFamily.R l) (P.Ans l),
    (∀ l, QueryBounded (Q l) (M l)) ∧
      ∀ l (H : P.game.Inst l), A.run l H = (M l).eval H

/-- **⚑ THE UNION BOUND, over the SHARED sampled oracle.** If every oracle the composed forger wins is
won by at least one of the two extracted layer forgers, its advantage is at most their sum. -/
theorem chained_rom_adv_le {F : KeyedRomFamily} (P : RomForgery F)
    (C₁ C₂ : RomCarrier F) (A : Adversary P.game)
    (B₁ : Adversary (romCarrierGame F C₁)) (B₂ : Adversary (romCarrierGame F C₂))
    (himp : ∀ l (H : P.game.Inst l), P.wins l H (A.run l H) →
      (romCarrierGame F C₁).wins l H (B₁.run l H)
        ∨ (romCarrierGame F C₂).wins l H (B₂.run l H))
    (l : ℕ) :
    gameAdv P.game A l
      ≤ gameAdv (romCarrierGame F C₁) B₁ l + gameAdv (romCarrierGame F C₂) B₂ l := by
  refine @Dregg2.Crypto.HermineHashCRRegrounded.winProb_le_add_of_imp _
    ((romCollisionGame F.toRomFamily).instFin l) _ _ _ (fun H hH => ?_)
  rw [Dregg2.Crypto.FloorGames.Adversary.hit_eq_true] at hH
  rcases himp l H hH with h | h
  · exact Or.inl ((B₁.hit_eq_true l H).mpr h)
  · exact Or.inr ((B₂.hit_eq_true l H).mpr h)

/-- **⚑⚑ THE CHAINED BINDING, FROM THE PROVED FLOOR.** A composed forger dominated by two extracted
query-bounded layer forgers has NEGLIGIBLE advantage: each layer is killed by `romCarrier_binds` (the
birthday floor — a THEOREM), and `Negl` is closed under addition. The ROM successor of
`chained_binding_advantage_bound`, with no `Eff` parameter left in the open and no false hypothesis. -/
theorem chained_rom_binds {F : KeyedRomFamily} (P : RomForgery F)
    (C₁ C₂ : RomCarrier F) (Q₁ Q₂ : ℕ → ℕ)
    (hQ₁ : PolyBounded (fun l => ((Q₁ l : ℝ) * (Q₁ l : ℝ) + 1)))
    (hQ₂ : PolyBounded (fun l => ((Q₂ l : ℝ) * (Q₂ l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary P.game)
    (B₁ : Adversary (romCarrierGame F C₁)) (B₂ : Adversary (romCarrierGame F C₂))
    (himp : ∀ l (H : P.game.Inst l), P.wins l H (A.run l H) →
      (romCarrierGame F C₁).wins l H (B₁.run l H)
        ∨ (romCarrierGame F C₂).wins l H (B₂.run l H))
    (hB₁ : RomCarrierEff F C₁ Q₁ B₁) (hB₂ : RomCarrierEff F C₂ Q₂ B₂) :
    Negl (gameAdv P.game A) :=
  negl_of_le (fun l => (gameAdv_mem_unit P.game A l).1)
    (chained_rom_adv_le P C₁ C₂ A B₁ B₂ himp)
    (negl_add (romCarrier_binds F C₁ Q₁ hQ₁ hw B₁ hB₁)
      (romCarrier_binds F C₂ Q₂ hQ₂ hw B₂ hB₂))

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  winProb_pos_of_witness,
  polyBounded_sq_add_two,
  OracleComp.bindComp_eval,
  OracleComp.bindComp_queryBounded,
  flatFamily_card_R,
  flatSite_binds,
  constTriple_in_eff,
  constTriple_gameAdv_pos,
  constTriple_binds,
  chained_rom_adv_le,
  chained_rom_binds
]

end Dregg2.Crypto.RomCarrierSites
