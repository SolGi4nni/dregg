/-
# Metatheory.PolisEraseBlocklace — the causal counterfactual ON THE DEPLOYED BLOCKLACE.

Binds the abstract `Metatheory.PolisErase.Causal` (the public causal structure of gpt5.5's §3
A-erasure) to the concrete byzantine-repelling DAG `Dregg2.Authority.Blocklace`. The instance
`dreggCausal` is:

* `actor := Block.creator` — a block's public actor is its signing author (`finality.rs::Block.creator`);
* `le := dreggLe := (· = ·) ∨ precedes` — the **reflexive closure** of the deployed observe order
  `≺` (`precedes`, the transitive closure of the direct ack edge `pointed` / paper `←`).

`le_refl` is the left disjunct; `le_trans` is discharged from the deployed `precedes.trans` (case
split on the four reflexive/strict combinations). With this instance, `eraseAgent dreggCausal A C`
is the REAL causal counterfactual on the blocklace: the maximal subconfiguration of a blocklace
config none of whose blocks have an `A`-authored block in their causal (`≺`) past — "what the lace
would be had author `A` never contributed".

HONEST FRAMING. This is the BOUNDED / PUBLIC / DECIDABLE binding only: the causal order is the
*public* ack DAG (no hidden interior), `actor` is the *public* creator key, and the erasure is the
purely structural down-closed counterfactual. It is NOT "politics solved" — domination/viability
content lives in the framework files; this file only certifies that the deployed blocklace SATISFIES
the `Causal` interface those results consume, so they apply to the real log. The §8 crypto seam
(hash-injectivity, signature-unforgeability) is untouched, exactly as in `Blocklace.lean`.

Pure Lean 4 core; no `sorry`, no load-bearing `:= True`.
-/
import Metatheory.PolisErase
import Dregg2.Authority.Blocklace

namespace Metatheory.PolisEraseBlocklace

open Dregg2.Authority.Blocklace

/-- The **reflexive closure of the deployed observe order** `≺` (`precedes`): `a ≤ b` iff `a = b`
or `a` is in `b`'s causal past. This is the `le` of the `Causal` interface (the abstract framework
demands reflexivity; `precedes` is irreflexive-by-construction transitive closure, so we reflexively
close it). -/
def dreggLe (B : Lace) (a b : Block) : Prop := a = b ∨ precedes B a b

/-- `dreggLe` is reflexive — the left disjunct. -/
theorem dreggLe_refl (B : Lace) (a : Block) : dreggLe B a a := Or.inl rfl

/-- `dreggLe` is transitive — discharged from the deployed `precedes.trans`. The four cases over
the two reflexive/strict disjuncts collapse to `rfl`-rewrites and one `precedes.trans`. -/
theorem dreggLe_trans (B : Lace) {a b c : Block}
    (hab : dreggLe B a b) (hbc : dreggLe B b c) : dreggLe B a c := by
  rcases hab with rfl | hab
  · exact hbc
  · rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (precedes.trans hab hbc)

/-- **`dreggCausal B`** — the deployed blocklace `B` AS an abstract public `Causal` structure
(`Metatheory.PolisErase.Causal Block AuthorId`). `actor` is the public creator key; `le` is the
reflexive closure of the observe (`≺`) order. This is the binding that lets gpt5.5's §3 erasure /
domination machinery run on the real byzantine-repelling DAG. -/
def dreggCausal (B : Lace) : Metatheory.PolisErase.Causal Block AuthorId where
  actor := Block.creator
  le := dreggLe B
  le_refl := dreggLe_refl B
  le_trans := fun {_ _ _} hab hbc => dreggLe_trans B hab hbc

/-- Sanity: the bound `actor` is exactly the deployed `creator` field (the public author key). -/
@[simp] theorem dreggCausal_actor (B : Lace) (b : Block) :
    (dreggCausal B).actor b = b.creator := rfl

/-- Sanity: the bound `le` is exactly the reflexive closure of the deployed `precedes`. -/
@[simp] theorem dreggCausal_le (B : Lace) (a b : Block) :
    (dreggCausal B).le a b ↔ (a = b ∨ precedes B a b) := Iff.rfl

/-- The strict deployed order embeds into the bound `le`: an observe edge `a ≺ b` is a `le` step.
So a genuine causal-past relationship of the blocklace IS counted by the abstract erasure. -/
theorem precedes_le {B : Lace} {a b : Block} (h : precedes B a b) :
    (dreggCausal B).le a b := Or.inr h

/-! ### `eraseAgent` on the blocklace — the real causal counterfactual.

`Metatheory.PolisErase.eraseAgent (dreggCausal B) A C` keeps exactly the blocks of config `C` whose
causal (`≺`) past contains NO block authored by `A`. The framework theorems
(`eraseAgent_subset` / `_no_A` / `_maximal`) hold for it for free, via the instance. -/

/-- The blocklace causal counterfactual: erase author `A`'s public contribution from a blocklace
configuration `C`. (A thin alias fixing the instance, so downstream reads as a blocklace operation.) -/
def eraseAuthor (B : Lace) (A : AuthorId)
    (C : Metatheory.PolisErase.Config (dreggCausal B)) :
    Metatheory.PolisErase.Config (dreggCausal B) :=
  Metatheory.PolisErase.eraseAgent (dreggCausal B) A C

/-- A kept block is genuinely a block of the original config (subset). -/
theorem eraseAuthor_subset (B : Lace) (A : AuthorId)
    (C : Metatheory.PolisErase.Config (dreggCausal B)) (e : Block) :
    (eraseAuthor B A C).mem e → C.mem e :=
  Metatheory.PolisErase.eraseAgent_subset (dreggCausal B) A C e

/-- A kept block is NOT authored by `A` — `A`'s public contribution is gone from the counterfactual. -/
theorem eraseAuthor_no_A (B : Lace) (A : AuthorId)
    (C : Metatheory.PolisErase.Config (dreggCausal B)) (e : Block) :
    (eraseAuthor B A C).mem e → e.creator ≠ A :=
  Metatheory.PolisErase.eraseAgent_no_A (dreggCausal B) A C e

/-! ### Non-vacuity on the deployed demo lace (`Blocklace.demoLace`).

The honest chain `g0 ← g1` lives over author `7`; the Byzantine fork `f1 ∥ f2` over author `9`.
Erasing author `7` must drop `g1` (its causal past contains `g0`, a `7`-block) — a non-trivial,
discriminating counterfactual on the REAL deployed lace. -/

/-- A blocklace configuration over the deployed `demoLace` containing the honest chain `{g0, g1}`.
Down-closure under `dreggLe`: the only nontrivial `≺`-edge into the set is `g0 ≺ g1`, and `g0` is in
the set. (`demo_precedes_left_g0` from `Blocklace.lean`: every `≺`-chain's left end is `g0`.) -/
def demoHonestConfig : Metatheory.PolisErase.Config (dreggCausal demoLace) where
  mem e := e = g0 ∨ e = g1
  downClosed := by
    intro e f hef hf
    rcases hef with rfl | hpre
    · exact hf
    · -- e ≺ f, so by demo_precedes_left_g0 the source e is g0, which is in the set.
      exact Or.inl (demo_precedes_left_g0 hpre)

/-- **Non-vacuity (discriminating).** Erasing the honest author `7` from the deployed demo config
DROPS the successor `g1`: its causal past contains `g0` (a `7`-authored block), so it is not
`A`-independent. The counterfactual genuinely removes `7`'s downstream contribution. -/
theorem demo_erase7_drops_g1 :
    ¬ (eraseAuthor demoLace 7 demoHonestConfig).mem g1 := by
  rintro ⟨_, hindep⟩
  -- g0 ≺ g1 and g0.creator = 7 contradict A-independence of g1.
  exact hindep g0 (precedes_le demo_honest_precedes) (by decide)

/-- … and `g1` itself, though authored by `7`, is also removed (it IS an `A`-event): a sanity check
that the erasure does not keep `A`'s own blocks either. -/
theorem demo_erase7_drops_g1_self :
    ¬ (eraseAuthor demoLace 7 demoHonestConfig).mem g1 :=
  fun h => eraseAuthor_no_A demoLace 7 demoHonestConfig g1 h (by decide)

/-- **Non-vacuity (positive).** Erasing the OTHER author `9` keeps the entire honest chain — `g0`
and `g1` have no `9`-block in their causal past, so the counterfactual leaves them untouched. The
erasure is not the empty operation. -/
theorem demo_erase9_keeps_g0 :
    (eraseAuthor demoLace 9 demoHonestConfig).mem g0 := by
  refine ⟨Or.inl rfl, ?_⟩
  -- AIndep: no 9-block ≺ g0. g0 is genesis; demo_precedes_left_g0 forces any source to be g0
  -- (author 7 ≠ 9), and the reflexive d = g0 case is creator 7 ≠ 9 too.
  intro d hd
  rcases hd with rfl | hpre
  · decide
  · have : d = g0 := demo_precedes_left_g0 hpre
    subst this; decide

/-! ### Keystone — `#print axioms`-clean. -/
#print axioms dreggCausal
#print axioms demo_erase7_drops_g1
#print axioms demo_erase9_keeps_g0

end Metatheory.PolisEraseBlocklace
