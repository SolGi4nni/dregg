/-
# Metatheory.PolisViewFunctor — the GENERAL, decidable blocklace → recovery-view abstraction.

`Metatheory.PolisDominationDregg` carries a public abstraction `viewOf : Bool → RecoveryView Nat`
that picks between two fixed poles (`poisonedView` / `cleanView`) by a single present/absent `Bool`.
That is a deliberate **2-point finitization**: it reads "is the dominator present" off a precomputed
flag rather than from the real config membership. This file CLOSES that residual.

What it provides:

* **`presentAuthor : Lace → AuthorId → Bool`** — a GENERAL, DECIDABLE membership query over an
  ARBITRARY blocklace config (represented by its finite kept-block list): does some `Block` whose
  `creator` is `A` occur in the config? This is `List.any` over `DecidableEq` author ids — public
  (reads only the published `creator` field), decidable for any config, no fixed poles.
* **`viewOfConfig : Lace → AuthorId → RecoveryView Nat`** — the general view functor: present ⇒ the
  poisoned (lock-in) view, absent ⇒ the clean (recoverable) view, driven by the REAL membership.
* the **generalization theorem** `viewOfConfig_generalizes`: on the deployed demo, `viewOfConfig`
  agrees with `PolisDominationDregg.viewOf` on BOTH poles, so the 2-point `viewOf` is exactly the
  restriction of this general functor to the demo present/absent cases.

The genuinely-deployed input is the causal config (`Metatheory.PolisErase.Config`). Its `mem` is a
`Prop`-valued down-closed predicate (not decidable in general); the public, decidable thing the
abstraction can actually evaluate is the FINITE list of blocks the config keeps. `keptBlocks` snapshots
that list against a backing lace using the config's own decidable-membership instance, and the bridge
lemmas tie `presentAuthor (keptBlocks …)` to the causal `Config.mem` so the general functor is driven
by the real down-closed config — including the `eraseAuthor` counterfactual.

## HONEST FRAMING — BOUNDED / PUBLIC / DECIDABLE

`presentAuthor` reads only the public `creator` keys of the FINITE kept-block list; it is decidable
for any config. It is NOT a peek into controller intent and NOT an unbounded membership oracle over an
infinite event space — it is the public author-occurrence of a finite published config snapshot.
The §8 crypto seam (hash-injectivity, signature-unforgeability) is untouched, exactly as in the
deployed `Blocklace.lean`. No `sorry`, no load-bearing `:= True`, no faked green.
-/
import Metatheory.PolisDominationDregg

namespace Metatheory.PolisViewFunctor

open Metatheory.PolisRecoveryFloor
open Metatheory.PolisDominationDregg
open Metatheory.PolisEraseBlocklace
open Dregg2.Authority.Blocklace

/-! ## 1. The general, decidable present-author query over an ARBITRARY config. -/

/-- **`presentAuthor B A` — the general, decidable author-occurrence query.** Over an ARBITRARY
blocklace config (its finite kept-block list `B`), does some `Block` authored by `A` occur? A
`List.any` over `DecidableEq AuthorId` — public (only the `creator` field is read), decidable for any
config, with NO fixed 2-point pole. This is the real membership the 2-point `viewOf` short-circuits. -/
def presentAuthor (B : Lace) (A : AuthorId) : Bool :=
  B.any (fun b => b.creator == A)

/-- `presentAuthor` is exactly "∃ a present block authored by `A`" — the decidable query reflects the
genuine occurrence predicate (not a precomputed flag). -/
theorem presentAuthor_iff (B : Lace) (A : AuthorId) :
    presentAuthor B A = true ↔ ∃ b ∈ B, b.creator = A := by
  unfold presentAuthor
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hmem, hbeq⟩; exact ⟨b, hmem, by simpa using (beq_iff_eq).1 hbeq⟩
  · rintro ⟨b, hmem, hbc⟩; exact ⟨b, hmem, by simpa using (beq_iff_eq).2 hbc⟩

/-- Absence reflects "no present block is authored by `A`" — the dual, decidable. -/
theorem presentAuthor_false_iff (B : Lace) (A : AuthorId) :
    presentAuthor B A = false ↔ ∀ b ∈ B, b.creator ≠ A := by
  rw [← Bool.not_eq_true, presentAuthor_iff]
  simp only [not_exists, not_and, ne_eq]

/-! ## 2. The general view functor. -/

/-- **`viewOfConfig B A` — the GENERAL blocklace → recovery-view abstraction.** Driven by the REAL,
decidable membership `presentAuthor`: if some block authored by `A` occurs in the config `B`, the
dominator's contribution is PRESENT and the cell is poisoned (lock-in, no roster-covered next),
`poisonedView`; otherwise the contribution is ABSENT and recovery is live, `cleanView`. No fixed
poles — `B` ranges over any config, `A` over any author. This is the de-finitization of the 2-point
`PolisDominationDregg.viewOf`. -/
def viewOfConfig (B : Lace) (A : AuthorId) : RecoveryView Nat :=
  if presentAuthor B A then poisonedView else cleanView

/-- The general functor lands on the poisoned pole exactly when the dominator is present. -/
theorem viewOfConfig_present (B : Lace) (A : AuthorId) (h : presentAuthor B A = true) :
    viewOfConfig B A = poisonedView := by unfold viewOfConfig; rw [h]; rfl

/-- … and on the clean pole exactly when the dominator is absent. -/
theorem viewOfConfig_absent (B : Lace) (A : AuthorId) (h : presentAuthor B A = false) :
    viewOfConfig B A = cleanView := by unfold viewOfConfig; rw [h]; rfl

/-- **`viewOfConfig` agrees with the 2-point `viewOf` for any config.** It is literally
`PolisDominationDregg.viewOf` applied to the REAL present/absent flag of the config, rather than a
hand-supplied `Bool`: `viewOfConfig B A = viewOf (presentAuthor B A)`. This is the precise sense in
which the general functor GENERALIZES the 2-point one. -/
theorem viewOfConfig_eq_viewOf (B : Lace) (A : AuthorId) :
    viewOfConfig B A = viewOf (presentAuthor B A) := by
  unfold viewOfConfig viewOf; rfl

/-! ## 3. Tie to the REAL causal config: the kept-block snapshot of a `Config`.

The deployed input is a `Metatheory.PolisErase.Config (dreggCausal B)` whose `mem` is a Prop-valued
down-closed predicate. The public, decidable object the abstraction evaluates is the finite list of
blocks of the backing lace the config keeps. `keptBlocks` snapshots that, given the config's own
`DecidablePred mem`; the bridge lemmas tie `presentAuthor (keptBlocks …)` to the causal `Config.mem`,
so the general functor is genuinely driven by the real down-closed config (incl. `eraseAuthor`). -/

/-- The finite kept-block snapshot of a causal config `C` against backing lace `B`: the blocks of `B`
that `C` keeps. Requires the config's membership to be DECIDABLE (which the concrete deployed configs
supply) — this is the public, evaluable face of the Prop-valued `Config.mem`. -/
def keptBlocks (B : Lace) (C : Metatheory.PolisErase.Config (dreggCausal B))
    [DecidablePred C.mem] : Lace :=
  B.filter (fun b => decide (C.mem b))

/-- **Membership of the snapshot reflects the causal config** (for blocks of the backing lace): a
block of `B` is in `keptBlocks` iff the config keeps it. The public snapshot is faithful to `mem`. -/
theorem mem_keptBlocks (B : Lace) (C : Metatheory.PolisErase.Config (dreggCausal B))
    [DecidablePred C.mem] {b : Block} (hb : b ∈ B) :
    b ∈ keptBlocks B C ↔ C.mem b := by
  unfold keptBlocks
  rw [List.mem_filter]
  exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨hb, decide_eq_true h⟩⟩

/-- **The bridge: `presentAuthor` of the snapshot reflects the causal config.** Author `A` occurs in
the kept snapshot iff the config keeps SOME block of the backing lace authored by `A`. So the general
functor `viewOfConfig (keptBlocks B C) A` is driven by the REAL down-closed config membership — this
is what removes the "precomputed flag" finitization. -/
theorem presentAuthor_keptBlocks (B : Lace) (C : Metatheory.PolisErase.Config (dreggCausal B))
    [DecidablePred C.mem] (A : AuthorId) :
    presentAuthor (keptBlocks B C) A = true ↔ ∃ b ∈ B, C.mem b ∧ b.creator = A := by
  rw [presentAuthor_iff]
  constructor
  · rintro ⟨b, hmem, hbc⟩
    have hbB : b ∈ B := (List.mem_filter.mp (by unfold keptBlocks at hmem; exact hmem)).1
    exact ⟨b, hbB, (mem_keptBlocks B C hbB).mp hmem, hbc⟩
  · rintro ⟨b, hbB, hkeep, hbc⟩
    exact ⟨b, (mem_keptBlocks B C hbB).mpr hkeep, hbc⟩

/-! ### The general absence law for ANY `eraseAuthor` counterfactual.

The `eraseAuthor` config's `mem` is `C.mem ∧ AIndep`, whose `AIndep` (`∀ d, le d e → …`) is NOT
decidable in general — so we do NOT compute its snapshot. Instead we characterize the ABSENT pole
abstractly: for ANY decidable config snapshot over a backing lace, if NO kept block is authored by
`A`, then `presentAuthor` of that snapshot is `false`. The deployed `eraseAuthor_no_A` supplies
exactly that hypothesis for the erased counterfactual — so the general functor lands on the clean
pole over the REAL erasure, decidability of the erased config not required. -/

/-- **General absence law.** If a decidable config keeps no block authored by `A` (the deployed
`eraseAuthor_no_A` shape), then `presentAuthor` of its snapshot is `false` — the functor's clean pole
over the real counterfactual. -/
theorem presentAuthor_keptBlocks_absent (B : Lace)
    (C : Metatheory.PolisErase.Config (dreggCausal B)) [DecidablePred C.mem]
    (A : AuthorId) (habsent : ∀ b ∈ B, C.mem b → b.creator ≠ A) :
    presentAuthor (keptBlocks B C) A = false := by
  rw [presentAuthor_false_iff]
  intro b hmem
  have hbB : b ∈ B := (List.mem_filter.mp (by unfold keptBlocks at hmem; exact hmem)).1
  exact habsent b hbB ((mem_keptBlocks B C hbB).mp hmem)

/-! ## 4. Generalization theorem: the general functor reproduces the 2-point poles on the demo.

On the deployed demo, `viewOfConfig` over REAL kept-block snapshots agrees with
`PolisDominationDregg.viewOf` on both poles — so the 2-point `viewOf` is exactly the restriction of
this general, decidable functor to the demo's present/absent cases.

* the ACTUAL honest config keeps `{g0, g1}`, both authored by `7` ⇒ author `7` is PRESENT;
* the `7`-ERASED counterfactual keeps NO block authored by `7` (`eraseAuthor_no_A`) ⇒ ABSENT.
-/

/-- Membership of `demoHonestConfig` (`e = g0 ∨ e = g1`) is DECIDABLE — the config snapshot is
computable, so `actualKept` is a concrete list. -/
instance : DecidablePred demoHonestConfig.mem := fun e =>
  inferInstanceAs (Decidable (e = g0 ∨ e = g1))

/-- The kept-block snapshot of the ACTUAL demo honest config: `[g0, g1]` (the blocks of `demoLace`
the config keeps). -/
def actualKept : Lace := keptBlocks demoLace demoHonestConfig

/-- **Author `7` is PRESENT in the actual demo snapshot** (its blocks `g0, g1` are kept). Proved via
the bridge `presentAuthor_keptBlocks`, with witness `g0` (in `demoLace`, kept by `demoHonestConfig`,
authored by `7`) — the REAL membership, not a precomputed flag. -/
theorem actual_present : presentAuthor actualKept 7 = true := by
  unfold actualKept
  rw [presentAuthor_keptBlocks]
  refine ⟨g0, ?_, Or.inl rfl, by decide⟩
  simp [demoLace]

/-- **Author `7` is ABSENT in the `7`-erased counterfactual** — via the deployed `eraseAuthor_no_A`:
the erasure keeps no block authored by `7`, so `presentAuthor` of ANY snapshot of it is `false`.
(Stated against an arbitrary decidable snapshot of the erased config — the absence is structural, not
a computed flag.) -/
theorem erased_absent (C : Metatheory.PolisErase.Config (dreggCausal demoLace))
    [DecidablePred C.mem]
    (hsub : ∀ b ∈ demoLace, C.mem b → (eraseAuthor demoLace 7 demoHonestConfig).mem b) :
    presentAuthor (keptBlocks demoLace C) 7 = false :=
  presentAuthor_keptBlocks_absent demoLace C 7
    (fun b hb hCb => eraseAuthor_no_A demoLace 7 demoHonestConfig b (hsub b hb hCb))

/-- **`viewOfConfig` reproduces the POISONED pole on the actual config** — driven by REAL membership
(author `7` present), it equals `PolisDominationDregg.viewOf true = poisonedView`. -/
theorem viewOfConfig_actual : viewOfConfig actualKept 7 = poisonedView :=
  viewOfConfig_present _ _ actual_present

/-- **`viewOfConfig` reproduces the CLEAN pole on the `7`-erased config** — driven by REAL membership
(author `7` absent via `eraseAuthor_no_A`), it equals `PolisDominationDregg.viewOf false = cleanView`,
over ANY decidable snapshot of the erased counterfactual. -/
theorem viewOfConfig_erased (C : Metatheory.PolisErase.Config (dreggCausal demoLace))
    [DecidablePred C.mem]
    (hsub : ∀ b ∈ demoLace, C.mem b → (eraseAuthor demoLace 7 demoHonestConfig).mem b) :
    viewOfConfig (keptBlocks demoLace C) 7 = cleanView :=
  viewOfConfig_absent _ _ (erased_absent C hsub)

/-- **THE GENERALIZATION THEOREM.** On the deployed demo, the general decidable functor agrees with
`PolisDominationDregg.viewOf` on BOTH poles:

* the ACTUAL config (author `7` present)  ↦ `viewOf true`  (`poisonedView`);
* any snapshot of the `7`-ERASED config (author `7` absent) ↦ `viewOf false` (`cleanView`).

So the 2-point `viewOf` is exactly the restriction of this general, real-membership-driven functor to
the demo present/absent cases — the "2-point finitization" residual is closed. -/
theorem viewOfConfig_generalizes
    (C : Metatheory.PolisErase.Config (dreggCausal demoLace)) [DecidablePred C.mem]
    (hsub : ∀ b ∈ demoLace, C.mem b → (eraseAuthor demoLace 7 demoHonestConfig).mem b) :
    viewOfConfig actualKept 7 = viewOf true ∧
      viewOfConfig (keptBlocks demoLace C) 7 = viewOf false := by
  refine ⟨?_, ?_⟩
  · rw [viewOfConfig_actual, viewOf_actual_present]
  · rw [viewOfConfig_erased C hsub, viewOf_erased_absent]

/-- **The deployed counterfactual pair, REBUILT from the general functor.** The `cfPairOf true false`
of `PolisDominationDregg` (the `⟨poisonedView, cleanView⟩` demo pair) is exactly the pair of general
functor views over the actual snapshot and ANY snapshot of the `7`-erased counterfactual — the
domination bar consumes the SAME object, now produced by real membership rather than a fixed flag. -/
theorem deployedPair_from_functor
    (C : Metatheory.PolisErase.Config (dreggCausal demoLace)) [DecidablePred C.mem]
    (hsub : ∀ b ∈ demoLace, C.mem b → (eraseAuthor demoLace 7 demoHonestConfig).mem b) :
    (⟨viewOfConfig actualKept 7, viewOfConfig (keptBlocks demoLace C) 7⟩ :
      Metatheory.PolisSelfCompose.CFPair (RecoveryView Nat)) = deployedPair := by
  unfold deployedPair cfPairOf
  rw [viewOfConfig_actual, viewOfConfig_erased C hsub, viewOf_actual_present, viewOf_erased_absent]

/-! ## 5. Non-vacuity of GENERALITY — the functor is not pinned to two configs.

A fresh config the 2-point `viewOf` never anticipated: a single-author lace. `presentAuthor` decides
it directly, and `viewOfConfig` produces the matching pole — demonstrating the functor ranges over
ARBITRARY configs, not the demo poles. -/

/-- A novel one-block config authored by `42` (not the demo's `7`/`9`). -/
def soloLace : Lace := [{ id := 99, creator := 42, seq := 0, preds := [] }]

-- Author 42 present here (poisoned pole), author 7 absent (clean pole) — a config off the demo axis.
-- The present/absent membership is decidable and computes directly:
#guard presentAuthor soloLace 42 == true
#guard presentAuthor soloLace 7 == false

-- … and the functor lands on the matching pole (`RecoveryView` has no `DecidableEq`, so the view
-- equality is proved by `rfl`/`simp` off the reduced flag — not `decide`):
example : viewOfConfig soloLace 42 = poisonedView :=
  viewOfConfig_present soloLace 42 (by rfl)
example : viewOfConfig soloLace 7 = cleanView :=
  viewOfConfig_absent soloLace 7 (by rfl)

-- The empty config: nobody present, clean pole (no 2-point finitization can name this case):
#guard presentAuthor ([] : Lace) 7 == false
example : viewOfConfig ([] : Lace) 7 = cleanView :=
  viewOfConfig_absent [] 7 (by rfl)

/-! ## 6. Axiom hygiene. -/

#print axioms presentAuthor_iff
#print axioms presentAuthor_keptBlocks
#print axioms viewOfConfig_generalizes
#print axioms deployedPair_from_functor

end Metatheory.PolisViewFunctor
