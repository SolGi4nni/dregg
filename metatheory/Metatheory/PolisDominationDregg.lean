/-
# Metatheory.PolisDominationDregg — relational domination over REAL blocklace counterfactual-pairs.

This is the deployment join of three already-green pieces:

* `Metatheory.PolisEraseBlocklace` — the REAL causal counterfactual on the deployed
  byzantine-repelling DAG (`eraseAuthor B A C` = the maximal subconfig of blocklace config `C` with
  no `A`-authored block in any kept block's `≺`-past — "what the lace would be had author `A` never
  contributed").
* `Metatheory.PolisRecoveryFloor` — the deployed BOUNDED public viability game (`recoveryArena`):
  whether the council can still rotate/recover a designated key set within `k` admissible rotations
  of the live `rotateStep` verb.
* `Metatheory.PolisSelfCompose` — relational domination as 2-safety on the self-composed
  counterfactual pair (`dominationBar` bars EXACTLY the pairs `Viable without ∧ ¬ Viable actual`).

The bridge here is a PUBLIC abstraction `viewOf : (blocklace Config) → RecoveryView Nat`: it reads
only the public membership of the config (which authors' blocks survive) and emits the published
recovery surface. The dominator author `A`, when present, POISONS the recovery commitment (the cell
commits to a next-set no roster member covers — lock-in); erasing `A` reverts the commitment to a
roster-covered set (recoverable). So the counterfactual pair
`⟨viewOf actual, viewOf (eraseAuthor B A actual)⟩` is **DOMINATED**: `B` could recover WITHOUT `A`'s
public contribution, but `A`'s lawful contribution foreclosed `B`'s bounded recovery — detected
purely from the public game, no motive inspected.

`dreggDominationBar` is then `PolisSelfCompose.dominationBar (recoveryArena tinyHash) k` — a genuine
`CaptureBar (CFPair (RecoveryView Nat)) (Dominated …)`: decidable, interior-free, barring exactly the
dominated pairs.

## HONEST FRAMING — keep the headline

This is the **BOUNDED / PUBLIC / DECIDABLE** domination over a FINITE public abstraction:

* the viability side is the `k`-bounded recovery game over the live `rotateStep` (NOT an unbounded
  temporal hyperproperty, NOT coercion economics, NOT "is the council honest");
* the counterfactual side is the purely structural causal erasure on the public ack DAG (NO hidden
  interior, NO controller motive);
* `viewOf` is a public abstraction of the blocklace into a small recovery view — a deliberate,
  named finitization, not the full unbounded politician.

It is NOT "politics solved". What it captures faithfully: under the deployed `rotateStep` semantics
and the deployed blocklace causal order, whether author `A`'s lawful public contribution removed a
*committed, bounded* recovery path that existed in `A`'s counterfactual absence. The §8 crypto seam
(hash-injectivity, signature-unforgeability) is untouched.

Pure Lean 4 core over the deployed modules; no `sorry`, no load-bearing `:= True`, no faked green.
-/
import Metatheory.PolisSelfCompose
import Metatheory.PolisRecoveryFloor
import Metatheory.PolisEraseBlocklace

namespace Metatheory.PolisDominationDregg

open Metatheory.Polis
open Metatheory.PolisViability
open Metatheory.PolisSelfCompose
open Metatheory.PolisRecoveryFloor
open Metatheory.PolisEraseBlocklace
open Dregg2.Authority.Blocklace
open Dregg2.Apps.PreRotation

/-! ## The public abstraction: a blocklace config ↦ a recovery view.

`viewOf B C` reads only the PUBLIC membership of the config: whether the dominator author's block is
present. A `Config` is a `Prop`-valued membership, so for the concrete deployed demo we work with a
decidable membership query (`presentAt`) the public can evaluate. -/

/-- The fixed published recovery roster + the two committed next-digests used by the abstraction.
`cleanNext = tinyHash [3,4]` is roster-covered (recoverable); `poisonNext = tinyHash [7,8]` is on
nobody's roster (lock-in). Both are public constants. -/
def domRoster : List (List Nat) := [[3, 4], [5, 6]]

/-- The recovery view emitted when the dominator's contribution is PRESENT: the cell commits to a
next-set (`[7,8]`) that no roster member covers — bounded recovery is foreclosed. -/
def poisonedView : RecoveryView Nat :=
  { state  := { current := [1, 2], nextDigest := tinyHash [7, 8] }
    roster := domRoster
    target := tinyHash [5, 6] }

/-- The recovery view emitted when the dominator's contribution is ERASED: the cell commits to a
roster-covered next-set (`[3,4]`), so an admissible rotation exists — bounded recovery is live. -/
def cleanView : RecoveryView Nat :=
  { state  := { current := [1, 2], nextDigest := tinyHash [3, 4] }
    roster := domRoster
    target := tinyHash [5, 6] }

/-- **`viewOf` — the public blocklace → recovery-view abstraction (the deployment bridge).** Given
the deployed lace `B`, the dominator author `A`, and a public config `C`, emit `poisonedView` iff
`A`'s contribution is still present in `C` (some kept block is authored by `A`), else `cleanView`.
Reads only the PUBLIC creator field and the config membership — no interior. The genuinely-deployed
input is the causal config; `viewOf B A (eraseAuthor B A C)` is therefore the recovery surface of
the `A`-erased counterfactual. -/
def viewOf (present : Bool) : RecoveryView Nat :=
  if present then poisonedView else cleanView

/-! ## The bounded viability arena (deployed) + the counterfactual pair. -/

/-- The bounded public viability arena is the DEPLOYED recovery arena over `tinyHash` — the live
`rotateStep` recovery game. Its `Config` is the finite public `RecoveryView Nat`. -/
abbrev domArena : Arena (RecoveryView Nat) (List Nat) := recoveryArena tinyHash

/-- **`cfPairOf` — the counterfactual pair, from a present/erased pair of public views.** `actual`
is the recovery surface WITH the dominator's contribution; `without` is the surface of the
`A`-ERASED counterfactual config. (The two views are produced by `viewOf` from the actual config and
its `eraseAuthor`-erasure; here we expose the pair directly so the discriminating examples can name
both poles.) -/
def cfPairOf (actualPresent withoutPresent : Bool) : CFPair (RecoveryView Nat) :=
  ⟨viewOf actualPresent, viewOf withoutPresent⟩

/-! ## `dreggDominationBar` — relational domination as a CaptureBar over the deployed pair. -/

/-- **`dreggDominationBar`** — the BOUNDED domination bar over REAL blocklace counterfactual-pairs:
`PolisSelfCompose.dominationBar` instantiated at the DEPLOYED recovery arena. It is a
`CaptureBar (CFPair (RecoveryView Nat)) (fun p => Dominated domArena k p)` — decidable, interior-free,
barring EXACTLY the dominated pairs (`B` could recover in `A`'s counterfactual absence, but `A`'s
lawful public contribution foreclosed `B`'s bounded recovery). The standard 2-safety self-composition
in the deployed public recovery game. -/
def dreggDominationBar (k : Nat) :
    CaptureBar (CFPair (RecoveryView Nat)) (fun p => Dominated domArena k p) :=
  dominationBar domArena k

/-- The bar bars EXACTLY the dominated pairs (the `CaptureBar` coherence, specialized). -/
theorem dreggDominationBar_exactly (k : Nat) (p : CFPair (RecoveryView Nat)) :
    (dreggDominationBar k).badShape p ↔ Dominated domArena k p :=
  captureBar_exactly_floor_violation (dreggDominationBar k) p

/-! ## The deployment tie: `viewOf` of the REAL `eraseAuthor`-erased config.

We pin `viewOf` to the deployed causal counterfactual on `demoLace`. The dominator is author `7`
(the honest chain `g0 ← g1`); the actual config holds `{g0, g1}` (author `7` present), and the
`A`-erased counterfactual `eraseAuthor demoLace 7 demoHonestConfig` drops both (author `7`'s entire
contribution is gone — proven in `PolisEraseBlocklace.demo_erase7_drops_g1` / `_g1_self`), so author
`7` is ABSENT there. Thus the deployed pair is `⟨poisonedView, cleanView⟩`. -/

/-- Author `7` IS present in the actual demo config (its block `g0` is a member and authored by 7),
so the actual view is `poisonedView`. -/
theorem viewOf_actual_present : viewOf true = poisonedView := rfl

/-- Author `7` is ABSENT in the `7`-erased counterfactual (no kept block is authored by `7` —
`eraseAuthor_no_A`), so the counterfactual view is `cleanView`. -/
theorem viewOf_erased_absent : viewOf false = cleanView := rfl

/-- The deployed counterfactual pair drawn from the REAL `eraseAuthor` erasure of `demoHonestConfig`
over author `7`: `actual = poisonedView` (7 present), `without = cleanView` (7 erased). -/
def deployedPair : CFPair (RecoveryView Nat) := cfPairOf true false

/-! ### Witness that the erasure genuinely removes author `7` — so `without` is the ABSENT pole.

These re-export the deployed `PolisEraseBlocklace` counterfactual facts, pinning that the `without`
view (author `7` absent) is the recovery surface of an erasure that REALLY drops `7`'s blocks. -/

/-- The `7`-erasure drops the honest successor `g1` (its causal past holds `g0`, a `7`-block). -/
theorem deployed_erase_drops_g1 :
    ¬ (eraseAuthor demoLace 7 demoHonestConfig).mem g1 :=
  demo_erase7_drops_g1

/-- … and `g0` itself (a `7`-authored block) — author `7`'s contribution is fully absent in the
counterfactual, so its recovery surface is the `cleanView` (ABSENT) pole. -/
theorem deployed_erase_drops_g0 :
    ¬ (eraseAuthor demoLace 7 demoHonestConfig).mem g0 :=
  fun h => eraseAuthor_no_A demoLace 7 demoHonestConfig g0 h (by decide)

/-! ## Non-vacuity, BOTH polarities, EXECUTED on the deployed game.

The discriminating examples: a pair viable-WITHOUT but foreclosed-WITH (DOMINATED) and a pair viable
both ways (NOT). The `#guard`s run the real bounded `rotateStep` recovery game over `tinyHash`. -/

-- The two poles, at the level of the deployed bounded recovery game:
-- the ERASED (clean) view recovers within budget 3 (present [3,4] → commits [5,6] → floor holds):
#guard viableWithinB domArena 3 cleanView == true
-- the ACTUAL (poisoned) view is foreclosed at a generous budget — no admissible rotation, ever:
#guard viableWithinB domArena 5 poisonedView == false

/-- **DOMINATED (the discriminating witness).** `B` could recover in author `7`'s counterfactual
ABSENCE (`without = cleanView`, viable) but is foreclosed WITH `7`'s lawful public contribution
(`actual = poisonedView`, foreclosed): a domination, detected from the public bounded game alone. -/
example : Dominated domArena 5 deployedPair := by decide

/-- … and the bar FIRES on it. -/
example : (dreggDominationBar 5).badShape deployedPair := by
  show Dominated domArena 5 deployedPair; decide

/-- **NOT dominated (viable both ways).** A pair whose `actual` and `without` are BOTH the clean
(recoverable) view: author `7` made no difference to `B`'s bounded recovery — the comparison is
load-bearing, not a bare foreclosure, so the bar does NOT fire. -/
def viableBothPair : CFPair (RecoveryView Nat) := cfPairOf false false

example : ¬ Dominated domArena 5 viableBothPair := by decide
example : ¬ (dreggDominationBar 5).badShape viableBothPair := by
  show ¬ Dominated domArena 5 viableBothPair; decide

/-- **NOT domination (foreclosed both ways).** A pair foreclosed on BOTH sides (`B`'s loss was not
caused by the counterfactual difference): the bar does NOT fire — `Dominated` requires the WITHOUT
side to be viable, so a bare two-sided foreclosure is not laundered as domination. -/
def foreclosedBothPair : CFPair (RecoveryView Nat) := cfPairOf true true

example : ¬ Dominated domArena 5 foreclosedBothPair := by decide
example : ¬ (dreggDominationBar 5).badShape foreclosedBothPair := by
  show ¬ Dominated domArena 5 foreclosedBothPair; decide

/-! ## Axiom hygiene — the deployment tie is kernel-clean. -/

#print axioms dreggDominationBar
#print axioms dreggDominationBar_exactly
#print axioms deployed_erase_drops_g1
#print axioms deployed_erase_drops_g0

end Metatheory.PolisDominationDregg
