# DEBT-A mod-p wrap-forgery audit — findings + repair playbook (2026-07-11)

The DEBT-A migration retargeted `VmConstraint.holdsVm .gate` from `body.eval = 0` over ℤ to
`body.eval ≡ 0 [ZMOD 2013265921]` (BabyBear `p < 2³¹`). This broke a large cascade of circuit-apex
soundness modules (~of 196 `Dregg2/Circuit/*.lean`) and — because `p < 2³¹` with un-range-checked
limbs — exposed a **class of deployed wrap forgeries**. This doc is the handoff: the classifying rule,
the two forgeries found, the mechanical repair pattern, and status — so any lane can sort forgery-vs-mechanical
instantly.

## THE CLASSIFYING RULE (extracted, load-bearing)
A migrated keystone is a **WRAP FORGERY** iff BOTH:
1. an **un-range-checked** operand/limb whose reconstructed ℤ value can exceed `p`, AND
2. the invariant is an **ORDER** (`≤`) — order is NOT preserved mod `p` (an underflow wraps to `+p ∈ [0,2³⁰)`,
   passing the 30-bit range check).

Otherwise it is **REPAIRABLE** by threading canonicality:
- **equality / tick / write** (e.g. `nonce+1`, `fields[slot]=v`): recover the exact ℤ equality via the row's
  canonicality envelope (`canon_eq_of_modEq`), OR state `≡ [ZMOD p]`.
- **`≡ [ZMOD p]` balance congruence** (debit/credit): restate the conclusion as the congruence, re-prove.
- **bitwise-boolean subset** (attenuation/facet non-amp): `bit·(bit−1) ≡ 0 [ZMOD p]` + bit-canonicality
  (`0 ≤ bit < p`) pins each bit `{0,1}` exactly → faithful.

## THE MECHANICAL RED CAUSE
The migrated `*Vm_faithful` / gate sources gained a new `hcanon`/`hgc`/`hhc`/`CapOpenRowCanon` argument
(the canonicality the deployed range-check supplies). Downstream refinement calls missing it go red →
Lean error-recovery inserts `sorryAx` → the `#assert_axioms` gate fails. **Fix = thread the canonicality**
(from the row's range table if the column is range-checked; as a NAMED residual field on the `rotatedEncodes*`
structure — documented — if it isn't), then restate faithfully per the rule above.

## THE TWO DEPLOYED FORGERIES (ember-gated denotation fix)
Both are **availability** (`amt ≤ bal`) — an ORDER over the un-range-checked amount limb. Relocated to
named `guardAvail`-style residuals with the witness documented (NOT faked as circuit-forced).
1. **Transfer availability** (`RotatedKernelRefinement.lean`) — `pre.bal=0, amt=10⁹ → post.bal=1013265921 ∈ [0,2³⁰)`
   passes, yet `amt>bal`. Mint-from-nothing.
2. **Burn availability** (`RotatedKernelRefinementMintBurn.lean`) — WORSE: burn's ledger frame credits the well
   `(a,a)`, so the underflow **inflates well supply** = mint-from-nothing into the well.
**Fix (ember-gated, NOT done):** range-check the amount limb `< p − 2³⁰`, add a no-underflow/borrow bit, or use a
field with `p ≥ 2^(2·BAL_LIMB_BITS)`. Applies identically to both.

## STATUS — repaired (green, axiom-clean, no sorryAx)
`RotatedKernelRefinement` (transfer), `…Attenuate`, `…IncNonce`, `…SetField`, `…MintBurn`, `…Facet`, `…CellSeal`
— 7 modules. Each: canonicality threaded, keystones restated faithfully, forgeries named-not-faked. The
`guardAvail` field was propagated to consumers (`CircuitCompleteness`, `ClosureTransfer`, `TransferDecodeBridge`,
`CircuitCompletenessValue`, `FloorsNonVacuousWave`).

## REMAINING (the DEBT-A campaign — multi-agent, cascading)
Red from the same migration, not yet repaired here: `…Birth`, `…Lifecycle`, `…CapFamily`(green?), `FacetTurnBound`,
`CapOpenTurnPins`, `AirChecksSatisfied`, `EffectCommit2`, `ActionDispatch`, `AccountsCommit`, `DeployedCapTree`,
`FriSoundness`, `RecursiveAggregation`, + more. Each is REPAIRABLE-or-FORGERY by the rule above. The whole-tree
gauntlet greens when the cascade completes. **Check each for the availability-class forgery** (order over an
un-range-checked limb) as you go — that's where the real deployed bugs hide.
