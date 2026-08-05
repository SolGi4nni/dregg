/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins06 — §16b — W-SPLIT

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Pins only. Every `def` this section had is in `…Fixture`; the namespace-wide axiom pin is in the
`KimchiWrapMain` umbrella, which imports every one of these.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ### §16b — ⚑ **W-SPLIT'S PINS, AS NAMED THEOREMS.**

Every claim §16 makes about a ROW is read off the emitted row list, and the two claims it makes
about upstream's ARITHMETIC are closed in the kernel rather than asserted in prose. No new `#guard`s. -/

/-- ⚑ **THE SELECTION FINDS EXACTLY THE `` `Field `` WORDS.** The wrap shape's ten `split_field`
calls are `wrap_main.ml:409` applied to the five `B Field` words of each of the two `per_proof`
blocks; the smoke shape's four-entry spread carries exactly one of those pairs, at positions
`(0, 1)`. A shape that selected a value half without its parity would contribute NO pair, which is
what makes this a pin on the WIDTH TABLE rather than on a hand-copied index list. -/
theorem split_pairs_are_the_field_words :
    splitPairs shapeSmoke = [(0, 1)]
    ∧ (splitPairs shapeWrap).length = 10
    ∧ (splitPairs shapeWrap).map (fun p => xhAt shapeWrap p.1)
        = [0, 2, 4, 6, 8, 32, 34, 36, 38, 40] := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE TIE IS TO §15's ENTRY SCALARS, NOT TO FRESH CELLS.** For every pair, the emitted row
list carries the half whose three permutation variables are `(x, y, is_odd)` with `y` and `is_odd`
the MSM entry scalars `xA k 4` and `xA k' 4` at `cSplit 1` — i.e.
`Field.Assert.equal ((of_int 2 * y) + is_odd) x`. This is the whole of W-SPLIT's content and it is
read off the ROWS. -/
theorem split_ties_the_msm_entry_scalars :
    ((splitPairs shapeSmoke).zip (List.range (splitPairs shapeSmoke).length)).all (fun pa =>
      hasHalf spRows [some (xSplitW shapeSmoke tKey.sp pa.2),
                      some (xA shapeSmoke tKey.sp pa.1.1 4),
                      some (xA shapeSmoke tKey.sp pa.1.2 4)] (cSplit 1)) = true := by
  rfl

/-- ⚑ **THE PARITY IS BOOLEAN-CONSTRAINED TWICE, AND BOTH ARE UPSTREAM'S.** `exists Typ.(field *
Boolean.typ)` in `split_field` is this section's; `assert_ (Constraint.boolean b)` at
`wrap_verifier.ml:573-576` is §15's `` `Cond_add `` arm. Emitting one would be LESS strict than
`wrap_main`, so the pin is that BOTH row lists carry the half — not that one does. -/
theorem split_parity_is_boolean_in_both_sections :
    hasHalf spRows [some (xA shapeSmoke tKey.sp 1 4), some (xA shapeSmoke tKey.sp 1 4),
                    some (xA shapeSmoke tKey.sp 1 4)] cBool = true
    ∧ hasHalf xhRows [some (xA shapeSmoke tKey.sp 1 4), some (xA shapeSmoke tKey.sp 1 4),
                      some (xA shapeSmoke tKey.sp 1 4)] cBool = true := by
  refine ⟨rfl, rfl⟩

/-- W-SPLIT spends `Generic` halves and σ-probes and NOTHING else — `split_field` has no curve op,
no sponge and no lookup. A row family appearing here would mean the gadget was read wrong. -/
theorem split_rows_are_generic_and_probe_only :
    ((splitRows tKey true).filter (fun r => r.kind == KGateType.generic)).length = 1
    ∧ ((splitRows tKey true).filter (fun r => r.probe)).length = 1
    ∧ ((splitRows tKey true).filter (fun r => r.kind == KGateType.varBaseMul)).length = 0
    ∧ ((splitRows tKey true).filter (fun r => r.kind == KGateType.completeAdd)).length = 0
    ∧ ((splitRows tKey true).filter (fun r => r.kind == KGateType.poseidon)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The `w7_split` rung is a strict superset of `w6_xhat`, its length is the sum of its parts, and
the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns — the property
that makes the harness's control byte-identical everywhere else. -/
theorem split_rung_extends_xhat :
    (rungRows tKey .split true).length
      = (rungRows tKey .xhat true).length + (splitRows tKey true).length
    ∧ (rungRows tKey .xhat true).length < (rungRows tKey .split true).length
    ∧ (((rungRows tKey .split true).zip (rungRows tKey .split false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tKey .split true).filter (fun r => r.probe)).length
    ∧ rungPub shapeSmoke .split = rungPub shapeSmoke .xhat := by
  refine ⟨rfl, by decide, rfl, rfl⟩

/-- `placeChecked` ACCEPTS the `w7_split` rung and no public word is inert — the fail-closed
placement, at the new top rung rather than at the one below it. -/
theorem split_rung_places_and_exposes_every_public_word :
    refusalOf shapeSmoke shapeSmoke.pubWords (wrapGates (rungRows tKey .split true)) = none
    ∧ inertPublicWords shapeSmoke.pubWords (wrapGates (rungRows tKey .split true)) = [] := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **WHAT `scale_fast2`'s TOP-BIT ZERO ACTUALLY BUYS — IN THE KERNEL, NOT IN PROSE.**
`plonk_curve_ops.ml:262-265` asserts ONE bit zero at width 255, giving `s_div_2 < 2^254`.

  * `2^254 < q`, so that bit CANONICALISES the ladder's own 255-cell decomposition: `B < 2^254 < q`
    is the unique representative of `s_div_2` mod `q`, and the multiplier the `EC_scale` gate uses
    IS the scalar `Field.Assert.equal !n_acc scalar` names.
  * `2·2^254 > q`, so it bounds `y = 2·s_div_2 + s_odd` by NOTHING: every `y ∈ Fq` has a split with
    `s_div_2 < 2^254`. Upstream's comment at `wrap_main.ml:64-68` calls this the deferred check on
    the high bits; it is a canonicity guard one level down, and §16 says so.

Both halves are needed: the first alone would read as "the deferral works", the second alone as "the
deferral is empty". Neither is true on its own. -/
theorem split_deferred_check_canonicalises_but_does_not_bound :
    2 ^ 254 < qN ∧ qN < 2 * 2 ^ 254 ∧ xhatTopZeros 0 = 1 ∧ xhatTopZeros 11 = 3 := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide

end Dregg2.Circuit.Emit.KimchiWrapMain
