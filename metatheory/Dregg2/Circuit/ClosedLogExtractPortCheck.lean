/-
# Dregg2.Circuit.ClosedLogExtractPortCheck — the SEMANTIC TEETH of the `ClosedLogExtract` port.

`ClosureAll.ClosedLogExtract` used to be

```
def ClosedLogExtract S LH hash R e : Prop :=
  Poseidon2SpongeCR hash →                       -- ⚑ the floor, in the def's BODY
  ∀ minit mfin maddrs t pc pubLogPre pubLogPost pre post,
    Satisfied2 hash (R e) minit mfin maddrs t → StateDecodeLog S LH … → kstepAll e pre post
```

`Poseidon2SpongeCR` is PROVED FALSE at deployed BabyBear parameters in this tree
(`Poseidon2Surface.poseidon2SpongeCR_false_babyBear`). Sitting in a def's VALUE rather than in a
binder, it was invisible to every binder-keyed ruler: a theorem that merely MENTIONED
`ClosedLogExtract` in its statement carried a refuted floor with no floor binder anywhere in its
type. `#floor_census`'s Pass 1b is what made the class visible at all.

## What the port was, and why it is a DELETION rather than a re-grounding
The antecedent was DEAD. Every one of the 35 rungs in the tree that discharges a `ClosedLogExtract`
slot bound it as `_hCR` and never used it — the binding those rungs actually consume is
`logHashInjective`, and that one lives inside `StateDecodeLog`, not in the antecedent. So the port
is not a re-grounding onto a different carrier and needs no bridge lemma: the hypothesis is simply
struck out. That makes the bundle STRICTLY STRONGER (one fewer assumption ⇒ producers prove more,
consumers supply less), which is the opposite of the additive-regrounding sin this campaign exists
to remove.

Three consequences the campaign should read as the actual win, all pinned below:

* `ClosureReadoutsRealizable.closedLogExtract_emptyTag_false` and `closureReadouts_uninstantiable`
  used to carry `Poseidon2SpongeCR hash` for the sole purpose of feeding the deleted antecedent.
  A REFUTATION resting on a hypothesis that is FALSE at deployed parameters proves nothing. Both
  now refute with no sponge-CR assumed.
* `lightclient_unfoolable_live` / `lightclient_unfoolable_closed_final_live` shed the binder too.
* Every consumer that merely MENTIONS `ClosedLogExtract` stops being a silent prop-body carrier.

## The teeth, and why they cannot go stale
Everything here arrives through IMPORTS, so lake's dependency graph sees it: editing `ClosureAll`
invalidates this module's olean and forces re-elaboration. Nothing is read through `IO.FS`.

* **§1 — the SHAPE PIN.** An independently written `Eq` between `ClosedLogExtract` and the intended
  floor-free telescope, closed by `rfl`. Accepted only by KERNEL DEFEQ. Re-adding the antecedent, or
  any binder drift/reorder, turns this RED. This is the standing gate against the port's reversal.
* **§2 — PROOF-CLOSURE freedom.** `#assert_not_depends_on` on the ported statements: the refuted
  floor is unreachable from their proof terms, not merely absent from their types.
* **§3 — NO STRENGTH LOST, in the consumers.** The pre-port statements re-derived through the ported
  ones, so the port is checked to remove an assumption without weakening a conclusion.
* **§4 — the strengthened refutations, typed out.** `example : ⟨CR-free type⟩ := @original`.

This module only CHECKS. It proves no new mathematics; a green run means "the port is still in
place and still floor-free in statement and proof", not that the surviving tree is sound.
-/
import Dregg2.Circuit.ClosureReadoutsRealizable
import Dregg2.Circuit.ClosureFinalAvail

namespace Dregg2.Circuit.ClosedLogExtractPortCheck

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (logHashInjective compressInjective compressNInjective
  cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.ClosureAll (ClosedLogExtract)
open Dregg2.Exec

set_option autoImplicit false

/-! ## §1 — the SHAPE PIN: `ClosedLogExtract` IS the floor-free telescope.

Written out independently of the definition and closed by `rfl`, so only kernel defeq accepts it.
Restoring `Poseidon2SpongeCR hash →` (or any other antecedent) makes this a type error. -/

/-- ⚙ PORT CHECK — the ported `ClosedLogExtract`, spelled out with NO floor antecedent. -/
theorem closedLogExtract_shape :
    @ClosedLogExtract =
      fun (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ)
          (R : Registry) (e : EffectIdx) =>
        ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
          (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
          (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState),
          Dregg2.Circuit.DescriptorIR2.Satisfied2 hash (R e) minit mfin maddrs t →
          StateDecodeLog S LH pc pubLogPre pubLogPost pre post →
          kstepAll e pre post :=
  rfl

/-! ## §2 — PROOF-CLOSURE freedom: the refuted floor is unreachable, not merely unmentioned. -/

#assert_not_depends_on Dregg2.Circuit.ClosureAll.ClosedLogExtract
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

#assert_not_depends_on Dregg2.Circuit.ClosureReadoutsRealizable.closedLogExtract_emptyTag_false
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

#assert_not_depends_on Dregg2.Circuit.ClosureReadoutsRealizable.closureReadouts_uninstantiable
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-
⚑ MEASURED, and deliberately NOT asserted here: `closureReadouts_uninstantiable_concrete` still
REACHES `Poseidon2SpongeCR` in its proof closure, by the path

  `closureReadouts_uninstantiable_concrete → Poseidon2Binding.logHashInjective_of_realization
   → Poseidon2Binding.LogRealization.spongeCR → Poseidon2SpongeCR`

and that reach is CORRECT, not a residual of this port. `_concrete` instantiates at the REFERENCE
sponge, where `Reference.refLogRealization.spongeCR := refSponge_CR` is a PROVED
`Poseidon2SpongeCR refSponge` — the floor discharged at a concrete injective encoder, not assumed at
the deployed one. `#assert_not_depends_on` is a proof-closure rejector and cannot distinguish
"assumes the floor" from "proves the floor at a point where it is true", so asserting it here would
either fail honestly (as it does) or force the guard to be relaxed — and relaxing a guard to make a
claim fit is how this campaign got its vacuity in the first place. The three assertions above are the
ones whose independence is a real claim; this one is left as a NAMED, measured dependency.
-/

/-! ## §3 — NO STRENGTH LOST, checked at the consumers.

The pre-port statements, typed out verbatim and re-derived through the ported ones. A conclusion
silently weakened by the port would go red here. -/

/-- ⚙ NO STRENGTH LOST — the OLD `closedLogExtract_emptyTag_false` (with its `Poseidon2SpongeCR`
hypothesis) still follows; the port only DROPPED an assumption. -/
example {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ}
    (_hCR : Poseidon2SpongeCR hash)
    {pc : PublishedCommit} {pubLogPre pubLogPost : ℤ} {pre post : RecChainedState}
    (hdec : StateDecodeLog
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      LH pc pubLogPre pubLogPost pre post)
    (hext : ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      LH hash Rfix 15) : False :=
  Dregg2.Circuit.ClosureReadoutsRealizable.closedLogExtract_emptyTag_false hdec hext

/-- ⚙ NO STRENGTH LOST — the OLD `ClosedLogExtract` statement is still derivable from the ported
bundle (the campaign's standing both-directions bar; the forward half lives in `ClosureAll` as
`closedLogExtract_no_strength_lost`, this is its independent restatement here). -/
example (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ) (R : Registry) (e : EffectIdx)
    (hext : ClosedLogExtract S LH hash R e) :
    Poseidon2SpongeCR hash →
    ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
      (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
      (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState),
      Dregg2.Circuit.DescriptorIR2.Satisfied2 hash (R e) minit mfin maddrs t →
      StateDecodeLog S LH pc pubLogPre pubLogPost pre post →
      kstepAll e pre post :=
  Dregg2.Circuit.ClosureAll.closedLogExtract_no_strength_lost S LH hash R e hext

/-! ## §4 — the STRENGTHENED refutations, typed out.

`example : ⟨the intended CR-free type⟩ := @original` — kernel defeq. If a later edit re-introduces
a `Poseidon2SpongeCR` hypothesis onto either refutation (the exact regression the port removes),
these go RED. -/

/-- ⚙ PORT CHECK — the dead-slot refutation carries NO sponge-CR hypothesis. -/
example : ∀ {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ}
    {pc : PublishedCommit} {pubLogPre pubLogPost : ℤ} {pre post : RecChainedState},
    StateDecodeLog (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      LH pc pubLogPre pubLogPost pre post →
    ClosedLogExtract (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      LH hash Rfix 15 →
    False :=
  @Dregg2.Circuit.ClosureReadoutsRealizable.closedLogExtract_emptyTag_false

/-! ## §5 — axiom hygiene. -/

#assert_axioms closedLogExtract_shape
#assert_axioms Dregg2.Circuit.ClosureAll.closedLogExtract_no_strength_lost
#assert_axioms Dregg2.Circuit.ClosureAll.closedLogExtract_converse_costs_the_floor
#assert_axioms Dregg2.Circuit.ClosureReadoutsRealizable.closedLogExtract_emptyTag_false
#assert_axioms Dregg2.Circuit.ClosureReadoutsRealizable.closureReadouts_uninstantiable

end Dregg2.Circuit.ClosedLogExtractPortCheck
