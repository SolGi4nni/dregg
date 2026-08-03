/-
# Dregg2.Verify.ClosureSurfaceApplicable — the closure keystone AT A CLOSED SURFACE, and the ONE
obstruction that survived the four-parameter deletion.

`ClosureSurface.S_live` carried four parameters — `hCmb`/`hCompress`/`hCompressN`/`hLeaf`, i.e.
`compressInjective cmb`, `compressInjective compress`, `compressNInjective compressN`,
`cellLeafInjective CH` — whose only job was to fill four `CircuitSoundness.CommitSurface` FIELDS.
Those fields were deleted on 2026-08-01 as refuted at deployed BabyBear width; the parameters were
left behind, `_`-prefixed, with the body IGNORING them. So every theorem over `S_live` was
inapplicable at deployed parameters SOLELY because of arguments its own proof term was logically
independent of. They are deleted (2026-08-02), and this file is the check that the deletion bought
something — plus the statement of exactly what it did not buy.

## What it bought (§1-§3)

`S_live` now takes the five primitives and `RestHashIffFrameFin RH`. `S_liveRef` below is a CLOSED
term of `CommitSurface` — no hypothesis, no `variable`, nothing left to discharge — built from
`FinBindsKernel.CH_fin` / `FinFrameHash.RH_fin` / `Freshness.spongeCompress` at the UNBOUNDED
reference sponge, with `restFrame` discharged by
`RestFrameFiniteSupportSuccessor.restHashIffFrameFin_satisfiable`. Over it, `StateDecode` FIRES at a
concrete published boundary (§2), and two of `ClosureSurface`'s three closed rungs are restated with
no refuted predicate anywhere in their types (§3). Before the deletion the same statements could not
be made without also supplying the four refuted predicates, which is precisely what made them say
nothing at deployed parameters.

⚑ These are NAMED theorems, not anonymous `example`s. The discipline that made
`RestFrameFiniteSupportSuccessor` §6's inhabitant anonymous — a declaration mentioning `CommitSurface`
was a `#floor_ratchet` `bundle-user` carrier — lapsed when the bundle's four injectivity fields were
deleted. `CommitSurface` is no longer a floor bundle, so naming these costs no baseline row. (Which
is itself the §4 problem: it costs no row because the instrument cannot see the field that remains.)

## ⚠ What it did NOT buy (§4) — and this is the finding

`S_live`'s surviving argument is `RestHashIffFrameFin RH`, and that is refuted AT DEPLOYED BABYBEAR
WIDTH by pigeonhole: the `denote`-image of `FinKernelState` is infinite, a bounded `RH` lands in ~2³¹
values, and the biconditional's forward direction turns any collision inside the image into a frame
equality those states do not have
(`RestFrameFiniteSupportSuccessor.restHashIffFrameFin_false_babyBear`, written 2026-08-02).
`no_babyBear_commitSurface` states the consequence directly: NO `CommitSurface` has a BabyBear-bounded
rest-hash, so no `S_live` does, so §3's rungs remain unavailable to a deployed light client. One
obligation instead of five, at the reference pole instead of nowhere — but not deployed.

⚑ AND NOTHING GATES IT. `#floor_ratchet` derives its refuted-floor set from
`FloorCensus.injShape`/`injShapeAnd` — the telescoped body must be an fvar equation or a conjunction
of them — and `RestHashIffFrameFin`'s body is an `∀`-`Iff` over an 18-fold conjunction, so it is not a
candidate however many refutations the tree holds, and it is not a named sentinel. That is why
`CommitSurface` could be dropped from `FloorRatchet.sentinelBundles` on 2026-08-01 on the strength of
its one remaining field being "satisfiable": true at the reference sponge, false at deployed width,
and the instrument cannot tell the difference. The refutation is a DOCUMENTED wound, not a DETECTED
one, and saying so is half the point of this file.

No `sorry`, no `axiom`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.ClosureSurface
import Dregg2.Verify.RestFrameFiniteSupportSuccessor

namespace Dregg2.Verify.ClosureSurfaceApplicable

open Dregg2.Exec (CellId AssetId Value RecordKernelState RecChainedState Turn)
open Dregg2.Circuit.CircuitSoundness (CommitSurface StateDecode PublishedCommit)
open Dregg2.Circuit.CircuitSoundnessAssembled (kstepAll)
open Dregg2.Circuit.ClosureSurface (S_live closedBridge_of_step)
open Dregg2.Circuit.RestFrameFin (RestHashIffFrameFin)
open Dregg2.Circuit.FinKernelState (denote finInit)
open Dregg2.Circuit.FinFrameHash (RH_fin)
open Dregg2.Circuit.FinBindsKernel (CH_fin finInit_accountsWF)
open Dregg2.Circuit.Freshness (spongeCompress)
open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Verify.RestFrameFiniteSupportSuccessor
  (restHashIffFrameFin_satisfiable restHashIffFrameFin_false_babyBear)
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Circuit.ActionDispatch (fullActionStep actionTag)

set_option autoImplicit false

/-! ## §1 — ★ `S_liveRef`: a CLOSED `S_live`. -/

/-- ★ **A CLOSED `S_live` SURFACE.** Every argument is a closed term: the five commitment primitives
at the reference sponge, and `restHashIffFrameFin_satisfiable` for the one remaining obligation.
Nothing is carried, so this is a VALUE and not a schema — which is exactly what the four deleted
parameters used to prevent at any width where they were refuted.

⚠ REFERENCE POLE, NOT DEPLOYED. `Reference.refSponge` is `Encodable.encode`: genuinely injective and
genuinely NOT BabyBear-bounded. §4 is the price of that word. -/
@[reducible] noncomputable def S_liveRef : CommitSurface :=
  S_live (CH_fin Reference.refSponge) (RH_fin Reference.refSponge)
    (spongeCompress Reference.refSponge) (spongeCompress Reference.refSponge)
    Reference.refSponge restHashIffFrameFin_satisfiable

/-- The closed surface's root IS `recStateCommit` at its own primitives — no seam, definitionally.
This is `ClosureSurface`'s whole claim, now readable at a value rather than under four binders. -/
theorem S_liveRef_commit (k : RecordKernelState) (t : Turn) :
    S_liveRef.commit k t
      = Dregg2.Circuit.StateCommit.recStateCommit (CH_fin Reference.refSponge)
          (RH_fin Reference.refSponge) (spongeCompress Reference.refSponge)
          (spongeCompress Reference.refSponge) Reference.refSponge k t := rfl

/-! ## §2 — the decode FIRES over it (so §3's `hdec` is not an over-ask). -/

/-- **`StateDecode S_liveRef` FIRES at a concrete published boundary.** `denote finInit` publishing
its own root at both ends, `AccountsWF` from `finInit_accountsWF`. Closed, no hypothesis. Without
this, §3 would be three implications with an unreachable antecedent — the shape this campaign has
already shipped three times. -/
theorem stateDecode_at_S_liveRef (t : Turn) :
    StateDecode S_liveRef
      ⟨S_liveRef.commit (denote finInit) t, S_liveRef.commit (denote finInit) t, t⟩
      ⟨denote finInit, []⟩ ⟨denote finInit, []⟩ :=
  ⟨rfl, rfl, finInit_accountsWF, finInit_accountsWF⟩

/-! ## §3 — the closure rungs, AT THE CLOSED SURFACE, with no refuted predicate left. -/

/-- **The generic decode-bridge, at the closed surface.** `closedBridge_of_step` never carried a
floor of its own; what is new is that its `S` can now be a closed VALUE rather than a schema over
four refuted predicates. -/
theorem closedBridge_at_S_liveRef {pc : PublishedCommit} {pre post : RecChainedState}
    (fa : FullActionA) (hdec : StateDecode S_liveRef pc pre post)
    (hstep : fullActionStep pre fa post) :
    kstepAll (actionTag fa) pre post :=
  closedBridge_of_step fa hdec rfl hstep

/-- ★ **RUNG 1 (transfer, tag 0) AT THE CLOSED SURFACE.** Every surviving hypothesis is a CIRCUIT
fact — the rotated table side, the `Satisfied2` witness, the per-effect `rotatedEncodes`, and the
decode — and none of them is a predicate this tree refutes. Before 2026-08-02 the same statement
additionally demanded `compressInjective cmb`, `compressInjective compress`,
`compressNInjective compressN` and `cellLeafInjective CH`, all four refuted at deployed BabyBear
width, and all four ignored by the proof term. -/
theorem transfer_rung_at_S_liveRef
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : Dregg2.Circuit.DescriptorIR2.VmTrace} {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) (pc : PublishedCommit)
    (hdec : StateDecode S_liveRef pc pre post)
    (henc : Dregg2.Circuit.RotatedKernelRefinement.rotatedEncodes
      hash minit mfin maddrs t pre post tr a) :
    kstepAll 0 pre post :=
  Dregg2.Circuit.ClosureSurface.transfer_descriptorRefines_closed
    hash hside hsat pre post tr a pc hdec henc

/-- ★ **RUNG 3 (revoke, tag 2) AT THE CLOSED SURFACE.** Same reading: the cap-family
`RevokeCapsTreeEncodes` is the circuit's own residual, and nothing refuted survives beside it.
(Rung 2, `cellSeal`, is deliberately NOT restated here: it genuinely binds
`compressNInjective compressN` for the cellSeal `FieldElem` sponge — a REAL floor its proof reads,
not one of the four this pass deleted — so putting it in this file would say something false about
what the deletion achieved.) -/
theorem revoke_rung_at_S_liveRef
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (pre post : RecChainedState) (holder tt : CellId) (pc : PublishedCommit)
    (hdec : StateDecode S_liveRef pc pre post)
    (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
      Scap pre post holder tt) :
    kstepAll 2 pre post :=
  Dregg2.Circuit.ClosureSurface.revoke_descriptorRefines_closed
    Scap pre post holder tt pc hdec henc

/-! ## §4 — ⚠ THE OBSTRUCTION THAT SURVIVED, and the gate that cannot see it. -/

/-- **⚠ NO `CommitSurface` HAS A BABYBEAR-BOUNDED REST-HASH.** The bundle's one surviving field is
`restFrame : RestHashIffFrameFin RH`, refuted at deployed width by pigeonhole. So `S_liveRef` is a
REFERENCE-pole object by necessity rather than by choice, and §3's rungs remain unavailable to a
deployed light client: the four deleted parameters were not the last thing between them and the
running system.

⚑ Nothing gates this. `RestHashIffFrameFin` is `Iff`-headed, so it can never enter `#floor_ratchet`'s
DERIVED refuted-floor set (`FloorCensus.injShape`/`injShapeAnd` both require an fvar equation), and it
is not a named sentinel. Its ~120 binder sites carry ZERO baseline rows and will keep carrying zero
however many refutations are written. -/
theorem no_babyBear_commitSurface (RH : RecordKernelState → ℤ)
    (hb : ∀ k, 0 ≤ RH k ∧ RH k < (2013265921 : ℤ)) :
    ¬ ∃ S : CommitSurface, S.RH = RH := by
  rintro ⟨S, rfl⟩
  exact restHashIffFrameFin_false_babyBear S.RH hb S.restFrame

/-- **The two poles, side by side, so neither reading can be taken alone.** A `CommitSurface` EXISTS
(the reference pole, §1) and NONE exists over a BabyBear-bounded rest-hash (§4). The first is what
the deletion bought; the second is what it did not. -/
theorem surface_exists_but_not_at_babyBear :
    (∃ S : CommitSurface, S.RH = RH_fin Reference.refSponge)
      ∧ ∀ RH : RecordKernelState → ℤ, (∀ k, 0 ≤ RH k ∧ RH k < (2013265921 : ℤ)) →
          ¬ ∃ S : CommitSurface, S.RH = RH :=
  ⟨⟨S_liveRef, rfl⟩, no_babyBear_commitSurface⟩

#assert_axioms S_liveRef
#assert_axioms S_liveRef_commit
#assert_axioms stateDecode_at_S_liveRef
#assert_axioms closedBridge_at_S_liveRef
#assert_axioms transfer_rung_at_S_liveRef
#assert_axioms revoke_rung_at_S_liveRef
#assert_axioms no_babyBear_commitSurface
#assert_axioms surface_exists_but_not_at_babyBear

end Dregg2.Verify.ClosureSurfaceApplicable
