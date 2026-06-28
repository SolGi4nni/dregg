/-
# Dregg2.Deos.CapacityCarrier — the capacity manifest is FORCED on the BOUND rotated leg.

This is **PIECE 1 of the VK epoch** (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6):
the *carrier* rung. `ConstraintBinding.lean` (the soundness CORE) proved omission is caught
*for a verifier that HOLDS the committed manifest opening* — the cap-membership posture, where
the caller re-derives the manifest from trusted state. This module upgrades that to a **pure
light client** (commitments only): the manifest a light client checks is the one bound into the
~124-bit wide commit via the **already-deployed rotated caveat carrier**.

## What the carrier already is (verified against HEAD)

The rotated caveat region — `RotCaveatManifest` (29 felts) chained by `caveatCommit` to the
published caveat-commit PI — is **in the deployed AIR** of every R=24 cohort descriptor
(`circuit/descriptors/rotation-v3-staged-registry.tsv`: `transferVmDescriptor2R24` carries the
manifest at cols 287.. chained by poseidon lookups to col 328, pinned `pi_index 45`). The
binding keystone `EffectVmEmitRotationCaveat.caveatCommit_binds` proves: equal caveat commits
force equal manifests, under the ONE `Poseidon2SpongeCR` floor. So a light client that binds the
caveat-commit PI (part of the wide commit) witnesses the **exact** manifest — it cannot be fed a
different (omitting) one off-AIR.

## The gap this closes

The deployed `sdk::verify_full_turn_bound_with_caveat_coverage` runs coverage against the *full-v1*
PI slot-caveat manifest (the `>= pi::BASE_COUNT` leg), which is NOT the leg a pure light client
binds. The capacity tags (17/18/19) are projected only onto that unbound leg. Porting the manifest
onto the **bound rotated carrier** (the Rust `slot_caveats_to_rotated_manifest` +
`verify_rotated_caveat_coverage` staged this pass) means the coverage check runs against the leg
the wide commit forces. This module is the Lean rung for *that*: **omission on the bound leg is
impossible** (the published manifest IS the committed one), and composed with the declaration-side
core it gives a pure-light-client omission tooth.

## NOT VK-affecting — the honest finding

The carrier binding (`caveatCommit` → PI) is already in the deployed VK; projecting capacity tags
onto the existing manifest columns is **data, not new constraint polynomials**. So this carrier
rung needs no VK change. The genuinely-VK-affecting remainder (the in-AIR weld of the capacity
gate's slot reads to the rotated state blocks, and the in-AIR coverage-forcing from the
`B_AUTHORITY_DIGEST` r23 limb) is the named tail in `VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypotheses are `Poseidon2SpongeCR` (the carrier's
collision-resistance floor — the SAME one `caveatCommit_binds` carries) and `DeclCommitBinds` (the
declaration-side floor inherited from `ConstraintBinding`). Never an axiom; no core edit.
-/
import Dregg2.Deos.ConstraintBinding
import Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat

namespace Dregg2.Deos.CapacityCarrier

open Dregg2.Deos.ConstraintBinding
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Substrate.Heap (refSponge)

set_option autoImplicit false

/-! ## §1 — the bridge: a rotated carrier manifest projects to a `ConstraintBinding.Manifest`.

The rotated wire entry is `RotCaveatEntry [typeTag, domainTag, key, p0..p3]` (`ℤ` fields). The
abstract coverage manifest is a `List ConstraintBinding.Entry { tag : Nat, satisfied : Bool }`.
The projection reads each entry's type tag (`toNat`) and its off-AIR gate verdict (`gate`), the
SAME verdict `verify_slot_caveat_manifest` computes. The four fixed slots map positionally; the
all-zero "no caveat" entries become tag-0 entries that cannot cover any capacity tag (17/18/19). -/

/-- One rotated entry → one abstract coverage entry: the wire type tag and the verifier's gate
verdict. `gate` is the off-AIR re-evaluation (the §6 `SettleGate`/`DischargeGate`/`VaultDepositGate`),
exactly the `satisfied` bit `ConstraintBinding.Entry` carries. -/
def toEntry (gate : RotCaveatEntry → Bool) (e : RotCaveatEntry) : Entry :=
  ⟨e.typeTag.toNat, gate e⟩

/-- The rotated carrier manifest → the abstract coverage manifest (the four positional entries). -/
def toConstraintManifest (gate : RotCaveatEntry → Bool) (m : RotCaveatManifest) : Manifest :=
  [toEntry gate m.e0, toEntry gate m.e1, toEntry gate m.e2, toEntry gate m.e3]

/-! ## §2 — THE CARRIER BINDING: the published manifest IS the committed one.

A pure light client binds the caveat-commit PI (part of the wide commit). By `caveatCommit_binds`,
any manifest a prover publishes that matches that commit equals the committed manifest — so the
abstract coverage manifest the light client checks is FORCED, not prover-substitutable. -/

/-- **THE CARRIER FORCING.** Two rotated manifests with the SAME caveat commit project to the SAME
abstract coverage manifest (for any fixed gate). A forger cannot publish an alternate manifest on
the bound leg — `caveatCommit_binds` collapses it to the committed one. -/
theorem carrier_manifest_forced (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (gate : RotCaveatEntry → Bool) {mBound mPub : RotCaveatManifest}
    (hcommit : caveatCommit hash mPub = caveatCommit hash mBound) :
    toConstraintManifest gate mPub = toConstraintManifest gate mBound := by
  rw [caveatCommit_binds hash hCR hcommit]

/-- **COVERAGE IS FORCED.** If the committed (bound) manifest covers the required set, then ANY
manifest a prover publishes matching the bound caveat commit covers it too — coverage rides the
commit, not the prover's choice. -/
theorem carrier_coverage_forced (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (gate : RotCaveatEntry → Bool) (required : List Tag) {mBound mPub : RotCaveatManifest}
    (hcommit : caveatCommit hash mPub = caveatCommit hash mBound)
    (hcov : verifierAccepts required (toConstraintManifest gate mBound)) :
    verifierAccepts required (toConstraintManifest gate mPub) := by
  rw [carrier_manifest_forced hash hCR gate hcommit]; exact hcov

/-- **THE CARRIER OMISSION TOOTH** — the sharp form. There is NO manifest a forger can publish that
BOTH matches the committed caveat commit of an honest covering manifest AND omits a required tag:
matching the commit forces equality with the bound manifest (which covers `t`), contradicting the
omission. A pure light client binding the caveat-commit PI catches the dropped capacity entry. -/
theorem carrier_omission_impossible (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (gate : RotCaveatEntry → Bool) (t : Tag) {mBound mPub : RotCaveatManifest}
    (hcommit : caveatCommit hash mPub = caveatCommit hash mBound)
    (hcov : covers (toConstraintManifest gate mBound) t)
    (homit : ∀ e ∈ toConstraintManifest gate mPub, e.tag ≠ t) :
    False := by
  rw [carrier_manifest_forced hash hCR gate hcommit] at homit
  obtain ⟨e, he, het, _⟩ := hcov
  exact homit e he het

/-! ## §3 — THE PURE-LIGHT-CLIENT SOUNDNESS CORE: both bindings composed.

A pure light client binds, in the ONE wide commit, BOTH the caveat commit (forces the published
manifest = the committed manifest, §2) AND the declaration commit (the `B_AUTHORITY_DIGEST` r23
limb — forces the required tags = the committed declaration's, the `ConstraintBinding.DeclCommitBinds`
floor). Composed, omission is caught WITHOUT the caller holding any opening: the cap-membership
posture is discharged by the carrier. -/

/-- **THE CARRIER KEYSTONE.** A turn on a capacity cell whose committed declaration requires tag
`t` is REJECTED if the prover publishes (on the bound rotated leg) a manifest omitting `t` — even
under an alternate presented declaration — because (a) the published manifest is forced equal to
the committed one by the caveat-commit binding, and (b) the presented declaration's required tags
are forced equal to the committed one's by `DeclCommitBinds`. This is `omission_caught_under_binding`
lifted from "verifier holds the opening" to "the wide commit forces it." -/
theorem carrier_omission_caught_pure_lightclient (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (gate : RotCaveatEntry → Bool) {Decl C : Type}
    (declCommit : Decl → C) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds declCommit requiredTags)
    (committedDecl presentedDecl : Decl)
    (hdcommit : declCommit presentedDecl = declCommit committedDecl)
    (t : Tag) (hreq : t ∈ requiredTags committedDecl)
    {mBound mPub : RotCaveatManifest}
    (hccommit : caveatCommit hash mPub = caveatCommit hash mBound)
    (homit : ∀ e ∈ toConstraintManifest gate mPub, e.tag ≠ t) :
    ¬ verifierAccepts (requiredTags presentedDecl) (toConstraintManifest gate mPub) := by
  rw [carrier_manifest_forced hash hCR gate hccommit] at homit ⊢
  exact omission_caught_under_binding declCommit requiredTags hbinds committedDecl presentedDecl
    hdcommit t hreq (toConstraintManifest gate mBound) homit

/-! ## §4 — the concrete capacity instances (tags 17 / 18 / 19). -/

/-- The rotated carrier entry the producer (`slot_caveats_to_rotated_manifest`) emits for a
sealed-escrow gate: tag 17, registers domain (0), the leg-A status slot as key. -/
def escrowEntry : RotCaveatEntry := ⟨(tagSettleEscrow : ℤ), 0, 0, 0, 0, 0, 0⟩

/-- A capacity carrier manifest declaring the sealed-escrow gate in slot 0. -/
def capacityManifest : RotCaveatManifest := ⟨1, escrowEntry, zeroEntry, zeroEntry, zeroEntry⟩

/-- The empty (omitting) carrier manifest — the forger's `count = 0` dodge. -/
def emptyManifest : RotCaveatManifest := ⟨0, zeroEntry, zeroEntry, zeroEntry, zeroEntry⟩

/-- **THE ESCROW CARRIER TOOTH.** The escrow omission cannot survive on the bound leg: a forger
publishing the empty manifest moves the caveat commit away from the honest covering manifest's, so
a light client binding PI 45 rejects it. The concrete tag-17 instance of `carrier_omission_impossible`. -/
theorem escrow_carrier_omission_impossible (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (gate : RotCaveatEntry → Bool) {mBound mPub : RotCaveatManifest}
    (hcommit : caveatCommit hash mPub = caveatCommit hash mBound)
    (hcov : covers (toConstraintManifest gate mBound) tagSettleEscrow)
    (homit : ∀ e ∈ toConstraintManifest gate mPub, e.tag ≠ tagSettleEscrow) :
    False :=
  carrier_omission_impossible hash hCR gate tagSettleEscrow hcommit hcov homit

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the carrier BITES, both polarities. -/

section Witnesses

/-- The all-pass gate (the off-AIR re-eval succeeds) — for the coverage polarity guards. -/
private def passGate : RotCaveatEntry → Bool := fun _ => true

-- The capacity manifest COVERS tag 17 (present + satisfied) once projected.
#guard decide (covers (toConstraintManifest passGate capacityManifest) tagSettleEscrow)
-- The empty (omitting) manifest does NOT cover tag 17 — the omission the coverage gate rejects.
#guard !decide (covers (toConstraintManifest passGate emptyManifest) tagSettleEscrow)
-- verifierAccepts the singleton required-set on the capacity manifest...
#guard decide (verifierAccepts [tagSettleEscrow] (toConstraintManifest passGate capacityManifest))
-- ...and REJECTS it on the omitting empty manifest.
#guard !decide (verifierAccepts [tagSettleEscrow] (toConstraintManifest passGate emptyManifest))

-- THE BINDING BITES: dropping the tag-17 entry MOVES the bound caveat commit (so a pure light
-- client binding PI 45 detects the omission — it cannot match the honest commit). Computed on the
-- reference sponge (deployment = the audited p3 Poseidon2 under the SAME CR floor).
#guard caveatCommit refSponge capacityManifest != caveatCommit refSponge emptyManifest
-- ...and the honest recompute is stable (the positive polarity).
#guard caveatCommit refSponge capacityManifest == caveatCommit refSponge capacityManifest

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  carrier_manifest_forced,
  carrier_coverage_forced,
  carrier_omission_impossible,
  carrier_omission_caught_pure_lightclient,
  escrow_carrier_omission_impossible
]

end Dregg2.Deos.CapacityCarrier
