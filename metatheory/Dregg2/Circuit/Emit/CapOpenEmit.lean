/-
# Dregg2.Circuit.Emit.CapOpenEmit — the LIVE cap-membership open, emitted into a real descriptor.

`DeployedCapOpen.lean` PROVES the in-circuit cap-tree membership-open as a set of generic
`Lookup` + gate `VmConstraint2`s (`leafLookup` + 16 `nodeLookup` + `dirBoolGate`/`rootPinGate`/
`targetBindGate`/`transferFacetGate`/`facetHiGate`/`authTagGate`) over an abstract `CapOpenCols`
column layout, with the keystone `capOpen_sound`: a `Satisfied` row yields `MembersAt cap_root leaf ∧
leaf.target = src ∧ confersTransferLeaf vkOfTag .signature leaf` (the FAITHFUL two-axis tier × facet
gate). But nothing LAID THOSE CONSTRAINTS DOWN into a live `EffectVmDescriptor2`: the proof existed,
disconnected from the wire.

This file welds it. It (a) pins `CapOpenCols` to a concrete appendix of trace columns past the
rotated R=24 width (`capOpenCols`, §1), (b) assembles the proven constraints into the effect-GENERAL
constraint list `capOpenConstraintsEff n` (§5.F) — `leafLookup` + the 16 `nodeLookup`s as `.lookup`,
the genuine SUBMASK facet gate (`effBitGateFor`/`maskBitBoolGate`/`maskReconGate`/`selectedBitGate`)
+ the binding gates as `.base (.gate …)` — and (c) appends them to each effect's rotated base
(`transferCapOpenEffV3`/`attenuateCapOpenEffV3` + the 6 fan-out, §5.F), widening the trace by
`CAP_OPEN_SPAN` and welding the `capRoot`/`src` columns to the committed rotated before-block cap-root
and the turn's src.

The keystones (§5.K, `transferCapOpenEffV3_authorizes`/`attenuateCapOpenEffV3_authorizes`): a
`Satisfied2` witness of the LIVE membership descriptor — against a sound chip table — REBUILDS
`DeployedCapOpen.SatisfiedEff`, hence `capOpenEff_authorizes`, hence (via
`deployedCapOpen_implies_authorizedEffB` + `authorizedFacetB = authorizedFacetEffB … EFFECT_TRANSFER`)
the kernel's FAITHFUL `authorizedFacetB`. The `&[]` cap-path placeholder is GONE: the depth-16 fold the
descriptor carries IS the proof. The genuine submask facet (a BROAD honest cap PASSES) + the DECODED
tier are what the deployed prover routes AND what the apex authority leg refines — wire and proof are
ONE. (The Signature-pinned `capOpenAttenuateV3`/`transferCapOpenV3` are DELETED, §3.)

## Law #1

NO new constraint SEMANTICS live here: every constraint is a `DeployedCapOpen` `Lookup`/gate that the
Rust `descriptor_ir2.rs` interpreter ALREADY realizes generically (chip lookups on the P2 bus, base
gates on the transition builder). This file is pure PLUMBING — a column layout + a constraint list +
the bridge proof. The Rust registry twin (`V3_STAGED_REGISTRY_TSV`) carries the byte-identical wire
string emitted by `emitVmJson2`.

## The chip-rate seam (CLOSED — decision #1, `SchemeRealizedByChip` DISCHARGED)

`leafLookup` is a single chip absorb of the 7 leaf fields (arity 7); each `nodeLookup` a single chip
absorb of `[FACT_MARK, l, r]` (arity 3). The DEPLOYED cap primitives are NOW exactly these single chip
absorbs: the cap-tree is re-committed to `cap_root.rs::cap_chip_absorb` (mirrored as
`DeployedCapTree`'s one `chipAbsorb` carrier), so `capLeafDigest S = S.chipAbsorb ∘ leafFields` and
`nodeOf S l r = S.chipAbsorb [FACT_MARK, l, r]`. The chip's `sponge (leafFields)` IS `capLeafDigest S
leaf` and `sponge [FACT_MARK, l, r]` IS `nodeOf S l r` when `sponge := S.chipAbsorb`.

`DeployedCapOpen`'s named bridge `SchemeRealizedByChip hash S` is therefore DISCHARGED by
`chipAbsorb_realizes` (both equations hold by `rfl`), and the two keystone theorems below specialize
`hash := S.chipAbsorb` and supply the realization internally — it is no longer a carried hypothesis.
The prior revision's rate-4 `hash_many` leaf + capacity-tagged `hash_fact` node (the source of the
gap) are GONE; one in-circuit cap hash everywhere.

## Mask convention (the fork CLOSED — the faithful two-axis gate)

The earlier revision's `writeMaskGate` pinned the abstract `Auth` rights mask `mask_lo == 3` — a
DIFFERENT convention from the deployed `cap_root.rs::CapLeaf.mask_lo` (the low-16 of a `cell/facet.rs`
`EffectMask` effect-KIND bitmap). The cutover RESOLVES that fork onto the deployed convention: the
authority leg now emits the FAITHFUL two-axis gates — `transferFacetGate` (`mask_lo == EFFECT_TRANSFER`)
+ `facetHiGate` (`mask_hi == 0`) decode the `EffectMask` facet and check the `EFFECT_TRANSFER` bit, and
`authTagGate` (`auth_tag == 1`) decodes the `AuthRequired` tier (`Signature`). A `Satisfied` row thus
discharges `confersTransferLeaf` (facet permits the effect-kind AND tier is satisfied), which the
bridge turns into the deployed `authorizedFacetB`. Residual: the tier is pinned to `Signature` here
rather than read off the leaf's committed `auth_tag` generically (FacetAuthority §10 named residual).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters only as the named
`CapHashScheme.chipAbsorb`/`chipCR` floor (and the chip-soundness `ChipTableSound`), inherited
unchanged from `DeployedCapOpen`. No sorry/native_decide/:= True.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.CapOpenEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint EFFECT_VM_WIDTH)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily TableId Lookup VmConstraint2 EffectVmDescriptor2 ChipTableSound Satisfied2)
open Dregg2.Circuit.DeployedCapOpen
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (capLeafDigest MembersAt confersTransferLeaf DeployedFaithful
   deployedCapOpen_implies_authorizedB)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (attenuateV3 APPENDIX_SPAN B_CAP_ROOT v3Of v3OfFrozen withSelectorGate withSelectorGate_satisfied2)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority (AuthProvided FacetCaps authorizedFacetB)

set_option autoImplicit false

/-! ## §1 — the concrete column layout: the cap-open appendix past the rotated R=24 width.

The rotated attenuate trace is `EFFECT_VM_WIDTH + APPENDIX_SPAN = 316` columns wide. The cap-open
appendix starts at `CAP_OPEN_BASE` and carries, in order: 7 leaf-field columns, 1 leaf-digest
column, then for each of `DEPTH = 16` levels a `(sib, dir, node)` triple, then the `capRoot` and
`src` columns. Total `CAP_OPEN_SPAN = 7 + 1 + 16·3 + 2 = 58`. -/

/-- The base column of the cap-open appendix (the first column past the rotated R=24 width). -/
def CAP_OPEN_BASE : Nat := EFFECT_VM_WIDTH + APPENDIX_SPAN

/-- The cap-open appendix width: 7 leaf + 1 digest + 16·(sib,dir,node) + capRoot + src + effBit +
`MASK_BITS` mask-bit columns. The trailing `effBit` column carries the turn's ACTUAL effect-kind bit;
the `MASK_BITS` bit columns (residual (a) — GENUINE MEMBERSHIP) carry the 24-bit decomposition of the
leaf's low mask limb, against which the genuine SUBMASK gate `facetEffGate` (`maskBitBoolGate` +
`maskReconGate` + `selectedBitGate`) checks `(effBit &&& mask_lo) = effBit` — NOT the over-strict
equality `mask_lo == effBit`. The bit columns are appended at the END of the block to localize the shift. -/
def CAP_OPEN_SPAN : Nat := 7 + 1 + DEPTH * 3 + 3 + MASK_BITS

/-- The concrete cap-open column layout, pinned to the appendix. Leaf fields 0..6 at
`CAP_OPEN_BASE..+6`; leaf digest at `+7`; level `lvl`'s sibling/direction/node at `+8+3·lvl`,
`+9+3·lvl`, `+10+3·lvl`; cap_root at `+56`; src at `+57`; effBit at `+58`; the 24 mask-bit columns at
`+59..+82` (`bit i = CAP_OPEN_BASE + 59 + i`). -/
def capOpenCols : CapOpenCols :=
  { leaf       := fun i => CAP_OPEN_BASE + i.val
  , leafDigest := CAP_OPEN_BASE + 7
  , sib        := fun lvl => CAP_OPEN_BASE + 8 + 3 * lvl
  , dir        := fun lvl => CAP_OPEN_BASE + 9 + 3 * lvl
  , node       := fun lvl => CAP_OPEN_BASE + 10 + 3 * lvl
  , capRoot    := CAP_OPEN_BASE + 8 + 3 * DEPTH       -- = CAP_OPEN_BASE + 56
  , src        := CAP_OPEN_BASE + 8 + 3 * DEPTH + 1   -- = CAP_OPEN_BASE + 57
  , effBit     := CAP_OPEN_BASE + 8 + 3 * DEPTH + 2   -- = CAP_OPEN_BASE + 58
  , bit        := fun i => CAP_OPEN_BASE + 8 + 3 * DEPTH + 3 + i } -- = CAP_OPEN_BASE + 59 + i

/-- The cap-open appendix width is 83 (the 59-col base + 24 mask-bit columns). -/
theorem cap_open_span : CAP_OPEN_SPAN = 91 := by decide

/-! ## §2 — the constraint list: the proven `DeployedCapOpen` constraints, assembled.

`leafLookup` + the 16 `nodeLookup`s ride `.lookup` (the chip-bus lookups the Rust interpreter
realizes); the four gate equations ride `.base (.gate …)` (the transition-builder gates). The list
is EXACTLY the constraints `DeployedCapOpen.Satisfied` quantifies over. -/

/-- The 16 per-level node-absorb chip lookups (`nodeLookup capOpenCols 0..15`). -/
def nodeLookups : List VmConstraint2 :=
  (List.range DEPTH).map (fun lvl => .lookup (nodeLookup capOpenCols lvl))

/-- The 16 per-level direction-boolean gates (`dirBoolGate capOpenCols 0..15`). -/
def dirBoolGates : List VmConstraint2 :=
  (List.range DEPTH).map (fun lvl => .base (.gate (dirBoolGate capOpenCols lvl)))

/-- The `MASK_BITS` per-bit boolean gates for the `mask_lo` decomposition (`maskBitBoolGate
capOpenCols 0..23`) — each `mask_lo` bit column is `0` or `1`. -/
def maskBitGates : List VmConstraint2 :=
  (List.range MASK_BITS).map (fun i => .base (.gate (maskBitBoolGate capOpenCols i)))

/-! ## §3 — (DELETED) the Signature-pinned `capOpenAttenuateV3`/`transferCapOpenV3` descriptors.

These were the over-strict (`mask_lo == effBit` equality + constant facet/tier pins) cap-open
descriptors, kept "for the apex/refinement proofs only". The apex authority leg now refines the LIVE
`…CapOpenEffV3` membership descriptors (`transferCapOpenEffV3_authorizes`, §5.K below), which is also
what the deployed prover routes — so nothing is proven about an unwired descriptor and both pinned
descriptors + their full lemma cohort (`capOpenConstraints`, `capOpenAttenuateV3*`,
`transferCapOpenV3*`) are DELETED (Stage D). The shared appendix helpers `nodeLookups`/`dirBoolGates`/
`maskBitGates` survive — the effect-general `capOpenConstraintsEff n` (§5.F) reuses them. -/

/-- The rotated TRANSFER cohort descriptor (`v3OfFrozen` of the transfer v1 face — transfer-via-cap is a
VALUE effect, so the authority-frame freeze welds apply). Same width invariant as `attenuateV3`
(`EFFECT_VM_WIDTH + APPENDIX_SPAN`), so the cap-open appendix at `CAP_OPEN_BASE` applies. It is the base of
the LIVE `transferCapOpenEffV3` (§5.F); freezing it forces AFTER-r23 == BEFORE-r23 (+ lifecycle) for the
transfer-via-cap leg too, matching `RotatedKernelRefinement.transferV3` (`v3OfFrozen` of the same face). -/
def transferV3 : EffectVmDescriptor2 :=
  v3OfFrozen Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor

/-! ## §5.F — THE FAN-OUT: the effect-GENERAL cap-open appendix + per-effect descriptors.

`capOpenConstraints` pins the facet to `EFFECT_TRANSFER` (the `effBitGate`/`transferFacetGate`/`authTagGate`
constants). The fan-out to the OTHER cap-authorized effects (delegate, introduce, grantCap, revoke,
refreshDelegation, …) reuses the WHOLE appendix EXCEPT those constant pins: `capOpenConstraintsEff n` swaps
`effBitGate` for `effBitGateFor (1 <<< n)` (THIS effect's bit) and DROPS `transferFacetGate`/`authTagGate`
(the general `facetEffGate` carries the facet axis; the tier rides the decoded `auth_tag`). A `Satisfied2`
witness of `<effect>V3 ++ capOpenConstraintsEff n` rebuilds `DeployedCapOpen.SatisfiedEff … n`, hence
`capOpenEff_authorizes` into `authorizedFacetEffB … (1 <<< n)` — the cap must permit THAT effect-kind. -/

open Dregg2.Circuit.DeployedCapOpen
  (SatisfiedEff MembershipCore effBitGateFor capOpenEff_authorizes satisfiedEff_rejects_wrong_facet)
open Dregg2.Exec.FacetAuthority (authorizedFacetEffB)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (DeployedFaithfulEff tierOfTag)

/-- **`capOpenConstraintsEff n`** — the effect-GENERAL cap-open constraint list for effect-kind bit
`1 <<< n`: the leaf lookup, the 16 node lookups, the 16 dir gates, the root pin, the target binding, the
high-limb pin, the committed effect-bit pin `effBitGateFor … (1 <<< n)`, and the general facet gate. The
transfer constant pins (`transferFacetGate`/`authTagGate`) are GONE — the facet is bound to the committed
effect-bit column, the tier to the decoded `auth_tag`. Count: 1 + 16 + 16 + 5 = 38. -/
def capOpenConstraintsEff (n : Nat) : List VmConstraint2 :=
  .lookup (leafLookup capOpenCols)
  :: nodeLookups
  ++ dirBoolGates
  ++ maskBitGates
  ++ [ .base (.gate (rootPinGate capOpenCols))
     , .base (.gate (targetBindGate capOpenCols))
     , .base (.gate (effBitGateFor capOpenCols ((1 <<< n : Nat) : ℤ)))
     , .base (.gate (maskReconGate capOpenCols))
     , .base (.gate (selectedBitGate capOpenCols n)) ]

/-- The effect-general constraint count is 1 leaf + 16 node + 16 dir + 32 mask-bit + 5 binding gates
(rootPin, targetBind, effBitGateFor, maskRecon, selectedBit) = 70. (NO `facetHiGate` — the FULL mask is
decomposed, so a broad `EFFECT_ALL` cap with `mask_hi ≠ 0` is admitted.) -/
theorem capOpenConstraintsEff_length (n : Nat) : (capOpenConstraintsEff n).length = 70 := by
  simp [capOpenConstraintsEff, nodeLookups, dirBoolGates, maskBitGates, DEPTH, MASK_BITS]

/-- **`effCapOpenV3 base name n`** — the GENERIC per-effect cap-open descriptor: an effect's rotated base
descriptor `base` (a `v3Of …` member, same `EFFECT_VM_WIDTH + APPENDIX_SPAN` width) widened by the cap-open
appendix at `CAP_OPEN_BASE`, carrying `capOpenConstraintsEff n` (THIS effect's bit). Every fan-out effect is
`effCapOpenV3 <effect>V3 "dregg-…-capopen" n`. -/
def effCapOpenV3 (base : EffectVmDescriptor2) (name : String) (n : Nat) : EffectVmDescriptor2 :=
  { base with
    name        := name
    traceWidth  := base.traceWidth + CAP_OPEN_SPAN
    constraints := base.constraints ++ capOpenConstraintsEff n }

/-- Every effect-general cap-open constraint is a constraint of the descriptor. -/
theorem effCapOpenV3_constraints_mem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ capOpenConstraintsEff n) :
    c ∈ (effCapOpenV3 base name n).constraints :=
  List.mem_append_right _ hc

/-- **`effCapOpenV3_satisfiedEff`** — a `Satisfied2` witness of `effCapOpenV3 base name n` rebuilds
`DeployedCapOpen.SatisfiedEff … n` on every row (the appendix constraints are satisfied regardless of the
base — they read no base column). The fan-out analog of `transferCapOpenV3_satisfied`. -/
theorem effCapOpenV3_satisfiedEff (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hsat : Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    SatisfiedEff hash t.tf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) n := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effCapOpenV3_constraints_mem base name n
  refine
    { core := ?_, targetBound := ?_, effBitPinned := ?_
    , maskBitsBool := ?_, maskRecon := ?_, facetEffBound := ?_ }
  · refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
    · have hin : VmConstraint2.lookup (leafLookup capOpenCols) ∈ capOpenConstraintsEff n := by
        simp [capOpenConstraintsEff]
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt] using h
    · intro lvl hlvl
      have hin : VmConstraint2.lookup (nodeLookup capOpenCols lvl) ∈ capOpenConstraintsEff n := by
        refine List.mem_cons_of_mem _ ?_
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
        exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt] using h
    · intro lvl hlvl
      have hin : VmConstraint2.base (.gate (dirBoolGate capOpenCols lvl)) ∈ capOpenConstraintsEff n := by
        refine List.mem_cons_of_mem _ ?_
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
        exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
    · have hin : VmConstraint2.base (.gate (rootPinGate capOpenCols)) ∈ capOpenConstraintsEff n := by
        simp [capOpenConstraintsEff]
      have h := hrow _ (hmem _ hin)
      simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (targetBindGate capOpenCols)) ∈ capOpenConstraintsEff n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (effBitGateFor capOpenCols ((1 <<< n : Nat) : ℤ)))
        ∈ capOpenConstraintsEff n := by simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · intro j hj
    have hin : VmConstraint2.base (.gate (maskBitBoolGate capOpenCols j)) ∈ capOpenConstraintsEff n := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (maskReconGate capOpenCols)) ∈ capOpenConstraintsEff n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · have hin : VmConstraint2.base (.gate (selectedBitGate capOpenCols n)) ∈ capOpenConstraintsEff n := by
      simp [capOpenConstraintsEff]
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **`effCapOpenV3_authorizes` — THE FAN-OUT AUTHORITY LEG (generic, live).** A `Satisfied2` witness of
`effCapOpenV3 base name n` whose opened leaf IS the faithfulness contract's `(actor ⇒ src)` edge discharges
the kernel's GENERAL `authorizedFacetEffB … (1 <<< n)` for the turn — over effect-kind `1 <<< n` (NOT
transfer), under any `provided` satisfying the committed tier. Every fan-out effect's authority leg is THIS
theorem at its `<effect>V3`/`n`. -/
theorem effCapOpenV3_authorizes {State : Type} (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < MASK_BITS) (S : CapHashScheme State) (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< n)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  capOpenEff_authorizes S t.tf capOpenCols _ n hn vkOfTag provided hChip
    (effCapOpenV3_satisfiedEff base name n S.chipAbsorb minit mfin maddrs t hsat i hi)
    caps leafAt hfaith actor src dst amt hsrc hedge htier

-- The effect-general cap-open shares the appendix width (+59) and adds 38 constraints (5 gate-pins).
section FanoutDescriptors

/-- The effect-kind bit exponents (`facet.rs` `1 <<< n`) for the cap-authorized fan-out effects. -/
def EFF_TRANSFER           : Nat := 1   -- transfer, attenuate-via-transfer-cap (EFFECT_TRANSFER)
def EFF_GRANT_CAPABILITY   : Nat := 2   -- grantCap, delegateAtten, attenuate (EFFECT_GRANT_CAPABILITY)
def EFF_REVOKE_CAPABILITY  : Nat := 3   -- revokeCapability (EFFECT_REVOKE_CAPABILITY)
def EFF_INTRODUCE          : Nat := 13  -- introduce (EFFECT_INTRODUCE)
def EFF_DELEGATION_OPS     : Nat := 16  -- delegate, revoke(Delegation), refreshDelegation (EFFECT_DELEGATION_OPS)

/-- The rotated INTRODUCE base (`v3Of` of the introduce v1 face). -/
def introduceV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitIntroduce.introduceVmDescriptor
/-- The rotated GRANT-CAP / DELEGATE-ATTEN base (`v3Of` of the attenuate-A v1 face — the deployed
grantCap base; `EffectVmEmitDelegateAtten.delegateAttenVmDescriptor` IS `attenuateVmDescriptor`, so
delegate-via-cap shares this base, distinguished only by the descriptor name string). -/
def grantCapV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptor
/-- The rotated REVOKE-DELEGATION base. -/
def revokeDelegationV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.revokeVmDescriptor
/-- The rotated REFRESH-DELEGATION base. -/
def refreshDelegationV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation.refreshVmDescriptor
/-- The rotated REVOKE-CAPABILITY base. -/
def revokeCapabilityBaseV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor

/-- **`delegateCapOpenV3`** — delegate-via-cap (the delegateAtten/attenuate base + the
`EFFECT_DELEGATION_OPS` appendix). The cross-vat delegate routes the in-circuit cap-membership open; the
cap must permit `EFFECT_DELEGATION_OPS` (`1 <<< 16`). -/
def delegateCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 grantCapV3 "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)
/-- **`introduceCapOpenV3`** — introduce-via-cap; the cap must permit `EFFECT_INTRODUCE` (`1 <<< 13`). -/
def introduceCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
    (effCapOpenV3 introduceV3 "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE)
/-- **`grantCapCapOpenV3`** — grantCap-via-cap; the cap must permit `EFFECT_GRANT_CAPABILITY` (`1 <<< 2`). -/
def grantCapCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
    (effCapOpenV3 grantCapV3 "dregg-effectvm-grantCap-v1-rot24-v3-capopen" EFF_GRANT_CAPABILITY)
/-- **`revokeCapOpenV3`** — revoke(Delegation)-via-cap; the cap must permit `EFFECT_DELEGATION_OPS`. -/
def revokeCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
    (effCapOpenV3 revokeDelegationV3 "dregg-effectvm-revoke-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)
/-- **`refreshDelegationCapOpenV3`** — refreshDelegation-via-cap; cap must permit `EFFECT_DELEGATION_OPS`. -/
def refreshDelegationCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
    (effCapOpenV3 refreshDelegationV3 "dregg-effectvm-refresh-v1-rot24-v3-capopen" EFF_DELEGATION_OPS)
/-- **`revokeCapabilityCapOpenV3`** — revokeCapability-via-cap; cap must permit `EFFECT_REVOKE_CAPABILITY`. -/
def revokeCapabilityCapOpenV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
    (effCapOpenV3 revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY)

/-- **`transferCapOpenEffV3`** (residual (a) — THE LIVE transfer cap-open) — the transfer base + the
effect-GENERAL appendix at `EFF_TRANSFER` (bit 1). Carries `capOpenConstraintsEff 1`: the genuine SUBMASK facet gate
(a BROAD honest transfer cap `mask_lo = 0xFFFF` PASSES — bit 1 set) and the DECODED tier (any committed
`auth_tag`, not pinned Signature). This is the descriptor the live `transferCapOpenVmDescriptor2R24`
routing proves through, so an honest transfer cap — broad mask, None/Signature tier — PROVES. -/
def transferCapOpenEffV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    (effCapOpenV3 transferV3 "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER)

/-- **`attenuateCapOpenEffV3`** (residual (a) — THE LIVE attenuate cap-open) — the attenuate base + the
effect-GENERAL appendix at `EFF_TRANSFER` (bit 1; the attenuate cap-open's leaf must permit
`EFFECT_TRANSFER`, mirroring the deployed `attenuateCapOpenVmDescriptor2R24` routing). Genuine submask
facet + decoded tier, so an honest broad/None-tier cap PROVES. -/
def attenuateCapOpenEffV3 : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.ATTENUATE_CAPABILITY
    (effCapOpenV3 attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER)

-- The live transfer/attenuate effect-general descriptors share the appendix + the appended
-- `selectorGate` tooth: +70 appendix constraints +1 selector gate = +71; +91 cols (the gate is
-- a `.base`, no new column).
#guard transferCapOpenEffV3.constraints.length == transferV3.constraints.length + 71
#guard attenuateCapOpenEffV3.constraints.length == attenuateV3.constraints.length + 71
#guard transferCapOpenEffV3.traceWidth == transferV3.traceWidth + 91
#guard attenuateCapOpenEffV3.traceWidth == attenuateV3.traceWidth + 91

-- Each fan-out descriptor adds the 70-constraint effect-general appendix + the selector-gate tooth
-- (+71 constraints total) + 91 cols past its base.
#guard delegateCapOpenV3.constraints.length == grantCapV3.constraints.length + 71
#guard introduceCapOpenV3.constraints.length == introduceV3.constraints.length + 71
#guard grantCapCapOpenV3.constraints.length == grantCapV3.constraints.length + 71
#guard revokeCapOpenV3.constraints.length == revokeDelegationV3.constraints.length + 71
#guard refreshDelegationCapOpenV3.constraints.length == refreshDelegationV3.constraints.length + 71
#guard revokeCapabilityCapOpenV3.constraints.length == revokeCapabilityBaseV3.constraints.length + 71
#guard delegateCapOpenV3.traceWidth == grantCapV3.traceWidth + 91
#guard introduceCapOpenV3.traceWidth == introduceV3.traceWidth + 91
#guard grantCapCapOpenV3.traceWidth == grantCapV3.traceWidth + 91
#guard revokeCapOpenV3.traceWidth == revokeDelegationV3.traceWidth + 91
#guard refreshDelegationCapOpenV3.traceWidth == refreshDelegationV3.traceWidth + 91
#guard revokeCapabilityCapOpenV3.traceWidth == revokeCapabilityBaseV3.traceWidth + 91

end FanoutDescriptors

/-! ## §5.K — THE LIVE AUTHORITY KEYSTONES (`…CapOpenEffV3_authorizes`): the apex authority leg over
the DEPLOYED descriptor.

The apex authority leg (`RotatedKernelRefinementFacet.TransferAuthoritySource`) must refine the descriptor
the LIVE prover selects — `transferCapOpenEffV3` for `[Transfer]`, `attenuateCapOpenEffV3` for
`[AttenuateCapability]` (both at `EFF_TRANSFER`, the genuine SUBMASK facet + DECODED tier). These keystones
give the kernel's faithful `authorizedFacetB caps provided turn` —
`authorizedFacetB caps provided turn` — but over the membership descriptor's `Satisfied2`, routed through
`effCapOpenV3_authorizes` (membership ⟹ `authorizedFacetEffB … (1 <<< EFF_TRANSFER)`) and the kernel
identity `authorizedFacetB = authorizedFacetEffB … (turnEffectBit turn)` (both `= EFFECT_TRANSFER = 1 <<<
1`). No constant is re-pinned; the facet axis is the genuine submask, the tier is the committed decode. -/

open Dregg2.Exec.FacetAuthority (authorizedFacetEffB authorizedFacetB_eq_eff turnEffectBit EFFECT_TRANSFER)

/-- **`transferCapOpenEffV3_authorizes` — THE LIVE TRANSFER AUTHORITY KEYSTONE.** A `Satisfied2` witness of
the LIVE `transferCapOpenEffV3` descriptor (the genuine submask facet at `EFF_TRANSFER` + decoded tier)
whose opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges the kernel's `authorizedFacetB
caps provided turn`, over the descriptor the live `transferCapOpenVmDescriptor2R24` route proves through. The authority is FORCED by the
in-circuit depth-16 membership open, NOT carried; the tier is the genuine committed decode (`htier`). -/
theorem transferCapOpenEffV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb transferCapOpenEffV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_TRANSFER) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  -- Strip the appended `selectorGate` tooth (constraint-subset monotonicity) before applying the
  -- bare keystone: the appendix reads no base/selector column, so the open is unaffected.
  have hsat := withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
    _ minit mfin maddrs t hsat
  have h := effCapOpenV3_authorizes (State := State) transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER (by decide)
    S vkOfTag provided minit mfin maddrs t hChip hsat i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier
  refine ⟨?_, h.2⟩
  -- `authorizedFacetB = authorizedFacetEffB … (turnEffectBit turn)`, and `turnEffectBit _ =
  -- EFFECT_TRANSFER = 1 <<< 1 = 1 <<< EFF_TRANSFER`, so the membership conclusion IS the gate.
  rw [authorizedFacetB_eq_eff]
  exact h.1

/-- **`attenuateCapOpenEffV3_authorizes` — THE LIVE ATTENUATE AUTHORITY KEYSTONE.** As
`transferCapOpenEffV3_authorizes` but over the LIVE `attenuateCapOpenEffV3` descriptor (the attenuate base +
the `EFF_TRANSFER` submask appendix) — the descriptor the live `attenuateCapOpenVmDescriptor2R24` route
proves through. Same `authorizedFacetB caps provided turn` conclusion, forced from the in-circuit open. -/
theorem attenuateCapOpenEffV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb attenuateCapOpenEffV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_TRANSFER) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hsat := withSelectorGate_satisfied2 S.chipAbsorb
    Dregg2.Circuit.Emit.EffectVmEmit.sel.ATTENUATE_CAPABILITY _ minit mfin maddrs t hsat
  have h := effCapOpenV3_authorizes (State := State) attenuateV3
    "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER (by decide)
    S vkOfTag provided minit mfin maddrs t hChip hsat i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier
  refine ⟨?_, h.2⟩
  rw [authorizedFacetB_eq_eff]
  exact h.1

/-- **`transferCapOpenEffV3_rejects_wrong_facet` (the LIVE transfer authority tooth).** A row of a
`transferCapOpenEffV3` witness whose leaf's `EFF_TRANSFER` mask bit is CLEAR (the cap does NOT carry the
transfer facet) CANNOT satisfy the appendix — the SELECTED-bit submask gate bites in-circuit. The negative
half of the live keystone (a wrong-facet cap ⟹ UNSAT), ported onto the deployed descriptor. -/
theorem transferCapOpenEffV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash transferCapOpenEffV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_TRANSFER hclear
    (effCapOpenV3_satisfiedEff transferV3 "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER
      hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
        _ minit mfin maddrs t hsat) i hi)

/-- **`attenuateCapOpenEffV3_rejects_wrong_facet` (the LIVE attenuate authority tooth).** As above over
`attenuateCapOpenEffV3`: a leaf lacking the `EFF_TRANSFER` facet bit ⟹ the appendix is UNSAT. -/
theorem attenuateCapOpenEffV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash attenuateCapOpenEffV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_TRANSFER hclear
    (effCapOpenV3_satisfiedEff attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER
      hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.ATTENUATE_CAPABILITY
        _ minit mfin maddrs t hsat) i hi)

/-! ## §5.F — THE FAN-OUT AUTHORITY KEYSTONES (`…CapOpenV3_authorizes`): the 6 cap-effects' apex
authority leg over their DEPLOYED fan-out descriptor.

`transfer`/`attenuate` ride `EFF_TRANSFER` (bit 1) and so collapse to `authorizedFacetB` (the
`turnEffectBit _ = EFFECT_TRANSFER` identity). The 6 fan-out effects ride DIFFERENT effect-kind bits
(introduce=13, delegate/revoke/refresh=16, grantCap=2, revokeCapability=3); their authority leg does NOT
collapse to `authorizedFacetB` — it is the GENERAL `authorizedFacetEffB caps provided (1 <<< n)` at the
effect's OWN bit, which is exactly what a per-effect authority gate needs (a cap permitting a DIFFERENT
effect-kind than the turn performs is REJECTED). Each keystone below is `effCapOpenV3_authorizes`
specialized to its `<effect>CapOpenV3`/`n`; each tooth is `satisfiedEff_rejects_wrong_facet` at the
effect's bit (the bit-clear leaf ⟹ the submask gate UNSAT). -/

/-- **`introduceCapOpenV3_authorizes` — THE LIVE INTRODUCE AUTHORITY KEYSTONE** (the BEACHHEAD). A
`Satisfied2` witness of the LIVE `introduceCapOpenV3` descriptor (the genuine submask facet at
`EFF_INTRODUCE` + decoded tier) whose opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges
the kernel's GENERAL `authorizedFacetEffB caps provided (1 <<< EFF_INTRODUCE)` for the turn — the
introduce facet, NOT the transfer facet. Forced by the in-circuit depth-16 membership open. -/
theorem introduceCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb introduceCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_INTRODUCE) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_INTRODUCE)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) introduceV3
    "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
      _ minit mfin maddrs t hsat) i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`delegateCapOpenV3_authorizes`** — the LIVE delegate-via-cap authority keystone (the delegateAtten
base + the `EFF_DELEGATION_OPS` appendix). Discharges `authorizedFacetEffB caps provided (1 <<<
EFF_DELEGATION_OPS)` — the delegation-ops facet — forced by the in-circuit open. -/
theorem delegateCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb delegateCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_DELEGATION_OPS) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) grantCapV3
    "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen" EFF_DELEGATION_OPS (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
      _ minit mfin maddrs t hsat) i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`grantCapCapOpenV3_authorizes`** — the LIVE grantCap-via-cap authority keystone. Discharges
`authorizedFacetEffB caps provided (1 <<< EFF_GRANT_CAPABILITY)` — the grant-capability facet. -/
theorem grantCapCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb grantCapCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_GRANT_CAPABILITY) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_GRANT_CAPABILITY)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) grantCapV3
    "dregg-effectvm-grantCap-v1-rot24-v3-capopen" EFF_GRANT_CAPABILITY (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
      _ minit mfin maddrs t hsat) i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`revokeCapOpenV3_authorizes`** — the LIVE revoke(Delegation)-via-cap authority keystone. Discharges
`authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)` — the delegation-ops facet. -/
theorem revokeCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb revokeCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_DELEGATION_OPS) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) revokeDelegationV3
    "dregg-effectvm-revoke-v1-rot24-v3-capopen" EFF_DELEGATION_OPS (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
      _ minit mfin maddrs t hsat) i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`refreshDelegationCapOpenV3_authorizes`** — the LIVE refreshDelegation-via-cap authority keystone.
Discharges `authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)` — the delegation-ops facet. -/
theorem refreshDelegationCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb refreshDelegationCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_DELEGATION_OPS) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) refreshDelegationV3
    "dregg-effectvm-refresh-v1-rot24-v3-capopen" EFF_DELEGATION_OPS (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
      _ minit mfin maddrs t hsat) i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-- **`revokeCapabilityCapOpenV3_authorizes`** — the LIVE revokeCapability-via-cap authority keystone.
Discharges `authorizedFacetEffB caps provided (1 <<< EFF_REVOKE_CAPABILITY)` — the revoke-capability
facet. -/
theorem revokeCapabilityCapOpenV3_authorizes {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb revokeCapabilityCapOpenV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_REVOKE_CAPABILITY) caps
      ((Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc capOpenCols.src = (src : ℤ))
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided (1 <<< EFF_REVOKE_CAPABILITY)
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  effCapOpenV3_authorizes (State := State) revokeCapabilityBaseV3
    "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY (by decide)
    S vkOfTag provided minit mfin maddrs t hChip
    (withSelectorGate_satisfied2 S.chipAbsorb Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
      _ minit mfin maddrs t hsat) i hi caps leafAt hfaith
    actor src dst amt hsrc hedge htier

/-! ### The fan-out authority TEETH (`…CapOpenV3_rejects_wrong_facet`): a leaf lacking the effect's
facet bit ⟹ the SELECTED-bit submask gate bites ⟹ the appendix is UNSAT. Both-polarity per effect. -/

/-- **`introduceCapOpenV3_rejects_wrong_facet`** — a row whose leaf's `EFF_INTRODUCE` mask bit is CLEAR
cannot satisfy the introduce appendix (the submask gate bites in-circuit). -/
theorem introduceCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_INTRODUCE) = 0) :
    ¬ Satisfied2 hash introduceCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_INTRODUCE hclear
    (effCapOpenV3_satisfiedEff introduceV3 "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE
      hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
        _ minit mfin maddrs t hsat) i hi)

/-- **`delegateCapOpenV3_rejects_wrong_facet`** — a leaf lacking the `EFF_DELEGATION_OPS` bit ⟹ UNSAT. -/
theorem delegateCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_DELEGATION_OPS) = 0) :
    ¬ Satisfied2 hash delegateCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_DELEGATION_OPS hclear
    (effCapOpenV3_satisfiedEff grantCapV3 "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen"
      EFF_DELEGATION_OPS hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        _ minit mfin maddrs t hsat) i hi)

/-- **`grantCapCapOpenV3_rejects_wrong_facet`** — a leaf lacking the `EFF_GRANT_CAPABILITY` bit ⟹ UNSAT. -/
theorem grantCapCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_GRANT_CAPABILITY) = 0) :
    ¬ Satisfied2 hash grantCapCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_GRANT_CAPABILITY hclear
    (effCapOpenV3_satisfiedEff grantCapV3 "dregg-effectvm-grantCap-v1-rot24-v3-capopen"
      EFF_GRANT_CAPABILITY hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        _ minit mfin maddrs t hsat) i hi)

/-- **`revokeCapOpenV3_rejects_wrong_facet`** — a leaf lacking the `EFF_DELEGATION_OPS` bit ⟹ UNSAT. -/
theorem revokeCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_DELEGATION_OPS) = 0) :
    ¬ Satisfied2 hash revokeCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_DELEGATION_OPS hclear
    (effCapOpenV3_satisfiedEff revokeDelegationV3 "dregg-effectvm-revoke-v1-rot24-v3-capopen"
      EFF_DELEGATION_OPS hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
        _ minit mfin maddrs t hsat) i hi)

/-- **`refreshDelegationCapOpenV3_rejects_wrong_facet`** — a leaf lacking `EFF_DELEGATION_OPS` ⟹ UNSAT. -/
theorem refreshDelegationCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_DELEGATION_OPS) = 0) :
    ¬ Satisfied2 hash refreshDelegationCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_DELEGATION_OPS hclear
    (effCapOpenV3_satisfiedEff refreshDelegationV3 "dregg-effectvm-refresh-v1-rot24-v3-capopen"
      EFF_DELEGATION_OPS hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
        _ minit mfin maddrs t hsat) i hi)

/-- **`revokeCapabilityCapOpenV3_rejects_wrong_facet`** — a leaf lacking `EFF_REVOKE_CAPABILITY` ⟹ UNSAT. -/
theorem revokeCapabilityCapOpenV3_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hclear : (Dregg2.Circuit.DescriptorIR2.envAt t i).loc (capOpenCols.bit EFF_REVOKE_CAPABILITY) = 0) :
    ¬ Satisfied2 hash revokeCapabilityCapOpenV3 minit mfin maddrs t := fun hsat =>
  satisfiedEff_rejects_wrong_facet hash t.tf capOpenCols
    (Dregg2.Circuit.DescriptorIR2.envAt t i) EFF_REVOKE_CAPABILITY hclear
    (effCapOpenV3_satisfiedEff revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen"
      EFF_REVOKE_CAPABILITY hash minit mfin maddrs t
      (withSelectorGate_satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
        _ minit mfin maddrs t hsat) i hi)

/-! ## §6 — the registry WITH the cap-open (F5 — `Rfix` ranges over the LIVE authority descriptor).

`EffectVmEmitRotationV3.v3Registry` is the 36-member cohort; it CANNOT itself name the cap-open
(`CapOpenEmit` imports `EffectVmEmitRotationV3`, so the dependency runs this way). The deployed wire
registry (`V3_STAGED_REGISTRY_TSV`) carries 44 lines — the 36 cohort members + the 6 fan-out cap-open
members + the 2 LIVE effect-general transfer/attenuate legs (`EmitRotationV3.lean` emits them).
`v3RegistryCapOpen` is the Lean twin of that 44-line registry. The soundness apex's `Rfix` is re-keyed
over THIS list, so `registryCommit Rfix` ranges over the LIVE cap-open descriptor (`Rfix 12 =
attenuateCapOpenEffV3`) — the one in-circuit authority gadget the apex authority leg refines IS inside
the registry the apex's `StarkSound` quantifies over (F5 CLOSED, on the LIVE descriptor). -/

/-- **`v3RegistryCapOpen`** — the 44-member deployed registry: the 36 cohort members
(`EffectVmEmitRotationV3.v3Registry`) + the 6 fan-out cap-open members (delegate/introduce/grantCap/
revoke/refreshDelegation/revokeCapability) + the 2 LIVE effect-general legs
(`transferCapOpenEffV3`/`attenuateCapOpenEffV3`, the genuine-submask + decoded-tier descriptors the
deployed prover routes AND the apex authority leg refines). The Lean twin of the staged registry TSV;
the soundness apex's `Rfix` re-keys over it. -/
def v3RegistryCapOpen : List (String × EffectVmDescriptor2) :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry
    ++ [ -- THE FAN-OUT (residual (a) closed for these 6): each carries the effect-GENERAL appendix
         -- (`capOpenConstraintsEff n`) binding the cap to THAT effect-kind bit, not transfer.
         ("delegateCapOpenVmDescriptor2R24", delegateCapOpenV3)
       , ("introduceCapOpenVmDescriptor2R24", introduceCapOpenV3)
       , ("grantCapCapOpenVmDescriptor2R24", grantCapCapOpenV3)
       , ("revokeCapOpenVmDescriptor2R24", revokeCapOpenV3)
       , ("refreshDelegationCapOpenVmDescriptor2R24", refreshDelegationCapOpenV3)
       , ("revokeCapabilityCapOpenVmDescriptor2R24", revokeCapabilityCapOpenV3)
       -- residual (a) — THE LIVE transfer/attenuate cap-open members (genuine submask facet +
       -- DECODED tier). The live prover routes these `…-eff` descriptors AND the apex authority leg
       -- refines them (`transferCapOpenEffV3_authorizes`) — the wire and the proven descriptor are
       -- ONE. An honest broad/None-tier cap PROVES.
       , ("transferCapOpenEffVmDescriptor2R24", transferCapOpenEffV3)
       , ("attenuateCapOpenEffVmDescriptor2R24", attenuateCapOpenEffV3) ]

/-- The registry-with-cap-open has 44 members (36 cohort + 6 fan-out + 2 live `-eff`
transfer/attenuate). The Signature-pinned `capOpenAttenuateV3`/`transferCapOpenV3` are DELETED — the
apex authority leg refines the LIVE `…CapOpenEffV3` descriptors, so nothing is proven about an
unwired descriptor. -/
theorem v3RegistryCapOpen_length : v3RegistryCapOpen.length = 44 := by
  simp [v3RegistryCapOpen, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry]

-- The cap-open authority members are positions 36..43; the 36 cohort members are unchanged at 0..35.
#guard v3RegistryCapOpen.length == 44
#guard (v3RegistryCapOpen[36]?.map (·.1)) == some "delegateCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[37]?.map (·.1)) == some "introduceCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[38]?.map (·.1)) == some "grantCapCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[39]?.map (·.1)) == some "revokeCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[40]?.map (·.1)) == some "refreshDelegationCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[41]?.map (·.1)) == some "revokeCapabilityCapOpenVmDescriptor2R24"
#guard (v3RegistryCapOpen[42]?.map (·.1)) == some "transferCapOpenEffVmDescriptor2R24"
#guard (v3RegistryCapOpen[43]?.map (·.1)) == some "attenuateCapOpenEffVmDescriptor2R24"
#guard (v3RegistryCapOpen[0]?.map (·.1)) == some "transferVmDescriptor2R24"

/-- The LIVE transfer cap-open member of the registry IS `transferCapOpenEffV3` (position 42). -/
theorem v3RegistryCapOpen_transferEff :
    (v3RegistryCapOpen[42]?.map (·.2)) = some transferCapOpenEffV3 := rfl

/-- The LIVE attenuate cap-open member of the registry IS `attenuateCapOpenEffV3` (position 43). -/
theorem v3RegistryCapOpen_attenuateEff :
    (v3RegistryCapOpen[43]?.map (·.2)) = some attenuateCapOpenEffV3 := rfl

/-- The delegate fan-out member IS `delegateCapOpenV3` (position 36). -/
theorem v3RegistryCapOpen_delegate :
    (v3RegistryCapOpen[36]?.map (·.2)) = some delegateCapOpenV3 := rfl

/-- The revoke fan-out member IS `revokeCapOpenV3` (position 39). -/
theorem v3RegistryCapOpen_revoke :
    (v3RegistryCapOpen[39]?.map (·.2)) = some revokeCapOpenV3 := rfl

/-! ## §7 — Axiom hygiene. -/

#assert_axioms effCapOpenV3_satisfiedEff
#assert_axioms effCapOpenV3_authorizes
#assert_axioms transferCapOpenEffV3_authorizes
#assert_axioms attenuateCapOpenEffV3_authorizes
#assert_axioms transferCapOpenEffV3_rejects_wrong_facet
#assert_axioms attenuateCapOpenEffV3_rejects_wrong_facet
#assert_axioms introduceCapOpenV3_authorizes
#assert_axioms delegateCapOpenV3_authorizes
#assert_axioms grantCapCapOpenV3_authorizes
#assert_axioms revokeCapOpenV3_authorizes
#assert_axioms refreshDelegationCapOpenV3_authorizes
#assert_axioms revokeCapabilityCapOpenV3_authorizes
#assert_axioms introduceCapOpenV3_rejects_wrong_facet
#assert_axioms delegateCapOpenV3_rejects_wrong_facet
#assert_axioms grantCapCapOpenV3_rejects_wrong_facet
#assert_axioms revokeCapOpenV3_rejects_wrong_facet
#assert_axioms refreshDelegationCapOpenV3_rejects_wrong_facet
#assert_axioms revokeCapabilityCapOpenV3_rejects_wrong_facet
#assert_axioms v3RegistryCapOpen_length
#assert_axioms v3RegistryCapOpen_transferEff
#assert_axioms v3RegistryCapOpen_attenuateEff
#assert_axioms v3RegistryCapOpen_delegate
#assert_axioms v3RegistryCapOpen_revoke

end Dregg2.Circuit.Emit.CapOpenEmit
