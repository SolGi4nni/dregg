/-
# Dregg2.Circuit.Satisfied2FaithfulDeployed — `Satisfied2Faithful` at the REAL DEPLOYED permutation.

## Honest scope (first sentence)

All three chip obligations of `Satisfied2Faithful` are discharged HERE at the REAL deployed
permutation `Poseidon2BabyBearW16.perm` (the KAT-validated bit-exact `Poseidon2BabyBear<16>`), NOT at
the constant-zero toy `permOutZ`:

  * `permWidth` — PROVED unconditionally: `perm` always emits a width-16 state (its last stage is an
    `externalRound` fold, whose body is `mdsLight = (List.range 16).map …`), so the deployed
    8-lane squeeze `(perm state).take CHIP_OUT_LANES` has length `CHIP_OUT_LANES` for EVERY input.
  * `chipHashIsLane0` — PROVED. The deployed v1 digest IS lane 0 of the genuine squeeze. This is the
    deployed design, NOT a chosen-to-fit hash: the `Ir2Air::Chip` constrains the FULL 16-lane
    permutation and "merely returns `state[0]`" (`DescriptorIR2.lean:1194`), and `chip_lookup_sound`
    forces `digestCol = ` the HEAD of the output block. So the honest deployed digest is
    `hashDeployed ins := (permOutDeployed ins).headD 0` — lane 0 of the REAL perm, non-constant
    (KAT lane 0 = `1906786279 ≠ 0`), NOT the toy's `permOut0 = fun _ => 0`.
  * `chipTableFaithful` — PROVED for a chip table whose row is a GENUINE `chipRowN permOutDeployed`
    tuple of the REAL permutation on a real 16-felt input (`deployedIns = 0..15`), mirroring
    `genuineChipTbl_sound` but over `perm`, not `permOutZ`.

`satisfied2Faithful_deployed` CONSTRUCTS the full `Satisfied2Faithful` object for the live
`transferV3` descriptor at `permOutDeployed`/`hashDeployed` — the SAME descriptor
`satisfied2Faithful_transferV3` uses at the toy, now at the deployed hash. It discharges the deployed
permutation for the chip legs of ALL 26 sites that ASSUME `Satisfied2Faithful` (every site is
parametric in `permOut`/`hash`; this exhibits the deployed pair those parameters denote and shows the
three chip obligations hold for it). What remains ASSUMED at those sites is the SAME as before — a
witness of the per-descriptor `Satisfied2` core for the site's own trace; this brick closes only the
"is the permutation the toy?" gap, at ALL of them, by exhibiting the real one.

## Teeth (both-truth)

  * The deployed perm SATISFIES `permWidth` (proved) and is genuinely NON-constant — the KAT
    `#guard`s below show `permOutDeployed (0..15)` is the real perm's first-8 squeeze, head `≠ 0`;
    whereas the toy `permOutZ` is `fun _ => replicate 8 0` (the vacuous/trivial case).
  * The chip table row is a REAL `chipRowN permOutDeployed` tuple of `perm`, not a degenerate row.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free. NEW file; imports read-only.
`Mathlib.Tactic` imported directly (omega/decide) in case a concurrent import-slimming lane trimmed it.
-/
import Mathlib.Tactic
import Dregg2.Circuit.FloorsNonVacuous
import Dregg2.Circuit.Poseidon2BabyBearW16

namespace Dregg2.Circuit.Satisfied2FaithfulDeployed

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Satisfied2Faithful
open Dregg2.Circuit.FloorsNonVacuous
open Dregg2.Circuit.Poseidon2BabyBearW16
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 memLog_graduateV1 mapLog_graduateV1)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3FrozenAuthority)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — `perm` is width-16 on every input (the structural fact `permWidth` rests on). -/

/-- `mdsLight` always emits a width-16 state (`(List.range 16).map …`). -/
theorem mdsLight_length (s : List Nat) : (mdsLight s).length = 16 := by
  simp [mdsLight]

/-- `externalRound` is `mdsLight (…)`, hence width-16. -/
theorem externalRound_length (rc s : List Nat) : (externalRound rc s).length = 16 := by
  unfold externalRound; exact mdsLight_length _

/-- A NON-EMPTY `externalRound` fold ends in an `externalRound`, so its output is width-16 — the
last stage of `perm` (`rcExtFinal.foldl externalRound …`) fixes the output width regardless of the
(internal-round) accumulator. -/
theorem foldl_external_length :
    ∀ (L : List (List Nat)), L ≠ [] → ∀ (init : List Nat),
      (L.foldl (fun st r => externalRound r st) init).length = 16
  | [], h, _ => absurd rfl h
  | [rc], _, init => by
      show (externalRound rc init).length = 16
      exact externalRound_length rc init
  | rc :: rc2 :: rest, _, init => by
      rw [List.foldl_cons]
      exact foldl_external_length (rc2 :: rest) (List.cons_ne_nil _ _) (externalRound rc init)

/-- **The deployed permutation always emits a width-16 state.** -/
theorem perm_length (x : List Nat) : (perm x).length = 16 := by
  unfold perm
  exact foldl_external_length rcExtFinal (by decide) _

/-! ## §2 — `permOutDeployed`: the honest ℤ-wrapper of the REAL `perm`, squeezed to `CHIP_OUT_LANES`.

The encoding: a chip input `z : ℤ` is the BabyBear canonical residue `(z % P).toNat` (`P` the
BabyBear prime `2013265921`); the chip absorbs `padTo CHIP_RATE ins` (the deployed 16-wide state);
`perm` runs; the squeeze exposes the first `CHIP_OUT_LANES` lanes, cast back to ℤ. This is the
deployed `Poseidon2BabyBear<16>` as a `List ℤ → List ℤ` — NOT a stub. -/

/-- ℤ → BabyBear canonical residue (a `Nat` in `[0, P)`). -/
def toNatP (z : ℤ) : Nat := (z % (P : ℤ)).toNat

/-- **`permOutDeployed`** — the deployed permutation's `CHIP_OUT_LANES`-lane squeeze on the absorbed,
`CHIP_RATE`-padded chip inputs:

    permOutDeployed ins = ((perm ((padTo CHIP_RATE ins).map toNatP)).take CHIP_OUT_LANES).map Int.ofNat

It wraps `Poseidon2BabyBearW16.perm` (the KAT-validated deployed hash), not a constant. -/
def permOutDeployed (ins : List ℤ) : List ℤ :=
  List.map Int.ofNat
    (List.take CHIP_OUT_LANES (perm (List.map toNatP (padTo CHIP_RATE ins))))

/-- The deployed v1 digest: lane 0 of the genuine squeeze (the deployed `Ir2Air::Chip` returns
`state[0]`). This is the honest deployed digest for the real perm, non-constant. -/
def hashDeployed (ins : List ℤ) : ℤ := (permOutDeployed ins).headD 0

/-! ## §3 — the three chip obligations, PROVED at the deployed permutation. -/

/-- **`permWidth` at the DEPLOYED perm.** `(permOutDeployed ins).length = CHIP_OUT_LANES` for EVERY
`ins`, from `perm`'s unconditional width-16 output. -/
theorem permOutDeployed_width (ins : List ℤ) :
    (permOutDeployed ins).length = CHIP_OUT_LANES := by
  unfold permOutDeployed
  rw [List.length_map, List.length_take, perm_length]
  simp only [CHIP_OUT_LANES]
  omega

/-- **`chipHashIsLane0` at the DEPLOYED perm.** The deployed digest IS lane 0 of the genuine
squeeze — true BY THE DEPLOYED DESIGN (`hashDeployed := lane 0`), for the REAL non-constant perm. -/
theorem permOutDeployed_lane0 :
    ∀ ins, hashDeployed ins = (permOutDeployed ins).headD 0 := fun _ => rfl

/-- A real deployed chip input: the 16-felt state `0..15`. -/
def deployedIns : List ℤ := (List.range 16).map (fun n => (n : ℤ))

/-- A GENUINE deployed chip table: the single row is a real `chipRowN permOutDeployed deployedIns` —
a wide-permutation tuple of the REAL `perm` on a real input (NOT the toy `permOutZ`). -/
def deployedChipTbl : Table := [chipRowN permOutDeployed deployedIns]

/-- **`chipTableFaithful` at the DEPLOYED perm.** Every row of `deployedChipTbl` is a genuine
`chipRowN permOutDeployed` tuple — the `Ir2Air::Chip` faithfulness at the REAL permutation. Mirrors
`genuineChipTbl_sound`, over `perm` instead of the constant-zero `permOutZ`. -/
theorem deployedChipTbl_sound : ChipTableSoundN permOutDeployed deployedChipTbl := by
  intro r hr
  simp only [deployedChipTbl, List.mem_singleton] at hr
  exact ⟨deployedIns, by simp [deployedIns, CHIP_RATE], hr⟩

/-! ## §4 — the faithful trace at the deployed tables, and the KEYSTONE construction. -/

/-- The deployed faithful auxiliary tables: the GENUINE deployed chip table on `.poseidon2`, the
genuine limb table on `.range`, empty elsewhere. Kept top-level so range-faithfulness reduces by
`unfold` without evaluating the size-`2^30` `rangeRows` list. -/
def deployedTf : TableId → Table := fun tid =>
  if tid = .poseidon2 then deployedChipTbl
  else if tid = .range then rangeRows BAL_LIMB_BITS
  else []

/-- The deployed faithful trace: zero main rows, deployed chip/range tables, empty mem/map. -/
def deployedTrace : VmTrace where
  rows := []
  pub  := fun _ => 0
  tf   := deployedTf

theorem deployedTf_poseidon2 : deployedTf .poseidon2 = deployedChipTbl := by unfold deployedTf; rfl
theorem deployedTf_range : deployedTf .range = rangeRows BAL_LIMB_BITS := by unfold deployedTf; rfl
theorem deployedTf_memory : deployedTf .memory = [] := by unfold deployedTf; rfl
theorem deployedTf_mapOps : deployedTf .mapOps = [] := by unfold deployedTf; rfl

theorem deployedTrace_tf : deployedTrace.tf = deployedTf := rfl
theorem deployedTrace_poseidon2 : deployedTrace.tf .poseidon2 = deployedChipTbl := by
  rw [deployedTrace_tf, deployedTf_poseidon2]
theorem deployedTrace_range : deployedTrace.tf .range = rangeRows BAL_LIMB_BITS := by
  rw [deployedTrace_tf, deployedTf_range]
theorem deployedTrace_memory : deployedTrace.tf .memory = [] := by
  rw [deployedTrace_tf, deployedTf_memory]
theorem deployedTrace_mapOps : deployedTrace.tf .mapOps = [] := by
  rw [deployedTrace_tf, deployedTf_mapOps]
theorem deployedTrace_rows : deployedTrace.rows = [] := rfl

/-- The underlying `Satisfied2` of the deployed trace (per-row legs vacuous over `rows = []`; mem/map
legs collapse to the empty log). Independent of the chip/range table CONTENT — mirrors
`satisfied2_faithfulTrace`, now over the deployed tables. -/
theorem satisfied2_deployedTrace (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash transferV3 minit mfin [] deployedTrace where
  rowConstraints := by intro i hi; rw [deployedTrace_rows] at hi; simp at hi
  rowHashes := by intro i hi; rw [deployedTrace_rows] at hi; simp at hi
  rowRanges := by intro i hi; rw [deployedTrace_rows] at hi; simp at hi
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1] at hop
    simp at hop
  memDisciplined := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    trivial
  memBalanced := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  memTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    rw [deployedTrace_memory, List.map_nil]
  mapTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      mapLog_graduateV1]
    rw [deployedTrace_mapOps]

/-- **`satisfied2Faithful_deployed` — THE KEYSTONE at the DEPLOYED permutation.** The full
`Satisfied2Faithful` object is inhabited for the live `transferV3` at `permOutDeployed`/`hashDeployed`
(the REAL `perm` and its lane-0 digest): `Satisfied2` PLUS the genuine deployed chip-table
faithfulness (`deployedChipTbl_sound`), the genuine range-table faithfulness (`rfl`), the deployed
permutation width (`permOutDeployed_width`), and the lane-0 digest identity (`permOutDeployed_lane0`).
Unlike `satisfied2Faithful_transferV3` (which uses the constant-zero `permOutZ`), this discharges the
three chip obligations at the ACTUAL deployed hash. -/
theorem satisfied2Faithful_deployed (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2Faithful permOutDeployed hashDeployed transferV3 minit mfin [] deployedTrace where
  toSatisfied2 := satisfied2_deployedTrace hashDeployed minit mfin
  permWidth := permOutDeployed_width
  chipHashIsLane0 := permOutDeployed_lane0
  chipTableFaithful := by rw [deployedTrace_poseidon2]; exact deployedChipTbl_sound
  rangeTableFaithful := deployedTrace_range

/-- **`satisfied2Faithful_deployed_inhabited` — the faithful object is inhabited AT THE DEPLOYED
PERMUTATION.** So the apex's `Satisfied2Faithful` hypothesis is realizable by the REAL perm, not only
the toy: the exhibited `permOut`/`hash` ARE the deployed `Poseidon2BabyBear<16>` pair. -/
theorem satisfied2Faithful_deployed_inhabited :
    ∃ (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
      (maddrs : List ℤ) (t : VmTrace),
      Satisfied2Faithful permOut hash transferV3 minit mfin maddrs t :=
  ⟨permOutDeployed, hashDeployed, fun _ => 0, fun _ => (0, 0), [], deployedTrace,
   satisfied2Faithful_deployed (fun _ => 0) (fun _ => (0, 0))⟩

/-- **The collapse recipe FIRES on the deployed keystone.** The v1 denotation `satisfiedVm` follows
from the deployed faithful object with NO free chip/range lever — the structure CARRIES them, at the
DEPLOYED permutation. (`rows = []`, so the conclusion is vacuous here; the point is the recipe accepts
the deployed-perm witness.) -/
theorem deployed_collapse_recipe
    (hgrad : Dregg2.Circuit.Emit.EffectVmEmitV2.graduable
      (rotateV3FrozenAuthority transferVmDescriptor) = true) :
    ∀ i, i < deployedTrace.rows.length →
      satisfiedVm hashDeployed (rotateV3FrozenAuthority transferVmDescriptor)
        (envAt deployedTrace i) (i == 0) (i + 1 == deployedTrace.rows.length) :=
  satisfied2Faithful_satisfiedVm permOutDeployed hashDeployed
    (rotateV3FrozenAuthority transferVmDescriptor)
    (fun _ => 0) (fun _ => (0, 0)) [] deployedTrace hgrad
    (satisfied2Faithful_deployed (fun _ => 0) (fun _ => (0, 0)))

/-! ## §5 — teeth: the deployed perm flows through `permOutDeployed` (KAT), and is NON-constant,
whereas the toy `permOutZ` is the trivial constant case. -/

/- `permOutDeployed (0..15)` is the deployed perm's first-8 squeeze, bit-exact (KAT from the deployed
Rust `default_babybear_poseidon2_16().permute([0..15])`). A single diverging limb fails the build. -/
#guard permOutDeployed ((List.range 16).map (fun n => (n : ℤ))) =
  [1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001, 1761127344]

/- The deployed digest is the genuine non-zero lane-0 squeeze of the real perm. -/
#guard hashDeployed ((List.range 16).map (fun n => (n : ℤ))) = 1906786279

/- Both-truth: the toy `permOutZ` is the CONSTANT-zero case (vacuous), while the deployed perm is
genuinely non-constant — they DISAGREE on `0..15`. -/
#guard permOutZ ((List.range 16).map (fun n => (n : ℤ))) = List.replicate CHIP_OUT_LANES 0
#guard ! (permOutDeployed ((List.range 16).map (fun n => (n : ℤ))) ==
          permOutZ ((List.range 16).map (fun n => (n : ℤ))))

/-! ## §6 — axiom hygiene. -/

#assert_axioms perm_length
#assert_axioms permOutDeployed_width
#assert_axioms deployedChipTbl_sound
#assert_axioms satisfied2_deployedTrace
#assert_axioms satisfied2Faithful_deployed
#assert_axioms satisfied2Faithful_deployed_inhabited
#assert_axioms deployed_collapse_recipe

end Dregg2.Circuit.Satisfied2FaithfulDeployed
