/-
# `Dregg2.Circuit.AlgoStarkSoundGeneral` — THE GENERAL ALL-EFFECTS ASSEMBLER: `AlgoStarkSound`
for ANY `d : EffectVmDescriptor2` from {floor + per-effect MEMORY LEGS}, with `hood`/`hbus`/
`MainAirAcceptF` DISCHARGED from the column-layout modelers.

## ⚑⚑ STATUS 2026-07-25 — THE THREE ASSEMBLERS DESCRIBED BELOW ARE DELETED. READ THIS FIRST.

`algoStarkSound_of_memoryLegs`, `algoStarkSound_of_memoryFree` and
`algoStarkSound_transferV3_ofBusModels` are GONE from this file. They took `FriLdtExtract … d` in
their FRI slot, and that bundle is PROVED to force `CircuitSoundness.verifyBatch` to reject EVERY
input at the deployed `cfg*` arguments (`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`,
`PremiseInhabitability.friLdtExtract_empties_deployed`) — so all three, and everything assembled
through them, quantified over an EMPTY accepting set and were VACUOUSLY true.

Their replacements live in `Dregg2/Circuit/ApexOodLaneRepair.lean`, same statements over
`FriLdtExtractCons` (`oodPoint = ood :: oodRest`, the shape `FriVerifier.batchTablesCheck` matches
at `FriVerifier.lean:805`):
`algoStarkSound_of_memoryLegs_cons`, `algoStarkSound_of_memoryFree_cons`,
`algoStarkSound_transferV3_ofBusModels_cons`.

The corrected premise is NOT a second vacuity: `ApexOodLaneRepair.friLdtExtractCons_iff_noOodShape`
proves it EQUIVALENT to itself with the OOD conjunct DELETED, because acceptance itself supplies the
cons shape (`acceptsFull_gives_cons_shape`) — zero added strength, so the repair can never be the
reason a premise is empty.

`FriLdtExtract` the DEFINITION (§1 below) is deliberately RETAINED as the SUBJECT of those vacuity
theorems, so the broken shape cannot be reintroduced silently. It has NO consumers left in the tree
outside the vacuity instruments.

⚠ The rest of this header is the PRE-DELETION text, kept because it still describes §1's bundles,
§2's `hbus` arm, §4's memory-leg machinery and `algoStarkSound_transferV3_subsumed` accurately.
Wherever it says `algoStarkSound_of_memoryLegs` / `_of_memoryFree` / `_transferV3_ofBusModels`,
read the `_cons` form in `ApexOodLaneRepair`. ⚠ `algoStarkSound_transferV3_subsumed` (still here)
rides `FriLdtExtractV3`, which is ITSELF proved empty
(`FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything`); its corrected chain
is `StarkSoundFriLdtCorrected`, and it is NOT migrated as of this date.

## What this closes (the one-line honest claim)

`algoStarkSound_of_memoryLegs (d)` assembles the full `AlgoStarkSound` at the registry slice
`fun _ => d` for ANY descriptor, and its residual `Prop` hypotheses are EXACTLY

  1. `Poseidon2SpongeCR sponge`      — the shared commitment-binding hash floor;
  2. `FriLdtExtract … d tr`          — the FRI-LDT-@-deployed extraction bundle, ∀ d (the general
        form of `AlgoStarkSoundTransferV3.FriLdtExtractV3`'s FRI-geometry payload: opening
        structure, Merkle recompute data, the GENERAL column-layout equation over
        `OodColumnLayout.oodBatchResidual d`, the honest FS ε-form non-exceptionality of Λ and ζ,
        and the published-commit link — NO `hood`, NO `MainAirAcceptF`, NO `hbus`);
  3. `BusModelFamily … d tr`         — the per-used-table LogUp bus models (`BusModelOk`, the
        named FS side conditions of `LogUpColumnLayout` §3) for `d`'s declared lookups;
  4. `MemoryLegs … d tr`             — the per-effect MEMORY/MAPOP legs: the non-lookup
        non-arith constraint arm (memOp/mapOp/umemOp/proofBind denotations) plus the six
        memory-table legs (Nodup / closed / `Disciplined` / `MemCheck` / the two table-assembly
        faithfulness equations);

plus two rfl-per-effect structural equations `d.hashSites = []` / `d.ranges = []` (the graduated
column shape — every graduated descriptor discharges them by `rfl`). NOT among the inputs:
`hood`, `hbus`, `MainAirAcceptF`, any per-descriptor column layout — those are DERIVED, per
accepting run, from the two modelers:

  * `OodColumnLayout.hood_of_oodColumnLayout` (∀ d) +
    `FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals` ⟹ `MainAirAcceptF d t`;
  * `LogUpColumnLayout.busModel_forces_lookup_holds` (∀ d), through `nonArithArm_of_busModels`
    (the split generalization of `LogUpColumnLayout.hbus_of_busModels` to descriptors that ALSO
    declare memory/map ops) ⟹ the whole non-arith `hbus` arm.

`algoStarkSound_of_memoryFree (d)` is the mem/map-free corollary: the MEMORY-LEGS input is
REPLACED by the graduated-shape fact (`∀ c, ¬arith → c is a lookup` — rfl-family per effect,
`transferV3` proves it via the committed `hbus_is_lookup`) plus the two aux-table-emptiness
assembly facts (`MemMapFree`), everything else identical.

## The kernel fan-out is now mechanical

Per effect, STARK-soundness = one invocation of `algoStarkSound_of_memoryLegs d` (or
`_of_memoryFree d`) + that effect's memory legs (mem/map-free effects: the `rfl`-shape facts).
Nothing else is per-effect: layout, RLC de-batch, `MainAirAcceptF`, and the LogUp bus discharge
are the ∀-d modelers. `transferV3_sideConditions_mechanical` exhibits the whole per-effect
obligation for the deployed transfer slice discharging by `rfl` + the committed shape brick.

## ★ transferV3 SUBSUMPTION — and the ONE NAMED GAP

  * `algoStarkSound_transferV3_ofBusModels` = `algoStarkSound_of_memoryFree transferV3 …`:
        the general assembler AT the deployed descriptor; residual =
        {`Poseidon2SpongeCR`, `FriLdtExtract … transferV3`, `BusModelFamily … transferV3`} +
        `MemMapFree` (the bundle emptiness facts) — the DEEPER form (the LogUp arm is DERIVED
        from `BusModelOk`, not carried).
  * `algoStarkSound_transferV3_subsumed`: the EXACT statement of
        `AlgoStarkSoundTransferV3.algoStarkSound_transferV3` ({`Poseidon2SpongeCR`,
        `FriLdtExtractV3`} → `AlgoStarkSound` at `transferV3`), RE-DERIVED with the
        `hood`/`MainAirAcceptF` wiring routed through the GENERAL modeler
        (`hood_of_oodColumnLayout transferV3` — the hand-wired `hood_of_reductions` chain of the
        template's §3 is subsumed; the template's layout equation feeds the general
        `oodBatchResidual transferV3` DEFINITIONALLY).

THE NAMED GAP (honest, structural — not faked over): full literal subsumption
"`algoStarkSound_transferV3 := algoStarkSound_of_memoryFree transferV3 …`" is blocked at the BUS
SLOT'S FORM. `FriLdtExtractV3` carries the LogUp arm POST-discharge (`… → c.holdsAt …`, the
`hbus` conjunct), while the general assembler's residual carries the PRE-discharge
`BusModelOk` family — and the proven modeler arrow runs `BusModelOk ⟹ arm`
(`busModel_forces_lookup_holds`), never backwards (a discharged membership cannot reconstruct
the bus's balance/non-exceptionality/fingerprint events). So the general instance
(`_ofBusModels`) has the STRICTLY DEEPER premise, and the old statement is separately re-derived
(`_subsumed`) consuming the bundle's own already-discharged arm. Closing the gap = restating the
deployed extraction bundle with `BusModelOk` in the bus slot (a `FriLdtExtractV3` REPLACEMENT,
which this read-only lane does not edit).

## Discipline

Sorry-free; no carrier; no `decide`/`Fintype` over `|F|`-sized objects; BabyBear arithmetic never
computed. New file; imports read-only; builds targeted
(`lake build Dregg2.Circuit.AlgoStarkSoundGeneral`).
-/
import Dregg2.Circuit.OodColumnLayout
import Dregg2.Circuit.LogUpColumnLayout

namespace Dregg2.Circuit.AlgoStarkSoundGeneral

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith
   TableOpening fullChecks)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof tracePublishedCommit)
open Dregg2.Circuit.DescriptorIR2
  (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Lookup memLog mapLog memOpsOf mapOpsOf opRow)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.OodColumnLayout (oodBatchResidual hood_of_oodColumnLayout)
open Dregg2.Circuit.LogUpColumnLayout (BusModelOk busModel_forces_lookup_holds mem_lookupsInto)
open Dregg2.Circuit.AlgoStarkSoundTransferV3 (FriLdtExtractV3)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §0 — Acceptance at the deployed verifier (the shared antecedent). -/

/-- Acceptance of batch `(pi, π)` by the specified deployed verifier — `verifyAlgo` at
`fullChecks core A toNat params.powBits` (the shape `verifyAlgo_accept_forces_table_identity`
and hence the whole OOD modeler ride on). -/
abbrev AcceptsFull
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (pi : BatchPublicInputs) (π : BatchProof) : Prop :=
  verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN (view pi π).1 (view pi π).2 = true

/-! ## §1 — THE THREE RESIDUAL BUNDLES, ∀ d (each a Prop over the Skolemized extracted trace
`tr : BatchPublicInputs → BatchProof → VmTrace` — the FRI extractor's output as data, so the
FRI bundle, the bus family, and the memory legs can be SEPARATE hypotheses about the SAME
per-batch trace). -/

/-- **`FriLdtExtract d`** — the FRI-LDT-@-deployed extraction bundle for ANY descriptor: the
∀-d form of `FriLdtExtractV3`'s FRI-geometry payload. Per accepting batch it delivers the OOD
point ζ, the RLC challenge Λ, the per-constraint quotients `qp`, the batched table opening with
its Merkle recompute data, the GENERAL column-layout equation (over
`OodColumnLayout.oodBatchResidual d` — the modeler's batching polynomial, NOT a per-descriptor
hand-model), the honest FS ε-form non-exceptionality of Λ and ζ, and the published-commit link.
Contains NO `hood`, NO `MainAirAcceptF`, NO `hbus` — those are DERIVED downstream. -/
def FriLdtExtract
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    ∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      -- FRI geometry / opening structure:
      (tr pi π).rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = [ood] ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      -- commitment recompute data (feeds the `Poseidon2SpongeCR` binding):
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      -- THE GENERAL COLUMN-LAYOUT equation (+ BabyBear→ℤ bridge), over the MODELER's batching
      -- polynomial for `d`'s ACTUAL arith layout:
      (oodBatchResidual d (tr pi π) ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      -- FS non-exceptionality of Λ (honest ε-form; `rlc_debatch`'s precondition):
      Λ ∉ exceptionalSet (oodBatchResidual d (tr pi π) ζ qp) ∧
      -- FS non-exceptionality of ζ, per arith constraint (honest ε-form of `hnonexc`):
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly d (tr pi π) c
                - vanishingPoly (tr pi π) * qp c)) ∧
      -- the published-commitment link (deployment fact):
      tracePublishedCommit (tr pi π) = pi.toPublished

/-- **`BusModelFamily d`** — per accepting batch, every lookup `d` declares has a sound
extracted LogUp bus (`LogUpColumnLayout.BusModelOk` at that lookup's table: pole-freeness,
the gate-forced balance, challenge non-exceptionality, distinct looked-up support, fingerprint
faithfulness on the supports — the NAMED FS side conditions, none new). -/
def BusModelFamily {F : Type*} [Field F] [DecidableEq F]
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
      ∃ mult : List ℕ, BusModelOk fp embed d (tr pi π) l.table mult

/-- **`MemoryLegs d`** — THE per-effect input: per accepting batch, a declared memory boundary
(`minit`/`mfin`/`maddrs`) together with (i) the non-lookup non-arith constraint arm — the
memOp/mapOp/umemOp/proofBind row denotations — and (ii) the six memory/map-table legs
(`Nodup` boundary, address closure, `Disciplined`, `MemCheck` multiset balance, and the two
table-assembly faithfulness equations). Everything else the class needs is floor or modeler. -/
def MemoryLegs
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
      (∀ i < (tr pi π).rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
          (∀ l : Lookup, c ≠ VmConstraint2.lookup l) →
          c.holdsAt hash (tr pi π).tf (envAt (tr pi π) i) (i == 0)
            (i + 1 == (tr pi π).rows.length)) ∧
      maddrs.Nodup ∧
      (∀ op ∈ memLog d (tr pi π), op.addr ∈ maddrs) ∧
      MemoryChecking.Disciplined (memLog d (tr pi π)) ∧
      MemoryChecking.MemCheck minit mfin maddrs (memLog d (tr pi π)) ∧
      (tr pi π).tf .memory = (memLog d (tr pi π)).map opRow ∧
      (tr pi π).tf .mapOps = mapLog d (tr pi π)

/-- **`MemMapFree`** — per accepting batch, the extracted trace's aux memory/map tables are
empty (the assembly fact a mem/map-free effect's bundle carries; `FriLdtExtractV3` carries
exactly these two conjuncts). -/
def MemMapFree
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    (tr pi π).tf .memory = [] ∧ (tr pi π).tf .mapOps = []

/-! ## §2 — THE `hbus` ARM FROM THE BUS MODELER, split for descriptors WITH memory legs.

`LogUpColumnLayout.hbus_of_busModels` discharges the whole non-arith arm for the all-lookup
(graduated) shape. Descriptors that also declare memOp/mapOp/umemOp/proofBind constraints have
non-arith non-lookup arms; this split sends every `.lookup` through the ∀-d bus modeler
(`busModel_forces_lookup_holds`) and routes ONLY the genuinely non-bus arms to the memory-legs
input. -/

/-- **The non-arith arm, assembled (∀ d): lookups from the BUS MODELER, the rest from the
memory legs.** No `hbus` is assumed anywhere: the `.lookup` case IS
`busModel_forces_lookup_holds` — a balancing, non-exceptional, faithfully-fingerprinted
extracted bus FORCES the membership. -/
theorem nonArithArm_of_busModels {F : Type*} [Field F] [DecidableEq F]
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (hok : ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        ∃ mult : List ℕ, BusModelOk fp embed d t l.table mult)
    (hrest : ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
        (∀ l : Lookup, c ≠ VmConstraint2.lookup l) →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi c hc hA
  cases c with
  | lookup l =>
      obtain ⟨mult, hm⟩ := hok l hc
      exact busModel_forces_lookup_holds fp embed d t l.table mult hm i hi l
        (mem_lookupsInto.mpr ⟨hc, rfl⟩)
  | base c₀ => exact hrest i hi _ hc hA (fun _ h => nomatch h)
  | windowGate w => exact hrest i hi _ hc hA (fun _ h => nomatch h)
  | memOp m => exact hrest i hi _ hc hA (fun _ h => nomatch h)
  | mapOp m => exact hrest i hi _ hc hA (fun _ h => nomatch h)
  | umemOp m => exact hrest i hi _ hc hA (fun _ h => nomatch h)
  | proofBind m => exact hrest i hi _ hc hA (fun _ h => nomatch h)

/-! ## §3 — ★ THE GENERAL ASSEMBLER: `AlgoStarkSound` for ANY `d`, per-effect inputs =
{memory legs} only; `hood`/`hbus`/`MainAirAcceptF` discharged from the modelers. -/

/-! **⚑ DELETED 2026-07-25 — `algoStarkSound_of_memoryLegs`.** It was the ∀-d assembler taking
`FriLdtExtract … d` in its FRI slot. That bundle is PROVED to force `CircuitSoundness.verifyBatch`
to reject EVERY input at the deployed `cfg*` arguments
(`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`,
`PremiseInhabitability.friLdtExtract_empties_deployed`), so this assembler and everything assembled
through it quantified over an EMPTY accepting set and was VACUOUSLY true.

Its replacement is `ApexOodLaneRepair.algoStarkSound_of_memoryLegs_cons` — the same statement with
`FriLdtExtractCons` (`oodPoint = ood :: oodRest`, the shape `FriVerifier.batchTablesCheck` matches at
`FriVerifier.lean:805`) in the FRI slot, every other input reused unchanged. It is NOT a weaker
theorem: `ApexOodLaneRepair.friLdtExtractCons_iff_noOodShape` proves the corrected bundle EQUIVALENT
to itself with the OOD conjunct deleted, because acceptance itself supplies the cons shape
(`acceptsFull_gives_cons_shape`) — so the corrected premise adds exactly ZERO strength and cannot
empty anything.

NO TWIN IS KEPT. A caller still holding the old bundle composes `ApexOodLaneRepair.friLdtExtract_imp_cons`
(a real implication) — but note that doing so buys nothing, since the old bundle is empty at deployed
args. `FriLdtExtract` the DEFINITION is deliberately retained below as the SUBJECT of the vacuity
theorems, so the broken shape cannot be reintroduced silently. -/

/-! ## §4 — the MEM/MAP-FREE corollary: no memory-leg input at all. -/

/-- No memOp constraints under the all-lookup non-arith shape. -/
theorem memOpsOf_eq_nil_of_lookupShape (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l) :
    memOpsOf d = [] := by
  unfold memOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  cases c with
  | memOp m =>
      obtain ⟨l, hl⟩ := hshape _ hc (fun h => h)
      exact absurd hl (fun h => nomatch h)
  | base c₀ => rfl
  | windowGate w => rfl
  | lookup l => rfl
  | mapOp m => rfl
  | umemOp m => rfl
  | proofBind m => rfl

/-- No mapOp constraints under the all-lookup non-arith shape. -/
theorem mapOpsOf_eq_nil_of_lookupShape (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l) :
    mapOpsOf d = [] := by
  unfold mapOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  cases c with
  | mapOp m =>
      obtain ⟨l, hl⟩ := hshape _ hc (fun h => h)
      exact absurd hl (fun h => nomatch h)
  | base c₀ => rfl
  | windowGate w => rfl
  | lookup l => rfl
  | memOp m => rfl
  | umemOp m => rfl
  | proofBind m => rfl

/-- The memory log of an all-lookup-shaped descriptor is empty on EVERY trace. -/
theorem memLog_eq_nil_of_lookupShape (d : EffectVmDescriptor2) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l) :
    memLog d t = [] := by
  unfold memLog
  rw [memOpsOf_eq_nil_of_lookupShape d hshape]
  simp

/-- The map-ops log of an all-lookup-shaped descriptor is empty on EVERY trace. -/
theorem mapLog_eq_nil_of_lookupShape (d : EffectVmDescriptor2) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l) :
    mapLog d t = [] := by
  unfold mapLog
  rw [mapOpsOf_eq_nil_of_lookupShape d hshape]
  simp

/-- **The memory legs of a mem/map-free effect are STRUCTURAL** — under the all-lookup shape
(rfl per effect) and the two aux-table-emptiness assembly facts, the whole `MemoryLegs` input
is derived: empty boundary, empty log, `MemCheck` reading `0 = 0`. -/
theorem memoryLegs_of_lookupShape
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l)
    (hfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    MemoryLegs hash perm RATE toNat params vk core A initState logN view tr d := by
  intro pi π hacc
  obtain ⟨hMem, hMap⟩ := hfree pi π hacc
  refine ⟨fun _ => 0, fun _ => (0, 0), [], ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- the non-lookup non-arith arm is VACUOUS: every non-arith constraint is a lookup
    intro i _ c hc hA hne
    obtain ⟨l, rfl⟩ := hshape c hc hA
    exact absurd rfl (hne l)
  · intro op hop
    rw [memLog_eq_nil_of_lookupShape d (tr pi π) hshape] at hop
    simp at hop
  · rw [memLog_eq_nil_of_lookupShape d (tr pi π) hshape]; trivial
  · rw [memLog_eq_nil_of_lookupShape d (tr pi π) hshape]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  · rw [memLog_eq_nil_of_lookupShape d (tr pi π) hshape, List.map_nil]; exact hMem
  · rw [mapLog_eq_nil_of_lookupShape d (tr pi π) hshape]; exact hMap

/-! **⚑ DELETED 2026-07-25 — `algoStarkSound_of_memoryFree`.** The mem/map-free corollary of the
deleted `algoStarkSound_of_memoryLegs`, carrying the same EMPTY `FriLdtExtract … d` premise.
Replacement: `ApexOodLaneRepair.algoStarkSound_of_memoryFree_cons` (identical statement over
`FriLdtExtractCons`; `memoryLegs_of_lookupShape`, retained above, is still its `MemoryLegs` input).
Same zero-added-strength receipt as above (`friLdtExtractCons_iff_noOodShape`). -/

/-! ## §5 — ★ transferV3 SUBSUMED. -/

/-! **⚑ DELETED 2026-07-25 — `algoStarkSound_transferV3_ofBusModels`.** The deployed-`transferV3`
specialization of the deleted `algoStarkSound_of_memoryFree`, carrying the same EMPTY
`FriLdtExtract … transferV3` premise — i.e. the apex instance at the deployed descriptor was
vacuously true. Replacement: `ApexOodLaneRepair.algoStarkSound_transferV3_ofBusModels_cons`, which
discharges the same per-effect side conditions (`hbus_is_lookup`, `transferV3_hashSites`,
`transferV3_ranges`) over `FriLdtExtractCons … transferV3`. -/

/-- **The hand-wired `algoStarkSound_transferV3`, RE-DERIVED through the general modeler** —
the EXACT statement of `AlgoStarkSoundTransferV3.algoStarkSound_transferV3`, with the
`hood`/`MainAirAcceptF` wiring now the ∀-d `hood_of_oodColumnLayout` (the template's §3
`hood_of_reductions`/`mainAirAcceptF_of_floor` chain, subsumed; the bundle's hand-stated
layout equation IS the general `oodBatchResidual transferV3` equation definitionally).

THE NAMED GAP: this is NOT literally `algoStarkSound_of_memoryFree transferV3` applied to
`FriLdtExtractV3`, because `FriLdtExtractV3`'s bus slot carries the POST-discharge LogUp arm
(`hbus : … c.holdsAt …`) while the general residual carries the PRE-discharge `BusModelOk`
family, and the proven arrow (`busModel_forces_lookup_holds`) only runs bus ⟹ arm. The
general instance with the modeled bus is `algoStarkSound_transferV3_ofBusModels` above; closing
the gap = restating the deployed bundle with `BusModelOk` in its bus slot (an edit to the
read-only template, out of this lane's charter). -/
theorem algoStarkSound_transferV3_subsumed
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3 sponge hash perm RATE toNat params vk core A initState logN view) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  Dregg2.Circuit.AlgoStarkSoundInstance.algoStarkSound_of_bricks_transferV3
    hash perm RATE toNat params vk (fullChecks core A toNat params.powBits) initState logN view
    (by
      intro pi π hacc
      obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
        hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc,
        hbus, hMem, hMap, hPub⟩ := hfri pi π hacc
      refine ⟨t, ?_, hbus, hMem, hMap, hPub⟩
      -- the bundle's hand-stated layout equation feeds the GENERAL modeler definitionally
      -- (`oodBatchResidual transferV3 = batchResidual (Rfam transferV3 …)` is `rfl`):
      exact ood_forces_mainAirAccept_field_of_residuals transferV3 t hcap ζ qp
        (hood_of_oodColumnLayout transferV3 sponge hCR perm RATE toNat params vk core A
          initState logN (view pi π).1 (view pi π).2 hacc t ζ Λ qp topen ood vCommitted root
          idx siblings hoodPt hmem hCommitted hOpened hlayout hLam)
        hnonexc)

/-! ## §6 — THE FAN-OUT RECEIPT: per-effect obligations at the deployed descriptor are
mechanical (rfl + the committed shape brick). What remains per effect for a mem/map-free
descriptor is EXACTLY this triple — everything else is floor or ∀-d modeler. -/

/-- The whole per-effect side-condition package of `algoStarkSound_of_memoryFree` at the
deployed `transferV3`, discharged with NO new proof work. -/
theorem transferV3_sideConditions_mechanical :
    (transferV3.hashSites = [] ∧ transferV3.ranges = []) ∧
      (∀ c ∈ transferV3.constraints, ¬ isArith c →
        ∃ l : Lookup, c = VmConstraint2.lookup l) :=
  ⟨⟨rfl, rfl⟩, Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup⟩

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms nonArithArm_of_busModels
#assert_axioms memOpsOf_eq_nil_of_lookupShape
#assert_axioms mapOpsOf_eq_nil_of_lookupShape
#assert_axioms memLog_eq_nil_of_lookupShape
#assert_axioms mapLog_eq_nil_of_lookupShape
#assert_axioms memoryLegs_of_lookupShape
#assert_axioms algoStarkSound_transferV3_subsumed
#assert_axioms transferV3_sideConditions_mechanical

end Dregg2.Circuit.AlgoStarkSoundGeneral
