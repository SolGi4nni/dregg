/-
# `Dregg2.Circuit.AlgoStarkSoundFanoutMemory` — the KERNEL STARK-SOUNDNESS FAN-OUT to the 7
MEMORY-TOUCHING (mapOp) EFFECTS: `algoStarkSound_<effect>` for noteSpend / noteCreate /
createCell / createCellFromFactory / spawn (+ spawnWrite) / refusal / heapWrite, each ONE
invocation of the general assembler `ApexOodLaneRepair.algoStarkSound_of_memoryLegs_cons` with
its `MemoryLegs` input ASSEMBLED from the MapOps-AIR modeler (`MapOpsColumnLayout`), never
re-assumed. (SetFieldDyn — the sole `.memOp` effect — is OUT OF SCOPE here; its leg load-bears
the named-open higher-order-pole LogUp extension, `docs/SUPERSEDED/MEMORY-LEGS-SCOPE.md` §4.)

## ⚑ MIGRATED OFF THE EMPTY PREMISE (2026-07-25)

Every `hfri` in this file was `AlgoStarkSoundGeneral.FriLdtExtract`, whose OOD conjunct
`oodPoint = [ood]` is REFUTED on every accepting run — `ApexOodLaneRepair.
friLdtExtract_makes_verifyBatch_reject_everything` proves that premise forces
`CircuitSoundness.verifyBatch` to reject EVERY input, so all ten statements below were vacuously
true. They now take `ApexOodLaneRepair.FriLdtExtractCons` (`oodPoint = ood :: oodRest`, the shape
`FriVerifier.batchTablesCheck` actually matches at `FriVerifier.lean:805`) and route through
`algoStarkSound_of_memoryLegs_cons`. ⚑ 2026-07-30: the line that stood here — "nothing is lost,
`friLdtExtract_imp_cons` sends the old premise into the new one" — is FALSE now and is corrected
rather than left. That implication is DELETED: `FriLdtExtractCons` gained the per-run opening
residual `¬ OpeningColl` and the landed bundle never carried it. Nothing is lost anyway, because
the old premise is one this tree PROVES makes `verifyBatch` reject every input. Nothing is silently re-emptied: §7 instantiates the `_iff_noOodShape` receipt at each
of the eight deployed descriptors — the corrected premise is EQUIVALENT to itself with the OOD
conjunct deleted, so the repair contributes exactly zero strength and cannot be the reason any
premise is empty. What it does NOT establish is satisfiability of the remaining conjuncts (the
FRI-LDT/Merkle extraction) at the deployed `opaque` `cfg*` arguments — that is the untouched FRI
floor, and one retained conjunct (`topen ∈ tableOpenings`) is refutable at the toy accepting pole
(`docs/WOUND-apex-premise-vacuity-2026-07-24.md` §2), so no accepting model of the corrected
bundle is exhibited anywhere.

## HONEST SCOPE (first sentence)

Per effect, the residual `Prop` hypotheses of `algoStarkSound_<effect>` are EXACTLY

  1. `Poseidon2SpongeCR hash` — the constraint-semantics hash floor, still carried by the map-op
     arm (`mapOpsArm_of_modeler` APPLIES it, so it is an ENDPOINT, not a threader).
     ⛑ 2026-07-30: the FRI-commitment instance `Poseidon2SpongeCR sponge` is GONE from every
     statement in this file — `ApexOodLaneRepair.FriLdtExtractCons` now carries the one per-run
     Merkle-opening residual that binder used to buy. The `hash` instance is NOT ported and these
     theorems REMAIN floor carriers on its account; that is the honest state, named rather than
     rounded off, and it is the control for the sponge-side port (if these cleared too, the gate
     would have stopped measuring rather than the tree improved);
  2. `FriLdtExtractCons … <descriptor>` — the ∀-d FRI-LDT-@-deployed extraction bundle at the
     CORRECTED cons-shaped OOD point (`ApexOodLaneRepair`; see the migration note above);
  3. `BusModelFamily … <descriptor>` — the per-used-table LogUp bus models;
  4. `MapReconcileFamily … <descriptor>` — NAMED (NEW here, per-effect): per accepting batch,
     the deployed `Ir2Air::MapOps` AIR's accepted reconcile gate data
     (`MapOpsColumnLayout.MapReconcileModelOk`) for every fired declared map op. This CARRIES
     the knowledge-extraction premise inside `ReconcileGatesAt` (the prover's committed
     `CanonicalHeapTree` behind the row's pre-root column — MEMORY-LEGS-SCOPE §3's honest crux,
     option (i)); what the modeler then DERIVES is that the row's `(root, key, value, new_root)`
     columns cannot lie about that heap (`mapOpsArm_of_modeler` — a lie is a Poseidon2 collision);
  5. `MapTableAssembly … <descriptor>` — NAMED (the SPECIES-B carried fact, the exact analog of
     transferV3's aux-table-emptiness pair `AirLegsDischarged.lean:30-35`): the committed memory
     table is EMPTY (none of the 7 declares a mem op) and the committed mapOps table IS the
     gathered `mapLog` (`mapTableFaithful`) — a table-ASSEMBLY fact, not an AIR consequence;
     carried, not laundered.

Everything else is DERIVED, ∀ d, with NO per-effect proof work:
  * `MainAirAcceptF` / `hood` — the OOD column-layout modeler at the cons shape (inside
    `algoStarkSound_of_memoryLegs_cons`, via `hood_of_oodColumnLayout_cons`);
  * the `.lookup` non-arith arm — the LogUp bus modeler (`busModel_forces_lookup_holds`);
  * the `.mapOp` non-arith arm — the MapOps-AIR modeler (`mapOpsArm_of_modeler`), routed through
    the `MemoryLegs` catch-all arm here (`memoryLegs_of_mapShape`);
  * the five Blum memory legs (`Nodup`/closure/`Disciplined`/`MemCheck`/`memTableFaithful`) —
    STRUCTURAL over the empty mem log (`memOpsOf <descriptor> = []`, itself DERIVED from the
    shape lemma, not asserted);
  * the graduated column shape (`hashSites = []` / `ranges = []`) — `rfl` per effect.

The per-effect content is ONE lemma each: the SHAPE fact (`<descriptor>_shape`) that every
non-arith constraint is a `.lookup` or a `.mapOp` — proved from `constraints_graduateV1_shapes`
plus the descriptor's literal append list (and, for refusal, the H1 headroom-pin wrap whose
appends are `.base` pins). The per-effect arithmetic teeth
(`*_grow_gate_forces_set_insert` / `*_forces_write` / `heapWrite_splice_forced`) are NOT inputs
here and are NOT re-proved: they consume `Satisfied2` DOWNSTREAM of these instances exactly as
before — the fan-out gives them the STARK-sound trace to bite on.

## Discipline

Sorry-free; no carrier props beyond the five NAMED residuals above; no `decide`/`Fintype` over
`|F|`-sized objects; BabyBear arithmetic never computed; the `2^16` heap never constructed
(everything rides `MapOpsColumnLayout`'s symbolic depth). NEW file; imports read-only; builds
targeted (`lake build Dregg2.Circuit.AlgoStarkSoundFanoutMemory`).
-/
import Dregg2.Circuit.AlgoStarkSoundGeneral
import Dregg2.Circuit.ApexOodLaneRepair
import Dregg2.Circuit.MapOpsColumnLayout
import Dregg2.Circuit.RotatedKernelRefinementExercise

namespace Dregg2.Circuit.AlgoStarkSoundFanoutMemory

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith fullChecks)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral (AcceptsFull BusModelFamily MemoryLegs)
open Dregg2.Circuit.ApexOodLaneRepair
  (FriLdtExtractCons FriLdtExtractConsNoOodShape algoStarkSound_of_memoryLegs_cons
   friLdtExtractCons_iff_noOodShape)
open Dregg2.Circuit.MapOpsColumnLayout
  (MapReconcileModelOk mapOpsArm_of_modeler memLog_nil_of_no_memOps)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 constraints_graduateV1_shapes)
open Dregg2.Circuit.Emit
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitHeapRoot (heapWriteSpliceVmDescriptor)
open Dregg2.Circuit.RotatedKernelRefinementExercise (heapWriteV3 heapSpliceWriteOp)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §0 — THE TWO NAMED PER-EFFECT RESIDUAL BUNDLES (over the Skolemized extracted trace,
exactly the `AlgoStarkSoundGeneral` §1 style). -/

/-- **`MapReconcileFamily d`** — NAMED per-effect deployed-modeling premise: per accepting
batch, every fired declared `.mapOp` row has accepted map-reconcile gate data
(`MapOpsColumnLayout.ReconcileGatesAt` at the deployed `MAP_TREE_DEPTH`) — what the deployed
`Ir2Air::MapOps` AIR checks (`circuit/src/descriptor_ir2.rs:2213`,
`heap_root.rs::CanonicalHeapTree`). Contains the knowledge-extraction premise (the prover's
committed canonical heap behind the pre-root column — MEMORY-LEGS-SCOPE §3, option (i)); the
modeler DERIVES from it that the row columns cannot lie (`mapOpsArm_of_modeler`). The `.mapOp`
analog of `BusModelFamily`. -/
def MapReconcileFamily
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    MapReconcileModelOk hash d (tr pi π)

/-- **⚑⚑ `MapDenotationFamily d` — THE APEX PREMISE, AS OF 2026-07-30, AND IT IS INHABITED.**

Per accepting batch, every declared `.mapOp` row DENOTES: the deployed row denotation
`DescriptorIR2.MapOp.holdsAt` holds, at the arity-3 indexed-Merkle commitment `heap_root.rs`
computes.

**Why this replaced `MapReconcileFamily` in the memory legs.** That one delivers
`MapReconcileModelOk` — "the arity-2 map-reconcile GATES accepted". The legs need the row
DENOTATION, and until tonight the two were the same object, so `mapOp_holds_of_mapReconcile` bridged
them. The denotation moved onto the deployed commitment; the arity-2 gates provably do not force it
(`MapReconcileImtRepoint.imtRoot_ne_mapRoot`), the bridge is DELETED, and — the part that matters —
`MapReconcileImtRepoint.old_model_is_false_on_deployed_rows` proves `MapReconcileModelOk` is FALSE on
the rows the deployed prover produces. **An apex whose premise is false on every real trace concludes
nothing about any real turn.** That was the vacuity.

This premise is not false there. `MapDenotationCutoverCheck.deployed_opensTo_inhabited` exhibits a
witness of the underlying denotation at the DEPLOYED depth, the DEPLOYED sparse occupancy and the
DEPLOYED sentinel, for an arbitrary hash and with no floor.

⚠ **Say what it is at its real resolution.** This is a MODELLER premise, the same species as
`BusModelFamily` — it is *assumed* here and *discharged* by the arity-3 gate laws in
`MapKindImtGates` / the `mapOpsArmImt*_of_modeler` family, which sit below this module. Two of the
five kinds cannot be discharged from the deployed AIR at all, and neither is a Lean defect:
`.insert` (op=3) constrains only the post-root — and is emitted by ZERO deployed descriptors — and
`.aafiInsert`'s POST side folds the physical append-order layout, which
`no_schema_commits_the_append_order_layout` shows no `MapLeafSchema` commits. Both are Rust-side. -/
def MapDenotationFamily
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    Dregg2.Circuit.MapOpsColumnLayout.MapDenotationModelOk hash d (tr pi π)

/-- **`MapTableAssembly d`** — the NAMED SPECIES-B carried fact (the mapOp-effect analog of
transferV3's `MemMapFree` emptiness pair, same epistemic classification as
`AirLegsDischarged.lean:30-35`): per accepting batch, (i) the committed memory table is EMPTY
(the descriptor declares no mem ops) and (ii) `mapTableFaithful` — the committed mapOps table IS
the gathered `mapLog d`. A table-ASSEMBLY fact about the deployed trace commitment, not an AIR
arithmetic consequence; carried NAMED, never derived-by-fiat. -/
def MapTableAssembly
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    (tr pi π).tf .memory = [] ∧ (tr pi π).tf .mapOps = mapLog d (tr pi π)

/-! ## §1 — THE SHAPE HELPERS (∀ base descriptor): every non-arith constraint of a
"graduated ++ mapOps" descriptor is a `.lookup` or a `.mapOp`. The 7 effects' entire per-effect
obligation reduces to ONE `rfl` application of these. -/

/-- Shape of `{graduateV1 d0 with constraints ++ ms.map .mapOp}`: graduated constraints are
`.base` (arith) or `.lookup`; the appends are `.mapOp`s. -/
theorem shape_of_graduated_append (d2 : EffectVmDescriptor2)
    (d0 : EffectVmDescriptor) (ms : List MapOp)
    (heq : d2.constraints
      = (graduateV1 d0).constraints ++ ms.map VmConstraint2.mapOp) :
    ∀ c ∈ d2.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) := by
  intro c hc hA
  rw [heq] at hc
  rcases List.mem_append.mp hc with hbase | happ
  · rcases constraints_graduateV1_shapes _ c hbase with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
    · exact absurd (show isArith (VmConstraint2.base c₀) from trivial) hA
    · exact Or.inl ⟨l, rfl⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp happ
    exact Or.inr ⟨m, rfl⟩

/-- Shape of the H1-headroom-pinned form (`refusalFieldsWriteV3`'s base): the wrap appends only
`.base .piBinding` pins (arith), so the non-arith shape is unchanged. -/
theorem shape_of_pinned_graduated_append (d2 : EffectVmDescriptor2)
    (d0 : EffectVmDescriptor) (ms : List MapOp)
    (heq : d2.constraints
      = (withRecordPin8Headroom2 (graduateV1 d0)).constraints ++ ms.map VmConstraint2.mapOp) :
    ∀ c ∈ d2.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) := by
  intro c hc hA
  rw [heq] at hc
  rcases List.mem_append.mp hc with hbase | happ
  · rw [withRecordPin8Headroom2_constraints] at hbase
    rcases List.mem_append.mp hbase with hgrad | hpin
    · rcases constraints_graduateV1_shapes _ c hgrad with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
      · exact absurd (show isArith (VmConstraint2.base c₀) from trivial) hA
      · exact Or.inl ⟨l, rfl⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hpin
      exact absurd (show isArith (VmConstraint2.base _) from trivial) hA
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp happ
    exact Or.inr ⟨m, rfl⟩

/-- Under the lookup-or-mapOp shape a descriptor declares NO mem ops (a `.memOp` is non-arith
but neither) — the mem-op-emptiness is DERIVED from the shape, never asserted per effect. -/
theorem memOpsOf_eq_nil_of_mapShape (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m)) :
    memOpsOf d = [] := by
  unfold memOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  cases c with
  | memOp m =>
      rcases hshape _ hc (fun h => h) with ⟨l, hl⟩ | ⟨m', hm⟩
      · exact absurd hl (fun h => nomatch h)
      · exact absurd hm (fun h => nomatch h)
  | base c₀ => rfl
  | windowGate w => rfl
  | lookup l => rfl
  | mapOp m => rfl
  | umemOp m => rfl
  | proofBind m => rfl

/-! ## §2 — THE MEMORY-LEGS ASSEMBLER for the 7-effect shape: the `.mapOp` arm from the MapOps
modeler, the five Blum legs structural over the (derived-)empty mem log, `mapTableFaithful`
from the NAMED assembly fact. `MemoryLegs` is ASSEMBLED here, not re-assumed. -/

/-- **`memoryLegs_of_mapShape`** — for any descriptor of the lookup-or-mapOp shape, the whole
`MemoryLegs` input of the general assembler is built from {the MapOps-AIR modeler's arm +
`MapTableAssembly`}: the non-lookup non-arith arm IS `mapOpsArm_of_modeler` (each `.mapOp` row
denotation forced through the CR path-binding law), the five memory legs are structural over the
empty mem log, and the two faithfulness legs are the named assembly conjuncts. -/
theorem memoryLegs_of_mapShape
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr d)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr d) :
    MemoryLegs hash perm RATE toNat params vk core A initState logN view tr d := by
  have hNoMem : memOpsOf d = [] := memOpsOf_eq_nil_of_mapShape d hshape
  intro pi π hacc
  obtain ⟨hMemE, hMapTF⟩ := hasm pi π hacc
  have hMemLog : memLog d (tr pi π) = [] := memLog_nil_of_no_memOps d (tr pi π) hNoMem
  refine ⟨fun _ => 0, fun _ => (0, 0), [], ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- the non-lookup non-arith arm: by the shape it is a `.mapOp`, and the MapOps-AIR modeler
    -- forces its row denotation (the ONLY non-structural content of the memory legs):
    intro i hi c hc hA hne
    rcases hshape c hc hA with ⟨l, rfl⟩ | ⟨m, rfl⟩
    · exact absurd rfl (hne l)
    · exact mapOpsArm_of_modeler hash d (tr pi π) (hrec pi π hacc) i hi m hc
  · intro op hop
    rw [hMemLog] at hop
    simp at hop
  · rw [hMemLog]; trivial
  · rw [hMemLog]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  · rw [hMemLog, List.map_nil]; exact hMemE
  · exact hMapTF

/-! ## §3 — THE ∀-d FAN-OUT ASSEMBLER: `AlgoStarkSound` for any lookup-or-mapOp descriptor,
residual = {the named floor ×2, `FriLdtExtractCons d`, `BusModelFamily d`, `MapReconcileFamily d`,
`MapTableAssembly d`}. -/

/-- **`algoStarkSound_of_mapShape`** — the general assembler at the 7-effect shape:
`ApexOodLaneRepair.algoStarkSound_of_memoryLegs_cons` with its `MemoryLegs` input assembled by
`memoryLegs_of_mapShape`. Nothing per-effect remains but the shape lemma and two `rfl`s.

MIGRATED (2026-07-25) off `AlgoStarkSoundGeneral.algoStarkSound_of_memoryLegs`/`FriLdtExtract`,
whose OOD conjunct `oodPoint = [ood]` is REFUTED on accepting runs
(`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`); the FRI premise is now
`FriLdtExtractCons` at the `ood :: oodRest` shape `FriVerifier.batchTablesCheck` matches. The
premise is the corrected bundle (the transport `friLdtExtract_imp_cons` is DELETED as of 2026-07-30
along with the residual it could not supply), and its OOD conjunct is implied by its own antecedent
(`fanout_correctedPremise_adds_no_strength` below). -/
theorem algoStarkSound_of_mapShape {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr d)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr d)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr d) :
    AlgoStarkSound hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memoryLegs_cons d sponge hash fp embed perm RATE toNat params vk core A
    initState logN view tr hsites hranges hfri hbusF
    (memoryLegs_of_mapShape hash hCRh perm RATE toNat params vk core A initState logN view tr d
      hshape hrec hasm)

/-! ## §4 — THE PER-EFFECT SHAPE LEMMAS (the ENTIRE per-effect obligation, each one `rfl`-fed). -/

set_option maxRecDepth 8192 in
/-- noteSpend: graduated nullifier-pin base ++ the freshness `.absent` + set-insert `.insert`.

`maxRecDepth` bump (below): the proof is `rfl`-fed through `shape_of_graduated_append`, and this
descriptor's constraint list grew past the default whnf budget — the same idiom the sibling fan-out
already uses (`AlgoStarkSoundFanoutSetField.lean:740`). Without it the module is RED at HEAD and, worse,
the error recovery leaves `algoStarkSound_noteSpend` and `fanout_sideConditions_mechanical` reported as
depending on non-kernel axioms — a faked-green leak into keystones, which is why this is a soundness fix
and not merely a build fix. -/
theorem noteSpendV3_shape :
    ∀ c ∈ noteSpendV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append noteSpendV3
    (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
    [nullifierFreshOp, nullifierInsertOp, spendAncestorFreshOp] rfl

/-- noteCreate: graduated commitment-key-pin base ++ the single commitments `.insert`. -/
theorem noteCreateV3_shape :
    ∀ c ∈ noteCreateV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append noteCreateV3
    (rotateV3WithCommitmentKeyPin EffectVmEmitNoteCreate.noteCreateVmDescriptor)
    [commitmentsInsertOp] rfl

/-- createCell: graduated new-cell-key-pin base ++ the accounts freshness + insert pair. -/
theorem createCellV3_shape :
    ∀ c ∈ createCellV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append createCellV3
    (rotateV3WithNewCellKeyPin NEW_CELL_KEY_PARAM_COL
      EffectVmEmitCreateCell.createCellActorVmDescriptor)
    [cellsFreshOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL,
     cellsInsertOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL] rfl

/-- createCellFromFactory: same pair keyed on the derived child VK (`param1`). -/
theorem factoryV3_shape :
    ∀ c ∈ factoryV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append factoryV3
    (rotateV3WithNewCellKeyPin FACTORY_CHILD_KEY_PARAM_COL
      EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor)
    [cellsFreshOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT FACTORY_CHILD_KEY_PARAM_COL,
     cellsInsertOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
       FACTORY_CHILD_KEY_PARAM_COL] rfl

/-- spawn: same pair, spawn selector. -/
theorem spawnV3_shape :
    ∀ c ∈ spawnV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append spawnV3
    (rotateV3WithNewCellKeyPin NEW_CELL_KEY_PARAM_COL
      EffectVmEmitSpawn.spawnActorVmDescriptor)
    [cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL,
     cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL] rfl

/-- spawnWrite (the cap-write rebase of spawn): same map-op pair over the cap-write rotation. -/
theorem spawnWriteV3_shape :
    ∀ c ∈ spawnWriteV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append spawnWriteV3
    (rotateV3WithNewCellKeyPinCapWrite NEW_CELL_KEY_PARAM_COL
      EffectVmEmitSpawn.spawnActorVmDescriptor)
    [cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL,
     cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL] rfl

/-- refusal: H1-headroom-pinned graduated record-pin base ++ the single audit-slot `.write`. -/
theorem refusalFieldsWriteV3_shape :
    ∀ c ∈ refusalFieldsWriteV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_pinned_graduated_append refusalFieldsWriteV3
    (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor)
    [refusalFieldsWriteOp] rfl

/-- heapWrite: graduated splice base ++ the single always-firing heap-splice `.write`. -/
theorem heapWriteV3_shape :
    ∀ c ∈ heapWriteV3.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) :=
  shape_of_graduated_append heapWriteV3
    (rotateV3 heapWriteSpliceVmDescriptor)
    [heapSpliceWriteOp] rfl

/-! ## §5 — ★ THE FAN-OUT: `algoStarkSound_<effect>` for the 7 memory-touching effects
(+ the spawnWrite deployment variant). Each is ONE application of `algoStarkSound_of_mapShape`;
the graduated-shape side conditions discharge by `rfl`. -/

section Instances

variable {F : Type*} [Field F] [DecidableEq F]
variable (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
variable (fp : List ℤ → F) (embed : ℤ → F)
variable (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
variable (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
variable (initState : List ℤ) (logN : Nat) (view : ProofView)
variable (tr : BatchPublicInputs → BatchProof → VmTrace)

/-- **NoteSpend** — STARK-soundness at the deployed `noteSpendV3` (nullifier freshness `.absent`
+ set-insert `.insert` on limb 26). Residual = the five named bundles of the header. -/
theorem algoStarkSound_noteSpend
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      noteSpendV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      noteSpendV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      noteSpendV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      noteSpendV3) :
    AlgoStarkSound hash (fun _ => noteSpendV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape noteSpendV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr noteSpendV3_shape rfl rfl hfri hbusF hrec hasm

/-- **NoteCreate** — STARK-soundness at the deployed `noteCreateV3` (commitments `.insert`,
limb 27; append-only, no freshness tooth). -/
theorem algoStarkSound_noteCreate
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      noteCreateV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      noteCreateV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      noteCreateV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      noteCreateV3) :
    AlgoStarkSound hash (fun _ => noteCreateV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape noteCreateV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr noteCreateV3_shape rfl rfl hfri hbusF hrec hasm

/-- **CreateCell** — STARK-soundness at the deployed `createCellV3` (accounts freshness +
insert, limb 0). -/
theorem algoStarkSound_createCell
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      createCellV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      createCellV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      createCellV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      createCellV3) :
    AlgoStarkSound hash (fun _ => createCellV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape createCellV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr createCellV3_shape rfl rfl hfri hbusF hrec hasm

/-- **CreateCellFromFactory** — STARK-soundness at the deployed `factoryV3` (accounts pair keyed
on the derived child VK). -/
theorem algoStarkSound_createCellFromFactory
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      factoryV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      factoryV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      factoryV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      factoryV3) :
    AlgoStarkSound hash (fun _ => factoryV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape factoryV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr factoryV3_shape rfl rfl hfri hbusF hrec hasm

/-- **Spawn** — STARK-soundness at the deployed `spawnV3` (accounts pair, spawn selector; the
cap-handoff rides `spawnWriteV3`'s constraint wrap, not a map op — see below). -/
theorem algoStarkSound_spawn
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      spawnV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      spawnV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      spawnV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      spawnV3) :
    AlgoStarkSound hash (fun _ => spawnV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape spawnV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr spawnV3_shape rfl rfl hfri hbusF hrec hasm

/-- **Spawn (cap-write deployment variant)** — STARK-soundness at `spawnWriteV3` (the cap-write
rotation rebase carrying the SAME accounts map-op pair; the cap-tree insert is an arith/lookup
constraint wrap, so the memory legs are identical in shape). -/
theorem algoStarkSound_spawnWrite
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      spawnWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      spawnWriteV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      spawnWriteV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      spawnWriteV3) :
    AlgoStarkSound hash (fun _ => spawnWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape spawnWriteV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr spawnWriteV3_shape rfl rfl hfri hbusF hrec hasm

/-- **Refusal** — STARK-soundness at the deployed `refusalFieldsWriteV3` (audit-slot `.write` on
limb 36 at the differential-pinned constant key). -/
theorem algoStarkSound_refusal
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      refusalFieldsWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      refusalFieldsWriteV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      refusalFieldsWriteV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      refusalFieldsWriteV3) :
    AlgoStarkSound hash (fun _ => refusalFieldsWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape refusalFieldsWriteV3 sponge hash hCRh fp embed perm RATE toNat
    params vk core A initState logN view tr refusalFieldsWriteV3_shape rfl rfl hfri hbusF
    hrec hasm

/-- **HeapWrite** — STARK-soundness at the deployed `heapWriteV3` (the always-firing sorted-heap
splice `.write` on the rotated heap-root limbs). -/
theorem algoStarkSound_heapWrite
    (hCRh : Poseidon2SpongeCR hash)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
      heapWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
      heapWriteV3)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr
      heapWriteV3)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr
      heapWriteV3) :
    AlgoStarkSound hash (fun _ => heapWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape heapWriteV3 sponge hash hCRh fp embed perm RATE toNat params
    vk core A initState logN view tr heapWriteV3_shape rfl rfl hfri hbusF hrec hasm

end Instances

/-! ## §6 — THE FAN-OUT RECEIPT: the whole per-effect side-condition package (shape + the two
graduated column facts + the DERIVED mem-op emptiness) is mechanical for every one of the 7 —
exhibited with no new proof work, the `transferV3_sideConditions_mechanical` pattern. -/

/-- Every per-effect structural obligation of the fan-out, discharged in one term. -/
theorem fanout_sideConditions_mechanical :
    (noteSpendV3.hashSites = [] ∧ noteSpendV3.ranges = [] ∧ memOpsOf noteSpendV3 = []) ∧
    (noteCreateV3.hashSites = [] ∧ noteCreateV3.ranges = [] ∧ memOpsOf noteCreateV3 = []) ∧
    (createCellV3.hashSites = [] ∧ createCellV3.ranges = [] ∧ memOpsOf createCellV3 = []) ∧
    (factoryV3.hashSites = [] ∧ factoryV3.ranges = [] ∧ memOpsOf factoryV3 = []) ∧
    (spawnV3.hashSites = [] ∧ spawnV3.ranges = [] ∧ memOpsOf spawnV3 = []) ∧
    (spawnWriteV3.hashSites = [] ∧ spawnWriteV3.ranges = [] ∧ memOpsOf spawnWriteV3 = []) ∧
    (refusalFieldsWriteV3.hashSites = [] ∧ refusalFieldsWriteV3.ranges = []
      ∧ memOpsOf refusalFieldsWriteV3 = []) ∧
    (heapWriteV3.hashSites = [] ∧ heapWriteV3.ranges = [] ∧ memOpsOf heapWriteV3 = []) :=
  ⟨⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ noteSpendV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ noteCreateV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ createCellV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ factoryV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ spawnV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ spawnWriteV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ refusalFieldsWriteV3_shape⟩,
   ⟨rfl, rfl, memOpsOf_eq_nil_of_mapShape _ heapWriteV3_shape⟩⟩

/-! ## §7 — ⚑ THE MIGRATION RECEIPT: the corrected premise adds ZERO strength, at the EIGHT
deployed descriptors this file is stated at. -/

/-- **The migrated premise cannot be the reason anything here is empty.** At each of the eight
deployed descriptors, `FriLdtExtractCons` is EQUIVALENT to itself with the OOD-shape conjunct
DELETED: the conjunct is supplied by the bundle's own antecedent (`AcceptsFull` ⟹ the OOD point is
`ood :: oodRest`, since `batchTablesCheck` returns `false` on an empty one —
`ApexOodLaneRepair.acceptsFull_gives_cons_shape`). Contrast the premise this file was migrated OFF:
its singleton conjunct is CONTRADICTED by the same antecedent, which is exactly why it emptied
every statement below it. Instantiation of `ApexOodLaneRepair.friLdtExtractCons_iff_noOodShape`,
which holds `∀ d`; recorded here at the deployed descriptors so the receipt is read where the
migration happened. -/
theorem fanout_correctedPremise_adds_no_strength
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) :
    ∀ d ∈ [noteSpendV3, noteCreateV3, createCellV3, factoryV3, spawnV3, spawnWriteV3,
        refusalFieldsWriteV3, heapWriteV3],
      (FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr d
        ↔ FriLdtExtractConsNoOodShape sponge perm RATE toNat params vk core A initState logN
          view tr d) :=
  fun d _ => friLdtExtractCons_iff_noOodShape sponge perm RATE toNat params vk core A initState
    logN view tr d

/-- **The fan-out assembler from a premise that never mentions the OOD shape** — the sharpest
form of "this migration introduced no second vacuity": every `algoStarkSound_<effect>` below is
available under a FRI bundle carrying NO OOD conjunct at all, so whatever emptiness the premise may
still have is inherited ENTIRELY from the FRI-LDT / Merkle / Fiat–Shamir conjuncts (the undischarged
floor) and NONE of it from the OOD repair. -/
theorem algoStarkSound_of_mapShape_noOodShape {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hfri : FriLdtExtractConsNoOodShape sponge perm RATE toNat params vk core A initState logN
      view tr d)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d)
    (hrec : MapDenotationFamily hash perm RATE toNat params vk core A initState logN view tr d)
    (hasm : MapTableAssembly perm RATE toNat params vk core A initState logN view tr d) :
    AlgoStarkSound hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_mapShape d sponge hash hCRh fp embed perm RATE toNat params vk core A
    initState logN view tr hshape hsites hranges
    ((friLdtExtractCons_iff_noOodShape sponge perm RATE toNat params vk core A initState logN
      view tr d).mpr hfri) hbusF hrec hasm

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms fanout_correctedPremise_adds_no_strength
#assert_axioms algoStarkSound_of_mapShape_noOodShape
#assert_axioms shape_of_graduated_append
#assert_axioms shape_of_pinned_graduated_append
#assert_axioms memOpsOf_eq_nil_of_mapShape
#assert_axioms memoryLegs_of_mapShape
#assert_axioms algoStarkSound_of_mapShape
#assert_axioms noteSpendV3_shape
#assert_axioms noteCreateV3_shape
#assert_axioms createCellV3_shape
#assert_axioms factoryV3_shape
#assert_axioms spawnV3_shape
#assert_axioms spawnWriteV3_shape
#assert_axioms refusalFieldsWriteV3_shape
#assert_axioms heapWriteV3_shape
#assert_axioms algoStarkSound_noteSpend
#assert_axioms algoStarkSound_noteCreate
#assert_axioms algoStarkSound_createCell
#assert_axioms algoStarkSound_createCellFromFactory
#assert_axioms algoStarkSound_spawn
#assert_axioms algoStarkSound_spawnWrite
#assert_axioms algoStarkSound_refusal
#assert_axioms algoStarkSound_heapWrite
#assert_axioms fanout_sideConditions_mechanical

end Dregg2.Circuit.AlgoStarkSoundFanoutMemory
