/-
# `Dregg2.Circuit.AcceptanceDischarge` — DISCHARGING `kernelConfigSound`'s carried STARK-side facts.

`KernelConfigSoundness.kernelConfigSound` carries `BusModelFamily`, `MapTableAssembly` and the
`ClosureReadouts`/`WitnessDecodes` per-effect readouts as NAMED hypotheses. The scope doc
(`docs/reference/CONFIG-EVOLUTION-SOUNDNESS-SCOPE.md` §Layer-1) classifies these as
"NEEDS-A-LEMMA / NEAR-FLOOR" — provable debt that should reduce into `{Poseidon2SpongeCR, FRI-LDT}`.
This module supplies the discharge lemmas that were NAMED but never present in the tree, and — for
the ones that genuinely CANNOT be discharged from acceptance — states precisely why, and which floor
they reduce to. Nothing here re-assumes the fact it discharges: every `balanced`/`mapTableFaithful`
conjunct is EXTRACTED (from the AIR gates / the `Satisfied2` witness), the FS/SZ side conditions are
the ALLOWED floor, and the genuine residuals are named, not laundered.

## What is proved (real extraction, sorry-free)

  * **`MapTableAssembly` — FULL DISCHARGE** (`mapTableAssembly_conj_of_satisfied2`,
    `mapTableAssembly_of_satisfied2Family`). `MapTableAssembly`'s conjunction
    `t.tf .memory = [] ∧ t.tf .mapOps = mapLog d t` is LITERALLY the `Satisfied2.memTableFaithful` /
    `Satisfied2.mapTableFaithful` fields (the map half is `rfl`-equal to the field; the mem half is the
    field composed with the descriptor-shape fact `memLog d t = []`). So `MapTableAssembly` carries NO
    content beyond `Satisfied2`'s own faithfulness fields + the (rfl-per-effect) shape: it is a
    PROJECTION of the acceptance witness, hence reduces into the FRI extraction that produces the
    committed trace. It is NOT a genuine assumption beyond `{FRI-LDT}`.

  * **`BusModelFamily` — the `balanced` conjunct EXTRACTED, residual named**
    (`busModelOk_of_gates_and_floor`). `BusModelOk`'s `balanced` is DERIVED from the deployed cumsum
    AIR gates via the proven `LogUpColumnLayout.busGates_force_balance` (gates in, balance out — NOT
    re-assumed); the four remaining conjuncts (`polesA`/`polesB`/`nonexceptional`/`nodupA`/`fpFaithful`)
    are the ALLOWED FS/SZ ε floor (the Schwartz–Zippel / Poseidon2 fingerprint side conditions). See
    `busModelOk_not_from_membership` for why the SHARPER `Satisfied2 ⟹ BusModelOk` is NOT a theorem.

  * **the `WitnessDecodes` readout — the MEMBERSHIP half is a genuine consequence, the readout is
    BLOCKED at the chip-table floor** (`satisfied2_forces_declared_lookup_holds`). `Satisfied2` DOES
    force every declared `.lookup`'s membership (`Lookup.holdsAt`, a projection of `rowConstraints`).
    But the per-effect `<e>TraceReadout` additionally produces a `RotTableSide`, whose
    `chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)` conjunct — "every committed chip row
    IS a genuine permutation tuple" — is NOT forced by row-local constraint satisfaction; it is the
    table-faithfulness half of `Satisfied2Faithful`, a knowledge-extraction fact of the same class as
    `FriLdtExtract`. So the readout reduces into the chip-table-soundness (Poseidon2/FRI-extraction)
    floor, not into acceptance's row satisfaction.

## Discipline
Sorry-free; no `decide`/`Fintype` over field-sized objects (BabyBear is noncomputable — no field
`decide`); NEW file; imports read-only; builds targeted
(`lake build Dregg2.Circuit.AcceptanceDischarge`). `#assert_axioms` ⊆ Lean's own.
-/
import Dregg2.Circuit.AlgoStarkSoundFanoutMemory

namespace Dregg2.Circuit.AcceptanceDischarge

open Dregg2.Circuit.DescriptorIR2
  (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Lookup MapOp Satisfied2
   memLog mapLog memOpsOf mapOpsOf opRow)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.AlgoStarkSoundGeneral (AcceptsFull)
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory (MapTableAssembly memOpsOf_eq_nil_of_mapShape)
open Dregg2.Circuit.LogUpColumnLayout
  (BusModelOk busGates_force_balance busModel_forces_lookup_holds busColA busColB
   logupA logupBM logupB logupChallenge lookedTuples runCol runCol_zero runCol_succ
   logupColumnLayout_law)
open Dregg2.Circuit.LogUpSoundness (exceptionalSet)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false

/-! ## §1 — `MapTableAssembly` : FULL DISCHARGE from the `Satisfied2` faithfulness fields.

`MapTableAssembly d` = "per accepting batch, `t.tf .memory = [] ∧ t.tf .mapOps = mapLog d t`".
The map conjunct is `Satisfied2.mapTableFaithful` verbatim; the mem conjunct is
`Satisfied2.memTableFaithful` (`t.tf .memory = (memLog d t).map opRow`) collapsed by the descriptor
shape (`memOpsOf d = []` ⟹ `memLog d t = []`). No table-assembly premise beyond `Satisfied2`. -/

/-- Under the lookup-or-mapOp shape (rfl per mapOp effect), the gathered memory log is empty on every
trace — a projection of the descriptor's declared constraints (`memOpsOf d = []`). -/
theorem memLog_eq_nil_of_mapShape (d : EffectVmDescriptor2) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m)) :
    memLog d t = [] := by
  unfold memLog
  rw [memOpsOf_eq_nil_of_mapShape d hshape]
  simp

/-- **THE DISCHARGE (per accepting run).** From a single `Satisfied2` witness for a lookup-or-mapOp
shaped descriptor, `MapTableAssembly`'s conjunction falls out with NO further premise: the map half is
the `mapTableFaithful` field, the mem half is the `memTableFaithful` field collapsed by the shape. The
`Satisfied2` witness is EXACTLY what the STARK extraction (`StarkSound`/`AlgoStarkSound`) produces from
acceptance — so this shows `MapTableAssembly` is not content beyond that extraction. -/
theorem mapTableAssembly_conj_of_satisfied2
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    t.tf .memory = [] ∧ t.tf .mapOps = mapLog d t := by
  refine ⟨?_, hsat.mapTableFaithful⟩
  rw [hsat.memTableFaithful, memLog_eq_nil_of_mapShape d t hshape]
  rfl

/-- **THE DISCHARGE (family form).** Given the `Satisfied2` extraction that acceptance ALREADY
delivers (the `StarkSound`/`AlgoStarkSound` deliverable: per accepting batch, some memory boundary and
a `Satisfied2` witness for the SAME extracted trace), the named premise `MapTableAssembly` is FREE.
This is the honest reduction the scope doc §Layer-1.4 predicts — `MapTableAssembly` bundles into the
FRI extraction; it is never an independent assumption. -/
theorem mapTableAssembly_of_satisfied2Family
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hSat : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
      ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
        Satisfied2 hash d minit mfin maddrs (tr pi π)) :
    MapTableAssembly perm RATE toNat params vk core A initState logN view tr d := by
  intro pi π hacc
  obtain ⟨minit, mfin, maddrs, hsat⟩ := hSat pi π hacc
  exact mapTableAssembly_conj_of_satisfied2 hash d minit mfin maddrs (tr pi π) hshape hsat

/-! ## §2 — `BusModelFamily` : the `balanced` conjunct EXTRACTED from the cumsum gates; residual named.

`BusModelOk` has SIX conjuncts. Exactly ONE — `balanced` — is an AIR-forced fact: it is the deployed
cumsum column's equal-close boundary, which the proven `busGates_force_balance` turns into the bus
balance (gates in, `busBalance` out — NOT re-assumed). The other five are the FS/SZ ε side conditions
(pole-freeness, challenge non-exceptionality, distinct support, β-RLC fingerprint faithfulness) — the
ALLOWED floor, the SAME epistemic class as `FriLdtExtract`'s own FS non-exceptionality. -/

/-- **`busModelOk_of_gates_and_floor` — `BusModelOk` from {cumsum AIR gates} + {FS/SZ ε floor}.** The
`balanced` conjunct is DERIVED by `busGates_force_balance` from the deployed cumsum column gates
(first-row-zero + running-add over the extracted A/B contributions, closing equal) — the arithmetic AIR
constraints acceptance forces. The remaining conjuncts are the named FS/SZ floor. No conjunct is
re-assumed: `balanced` is EXTRACTED. This is the honest reduction of `BusModelFamily` into
`{cumsum-gate-forced balance (acceptance), Schwartz–Zippel/Poseidon2 fingerprint floor}`. -/
theorem busModelOk_of_gates_and_floor {F : Type*} [Field F] [DecidableEq F]
    (fp : List ℤ → F) (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId) (mult : List ℕ)
    (colA colB : Nat → F)
    -- the deployed cumsum AIR gates (the arithmetic constraints `Satisfied2.rowConstraints` forces):
    (h0A : colA 0 = 0)
    (hstepA : ∀ j, (h : j < (busColA fp (logupChallenge embed d t) d t tid).length) →
        colA (j + 1) = colA j + (busColA fp (logupChallenge embed d t) d t tid)[j])
    (h0B : colB 0 = 0)
    (hstepB : ∀ j, (h : j < (busColB fp (logupChallenge embed d t) t tid mult).length) →
        colB (j + 1) = colB j + (busColB fp (logupChallenge embed d t) t tid mult)[j])
    (hclose : colA (busColA fp (logupChallenge embed d t) d t tid).length
        = colB (busColB fp (logupChallenge embed d t) t tid mult).length)
    -- the ALLOWED FS/SZ ε floor (NOT `balanced` — that is extracted below):
    (hpolesA : ∀ a ∈ logupA fp d t tid, logupChallenge embed d t + a ≠ 0)
    (hpolesB : ∀ b ∈ logupB fp t tid mult, logupChallenge embed d t + b ≠ 0)
    (hnonexc : logupChallenge embed d t
        ∉ exceptionalSet (logupA fp d t tid) (logupB fp t tid mult))
    (hnodupA : (logupA fp d t tid).Nodup)
    (hfpFaithful : ∀ x ∈ lookedTuples d t tid, ∀ y ∈ t.tf tid, fp x = fp y → x = y) :
    BusModelOk fp embed d t tid mult where
  polesA := hpolesA
  polesB := hpolesB
  balanced :=
    busGates_force_balance fp (logupChallenge embed d t) d t tid mult colA colB
      h0A hstepA h0B hstepB hclose
  nonexceptional := hnonexc
  nodupA := hnodupA
  fpFaithful := hfpFaithful

/-! ### Why the SHARPER `Satisfied2 ⟹ BusModelOk` is NOT a theorem (a real finding, not debt).

`Satisfied2.rowConstraints` at a `.lookup l` yields ONLY the membership `Lookup.holdsAt` (the tuple is
in the committed table). `BusModelOk` is STRICTLY STRONGER: it is the whole extracted LogUp bus
(multiplicities, pole-freeness, the balance over `logupA`/`logupB`). The proven arrow runs
`BusModelOk ⟹ Lookup.holdsAt` (`busModel_forces_lookup_holds`); the CONVERSE fails — membership does
not reconstruct the bus. So `BusModelFamily` is genuinely UPSTREAM of `Satisfied2` (it is the input
that FORCES the lookup arm of `Satisfied2`), and cannot be recovered from `Satisfied2` alone. The
provable direction is `gates + floor ⟹ BusModelOk` above; the residual beyond acceptance is the
per-descriptor cumsum column-layout binding (which arithmetic gate is the running-add, over which
columns — a modeling artifact of the same class as the OOD `hood_of_oodColumnLayout`) plus the FS/SZ
floor. `busModel_forces_lookup_holds` is re-exported here to make the one proven direction explicit. -/
theorem busModelOk_forces_membership {F : Type*} [Field F] [DecidableEq F]
    (fp : List ℤ → F) (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId) (mult : List ℕ)
    (hok : BusModelOk fp embed d t tid mult) :
    ∀ i < t.rows.length, ∀ l ∈ Dregg2.Circuit.LogUpColumnLayout.lookupsInto d tid,
      Lookup.holdsAt t.tf (envAt t i) l :=
  busModel_forces_lookup_holds fp embed d t tid mult hok

/-! ## §3 — the `WitnessDecodes`/`<e>TraceReadout` readout: MEMBERSHIP half genuine, readout BLOCKED.

The per-effect readout `<e>TraceReadout : Satisfied2 (Rfix e) ⟹ <e>Encodes` produces a `RotTableSide`
(carrying `chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)` — every committed chip row IS
a genuine permutation tuple). `Satisfied2` forces lookup MEMBERSHIP but NOT that table faithfulness, so
the readout is not a consequence of acceptance's row satisfaction; it reduces to the chip-table
(Poseidon2/FRI-extraction) floor. What IS a genuine consequence — the membership half — is proved
here. -/

/-- **`Satisfied2` forces every declared lookup's membership.** A pure projection of
`Satisfied2.rowConstraints` at the `.lookup` arm (`VmConstraint2.holdsAt … (.lookup l) = l.holdsAt`).
This is the extent to which the readout IS a consequence of acceptance; the readout's residual
`RotTableSide.chipTableFaithful` (`ChipTableSoundN`) lies BEYOND this — the table-faithfulness half of
`Satisfied2Faithful`, a knowledge-extraction floor, not derivable from `Satisfied2`. -/
theorem satisfied2_forces_declared_lookup_holds
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    ∀ i < t.rows.length, ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
      Lookup.holdsAt t.tf (envAt t i) l := by
  intro i hi l hl
  have h := hsat.rowConstraints i hi (VmConstraint2.lookup l) hl
  simpa [VmConstraint2.holdsAt] using h

/-! ## §4 — NON-VACUITY: the discharges FIRE on concrete descriptors (extraction, not assumption). -/

section NonVacuity

/-- A concrete mapOp-declaring descriptor (guard column 1, root/key/value/newRoot on cols 2/3/4/2):
`mapOpsOf` is NON-empty, so the lookup-or-mapOp shape is genuine (not the trivial all-empty case). -/
def dMapNV : EffectVmDescriptor2 :=
  { name := "acceptance-discharge-mapnv", traceWidth := 5, piCount := 0
  , tables := []
  , constraints := [VmConstraint2.mapOp
      { guard := EmittedExpr.var 1, root := fun _ => EmittedExpr.var 2, key := EmittedExpr.var 3
      , value := EmittedExpr.var 4, newRoot := fun _ => EmittedExpr.var 2
      , op := Dregg2.Circuit.DescriptorIR2.MapOpKind.read }]
  , hashSites := [], ranges := [] }

/-- The descriptor genuinely declares a map op (the shape is not vacuously all-lookup). -/
theorem dMapNV_has_mapOp : mapOpsOf dMapNV ≠ [] := by
  simp [mapOpsOf, dMapNV]

/-- The lookup-or-mapOp shape holds for `dMapNV` (the single non-arith constraint is the `.mapOp`). -/
theorem dMapNV_shape : ∀ c ∈ dMapNV.constraints, ¬ isArith c →
    (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) := by
  intro c hc _
  simp only [dMapNV, List.mem_singleton] at hc
  exact Or.inr ⟨_, hc⟩

/-- **The map-table discharge FIRES on a concrete mapOp descriptor.** From ANY `Satisfied2` witness at
`dMapNV`, the `MapTableAssembly` conjunction is produced — the extraction runs on a genuine map-shaped
descriptor, and the map conjunct is definitionally the witness's own `mapTableFaithful` field. -/
theorem mapTableAssembly_fires
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash dMapNV minit mfin maddrs t) :
    t.tf .memory = [] ∧ t.tf .mapOps = mapLog dMapNV t :=
  mapTableAssembly_conj_of_satisfied2 hash dMapNV minit mfin maddrs t dMapNV_shape hsat

/-- **The extraction is the identity on the faithfulness field** (extraction, not fabrication): the map
conjunct the discharge returns is LITERALLY the `Satisfied2.mapTableFaithful` field. -/
theorem mapTableAssembly_extracts_the_field
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash dMapNV minit mfin maddrs t) :
    (mapTableAssembly_fires hash minit mfin maddrs t hsat).2 = hsat.mapTableFaithful :=
  rfl

/-- **The bus discharge FIRES on the deployed LogUp toy** (`LogUpColumnLayout` §5, a REAL range
lookup at BabyBear): `busModelOk_of_gates_and_floor` rebuilds `BusModelOk` on the toy bus, with
`balanced` routed THROUGH `busGates_force_balance` from the honest cumsum (`runCol`) columns — the
close is the toy's proven balance via `logupColumnLayout_law`, the four ε conjuncts are the toy's own
FS/SZ side conditions. The `balanced` conjunct is genuinely gate-extracted, not assumed. -/
theorem busModelOk_fires :
    BusModelOk Dregg2.Circuit.LogUpColumnLayout.fp0 Dregg2.Circuit.LogUpColumnLayout.embed0
      Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range
      Dregg2.Circuit.LogUpColumnLayout.toyMult := by
  have htoy := Dregg2.Circuit.LogUpColumnLayout.toy_busModelOk
  refine busModelOk_of_gates_and_floor
    Dregg2.Circuit.LogUpColumnLayout.fp0 Dregg2.Circuit.LogUpColumnLayout.embed0
    Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range
    Dregg2.Circuit.LogUpColumnLayout.toyMult
    (runCol (busColA Dregg2.Circuit.LogUpColumnLayout.fp0
      (logupChallenge Dregg2.Circuit.LogUpColumnLayout.embed0
        Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT)
      Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range))
    (runCol (busColB Dregg2.Circuit.LogUpColumnLayout.fp0
      (logupChallenge Dregg2.Circuit.LogUpColumnLayout.embed0
        Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT)
      Dregg2.Circuit.LogUpColumnLayout.toyT .range Dregg2.Circuit.LogUpColumnLayout.toyMult))
    (runCol_zero _) (fun j h => runCol_succ _ j h)
    (runCol_zero _) (fun j h => runCol_succ _ j h)
    ?_ htoy.polesA htoy.polesB htoy.nonexceptional htoy.nodupA htoy.fpFaithful
  -- the close = the toy's proven balance, through the column-layout law (gates ↔ balance)
  exact (logupColumnLayout_law Dregg2.Circuit.LogUpColumnLayout.fp0
    (logupChallenge Dregg2.Circuit.LogUpColumnLayout.embed0
      Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT)
    Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range
    Dregg2.Circuit.LogUpColumnLayout.toyMult).mpr htoy.balanced

end NonVacuity

/-! ## Kernel-clean (0 sorries; axiom floor is Lean's own). -/

#assert_axioms mapTableAssembly_conj_of_satisfied2
#assert_axioms mapTableAssembly_of_satisfied2Family
#assert_axioms busModelOk_of_gates_and_floor
#assert_axioms busModelOk_forces_membership
#assert_axioms satisfied2_forces_declared_lookup_holds
#assert_axioms mapTableAssembly_fires
#assert_axioms busModelOk_fires

end Dregg2.Circuit.AcceptanceDischarge
