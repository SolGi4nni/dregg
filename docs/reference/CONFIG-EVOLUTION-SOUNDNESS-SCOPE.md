# CONFIG-EVOLUTION-SOUNDNESS-SCOPE — the honest target that stops carrying the content

**Read-only scope, grounded at HEAD (2026-07-12); every claim cites file:line.** The complaint is
correct in shape: the kernel STARK object lands at `Satisfied2` (trace satisfaction) and CARRIES real
content as hypotheses. This doc classifies EVERY carried fact and states the honest target:
`verifyAlgo-accept ⟹ real frame-respecting config transition, modulo {Poseidon2SpongeCR, FRI-LDT}`.

**Headline verdict (the biggest finding):** `kstepAll` is **NOT a toy**. It is the real executor
`execFullA` over a real record kernel (heap/nullifier/commitment/balance/caps evolution), with
conservation proved and cross-step frame DERIVED. The config-evolution content is therefore
**carried-because-provable (DEBT), not carried-because-missing (toy)**. Both layers carry
EXTRACTION-class facts (the circuit-witness decode; FRI-LDT; the bus/map-reconcile modeling), not the
Hoare content. Exactly ONE carried fact is a genuine assumption beyond the allowed modulus:
`MapReconcileFamily`'s `CanonicalHeapTree` existential (§Layer-1.3).

---

## Layer 2 first (it settles the framing): is `kstepAll` a real config transition?

`kstepAll e = dispatchArm e = ∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`
(`CircuitSoundnessAssembled.lean:630`, `CircuitSoundness.lean:510`).

`fullActionStep` (`ActionDispatch.lean:171`) case-splits every `FullActionA` to its leaf `*Spec`, and
**`fullActionStep_exec_iff` PROVES `execFullA st fa = some st' ↔ fullActionStep st fa st'` for all 30
arms** (`ActionDispatch.lean:335`, `#assert_axioms`-clean at `:522`), each arm delegating to a named
`execFullA_*_iff_spec` keystone (27 such keystones tree-wide). So `kstepAll` IS the real executor.

The executor runs over `RecChainedState.kernel : RecordKernelState` with REAL fields — `accounts`,
`bal : CellId → ℤ` per-asset, `caps` (the l4v c-list lift), `nullifiers`, `commitments`, `revoked`,
`heaps` + `heap_root`, record `fields`, `program`, `vk`, `nonce` (`Kernel.lean:35`,
`RecordKernel.lean`). The per-effect Specs are genuine transitions WITH frame:

* transfer → `transferBal` debit/credit on `bal` only (`Kernel.lean:63`); conservation Law 1 PROVED
  (`transfer_sum_conserve` `:90`, `exec_conserves` `:107`).
* noteSpend → inserts `nullifiers` ONLY, `bal`/`escrows` fixed (`TurnExecutorFull.lean:2859`).
* heapWrite → splices `heaps` + `heap_root` ONLY, bal-neutral (`heapStepW_conserves`, `:2913`).
* revoke → `removeEdgeCaps` on the `(holder,t)` edge; etc.

Cross-step frame is a **theorem, not an assumption**: `stateDecodeChain_frame_continuous`
(`CircuitSoundness.lean:279`) forces `a.post.kernel = b.pre.kernel` from the shared published
commitment + faithfulness. **This is genuine Hoare/frame content, and it is already real.**

### Is `ClosedLogExtract` (`Satisfied2 + StateDecodeLog ⟹ kstepAll`) provable with existing teeth?

**Yes — and it is already ASSEMBLED, load-bearing.** `ClosureFanoutGenuine.closedLogExtract_all_genuine`
(`ClosureFanoutGenuine.lean:46`) discharges `∀ e, ClosedLogExtract` by a 36-way `actionTag` case split;
**every slot CALLS its proven `<e>_closedLog` rung** on the extracted encode (grep: every discharger
names a `*_closedLog`; e.g. `mint_closedLog` `:120`, `burn_closedLog` `:145`). Those rungs call the
landed per-effect teeth — 22 `*_grow_gate_forces_set_insert` / `*_forces_write8` /
`heapWrite_splice_forced` theorems tree-wide — so the `RotatedKernelRefinement*` soundness rungs are
load-bearing, not decorative.

**What is genuinely carried per effect is NOT the Hoare step — it is the decode-extraction**
`<e>TraceReadout : Satisfied2 (Rfix e) ⟹ <e>EncodesMinusLog` (`ClosureFanoutGenuine.lean:12`,
`:98`+): the limb-level column read (guard fields, cap-tree opening, per-row reads) the LEDGER-ROOT
commitment `StateDecode` structurally cannot certify. This is the `WitnessDecodes` class — the same
FRI/SNARK-witness-extraction class as Layer 1's floors, **not** missing Hoare infrastructure.

**Layer-2 classification: PROVABLE-WITH-EXISTING-TEETH.** The config-evolution core (`encode ⟹ Spec ⟹
dispatchArm`) is landed for all 36 effects and assembled; the residual is the witness-column readout,
an extraction floor, not a toy and not new frame infrastructure.

---

## Layer 1 — the STARK-side carried facts (`AlgoStarkSoundGeneral` / `AlgoStarkSoundFanoutMemory`)

The assembler `algoStarkSound_of_memoryLegs` produces the `StarkSound`-class extraction
(`AcceptsFull ⟹ ∃ trace, Satisfied2 + published-PI agreement`). It **DERIVES** the arith arm
(`MainAirAcceptF`, via the OOD column-layout modeler `hood_of_oodColumnLayout` —
`AlgoStarkSoundGeneral.lean:294`), the `.lookup` non-arith arm (via `busModel_forces_lookup_holds`),
and the `.mapOp` arm (via `mapOpsArm_of_modeler`). The CARRIED hypotheses are these:

### 1. `FriLdtExtract d` (`AlgoStarkSoundGeneral.lean:134`) — this IS the `{FRI-LDT}` modulus.
Not to be discharged; it is the allowed floor. **Classify: ALLOWED-FLOOR (do not discharge).**

### 2. `BusModelFamily d` (`AlgoStarkSoundGeneral.lean:170`): `AcceptsFull ⟹ ∃ mult, BusModelOk`.
`BusModelOk` (`LogUpColumnLayout.lean:309`) = { `polesA/polesB` pole-freeness, `balanced`,
`nonexceptional` (SZ ε-event), `nodupA` (multiplicity), `fpFaithful` (β-RLC collision ε under
Poseidon2SpongeCR) }. The `balanced` conjunct is literally the LogUp AIR row constraint — **forced by
`MainAirAcceptF`/`Satisfied2`**. The remaining conjuncts are FS/SZ ε-game facts + Poseidon2SpongeCR —
the SAME epistemic class as `FriLdtExtract`'s own FS non-exceptionality (`:157-162`).
`busModel_forces_lookup_holds` (`LogUpColumnLayout.lean:325`) already PROVES `BusModelOk ⟹ membership`.
**Classify: NEEDS-A-LEMMA — reduces into `{Poseidon2SpongeCR, FRI-LDT}`.** The missing step is a wiring
lemma extracting `(mult, BusModelOk)` from the accepted LogUp columns; no new crypto, no new modulus.

### 3. `MapReconcileFamily d` (`AlgoStarkSoundFanoutMemory.lean:97`): `AcceptsFull ⟹ MapReconcileModelOk`.
`MapReconcileModelOk` = per fired `.mapOp` row, `ReconcileGatesAt` (`MapOpsColumnLayout.lean:577`):
```
∃ h : FeltHeap, SortedKeys h ∧ h.length = 2^dep ∧ mapRoot hash dep h = (m.root 0).eval a ∧ <per-kind path-recompute gates>
```
The **per-kind path-recompute gates ARE AIR constraints** (forced by `Satisfied2`), and
`reconcileGates_force_opening` (`:611`) PROVES they yield the `opensTo`/`writesTo` denotation under
Poseidon2SpongeCR. But the leading existential — **the whole sorted `2^16`-leaf `CanonicalHeapTree`
behind the pre-root COLUMN** — is a knowledge-extraction premise: under CR a path pins only the path,
not the whole sorted tree (`MEMORY-LEGS-SCOPE.md:117-126`, the honest crux). **The sorted-canonical-heap
is NOT forced by the AIR's sorted-tree gates — the AIR recomputes a sibling path only.**
**Classify: GENUINE-ASSUMPTION (knowledge-extraction) — the ONE fact beyond the allowed modulus.**
Closing it is option (i): a shared `CanonicalHeapTree`-extraction modeling lane (one lane for all 7
mapOp effects; the `.absent` two-adjacent-leaf gap arm is its only extra structure) — real one-time
modeling, NOT wiring. Option (ii) keeps it carried at transferV3-`hbus` parity.

### 4. `MapTableAssembly d` (`:114`) / `MemMapFree` (transfer): trace-commitment-ASSEMBLY facts.
`committed memory table = [] ∧ committed mapOps table = mapLog d`. The emptiness half is DERIVED from
descriptor shape (`memOpsOf_eq_nil_of_mapShape`, `:168`). The `mapTableFaithful` half relates the
extracted trace's committed aux columns to the gathered log — a fact about which columns the FRI
extraction commits, same epistemic status as transferV3's aux-table-emptiness pair
(`AirLegsDischarged.lean:30-35`). **Classify: NEEDS-A-LEMMA / NEAR-FLOOR — bundle-able with
`FriLdtExtract` (the extraction's column-commitment structure); no new crypto.**

---

## The grounded plan to reach the honest target

Target: `verifyAlgo-accept ⟹ real frame-respecting config transition, modulo {Poseidon2SpongeCR, FRI-LDT}`.

**What is ALREADY THERE (no new proof):**
* The real config model + frame: `kstepAll ⟺ execFullA` (`ActionDispatch.lean:335`), conservation Law 1
  (`Kernel.lean:107`), cross-step frame continuity (`CircuitSoundness.lean:279`).
* The per-effect Hoare core `encode ⟹ Spec ⟹ dispatchArm` for all 36 effects (`RotatedKernelRefinement*`,
  22 forcing teeth), ASSEMBLED and load-bearing through `closedLogExtract_all_genuine`.
* The proven STARK modelers: OOD arith arm, `busModel_forces_lookup_holds`, `reconcileGates_force_opening`.

**What is WIRING (Layer-1/2 into the floor — mechanical, no new modulus):**
* Layer 1.2 `BusModelFamily` → discharge lemma extracting `BusModelOk` from accepted LogUp columns.
* Layer 1.4 `MapTableAssembly`/`MemMapFree` → fold the aux-table-column facts into `FriLdtExtract`.
* Layer 2 `<e>TraceReadout` → the `WitnessDecodes`-class limb decode; already NAMED per effect, the
  same class as the FRI witness extraction. Reduces into the extraction floor, not Hoare work.

**What is a REAL NEW PROOF LANE (the only genuinely-missing content):**
* Layer 1.3 `MapReconcileFamily` `CanonicalHeapTree` extraction — option (i), ONE shared lane for the 7
  mapOp effects. This is the honest residual beyond `{Poseidon2SpongeCR, FRI-LDT}`. Everything the
  downstream needs (`opensToMerkle`/`writesToMerkle`, anti-ghosts, the `.absent` gap constructor)
  already exists (`MEMORY-LEGS-SCOPE.md:112-115`); the lane is the path-recompute ⟹ whole-heap-existential
  argument. (Strategic note `MEMORY-LEGS-SCOPE.md:128`: if the umem-cohort rotation flips, write this
  against the umem boundary-table shape instead, or it is thrown away.)
* SetFieldDyn's memory-bus leg is out of scope here (the higher-pole SZ lemma, `MEMORY-LEGS-SCOPE.md §4`).

**Honest bottom line.** Nothing here is a toy. The Hoare/frame content is real and largely assembled;
the carried facts are extraction-class debt that reduces into `{Poseidon2SpongeCR, FRI-LDT}` by
wiring — EXCEPT the single `CanonicalHeapTree` knowledge-extraction premise, which needs one shared
modeling lane (or stays a named FRI-extraction premise at transferV3 parity). The content is carryable
because it is provable, not carried because it is missing.
