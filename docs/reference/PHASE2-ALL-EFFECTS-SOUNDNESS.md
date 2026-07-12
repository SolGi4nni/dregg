# Phase 2 — All-Effects Kernel STARK-Soundness (read-only assessment + grounded plan)

**Scope date:** 2026-07-11. Grounded at HEAD against `metatheory/Dregg2/Circuit/*`.
Phase 1 (`transferV3`) has a real `AlgoStarkSound` slice being reduced to the floor
`{Poseidon2SpongeCR, FRI-LDT, FS-game}`. Phase 2 = extend soundness from **one effect** to the
**whole kernel** (the 27 `EffectTag`s, `Substrate/VerbRegistry.lean:213`).

This doc is an honest census, not a celebration. The one-line verdict:

> **1 of 27 effects (transfer) is at the REAL Poseidon2 permutation, and only in a zero-row
> slice.** The other 26 have no `Satisfied2Faithful`-level keystone at all (real *or* toy) — only
> `Nonempty`-of-premise (readout non-vacuity) witnesses. The kernel is **not** STARK-sound; it is
> **transfer-sound modulo {the shared LogUp floor, a split active/deployed witness}**.

---

## 0. The two seams that already generalize (the good news, stated first)

* **The registry EXISTS and is real.** `CircuitSoundnessAssembled.Rfix : Registry` (=
  `EffectIdx → EffectVmDescriptor2`, `CircuitSoundnessAssembled.lean:400`) is a **total**,
  `actionTag`-keyed lookup into `v3RegistryHeap`, landing each effect at its genuine deployed
  descriptor (`Rfix 0 = transferV3Membership` by `rfl`; `Rfix 38 = makeSovereign` key-commit; …).
  Phase 2 does **not** need to build the registry; `fun _ => transferV3` → `Rfix` is already done in
  the assembled layer.
* **`algoStarkSound_of_bricks` is already general over any `R`.**
  `AlgoStarkSoundInstance.lean:150` proves `AlgoStarkSound hash R perm …` for an **arbitrary**
  registry `R` — the deployed-slice `_transferV3` (line 107) is just `R := fun _ => transferV3`. So
  `AlgoStarkSound hash Rfix …` follows the instant you supply its `hextract` hypothesis. **The lift
  is not the gap.** The gap is *discharging* `hextract` per effect (the eight
  `airAccept_forces_satisfied2` legs), rather than carrying it.

The apex consumes this as an assumed class: `CircuitCompletenessAssembled.lean:844` and
`CircuitSoundnessAssembled.lean:65` take `[StarkSound hash Rfix]` as a **hypothesis instance**.
Phase 2 is precisely: **discharge `[StarkSound hash Rfix]`** the way Phase 1 discharged it for the
`fun _ => transferV3` slice.

---

## 1. The `permOutZ` toy census (~127 occurrences)

`permOutZ : List ℤ → List ℤ := fun _ => List.replicate CHIP_OUT_LANES 0`
(`FloorsNonVacuous.lean:108`) — the **all-zero-squeeze** permutation. The real deployed hash is
`Poseidon2BabyBearW16.perm` (KAT-validated `Poseidon2BabyBear<16>`), wrapped as
`Satisfied2FaithfulDeployed.permOutDeployed` (non-constant; lane-0 head `1906786279 ≠ 0`).

| File | count | what `permOutZ` stands in for | classification |
|---|---|---|---|
| `FloorsNonVacuous.lean` | 28 | def of `permOutZ`/`permOut0`; the `ChipTableSoundN` inhabit/separate witnesses (§2); the **toy transferV3 keystone** `satisfied2Faithful_transferV3` (§3) | **mixed**: the §2 separation uses are **legit toy** (non-vacuity of a *predicate*); the §3 keystone is a **real-perm faithfulness placeholder** — already lifted for transfer by `Satisfied2FaithfulDeployed` |
| `Satisfied2FaithfulActive.lean` | 27 | the **active+faithful** transferV3 keystone at `permOutZ` (real active rows + faithful chip/range tables) | **faithfulness placeholder** — but load-bearing-honest: on the active transfer rows the chip **output block is genuinely all-zero** (the digest/lane columns are high columns the active rows never populate), so `permOutZ` *is* the true evaluated tuple there. The real-perm-**and**-active union is **not built** (the deployed lift has zero rows). |
| `FloorsNonVacuousWave.lean` (10), `…WaveLifecycle` (9), `…WavePermsProgram` (9), `…WaveBirth` (7), `…WaveTransfer` (6), `…WaveMiscNotes` (11) — **52** | the `RotTableSide` chip-table half of each per-effect `<E>TraceReadout` **`Nonempty`** witness | **legit toy** — these prove a *premise is inhabitable* (not secretly empty), not any faithfulness. `Nonempty` of a readout needs *a* valid chip table, never the real perm. |
| `Satisfied2FaithfulDeployed.lean` | 10 | the both-truth teeth `#guard permOutDeployed … ≠ permOutZ …` | **this is the FIX, not a placeholder** — the file that lifts transfer to `permOutDeployed`; the `permOutZ` mentions only exhibit the toy as the vacuous case. |

**Honest tally of the perm question:** exactly **one** effect (transfer) has a `Satisfied2Faithful`
at the **real** perm (`satisfied2Faithful_deployed`, zero rows). **One** effect (transfer, again)
has a **toy-perm** active keystone. **Zero** effects have a unified real-perm-**and**-active keystone.
The other **26** effects have **no** `Satisfied2Faithful` keystone at any perm — only Wave
`Nonempty` witnesses. So the ~52 Wave `permOutZ` are legit; the load-bearing toys are the **27**
in `Satisfied2FaithfulActive` (transfer) plus the **26 keystones that don't yet exist**.

---

## 2. How much `Satisfied2FaithfulDeployed` (the template) generalizes

`Satisfied2FaithfulDeployed.lean` is the pattern every other graduated effect copies. Splitting it:

**Fully reusable, descriptor-INDEPENDENT (shared, ride for free):**
`perm_length`, `permOutDeployed`, `permOutDeployed_width`, `permOutDeployed_lane0`, `hashDeployed`,
`toNatP`, `deployedIns`, `deployedChipTbl_sound` — all about the Poseidon2 perm and the chip table.
Identical for every effect.

**transferV3-specific but SHALLOW (one-line swap):** `satisfied2_deployedTrace` and
`satisfied2Faithful_deployed` name `transferV3` and rewrite
`transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)`, then discharge the six
mem/map legs with `memLog_graduateV1`/`mapLog_graduateV1` — lemmas that hold for **every**
`graduateV1` descriptor. Swapping the descriptor identity is the only per-effect edit; the proof
structure (empty logs ⇒ legs collapse) is verbatim. **Generalizes mechanically to any pure-graduated
effect.** Does **NOT** generalize to effects that append real `.mapOp`/`.memOp` (see §3).

**Structural limitation that replicates per effect:** the deployed keystone uses `rows = []`, so the
per-row arithmetic gates are vacuous — it certifies chip/range faithfulness at the real perm, and
says nothing about the effect's actual transition logic. That is why transfer needs the *separate*
`Satisfied2FaithfulActive` (active rows, toy perm). Every effect inherits this split; neither half
is the whole object.

---

## 3. The memory / mapOp legs (the genuinely per-effect crypto content)

`transferV3` is mem/map-op-free: `memLog transferV3 t = []`, `mapLog transferV3 t = []`
(`AirLegsDischarged.lean:86,90`, from `graduateV1` emitting no `.memOp`/`.mapOp`). Its
`mem`/`mapTableFaithful` legs collapse to the assembly facts `t.tf .memory = [] ∧ t.tf .mapOps = []`.

**This is FALSE for the ~8 effects that append real map/mem ops** (grep `\.mapOp`/`\.memOp` over the
v3 registry):

| effect | descriptor | appended op(s) | leg |
|---|---|---|---|
| **NoteSpend** | `noteSpendV3` (`EffectVmEmitRotationV3.lean:2274`) | `.mapOp nullifierFreshOp`, `.mapOp nullifierInsertOp` | nullifier tree: absence (double-spend tooth) + sorted insert |
| **NoteCreate** | `noteCreateV3` (:2468) | `.mapOp commitmentsInsertOp` | commitment tree insert |
| **CreateCell** | (:2597) | `.mapOp (cellsFreshOp …)` | cells map: freshness + insert |
| **CreateCellFromFactory** | (:2607) | `.mapOp (cellsFreshOp …)` | cells map insert |
| **SpawnWithDelegation** | (:2620, :2653) | `.mapOp (cellsFreshOp …)` | cells map insert (+ delegation variant) |
| **Refusal** | (:4649) | `.mapOp refusalFieldsWriteOp` | refusal-fields write |
| **SetFieldDyn** | (:4755) | `.memOp fieldWriteOp`, `.memOp fieldReadbackOp` | **flat MEMORY** write + readback |
| **HeapWrite** | `heapWriteV3` (`RotatedKernelRefinementExercise.lean:407`) | `.mapOp heapSpliceWriteOp` | sorted-Merkle heap splice |

So **~8 of 27 effects have non-empty aux-table legs; ~19 are pure-graduated** (empty logs, ride
transfer's discharge for free).

**In-tree machinery vs open:** the *balance* predicates exist and are general —
`MemoryChecking.MemCheck` / `.Disciplined` (multiset init+write = read+final). The per-effect *arithmetic
content* is largely **already proven as descriptor teeth** (e.g.
`noteSpendV3_grow_gate_forces_set_insert` forces the sorted insert; the birth `cellsFreshOp` teeth
force set-insert). What is **not** in the Lean semantics is the **assembly/bus bridge**:
`t.tf .mapOps = mapLog d t` ("the committed table IS the gathered log") — for a non-empty log this is
exactly a **LogUp permutation-argument** obligation, the same un-modeled bus as `hbus` (§4). So the
mem/map legs are **not a fresh per-effect crypto obligation** — they reduce to (a) the shared LogUp
floor and (b) per-effect arithmetic teeth that mostly already exist.

---

## 4. The LogUp bus floor (`hbus`) — SHARED, not per-effect

`AirLegsDischarged.hbus_is_lookup` (`:138`) pins the shape: every remaining non-arithmetic
`transferV3` constraint is a `.lookup` (chip or range). AIR acceptance does **not** force lookup
membership (`arithResidual (.lookup _) = 0`); the "bus balances ⟹ multiset supported by the table"
bridge is **explicitly out of the Lean semantics** (`Lookup.lean:17`, "LogUp is how the prover
enforces it efficiently — that lives in the Rust AIR").

This floor is **SHARED across all effects and both aux-table families**:
* every effect's chip lookups target the **same** `.poseidon2` chip table (one perm) and its range
  lookups the **same** `rangeRows BAL_LIMB_BITS` range table — the table **contents** are shared, and
  their faithfulness (`deployedChipTbl_sound`, `RangeTableSound`) is already at the **real** argument;
* the mem/map table faithfulness (§3) reduces to the **same** LogUp permutation soundness.

So Phase 2 does **not** multiply the LogUp obligation by 27. **One** LogUp permutation-argument
soundness (the p3/FRI bus, part of the Phase-1 floor `{FRI-LDT, FS-game}`) discharges `hbus` **and**
the aux-table assembly bridge for **every** effect. Naming it once is the correct move.

---

## 5. The registry assembly gap

`Rfix` (§0) is real and total. `algoStarkSound_of_bricks` (§0) already produces
`AlgoStarkSound hash Rfix …` from its `hextract` hypothesis. The gap is **discharging `hextract`
per effect**: for each `(pi, π)`, on accept, the opened trace must satisfy the eight
`airAccept_forces_satisfied2` legs at `R pi.effect = Rfix pi.effect`. For `transferV3`,
`AirLegsDischarged.airAccept_forces_satisfied2_transferV3` (`:154`) discharges **6 of 8**
structurally (hashSites/ranges empty, mem/map empty) and carries **2** (`hbus` + table emptiness).
There is **no** analogue for the other 26 tags. Assembling `[StarkSound hash Rfix]` = producing a
per-effect `airAccept_forces_satisfied2_<e>` for all 27 and feeding the bundle to
`algoStarkSound_of_bricks hash Rfix`, then `starkSound_of_verifyAlgo` (the `AlgoStarkSound ⟹
StarkSound` lift, already proven).

---

## 6. Grounded Phase-2 work-list + effort shape

**SHARED — done once, rides for all 27 (no per-effect cost):**
- the crypto floor `{Poseidon2SpongeCR, FRI-LDT, FS-game}` (Phase 1);
- the LogUp permutation-argument soundness → discharges `hbus` **and** the aux-table bridge (§4);
- the real-perm chip/range **table** faithfulness (`deployedChipTbl_sound`, `RangeTableSound`) — the
  perm-level half of `Satisfied2FaithfulDeployed` (§2);
- `algoStarkSound_of_bricks` general lift + `Rfix` registry (§0).

**PER-EFFECT — MECHANICAL (~19 pure-graduated effects):** each needs
`airAccept_forces_satisfied2_<e>` (copy `AirLegsDischarged` §2: hashSites/ranges/memLog/mapLog all
`[]` by the `graduateV1` lemmas — one descriptor swap) **and** a real-perm keystone
`satisfied2Faithful_<e>_deployed` (copy `Satisfied2FaithfulDeployed`, one descriptor swap, §2). No new
crypto. **~2 × 19 ≈ 38 mechanical instantiations.**

**PER-EFFECT — REAL LEGS (~8 aux-table effects, §3):** for each of NoteSpend, NoteCreate, CreateCell,
CreateCellFromFactory, SpawnWithDelegation, Refusal, SetFieldDyn, HeapWrite:
- the `graduateV1` empty-log shortcut does **not** apply — the `mem`/`mapTableFaithful` legs carry the
  **real** `mapLog`/`memLog`, discharged against the shared LogUp bridge (§4) + the (mostly existing)
  per-effect set-insert/write teeth. The `memBalanced`/`MemCheck` leg needs a real `minit`/`mfin`
  boundary for the touched addresses (not the empty boundary transfer uses).
- **Not a fresh crypto obligation** — but genuinely more than a descriptor swap: each needs its own
  boundary witness + wiring the existing tooth into the aux-table faithfulness leg.

**PER-EFFECT — the active keystone (all 27):** transfer's `Satisfied2FaithfulActive` (active rows,
toy perm) has **no** analogue for other effects and is **not** unified with the deployed (real-perm,
zero-row) half even for transfer. Whether Phase 2 must build 27 active+real-perm unified keystones,
or whether the `algoStarkSound_of_bricks` route (which only needs `airAccept_forces_satisfied2`, not a
`Satisfied2Faithful` keystone) makes the active keystone a *non-vacuity* obligation rather than a
*soundness* one, is the **key scoping decision** — the soundness path (§5) does **not** consume the
active keystones; they are the non-vacuity guarantee that the accept-set is inhabited.

**Effort shape verdict:** the soundness spine is **~38 mechanical instantiations + ~8 real aux-table
legs + 1 shared LogUp floor**. There are **no** 27 independent hard crypto obligations — the hardness
is concentrated in the **single shared LogUp floor** and the **8 per-effect aux-table wirings** (each
moderate, not a new primitive). The bulk (19 effects × 2) is copy-swap.

---

## 7. The honest kernel-soundness bar

"The KERNEL is STARK-sound" (not just transfer) means: `[StarkSound hash Rfix]` is **discharged**
(no longer an assumed class in the apex), i.e. for **every** one of the 27 `EffectTag`s, an accepting
`verifyAlgo` on the deployed descriptor `Rfix e` forces `Satisfied2` at the **real** perm, with the
LogUp floor **named once** and the aux-table legs **real** where the effect touches memory/maps.

Current honest state against that bar:
- Registry + general lift: **done** (§0).
- Per-effect leg discharge: **1 / 27** (transfer, and 6/8 structural + hbus/emptiness carried).
- Real-perm chip faithfulness keystone: **1 / 27** (transfer, zero-row).
- Real aux-table legs: **0 / 8** (all ~8 map/mem effects still owe the non-empty-log faithfulness).
- Unified active + real-perm keystone: **0 / 27** (transfer is split; nobody is whole).

So: **the kernel is not STARK-sound today.** It is **transfer-sound modulo the shared LogUp floor and
a split active/deployed witness.** Phase 2 closes the gap by the §6 work-list — dominated by
mechanical copy-swaps and one shared floor, with ~8 real (but not novel-crypto) aux-table legs — and
by naming the LogUp permutation-argument soundness exactly once, as a floor, not per effect.
