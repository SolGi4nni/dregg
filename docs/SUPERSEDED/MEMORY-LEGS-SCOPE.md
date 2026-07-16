# MEMORY-LEGS-SCOPE — the per-effect MEMORY/MAPOP aux-table faithfulness legs for the STARK-soundness fan-out

**Honest scope, first sentence.** This is a read-only scoping of what replaces transferV3's trivial
aux-table discharge (`t.tf .memory = [] ∧ t.tf .mapOps = []`,
`metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean:162`) for the ~8 effects whose descriptors
append REAL mem/map ops. Grounded at HEAD (2026-07-12); every claim cites file:line. Verdict up front:
**the fan-out is (b) bounded real work, not (a) purely mechanical and not (c) a hidden per-effect
deathmarch** — 7 of the 8 effects are bundle copy-swaps once TWO SHARED modelers exist, and those two
modelers (a MapOps-AIR layout modeler and a memory-bus multiset modeler) are real but *shared* work,
written once. The hardest single effect is **SetFieldDyn**, because its leg is the only one that
load-bears the *named-open* higher-order-pole LogUp extension.

---

## 0. Anatomy: what "the memory leg" IS at the assembler

For transferV3 the assembler `algoStarkSound_of_bricks_transferV3`
(`Dregg2/Circuit/AlgoStarkSoundInstance.lean:107-135`) collapses the six `Satisfied2` memory/map legs
to the two emptiness facts. A memory-touching effect must instead use the GENERAL assembler
`algoStarkSound_of_bricks` (`AlgoStarkSoundInstance.lean:150-183`), whose extraction hypothesis
carries, per accepting run (lines 162-174):

1. the **non-arith row arm** `∀ i c, ¬isArith c → c.holdsAt …` — which for these effects contains not
   only `.lookup`s but **`.mapOp` constraints, whose row denotation is the existential Merkle opening**
   `MapOp.holdsAt` = `opensTo`/`writesTo` (`Dregg2/Circuit/DescriptorIR2.lean:511-522`), and `.memOp`s
   (row-locally `True`, `DescriptorIR2.lean:593` — their content is global);
2. the **six global legs** of `Satisfied2` (`DescriptorIR2.lean:612-617`): `maddrs.Nodup`, `memClosed`,
   `MemoryChecking.Disciplined (memLog d t)`, `MemoryChecking.MemCheck minit mfin maddrs (memLog d t)`,
   `memTableFaithful : t.tf .memory = (memLog d t).map opRow`,
   `mapTableFaithful : t.tf .mapOps = mapLog d t`.

So "the leg" splits into three species with different discharge stories:

- **Species A — the `.mapOp` row arm** (7 of 8 effects): "the emitted `(root, key, value, op, new_root)`
  columns are a genuine sorted-heap opening/write."
- **Species B — table-assembly faithfulness** (`memTableFaithful`/`mapTableFaithful`): "the committed
  aux table IS the gathered log." For transferV3 this was the irreducible emptiness pair
  (`Dregg2/Circuit/AirLegsDischarged.lean:30-35` — explicitly "NOT LogUp"); for these effects it is the
  same species of DEPLOYED-MODELING fact, now content-bearing.
- **Species C — the Blum memory legs** (`Disciplined`/`MemCheck`/`Nodup`/`Closed`): REAL only for
  SetFieldDyn (the sole `.memOp` emitter); trivially empty for the 7 mapOp effects, whose
  `memOpsOf d = []` still (the `.mapOp` appends contribute nothing to `memLog`,
  `DescriptorIR2.lean:553-563`).

## 1. Does the LogUp modeler discharge these? — NO (and here is exactly why)

`busModel_forces_lookup_holds` (`Dregg2/Circuit/LogUpColumnLayout.lean:325-352`, ∀ d) produces ONLY
`Lookup.holdsAt` — lookup-membership in a committed table. Its assembler `hbus_of_busModels`
(`LogUpColumnLayout.lean:358-369`) requires the graduated SHAPE `hshape : every non-arith constraint is
a .lookup` — which **fails for all 8 of these descriptors** (they carry `.mapOp`/`.memOp`). Three
distinct reasons the LogUp floor does not cover the rest:

- The **mapOps table is not a LogUp bus**: its `TableDef` kind is `.mapReconcile`
  (`DescriptorIR2.lean:169`, kind at `:95`) — one row per boundary reconciliation, checked by the
  deployed `Ir2Air::MapOps` AIR's in-circuit binary-Merkle path recomputation
  (`circuit/src/descriptor_ir2.rs:2213` per the header at `DescriptorIR2.lean:450-461`), NOT a
  cumulative-sum bus. Different argument, different modeler.
- The **memory table IS LogUp-shaped** (`.memAccess`, `DescriptorIR2.lean:93,164`), but its statement
  is `MemCheck` — a multiset **EQUALITY** `initSet + writeSet = readSet + finalSet`
  (`Dregg2/Crypto/MemoryChecking.lean:138-143`) — while the proven LogUp crown is
  `busBalance_forces_membership`, one-directional support CONTAINMENT under `Nodup`
  (`Dregg2/Circuit/LogUpSoundness.lean:355`). Multiset equality is exactly the **named-open
  higher-order-pole / multiplicity extension** (`LogUpSoundness.lean:31-32` and `:473-477`: "only the
  single-occurrence case is proved"). For lookup legs that residual was benign; **for SetFieldDyn's
  `MemCheck` it becomes load-bearing.**
- The **faithfulness legs (Species B) are assembly facts**, not AIR consequences at all — the same
  classification `AirLegsDischarged.lean:30-35` already gives for the empty case.

What the LogUp modeler DOES give these effects for free: their chip/range `.lookup` constraints
(every one of these descriptors is graduated, so all hashing/range work is lookups) ride
`busModel_forces_lookup_holds` unchanged. The needed Lean wiring is a mild generalization of
`hbus_of_busModels` whose shape hypothesis is "every non-arith constraint is a `.lookup` OR one of
these named `.mapOp`s/`.memOp`s", splitting the non-arith arm — mechanical.

## 2. The per-effect work-list

Common to all 8 (mechanical, per effect):
- `FriLdtExtract_<effect>` bundle copy-swap (`docs/reference/STARK-COMPLETION-AUTOMATION.md` §1f) with
  the two emptiness facts replaced by the effect's legs from §0;
- `@mainAirAcceptF_of_floor <descriptor>` instantiation (already ∀ d,
  `AlgoStarkSoundTransferV3.lean:219-245`);
- an `airAccept_forces_satisfied2_<effect>` bridge (the `AirLegsDischarged` template: `rowHashes`/
  `rowRanges` are `[]`-vacuous for every graduated descriptor, same proof as
  `AirLegsDischarged.lean:98-111`);
- for the 7 mapOp effects: `memLog_<effect> t = []` lemmas (don't exist yet; `rfl`-adjacent —
  `memOpsOf` filterMaps `.mapOp` to nothing) so the five mem legs discharge exactly as transferV3's
  (`AirLegsDischarged.lean:113-118` pattern), leaving `mapTableFaithful` + the `.mapOp` row arm.

| # | Effect / descriptor | Aux op(s) + file:line | Leg needed beyond transferV3's | Existing teeth (downstream of `Satisfied2`) | Missing | Effort |
|---|---|---|---|---|---|---|
| 1 | **NoteSpend** — `noteSpendV3` (`Emit/EffectVmEmitRotationV3.lean:2271-2274`) | `nullifierFreshOp` `.absent` (:2245) + `nullifierInsertOp` `.insert` (:2256), sel-gated, limb 26 | Species A ×2 (incl. the `.absent` GAP opening) + Species B mapTF | `noteSpendV3_grow_gate_forces_set_insert` (:2286) — `Satisfied2 ⟹ opensTo none ∧ writesTo`; `opensTo_none_of_gap` constructor (`DescriptorIR2.lean:502-507`); functionality anti-ghosts (:480-497) | the shared MapOps-AIR modeler (§3); memLog-empty lemma; bundle | **MECHANICAL** once §3 exists (`.absent` rides the modeler's gap arm) |
| 2 | **NoteCreate** — `noteCreateV3` (:2465-2468) | `commitmentsInsertOp` `.insert` (:2451), limb 27 | Species A ×1 (insert only — append-only, no freshness tooth) + B | `noteCreateV3_grow_gate_forces_set_insert` (:2479) | same as #1, minus the gap arm | **MECHANICAL** once §3 exists |
| 3 | **CreateCell** — `createCellV3` (:2592-2598) | `cellsFreshOp` `.absent` + `cellsInsertOp` `.insert` (:2564, :2575), limb 0 | = #1's shape on the accounts tree | `createCellV3_grow_gate_forces_set_insert` (:2663) | same as #1 | **MECHANICAL** once §3 exists |
| 4 | **CreateCellFromFactory** — `factoryV3` (:2602-2610) | same pair, key = `param1` child VK (:2585) | = #3 | `factoryV3_grow_gate_forces_set_insert` (:2683) | same | **MECHANICAL** once §3 exists |
| 5 | **Spawn** — `spawnV3` (:2615-2621) / `spawnWriteV3` (:2649-2654, still exactly 2 map-ops, `#guard :5615`) | same pair, sel 32 | = #3 (cap-handoff is NOT here — it rides `effCapInsertV3_forces_write8`, a constraint-family, :2743-2746) | `spawnV3_…` (:2703), `spawnWriteV3_…` (:2725) | same | **MECHANICAL** once §3 exists |
| 6 | **Refusal** — `refusalFieldsWriteV3` (:4645-4649) | `refusalFieldsWriteOp` `.write` (:4632), limb 36, const key `refusalAuditKeyFelt` (:4619, differential-pinned) | Species A ×1 (`.write` = update-at-present-key) + B | `refusalFieldsWriteV3_forces_write` (:4657); guard both-polarity `#guard`s (:4699-4702) | same as #2 | **MECHANICAL** once §3 exists |
| 7 | **HeapWrite** — `heapWriteV3` (`RotatedKernelRefinementExercise.lean:405-407`) | `heapSpliceWriteOp` `.write` (:374), always-firing guard, rotated heap-root limbs (:385-389) | Species A ×1 + B | `heapWrite_splice_forced` (:457), `heapWrite_addr_forced` (:424 — key IS `hash[coll,key]`); non-stub recompute `#guard`s (:345-347) | same as #6; NOTE the file already flags that the appended MapOp changes `mapTableFaithful` vs the graduated base (:432-434) | **MECHANICAL** once §3 exists |
| 8 | **SetFieldDyn** — `setFieldDynV3` (`Emit/EffectVmEmitRotationV3.lean:2084-2085`; forced variant `setFieldDynForcedV3` :4752-4755) | `.memOp fieldWriteOp` + `.memOp fieldReadbackOp` (`Emit/EffectVmEmitV2.lean:1383-1399`); `mapOpsOf = []` (`#guard :5587-5588`) | **Species C for real**: `Disciplined`/`MemCheck`/`Nodup`/`Closed` on a genuine 2-op log + `memTableFaithful` with content | Blum PROVED unconditionally (`memcheck_sound`, applied at `satisfied2_mem_consistent`, `DescriptorIR2.lean:623-627`); `setFieldDyn_readback_genuine` (`EffectVmEmitV2.lean:1438`), transported `setFieldDynV3_readback_genuine` (`EffectVmEmitRotationV3.lean:5649`), `setFieldDynV3_memLog` (:5643) | the memory-bus modeler (§4): `MemCheck` from the deployed zero-sum requires the **named-open multiset-equality LogUp extension**; `Disciplined` requires the memory-table's per-row gates modeled (currently unmodeled in Lean) | **REAL** (the hardest; see §4) |

Excluded on evidence: the whole cap family (attenuate, delegate, grantCap, introduce, delegateAtten,
revokeDelegation, revokeCapability, refreshDelegation) carries **zero** mem/map ops — their scalar
map-op pairs were DROPPED as shape-UNSAT and the 8-felt writes ride the `effCapInsertV3`/
`effCapRemoveV3`/`effCapOpenWriteV3` constraint wraps (`#guard`s `EffectVmEmitRotationV3.lean:5588-5612`,
header :5690-5703). They are arith/lookup-leg effects for this fan-out, not memory-leg effects.

## 3. The ONE shared real item for effects 1-7: the MapOps-AIR layout modeler

The analog of `LogUpColumnLayout` for the `.mapReconcile` table. Statement to produce (∀ d, once):
*from the deployed `Ir2Air::MapOps` AIR's accepted path-recompute columns (the `mix` closure over the
sibling path, `heap_root.rs::CanonicalHeapTree` update/membership witnesses), every declared `.mapOp`'s
`MapOp.holdsAt` follows* — i.e. the existential `opensTo`/`writesTo` (`DescriptorIR2.lean:468-474`).
What already exists on the Lean side of the seam: the full downstream algebra —
`opensToMerkle`/`writesToMerkle` (`Dregg2/Circuit/MapMerkleRoot.lean:196-203`), functionality +
some-excludes-none anti-ghosts under `Poseidon2SpongeCR` (`:211-223`), the `.absent` constructor from
gap bracketing (`opensTo_none_of_gap`, `DescriptorIR2.lean:502-507`).

What is genuinely missing (the honest crux): the denotation quantifies over the **whole sorted
`2^16`-leaf heap** (`∃ h, SortedKeys h ∧ h.length = 2^d ∧ mapRoot … = r ∧ get …`), while the AIR opens
a **sibling path**. Path-recompute ⟹ whole-heap-existential is a knowledge-extraction-shaped argument
(under CR a path pins only the path), so the modeler either (i) models the extraction (the prover's
committed update witness IS the whole-tree witness the honest prover has — real, one-time modeling
work), or (ii) the bundle CARRIES `MapOp.holdsAt` per accepting run as a named FRI-extraction premise,
exactly the epistemic status transferV3's `hbus` had before `LogUpColumnLayout` landed. Option (ii) is
the transferV3-parity bar and makes effects 1-7 immediate copy-swaps; option (i) is the
LogUpColumnLayout-parity bar and is ONE lane, shared by all 7 (the `.absent` gap arm — two adjacent
leaves — is its only extra structure). Neither is per-effect novel work.

Strategic note (don't scope twice): the STAGED umem cohort (`Emit/EffectVmEmitUMemCohort.lean:145`
`nullifierFreshUMem` etc., `Satisfied2U` with the boundary anchored to the committed root,
`DescriptorIR2.lean:581-582,788`) REPLACES the per-map MapOp reconciliation for the cohort effects if
the rotation flips. If that flip is near, the Species-A modeler should be written against the umem
boundary table shape, not `.mapReconcile`, or it gets thrown away.

## 4. The one hard leg: SetFieldDyn's memory-bus discharge

`MemCheck` is the multiset equality (`MemoryChecking.lean:138-143`). To DISCHARGE it (rather than
carry it) from the deployed memory-table LogUp zero-sum needs: (i) the cumsum-gate extraction — the
`runCol`/`busGates_force_balance` machinery (`LogUpColumnLayout.lean:191-297`) reuses verbatim; (ii)
**"equal `logupSum` at a non-exceptional challenge ⟹ equal multisets"** — strictly stronger than the
proved `busBalance_forces_membership` (containment under `Nodup A`,
`LogUpSoundness.lean:355`) and precisely the residual `LogUpSoundness.lean:473-477` names as "a
PROVABLE SZ extension" via `rootMultiplicity` on `busNum` — provable, but nobody has proved it, and a
memory log genuinely repeats addresses so `Nodup` cannot be assumed away; (iii) `Disciplined`
(`MemoryChecking.lean:146+`) from the memory table's per-row gates — those gates are currently
unmodeled in Lean (the memory AIR has no `LogUpColumnLayout`-style twin). Blum itself
(`memcheck_sound`) is already unconditional. So SetFieldDyn = one real proof (the higher-pole SZ
lemma, self-contained polynomial algebra), one modeling lane (memory-row gates ⟹ `Disciplined`), and
the usual bundle/bridge mechanics. Carry-in-bundle parity is available here too, at the cost of a
fatter floor.

## 5. Verdict

**(b) — bounded real work, dominated by two shared lanes, not eight.**

- **Not (a)**: the LogUp modeler (`busModel_forces_lookup_holds`) discharges NONE of the new legs —
  it is lookup-membership only; the mapOps table is a different argument (Merkle recompute, not a
  bus) and `MemCheck` needs a stronger lemma than the proved containment.
- **Not (c)**: no effect hides novel per-effect crypto. The 7 mapOp effects share ONE op-kind algebra
  (`.insert`/`.write`/`.absent`) whose entire downstream (functionality, gap, anti-ghost, per-effect
  arithmetic teeth `*_grow_gate_forces_set_insert` / `*_forces_write` / `heapWrite_splice_forced`)
  is already proven and axiom-clean; what's missing above them is one shared modeler (§3) + per-effect
  `rfl`-grade emptiness lemmas + bundle copy-swaps.
- **Hardest effect: SetFieldDyn** — the only one whose leg load-bears a named-open lemma (the
  higher-order-pole multiset-equality SZ extension) plus an unmodeled AIR surface (the memory-row
  discipline gates). It should be its own lane, not batched with the mechanical seven.
- **Two-bar honesty**: at *transferV3 parity* (legs CARRIED in the `FriLdtExtract_<effect>` bundle as
  named deployed-modeling premises, the same status `hbus`/emptiness had) all 8 are mechanical
  today. At *LogUpColumnLayout parity* (legs DERIVED from modeled deployed structure) the cost is:
  1 shared MapOps-AIR modeler + 1 memory-bus modeler + 1 higher-pole SZ proof — three real,
  bounded, shared work items.
