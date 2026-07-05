# umem efficiency + protocol-design assessment

*An honest mirror, grounded in measurement. The question: is dregg's universal-memory
(umem) argument EFFICIENT, do we have BENCHMARKS, and is it GOOD protocol design — or is
the per-map approach it replaces actually fine and umem complexity for marginal gain?*

Method: read the code at HEAD, parse the deployed descriptor registries for a static
column/constraint/chip comparison, and RE-RAN the committed micro-benchmarks (release,
proofs independently verified, byte sizes are deterministic). Numbers below are measured at
HEAD unless flagged. Where a memory note and the code disagree, the code wins.

---

## TL;DR

- **Benchmarks exist and are honest** — `circuit/tests/effect_vm_ir2_size_measure.rs` proves
  the same access pattern both ways through the *production* config and independently verifies
  BOTH proofs before measuring byte sizes. I re-ran two of them at HEAD; they reproduce the
  committed numbers.
- **The "−48.6% chip-drop" is REAL and reproducible** — but it is an **isolated micro-probe**
  (a synthetic 4-row, 6-column descriptor), and the win materializes **only when the chip table
  is dropped**, which a "memory-only descriptor" does and a real deployed effect does NOT.
- **On the DEPLOYED path the win is unrealized — and the welded prover is not yet the default.**
  Two umem toggles must not be conflated. The executor's umem *observation bridge* is ON by default
  (`umem_witness_enabled: AtomicBool::new(true)` at every `TurnExecutor` ctor,
  `turn/src/executor/mod.rs:1008/1070/1114` — the G4 observation epoch: the deployed executor *witnesses*
  the umem boundary). But the umem-**welded proving registry / VK** stays **STAGED, not flipped**: the
  deployed prover default remains per-map until the gated VK epoch (`sdk/src/full_turn_proof.rs` —
  "no VK bump, no default flip, `umem_witness_enabled` untouched"; `rotation-wide-umem-welded-registry-staged.tsv`
  is the staged *target*, not the deployed default). Measured on that staged welded form it is **purely
  additive**: it keeps `main/chip/range/memory/map_ops` and ADDS `umemory/umem_boundary` on top. 0 of 54
  members drop the chip. Static cost: **+0.8% summed trace width, +2 tables/member, +0.6% constraints**.
  In its current welded form umem is a small **regression**, not a win — and the table-collapse win
  remains the pending lever the gated VK epoch would unlock.
- **The "~130,000×" is NOT a umem benchmark** — it is a dated profiler note about per-turn
  *commitment* FFI (a different subsystem). It does not belong in the umem efficiency story and
  is not cited here as evidence.
- **Design verdict: GOOD, standard, field-aligned technique — but sold on the wrong axis.**
  Blum/offline-memory-checking is exactly what modern zkVMs (Jolt et al.) use for RAM; umem
  applies it correctly. The honest justification for umem is the **capability surface**
  (passable/composable/checkpointable witnessed memory), NOT the −48.6% proof-shrink, which is
  latent and modest at per-turn scale. For pure proof efficiency on today's effect set, the
  **per-map approach was fine** and umem adds soundness-critical complexity for a deferred win.

---

## 1. Do benchmarks exist? What is measured vs claimed.

**Yes — and they are good benchmarks.** `circuit/tests/effect_vm_ir2_size_measure.rs` is a
measurement harness (`docs` note in its header: *"a negative result … is exactly what it exists
to surface"*). Each probe proves the SAME access pattern through both regimes, runs each
proof's independent verifier, then postcard-serializes and reports the wire size with a per-
component breakdown. Byte sizes are deterministic (independent of debug/release), so the
KiB figures are trustworthy even though prove *times* in debug would be lies.

### Re-ran at HEAD (release, both proofs verified)

`ir2_mapop_interior_to_umem_chip_drop` — a c-list READ + WRITE (the deployed attenuate/
revoke-cap bookkeeping shape) expressed as `map_op` vs as `umem`:

| form | wire size | committed instances | prove |
|---|---|---|---|
| `map_op` (chip-bearing) | **132.4 KiB** (135,578 B) | `[2,6,3]` = main + chip(2⁶) + byte | 74 ms |
| `umem` (no chip)        | **68.0 KiB** (69,672 B)  | `[2,4,3,3]` = main + byte + umemory + umem_boundary | 9 ms |
| **delta** | **−64.4 KiB, ratio 0.514 (−48.6%)** | chip dropped | |

`ir2_umem_vs_map_size_probe` — one write + read-back:

| form | wire size |
|---|---|
| map-write | 131.8 KiB |
| **umem write+read** | **67.6 KiB** |
| absent (non-membership) | 161.8 KiB |

So the headline numbers are **measured and reproducible**: the 67.6 KiB umem figure matches the
doc exactly; the map comparand drifted slightly (committed `128.7` → measured `131.8`, a config
change), and the **−48.6% chip-drop reproduces to the decimal**. (`UMEM-PRIMITIVE.md:39`,
`UMEM-CROSS-REVIEW.md:19` cite these; both now grounded.)

**The "~130,000×" claim**: not present anywhere in `docs/`; it lives only in memory and refers
to per-turn *commitment* cost (the `lean_object*` FFI + sparse-Merkle work of the
perf-kernel-supply epoch), NOT umem proof size. Treat it as out-of-scope for umem efficiency.

### What the benchmarks do NOT measure

These are **isolated synthetic descriptors** (4 rows, 4–6 columns, hand-built `UMemOpSpec`/
`MapOpSpec`), not a real per-turn proof. The headline `effect-vm` per-turn proof is **451.7 KiB**
(`.docs-history-noclaude/PROOF-ECONOMICS.md:20`). The −48.6% is a per-*op-leg* figure on a probe
that contains *only* that leg. It does not (and does not claim to) measure a real deployed turn.

---

## 2. The static column / constraint / chip comparison (the deterministic core)

Parsed from the deployed staged registries, matching members by name (54 members common to
both; `rotation-wide-registry-staged.tsv` = the per-map "bare wide" baseline at the 8-felt
commitment, `rotation-wide-umem-welded-registry-staged.tsv` = the umem-welded form — **STAGED**, the
target of the gated VK epoch, *not* yet the deployed prover default (the executor observation bridge is
on; the welded VK is not flipped):

| metric (summed over 54 matched members) | bare wide (per-map) | umem-welded | Δ |
|---|---|---|---|
| trace width | 47,632 | 48,010 | **+378 (+0.8%)** |
| table instances | 270 (5/member) | 378 (7/member) | **+108 (+2/member)** |
| constraints | 8,884 | 8,938 | **+54 (+0.6%)** |

Per-member table sets (e.g. `transferVmDescriptor2R24`):

```
bare:  main(817) + poseidon2_chip(20) + range(1) + memory(5) + map_ops(5)
weld:  main(824) + poseidon2_chip(20) + range(1) + memory(5) + map_ops(5)
                 + umemory(8) + umem_boundary(7)          ← purely ADDED
```

**The decisive static fact: 0 of 54 welded members drop the chip or the map_ops table.** The
deployed weld is *additive* — it carries the per-map machinery AND the umem witness side by
side. This is deliberate (`descriptor_ir2.rs:90-93`: the full per-map "table-collapse … is
flag-day work … rides THE ONE ROTATION … never before it") and is why the weld can verify
identically to bare wide while threading the umem witness. But it means the proof-shrink the
benchmarks demonstrate **is not what the deployed path achieves today** — the deployed path pays
a small overhead.

**Why the chip can't just be dropped for real effects:** the umem *interior* Blum trace is genuinely
"zero intra-proof hashing," but the umem *boundary* still binds its init image to committed
roots via a `MapOp::Read` per touched key, and the whole-image fold rides a `MapKind::Insert`
chip chain (`descriptor_ir2.rs:96-128`). Boundary reconciliation stays map-op-shaped "once per
touched key per proof" (`UMEM-CROSS-REVIEW.md`, `descriptor_ir2.rs:90`). Real effects ALSO carry
genuine state-recompute hashing, so they keep a chip table regardless. The chip-drop only fully
materializes for a **memory-only descriptor** — pure bookkeeping with no recompute hashing
(transient scratch, an isolated c-list leg) — which is exactly the shape the micro-probe builds
and the deployed effects are not. Memory itself flags this: *"proof-shrink stays latent (−48.6%
chip-drop, needs a memory-only descriptor — circuit work)."*

A second, more deployment-relevant lever exists and is asserted (not re-run here):
`ir2_umem_cohort_vs_general_boundary_size` shrinks the boundary AIR from width-38 to width-9 for a
single-address leg (sound by `nodup_singleton`/`universal_memory_sound_single`,
`UniversalMemory.lean:236`). This one compounds up the IVC fold, so it is the lever more likely to
pay on the real aggregation path — worth measuring end-to-end before the flag-day.

---

## 3. Is it good protocol design? (vs how the field does ZK state)

**The technique is correct and standard.** Offline/Blum memory-checking — prove a single
multiset-permutation balance over `(addr, val, prev_val, serial)` access tuples instead of a
Merkle opening per access — is exactly how modern zkVMs (Jolt, and the lookup-centric SP1/RISC0
lineage) handle RAM. umem IS this technique, applied to protocol state: one global `Domain×κ`
address space, one Blum balance (`universal_memory_sound`, `UniversalMemory.lean:210`,
`#assert_axioms`-clean), tag-isolation proven so many domains coexist in one trace
(`consistentFrom_filter/_strip`), sorted-Poseidon2 boundary. The Lean foundation is real and
clean (32 theorems). As an *application of a known-good technique*, this is good design, not a
home-grown gamble.

**The unification is architecturally cleaner than per-map** — one universal argument vs five
separate sorted-Merkle map tables (cap / nullifier / heap / index / record-digest), each with its
own reconciliation. Collapsing them removes duplicated boundary-reconciliation machinery, and the
per-op micro-win (−48.6% when the chip drops) is genuine. The catch is purely about *realization*:
the now-deployed form is an additive overlay (§2), so the architectural payoff — the table collapse —
is **still pending, not delivered**. You currently pay the abstraction's cost (two extra tables, a new
soundness-critical AIR family, the boundary-binding leg) without yet collecting its proof-size
dividend.

**Honest design verdict:** good, field-aligned technique; the unification is the right *eventual*
shape; but it is being **justified on the wrong axis**. The −48.6% proof-shrink is real,
reproducible, latent, and modest in absolute KiB at per-turn scale — it is not a compelling reason
on its own, and the per-map approach is already deployed, proven, and adequate for today's effect
set. The compelling reason is **capability**: passable/composable/checkpointable *witnessed*
memory, which the per-map tables structurally cannot express (see §4).

---

## 4. Is the complexity justified? (the 10× flag-day refusals)

The umem flip has been refused **10 times** (memory: `project-umem-as-primitive-epoch.md`), each
a real deployed-correctness defect caught by the gate — missing verifier leg (6th), domain-2
`OodEvaluationMismatch` (7th), present-table-set mismatch on `setPerms`/`setVK` (9th), a
pre-existing 31-bit cap-open waist (10th). This is a lot of soundness-critical surface
(`turn/src/umem.rs` 2,636 lines, `circuit/src/descriptor_ir2.rs` 7,545 lines, 17 dedicated umem
test files). Two honest readings:

**(a) genuine depth.** The refusals are the gate working: each found a real defect before
flag-day, and several (the 31-bit cap-open waist, `node/src/turn_proving.rs:1140`) are soundness
fixes worth doing regardless of umem. The discipline is sound and the defects were real.

**(b) over-engineering for the stated efficiency goal.** Per-map is already live, proven, and
fine. If the *only* goal were proof efficiency, the −48.6% is latent on the deployed path and the
absolute per-turn saving is unproven (no real-turn benchmark, only micro-probes). Ten refusals
across a soundness-critical path is a high price for a deferred, micro-scale, currently-unrealized
size win. On the efficiency axis alone, **the per-map approach was fine and umem is premature.**

**Weighing them:** the complexity is justified IF and ONLY IF the value is the **capability
surface**, not the efficiency. The five revolutions (time-travel = restore-a-boundary;
continuations as passable umems; membrane field-granular fork/stitch; agent-memory checkpoint;
checkpointable confined-runtime) are things the per-map tables cannot do — memory as a
first-class, passable, witnessed object. Those are real and load-bearing in the cockpit
(`b1bd3305`/`087a4cd7`/`8334fffa`/etc.). If dregg wants witnessed time-travel and passable
computation, umem is the right primitive and the complexity buys something per-map never could.
If dregg wanted *only* a cheaper state proof, this is over-engineered and the −48.6% headline
oversells it.

**Recommendation for the honest story:** sell umem on **capability** (passable/composable
witnessed memory) and on the **architectural unification** (one argument, table-collapse as the
eventual win), not on the −48.6% chip-drop. With the observation bridge on by default but the welded
prover still STAGED (per-map remains the deployed default), the still-open lever is to either (i)
measure a REAL deployed turn umem-vs-per-map (not a
micro-probe) so the proof-size claim is grounded at deployment scale, or (ii) commit to the
table-collapse form (drop the per-map tables for the descriptors that can) so the win is actually
realized rather than an additive overlay that regresses size by +0.8%.

---

## Sources (file:line, verified at HEAD)

- Benchmarks: `circuit/tests/effect_vm_ir2_size_measure.rs` (`ir2_mapop_interior_to_umem_chip_drop`
  :574, `ir2_umem_vs_map_size_probe` :159, `ir2_umem_cohort_vs_general_boundary_size` :752).
- Re-ran at HEAD: `cargo test -p dregg-circuit --release --test effect_vm_ir2_size_measure`
  (the `recursion` feature in the test header is stale/gone; the test compiles by default).
- Deployed registries: `circuit/descriptors/rotation-wide-registry-staged.tsv` (per-map baseline),
  `circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` (umem flag-day target).
- Circuit AIR: `circuit/src/descriptor_ir2.rs` — `Ir2Air::UMemory/UMemBoundary` (:1809), the
  additive boundary note (:90-128), `BUS_UMEM_*` (:282).
- Executor bridge: `turn/src/umem.rs` — `project_executor_state` (:513), `fold` (:1062),
  `emit_trace`/Blum trace. **The executor observation bridge is ON by default**
  (`umem_witness_enabled: AtomicBool::new(true)`, `turn/src/executor/mod.rs:1008/1070/1114` — the G4
  observation epoch, the deployed executor *witnesses* the umem boundary). The umem-**welded proving
  registry / VK stays STAGED**: per-map remains the deployed prover default until the gated VK epoch
  (`sdk/src/full_turn_proof.rs`: "STAGED … no VK bump, no default flip, `umem_witness_enabled`
  untouched"; `turn/src/executor/proof_verify.rs:1162`). Do not read the observation flag as the VK flip.
- Lean: `metatheory/Dregg2/Crypto/UniversalMemory.lean` — `universal_memory_sound` (:210),
  `_single` (:236).
- Per-turn baseline: `.docs-history-noclaude/PROOF-ECONOMICS.md:20` (451.7 KiB `effect-vm`).
</content>
</invoke>
