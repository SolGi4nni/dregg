# dregg performance: the measured numbers

The wall-clock cost of every hot path in dregg, measured — not estimated. Each
number below comes from a real criterion bench in the `dregg-perf` crate driving
the crate's PUBLIC production API; `docs/PERF.md` is the recipe (how to run +
profile + capture a baseline), this document is the result.

The single fact this document exists to make concrete: **a turn that is only
*admitted* costs microseconds; a turn that is *proven* costs hundreds of
milliseconds.** The whole "prove every turn vs admit-then-prove-async" product
decision turns on that ratio, and it is ~10⁴–10⁵×.

```
cargo bench -p dregg-perf                    # the SMOKE suite (the numbers here)
PERF_FULL=1 cargo bench -p dregg-perf        # the FULL ladder (persvati capture)
```

## Machine + config

- **Host:** Apple M2 Max (12 logical cores), `bench` profile (optimized).
- **Prover:** Plonky3, BabyBear field, FRI `log_blowup` per `ir2_config` (lb=6,
  19 queries, 16 PoW bits for the IR-v2 multi-table batch); the rotated descriptor
  is the live EffectVM circuit under the `recursion` default.
- **Embedded executor:** the verified Lean kernel `libdregg_lean.a` linked in
  (`shadow_exec_full_forest_auth` = the `@[export] dregg_exec_full_forest_auth`).
- **Regime:** every number here is SMOKE (the single canonical transfer). The
  FULL ladder (`PERF_FULL=1`, the 1/4/16-effect + N-leaf sweeps) is the persvati
  capture; run it there for the scaling curves.

Numbers are the criterion median; the µs/ns legs are tight (±1%), the
seconds-scale proving legs are noisier (read them to two significant figures).

---

## THE HEADLINE: witness-only vs full-proving (one turn, every leg)

The `turn_witness_vs_proving` bench times all four legs of one transfer turn side
by side so the proving multiplier reads off directly.

| leg | what it is | cost |
|---|---|---:|
| `witness_only` (executor execute) | the node ADMIT path: state lookup, auth gating, effect apply, receipt + commitment — **no SNARK** | **7.0 µs** |
| `witness_gen` (effect-vm trace) | build the Effect-VM trace the prover consumes (whether or not a proof is then minted) | **319 µs** |
| `full_proving` (rotated `prove_full_turn`) | the real self-sovereign commit-path prove (rotated IR-v2 descriptor leg + recursion/PI-binding) | **147 ms** |
| `verify` (rotated `verify_full_turn`) | the light-client side: re-runs the in-circuit recursion verification | **149 ms** |

**The multiplier: `full_proving / witness_only` ≈ 147 ms / 7 µs ≈ ~21,000×.**

The proven turn's wire artifact is **~169 KiB** (postcard `FullTurnProof`, the
rotated path — `proof-sizes` bin); `docs/PROOF-ECONOMICS.md` carries the full
proof-byte breakdown + the FRI size/security grid.

Two consequences this measurement makes concrete:

1. **Admit-then-prove-async is the right architecture.** Admitting a turn is
   ~7 µs; the node can admit at >100k turns/s/core on this path and defer the
   ~147 ms proof to an off-lock async prover. Proving every turn inline caps
   throughput at ~7 turns/s/core.
2. **Verify is NOT cheap on the rotated path.** The rotated full-turn `verify`
   (~149 ms) is *as expensive as prove*, because it re-runs the in-circuit
   recursion verification rather than a bare FRI check. A light client pays
   ~149 ms per turn it independently verifies — see §"where verify cost lives".

---

## (a) Executor turn — witness-only vs full-proving

| bench | path | cost |
|---|---|---:|
| `executor_turn` | `TurnExecutor::execute` over a `Ledger` (two open cells, one transfer) | **8.2 µs** |
| `turn_witness_vs_proving/witness_only` | the same execute, co-located with the proving legs | **7.0 µs** |
| `turn_witness_vs_proving/witness_gen` | `generate_effect_vm_trace` (the prover's input) | **319 µs** |
| `turn_witness_vs_proving/full_proving` | rotated `prove_full_turn` (the live commit prover) | **147 ms** |
| `turn_witness_vs_proving/verify` | rotated `verify_full_turn` | **149 ms** |

The Rust `TurnExecutor::execute` and the verified Lean kernel commit (§d) are two
realizations of the same admit path; both are microseconds-scale and ~10⁴× below
the prover.

## (b) The rotated multi-table circuit — prove + verify per effect cohort

The `cohort_circuit` bench proves the EPOCH IR-v2 multi-table batch STARK (the
LIVE rotated commit circuit) across the distinct effect-cohort *table shapes* —
the chip-bearing map ops vs the no-chip universal-memory multiset. Each proof is
independently verified before its verify leg is timed.

| cohort | table shape | prove | verify |
|---|---|---:|---:|
| `transfer_5table` | graduated `transferVmDescriptor2`: main + poseidon2-chip + range + memory + map-ops, over a real transfer trace | **52 ms** | **3.9 ms** |
| `map_write_chip` | one in-place sorted-Poseidon2 write riding the chip bus | **227 ms** | 3.8 ms |
| `umem_write_read_nochip` | the same write+read as universal-memory ops — commits NO chip table | **14.9 ms** | **2.1 ms** |
| `absent_chip` | a sorted-Poseidon2 non-membership (the boundary-gap leg) | **137 ms** | 4.9 ms |

(the non-transfer rows are the `PERF_FULL=1` capture.)

The transfer cohort (the rotated EffectVM leg in isolation) proves in **~52 ms**
and verifies in **~3.9 ms**. This **~52 ms** descriptor leg is the floor of the
full-turn ~147 ms prove (§a): the remaining ~95 ms is the recursion-binding +
PI-binding main proof the rotated full turn wraps the leg in.

**Finding — the universal-memory economics, measured.** The chip-vs-no-chip
contrast is stark: a map-op that rides the Poseidon2 chip table (`map_write_chip`
~227 ms, `absent_chip` ~137 ms) proves **~10–15× more expensive** than the SAME
state intent expressed as universal-memory ops (`umem_write_read_nochip`
~14.9 ms), because the universal-memory shape commits NO chip table — the one Blum
multiset hashes nothing intra-proof. Verify is also cheaper for the no-chip shape
(~2.1 ms vs ~3.8–4.9 ms). This is the intra-proof half of the universal-memory
case, in wall-clock: moving boundary work out of the chip is the lever for the
per-turn prove cost.

## (c) Recursive aggregation fold

The `recursion_fold` bench times the bundle-tree fold — the Poseidon2
compress-chain that recursively folds N child digests into one aggregate root —
proven through the Lean-emitted `bundle_tree_fold_descriptor` (law #1) via the
multi-table batch STARK. This is the aggregation a joint turn / bundle pays to
collapse a fan-out of per-participant digests into one.

| fan-out | prove | verify |
|---|---:|---:|
| 2 leaves | **10.2 ms** | **2.4 ms** |
| 8 leaves | 14.0 ms | 2.2 ms |
| 32 leaves | 35.6 ms | 2.5 ms |
| 128 leaves | 98 ms | 2.8 ms |

(the 8/32/128 rows are the `PERF_FULL=1` capture.)

The fold **prove** scales sub-linearly with fan-out (~2× per 4× leaves: 10→14→36→98 ms
for 2→8→32→128), dominated by the compress-chain trace's degree. The fold **verify
is ~constant — ~2.4 ms regardless of bundle size** (2 to 128 leaves): the aggregate
proof is succinct, so verifying a 128-way fold costs the same as a 2-way fold. This is
the property that makes recursive aggregation worth its prove cost. The fold is the
cheapest of the three proving shapes (fold ~10 ms < descriptor leg ~52 ms < full turn
~147 ms).

## (d) Embedded-executor commit throughput (the node / seL4-PD hot path)

The `embedded_commit` bench times the verified Lean kernel commit the node and
the seL4 `executor` PD drive: `shadow_exec_full_forest_auth` over the GOLDEN
committing turn the firmament boots (`wideDemoState` + `gatedDemoTurn` — a
signed 30-unit transfer that body-commits `status:2 ok:1`, conserving asset 0,
100+5 → 70+35).

| leg | what it is | cost |
|---|---|---:|
| `forest_auth_transfer` | run the verified kernel, get the post-state wire (the on-device commit) | **157 µs** |
| `forest_auth_transfer_decode` | run it AND decode the verdict (`decode_shadow_verdict` — the full node ACCEPT decision) | **159 µs** |

The verified embedded commit is **~157 µs** — microseconds-scale, the same order
as the Rust executor (§a), confirming the verified Lean kernel is a viable inline
admit path (the ~22 µs of decode-on-top is negligible). The ~10⁴× gap to the
prover (§a) holds for the verified kernel too: admit verified-and-cheap, prove
async.

## (e) The deos desktop — the whole-system UI-render measure

The gpui cockpit's actual GPU FIRST-PAINT (a real lavapipe/Metal scan-out) is
captured on persvati (the cockpit is scanned out of the seL4 ramfb — see the
desktop keystone). What the `ui_projection` bench measures HERE — on any host,
without a GPU or window — is the whole-system cost the cockpit pays to HAVE
something to paint + the per-frame projection:

| leg | what it is | cost |
|---|---|---:|
| `demo_world_seed` | the FIVE real embedded `commit_turn`s (through the verified `DreggEngine`) that build the live provenance image the first paint renders | **5.8 s** |
| `demo_genesis_instant` | the genesis half: install the anchor cells + issuer well via the firmament fabric (NO turns) | **1.24 s** |
| `compose_scene` | `Shell::compose_scene` — the VERIFIED compositor scene (region/focus/source-root §5 discipline) the cockpit routes paint + input through | **102 ns** |
| `compose_paint_list` | `Shell::compose` — the ordered back-to-front paint list + per-surface trusted-path identity chrome the renderer turns into pixels | **472 ns** |
| `affordance_project` | `AffordanceSurface::project_for` — the per-viewer deos affordance projection (progressive attenuation) | **96 ns** |

The per-frame projection is **nanoseconds** — composing the scene (~102 ns), the
paint list (~472 ns), and projecting a viewer's affordances (~96 ns) are all far
below a 60 Hz frame budget (16.7 ms), so the compositor is never the bottleneck;
the GPU scan-out (measured on persvati) is.

The first-paint DATA cost is dominated by the embedded executor: building the
demo image runs five real verified commits (`demo_world_seed` ~5.8 s ≈ 5 × ~1.16 s
amortized per commit through the full `DreggEngine` + replay-tape re-execution),
and even the turn-free genesis (`demo_genesis_instant`) is ~1.24 s. This is why
the live cockpit opens its window on the *instant genesis* image first and seeds
the five turns asynchronously afterward (each cell appears live as its commit
lands) — the architecture the measurement validates.

---

## Supporting primitives (context)

| primitive | bench | cost |
|---|---|---:|
| Poseidon2 width-16 permutation | `poseidon2/permute_width16` | **1.37 µs** |
| Poseidon2 2→1 compression | `poseidon2/hash_2_to_1` | **2.8 µs** |
| Poseidon2 sponge (8 elems) | `poseidon2/hash_many_8` | **4.7 µs** |
| Effect-VM trace gen (base) | `trace_gen_base` | **400 µs** |
| Effect-VM trace gen (+ descriptor matrix) | `trace_gen_witness_ext` | **499 µs** |
| canonical cell commitment v8 | `commitment/canonical_v8` | **225 ms** |
| canonical cell commitment v9 (rotated) | `commitment/canonical_v9_rotated` | **157 ms** |

### Finding: the cell commitment is dominated by the cap-root Poseidon2 tree

`compute_canonical_state_commitment` is a blake3 envelope (which alone would be
microseconds), but it absorbs the **openable sorted-Poseidon2 capability root**
(`compute_canonical_capability_root`, cap Phase A). Building that full-depth
sorted-Poseidon2 Merkle tree — even over an empty capability set — is what costs
**~225 ms** (v8) / **~157 ms** (v9). The commitment, not the trace gen, is the
heaviest *non-FRI* per-turn primitive; it is a candidate for the same
witness-vs-recompute split the prover already uses (compute once, cache, prove
the delta), and it is the long pole of the genesis/first-paint cost in §e.

---

## Where verify cost lives (the rotated-path light-client cost)

The rotated **full-turn verify (~149 ms)** is two orders of magnitude above the
bare **multi-table descriptor verify (~3.9 ms, §b)** and the **fold verify
(~2.4 ms, §c)**. The difference is the in-circuit recursion verification the full
turn carries: `verify_full_turn` re-checks the recursion-binding proof, not just
the leaf descriptor STARK. A light client that only needs to check one leaf's
descriptor pays ~3.9 ms; one that verifies the full self-sovereign commit (the
recursion-bound turn) pays ~149 ms. This is the number the ARGUS light-client
story is grounded on, and the lever (a cheaper terminal verifier — the
Plonky3-native BN254 wrap, the EVM-bridge endgame) is where the verify cost gets
bought down.

## Where prove cost lives (the proving long pole)

Ordered by measured cost, the proving stack is:

1. **Full rotated turn — ~147 ms** = the rotated descriptor leg (~52 ms) + the
   recursion-binding / PI-binding main proof (~95 ms). The recursion wrap, not the
   leaf, is the majority of the per-turn prove.
2. **The rotated descriptor leg (IR-v2 5-table) — ~52 ms.** The EffectVM circuit
   in isolation; dominated by FRI + the LDE/Merkle commit over the chip table.
3. **The aggregation fold — ~10 ms** for 2 leaves; scales with fan-out.
4. **Witness gen — ~0.3 ms** and **the cell commitment — ~225 ms** (the cap-root
   tree; see the finding above — this is a non-FRI outlier worth its own lane).

The FRI knobs (blowup, query count) and the recursion terminal are the levers;
`docs/PROOF-ECONOMICS.md` carries the proof-SIZE economics + the FRI grid, and
`docs/PERF.md` the profiling recipe (flamegraph/samply on the `prove` bench).
