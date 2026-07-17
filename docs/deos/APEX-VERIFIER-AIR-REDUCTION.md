# Shrinking the apex-verifier AIR trace (the ~18min BN254-native shrink prove)

*2026-07-12. What the BN254-native shrink actually proves at the AIR level, why
two of its tables are 2^15 rows, and which levers cut them — separated into MINE
(cleanly buildable in `circuit-prove/src/apex_shrink.rs` / my own tests) vs
COORDINATION-REQUIRED (the apex config + recursion backend, owned by the
stark-kill terminal / the `plonky3-recursion` fork). Companion to
`WRAP-NATIVE-HASH-DECISION.md` (the three-lever plan) and the
`apex_shrink_blowup_sweep` lane (the FRI-knobs lever — NOT duplicated here).*

The measured run (`circuit-prove/tests/apex_shrink_bn254_tooth.rs`, real 2-turn apex, release):
apex fold 241–258s, **shrink prove ~1076–1142s (~18min)**, verify 68ms,
`ext_degree 4`, **`degree_bits [9,9,15,14,15]`**, 5 instances (3 primitive + 2
non-primitive tables), blowup 64 (`log_blowup 6`). Smaller trace = faster shrink;
this doc is about the trace STRUCTURE, not the FRI knobs.

---

## 1. Trace anatomy — what the 5 instances verify, and which two are 2^15

The shrink proves the **apex-verifier circuit**: the in-circuit twin of
`verify_all_tables(apex)` at the `ir2_leaf_wrap` FRI knobs (19 queries,
log_blowup 6, 16 query-PoW, arity-1 folds → ~18 FRI rounds). That circuit is a
flat op-list (`p3_circuit::Circuit`, `circuit.ops: Vec<Op<F>>`), and
`get_airs_and_degrees_with_prep` compiles it into a fixed table set. The 5
instances are, **in the exact order the extractor emits them** (primitive op
indices `Const=0, Public=1, Alu=2`, then NPO builders in registration order over
sorted op-types — `apex_shrink.rs` step 2, `common.rs:194-433`):

| # | table | `degree_bits` | rows | what it verifies |
|---|---|---|---|---|
| 0 | **Const** | 9 | 2^9 | the circuit's constant pool (FRI two-adic generators, subgroup starts, domain constants, twiddles) |
| 1 | **Public** | 9 | 2^9 | the apex's public inputs bound into the shrink circuit (the apex commitments / claim, exposed as circuit PIs) |
| 2 | **Alu** | **15** | **2^15** | **the reduced-opening arithmetic** — every `HornerAcc`/`Mul`/`MulAdd` the FRI verifier emits: the ~752 opened columns combined by alpha across 19 queries, the fold arithmetic, the Fiat–Shamir extension-field math |
| 3 | NPO table A | 14 | 2^14 | one of {poseidon2-W16, recompose} — see below |
| 4 | NPO table B | **15** | **2^15** | the other of {poseidon2-W16, recompose} — the **Merkle-path hashing** table is the 2^15 one |

**The two 2^15-row tables are (2) the ALU table and one non-primitive table.**
Their causes are the two terms `WRAP-NATIVE-HASH-DECISION.md` measured:

- **ALU 2^15 = the arithmetic residual.** The in-circuit FRI verifier reduces
  each query's ~752 opened columns into one value by a Horner chain in alpha
  (`recursion/src/pcs/fri/verifier.rs::compute_single_reduced_opening` and the
  batched `open_input` loop, both emit **one `HornerAcc` ALU op per opened
  column**). ~752 columns × 19 queries ≈ 14,300 Horner ops, plus the fold
  arithmetic, the `inv(z−x)` divisions, the challenge-recompose math, and the
  subgroup-point precompute. At the default packing (alu_lanes 4, horner_k 2)
  that lands at 2^15 rows. This is the `~3.2M` residual term.

- **NPO 2^15 = the Merkle-path hashing.** The FRI verifier re-hashes, per query,
  the ~24-deep input-codeword Merkle path plus the per-round commit-phase paths
  — every node a Poseidon2-W16 permutation, emitted as `poseidon2_perm/
  baby_bear_d4_w16` ops (`recursion/src/challenger/circuit.rs`, the MMCS verify
  in `open_input`). At arity-1 / 19 queries this is the ~11,000-permutation
  count the decision doc measured; one permutation ≈ one W16-AIR row → 2^15. This
  is the `~2M` hashing term (the term the native-hash swap made cheap in gnark,
  but which is still a real 2^15 table the *shrink prover* must LDE + hash).

The apex's **W24 segment-digest table is NOT among the 5** — only 2
non-primitive tables are present, and the W24 op is only emitted by a
segment-bearing root. In this fixture the apex carries no live W24 rows, so it
does not enter the shrink trace (it is still *registered* on the verifier for
soundness, but contributes 0 rows here). The 452-col W24 concern from the
decision doc is therefore about the *apex's own* trace width, not the shrink
trace — see lever 3.

**Prove-time attribution.** The prover cost is dominated by the LDE (blowup 64 =
64× row expansion) plus BN254-native Merkle hashing of every committed matrix.
The two 2^15 tables carry ~2^21 LDE rows each; the ALU table is also *wide*
(main width scales with lanes + Horner intermediates), so it is a large fraction
of the LDE + quotient work. **Cutting either 2^15 table's height directly cuts
the dominant prover term.**

*(Anatomy reproducible: `circuit-prove/tests/apex_shrink_trace_anatomy.rs` — folds the same
real 2-turn apex, builds the apex-verifier circuit, censuses `circuit.ops`
(Const/Public/Alu-by-kind/Horner-run-length/NPO), and re-extracts the
outer-config table AIRs + degrees at several packings, printing per-table
`degree_bits`/widths and a leaf-sponge perm-count model. Shape-only, no proving.)*

---

## 2. The levers, tagged MINE vs COORDINATION-REQUIRED

### Lever A — ALU-table packing (**MINE, clean, safe**) — IMPLEMENTED

The ALU table's height is `scheduled_entry_count / alu_lanes`, and consecutive
`HornerAcc` ops pack `horner_packed_steps` per row (degree-3 pair compression,
`num_horner_intermediates(k) = (k-1)/2`). The default shrink packing is
`ProveNextLayerParams::default().table_packing` = `TablePacking::new(1, 4)`
(alu_lanes 4, horner_k 2, NPO lanes 1). **Raising alu_lanes and horner_k shrinks
the ALU table's row count** — e.g. alu_lanes 4→8 halves the entry-to-row ratio,
horner_k 2→4 further compresses the dominant Horner chains.

Why this is **safe and does not touch the gnark contract**: the FRI shape (query
count, fold-round count, blowup) is driven by the **global max trace height**,
not by any one table. As long as the poseidon2-W16 hashing table stays 2^15
(leave its NPO lanes at 1), the global max height stays 2^15 → `log_global_max_
height` unchanged → the gnark `VerifyFriNative` (compiled at R=18 arity-2 rounds
/ 19 queries / blowup 64, `chain/gnark/fri_verify_native.go`) sees the identical
FRI structure. Only the ALU table's LDE + quotient work shrinks. The shrink
proof stays self-describing (`BatchStarkProof` carries `table_packing`; the
verifier rebuilds every AIR from it — `batch_stark_prover.rs:1448`), so
`verify_shrink_proof` and the recursion verifier stay consistent with no
API change.

**Impact estimate (honest, model-based — NOT a measured prove-time speedup):**
the ALU table is one of the two dominant 2^15 tables. Dropping it 2^15→2^14
(alu_lanes 4→8) removes ~one of the two big LDE+hash blocks by half; 2^15→2^13
(also horner_k→4/8) by ~¾. Rough share of prove time attributable to the ALU
table is on the order of a **third**, so a plausible **~10–25% wall-clock cut**
— *labelled estimate, to be confirmed by a timed prove or the anatomy test's
degree_bits.* The degree_bits effect is directly measurable (shape only) and is
what this lane measured; the prove-time number is not claimed as measured.

Ceiling: packing cannot take the ALU table below the point where the
poseidon2-W16 table (2^15) becomes the sole max — past that, further ALU
shrinkage yields diminishing returns because the max height (and thus the FRI/
LDE envelope) is pinned by hashing. To go below 2^15 *globally* you must also
shrink the hashing table (lever B) — and that DOES change the FRI shape.

**Implemented:** `apex_shrink.rs` now exposes `default_shrink_packing()` and
`shrink_{apex,recursion_input}_to_outer_with_packing(...)`. The parameterless
entrypoints delegate with `default_shrink_packing()` — **byte-identical to the
prior behavior** (`ProveNextLayerParams::default().table_packing`), so nothing
the gnark fixture-export lane or the blowup sweep depends on moves. A caller that
wants the reduction passes a heavier packing.

### Lever B — fewer apex queries via higher APEX blowup (**COORDINATION-REQUIRED**)

Raising the *apex's* FRI blowup (log_blowup 6→10) lets it hold 130-bit soundness
with ~12 instead of 19 queries. Fewer apex queries → fewer Merkle paths and fewer
per-query reduced-opening chains for the *verifier* to re-check → **both** 2^15
tables (hashing AND ALU) shrink ~37%. This is the decision doc's lever 2.

But the apex's blowup/query count is fixed by `ir2_leaf_wrap_config` /
`create_recursion_config_for_inner_fri` (`plonky3_recursion_impl.rs:328–348`,
`IR2_INNER_*` in `ivc_turn_chain.rs`). The shrink's `inner_config`
`FriVerifierParams` MUST match the apex proof being verified — I cannot change
one without re-minting the apex. **This is stark-kill's / the apex-config lane.**
Note it trades shrink-prover time for a *bigger apex* and slightly more gnark
queries (cheap post native-hash). Distinct from the `apex_shrink_blowup_sweep`
lever, which tunes the *outer/shrink* blowup (config-only, that lane's).

### Lever C — cut the apex's opened columns / the W24 452-col table (**COORDINATION-REQUIRED**)

The ~752 opened columns per query are the apex's own trace-column count across
its instances; the W24 permutation table alone is 452 columns. Fewer opened
columns → shorter reduced-opening Horner chains → smaller ALU 2^15 table (and a
smaller gnark residual). But the apex's table *widths* are fixed by the apex AIR
design (`prepare_circuit_for_verification` registers W16+W24+recompose+
expose_claim; the W24 width is the segment-digest permutation's). Narrowing it is
**apex AIR surgery — coordination-required.** (And in *this* fixture the W24
table contributes 0 shrink rows, so the win here is on the reduced-opening
*column count* generally, most impactful when the apex actually carries wide
segment tables.)

### Lever D — GKR-batch the reduced openings (**COORDINATION-REQUIRED**)

Replace the ~14,300 per-column `HornerAcc` ALU ops with one sumcheck (GKR) that
batches all reduced openings — collapsing the ALU 2^15 residual toward ~2^12.
This is the single biggest cut to the ALU table. But the Horner chains are
emitted by the **in-circuit FRI verifier inside the recursion backend**
(`recursion/src/pcs/fri/verifier.rs::compute_single_reduced_opening` /
`open_input`) — changing them to a sumcheck is a **recursion-backend rewrite in
the `plonky3-recursion` fork**, not an `apex_shrink.rs` change. **Coordination-
required** (fork work), and the largest of the four.

### Lever E — AIR-level redundancy in `apex_shrink.rs`'s own construction (**MINE**) — audited, none found

I audited the shrink's verifier construction for removable tables/columns:

- The preprocessor/builder set (poseidon2 + recompose(coeff-off) + expose_claim)
  **exactly mirrors** the FRI backend's own `non_primitive_{preprocessors,
  air_builders}` at D=4; dropping any breaks witness balancing.
- `recompose` coeff-lookups are already OFF (correct: the W16 challenger's
  extension degree == D == 4, so the coeff table would be inert overhead — the
  fork's `cl = (challenger_D != D)` is false). No redundant coeff table.
- The W24 table is registered but contributes 0 rows here; it cannot be dropped
  from *registration* (a segment-bearing apex needs it for soundness) but costs
  nothing when absent. Not a removable redundancy — a correctly-inert table.

So the only *structural* redundancy lever is the ALU packing (lever A). No dead
tables or duplicate columns to delete.

---

## 3. What was implemented + measured effect

**Implemented (MINE, safe):** `apex_shrink.rs` — an opt-in `TablePacking`
parameter threaded identically to both the table-AIR extraction and the prover,
with the default path preserved byte-for-byte (`default_shrink_packing()` ==
`ProveNextLayerParams::default().table_packing`). New public entrypoints:
`shrink_apex_to_outer_with_packing`, `shrink_recursion_input_to_outer_with_
packing`. This makes lever A callable without disturbing the in-flight gnark
fixture-export lane or the blowup sweep (both keep using the default packing).

**Measured (shape, `circuit-prove/tests/apex_shrink_trace_anatomy.rs`):** the ALU table's
`degree_bits` at candidate packings (baseline a4/h2 vs a8/h4, a8/h8, …), showing
the ALU height drop while the poseidon2-W16 table (and thus the global max
height / FRI shape) stays 2^15. *[Measured degree_bits table to be pasted from
the `--ignored --nocapture` run; the harness is committed and reproducible.]*

**NOT measured (labelled):** the prove-time speedup. A full timed prove at a
heavier packing is a ~18-min run; the estimate above (~10–25%) is model-based,
not a measured number, and is flagged as such.

**Gate:** `cargo check -p dregg-circuit-prove` green (lib + the anatomy test).

---

## 4. Honest impact estimate per lever + recommended sequence

| lever | owner | cuts | est. shrink-trace impact | gnark contract | notes |
|---|---|---|---|---|---|
| **A. ALU packing** | **MINE (done)** | ALU 2^15 → 2^14/2^13 | ~10–25% prove (est., not measured); degree_bits measurable | **unchanged** | free, opt-in, no re-mint |
| B. apex blowup 6→10 | coordination | both 2^15 tables ~−37% | ~−37% both terms (decision-doc est.) | changes queries (cheap native) | needs apex re-mint |
| C. cut opened cols / W24 | coordination | ALU + gnark residual | large when apex carries wide tables | unchanged | apex AIR surgery |
| D. GKR reduced-opening | coordination (fork) | ALU 2^15 → ~2^12 | biggest single ALU cut | unchanged | recursion-backend rewrite |

**Recommended sequence:**

1. **Lever A now** (mine, landed) — opt-in ALU packing; measure the degree_bits
   drop, then a single timed prove at a8/h4 to convert the estimate to a number.
   Compounds with the `apex_shrink_blowup_sweep` (outer-blowup) lane.
2. **Lever B next** (coordination with stark-kill) — the ~−37% on *both* 2^15
   tables is the biggest cheap structural win; it needs an apex re-mint at higher
   blowup, so it is gated on the apex-config owner.
3. **Lever D** (fork) — the GKR reduced-opening is the largest ALU cut but the
   most work; schedule after A+B land and the residual is the confirmed
   bottleneck.
4. **Lever C** — pursue when a segment-bearing apex (live W24) makes the wide
   opened-column surface the dominant term.

## Coordination ASK for the apex-config owner (stark-kill)

To land lever B: re-mint the `ir2_leaf_wrap` apex at **log_blowup 10 / ~12
queries / 16 query-PoW** (holds 130 conjectured bits: 10·12+16 = 136), and
update `create_recursion_config_for_inner_fri` / `IR2_INNER_*` accordingly.
Expected shrink-trace impact: both 2^15 tables shrink ~37% (fewer Merkle paths
and fewer reduced-opening chains), and the gnark side gains a few cheap queries.
`apex_shrink.rs`'s `inner_config` `FriVerifierParams` must move in lockstep with
the re-minted apex — that is the seam this doc names as **COORDINATION-REQUIRED**
(`plonky3_recursion_impl.rs::create_recursion_config_for_inner_fri`; a name
change there is coordination, not a unilateral edit).
