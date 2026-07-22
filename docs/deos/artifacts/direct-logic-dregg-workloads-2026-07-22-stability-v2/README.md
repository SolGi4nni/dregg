# DREGG direct-logic timing stability campaign v2

## Result first

The live prover timings are reproducible for a **fixed proof transcript**, but
they do **not** support a general source-to-optimized proving-speed claim.  The
consumer verifier is different: a separate seven-session sweep over every
accepting assignment finds stable, modest improvements—about 23% for Admission
and 9.7% for the shared Upgrade/Clearance shape—with the byte-identical Strand
control at 1.00.

Seven fresh-process sessions on a CPU-pinned persvati lane make the canonical
assignment ratios look extremely stable.  That stability is real clock
stability, but the proof-byte audit shows why it is not seven independent
cryptographic samples: all repeated proofs for one fixture are byte-identical.
The FRI configuration has `query_pow_bits = 16`; the captured Plonky3 prover
calls `challenger.grind(params.query_proof_of_work_bits)`.  A fixed descriptor,
trace, and public statement therefore fixes the Fiat-Shamir transcript and its
particular proof-of-work search.

Sweeping **every accepting Boolean assignment** for the three distinct
descriptor shapes exposes the confounder:

| shape | accepting assignments | optimized faster | opt/source prove ratio | PoW-witness/time Pearson |
|---|---:|---:|---:|---:|
| Admission | 3 | 2 | 0.325 to **9.412** | 0.991 |
| shared Upgrade/Clearance branch | 3 | 3 | 0.074 to 0.736 | 0.982 |
| Strand byte-identical null | 7 | 4 | 0.968 to 1.014 | **0.9997** |

Admission reverses direction: one optimized proof takes about 9.4 times the
source proof even though its relation is smaller.  Across the seven Strand
statements, the same byte-identical source/optimized descriptor takes roughly
16 to 224 ms depending on the transcript, while the paired source/optimized
ratio stays close to one.  The retained proof's public query-PoW witness ranks
these seven Strand times perfectly (Spearman 1.0).  This is direct evidence
that query grinding, not only relation size, dominates these tiny one-row
proving times.

The certified deterministic wins remain valid and are the evidence we should
publish without qualification: fewer columns, constraints, nonlinear
multiplications, auxiliaries, and smaller proof bytes for the selected
canonical statements.  Timing needs either grinding-disabled instrumentation
or a much larger randomized statement population before it becomes a causal
optimizer result.

## Four semantic workloads, three descriptor shapes

The benchmark names four real DREGG decisions:

1. `Exec.Admission.admissible` — a 12-atom admission shape;
2. `Upgrade.AuthorizedUpgrade` — a 4-atom shared-prefix branch shape;
3. `CredentialAttenuation.Clearance.admits` — the same descriptor shape as
   Upgrade, but a distinct production meaning and atom interpretation; and
4. `StrandAdmission.admitted` — a minimal 3-way disjunction and negative
   optimization control.

Upgrade and Clearance are not two independent compiler shapes.  Their source
descriptor bytes are identical to one another, and their optimized descriptor
bytes are identical to one another.  Their canonical assignments select
opposite branches, which changes the proof transcript.  Their fixed-statement
proving ratios were about 0.53 and 0.076 respectively.  That difference is a
particularly clean warning against reporting either ratio as “the” speedup.

## Fixed-transcript reproducibility campaign

The existing canonical benchmark source was not edited.  The exact release
binary was built once in the warm `proof-backend-seam` pbuild lane, then seven
fresh processes were captured.  Each process used:

- CPUs 22–23, two distinct physical compact cores on the AMD Ryzen AI 9 HX PRO
  370 (their SMT siblings were not exclusively reserved);
- `RAYON_NUM_THREADS=2` and the performance governor;
- 8 warmups per variant;
- 30 paired prove rounds and 100 paired verify rounds per workload;
- alternating source/optimized order, reversed on odd rounds;
- verification of every measured proof outside the timed prove interval; and
- one-second load, runnable-task, CPU-counter, and frequency telemetry.

This yields 210 prove pairs and 700 verify pairs per semantic workload: 3,640
paired rounds and 7,280 individual endpoint timings.  Load-1 ranged from 2.97
to 10.06 and the maximum sampled runnable-task count was 39.  Strand is the
byte-identical control.

`paired-summary.csv` uses within-round log ratios.  Its 95% intervals resample
whole process sessions as the outer unit and even/odd order strata within each
session.  These are correctly labeled `FIXED_TRANSCRIPT_*`; every row sets
`general_speedup_claim=false`.

| workload | stage | fixed opt/source ratio | 95% hierarchical interval |
|---|---|---:|---:|
| Admission | prove | 0.8234 | 0.8209–0.8256 |
| Upgrade | prove | 0.5313 | 0.5296–0.5323 |
| Clearance | prove | 0.0757 | 0.0756–0.0759 |
| Strand | prove | 1.0001 | 0.9980–1.0027 |
| Admission | verify | 0.7637 | 0.7626–0.7659 |
| Upgrade | verify | 0.9039 | 0.9014–0.9062 |
| Clearance | verify | 0.9025 | 0.9003–0.9069 |
| Strand | verify | 1.0004 | 0.9965–1.0027 |

The intervals say the machine protocol is reproducible.  They do not remove
the deterministic transcript/grinding confounder.

## Complete accepting-assignment sweep

`EmitTranscriptSweep.lean` imports the formal workload module and emits every
accepting assignment for each unique Boolean shape:

- three Admission assignments (`expiry-none`, `expiry-timed`, and an abstract
  both-true assignment—the last is a Boolean-skeleton case, not a realizable
  `Option` value);
- three shared-branch assignments (`left`, `right`, `both`); and
- all seven accepting Strand assignments.

For every source/optimized endpoint, `transcript-sweep.rs` alternates order,
proves ten times, verifies outside the timed interval, and retains every
postcard proof.  All ten repetitions of each endpoint have one unique hash,
confirming deterministic repeat proofs.  The exact assignment-level numbers
are in `transcript-sweep-summary.csv`; the shape census is in
`transcript-sweep-shape-summary.csv`.

`pow-witness-audit.rs` deserializes every retained proof and extracts
`opening_proof.query_pow_witness`.  The selected witness is constant across all
ten repeats of an endpoint.  Witness value and median time have Pearson
correlations 0.991 (Admission), 0.982 (branch), and 0.9997 (Strand); Strand's
rank correlation is exactly 1.0.  The challenger searches candidate witnesses
in parallel, so the witness is not asserted to be an exact serial iteration
count.  It is nevertheless an observed proof field whose near-perfect
association with elapsed time directly identifies grinding as the confounder.

For the direction-reversing Admission assignment, the source proof selects
witness 10,782 and takes 21.5 ms, while the optimized proof selects witness
120,205 and takes 202.2 ms.  The relation got smaller; the transcript got much
less lucky.

The branch shape is faster for all three accepting assignments in this census,
but three transcripts are too few to separate its deterministic relation-cost
reduction from proof-of-work luck.  Admission's direction reversal is enough
to reject a general timing claim today.

## Consumer-verifier result across the complete census

Verification checks the supplied PoW witness once; it does not perform the
prover's grinding search.  `verify-transcript-sweep.rs` therefore reuses the
retained proof for every accepting endpoint and measures only the actual
consumer `verify_vm_descriptor2` boundary.  Seven fresh processes each run 200
paired, alternating-order rounds per assignment after 20 warmups: 18,200
paired rounds and 36,400 verifier calls.

The verifier sweep remained CPU-pinned but was deliberately not described as
an idle-host capture: load-1 was 23.44 immediately before and 21.62 immediately
after, with concurrent Rust compilation visible in the retained host snapshots.
The tight paired ratios, agreement across seven fresh processes, and passing
Strand null are the controls that support the within-host comparison.

| shape | assignments | opt/source ratio range | result |
|---|---:|---:|---|
| Admission | 3 | 0.7690–0.7701 | optimized ~23% faster |
| shared branch | 3 | 0.9012–0.9042 | optimized ~9.7% faster |
| Strand identical null | 7 | 0.9993–1.0006 | null passes |

Every Admission and branch assignment has a hierarchical 95% interval below
one and all seven process medians agree in direction.  Every Strand interval
contains one.  Thus the honest performance statement is asymmetric:

- **proving:** no general ratio yet; query grinding dominates these tiny rows;
- **verification:** stable reductions across the complete accepting-assignment
  census for these exact descriptor shapes, backend, proof parameters, and
  host protocol.

This is a useful shipped-path result, but it is not a 10–100× result and it is
not an end-to-end DREGG turn benchmark.  Exact intervals are in
`verifier-transcript-sweep-summary.csv`; the shape verdicts are in
`verifier-transcript-sweep-shape-summary.csv`.

## Proof bytes and the actual tamper boundary

`proof-byte-audit.rs` independently retained five verified postcard proofs for
all eight canonical semantic/variant fixtures (40 files).  Within a fixture,
all five lengths and hashes are identical.  It also distinguishes two outcomes
that the canonical log's historical label combined:

- `producer_refused`; versus
- `consumer_verifier_rejected` after the release prover returned a proof.

All eight changed-public-input cases reached the second path: the **actual
consumer verifier rejected** every tampered proof.  See
`proof-byte-manifest.csv` and `proof-byte-summary.csv`.

Proof size is statement-dependent under postcard.  For example, Admission
source proofs in the sweep vary between 13,976 and 14,016 bytes.  The canonical
14,016→11,894 figure is an exact selected-statement measurement, not a
statement-independent proof-size theorem.

## No-proof Boolean baseline

`boolean-baseline.rs` times native Boolean evaluation after all production
atoms are already known.  Twenty-five batches of ten million evaluations land
between roughly 0.38 and 1.22 ns per skeleton evaluation on the pinned core.
The source/optimized direction can itself change with short-circuit behavior;
LLVM is allowed to optimize ordinary Boolean code.  This is intentionally not
a proof-system comparison.  It only establishes that these tiny Boolean
skeletons are negligible beside millisecond-scale proof construction, so a
claimed proof-system speedup must account for the prover, transcript grinding,
atom computation, batching, and amortization—not merely formula evaluation.

## Reproduction and integrity

The artifact is self-contained for its direct inputs:

- `inputs/generated/` contains every descriptor, trace, public vector, truth
  vector, and manifest used by the canonical benchmark;
- `inputs/formal/` contains the exact workload theorem source and canonical
  emitter;
- `inputs/rust/` contains the exact benchmark, DescriptorIR2 backend, and FRI
  prover/challenger sources showing the grinding call and candidate search;
- `inputs/Cargo.lock` and `inputs/rust-toolchain.toml` pin dependencies and the
  toolchain; and
- `exact-build-toolchain.txt` pins the compiler, Cargo, executable, lock, and
  source hashes.

`SHA256SUMS` covers every retained input, script, raw session, telemetry stream,
summary, and proof byte file.  Regenerate analyses with:

```sh
python3 analyze.py
python3 supplementary-analysis.py
python3 verify.py
shasum -a 256 -c SHA256SUMS
```

One partial process is preserved in `sessions/aborted-session-04/`.  Its parent
SSH orchestration window closed before timing samples began; it is excluded by
the analysis glob and is not silently counted.

## Honest boundary

This campaign measures one-row BabyBear BatchSTARK proofs of certified Boolean
skeletons.  The production atoms—hashes, arithmetic comparisons, membership,
capability lookup, lifecycle, and receipt binding—remain outside this new
Boolean compiler.  It is neither an end-to-end turn benchmark nor evidence for
ModulusZK's advertised 10–100× claim.  It is stronger evidence for our narrower
claim: the structural optimizer is certified and materially shrinks these
relations; verifier improvements survive the complete accepting census; and
prover elapsed-time ratios are transcript-sensitive and must not be marketed as
general proving speedups.
