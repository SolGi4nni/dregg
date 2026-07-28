# FRI: a genuinely secure parameterization, and the price of every knob that gets there

**Measured 2026-07-27.** Ledger arithmetic: `metatheory/Dregg2/Circuit/FriCommitPow.lean` (new) over
`FriLedger.lean` / `FriLedgerSound.lean` / `FriDeployedHeightPairing.lean`. Grind cost:
`circuit/tests/commit_pow_cost_measure.rs` (new). Extension-degree cost:
`docs/reference/EXT-DEGREE-COST.md` (existing, measured).

---

## ⚑⚑ CORRECTION, 2026-07-28 — READ THIS BEFORE §3. ROWS **D** AND **E** DO NOT RUN.

This document was written from ledger arithmetic. When the flip was attempted — flip the deployed
config to row **D**, prove one real proof at it — **rows D and E turned out to describe configs the
prover cannot be handed**, and they are the only two ≥100 rows here that needed no ember-gated step.
The instrument is `circuit-prove/tests/fri_hundred_bit_cutover.rs` (new): it hands each candidate to
the real `create_recursion_config_with_fri` and makes it carry a real workload end to end.

**Two facts a `FriParams` cannot carry, and neither was checked:**

1. **`log_blowup ≥ 3` is a hard floor on BOTH halves of the wrap path.** plonky3 splits `Q(x)` into
   `2^⌈log₂(deg−1)⌉` chunks and evaluates the trace on a domain that size
   (`uni-stark/src/prover.rs:197-208`). The IR-v2 batch's own **frozen, symbolically-computed**
   degree budget is **8** (the `setFieldDyn` slot gate) with the Poseidon2 chip at **7** —
   `circuit/src/descriptor_ir2.rs::ir2_degree_budget`, a `#[test]`, not a comment. The p3-recursion
   circuit AIR carries the degree-7 `x⁷` S-box. So `logBlowup 2` (row D) and `logBlowup 1` (row E)
   are **illegal**, not merely unusual.
2. **The wrap trace is `2^16` NATURALLY, not `2^15` padded.** §3 assumed *"the measured natural
   running-fold height is `2^15`, so the `2^16` floor is pure padding"*. Measured off a real
   leaf-wrap output proof's `degree_bits`: **`[10, 9, 16, 14, 16]`** ⇒ `2^16`, `|D⁽⁰⁾| = 2^22`. The
   `[9,9,15,14,15]` §3 quotes is the **accumulator's aggregation fold** — a different circuit.
   `WRAP_LOG_CEIL` is a FLOOR, so lowering it cannot shrink a table that is naturally `2^16`.

**What survives.** At `extDeg = 4`, on the geometry the prover runs (`logBlowup ≥ 3`,
`|D⁽⁰⁾| = 2^19` at the lowest legal blowup over the measured `2^16` trace), the commit branch is
`68`, so even at the full `30`-bit grind cap the composite is **at most 97 — for every query count
and every query-PoW**, because `ε_C` contains neither. That is
`FriCommitPow.ext4_cannot_reach_100_at_any_runnable_blowup_and_the_measured_wrap_height`, stated
`∀ q, ∀ pw`. `ext4_reaches_100_only_if_the_wrap_trace_shrinks_to_2e14` shows the ceiling is a fact
about the HEIGHT and not an impossibility: at a `2^14` wrap trace, `logBlowup 3 · 67 queries ·
commit_pow 29` reads **100**.

| geometry | max composite at `extDeg 4`, `lb ≥ 3`, `cpow ≤ 30` |
|---|---:|
| **`|D⁰| = 2^22` (deployed today, `lb 6`)** | 87 |
| `|D⁰| = 2^19` (`lb 3` over the **measured** `2^16` trace) | **97** |
| `|D⁰| = 2^18` (`lb 3` over a `2^15` trace) | 99 |
| `|D⁰| = 2^17` (`lb 3` over a `2^14` trace) | **101** |

**So ≥100 at `extDeg = 4` is not a knob turn.** It needs either a smaller recursion verifier circuit
or the degree-5/8 flag day — and the flag day is ember-gated (fresh Groth16 setup, on-chain re-key).
The flip was NOT performed. §4.2's *"cheapest path to ≥100 with no ember-gated step"* is **withdrawn**.

⚑ The generalisable lesson, and it is the reason this correction exists rather than a patch: §1.3
caught one runnability guard (the 30-bit grind cap) and the file then read as though runnability had
been handled. **A runnability guard that was checked does not imply the ones that were not.** The
only instrument that can tell a config the calculator likes from a config the prover runs is a real
proof at the real knobs.

---

## 0. THE RECORD, CORRECTED

> **"`FriLedgerSound.query_and_pow_cannot_pass_epsC` shows a ≥100-bit parameterization is
> impossible."**

**That is false, and it was never what the theorem said.** `query_and_pow_cannot_pass_epsC` is
scoped to exactly two knobs — `numQueries` and `powBits` — and proves they leave `ε_C` where it is.
That is true. Generalising it to "the commit branch cannot be moved" required an extra premise that
`FriLedger.lean`'s own text already flagged as false: there is a **third** grinding knob,
`commit_proof_of_work_bits`, which the file calls *"unpriced — a named residual, not a swept one"*.

Two things were wrong with the posture, and both are now priced in Lean:

| | defect | worth |
|---|---|---|
| **R1** | `commit_proof_of_work_bits` ships at `0` at all ten config sites and no column priced it | up to **+30 bits** on the binding branch |
| **R2** | the `min` composed the commit branch at `m = 7` against the Johnson branch at `m = ∞` — **two different `m`, so not ethSTARK eq. (20) at all** | **+7 bits** at the deployed knobs |

**A ≥100-bit configuration exists at `extDeg = 4`** — no field change, no VK rotation, no trusted
setup. `FriCommitPow.a_hundred_bit_parameterization_exists` is the constructive witness.
**≥128 is reachable, but not at `extDeg = 4`**: it needs the degree-8 extension.

---

## 1. WHAT `commit_proof_of_work_bits` ACTUALLY BUYS — the headline

### 1.1 It is real on the path dregg runs

| | prover | verifier |
|---|---|---|
| **native plonky3** (leaf wrap, recursion, prod v1, zk) | `fri/src/prover.rs:224` — `challenger.grind(params.commit_proof_of_work_bits)`, **inside the fold loop**, after the round commitment is observed and **before `β` is sampled** | `verifier.rs:222` — `check_witness` per round, plus a witness-count pin at `:206` |
| **gnark ETH wrap** (BN254, in-circuit) | n/a | `chain/gnark/fri_verify.go:117` and `fri_verify_native.go:351` call `CheckWitness(ch, cfg.CommitPowBits, frontend.Variable(0))` — **the witness is a hardcoded `0`** |

So on the **native** path it is a pure knob turn: fully implemented both sides, and
`circuit/src/plonky3_prover.rs:199` `create_config_with_fri_full` already exposes it.
On the **gnark** path it is *not* — the circuit passes a constant witness, which is only correct at
`0` bits, and `chain/gnark/apex_shrink_real_fixture_test.go:192` fails closed on
`CommitPowBits != 0`. Turning it on at the outer config is a circuit change and a fresh Groth16
setup.

### 1.2 What it is worth, and why that is a correction rather than an inflation

`ε_C` bounds the probability that a folding challenge `β` is bad. Under Fiat–Shamir a prover
re-samples `β` by changing a round commitment — or merely by finding a *second* valid PoW witness,
since `check_witness` admits many and each absorbs to a different state. Each redraw costs
`2^commit_pow` permutations, so the work to find a bad `β` is `2^commit_pow / ε_C`:

```
commit branch  =  −log₂ ε_C  +  commit_pow
```

This is the **same convention the Johnson column already uses**: `johnsonBits = q·lb/2 + powBits`
adds *its* grinding bits, and that `+ powBits` is only meaningful as a work factor. The two columns
were in different conventions and the `min` compared them anyway. Adding the commit term makes them
consistent; it does not invent a new optimism.

⚠ **It is not a discharged reduction.** There is no adversary object here — no more and no less than
for the `+ powBits` that has sat in `johnsonBits` since that column was written. If one is
laundering, both are. They are now at least laundering identically, which is the minimum a `min` of
two branches needs to mean anything.

### 1.3 ⚑ THE HARD CAP NOBODY HAD WRITTEN DOWN: 30 BITS

`grind` (`challenger/src/grinding_challenger.rs:107`) opens with

```rust
assert!((1u64 << bits) < F::ORDER_U64);
```

and the witness is a **single base-field element** (`type Witness = F`). Over BabyBear
(`p ≈ 2^30.91`) that caps **both** PoW knobs at **30 bits**. At 31 the prover asserts out.

This is load-bearing. The first draft of the ≥100 theorem in this campaign used `commit_pow = 34`,
read `100`, and **described a config no prover can produce** — the exact fake-green this repo has a
law against. `FriCommitPow.maxGrindBits_is_the_babybear_witness_cap` pins the cap to the modulus and
every config theorem carries `≤ maxGrindBits` as a conjunct, so the ledger can no longer quote an
ungrindable posture.

### 1.4 Measured cost

`circuit/tests/commit_pow_cost_measure.rs`. Measured whole-machine rate across two runs:
**0.85 M – 7.9 M witness trials/s**, conservative floor **0.85 M**. A single `grind`'s trial count
is geometric, so that spread is the distribution, not measurement error — the table below uses the
floor, which over-states cost, the safe direction for a knob being recommended.

`grind` is already SIMD-packed *and* rayon-parallel (`into_par_iter().find_map_any`,
`grinding_challenger.rs:166`), so this is a whole-machine figure with **no further thread multiplier
to apply** — a per-core rate times a core count would count the same parallelism twice.

Cost is `fold_rounds × 2^commit_pow` trials. **The verifier pays nothing**: one `check_witness` per
fold round, and the proof grows by one BabyBear element per round (**4 bytes/round**; 20–64 bytes
total at the shapes below).

| `commit_pow` | trials @ 5 rounds | wall clock | @ 16 rounds | wall clock |
|---:|---:|---:|---:|---:|
| 16 | 3.3e5 | 0.4 s | 1.0e6 | 1.2 s |
| 20 | 5.2e6 | 6 s | 1.7e7 | 20 s |
| 24 | 8.4e7 | 99 s | 2.7e8 | 317 s |
| 28 | 1.3e9 | 1 578 s | 4.3e9 | 5 074 s |
| 30 | 5.4e9 | 6 316 s | 1.7e10 | 20 297 s |
| **31+** | — | — | — | **ASSERTS OUT** |

(Divide by up to ~9× on a fast run; the fast-path readings put `cpow 28 @ 5 rounds` nearer 890 s.)

**Headline:** commit-PoW is nearly free up to ~20 bits, affordable to ~24, painful at 28–30, and
impossible above 30. It buys bits *one-for-one* on the branch that binds — but see §2.2: on the
**deployed geometry** it saturates at +10, because the Johnson branch then takes over.

---

## 2. THE DEPLOYED POSTURE, RE-READ

Deployed = `ir2_leaf_wrap_config()` — `logBlowup 6`, `19` queries, query-PoW `16`, arity `2`,
`extDeg 4` — at `|D⁽⁰⁾| = 2^22` (`WRAP_LOG_CEIL 16` × blowup `2^6`).

### 2.1 Three readings of the same config

| reading | commit branch | Johnson branch | composite |
|---|---:|---:|---:|
| the tree's (`m = 7` vs `m = ∞`) | 51 | 73 | **50** |
| m-consistent at `m = 7` | 51 | 71 | 50 |
| **m-consistent at `m = 3`** (the analyst's best choice) | **58** | **68** | **57** |

`m` is universally quantified in BCIKS20 Thm 8.3's hypothesis, so every `m ≥ 3` gives a true bound
and the best is ours to take. The circulating `50` is **7 bits pessimistic**, entirely from the
mixed-`m` composition. `FriCommitPow.the_deployed_composite_is_57`.

⚑ `57` corrects a number. It does not rescue a posture.

### 2.2 …and commit-PoW alone does not rescue it either

| deployed + `commit_pow` | commit branch | Johnson | composite |
|---:|---:|---:|---:|
| 0 | 58 | 68 | 57 |
| 16 | 74 | 68 | **67** |
| 32 (*over* the 30-bit cap — shown only to exhibit saturation) | 90 | 68 | **67** |

**+10 bits, then it stops.** The Johnson branch takes over the `min`. Passing 67 on the deployed
geometry requires buying queries as well — a different knob with a proof-size price.
`FriCommitPow.commit_pow_saturates_at_the_deployed_geometry` is the anti-inflation tooth.

---

## 3. THE CONFIG SPACE

Costs are relative to the deployed wrap. Prover ≈ LDE volume (linear in `|D⁰|`) × the measured
extension factor; proof ≈ query openings (`q` × per-round siblings + path) × the measured extension
factor. Extension factors from `docs/reference/EXT-DEGREE-COST.md` at deployed-realistic width:
**d=5 → +7 % prover / +4.6 % proof; d=8 → +25 % prover / +20 % proof.**

All rows take trace `2^15`, which `EXT-DEGREE-COST.md` §0.5 already recommends independently
(`WRAP_LOG_CEIL 16 → 15`, *"+2.00 proven bits and ~2× less apex prover work at zero wrap cost"*) —
the measured natural running-fold height is `2^15`, so the `2^16` floor is pure padding.

### 3.1 ≥100 bits

⚠ **Read the 2026-07-28 correction at the top first.** Rows **D** and **E** are `logBlowup 2` and
`logBlowup 1`; the deployed AIRs' constraint degrees force `logBlowup ≥ 3`, so **the prover cannot
be handed either.** They are struck below, not deleted, because how the error was made is the useful
part: every column in them is correct arithmetic.

| # | ext | lb | q | arity | qpow | **cpow** | \|D⁰\| | m | commit | john | **comp** | prover | proof | grind |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **A** | 5 | 4 | 48 | 8 | 16 | **4** | 2^19 | 3 | 102 | 101 | **100** | 0.13× | 0.96× | 0.0 s |
| **B** | 5 | 6 | 31 | 8 | 16 | **10** | 2^21 | 3 | 101 | 102 | **100** | 0.54× | 0.69× | 0.0 s |
| **C** | 8 | 6 | 29 | 8 | 16 | 0 | 2^21 | 11 | 172 | 101 | **100** | 0.62× | 0.84× | 0 |
| ~~**D**~~ | 4 | ~~2~~ | 110 | 8 | 16 | 28 | 2^17 | 3 | 102 | 101 | ~~100~~ | — | — | **UNRUNNABLE: `lb < 3`** |
| ~~**E**~~ | 4 | ~~1~~ | 307 | 8 | 16 | 24 | 2^16 | 3 | 101 | 101 | ~~100~~ | — | — | **UNRUNNABLE: `lb < 3`** |
| **D′** | **4** | **3** | 67 | 8 | 16 | **29** | 2^17 | 3 | 101 | 101 | **100** | — | — | ⚠ needs a **2^14** wrap trace; the measured one is **2^16** |

`D` and `E` were the **no-flag-day** rows. With both struck there is **no no-flag-day row**: at
`extDeg = 4` and the lowest legal `logBlowup 3`, the measured `2^16` wrap trace puts `|D⁰|` at `2^19`
and the commit branch at `68`, capping the composite at **97** for every `(q, pow)` even at the
`30`-bit grind cap. `D′` shows what would have to move — the *trace*, not a knob.

### 3.2 ≥128 bits

| # | ext | lb | q | arity | qpow | cpow | \|D⁰\| | m | commit | john | **comp** | prover | proof | grind |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **F** | 8 | 6 | 38 | 8 | 16 | 0 | 2^21 | 28 | 163 | 129 | **128** | 0.62× | 1.10× | 0 |
| **G** | 8 | 7 | 33 | 8 | 16 | 0 | 2^22 | 10 | 169 | 129 | **128** | 1.25× | 1.00× | 0 |
| **H** | 5 | 4 | 62 | 8 | 16 | **30** | 2^19 | 4 | 130 | 129 | **128** | 0.13× | 1.24× | 1–2 h |

**⚑ `extDeg = 4` cannot reach 128 at any knob setting.** The commit branch tops out at
`−log₂ ε_C ≤ 107` over *all* geometry (maximised at an absurd `|D⁰| = 2^1`), and `+30` of grinding
caps it at `137` only there; at any trace the tree actually runs, `+30` lands short. This is the
**true, narrow** version of the impossibility claim: not "≥100 is impossible", but *"≥128 is out of
reach at degree 4"*.

### 3.3 The commit-branch ceiling, per extension degree

| extDeg | \|F\| bits | ceiling, cpow 0 | + cpow 30 | reaches 100? | reaches 128? |
|---:|---:|---:|---:|---|---|
| 4 | 123.6 | 107 | 137 | **yes** (D, E) | **no** at any runnable trace |
| 5 | 154.5 | 138 | 168 | yes, ~free (A, B) | yes, expensive grind (H) |
| 8 | 247.3 | 231 | 261 | yes, cpow 0 (C) | **yes, cpow 0** (F, G) |

`extDeg = 8` is real upstream: `p3-baby-bear` implements `BinomialExtensionData<4>`, `<5>` **and
`<8>`** (`baby-bear/src/baby_bear.rs`). Degree 5 carries no extra two-adicity
(`EXT_TWO_ADICITY = 27`, empty generator table) — enough for the domains here, but check it before
committing to degree 5.

---

## 4. RECOMMENDATIONS

### 4.1 Cheapest genuinely-secure config: **F** — 128 bits, and the prover gets *faster*

```
extDeg 8 · logBlowup 6 · 38 queries · arity 8 · query_pow 16 · commit_pow 0 · trace 2^15 (|D⁰| = 2^21)
composite 128    prover 0.62×    proof 1.10×    grind 0
```

The prover is **cheaper than today** because the domain shrinks (`WRAP_LOG_CEIL 16 → 15`,
`2^22 → 2^21`) by more than degree 8 costs. `logBlowup 6` and `q = 38` are both values the tree
already ships elsewhere.

⚑ **Every row in §3 assumes arity 8**, i.e. the pending `INNER_FRI_MAX_LOG_ARITY 1 → 3` flip that
`FriDeployedHeightPairing` §5 records as *E2 reports GO*. That flip is what collapses the fold
count from 16 rounds to 5, which is most of why the proof sizes and grind costs above are tolerable.
It does **not** move the commit column at all (`arity_flip_does_not_move_the_commit_column`), so it
is orthogonal to the security arithmetic here — but the *costs* quoted do depend on it. At the
deployed arity 2 the grind costs multiply by ~3× (16 rounds instead of 5). At degree 8 the commit branch carries **35 bits of slack** and stops
binding at all — the posture becomes query-limited, which is the regime `numQueries` was always for.

**This is a flag day**, and here is exactly what it is:
- rebuild at `BinomialExtensionField<BabyBear, 8>` — `PROD_EXT_DEGREE` / `ZK_EXT_DEGREE` /
  `OUTER_EXT_DEGREE` / `RECURSION_EXT_DEGREE` are already named constants, but **27 `const D: usize
  = 4` sites** in `circuit-prove/src/` are inline and must move with them;
- every descriptor re-emits; every VK rotates; the chain re-genesises;
- **⚑ ember-gated:** a fresh Groth16 trusted setup and an on-chain re-key. `EXT-DEGREE-COST.md`
  measures the BN254 recursion circuit at **4 980 767 R1CS** with a 13-min / **23 GB** setup at
  d=4, and estimates **7.5 M – 12 M R1CS at d=8**. That is the real gate, not the STARK cost.

### 4.2 ~~Cheapest path to ≥100 with **no ember-gated step**: **D**~~ — ⚑ WITHDRAWN 2026-07-28

**There is no such path.** `logBlowup 2` is below the deployed AIRs' quotient-domain floor, so this
recommendation names a config the prover refuses. The paragraph is kept as written, struck, because
its own closing sentence — *"There is no free row at `extDeg = 4`; that is the honest finding"* —
was closer to the truth than the row it was recommending. What follows is the withdrawn text.

```
extDeg 4 · logBlowup 2 · 110 queries · arity 8 · query_pow 16 · commit_pow 28 · trace 2^15 (|D⁰| = 2^17)
composite 100    prover 0.03×    proof 1.75×    grind 0.9–26 min
```

Everything here is a `FriParameters` field plonky3 already honours and
`create_config_with_fri_full` already exposes. No field change, no VK rotation, no trusted setup,
no on-chain anything. The prover's LDE work drops ~30× (the domain goes `2^22 → 2^17`); the price is
a 1.75× proof and roughly 1–26 minutes of grinding per proof (rate-dependent; see §1.4).

**Judge that against where the config runs.** For a leaf or an apex shrink it is
plausible. For `Accumulator::accumulate`, which runs on **every fold**, it is almost certainly not —
in which case row **E** (1–5 min grind, 4.5× proof) trades the other way, and a 4.5× proof is itself
punitive for a *recursive* wrap because the next layer verifies it in-circuit. There is no free row
at `extDeg = 4`; that is the honest finding.

### 4.3 The middle: **A/B** — degree 5

`extDeg = 5` reaches 100 with a **trivial** grind (`cpow 4–10`, milliseconds) at +7 % prover /
+4.6 % proof — measured, not estimated. It is still a flag day (VK rotation, fresh gnark setup:
~120 R1CS per `ExtMul` vs 92 at d=4), but a much smaller circuit than degree 8, and
`EXT-DEGREE-COST.md` already recommends d=5 on independent grounds. **If the Groth16 re-setup is
happening anyway, do degree 8 and get 128 — the marginal cost over degree 5 is the R1CS count, and
the marginal benefit is 28 bits and the commit branch ceasing to bind.**

### 4.4 Knob turn vs flag day

| change | classification |
|---|---|
| `commit_pow 0 → k` on the **native** path (leaf wrap / recursion / prod v1 / zk) | **knob turn** — implemented both sides, already plumbed |
| `commit_pow 0 → k` on the **gnark ETH wrap** | **flag day + ember-gated** — the circuit passes a constant witness; needs a circuit change and a fresh Groth16 setup |
| `num_queries`, `log_blowup`, `max_log_arity` | **knob turn**, but proofs from different configs are not interchangeable — re-emit descriptors. The gnark sweep test refuses `lb·q + pow < 130`. |
| `WRAP_LOG_CEIL 16 → 15` | **knob turn**, independently recommended, +2 bits and ~2× less prover work |
| `extDeg 4 → 5` or `4 → 8` | **flag day, ember-gated** — 27 inline `const D = 4` sites, VK rotation, fresh Groth16 setup, on-chain re-key |
| choosing `m` | **not a knob at all** — an analysis parameter, free to optimise, worth 7 bits today |

---

## 5. WHAT DID NOT CHANGE, AND WHAT THIS IS NOT

- **No shipped config was flipped.** This is analysis plus a Lean ledger extension. Every row above
  is a reading of knobs the prover *can* be handed; none is a claim about what runs today. Turning
  one on is a separate, deliberate act.
  ⚑ **2026-07-28: that act was attempted, and it is what found rows D/E unrunnable.** Two of those
  rows were readings of knobs the prover *cannot* be handed — the sentence above was written in
  good faith and was false. What DID land from the attempt, none of it a knob move:
  `commit_proof_of_work_bits` is an exported `const` at all six shipped const blocks (it was ten
  inline `0`s that no gate could read, which is why no column priced it); `IR2_INNER_*` is `pub` and
  the params gate's `ir2_leaf_wrap_config` row reads the constants that config actually passes
  instead of a different config's; `create_recursion_config`'s in-circuit `FriVerifierParams` read
  the `RECURSION_FRI_*` consts instead of matching them by coincidence; `DEPLOYED_WORST_LOG_D0` is
  `WRAP_LOG_CEIL + IR2_INNER_LOG_BLOWUP = 22` (it was 19, adding one path's trace floor to another
  path's blowup — known wrong since 2026-07-20 and deferred); and the ledger export carries the
  composite so a caller can read the number rather than only Lean prove it.
- **The scope of `FriDeployedHeightPairing` carries over unweakened.** These are arithmetic
  statements about a formula transcribed from BCIKS20 and ethSTARK. **There is no adversary object
  anywhere in this tree**, the FRI extraction guarantee the apex consumes (`FriLdtExtractV3`) is
  still *assumed*, and none of these bits discharge it. "128 bits" here means *our calculator reads
  128 at these knobs* — never "the system has 128 bits".
- **`capacityBits` remains a refuted-conjecture drift canary** and is not used anywhere above.
- ⚑ **ONE UNRECONCILED NUMBER.** `docs/reference/FRI-BOTH-WIN-LEVERS.md` §4.4 prices
  `commit_pow 0 → 16` at **+1.45 bits** deployed; this document says **+10** (57 → 67). The
  *mechanism* agrees — both say it saturates when the Johnson branch takes over the `min` — and that
  is now a theorem. The saturation *point* does not: that doc's apex query column reads ≈ 59.43,
  the Lean-pinned Johnson branch reads 68 at `m = 3`. **68 is forced by the tree's own exported
  column**: `johnsonBits = 73` at `m → ∞`, and the finite-`m` penalty `q·log₂(1 + 1/2m)` cannot
  exceed `19 × 0.222 ≈ 4.2` bits, so no `α`-based query column lands below ≈ 68.8. I could not
  derive 59.43 from that `α` and have not established where it comes from.
  **`docs/reference/PROVEN-120-CONFIG.md` independently corroborates the column used here** — its
  `d=8, lb=6, q=36, pow=16 ⟹ λ = 122.60` is `(122.60 − 16)/36 = 2.961` bits per query against this
  document's `2.97` at the same blowup, and its *"deployed ceiling at `d = 4` is **57** at the
  apex"* is exactly `the_deployed_composite_is_57`. Two of three sources agree; the levers doc's
  59.43 is the outlier. **Flagged, not swept** — but §3 does not hang on it.
- The BCSS25 `O(n²) → O(n)` improvement is still **not** taken (worth +17 to +31 bits); it would
  need a composition into FRI's round structure that no public source performs. See `FriLedger.lean`.

---

## 6. WHERE THE CLAIMS LIVE

| claim | authority |
|---|---|
| commit-PoW moves the commit branch, `∀ k` | `FriCommitPow.commit_pow_moves_the_commit_branch` |
| the extension is conservative at `cpow = 0` | `FriCommitPow.commitPowBranch_at_zero_is_the_old_column` |
| the exported Johnson column over-claims at every finite `m` | `FriCommitPow.the_exported_johnson_column_overstates_at_every_finite_m` |
| deployed composite is 57, not 50 | `FriCommitPow.the_deployed_composite_is_57` |
| commit-PoW saturates at +10 on the deployed geometry | `FriCommitPow.commit_pow_saturates_at_the_deployed_geometry` |
| the 30-bit grind cap is the BabyBear modulus | `FriCommitPow.maxGrindBits_is_the_babybear_witness_cap` |
| ≥100 at `extDeg 4` **as arithmetic** (row D) — ⚠ at an unrunnable `lb` | `FriCommitPow.ext4_reaches_100_without_a_field_flag_day` |
| ≥128 at `extDeg 8`, `cpow 0` (row F) | `FriCommitPow.ext8_reaches_128` |
| the impossibility claim is false | `FriCommitPow.a_hundred_bit_parameterization_exists` |
| grind rate and per-`cpow` wall clock | `circuit/tests/commit_pow_cost_measure.rs` |
| extension-degree prover/proof/R1CS cost | `docs/reference/EXT-DEGREE-COST.md` |
| **⚑ `extDeg 4` cannot reach 100 on the runnable geometry, `∀ q, ∀ pow`** | `FriCommitPow.ext4_cannot_reach_100_at_any_runnable_blowup_and_the_measured_wrap_height` |
| **⚑ …and that ceiling is a fact about the TRACE, not an impossibility** | `FriCommitPow.ext4_reaches_100_only_if_the_wrap_trace_shrinks_to_2e14` |
| **⚑ `log_blowup 2` yields a proof that does not verify** (live tooth) | `circuit-prove/tests/fri_hundred_bit_cutover.rs::log_blowup_below_the_deployed_air_degree_floor_produces_an_invalid_proof` |
| **⚑ the deployed AIRs' frozen constraint-degree budget (8)** | `circuit/src/descriptor_ir2.rs::ir2_degree_budget` |
| **⚑ the wrap's MEASURED `degree_bits` / runnability of each candidate** | `circuit-prove/tests/fri_hundred_bit_cutover.rs` (sweep) |
| **⚑ the composite, READABLE by the caller who sets the knobs** | `FriLedger.friLedgerFFI` (9-in/10-out) → `dregg_lean_ffi::FriLedger::composite_bits` |
