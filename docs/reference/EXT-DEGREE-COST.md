# EXT-DEGREE-COST — what raising the BabyBear extension degree actually costs

**ember's question, verbatim:** *does ext-degree-8 slow dregg down a lot?*

**What this is.** The security side of the extension-degree decision was settled by
[`FRI-BOTH-WIN-LEVERS.md`](./FRI-BOTH-WIN-LEVERS.md) (§1.2): the proven ceiling is derived,
Lean-mechanized, and reproduces every anchor. The **cost** side was never measured — that doc's own
§3.5 says so in its own voice: *"Estimated 4→8 slowdown ≈ 1.3–1.6× — **an estimate, not a
measurement**."* A decision resting on a hand-waved cost column is a decision resting on intuition.

**This document measures it.** It changes no parameter, no config, no Lean, and nothing deployed.
It is a decision input.

**Reproduce:** `cargo test -p dregg-circuit-prove --release --test ext_degree_cost_measure -- --nocapture`
(`circuit-prove/tests/ext_degree_cost_measure.rs` — checked in, ~5 min).

---

## 0. Headline

1. **⚑ The native prover is NOT the cost gate, and the estimate was pessimistic.** MEASURED, at
   deployed-realistic trace width: **d=5 costs +7%, d=8 costs +25%** of prover wall-clock. Not 1.3–1.6×.
   The mechanism is now measured rather than asserted: **extension arithmetic is only ~14–18% of prover
   time** — the other ~82–86% is trace LDE, Merkle commit and quotient work, all base-field and
   D-invariant. That fraction is a **hard ceiling on how much degree can ever slow the prover**, and it
   is why an ext-multiply that costs **2.79×** more (also measured) buys only a **1.25×** slower prove.

2. **⚑ Proof size barely moves: d=5 = +4.6%, d=8 = +20%.** MEASURED, and stable to ±1 point across
   every shape tried. Field elements do scale with degree — but the proof is dominated by Merkle
   authentication paths and opened *base*-field values, neither of which D touches.

3. **⚑⚑ THE COST GATE IS THE GNARK WRAP, and it is not close.** The BN254 recursion circuit sits at
   **4,980,767 R1CS** (MEASURED, `docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md:22`) with a **13-minute,
   23 GB** Groth16 setup. Its `ExtMul` costs **92 R1CS** (MEASURED) against a `d² + d·reduce` model that
   reproduces 92 exactly ⟹ **~120 at d=5, ~216 at d=8**. Whole-circuit: **ESTIMATED ~7.5M–12M R1CS at
   d=8**. The binding resource is **setup memory**, not prove time. **The wrap is where the degree
   decision is actually paid, and the repo already owns the instrument to measure it instead of
   estimating it** (§3.4).

4. **⚑ d=5 is real, is supported, and is the sweet spot on cost — but it carries two teeth d=8 does not.**
   `W` collapses **11 → 2** at d=5 (VERIFIED at source), which makes its gnark reduction bound *tighter*
   than deployed d=4 (66 vs 68) — a genuine, counterintuitive win. But d=5 **loses two-adicity, 29 → 27**
   (d=8 *gains* it, → 30), and its non-power-of-two lane geometry costs more than its multiply price
   predicts (measured; §1.3). **Its proven bits are the real argument, not its cost.**

5. **⚑ The trace-height lever is strictly better value — and it is free.** `WRAP_LOG_CEIL 16 → 15` buys
   **+2.00 proven bits AND ~2× less apex prover work**, at **zero wrap cost** — the code's own comment
   concedes `2^15` is the natural max and `2^16` is "a safe pad" (`accumulator.rs:225-238`). **It should
   land first regardless of what is decided about degree**, because it is not on the same trade-off
   curve: it is the both-win, and degree is the trade.

> **The one-line answer to ember:** *No — degree 8 does not slow the prover down a lot; it costs ~25%,
> because 85% of proving is base-field work that degree cannot touch. The prover was never the gate. The
> gate is the gnark wrap, where d=8 is an estimated 1.5–2.4× constraint blow-up on a circuit whose setup
> already needs 23 GB — and **d=5 buys ~93 proven bits for ~7% prover and a materially smaller wrap
> rewrite**, which is why d=5, not d=8, is the recommendation.*

---

## 1. Native prover cost — MEASURED

### 1.1 What was measured, and what is a proxy

**REAL:** the prover. Every path a deployed prove takes — `Radix2DitParallel` LDE, the
Poseidon2-BabyBear `MerkleTreeMmcs` commit, quotient computation, the `TwoAdicFriPcs` FRI commit/query
phases, the `DuplexChallenger` transcript — is the pinned plonky3 (rev `82cfad73`), unmodified. Only the
`Challenge` type argument moves. **REAL:** the FRI knob-sets, both of them (`LEAF` =
`circuit::plonky3_prover::PROD_FRI_*`, lb 3 / q 38; `WRAP` = `ir2_leaf_wrap_config`, lb 6 / q 19,
`circuit-prove/src/ivc_turn_chain.rs:867-870`), at the `WRAP_LOG_CEIL = 16` height every running fold is
padded to.

**PROXY — state it plainly:** the AIR. The deployed leaf/apex are multi-table `p3-batch-stark` circuits
reachable only through `DreggRecursionConfig`, which **pins `D = 4`** at
`circuit-prove/src/plonky3_recursion_impl.rs:74` and ~30 sibling `const D: usize = 4` sites. Retargeting
those to D=5/8 **is the engineering this document is a decision input for** — so it cannot be a
precondition of the measurement. Instead: a **degree-7 AIR** (the deployed constraint-degree max, which
is what forces `lb ≥ 3`) at deployed-shaped height and width, through the identical engine.

**So: the RATIOS are the result; the absolute times are not the deployed leaf's.** That is exactly the
question asked — "does it slow us down a lot" is a ratio.

### 1.2 ⚑ The table

MEASURED. `min` of 3 timed repeats after an untimed warm prove (this box is shared; contention noise is
strictly additive, so the min measures the prover and the mean measures the neighbours — see §1.5).

| FRI knobs | trace | width | \|D⁽⁰⁾\| | **d=4** | **d=5** | **d=8** |
|---|---:|---:|---:|---:|---:|---:|
| LEAF (lb 3, q 38) | 2^14 | 32 | 2^17 | 345 ms — 1.000× | 420 ms — **1.217×** | 512 ms — **1.485×** |
| LEAF (lb 3, q 38) | 2^14 | **128** | 2^17 | 690 ms — 1.000× | 739 ms — **1.071×** | 857 ms — **1.242×** |
| **WRAP** (lb 6, q 19) | **2^16** | 32 | **2^22** | 10.5 s — 1.000× | 11.9 s — **1.137×** | 15.4 s — **1.472×** |
| WRAP′ (lb 6, q 19) | 2^14 | 32 | 2^20 | 2.6 s — 1.000× | 3.0 s — **1.160×** | 3.9 s — **1.515×** |
| WRAP′ (lb 6, q 19) | 2^14 | **128** | 2^20 | 5.1 s — 1.000× | 5.4 s — **1.075×** | 6.4 s — **1.274×** |

**Width was swept, not assumed** — and it is the one thing that moves the answer. Both directions were
arguable a priori: width scales the base-field column (LDE + Merkle) linearly, which *dilutes* D; but it
also scales the opened-values / reduced-opening work, which is EF-valued, which would *concentrate* it.
**Measured: width dilutes.** d=8 falls **1.49× → 1.24×** and d=5 falls **1.22× → 1.07×** going from width
32 to width 128, consistently at both FRI knob-sets.

⚑ **Deployed traces are WIDE** — the apex ALU table alone is ~752 opened columns
(`circuit-prove/src/apex_shrink.rs:141`, `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md`). **So the width-128
rows are the ones to quote, and even they are narrower than deployed** ⟹ the real deployed slowdown is
**at or below +7% (d=5) and +25% (d=8)**. These are conservative.

### 1.3 ⚑ The fraction — the ceiling on the whole lever

The ingredient, MEASURED on the same box (throughput, independent accumulator chains — bulk fold work,
not latency):

| D | ns/mul | vs d=4 | naive `O(d²)` predicts |
|---|---:|---:|---:|
| 4 | 2.832 | 1.000× | 1.00× |
| 5 | 4.027 | **1.422×** | 1.56× |
| 8 | 7.889 | **2.786×** | 4.00× |

*(SIMD beats the naive model, as `FRI-BOTH-WIN-LEVERS.md` §3.5 reported. Its aarch64 numbers were 3.58 /
4.19 / 10.91 ns → 1.00 / 1.17 / 3.05×; this box is faster in absolute terms and its d=5 is relatively
dearer, but the shape — **sub-quadratic, ~3× at d=8** — reproduces.)*

Now **solve** for the extension-arithmetic fraction `f` instead of asserting it. If wall-clock is
`T(D) = base + ext·r(D)` with `r` the measured multiply ratio, then `T(D)/T(4) = (1−f) + f·r(D)`:

| shape | f solved from d=8 | f solved from d=5 | agree? |
|---|---:|---:|---|
| LEAF w32 | 0.272 | 0.514 | **no** |
| LEAF **w128** | **0.136** | **0.168** | **yes** |
| WRAP 2^16 w32 | 0.264 | 0.325 | ~ |
| WRAP′ w32 | 0.288 | 0.379 | no |
| WRAP′ **w128** | **0.153** | **0.178** | **yes** |

> ### ⚑ **At deployed-realistic width, extension arithmetic is ~14–18% of prover wall-clock.**
> Two independent solves — one from d=5, one from d=8 — **agree** there, which is the check that the
> model is the right one. **~85% of proving is base-field and D-invariant.** This is a hard ceiling: even
> a *free* extension field could not make the prover more than ~1.2× faster, and a degree that made
> multiplies infinitely expensive could not make it more than ~6× slower. **Degree is a small knob on the
> prover, and now we know why, and by how much.**

This **CONFIRMS** `FRI-BOTH-WIN-LEVERS.md` §3.5's qualitative claim (*"trace LDE + Merkle dominate,
~70–85%, base-field, D-independent; only the FRI fold and DEEP reduce are `O(D²)`, ~10–20%"*) — the ~14–18%
measured lands inside its asserted 10–20% band. Its *numeric* estimate (1.3–1.6× at 4→8) is **pessimistic
by roughly a factor of two** on the width that matters: measured **1.24×**.

⚑ **The one place the model creaks — and it is d=5's tooth.** At width 32 the two solves disagree badly
(0.272 vs 0.514): d=5 costs **more than its multiply price predicts**. The multiply model says d=5 should
land at 1.11×; it measures 1.22× (w32). The natural reading is lane geometry — 5 is not a power of two,
and plonky3's NEON quintic path does 4 coefficients in-vector and the 5th on the scalar ALU
(`aarch64_neon/packing.rs:1113`), so d=5 carries a per-op overhead the microbench under-prices. **It
mostly washes out at deployed width** (1.07×, where the solves agree) — but it is a real effect, it is
d=5-specific, and it is why d=5's case rests on its proven bits, not on its cost.

### 1.4 Proof size and verify — MEASURED

| shape | d=4 | d=5 | d=8 |
|---|---:|---:|---:|
| LEAF w32 | 149,099 B | 156,890 B — **+5.2%** | 180,880 B — **+21.3%** |
| LEAF w128 | 170,622 B | 179,463 B — **+5.2%** | 206,055 B — **+20.8%** |
| WRAP 2^16 w32 | 107,141 B | 111,848 B — **+4.4%** | 126,562 B — **+18.1%** |
| WRAP′ w32 | 91,215 B | 95,314 B — **+4.5%** | 108,764 B — **+19.2%** |
| WRAP′ w128 | 103,812 B | 108,896 B — **+4.9%** | 125,027 B — **+20.4%** |

**Remarkably stable: d=5 = +4.6% ±0.4, d=8 = +20% ±1.5, across every height, width and FRI knob-set.**
The reason D does not double the proof at d=8 is structural: the wire is dominated by **Merkle
authentication paths** and **opened base-field values**, and `ExtensionMmcs` flattens EF to base and
delegates to the base inner MMCS — **no EF element is ever hashed**, so paths are D-independent. D moves
only the FRI commit-phase openings, the final poly, and the leaf *width* of the FRI trees.

**Verify time is a non-event**: 3.7 → 4.6 ms (LEAF w32), 2.6 → 3.1 ms (WRAP). D=8 costs ~0.5–0.9 ms.
**Native verify is not an argument in this decision either way.**

### 1.5 What could still be wrong with these numbers

Stated so they can be attacked:

- **The AIR is a proxy** (§1.1). Deployed is multi-table batch-STARK with LogUp; this is single-table
  uni-stark. Lookups add EF-valued work (LogUp fractions live in the challenge field), so the deployed
  `f` is plausibly **higher** than 14–18% — which would push d=8 above +25%. Bounding that needs
  `DreggRecursionConfig` parameterized in D, which is the very work being priced. **Named, not closed.**
- **The box is shared.** Mitigated by min-of-3 (the first draft of the harness took single samples and
  produced a *0.38× "speedup" from raising the degree* — a throttled d=4 sample. That is in the file's
  comments as a warning). The surviving numbers are internally consistent across five shapes.
- **aarch64 only.** The GPU prover path (`gpu_backend.rs`, `const D: usize = 4` at `:3702`) is **not
  measured here at all**. Its base/ext split may differ; a GPU that is memory-bound would hide D even
  further, but that is a guess and is labeled as one.

---

## 2. Is degree 5 / 8 actually supported? — VERIFIED AT SOURCE, not from the doc

`FRI-BOTH-WIN-LEVERS.md` claims *"plonky3 supports BabyBear degree 5 and 8 today, panics on 6"*. Checked
against the pinned rev, because the research could be wrong:

**CONFIRMED, and stronger than a claim — the harness in this document COMPILES AND RUNS a real prover at
D=5 and D=8 on the pinned rev.** That is not a table; it is an executed proof-and-verify at each degree.

`~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/baby-bear/src/baby_bear.rs`:

| d | impl | `W` | `DTH_ROOT` | `EXT_TWO_ADICITY` |
|---|---|---:|---:|---:|
| 4 | `:65` | **11** | 1728404513 | **29** |
| 5 | `:76` | **2** | 815036133 | **27** |
| 8 | `:92` | **11** | 420899707 | **30** |
| 6 | **absent** | — | — | — |

Two corrections to the standing docs fall out:

- ⚑ **`W` is NOT uniform across degrees — it is 2 at d=5, 11 at d=4 and d=8.** No doc says this, and it
  drives the gnark cost (§3.3). It is the single most load-bearing fact for a d=5 wrap rewrite.
- ⚑ **d=4's ext two-adicity is 29, not 28** (`FRI-BOTH-WIN-LEVERS.md` §3.7 says *"30 vs 27/28"*). So the
  real two-adicity story is **d=5 LOSES 2 (29→27); d=8 GAINS 1 (29→30)** — a genuine, unrecorded argument
  for 8 over 5.

**The `d ≤ 8` ceiling is REAL and hard** — `matrix/src/lib.rs:530-537` is not merely a `debug_assert`; it
is backed by a fixed `let mut coeff_accs: [T::Packing; 8]`, with the comment *"we set D to 8, which is the
maximum degree of the extension field supported"*. **8 is the top of this lever, full stop.**

⚑ **And plonky3's own security model argues for d ≥ 5**: `uni-stark/src/security.rs:157-158` does
`bits = min(bits, num_modulus_bits)` — it caps conjectured security by the challenge field size.
**d=4 → 123.6 bits, below a 128-bit target.** *plonky3 itself documents that our extension degree is too
small for 128.*

---

## 3. ⚑⚑ The gnark wrap — the real cost gate

### 3.1 The cost model, and why it is favorable

**Not emulated-field arithmetic.** A BabyBear element is **one BN254 `frontend.Variable`** holding a
canonical residue, with hinted reduction — the lazy-reduction trick (`chain/gnark/babybear.go:1-12`,
`:50-53`). No `gnark/std/math/emulated`, no limb decomposition. `BBExt = [4]frontend.Variable`
(`babybear_ext.go:23`). This is the favorable "small modulus inside a big field" regime and it sets
everything below.

The consequence that makes the model simple: **`api.Mul(constant, variable)` and every `api.Add` are FREE
in R1CS** (they fold into a linear combination). So an ext-mul costs only its `d²` cross-products and its
`d` reductions:

```
ExtMul(d) = d²·(api.Mul)  +  d·ReduceBounded
d=4:        16            +  4×19          =  92
```

**MEASURED: 92** (`HORIZONLOG.md:8468`, from `TestSettlementGadgetMarginalCosts`,
`chain/gnark/settlement_profile_test.go:396-412`; also `ExtAdd=64 = 4×16` ✓, `Poseidon2Bn254=240`).
**The model reproduces the measurement exactly**, which is what licenses extrapolating it:

| d | ExtMul R1CS | vs d=4 | ExtAdd |
|---|---:|---:|---:|
| 4 | **92** (MEASURED) | 1.00× | 64 |
| 5 | ~120 (COMPUTED) | **1.30×** | 80 |
| 8 | ~216 (COMPUTED) | **2.35×** | 128 |

### 3.2 Where the wrap's constraints are — MEASURED

`HORIZONLOG.md:8465-8475`, phase-stripped compiles; sums exactly to the total:

| phase | R1CS | share | d-scaling |
|---|---:|---:|---|
| transcript + pins | 182,306 | 3.7% | ~d (observe/sample) |
| STARK algebra | 472,860 | 9.5% | mixed |
| FRI core | 1,857,611 | 37.3% | **d²** (folds) + d-free Merkle |
| open_input | 2,467,990 | 49.6% | **mixed — `S_z` is d², `S_x` is d-LINEAR** |
| **total SettlementCircuit** | **4,980,767** | | |

| quantity | value | source |
|---|---|---|
| R1CS | **4,980,767** | `docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md:22` |
| Groth16 prove / verify | **16.7 s** / 2 ms | same |
| Groth16 **setup** | **13m11s / 23 GB** (at the older 12.2M circuit) | `HORIZONLOG.md:8375`, `docs/deos/ETH-NATIVE-WRAP.md:6` |
| VK / PK | **2,576 B** / 2.07 GB | `chain/gnark/fixtures/settlement_groth16.vk` |

### 3.3 ⚑ The whole-circuit estimate — ESTIMATED, and scoped as such

**A flat `d²` scaling of 4.98M is WRONG** and must not be quoted: `S_x` accumulates without a `W`
wraparound and is **d-linear** (`stark_open_input.go:456-458`); Merkle/Poseidon2Bn254 (240 R1CS × levels
× 19 queries) is **d-independent**; only `S_z`, the FRI folds and `ExtInv` are `d²`.

> **ESTIMATED: d=8 lands at ~1.5–2.4× ⟹ roughly 7.5M–12M R1CS.** d=5 ⟹ ~1.2–1.4× ⟹ **~6M–7M**.

**This is an estimate and is labeled one.** It is not fatal — **12.2M has been set up and proven before**
in this repo. But:

- ⚑ **It breaks the stated bar.** `dregg_outer_config.rs:130-133` frames a "~5M Groth16 ceiling"; the
  circuit already sits at 4.98M. **Any degree bump breaks that framing** — d=5 as surely as d=8.
- ⚑ **The binding resource is SETUP MEMORY, not prove time.** 23 GB at 12.2M. A d=8 wrap plausibly needs
  **~15–25 GB+** of setup peak. That is the number that decides feasibility, and prove time (16.7 s) is
  a rounding error next to it.
- **VK size is INDEPENDENT of d.** Groth16 VK size is a function of the public-input count only (IC =
  nPublic+1 G1 points); the wrap pins 26 public variables (`settlement_snark_test.go:94-96`) and all 25
  lanes are **base-field** (`stark_verify_native.go:228-229`). **VK stays 2,576 bytes at any degree.**
  What moves is the PK (2.07 GB, ∝ constraints) and the VK's *value* — a **full re-key across every
  consumer** (`chain/contracts/DreggGroth16Verifier25.sol`, the pinned `DreggApexRecursionVk`
  fingerprint at `apex_shrink_gnark_export.rs:192-233`).
- **Good news, verified:** the native leaf hash absorbs `2d` limbs against `blockLimbs = 16`
  (`fri_verify_native.go:128`) ⟹ **d ≤ 8 stays at ONE Poseidon2Bn254 permutation.** The leaf hash is
  d-free right up to 8. (The *emulated* path would double at d≥5 — but that path is the 40.9M legacy
  comparison, not what ships.)

### 3.4 ⚑ The estimate can be replaced by a measurement — and should be, before any rewrite

**The repo already owns the instrument.** `TestSettlementGadgetMarginalCosts`
(`settlement_profile_test.go:396-412`) isolates exactly the `ExtMul`/`ExtAdd` marginals, and the
phase-stripped profile gives the attribution. **It has simply never been run at d ≠ 4.** Parameterizing
`BBExt` and re-running the profile settles the d=5/d=8 wrap cost **empirically, before committing to the
rewrite** — which is the order `FRI-SOUNDNESS-FRONTIER-RESEARCH.md:640-647` (item 12) asks for anyway.
**That is the next lane, and it is small.**

### 3.5 The rebuild work, named

`FRI-BOTH-WIN-LEVERS.md:442` says *"~16 gnark files / 136 BBExt sites / four hand-unrolled kernels"*.
**Recounted: 20 files, 243 occurrences (149 non-test) — it undercounts on all three.**

**Mechanical** (the Go/Rust compiler catches every one): each `[4]` shape, `i<4` loop, `len/4`,
`4*i:4*i+4` slice, the fixture wire (`initial_eval: [u32; 4]`, `apex_shrink_gnark_export.rs:631`).

**3 genuinely unrolled kernels:** `ExtMul` (`babybear_ext.go:67-85`), `extMulRawInto`
(`stark_open_input.go:206-217`), `ExtFromBasisCoefficients` (`stark_verify_native.go:193-202`).
**+7 d-hardcoded circuit sites:** the `S_z` reduce block (`stark_open_input.go:287-296`), the `S_x`
accumulate+reduce (`:453-465`), `ExtInv`'s 4-in/4-out hint (`stark_verify_native.go:147-156`),
`friMerkleLeafHashNative`'s explicit 8-coord list (`fri_verify_native.go:148-152`), `friMerkleLeafHash`
(`fri_query.go:157-170`), `groupEF`/`sampleExt` (`settlement_circuit.go:288-299`), the type itself
(`babybear_ext.go:23`). **+4 host twins:** `bbExtRef`, `bbExtMulRef`, `bbExtFromBasisRef`, `bbExtInvRef`.

**Needs new derivation — nothing catches these:**

- **All four bound constants** (68 / 77 / 37; the 71 survives) — the silent-failure class.
- **`W`: 11 → 2 at d=5** — every `BBExtW` use, both sides. (d=8 keeps 11.)
- `bbExtInvRef`'s Fermat exponent `p^4 − 2` (`stark_verify_native_ref.go:48`, `big.NewInt(4)`).
- `DTH_ROOT` / `EXT_GENERATOR` / `TWO_ADIC_EXTENSION_GENERATORS` re-pin (values in §2).
- **Two independent `4`s in Rust that nothing links:** `OUTER_EXT_DEGREE = 4`
  (`dregg_outer_config.rs:125`) and a separate `const D: usize = 4` (`apex_shrink_gnark_export.rs:107`).

### 3.6 ⚑ The `ReduceBounded` hazard is ALREADY REALIZED — today, at d=4

`FRI-BOTH-WIN-LEVERS.md:445-450` names *the* hazard of a degree bump: *"`ReduceBounded(c0, 68)` — that
`68` is a soundness constant, not a type. The Go compiler will not catch a stale bound."* **Correct — and
it is not hypothetical. Two bound comments are wrong in the tree right now, before anyone touches the
degree:**

- `babybear.go:11-12` — *"q < 2^qBits (**qBits ≤ 38 here**)"*. **False:** `stark_open_input.go:292` calls
  `ReduceBounded(acc[0], 77)` ⟹ `rc.Check(q, 47)`.
- `babybear.go:84-85` — *"our widest accumulation is < 2^68"*. **False:** the widest is 2^77, same site.

**Not a soundness bug** — `ReduceBounded` takes `boundBits` as a *parameter* and constrains correctly, and
`q·p + r < 2^78 ≪ 2^254`. But it is [[feedback-a-doc-comment-is-a-name-not-a-proof]] exactly: **the
documentation of a soundness constant has already drifted from the constant.** Fix these before any
degree work, not during.

The exact derivation (COMPUTED), so the d=5/d=8 values are not guessed. Canonical `a_i,b_j < p < 2^31` ⟹
`a_i·b_j < 2^62`. The wraparound `X^d = W` gives `c0 = a0b0 + W·(a1b_{d-1} + … )` — one unwrapped product
plus `W` times `d−1` wrapped ones (`c0` is widest; the wrapped count is `d−1−k`, maximal at `k=0`):

```
boundBits(d) = 62 + ceil(log2(1 + W·(d−1)))
d=4, W=11:  1 + 11·3 = 34  ⇒  62 + 6 = 68   ✓ matches the code
d=5, W=2:   1 +  2·4 =  9  ⇒  62 + 4 = 66
d=8, W=11:  1 + 11·7 = 78  ⇒  62 + 7 = 69
```

> ⚑ **Counterintuitive and load-bearing: d=5 is TIGHTER than deployed d=4** (66 < 68), because `W`
> collapses 11 → 2. **The bound does not scale with `d` — it scales with `W·d`.** All stay far under
> `ReduceBounded`'s `>100` panic guard (`babybear.go:90-92`).

| site | d=4 (in code) | d=5 | d=8 |
|---|---:|---:|---:|
| `extMulRawInto` term (`stark_open_input.go:204`) | 68 | **66** | 69 |
| `S_z` block ×512 (`:274`, `:292-295`) | **77** | 75 | 78 |
| `S_x` block ×512 (`:399`, `:461-464`) | **71** | 71 | 71 — *no W wrap; d-independent* |
| `ExtFromBasisCoefficients` (`stark_verify_native.go:191-200`) | **37** | 35 | 38 |

### 3.7 The measurement gap in the wrap

Every gnark number above lives in **prose only** — no committed machine-readable output.
`settlement_profile_test.go` asserts **no absolute count** (its canary at `:209-214` compares twin-vs-real,
not against a golden), so **a 2× regression passes silently**. Both heavy tests are env-gated
(`DREGG_PROFILE=1`, `DREGG_SNARK=1`) and **gnark never runs in CI**
(`.github/workflows/armed-teeth.yml:90`, deliberately). `chain/gnark/README.md:42` still says "~12.2M
R1CS" — two generations stale. **A degree decision that lands on the wrap lands on an unguarded surface.**

---

## 4. ⚑ THE DECISION TABLE

Proven bits from the derived ceiling `30.907·d − 12.65 − 2·log₂(T) − 3.5·lb`
(`FRI-BOTH-WIN-LEVERS.md` §1.2), at the apex (`T = 2^16`, `lb = 6` ⟹ `|D⁽⁰⁾| = 2^22` — the artifact a
light client verifies). *(The brief quotes 61/93/186 at `T=2^19, lb=3`, the same `|D⁽⁰⁾| = 2^22` reached
by the other deployed knob-set — `62.48/93.38/186.11` before eq. (20)'s −1. Both conventions are in the
table so neither has to be trusted; the **deltas**, which are what the decision turns on, are identical:
**+30.91 bits per degree**.)*

| | **d=4 (deployed)** | **d=5** | **d=8** |
|---|---|---|---|
| **proven bits** @ apex `T=2^16, lb=6` | **57.98** | **88.88** | **181.61** |
| **proven bits** @ `T=2^19, lb=3` (the brief's) | **62.48** (~61) | **93.38** (~93) | **186.11** (~186) |
| **reaches 128 proven?** | **NO — at any q** | **NO** at these knobs; **yes** at short-trace/low-lb (§2 of the levers doc: ceiling 119.38 → short) | **YES**, comfortably |

⚠ **These "proven bits" rows are `m`-optimized CEILINGS (max λ, an upper bound), not the deployed
posture.** The machine-checked fixed-`m` ledger reads the deployed `d=4` apex commit column as **51 bits**
at `|D⁰| = 2^22` (`FriDeployedHeightPairing.deployed_wrap_commitBits`); the `57.98`/`62.48` here are the
ceiling and are refuted as the deployed number (`deployed_wrap_is_not_the_proven120_number`,
`deployed_wrap_is_not_61`). The **deltas** (+30.91 bits/degree), which are what this cost table turns on,
are unaffected.
| **native prover** (MEASURED, w128) | 1.000× | **1.071–1.075×** | **1.242–1.274×** |
| **native prover** (MEASURED, w32 — narrow, conservative) | 1.000× | 1.137–1.217× | 1.472–1.515× |
| **ext-arith fraction of prove** (MEASURED/solved) | ~14–18% | ~14–18% | ~14–18% |
| **ext-mul** (MEASURED) | 2.83 ns | 4.03 ns (1.42×) | 7.89 ns (2.79×) |
| **proof size** (MEASURED) | 1.000× | **+4.6%** | **+20%** |
| **native verify** (MEASURED) | 2.6–3.7 ms | +0.2 ms | +0.5–0.9 ms |
| **gnark ExtMul R1CS** | **92** (MEASURED) | ~120 (COMPUTED, 1.30×) | ~216 (COMPUTED, 2.35×) |
| **gnark whole circuit** | **4.98M** (MEASURED) | **~6M–7M** (ESTIMATED) | **~7.5M–12M** (ESTIMATED) |
| **gnark setup peak** | 23 GB @ 12.2M (MEASURED) | ESTIMATED ~12–15 GB | **ESTIMATED ~15–25 GB — the gate** |
| **gnark VK size** | 2,576 B | **2,576 B** (d-independent) | **2,576 B** (d-independent) |
| **gnark `ReduceBounded`** | 68 | **66 — TIGHTER** (W: 11→2) | 69 |
| **ext two-adicity** | **29** | **27 — LOSES 2** | **30 — GAINS 1** |
| **plonky3 today?** | yes | **YES** (`baby_bear.rs:76`; proven+verified in this doc's harness) | **YES** (`:92`; ditto) |
| **wrap rebuild** | — | ~20 files, 3 kernels + 7 sites + 4 twins, **4 bound constants, W 11→2** | same **minus** the W change |

**The alternative lever, for comparison** — not a degree row, a different axis entirely:

| move | proven bits | prover | wire | wrap cost | status |
|---|---|---|---|---|---|
| **`WRAP_LOG_CEIL` 16 → 15** | **+2.00** | **~2× LESS apex work** | 0 | **0** | **free — the code says 2^15 IS the natural max** (`accumulator.rs:225-238`) |
| `WRAP_LOG_CEIL` 16 → 14 | +4.00 | ~4× less | 0 | 0 | needs the 2^15 tables to fall first |
| **d=4 → d=5** | **+30.91** | **1.07× MORE** | +4.6% | **the whole rewrite** | plonky3 ready |
| **d=4 → d=8** | **+123.6** | **1.24× MORE** | +20% | the rewrite, bigger | plonky3 ready |

> ⚑ **These are not competitors — they compose, and they should be sequenced.** Trace height is the
> **both-win** (it buys bits *and* prover time, for free, because `|D⁽⁰⁾|` is simultaneously the LDE work
> unit and the numerator of `ε_C`). Degree is the **trade** (it buys the ceiling; it costs the wrap).
> **Do the free one first.** But note the honest asymmetry: **trace height buys 2–4 bits and degree buys
> 31–124.** Height cannot rescue d=4 — `2^16 → 2^14` at d=4 is 61.98 proven, still nowhere near 128.
> **Only degree moves the ceiling.** Height makes the apex cheaper and slightly sounder; degree decides
> whether 128 is reachable at all.

---

## 5. ⚑ Plain-English recommendation

**Is d=5 the sweet spot? — Yes, on the cost side, and it is the right first target.**

- It buys **~89–93 proven bits** — a comfortable floor, and ~31 bits above deployed — for a **measured
  +7% prover** and **+4.6% wire**. That is close to free on the axis ember asked about.
- Its wrap rewrite is **materially smaller than d=8's on constraints** (~1.3× vs ~2.35× per ExtMul; ~6–7M
  vs ~7.5–12M R1CS) — and the difference lands squarely on the **23 GB setup**, the binding resource.
- Its `ReduceBounded` bound is **tighter than deployed** (66 vs 68) because `W` collapses 11 → 2.
- plonky3 supports it; this document's harness **proves and verifies at it**.

**Two honest counts against d=5, both new here:** it **loses two-adicity 29 → 27** (d=8 gains, → 30), and
its `W: 11 → 2` means its wrap rewrite must touch **every `BBExtW` site on both sides** — work d=8 does
*not* need, since d=8 keeps `W = 11`. **So d=5 is cheaper to run and slightly more awkward to port.**

**And d=5 does not reach 128 proven at the apex's current knobs** (88.88). If the bar is *"128 proven
bits on the artifact a light client verifies"*, **only d=8 clears it** (181.61) — and d=8 costs a measured
**+25% prover / +20% wire**, which is **not "a lot"**. If the bar is *"a comfortable proven floor well
clear of the 58 we have"*, d=5 is the efficient answer.

> **⚑ That is the real question to put back to ember, and it is not a cost question:** *is the target 128
> proven, or a comfortable floor?* **The cost column no longer discriminates** — the prover delta between
> d=5 and d=8 is 7% vs 25%, and neither is a reason to choose. **Answer the bar, and the degree follows.**

**Is the wrap the true cost gate? — Yes, unambiguously, and it is the only thing in this document that is
still an estimate.** The native prover question is settled and the answer is "cheap": **degree cannot cost
more than ~1.2× on a prover that is 85% base-field work.** The gnark wrap is a 4.98M-constraint circuit
with a 13-minute, 23 GB setup, ~243 `BBExt` sites, four bound constants that fail *silently*, two of which
are **already documented wrong at d=4**, and a full VK re-key across every consumer.

**So the sequence:**

1. **`WRAP_LOG_CEIL` 16 → 15.** Free, both-win, +2 bits and ~2× less apex prover. Independent of the
   degree decision. Do it regardless.
2. **Fix the two stale `ReduceBounded` bound comments** (`babybear.go:11-12`, `:84-85`) and put a golden
   absolute R1CS count on `settlement_profile_test.go`. **Small, and it retires the silent-failure class
   before the degree work can land inside it.**
3. **Parameterize `BBExt` by degree and re-run `TestSettlementGadgetMarginalCosts` at d=5 and d=8.**
   This replaces §3.3's estimate with a measurement, for a fraction of the rewrite's cost, **before**
   committing to it. **This is the next lane and it is the one that actually decides.**
4. **Then choose the degree** — against a measured wrap cost and an answered bar, not against intuition.

**Nothing here is a recommendation to move the deployed degree.** The deployed d=4 stands. This is the
cost column ember asked for, measured.

---

## Provenance

| claim | label | source |
|---|---|---|
| native prover ratios, proof size, verify time | **MEASURED** | `circuit-prove/tests/ext_degree_cost_measure.rs`, min-of-3, pinned plonky3 `82cfad73` |
| ext-mul ns/mul | **MEASURED** | same file, `ext_mul_microbench` |
| ext-arith fraction ~14–18% | **SOLVED** from the two above (two independent solves agree at deployed width) | §1.3 |
| BabyBear d ∈ {4,5,8}, W, DTH_ROOT, two-adicity | **VERIFIED AT SOURCE** | `…/82cfad7/baby-bear/src/baby_bear.rs:65,76,92` |
| `d ≤ 8` hard ceiling | **VERIFIED AT SOURCE** | `…/82cfad7/matrix/src/lib.rs:530-537` |
| plonky3 caps security at `num_modulus_bits` | **VERIFIED AT SOURCE** | `…/82cfad7/uni-stark/src/security.rs:157-158` |
| gnark ExtMul = 92 R1CS, ExtAdd = 64, circuit = 4.98M, phases | **MEASURED (in-repo)** | `HORIZONLOG.md:8465-8475`; `docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md:22` |
| gnark `d² + d·reduce` model | **COMPUTED** — reproduces the measured 92 exactly | §3.1 |
| `boundBits(d) = 62 + ceil(log2(1 + W·(d−1)))` | **COMPUTED** — reproduces the deployed 68 | §3.6 |
| gnark whole-circuit R1CS at d=5 / d=8 | **⚠ ESTIMATED** — no per-phase d-attribution exists | §3.3, §3.4 |
| gnark setup peak at d=5 / d=8 | **⚠ ESTIMATED** | §3.3 |
| proven-bit ceilings | **DERIVED** (not measured, not mine) | `FRI-BOTH-WIN-LEVERS.md` §1.2, Lean-mechanized |
