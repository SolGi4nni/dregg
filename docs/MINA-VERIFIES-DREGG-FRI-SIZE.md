# Can a Kimchi circuit verify dregg's FRI-STARK *directly*? — the size question

*Research / circuit budget, 2026-07-27. `docs/MINA-DREGG-ZKAPP-BRIDGE.md` correctly ruled out
verifying dregg's **BN254 Groth16 wrap** on Mina: Kimchi has no pairing gate and the Fp12/Miller
stack does not exist. That verdict is about the **wrap**. This document asks the different question
its own §5 named as "Route A": dregg's **inner** proof is a BabyBear FRI-STARK hashed with
Poseidon2-w16 — 31-bit field arithmetic and a hash, **no pairing anywhere**. Every primitive is one
Kimchi already has. So: what does it **cost**, and does it **fit**?*

*This turns "feasible in principle" into a row budget. Both halves of the product are grounded:
the permutation count against an **in-tree empirical measurement**, the per-permutation row price
against the Kimchi/Pickles source.*

---

## 0. Verdict up front

**Feasible-but-huge. Not blocked; nowhere near a handful. ~2 × 10^7 Kimchi rows ⇒ several hundred
chained Pickles step circuits at deployed parameters, and the FRI knobs alone cannot get it under
~200.**

| | value | grounding |
|---|---|---|
| Poseidon2-w16-BabyBear permutations for **one** full root verify | **~11,000** (measured range 10,000–13,000) | **empirically measured in-tree** (`docs/deos/WRAP-NATIVE-HASH-DECISION.md:102-106`); independently re-derived here at ~10,250 (§2) |
| Kimchi rows per Poseidon2-w16-BabyBear permutation | **~2,000** (range 1,600–2,600) | derived from Kimchi gate/row source (§3); **pessimistic band ~8,400** — see §3.7 |
| **Total row budget** | **~2.2 × 10^7 rows** (band 1.8 × 10^7 – 9 × 10^7) | product |
| Usable rows per Pickles step | **~48,000–55,000** of 65,536 | §4.1, measured overheads |
| **Pickles step circuits** | **~500–800** deployed; ~1,900–2,800 in the pessimistic band | §4.2 |
| After the dregg-side FRI knobs (§5) | **~250–350** | |
| Floor without a column reduction or a Mina-targeted shrink | **~200** | §5.3 |
| Security the budget buys | **~50 bits** (`min{51, 73} − 1`) | machine-checked as an *arithmetic reading*, not an adversary bound (§6) |

**The single biggest cost driver is not the FRI logic, not the S-boxes, and not the AIR
evaluation. It is the `mod p` reduction.** "BabyBear is 31-bit so it fits natively in Pasta" is
true and load-bearing — it is exactly what makes this route *expressible* where the pairing route
is not. But a 31-bit prime inside a 255-bit field is still a **foreign modulus**: every
multiplication chain must be reduced with a witnessed quotient and **range checks**, and those
range checks are ~70% of the per-permutation rows. Kimchi's native Poseidon costs 11 rows per
permutation; this shape over a foreign 31-bit prime costs ~2,000. **The ~180× is the reduction,
not the hash.**

---

## 1. What exactly is being verified

The object a Mina circuit would check is `WholeChainProof.root` — the root batch-STARK, verified by
`verify_wide_turn_chain_recursive` under `ir2_leaf_wrap_config()`
(`circuit-prove/src/ivc_turn_chain.rs:3081`, config at `:1315`).

### 1.1 The one permutation

There is exactly **one** BabyBear permutation in the whole engine — MMCS leaf hash, Merkle node
compression, FRI transcript, and challenger all use it. ⚑ And the verifier **hashes only
width-16**: the width-24 table is constraint-checked, never hashed
(`WRAP-NATIVE-HASH-DECISION.md:107-110`, `all_perms == w16_perms`), so the entire hashing budget is
one permutation shape.

| | value | source |
|---|---|---|
| permutation | `Poseidon2BabyBear<16>` (`default_babybear_poseidon2_16`) | `circuit-prove/src/plonky3_recursion_impl.rs:36,126` |
| WIDTH / RATE / DIGEST_ELEMS | 16 / 8 / 8 | `plonky3_recursion_impl.rs:75-77` |
| leaf hash | `PaddingFreeSponge<Perm,16,8,8>` ⇒ `ceil(n/8)` permutations for `n` elements | `plonky3_recursion_impl.rs:127`; `p3-symmetric/src/sponge.rs` `hash_iter` |
| node compression | `TruncatedPermutation<Perm,2,8,16>` — arity 2, **exactly one permutation per node** | `plonky3_recursion_impl.rs:128`; `p3-symmetric/src/compression.rs:40-47`; Lean `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean:179-182` |
| challenger | `DuplexChallenger<F,Perm,16,8>` — one permutation per 8 absorbed elements | `plonky3_recursion_impl.rs:138`; `p3-challenger/src/duplex_challenger.rs:85-98,148-157` |
| rounds | 4 external-initial + 13 internal + 4 external-final, S-box `x^7` | `Poseidon2BabyBearW16.lean:26-27,172-177` (KAT-pinned bit-exact to the deployed Rust, `:190-205`) |
| external linear layer | `MDSMat4` circulant + block sum — **ADD-ONLY** | `Poseidon2BabyBearW16.lean:72-95` |
| internal linear layer | broadcast `fullSum` + per-lane **constant** scalar (`±2,3,4,½,¼,⅛,2⁻⁸,2⁻²⁷,…`) | `Poseidon2BabyBearW16.lean:104-124` |

The Lean module is the calibrated referent: byte-exact against
`default_babybear_poseidon2_16().permute(·)`, and a diverging limb fails the build.

### 1.2 The root's FRI knobs

`ir2_leaf_wrap_config()` = `create_recursion_config_for_inner_fri(6, 0, 0, 16)`
(`ivc_turn_chain.rs:1315-1329`, constants at `:1242-1245`), with `INNER_FRI_NUM_QUERIES = 19` and
`INNER_FRI_MAX_LOG_ARITY = 1` (`plonky3_recursion_impl.rs:118-121`).

| knob | value | source |
|---|---|---|
| `log_blowup` | **6** | `ivc_turn_chain.rs:1242` |
| `num_queries` | **19** | `plonky3_recursion_impl.rs:121` |
| `query_proof_of_work_bits` | **16** | `ivc_turn_chain.rs:1245` |
| `commit_proof_of_work_bits` | **0** — so the 16 per-layer `check_witness` calls are **free** | `ivc_turn_chain.rs:1244`; `p3-challenger/src/grinding_challenger.rs:41-43` |
| `max_log_arity` | **1 — the root folds by 2** | `plonky3_recursion_impl.rs:118` |
| `log_final_poly_len` | **0** | `ivc_turn_chain.rs:1243` |
| **`cap_height`** | **0 — full Merkle paths, never truncated** | `plonky3_recursion_impl.rs:346,442` (`MyMmcs::new(hash, compress, 0)`); semantics + the no-op truncate at `p3-merkle-tree/src/mmcs.rs:369-386` |

⚑ **Three documented traps, all re-checked here.**

- **`max_log_arity` is 1, not 3.** `ir2_leaf_wrap_config`'s own doc-comment (`ivc_turn_chain.rs:1310`)
  says "max_log_arity 3" — that describes the *inner* `ir2_config` batch the circuit verifies, not
  the config the fn builds. Documented at `plonky3_recursion_impl.rs:107-121` and independently
  confirmed empirically at `WRAP-NATIVE-HASH-DECISION.md:98-101`. **The arity that prices the
  root's own FRI is 2, and it is the single largest avoidable cost in this whole document.**
- **`|D⁰| = 2^22`, not 2^19.** `WRAP_LOG_CEIL = 16` (`circuit-prove/src/accumulator.rs:236`) ×
  `log_blowup = 6`. The constant `DEPLOYED_WORST_LOG_D0 = 19`
  (`circuit-prove/tests/fri_trace_height_measure.rs:133-144`) is annotated **MIS-DERIVED** in
  place — it sums `WRAP_LOG_CEIL` with the *wrong* blowup (3, from `create_recursion_config`,
  which is not on the wrap path at all). Do not quote it.
- ⚑ **`degree_bits = [9,9,15,14,15]` is NOT the root.** That measurement is of the **BN254 shrink**
  proof (`docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:11-14`,
  `circuit-prove/tests/apex_shrink_bn254_tooth.rs`), re-quoted at `accumulator.rs:227` and
  `fri_trace_height_measure.rs:55`. **No committed measurement of the root's own `degree_bits`
  exists.** §1.3 derives the root's table set structurally instead.

Commit-phase layers = `(log|D⁰| − log_final_height) / max_log_arity` with
`log_final_height = log_blowup + log_final_poly_len = 6` ⇒ **(22 − 6)/1 = 16 layers**.

⚑ **Two root shapes, and they differ.** `WholeChainProof` has two producers:
`Accumulator::finalize` returns the running proof as the root under `wrap_params()` with
`min_trace_height = 2^16` (`accumulator.rs:236,242-248,888-892`) ⇒ every table floored to 2^16,
`|D⁰| = 2^22`, 16 layers. `prove_chain_core_rotated` (what `prove_turn_chain_recursive` calls) uses
`ProveNextLayerParams::default()` (`ivc_turn_chain.rs:3400,3464`), whose `min_trace_height` is 1 ⇒
natural heights, max ≈ 2^15, `|D⁰| ≈ 2^21`, 15 layers. **The counts below differ by ~5%** between
the two; this document prices the accumulator shape (the larger, and the one the Lean ledger pins).

### 1.3 The tables — 7, at 940 columns

The root is verified by `verify_recursive_batch_proof_with_config` → `verify_all_tables` →
`p3_batch_stark::verify_batch` (`plonky3_recursion_impl.rs:797-817`). The AIR set is **3 primitives
always** (`Const`, `Public`, `Alu` — `plonky3-recursion@0a4a554
circuit-prover/src/batch_stark_prover.rs:1483`) **plus one per non-primitive op-type present**
(`:1489-1503`), from the four registered at `plonky3_recursion_impl.rs:804-813`. A `K ≥ 2` root
carries `expose_claim` (that is how `root_exposed_claims` reads the 25-lane segment,
`ivc_turn_chain.rs:582-596`) and W24 (`seg_poseidon_config()`, `:376-385`, sponge steps at `:475,497`),
so **7 tables**:

| table | main cols | prep cols | source |
|---|---:|---:|---|
| Const | 4 | 2 | `circuit-prover/src/air/const_air.rs:144-150` |
| Public | 4 | 2 | `air/public_air.rs:98-116` |
| Alu | 76 | 59 | `air/alu_air.rs:289-309`, `air/alu_columns.rs:9-23,74-77` |
| poseidon2-**W16** | 300 | 24 | `poseidon2-circuit-air/src/air.rs:538-542`, `columns.rs:87,210-214` |
| poseidon2-**W24** | **452** | 36 | same formula at `pr=21`, `plonky3-recursion/circuit/src/ops/poseidon2_perm/config.rs:78-86` (`BABY_BEAR_D4_W24`) |
| recompose | 4 | 2 | `air/recompose_air.rs:56-75` |
| expose_claim | 100 | 50 | `air/expose_claim_air.rs:125-135`; `SEG_WIDTH = NUM_CHAIN_CLAIMS = 25` at `ivc_turn_chain.rs:366,278` |
| **Σ** | **940** | **175** | |

The W24 width of **452** independently matches the figure recorded at
`docs/deos/WRAP-NATIVE-HASH-DECISION.md:109-110` and `APEX-VERIFIER-AIR-REDUCTION.md:145-147` —
a real cross-check on the width formula. The measured *apex* figure is **~752 opened columns**
(`APEX-VERIFIER-AIR-REDUCTION.md:34,42,45`), i.e. the same order; **752–940** is the honest band, and the
difference is whether a live W24 table is present.

Constraint degree is **3** (`n_chunks = 2` ⇒ `constraint_degree − 1 ∈ (1,2]`,
`p3-batch-stark/src/symbolic.rs:60-95`), so the quotient round carries 2 chunks × D=4 = 8 base
columns per instance.

---

## 2. COST — the permutation count for one full root verify

### 2.1 The measured number

⚑ **This has already been measured in-tree and I use that number, not an estimate:**

> *"**Real Poseidon2-w16 perm count ≈ 10,000–13,000** (central ~11,000), NOT the ~1,000–3,000 first
> estimated — driven by arity-1's ~18 rounds + a ~3,636 constant (leaf-hash/injection/challenger).
> Empirically measured via an instrumented `verify_all_tables` at the exact ir2 knobs; model
> `perms(m) = 19·[(m+5)(m+6)/2 + 5m + 9] + 3636`."*
> — `docs/deos/WRAP-NATIVE-HASH-DECISION.md:102-106`

Corroborated by the AIR-level view: the W16 table of the shrink circuit — one row per permutation —
is **2^15 rows** (`APEX-VERIFIER-AIR-REDUCTION.md:59-63`, *"one permutation ≈ one W16-AIR row"*).

### 2.2 The independent structural re-derivation

Rebuilt from the vendored verifier (`vendor/plonky3-fri-82cfad73/src/verifier.rs`, the exact
`82cfad73` source pinned at `Cargo.toml:220`) rather than assumed, so the measured number has a
structure attached:

**Commit phase.** `verify_query` runs one `mmcs.verify_batch` per fold round against a matrix of
`width = arity`, `height = 1 << log_folded_height` (`verifier.rs:436-455`); `log_current_height`
starts at 22 and drops by `log_arity = 1` per round ⇒ tree depths **21, 20, …, 6**.

- compressions/query = Σ_{d=6}^{21} d = **216**
- leaf hashes/query = 16 × 1 (each leaf is `arity = 2` extension elements = 8 base elements ⇒
  exactly 1 permutation; `p3-commit/src/adapters/extension_mmcs.rs:70-96`) = **16**

**Input openings.** `verifier.rs:555-597` calls `input_mmcs.verify_batch` once per element of
`commitments_with_opening_points`. The batch-STARK verifier pushes **4 rounds** — main trace,
quotient chunks, preprocessed, permutation/LogUp — with the ZK-random round absent
(`p3-batch-stark/src/verifier/mod.rs:317,356,406,471,498,502`; `SC::Pcs::ZK == false`, shape-checked
at `:74-82`). All four trees share the identical height profile `2^(degree_bits[i] + 6)`
(`verifier.rs:563-566`), so at the accumulator shape all four are **depth 22**.
`MerkleTreeMmcs::verify_batch` costs `d` compressions + `ceil(n/8)` leaf-hash permutations
(`p3-merkle-tree/src/mmcs.rs:1052-1180`).

| per query | perms |
|---|---:|
| main round: 22 + `ceil(940/8)` = 118 | 140 |
| quotient round: 22 + `ceil(56/8)` = 7 | 29 |
| preprocessed round: 22 + `ceil(175/8)` = 22 | 44 |
| permutation round: 22 + `ceil(28/8)` = 4 | 26 |
| **input subtotal** | **239** |
| commit phase (216 compressions + 16 leaf hashes) | **232** |
| **per query** | **471** |

`471 × 19 = 8,949`, plus the transcript (§2.3) ≈ 1,300 ⇒ **≈ 10,250**.

The published model at `m = 16` yields **9,716**. Structural derivation **10,250**. Measured central
**~11,000**. **Three independent routes agreeing within ~10%** — and the model's `(m+5)(m+6)/2` term
is recognisably the commit-phase depth sum, its `5m+9` the 4-round input-path sum. **Use ~11,000.**

### 2.3 The transcript is ~12%, and one term dominates it

`DuplexChallenger` permutes once per 8 absorbed elements. The observe sites are enumerable
(`p3-batch-stark/src/verifier/transcript.rs:27-119`, `p3-batch-stark/src/verifier/mod.rs:144,274-300`;
`vendor/plonky3-fri-82cfad73/src/verifier.rs:143,221-268`), and everything except one is small:
instance bindings 28, main digest + public values 33, preprocessed 15, permutation 36, quotient 8,
16 commit-phase commitments 128, final poly 4, arities 16.

The dominant term is `observe_algebra_slice` over **every opened value at ζ** before the PCS
challenges are drawn (`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:782-788`):
≈ `2·940 + 7·2·4 + 2·175 + 7·2·4` ≈ 2,342 extension values ≈ 9,368 base elements ⇒ **≈ 1,171
permutations**. Total transcript **≈ 1,250–1,400**.

### 2.4 The arithmetic residual — small, but *not* negligible

The verifier also does the reduced-opening arithmetic and the AIR constraint evaluation at ζ. This
costs extension multiplications, not permutations, and it too is measured:

> *"~752 columns × 19 queries ≈ 14,300 Horner ops, plus the fold arithmetic, the `inv(z−x)`
> divisions, the challenge-recompose math… This is the `~3.2M` residual term."*
> — `APEX-VERIFIER-AIR-REDUCTION.md:41-49`; the term also appears at
> `WRAP-NATIVE-HASH-DECISION.md:119` as ~96–221 R1CS/column

In Kimchi, a Horner step `acc ← acc·α + v` over the degree-4 extension is ~9–16 BabyBear
multiplications at 0.5 rows each. Crucially — unlike the S-box (§3.3) — this **is** a linear
accumulation, so lazy reduction genuinely amortises: `acc` grows only ~31 bits per step, so ~7
steps ride between reductions. That lands at ~7 rows per Horner op ⇒ **~200,000–400,000 rows**,
plus the AIR constraint fold (~1,000–1,200 degree-3 constraints, ~10^4 quartic mults ⇒ tens of
thousands of rows).

**≈ 1.5–2% of the total.** Real, worth budgeting, not the driver. **The size question is a hashing
question.**

---

## 3. Pricing ONE Poseidon2-w16-BabyBear permutation in Kimchi rows

### 3.1 The multiplication count is small

Per permutation, from `Poseidon2BabyBearW16.lean:60-63,127-128,172-177`:

- `sbox x = x^7` = `x2 = x·x; x4 = x2·x2; x7 = (x4·x2)·x` — **4 multiplications**.
- 8 external rounds × 16 lanes + 13 internal rounds × 1 lane = **141 S-boxes ⇒ 564 multiplications**.
- The external linear layer is **add-only** (`mdsLight`, `:86-95`) — 0 multiplications.
- The internal layer's per-lane factors are **compile-time constants** (`fmul 3`, `fhalve`,
  `fdiv2exp … 27`), i.e. linear-combination coefficients — 0 multiplications.

564 multiplications and a few hundred additions. In a *native* field this is a genuinely cheap
hash. It is not native here, and that is the entire story.

### 3.2 Kimchi's unit of account

Kimchi's `Generic` gate is a **double generic**: one row carries **two independent** constraints
`c₀·l + c₁·r + c₂·o + c₃·(l×r) + c₄ = 0`
(`proof-systems/kimchi/src/circuits/polynomials/generic.rs:1,4,15`), with `GENERIC_REGISTERS = 3`,
`GENERIC_COEFFS = 5`, `DOUBLE_GENERIC_REGISTERS = 6`, `DOUBLE_GENERIC_COEFFS = 10`,
`CONSTRAINTS = 2` (`generic.rs:56,59,64,67,70`). The OCaml side confirms this is what Pickles
emits — *"As there are two generic gates per row, we queue every other generic gate"*
(`mina/src/lib/crypto/kimchi_backend/common/plonk_constraint_system.ml:1135-1148`).

- **1 row = 2 constraints, each 3 wires and one multiplication.**
- A multiplication `o = l·r`, a scaled 2-input addition `o = a·l + b·r`, and the reduction identity
  `t − p·q − r = 0` are each **3 wires ⇒ 0.5 rows**.
- ⚑ **Multiply-accumulate is NOT free.** `o = l·r + w` is 4 variables, does not fit one gate ⇒
  2 gates = 1 row.
- A generic row uses **6 of 15 witness columns**; the other 9 are dead weight (`generic.rs:17-21`).
  Only the first 7 columns are copyable at all (`kimchi/src/circuits/wires.rs:7,10`).
- ⚑ **Each public-input field element costs one full row** (`plonk_constraint_system.ml:1013-1023`),
  plus 3 `zk_rows` per circuit (`mina/src/lib/pickles/fix_domains.ml:3`;
  `kimchi/src/circuits/constraints.rs:801`).
- An odd trailing generic gate is flushed as a **half-empty full row**
  (`plonk_constraint_system.ml:1000-1003`).

**Kimchi's `Poseidon` gate cannot be reused.** `POS_ROWS_PER_HASH = 11` (+1 trailing `Zero` ⇒ 12
rows/permutation in practice, `poseidon.rs:62,134`), but it is structurally Pasta-only on three
independent counts:

1. `ROUNDS_PER_ROW = COLUMNS / SPONGE_WIDTH = 15/3 = 5` with `STATE_ORDER: [usize; 5]`
   (`poseidon.rs:56,65-73`) — **a width-16 state does not fit a 15-column row at all**.
2. The MDS matrix is a Rust type-level constant, `pub mds: &'static [[F; 3]; 3]`
   (`kimchi/src/circuits/expr.rs:75-82`), emitted as `ConstantTerm::Mds{row,col}`
   (`kimchi/src/circuits/argument.rs:139-145`). Not a coefficient, not a witness.
3. The S-box exponent is folded into the constraint polynomial at build time
   (`poseidon.rs:373-375`), and the gate models 5 *identical full rounds* (`ROUND_EQUATIONS`,
   `:289-310`) — Poseidon2's split external/internal structure has no representation in it.

Only the **round constants** are soft; they live in the `coefficients` columns
(`poseidon.rs:214-220,378-385`). That is nowhere near enough. **Generic gates it is.**

### 3.3 The reduction, which is the whole cost

BabyBear `p = 2^31 − 2^27 + 1` is 31 bits; Pasta Fp is ~254 bits. **No `ForeignField` gadget is
needed** — a BabyBear product fits in a native element with 190 bits to spare, and that is exactly
why this route exists where the pairing route does not. But "fits" is not "free": the circuit must
still enforce `a·b ≡ c (mod p)`, which means witnessing `q, r` with `a·b = q·p + r` and
**range-checking them**, or the witness is unconstrained.

Two facts set the floor, and both are real savings worth naming:

1. **`p` is a compile-time constant**, so `q·p` is a *coefficient*, not a multiplication. The
   reduction identity is 3 wires ⇒ **one generic gate ⇒ 0.5 rows**. (A generic foreign-field
   multiply, where the modulus is a witness, has no such shortcut.)
2. **Intermediate values need not be canonical.** Both Poseidon2 linear layers and `x ↦ x^7` are
   functions of the *residue class*, so any representative is sound; only the digest needs
   canonicalising. This removes the `x < p` comparison (2 range checks + a gate) from every
   intermediate step — **8 lanes per permutation need it, not 564 values**.

⚑ **But the S-box defeats the standard lazy-reduction advice.** The usual counsel for a small prime
inside a big field — *"you can accumulate ~2^190 of products before reducing, so amortise the
reduction to near zero"* — holds for **dot products**, where accumulation is *linear*. That is why
§2.4's Horner chains really are cheap. `x^7` is a **multiplication chain**: each step *squares* the
bit-width, so at most four multiplications ride before the native modulus is hit, and there is **no
amortisation across S-boxes**. This is the crux of the entire cost, and it is why the naive
"BabyBear is cheap in Pasta" intuition is wrong for the hash specifically.

With a 31-bit input: `x² < 2^62`, `x⁴ < 2^124`, `x⁶ < 2^186`, `x⁷ < 2^217` — all four
multiplications run unreduced, then **exactly one reduction per S-box**. Soundness of that
reduction needs `q·p + r < N` (the Pasta modulus), i.e. `q < 2^223`; honest `q < 2^186`, so
`rangeCheck(q, 192)` is both sufficient and satisfiable.

**Per S-box, with the lookup-backed range-check gates:**

| item | rows | basis |
|---|---:|---|
| 4 multiplication gates (`x², x⁴, x⁶, x⁷`) | 2.0 | 0.5 rows each, §3.2 |
| 1 reduction gate `x⁷ − p·q − r = 0` | 0.5 | 3 wires |
| `rangeCheck(q, 192)` | ~5 | 3 limbs; `kimchi/src/circuits/polynomials/range_check/gadget.rs:84-116` = 4 rows for three 88-bit values, + recomposition |
| `rangeCheck(r, 32)` | ~1 | `range_check/gadget.rs:63-70`, `circuitgates.rs:136-137` — a 64-bit check is 1 row |
| **total** | **~8.5** | |

### 3.4 Per-permutation total

**141 S-boxes ⇒ ~1,200 rows.** Linear layers: the external layer is ~72 two-input operations ⇒
36 rows, × 8 = **288**; each internal round is ~31 scaled additions ⇒ 16 rows, × 13 = **~200**.

**Plus the internal layer's re-bounding.** Its `2⁻⁸` / `2⁻²⁷` / `¼` / `⅛` coefficients are
*full-width* field constants (they are inverses mod `p` — `Poseidon2BabyBearW16.lean:117-123`), so
those lanes leave a round at ~2^62 and the `fullSum` broadcast propagates the growth to all 16
lanes. The state must be re-bounded about once per internal round: ~10 lanes × ~2.8 rows × 13
rounds ⇒ **~370 rows**.

| per permutation | rows |
|---|---:|
| S-boxes (mults + reductions + range checks) | ~1,200 |
| external linear layers (8×) | ~288 |
| internal linear layers (13×) | ~200 |
| internal-layer re-bounding | ~370 |
| **TOTAL** | **~2,050 — call it ~2,000** (range 1,600–2,600) |

### 3.5 ⚑ Lookups are mandatory, and not free either

Every number above assumes `RangeCheck0`/`RangeCheck1`, which are lookup gates against the 12-bit
table (`kimchi/src/circuits/lookup/tables/range_check.rs:4-11`; ≤4 lookups/row,
`range_check/circuitgates.rs:57,99`).

**Without lookups, a 31-bit range check is 31 booleanity + 30 recombination constraints ≈ 31 rows**
instead of ~1.33 — a 10–20× penalty that would put one permutation near 20,000 rows and this route
out of reach entirely. **Lookups are a precondition, not an optimisation.**

Their cost: enabling them flips Pickles feature flags
(`mina/src/lib/pickles_types/plonk_types.ml:190-232` — `range_check0`, `range_check1`, `lookup`,
…), and o1js states plainly that *"`Maybe` feature flags incur a proving overhead"*
(`o1js/src/lib/proof-system/feature-flags.ts:32`). Budget it; it does not change the verdict.

Also note o1js only exposes range checks at **multiples of 16 bits**
(`o1js/src/lib/provable/gadgets/range-check.ts:283-296`, `assert(n % 16 === 0)`), so `rangeCheck32`
is the closest primitive to a 31-bit bound — hence the `r < 2^32` (non-canonical) intermediate,
which §3.3 shows is sound.

### 3.6 The honest sanity check

Kimchi's *native* Pasta-Poseidon costs **11 rows** per permutation with its custom gate
(`poseidon.rs:62`; o1js corroborates — *"2^12 × 11 rows < 2^16 rows, should just fit"*,
`o1js/src/examples/benchmarks/hash-witness.ts:8`). Without the gate it would be ~400 rows of
generic gates (55 rounds × 3 lanes × 4 mults at 0.5 rows, plus a width-3 MDS). Our figure is ~2,000
for a permutation with **fewer S-boxes** (141 vs 165).

**11 → 2,000 is ~180×. About 5× of that is "no custom gate"; about 35× is "foreign modulus".**
Naming which is which matters, because only the smaller one is fixable — and only by a hard fork.

### 3.7 ⚑ The pessimistic band, from a measured comparable

There is a **measured** datapoint in-tree for exactly this problem — the same Poseidon2-w16-BabyBear
permutation emulated inside a *different* foreign field:

> *"only the w16 187/**16,837** [enters]"* … *"Swing on the hashing term ≈ 16,837/243 ≈ 69×."*
> — `docs/deos/WRAP-NATIVE-HASH-DECISION.md:104-113`: **16,837 R1CS constraints per emulated
> BabyBear-Poseidon2-w16 permutation** in gnark over BN254, versus 243 R1CS for a *native* BN254
> Poseidon2.

One R1CS constraint and one Kimchi generic gate are comparable units (one multiplication each), so
16,837 R1CS ≈ **~8,400 Kimchi rows** — **4× my §3.4 figure**. The gap is real and explicable:
gnark's `emulated` package uses a generic **multi-limb** representation and does *not* exploit that
BabyBear is 200+ bits smaller than BN254. §3.3's whole method — one native element per BabyBear
value, `p` as a coefficient, non-canonical intermediates, one reduction per S-box — is precisely
that unexploited headroom.

**So the honest band is:**

| assumption | rows/perm | total (× 11,000) |
|---|---:|---:|
| §3.3 single-native-element method delivers | ~2,000 | **~2.2 × 10^7** |
| generic-emulation parity with the measured gnark figure | ~8,400 | **~9 × 10^7** |

The ~2,000 is a design claim, not a measurement. **The first thing to build is a single o1js
`P2.perm` gadget and read `getRows()` off it** — that one number collapses this 4× band and costs
an afternoon, versus a 500-step build sitting on an unmeasured assumption.

### 3.8 What a custom gate would buy — and why it is not on the table

A `Poseidon2BabyBear` gate could plausibly do one round per 2 rows (a width-16 state does not fit
15 columns, so it spans `Curr`/`Next`) ⇒ ~42 rows for 21 rounds. **But the mod-`p` range checks do
not go away** — they are lookups, not gate constraints — so ~141 reductions still cost ~800–1,000
rows. Realistic custom-gate figure: **~900–1,100 rows/permutation, a ~2× win**, nothing like the
~40× Kimchi's Pasta Poseidon gate buys over generic gates.

And it is a **Mina hard fork, not an app-level change.** `GateType` is a closed 16-variant enum
(`kimchi/src/circuits/gate.rs:71-97`, mirrored at `kimchi_types.ml:136`); the in-circuit
verification key is a **versioned** record with exactly 6 gate selectors
(`mina/src/lib/pickles_types/plonk_verification_key_evals.ml:5-15`, `Stable.V2`); the optional
selectors are a closed versioned menu (`plonk_types.ml:365-389`, `Evals.Stable.V2`). Adding one
means a new Kimchi gate + constraint polynomial, a new selector in two versioned wire types, a new
`Features` flag, changes to `step_verifier.ml` **and** `wrap_verifier.ml` — which are themselves
circuits, so the hardcoded `Common.wrap_domains` constants (`mina/src/lib/pickles/common.ml:25-29`),
*exactly asserted* at `compile.ml:722-731`, move — then new serialisation versions network-wide and
a new o1js release. Every added gate type also permanently inflates the recursive verifier: one
more commitment in the in-circuit MSM, currently `Nat.N45.n = 45` (`step_verifier.ml:604`) at ~34
rows each. That is exactly why the set is closed and why the 8-flag Feature-Flags menu exists
*instead of* extensibility.

**Assume generic gates.**

---

## 4. DOES IT FIT

### 4.1 The real per-step budget

One o1js `@method` compiles to one Pickles **step** circuit with a hard ceiling of
**2^16 = 65,536 rows** (`mina/src/lib/crypto/kimchi_backend/pasta/basic/kimchi_pasta_basic.ml:16-17`
`Step = Nat.N16`; `mina/src/lib/pickles/common.ml:4-13`).

- **Pickles hard-rejects chunking.** `mina/src/lib/pickles/verify.ml:61-76` raises `Is_chunked` if
  any evaluation array has length > 1, then asserts `"only uses single chunks"`. Upstream Kimchi
  supports chunking; **Mina does not accept it.** The ceiling is enforced at `verify.ml:86-88`.
- **Pickles' own recursive verifier eats the front of every step.** Component costs are citable:
  `Scalar_challenge.endo` = 33 rows (`endosclmul.rs:112-113`), a 255-bit `scale_fast2` = 102 rows
  (`plonk_curve_ops.ml:66,251-256`; `varbasemul.rs:59,67`), a Poseidon permutation = 12 rows. The
  step verifier combines 47 commitments (`step_verifier.ml:604`, `Nat.N45.n` + `Wrap_hack`
  padding) at ~34 rows each ≈ 1,564 rows, plus a 15-round `bullet_reduce` ≈ 1,560, plus `ft_comm`
  ≈ 700, plus sponge absorbs ≈ 300. **⇒ ~6,000–8,000 rows per previous proof verified.**
  Hard anchor: the *wrap* circuit does the mirror-image job in a domain of exactly **2^13 = 8,192
  rows** for `proofs_verified = 0` (`common.ml:25-29`, exactly asserted at
  `wrap_domains.ml:52-60` + `compile.ml:722-731`).
- Subtract 3 `zk_rows` and **1 full row per public-input element**.
- ⚑ **The domain is a power of two**: crossing 32,768 rows doubles proving cost even at 32,769.

| `max_proofs_verified` | Pickles overhead | usable of 65,536 |
|---|---:|---:|
| 0 | bounded < 16,384 | ~50,000–60,000 |
| 1 | ~6,000–8,000 | ~55,000 |
| **2** (needed for an aggregation tree) | ~12,000–16,000 | **~48,000–52,000** |

### 4.2 The arithmetic

```
~11,000 permutations  ×  ~2,000 rows  =  ~2.2 × 10^7 rows
2.2 × 10^7 / 48,000 usable            =  ~460 work-carrying step circuits
+ a binary aggregation tree over them =  ~500–800 Pickles steps total
```

In the §3.7 pessimistic band: **~1,900–2,800 steps.**

### 4.3 It does split cleanly, which is what keeps this "huge" and not "blocked"

1. **One transcript step** replays the Fiat–Shamir challenger and emits the 19 query indices, the
   16 fold challenges `β_i`, `ζ`, and `α` as a Poseidon-committed public output (~1,300
   permutations ⇒ ~2.6 × 10^6 rows ⇒ **~55 steps**).
2. **19 independent per-query chains** (one query ≈ 471 permutations ≈ 9.4 × 10^5 rows ⇒ **~20
   steps each**, ~380 steps total), each consuming the committed challenge digest.
3. **A binary aggregation tree** (Pickles steps take up to 2 previous proofs), ~another 400 steps
   whose *only* content is the recursive verification.
4. **One final chain** for the reduced-opening arithmetic and AIR constraint evaluation at ζ —
   ~1.5–2% of the work (§2.4) ⇒ ~10 steps.

Each step is a real Pickles proof at 10–30 s, so **~500–800 steps ≈ 2–7 hours of Mina-side proving
per dregg root verified**, parallel across the 19 query chains, sequential up the tree.

### 4.4 So: a handful, or hundreds?

**Hundreds.** Nowhere near a handful. "BabyBear is 31-bit so it fits natively in Pasta" is *true
and load-bearing* — it is what makes the circuit expressible at all — but it buys **expressibility,
not cheapness**.

---

## 5. The knobs that move it, and the floor underneath them

All dregg-side. All ordinary greenfield re-emits (rotate the epoch, re-emit descriptors, re-genesis
— nothing holds the old shape).

### 5.1 The FRI knobs

| knob | now | change | effect | cost |
|---|---|---|---|---|
| **`max_log_arity`** | **1** (fold by 2) | 3 (fold by 8) | 16 layers → 6; commit-phase 232 perms/query → **~95** | machine-checked: moves `perFoldBits` 112 → 109 and `commitBits` **by 0** (`FriDeployedHeightPairing.the_flip_moves_perFold_only`) |
| **`cap_height`** | **0** (`plonky3_recursion_impl.rs:346,442`) | 8 | truncates 8 levels off every path; ~80 perms/query | commitment becomes 2^8 digests absorbed once; **no soundness change** |
| **`WRAP_LOG_CEIL`** | **16** (`accumulator.rs:236`) | 15 (the natural max) | `\|D⁰\|` 2^22 → 2^21; ~5% | ~2 bits on the commit column (`ε_C ∝ \|D⁰\|²`) |
| **`num_queries`** | **19** | fewer | linear in everything | **directly weakens the query leg**, and §6 shows it cannot buy back the binding column. Not recommended. |

Turning the first three lands around **~5,500–6,500 permutations ⇒ ~1.2 × 10^7 rows ⇒ ~250–350
steps.**

### 5.2 ⚑ The knob the FRI parameters cannot touch

Look at where the remaining cost sits after §5.1. The **input-round leaf hashes** —
`ceil(940/8) = 118` permutations per query for the main round alone, ~151 across all four rounds,
**2,869 permutations over 19 queries** — are a function of the root's **column count**, and *no FRI
parameter moves them.* Neither does the ~1,171-permutation opened-value absorb in the transcript
(§2.3), which is the same 940 columns.

**~48% of those 940 columns are the W24 poseidon table** (§1.3). `APEX-VERIFIER-AIR-REDUCTION.md`
is already the campaign for exactly this reduction. So the lever with the most headroom left is
**narrow the root's trace**, not tune FRI.

*(Note the open contradiction §1.3 inherits: `APEX-VERIFIER-AIR-REDUCTION.md:59-63` states the apex
carries no live W24 rows, while `ivc_turn_chain.rs:475,497` emits W24 sponge steps on every
`merge_two_segment_proofs`. If W24 is genuinely absent the root is 6 tables at Σ 488 columns and
the whole count drops ~1,200 permutations. **Worth measuring — it is a real ~10% on this budget,
and nobody has read a root proof's `degree_bits`.**)*

### 5.3 The floor

Even with arity 8, `cap_height = 8`, and `WRAP_LOG_CEIL = 15`, the irreducible work is the
column-driven leaf hashing (~2,900), the transcript (~1,300), the capped input paths (~1,100), and
the folded commit phase (~600) ⇒ **~5,900 permutations ⇒ ~1.2 × 10^7 rows ⇒ ~200 steps.**

Below that needs one of two real design moves, and **the second is the one worth arguing**:

- **narrow the root's trace** (§5.2), or
- **a Mina-targeted shrink layer** — re-prove the root at a small domain with few queries and
  arity 8, exactly analogous to the BN254 shrink `dregg_outer_config.rs` that already exists for the
  Groth16 path (`docs/MINA-DREGG-ZKAPP-BRIDGE.md:79-83`). That is what turns a 500-step monster into
  something a zkApp could plausibly carry, and it is **dregg's decision alone** — no Mina-side work
  at all.

---

## 6. What the row budget actually buys — the ε_C ceiling

⚑ **Spending 2 × 10^7 rows on Mina does not buy 128 bits.** At the deployed pairing the ledger
reads:

- `commitBits = 51` at `|D⁰| = 2^22`
  (`metatheory/Dregg2/Circuit/FriDeployedHeightPairing.lean:142-144`, `deployed_wrap_commitBits`,
  `#assert_axioms`-clean).
- `johnsonBits = 73`; the ethSTARK eq.-(20) composite `min{51, 73} − 1 = **50**`
  (`FriDeployedHeightPairing.lean:252-256`, `the_commit_column_binds_at_the_deployed_pairing`).

And for anyone hoping to tune their way out:

> *"Buying queries cannot help: `ε_C` contains no `numQueries` and no `powBits`
> (`FriLedgerSound.query_and_pow_cannot_pass_epsC`). Only `extDeg` moves it."*
> — `FriDeployedHeightPairing.lean:247-249`

So the **commit column binds**, the Johnson column's 73 bits are 22 bits of slack nobody can spend,
and the only lever is the extension degree. Raising `extDeg` 4 → 8 would move it — and would
**roughly double this entire circuit**: every FRI commit-layer leaf goes from 8 to 16 base elements
(2 permutations instead of 1), the opened-value absorb doubles, and every extension multiplication
in §2.4 goes from ~9 to ~30 BabyBear mults.

**At current resolution:** a Mina-side direct FRI verify at deployed parameters is ~2 × 10^7 rows
for a **~50-bit dial reading**, and that reading is an arithmetic statement about a transcribed
formula — *not* an adversary-quantified security bound. Per `docs/OPENING-SOUNDNESS-DECONFLATED.md`
this is a **tag-(a)** number: a knob position, not a wall. The **tag-(b)** residual (wiring the
proven proximity theorem to the deployed verifier) and the **tag-(c)** carriers (Poseidon2
collision-resistance, Fiat–Shamir RO) are **completely unchanged** by moving the verifier into
Kimchi. A Mina-side recompute inherits exactly dregg's floor — and adds **Mina's own IPA
discrete-log assumption** on top of it, which dregg's PQ-safe hash-based stack does not otherwise
carry.

---

## 7. THE APPROACH — the concrete gadget shape

If this is built, this is what it is made of. All of it is o1js-expressible today; none of it needs
`ForeignField`.

### 7.1 The BabyBear layer (`BB` — the base gadget)

```
BB.mulUnreduced(a, b)  →  Field    // a native Field multiply; nothing else
BB.reduce(t, bitsIn)   →  Field    // witness q, r; assert t = q·p + r  (ONE generic gate, p is a coeff)
                                   //   Gadgets.rangeCheck(q, ceil16(bitsIn − 31))
                                   //   Gadgets.rangeCheck32(r)
BB.canonical(x)        →  Field    // reduce + the two-check `x < p` trick — DIGEST LANES ONLY
BB.sbox(x)             →  Field    // x², x⁴, x⁶, x⁷ unreduced, then ONE BB.reduce(·, 217)
```

There is no limb decomposition, no CRT, no `ForeignFieldMul`. `p` is a constant, so `q·p` is a
coefficient — the reduction is 3 wires.

⚑ **The soundness note that licenses non-canonical `r`:** both Poseidon2 layers and `x ↦ x^7` are
functions of the residue class, so a non-unique representative is sound at every intermediate
point. **`canonical` is needed exactly once per permutation output, on the 8 digest lanes.**
Canonicalising everywhere roughly doubles the row count for nothing; forgetting it on the digest
breaks binding. Both mistakes are easy and neither is loud.

### 7.2 The permutation

```
P2.mdsLight(state16)     // add-only; mirror Poseidon2BabyBearW16.lean:72-95 op-for-op
P2.externalRound(rc, s)  // 16 × BB.sbox, then mdsLight
P2.internalRound(rc, s)  // 1 × BB.sbox on lane 0; partSum; per-lane constant scale;
                         //   then BB.reduce on the wide lanes (the 2⁻ᵏ ones)
P2.perm(state16)         // mdsLight ∘ 4 ext ∘ 13 int ∘ 4 ext
P2.compress(a8, b8)      // perm(a ++ b).take 8       — TruncatedPermutation<·,2,8,16>
P2.hashIter(xs)          // ceil(n/8) perms, rate 8   — PaddingFreeSponge<·,16,8,8>
```

**The round constants are Lean-sourced, not retyped.** `Poseidon2BabyBearW16.lean:133-165` holds the
real `RC_16_EXTERNAL_INITIAL / _FINAL / _INTERNAL` and is KAT-pinned to the deployed Rust
(`:190-205`). The o1js table must be **emitted from that file**, with the same three KATs replayed
as an o1js assertion — the live-handshake pattern the existing PoC already uses
(`docs/MINA-DREGG-ZKAPP-BRIDGE.md:207-218`), where the Rust value is the input and the circuit
asserts equality. Anything less and the two hashes drift silently, which is the one failure here
that produces a green build and a broken bridge.

### 7.3 The verifier

```
FRI.verifyQuery(idx, β[], openings)   // 16 folds; per fold: reconstruct the arity-2 row,
                                      //   P2.hashIter(8 base) → 1 perm, walk d compressions,
                                      //   then foldRow over EF4
FRI.foldRow(...)                      // BinomialExtensionField<BabyBear,4>; ~9 BB mults per EF mult
MMCS.verifyBatch(commit, dims, i, op) // mirror p3-merkle-tree/src/mmcs.rs:1052-1180 exactly,
                                      //   INCLUDING the shorter-matrix injection (:1145-1170) —
                                      //   omitting it silently accepts a different tree
Challenger.observe/sample             // one perm per 8 absorbed elements; the opened-value
                                      //   absorb is ~1,171 perms on its own (§2.3)
Horner.reducedOpening(...)            // the ~14,300 HornerAcc chain — lazy reduction DOES
                                      //   amortise here (§2.4); ~7 rows/op
AIR.evalAtZeta(...)                   // 7 AIRs, degree 3, ~1,000–1,200 constraints over EF4
```

### 7.4 The Pickles wiring

- Public input per work step: `Poseidon.hash([rootCommitDigest, challengeDigest, chunkIndex])` — a
  single Field, because **each public-input element costs a full row** (§3.2).
- Public output: an accumulator digest folded up the tree.
- Aggregation: a binary tree of `SelfProof` steps at `max_proofs_verified = 2` (~48,000 usable rows
  each).
- ⚑ **The challenge derivation must be its own step, not replicated per query.** Replaying the
  ~1,300-permutation transcript inside all 19 query chains multiplies it by 19 — ~24,000 wasted
  permutations, ~5 × 10^7 rows, more than doubling the whole build.
- ⚑ `.verify()` still consumes **only Pickles proofs**. This route does not change that; the dregg
  proof enters as **witness data**, and the Mina-side proof asserts *"I recomputed dregg's FRI
  verifier over this witness and it accepted."* That is the correct and only available shape.

---

## 8. VERDICT

**Feasible-but-huge.** Route A is real: every primitive dregg's root proof needs is one Kimchi
already has, there is no missing gadget stack, and no pairing wall. That is categorically different
from the Groth16 wrap, which is *blocked* on a missing primitive.

- **Blocked?** **No.** Nothing here is unbuildable.
- **A handful of step circuits?** **No.** **~500–800** at deployed parameters (~1,900–2,800 if
  §3.7's optimisation underdelivers); **~250–350** after the dregg-side FRI knobs; **~200** is the
  floor short of narrowing the root's trace or adding a Mina-targeted shrink layer.
- **Honest row budget:** **~2.2 × 10^7 Kimchi rows**, ~98% of it Poseidon2-w16-BabyBear.
- **Single biggest cost driver:** the **mod-`p` reduction and its range checks** — ~70% of the
  per-permutation rows, because the S-box is a *multiplication chain* and lazy reduction cannot
  amortise across it. *Not* the S-boxes (564 multiplications is nothing), *not* the FRI logic,
  *not* the AIR evaluation (~1.5–2%).
- **Second driver:** `max_log_arity = 1` and `cap_height = 0`. Together ~2.5×, against a
  configuration available today that costs **3 bits on a column that is not the binding one**.
- **What the budget buys:** ~50 bits of ledger reading, commit-column-bound, with **queries
  provably unable to move it**.

**The two things worth doing before building any of this, in order — and neither is Mina-side:**

1. **Measure the gadget.** Write one o1js `P2.perm` and read `getRows()`. That collapses §3.7's 4×
   band (~2.2 × 10^7 vs ~9 × 10^7 rows — the difference between "ambitious" and "no"), and it
   costs an afternoon rather than a 500-step build resting on an unmeasured design claim.
2. **Turn the dregg-side knobs and measure a real root.** Flip `max_log_arity` to 3, set
   `cap_height`, and — the actual open question — **read a root proof's `degree_bits`**, which
   §1.3 shows nobody ever has. Then decide whether a **Mina-targeted shrink layer** is the right
   final stage, exactly as `dregg_outer_config.rs` is for BN254.

---

## 9. Scorecard

| Claim | Resolution |
|---|---|
| Kimchi can verify dregg's FRI-STARK **directly**, no Groth16 wrap | **Yes in principle** — field + hash only, every primitive exists. Unlike the pairing route, nothing is missing. |
| BabyBear fits natively in Pasta ⇒ cheap | **Half true.** It fits (no `ForeignField`), which is why the route exists. It is **not** cheap: reduction + range checks are ~70% of the rows. |
| Kimchi's Poseidon gate can be reused | **No.** Structurally width-3 Pasta (`&'static [[F;3];3]` MDS, `COLUMNS/SPONGE_WIDTH` layout). A new gate is a **Mina hard fork**, not an app change. |
| Permutation count | **~11,000 — measured in-tree**, independently re-derived here at ~10,250. |
| Rows per permutation | **~2,000** by §3.3's method; **~8,400** at parity with the one measured foreign-field comparable. **Band unresolved — measure it first.** |
| Total | **~2.2 × 10^7 rows** (band 1.8 × 10^7 – 9 × 10^7). |
| Fits in one circuit | **No** — ~340× the 2^16 ceiling, and **Pickles hard-rejects chunking** (`verify.ml:61-76`). |
| N step circuits | **~500–800** deployed; **~250–350** knobbed; **~200** floor. |
| It buys 128 bits | **No — ~50**, commit-column-bound, and `numQueries` provably cannot move it. |
| The AIR evaluation is the expensive part | **No — ~1.5–2%.** It is entirely a hashing problem. |
| `degree_bits = [9,9,15,14,15]` describes the root | **No** — that is the BN254 **shrink** proof. The root's own heights are **unmeasured**. |

**Sources of record.** dregg: `circuit-prove/src/plonky3_recursion_impl.rs` (config, hash types,
`cap_height = 0`), `circuit-prove/src/ivc_turn_chain.rs` (root verify, `ir2_leaf_wrap_config`, the
7-table set), `circuit-prove/src/accumulator.rs:236,242-248,888-892` (`WRAP_LOG_CEIL`, the two root
shapes), `circuit-prove/tests/fri_trace_height_measure.rs:120-144` (the mis-derived constant),
`docs/deos/WRAP-NATIVE-HASH-DECISION.md:98-119,204` (**the measured permutation count, the 16,837
R1CS/perm comparable, the arithmetic residual, the real 12.2M-R1CS wrap**),
`docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:11-63` (trace anatomy, the 752-column Horner term).
plonky3: `vendor/plonky3-fri-82cfad73/src/verifier.rs:363-501,555-597`,
`two_adic_pcs.rs:771-806`, `p3-merkle-tree/src/mmcs.rs:369-386,1052-1180`,
`p3-symmetric/src/{sponge,compression}.rs`, `p3-batch-stark/src/verifier/mod.rs:74-82,317-502`.
Lean: `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean` (the KAT-pinned permutation),
`metatheory/Dregg2/Circuit/FriDeployedHeightPairing.lean:142-256` (the 51/50-bit readings),
`docs/OPENING-SOUNDNESS-DECONFLATED.md` (what those numbers are and are not).
Mina/Kimchi (`~/dev/proof-systems` @ `f6d958d`, `~/dev/mina`): `kimchi/src/circuits/`
`polynomials/{generic,poseidon,range_check}.rs`, `gate.rs`, `wires.rs`, `expr.rs`;
`mina/src/lib/pickles/{common,verify,fix_domains,wrap_domains,compile,step_verifier}.ml`,
`pickles_types/{plonk_types,plonk_verification_key_evals}.ml`,
`kimchi_backend/common/plonk_constraint_system.ml`, o1js 1.9.1 gadgets.

**Companion:** `docs/MINA-DREGG-ZKAPP-BRIDGE.md` — this document answers its §5 "Route A" with a
budget, and does not disturb its Groth16 verdict.
