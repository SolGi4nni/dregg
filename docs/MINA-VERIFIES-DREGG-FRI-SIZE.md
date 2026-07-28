# Can a Kimchi circuit verify dregg's FRI-STARK *directly*? — the size question

*Research / circuit budget, 2026-07-27. `docs/MINA-DREGG-ZKAPP-BRIDGE.md` correctly ruled out
verifying dregg's **BN254 Groth16 wrap** on Mina: Kimchi has no pairing gate and the Fp12/Miller
stack does not exist. That verdict is about the **wrap**. This document asks the different question
its own §5 named as "Route A": dregg's **inner** proof is a BabyBear FRI-STARK hashed with
Poseidon2-w16 — 31-bit field arithmetic and a hash, **no pairing anywhere**. Every primitive is one
Kimchi already has. So: what does it **cost**, and does it **fit**?*

*This turns "feasible in principle" into a row budget. Both halves of the product are grounded:
the permutation count against an **in-tree empirical measurement**, the per-permutation row price
**now against a measured o1js circuit** (§3.8, 2026-07-28) rather than the Kimchi/Pickles source
reading it was first derived from.*

---

## 0. Verdict up front

**Feasible-but-huge. Not blocked; nowhere near a handful. ~2.9 × 10^7 Kimchi rows ⇒ several
hundred chained Pickles step circuits at deployed parameters, and the FRI knobs alone cannot get it
under ~260.**

| | value | grounding |
|---|---|---|
| Poseidon2-w16-BabyBear permutations for **one** full root verify | **~11,000** (measured range 10,000–13,000) | **empirically measured in-tree** (`docs/deos/WRAP-NATIVE-HASH-DECISION.md:102-106`); independently re-derived here at ~10,250 (§2) |
| Kimchi rows per Poseidon2-w16-BabyBear permutation | **2,600.5 — MEASURED** | **§3.8** — an o1js circuit that compiles, proves, and reproduces the deployed permutation's KAT. Supersedes the ~2,000 design claim (§3.3–3.4) and closes §3.7's 4× band at the optimistic end |
| **Total row budget** | **~2.9 × 10^7 rows** (2.7–3.4 × 10^7, all remaining spread from the permutation count) | product; **the independent per-object sum in §3.14 now reads ~3.0 × 10⁷** |
| Kimchi rows per **Merkle LEVEL** (the object FRI buys) | **2,677 — MEASURED** | **§3.9** — +76.5 over the bare permutation: 8 witnessed-lane range checks + 8 lane reductions + the cond-swap, none of which a single permutation pays |
| Kimchi rows for the deployed **depth-22 opening** | **58,971 — MEASURED** | §3.9 — **more than one Pickles step's usable rows** |
| Kimchi rows for **ONE FRI QUERY** at deployed knobs | **684,726 — MEASURED** | **§3.10** — 238 Merkle levels + 16 sponges + 16 arity-2 folds; 13–15 Pickles steps. FRI walk only, no DEEP/AIR/challenger |
| Kimchi rows for the whole **Fiat–Shamir TRANSCRIPT** | **62,637 — MEASURED** | **§3.12** — 23 permutations. **0.48% of the walk it authorises**, and without it a prover picks its own queries. The single most important rung, and the cheapest |
| Kimchi rows for one query's whole **16-layer commit phase** | **623,310 — MEASURED** | **§3.13** — and building it against p3's own 16-round chain found the coset descent taking the wrong index bit |
| Kimchi rows for **transcript + one commit phase, JOINTLY** | **686,005 — MEASURED** | **§3.13b** — the join costs 58 rows. This is the statement that says *the prover's* FRI proof rather than *a* FRI proof |
| Kimchi rows for one extension **Horner step** | **49 — MEASURED** | §3.14 — ⚑ **§2.4 priced it at ~7** |
| Kimchi rows for the whole **DEEP QUOTIENT**, one query | **154,523 — MEASURED** | **§3.15** — at the root's real 940+175-column table set, 2,286 terms. **2.94 × 10⁶ across 19 queries**, and §3.14 had priced DEEP *and* AIR together at 1.0 × 10⁶. ⚑ This is the rung that stops the fold chain starting from a number the prover chose |
| Kimchi rows to **observe the opened values** into the challenger | **2.97 × 10⁶ — MEASURED unit × exact count** | **§3.16** — 2,286 values × 4 lanes = 1,143 permutations. §3.12 stood the whole batch-STARK preamble in with 13 lanes |
| Kimchi rows for the **AIR evaluation at ζ** | **`A + N·h`, `A` = 14,175 and `h` = 48 MEASURED; `N` UNCOUNTED** | **§3.16** — selectors, α-fold, chunk recomposition and closing equality, KAT'd against p3's own domain algebra. `C_i` itself is not built |
| Usable rows per Pickles step | **~48,000–55,000** of 65,536 | §4.1, measured overheads |
| **Pickles step circuits** | **~650–1,040** deployed | §4.2 |
| After the dregg-side FRI knobs (§5) | **~325–455** | |
| Floor without a column reduction or a Mina-targeted shrink | **~260** | §5.3 |
| Security the budget buys | **~50 bits** (`min{51, 73} − 1`) | machine-checked as an *arithmetic reading*, not an adversary bound (§6) |

**The single biggest cost driver is not the FRI logic, not the S-boxes, and not the AIR
evaluation. It is the `mod p` reduction** — now measured at **~64% of the per-permutation rows**
(§3.8), of which pure range-check gates are 38%. "BabyBear is 31-bit so it fits natively in Pasta"
is true and load-bearing — it is exactly what makes this route *expressible* where the pairing
route is not. But a 31-bit prime inside a 255-bit field is still a **foreign modulus**: every
multiplication chain must be reduced with a witnessed quotient and **range checks**. Kimchi's
native Poseidon costs 11 rows per permutation; this shape over a foreign 31-bit prime costs
**2,600**. **The ~236× is the reduction, not the hash.**

⚑ **The measurements are wired.** `scripts/check-mina-attestation.sh` — a `scripts/local-gates.sh`
row and a `ci.yml` job — re-runs **every bolded MEASURED figure above** and fails if any drifts more
than 2%, on top of KATs against the deployed p3 objects and **56 fault injections** with a
two-second pre-flight that verifies each still matches a real pattern. §3.14 separates what is
measured, what is a stated count × a measured price, and what is still a count nobody has taken.

⚑ **AND THE MEASUREMENTS ARE NOT THE POINT.** As of §3.12 the query indices and fold challenges are
**DERIVED from a Fiat–Shamir transcript** rather than witnessed, and §3.13b joins the derivation to
the walk in one statement. That is the difference between *"there exist 19 indices at which this
proof is consistent"* — which a cheating prover satisfies by choosing them — and a FRI check. It
cost 0.48% of the walk's rows. **The row budget was never the hard part; the binding was.**

⚑ **AND AS OF §3.15 THE WALK IS ABOUT SOMETHING.** Every rung through §3.13b starts its fold chain
from a **witnessed** reduced opening — so it authenticates a number the prover chose, and says
nothing about the committed trace. §3.15 computes that number instead, from the MMCS-opened rows,
the claimed evaluations at ζ (which are **absorbed** before `alpha` is sampled) and the transcript's
own index. The gate does not assert the closure: it **proves a witness the previous statement admits
and requires the new one to refuse it**. What is still missing is §3.16's `C_i` — the constraints
themselves. Until those are evaluated, the walk authenticates a low-degree function that encodes
nothing in particular.

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

> ⚑ **CORRECTION, 2026-07-28 (§3.14): the ~7 rows/Horner is wrong. It is 49 — MEASURED.** The lazy
> reduction argument above is sound in kind and wrong in size: `extAdd` alone costs 19 rows because
> each of the 4 lanes carries a `reduceLane`, and `extMul` costs 31. So the residual is
> **≈ 1.0 × 10⁶ rows, ~3.5% of the total**, not 1.5–2%. The conclusion survives — this is still a
> hashing problem, not an arithmetic one — but the number was optimistic by 2.5–3×.

**≈ 3.5% of the total** (measured unit × §2.4's own count). Real, worth budgeting, not the driver.
**The size question is a hashing question.**

---

## 3. Pricing ONE Poseidon2-w16-BabyBear permutation in Kimchi rows

> ⚑ **§3.3–3.7 are the DERIVATION, kept because its method is what the measurement confirms.
> The ANSWER is §3.8: 2,600.5 rows, measured on a circuit that compiles and proves.** Where a
> number here disagrees with §3.8, §3.8 wins.

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

| per permutation | rows | **measured (§3.8)** |
|---|---:|---:|
| S-boxes (mults + reductions + range checks) | ~1,200 | **1,410** |
| external linear layers (8×) | ~288 | **272** (+34 initial, +128 round-constant adds) |
| internal linear layers (13×) | ~200 | **728**, together with the re-bounding |
| internal-layer re-bounding | ~370 | ↑ |
| **TOTAL** | **~2,050 — call it ~2,000** (range 1,600–2,600) | **2,600.5** |

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

**So the honest band was:**

| assumption | rows/perm | total (× 11,000) |
|---|---:|---:|
| §3.3 single-native-element method delivers | ~2,000 | **~2.2 × 10^7** |
| generic-emulation parity with the measured gnark figure | ~8,400 | **~9 × 10^7** |

The ~2,000 was a design claim, not a measurement.

### 3.8 ⚑ MEASURED — the band is closed, and the design claim was ~30% low

*2026-07-28. §3.7's own recommendation was "write a single o1js `P2.perm` gadget and read
`getRows()` off it". Done: `bridge/mina-zkapp/src/Poseidon2BabyBearW16.ts`, measured by
`bridge/mina-zkapp/scripts/poseidon2-babybear-rows.ts` (`npm run poseidon2-rows`) at o1js 2.15.0.
Everything below this line replaces the estimate above it.*

> ## **2,600.5 Kimchi rows per Poseidon2-w16-BabyBear permutation.**
>
> **1.30× the ~2,000 design claim. 3.2× CHEAPER than gnark-emulation parity.**
> The 4× band is closed at the optimistic end.

`Provable.constraintSystem` reports **2,602 rows** for one permutation and 8,673 for three;
the marginal figure is `(8,673 − 2,602)/2 = 2,600.5`. Gate mix for one permutation:
`Generic 1,623 · RangeCheck0 701 · Lookup 278`. `compress(l,r)` — the deployed
`TruncatedPermutation<·,2,8,16>` the Merkle tree actually calls — is the same 2,602 rows, because
the truncation to 8 lanes is free.

**It is a measurement of the right object, and of an object that exists.**

- The circuit is checked inside `Provable.runAndCheck`, on three inputs, against a bigint
  reference which is itself checked against the two `#guard` vectors of
  `metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean` — i.e. against
  `default_babybear_poseidon2_16().permute(·)`, bit-exact. A wrong output makes the constraint
  system unsatisfiable (asserted, not assumed).
- It **compiles and proves**: a one-permutation `ZkProgram` compiles in ~6 s, proves in ~6 s,
  verifies, and its public output *is* `perm([0..15])`. So "2,602 rows" is a claim about a circuit
  Pickles accepts, not about a gate count nobody ran.
- Bound tracking is explicit and enforced: every value carries an integer upper bound and
  `assertSafe` throws if one could reach the Pasta modulus, because at that point field arithmetic
  stops agreeing with integer arithmetic and the circuit is unsound rather than slow. (The gate's
  self-test injects exactly that fault — a 2^32 lane bound instead of 2^31 — and requires a red.)

**Where the rows actually go — §3.4's table, measured.** Marginal rows, from differencing two
copies of each component:

| item | §3.4 estimate | **MEASURED** | note |
|---|---:|---:|---|
| S-box `x^7` (141 per permutation) | ~1,200 (8.5 ea) | **1,410** (10.0 ea) | of the 10, **8 are the `mod p` reduction** |
| external linear layer (9× incl. the initial one) | ~288 | **306** (34 ea) | add-only; the estimate was *right* |
| external round-constant materialisation | not budgeted | **128** (16/round) | `lane + rc` is a generic gate, not free |
| internal rounds, layer + re-bounding (13×) | ~570 | **728** (56 ea) | the estimate's biggest miss |
| final re-bound before the last external round | not budgeted | **~28** | |
| **TOTAL** | **~2,050** | **2,600.5** | |

Three corrections worth naming:

1. **§3.3's S-box price was good.** 8.5 estimated, 10.0 measured — the reduction method (one
   native element per BabyBear value, `p` as a coefficient, non-canonical intermediates, exactly
   one reduction per S-box) works as described. The extra 1.5 is o1js's cheapest sub-32-bit range
   check costing ~2.5 rows rather than the ~1.33 §3.3 assumed, plus the 4-limb quotient check.
2. **§3.4 under-priced the internal layer's re-bounding by ~2×** (~370 → ~728 including its
   linear ops). The nine lanes carrying a full-width inverse coefficient (`½`, `2⁻⁸`, `2⁻²⁷`, …)
   gain ~31 bits *every* internal round and must be reduced every round; only the six
   small-coefficient lanes can be left to grow. Reducing `partSum` once per round instead of all
   fifteen lanes is what keeps this at 728 rather than ~1,000 — that is an optimisation the
   measured implementation takes and the estimate did not model.
3. **⚑ The reduction is confirmed as the driver, and the share is now measured: ~64%.**
   `RangeCheck0` + `Lookup` gates alone are 979 of 2,602 rows (38%), and the generic gates that
   carry the `v = q·p + r` identities take it to ~1,676 (64%). §0's "~70%" stands.

**What this does NOT say.** This is a first-cut implementation on o1js's *stock* gadgets
(`rangeCheck64`, `rangeCheck3x12`, `multiRangeCheck`). A hand-tuned version could plausibly shave
10–20% — batching quotient limbs across S-boxes into shared `multiRangeCheck` slots is the obvious
one — but not 2×, because 64% of the cost is range-check gates whose per-bit rate (~66 bits/row) is
a property of Kimchi's lookup gates, not of this code. **And it re-prices §3.11's custom gate:** a
`Poseidon2BabyBear` gate would delete the generic gates and leave the reductions, i.e. **~1,700
rows, not the ~900–1,100 §3.11 guesses** — a 1.5× win, not 2×.

**It is ratcheted, not just recorded.** `scripts/check-mina-attestation.sh` (a `local-gates.sh` row
and a `ci.yml` job) re-runs the measurement and FAILS if rows/permutation moves more than 2% from
the 2,600.5 quoted here. A cited number nothing re-produces is not a measurement, and this document
has been the reason to care about exactly that distinction.

### 3.9 ⚑ MEASURED — a Merkle OPENING, which is the object FRI actually pays for

*2026-07-28. §3.8 measured one permutation. A FRI verifier never buys one permutation; it buys
**openings**, and an opening is not `depth × 2,600.5`. `bridge/mina-zkapp/src/Poseidon2Merkle.ts`,
measured by `bridge/mina-zkapp/scripts/poseidon2-merkle-rows.ts` (`npm run poseidon2-merkle`).*

> ## **2,677 Kimchi rows per Merkle level. 58,971 rows for the deployed depth-22 opening.**
>
> **ONE input-phase opening does not fit in one Pickles step.** 58,971 rows is 0.90× the 2^16
> step *domain* and **1.07–1.23× the usable rows** (§4.1).

| item | **MEASURED** |
|---|---:|
| one permutation, standalone (§3.8) | 2,600.5 |
| **one Merkle level** (cond-swap + range checks + compress + lane reduction) | **2,677** |
| depth-22 opening (the deployed `\|D⁰\| = 2^22`, `cap_height = 0`) | **58,971** |
| one leaf-sponge block (`PaddingFreeSponge<·,16,8,8>`, `ceil(w/8)` blocks) | **2,632** |
| row opening (width-13 sponge + depth-2 fold), as a `ZkProgram` | **10,775** |

**The +76.5 rows/level over the bare permutation is not overhead to be optimised away.** It is:

- **8 range checks on the witnessed sibling lanes.** The bound tracking §3.8 rests on is a claim
  about the size of every value in the circuit. A sibling arrives as an unconstrained private
  input, so without `assertLaneLt2p31` on each of its 8 lanes the whole soundness argument is
  about numbers nothing forces to be small. The measurement script injects an out-of-range lane
  and requires a refusal.
- **8 lane reductions.** ⚑ **A correction to `Poseidon2BabyBearW16.ts`, which claimed the
  permutation's output lanes are `< 2^31` and "one conditional subtraction away" from canonical.**
  They are not: the last thing a permutation does is the ADD-ONLY external layer, fan-in 35, so an
  output lane is bounded by ~35·2^31 ≈ 2^36.13. Re-feeding a digest costs a full `reduce`;
  comparing one costs a `reduce` *and* a conditional subtraction. That distinction is invisible
  when you measure ONE permutation — which is exactly what §3.8 did — and it is the first thing a
  hash chain runs into.
- the conditional swap (16 `Provable.if`s per level).

**It is KAT'd against the DEPLOYED Rust, not against a transcription.**
`circuit-prove/sketches/mina-pasta-hash-probe`'s `p2merkle` subcommand calls
`p3_baby_bear::default_babybear_poseidon2_16`, `p3_symmetric::TruncatedPermutation<·,2,8,16>` and
`p3_symmetric::PaddingFreeSponge<·,16,8,8>` at the workspace's pinned p3 rev `82cfad73`, on rows
carrying a git HEAD, a millisecond timestamp and a 128-bit nonce. o1js must reproduce, elementwise:
every leaf digest, all 23 levels of the zero-subtree ladder, all 22 siblings, all 22 `isRight` bits,
all 22 intermediate nodes, and the root. The circuit then reproduces the same root inside
`Provable.runAndCheck`, and a depth-3 instance **compiles, proves and verifies** with the p3-emitted
leaf as its public output.

**Ratcheted** by `scripts/check-mina-attestation.sh` at 2% on all three of rows/level,
rows/depth-22-opening and rows/sponge-block.

### 3.10 ⚑ MEASURED — one whole FRI QUERY at the deployed geometry

*2026-07-28. `bridge/mina-zkapp/src/FriQueryStep.ts`, measured by `bridge/mina-zkapp/scripts/fri-query-rows.ts`
(`npm run fri-query`). This is `verify_query` (`vendor/plonky3-fri-82cfad73/src/verifier.rs:363`)
at `|D⁰| = 2^22`, `max_log_arity = 1`, 16 commit-phase layers, `cap_height = 0`.*

> ## **684,726 Kimchi rows for ONE FRI query. 13–15 Pickles steps. 10.4× the 2^16 domain.**
>
> **19 queries ⇒ 1.30 × 10⁷ rows ⇒ 237–272 Pickles steps — for the FRI query walk ALONE.**

Per query: the input-phase opening at depth 22, plus one commit-phase opening per layer at depths
21…6 = **238 Merkle levels**, plus 16 leaf sponges (each arity-2 row is 8 BabyBear elements = one
full sponge block = exactly one permutation), plus 16 arity-2 folds in
`BinomialExtensionField<BabyBear, 4>`, plus the coset-point descent. Implied rows per Merkle level
inside the query: **2,877** — higher than §3.9's 2,677 because the per-round sponge, fold and
extension arithmetic are amortised into it.

**The fold arithmetic is KAT'd against p3.** The probe's `p2fold` subcommand computes the same
two-point Lagrange interpolation `fold_row` does; the crate's own tests check its `ext_mul` against
p3's `BinomialExtensionField<BabyBear, 4>` multiplication, pin `X⁴ = 11` against that same type, and
check the interpolation against an independently solved interpolant plus both boundary cases. o1js
must reproduce the extension product, the fold, and the coset point — the last **derived from the
witnessed query-index bits**, not witnessed alongside them.

⚑ **The coset descent is `x_{r+1} = (−1)^{b_r} · x_r²`, not `x_r²`.** `rbl(i, L) = b·2^{L−1} +
rbl(i≫1, L−1)` and `g_L^{2^{L−1}} = −1`, so the naive squaring is wrong on exactly half the
indices — invisible to any test whose index happens to be even.

**And the first version of this check WAS that test.** It drew a random query index, so with the
sign correction deleted from the circuit it went **green** — measured, by injecting exactly that
fault. The repair is deterministic: the check now runs the descent at `index & ~1` *and*
`index | 1`, requires the naive `x²` to be **right on the even one and wrong on the odd one**, and
fails if the odd polarity never ran. The Rust side's
`coset_points_descend_by_squaring_and_a_sign` walks the deployed 16-layer schedule and asserts it
saw both. A gate that can only go red on half its inputs is half a gate.

⚑ **The 22 query-index bits are ONE object.** Bit `r` selects which slot round `r`'s folded value
occupies; bits `r+1…22` are the path directions for round `r`'s depth-`21−r` opening; and bit
`r+1` — **not** bit `r` — carries the sign of round `r`'s coset descent. A circuit that witnessed a
fresh index per round would measure identically and verify something strictly weaker.

> ⚑ **CORRECTION, 2026-07-28: this section's own circuit had the third of those three wrong.**
> `commitPhaseRound` descended on the SLOT bit. `verify_query` shifts the index *before* it folds,
> so round `r` folds at `i_r = index ≫ (r+1)` and the descent sign is the low bit of `i_r`, i.e.
> `indexBits[r+1]`. The two readings agree whenever two consecutive index bits are equal — on about
> half of any chain's rounds, and on **100% of the all-zero index every `getRows()` measurement
> uses**. The single-round descent check *directly above*, which the previous lane had already
> caught being green-with-the-fault and repaired into a deterministic both-polarity test, **stayed
> green through it**: one round never consumes two bits, so no single-round instrument can see it.
> It was found by §3.13, against p3's own sixteen-round chain. The row count is unchanged (a
> `Provable.if` costs the same on either bit), so **nothing in this document's arithmetic moves** —
> which is exactly why it survived. See §3.13.

**⚑ WHAT IS NOT IN THE 684,726.** The DEEP quotient (reduced openings and their `alpha` powers),
the AIR constraint evaluation, the Fiat–Shamir challenger that produces `beta` and the query index,
and the proof-of-work grind. **A query costs at least this, not at most.** The 237–272 steps is
therefore a *floor* on the query walk, and it is already consistent with §5.3's ~260.

The challenger and the grind are no longer merely absent from the number — **§3.12 builds them and
measures them at 62,637 rows**, i.e. 0.48% of the 19-query walk. The DEEP quotient and the AIR
evaluation are still not built; §3.14 prices them from measured units and keeps them on the ledger
as the next rungs.

**Ratcheted** at 2%. ⚑ The measurement needs `--max-old-space-size=16384`: o1js holds all 684,726
rows in the JS heap and OOMs at the 4 GB default.

### 3.11 What a custom gate would buy — and why it is not on the table

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

### 3.12 ⚑ MEASURED — the CHALLENGER, and why it outranks every row count here

*2026-07-28. `bridge/mina-zkapp/src/FriChallenger.ts`, measured by `bridge/mina-zkapp/scripts/fri-challenger-rows.ts`
(`npm run fri-challenger`). This is `DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>`
running exactly the schedule `p3_fri::verifier::verify_fri` runs at the deployed knobs.*

> ## **62,637 Kimchi rows for the WHOLE Fiat–Shamir transcript. 23 permutations. 2 Pickles steps.**
>
> **0.48% of the 1.30 × 10⁷-row query walk it authorises — and without it that walk proves
> nothing.**

**This is the rung that changes what the others mean.** §3.10 walks one FRI query at a **witnessed**
index under **witnessed** `beta`s. That statement says *"there exist 19 indices at which this proof
is consistent"*, and a cheating prover supplies the 19 it can answer. FRI's soundness is entirely
the claim that the indices are drawn *after* the commitments by a function the prover cannot steer.
§3.10 showed we can walk *a* FRI proof; this is what makes it *the prover's*.

The schedule, read off `fri/src/verifier.rs:139-270` line for line, and the permutations each part
costs at the deployed knobs:

| step | source | perms |
|---|---|---:|
| the batch-STARK preamble (stand-in, 13 elements) | — | 1 |
| `alpha = sample_algebra_element()` — the 5 buffered preamble elements force a duplex on a PARTIAL rate | `:139` | 1 |
| 16 × (`observe(commit)`; `check_witness(0, ·)`; `beta = sample_algebra_element()`) | `:211-219` | 16 |
| `observe_algebra_slice(final_poly)` | `:236` | 0 |
| 16 × `observe(Val::from_usize(log_arity))` | `:249-251` | 2 |
| `check_witness(16, query_pow_witness)` | `:254` | 1 |
| 19 × `sample_bits(22)` | `:268` | 2 |
| **total** | | **23** |

**95.5% of the 62,637 rows are the permutations.** The rest is lane hygiene, the 19 22-bit
decompositions and the PoW range check — about 2,800 rows for the entire index derivation.

**It is KAT'd against the deployed challenger, not against a transcription.** The probe's `p2chal`
subcommand runs `p3_challenger::DuplexChallenger` on scripted observe/sample traces and emits every
value plus the final sponge state, input buffer and output buffer; `p2fritranscript` runs the whole
`verify_fri` schedule and emits `alpha`, all 16 `beta`s, a **ground** 16-bit PoW witness and all 19
query indices. o1js must reproduce all of it in the bigint twin *and* inside the circuit.

⚑ **The hash was never the risk. The state machine was.** Three edges each look like a detail and
each silently changes every challenge downstream, and each gets a check *plus* a discriminating
polarity showing the plausible wrong reading gives a different answer:

1. **`output_buffer.pop()` takes from the BACK** (`duplex_challenger.rs:243-245`). The first sample
   after a permutation is `sponge_state[RATE-1]`, not `[0]`.
2. **A partial absorb OVERWRITES only its prefix** (`:86-99`); the unabsorbed rate lanes keep the
   *previous* permutation's output rather than being zero-filled. The deployed schedule hits this
   at `alpha`, because the preamble does not end on a rate boundary.
3. **`check_witness(0, w)` returns BEFORE observing** (`grinding_challenger.rs:41-43`). The deployed
   commit-phase PoW is 0 bits, so all 16 per-layer calls must leave the transcript byte-identical.
   A circuit that "checked" them by absorbing the witness would get **all 16 `beta`s wrong.**

> ⚑ **THIS LIST SAID FOUR, AND THE SELF-TEST REFUTED THE FOURTH.** `observe` also clears the output
> buffer (`:150`), written up here as load-bearing. It is not: `sample` re-duplexes whenever the
> INPUT buffer is non-empty and `observe` always makes it non-empty, so a stale output buffer can
> never be read. The clear is **defensive**. The fault injection written for it — delete the clear,
> require the gate to go red — **stayed green**, which is how the over-claim surfaced, and it was
> deleted rather than kept as a falsifier that cannot fire. The leg now *proves the removal
> invisible* on five schedules chosen to stress it. A guard that cannot fail is not a guard, and a
> claim that survives only because nobody tried to falsify it is not a finding.

⚑ **And one constraint that no KAT can see.** `sample_bits(k)` splits a canonical lane as
`c = hi·2^k + Σ bᵢ2ⁱ`. Every KAT above compares against p3 on an *honest* witness, which produces
the right decomposition whether or not anything forces it to. **Drop the bound on `hi` and the
relation is satisfiable over Pasta for every bit pattern** — `hi = (c − lo)·2^{−k}` always exists —
so the prover derives whatever query index it likes out of a perfectly correct sponge, and every
other check stays green. The constraint is therefore split from its witnessing
(`assertLowBitsSplit`), and the gate supplies a lying `hi` for a named wrong index and requires a
refusal, at a fixed lane, both polarities.

**A 4-layer instance of the same schedule — same 16-bit PoW, same 22-bit index width — compiles
(41,033 rows), proves and verifies**, its public output binds every derived challenge, a perturbed
commitment does not reach the same binding, and no proof exists for a PoW witness one off the
ground one.

> ⚑ **AND AN INSTRUMENT LIMITATION THAT AFFECTS EVERY RANGE CHECK IN THIS DIRECTORY, found by the
> negative test above coming back GREEN.** `Provable.runAndCheck` **does not evaluate lookup
> constraints.** Measured: `Gadgets.rangeCheck3x12(Field(4096))` — a 12-bit lookup on 2^12 — runs
> clean under `runAndCheck`. So a bound that rests on the lookup alone is sound *in a proof* and
> **undemonstrable outside one**: no gate can ever show it refusing. The reason
> `assertLaneLt2p31(2^31)` *is* caught is not the lookup at all — it is that its witness truncates
> to 12+12+7 = 31 bits, so an out-of-range value loses bits and the recomposition
> `a + 2¹²b + 2²⁴c = r` fails a plain equality. `assertLtPow2` originally witnessed a full 12-bit
> top limb, leaving the recomposition slack by `12 − topBits` bits and the bound carried *only* by
> the lookup — and its own both-polarity test passed. It now masks the top limb to `topBits`, so
> **the bound is carried twice** and the second carrier is the one an instrument can see.

⚑ **What this does NOT close.** The transcript starts from a *preamble* standing in for the
batch-STARK's own observes (degree bits, trace commitments, public values, ζ) that precede
`verify_fri`. Binding that preamble to the real STARK preamble is a further rung. It is a strictly
smaller hole than a witnessed index — the preamble is absorbed, so changing it changes every `beta`
and every index — but it is a hole, and §3.14 keeps it on the ledger.

**Ratcheted** at 2% on rows, and **exactly** on the permutation count: a schedule change that
happens to land within 2% of 62,637 still fails.

### 3.13 ⚑ MEASURED — the COMMIT PHASE as ONE object, and the defect that found

*2026-07-28. `verifyCommitPhase` in `bridge/mina-zkapp/src/FriQueryStep.ts`, measured by
`bridge/mina-zkapp/scripts/fri-chain-rows.ts` (`npm run fri-chain`).*

> ## **623,310 rows for one query's whole 16-layer commit phase. 45,186 with the paths capped — which FITS, and PROVES.**

| shape | **MEASURED** |
|---|---:|
| 16 layers, deployed path depths 21…6 (216 Merkle levels), final-poly check | **623,310** |
| 16 layers, path depth 0 (`cap_height = log_folded_height`), final-poly check | **45,186** |
| marginal cost of one reduced-opening roll-in | **88** |
| implied rows per Merkle level inside the chain | **2,677** — exactly §3.9's standalone figure |
| the same chain as a `ZkProgram` at depth 0 (public commitments + derived index out) | **45,362** |

**A chain of rounds is not sixteen copies of one round**, and §3.10 proved one round. What only a
chain has: one index doing three jobs at three different offsets; a coset point descending sixteen
times; a landing value that has to *mean* something (the comparison against the final polynomial at
the point the leftover index bits name); and reduced openings rolling in partway down scaled by
`beta^arity`. All four are now in the circuit and all four are KAT'd against **`p2chain` — p3's own
sixteen-round chain**, not sixteen calls to a one-round emitter. That distinction is the whole
point: a script that chains a one-round emitter itself cross-checks the composition against nothing.

⚑ **It found a real defect on the first run.** The coset descent took `indexBits[r]` where
`verify_query` takes `indexBits[r+1]` — see §3.10's correction box. The leg now runs the chain at
four indices chosen so the two readings *coincide* (all-zero, all-ones) and *differ at every round*
(alternating bits), keeps the wrong reading as a **live twin** rather than a comment, and fails if
that twin ever stops diverging. A "we fixed it" with no standing counter-example is precisely how
the single-round check stayed green.

**The capped shape is a real p3 configuration, not a fiction**: at path depth 0 the round's leaf
digest *is* its commitment, which is the `cap_height = log_folded_height` corner of the same
`MerkleTreeMmcs`. So the whole 16-layer chain **compiles, proves and verifies**, its public output
names the index it walked, and there is no proof for a final polynomial it does not land on, a
mid-chain commitment its row does not open under, or a different index against the same
commitments.

#### 3.13b THE SEAM — the chain driven by DERIVED challenges

> ## **686,005 rows: the whole transcript plus one commit phase at deployed depths, in ONE statement. The join costs 58 rows.**

§3.12 derives an index; §3.13 walks a chain at one. **Each alone is satisfiable by a prover that
answers at its own index while deriving a different one.** They are a FRI verifier only when the
*same* index does both jobs — an identity that exists nowhere except inside a program that performs
both. `makeDerivedQueryProgram` is that program: the index and every `beta` come out of the
transcript, and **the commitment the challenger absorbs is the commitment the row must open
under.**

62,637 + 623,310 = 685,947, measured jointly at **686,005**. The composition is essentially free;
what it buys is the only thing that made the other two mean anything.

⚑ **Finding an honest witness for it is itself the argument.** Because the absorbed commitments are
the opened-under commitments, the derived index depends on the very rows it selects. A real prover
escapes the circularity by committing to a whole *codeword* first and opening afterwards; a test
carrying one row per layer cannot, and must **search** for a fixed point. That the search is
necessary is the property being demonstrated: the prover does not get to pick the index. The proved
instance runs at `|D⁰| = 2^6`, 2 layers, 19,248 rows — and, a **labelled reduction**, an 8-bit
rather than 16-bit query PoW, because the search re-grinds per candidate. The deployed 16 bits are
exercised at full width by §3.12 (twin, circuit and proof) and by this leg's own refusal. Three
refusals hold: a commitment absorbed but not opened under, a preamble one element off, and a PoW
witness that does not grind.

### 3.14 ⚑ The honest remaining distance

*What is now measured, what is derived from measured units, and what is still a count nobody has
taken. **Everything in the first block is a `getRows()` on a committed circuit that is KAT'd
against the deployed Rust and ratcheted at 2%.***

**MEASURED**

| object | rows | § |
|---|---:|---|
| one Poseidon2-w16-BabyBear permutation | 2,600.5 | 3.8 |
| one Merkle level | 2,677 | 3.9 |
| the deployed depth-22 opening | 58,971 | 3.9 |
| one whole FRI query (input opening + 16-layer commit phase) | 684,726 | 3.10 |
| the whole Fiat–Shamir transcript (23 permutations) | 62,637 | 3.12 |
| one query's 16-layer commit phase at deployed depths | 623,310 | 3.13 |
| transcript + one commit phase, jointly | 686,005 | 3.13b |
| extension multiply / add / scale | 31 / 19 / 19 | 3.14 |
| base-field inverse | 15 | 3.14 |
| one arity-2 `fold_row` | 150 | 3.14 |
| **one extension Horner step `acc ← acc·α + v`** | **49** | 3.14 |
| one reduced-opening roll-in | 88 | 3.13 |
| **the whole DEEP quotient, ONE query, at the root's 940+175-column table set** | **154,523** | **3.15** |
| the same, p3's literal per-column loop | 287,123 | 3.15 |
| transcript + DEEP + the capped commit phase, jointly | 280,513 | 3.15 |
| the DEEP-bound query program, proved (2^6, 2 layers, 3 batches) | 50,409 | 3.15 |
| the same with `initial` witnessed — every rung before 3.15 | 48,655 | 3.15 |
| the AIR side's per-instance FIXED cost (selectors, chunk recomposition, closing equality) | 2,025 | 3.16 |
| the AIR side's per-CONSTRAINT α-fold (**not** `C_i`) | 48 | 3.16 |

⚑ **§2.4 priced a Horner step at "~7 rows". It is 49 — 7× off**, and the DEEP-quotient and AIR
residual scales linearly with it. At §2.4's own count (~14,300 Horner ops for the reduced openings,
plus ~10⁴ quartic multiplies for the constraint fold) that residual is **≈ 1.0 × 10⁶ rows, not the
2–4 × 10⁵ estimated** — the number in §2.4 is wrong by 2.5–3× and was corrected here.

⚑ **AND THAT CORRECTION WAS ITSELF LOW BY 3×, MEASURED 2026-07-28.** §3.15 builds the DEEP quotient
at the root's own column census — 940 main × 2 points + 175 preprocessed × 2 points + 7 instances ×
2 chunks × D=4 = **2,286 terms per query** — and it is **154,523 rows per query, 2.94 × 10⁶ across
19**. The "~2.4 × 10⁴ ext ops" above counted roughly one term per *column*, not per (matrix, point,
column). So the DEEP quotient **alone** costs three times what this row allotted to DEEP *and* AIR
together. And §3.16 adds a term nobody had counted at all: the **2.97 × 10⁶ rows** of challenger
permutations required just to *observe* those 2,286 opened values before `alpha` is sampled.

**DERIVED FROM MEASURED UNITS** (a stated count × a measured price — no longer an estimate × an
estimate)

| object | derivation | rows |
|---|---|---:|
| input-phase openings, per query, 4 rounds all at depth 22 (§2.2) | 88 levels × 2,677 + 151 sponge blocks × 2,600.5 | **6.3 × 10⁵** |
| … × 19 queries | | **1.2 × 10⁷** |
| ~~DEEP quotient + AIR constraint evaluation~~ | ~~~2.4 × 10⁴ ext ops × 31–49~~ | ~~≈ 1.0 × 10⁶~~ — **superseded, see below** |
| **DEEP quotient × 19 queries** | 154,523 × 19, **measured** (§3.15) | **2.94 × 10⁶** |
| **observing the 2,286 opened values into the challenger** | 1,143 perms × 2,600.5 (§3.16) | **2.97 × 10⁶** |
| AIR constraint evaluation | `A + N·h` = 14,175 + N × 48, **plus `C_i`** (§3.16) | **≥ 1.4 × 10⁴, N UNCOUNTED** |
| commit phase × 19 queries | 623,310 × 19 | **1.18 × 10⁷** |
| transcript (FRI schedule only) | measured | **6.3 × 10⁴** |
| **whole root verify** | sum | **≈ 3.0 × 10⁷** — and the independent permutation count in §0 says 2.9 × 10⁷ |

**STILL UNCOUNTED — and these are counts, not prices**

1. **The root's own `degree_bits`.** §1.3 says no committed measurement exists; §5.2's open
   contradiction (is there a live W24 table?) is worth ~10% on its own. Every "4 rounds all at
   depth 22" above rests on it.
2. ~~**The roll-in schedule.**~~ **CLOSED as a schedule, 2026-07-28 (§3.15d).** It was never a free
   parameter: the opening at height `L` rolls in after round `LGMH − 1 − L`, the opening at `LGMH`
   is `initial`, and `verify_query` refuses any other first height. `rollInSchedule` computes it and
   the circuit uses it. What remains is the *set of heights*, which is (1).
3. **The input row widths.** §3.10 measures an 8-element input row (one sponge block). The real main
   round is 940 columns ⇒ 118 blocks. That is in the derivation above, not in the 684,726.

**STILL OPEN AS SOUNDNESS, not as size**

1. **The preamble binding.** §3.12's transcript starts from a **13-lane stand-in** for the
   batch-STARK's own observes. Until those are the real ones, the derivation is "the challenges
   given this state", not "the challenges". ⚑ And §3.16 measures what the real one costs:
   **2.97 × 10⁶ rows** of challenger permutations just to absorb the 2,286 opened values. It was
   listed here only as a soundness residual; it is a **size term of the same order as the DEEP
   quotient**.
2. ~~**The DEEP quotient.**~~ **CLOSED 2026-07-28 — §3.15.** The reduced openings are now COMPUTED
   from the MMCS-opened rows, the absorbed claimed evaluations and the transcript's `alpha`.
   `makeDeepBoundQueryProgram` keeps the pre-3.15 statement compiled beside it and the gate
   **proves a witness the old statement admits and the new one refuses**, so the closure is
   exhibited rather than asserted.
3. **The AIR constraint evaluation** at ζ. **STARTED, §3.16**: the selectors, the α-folded
   accumulator, the quotient-chunk recomposition and the closing equality are built, KAT'd against
   p3's own domain algebra at four `degree_bits`, and priced at `A + N·h`. **`C_i` itself — dregg's
   seven AIRs — is not built, and `N` is not counted.** Until it is, the walk still authenticates a
   low-degree function that encodes nothing in particular.
4. **19 queries, not 1.** Every rung here walks one.
5. **The input-phase MMCS opening over MIXED heights.** §3.15's program carries ONE matrix per
   batch; `MerkleTreeMmcs::verify_batch` over several matrices of different heights under one root
   is priced (§3.14's 6.3 × 10⁵/query) and not implemented.

---

### 3.15 ⚑ MEASURED — the DEEP QUOTIENT, and the number that stops being the prover's

*2026-07-28. `bridge/mina-zkapp/src/DeepQuotient.ts`, measured by
`bridge/mina-zkapp/scripts/fri-deep-rows.ts` (`npm run fri-deep`), KAT'd against
`p2deep` — `p3_fri::verifier::open_input` over `BinomialExtensionField<BabyBear,4>`.*

> ## **154,523 rows for ONE query's whole DEEP quotient at the root's real 940+175-column table set. 2.94 × 10⁶ across 19 queries — and §3.14 priced DEEP *and* AIR together at 1.0 × 10⁶.**

**This is the rung §3.14 named as the last structural gap, and it is the same *kind* of rung the
challenger was.** Every measurement above §3.15 starts its fold chain from `initial` — the reduced
opening at the global max height — and in every one of them `initial` is a **witness**. A FRI walk
over a witnessed starting value authenticates *a number the prover chose*. It says "some low-degree
function takes this value at this point"; it says nothing whatever about the committed trace. §3.12
made the index unchooseable and §3.13b made the walk the prover's own — neither touched the number
the walk is about.

`open_input` (`vendor/plonky3-fri-82cfad73/src/verifier.rs:524-660`) is the object that closes it:

```
ro[L] += alpha^k * (f(z) - f(x)) / (z - x)
```

for every opened matrix at height `2^L`, every opening point `z` and every column `f`, with

- **`f(x)`** an entry of the MMCS-opened input row — bound by the input-phase Merkle path;
- **`f(z)`** the claimed out-of-domain evaluation — bound by being **absorbed** into the challenger
  before `alpha` is sampled (`two_adic_pcs.rs:780-788`), so moving one moves every challenge and
  every query index;
- **`x`** derived from the same index bits the transcript produced;
- **`alpha`** the transcript's.

and `(f(z) - f(x))/(z - x)` is `q(x)` for `q(X) = (f(X) - f(z))/(X - z)`, which is low-degree
**exactly when `f(z)` is the true evaluation**. That equivalence is what the whole FRI walk is
*for*. It is pinned on the Rust side by `deep_quotient_is_the_quotient_polynomial`, which builds `q`
by **synthetic division** rather than by rearranging the same formula, and requires a falsified
`f(z)` to give a different DEEP term.

| shape | **MEASURED** |
|---|---:|
| the whole DEEP quotient, ONE query, 2,286 terms, factored Horner | **154,523** |
| the same, p3's literal per-column loop | **287,123** (1.86×) |
| per DEEP term | **67.6** factored / **125.6** literal |
| × 19 queries | **2,935,937** |
| transcript + DEEP + the **capped** commit phase, jointly | **280,513** |
| the join, over the three standalone figures (62,637 + 45,186 + 154,523) | **18,167** |
| the proved DEEP-bound query program (`|D⁰| = 2^6`, 2 layers, 3 batches, depth 0) | **50,409** |
| the same statement with `initial` **witnessed** — i.e. every rung before this one | **48,655** |
| **what the binding costs at that shape** | **1,754** |

The **factored** form is one Horner over each (matrix, point)'s columns followed by a single scale
by `alpha_pow · q`, instead of p3's three extension multiplies per column. It is an algebraic
identity, pinned both by `the_factored_horner_form_agrees_with_p3s_per_column_loop` on the Rust side
and by the in-circuit KAT running **both** forms against the same p3 output.

⚑ **The deployed-depth joint figure is a COMPOSITION, and is labelled as one.** 280,513 +
(623,310 − 45,186) = **858,637 rows** for transcript + DEEP + one commit phase at real Merkle
depths — 16–18 Pickles steps for one query, 297–340 for nineteen. It is not a single `getRows()`
because `Provable.constraintSystem` serialises the whole gate vector through the Kimchi wasm and
that allocator dies somewhere past ~8 × 10⁵ rows (the deployed-depth joint circuit OOMs it — the
wasm heap, not node's). The **join** is measured on the capped chain, where it is the same object
minus 216 Merkle levels that compose additively and were measured standalone in §3.13.

⚑ **And the join is ATTRIBUTED, not left as a number.** §3.13b measured the transcript-plus-chain
join at **58 rows**; this one is three orders larger, so the same circuit is measured a second time
*without* the DEEP quotient. Whatever the split, the DEEP seam is the term that grew, and the leg
prints both halves rather than reporting one figure and letting a reader assume it is free.

#### 3.15b THE GAP, EXHIBITED — not asserted

A rung whose predecessor cannot be caught accepting what it now refuses is a rung nobody has
measured. So `makeDeepBoundQueryProgram` carries **two methods compiled together**: `proveDeepQuery`
(the reduced opening computed) and `proveWitnessedInitial` (the reduced opening witnessed — exactly
the statement of §3.13b and everything before it). The leg then:

1. searches for a witness whose starting value is **not** the DEEP quotient of its own opened rows;
2. **proves it** under `proveWitnessedInitial`, and verifies the proof — a real proof object of the
   pre-rung-6 statement;
3. requires `proveDeepQuery` to **refuse the same public claim**.

Both happen, every run. Three further refusals hold and each isolates a different half of the
binding: an opened row one element off (the row is **not** in the transcript, so nothing but the
DEEP computation can see it), a claimed `f(z)` one element off (which moves the transcript *and*
the reduced opening), and an opening point `z` one element off.

#### 3.15c ⚑ FOUR CONVENTIONS THAT ARE EACH RIGHT ON A DEGENERATE FIXTURE — and one that is not a convention at all

The coset-descent defect of §3.13 survived a deterministic both-polarity check because **one round
never consumes two index bits**, so the check was right on 100% of the all-zero index every row
measurement supplies. `open_input` has four of the same shape, and every fixture in this leg
therefore carries **two heights, two matrices sharing a height in different batches, and multiple
opening points**:

| convention | when the wrong reading is invisible | live twin diverges |
|---|---|---:|
| `x` carries the multiplicative `GENERATOR` (31) | — | 16× |
| `x` uses `g_L`; the **fold chain** uses `g_{L+1}` | at reversed index 0 — the all-zero index | 12× |
| the index is **shifted down** by `LGMH − L` before reversal | if every matrix sits at the top height | 2× |
| `x` reads the **high** bits, not the low ones | at index 0 and at all-ones | 2× |
| no bit-reversal at all | when `rev(s) = s` | 8× |
| `alpha_pow` keyed by **height**, in **encounter** order | unless two matrices share a height AND a second height exists | both twins |

#### 3.15e ⚑ A FALSIFIER THAT COULD NOT FIRE — and what it says about every rung here

The fault injection written for *"the DEEP-bound query goes back to a witnessed starting value"* was
`initial: Provable.witness(BbExt, () => ro[0].ro)`. **It stayed green, every run.** The honest
prover's witness callback recomputes the same value from the same inputs, so **a derived variable
and a witness carrying that variable's value are indistinguishable to `Provable.runAndCheck`, to
`prove`, and to `getRows()`.** Nothing in this harness can tell them apart.

That is the same shape as the challenger's `observe`-clears-the-output-buffer twin (§3.12), and it
was deleted for the same reason: a falsifier that cannot fire is worse than no falsifier, because a
green run reads as a discharged obligation. Two of these have now been found by *building* the
instrument, and both times the finding was that a check nobody would have questioned was free.

What **can** see the realistic form of the regression — witness the value *and* delete the now-dead
computation, which is what a cleanup pass does — is the **row delta between the two compiled
methods**: 50,409 − 48,655 = **1,754 rows**, now ratcheted at 2%. A binding that stops costing
anything is a binding that stopped existing. Two mis-wirings an honest run *does* catch (starting
the chain from the wrong height's opening, and roll-ins off by one opening) are injected beside it.

⚑ **The general lesson, which applies above this section as well as inside it:** every "X is
derived, not witnessed" claim in §3.12–§3.15 rests on **reading the circuit**, not on a test that
could distinguish the two. The tests establish that the derived value is *correct*; only the row
delta establishes that the derivation is *load-bearing*.

⚑ **AND A THIRD ONE, FOUND BY RUNNING THE GATE RATHER THAN READING IT — IN §3.9's LEG, NOT THIS
ONE.** The Merkle rung's soundness check ("the circuit REFUSES an out-of-range sibling lane") built
its fault value as `s[0] + p`. But `assertLt2p31` bounds a lane by **2^31, not by `p`**, and
`s[0] + p ≥ 2^31` only when `s[0] ≥ 2^31 − p = 134,217,727` — **93.3%** of canonical lanes. On the
other **6.7%** the "fault" is a perfectly legitimate non-canonical representative under 2^31, the
circuit is *right* to accept it, and the check fails a green tree. The emitted leaves carry a fresh
128-bit nonce every run, so this was a **one-in-fifteen spurious red**, and the run that found it was
an ordinary full-gate run. The offset is now `2^31`, which is out of range unconditionally, and the
leg **asserts its own premise** before using it. A negative check whose fault value might not be a
fault is a check that reports on the weather.

⚑ **And a sixth "reading" that is not one.** `g_{L+1}^{reverse_bits_len(s, L+1)}` looks like another
mistake and is **algebraically the same function**: `s` carries `L` significant bits, so
`rev(s, L+1) = 2·rev(s, L)`, and `g_{L+1}² = g_L`. A fault injection written against it **could
never fire** — the same shape as the challenger's `observe`-clears-the-output-buffer twin (§3.12),
which stayed green and was deleted. It is **asserted as an identity** here rather than counted as a
divergence, and the leg fails if the identity ever breaks. Two of these have now been found by
building the instrument rather than by reading the code; the pattern is worth naming.

#### 3.15d The roll-in schedule was never a free parameter

§3.14 listed "the roll-in schedule" as an uncounted quantity. It is a **function**: `verify_query`
rolls the opening at height `L` in after the round whose *folded* height is `L`, so at
`max_log_arity = 1` that is round `LGMH − 1 − L`, and the opening at `LGMH` is not rolled in at all
— it is `initial`, and `verify_query` **refuses** a proof whose first reduced opening sits anywhere
else (`:388-393`). `rollInSchedule` computes it, the circuit uses it, and the leg checks the refusal.
What remains uncounted is the *set of heights*, which is the root's `degree_bits` — §3.14 item 1,
still open.

### 3.16 ⚑ MEASURED — the AIR constraint evaluation at ζ, started and priced

*2026-07-28. `bridge/mina-zkapp/src/AirEval.ts`, measured by
`bridge/mina-zkapp/scripts/air-eval-rows.ts` (`npm run air-eval`), KAT'd against `p2air` — p3's own
`TwoAdicMultiplicativeCoset::selectors_at_point`, `create_disjoint_domain`, `split_domains` and
`recompose_quotient_from_chunks`.*

> ## **The AIR side is `A + N·h` with `A = 14,175` and `h = 48`, both MEASURED — and `N`, the number of constraints across the root's 7 AIRs, is a count nobody has taken. It is written that way on purpose.**

Rungs 1–5 authenticate a value; §3.15 ties it to the claimed evaluations at ζ. **Nothing yet says
those evaluations satisfy dregg's constraint system**, so a verifier stopping at §3.15 certifies
that some low-degree function takes some values at ζ — true of an arbitrary polynomial. The closing
object is `VerifierData::verify_constraints_with_lookups`
(`p3-batch-stark/src/verifier/data.rs:49-102`):

```
accumulator = fold_i alpha (C_i(trace_local, trace_next, prep, ...))
accumulator * inv_vanishing(zeta) == quotient(zeta)
```

with `quotient(ζ)` recomposed from the opened chunks by Lagrange over the chunk domains. **This
module builds everything except `C_i`**, and every piece of it is KAT'd against p3 at four different
`degree_bits` (4, 9, 15, 16) — because `Z_H(X) = (g^{-1}X)^{2^k} − 1` is a chain of `k` squarings
and a fixture at one `k` cannot see an off-by-one in it, exactly as one FRI round could not see the
coset-descent sign.

| object | **MEASURED** |
|---|---:|
| one instance at `N = 1` / at `N = 101` | **2,073** / **6,873** |
| per CONSTRAINT — the α-fold only, **not** `C_i` | **48** |
| per-instance FIXED, net of the free first fold | **2,025** |
| `A` = the fixed cost across the root's **7** tables | **14,175** |

The split into `A` and `h` is the affine fit through two measured points; the *totals* are what is
measured. `measure(1)` includes one constraint whose fold is free (the Horner accumulator starts at
`C_0`), so subtracting one marginal price is what makes `A + N·h` exact for every `N` rather than
off by one fold.

| if `N` were … | fold rows | `+ A` |
|---|---:|---:|
| 558 (0.5 × columns) | 26,784 | 40,959 |
| 1,115 (1 × columns) | 53,520 | 67,695 |
| 2,230 (2 × columns) | 107,040 | 121,215 |
| 3,345 (3 × columns) | 160,560 | 174,735 |

⚑ **And `C_i` itself is in none of those numbers.** A degree-3 constraint over extension values
costs at least two extension multiplies (~62 rows) on top of its fold, so the table is a **floor**
on the AIR side rather than an estimate of it. Saying that is the point: §2.4 put a guessed unit
inside a guessed count and was **7× out on the unit alone**.

⚑ **The table set is the ROOT's seven.** `degree_bits = [9,9,15,14,15]` is the **BN254 shrink**
proof (§1.2). Pricing the AIR side against it would under-count by more than an order of magnitude,
and that mis-attribution has already been made once in this tree.

**What the AIR side does make exact, and it is large.** Every one of the **2,286** opened values is
`observe_algebra_slice`d into the challenger before `alpha` is sampled (`two_adic_pcs.rs:780-788`).
That is 9,144 lanes ⇒ **1,143 permutations ⇒ 2.97 × 10⁶ rows**, and §3.12 stood the entire
batch-STARK preamble in with **13 lanes**. It was listed only as a soundness residual; it is a size
term of the same order as the DEEP quotient.

**Three shift conventions are pinned, each with a live twin.** `create_disjoint_domain` multiplies
the shift by `GENERATOR`; `split_domains` by `h^i`; and `from_ext_basis_coefficients` is a lane
shift with the overflow folded back by `W = 11`, **not** four extension multiplies. Dropping the
chunk shift must move the Lagrange weights, and the leg fails if it does not. The closing equality
accepts a constructed honest instance and refuses a chunk one lane off, the two chunks swapped, and
— the whole point of the rung — **a constraint one element off**.

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
~11,000 permutations  ×  2,600.5 rows  =  ~2.86 × 10^7 rows      [§3.8, MEASURED]
2.86 × 10^7 / 48,000 usable            =  ~600 work-carrying step circuits
+ a binary aggregation tree over them  =  ~650–1,040 Pickles steps total
```

Only 25 permutations fit in one 2^16 step (`floor(65,536 / 2,600.5)`), and ~18 after the Pickles
recursive-verifier overhead of §4.1 — a useful sanity handle: **one FRI query alone (471
permutations) is ~26 steps.**

The remaining spread is now entirely the permutation count, not the row price:

| perms/root-verify | total rows | Pickles steps (55k / 48k usable) |
|---|---:|---:|
| 10,250 (§2.2, structural) | 2.67 × 10^7 | 485–556 work-carrying |
| **11,000 (§2.1, measured)** | **2.86 × 10^7** | **521–596 work-carrying** |
| 13,000 (§2.1, top of range) | 3.38 × 10^7 | 615–705 work-carrying |

*(Previously this section read `~2,000 rows ⇒ ~2.2 × 10^7 ⇒ ~500–800 steps`, with a §3.7
pessimistic band of ~1,900–2,800 steps. The measurement lands 1.30× above the optimistic figure
and 3.2× below the pessimistic one; the pessimistic branch is retired.)*

### 4.3 It does split cleanly, which is what keeps this "huge" and not "blocked"

*Recomputed at the measured 2,600.5 rows/permutation (§3.8); the shape is unchanged, every
count is 1.30× its previous value.*

1. **One transcript step** replays the Fiat–Shamir challenger and emits the 19 query indices, the
   16 fold challenges `β_i`, `ζ`, and `α` as a Poseidon-committed public output (~1,300
   permutations ⇒ ~3.4 × 10^6 rows ⇒ **~71 steps**).
   ⚑ **§3.12's 62,637 rows do NOT replace this figure — they are its FRI-only tail.** The 23
   permutations §3.12 measures cover `verify_fri`'s own schedule (`alpha`, the 16 commitments and
   `beta`s, the final poly, the arity tags, the query PoW, the 19 indices). The ~1,300 here is the
   WHOLE batch-STARK transcript, and ~1,171 of it is the single `observe_algebra_slice` over every
   opened value at ζ (§2.3) — a 940-column term that no FRI knob touches. Binding §3.12's preamble
   to that absorb is precisely the residual §3.14 lists first.
2. **19 independent per-query chains** (one query ≈ 471 permutations ≈ 1.22 × 10^6 rows ⇒ **~26
   steps each**, ~494 steps total), each consuming the committed challenge digest.
3. **A binary aggregation tree** (Pickles steps take up to 2 previous proofs), ~another 500 steps
   whose *only* content is the recursive verification.
4. **One final chain** for the reduced-opening arithmetic and AIR constraint evaluation at ζ —
   **~3.5%** of the work at the measured 49 rows/Horner step (§3.14, correcting §2.4's ~7)
   ⇒ **~20–25 steps**, not ~13.

Each step is a real Pickles proof at 10–30 s, so **~650–1,040 steps ≈ 3–9 hours of Mina-side
proving per dregg root verified**, parallel across the 19 query chains, sequential up the tree.

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

Turning the first three lands around **~5,500–6,500 permutations ⇒ ~1.6 × 10^7 rows ⇒ ~325–455
steps** at the measured 2,600.5 rows/permutation (§3.8).

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
the folded commit phase (~600) ⇒ **~5,900 permutations ⇒ ~1.5 × 10^7 rows ⇒ ~260 steps** at the
measured 2,600.5 rows/permutation (§3.8).

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

- **Blocked?** **No.** Nothing here is unbuildable — and as of §3.8 one permutation of it has been
  compiled, proved and verified on Mina's own proof system.
- **A handful of step circuits?** **No.** **~650–1,040** at deployed parameters; **~325–455** after
  the dregg-side FRI knobs; **~260** is the floor short of narrowing the root's trace or adding a
  Mina-targeted shrink layer. (The ~1,900–2,800 pessimistic branch is **retired** — §3.8 measured
  the gadget at 3.2× cheaper than the gnark-emulation parity that generated it.)
- **Honest row budget:** **~2.9 × 10^7 Kimchi rows**, ~98% of it Poseidon2-w16-BabyBear.
- **Single biggest cost driver:** the **mod-`p` reduction and its range checks** — **measured at
  ~64%** of the per-permutation rows (§3.8), because the S-box is a *multiplication chain* and lazy
  reduction cannot amortise across it. *Not* the S-boxes (564 multiplications is nothing), *not*
  the FRI logic, *not* the AIR evaluation — but see the correction below: the **DEEP quotient** is
  2.94 × 10⁶ rows and the **observes** are 2.97 × 10⁶, so "the arithmetic residual" is ~20% of the
  budget, not the ~3.5% §3.14 first recorded.
- **Second driver:** `max_log_arity = 1` and `cap_height = 0`. Together ~2.5×, against a
  configuration available today that costs **3 bits on a column that is not the binding one**.
- **What the budget buys:** ~50 bits of ledger reading, commit-column-bound, with **queries
  provably unable to move it**.

**The two things worth doing before building any of this, in order — and neither is Mina-side:**

1. ~~**Measure the gadget.**~~ **DONE, 2026-07-28 — §3.8.** `bridge/mina-zkapp/src/Poseidon2BabyBearW16.ts`,
   **2,600.5 rows/permutation**, KAT-checked against the deployed hash and Pickles-provable. The 4×
   band is closed: **~2.9 × 10^7 rows**, i.e. "ambitious", not "no". It cost an afternoon, as
   predicted, and the estimate it replaces was 30% low.
2. **Turn the dregg-side knobs and measure a real root.** Flip `max_log_arity` to 3, set
   `cap_height`, and — **still the number the most rests on** — **read a root proof's
   `degree_bits`**, which §1.3 shows nobody ever has. Since 2026-07-28 there is a second uncounted
   number beside it: **`N`, the constraint count across the root's seven AIRs** (§3.16), which is a
   `get_symbolic_constraints` call away and which nothing in this budget can price without. §5.2's open contradiction (is there a live
   W24 table in the root or not?) is worth ~10% on its own. Then decide whether a **Mina-targeted
   shrink layer** is the right final stage, exactly as `dregg_outer_config.rs` is for BN254.

---

## 9. Scorecard

| Claim | Resolution |
|---|---|
| Kimchi can verify dregg's FRI-STARK **directly**, no Groth16 wrap | **Yes in principle** — field + hash only, every primitive exists. Unlike the pairing route, nothing is missing. |
| BabyBear fits natively in Pasta ⇒ cheap | **Half true.** It fits (no `ForeignField`), which is why the route exists. It is **not** cheap: reduction + range checks are **measured at ~64%** of the rows (§3.8). |
| Kimchi's Poseidon gate can be reused | **No.** Structurally width-3 Pasta (`&'static [[F;3];3]` MDS, `COLUMNS/SPONGE_WIDTH` layout). A new gate is a **Mina hard fork**, not an app change. |
| Permutation count | **~11,000 — measured in-tree**, independently re-derived here at ~10,250. |
| Rows per permutation | **2,600.5 — MEASURED** (§3.8), on an o1js circuit that compiles, proves, verifies and reproduces the deployed permutation's Lean-pinned KAT. 1.30× the ~2,000 design claim; 3.2× cheaper than the ~8,400 gnark-emulation parity. **Band closed.** |
| Total | **~2.9 × 10^7 rows** (2.7–3.4 × 10^7; the spread is now the permutation count alone). |
| Fits in one circuit | **No** — ~440× the 2^16 ceiling (**25 permutations per step**), and **Pickles hard-rejects chunking** (`verify.ml:61-76`). |
| N step circuits | **~650–1,040** deployed; **~325–455** knobbed; **~260** floor. |
| It buys 128 bits | **No — ~50**, commit-column-bound, and `numQueries` provably cannot move it. |
| The AIR evaluation is the expensive part | **Still no, but the surrounding arithmetic is bigger than claimed.** §3.15 measures the DEEP quotient at 2.94 × 10⁶ rows over 19 queries and §3.16 the observes at 2.97 × 10⁶ — together ~20% of the budget, where §3.14 first recorded ~3.5% for DEEP *and* AIR. The AIR **fold** itself is `A + N·h` = 14,175 + N × 48 and remains small; `C_i` and `N` are uncounted. It is still mostly a hashing problem. |
| The DEEP quotient / reduced opening is bound to the trace | **Yes as of §3.15.** The reduced openings are computed from the MMCS-opened rows, the absorbed `f(ζ)` and the transcript's `alpha`, KAT'd against `p3_fri::verifier::open_input`. The gate **proves a witness the previous statement admits and requires the new one to refuse it**, so the closure is exhibited, not asserted. |
| The AIR constraint evaluation is started | **Partly, §3.16.** The selectors, the α-fold, the chunk recomposition and the closing equality are built and KAT'd against p3's own domain algebra at four `degree_bits`. **`C_i` — dregg's seven AIRs — is not built and `N` is not counted.** Until it is, the FRI walk authenticates a low-degree function that encodes nothing in particular. |
| A custom `Poseidon2BabyBear` Kimchi gate would buy ~2× | **No — ~1.5×.** §3.11 guessed ~900–1,100 rows/perm; the measured split (§3.8) puts the reductions a custom gate CANNOT remove at ~1,700 rows. Still a Mina hard fork. |
| The row price is a design claim nobody has run | **No longer.** §3.8–3.14 are measured, the circuits are committed under `bridge/mina-zkapp/src/`, and `scripts/check-mina-attestation.sh` fails if any of nine figures drifts >2%. |
| `degree_bits = [9,9,15,14,15]` describes the root | **No** — that is the BN254 **shrink** proof. The root's own heights are **unmeasured**, and §3.14 shows how much rests on that. |
| The FRI walk these circuits perform is *the prover's* | **Yes as of §3.12–3.13b at the fold chain, and as of §3.15 at the value it starts from.** The query index and every `beta` are DERIVED from a `DuplexChallenger` transcript KAT'd against the deployed one, the 16-bit query PoW is checked, one program joins the derivation to the walk, and the reduced opening is now COMPUTED from the opened rows rather than witnessed. **Not yet** for the input-phase opening over MIXED matrix heights (one matrix per batch is built), nor for the batch-STARK preamble the transcript starts from. |
| The challenger is a rounding error next to the query walk | **Yes — 0.48%, measured (§3.12).** Which is the point: the binding was cheap and was simply absent. |
| The DEEP/AIR arithmetic is ~1.5–2% | **No — ≈3.5%.** §2.4 priced a Horner step at ~7 rows; it is **49, measured** (§3.14). Still not the driver. |
| A both-polarity, deterministic check of a step implies the chain is right | **No, and this cost a day.** The single-round coset-descent check was made deterministic and both-polarity on 07-27 and stayed green while the CHAIN descended on the wrong index bit — right on ~half of any chain's rounds and on 100% of the all-zero index every row measurement uses. **Composition needs its own referent** (§3.13). |

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
`kimchi_backend/common/plonk_constraint_system.ml`, **o1js 2.15.0 gadgets** (the §3.8 measurement;
§3.3/§3.5 read o1js 1.9.1 sources — and ⚑ two of their *row prices* are wrong, measured marginally
on 2.15.0: `rangeCheck32` costs **2 rows**, not ~1, and `rangeCheckN(192)` costs **13**, not ~5.
The cheap bulk checks are `rangeCheck64` at **1 row/64 bits**, `multiRangeCheck` at **4 rows/264
bits**, and `rangeCheck3x12` at **1 row/36 bits** — ~66 bits/row is the ceiling, and §3.8's circuit
uses those. §3.5's "lookups are a precondition, not an optimisation" stands.)
o1js circuits + measurement, all run by `scripts/check-mina-attestation.sh`:
`bridge/mina-zkapp/src/Poseidon2BabyBearW16.ts` (§3.8), `src/Poseidon2Merkle.ts` (§3.9),
`src/FriQueryStep.ts` (§3.10, §3.13), `src/FriChallenger.ts` (§3.12, §3.13b), with
`scripts/{poseidon2-babybear-rows,poseidon2-merkle-rows,fri-query-rows,fri-challenger-rows,fri-chain-rows}.ts`.
The deployed-object referents are `circuit-prove/sketches/mina-pasta-hash-probe`'s `p2merkle`
(the MMCS), `p2fold` (one fold), `p2chain` (the whole 16-round chain), `p2chal` and
`p2fritranscript` (`p3_challenger::DuplexChallenger` and the `verify_fri` schedule) — every one of
them calling the p3 types at rev `82cfad73`, never a transcription.

**Companion:** `docs/MINA-DREGG-ZKAPP-BRIDGE.md` — this document answers its §5 "Route A" with a
budget, and does not disturb its Groth16 verdict.
