# Can a Kimchi circuit verify dregg's FRI-STARK *directly*? — the size question

> ⚠ **CITATION CONVENTION.** The measurement scripts live at `bridge/mina-zkapp/scripts/*.ts` and
> must be cited with that full prefix. Dropping it and writing them bare — natural, since this
> document is *about* the zkapp — resolves against the repo ROOT, where no such directory exists, and
> `check-doc-refs` then refuses the push for everyone. This has now happened three times in this file.
>
> (Yes: the first draft of this very note spelled out the bad form as an example, and the checker
> refused *that* — correctly. A path in backticks is a citation no matter what the surrounding prose
> says about it.)


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

⚑ **AS OF §3.22–§3.25 (2026-07-29) THE HEADLINE NUMBERS ARE EMITTED, NOT PROJECTED.** The row
budget is **2.46 × 10⁷** measured per atom, the deployed step count is **519** (448 at
`max_proofs_verified = 1`) scheduled over that emitted list, and the AIR term in it is the root's
own **1,093** constraints rather than the fixture's four. The root's constraint system is
**275,143 rows — 4.20× a Pickles step**, so it has no one-step verifier; three chained steps over it
are proved. And it now runs on **dregg's committed root proof**: all seven instances' closing
equalities checked as Kimchi constraints, with one instance (`expose_claim`, `degree_bits = 0`)
measured **not to bind ζ at all**.

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
| Kimchi rows for ONE STEP BOUNDARY at deployed geometry | **34,566 — MEASURED** under a FLAT `rootCommitDigest`; **1,402 — MEASURED** under the chunked one | **§3.20** — 9,103 + 95 carried lanes, linear at 3.75 rows/lane, **69.8% of an aggregation-tree step**. **§3.21** — a step that re-binds only the chunks it READS pays 24.6× less, and §3.21's probe reproduces §3.20's flat figure to 0.03% |
| **Pickles step circuits** | **591 work-carrying — SCHEDULED** (504 at `max_proofs_verified = 1`) | **§3.21** — a dynamic program over 27,590 atoms and the measured carry. ⚑ §4.2's ~650–1,040 subtracts no carry at all; §3.20 measured one and got a band of **564–1,838**; §3.21 places the cuts and the band collapses |
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
than 2%, on top of KATs against the deployed p3 objects and **83 fault injections** with a
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

⚑ **AND AS OF §3.20 THE STEP COUNT IS A MECHANISM.** §3.19 fits one step; §4 divides a projected row
count by a per-step budget and calls the quotient "~573 steps". Nobody had ever fed one step's
output to the next. §3.20 takes a dregg proof with **no one-step verifier** — 103,554 rows, 1.58× the
domain — and verifies it with **four chained Pickles steps from TWO verification keys**, carrying one
field element per boundary, with **eight splice attempts refused against real proof objects** and a
control for each. The boundary is priced: **1.09% at the fixture's geometry, 34,566 rows (69.8% of a
step) at a deployed query entry, 762 rows inside a query.** The deployed count was therefore left as
a **band, 564–1,838**, and where it lands is a scheduling decision, not a division.

⚑ **AND AS OF §3.21 THAT DECISION IS TAKEN: 591 STEPS.** The scheduler is a dynamic program over
27,590 atoms and §3.20's measured carry, and it collapses the band to **591 work-carrying steps at
`max_proofs_verified = 2`** — 27 above the optimistic end, **1,247 below the pessimistic one** — with
**521 of its 590 boundaries landing inside a query and 2 at a query entry**. The 3.3× decomposes:
placement is 1.66× of it, and the other 2.00× is a change to the COMMITMENT — `rootCommitDigest`
becomes the Poseidon hash of a **vector of chunk digests**, so a step re-witnesses only the chunks it
reads and a fold chain stops paying for 8,920 lanes of opened evaluations it never looks at. And it
is **proved, not computed**: a query is two chained steps cut at the DEEP/fold seam, seven steps from
one verification key, nine splices refused with a control that builds its own predecessor.

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
  `fri_trace_height_measure.rs:55`. `[10,9,16,14,16]` is the **leaf-wrap** 5-table proof
  (`fri_trace_height_measure.rs:145`). Neither is the root.

⚑ **THE ROOT'S OWN `degree_bits`, READ 2026-07-28 — `[10, 10, 16, 15, 3, 16, 0]`.** This paragraph
previously said no committed measurement existed. It was sitting in three committed artifacts all
along: the `root_proof` blob of `ugc-dregg/tests/fixtures/whole_history_proof.bin` (and the same
fold in `site/light-client/history.json`, `site/dist/light-client/history.json`,
`portal/dist/history.json`), a 3-turn `prove_turn_chain_recursive` root under VK `434f57d2…`.
`degree_bits` is the last field of `p3_batch_stark::BatchProof` (`batch-stark/src/proof.rs:23`,
built at `prover.rs:668`), reachable as `WholeChainProof.root.0.proof.degree_bits`.

| i | table | `degree_bits` | padded rows | logical rows |
|---|---|---:|---:|---|
| 0 | Const | 10 | 1,024 | 529 |
| 1 | Public | 10 | 1,024 | 534 |
| 2 | Alu | **16** | 65,536 | 142,589 ops / 4 lanes |
| 3 | poseidon2-W16 | 15 | 32,768 | 32,768 |
| 4 | poseidon2-W24 | 3 | 8 | 8 |
| 5 | recompose | **16** | 65,536 | 41,353 |
| 6 | expose_claim | 0 | 1 | 25 claims / 25 lanes |

Cross-checked inside the same blob: the trailing `stark_common.preprocessed.instances` carry
`(matrix_index, prep_width, degree_bits)` with prep widths `[2,2,59,24,36,2,50]` — **exactly §1.3's
per-table preprocessed column census**, which independently pins the table→index mapping. The same
blob decodes `table_packing = {public_lanes 1, alu_lanes 4, npo_lanes [], min_trace_height 1,
horner_packed_steps 2}` and `ext_degree 4`.

⚑ **AND IT CORRECTS THE PARAGRAPH BELOW.** `max = 16`, so `|D⁰| = 2^(16+6) = 2^22` and
**(22 − 6)/1 = 16 commit-phase layers — on the `prove_chain_core_rotated` path too.** The claim that
that producer has "natural heights, max ≈ 2^15, |D⁰| ≈ 2^21, 15 layers" and that "the counts differ
by ~5%" is **wrong**: the ≈2^15 was itself inherited from the shrink's `[9,9,15,14,15]`. The two
root producers do not differ in FRI depth at all, and `WRAP_LOG_CEIL = 16` is a no-op on `|D⁰|`
here — it still pads the five short tables up to 2^16, which is prover cost, not FRI depth. Under
the floor the accumulator root's vector would be `[16,16,16,16,16,16,16]`; that root is an AGG∘LEAF
circuit, so its *natural* heights remain unmeasured.

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
| **AIR constraint evaluation, ONCE per verify** | `A + N·h` = 14,175 + **1,093** × 48 = 66,639, plus `C_i` **MEASURED through the DAG source language at 187,295** (§3.18) | **≈ 2.5 × 10⁵** |
| commit phase × 19 queries | 623,310 × 19 | **1.18 × 10⁷** |
| transcript (FRI schedule only) | measured | **6.3 × 10⁴** |
| **whole root verify** | sum | **≈ 3.0 × 10⁷** — and the independent permutation count in §0 says 2.9 × 10⁷ |

**STILL UNCOUNTED — and these are counts, not prices**

1. ~~**The root's own `degree_bits`.**~~ **CLOSED 2026-07-28 — §1.2.** `[10, 10, 16, 15, 3, 16, 0]`,
   read out of the committed `whole_history_proof.bin` root blob and cross-checked against the
   preprocessed instance metas. `max = 16` ⇒ `|D⁰| = 2^22` ⇒ **16 commit-phase layers**, which is
   what "4 rounds all at depth 22" rested on and it holds. It also **settles §5.2**: the W24 table
   is live and present, at `degree_bits = 3` — eight rows, so its ~10% worry was a worry about a
   table that costs almost nothing in FRI depth while costing its full 452 columns in the DEEP
   quotient and the observe.
2. ~~**The roll-in schedule.**~~ **CLOSED as a schedule, 2026-07-28 (§3.15d).** It was never a free
   parameter: the opening at height `L` rolls in after round `LGMH − 1 − L`, the opening at `LGMH`
   is `initial`, and `verify_query` refuses any other first height. `rollInSchedule` computes it and
   the circuit uses it. What remains is the *set of heights*, which is (1).
3. **The input row widths.** §3.10 measures an 8-element input row (one sponge block). The real main
   round is 940 columns ⇒ 118 blocks. That is in the derivation above, not in the 684,726.

**STILL OPEN AS SOUNDNESS, not as size**

1. ~~**The preamble binding.**~~ **CLOSED 2026-07-30 — §3.29.** §3.12's transcript started from a
   **13-lane stand-in** for the batch-STARK's own observes, so the derivation was "the challenges
   given this state" and not "the challenges"; §3.28 carried the same hole at real geometry, as a
   committed witness. The real sequence now runs in circuit — `observe_instance_count`, the seven
   per-instance bindings, all four commitments **in the transcript's own order, which is not the PCS
   round order**, the 25 public values, the 64 cumulative sums, `α_stark`, `ζ` and all **2,630**
   opened values — and the derived `ζ` is asserted to BE the point all 35 committed matrices were
   opened at. ⚑ **The size estimate on this row was low.** 1,373 permutations and **3,575,411
   rows**, not the 1,143 / 2.97 × 10⁶ derived here from the superseded 2,286-value census; §3.28's
   correction to 2,630 is what moves it. It is a size term of the same order as the DEEP quotient,
   exactly as this row said.
2. ~~**The DEEP quotient.**~~ **CLOSED 2026-07-28 — §3.15.** The reduced openings are now COMPUTED
   from the MMCS-opened rows, the absorbed claimed evaluations and the transcript's `alpha`.
   `makeDeepBoundQueryProgram` keeps the pre-3.15 statement compiled beside it and the gate
   **proves a witness the old statement admits and the new one refuses**, so the closure is
   exhibited rather than asserted.
3. **The AIR constraint evaluation** at ζ. **NARROWED FURTHER — §3.16 + §3.17 + §3.18.** The
   protocol arithmetic around `C_i` is built and KAT'd at four `degree_bits` (§3.16). **`N = 1,093`
   is measured**, and with the DAG source language **`C_i` is now a compiler output for ALL 901 of
   the base constraints** — 8,698 nodes, 2,433 multiplies, 187,295 rows, 0.85% of this budget —
   with `dagFold_forces` proving the emitted Kimchi rows force p3's accumulator and
   `dagDenote_unfold` proving the sharing sound (§3.18). What remains: **the 192 LogUp constraints
   are still not in this vocabulary** (the extension they need is named in §3.18); the extraction
   is still a differentially-checked SEAM, not a theorem; and the Lean accumulator is not welded to
   `AirEval.ts`'s closing equality. **Until those close, the walk still authenticates a low-degree
   function whose encoding is only partly pinned.**
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

---

### 3.17 ⚑ MEASURED — `N = 1093`, and `C_i` GENERATED

*2026-07-28. `circuit-prove/tests/root_air_constraint_census.rs` (the census + the `Head`
extractor) and `metatheory/Dregg2/Circuit/Emit/KimchiRootAirEval.lean` (the generator + its
soundness theorem).*

> ## **`N` = 1,093. It was never uncountable — `p3_batch_stark::symbolic::get_symbolic_constraints` returns the list and `RecursiveAir::eval_folded_circuit` folds exactly `base.len() + ext.len()` of them. And `C_i` is now a COMPILER OUTPUT for two of the seven tables, with the lowering proved to force p3's accumulator.**

**The census.** Every AIR is built at the deployed shape — `TablePacking::new(1, 4)` from
`ProveNextLayerParams::default()`, `horner_packed_steps = 2`, `W = 11`, `recompose` at
`lanes = 1, coeff_lookups = false`, `expose_claim` at 25 claims — and run through
`get_symbolic_constraints` with `LogUpGadget`.

| table | main | prep | base | ext | lookups | **N** |
|---|---:|---:|---:|---:|---:|---:|
| Const | 4 | 2 | **0** | 3 | 1 | 3 |
| Public | 4 | 2 | **0** | 3 | 1 | 3 |
| Alu | 76 | 59 | 92 | 54 | 18 | 146 |
| poseidon2-W16 | 300 | 24 | 316 | 21 | 7 | 337 |
| poseidon2-W24 | 452 | 36 | 468 | 33 | 11 | 501 |
| recompose | 4 | 2 | **0** | 3 | 1 | 3 |
| expose_claim | 100 | 50 | 25 | 75 | 25 | 100 |
| **Σ** | **940** | **175** | **901** | **192** | | **1,093** |

Two independent confirmations that these are the DEPLOYED AIRs and not a plausible reconstruction:
the column totals are §1.3's 940/175, and the per-table preprocessed widths `[2,2,59,24,36,2,50]`
are byte-for-byte the ones in the real serialized root proof (§1.2). `N ≈ 0.98 ×` the column count,
so §3.16's "1,115 (1 × columns)" row was almost exactly right by accident.

⚑ **Three of the seven tables have ZERO base constraints.** `Const`, `Public` and `recompose` are
pure lookup tables — `ConstAir::eval` pushes one `WitnessChecks` interaction and asserts nothing. So
192 of the 1,093 are LogUp permutation constraints over the CHALLENGE extension, and for those three
tables they are *all* of it.

⚑ **The count is a property of the AIR, not of the fixture** — asserted, not assumed. `ConstAir` and
`AluAir` both take a row parameter, so a reading at one row-count is indistinguishable from a
reading of a function of it. `constraint_count_does_not_depend_on_row_count` sweeps
`{16, 256, 4096, 65536, 1048576}` and refuses on any movement. What DOES move it is the ALU packing,
and that is measured too: `N_alu` = 50 / 82 / **146** / 274 at `alu_lanes` = 1 / 2 / **4** / 8.

**The price, re-measured.** `A + N·h` = 14,175 + 1,093 × 48 = **66,639 rows** for the fold —
still not `C_i`.

**`C_i` itself, and the finding that matters.** All 901 base constraints ARE expressible as
`AirBuilder.Head` (`Σ coeff·∏cols + const`) — measured by attempting the flat expansion on every
one. But `Head` is FLAT and p3's `SymbolicExpression` is an `Arc`-SHARED DAG, and flattening
destroys the sharing:

| table | base | DAG multiplies | flat-`Head` multiplies | ratio |
|---|---:|---:|---:|---:|
| Alu | 92 | 356 | 1,304 | 3.7× |
| poseidon2-W16 | 316 | 958 | 243,849 | **254×** |
| poseidon2-W24 | 468 | 1,598 | 1,284,686 | **804×** |
| expose_claim | 25 | 25 | 50 | 2.0× |
| Const / Public / recompose | 0 | 0 | 0 | — |
| **Σ** | **901** | **2,937** | **1,529,889** | **521×** |

At the measured 31 rows per extension multiply (§3.14), that is **≈9.1 × 10⁴ rows** through a
sharing-preserving lowering against **≈4.7 × 10⁷** through the flat one. The flat form ALONE exceeds
§3.14's whole-verifier ≈3.0 × 10⁷. So the honest statement is not "the compiler cannot express the
Poseidon2 tables" — it can, and must not. **The compiler's next rung is a DAG-shaped source language
with a common-subexpression cache**, which is exactly what p3's own `SymbolicCompiler::compile_base`
does (`recursion/src/traits/air.rs:150-156`, `base_cache`), and its lowering theorem is the same
shape as the one below, one `Gen1` per DAG node.

**⇒ the AIR side, done right: ≈ 6.7 × 10⁴ (fold) + ≈ 9.1 × 10⁴ (`C_i`) ≈ 1.6 × 10⁵ rows, ONCE per
verify** — `verify_constraints_with_lookups` runs per instance per proof, not per query. That is
**~0.5% of the ≈3.0 × 10⁷ total**, not the ≈3.5% §3.16 hedged at. The AIR side is not the budget
problem; getting the lowering's source language wrong would have been.

**What was GENERATED, and what is proved.** `KimchiRootAirEval.lean` compiles a `List Head` to
Kimchi rows through `packGen`, and `airFold_forces` proves, at an arbitrary `CommRing`, that any
assignment satisfying the emitted rows puts p3's accumulator `fold_i (acc·α + C_i)` in the output
variable — the object `verify_constraints_with_lookups` compares against `quotient(ζ)·Z_H(ζ)`. Two
tables are generated end-to-end from extractor output with no hand-written constraint:

| table | constraints | sub-gates | packed rows | extension multiplies |
|---|---:|---:|---:|---:|
| `expose_claim` | 25 | 176 | **88** | 75 |
| `Alu` | 92 | 2,359 | **1,180** | 1,396 |

with the row counts as a *theorem* (`airFoldRows_length`) rather than a measurement, and a `#guard`
that runs the emitted straight-line program at a non-degenerate seeding, checks every sub-gate, and
compares the output variable against an independent evaluation of the same heads.

⚑ **A DEFECT IN THE RUNG BELOW IT, FOUND BY USING IT.** `KimchiLower`'s header scopes `lowerHead` as
"precisely the verifier's `AIR.evalAtZeta` rung". Its body ends in `Gen1.isZero` — the emitted rows
assert the head **VANISHES**. At ζ that is FALSE for an honest proof: the constraints vanish on `H`,
ζ is sampled outside `H` precisely so they do not, and `Q = (Σ αⁱ Cᵢ)/Z_H` is only meaningful
because `Cᵢ(ζ) ≠ 0`. A verifier built on `lowerHead` as scoped would have been **unsatisfiable on
every honest proof**, and would have looked right, because `lowerHead_sound` is a true theorem about
it. §1 of the new file supplies the value-producing lowering; its forcing lemma is `lowerAcc_forces`,
already proved. The fix was three lines. Noticing that a constraint-GATE lowering and a
constraint-EVALUATION lowering are different objects was the whole of it.

⚑ **AND THE α-FOLD IS OFF BY ONE IN `AirEval.ts`.** `foldConstraints` seeds with `constraints[0]`
and pays `N − 1` folds; p3 seeds with ZERO and pays `N` (`recursion/src/traits/air.rs:148`). §3.16
corrected for it by subtracting one marginal price; the generated fold matches p3 structurally.

**What this does NOT close.** The extraction `SymbolicExpression → Head` is a Rust-side SEAM, checked
by a differential over all 901 base constraints at pseudorandom assignments — a confession, not a
mitigation. The 192 LogUp constraints are not in this vocabulary at all. The closing equality is
still `AirEval.ts`'s, and nothing states the Lean half and the TypeScript half compose. Everything is
in EXTENSION-element currency; the lowering to Pasta lanes interleaves `RangeCheck0` rows, for which
`KimchiLower`'s `renderOps_gens_sound` is named and unproved. **The verifier is not sound because
`C_i` landed.**

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

### 3.18 ⚑ MEASURED — the DAG SOURCE LANGUAGE, and all 901 base constraints as compiler output

*§3.17 stopped at 117 of 901 and said exactly why: `Head` is FLAT, p3's constraints are an
`Arc`-shared DAG, and flattening costs 521× in multiplications — enough that the flat form of `C_i`
ALONE exceeds §3.14's whole-verifier budget. The next rung was named there: a DAG-shaped source
language with a common-subexpression cache. It is built.*

`metatheory/Dregg2/Circuit/Emit/KimchiDag.lean`. `Node` is a 1:1 image of `SymbolicExpr` —
`Leaf`/`Add`/`Sub`/`Neg`/`Mul` — with each `Arc` child replaced by the INDEX of the node it became.
The lowering is one `Gen1` per node, node `k` to variable `nv + k`, which is
`SymbolicCompiler::compile_base`'s shape with the `CircuitBuilder` replaced by sub-gates.

**The measurement, over all seven tables** (`dag_source_language_census`):

| table | base | DAG nodes | DAG multiplies | flat-`Head` multiplies | ratio |
|---|---:|---:|---:|---:|---:|
| Alu | 92 | 850 | 356 | 1,304 | 3.7× |
| poseidon2-W16 | 316 | 2,850 | **754** | 243,849 | **323×** |
| poseidon2-W24 | 468 | 4,848 | **1,298** | 1,284,686 | **990×** |
| expose_claim | 25 | 150 | 25 | 50 | 2.0× |
| Const / Public / recompose | 0 | 0 | 0 | 0 | — |
| **Σ** | **901** | **8,698** | **2,433** | **1,529,889** | **629×** |

⚑ **2,433, not §3.17's 2,937.** p3's own cache keys on the raw `Arc` pointer, so two structurally
identical but separately allocated subtrees stay separate; the extractor here interns on
STRUCTURAL identity of the already-numbered node and merges them. The 504-node difference is
entirely in the two Poseidon2 tables.

**THE PRICE, RE-MEASURED — and §3.17's ≈9.1 × 10⁴ was low, because it counted only multiplies.**
The node census is `var 1,063 · cst 377 · add 3,547 · sub 1,249 · neg 29 · mul 2,433`. At §3.14's
measured units (extension multiply 31, extension add/scale 19, a constant pin ≈ 0):

| term | rows |
|---|---:|
| 2,433 multiplies × 31 | 75,423 |
| 4,825 add/sub/neg × 19 | 91,675 |
| 1,063 `.var` copy nodes × 19 (**elidable** — `KimchiDag` §11.2) | 20,197 |
| **`C_i`, all 901 base constraints** | **187,295** |
| the α-fold, `A + N·h`, all 1,093 | 66,639 |
| **the AIR side, whole root** | **≈ 2.5 × 10⁵** |

**⇒ 0.85% of §3.14's ≈3.0 × 10⁷.** The flat form's multiplies ALONE are 47,426,559 rows — **158% of
the whole budget.** So `C_i` is not a budget problem and never had to be; getting the source
language wrong would have made it one, and that is now a `#guard` and two Rust assertions rather
than a paragraph.

**What is PROVED, and it is the same shape as before.** `dagGens_forces`: any assignment satisfying
the emitted rows makes variable `nv + k` hold node `k`'s denotation, for every `k`, at an arbitrary
`CommRing`, over the actual emitted list. `dagFold_forces` puts p3's accumulator in the output
variable. **`dagDenote_unfold` is the sharing statement** — node `k` is lowered to ONE variable and
every parent reads it, and that variable is forced to `evalNode` of `k`'s own children's
denotations, so an `m`-times-shared node is `m` reads of one forced value rather than `m` values a
satisfying assignment could pull apart. `cseGo_denote` goes the other way: a TREE compiled through a
structural-identity cache yields a DAG whose root denotes exactly the tree's value. All
`#assert_axioms`-clean, no `sorry`, no `native_decide`.

**⚑ `dagWf` is a HYPOTHESIS, not a lemma.** Every child index must be strictly below its parent's;
an out-of-order list reads a child that has not been forced and the theorem is FALSE for it. It is
`#guard`ed on all four emitted tables and the Rust emitter refuses to print a DAG that fails it.
Mutation-tested: a forward reference reds three guards.

**THE REGRESSION, and it bites.** The two tables §3.17 already generated are re-emitted through the
new path, and `dagHornerZ` (walks nodes) and `hornerZ` (walks monomials) must agree in the field at
the same seeding. A wf-preserving one-child edit to a single Alu node — same node count, same kinds,
same multiply count, still topologically sorted — is caught by **exactly that guard and no other**.
On the Rust side the same comparison runs at 8 pseudorandom assignments over both tables (936
agreements) and against p3's own evaluation over all 901 constraints of all seven tables (7,208).

**What this does NOT close.** The extraction is still a SEAM — narrower, because `to_dag` renumbers
where `to_head` distributed, but a differential all the same. The **192 LogUp constraints remain
outside the vocabulary**, and the extension they need is named precisely: `SymbolicExpressionExt`'s
leaves are `ExtLeaf::Challenge` (β, γ) and `ExtLeaf::Base` (a lifted base expression), so `Node`
needs `chal (i)`, a permutation-column leaf, and a `lift` embedding a base-DAG index — exactly
`compile_ext`'s shape, sharing the same `base_cache`. The lowering itself needs no change: `Gen1` is
already at arbitrary `CommRing`. Three of the seven tables have ZERO base constraints, so for them
this rung still covers nothing. The closing equality is still `AirEval.ts`'s. The lane currency
still needs `renderOps_gens_sound`. **The verifier is not sound because the DAG language landed.**

---

### 3.19 ⚑ MEASURED — THE ASSEMBLY: one ZkProgram that consumes a dregg proof and DECIDES

*`bridge/mina-zkapp/src/DreggProofVerify.ts`, `bridge/mina-zkapp/scripts/dregg-proof-verify.ts`,
`circuit/src/bin/mina_stark_fixture.rs`. Gate leg 10.*

Everything above §3.19 is a **component**. Each rung verifies a piece of a FRI-STARK proof, each is
KAT'd against the deployed p3 object, and **every one of them is fed a fixture the measurement
synthesised** — an opened row no prover produced, a fold chain over a value nobody committed to, a
transcript whose preamble is a stand-in. Until something consumes a proof, "Mina verifies dregg" is
a statement about a parts list.

**What was built.** `circuit/src/bin/mina_stark_fixture.rs` mints a real proof with
`p3_uni_stark::prove` under `DreggStarkConfig` — the same `Poseidon2BabyBear<16>`, the same
`PaddingFreeSponge<.,16,8,8>` / `TruncatedPermutation<.,2,8,16>` MMCS, the same
`DuplexChallenger<.,16,8>`, the same `BinomialExtensionField<BabyBear,4>`, the same `TwoAdicFriPcs`
the deployed root runs, with only the six FRI knobs turned down — and runs **dregg's own
`p3_uni_stark::verify` before emitting anything**. `DreggProofVerify` then does the whole of that
verifier in one Kimchi circuit:

| | |
|---|---|
| the STARK preamble | `degree_bits`, `base_degree_bits`, `preprocessed_width`, the trace commitment and the public values absorbed; `α` SAMPLED; the quotient commitment absorbed; `ζ` SAMPLED (`uni-stark/src/verifier.rs:361-390`) |
| the opened values | every claimed evaluation absorbed in round order **before** FRI's own `α` (`two_adic_pcs.rs:780-788`) |
| the FRI transcript | `α`, every `β`, the arity schedule, the 16-bit query grind and every query index DERIVED |
| **the AIR closing equality** | `Σ αⁱ C_i · Z_H(ζ)⁻¹ == quotient(ζ)`, the three Lagrange selectors computed, the quotient recomposed from **2 chunks** by Lagrange over p3's own chunk domains |
| per query | the input-phase MMCS openings under the commitments the transcript absorbed, the **DEEP quotient**, and the fold chain onto the final polynomial |

**It proves.** At `degree_bits = 1`, `log_blowup = 1`, 1 query, 1 fold layer, `|D⁰| = 2²`,
`query_pow_bits = 16` (the deployed value):

| | |
|---|---:|
| **rows** | **56,927** (86.9% of the 2^16 step domain) |
| compile | ~28 s |
| **prove** | **~12 s** |
| verify | ~0.3 s |
| the PROVEN public output | the DERIVED query index — **equal to the one p3's own challenger drew** |

**The ceiling is real and was found, not assumed.** The same program at `degree_bits = 2` is
**73,259 rows** and `compile()` aborts inside kimchi's wasm (`RuntimeError: unreachable`). 56,927 is
therefore the largest end-to-end dregg-proof verifier that exists as a single Pickles step today.

**It discriminates, as real `prove()` refusals.** Seven bends, each applied to the same proof
structure and each **required to be refused by dregg's own verifier before it is emitted** — a
fault injection that no longer matches its target silently becomes a passing test:

a claimed out-of-domain evaluation · a quotient chunk · the final polynomial · a commit-phase
sibling · an input-phase opened row element · an input-phase Merkle sibling · the query PoW witness.

**And the AIR closing equality is shown REFUSING.** §3.16 built the arithmetic around `C_i` and
could not watch it bite, because nothing fed it a proof. Here the proof, the transcript, the
openings and the whole fold chain are IDENTICAL and only the constraint evaluator moves: an AIR
reading `a²` where dregg proved `a³` is **refused**, and the control — the same proof under the
PCS-only statement with no AIR check — is **accepted**. The refusal is attributable.

**⚑ A falsifier that a single geometry cannot see, and it is an identity.** The fold-order
falsifier (swap `C₁` and `C₃`) is **blind at `degree_bits = 1`** and the leg says so and proves why:
on a two-row trace `is_first_row = X+1` and `is_last_row = X−1`, so both boundary constraints are
the *same* multiple of `X²−1` and permuting them cannot change the accumulator. Every falsifier is
therefore run at `degree_bits = 2` as well, and the blindness is asserted as an identity rather than
left as an unexplained green — the same discipline §3.15c applied to `open_input`'s conventions and
§3.15e applied to the challenger's `observe`.

**⚑ And one instrument defect this found in itself.** The transcript-polarity check originally bent
four absorbed positions and compared `{ζ, α_FRI, indices}`. That comparison **cannot see a bend in
the last absorbed element** — the query PoW witness — because `ζ` and `α_FRI` are sampled before it
and the index is only `log_global_max_height` bits wide (2 here): a one-in-four coin flip, and it
came up green-then-red across runs. The comparison now includes the grind's own verdict and bends
one element of each of **eight named transcript regions**.

**The marginals, measured.**

| | rows |
|---|---:|
| per additional query (at the proved geometry) | 23,314 |
| per additional fold layer + Merkle level | 16,332 |
| per additional opened trace column — **absorbed once** | 2,705 |
| per additional opened trace column — **per query** (its DEEP term + MMCS lane) | 481 |
| deriving the whole transcript (vs witnessing every challenge) | **32,430 — 57% of the program** |

That last row is the §3.15e evidence: a derived variable is indistinguishable from a witness
carrying its value to `runAndCheck`, to `prove` AND to `getRows()`, so a **row delta against a twin
that witnesses them** is the only instrument that can see the difference. It is 32,430 rows.

**The distance to deployed geometry — measured, then projected from measured marginals.**

| | rows |
|---|---:|
| ONE query at the deployed FRI geometry (`\|D⁰\| = 2²²`, 16 arity-2 layers, `log_blowup 6`, depth-22 input paths), carrying the fixture AIR | **827,887** — 12.6× a 2^16 step |
| the same, challenges witnessed and no AIR check — i.e. the query WALK alone | 748,438 |
| ⇒ transcript + AIR arithmetic at deployed geometry | 79,449 |
| ⇒ 19 query walks | 14,220,322 |
| ⇒ + 1,112 more opened columns (940 main + 175 preprocessed − the fixture's 3) | 13,163,370 |
| **⇒ the deployed root** | **≈ 2.75 × 10⁷ rows, 500–573 Pickles steps** |

⚑ **TWO queries at the deployed geometry does not build**: `analyzeMethods` on the ~1.7 M-row
circuit aborts in kimchi's **wasm** allocator (32-bit address space), not the node heap. So the
fixed/per-query split is taken from a witnessed-challenge, AIR-free twin at one query — both halves
measured, neither subtracted from a guess.

⚑ **2.75 × 10⁷ is a FLOOR, and 500–573 steps is a floor.** The AIR term inside it is the fixture's
**four** constraints, not the root's **1,093** (§3.17) plus the 187,295 rows of `C_i` (§3.18); and
the projection prices the extra columns at the fixture's per-column marginal, which does not include
the root's mixed-height input batches (§3.14 residual 5). The independent §3.14 sum reads
≈ 3.0 × 10⁷ from an entirely different decomposition, and §0's permutation count reads 2.9 × 10⁷.
**Three methods now land within 10% of each other.**

**What §3.19 closes, and what it does not.**

* **CLOSES: "nothing consumes a proof."** A proof dregg's prover made is decided by one Pickles
  step, and the discrimination is seven real `prove()` refusals plus three wrong AIRs.
* **CLOSES, at the uni-STARK shape: §3.14's preamble residual.** The transcript here is not a
  13-lane stand-in — it is `uni-stark/src/verifier.rs`'s own observe sequence and *every* opened
  value. At the **batch**-STARK shape (`observe_instance_count`, per-instance bindings, the
  permutation commitment and the lookup cumulative sums) it is still a stand-in.
* **NARROWS: multi-matrix batches.** The quotient commitment here holds **two** matrices under one
  root, hashed into one leaf. Batches over matrices of **different heights** are still priced and
  not implemented.
* **DOES NOT CLOSE: the AIR is not dregg's.** `MinaFixtureAir` is 3 columns and 4 constraints. The
  root's seven tables at `N = 1,093` are §3.17/§3.18's object; wiring that evaluator into
  `DreggProofVerify`'s `constraints` argument is the remaining seam, and it is an argument, not a
  rewrite.
* **DOES NOT CLOSE: 19 queries and 2²² domains.** The program is parameterised by both and measured
  at both; it does not FIT in one step at either. ⚑ **The PARTITION is no longer on this list —
  §3.20 runs it**, and the step count it produces is not the one §4.2 quotes.

---

### 3.20 ⚑ MEASURED — THE PARTITION: a proof too big for one step, verified by a CHAIN

*`bridge/mina-zkapp/src/DreggProofPartition.ts`, `bridge/mina-zkapp/scripts/partition-chain.ts`,
`metatheory/Dregg2/Circuit/Emit/KimchiPartition.lean`. Gate leg 11.*

§3.19 ends with a row count and §4 divides it by a per-step budget to get ~500–573 Pickles steps.
**That division was an arithmetic over a mechanism nobody had run.** `⌈rows / usable⌉` is a
quotient; a chain is a different kind of object, and every property that makes one — a step's output
feeding the next step's input, both proved, a splice refused, the boundary priced — was untested.
`KimchiPartition` designed the step-boundary contract in Lean and proved the two things a *list*
partition must satisfy (`chunks_concat`, `chunks_fits`); nothing on the Kimchi side had ever emitted
a boundary.

**The geometry was chosen so the chain is not decorative.** §3.19's one-step verifier is the
*largest* dregg proof that happens to fit. The same program at **three queries is 103,554 rows —
1.58× the 2^16 step domain, and past the 73,259 rows at which `compile()` was watched to abort.**
That proof has no one-step verifier at all.

**The contract, as an object.** A work step's public input is ONE field element:

```
boundary_k = Poseidon(rootCommitDigest, challengeDigest, k)
```

`rootCommitDigest` covers the whole shared proof object — commitments, final polynomial, public
values, **every claimed out-of-domain evaluation** and the query PoW witness. The opened evaluations
have to be in it: a later step's DEEP quotient reads them, and a digest that skipped them would let
a step splice openings from another proof while every commitment matched. `challengeDigest` covers
`α`, `ζ`, FRI's `α`, every `β` and **every query index** — the whole transcript, not a step's slice
of it. The per-query MMCS rows and paths are in neither: each belongs to exactly one step and never
crosses.

⚑ **The carrier is Mina-Poseidon over PACKED lanes, and that is a measurement, not a taste.**
Hashing the carried BabyBear lanes with the deployed sponge would cost ~333 rows/lane. Eight 31-bit
lanes pack losslessly into one 254-bit Pasta field and Mina-Poseidon absorbs two of those per
permutation. The boundary is not a dregg object — nothing in dregg reads it, it lives between two
Kimchi steps — so it is not built like one. **Measured: 2,208 rows saved on a 4-step chain, 2.96×.**
The leg requires all 87 single-lane bends to give distinct digests, so the packing is shown
injective rather than argued to be.

**⚑ ONE WALK CIRCUIT, INVOKED N TIMES — not N circuits, and the first version was N circuits.**
Per-step programs work at three steps and do not scale: a verifier would need one VK per step, 573
steps would mean 573 compiles, and — measured — **a node process that has compiled four step
circuits HANGS at the first `prove`** (kimchi's wasm heap is 32-bit; the worker dies and the promise
never settles). So the chain is **two** verification keys: a transcript step, and a walk step
(`first`/`step`) invoked once per query.

A uniform circuit cannot bake in its own position, so the step index `k` and the terminal bit are
**witnesses** — values the prover chooses. Three things pin them together, none sufficient alone:
`first` uses the constant `k = 1`; `step` checks `Poseidon(rcd, cd, k) == publicInput` **and**
`predecessor.publicOutput == publicInput`, while the predecessor emitted `Poseidon(rcd, cd,
k_prev + 1)`, so `k = k_prev + 1` by collision resistance, inductively from 1; and the **closing
seal** carries `k + 1`, which the verifier compares against `nSteps`. Step `k` walks query `k − 1`,
selected from the carried index set by a multiplexer that also asserts `1 ≤ k ≤ num_queries`.
Together those are **`KimchiPartition.chunks_concat` as an in-circuit invariant** rather than a Lean
theorem about a list: every query walked exactly once, none twice, none skipped, and a chain that
dropped one cannot produce the seal.

**Both ends of the chain are verifier-computable, and getting that took a redesign.** An interior
boundary contains `challengeDigest`, which a verifier cannot compute without running the transcript
— which is the work it delegated. So the chain **opens** at `Poseidon(rcd, ⊥, 0)` and **closes** at
`Poseidon(rcd, ⊥, nSteps)`, both computable from the dregg proof alone, and the single external
check is one field comparison against the terminal proof.

**It proves.** At `degree_bits = 1`, `log_blowup = 1`, 3 queries, `query_pow_bits = 16`:

| | rows | |
|---|---:|---|
| the ONE-STEP assembly at 3 queries | **103,554** | 1.58× the domain — **it does not exist** |
| step 0 — transcript + AIR closing equality + carry | **33,834** | 51.6% of the domain |
| walk.first — query 0 + carry | **23,623** | |
| walk.step — query `k−1` + carry, the SAME circuit reused | **23,612** | × 2 |
| **the chain — 4 steps from 2 VKs** | **104,681** | every step FITS |
| **⇒ the CARRY** | **1,127** | **1.09%**, 376 rows per boundary crossed |

Compile 24.4 s + 20.9 s; prove 11.5 / 13.2 / 19.2 / 18.4 s; all four verified; each step's
`publicInput` **is** its predecessor's `publicOutput`, and every public field is checked against an
out-of-circuit twin computed by the same functions the circuit calls.

**The splice is REFUSED — eight attempts, every one against real proof objects**, i.e. an actual
step-0 Pickles proof over an actual dregg proof:

a step-0 proof over dregg proof **A** with everything else from dregg proof **B** · A's boundary and
predecessor but B's witness · **a carried challenge the walk never reads (`α_stark`) bent** · **a
carried proof datum the walk never reads (the query PoW witness) bent** · step 2 re-declaring itself
as step 3 (double-count) · step 2 walking query 2 instead of its own query 1 (skip) · a step index
outside `1..3` · a chain closed one step early. Plus: step 0 refuses an entry boundary belonging to a
different dregg proof.

⚑ **The third and fourth are the ones that matter, and they are why the CONTROL exists.** `α_stark`
and the query PoW witness are carried but *never read by the walk* — so bending them cannot break
the walk, and a refusal is attributable to the carried digest **only if something shows the walk
would otherwise have accepted**. The leg compiles the same walk circuit with the three boundary
assertions removed and **requires it to ACCEPT** all three cases the bound one refused, including a
public input with no relation to its predecessor. Without that control, eight refusals are
consistent with "the bend broke the walk", and the leg would prove nothing about the binding.

⚑ **AND ONE OF THE EIGHT WENT GREEN BY ACCIDENT, WHICH IS HOW IT WAS FOUND.** `|D⁰| = 2²`, so three
query indices collide often; on a run that drew `[0,0,0]`, "step 2 walked query 2 instead of query
1" is not a substitution at all — the rows, the paths and the fold are the same object — and the
falsifier passed without firing. The falsifier was fine; the **parameter** was not, exactly as in
§3.19 [8]. Fixture A is now minted until its query indices are **pairwise distinct**, and the leg
asserts that premise before using it.

**What a boundary costs at deployed geometry — measured, not extrapolated.** At `|D⁰| = 2²²`, 16
layers, 19 queries and the root's 940 + 175 columns, **9,103 root + 95 challenge lanes cross one
boundary**. The carry as a circuit — re-witness, range-check, pack, hash, bind — is measured at
three sizes and is linear at **3.75 rows/lane** across a 100× range (two independent slopes agreeing
within 5%, so the projection is not a two-point guess):

| | rows |
|---|---:|
| **ONE deployed boundary, full carry** | **34,566** |
| of which pack + hash + bind | 11,571 |
| **of which range-checking the re-witnessed lanes** | **22,995** |
| a boundary carrying only the transcript state and a fold value | 762 |

⚑ **And that is the number that changes the shape of the answer — but it is a BAND, and a single
number here would be a worst case wearing a total.** A boundary at a **query entry** carries the
whole opened-value set, because the next step's DEEP quotient reads all of it: 34,566 rows, **69.8%
of an aggregation-tree step**. A boundary **inside** a query, after the DEEP quotient has been
formed, carries the transcript state and a fold value: 762 rows, 1.5%. One deployed query is 827,887
rows (§3.19) — 17 steps on its own — so **most deployed boundaries are the cheap kind**, and which
end of the band the total lands on is exactly the scheduler `KimchiPartition` names as its
remainder.

| `max_proofs_verified` | usable | every boundary full-carry | intra-query boundaries | carry ignored (what §4.2 quotes) |
|---|---:|---:|---:|---:|
| 1 (a straight chain) | 57,532 | **1,198** steps | **485** steps | 478 |
| **2 (an aggregation tree)** | **49,532** | **1,838** steps | **564** steps | 556 |

**⇒ the deployed count is 564–1,838 work-carrying steps, not 556**, and two thirds of the expensive
end is **range-checking lanes a one-step verifier range-checks once** — which is what a boundary
*is*. ⚑ **§3.21 schedules against exactly this table and lands at 591 and 504.**

**What §3.20 closes, and what it does not.**

* **CLOSES: "nobody has run the partition."** A dregg proof with no one-step verifier is verified by
  four chained Pickles steps from two VKs, all proved and verified, with `KimchiPartition
  .StepPublicInput`'s one field element as the only thing crossing a boundary.
* **CLOSES: the boundary is a BINDING, not a sequence marker.** Eight splice refusals against real
  proof objects, each with a control showing the unbound circuit accepting the same witness.
* **CLOSES: a chain does not need a VK per step.** One walk circuit, invoked N times, with the step
  index and the terminal bit witnessed and pinned inductively.
* **CLOSES: the per-step carry is a measured number** at the fixture's and at the deployed geometry,
  linear in the carried lane count over a 100× range.
* **NARROWS: the step count.** ~556 becomes **564–1,838**, and the spread is a scheduling decision
  with a measured price on each side. ⚑ **§3.21 takes that decision and the answer is 591.**
* **DOES NOT CLOSE: the AGGREGATION TREE.** This is a straight chain at `max_proofs_verified = 1`.
  §4.1's binary tree needs steps that verify TWO previous proofs; the ~12,000–16,000-row overhead in
  the table above is §4.1's source reading, **not measured here**.
* **DOES NOT CLOSE: the geometry is still the fixture's.** The chain carries a 3-column AIR over a
  2²-point domain. The deployed *carry* is measured; the deployed *walk* is not — one query at
  deployed geometry is 827,887 rows, which needs the query walk itself partitioned, not merely
  separated from the transcript.
* **DOES NOT CLOSE, AND MUST NOT: nothing here is wired to `setDreggRoot`.** The fixture AIR says
  nothing about dregg's state, so anchoring on it would look proof-gated while proving a toy —
  strictly worse than the labelled `placeholderRelay`, which stays.

⚑ **§3.21 CLOSES THE SCHEDULER AND THE BAND IS GONE: 591 steps, not 564–1,838.**

---

### 3.21 ⚑ MEASURED — THE SCHEDULER: the band is a number, and the number is 591

*`bridge/mina-zkapp/src/PartitionSchedule.ts` (the scheduler), `src/DreggProofSchedule.ts` (the
chain it schedules), `bridge/mina-zkapp/scripts/partition-schedule.ts`. Gate leg 12.*

§3.20 priced a step boundary and found the price is a function of **where the cut is** — 34,566 rows
at a query entry, 762 inside a query — so it could only report the deployed count as a **band,
564–1,838 work-carrying steps**, and named the scheduler as its remainder. A 3.3× spread is the
difference between a feasible engineering project and an infeasible one.

**The answer is 591 work-carrying steps at `max_proofs_verified = 2`** — 27 above the band's
optimistic end, **1,247 below its pessimistic one** — and **504** at `max_proofs_verified = 1`
against that row's 485–1,198.

**⚑ And the reason the band existed is the COMMITMENT, not only the placement.** A query-entry
boundary costs 34,566 rows because `rootCommitDigest` is the digest of **one flat lane list**, so any
step that re-derives it re-witnesses all 9,103 deployed root lanes — **8,920 of which are claimed
opened evaluations that a fold chain never reads**. Commit to the **vector of chunk digests**
instead,

```
rootCommitDigest = Poseidon(d_0, …, d_{m-1}),   d_i = digest of chunk i
```

and a step witnesses the **lanes** of the chunks it reads and the **digests** of the chunks it does
not, re-deriving the same root either way. The boundary is still **one field element**,
`KimchiPartition.StepPublicInput`'s three slots are unchanged, and a spliced chunk still moves the
boundary because it moves that chunk's digest. What changes is that a fold step's carry stops being a
function of how big the proof is.

⚑ **TWO CARRIERS NOW EXIST IN THE TREE AND THAT IS DELIBERATE, WHICH IS NOT THE USUAL ANSWER HERE.**
§3.20's chain keeps the flat `rootCommitDigest`, and normally the right move would be to delete it
rather than keep two shapes that agree today. It stays because it is not a second *design* — it is
the **measurement** that makes 34,566 a number instead of a claim, and §3.21's own probe is
cross-checked against it to 0.03%. The chunked carrier is the one a deployed verifier would use, and
this document says so in every place that quotes a step count.

**The three numbers decompose the 3.3× exactly** (`max_proofs_verified = 2`, 49,532 usable):

| | steps |
|---|---:|
| cut at the ceiling under a flat digest — what §3.20's band tops out at | **1,963** |
| **scheduled**, flat digest — *placement alone* | **1,184** |
| **scheduled**, chunked digest — this section | **591** |
| the carry ignored entirely — what §4.2 quotes | 556 |

⇒ **placement is 1.66×, the chunked commitment a further 2.00×, 3.32× together.**

**The scheduler is a dynamic program over a measured cost function, not a rule of thumb.** The
deployed verifier is decomposed into **27,590 atoms** — one per absorbed column, per input-path
level, per DEEP column term, per fold round, per commit-path level — summing to **27,497,697 rows,
0.01% from §3.19's measured 2.75 × 10⁷**, and every row figure in it is one of §3.19's measured
marginals or a sum of them. The largest indivisible atom is **3,221 rows, 6.5% of a step**, so the
result is a placement and not a rounding. `f[j]` = fewest steps covering `atoms[0..j)`, ties broken by
least carry; the window is bounded by the domain, so it is `O(n·w)`.

**The placement rule it found.** Of its 590 boundaries, **521 land inside a query**, 67 inside the
transcript block and **2 at a query entry**. The expensive cut is the one it does not make.

**⚑ AND IT IS PROVED, NOT COMPUTED — which is the whole reason this section exists.** §3.20 exists
because "~573 steps" was a division nobody had run; a schedule that is only arithmetic would be the
same mistake one rung up. So the chain the scheduler describes is built and proved at the geometry
that runs — `degree_bits = 2`, `log_blowup = 1`, 3 queries, 2 fold layers:

| | rows | |
|---|---:|---|
| the ONE-STEP assembly at 3 queries | **146,951** | 2.24× the domain, past the 73,259 rows §3.19 watched `compile()` refuse — **no one-step verifier** |
| `transcript` — absorb, derive, AIR closing equality, commit to every chunk | **36,716** | 56.0% of the domain |
| `deep(q)` — query `q`'s input MMCS and DEEP quotient | **23,481** | reads the opened evaluations |
| `fold(q)` — query `q`'s fold chain | **14,095** | **40.0% cheaper — it never witnesses an opened evaluation** |
| ⇒ the chain | 149,444 over **7 steps from ONE verification key** | every step fits |

**A query is TWO steps, and the cut between them is the cheap one.** `deep(q)` emits
`Poseidon(rcd, cd_deep(q), 2q+2)` where `cd_deep` covers the **reduced openings** its own DEEP
quotient produced and nothing else; `fold(q)` enters it, reads the `fold` chunk, and forwards every
other chunk as a digest. That is §3.20's cheap class — "a boundary carrying the transcript state and
a fold value" — **built** rather than projected. Its price at the fixture's geometry is small
because the fixture is small; its price at *deployed* lane counts is the 1,402-row probe below, and
that is the figure the 591 is made of.

**Three methods, one program, and the alternation is forced by the boundary, not by the type
system.** §3.20 measured that four compiled step circuits hang at the first `prove`, so the
transcript is a *method* and every predecessor is a `SelfProof`. A `fold` cannot follow a `fold`
because a fold **emits** a plain challenge digest at an odd index and **enters** a deep digest at an
even one; a `deep` cannot follow a `deep` for the mirror reason. Both are exhibited as refusals.

**The splice is REFUSED — nine attempts against real proof objects**: proof B's commit-phase chunk ·
**query 1's reduced openings handed to query 0's fold half (the intra-query splice)** · a fold half
re-declaring its query · a deep half re-declaring itself as the next query · **a carried challenge
the fold half never reads (`α_stark`) bent** · **a carried chunk digest the fold half never reads
(the query PoW witness) bent** · a fold whose predecessor is a fold · a query index out of range · a
chain closed one step early. Plus the transcript refusing a foreign entry boundary. Every one is a
`prove()` refusal, and each caught error is checked **not** to be a JavaScript shape error — a
`TypeError` from a mis-shaped argument would look identical to a `catch {}` and would make the
section a green that measures the harness.

**⚑ The control builds its own predecessor, and getting that wrong would have read as success.**
The unbound twin — the same circuit with the three boundary assertions removed — must ACCEPT the
`α_stark` bend, the PoW-digest bend and a public input unrelated to its predecessor. Because the
chain is one program, a proof made by the *bound* program does not verify under the unbound
program's VK: the first version handed the bound `deep` proof across and the control refused
everything, which is exactly the shape of a control that appears to confirm the binding while
testing nothing. The control now proves the transcript and the DEEP half with the unbound circuit
itself.

**⚑ AND THE GEOMETRY MOVED FOR A FALSIFIER REASON, WHICH IS THE THIRD TIME THIS EXACT TRAP HAS
FIRED.** At `degree_bits = 1` the trace polynomials are **linear**, so every DEEP quotient
`(p(x) − p(z))/(x − z)` is a **constant** and all three queries produce the *same* reduced opening —
measured, not feared: indices `[3,0,2]` gave one value three times. "The fold half was handed another
query's reduced openings" would then substitute a value for itself and pass without firing, exactly
as §3.19 [8]'s fold-order falsifier is blind at `degree_bits = 1` and §3.20's skip falsifier is blind
when two query indices collide. The leg runs at `degree_bits = 2` **and asserts the premise** — the
reduced openings must be pairwise distinct — before the splice uses it.

**What §3.21 closes, and what it does not.**

* **CLOSES: the step count is a scheduling RESULT, not a band.** 591 at `max_proofs_verified = 2`,
  504 at 1, from a DP over 27,590 atoms and a measured carry, with the placement census reported.
* **CLOSES: the cheap cut is BUILT.** A query verified by two chained steps whose boundary carries
  the reduced openings, proved and verified, with the intra-query splice refused and a control.
* **CLOSES: a step's carry can be made a function of what it READS.** The chunked
  `rootCommitDigest` is proved as the chain's actual commitment, shown elementwise to cover exactly
  what the flat one did, shown order-sensitive, and every chunk shown to move the boundary.
* **NARROWS: what a deployed boundary costs.** At deployed lane counts this leg's flat-digest probe
  reads **34,555 rows against §3.20's recorded 34,566** — two harnesses, the same boundary — while
  the same probe for a **scheduled fold step** (74 chunk digests + 132 fold lanes + 95 challenge
  lanes) reads **1,402: 24.6× cheaper**, and that is the number the 591 is made of.
* **DOES NOT CLOSE: a step reading a PROPER SUBSET of the opened-evaluation chunks.** The proved
  chain has steps that read **all** of them (`transcript`, `deep`) and steps that read **none**
  (`fold`), which is the same code path — `computed` digests spliced into witnessed ones — at its
  two extremes. The deployed schedule needs a DEEP step that reads chunks *k…k+j* of *m*, and that
  is priced by probe here, not proved: the fixture's three-column DEEP quotient is not big enough to
  split across two steps and doing so would demonstrate nothing.
* **DOES NOT CLOSE: the AGGREGATION TREE**, same as §3.20 — this is a straight chain, and the
  12,000–16,000-row `max_proofs_verified = 2` overhead the 591 is computed against is §4.1's source
  reading, not a measurement.
* **DOES NOT CLOSE: the deployed WALK is still not built.** The atom model's row figures are §3.19's
  measured marginals and its aggregate matches §3.19's projection to 0.01%, but a 2.75 × 10⁷-row
  circuit has never been emitted. **591 is a schedule over a measured model, not over an emitted
  row list** — which is precisely the distinction `KimchiPartition` draws between "a partitioning
  number" and "a compiler output", and it is still open.
* **DOES NOT CLOSE: 2.75 × 10⁷ is itself a FLOOR** (§3.19: the AIR term in it is the fixture's four
  constraints, not the root's 1,093). A floor scheduled is still a floor.
* **DOES NOT CLOSE, AND MUST NOT: nothing here is wired to `setDreggRoot`.**

---

### 3.22 ⚑ MEASURED — THE ROOT'S OWN AIR, EMITTED: all 1,093 constraints, 275,143 rows

*`bridge/mina-zkapp/src/RootAirDag.ts`, `src/generated/root-air-dag.json`,
`bridge/mina-zkapp/scripts/root-air-rows.ts`, and the extension half of the extractor in
`circuit-prove/tests/root_air_constraint_census.rs`. Gate leg 13.*

§3.19 named exactly one thing in the assembly as still the fixture's — `DreggProofVerify`'s
`constraints` argument, a 3-column AIR with **four** constraints against the root's **1,093** — and
said in terms what that made every figure downstream: *"2.75 × 10⁷ is a FLOOR ... the AIR term
inside it is the fixture's four constraints"*. §3.21 inherited it whole: *"a floor scheduled is
still a floor."*

**The root's constraint system is now an artifact the o1js side consumes.**

**§3.18's named remainder is built.** `to_dag` covered the 901 base constraints and left the 192
LogUp ones *"outside the vocabulary"*, naming the extension precisely — `ExtLeaf::Challenge`, a
permutation-column leaf, a `lift` of a base index, sharing `base_cache`. `to_dag_full` is that, and
the whole root is **one shared DAG**:

| | |
|---|---:|
| constraints | **1,093** = 901 base + 192 LogUp |
| DAG nodes | **10,417** |
| multiplies | **3,029** |
| node census | var 1,282 · cst 377 · add 3,797 · sub 1,571 · neg 41 · mul 3,029 · **evar 320** |
| column variables | 1,282 base + 320 extension |

⚑ Three of the seven tables (`Const`, `Public`, `recompose`) have **zero** base constraints, so
until now this rung covered *nothing* for them. They have 3 LogUp constraints each and are covered.

**THE MEASUREMENT, EMITTED** — `getRows()` on a circuit that walks every node and folds every
constraint, not a model of one:

| table | N | nodes | cols | witness | `C_i` | fold | rows |
|---|---:|---:|---:|---:|---:|---:|---:|
| Const | 3 | 32 | 14 | 365 | 432 | 130 | 927 |
| Public | 3 | 32 | 14 | 365 | 432 | 130 | 927 |
| Alu | 146 | 1,319 | 307 | 7,983 | 23,610 | 6,986 | 38,579 |
| poseidon2-W16 | 337 | 3,036 | 379 | 9,855 | 53,381 | 16,162 | 79,398 |
| poseidon2-W24 | 501 | 5,138 | 571 | 14,847 | 90,389 | 24,034 | 129,270 |
| recompose | 3 | 32 | 14 | 365 | 432 | 130 | 927 |
| expose_claim | 100 | 828 | 303 | 7,879 | 12,450 | 4,786 | 25,115 |
| **Σ** | **1,093** | **10,417** | **1,602** | **41,659** | **181,126** | **52,358** | **275,143** |

and the per-operation marginals are emitted too: **extAdd 18, extSub 18, extMul 30, one α-fold step
48** — §3.16's measured `h = 48`, reproduced from its two halves. §3.14's model units (31 and 19)
land 3% and 5% high.

**⇒ the AIR term is 1.00% of §3.19's 2.75 × 10⁷.** That is a small number and it is the whole
point: it had never been *measured*, so the projection could not honestly be quoted as anything but
a floor.

**THE SEAM, AND WHAT JOINS IT.** The TypeScript walker is a **third** implementation beside p3's
and Lean's and nothing proves it faithful. What joins it is 21 KAT vectors carrying the α-folded
accumulator the Rust side computed from p3's own AIRs, reproduced **both** out of circuit and as an
**in-circuit assertion** for all seven tables. It refuses a wf-preserving one-child edit to a single
Alu node, two constraint roots swapped, and one constraint dropped — each checked to be `Constraint
unsatisfied` and not a harness shape error. The ext walk is separately differential-checked against
p3's own `SymbolicExpressionExt` evaluation over all 192 constraints, **1,536 agreements**.

**⚑ TWO CORRECTIONS TO THE RECORD, both found by running what the record described.**

- §3.17 records *"the α-FOLD IS OFF BY ONE IN `AirEval.ts`"*. That is a true reading of both bodies
  and a **wrong conclusion**: seeding with zero and folding `C_0` gives `0·α + C_0 = C_0`, so p3's
  first fold **is** the other one's seed. Both compute `C_0·α^{N−1} + … + C_{N−1}` exactly, measured
  here on all 146 Alu constraints. The difference is **34 emitted rows spent on an identity** — a
  row difference, not a different accumulator. A verifier built on `foldConstraints` would have been
  **right**. §3.16's "corrected for it by subtracting one marginal price" was the correct treatment;
  the §3.17 note over-read it. This now runs as a **permanent control** on every green pass.
- §3.18 charged 1,282 `.var` copy nodes at 19 rows each (24,358 rows) and called them "elidable".
  **Emitted they are free** — `reduceLane` does not reduce a lane already under 2³¹ — so the elision
  was always taken and the model overcharged for it. A `constScale` elision measures **zero** for
  the same reason: a multiply's cost is its four lane *reductions*, not its sixteen products, which
  is §3.8's central finding one rung out.

**What §3.22 does NOT close.** The extraction is still a Rust seam. One accumulator over all seven
tables is not the batch-STARK per-instance comparison. Nothing is wired to `setDreggRoot`.

---

### 3.23 ⚑ MEASURED — THE SCHEDULE OVER AN EMITTED ROW LIST: 591 is 519

*`bridge/mina-zkapp/scripts/emitted-atoms.ts` and `bridge/mina-zkapp/scripts/emitted-schedule.ts`,
`PartitionSchedule.emittedProgram`. Gate leg 14.*

§3.21 says what its 591 is not: *"591 is a schedule over a measured MODEL, not over an emitted row
list — which is precisely the distinction `KimchiPartition` draws between 'a partitioning number'
and 'a compiler output', and it is still open."*

**Of the model's 27,590 atoms, every row figure was a measured marginal EXCEPT two divisions:**
`perArith = (deployedQueryWalk − pathLevels × PERM_ROWS)/(layers+1)` and `tailRows/nTail`. Both are
replaced by **in-context marginals on the deployed program itself** — rows at 16 fold layers against
15 against 14 separates a *round* from a *path level*; input depth 22 against 21 gives the input
level:

| atom | modelled | **EMITTED** | delta |
|---|---:|---:|---:|
| one commit-phase path level | 2,668 | **2,677** | +0.3% |
| one fold **round**'s arithmetic | 3,221 | **2,809** | **−12.8%** |
| one input-phase path level | 2,668 | **2,677** | +0.3% |

**99.0%** of the 748,438-row deployed query walk is now atoms carrying their own in-context
marginal; the residual is 7,496 rows.

⚑ **The atom that moved is the one the model leaned on.** 3,221 is the model's *"largest indivisible
atom, 6.5% of a step"* — the figure that licensed "this is a placement and not a rounding". It is
2,809, because the division charged the fold rounds for a residual that is not theirs.

**THE FLOOR MOVED IN BOTH DIRECTIONS AND THE NET IS NOT THE DIRECTION "FLOOR" IMPLIES:**

| | atoms | rows |
|---|---:|---:|
| §3.21's atom model (fixture AIR, divided marginals) | 27,590 | 27,497,697 |
| EMITTED, no AIR | 27,566 | 24,333,629 |
| **EMITTED, the ROOT's AIR** | **39,076** | **24,574,325** |

The AIR term is **+240,696** rows and **+11,510** atoms; the walk term is **−3.16 × 10⁶**. Net the
emitted total is **10.64% BELOW** §3.19's projection. The projection was called a floor because its
AIR term was too small; it was **also too big everywhere else, and by more**.

**THE SAME DYNAMIC PROGRAM, THE SAME CHUNK-SIZE SWEEP:**

| | `max_proofs_verified = 1` | `max_proofs_verified = 2` |
|---|---:|---:|
| §3.21, modelled atoms, fixture AIR | 504 | **591** |
| EMITTED atoms, no AIR | 443 | 514 |
| **EMITTED atoms, the ROOT's AIR** | **448** | **519** |

The model arm reproduces 591 and 504 **exactly**, and the leg fails if it drifts by one step — so
the movement is the emission and the AIR, not a different scheduler. Boundaries at mpv = 2: 513
inside a query, 5 in the transcript/AIR block, **zero** at a query entry.

⚑ **AND THOSE COUNTS ARE STILL OPTIMISTIC, BY §3.24's MEASUREMENT.** They are computed against
§4.1's arithmetic budget of 57,532 usable rows, and §3.24 measures a two-branch program failing to
compile at that budget. The honest per-branch budget is lower; the schedule has not been re-run
against it.

---

### 3.24 ⚑ MEASURED — THE ROOT AIR AS A CHAIN, PROVED, and §4.1's budget is ~13% too generous

*`bridge/mina-zkapp/src/RootAirChain.ts`, `bridge/mina-zkapp/scripts/root-air-chain.ts`. Gate leg 15.*

275,143 emitted rows is **4.20× the 65,536-row Pickles step domain**, so **dregg's root constraint
system has no one-step verifier** — the situation §3.20 constructed deliberately by choosing three
queries, arrived at here by the object itself.

**THREE CHAINED PICKLES STEPS OVER IT ARE PROVED AND VERIFIED.**

| | nodes | constraints | rows | |
|---|---|---|---:|---|
| slice 0 | [0, 1,537) | [0, 186) | **50,398** | 76.9% of the domain |
| slice 1 | [1,537, 3,327) | [186, 345) | **48,181** | 73.5% |
| slice 2 | [3,327, 4,798) | [345, 543) | **49,774** | 75.9% |

⇒ **4,798 of 10,417 nodes, 543 of 1,093 constraints**, and the whole of `Const`, `Public`, `Alu`
and `poseidon2-W16` — four of the seven root tables. Compile 53.4 s for three circuits, prove
13–14 s each, all verified; each step's `publicInput` **is** its predecessor's `publicOutput`, and
every public field is checked against an out-of-circuit twin.

⚑ **THE CUT WIDTH IS WHY THIS IS AFFORDABLE, AND IT IS A PROPERTY OF THE DAG.** The extractor emits
in DFS post-order, so the number of values computed before a boundary and read after it **never
exceeds 102** across all 10,417 nodes (median 66). A boundary carries ~100 extension values, not the
1,602 column variables. `liveness` computes it exactly, charging each fold at the position it
actually happens (`max(roots[0..j])`, not `roots[j]`) — a root computed early and folded late stays
live the whole way.

**The splice is REFUSED — six attempts**, each a `prove()` refusal checked *not* to be a JavaScript
shape error: a public input with no relation to its predecessor · one carried **live value** bent ·
one **column lane** bent in a chunk the slice **does** read · a chunk **digest the slice never
reads**, bent · the incoming **accumulator** bent · slice 2 handed slice 0's proof, **skipping** the
middle slice. **The control runs in a CHILD process and builds its own predecessor** (§3.21's
lesson), and accepts both the unrelated public input and the unread-digest bend — so the fourth
refusal is the commitment biting rather than the work breaking.

⚑ **§4.1's USABLE-ROW BUDGET IS TOO GENEROUS, MEASURED.** §4.1 computes 65,536 − 3 `zk_rows` − 1
public input − ~8,000 recursive-verifier overhead = **57,532** usable at `max_proofs_verified = 1`.
At that budget these slices measure 56,772 / 55,715 / 57,430 rows by `analyzeMethods` — **all under
the domain** — and `compile()` **fails**:

```
length mismatch in Array.map2_exn: 1 <> 2
```

That is Pickles refusing a **chunked branch**: `analyzeMethods` reports the method *body*'s rows,
the branch Pickles builds carries the recursive verifier on top, and one branch crosses 2¹⁶ while
another does not, so the two disagree on `numChunks`. Measured: **50,000 compiles, 57,532 does
not.** ⚑ **Every deployed step count in §3.23 and §4.2 is computed against 57,532 and is optimistic
by that gap.**

⚑ **THE OTHER WALL, AND WHY IT IS DIFFERENT FROM §3.20's.** The full chain is **7 slices** at the
measured budget, and they are structurally **different** circuits — different nodes, different
operands — so §3.20's "one walk circuit invoked N times" is not available: a uniform circuit would
need an in-circuit multiplexer over the 102-value live set, ~102 rows per operand lane against 30
for a whole extension multiply, a **27× blowup**. §3.20 measured a node process that compiled
**four** step circuits hanging at the first `prove`, so one process carries **three**; a 6-slice
build is **refused at build time** with that number rather than left to hang. What makes a VK per
slice acceptable here and not there: **the AIR is a FIXED program**, so its slice VKs are protocol
*constants* emitted once, not a per-proof cost. Full coverage is a process-per-slice architecture —
each process compiling its predecessor's program for the VK plus its own, two circuits, for any
chain length. **Not built.**

**What §3.24 does NOT close.** The chain runs on a pseudorandom column assignment; §3.25 runs the
real one, unchained. A **partial** chain's far end is **not** verifier-computable — the live set is
in the terminal seal's preimage — and the leg says so rather than quoting the complete chain's
property for it.

---

### 3.25 ⚑ MEASURED — THE ROOT'S AIR ON THE ROOT'S OWN PROOF, and one instance does not bind ζ

*`circuit-prove/src/bin/root_air_instance.rs`, `bridge/mina-zkapp/scripts/root-air-real.ts`. Gate
leg 16.*

§3.22 evaluates the root's constraints at **pseudorandom** extension-valued assignments. That
measures arithmetic and decides nothing — §3.19 killed exactly this one rung down: *"until something
consumes a proof, 'Mina verifies dregg' is a statement about a parts list."*

`root_air_instance` loads dregg's **committed** root proof — `ugc-dregg/tests/fixtures/
whole_history_proof.bin`, a 3-turn `prove_turn_chain_recursive` root under VK `434f57d2…`,
`degree_bits [10,10,16,15,3,16,0]`, exactly §1.2's reading — decodes the `BatchProof`, replays
`verify_batch`'s observe/sample sequence, and emits every instance's opened values at ζ: main and
preprocessed local and next, the LogUp permutation columns and cumulative sums, the permutation
challenges, the quotient chunks, the four Lagrange selectors, the recomposed `quotient(ζ)` and p3's
folded accumulator.

```
alpha [923772376, 422847819, 814749997, 1738989069]
zeta  [656249784, 609259845, 1101119587, 318054937]
```

It **refuses to emit** unless it has itself verified all seven closing equalities with the replayed
challenges, and p3's own `verify_batch` — full FRI/PCS, its own sampling — accepts the proof first,
so a drifted replay is a red rather than a plausible JSON. No visibility was widened; three private
bodies are replicated and named in place. Run time **17 ms**.

**The emitted DAG reproduces p3's accumulator on all seven instances, exactly**, and
`acc · Z_H(ζ)⁻¹ == quotient(ζ)` holds for each — first out of circuit, then as a **Kimchi
constraint**. That is the extraction seam closed against the deployed object on deployed values.
Six bends refused: an opened trace value · an opened preprocessed value · an opened **LogUp
permutation** value · `quotient(ζ)` itself · the transcript's α · the vanishing-polynomial inverse.

⚑ **THE FINDING, AND IT IS ABOUT THE DEPLOYED ROOT, NOT ABOUT THIS CIRCUIT.**

| table | `degree_bits` | α binds | **ζ binds** |
|---|---:|---|---|
| Const | 10 | yes | yes |
| Public | 10 | yes | yes |
| Alu | 16 | yes | yes |
| poseidon2-W16 | 15 | yes | yes |
| poseidon2-W24 | 3 | yes | yes |
| recompose | 16 | yes | yes |
| **expose_claim** | **0** | yes | **NO** |

`expose_claim` has a **one-row trace domain**, and for *this, honest* transcript its closing
equality is an **identity in ζ**. With `|H| = 1`, `is_first_row` and `is_last_row` are ζ-free
constants, `is_transition = ζ − 1 = Z_H(ζ)`, and the two size-1 quotient chunks carry **equal**
values, so the recomposition `[(Q₀+Q₁) + (ζ/g)(Q₀−Q₁)]/2` collapses to `Q₀`. **Both sides are
constant in ζ.** All six `degree_bits > 0` instances do bind ζ, and α binds all seven — both
asserted, the α one as a hard floor.

⚑ **`zetaBinding: false` IS NOT "the check is free", AND A MINA-SIDE VERIFIER MUST NOT SKIP THE OOD
POINT THERE.** A one-row trace polynomial *is* a constant, so holding the openings fixed while
moving ζ is the correct continuation rather than a perturbation: the insensitivity is a property of
an honest prover, not of the verifier's check. The check itself evaluates, at a uniform ζ,
`P(X) = A + (X−1)·B − (X−1)·Σᵢ zpsᵢ(X)·cᵢ` of degree ≤ 2 — `A` the α-fold of every constraint not
gated by `when_transition`, `B` the fold of the gated ones, `cᵢ` the chunk openings — all of them
fixed **before** ζ is sampled and each pinned to a constant by p3-fri's height-1 guard (the
`reduced_openings.get(&params.log_blowup)` must-be-zero check). `P(1) = A`, so a prover with `A ≠ 0`
is refused except with probability `≤ 2/|EF| ≈ 2⁻¹²³`. That is now MEASURED and emitted per instance
as **`zetaBindsForgery`**, asserted for **all seven** with no `degree_bits = 0` carve-out: a forgery
solved to close at the sampled ζ dies at every bent ζ, `expose_claim` included. The three flags ride
in the emitted JSON, and this leg's own falsifiers are aimed at a table that **does** bind ζ — the
same discipline §3.19 [8] and §3.20 applied after a falsifier went green on a degenerate parameter.
`circuit-prove/tests/height1_air_check_binding.rs` is the standing control for the shape: it
reproduces the identity from the geometry alone, exhibits the forger repairing the equality at one
prescribed ζ, requires the repair to die at twelve others, and refuses any `degree_bits = 0` table
that hides a constraint behind `when_transition` (the real one-row hazard — `is_transition` vanishes
on a one-row domain, so such a constraint is simply unenforced).

**What §3.25 does NOT close.** This is the per-instance AIR closing equality, not the batch-STARK
verifier: the FRI walk, the MMCS openings and the transcript derivation over *this* proof are not in
this circuit (§3.19 does them at fixture geometry). Nothing is wired to `setDreggRoot`.

---

### 3.26 ⚑ MEASURED — THE COMPILE CEILING, and `usableRows` names something that does not exist

*`bridge/mina-zkapp/scripts/root-air-ceiling.ts`, `src/PartitionSchedule.ts`. Gate leg 16.*

§3.24 left the per-branch budget as a bracket — 50,000 compiles, §4.1's arithmetic 57,532 does not —
and every step count in the record is priced against the arithmetic. Narrowed on the **real**
three-slice chain, five trials a round in five child processes so a wasm abort is a failed trial and
not a dead search:

| | budget | widest branch, EMITTED | `compile()` |
|---|---:|---:|---|
| largest that compiles | **54,289** | **54,300** | ✔ |
| smallest that fails | 54,324 | 54,376 | ✗ `Array.map2_exn: 1 <> 2` |

⇒ **§4.1 assumed 8,000 rows of recursive-verifier overhead. Measured it is 11,160–11,236 — 1.40×.**

⚑ **AND THE INSTRUMENT REFUTED ITS OWN PREMISE, WHICH IS THE REAL RESULT.** The first version of
this leg was a **dialable synthetic probe** with the same gate vocabulary — witnessed BabyBear
lanes through `canonicalLane`, then an `extMul`/`extAdd` chain, plus a one-row knob — on the theory
that a ceiling is `65536 − OVERHEAD(proof arity)` and the body only has to supply rows. It is not:

- **57,769 rows** — one `SelfProof` branch beside a small sibling, rows from the extension
  arithmetic — `compile()` **FAILS**;
- **63,300 rows** — the *same program shape*, the *same sibling*, the extra rows supplied by
  single-row field multiplies — `compile()` **SUCCEEDS**.

A **bigger** circuit compiling where a **smaller** one does not is not a ceiling in rows at all.
Kimchi's row count is not what crosses 2¹⁶: range checks and lookups carry a table and a domain
requirement `analyzeMethods` never reports, so **the crossing is a function of the gate MIX**.
⚑ **That kills what `usableRows(overhead)` names** — a per-`max_proofs_verified` constant good for
any circuit, which is exactly the shape of §4.1's table. A ceiling is only honest for the shape it
was measured on. Every arm of the leg is therefore a **real slice body** (`sliceCommitment` and
`sliceWork`, imported from the chain being priced), and the two points above survive as a
**permanent control**, so a reader reinstating a single-number ceiling has to walk past a green test
saying it cannot be one.

**What is narrowed and what is not, named as such.** `MEASURED_CEILING.mpv1` is a narrowed crossing.
`mpv2AtLeast` (40,073 — two real slice bodies, one verifying **two** previous proofs) and
`sideloadAtLeast` (51,136 — §3.27's shape, compiled *and proved*) are **envelopes**: a lower bound
on the ceiling, hence an upper bound on a step count. Their re-check is one-sided and **cannot
notice a ceiling moving up**; `CEILING_FULL=1` narrows them.

**THE SCHEDULE, RE-RUN (leg 14b [3b]).** At the narrowed mpv = 1 ceiling of 54,300 usable rows
instead of §4.1's 57,532, the deployed verifier's step count rises. At **`max_proofs_verified = 2`,
which is §3.23's headline 519**, the honest figure is a **bracket and not a number** — bounded below
by 40,073 usable (observed to compile) and above by 54,300 (a two-proof verifier cannot be smaller
than a one-proof one). ⚑ **519 is replaced by that bracket.** A single number there would be an
extrapolation in a measurement's voice.

---

### 3.27 ⚑ MEASURED — THE FULL CHAIN: seven slices, seven processes, on dregg's committed root proof

*`bridge/mina-zkapp/src/RootAirProcessChain.ts`, `bridge/mina-zkapp/scripts/root-air-fullchain.ts`. Gate leg 17.*

§3.24 proves the largest chain **one** process holds — three slices, 4,798 of 10,417 nodes — and
names the rest: *"the full AIR chain is 7 slices and one process carries 3 (a process-per-slice
architecture is priced, not built)."* **It is built, and it runs on the values
`root_air_instance.rs` decodes out of `whole_history_proof.bin`, not on an LCG instance.**

| | nodes | constraints | EMITTED rows | |
|---|---|---|---:|---|
| slice 0 | [0, 1,537) | [0, 186) | 50,398 | 76.9% of the domain |
| slice 1 | [1,537, 3,327) | [186, 345) | 48,181 | 73.5% |
| slice 2 | [3,327, 4,798) | [345, 543) | 49,776 | 76.0% |
| slice 3 | [4,798, 6,410) | [543, 731) | 48,763 | 74.4% |
| slice 4 | [6,410, 8,286) | [731, 820) | 48,805 | 74.5% |
| slice 5 | [8,286, 9,729) | [820, 1,016) | 51,136 | 78.0% |
| slice 6 | [9,729, 10,417) | [1,016, 1,093) | 28,296 | 43.2% |

⇒ **ALL 10,417 nodes, ALL 1,093 constraints, an EMPTY terminal live set.** 325,355 emitted rows over
seven circuits; compile 1,200 s, prove 442 s, 29 min end to end. Every proof verified; every step's
`publicInput` **is** its predecessor's `publicOutput`; every public field checked against an
out-of-circuit twin **by a process that compiled nothing**. **No process compiled more than one
circuit**, so §3.20's four-per-process wall is never approached.

⚑ **THE OBVIOUS ARCHITECTURE DOES NOT WORK, AND §3.24 PREDICTED THE WRONG ONE.** `SelfProof` means
"a proof of *this* program", so seven slices as seven methods is seven branches compiled in every
process — the wall, unchanged. Seven separate programs each taking its predecessor's `Proof` is
**worse**: o1js resolves a non-self proof type through `CompiledTag`, which exists only if the
producer was **compiled in the same process** —

```
${consumer}.compile() depends on ${producer}, but we cannot find compilation output for ${producer}.
```

— and that dependency is **transitive**, so compiling slice 6 means compiling slices 0–5 first.
§3.24's *"each process compiling its predecessor's program for the VK plus its own, two circuits,
for any chain length"* is **wrong** and this replaces it.

**So the predecessor is SIDE-LOADED.** A `DynamicProof` is verified against a key that arrives as a
**runtime input**, so slice k's circuit is built and compiled knowing nothing about slice k−1's
prover. One compile per process, and the boundary crosses as **three files**: the proof's JSON
(34,629 bytes), the key (`{data, hash}`), and the feature flags the predecessor's own
`analyzeMethods` produced.

⚑ **AND THAT MOVES A BINDING OUT OF THE CIRCUIT; ONE CONSTANT PUTS IT BACK.** o1js says it plainly —
a `DynamicProof` circuit *"makes no assertions about the verificationKey used on its own"*. A prover
who supplies some **other** program's proof together with **that** program's key satisfies
`prev.verify(vk)` perfectly, and the chain would "verify" while carrying a value nothing in it
computed. The fix is one constraint and it must be a **constant**:

```ts
vk.hash.assertEquals(Field(<slice k−1's verification key hash>));
```

so slice k's circuit — and therefore slice k's **own** key — is a function of slice k−1's. The seven
keys form a chain ending in one field element a verifier pins. Affordable for §3.24's reason: **the
AIR is a fixed program**, so slice keys are protocol constants emitted once. And the slice compiles
to the **same** key in a second, independent process — a pinned hash means nothing if the key is not
reproducible.

**SEVEN SPLICES REFUSED**, in a process that compiled only the slice it was bending, against a
predecessor proof another process made: an unrelated public input · a carried **live value** · a
**column lane** in a chunk it reads · a chunk **digest it never reads** · the incoming
**accumulator** · ⚑ **slice 1's proof handed with slice 1's OWN key** · the right proof under a key
it was not made under. Each checked *not* to be a JavaScript shape error.

⚑ **THE CONTROL GOT STRONGER, AND THE OLD LESSON WAS ABOUT BAKED-IN KEYS.** §3.21 and §3.24 both had
to build a **parallel predecessor**, because a bound `SelfProof` cannot verify under an unbound VK.
Side-loading dissolves that — the key is an input — so the control refutes the binding **on the
bound chain's own proof objects**. Three of them: **UNBOUND** accepts the unrelated public input and
the unread-digest bend; **UNBOUND-but-PINNED** still **refuses** the foreign proof; **UNPINNED**
**accepts** it. So the foreign-proof refusal is attributable to the pin and to nothing else.

⚑ **THE TERMINAL SEAL IS VERIFIER-COMPUTABLE FROM THE PROOF ALONE.** Folding p3's way over the
**concatenated** constraint list is Horner over contiguous spans, so

```
acc_unified  =  Σ_T  acc_T · α^(1093 − b_T)
```

for tables `T` whose root spans end at `b_T`. Every `acc_T` is p3's **own** per-instance
accumulator, which the root proof's own closing equality pins to its opened quotient — and the
identity is checked against the Rust side's seven accumulators and **holds exactly on the real
proof**. A Mina-side verifier holding dregg's root proof can compute the value the chain seals to.

**What §3.27 does NOT close.** This is the AIR half — the seven per-instance closing equalities —
not the FRI walk over that proof. ⚑ **§3.28 braids that walk onto this seal and runs it at the
root's REAL geometry**; what remains of this sentence is the part §3.28 also does not close. The side-loaded
shape's ceiling is an **envelope**, not a narrowed crossing (§3.26). Nothing is wired to
`setDreggRoot`.

---

### 3.28 ⚑ MEASURED — THE BRAID: the AIR seal chained into the FRI walk, at the root's real geometry

*`bridge/mina-zkapp/src/RootFriWalk.ts` (the segment list and the planner),
`src/RootFriSlice.ts` (the interpreter, the twin and the side-loaded slice program),
`bridge/mina-zkapp/scripts/root-fri-braid.ts` (the leg), `bridge/mina-zkapp/scripts/fri-walk-plan.ts` (the plan alone),
`circuit-prove/src/bin/root_fri_instance.rs` (the FRI half of the committed root proof).*

§3.27 closes the AIR half at real geometry and ends by naming what it does not close: *"this is the
AIR half — the seven per-instance closing equalities — not the FRI walk over that proof, which is
still §3.19's at fixture geometry."* This is that walk, at the root's real geometry, chained to the
AIR half's terminal seal.

**Two chains glued end to end would prove strictly less than either looks like it proves**: the AIR
half folds one set of opened values, the FRI half authenticates another, and nothing says they are
the same set. So the braid is built on **one column commitment**. `dagDigest` — the AIR chain's own
chunked commitment over its 1,602 extension values — is carried across the seal, and FRI slice 0
**recomputes `terminalSeal(dagDigest, digest(acc), 7)` from the AIR column assignment it loads** and
asserts it *is* AIR slice 6's public output. That check runs **out of circuit before anything
compiles**, and it passes against the artifact §3.27's run left on disk:

```
acc              1115370058, 392087499, 1512245278, 1909299373
recomputed seal  9641100034022665855204649324820202945538794125581438690095474365720638566508
AIR slice 6 out  the same
```

#### The walk, and it reproduces p3's own verification

The FRI half of the committed root proof is dumped by `root_fri_instance.rs`, which runs p3's own
`verify_batch`, re-verifies every Merkle opening with the real MMCS, and refuses to emit if its
mirrored challenger state does not reproduce the 16-bit query grind. **The `DuplexChallenger` state
at `verify_fri`'s door is emitted**, so the o1js side starts its transcript where dregg's own
verifier starts it.

Against that, the whole 11,303-segment walk runs **out of circuit, in seconds**, by the same
functions the circuit calls:

| | |
|---|---|
| FRI `α`, all 16 `β`s, all 19 query indices | **derived, and equal to p3's own** |
| 76 mixed-height input openings (19 queries × 4 rounds) | **reproduce dregg's own four commitments** |
| all 95 reduced openings | **reproduce p3's own `open_input`** |
| 304 fold steps | **reproduce p3's own fold chain** |
| all 19 queries | **land on the committed final polynomial** |

⚑ **THAT INSTRUMENT EXISTS BECAUSE THE SLICE RUN CANNOT BE IT.** A slice run proves the first N cuts;
the first assertion against a committed Merkle root is ~12 slices in and the fold chain ~30, so a
wrong convention **compiles and proves cleanly for as far as any affordable run reaches.** It found
four, and every one of them would have been a green:

1. **The transcript does not start empty.** `verify_fri` is entered with the challenger's *output
   buffer already full* — `two_adic_pcs::verify` has just observed every opened evaluation — so
   FRI's `α` is drawn by **popping**, with no permutation. Duplexing first puts `α`, every `β`, the
   PoW sample and all 19 indices one permutation ahead.
2. **`sample_bits(k)` is the low `k` bits**, not the sample.
3. **`alpha_pow` starts at one.** At zero every reduced opening is zero — and a chain of zeros folds
   and closes without complaining.
4. **A missing derived knob is silent.** The dumper emits p3's knobs, not this side's derived
   `indexBits`; undefined, `Array.from({length: undefined})` is an empty bit array, every path
   direction is `undefined`, and every `undefined ? a : b` takes the same branch. A walk that runs,
   proves, and is about nothing.

#### What the braid binds, as a number

⚑ **The permutation round is NOT in the AIR's assignment, and assuming it was is an error this leg
made and measured.** The PCS commits an extension permutation column as **four base columns** and
opens each at `ζ`; the AIR holds **one** extension value, the whole column's opening. They are
related — `perm[p][k] = Σ_j f_{4k+j}(ζ)·X^j` — and not equal. Mapped as equal, 216 of 512 matched by
coincidence of layout and 296 did not.

| | opened values | |
|---|---:|---|
| lanes of the AIR chain's own column commitment, read out of it | **1,236** | 47.0% |
| bridged to it by `permBind` (`Σ_j f_j(ζ)·X^j`, paid **once**, not per query) | **512** | 19.5% |
| under `friDigest` alone — main and preprocessed columns the AIR never reads, plus all 56 quotient-chunk openings | 882 | 33.5% |
| **total per query** | **2,630** | |

⚑ **2,630, and §3.14/§3.15 say 2,286 — wrong in two directions that do not cancel.** The old census
`940·2 + 175·2 + 7·2·4` **omits the permutation round** (64 extension columns × 4 × 2 = 512 terms)
and **assumes two opening points everywhere**, which the proof refuses: `Const`, `Public`,
`recompose` and `expose_claim` reference no next-row main or preprocessed value, so those matrices
are opened at `ζ` alone — 168 terms §3.15 charges and the proof does not have.

⚑ **And every input-phase opening is MIXED-HEIGHT.** The root's committed matrices sit at **five**
distinct heights (22, 21, 16, 9, 6), so `MerkleTreeMmcs::verify_batch` compresses a shorter matrix's
own row digest into the running root at the level its height names — four injections per round. §3.14
residual 5 ("the input-phase MMCS opening over MIXED heights ... is priced and not implemented") is
**closed**; §3.14's flat-depth-22 derivation of 6.3 × 10⁵ rows/query was pricing a different tree.

#### The size, and the cut list

| | |
|---|---:|
| segments in the walk | **11,303** |
| modelled work rows | **30,363,795** |
| carry | **9,275,994** (23.4%) |
| **⇒ slices at a 50,000-row budget** | **839** |
| slices per query | 43–45 |
| carry per slice | min 4,940 · median 7,215 · max 32,318 |
| widest single segment | 9,600 rows |
| widest live set | 135 lanes |

The carry band is §3.20's, confirmed at the real geometry and at a finer granularity: a boundary
inside a Merkle path carries a digest and the derived challenges; a boundary inside the DEEP quotient
carries five height accumulators, their `alpha_pow`s and the column chunks it reads.

#### It proves, and 48 slices is one complete query walk

Every slice below is its own `ZkProgram`, compiled and proved in **its own process**, taking its
predecessor as a side-loaded `DynamicProof` with the predecessor's verification-key hash pinned as
a compile-time constant — §3.27's mechanism, extended by one link: **FRI slice 0's predecessor is
AIR slice 6.**

| FRI slice | segments | | EMITTED rows | model | compile | prove |
|---:|---|---|---:|---:|---:|---:|
| 0 | [0, 17) | the transcript, from dregg's own challenger state | 46,439 | 47,946 | 111 s | 31 s |
| 1 | [17, 32) | the transcript closes; `permBind` begins | 48,476 | 47,361 | 58 s | 39 s |
| 2 | [32, 44) | `permBind` — the permutation round bridged to the AIR | 47,134 | 47,887 | 94 s | 23 s |
| 3 | [44, 60) | the main round's opened rows, sponged | 46,656 | 49,559 | 49 s | 18 s |
| 11 | [167, 180) | **the main round's MIXED-HEIGHT root, closed on dregg's commitment** | 43,494 | 46,009 | 42 s | 16 s |
| 13 | [193, 208) | the quotient round's root | 46,890 | 49,695 | 39 s | 13 s |
| 21 | [313, 318) | **the DEEP quotient begins** — f(z) read out of the AIR's own chunks | 39,615 | 44,649 | 35 s | 13 s |
| 31 | [365, 378) | the last DEEP run; the fold chain begins | 42,411 | 47,604 | 67 s | 24 s |
| 36 | [443, 459) | a commit-phase row: leaf, fold at β, coset descent | 45,068 | 48,412 | 72 s | 21 s |
| 47 | [623, 640) | **query 0 lands on the committed final polynomial** | 45,570 | 47,770 | 43 s | 14 s |

| | |
|---|---:|
| **FRI slices proved** | **48** of 839 |
| **the braided chain** | **55 steps** — 7 AIR + 48 FRI, one key-pinned side-loaded chain |
| emitted rows | **2,101,955** (the model said 2,245,109 — **−6.4%**) |
| compile / prove | 2,621 s / 960 s |
| **per slice** | **75 s** |
| **of the walk, PROVED** | segments [0, 640) of 11,303 — **5.66%** |
| **⇒ the whole 19-query walk, EXTRAPOLATED** | 839 × 75 s = **17.4 hours serial** |

⚑ **Segments [0, 640) contain query 0's ENTIRE walk** — its four mixed-height input openings, its
whole DEEP quotient, all sixteen fold layers with their four roll-ins, and its landing on the
committed final polynomial. So what is proved is not a prefix of a query; it is **one complete
query, end to end, braided to the AIR half**, plus the transcript and the permutation bridge that
the other eighteen share.

**The splice is refused, and every refusal is attributable.** Eight attempts in a process that
compiled only the spliced slice, against a predecessor proof another process made — at a cut the leg
**chooses and prints**:

a boundary unrelated to its predecessor · **the carried AIR accumulator bent** · a digest of an AIR
column chunk the slice never reads, bent · the same for a FRI lane chunk · a carried live lane bent ·
a Merkle sibling bent · **AIR slice 5's proof under AIR slice 5's own key** · the right proof under a
key it was not made under.

⚑ **"A cut that carries Merkle data" is NOT enough, and that was the rule this table used to state.**
What refuses a *bent* sibling is the assertion that CLOSES over it — the `cur == commitment` of that
sibling's own round — and it can be several cuts later. Corrected 2026-07-30: a cut can attribute the
bend iff it contains a closer for the **same** round or fold layer as its **first** aux-consuming
segment, **positioned after** it. Censused over the plan: **489 of 839 cuts carry a sibling and only
330 can attribute a bend in it.** The 48-slice run above lands on cut 47, which closes `cpRoot L15`,
so its sibling row did fire — but an 11-slice run lands on cut 10, which carries **96** sibling lanes
and closes nothing, where an accept is correct behaviour by the circuit. `[5]` is therefore
three-valued (refused / accepted / **NOT ATTRIBUTABLE**, with the reason) and floors the attributed
count, and `[2c]` publishes the census at tier 0. See `docs/MINA-GATE-TIERS.md`.

And the controls, which are what make those refusals mean anything. The same slice with the
boundary assertions removed **accepts** a public input unrelated to its predecessor and **accepts** a
bent digest of a chunk it never reads — so the bound refusals are the braid biting, not the work
breaking. Unbound **but pinned** still refuses the foreign proof; **unpinned accepts it** — so
side-loading's named hole is shown open and one constant shown closing it. ⚑ Side-loading makes
those controls strictly better than a fault injection: the key is an input, so the control refutes
the binding **on the bound chain's own proof objects**.

#### What is PROVED, and what is extrapolated

⚑ **The two are never the same sentence.** `FRIBRAID_LIMIT` says how many of the 839 slices a run
proves; the rest is a rate multiplied out, and it is labelled as one.

Every proved slice is its own `ZkProgram` compiled in its own process, taking its predecessor as a
side-loaded `DynamicProof` with the predecessor's verification-key hash pinned as a compile-time
constant — §3.27's mechanism, unchanged, extended by one link: **FRI slice 0's predecessor is AIR
slice 6**, so the object is ONE key-pinned chain and not two.

#### What the braided chain establishes — and what it does not

**It establishes**, at the resolution the artifacts support:

* the root's 1,093 AIR constraints fold, at the opened values under `dagDigest`, to an accumulator
  that IS the α-weighted sum of p3's own seven per-instance accumulators (§3.27);
* **those same opened values** — 47.0% of them literally the AIR's own lanes, a further 19.5%
  bridged by `permBind` — open under the four commitments dregg's transcript absorbed, at the 19
  query indices that transcript derived, through mixed-height `verify_batch` paths;
* their DEEP quotients fold through sixteen layers onto the committed final polynomial.

**It does not establish**:

* **that the committed function is low-degree.** That is the FRI soundness argument, and it is
  exactly as undischarged here as everywhere else in this tree. A verifier that runs every query
  correctly still inherits the FRI floor.
* ~~**that the challenger state entering FRI is the batch-STARK's.**~~ **CLOSED 2026-07-30 —
  §3.29.** It was a committed WITNESS emitted by the Rust side; it is now derived in circuit from
  the batch's own commitments, public values, cumulative sums and all 2,630 opened values, and a
  forged-but-consistent transcript is refused with the refusal attributable to an unsealed control.
  **1,373 permutations, 3,575,411 rows, +10.8% on the query-aligned walk.**
* **anything about all inputs.** Every figure here is `getRows()` on a committed circuit and a
  `prove()` that returned; "it proves on a box" is the resolution.
* **and nothing is wired to `setDreggRoot`.** `placeholderRelay` stays.

### 3.29 ⚑ MEASURED — THE PREAMBLE: the challenger state entering FRI, DERIVED

*2026-07-30. `bridge/mina-zkapp/src/RootFriWalk.ts` (`preambleOps`, the `preSeal` segment),
`src/RootFriSlice.ts` (the twin and the interpreter), `bridge/mina-zkapp/scripts/root-fri-preamble.ts`
(`npm run root-fri-preamble`). The script is read off `batch-stark/src/verifier/mod.rs:144,274-300`,
`batch-stark/src/transcript.rs` and `fri/src/two_adic_pcs.rs:782-788`.*

§3.28 ends by naming its own largest residual: *"the challenger state entering FRI is a committed
WITNESS … it is now the largest thing between this chain and a verifier."* This is that, closed.

**It is the same shape rung 6 closed one level down.** Before `DeepQuotient` the fold chain started
from a value the prover chose, and binding it is what turned the walk from *authenticates a number*
into *authenticates a claim*. A prover who picks the challenger state picks FRI's `α`, all 16 `β`s
and all 19 query indices, and the 11,303-segment walk then authenticates a transcript nobody forced.

#### What the state is a function of, from p3's own source

| | source |
|---|---|
| `observe_instance_count(7)` | Plonky3 upstream — the verifier module, mod.rs line 144 (not a path in this repo) |
| `observe_instance_binding(ext_db, base_db, width, n_chunks)` × 7 | `:274` |
| `observe_main(main_commit, public_values)` | `:278` |
| `observe_preprocessed(prep_widths, prep_commit)` | `:279` |
| `sample_perm_challenges` — 2 per **bus**, on first encounter | `:289`, `transcript.rs:84-99` |
| `observe_perm_and_sample_alpha(perm_commit, 64 cumulative sums)` | `:290` |
| `observe_quotient_commitment` | `:294` |
| `sample_zeta` | `:300` |
| all **2,630** opened values, in round / matrix / point order | `two_adic_pcs.rs:782-788` |

**10,993 ops, 1,373 permutations.** The out-of-circuit twin reproduces p3's own `α_stark`, its own
`ζ`, all 16 sponge lanes and **both buffers** exactly, and the 128 LogUp challenges it draws are the
ones the AIR half folds with.

⚑ **TWO READINGS THAT WOULD HAVE COMPILED AND PROVED CLEANLY**, and both are in the same function:

1. **The commitment-observe order is NOT the PCS round order.** The transcript absorbs **main,
   preprocessed, permutation, quotient**; `coms_to_verify` is built **main, quotient, preprocessed,
   permutation** — and *that* second order is the one the opened values are absorbed in.
2. **`observe_usize(v)` is FOUR elements, not one.** `observe_base_as_algebra_element::<EF>` lifts
   to the extension and absorbs `[v, 0, 0, 0]` (`challenger/src/lib.rs:141-147`). Reading it as one
   costs 14 permutations and every challenge after the first.

Eight discriminating polarities are kept as a live table, and **all eight land on a different
challenger state.** The last two — opened values in transcript order, and point-major within a round
— reach the *same* `ζ` and a *different* state, which is correct and is why the table checks the
state and not only the challenges.

#### What feeds it — and why this is a derivation and not a rehash

**Every non-literal input is already under a commitment the braid carries.** The public values are
`expose_claim|public[i]` and the 64 cumulative sums are `<table>|perm_value[i]` — both `dagDigest`
lanes the AIR half reads. The four round commitments are the `ft.inputCommit` lanes the walk's own
Merkle roots close against. The 2,630 opened values resolve through the same `OpenedPlan` the DEEP
quotient uses, **1,236 of them literally the AIR chain's own lanes.** There is no fresh witness
anywhere in the derivation. The batch's *shape* — instance count, degree bits, widths, chunk counts
— is absorbed as **literals**, so that part of the transcript is not reachable by a prover at all.

#### The teeth, and why they are local

A `preSeal` segment asserts the derived `ζ` **is** the point all 35 committed matrices were opened
at, and the derived LogUp challenges **are** the AIR chain's `challenge[k]`. Without it a bent input
produces a perfectly self-consistent *wrong* transcript whose first contradiction is a Merkle root
~12 slices later — which is exactly the failure mode §3.28 built the twin to avoid.

**The gate, four rows, every refusal a real constraint failure:**

| | slice | |
|---|---:|---|
| **BOUND** (seal armed) on the **forged** transcript | 88 | **REFUSED** |
| **UNSEALED** (seal removed) on the **same forged** transcript | 88 | ACCEPTED |
| **BOUND** (seal armed) on the **real** transcript | 88 | ACCEPTED |
| **UNBOUND** — the §3.28 walk — on a **forged challenger state** | 0 | ACCEPTED |

The forgery bends **one** absorbed AIR lane (`expose_claim|public[0]`, +1) and re-derives the whole
preamble honestly from it: a reachable state, a consistent `ζ`, consistent challenges. Nothing about
it is malformed. ⚑ **The unsealed control is segment-for-segment and row-for-row identical to the
bound walk** — only the closing equalities are gone — so the refusal is attributable to the binding
and not to shape. Row 4 exhibits the residual being closed rather than describing it.

#### The cost

| | |
|---|---:|
| preamble segments | **1,374** (1,373 permutations + the seal) |
| preamble modelled rows | **3,575,411** |
| 1,315 of those permutations | the opened-value absorb **alone** |
| the FRI transcript it authorises (§3.12) | 23 permutations — the preamble is **60×** what it authorises |

| at a 50,000-row budget | segments | rows | slices |
|---|---:|---:|---:|
| the §3.28 walk | 11,303 | 30,363,795 | 839 |
| with the preamble | 12,677 | 33,939,206 | 928 |

⚑ **PRICED AGAINST `bfdc935a5`, NOT AGAINST §3.28.** The 839 slices are 43 shapes repeated 19 times,
so query-aligned cuts give 820 instances from 46 distinct programs; §3.28's compile side was already
stale when it was written.

| query-aligned | head | block | **instances** | **programs** | rows |
|---|---:|---:|---:|---:|---:|
| without the preamble | 36 segs → 3 | 593 × 19 → 43 | **820** | **46** | 38,133,228 |
| with the preamble | 1,410 segs → 88 | 593 × 19 → 43 | **905** | **131** | 42,245,547 |
| delta | | | **+85** | **+85** | **+4,112,319 (+10.8%)** |

**The 19 query blocks are untouched** — the preamble is absorbed once, not once per query, so every
new slice is a head slice and `assertHomogeneous` still passes unchanged.

⚑ **AND THE NEW HEAD IS 13 STRUCTURAL SHAPES, NOT 88.** 1,315 of the 1,374 preamble segments —
**95.7%** — are one shape: a duplex absorbing eight opened values and sampling nothing. Those +85
compiles are the compressible part and are **not** compressed here: `assertHomogeneous` keys on a
per-query *lane shift* and the absorb block's reads are not a shift — they follow `OpenedPlan`,
which interleaves AIR-held and FRI-held values. That is named, not claimed.

**Proved, in its own process each:** slice 0, segments [0, 16) — **47,383** emitted rows against a
49,104 model, compiled, proved and verified in 115.1 s; slice 1, segments [16, 31) — **48,969**
against 49,987. The seal slice 88, segments [1373, 1385) — **53,165** against 48,252.

⚑ **ROW COUNT IS THE ONLY SIGNAL FOR "DERIVED, NOT WITNESSED".** A derived variable is
indistinguishable from a witness carrying its value to `runAndCheck`, `prove` **and** `getRows()`.
The unbound walk reaches this state in **zero** rows because it reads it; this one pays 3,575,411
modelled rows to compute it, and that delta is the claim.

**Ratcheted**: the rows at 2%, and **exactly** on the permutation count, the 2,630 opened values,
the 64 cumulative sums, the 25 public values, the 2 LogUp challenges and the 1,374 segments — those
are counts, not prices.

#### What this does NOT close, and what is now the largest gap

⚑ **CLOSED 2026-07-30 — §3.30.** The paragraph below stood for one day. The claim is now a public
output of the chain, sealed against the same `dagDigest` lanes this preamble absorbs, with a
forged-claim chain refused and the refusal attributable. Read on for what it was, then §3.30 for
what it is.

⚑ **THE CHAIN VERIFIES A PROOF AND NEVER SAYS WHAT THE PROOF CLAIMS.** Every statement in this
tower is relative to `dagDigest` and `friDigest` — digests of lane tables the prover supplies. The
AIR chain's slice 0 enters `stepBoundary(dagDigest, GENESIS_LIVE_DIGEST, 0)`, a genesis constant,
and the terminal seal is `terminalSeal(dagDigest, digest(acc), 7)`. Nothing in circuit names *which*
batch-STARK proof this is. A Mina-side verifier handed the whole 905-slice chain learns

> *some* batch of seven AIRs with these column digests has a FRI proof that verifies

and **not**

> dregg's root proof, for chain head H, over N turns, verifies.

**It is the same shape as the two this arc has already closed** — a value the prover chooses, feeding
everything downstream. First the fold chain's `initial` (§3.15), then the challenger state (here),
and now the *identity of the proof itself*.

**And the fix is one rung, not a research programme.** The root's claim is already in the lane
table: `expose_claim`'s **25 public values**, which this preamble now absorbs into the transcript —
`[digest₈][digest₈][3][digest₈]`, and the artifact's `numTurns` is 3. Closing it means carrying
those 25 lanes out as a public output of the chain, so the Mina side compares them against the root
it was told about rather than against nothing. Until then the tower is a verifier for an unnamed
proof, and `placeholderRelay` staying is the honest consequence rather than an oversight.

Smaller and still open, unchanged by this leg: the **192 LogUp constraints** are not in the DAG
vocabulary and the `C_i` extraction is a differentially-checked seam rather than a theorem (§3.18);
**19 queries, not 1**, though `bfdc935a5` makes that a compute residual rather than a structural one;
and the **FRI soundness floor**, undischarged here as everywhere.


### 3.30 ⚑ MEASURED — THE CLAIM: the chain says WHICH proof it verified

*2026-07-30. `bridge/mina-zkapp/src/RootClaim.ts`, the `claim` option on
`src/RootFriUniform.ts`'s `makeUniformSliceProgram`, `bridge/mina-zkapp/scripts/root-claim-carry.ts`
(`npm run root-claim-carry`). The layout is mirrored from
`circuit-prove/src/ivc_turn_chain.rs:268-278,343-368` and the Rust host's own segment tooth at
`:3096-3115`.*

§3.29 closed the challenger state and named what it did not close: *"the chain verifies a proof and
never says what the proof claims."* This is that, closed — **the third and last instance of one
shape.** A prover-chosen value feeding everything downstream: first the fold chain's `initial`
(§3.15, closed by the DEEP quotient binding), then the transcript (§3.29, closed by deriving it from
the batch's own commitments), now the **identity of the proof itself**.

#### What was actually missing

Not a binding of the claim to the proof — **the preamble already absorbs all 25 public values**, so
bending one moves `ζ` and §3.29's `preSeal` refuses. What was missing is the lanes coming **out**,
where a verifier can read them. Every public field the chain emitted was a `Field`: a boundary hash
over `Poseidon(dagDigest, friDigest)`, digests of lane tables the *prover* supplies.

#### Where the claim is, measured rather than assumed

`expose_claim`'s 25 public values **are** the chain claim — `[first_old8 ‖ last_new8 ‖ count ‖
acc_0..7]` (`ivc_turn_chain.rs:278`, `SEG_ANCHOR_WIDTH = SEG_DIGEST_WIDTH = 8`) — and the Rust host
compares exactly that vector against `[genesis_root8 ‖ final_root8 ‖ num_turns ‖ chain_digest]`.

On dregg's committed root proof: **AIR extension indices 1105..1177, stride 3** (they are *not*
contiguous — the legend interleaves them with `prep[]` and `main[]`), **lanes 4420..4708**, spanning
**AIR chunks 17 and 18**.

#### The differential, against three independent oracles

| | |
|---|---|
| all 25 lanes = the proof's own `expose_claim` `public_values` | **oracle 1** |
| `numTurns` decodes to **3** = the artifact's own top-level `numTurns` | **oracle 2 — outside the assignment** |
| the preamble absorbs **exactly** these 25 | **oracle 3** |
| limbs 1..3 are zero in all 25 — a public value **is** a base element | |
| all 25 canonical, so the octet packing is injective | |
| the 4-field packing round-trips to all 25 lanes | |
| the chunk accessor and the flat lane table agree on all 25 | |

Oracle 2 is the one that matters: `numTurns` is recorded at the top of the artifact, **outside** the
column assignment the claim is read from, so the decode is checked against something that is not
itself.

⚑ **EIGHT DISCRIMINATING POLARITIES, and two of them leave `numTurns` at 3.** That is why every row
of the table is signed on all four fields rather than on the count:

| the misreading | it decodes to |
|---|---|
| the AIR index read as a **lane** index (`at`, not `4·at`) | turns 1284447546 |
| the **pre-lift** 4-lane anchor width (`SEG_ANCHOR_WIDTH` *was* 4) | turns 1139774588 |
| the 25 public columns as **contiguous** indices | turns 1885745139 |
| `count` **last** | turns 1659981296 |
| the two anchors **swapped** | turns 3, `finalRoot` moves |
| **positional** packing — `packLanes` over the flat 25 | turns 3759344820… |
| an octet packed **most-significant lane first** | turns 3, `finalRoot` moves |
| read off the `Public` table | **unresolved** |

The pre-lift width is not invented: the FAITHFUL-FLOOR lift widened the anchors from 4 lanes
(~62-bit birthday) to 8, so anyone working from the older record decodes a claim and gets a
different one.

#### What comes out, and why it is not a fresh witness

The public output is `ClaimedBoundary { boundary, claim }`. `boundary` is byte-for-byte §3.29's
field; `claim` is four Pasta fields — `genesisRoot`, `finalRoot`, `numTurns`, `chainDigest` — three
of them a BabyBear octet packed at 31 bits a lane (248 of 254) and one a small integer a verifier
reads directly.

⚑ **PACKED PER NAMED BLOCK, NOT POSITIONALLY.** `packLanes` over the flat 25 cuts at 0-7 / 8-15 /
16-23 / 24, and its third field straddles `num_turns` and seven digest lanes — a field with no name,
for the same four fields.

⚑ **AND THE CLAIM IS NOT WITNESSED.** `readClaimLanes` resolves the 25 lanes out of the **same
loaded AIR chunks** whose digests were just spliced into `dagDigest`, which
`Poseidon(dagDigest, friDigest) == publicInput` already pins. Replacing one prover-chosen value with
another would have been this campaign's failure mode rather than its fix.

#### Where the seal goes — found, not chosen

The 25 lanes span AIR chunks 17 and 18, and **head slice 1 (segments [17, 32)) already loads
[17, 18, 20, 21]**. So the seal costs **zero extra chunk loads**, the planner's carry does not move,
and the plan is unchanged. Every other slice only propagates.

#### The two equalities, and why only one of them costs rows

| | emitted rows |
|---|---:|
| the **seal** — `claim` **is** the lanes under `dagDigest`, on one slice | **+185** |
| of which the read, the packing and the range checks | +162 |
| of which the **four closing equalities** | **+23** |
| the **carry** — `claim` equals its predecessor's, on each of the other 904 | **+0** |
| the whole chain, on 42,245,547 | **+185 — 0.0004%** |

⚑ **ZERO IS NOT AN ABSENCE, AND THIS IS THE PLACE THAT MISREADS.** An equality between two *witness*
variables compiles to a Kimchi **copy constraint**: the permutation argument enforces it and no gate
row is emitted. So the carry is free **and** enforced, and the row count is silent about which.
§3.29's own rule — *"row count is the only signal for derived, not witnessed"* — **does not transfer
here**, and the accept/refuse table below is the only thing in the leg that says the carry bites.

**Measured on the deployed program, not only on a probe:**
`dregg-root-fri-head1-CLAIM` emits **51,091** rows against **50,906** for the same position without
the claim (measured in a child process — one `DynamicProof` class per process, and the two variants
carry different public-output types). +185, the same figure the standalone probe pair gives.

#### The gate, five rows, every refusal a real constraint failure

| | | |
|---|---|---|
| **BOUND** (seal armed) on the **forged claim** | head 1 | **REFUSED** |
| **UNSEALED** (seal removed) on the **same forged claim** | head 1 | ACCEPTED |
| **BOUND** (seal armed) on the **real claim** | head 1 | ACCEPTED |
| **UNBOUND** — the §3.29 chain — on the **forged claim** | head 1 | ACCEPTED |
| **CARRY** — claim ≠ **predecessor's** claim, seal removed | head 1 | **REFUSED** |

⚑ **THE LANE TABLE IS UNTOUCHED.** Bending an `expose_claim` lane moves `ζ` and §3.29's preamble
seal refuses — that hole is already closed. This forgery leaves every committed lane exactly as
dregg emitted it, so every Merkle root, every DEEP quotient, every fold and the preamble seal itself
still pass, and lies **only** about what the proof is *of*. Today that is not even a lie, because
the chain says nothing.

⚑ **ROW 4 IS A MEASUREMENT, NOT A TAUTOLOGY.** The §3.29 chain's public output is **identical**
under the real claim and the forged one — checked, field for field — and the claim-carrying output
**differs**. That is the gap exhibited rather than described.

⚑ **ROW 5 EXISTS BECAUSE THE CARRY COSTS NOTHING.** Row 2 is its control: same mode, same reads,
same rows, `prev == claim`. And the harness's own first version compared the claim **against
itself** — a tautology that passes for every input and would have reported the carry as gated while
nothing gated it.

#### What a Mina-side verifier now learns, and what it still does not

> **dregg's root proof — genesis root `G`, final root `H`, over `N` turns, with ordered-history
> commitment `D` — has a batch-STARK whose seven AIRs' closing equalities hold at values dregg
> committed to, and whose FRI walk over those commitments verifies at a transcript derived from the
> batch itself.**

with `G`, `H`, `N`, `D` read off the terminal proof rather than supplied to it.

**What it still does not:**

1. **That the committed function is low-degree.** The FRI soundness argument is exactly as
   undischarged here as everywhere else in this tree.
2. **That `(G, H, N, D)` is the chain head Mina should care about.** Nothing is wired to
   `setDreggRoot`; `placeholderRelay` stays. The chain now *states* a claim a relay could compare
   against the root it was told about — comparing it is a separate rung.
3. **That the 25 lanes are what the AIR's `expose_claim` constraints force.** The AIR half proves
   the closing equalities hold at the opened values; that `public[i]` *is* the fold of the real wide
   descriptor leaves is the Rust host's tooth (`ivc_turn_chain.rs:3096-3115`), not this chain's.
4. **The 192 LogUp constraints** are still not in the DAG vocabulary and the `C_i` extraction is
   still a differentially-checked seam (§3.18).

**BREAKING.** The public output type changes from `Field` to `ClaimedBoundary`, so **every
verification key in the chain changes and the whole 131-key list re-emits.** The `DynamicProof`
predecessor class takes a `withClaim` parameter because head slice 0's predecessor is the AIR chain
and still emits a plain `Field`. With `claim` absent the program is byte-identical to §3.29's, which
is what makes row 4 of the gate buildable.

**Ratcheted**: the rows at 2%, and **exactly** on the 25 lanes, the stride of 3, the chunks
`[17,18]`, the binding head slice 1, `numTurns = 3`, and 905 instances / 131 programs.



---

### 3.31 ⚑ THE HASH IS A PARAMETER — and the residual list, re-stated with that pulled

*2026-07-30. `src/HashSuiteType.ts`, `src/HashSuites.ts`, `src/PastaMmcs.ts`,
`src/PastaChallenger.ts`; `npm run pasta-differential`, `npm run pasta-verify`,
`npm run pasta-root-rows`, `npm run pasta-chain`. The full account is
`MINA-FACING-TERMINAL-OPTIONS.md` §0.2.*

`DreggProofVerify`'s walk now takes a `HashSuite` and a real proof minted under
`DreggMinaConfig` is consumed, **proved and verified**, with seven bends refused
and a five-step chain whose splices are refused in a fresh process from
serialised bytes. **17.2×** fewer rows than the same statement under the deployed
hash — and 145,323 rows does not fit a Pickles step while 8,445 does.

**Measured at the root's geometry: 2.906 × 10⁶ rows = 54 slices**, against the
2.85 × 10⁶ / 53 projection (+2.0%). **The shape has flipped**: hashing was 89% of
this budget and is **7.4%**; the DEEP quotient was 10% and is **86.0%**.

#### What that does to the list above

| row | then | now |
|---|---|---|
| the hash | the dominant term, and every other lever was priced against it | **7.4%.** A **3× error in every measured Pasta unit price is worth 7 slices.** It is no longer a lever. |
| the FRI knobs (§6, ember-gated) | worth ~35% | worth **~1%** — and still rotates the apex VK. Do not. |
| the compile lever (§5.1) | 839 → 46 keys, the cheapest real win | still real, still orthogonal, and now **second-order against the columns** |
| **column narrowing** | "then, and only then" | ⚑ **THE LEVER.** 2.50 × 10⁶ rows over ~2,342 opened values at ζ = **1,067 rows per opened value**. Halving the root's committed column count is **54 slices → 31.** |

#### ⚑ THE LARGEST REMAINING GAP — ✅ CLOSED ON THE CONSUMER SIDE, 2026-07-30

*See §3.32. `verifyPlan`'s `nBatches !== 2` throw is gone, the consumer takes
dregg's committed four-round root at either hash, and the answer is MEASURED at
**61 Pasta slices** rather than projected at 54. The paragraphs below are the gap
as it stood; the half that is still open is named at the end of §3.32.*

**The two halves of "Mina verifies dregg" are each missing what the other has.**

- `DreggProofVerify` + `DreggProofSchedule` consume a **real emitted proof end to
  end** — transcript derived, DEEP quotient computed, AIR closing equality
  checked, chain proved, splices refused — and are now **hash-agnostic**. But
  `verifyPlan` **throws on `nBatches !== 2`**: it wires the trace round and the
  quotient round only, and a preprocessed or permutation round has point wiring
  that is neither shape. **The root has four.**
- `RootFriSlice` / `RootFriUniform` run at the root's **real four-round
  geometry** (§3.28, §5.1a — 839 compiles collapsed to 46 keys). But they
  hard-code `compressBB` / `condSwap` / `provablePermBounded`: they are
  **Poseidon2-BabyBear**, and `RootFriWalk`'s `PRICE` is `priceAt(BABYBEAR_HASH)`
  while `PASTA_HASH` sits in `CostModel.ts` used by nothing but a comment.

So the verifier that consumes a proof cannot be pointed at the root's shape, and
the walk at the root's shape does not consume a proof and does not hash natively.
**Neither half is both, and closing it is engineering rather than research:**
`RootFriSlice` takes the same `HashSuite` parameter `commitPhaseRound` already
takes, and `verifyPlan`'s two-batch refusal becomes per-round point wiring.

### 3.32 ⚑ THE CONSUMER TAKES THE REAL ROOT — four rounds, five heights, both hashes, MEASURED

*2026-07-30. `src/RootConsume.ts`, `src/DreggProofVerify.ts`;
`npm run root-consume-differential` (tier 0, 4.7 s) and `npm run root-consume-rows`
(tier 1). Commits `a78740745`, `2fa1234a8`.*

`verifyPlan` no longer refuses a third PCS round. The wiring that made the
refusal correct — *"batch 0 is the trace, everything else is a quotient chunk"* —
is deleted rather than widened: `MatrixShape.pointScales` declares the constant
multiples of ζ each matrix opens at, and `runQueryInputAndDeep` implements
`MerkleTreeMmcs::verify_batch` over **mixed heights**, sponging the tallest
matrices' rows into the leaf and compressing each shorter matrix's row digest in
at the level its padded height names. A single-height batch degenerates to the
flat path the two-round fixture always walked, which is why **no measured
BabyBear row count moves** (`npm run schedule` 14/14 recorded figures unchanged;
`dregg-verify` 56,927 / 827,887 unchanged).

**THE OUT-OF-CIRCUIT DIFFERENTIAL RAN FIRST**, as everything that has found a
defect in this arc did. On `.fullchain/real-root-fri.json`, in 4.7 seconds,
nothing compiled: 4 rounds, 35 matrices, heights [22, 21, 16, 9, 6], census
**2,630**; all **76** input-phase openings (19 queries × 4 rounds, 1,672 Merkle
levels, 76 leaf sponges + 304 injected sponges) reproduce the commitments p3
emitted; all 95 reduced openings and all 304 commit-phase openings reproduce
p3's; the roll-in schedule DERIVED from the heights is the emitted [0, 5, 12, 15].

Four bends, each **REFUSED at all 76 openings**: no injection at all (the
two-round reading); the injection compressed the other way round; every injection
one level late; the leaf sponged over the whole batch row. A fifth — the level's
index bits taken from the global max height — is **NOT ATTRIBUTABLE**, with its
reason: every round tops out at the global max height, so the bend is a no-op.

⚑ **And the instance that opens at ζ TWICE.** Instance 6 sits at `degree_bits =
0`, so its next-row point is `ζ·g_0 = ζ`. Its permutation matrix opens at ζ twice
and both points are wired to distinct opened-value runs; a wiring that deduped
equal points would drop **100 DEEP terms** and still produce a number.

#### The measurement

| | deployed hash | Pasta hash |
|---|---:|---:|
| input phase, one query | 759,797 | **4,171** |
| DEEP quotient, one query | 161,312 | **161,313** |
| fold chain, one query | 615,929 | **6,258** |
| ×19 + the once-per-proof term | 29,234,449 | **3,293,825** |
| **slices @ 54,300** | **539** | **61** |

**8.9× measured**, at the root's real geometry; the input phase alone is 182×.
The DEEP quotient agrees to **one row** between the hashes, which is what "no
hash choice touches it" means once it is measured. And the disagreement with the
projection is attributed by segment class rather than reported as a mood: the
**input** term is −65.7% (the `witnessLane` conservatism `cost-model-gate`
names), the **DEEP** term −21.5% (which it does not). The gate sizes its own
margin at "~2%"; end to end it is **23%**, in the safe direction.

**PROVED on the real object**: the four-round Pasta input phase over 7 of the 19
real queries, 48,224 rows = 88.8% of the measured ceiling, compiled 25.8 s,
proved 11.2 s, verified, public output the 7 DERIVED query indices. Three bends
refused — a bent opened row lane, a bent path sibling **at an injection level**,
and query 0 re-declaring itself as query 1 — with the honest object still proving
after all three.

#### ⚑ A DEFECT NOTHING COULD HAVE FOUND BEFORE THIS MERGE

A `ZkProgram` whose whole body is eight `assertLt2p31` calls on honest in-range
lanes **compiles, analyses (21 rows), passes `runAndCheck`** — and dies in
`prove()`:

```
Error: the lookup failed to find a match in the table: row=16
```

kimchi installs the fixed 12-bit table only for a circuit that also carries a
`RangeCheck0`, and `Gadgets.rangeCheck3x12` emits none. Every Pasta circuit in
this tree also ran BabyBear extension arithmetic, whose `quotientTimesP` calls
`rangeCheck64` — so **the deployed hash was installing the Mina-native hash's
lookup table**, and the dependency was invisible for exactly as long as nobody
built a Pasta-only body. The four-round merge is the first thing that can: a
Pickles step holding only mixed-height MMCS openings has no BabyBear arithmetic
in it at all.

The fix is `MerkleSuite.anchorLookupTable` — absent for BabyBear, one
`RangeCheck0` for Pasta — and the falsifier is `root-consume-rows` [4], which
proves the anchored body and **requires the bare one to fail with that exact
error**, so the anchor cannot become a dead no-op.

#### What is still missing from which half

`RootFriWalk.priceForSuite` closes the pricing half: the real-geometry model can
now be costed at either hash, importing `CostModel`'s constants rather than
re-deriving them, and refusing an unknown suite by name.

⚠ **Pricing is not execution, and this is the open item.** `RootFriSlice`'s
segment executor still calls `compressBB` / `condSwap` directly and its state
slots are eight lanes wide (`LANES_PER_DIGEST`), so the **sliced** chain — the
braid and the uniform walk — runs the deployed hash whatever `priceForSuite`
returns. The path that is both four-round and hash-agnostic is the **consumer**,
and that is what §3.32 measures. Making the slice executor's digest width a
function of the suite is the remaining engineering.

#### The other residuals, unchanged by this work and named so they are not read as closed

1. **Three objects, one measured.** The 54 slices price a **Pasta-hashed root**.
   The proof actually consumed is a small `DreggMinaConfig` **fixture**. The
   third — the real **Mina terminal** (`mina_terminal_tooth.rs`: a real apex
   shrunk under `DreggMinaConfig`, log_blowup 3, 38 queries) — **has never been
   priced on the Mina side at all.** Its `degree_bits` are far below the root's
   2^22, so it is plausibly the cheapest of the three and it is the next
   measurement worth taking.
2. **The AIR is still a parameter** (§3.18): 901 of 1,093 base constraints
   compile from the DAG, the **192 LogUp constraints are not in that
   vocabulary**, the extraction is a differentially-checked **seam** and not a
   theorem, and the Lean accumulator is not welded to `AirEval.ts`'s closing
   equality. The AIR term in the 2.906 × 10⁶ is §3's figure for an object that
   is only partly built.
3. **Leaf lanes are bounded `< 2^31`, not `< p_BabyBear`** — inherited from the
   deployed path, not introduced. Stated precisely rather than as a scare: a
   non-canonical lane packs to a **different** Pasta element, so it fails the
   Merkle check rather than being accepted. It is a completeness wart. The
   **challenger squeeze does not inherit it** — `assertCanonicalBb` makes every
   squeezed limb canonical, because there a non-canonical limb *would* be a hole
   with teeth.
4. **The Pasta ROM idealization is unconnected.** It is named on the Pickles side
   (`PicklesTranscriptBinding`'s `SpongeKeyedROFaithful`) and points at none of
   the FRI/MMCS carrier sites the way `Poseidon2RomInstantiation` points at the
   BabyBear ones. An unconnected leg, not a hole — and the hash swap moved the
   carrier without moving the leg.
5. **Nothing wires any of this to the governance-pinned dregg root.**
   `setDreggRoot` is untouched and `placeholderRelay` stands. The chain's
   terminal seal says *"I verified the proof with this `rootCommitDigest`"*; it
   does not say that digest is dregg's.
6. **The FRI/STARK floor is undischarged**, as everywhere. A Kimchi proof that a
   FRI verifier accepted is not a proof that the committed function is low
   degree.

---

### 3.33 ⚑ THE HASH IS THE WALK'S SHAPE — and the sliced chain's blocker is the TRANSCRIPT, not the digest width

*2026-07-30. `src/RootFriWalk.ts` §1a, `src/HashSuiteType.ts`, `src/Poseidon2Merkle.ts`,
`src/PastaMmcs.ts`, `src/RootFriSlice.ts`, `src/RootFriUniform.ts`. Commits `557ac33fd`,
`39d68ee84`. Tier 0 throughout; nothing here compiled a chain.*

§3.32 named the remaining engineering as *"making the slice executor's digest width a function of
the suite."* That is done. Doing it found that the digest width was not the blocker.

**`WalkHash` is the structural half of a hash choice**, beside `WalkPrice`'s cost half: digest
lanes, leaf-sponge rate, leaf-sponge state width, challenger state width, challenger absorb rate,
challenger squeeze count. Those reach the **lane table** (a commitment is `digestLanes` lanes, not
eight), the **slot layout** (`cur`, `inj`, `sponge`, `chal`), the **segment list**
(`ceil(w / spongeRate)` sponge blocks), the **aux widths** and the **executor**. A price table can
move none of them, which is exactly the gap `priceForSuite` left. `SegmentedWalk` now *carries* its
hash, so `segmentReads`, `auxLanes`, `runSegments` and the uniform planner cannot drift from the
table they were built against; `assertWalkHashMatchesSuite` requires the record and the suite to
agree on all four shared numbers.

`MerkleSuite.spongeStream` is new: the leaf sponge as a **streaming** machine, because the sliced
walk cannot use the whole-row `sponge` — an opened row is up to 452 lanes and the sponge over it
crosses cuts. `RootFriSlice`'s `inBlock` *was* that machine, hand-written at one hash; it is lifted
out gate for gate and implemented for both suites. `compressBB` / `condSwap` / `BbDigest` /
`DIGEST_ELEMS` / `assertDigestInRange` are gone from the executor.

#### ⚑ TWO REFUSALS, AND THEY ARE THE FINDING

**1. `segmentWalk` refuses a hash whose TRANSCRIPT it does not model.** The Merkle half of a hash
swap is a substitution. The transcript half is a different *state machine*:
`MultiField32Challenger` packs eight BabyBear lanes into a Pasta cell to absorb, splits a cell into
seven canonical limbs to squeeze, absorbs a digest **natively** after flushing the pending base
buffer, tags the capacity with a length, and pops its queue **from the back**. `challengerRun` emits
none of that.

⚠ **And there is no oracle for it.** `RootConsume.rehash` re-commits the root's MMCS digests under a
suite — so the Merkle half of a Pasta walk *has* a twin to check against — but it does **not**
re-derive the transcript, and `ROOT_CHALLENGE_STATUS` says the root path **carries** its challenges.
dregg mints no Pasta-hashed root. A Pasta preamble written today would compile, prove, and be about
a protocol nobody runs — which is the exact shape this directory's record says its cheap
differentials keep catching. So it refuses by name instead.

**2. `assertLanesAreBabyBear` refuses to COMMIT a non-eight-lane walk.** The lane table is committed
with `canonicalLane(l, 2^31 − 1)` on **every** lane. Under Pasta the four round commitments, the
sixteen commit-phase commitments and the challenger state are **native Pasta elements** in that same
space, and canonicalising one to `< p_BabyBear` refuses every honest proof. The lane table needs a
per-lane **kind**. That would have been invisible until a Pasta chain failed to prove, so removing
the first blocker cannot silently expose the second.

**`priceOnly` names the hybrid.** Pricing a BabyBear-shaped walk at Pasta unit prices is §3.31's
`2.906 × 10⁶ rows = 54 slices` and is a legitimate **projection**; passing a price whose sponge rate
disagrees with the shape without saying so is now refused, and `SegmentedWalk.priced` carries
`'shaped' | 'price-only'` so a report cannot lose the distinction.

#### ⚑ THE ROW CHANGE NO MODEL FIGURE COULD SEE

`MerkleSuite` has two leaf hashes and the commit-phase leaf reached for the wrong one. Measured with
`Provable.constraintSystem`, no compile:

| body | rows |
|---|---:|
| `cpLeaf`, the inline predecessor | 2,648 |
| `cpLeaf`, `spongeStream` | **2,648 — identical** |
| `cpLeaf`, the one-shot `sponge` | 2,616 — **−32** |
| `inBlock`, inline vs `spongeStream` | 2,666 / **2,666** |

The one-shot BabyBear sponge reduces only the eight lanes it *returns*; the streaming form reduces
all sixteen, because its state crosses a boundary. So `sponge` would have dropped 32 rows on each of
the **304** commit-phase leaves — **9,728 emitted rows** — while the model prices a leaf at `P.perm`
either way and **every tier-0 figure stayed exactly where it was**. A refactor whose only instrument
is the model, changing the thing the model does not price; the row count would first have moved at
the compile the coordinator was told to run once.

**Nothing moved on the deployed path**, re-checked at tier 0 after each commit: braid 11,303
segments / 30,363,795 work rows / 839 slices / cut census 489-330-0-11; uniform 820 / 46 /
38,133,228; preamble 905 / 131 / 42,245,547 and all eight discriminating polarities. The twin still
derives p3's own α, all 16 βs and all 19 query indices and reproduces all 76 input openings, all 95
reduced openings and all 304 fold steps.

---

### 3.34 ⚑ THE COLUMN LEVER, MEASURED — and the number three documents quote for it is 39% low

*2026-07-30. `bridge/mina-zkapp/scripts/deep-column-census.ts`, `npm run deep-columns` — tier 0, 0.2 s, nothing
compiles. Commit `bb991153c`.*

§3.31 names one lever and prices it at *"2.50 × 10⁶ rows over ~2,342 opened values at ζ = 1,067 rows
per opened value; halving the root's committed column count is 54 slices → 31."* Three things come
out different when it is re-derived from the owner rather than quoted.

**1. The unit price is 1,484, not 1,067 (+39%).** From `ARITH_PRICE`, which is the registered owner:
per column `horner 49 + 4 × witnessLane 6.50 = 75.00`; per close
`extInverse 88 + 2 × extMul 31 + extAdd 19 = 169`, × 48 (matrix, point) pairs; per query
`2,630 × 75 + 48 × 169 + 20 = 205,382`; × 19 queries = **3,902,258 rows**. The 1,067 is
`2.5 × 10⁶ / 2,342`, two literals in `bridge/mina-zkapp/scripts/pasta-root-rows.ts`, and **2,342 is the retired flat
census** — 2,286 plus the 56 quotient openings counted twice — which `CostModel.RETIRED_FLAT_MODEL`
already documents as wrong. ⚑ The direction matters: **the lever is bigger than advertised.**

**2. "86% of the budget" is the WORK-ONLY share, and a sliced chain is not work-only.** At the Pasta
price the walk with the preamble is 4,316,316 work rows with DEEP at **90.4%** — but `planFriWalk`
at the 50,000-row budget adds **5,165,797 rows of carry**, and carry is **hash-independent**.
Against work + carry the DEEP share is **41.2%** and the chain is **218 slices**, not 54. A lever
priced against the work share is priced against the wrong denominator for the only kind of chain
this directory builds.

**3. The answer is per-INSTANCE, and it is one table.**

| instance | LDE rows | main | quot | prep | perm | total | share |
|---|---:|---:|---:|---:|---:|---:|---:|
| `poseidon2_perm/baby_bear_d4_w24` | **512** | 904 | 8 | 72 | 88 | **1,072** | **40.8%** |
| `poseidon2_perm/baby_bear_d4_w16` | 2,097,152 | 600 | 8 | 48 | 56 | 712 | 27.1% |
| `Alu` | 4,194,304 | 152 | 8 | 118 | 144 | 422 | 16.0% |
| `expose_claim` | 64 | 100 | 8 | 50 | 200 | 358 | 13.6% |
| `Const` / `Public` / `recompose` | | 4 | 8 | 2 | 8 | 22 each | 2.5% |

⚑ **A DEEP term is priced per opened value and is INDEPENDENT OF HEIGHT.** One Horner step, four
witnessed lanes. So an 8-trace-row, 452-column matrix is priced identically to a four-million-row
one — and after the hash swap, height is what the *Merkle path* costs while width is the *whole
budget*. **The widest table in the batch is the shortest one**, and it exists as an **isolation**
device: a second Poseidon2 op-type so the IVC segment-digest sponge shares no chain-state, CTL bus
or CSE collapse with the FRI challenger's W16 perm. That is a **distinctness** requirement, not a
width-24 one.

| lever | census | Δ | DEEP rows |
|---|---:|---:|---:|
| **baseline** (dregg's committed root) | 2,630 | | 3,902,258 |
| **A.** merge the w24 op-type into w16 | **1,558** | **−1,072** | 2,348,894 |
| **A′.** the same instance at W16 widths, not deleted | 2,270 | −360 | 3,389,258 |
| **B.** `expose_claim` as 25 rows × 1 lane, not 1 × 25 | 2,296 | −334 | 3,426,308 |
| **C.** `alu_lanes` 4 → 1 | 2,360 | −270 | 3,517,508 |
| **D.** max constraint degree 3 → 2 | 2,602 | −28 | 3,839,881 |
| **E.** batch LogUp to one running sum per instance | 2,174 | −456 | 3,252,458 |
| **A + B + C** | **1,224 (46.5%)** | **−1,406** | **1,872,944** |

**A + B + C is past the halving §3.31 asked for, and none of the three is a hash change, a FRI-knob
change or an upstream-fork change. All three are dregg-side AIR layout.**

**Where it cannot be cut — with the number, so the question closes rather than hopes:**

- the **quotient round is 56 of 2,630 (2.1%)**; width is `D = 4` per chunk and the chunk count is
  `2^log2_ceil(maxDegree − 1) = 2`. Best case **28 terms (1.1%)**, and it costs every AIR a degree.
- the **permutation round is 512 (19.5%)**, forced by 64 LogUp interactions, forced by
  `permutation_width = contexts.len()`. There is **no batch parameter in p3-lookup** at the pinned
  rev — lever E is a change to the **upstream fork**, not a knob.
- **`p2_w16`'s 600 main terms (22.8%)** are the Poseidon2-w16 round schedule itself
  (`W(1 + 2·HF·(SR+1)) + PR·(SR+1) + 2 = 300`). Narrowing it means changing the hash the root
  commits with, which **rotates the apex VK**. Not this lane's to turn.

---

### 3.35 ⚑ BUILD REQUEST — the one expensive run, what it costs, and what it produces

**Compile the claim-carrying uniform chain: 131 programs, one process each, into
`.fullchain/uniform-claim`. Then `npm run head-anchor-pins -- --emit`.**

#### The shape, re-planned and re-priced on the code as it now stands

Reproduced at tier 0 after every commit above (`npm run root-fri-preamble`, `npm run
root-fri-uniform`, `npm run head-anchor-pins`):

| | |
|---|---:|
| walk | 12,677 segments (1,374 preamble + 11,303) |
| uniform layout | 1,410 head segments, then 19 blocks of 593 |
| **slice instances** | **905** (88 head + 19 × 43 block) |
| **distinct programs / keys** | **131** |
| chain length | 905 uniform + 7 AIR = **912 steps** — the `totalSteps` pin |
| modelled rows | **42,245,547** (of which the claim is +185, 0.0004%) |
| per-instance budget | 50,000; mean 46,681 |
| terminal | `block42`, key-tree leaf 130, `VK_TREE_DEPTH = 7` |
| claim | 25 lanes, AIR chunks `[17, 18]`, binding head slice 1 |
| genesis anchor | `0x7393bc8b02186f4b83317f9d622429c3b51bf90e91d883409e60895ae4abbc` |

#### What it costs

The only measured per-slice figures on real bodies of this size class are §3.28's: **48 FRI slices,
compile 2,621 s and prove 960 s** — **54.6 s to compile, 20.0 s to prove**, per slice, at ~47k rows.
§3.29's head slice 0 (47,383 rows, with the preamble) **compiled, proved and verified in 115.1 s**.

- **The compile run: 131 × 54.6 s ≈ 7,150 s ≈ 2.0 hours serial**, and it is **embarrassingly
  parallel** — 131 independent processes, no ordering, `Cache.None`, `--max-old-space-size=16384`
  each. Wall clock is a function of how many fit in RAM at once.
- **The proving run is a different object and is NOT this request.** 905 instances, strictly
  sequential (instance `k+1` consumes instance `k`'s proof). One process per program holding its key
  and serving its 19 instances gives `131 × 54.6 + 905 × 20.0 ≈ 7.0 hours`; the naive one process
  per instance gives `905 × 75 s ≈ 18.9 hours`. Either way it is gated on the compile, so the
  compile is the thing to spend now.

#### What it produces

1. `.fullchain/uniform-claim/key-<name>.json` × **131** — the verification-key list. `head-anchor-pins`
   refuses a partial directory and says which shape it found; `.fullchain/uniform`'s existing 46 keys
   are **not** the answer (they are the §3.29 chain: `publicOutput: Field`, no claim, no preamble —
   §3.30 changed the public output type, so every key changed).
2. `dregg-chain-pins.json` — `terminalVkHash`, `chainVkRoot`, `totalSteps = 912`, `genesisRoot`.
   These are the four constants `DreggHeadGate` bakes into its own verification key and refuses to
   exist without.
3. The **one currently NOT-ATTRIBUTABLE row in `npm run head-anchor`** — *"dregg's REAL terminal
   proof is accepted by `advanceHead`"* — becomes runnable. It is the only row in that leg whose
   reason is an absent artifact rather than a property.

#### What would make us do it again — say it before spending it, not after

- **Any change to a slice's public output type or to the boundary algebra.** §3.30 moved `Field` →
  `ClaimedBoundary` and every one of the 131 keys changed. There is no partial re-emit.
- **Any change to the plan's cut points** — the budget, `CLAIM_CHUNK`, `assertHomogeneous`'s
  grouping, or `UNIFORM_OVERHEAD_ROWS`. `head-anchor-pins` refuses a plan that is not 905 / 131.
- **Any emitted-row change inside a slice body**, because the plan is budgeted at 50,000 and a body
  that crosses it re-cuts the chain. §3.33's 9,728-row near-miss is exactly this.
- **A hash swap**, once the two refusals in §3.33 are cleared. A Pasta-shaped walk has a different
  lane table, different slot widths and a different segment count, so it is a different 131.
- **Any of §3.34's column levers landing**, since each re-mints the root and re-shapes the walk.

⚑ **AND WHAT THIS COMPILE DOES NOT BUY, so it is not read as more than it is.** It produces a KEY
LIST. It does not prove the chain, it does not verify dregg's root on Mina, and it does not wire
anything to `setDreggRoot` — `placeholderRelay` stands. Every residual in §3.32 is untouched by it.

#### Which guarantees the run must RE-CONFIRM, because tier 0 cannot

Three of the five survive the re-shaping at tier 0 and were re-run on this checkout after every
commit above. Two are compile-gated and **must not be assumed to transfer**:

| guarantee | status |
|---|---|
| `k` / `q` bound so double-count and skip are impossible | ✅ tier 0 — `root-fri-uniform` [3b], all **820** boundaries out of circuit, both joins the deployed chain does not have |
| the challenger **derived**, not witnessed | ✅ tier 0 — `root-fri-preamble` [2], all **8** discriminating polarities land on a different challenger state, and the seal holds against all 35 matrices and 128 challenge lanes |
| the anchor's terminal seal pins chain **LENGTH** | ✅ tier 0 — `head-anchor` [1], **all four** preimage slots move the seal; the key-list root and the length both bite |
| **15/15 splices refused with four attributable controls** | ⚠ **COMPILE-GATED.** Tier 0 gives only the plan-level precondition (the cut-rule census: 489 cuts carry a sibling, **330** can attribute, 0 `block9`-shaped, first at cut 11). The refusals themselves need proofs from other processes. |
| **the claim carried as public output** | ⚠ **COMPILE-GATED.** `root-claim-carry` [4b]/[5] — the +185-row seal on the deployed program and the five-row forgery table, of which the CARRY row emits **zero** rows and is the only thing that says the carry bites. |

⚑ `root-claim-carry` is **not tier-aware** — it compiles regardless of `MINA_TIER`. That is a real
gap in the tier discipline and is named here rather than worked around.

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

⚑ **THIS TABLE'S PREMISE IS FALSE, MEASURED (§3.26) — IT IS NOT THAT A ROW IS TOO GENEROUS.**
The `max_proofs_verified = 1` row is too generous by **1.40×**: narrowed on the real object, the
overhead is **11,160–11,236**, not ~8,000, so the usable budget is **54,300** and not 57,532. Every
step count computed against 57,532 — §3.23's included — is optimistic by that gap. **But the deeper
problem is the column heading.** A per-`max_proofs_verified` "usable of 65,536" is a constant good
for any circuit, and there is no such constant: a **63,300-row** branch of one shape COMPILES where
a **57,769-row** branch of the *same program shape* built from a different gate mix FAILS, because
range checks and lookups carry a domain requirement `analyzeMethods` never reports. **A ceiling is
only honest for the shape it was measured on.** Read the rows below as the order of magnitude they
are; the numbers that price anything are `PartitionSchedule.MEASURED_CEILING`, and each of those
names the shape it came from.

### 4.2 The arithmetic

```
~11,000 permutations  ×  2,600.5 rows  =  ~2.86 × 10^7 rows      [§3.8, MEASURED]
2.86 × 10^7 / 48,000 usable            =  ~600 work-carrying step circuits
+ a binary aggregation tree over them  =  ~650–1,040 Pickles steps total
```

Only 25 permutations fit in one 2^16 step (`floor(65,536 / 2,600.5)`), and ~18 after the Pickles
recursive-verifier overhead of §4.1 — a useful sanity handle: **one FRI query alone (471
permutations) is ~26 steps.**

⚑ **THAT DIVISION SUBTRACTS NO CARRY, AND §3.20 MEASURES ONE.** Splitting a circuit at row `k` is
only sound if everything the second half reads from the first crosses the boundary, and in Pickles a
boundary costs re-witnessing plus a hash in *both* adjacent steps. At deployed geometry a boundary
that carries the opened-value set is **34,566 rows — 69.8% of a `max_proofs_verified = 2` step**; one
inside a query is **762**. So the honest deployed figure was a band, **564–1,838 work-carrying
steps**, and the arithmetic below is its optimistic end with the carry set to zero.

⚑ **AND §3.21 SCHEDULES IT: 591 work-carrying steps**, from a dynamic program over 27,590 atoms
against that measured carry, with the commitment chunked so a step re-binds only what it reads. The
arithmetic below is superseded as an ANSWER and kept as an input — its row totals are what §3.21's
atom model reproduces to 0.01%.

⚑ **AND §3.23 RE-RUNS THAT SCHEDULE OVER AN EMITTED ROW LIST: 519 work-carrying steps**, 448 at
`max_proofs_verified = 1`. The two atom prices §3.21 obtained by DIVIDING an aggregate are replaced
by in-context marginals on the deployed program, and the AIR term becomes the root's own 1,093
constraints (§3.22) instead of the fixture's four. The emitted total is **2.46 × 10⁷**, 10.64%
BELOW §3.19's projection — the "floor" was too small in its AIR term and too large everywhere else,
by more. ⚑ **519 and 448 are themselves optimistic**: they use §4.1's 57,532 usable rows, and §3.24
MEASURES a two-branch program failing to compile at that budget.

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

⚑ **AS OF §3.20 THIS IS RUN, NOT PROJECTED — at the fixture's geometry.** The decomposition below
(one transcript step, then independent per-query chains, each consuming the committed challenge
digest) is exactly the shape §3.20 builds and proves: `walk.first`/`walk.step` consume
`Poseidon(rootCommitDigest, challengeDigest, k)` and nothing else. What is projected is its SIZE at
the deployed geometry, and item 2's "19 independent per-query chains" is where the expensive
boundaries are — each query entry re-witnesses the whole opened-value set.

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
proving per dregg root verified**, parallel across the 19 query chains, sequential up the tree. ⚑ At
§3.21's scheduled **591 work-carrying steps** (plus the tree) the wall-clock reading is the same
order: the step count moved, the per-step time did not, and §3.21 measured **9–20 s per step** at
the fixture's geometry on one laptop core.

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

*(⚑ **RESOLVED 2026-07-28 — and the ~10% does NOT drop.** `APEX-VERIFIER-AIR-REDUCTION.md:59-63`
said the apex carries no live W24 rows; `ivc_turn_chain.rs:475,497` emits W24 sponge steps on every
`merge_two_segment_proofs`. The root's `degree_bits` — read at last, §1.2 — is
`[10, 10, 16, 15, 3, 16, 0]`: **the W24 table is PRESENT, at 2³ = eight rows.** Both statements were
half-right, and they were about different things. Being nearly EMPTY costs the W24 table nothing in
FRI depth — it is the `Alu` and `recompose` tables at 2¹⁶ that set `|D⁰|` — but its **452 columns are
opened and observed in full regardless of its height**, because the DEEP quotient and the challenger
absorb pay per COLUMN, not per row. So the root is 7 tables at Σ 940 columns, the ~1,200
permutations stay, and the reduction lever §5.2 names is still the right one: **narrow the trace's
WIDTH.** Reducing the W24 table's height buys nothing at all.)*

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
- **A handful of step circuits?** **No.** **591 work-carrying** at deployed parameters as of §3.21
  — a scheduled number, not a division — against §4.2's carry-free ~650–1,040; **~325–455** after
  the dregg-side FRI knobs; **~260** is the floor short of narrowing the root's trace or adding a
  Mina-targeted shrink layer. (The ~1,900–2,800 pessimistic branch is **retired** — §3.8 measured
  the gadget at 3.2× cheaper than the gnark-emulation parity that generated it.)
- **Is the step count a mechanism or a division?** **A mechanism as of §3.20, and a SCHEDULE as of
  §3.21.** A dregg proof with no one-step verifier is decided by chained Pickles steps, each proved
  and verified, with one field element per boundary and an unbound control for every refusal; and
  where the cuts GO is a dynamic program over 27,590 atoms and a measured carry, which turns
  §3.20's 3.3× band into **591**.
- **Honest row budget:** **2.46 × 10^7 Kimchi rows — EMITTED per atom (§3.23)**, against ~2.9 × 10^7
  projected. ~98% of it is still Poseidon2-w16-BabyBear; the root's whole AIR is 1.1% of it.
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
| N step circuits | **519 work-carrying — SCHEDULED OVER AN EMITTED ROW LIST (§3.23)**, 448 at `max_proofs_verified = 1`, against §3.21's modelled 591/504 (reproduced exactly as the baseline). ⚑ Both are computed against §4.1's 57,532 usable, which §3.24 measures failing to compile. Previously: **591 — SCHEDULED (§3.21)**, 504 at `max_proofs_verified = 1`. ⚑ §4.2's **~650–1,040** deployed / **~325–455** knobbed / **~260** floor all set the step-boundary carry to **zero**; §3.20 measured one and the honest figure became a band, **564–1,838**; §3.21's dynamic program places the cuts and chunks the commitment, and the band collapses to a number. |
| Where the cuts GO | **§3.21 — 521 of 590 boundaries INSIDE a query, 2 at a query entry.** The 3.3× spread decomposes as 1.66× placement and 2.00× commitment: `rootCommitDigest` becomes the hash of a **vector of chunk digests**, so a fold step stops re-witnessing the 8,920 opened-evaluation lanes it never reads. Proved as a 7-step chain from ONE verification key, nine splices refused, with a control. |
| The partition is a compiler problem with a known contract | **RUN as of §3.20, and it was arithmetic before.** A dregg proof at 103,554 rows — 1.58× the domain, past the measured compile wall, **no one-step verifier** — is verified by four chained Pickles steps from **two** VKs. One field element per boundary (`Poseidon(rootCommitDigest, challengeDigest, k)`), each step proved and verified, its `publicInput` its predecessor's `publicOutput`, both ends of the chain computable by a verifier from the dregg proof alone. |
| The boundary is a binding, not a sequence marker | **Yes, §3.20 — eight `prove()` refusals against REAL proof objects**, including two on values the walk never reads (`α_stark`, the query PoW witness), each paired with a CONTROL that shows the same circuit ACCEPTING the splice once the three boundary assertions are removed. ⚑ One of the eight went green by accident on a degenerate query draw (`[0,0,0]` at `\|D⁰\| = 2²`) and the fixture is now minted for pairwise-distinct indices. |
| A chain needs one verification key per step | **No — §3.20 uses ONE walk VK invoked N times**, with the step index and terminal bit witnessed and pinned inductively by the boundary chain. ⚑ Measured why it matters: a node process that has compiled **four** step circuits HANGS at the first `prove` (kimchi's wasm heap is 32-bit). A per-step-VK chain is not merely inelegant, it does not build. |
| It buys 128 bits | **No — ~50**, commit-column-bound, and `numQueries` provably cannot move it. |
| The AIR evaluation is the expensive part | **Still no, but the surrounding arithmetic is bigger than claimed.** §3.15 measures the DEEP quotient at 2.94 × 10⁶ rows over 19 queries and §3.16 the observes at 2.97 × 10⁶ — together ~20% of the budget, where §3.14 first recorded ~3.5% for DEEP *and* AIR. The AIR **fold** itself is `A + N·h` = 14,175 + N × 48 and remains small; `C_i` and `N` are uncounted. It is still mostly a hashing problem. |
| The DEEP quotient / reduced opening is bound to the trace | **Yes as of §3.15.** The reduced openings are computed from the MMCS-opened rows, the absorbed `f(ζ)` and the transcript's `alpha`, KAT'd against `p3_fri::verifier::open_input`. The gate **proves a witness the previous statement admits and requires the new one to refuse it**, so the closure is exhibited, not asserted. |
| The AIR constraint evaluation is started | **CLOSED as of §3.22, and RUN ON THE REAL PROOF as of §3.25.** All 1,093 constraints of dregg's seven root tables are emitted as one 10,417-node shared DAG and measured at **275,143 Kimchi rows** — 1.00% of the projection. §3.25 evaluates it at the COMMITTED root proof's opened values at ζ, reproduces p3's accumulator on all seven instances, and checks `acc · Z_H(ζ)⁻¹ == quotient(ζ)` as a Kimchi constraint, refusing six bends. Previously: "`C_i` is not built and `N` is not counted." |

| The AIR fits in one Pickles step | **No — §3.24.** 275,143 rows is 4.20× the domain, so the root's constraint system has NO one-step verifier. Three chained steps over it are proved and verified (4,798 of 10,417 nodes, 543 of 1,093 constraints, four of the seven tables), six splices refused with a control that builds its own predecessor. The full chain is 7 slices; the process wall is 3 compiled circuits. |

| The AIR closing equality binds ζ | **In all seven against a forgery; in six of seven for the honest transcript — §3.25.** `expose_claim` has `degree_bits = 0`, so `|H| = 1`, the selectors are ζ-free constants and the two size-1 quotient chunks are equal: **both sides are constant in ζ**, which is what a *constant* trace polynomial forces and is a property of the honest prover, not of the check. Measured as `zetaBindsForgery`: a forgery solved to close at the sampled ζ is refused at every bent ζ in **all seven**, asserted with no carve-out. α binds all seven. A Mina-side verifier must NOT skip the OOD point on the strength of `zetaBinding: false`. |
| A custom `Poseidon2BabyBear` Kimchi gate would buy ~2× | **No — ~1.5×.** §3.11 guessed ~900–1,100 rows/perm; the measured split (§3.8) puts the reductions a custom gate CANNOT remove at ~1,700 rows. Still a Mina hard fork. |
| The row price is a design claim nobody has run | **No longer.** §3.8–3.14 are measured, the circuits are committed under `bridge/mina-zkapp/src/`, and `scripts/check-mina-attestation.sh` fails if any of nine figures drifts >2%. |
| `degree_bits = [9,9,15,14,15]` describes the root | **No** — that is the BN254 **shrink** proof. The root's own heights are **unmeasured**, and §3.14 shows how much rests on that. |
| The FRI walk these circuits perform is *the prover's* | **Yes, and as of §3.29 the transcript is too.** The query index and every `beta` are DERIVED (§3.12–3.13b), the reduced opening is COMPUTED from the opened rows (§3.15), the mixed-height input opening is built (§3.28), and the state the whole transcript starts from is now derived from the batch's own commitments, public values, cumulative sums and all 2,630 opened values rather than witnessed — with a forged-but-consistent transcript refused and the refusal attributable to an unsealed control. **What is left is not inside the walk:** ~~nothing in circuit says which *proof* this is~~ — **§3.30 carries `expose_claim`'s 25 public values out as the chain's public output**, so the terminal proof states `(genesisRoot, finalRoot, numTurns, chainDigest)`. |
| The challenger is a rounding error next to the query walk | **NO — and this row was measuring 1.7% of the challenger.** §3.12's 0.48% is the FRI schedule *alone*, 23 permutations. The transcript that authorises it is **1,373** permutations and **3,575,411 rows — 10.5% of the walk, +10.8% on the query-aligned total** (§3.29), because 1,315 of them are the opened-value absorb. The binding was never cheap; only the part that had been measured was. |
| The chain says *which* proof it verified | **Yes — §3.30.** The public output is `ClaimedBoundary`, and its claim is `expose_claim`'s 25 public values — `genesisRoot`, `finalRoot`, `numTurns`, `chainDigest` — SEALED against the same `dagDigest` lanes the §3.29 preamble absorbs, on head slice 1, which already loads the chunks they live in. A forged claim over an UNTOUCHED lane table is refused, the refusal is attributable to an unsealed control that is row-for-row identical, and the carry across the other 904 slices has its own falsifier because it costs **zero rows** (a Kimchi copy constraint). +185 rows on 42,245,547 — **0.0004%** — and 905 instances / 131 programs are unchanged. ⚑ What it still does NOT say: that `(G,H,N,D)` is the head Mina should care about. Nothing is wired to `setDreggRoot`. |
| The DEEP/AIR arithmetic is ~1.5–2% | **No — ≈3.5%.** §2.4 priced a Horner step at ~7 rows; it is **49, measured** (§3.14). Still not the driver. |
| A Mina zkApp could today verify a dregg **proof**, not a dregg commitment | **Yes, at a reduced geometry — §3.19.** One `ZkProgram` consumes a proof `p3_uni_stark::prove` made under `DreggStarkConfig` and DECIDES it (preamble, opened-value absorption, FRI transcript, the AIR closing equality, the DEEP quotient, the MMCS openings, the fold chain) in **56,927 rows — ONE 2^16 Pickles step**, compiling, PROVING, verifying, and REFUSING seven bends and three wrong AIRs as real `prove()` refusals. **Not** at the deployed root's geometry: that projects to ≈ 2.75 × 10⁷ rows / 500–573 steps from §3.19's own measured marginals, and the AIR term in that total is the fixture's four constraints, not the root's 1,093. |
| The rungs are assembled | **Yes as of §3.19, and they were not before.** Every rung up to §3.18 was fed a fixture the measurement synthesised. §3.19's fixture is a proof dregg's prover made and dregg's own verifier accepted before it was emitted. |
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
`bridge/mina-zkapp/src/RootAirDag.ts` + `src/generated/root-air-dag.json` (§3.22 — the root's own
1,093 constraints as an emitted DAG), `src/RootAirChain.ts` (§3.24 — the chain over it),
`PartitionSchedule.emittedProgram` (§3.23), with
`scripts/{root-air-rows,emitted-atoms,emitted-schedule,root-air-chain,root-air-real}.ts`.
§3.22's extension extractor is `circuit-prove/tests/root_air_constraint_census.rs`'s `to_dag_full`;
§3.25's real-proof dumper is `circuit-prove/src/bin/root_air_instance.rs`, which decodes
`ugc-dregg/tests/fixtures/whole_history_proof.bin` and self-checks all seven closing equalities
before emitting.

`bridge/mina-zkapp/src/Poseidon2BabyBearW16.ts` (§3.8), `src/Poseidon2Merkle.ts` (§3.9),
`src/FriQueryStep.ts` (§3.10, §3.13), `src/FriChallenger.ts` (§3.12, §3.13b),
`src/DeepQuotient.ts` (§3.15), `src/AirEval.ts` (§3.16), **`src/DreggProofVerify.ts` (§3.19 — the
assembly)**, **`src/DreggProofPartition.ts` (§3.20 — the chain)**, **`src/PartitionSchedule.ts` and
`src/DreggProofSchedule.ts` (§3.21 — where the cuts go, and the chain that goes there)**, with
`scripts/{poseidon2-babybear-rows,poseidon2-merkle-rows,fri-query-rows,fri-challenger-rows,fri-chain-rows,fri-deep-rows,air-eval-rows,dregg-proof-verify,partition-chain,partition-schedule}.ts`.
§3.20's step-boundary contract is `metatheory/Dregg2/Circuit/Emit/KimchiPartition.lean`
(`StepPublicInput`, `StepBoundary`, `chunks_concat`, `chunks_fits`) — the Lean side designed it and
proved the list-partition half; §3.20 is the first object that emits a boundary, and §3.21 is the
scheduler `KimchiPartition` §3 names as its remainder ("the SCHEDULER is naive on purpose … a
smarter scheduler that minimises carried state is named in the remainder"). ⚑ The Lean file's own
`stepCountOfRows` is still the naive `⌈rows / usable⌉` with the carry set to zero; §3.21 does not
touch `metatheory/`, so that arithmetic and this schedule now disagree by design and the Lean side
is the stale one.
§3.19's fixture emitter is `circuit/src/bin/mina_stark_fixture.rs` — `p3_uni_stark::prove` under
`dregg_circuit::plonky3_prover::DreggStarkConfig`, self-verified before emission, canonical-u32 (NOT
Montgomery) on the wire.
The deployed-object referents are `circuit-prove/sketches/mina-pasta-hash-probe`'s `p2merkle`
(the MMCS), `p2fold` (one fold), `p2chain` (the whole 16-round chain), `p2chal` and
`p2fritranscript` (`p3_challenger::DuplexChallenger` and the `verify_fri` schedule) — every one of
them calling the p3 types at rev `82cfad73`, never a transcription.

**Companion:** `docs/MINA-DREGG-ZKAPP-BRIDGE.md` — this document answers its §5 "Route A" with a
budget, and does not disturb its Groth16 verdict.
