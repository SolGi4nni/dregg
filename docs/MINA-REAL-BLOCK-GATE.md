# MINA-REAL-BLOCK-GATE.md — a real Mina block, driven through our checks, per check

**Date:** 2026-07-28. **Status:** the gate is OPEN and green.
**Artifacts:** `metatheory/fixtures/pickles-extractors/` (extractor + fixtures, tracked),
`metatheory/mina_real_block_proof.json` (the dump),
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockGate.lean` (18 theorems, axiom-clean).

Import line for the new module (the `Dregg2` root was **not** edited, per house practice for
gates):

```
import Dregg2.Circuit.Emit.MinaRealBlockGate
```

---

## 0. What changed, in one paragraph

`docs/PICKLES-VERIFIER-SCOPE.md` said, correctly, that P0's residual was "**no real Wrap fixture**
— that needs a mainnet block through mina-rust's `verify_block`". Everything the campaign had ever
run on was ours: `KimchiRealProofGate` used a proof **we** generated from `create_circuit(0, 5)`,
and `PicklesRecursion` P0–P2 used **synthetic witnesses at a `2^5` domain**. That residual is now
closed. A real Mina devnet block's Wrap proof — Pallas-committed, `k = 15`, `prev_challenges = 2`,
`public = 40`, domain `2^14` — is a committed fixture, **o1-labs' own Kimchi verifier accepts it**,
and it runs through the assembled Lean decision, which accepts it and rejects every tamper.

## 1. Where the proof came from

* Mina **devnet**, chain id `29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6`,
  genesis `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`.
* Block **539508**, state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`.
* Fetched read-only over GraphQL from the public node `api.minascan.io/node/devnet` on 2026-07-28.
  No keys, no transactions, no mainnet writes. The raw response is pinned in
  `metatheory/fixtures/pickles-extractors/mina_devnet_block.json`; the proof is the base64url of
  the binprot `Mina_base.Proof.Stable.V2`, 11138 bytes.

## 2. That Mina's own verifier accepts it

Asserted in the extractor, in order, before anything is emitted (see the README for why
`verify_block` is assembled from its two halves rather than called whole, and why that
substitution is self-checking):

| # | check | code that runs | verdict |
|---|---|---|---|
| 1 | devnet blockchain VK loads | openmina `BlockVerifier::make()` | `public=40 prev_challenges=2 domain=2^14 max_poly_size=2^15 zk_rows=3` |
| 2 | `sg` accumulator discharge | openmina `accumulator_check` → `batch_dlog_accumulator_check` | **true** |
| 3 | the Wrap Kimchi proof | **o1-labs `kimchi::verifier::verify::<Pallas,…>`** | **`Ok(())`** |

Plus six Rust cross-checks tying our numbers to `proof.oracles(...)` — the C8 fold over the 47 `es`
entries reproduces `combined_inner_product`; the C5 body reproduces `ft_eval0`; `zkPolyR`
reproduces kimchi's permutation vanishing polynomial; `ω^(n−3)` reproduces `index.w()`; and K4c's
`bEval` reproduces `RecursionChallenge::evals` at ζ and ζω for **both** carried accumulators.

## 3. Our side, check by check

`shapeOkRec`/`prevChalFoldOk`/`kimchiVerifyDecisionFieldRec` are the P6 retirement a sibling lane
landed the same day; this is the first time any of them has seen a Mina object.

| our check | on the real block | verdict |
|---|---|---|
| **C1 `shapeOk`** (K5, frozen at `prevLen = 0`) | `prev_challenges = 2` | **REFUSES the real block** — `real_block_refused_by_freeze`. The freeze was not conservative; it rejected Mina. |
| **C1 `shapeOkRec`** at the real index | `idxPrev = 2, prev = 2, public = 40, w = 15, σ = 6, coeff = 15, t = 7, chunk = 1` | **accepts**; 6 single-count tampers reject |
| **P6 recursion fold** `prevChalFoldOk` | the 2 leading `es` entries at ζ and ζω vs. the 2×15 carried challenges | **accepts** — the exposed accumulator evaluations ARE K4c's b-polynomial of the carried challenges |
| **K4c `bEval` / `sVec_eq_bPoly`** | `bEvalSq ZETA CHALS_i`, `bEvalSq ZETAW CHALS_i`, i∈{0,1} | **reproduces all four**, and `bEvalSq_eq_bEval` ties the value to the object `sVec_eq_bPoly` is about |
| **C8 `combinedInnerProduct`** | 47-entry `es` list **including** the recursion prefix, `ξ`/`r` from `oracles()` | **reproduces `combined_inner_product`**; 4 tampers reject |
| **C5-inv** witnessed inverse | `(ζ − ω^{n−3})(ζ − 1) · DINV = 1` in `ZMod qN` | **holds** (no `Field (ZMod qN)` instance needed) |
| **C5 `ftEval0R`** | real `n = 2^14`, real ω, ζ, β, γ, α^21..α^23, w[0..6], σ[0..5], shift[0..6], linearization constant term | **reproduces `ft_eval0`**; 3 tampers reject |
| **composed `kimchiVerifyDecisionFieldRec`** | all of the above at once | **ACCEPTS the real Mina block**; 4 tampers reject; the pre-P6 decision refuses it outright |

Everything above is `by decide`/`rfl`, no `sorry`, no `native_decide`;
`#assert_namespace_axioms` reports **18 theorems pinned kernel-clean**. `lake build` on hbox:
**82s**.

### What could NOT be fed, and why

* **C3 (the Fiat–Shamir transcript)** — the challenges are *recorded*, not *re-derived*. The Wrap
  side needs the **Fq-state Poseidon sponge over Pallas's base field**, which is exactly the K3
  residual a sibling lane is closing (`PastaPoseidonFq.lean`). Until it lands, β/γ/α/ζ/ξ/r on the
  real block are carried, not recomputed. This is the single largest remaining hole in the gate:
  every scalar we check is checked *given* the challenges.
* **C9 / the terminal `msm == 0`** — the IPA opening-soundness floor. Unchanged, inherited, P10.
* **The commitment arithmetic** — `w_comm`, `t_comm`, `lr`, `delta`, `sg` are dumped as Pallas
  points but nothing in-kernel touches them. K2/K4a/K4b have the curve ops; no gate composes them
  into the Wrap group check.
* **The deferred STEP values** — `expand_deferred`'s Fp outputs (`b`, `combined_inner_product`,
  `xi`, `perm`, `zeta_to_domain_size`, shifted Type1) are dumped and are the P3/P4 input, but no
  Lean check consumes them yet.

## 4. Corrections to `docs/PICKLES-VERIFIER-SCOPE.md`, measured

That document is being edited by a sibling lane, so the corrections are recorded here rather than
applied in place.

1. **P0's "no real Wrap fixture" residual is CLOSED**, and the fixture is a devnet block, not a
   mainnet one — see §5.
2. **The wrap domain is not always `2^15`.** §D says wrap domain `∈ {2^13, 2^14, 2^15}` keyed by
   `proofs_verified` (`0→13, 1→14, 2→15`). The real devnet **blockchain** VK has
   `domain = 2^14` while `branch_data = {proofs_verified: N2, domain_log2: 16}`. `branch_data`
   describes the **Step** side (2^16, two previous proofs); the Wrap VK's own domain is 2^14 and
   its `max_poly_size` is 2^15. Any model that reads "Wrap ⇒ 2^15 domain" off §A is wrong; 2^15 is
   `max_poly_size` / the SRS depth, and `chunk_size = 1` because `2^14 < 2^15`.
3. **`prev_challenges = 2` is not "Wrap_hack padding" on this block — it is real.** The proof
   carries two genuine `challenge_polynomial_commitments`, so `verify.ml:361-364`'s pad-to-2 is a
   no-op here (the extractor asserts it rather than padding silently).
4. **A new, measured cost wall.** `ftEval0R` raises ω to `n−3`, `n−2`, `n−1` and ζ to `n` through
   unary `Monoid.npow`. At `KimchiRealProofGate`'s `n = 32` that is free; at the real `n = 2^14` it
   is ~65k kernel multiplications in `ZMod qN` and it is why the file needs
   `set_option maxRecDepth 100000`. It still builds (82s total), but C5 has no `sqIter` ladder the
   way the b-polynomial does, and the next domain size up doubles it.

## 5. A measured openmina defect: mainnet block verification is broken at HEAD

At openmina `82480cd468`, `crates/ledger/src/proofs/data/mainnet_*_verifier_index.json` are in a
**stale serde format** — `PolyComm` as `{unshifted, shifted}`, no `zk_rows`, `domain` as a
172-byte arkworks-0.3 int array — while the pinned proof-systems `0.3.0` `SerdeAs` reads a hex
string from any human-readable format. `BlockVerifier::make()` therefore **panics** on mainnet with
`invalid type: sequence, expected a hex encoded string`. Not feature-dependent: `serde_json` is
always human-readable. The devnet files were regenerated and are fine. Reproduction:
`cargo run --release -- mainnet` in the extractor. A real mainnet block header (height 359606) is
committed alongside so that the moment the index is regenerated, `verify_block` can be called
literally.

## 6. The honest distance to "we verify a real Mina block"

Ordered by effort, with the synthetic-witness estimates replaced by what the real object cost.

| # | what | measured status |
|---|---|---|
| 0 | get a real Mina proof and confirm Mina accepts it | **DONE.** ~1 build of openmina's `mina-tree` (1m41s incremental once the lockfile is seeded) + a GraphQL read. |
| 1 | C1 at the real Wrap shape | **DONE** (P6's shape half, sibling; measured here). |
| 2 | the recursion fold into C8 (P6 arithmetic half) | **DONE** on real data. |
| 3 | C8 / C5 / the witnessed inverse on real Wrap scalars | **DONE**. |
| 4 | **the Fq-state Poseidon sponge (K3 mirror)** — makes C3 re-derivable instead of carried | **THE NEXT THING.** A sibling lane has the Fq KATs and a `prev_challenges = 2` Kimchi fixture in flight (`PastaPoseidonFq.lean`, `KimchiRecursionGate.lean`). Cost: the KATs exist; wiring them to the real block's absorb order is a day, not a week — the extractor already dumps every input in `verifier.rs:159-276` order. |
| 5 | the Wrap **group** check — `ft_comm`, the linearization commitment, `check_bulletproof` | **NOT STARTED.** K2/K4a/K4b have the curve arithmetic; nothing composes it. This is the largest genuinely-unbuilt block, and it is where the real block's 15 `lr` pairs, `delta` and `sg` finally get consumed. Weeks. |
| 6 | P3/P4 — `finalize_other_proof` + the transcript-equality binding | **NOT STARTED**, and the real block now supplies the inputs: `step_deferred_values` in the dump is `expand_deferred`'s output, Type1-shifted, with the unshifted values alongside. P4 remains the single hardest buildable item. |
| 7 | P7/P8/P9 — base case, wrap-VK model, Mina's instantiation | **NOT STARTED**, but P8/P9's *data* is now concrete rather than notional: the devnet blockchain VK is a loadable object with known counts. |
| 8 | P10 — the IPA `msm == 0` opening-soundness floor | **INHERITED, undischarged**, as before. |

**Say it at the right resolution:** we do not verify a Mina block. We check, in-kernel, on a real
Mina block, that its shape is the shape the real verifier index demands, that the accumulator
evaluations it exposes are the b-polynomial of the challenges it carries, and that its aggregated
opening value and `ft(ζ)` are what the claimed evaluations and the sampled challenges produce —
**given** those challenges, and with no group element ever touched. The gap between that and a
light client is items 4, 5 and 6 above, on top of the P10 floor.
