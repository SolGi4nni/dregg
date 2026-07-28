# MINA-REAL-BLOCK-GATE.md — a real Mina block, driven through our checks, per check

**Date:** 2026-07-28. **Status:** the gate is OPEN and green; **C3 is no longer carried**,
**group elements are no longer untouched** (§6.1 rungs 5a–5d), and **a commitment is now
opened** (§6.1 rungs 5e–5f) — subject to the two premises §6.1 names and does not discharge.
**Artifacts:** `metatheory/fixtures/pickles-extractors/` (extractors + fixtures, tracked —
`src/main.rs` for the scalar side, `src/bin/wrap_group_export.rs` for the group side),
`metatheory/mina_real_block_proof.json` and `metatheory/mina_real_block_wrap_group.json` (the
dumps),
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockGate.lean` (18 theorems, axiom-clean),
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockTranscript.lean` (13 theorems, axiom-clean — the
Fiat–Shamir derivation),
`metatheory/Dregg2/Circuit/Emit/MinaWrapGroupGate.lean` (15 theorems, axiom-clean — the `ft_comm`
assembly on real Pallas points, `lake build` 25 s),
`metatheory/Dregg2/Circuit/Emit/MinaWrapAggregationGate.lean` (7 theorems, axiom-clean — the
47-term polyscale aggregation, 93 s),
`metatheory/Dregg2/Circuit/Emit/MinaWrapPublicCommGate.lean` (11 theorems, axiom-clean — rung 5e,
`public_comm` derived from the 40-element public input, 159 s) and
`metatheory/Dregg2/Circuit/Emit/MinaWrapOpeningGate.lean` +
`MinaWrapOpeningWeld.lean` (26 + 1 theorems, axiom-clean — rung 5f, **the IPA opening relation**,
153 s + 75 s).

All seven are wired into `metatheory/Dregg2.lean` — the first four by `06de765e9` / `73853b50f`,
the three new ones by `ec839066d` (a sibling orphan-sweep lane; this lane reported the import
lines rather than editing the root itself, per house practice):

```
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate
import Dregg2.Circuit.Emit.MinaWrapOpeningGate
import Dregg2.Circuit.Emit.MinaWrapOpeningWeld
```

`#floor_ratchet` reads the environment of that root and nothing else, so a module it cannot see
cannot arm it. **Measured before the wiring landed, with the three added lane-locally on hbox
(`lake build Dregg2`, 10413 modules): still exactly 1**, and the same name —
`Emit.AutomataflRevealRefine.not_revealColl_of_hash4NoCollision`, the violation
`docs/DREGG-IN-DREGG-BUILD.md` records as pre-existing. Expected, and worth saying why: these
modules bind no floor at all. Every theorem is `by decide` or `#guard` over concrete
`Nat`/`ZMod` values, so there is no `CommitSurface`, no injectivity hypothesis and nothing for the
gate to promote.

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

And, added 2026-07-28 with C3, **three transcript cross-checks** — the extractor replays *both*
Fiat–Shamir sponges with the real upstream `DefaultFqSponge`/`DefaultFrSponge` and asserts each
challenge against `oracles(...)`:

```
[c3] phase-1 Fq-sponge (fp_kimchi over Fp) replay reproduces beta, gamma, alpha', zeta', digest : true
[c3] phase-2 Fr-sponge (fq_kimchi over Fq) replay over 91 absorbed elements reproduces v', u' : true
[c3] order controls: ft_eval1-after-public-evals and no-prev-challenge-digest BOTH move v' : true
```

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
| **C3 the Fiat–Shamir transcript** (`MinaRealBlockTranscript`) | both sponges, over the block's own commitment coordinates and evaluations | **DERIVES β, γ, α′, ζ′, the digest, the prev-challenge digest, ξ′ and r′**; the endo lifts give α, ζ, ζω, ξ, r; 15 non-vacuity pins |
| **the group assembly** (`MinaWrapGroupGate` / `MinaWrapAggregationGate`) | the block's 7 `t_comm` chunks, the index's `sigma_comm[6]`, all 47 aggregation commitments | **reproduces `ft_comm` and `Σ ξⁱ·Cᵢ`** over the real group law; `ft_comm` is pinned by o1-labs' own `SRS::verify`; 9 tampers reject — §6.1 rungs 5a–5d |
| **`public_comm`** (`MinaWrapPublicCommGate`) | 40 SRS Lagrange points × the block's 40-element public input, + the `+1·h` blinder | **DERIVES the commitment C3 absorbs**; 5 tampers reject — §6.1 rung 5e |
| **the IPA opening relation** (`MinaWrapOpeningGate` / `…Weld`) | `lr[0..14]`, `sg`, `delta`, `u_base`, the 47-term aggregate, at challenges continued from the block's own sponge | **`c·Q + delta − z1·sg − z1·b0·U − z2·H = O`**; 9 tampers reject — §6.1 rung 5f, **the rung that opens a commitment**, on the two premises §6.1 names |

Everything above is `by decide`/`rfl`/`#guard`, no `sorry`, no `native_decide`;
`#assert_namespace_axioms` reports **18 theorems pinned kernel-clean** for the gate, **13** for the
transcript, **15 / 7** for the two group modules, **11** for `public_comm` and **25 / 1** for the
opening rung. `lake build` on hbox: **82s** gate, **14s** transcript, **25s / 93s** group,
**159s** `public_comm`, **153s / 75s** opening.

### C3, retired — what the transcript module derives (2026-07-28)

The Wrap proof is **Pallas**-committed, so by `curve.rs:62-72,87-104` its two sponges are the
*mirror* of the Vesta-committed Step fixture `PastaPoseidonFq` was built on: **phase 1 is
`fp_kimchi` over `Fp`** (K3's own constants — `core_is_Ref_at_Fp` proves the instantiation IS
`PastaPoseidon.Ref`), and **phase 2 is `fq_kimchi` over `Fq`** (`PastaPoseidonFq`). One parametric
absorb schedule runs both; there is no second transcription to get wrong.

| value | how | pin |
|---|---|---|
| β, γ | raw 128-bit squeezes of the phase-1 sponge after 37 absorbed `Fp` elements (index digest · 2 recursion commitments · public commitment · 15 witness commitments) | `wrapPhase1`; `derived_beta`/`derived_gamma` tie the `Nat` to the `Fq` element C5 consumed |
| α′ → α | + `z_comm`, squeeze, `endoMap ENDO_R` | `derived_alpha`; `derived_alpha_powers` ties α to C5's α²¹/α²²/α²³ |
| ζ′ → ζ, ζω | + `t_comm` (7 chunks), squeeze, `endoMap` | `derived_zeta` |
| fq digest | `squeeze_field()` reinterpreted in `Fq` (the mirror of the Step side's `Fp`) | `wrapPhase1` |
| prev-challenge digest | a FRESH `fq_kimchi` sponge over the **30** carried challenges — an EVEN-length absorb, the branch the 07-27 double-permute defect lived on | `Core.hash fqParams CHALS_FLAT`, with the double-permute anti-value pinned |
| ξ′ → ξ, r′ → r | phase-2 sponge over 91 `Fq` elements, two squeezes (lanes 0 and 1 of one permuted state), `endoMap` | `wrapPhase2`; `derived_v`/`derived_u` |

⚑ **The phase-2 tape is not a second copy of the evaluations.** `absorb_evaluations`' 86-element
stream is exactly entries 4.. of the gate's own C8 columns, interleaved ζ/ζω, read through
`ZMod.val`; `ft_eval1` is `EVZW[3]` and `p(ζ)`/`p(ζω)` are `EVZ[2]`/`EVZW[2]`. A prover cannot show
one set of evaluations to the transcript and another to the aggregation.

`real_block_accepts_on_derived_challenges` restates the gate's accept with **every** challenge
argument replaced by the derived expression, and is proved by rewriting — not by a second `decide`.

**Two order facts, verified against `verifier.rs`/`plonk_sponge.rs` at the pinned tag (`0.3.0` =
`a73ca6ed58`) rather than off a doc, and MEASURED on this object:** `ft_eval1` is absorbed at
`:382`, **before** the public evaluations at `:391-392`; and the prev-challenge digest (`:290-299`)
sits between the fq digest and `ft_eval1`. Both mis-orderings produce a **different ξ′** — asserted
in Rust and pinned in Lean. Both are dead at `prev_challenges = 0`; this block carries 2.

### What could NOT be fed, and why

* **C9 / the terminal `msm == 0`** — the IPA opening-soundness floor. Unchanged, inherited, P10.
* **The commitment arithmetic** — *superseded the same day, twice.* This bullet used to read
  "nothing in-kernel touches them"; then, after 5a–5d, "nothing yet checks that a commitment
  commits to anything". **Both are now out of date.** `MinaWrapGroupGate` /
  `MinaWrapAggregationGate` compose K4a's RCB complete add and K4b's ladder over the block's own
  `t_comm` chunks, the index's `sigma_comm[6]` and all 47 aggregation commitments (5a–5d);
  `MinaWrapPublicCommGate` **derives** `public_comm` from the block's 40 public inputs, so C3 no
  longer eats those two coordinates (5e); and `MinaWrapOpeningGate` states the IPA **opening
  relation** over `lr`, `delta`, `sg`, `u_base` and the aggregate (5f). What remains true: C3
  still eats the `(x, y)` of the two RECURSION commitments and of `w_comm`/`z_comm`/`t_comm` —
  the group gates check curve membership of every point they consume, but the transcript itself
  does not — and a `RecursionChallenge`'s `comm` is still not checked to be
  `⟨b_poly_coefficients(chals), G⟩` (5g). See §6.1 for what 5f establishes versus assumes.
* **The verifier-index digest is still an input.** `index.digest::<EFqSponge>()` is itself a sponge
  over every commitment of the VK (`verifier_index.rs:399-450`); it is absorbed as a value. Making
  it derived is P8/P9 (a model of the Wrap VK), not C3.
* **`KimchiVerify.frPhase2Inputs` is the `prev_challenges = 0` helper only** — it hard-codes the
  prev-challenge digest as `Ref.hash []` *and* runs over `fp_kimchi`/`pN`, which is right for a
  Vesta-committed Step proof and wrong on both counts for a Wrap proof. Its one caller
  (`KimchiRealProofGate`) is a `nPrev = 0` Step fixture, so nothing is presently wrong; the
  recursive/Wrap phase-2 model is `MinaRealBlockTranscript.fqTape2`. Named as debt, not fixed here.
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
| 4 | **C3 — the Fiat–Shamir transcript re-derived instead of carried** | **DONE, 2026-07-28.** `MinaRealBlockTranscript.lean`, 13 theorems + 15 `#guard` pins, `lake build` 14s. All six challenges plus both digests fall out of the two sponges over the block's own commitments and evaluations; `real_block_accepts_on_derived_challenges` is the gate's accept with every challenge argument replaced. The estimate ("a day, not a week") held. What it needed that was NOT in the dump: the verifier-index digest, the public commitment's coordinates, the prev-challenge digest and `endo_r` — added to the extractor, which now also **replays both sponges in Rust** against `oracles(...)`. |
| 5 | the Wrap **group** check | **5a–5f DONE, 2026-07-28** — no longer one block. Broken into rungs and re-priced below. 5f is the rung that opens a commitment; 5g is deferred by design and 5h by measurement, and both are the P10 story. |
| 6 | P3/P4 — `finalize_other_proof` + the transcript-equality binding | **NOT STARTED**, and the real block now supplies the inputs: `step_deferred_values` in the dump is `expand_deferred`'s output, Type1-shifted, with the unshifted values alongside. P4 remains the single hardest buildable item. |
| 7 | P7/P8/P9 — base case, wrap-VK model, Mina's instantiation | **NOT STARTED**, but P8/P9's *data* is now concrete rather than notional: the devnet blockchain VK is a loadable object with known counts. |
| 8 | P10 — the IPA `msm == 0` opening-soundness floor | **INHERITED, undischarged**, as before — and rung 5f is exactly the place to keep saying so. 5f states the verifier's opening *check* in-kernel and it passes; P10 is the claim that passing it implies the prover KNOWS an opening. Landing 5f moves P10 not at all, and the temptation to read "we opened a commitment" as "the opening is sound" is now a live one, so §6.1 spells the difference out. |

### 6.1 Item 5 opened up — the Wrap group check, rung by rung

"Weeks, the largest genuinely-unbuilt block" was an estimate over an unmeasured object. Measured,
it is **eight rungs of very unequal size**, and the two facts that reorder them are:

1. **The devnet blockchain Wrap index has ZERO `linearization.index_terms`.** Every selector,
   coefficient and witness column the linearization could reference has its evaluation *supplied*
   by the proof, so kimchi folds it into the linearization **constant term** — the scalar C5 /
   `ftEval0R` already reproduces on this block. The only column with no supplied evaluation is
   `sigma_comm[PERMUTS−1]` (`s` carries `PERMUTS−1 = 6` evaluations, not 7). So the "linearization
   commitment MSM" that item 5 named as a major sub-block is a **one-term MSM**.
2. **The terminal `msm == 0` is 82 non-SRS points plus `|srs.g| = 32768`.** Counted from
   `ipa.rs:170-285` on this block: `H`, `sg`, `u`, 2×15 `lr`, the 47 combined commitments, `u`
   again, `delta`. Everything expensive is the one `⟨s, G⟩` term.

**Unit of cost, measured on this hardware (hbox, `lake build`):** one 255-bit RCB double-and-add
ladder ≈ **0.19 s** of kernel (each `by decide` pays it twice — elaborator, then kernel recheck).
The 47-term fold in 6.1d is **93 s at 10.2 GB peak RSS**; that is the datum the extrapolations
below use. **5e and 5f are the first check on it, and it held**: 5e's nine 40-ladder instances
predicted ~135 s and cost **159 s / 14.5 GB**; 5f's ten 34-ladder instances plus the sponge
predicted ~130 s and cost **153 s / 14.3 GB**; the 80-ladder weld cost **75 s / 9.6 GB**. Time is
linear in ladders as assumed; **memory is not** — it tracks the largest single `decide`, not the
file's total, which is why splitting the weld out worked and why the 5h ~7 TB figure is an upper
bound on a shape nobody should build that way.

| rung | what | scalar-muls | status |
|---|---|---|---|
| **5a** | `f_comm` = the linearization MSM (`perm_scalars · sigma_comm[6]`) | 1 | **DONE** — `MinaWrapGroupGate.fComm_reproduces_kimchi` |
| **5b** | `chunk_commitment(t_comm, ζ^{2^15})` — Horner over the block's 7 real `t_comm` points | 6 | **DONE** — `chunkedT_reproduces_kimchi` |
| **5c** | **`ft_comm`** = `chunk(f_comm) − (ζⁿ−1)·chunk(t_comm)`, Maller's optimization | 10 | **DONE** — `ftComm_reproduces_kimchi`, and the gold is **pinned by o1-labs' own `SRS::verify`** on the real opening proof (refuted at `ft_comm + G`) |
| **5d** | `combine_commitments` — the 47-term `Σ ξⁱ·Cᵢ` aggregation that feeds the terminal MSM | 46 | **DONE** — `MinaWrapAggregationGate.combinedComm_reproduces_kimchi`, and `combinedComm_from_our_ftComm` fills the `ft_comm` slot with 5c's kernel-computed point rather than the dumped gold |
| **5e** | `public_comm` = `MSM(lagrange[0..40], −public_input)` + blinder | 40 | **DONE** — `MinaWrapPublicCommGate.publicComm_reproduces_kimchi`, 11 theorems, **159 s**. And `publicComm_is_the_transcript_preimage`: the point the kernel builds from the block's 40 public inputs IS the `(x, y)` C3 absorbs third, so the public-commitment coordinates are **derived, not eaten**. Pinned by o1-labs' `commit_public` and refuted at `public_comm + G` through their own `SRS::verify`. The blinder is a FIXED `+1·h` (`mask_custom` with `PolyComm::one`), and `tamper_blinder_dropped` says it is load-bearing anyway. |
| **5f** | **`check_bulletproof` minus `⟨s,G⟩`** — the `lr` fold, `sg`, `delta`, `u_base`, `c` | 34 | **DONE — this is the rung that opens a commitment.** `MinaWrapOpeningGate.opening_relation_holds`, 26 theorems, **153 s**; plus `MinaWrapOpeningWeld` (**75 s**, 80 ladders in one `decide`) which re-states it with the 47-term aggregate supplied by 5d's own kernel fold rather than the dumped gold. See "what 5f establishes vs assumes" below. |
| **5g** | the recursion commitments as `⟨b_poly_coefficients(chals), G⟩` | 2 × 2^15 | **DEFERRED BY DESIGN — and now priced, so the "by design" is not doing the work alone.** 65536 ladders is **twice 5h**: ~36 hours and ~14 TB in-kernel by the same 5d extrapolation. It is precisely the obligation K4c prices (`sVec_eq_bPoly`, `deferral_compression`); P1 (`accumulator_check_splits`) proved the real MSM splits into these blocks; and it is asserted on THIS block in Rust by openmina's own `accumulator_check` → `batch_dlog_accumulator_check`, which is ground truth 2 of the extractor. So, like 5h, it is a **known-true premise** rather than an open question — just not one this kernel checks. |
| **5h** | **`⟨s, G⟩`** — the 2^15-term SRS MSM inside the terminal `msm == 0` | 32768 | **DEFERRED, and the deferral is a measurement not a preference.** Linear extrapolation from 5d (47 terms → 93 s, 10.2 GB) puts a naive in-kernel `⟨s,G⟩` at **~18 hours and ~7 TB of elaborator memory**. Brute force is not a scheduling problem; the route is the product structure `sVec_eq_bPoly` already gives, on top of the P10 floor, which this rung does **not** discharge either way. **New, 2026-07-28:** the extractor now asserts `⟨b_poly_coefficients(chal), srs.g⟩ == opening.sg` in Rust (`[gt8]`), so 5h's statement is a **known-true premise** of 5f rather than an unexamined one. |

**What rung 5f establishes, and what it assumes — both, in the same breath.**

`SRS::verify` (`poly-commitment/src/ipa.rs:118-300`) folds two independent statements into one
randomised MSM with independent randomisers `rand_base` and `sg_rand_base`:

```text
(A)  sg == ⟨s, srs.g⟩                                    -- rung 5h; NOT checked in-kernel
(B)  c·Q + delta − z1·sg − z1·b0·U − z2·H == O            -- rung 5f; THIS
     where  Q = Σⱼ (chal_invⱼ·Lⱼ + chalⱼ·Rⱼ) + Σᵢ ξⁱ·Cᵢ + cip·U
```

**Establishes.** (B) holds in the Lean kernel, over K4a's complete add and K4b's 255-bit ladder,
on the block's own 15 `lr` pairs, `sg`, `delta`, the 47-term aggregate and a derived `u_base` —
and **at challenges the block's own transcript samples, not carried ones**. §3's sponge continues
from `o.fq_sponge` (the state right after ζ′, since `oracles` takes its `digest()` on a clone)
through `absorb_fr(shift_scalar(cip))` → `challenge_fq` → 15 `absorb_g(L)/absorb_g(R)/squeeze`
rounds → `absorb_g(delta)`, and **all 16 challenges of the opening argument fall out of it**.
`b0` is re-derived as `b_poly(chal, ζ) + r·b_poly(chal, ζω)` at the gate's own ζ and `r`;
`chal_inv` is checked to be the inverse of `chal`; `cip` is proved equal to the gate's `CIP`,
which C8 already proved is the (ξ, r)-fold of the block's **claimed evaluations**. So (B) is the
first statement in this campaign whose truth says a *committed polynomial has the evaluation the
proof claims*.

`u_base` is derived too: the SvdW group map (`groupmap/src/lib.rs:65-125`) is run in-kernel on the
full `challenge_fq` squeeze, with the inverse `alpha` and the square root as witnesses, and — this
is the part that is easy to skip — **the two skipped candidate x's are certified as non-residues
by Euler's criterion**, so the branch `get_xy`'s search takes is derived rather than transcribed.
The one thing that is not: which of `±y` arkworks' `sqrt()` returns. `tamper_u_base_sign` bounds
that by showing the other root breaks the relation, so the sign is pinned by o1-labs' output.

**Assumes, and does not discharge:**

1. **P10.** (B) is the verifier's *check*. That a prover passing it must KNOW an opening is the
   IPA/dlog extraction argument, undischarged here and everywhere in this stack. **"We opened a
   commitment" means "the opening check passes", not "the opening is sound".**
2. **(A).** (B) uses `sg` as the IPA's final `G`. Without 5h, (B) is a statement about an opening
   against a `G` the proof supplied. It is measured true in Rust and discharged out-of-circuit by
   openmina's `accumulator_check`; it is not checked in this kernel.
3. Poseidon's collision resistance; `p` prime (Euler); and the SRS itself — that `srs.g` and
   `srs.h` are what they claim is checked by nothing here.

**Order to build them in:** item 6 (P3/P4) is next. 5g/5h are not; they are the P10 story and
belong with the FRI/IPA floor work.

**Say it at the right resolution:** we do not verify a Mina block. We check, in-kernel, on a real
Mina block, that its shape is the shape the real verifier index demands, that the accumulator
evaluations it exposes are the b-polynomial of the challenges it carries, that its aggregated
opening value and `ft(ζ)` are what the claimed evaluations and the sampled challenges produce,
that **those challenges are the ones its own transcript samples** rather than the ones it hands
us, and — since rungs 5e–5f — that its public commitment is a commitment to its public input and
that **the IPA opening relation holds for the aggregate of all 47 of its commitments**. Two
sentences that were true this morning are now false: *"no group element is touched by any check"*
and *"no check says a commitment is a commitment to anything."* What is still true, and is the
whole of the remaining distance: the opening relation is the verifier's **check**, not the
extraction argument behind it (P10), and it rests on `sg == ⟨s, srs.g⟩`, which is measured in
Rust and not in this kernel (5h). The gap between here and a light client is 5g, 5h and item 6,
on top of that floor.
