# Verifying Mina at a checkpoint cadence — what it costs, and what a longer one loses

**Status 2026-07-30, after two coordinator build runs.**

* **`Dregg2.Bridge.MinaCheckpoint` — ELABORATES CLEAN**, hygiene silent. Every safety theorem below
  *and* the gate welds hold, so `provisional_never_ratchets` is a property of the **exported symbol**,
  not of a function beside it.
* **`Dregg2.Bridge.MinaWrapChallenges` — ELABORATES CLEAN**, hygiene silent.
* **`MinaWrapChallengesWeld` — NOT YET RUN.** Attempt 1 stopped before it; attempt 2 hit a syntax
  error in it. ⚑ **The per-block compiled derivation is therefore still UNVERIFIED**, and it is the
  lane's headline result. Nobody has seen it.
* **`MinaWrapPublicInput` — RED.** Two orphaned doc-comments (a `/-- … -/` cannot precede a `#guard`;
  `#guard` is a command, not a declaration) plus a bare `unfold` that rewrote without closing, which
  Lean recovered with `sorryAx`. Both fixed; unverified.

Attempt 1's failure was one bug: a two-level `match` does not iota-reduce under `rw`, so the second
rewrite in each weld found nothing. Attempt 2's was another: a theorem→`#guard` conversion left its
docstring attached to nothing, in 22 places.

**Update 2026-07-30 — the MSM moved, and the projection it rested on was wrong by 1.75×.**
`Dregg2.Bridge.MinaWrapSg` (the compiled checker, rooted at +0 closure), its instance differential
`MinaWrapSgWeld`, and `lean_exe mina_sg_bench` are **WRITTEN AND NOT YET BUILT** — no build has seen
them. What *has* been measured, at full scale and compiled, is the evaluator they call: **35.1 s and
18.8 MB for one 32,768-point Pallas MSM**, against ~3.5 h and ~28 GB in the kernel. So the
kernel→compiled ratio is **359×, not the 630× §5a projected**, a checkpoint is **~105 s, not ~60 s**,
and **the 10-minute cadence still closes** — with a 5.7× margin instead of a 10× one. §5a carries the
per-add rate, the box, and the falsifier.

Read the verbs literally. **Elaborated clean** = seen by a build. **States** = written and not yet
seen by a build. **Predicted** = arithmetic from a measured figure, with the falsifier named. The
cadence result rests only on measured protocol constants and on the first two.

---

## 1. The insight, and why it resizes the problem

**Mina's Pickles proof is recursive: block N's Step proof verifies block N−1's Wrap proof.**
Verifying ONE block's Wrap proof attests the *validity* of the whole chain behind it — every
transition, every in-circuit density update, every leader-election check, back to genesis.

So a client does not need per-block verification at Mina's 180 s block cadence. It needs
**per-checkpoint verification at whatever cadence it chooses**, and the cost of a longer cadence is
**latency and liveness, not safety** — provided nothing a longer cadence leaves unverified can move
the finalized point.

That proviso is a theorem rather than a convention — and these three, plus the welds that tie them to
the exported symbol, **elaborate clean**. `Dregg2.Bridge.MinaCheckpoint`:

* `provisional_never_ratchets` — a between-checkpoint step is *definitionally* unable to touch the
  verified head;
* `runSteps_finalized_monotone` — the ratchet never decreases under **any** interleaving of the two
  tiers, in any order, of any length;
* `a_checkpointless_run_finalizes_nothing` — a run with no checkpoint leaves `finalized` exactly
  where it started, so a longer cadence makes the ratchet *wait*, not move on weaker evidence.

## 2. ⚑ What recursion buys, and what it does not

**Buys: chain validity, transitively — and with it the density window.** `min_window_density` is
updated in-circuit by the blockchain SNARK's transition function, so a verified tip's density is
verified all the way back. **A checkpoint therefore does not need two consecutive headers.**

**Does not buy: which chain.** Every valid fork — including a long private low-density one — has a
valid Pickles proof. Choosing between them is Samasika `select`, which is not in the SNARK, and
`select` is only meaningful when *both* tips are valid. **So the checkpoint cadence is exactly the
cadence at which fork choice is meaningful at all.** Between checkpoints the tip is a guess.

**The interaction, which inverts the obvious worry** ("a checkpoint every 20 blocks does not
obviously give you consecutive-header density"):

| | density comes from | needs consecutive headers? |
|---|---|---|
| at a **checkpoint** | the Wrap proof (the SNARK's own transition function) | **no** |
| **between** checkpoints | `MinaSlidingWindow.step` re-run from the parent | **yes — and that is why the cheap tier takes a parent** |

The cheap check and the expensive check discharge the **same obligation by different means**. The
cheap one runs continuously; the expensive one re-anchors and does not need the cheap one's history.
This closes `docs/MINA-LIGHT-CLIENT.md` row 7 for the provisional tier — the head no longer
bound-checks a *served* window, it recomputes the one value the daemon's own
`update_min_window_density` produces (`MinaCheckpoint.densityFollowsParent`, with
`density_admits_exactly_the_step` proving it refuses a `+1` that every bound check admits).

## 3. The number that makes the cadence question easy

`k = 290` blocks and a slot is 180 s, so **Mina's own finality latency is 290 × 180 s = 52,200 s
≈ 14.5 hours.** The finalized height the client ratchets is `blockchain_length − k`. A checkpoint
every `C` blocks delays a height's finalization by at most `C × 180 s` **on top of that 14.5 hours**.

| cadence | `C` | added latency | vs Mina's own 14.5 h | unverified run | verdict |
|---|---|---|---|---|---|
| **10 min** | 3 | +9 min | **+1.0 %** | ≤ 3 blocks | free, if the checkpoint is seconds |
| **1 hour** | 20 | +1 h | **+6.9 %** | ≤ 20 blocks | **recommended default** |
| **1 day** | 480 | +24 h | **+166 %** | ≤ 480 blocks | ⚑ this one hurts — it more than doubles end-to-end settlement latency |

## 4. What a longer cadence actually costs — three things, precisely

1. **Settlement latency**, as tabulated. Below `k` it is a rounding error; at a day it dominates.
2. **The length of the unverified provisional run.** `select` is a **tournament** with genuine
   3-cycles at real mainnet constants (`MinaChainSelection.beats_not_transitive`), so a peer
   controlling presentation order can walk the tip around a cycle. The ratchet cannot follow it —
   but anything *reading the tip* (a UI, a speculative execution) is reading a guess, and a longer
   cadence means a longer guess. `CheckpointCadence::run_cap` bounds it; past the cap the cheap tier
   **refuses** (`a_stale_run_refuses_to_move_the_tip`), converting a stalled checkpoint into a
   refusal rather than an ever-longer unverified prefix.
3. **Detection latency for what the cheap checks cannot see.** The cheap tier catches a broken parent
   link, a fabricated density window, non-canonical field elements, carried constants that disagree
   with the pin, and a Wrap proof of the wrong shape. It does **not** catch an invalid transaction or
   a stolen block reward — only the proof does. A longer cadence is a longer window in which the tip
   could be well-formed and not valid.

## 5. What a checkpoint costs — and the two costs that must not be conflated

### 5a. The cost to **CHECK** (what a light client pays)

| leg | object | measured / predicted |
|---|---|---|
| public-input words 11, 12 | 2 Poseidons (93 + 32 elements) + 62 endo expansions | **28.9 ms — MEASURED**, through the C ABI |
| `expand_deferred` | the six wire-dropped words | sub-ms; **NOT WRITTEN** |
| `public_comm` | 40-point Lagrange MSM (≈5.4 k complete adds) | ~45 ms predicted, at the rate below |
| phase-1 + phase-2 + IPA sponges | ~150 Poseidon permutations | ~45 ms predicted |
| opening relation (rung 5f) | 34 × 255-bit ladders (≈17 k complete adds) | ~150 ms predicted, at the rate below |
| **`⟨s, srs.g⟩` (rung 5h)** | **32,768-point MSM, 4,161,791 complete adds** | **35.1 s — MEASURED** |
| **the 2 accumulator MSMs (5g)** | **2 × 32,768, same shape** | **70.2 s — by symmetry** |
| | | **≈ 105 s per checkpoint, 99.7 % of it the three 2^15 MSMs** |

**⚑ THE 630× DID NOT TRANSFER. IT IS 359×, MEASURED (2026-07-30).** The row above is no longer a
ratio applied to a kernel cost — it is a clock.

The evaluator (`PastaIpaFold.msmHornerM` at `(p, b3 = 15, nbits = 255)`, driving
`PastaCurveComplete.rcbTraceM`: 12 mulmods, 2 const-muls, 19 add/sub-mods and one 33-field
allocation per complete add) was run standalone at **full scale — 32,768 points, 255 bit planes,
4,162,977 complete adds** — compiled by `leanc -O3`:

| | per complete add | one 2^15 MSM | peak RSS |
|---|---|---|---|
| **native (`leanc -O3`)** | **8.44 µs** | **35.1 s** | **18.8 MB** |
| interpreted (`lean --run`, = what `#guard` costs) | 12.31 µs | 51.2 s | — |
| kernel `decide` (prior lane, measured on hbox) | ~3.0 ms | ~3.5 h serial | ~28 GB |

Linear to within 0.5 % across n = 1024 / 4096 / 8192 / 32768. Box: **Apple M2 Max, one core.**

* **kernel → native compiled = 12,600 s / 35.1 s ≈ 359×**, not 630×. The 630× was `3.5 h / 20 s`
  where the 20 s had no located measurement anywhere in this tree — it appeared only in the sentence
  that defined the ratio.
* **kernel → `#guard` = 244×.** `#guard` uses Lean's *untrusted evaluator*, and this package sets no
  `precompileModules`, so it interprets imported IR. That costs 1.46× native here — small, because
  GMP dominates. **A `#guard` wall time is an upper bound on the compiled cost, never the compiled
  cost**; `lean_exe mina_sg_bench` exists to keep the two apart.
* ⚑ **Memory, which was the constraint that actually bit.** The kernel path peaks at ~28 GB (and
  near 75 GB per chunk when rooted, which is what made `lake build Dregg2` unable to finish). The
  compiled path peaks at **18.8 MB** — a factor of ~1,500 to ~4,000. **The reason `MinaWrapSg*` is
  allowlisted out of the root does not exist on this path.**
* Where the time is NOT: the bit-plane traversal (`as.zip ps` rebuilt per plane, 8.4 M
  `Nat.testBit`s) is **0.8 %** of the total — measured by running the same scan with all-zero
  scalars. Hoisting the zip out of the plane loop was implemented and measured: **no gain, 8.50 µs
  vs 8.57 µs**, i.e. inside the noise. It was not landed. The cost is the modular arithmetic, all of
  it: ~256 ns per 255-bit `Nat` mulmod including allocation.

**Evidence class, stated plainly.** The 35.1 s is measured on a **faithful standalone
re-expression** of the deployed evaluator — same `rcbTraceM` op sequence, same 33-field allocation,
same fold, full scale — not yet on the artifact. `metatheory/MinaSgBench.lean` (`lake build
mina_sg_bench`) measures the artifact itself and is self-checking in both polarities. **Its falsifier
is stated in the build request; if it comes in above ~5 min, the 10-minute row needs re-examining.**

**A lever left inside the pure-Lean path:** `PastaMsmWindowed` is already authored — bucketed at an
11-bit window is ≈ 0.86 M complete adds against 4.16 M, **~4.9×, ~7 s per MSM** — and it is algebra
needing its own identity theorem, not FFI. And openmina itself **defers and batches** the `sg`
accumulator check (`batch_dlog_accumulator_check`), so a client batching legs 5g/5h across
checkpoints is following the upstream design.

### 5a-bis. ⚑⚑ THE THIRD EVALUATOR: Lean calling out to Rust — 46 ms, and a better reason than speed

`metatheory/Dregg2/World.lean` already declares `@[extern "dregg_world_clock"]`,
`@[extern "dregg_world_recv"]`, `@[extern "dregg_world_rand"]`: the law stated in Lean, the
realization outside it. It has only ever been used for **effects**. Using it for **compute** is a
small extension of an established idiom, and the Rust side already holds real Pasta arithmetic —
the extractors link o1-labs' `proof-systems` and arkworks.

**MEASURED 2026-07-30, same box, same block, same statement**
(`metatheory/fixtures/pickles-extractors/src/bin/sg_msm_bench.rs`, `cargo run --release --bin
sg_msm_bench` — reproduces block 539508's `opening.sg` and refuses the one-generator tamper):

| evaluator | schedule | arithmetic | one 2^15 MSM |
|---|---|---|---|
| Lean kernel `decide` | sequential bit-plane, 4.16 M complete adds | kernel `Nat` | ~3.5 h, ~28 GB |
| Lean compiled (`leanc -O3`) | **the same** sequential schedule | boxed `Nat` + GMP | 35.1 s, 18.8 MB |
| **arkworks `msm_bigint`** | **bucketed (Pippenger)** | Montgomery + asm, rayon | **~46 ms** (44–56 ms, median of 5) |

**~760× over compiled Lean; ~274,000× over the kernel.** Two independent changes compound: the
schedule (4.16 M sequential adds → ~0.86 M bucketed) and the arithmetic (~256 ns per boxed `Nat`
mulmod → tens of ns in Montgomery form).

**⚑ THE COST TABLE COLLAPSES, AND SO DOES THE CADENCE QUESTION.** Three MSMs are **~140 ms**; the
transcript legs still in pure Lean are ~300 ms. **A checkpoint is well under a second.** At that
price a client can verify a Wrap proof **every block** (180 s), never mind every ten minutes, and
§3's table stops being a trade-off — every row is free except the one nobody wanted.

**⚑⚑ THE REAL REASON TO DO IT IS NOT THE SPEED.** Rungs 1–3 above compare the Lean kernel against
compiled Lean. That is **one definition evaluated two ways**: it catches evaluator bugs and nothing
else, and both readings share every modelling mistake, transcription error and wrong constant. The
Rust path is a **second implementation** — o1-labs' own `b_poly_coefficients`, arkworks' own MSM,
the code Mina itself runs. This is the discipline the rest of the campaign runs on: the Mina work
asserts **o1-labs' own verifier accepts a block** before anything is emitted, and the Samasika lane
drove **openmina's own consensus code** over 57 vectors and found **8 verdict divergences**. Neither
would have surfaced from re-evaluating our own model faster.

So calling out is not a shortcut around the check. **It upgrades the check from a re-evaluation to
a differential.** `scripts/run-mina-sg-compiled.sh` step (4) closes the chain with no linking and
no modular inversion: Rust asserts `arkworks_fold == gold_sg` and prints the point; Lean asserts
`lean_fold ≡ SG` by cross-multiplication and prints `SG`; the two lines matching gives
`lean_fold ≡ arkworks_fold`.

**⚠ WHAT A GREEN MEANS CHANGES, AND THE CHANGE MUST BE STATED.** A `#guard` that calls Rust is **no
longer kernel-checked**. It becomes a differential against an implementation whose correctness is
not in the TCB — which is *right* for an instance check and *wrong* for a checker theorem. So:

* **`Dregg2.Bridge.MinaWrapSg.sgVerdict` — the CHECKER — stays pure Lean and kernel-evaluable, and
  calls nothing.** Its theorem (`PastaIpaFold.msmHorner_eq_msmN`) is where the assurance lives.
* Only the weld's **INSTANCE evaluation** may call out, and an `@[extern] opaque` structurally
  cannot leak into a proof: `opaque` has no kernel reduction, so no `decide` can ever consume it.
  That is the same property `World.lean` relies on.
* **HOUSE LAW #1 is untouched.** It governs **AIR authorship** — constraints, gadgets,
  `air_accepts` — all of which stay Lean-authored and are not moved. What moves is the arithmetic
  that decides whether *this block's* fold lands on *this block's* `sg`. **A differential's job is
  to disagree with us, not to be trusted by us.**

**The seam, designed and priced, not yet written.** The right ABI keeps the SRS on the Rust side —
it is trusted config, not per-block data (§6.5), and `get_srs` already holds it — so the boundary
carries **15 challenges and one point**, ~17 field elements, and marshalling is free rather than
98,304 bignum conversions. `@[extern "dregg_mina_wrap_sg_fold"] opaque sgFoldNative (chals : @&(List
Nat)) : Option (Nat × Nat × Nat)`, with the differential in an executable (`moreLinkArgs` on a
`lean_exe`) rather than a `#guard`, so no `extern_lib` machinery and no `lakefile.lean` conversion
is needed. **Not written**: the linking is untested and the dependency question — whether
`mina-rust`/arkworks enters the node's graph or stays in the out-of-workspace extractor crate — is
a topology decision, not a lane decision.

⚑ **None of this retires the two measurements above.** The 359× and the ~1,500× memory collapse are
properties of the *pure-Lean* path, and the memory one is structural: **~28 GB → 18.8 MB means the
constraint that exiled `MinaWrapSg*` from the root does not exist on that path**, whether or not a
faster option exists beside it. Keeping both is the point — pure-Lean compiled buys
kernel-adjacency and no new trust; Rust FFI buys three orders of magnitude and a genuine second
opinion. **The checker runs neither.**

Two things could improve it and neither is in the estimate: `Circuit.Emit.PastaMsmWindowed` is
already authored (a windowed MSM instead of 32,768 independent ladders), and **openmina itself
defers and batches the `sg` accumulator check** (`batch_dlog_accumulator_check`). Legs 5g/5h are
exactly what Mina's own client defers — a checkpoint client batching them across checkpoints is
following the upstream design, not inventing a shortcut.

### 5b. The cost to **PROVE** the check (what dregg pays to make it a fact its chain can carry)

`MinaObserver::prove_opening_check` is **20.24 s MEASURED** on a real served block — for **4 of
10,922** slices of the `⟨s, srs.g⟩` MSM, as a dregg STARK. Extrapolated to the whole MSM:
`10922 / 4 × 20.24 s ≈ 15.4 hours`. **The proved checkpoint is a daily object at today's
throughput** and needs batching or parallelism to be anything else.

### 5c. So: three tiers, three cadences

| what closes | cost | duty cycle at 10 min | cadence it supports |
|---|---|---|---|
| the cheap tier (decode, link, density, `select`) | milliseconds | ~0 | **every block, 180 s** |
| a **checked** checkpoint, **Lean calling out to Rust** | **~0.45 s** (140 ms of MSM, measured) | 0.08 % | **every block**, and the question stops mattering |
| a **checked** checkpoint, **pure compiled Lean** | **~105 s**, 35.1 s of it measured | **17.6 % of one core** (5.9 % on three) | **10 min, with margin**; 1 h is free |
| a **checked** checkpoint in the kernel (today's rungs) | ~10.5 h *measured* (3 × 3.5 h) | 175× oversubscribed | **nothing below a day** |
| a **proved** checkpoint (a dregg STARK of the check) | ~15.4 h *extrapolated from a measurement* | — | **a day**, and only with batching |

**The headline, in pure Lean: a Mina checkpoint closes at a 10-minute cadence** — 105 s of
single-core compute inside a 600 s period — **because the 2^15 MSM moved from kernel `decide` to
compiled Lean. In the kernel it is 10.5 hours and nothing below a day is possible.** The move is
worth **359×** in time and ~**1,500×** in memory; it is not worth the 630× that was projected, and
105 s is not the 60 s that was projected either. Neither correction changes the recommendation:
105 s ≪ 600 s, so the 10-minute row survives with a 5.7× margin and the "+1.0 % of Mina's own
14.5 h" figure stands.

**And with the Rust differential beside it (§5a-bis), the cadence question dissolves entirely** —
~0.45 s per checkpoint, affordable every block. That path is a *second implementation* rather than a
faster reading of our own, which is why it is worth having for reasons other than the clock; and it
is **not in the TCB**, which is why it does not replace the row above it.

**What would change the recommendation.** If the artifact-true pure-Lean bench comes in ≥ 5× worse
than the standalone measurement — above ~3 min per MSM, ~9 min per checkpoint — the 10-minute
cadence stops having margin and the recommended default becomes the 1-hour row, which is +6.9 % of
a delay Mina already imposes on itself and still costs nothing that matters. **A day remains the
only bad option, and nothing measured here puts us near it.**

## 6. ⚑ What stays trusted — at every cadence

A cadence table must not hide the floor. Nothing below changes with `C`.

1. **The Wrap verifier index** — `MinaWrapIndexParams::DEVNET_BLOCKCHAIN` and the 56 `VK_INDEX`
   field elements. **The largest single trusted object under the whole proof story.** Nothing derives
   it from the chain; P8/P9 is not started. A wrong VK makes every checkpoint at every cadence a
   verification of the wrong claim, silently, and no amount of checking downstream can notice.
2. **`state_hash` is re-derived nowhere.** The hashes on every gate wire are supplied by the peer's
   framing (`docs/MINA-LIGHT-CLIENT.md` row 12): `state_hash = Poseidon("MinaProtoState")
   [previous_state_hash, body_hash]` and `Body.hash` absorbs `to_input` in an order that is **not**
   the binprot order. `previous_state_hash` **is** decoded and **is** a genuine parent link, so a
   *run* is checkable; a tip's own identity is not.
3. **Leader election is not checkable by any verifier.** `vrf_output` needs the delegator's secret
   scalar (`eval sk m = H(m, sk·H₂(m))`) and Mina ships no standalone VRF verifier. A client that
   verifies the Pickles proof **inherits** the threshold check. That is how Mina itself works and is
   not a defect of this design — but it means "we verified the block" never means "we checked who was
   allowed to produce it".
4. **The density window is bound-checked from the served value** wherever a parent is not exhibited —
   `MinaBinprot.decodeProtocolStateChecked`. The provisional tier now re-derives it instead
   (§2), so this is residual only where a parent is unavailable.
5. **The SRS** — that `srs.g` and `srs.h` are what they claim.
6. **The byte source, for availability only.** Every byte goes through the Lean decoder's refusals
   and then through `select`. The worst a malicious source achieves is to be refused, or to
   **withhold** — and withholding is not defensible by any light client at any cadence.
7. **The FRI/STARK floor** beneath any *proved* checkpoint, and Pickles'/IPA's own extraction
   argument (P10) beneath the check itself.

## 7. ⚑ What is not done, and no cadence fixes it

`Dregg2.Bridge.MinaWrapChallenges` derives a block's own IPA challenges **per block, compiled, from
wire data** — that is written, and `MinaWrapChallengesWeld` checks it reproduces the literals rung
5f's 153 s of kernel is stated over. It closes the wrong half of the problem's reputation: the
"153 s per block" in `bridge/src/mina_opening_check.rs` was a **kernel `decide` cost, never the
function's**, and the sponge continuation was already a compiled `#guard`.

**The real blocker is `public_comm`**, and through it `expand_deferred`:

* 34 of the 40 public-input words are reachable from bytes a peer already serves, and
  `bridge/src/mina_pickles.rs` `decode_proof_at` **already walks past every one of them** — it
  discards them because nothing asked. The census, with the width signature that discriminates a
  wrong slot map on real data, is `Dregg2.Bridge.MinaWrapPublicInput`.
* The other six — `combined_inner_product`, `b`, `zeta_to_srs_length`, `zeta_to_domain_size`, `perm`,
  `xi` — are `expand_deferred`'s outputs and **exist nowhere in this tree, in any language**.
* ⚑ And they need **nothing but the Wrap proof's own bytes**: `xi` and the evaluation scale come
  from an `Fr`-sponge seeded with `sponge_digest_before_evaluations`, which is public-input word 10
  and is on the wire; `combined_inner_product` is the fold of `prev_evals`, which is on the wire and
  which `MinaRealBlockGate.cipR` already reproduces; `b` is `b_poly` over
  `old_bulletproof_challenges`, on the wire. **There is no missing source, only missing
  computation** — which is what `docs/MINA-REAL-BLOCK-GATE.md` §8.3 already concluded.

Until `expandDeferred` exists, `WrapProver` has exactly one implementation that can say `Verified`
(the pinned height), and every other height is `WrapVerdict::Unavailable` — which
`bridge/src/mina_checkpoint.rs` treats as a refusal, with its own message, never as an `Ok` that
means "checked nothing".

## 8. Where the code is

| piece | file |
|---|---|
| the checkpoint loop, the two tiers, the ratchet theorems, `@[export] dregg_mina_checkpoint_advance` | `metatheory/Dregg2/Bridge/MinaCheckpoint.lean` |
| the 40-word public-input census + parameterised `publicCommOf` | `metatheory/Dregg2/Bridge/MinaWrapPublicInput.lean` |
| the per-block challenge derivation, `@[export] dregg_mina_wrap_challenges` | `metatheory/Dregg2/Bridge/MinaWrapChallenges.lean` |
| its reality gate against real devnet block 539508 | `metatheory/Dregg2/Bridge/MinaWrapChallengesWeld.lean` |
| the client, the cadence policy, the fail-closed arms | `bridge/src/mina_checkpoint.rs` |
| archive rooting (+1 and +0 modules, measured on the import graph) | `metatheory/Dregg2/FFI.lean` |
| export presence + `REQUIRED_DECISION_EXPORTS` | `dregg-lean-ffi/build.rs` |
| **the `2^15` MSM as a compiled checker** — `sgVerdict chals gens sg`, no fixture, `some true`/`some false`/**`none`** | `metatheory/Dregg2/Bridge/MinaWrapSg.lean` (ROOTED, +0 closure) |
| its instance differential on block 539508 — both polarities, plus the 32 chunk statements the kernel `decide`s | `metatheory/Dregg2/Bridge/MinaWrapSgWeld.lean` (not rooted; carries the fixture) |
| the native-compiled timing, self-checking in both polarities | `metatheory/MinaSgBench.lean`, `lake build mina_sg_bench` |
| the evaluator both paths share (`msmHornerM`, §3c) and the theorem that says it computes the MSM (`msmHorner_eq_msmN`) | `metatheory/Dregg2/Circuit/Emit/PastaIpaFold.lean` |
| runner for all three | `scripts/run-mina-sg-compiled.sh` |

## 9. ⚑ What the compiled path does NOT change

1. **It is not a proof.** `#guard` is Lean's untrusted evaluator. The kernel proves the CHECKER
   (`PastaIpaFold.msmHorner_eq_msmN`: the bit-plane scan computes the MSM, at arbitrary
   `AddCommGroup`, with the 255-bit budget a real hypothesis); a differential checks the INSTANCE.
   Rung 5h's 32 kernel theorems still say what they said and are not superseded — `MinaWrapSgWeld`
   §4 reproduces their 32 statements as `#guard`s precisely so the two paths are compared on one
   object rather than trusted separately.
2. **It binds CONTENTS, not a proof object.** `sg` really is `⟨s, srs.g⟩` over the real generators.
   The `5h-AIR` rungs (`PastaMsmBound`/`PastaMsmOnCurve`) force an emitted row's source to be
   `srs.g` at the index the manifest names and bind **no contents**. Neither subsumes the other.
3. **`srs.g` is still trusted** (§6.5). On-curve-checked — now in compiled code too, as part of the
   shape gate — but not derived.
4. **The RCB residual is still carried.** `PastaIpaFold` §3's group statement transports to §3c's
   `Nat`-triple evaluation by RCB'15 Thm 1, inherited from rungs 5a–5f. The compiled path adds no
   new assumption and removes none.
5. **`expand_deferred` is still the blocker** (§7). A fast `sg` leg does not make `public_comm`
   derivable, and until it is, every height but the pinned one is `WrapVerdict::Unavailable`.
