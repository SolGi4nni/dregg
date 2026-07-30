# Verifying Mina at a checkpoint cadence — what it costs, and what a longer one loses

**Status 2026-07-30, after the coordinator's first build run.** Build attempt 1 elaborated the three
Lean modules and **failed on three gate-rendering welds only** — `rewrite` could not find its pattern
because a two-level `match` does not iota-reduce under `rw`, and Lean inserted `sorryAx` to recover.
The axiom-hygiene check named those three theorems and **no others**, so the safety theorems below
(`provisional_never_ratchets`, `runSteps_finalized_monotone`,
`a_checkpointless_run_finalizes_nothing`) **elaborated clean in that run**. Build attempt 2 is
pending; the three welds have been restructured to a single-scrutinee shape and the 40-ladder kernel
`decide` demoted to a `#guard`.

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

That proviso is a theorem rather than a convention — and these three **elaborated clean** in the
coordinator's build run. `Dregg2.Bridge.MinaCheckpoint`:

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
| `public_comm` | 40-point Lagrange MSM | ~28 ms predicted |
| phase-1 + phase-2 + IPA sponges | ~150 Poseidon permutations | ~30 ms predicted |
| opening relation (rung 5f) | 34 × 255-bit ladders | ~24 ms predicted |
| **`⟨s, srs.g⟩` (rung 5h)** | **32,768-point MSM** | **~20 s predicted** |
| **the 2 accumulator MSMs (5g)** | **2 × 32,768** | **~40 s predicted** |
| | | **≈ 60 s per checkpoint, 99 % of it the three 2^15 MSMs** |

**Where the predictions come from, and their falsifier.** The kernel figures are measured: rung 5h
is **105 min of wall at 2-way parallelism ≈ 3.5 h of serial kernel, ~28 GB peak**, on this block, in
this tree. The kernel→compiled ratio is taken from a sibling that moved the *same shape* — a 2^15
MSM — from 3.5 h of kernel to a 20 s compiled path, **≈ 630×**. Every "predicted" row above is that
ratio applied to a measured kernel cost. **The falsifier is the build request's timing test**: if a
compiled 32,768-point Pallas MSM in Lean is not within an order of magnitude of 20 s, the 10-minute
cadence is not real and the table's first row goes away.

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

| what closes | cost | cadence it supports |
|---|---|---|
| the cheap tier (decode, link, density, `select`) | milliseconds | **every block, 180 s** |
| a **checked** checkpoint (compiled Lean Wrap verify) | ~60 s *predicted* | **10 min**, comfortably 1 h |
| a **checked** checkpoint in the kernel (today's rungs) | ~3.5 h *measured* | **nothing below a day** |
| a **proved** checkpoint (a dregg STARK of the check) | ~15.4 h *extrapolated from a measurement* | **a day**, and only with batching |

**The headline: a Mina checkpoint closes at a 10-minute cadence if the 2^15 MSM moves from kernel
`decide` to compiled Lean, and at nothing shorter than a day if it does not.** That single move is
the whole difference, and it is the same move a sibling already made once on the same shape.

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
