# Samasika: what we found formalizing it

**Date:** 2026-07-29 · **Status:** findings, machine-checked in Lean, differentialed against real
implementations and real chain data.

This document exists to be **readable by someone outside this repo** — in particular by Mina
contributors — because three of these findings are about Mina's own artifacts rather than about ours.
Everything below is either a Lean theorem, a differential against a real implementation, or a replay
against real chain data. Where something is measured rather than proved, it says so.

Provenance: `Dregg2/Bridge/MinaChainSelection.lean`, `MinaChainSelectionDifferential.lean`,
`MinaSlidingWindow.lean`, `MinaVrfThreshold.lean`; extractors and fixtures under
`metatheory/fixtures/samasika-forks/` and `metatheory/fixtures/samasika-density/`, both in-tree.

**Reading the citations.** Those four `.lean` paths and the two `fixtures/` directories are the only
paths in this document that live in **this** repository. Every other `file:line` — `proof_of_stake.ml`,
`constants.ml`, `consensus_vrf.ml`, `slot.ml`, `global_slot.ml`, `global_sub_window.ml`, `mainnet.mlh`,
`devnet.mlh`, and the consensus spec `README.md` under their `docs/specs/consensus/` — is
**upstream `MinaProtocol/mina`**, and
`consensus.rs`, `block.rs`, `bigint.rs`, `generated.rs` are **upstream `openmina/openmina`**. Line
numbers are as of 2026-07-29 and will drift; the surrounding identifier is the durable reference.

---

## 1. `select` is not a total order — it is a tournament

`beats_not_transitive` exhibits genuine 3-cycles — `B` beats `A`, `C` beats `B`, `A` beats `C` —
`decide`-checked at **real mainnet constants**, by two independent mechanisms:

1. **Mixed regime.** `is_short_range` partitions pairs differently, so different *pairs* are judged by
   different rules (longest-chain vs. relative density).
2. **Long regime alone.** The relative minimum window density **is not an intrinsic scalar**. It is a
   function of the *pair*, via `max_slot`. `relative_density_is_pair_dependent`: the same chain
   measures **70** against a rival at its own slot, and **7** projected twelve slots forward.

The second is the structural one, and it survives even if the first is dismissed as a boundary case.

**Consequence.** "The canonical chain" is **not a function of a candidate set**. Folding `select` over
a list of candidates is order-dependent, and a peer that controls presentation order can walk a node
around a cycle. Any implementation that reduces a candidate set with `select` inherits this.

We did not work around it. `minaBetterTip` is a **pairwise** comparison against a fixed anchored
segment, and `minaBetterTip_is_not_foldable` states the limitation as a theorem rather than leaving it
as folklore.

*Also proved:* determinism (selection factors through an eight-field key, by `rfl` — which typechecks
only because nothing else is projected), irreflexivity, **asymmetry** (an invariant the OCaml only
QuickChecks, `proof_of_stake.ml:4617`), ties-only-on-equal-keys, and transitivity *restricted* to
pairwise-short-range tips.

---

## 2. openmina and the daemon adopt different chains

Driving **openmina's own `mina_core::consensus`** over 5 real fork pairs (openmina's own test
fixtures, re-asserted in Rust before emitting) plus 52 vectors derived by moving `curr_global_slot`
across sub-window and grace-period boundaries in both orientations:

| | rows |
|---|---|
| match our Lean rendering | **57 / 57** |
| differ from openmina in relative density | **30 / 57** |
| **differ from openmina in the final verdict** | **8 / 57** |

Three compounding defects, each now a theorem:

- **Shift count in slots, not sub-windows.** openmina measures the shift in *slots* where the daemon
  works in *sub-windows* (`consensus.rs:88`). Note the written spec's §5.4.12 contradicts its own
  §5.4.9 here, so this is a spec ambiguity as much as an implementation choice.
- **`for _ in 0..=shift_count`** (`consensus.rs:101`) zeroes one sub-window more than the pseudocode
  it transcribes.
- **`GRACE_PERIOD_END = 1440`** hardcoded (`consensus.rs:15`) against the daemon's derived **2237**.

`three_renderings_three_answers` pins a single question at **50 (daemon) / 23 (openmina) / 28 (the
spec document's own pseudocode)**.

Separately: openmina's `is_short_range_fork` keys on `epoch_count` where the daemon keys on
`curr_global_slot / slots_per_epoch` (`proof_of_stake.ml:1140`). Since `epoch_count` increments by one
per *transition*, these diverge **permanently after any fully-empty epoch**. It also drops the
daemon's `Slot.succ`, an off-by-one at the boundary slot.

⚠ openmina's **block-production** density (`crates/ledger/src/proofs/block.rs:1116`) **is** a faithful
port. The two paths live in the same repository and disagree with each other.

⚠ **openmina's fork fixtures no longer deserialize with openmina's own types**
(`curr_global_slot` → `curr_global_slot_since_hard_fork`, `generated.rs:204`), so the only tests it
has over its chain-selection code do not currently run.

---

## 3. `grace_period_end` is 2237, not 1440

`mainnet.mlh` ≡ `devnet.mlh` byte-identical: `grace_period_slots = 2160` (`:20`),
`slots_per_window = 77` (`constants.ml:227`), so `grace_period_end = 2237` (`constants.ml:239-241`).

The written spec's constants table — upstream, at
<https://github.com/MinaProtocol/mina/blob/develop/docs/specs/consensus/README.md#L107>, **not a path
in this repo** — says **1440**, and openmina
hardcodes **1440**. Two independent lanes here caught this from opposite directions.

---

## 4. The density bound is not an invariant of the update function

`d[i] ≤ slots_per_sub_window` is **not** preserved by the window update alone —
`density_bound_is_not_a_step_invariant` shows `step` yielding **8** on mainnet constants, by `decide`.
What preserves it is `step` *composed with* the strict slot increase that block validity enforces
(`proof_of_stake.ml:1976-1987`; in-circuit `:2201-2207`).

**A light client replaying the window must independently check `parent.slot < child.slot`.** The
density arithmetic never re-checks it — and a backwards slot is not *refused*, it is **mis-computed**:
the same 21-sub-window gap reads as density **77** backwards and **0** forwards, because
`overlapping` becomes vacuously true and stale entries are retained. Both directions proved.

---

## 5. The window replay reproduces the chain, and the surface API cannot seed it

**849 real consecutive canonical devnet transitions**, replayed from **one seed and the slot sequence
alone**, reproducing every block's own reported `min_window_density` *and* its 11-entry
`sub_window_densities`. **Zero mismatches.** Two runs — heights 539482–539772 (290 transitions), and
302561–303120 (559 transitions, an outage era where the minimum walks **34 → 14 → 8 → 3**, slot gaps
to 43). Two mutations (dropping the projection; an off-by-one ring index) are refuted by both runs.

The slide law, which the source states as two comparisons without saying what they compute: index `i`
carries sub-window `prevGsw − age i` with `age i = (prevRel + 11 − i) % 11`, and the entry survives
exactly when `age i + diff ≤ 11`. Proved exhaustively over 11 ring positions × 11 shifts × 11 indices.

⚠ **`subWindowDensities` is not a field of the public GraphQL `ConsensusState`** (probed live against
`api.minascan.io/node/devnet`; resolver `proof_of_stake.ml:2440-2536`). `minWindowDensity` is exposed;
the array is not. **So the long-range selection rule cannot be evaluated from the public API at all.**
The short-range rule can. This replay had to use the precomputed-block archive — where a bare height
lookup returned **4 linked blocks out of 301**, the rest orphans, so the run required walking
`previous_state_hash` backwards.

---

## 6. Leader election is not checkable by a light client

Of the threshold's three inputs, only `total_stake` is in the header.

- `my_stake` is `winner_account.balance` from the **staking epoch ledger** under a checked Merkle path
  (`proof_of_stake.ml:718-731,765`). The header carries the ledger *hash*; a client needs per-block
  inclusion proofs into a ~6,200-account ledger.
- **`vrf_output` cannot be recomputed by a verifier at all.** `eval sk m = H(m, sk·H₂(m))` requires the
  delegator's *secret* scalar. It can only be **proved** — which Mina does inside the blockchain SNARK,
  where the threshold constraint also lives. **Mina ships no standalone VRF verifier**; openmina's
  `mina_vrf` is evaluation-only.

So a client that verifies the Pickles proof **inherits** the threshold check; an independent check is
not available. Our `MinaVrfThreshold` is therefore a **specification of what that proof asserts**, not
a second opinion.

**The asymmetry is the result:** of Samasika's two mechanisms, the density window is checkable from two
consecutive headers and nothing else, and leader election is not checkable at all.

*Also:* the threshold's eleven Taylor coefficients were **derived** in Lean from `f = 3/4` by Mina's own
`Snarky_taylor.Exp.params` algorithm and proved equal to the integers openmina hardcodes
(`block.rs:317-345`), with an independent Python re-derivation matching first. The OCaml comment says
`2^256` where the code divides by `2^253` (`consensus_vrf.ml:208,228-234`).

**The 20-bit quantisation cliff.** The stake fraction is floored to `per_term_precision = 20` bits
*before* the series, so any delegation below `total / 2^20` has a threshold of **exactly zero** and wins
only on a VRF output of exactly zero. On devnet at time of writing that is **1510.919197082 MINA** —
below it, block production is arithmetically impossible rather than merely unlikely.

---

## Scope and honesty

- Selection assumes both tips are **already valid**. This is not block validation.
- All of this is **off-circuit**: Mina does not prove selection in a SNARK either (the in-circuit
  density code is block *production*, a different function).
- Not covered by real data: the **disjoint-window** branch (devnet never went dark >11 sub-windows in
  the ranges replayed) and the **grace period** (unreachable on any modern block). Both are covered by
  the exhaustive slide law and constructed cases instead.
- We deliberately added **no `@[export]`** for selection: its long-range branch needs data the public
  API does not supply, so an export would be a gate nothing could call.
