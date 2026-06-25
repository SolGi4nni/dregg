# THE EPOCH — boundary/interior proving, one layout, one flag-day

*(approved scope, 2026-06-11; supersedes the relayout notes in REFINEMENT-DESIGN
where they conflict. This is the spec the build lanes execute against.)*

## The principle

**Hashing is a boundary phenomenon.** Inside one proof's transcript, state
consistency does not need authenticated structure: every read and write is a
tuple in a multiset, and a LogUp/grand-product argument proves
read-multiset = write-multiset (offline memory checking — Blum's theorem).
Authenticated structure (Merkle/Poseidon2) is needed only where a proof meets
the world: the commitments at its edges. The epoch's whole design follows from
making interiors hashless and edges rare.

Two standing refusals, restated: the edges stay **hash-based and post-quantum**
(Poseidon2-BabyBear, whose collision-resistance is the one floor we have
actually discharged against the real AIR) — no pairing/trusted-setup
commitments, ever, regardless of size advantages. And **all tables and
relations are emitted from Lean** (descriptor IR v2); Rust interprets.

## The tables (multi-table batch STARK)

| table | rows | role |
|---|---|---|
| **main** | one per effect | selector, register deltas, PI bindings — thin (~40–60 cols vs 1,654 extended today) |
| **poseidon2 chip** | one per permutation | every hash site becomes an (input, output) lookup — the measured 85% lever |
| **range** | table of limbs | range checks by lookup; kills range-bit columns; gives signed wells their two-limb discipline |
| **memory** | one per state access | the read/write multiset (offline memory checking) — registers, heap ops, cap checks, nullifier inserts pay ZERO hashing intra-proof |
| **map-ops** | one per boundary reconciliation | (root, key, value, op) → new_root openings, only where commitments materialize |

## Per-structure choices (by access pattern, not by habit)

- **Registers (16, named)**: not a map — direct limbs in the commitment.
  `FactoryDescriptor` gains the `fields` name declaration; compilation resolves
  indices.
- **Keyed maps with non-membership** (capabilities, nullifiers, heap): sorted
  Poseidon2 Merkle **at boundaries only** — the gap-opening machinery is
  proven (`sorted_gap_excludes`, `root_injective`) and stays. Intra-proof
  operations ride the memory table; sorted-insert is per-boundary
  reconciliation, not per-touch cost.
- **The receipt index**: an **append-only range structure (MMR)**, not a
  sorted map. History keys are dense positions; appends are amortized O(1)
  peaks and completeness holds by construction — the non-omission proofs
  specialize and get cheaper on exactly the structure that is append-only.
- **Hot intra-proof state**: no structure at all — pure multiset.

## The commitment layout

`recStateCommit` limbs, in order: cells root · the 16 registers · the map
roots **adjacent and uniform** (cap_root, nullifier_root, heap_root) · the
receipt-index root **last** (the `CommitBindsIndex` pin — whole-history
non-omission discharges by construction) · lifecycle · epoch · committed
height. Uniformity of map limbs is the universal-map forward-shape: a future
state component is a new collection id, never a new column.

**The derivability invariant (stated, not accidental):** every global root in
the commitment is derivable from the receipt record alone. The durable truth
is the commit log and the receipt chains; the executor's tables are caches of
strand heads; the maps are views. This is already true of the implementation —
the epoch makes it an invariant the assurance case states, so attested views
(`server_cannot_omit`) can be served by anyone and trusted by no one. The
self-certifying-receipt horizon (per-strand recursive attestation) is NOT in
this epoch: it earns its complexity only with many federations and untrusted
infrastructure, and the derivability invariant is the whole cost of keeping
that door open.

## What rides the one flag-day

1. The five tables + descriptor IR v2 (Lean emits table definitions, lookup
   relations, memory-op and map-op kinds; the Rust interpreter gains generic
   multi-table assembly — no authored constraints).
2. **Graduation completes**: the lookup/accumulator/membership constraint
   kinds are exactly what blocked Grant/Attenuate/Revoke/Custom/SetField —
   `CutoverFallback` and the legacy AIR path die.
3. **Cap-crown phase B**: in-circuit `granted ⊆ held` = membership lookup +
   lattice compare in the map-ops/guard machinery (task #103's circuit leg).
4. Registers 8→16 with names; RESERVED dies; the 186-column layout dies (the
   159 target is obsolete — the post-LogUp main table is far thinner).
5. **Signed wells** (Rust value model goes two-limb signed) + **genesis as
   issuer-moves** + **fees as moves** — guarantee B holds over the deployed
   chain; the assurance case's deployment-correspondence caveats close.
6. PI v3: committed-height column (closing the temporal gate's
   prover-chosen-height note), rateBound + challengeWindow caveat tags,
   selector binding carried forward.
7. One descriptor regeneration, one VK/commitment bump, succession drill.
   (q=38 already landed and rides the same Fiat–Shamir change.)

## New proof obligations (the honest list)

- **Blum's theorem in Lean**: multiset equality of reads/writes (with
  timestamps/serials) implies memory consistency — the semantic contract for
  the memory-op kind, sitting exactly where `sorted_gap_excludes` sits for
  maps. Classical, well-scoped.
- The MMR theory (append, peak bagging, range openings, positional
  completeness) — a specialization of the existing sorted-map work.
- Re-anchoring the per-effect faithfulness theorems onto IR v2 emission (the
  refinement tower's shape is unchanged; the emission target changes).

## Sequencing (one VK epoch at the end; verification batched on persvati)

1. Lean: descriptor IR v2 + Blum + MMR + the table emitters; faithfulness
   re-anchored. Continuous check: lake only.
2. Rust: interpreter multi-table assembly + witness generation restructure +
   the signed-well value model + genesis/fee moves.
3. The differential gauntlets replay (cell≡circuit per map; per-effect AGREE;
   the memory argument adversarial suite — a tampered read must refuse).
4. Regenerate, bump, drill. Deploy when ember says deploy.

## Expected landing

Per-turn proofs ~100–200 KiB (from 452); prover flat or faster (one hash-table
commitment replaces per-row aux); the last fallback arms gone; the two largest
correspondence caveats closed; the guard-ISA rearrangement (verb-compression
as circuit architecture) available later WITHOUT another flag-day, because the
guard atoms are already first-class lookups.
