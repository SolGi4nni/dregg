# grain-fork

**Fork, rewind, and branch-and-stitch a hosted agent grain's mind — the "the mind is a umem
cell you own" superpower made real on the hosting substrate.**

A vendor hosts an agent as an opaque instance you cannot copy, roll back, or branch. A dregg
**grain** makes the *object* the source of truth: the mind is a committed `dregg_cell::Cell`
(its heap is the durable working-memory image, its c-list is its authority) wrapped by a
`hosted_lease::HostedLease` (rent + own-obligor economics). Because the mind is a real
committed cell, everything proven about cells becomes true of it.

## The core API (`src/lib.rs`)

| item | what it does |
|---|---|
| `Grain::rent` | mint a fresh root grain (mind balance 0 — value lives in the lease), open the lease at the mind's genesis root, commit the genesis checkpoint |
| `learn` / `forget` / `recall` | write / clear / read a `(MIND_COLL, key)` working-memory address (the per-address divergence a stitch folds) |
| `grant` / `revoke` / `holds` | the mind's c-list authority (the thing the settlement gate checks at the tip) |
| `checkpoint` / `rewind` | commit both state planes (heap + overflow fields) to the root-addressed timeline and advance the lease cursor; `rewind` is **fail-closed** — the reified image must re-derive its committed root under the kernel's real `compute_heap_root`/`compute_fields_root` (`BoundaryMismatch`) |
| `Grain::fork` | branch a child from the committed image at its checkpoint root, under its OWN lease; **no value or authority minted** (child gets only conferred caps the parent holds — `UnconferrableCap`) |
| `stitch` / `Grain::absorb` | merge a child back through the PROVEN pushout + authority gate; `absorb` is fail-closed three ways (`ForeignStitch` / `NotSettled` / `AbsorbDivergence`), staged on a scratch copy |

`confined.rs` adds `ConfinedSession` — the fork of a live *confined* session:

| item | what it does |
|---|---|
| `ConfinedSession::rent` / `wrap` | a grain welded to an egress `Confinement` + a receipt chain |
| `record_turn` / `receipt_head` / `verify_receipt_chain` | drive + fold the domain-separated `H(prev ‖ label ‖ cost)` chain a third party recomputes from `(chain_root, turns)` |
| `fork_two` / `fork` | ONE checkpoint → TWO (or one) sovereign lives — the four teeth below |

## What is proven vs. composed

The state pushout (`stitch_projections`) and the settlement-sound authority gate
(`settle_umem_stitch`) are the PROVEN pieces, CONSUMED from `starbridge_v2::umem_membrane`
(the operable shadow of `Metatheory.SettlementSoundness.stitch_drops_revoked_authority`) — this
crate does not reimplement the theorem, it calls it. Its contribution is the *composition*:
welding those onto the hosted grain (lease + committed mind cell).

## The four fork teeth (`ConfinedSession::fork_two`)

1. **Sovereign** — own lease/obligor, own committed mind, own confinement, own receipt chain.
2. **Attenuated, never amplified** — egress ⊆ parent (`EgressNotAttenuated`), caps ⊆
   parent-held (`UnconferrableCap`).
3. **Budget-conserving** — the two shares SUM to ≤ the parent's budget (`BudgetOverdraw`); the
   prepaid reserve is SPLIT, not duplicated.
4. **Independently verifiable + isolated** — each child's receipt chain is a fresh hash chain
   rooted at the SHARED fork root; a turn in one touches neither the other's mind (umem heap
   isolation) nor its receipt chain.

## How it fits the economy

Disjoint learnings fold clean; a same-address clash is a first-class `UmemConflict` (never
silent last-writer-wins); a cap revoked between branch and settlement is LINEAR-DROPPED at the
tip. State and authority are ORTHOGONAL, exactly as the proven shape requires. This is the
*committed-kernel-mind* fork surface; `grain-commons::fork` forks the *hosting `/var` image*
with pedigree — the named weld is to make the two roots the same 32 bytes.

## Tests

```sh
cargo test -p grain-fork
```

Note: `grain-fork` is a workspace `member` but not in `default-members`.
