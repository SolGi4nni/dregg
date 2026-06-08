# Guide: The Circuit, the Descriptor, and the Assurance Story

*A newcomer's orientation to how dregg2 turns a verified effect into a STARK-checkable circuit —
and, crucially, the **honest** per-effect assurance state: the circuit is NOT broadly verified.*

See also: [`../NAVIGATION.md`](../NAVIGATION.md) · [`executor.md`](executor.md) ·
[`../rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md`](../rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md) (the
ledger this guide summarizes).

---

## Read this first: the assurance is uneven

The most important fact, and the one most likely to be mis-stated: **the circuit is not broadly
class-A verified.** Out of ~56 effects:

- **~12 are genuine class A** — `transfer` (the keystone) + the economic family (mint, burn, the
  escrow/bridge-escrow family).
- **~40 are class C** — the descriptor binds the *frozen frame* + a balance/nonce leg, **but the
  field or side-table that IS the effect is not bound** by the deployed row's commitment.
- **~2 A−** (one residual each), **~2 D** (unverified).

The per-effect ledger ([`_CIRCUIT-ASSURANCE-PER-EFFECT.md`](../rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md))
is the authoritative source — it cites every theorem at `file:line` and was finalized 2026-06-08.
**A completion count is not an assurance count.** When you read "N effects emit a circuit," that says
nothing about whether the circuit *enforces the effect's real semantics*.

## The architecture, top to bottom

```
   verified effect (recKExec / universe-A *Spec)
            │  emit
            ▼
   EffectVmDescriptor  (Dregg2/Circuit/Emit/EffectVmEmit*.lean)   ← per-effect, in Lean
            │  satisfiedVm <descriptor> env  ⟹  post-state semantics   (the soundness theorem)
            ▼
   state_commit  (13 absorbed columns, anti-ghost)   (Dregg2/Circuit/StateCommit.lean)
            │  witness extraction
            ▼
   Plonky3 STARK  prove / verify   (circuit/src/, witness in Dregg2/Circuit/Witness/)
```

## What "class A" actually requires

A class-A effect has a from-scratch theorem of the shape

> `satisfiedVm <descriptor> env  ⟹  FULL per-cell post-state of the effect`

where **FULL** means: every field the effect *touches* is moved-or-frozen as the spec says; the
side-table / membership root that *is* the effect is **bound**; the **anti-ghost** commitment covers
all of it (tampering any of it changes `state_commit` ⇒ UNSAT); and it's welded to the verified
executor `recKExec` (or universe-A's validated `*_full_sound`), and is non-vacuous (a true witness
AND a refuted tamper witness).

**The keystone is `transfer`** (`Dregg2/Circuit/Emit/EffectVmEmitTransferSound.lean`):

| Theorem | What it gives |
|---|---|
| `transferDescriptor_full_sound:238` | `bal_lo` moved by the signed amount; `bal_hi`/8 fields/`cap_root`/`reserved` frozen — the full per-cell post-state. |
| `transferDescriptor_commit_binds_state:346` | the 13 state-block columns are determined by `state_commit` (anti-ghost). |
| `tampered_rejected:413` | tampering any of those columns ⇒ UNSAT. |
| `EffectVmEmitTransferUnify.unify_debit_exec:293` / `unify_credit_exec:297` | welded to `recKExec`. |

Every other effect is measured against this. (`#print axioms` on these → exactly
`{propext, Classical.choice, Quot.sound}`.)

## Why most effects are only class C — "conservation ≠ correctness"

The deployed EffectVM row's `state_commit` absorbs **exactly 13 columns**: `bal_lo, bal_hi, nonce,
fields[0..7], cap_root` (`EffectVmEmitTransferSound.absorbedCols`). It does **not** absorb the
cap-table digest as a *computed* root, nor any side-table digest (nullifiers, escrows, queue, seals,
sturdyrefs, supply totals) **unless that digest rides inside one of the 13 columns**.

So an effect whose real content is a *side-table mutation* (cap-table grant, nullifier insert,
note-commitment insert, seal write, cell-table insert) is bound by the descriptor **only if that
side-table's root is carried in `fields[i]`**. For most, it isn't — it rides `params`/`effects_hash`
or a separate record-layer commitment the deployed row doesn't carry. That's class C. The honest
discipline: the per-effect files **prove** the gap (e.g. `noteSpend_nullifier_insert_is_out_of_row`,
`createCell_offrow_unenforced`, `escrow_root_not_in_descriptor_commit`) instead of papering it.

## How the economic family got to class A

The escrow/bridge-escrow effects were promoted by a shared primitive
**`Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean`** that replaced the old *opaque additive step*
(`sys_digest_after = sys_digest_before + step_param`, prover-chosen) with **two in-row hash-sites**
that FORCE the root:

```
record_leaf = hash[id, creator, recipient, amount, asset, resolved]   -- amount = the moved amount
new_root    = hash[record_leaf, old_root]                              -- a prepend-accumulator advance
```

Now the side-table root is *genuinely recomputed* (`escrowRootAdvance_forced`), the moved amount IS
the parked record's amount, and tampering any record field provably moves the root ⇒ moves
`state_commit` ⇒ UNSAT (`escrowRoot_binds_record`). mint/burn were promoted by the per-cell class-A
capstone (`*_classA`): the moved column IS the whole per-cell effect (the global supply total is a
turn-level accumulator, the same boundary transfer's two-sided conservation has).

## The witness → STARK path

`Dregg2/Circuit/Witness/` + `Circuit/TransferWitness.lean` + `Circuit/TurnWitness.lean` build an
executor-derived witness and feed it to a **real Plonky3** `prove`/`verify` (Plonky3 rev `82cfad73`,
pinned in the root `Cargo.toml`). The anti-ghost tooth makes a forged state UNSAT. Whole-turn proofs
(`Circuit/TurnEmit.lean`, `CoordinatedTurnEmit.lean`) bind a turn's effects to **one authenticated
state root** per cell. The node commit path proves every finalized turn under `--prove-turns`.

## The Rust circuit (and why both exist)

`circuit/src/` holds hand-written Plonky3 AIRs (`effect_vm/*.rs`, `*_air.rs`). These are **kept as
diversity**, not deleted — the verdict in
[`_RUST-CIRCUIT-CONSOLIDATION.md`](../rebuild/_RUST-CIRCUIT-CONSOLIDATION.md) is "no blanket delete
yet." Where a Lean descriptor and a hand-AIR agree, that **differential** (`descriptor_agrees_with_executor*`)
is an *additional cross-check on top of* a from-scratch soundness theorem — never the sole assurance
(so class B is deliberately empty in the ledger).

## The verifier + codec

- **`Dregg2/Crypto/VerifierKernel.lean`** — `verify` is *defined* as "the extracted circuit is
  satisfiable", with `*_verify_sound` a *derived* theorem, not an assumed oracle.
- **`Dregg2/Exec/CodecRoundtrip*.lean`** + `wire/` — the FILL-J codec roundtrip proofs (the wire ↔
  Lean term marshalling that the FFI relies on).

## The roadmap (where the C effects go)

Ordered lowest-effort-first in the ledger's GAP LIST:

1. **A− four** — incrementNonce (add a `recKIncNonce` executor home), mint/burn supply-total,
   queue-family in-row root recompute.
2. **Cap-graph family** (attenuate/delegate/revoke/introduce/dropRef/grant/revoke) — ONE shared IR
   extension (a cap-table membership update gate) so `cap_digest_new` is *forced*, not asserted.
   Highest leverage: unlocks nine effects.
3. **Side-table-into-commitment** — widen `EFFECT_VM_WIDTH` so the deployed row carries the
   `system_roots` digest column (the "amplified-not-deployed" cohort; the Lean side is already
   proved, the gap is purely deployment + a Rust-side commitment-slot absorb).
4. **Privacy / membership** (noteCreate, noteSpend) — needs NEW IR: commitment-tree membership
   append, sorted-set / Merkle NON-membership (no-double-spend), and the §8 spending-proof gate.
   The genuine crown-jewel hard core.

## Where to start reading

1. [`_CIRCUIT-ASSURANCE-PER-EFFECT.md`](../rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md) — the ledger.
2. `Dregg2/Circuit/Emit/EffectVmEmitTransferSound.lean` — the class-A keystone, end to end.
3. `Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean` — how a side-table root is genuinely recomputed.
4. `Dregg2/Circuit/StateCommit.lean` — the 13-column anti-ghost commitment.
