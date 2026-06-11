# The Cell-Program Language — turn-context atoms, composite gates, and the staged closure

The constraint language a cell program is written in (`cell/src/program.rs`,
`StateConstraint` / `SimpleStateConstraint`) is the contract between an app
author and the executor: whatever the grammar can name, the executor enforces
on every turn that touches the cell. This document is the language design that
closes the gaps the real app-building lanes hit — each construct is justified
by a documented requirement from a lane that shipped an app, classified by its
coordination / disclosure / proving cost (the §8 discipline), and marked
either LANDED (no layout rotation) or STAGED (needs the rotation).

Sources for the requirements:

* the factory lane — `cell/src/blueprint.rs` module docs ("What the program
  CANNOT see") + the settlement e2e (`sdk/tests/factory_settlement_e2e.rs`);
* the polis lane — `starbridge-apps/polis/src/lib.rs` header, "Expressibility
  gaps" 1–7;
* the Lean guard algebra — `metatheory/Dregg2/Authority/{RelationalClosure,
  ArithmeticClosure, QuantifiedPredicate, ConfluenceClassifier}.lean` (the §8
  closure: affine half-spaces → bounded-degree polynomials → bounded
  quantifiers, each guard with a proved coordination-cost classification).

## Contents

1. [The gap list and the dissolution matrix](#1-the-gap-list-and-the-dissolution-matrix)
2. [Design principle: read what the executor already holds](#2-design-principle)
3. [LANDED — turn-context atoms](#3-landed--turn-context-atoms)
4. [LANDED — composite leaves (`PreimageGate` under guards)](#4-landed--composite-leaves)
5. [Cost classification of every construct (§8 discipline)](#5-cost-classification)
6. [STAGED — what needs the layout rotation](#6-staged--layout-rotation)
7. [STAGED — birth grants (factory-creator capability)](#7-staged--birth-grants)
8. [STAGED — first-class parameter imports (the cross-cell answer)](#8-staged--imports)
9. [The Lean lockstep](#9-the-lean-lockstep)
10. [What real-app naturalness still needs](#10-what-still-needs)

---

## 1. The gap list and the dissolution matrix

| # | Gap (source) | Construct | Status |
|---|--------------|-----------|--------|
| 1 | committed-value condition gates can't compose under state guards (blueprint) | `SimpleStateConstraint::PreimageGate` — the gate is now an `AnyOf`/`Implies` leaf | **LANDED** |
| 2 | programs can't see their own balance; "resolve drains the balance" was builder-shape (blueprint) | `BalanceGte` / `BalanceLte` atoms reading the sealed `CellState::balance` | **LANDED** |
| 3 | no factory-birth creator grant — the adopt-turn workaround (blueprint) | `FactoryDescriptor` birth-grant field (§7) | **STAGED** (design here, executor + Lean lockstep next) |
| 4 | fee ≡ computron budget couples deal balance to operational cost (blueprint) | not a constraint-language item — needs a second balance lane (§6.3) | **STAGED** (layout rotation) |
| 5 | no per-slot SENDER binding — WHO flips a slot was capability possession (polis 1) | `SenderIs` / `SenderInSlot` atoms; the binding idiom `AnyOf[Immutable{slot}, SenderIs{pk}]`; `CouncilCharter::with_member_keys` | **LANDED** (e2e: `approval_slots_are_actor_bound`) |
| 6 | no cross-cell reads — constitution params copied at birth (polis 2) | deliberately NOT a constraint (I-confluence cost, §8); instead first-class imports (§8 of this doc) | **STAGED** (descriptor `imports` block) |
| 7 | 8-slot budget caps councils at N≤3 (polis 7) | variable-length regions / slot-map grammar | **STAGED** (layout rotation, §6.1) |
| 8 | executed-action ≟ staged-hash needs receipt recomputation (polis 3) | a turn-payload commitment atom (`TurnEffectsHashIs`) reading the action's effect hash from `TransitionMeta` | **STAGED** (§6.2 — meta widening, no column change; small) |

The two LANDED constructs dissolve gaps **1, 2, 5** outright and weaken 8
(timeouts and knowledge gates now compose, so more of a ceremony is
program-held). Gaps **3** and **8** are small follow-ups that need executor
arms, not grammar redesign. Gaps **4, 6, 7** genuinely need the layout
rotation or a descriptor-level feature and are staged with designs below —
forcing them through the current grammar would produce a weak, dishonest
subset.

## 2. Design principle

**The smallest extension that dissolves the most gaps is to make
program-readable what the executor already holds at evaluation time.**

`evaluate_constraint_full(constraint, new_state, old_state, ctx, witnesses)`
already receives:

* `ctx.sender` — the acting cell's public key (plumbed by
  `turn/src/executor/execute_tree.rs` for every touched cell);
* `ctx.block_height` / `current_epoch` — already exposed (`TemporalGate`,
  `FieldGteHeight`…);
* `new_state.balance()` — the sealed computron balance rides on `CellState`
  itself; the evaluator could always reach it and simply had no atom naming
  it;
* the witness bundle — `PreimageGate` could always be checked, it just
  couldn't *compose*.

So gaps 1/2/5 were not missing machinery — they were missing *names in the
grammar*. No executor plumbing changed for any LANDED construct; the entire
uplift is grammar + evaluator arms + view projection + Lean mirror. That is
also why the blast radius stayed contained: the postcard encoding is
variant-index based and every new variant is APPENDED, so existing serialized
programs, factory VKs, and content addresses are byte-identical.

## 3. LANDED — turn-context atoms

New `SimpleStateConstraint` variants (and their `StateConstraint` lifts), all
composable under `AnyOf` / `Not` / `implies`:

```rust
SenderIs     { pk: [u8; 32] }   // turn sender == literal identity
SenderInSlot { index: u8 }      // turn sender == identity held in new[index]
BalanceGte   { min: u64 }       // own post-turn balance >= min
BalanceLte   { max: u64 }       // own post-turn balance <= max
```

Semantics (all fail-closed):

* `SenderIs` / `SenderInSlot` surface `MissingContextField` when no sender is
  in context (system turns), `ConstraintViolated` on mismatch. Inside `AnyOf`
  an unevaluable branch is a failed branch, never a pass; under `Not` the
  error propagates (negating an unevaluable predicate is unevaluable — the
  Heyting fail-closed contract of `evaluate_simple_constraint`).
* `BalanceGte`/`BalanceLte` read `new_state.balance()` — the post-effect
  balance of the touched cell — and need no context at all.

### The idioms these unlock

**Per-slot actor binding** (polis gap 5, the council's approval slots):

```rust
// approval slot i flips only in a turn whose sender is member i:
StateConstraint::AnyOf { variants: vec![
    SimpleStateConstraint::Immutable { index: approval_slot_i },
    SimpleStateConstraint::SenderIs  { pk: member_keys[i] },
]}
```

`Immutable` admits every turn that leaves the slot alone (propose, certify,
execute, the other members' approvals), so the ceremony stays open; flipping
the slot demands the bound sender. This is now installed by
`CouncilCharter::with_member_keys` (`starbridge-apps/polis`), and the e2e
`approval_slots_are_actor_bound` (`sdk/tests/polis_governance_e2e.rs`) proves
on the real executor that a member with a *genuinely granted* capability still
cannot flip another member's slot, a non-member capability holder can flip
none, and the operator can no longer relay approvals. Receipts-record-the-
signer is no longer the carry; the program is.

**Dynamic controller** (`SenderInSlot` + `WriteOnce` on the same slot): the
cell stores its own controller identity and re-points it by ordinary
governed writes — no descriptor reissue.

**The drain tooth** (blueprint gap 2):

```rust
// state == RESOLVED ⇒ balance == 0 (value can never be stranded):
when_state(STATE_RESOLVED_A, SimpleStateConstraint::BalanceLte { max: 0 })
```

and solvency floors (`BalanceGte` under an `OPEN`-state guard) for cells that
must retain a fee reserve. Note the balance these atoms see is the kernel
computron balance — gap 4 (deal-value vs operational-fee coupling) is a
*separate* problem the atoms make visible but do not solve (§6.3).

## 4. LANDED — composite leaves

`PreimageGate` joined `SimpleStateConstraint` (same fields, same evaluator —
`lift_simple` maps it onto the existing top-level arm, witness bundle
threaded through `evaluate_simple_constraint`). The blueprint's named blocker

> "The committed-escrow knowledge gate (release on a HASH-PREIMAGE reveal)
> needs `PreimageGate` under a state guard, which the current constraint
> grammar cannot express"

is now one line:

```rust
when_state(STATE_RESOLVED_A, SimpleStateConstraint::PreimageGate {
    commitment_index: CONDITION_SLOT, hash_kind: HashKind::Blake3,
})
```

(`cell/src/program.rs::tests::preimage_gate_composes_under_state_guard` is
the admit/reject/wrong-reveal/dormant pin.)

Deliberately NOT lifted into the composable fragment: `SenderAuthorized`,
`Witnessed`, `Custom`, `BoundDelta` — the registry-dispatched and cross-cell
shapes. Their proof-binding discipline (unique-blob binding, explicit
`proof_witness_index`) does not survive naive disjunction: an `AnyOf` branch
that *fails to verify a proof* must be distinguishable from one that *needs no
proof*, or a submitter strips proofs to slide down the cheap branch. Lifting
those needs the branch-witness-binding design (§6.4), not a quick grammar
edit. The general recursive-grammar refactor ("make `StateConstraint` one
recursive type") is therefore postponed wholesale: the only *demanded*
composite leaves were the knowledge gate (landed) and the context atoms
(landed); the rest of the demand is satisfied by `implies`/`AnyOf` over the
enlarged simple fragment.

## 5. Cost classification

Per the §8 discipline (`ConfluenceClassifier.lean`: a guard's true cost is
whether its invariant is I-confluent — coordination-free under merge — plus
what it discloses and what it costs to prove):

| Construct | Coordination (I-confluence) | Disclosure | Proving cost |
|---|---|---|---|
| `SenderIs` | **free** — predicate over the single turn's own context; no cross-turn invariant; merges trivially | the bound pk is a public descriptor literal | equality vs a context column (1 gate when sender lands in the PI; today executor-enforced) |
| `SenderInSlot` | free (as above; the slot read is post-state-local) | controller identity is public state | 1 equality vs a state column |
| `BalanceGte { min }` | **floor guard — NOT i-confluent in general** (a lower bound on a *decrementable* quantity is the `bounded_resource_not_iconfluent` pole when concurrent debits exist; single-cell serial execution makes it safe today, n>1 forces ordering on the cell) | balance becomes program-visible (it already is ledger-visible) | 1 range gate |
| `BalanceLte { max }` | for `max = 0` under a terminal guard: monotone-terminal, confluence-keeping (the cell is inert after); general ceilings are the bounded pole — ordering | as above | 1 range gate |
| `PreimageGate` (simple) | free — witness-local | the *reveal* discloses the preimage to the chain (by design: it is a reveal gate) | the hash gadget (Poseidon2 in-AIR; BLAKE3 executor-side) |
| existing affine/`MemberOf`/`Reachable`… | classified in `RelationalClosure`/`ConfluenceClassifier`: monotone floor = free, ceilings = ordering, relational = decided-by-merge | public literals | linear gates |

The classifier's verdict is the language's honesty contract: a council using
`BalanceGte` as a treasury floor must know it is choosing a tier-ordering
guard, and the docs of each atom say so. Nothing landed here changes any
cell's tier: today's executor is the single serializer (n=1 collapses the
bounds, per the single-machine principle), and the atoms' classifications are
recorded for the day the topology widens.

## 6. STAGED — layout rotation

These need changes to what the commitment scheme / circuit columns assume and
are *designed now, staged for the rotation* (VK + cell-commitment bump, the
same v-bump lane as the cap-root Phase A):

### 6.1 Variable-length regions (gap 7)

`STATE_SLOTS = 8` is baked into `CellState`, the canonical state commitment,
and the Effect-VM state columns. The grammar for the successor is the
*name-keyed record* the Lean side already uses (`Exec/Value.lean` records,
`Exec/Program.lean` constraints keyed by `FieldName`, `FieldsMap.lean` for the
flatten): constraints address named fields, the commitment becomes a keyed
Merkle/Poseidon map (the `cap_root` openable-sorted-map pattern is the
precedent), and the 8-slot array becomes the degenerate fixed schema. The
council then constrains `approval[m]` for any member id `m`; `MAX_MEMBERS`
dies. **Grammar verdict: do NOT pre-land a slot-map grammar against the
8-slot layout** — every name-keyed constraint would be a lie until the
commitment opens; this is one rotation, done once, with the Lean record
semantics as the spec (it is already proved there).

### 6.2 Turn-payload commitment (gap 8) — small, near-term

`TransitionMeta` already carries `method` and the effects mask. Widening it
with the action's canonical effects-hash (which receipts already compute)
gives `TurnEffectsHashIs { slot: u8 }` — "this transition is admitted only if
the turn's effect payload hashes to the value staged in `slot`" — and the
council's EXECUTED arm becomes `AnyOf[Not(state==EXECUTED),
TurnEffectsHashIs{PROPOSAL_HASH_SLOT}]`. No column change (executor-enforced
first, like `RateLimit`), but it is meta-plumbing in the executor + receipt
snapshot semantics, so it is staged behind the actor-binding wave rather than
rushed into it.

### 6.3 The second balance lane (gap 4)

Deal value and computron budget are ONE `u64` today. The blueprint's
"fee≡computron-budget couples deal balance to operational cost" needs an
asset-valued balance separate from the execution meter — that is a kernel
state-shape change (an `AssetId := issuer-cell` map per DREGG3 §) and rides
the same rotation as 6.1, not a grammar item.

### 6.4 Witnessed branches in disjunctions

To put `SenderAuthorized`/`Witnessed`/`Custom` under `AnyOf`, each branch
needs an explicit witness binding (`branch_witness_index`) so proof-stripping
cannot select a cheaper branch ambiguity. Design: an `AnyOfBound { branches:
Vec<(SimpleOrWitnessed, Option<u8>)> }` where every witnessed branch names its
blob; the unique-blob global scan (audit item 4) stays for the legacy shapes.
Demand-driven — no current app blocked on it.

## 7. STAGED — birth grants

Gap 3: a factory-born cell has no capability holder until the operator runs
`execute_as(cell, self-grant, ADOPT_TURN_FEE)` — the "adopt turn" that every
plan (`crate::factories`, `dregg_sdk::polis::bootstrap_plan`) cargo-cults and
that costs a funded fee before the cell can do anything.

Design: a `creator_grant: Option<CapTemplate>` field on `FactoryDescriptor`.
At the `CreateCellFromFactory` arm the executor installs the instantiated
capability (target = the new cell, holder = the creating turn's agent)
atomically with the birth — content-addressed like everything else in the
descriptor, so "what the creator can do from birth" is part of the factory's
identity. Touches: `cell/src/factory.rs` (descriptor + hash), the executor's
factory-birth arm (`turn/src/executor/apply.rs`), and **Lean lockstep is
mandatory in the same change**: `Dregg2/Exec/Factory.lean`'s
`createCellFromFactory` model gains the same grant-at-birth so the
cap-conservation keystones (no-amplification: the grant ⊆ the descriptor's
`allowed_cap_templates`) are proved, not assumed. The adopt-turn then becomes
a compatibility path, and `bootstrap_plan` drops a whole funded turn. Staged
because it is an executor+kernel change in the capability lane (the cap-crown
D remains open there), not a constraint-grammar item.

## 8. STAGED — imports

Gap 6 (cross-cell reads) stays OUT of the constraint language deliberately:
a guard that reads another cell's live state makes every turn on this cell
order against every turn on that cell (the I-confluence cost is exactly the
`relational_decided_by_merge` arm with a non-local relation — coordination,
always). The polis already proved the copied-parameter pattern is *sound*
(content-addressing makes a lying builder visible); what it lacks is being
*first-class*. Design:

```rust
// FactoryDescriptor
imports: Vec<ImportedParam> // { name, source_cell, source_slot,
                            //   value: FieldElement, provenance: ReceiptRef }
```

The descriptor records WHERE each copied literal came from (cell, slot, and
the receipt/height at which it held that value); `dregg explain` and the
inspectors render "this council threshold was imported from constitution v3
at height H". Verification is recomputation against the receipt chain —
exactly what verifiers do today, minus the archaeology. An amendment-reissue
then *visibly* supersedes stale imports. No executor semantics change; this
is descriptor schema + tooling, staged behind the birth-grant work.

## 9. The Lean lockstep

The mirror is layered so every existing keystone survives untouched:

* **`Dregg2/Exec/Program.lean`** (LANDED, this change):
  `SimpleConstraint` gains `senderIs / senderInField / balanceGe / balanceLe /
  preimageGate`; the ctx-less `evalSimple` evaluates all five FAIL-CLOSED
  (mirroring `MissingContextField`); the new `TurnCtx` structure
  (`sender/balance/revealedHash`, all `Option`, absence = reject) feeds the
  new `evalSimpleCtx / evalConstraintCtx / RecordProgram.admitsCtx`.
  Conservative-extension keystones: `evalSimpleCtx_empty`,
  `evalConstraintCtx_empty`, `admitsCtx_empty` (the empty context recovers
  the old evaluator exactly — every prior guard theorem lifts verbatim).
  Admit-characterizations proved for every atom
  (`evalSimpleCtx_senderIs_iff`, `…_senderInField_iff`, `…_balanceGe_iff`,
  `…_balanceLe_iff`, `…_preimageGate_iff`) and THE actor-binding keystone
  triple: `actorBound_owner_flips` / `actorBound_flip_requires_sender` /
  `actorBound_untouched_open` — the Lean statement of "approval slots are
  actor-bound". All `#assert_axioms`-clean, with `#guard` non-vacuity pairs
  per atom (the council binding, the drain tooth, the committed release).
* **`Dregg2/Exec/EffectsState.lean` (`stateStepGuarded`)** — the kernel's
  per-slot caveat gate already evaluates `(actor, old, new)` and its
  `SlotCaveat.senderAuthorized (authorized : List CellId)` *already contains*
  the per-slot actor binding (a singleton list IS `senderIs`); the
  `stateStepGuarded_*` family needed no change. NEXT (with birth grants /
  the rotation): thread the cell's own balance into `SlotCaveat.eval` so the
  balance atoms gain kernel-level twins, and extend
  `Exec/Factory.lean::createCellFromFactory` for §7.
* **`Dregg2/Authority/{RelationalClosure, ArithmeticClosure,
  QuantifiedPredicate}.lean`** remain the closure spec for the rotation
  grammar (§6.1): when constraints go name-keyed, the runtime should expose
  `RelPred`/`ArithPred` instances, not more one-off atoms.

Downstream Lean importers (`FieldsMap`, `RecordKernel`, `RecordCell`,
`StateMigration`, `Proof/WP`, `DSL`) all build unchanged against the extended
inductive (verified in this change).

## 10. What still needs

Honest residue after this wave, in priority order:

1. **The slot ceiling is the naturalness ceiling** (§6.1). Councils of 3,
   7-field deal schemas, path predicates squeezed into `seg_indices` — every
   app still *feels* the 8 slots. The rotation to name-keyed records is the
   single highest-leverage move left and it is a layout change, not grammar.
2. **Birth grants** (§7) — every app plan still carries the adopt-turn wart.
3. **Turn-payload commitment** (§6.2) — "the execute turn performs exactly
   the proposed action" should be a program tooth, not receipt archaeology.
4. **AIR parity for the new atoms** — `SenderIs`/`Balance*` are
   executor-enforced; the slot-caveat PI manifest
   (`turn/src/executor/mod.rs::project_slot_caveat_manifest`) defers them
   like the other context-dependent variants. The sender pk and balance are
   natural context columns for the rotation's PI layout.
5. **The second balance lane** (§6.3) for real markets.
6. **DSL surface** — `dregg_program { … }` (Lean `DSL.lean`) and the Rust
   builders should grow `sender is`, `balance >=`, `reveals` sugar so app
   authors write the idioms, not the encodings.
