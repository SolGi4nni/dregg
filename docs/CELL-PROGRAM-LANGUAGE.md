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
11. [The next rungs — grammar that makes a REAL app natural](#11-the-next-rungs)

---

## 1. The gap list and the dissolution matrix

| # | Gap (source) | Construct | Status |
|---|--------------|-----------|--------|
| 1 | committed-value condition gates can't compose under state guards (blueprint) | `SimpleStateConstraint::PreimageGate` — the gate is now an `AnyOf`/`Implies` leaf | **LANDED** |
| 2 | programs can't see their own balance; "resolve drains the balance" was builder-shape (blueprint) | `BalanceGte` / `BalanceLte` atoms reading the sealed `CellState::balance` | **LANDED** |
| 3 | no factory-birth creator grant — the adopt-turn workaround (blueprint) | `FactoryDescriptor` birth-grant field (§7) | **STAGED** (design here, executor + Lean lockstep next) |
| 4 | fee ≡ computron budget couples deal balance to operational cost (blueprint) | not a constraint-language item — needs a second balance lane (§6.3) | **STAGED** (layout rotation) |
| 5 | no per-slot SENDER binding — WHO flips a slot was capability possession (polis 1) | `SenderIs` / `SenderInSlot` atoms; the binding idiom `AnyOf[Immutable{slot}, SenderIs{pk}]`; `CouncilCharter::with_member_keys` | **LANDED** (e2e: `approval_slots_are_actor_bound`) |
| 6 | no cross-cell reads — constitution params copied at birth (polis 2) | a *live* read stays NOT-a-constraint (I-confluence cost, §8); the *finalized* read IS a constraint — `ObservedFieldEquals` (§11.2), a witnessed cross-cell read of a peer's finalized field (free because finalized = monotone). The descriptor `imports` block (§8) remains the first-class copied-literal form. | **LANDED** (`ObservedFieldEquals`, §11.2); imports STAGED |
| 7 | 8-slot budget caps councils at N≤3 (polis 7) | variable-length regions / slot-map grammar | **STAGED** (layout rotation, §6.1) |
| 8 | executed-action ≟ staged-hash needs receipt recomputation (polis 3) | a turn-payload commitment atom (`TurnEffectsHashIs`) reading the action's effect hash from `TransitionMeta` | **STAGED** (§6.2 — meta widening, no column change; small) |
| 9 | N≤3 council / multi-admin boards re-enumerate `AnyOf[SenderIs…]` by hand (apps) | `SenderMemberOf { members }` — sender ∈ literal id-set, one atom | **LANDED** (Lean `senderMemberOf`; e2e idiom `AnyOf[Immutable, SenderMemberOf]`) |
| 10 | no per-turn spend/withdrawal RATE bound — only absolute floors/ceilings (apps) | `BalanceDeltaLte`/`BalanceDeltaGte` (own-balance rate gates) | **LANDED** (Lean `balanceDeltaLe`/`balanceDeltaGe`) |
| 11 | no COMBINED multi-field per-turn budget — `DeltaBounded` is single-field (apps) | `AffineDeltaLe { terms, c }` — `Σ kᵢ·Δfieldᵢ ≤ c` | **LANDED** (Lean `affineDeltaLe`) |

The two original LANDED constructs dissolve gaps **1, 2, 5** outright and weaken 8
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

A second wave of turn-context atoms (apps gaps 2/3/4) landed the same way —
each is the Rust twin of a now-proven Lean atom in
`metatheory/Dregg2/Exec/Program.lean`, appended variant-index-based so factory
VKs and content addresses stay byte-identical:

```rust
// SimpleStateConstraint (compose under AnyOf / Not):
SenderMemberOf  { members: Vec<[u8; 32]> }  // turn sender ∈ literal id-set
BalanceDeltaLte { max: i64 }                // new.balance − old.balance <= max
BalanceDeltaGte { min: i64 }                // new.balance − old.balance >= min
// StateConstraint only (reads BOTH old and new — does not lift into the
// post-state-local simple fragment, exactly as in Lean):
AffineDeltaLe   { terms: Vec<(i64, u8)>, c: i64 }  // Σ kᵢ·(new[fᵢ]−old[fᵢ]) <= c
```

These dissolve the app-lane gaps the first wave could not:

* **`SenderMemberOf`** is the clean **multi-admin actor binding** — the
  `AnyOf[SenderIs{a}, SenderIs{b}, …]` idiom a board would have to widen by
  hand each time a member joins, as ONE atom. The N-member per-slot binding is
  `AnyOf[Immutable{slot}, SenderMemberOf{board}]` (the generalization of the
  single-key polis tooth). Lean twin `senderMemberOf` /
  `evalSimpleCtx_senderMemberOf_iff`.
* **`BalanceDeltaLte` / `BalanceDeltaGte`** are the per-turn balance **rate
  gates** (a withdrawal-cap / spend-floor): they bound `new.balance −
  old.balance`, where the pre-turn balance is the executor's already-plumbed
  `old_state` (`CellState::balance` BEFORE the effect — the `balanceBefore`
  twin; no `EvalContext` change was needed). Bounds are SIGNED (`i64`,
  mirroring the Lean `Int`): a negative `max` forces a loss, a negative `min`
  caps a loss. Lean twins `balanceDeltaLe`/`balanceDeltaGe` /
  `evalSimpleCtx_balanceDeltaLe_iff`/`_balanceDeltaGe_iff`.
* **`AffineDeltaLe`** is the genuine **multi-field delta gate** the
  single-field `DeltaBounded`/`FieldDelta` cannot express — a treasury's
  COMBINED per-turn outflow across several spend slots (`[(1,out_a),(1,out_b)]
  ≤ budget` over the deltas), or a weighted basket `2·Δprice − Δindex ≤ k`. It
  reads both `old_state` and `new_state` (so, like the Lean `affineDeltaLe`, it
  is a `StateConstraint`, not a liftable simple). Lean twin `affineDeltaLe` /
  `evalConstraint_affineDeltaLe_iff`.

(The Rust evaluator arms, the `affine_delta_sum` helper, and the
admit/reject/fail-closed unit pins `sender_member_of_binds_multi_admin` /
`balance_delta_atoms_bound_the_rate` / `affine_delta_le_bounds_combined_outflow`
are in `cell/src/program.rs`. Each Rust arm mirrors its named Lean
admit-characterization — LAW #1: the evaluator never authors new semantics.)

Semantics (all fail-closed):

* `SenderIs` / `SenderInSlot` / `SenderMemberOf` surface `MissingContextField`
  when no sender is in context (system turns), `ConstraintViolated` on
  mismatch / off-board. Inside `AnyOf` an unevaluable branch is a failed
  branch, never a pass; under `Not` the error propagates (negating an
  unevaluable predicate is unevaluable — the Heyting fail-closed contract of
  `evaluate_simple_constraint`).
* `BalanceGte`/`BalanceLte` read `new_state.balance()` — the post-effect
  balance of the touched cell — and need no context at all.
* `BalanceDeltaLte`/`BalanceDeltaGte`/`AffineDeltaLe` read BOTH `old_state` and
  `new_state` and so surface `TransitionCheckRequiresOldState` when no
  pre-state is in scope (a rate / delta gate cannot be satisfied without both
  endpoints), the same fail-closed posture the existing `DeltaBounded` takes.

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
| `SenderMemberOf` | **free** — single-turn-context predicate (a set-membership of the acting sender), no cross-turn invariant; the exact `SenderIs` class | the board is public descriptor literals | one membership check vs the sender context column |
| `BalanceDeltaLte`/`BalanceDeltaGte` | **BOUNDED / ordering pole** — a rate-bound on the *decrementable* balance is the `bounded_resource_not_iconfluent` case once concurrent debits exist; n=1 serial execution collapses the bound (single-machine principle), n>1 forces ordering | balance is program-visible (already ledger-visible) | one range gate over the `(old.balance, new.balance)` pair |
| `AffineDeltaLe` | **BOUNDED / ordering pole** — a bound on per-turn CHANGE of (generally decrementable) quantities; same n=1-collapses class as the balance-delta gates | public literals | one linear gate over the `(old, new)` wire pair |
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

`STATE_SLOTS = 16` is baked into `CellState`, the canonical state commitment,
and the Effect-VM state columns. The grammar for the successor is the
*name-keyed record* the Lean side already uses (`Exec/Value.lean` records,
`Exec/Program.lean` constraints keyed by `FieldName`, `FieldsMap.lean` for the
flatten): constraints address named fields, the commitment becomes a keyed
Merkle/Poseidon map (the `cap_root` openable-sorted-map pattern is the
precedent), and the 16-slot array becomes the degenerate fixed schema. The
council then constrains `approval[m]` for any member id `m`; `MAX_MEMBERS`
dies. **Grammar verdict: do NOT pre-land a slot-map grammar against the
16-slot layout** — every name-keyed constraint would be a lie until the
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
  **The apps-gap-2/3/4 wave** added `senderMemberOf` / `balanceDeltaLe` /
  `balanceDeltaGe` (on `SimpleConstraint`) and `affineDeltaLe` (on
  `StateConstraint`, reading the `affineDeltaSum` over `(old, new)`), each with
  its `#assert_axioms`-clean admit-characterization
  (`evalSimpleCtx_senderMemberOf_iff`, `evalSimpleCtx_balanceDeltaLe_iff`,
  `evalSimpleCtx_balanceDeltaGe_iff`, `evalConstraint_affineDeltaLe_iff`). The
  Rust twins (`cell/src/program.rs`) were APPENDED last, after the Lean was
  green — so the proof is the spec and the evaluator mirrors it, never the
  reverse (LAW #1). `lake build Dregg2` stays axiom-clean (3930 jobs).
  NEXT (with the rotation): thread the cell's own balance into
  `Exec/EffectsState.lean::SlotCaveat.eval` so the balance-delta atoms gain
  kernel-level twins (today the `(actor, old, new)` gate carries the sender
  binding but not the sealed balance).
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
4. **AIR parity for the new atoms** — `SenderIs`/`SenderMemberOf`/`Balance*`/
   `BalanceDelta*`/`AffineDeltaLe` are executor-enforced; the slot-caveat PI
   manifest (`turn/src/executor/mod.rs::project_slot_caveat_manifest`) defers
   them like the other context-dependent variants. The sender pk and the
   `(old.balance, new.balance)` pair are natural context columns for the
   rotation's PI layout (the balance-delta gates need both balance endpoints in
   the PI; `AffineDeltaLe` needs the `(old, new)` slot pair the delta reads).
5. **The second balance lane** (§6.3) for real markets.
6. **DSL surface** — `dregg_program { … }` (Lean `DSL.lean`) and the Rust
   builders should grow `sender is` / `sender in {…}` / `balance >=` /
   `balance change <= ` / `reveals` sugar so app authors write the idioms, not
   the encodings.

## 11. The next rungs

The atoms above stop the *expressibility* bleeding — a board binds its members,
a treasury bounds its outflow, an escrow gates its release. But three things
still make a real app *feel* like a toy, and each has a concrete additive
design in the proven §8 style: a Lean twin in `Exec/Program.lean`, a fail-closed
Rust evaluator arm that mirrors it, and a named admit-characterization keystone.
The order below is the leverage order. Each is pinned with its cost class so an
author choosing it knows what coordination it buys.

### 11.1 The council cap — name-keyed fields (the single highest-leverage move)

**The disease.** `STATE_SLOTS = 16` (8 in the deployed layout) is the ceiling
on *everything*: a council of 3, a 7-field deal schema, a path predicate
squeezed into `seg_indices`. Every app feels the slots because the commitment,
the AIR columns, and `CellState` all bake the fixed array. A "real" governance
cell wants `approval[member_id]` for *any* member; a real market wants
`order[i]` for an unbounded book.

**The design (the rotation owns it — do NOT pre-land against 16 slots).** The
Lean side already speaks the answer: `Exec/Value.lean` records are *name-keyed*
(`Value.record : List (FieldName × Value)`), every `SimpleConstraint` reads a
`FieldName` (not a `u8`), and `FieldsMap.lean` flattens a keyed map to wires.
The runtime catches up by making `CellState` a keyed Poseidon map (the
`cap_root` openable-sorted-map pattern is the precedent — §6.1) with the 16-slot
array as the degenerate fixed schema. **No new atom is needed** — the existing
catalog becomes `FieldName`-addressed and `MAX_MEMBERS` dies. The council then
writes `Immutable(field("approval", m))` for member id `m`, and
`SenderMemberOf{board}` (§3) binds it — the multi-admin tooth scales to N. This
is a *layout rotation*, not grammar: every name-keyed constraint would be a lie
against the 16-slot commitment until it opens, so it lands once, with the Lean
record semantics (already proved) as the spec. **Cost:** unchanged per-atom; the
map open is the precedent's logarithmic Merkle cost.

A useful *bridge* that ships before the rotation, fully additive against the
fixed array: a **`SlotRange` guard** — `forAllSlots lo hi c` applying a simple
constraint `c` uniformly to every slot in `[lo, hi)` (e.g. "every approval slot
in `[2, 16)` is `MemberOf {0,1}`"). It is a `StateConstraint` whose evaluator
folds `c` across the slot window (Lean: a `List.all` over `(List.range' lo
(hi-lo)).map`; keystone `evalConstraint_forAllSlots_iff` = "admits IFF `c` holds
at every slot in the window"). It does not lift the *count* ceiling (still 16),
but it makes "all N approvals obey the same rule" one atom instead of N copied
constraints — the council's repetitive shape, today, with zero layout risk.

### 11.2 Cross-cell reads — the verified-observation atom (NOT a live read) — **LANDED**

**The disease.** A polis constitution copies its parameters into every child at
birth (polis gap 2); an amendment can't propagate. Apps want "this council's
threshold IS constitution v3's threshold" as a *live* fact.

**Why a live cross-cell read stays OUT of the constraint language.** A guard
that reads another cell's *current* state makes every turn on this cell order
against every turn on that cell — the `relational_decided_by_merge` arm with a
non-local relation, which is coordination, *always* (§8, and the
`ConfluenceClassifier` verdict is unambiguous). Putting it in the simple
fragment would silently make ordinary cells non-confluent. So the rung is not
"read the peer's live slot"; it is **verified observation of a peer's
*finalized* state** — a fact already committed and receipted, which is
monotone (a finalized value never un-finalizes) and therefore safe to witness.

**The design — `ObservedFieldEquals` (a witnessed, `StateConstraint`-only
atom).** It joins the `WitnessedPredicate` family (`cell/src/predicate.rs`),
NOT the composable simple fragment (the §4 discipline: witnessed shapes don't
survive naive disjunction). Shape:

```rust
// StateConstraint
ObservedFieldEquals {
    local_field:  u8,            // new[local_field] must equal …
    source_cell:  [u8; 32],      // … the value field `source_field` held by …
    source_field: u8,            // … this peer cell …
    at_root:      [u8; 32],      // … at this finalized state-commitment root.
    proof_witness_index: usize,  // a Merkle-open proof: source_field ∈ at_root.
}
```

Semantics, fail-closed: admits IFF the host root authority confirms `at_root` is
a genuine finalized commitment of `source_cell` AND opens `source_field` in it to
a value `v`, AND `new[local_field] == v` (the Merkle-open proof rides in the
witness at `proof_witness_index`; its absence fails closed). The host channel is
`FinalizedRootAuthority` (`cell/src/predicate.rs`), the cross-cell twin of the
`IssuerRootAuthority` precedent — the host installs "which roots are real," and
when *no* authority is installed every `ObservedFieldEquals` REJECTS, exactly as
a missing `IssuerRootAuthority` rejects every BlindedSet proof (the cross-cell
self-fabrication forge stays closed). Verification is recomputation against the
receipt chain — what verifiers already do, minus the archaeology — so it is the
first-class form of the *already-sound* copied-parameter pattern (§8's
`imports`), now a program tooth instead of a descriptor literal. **Lean twin:**
`Exec/Program.lean` `observedFieldEquals` reading a
`TurnCtx.observedFields : List (Int × FieldName × Int)` carrier (the opened
`(cell, field, value)` triples the §8 crypto portal hands the evaluator, like
`exhibitedCommit`); keystone `evalConstraintCtx_observedFieldEquals_iff` =
"admits IFF the carrier holds `(source_cell, source_field, v)` AND
`new[local_field] = v`," with `observedFieldEquals_mismatch_refuses` (the local
field cannot diverge from the finalized value) and
`evalConstraintCtx_observedFieldEquals_absent_proof_refuses` (no opened triple ⇒
reject — the anti-forge tooth). The Merkle-open + root-authenticity stays in the
portal; the ordering law is proved here. **Cost (§8):** the disclosure is the
peer's finalized value (already public on the chain); coordination is **free
for finalized reads** — a monotone, already-committed fact is the
`monotone_terminal` confluence-keeping case, NOT the live-read ordering pole.
That distinction (finalized vs live) is *why* this rung is admissible where a
live read is not, and the doc of the atom must say so.

**LANDED** — the Lean twin is proved (`lake build Dregg2` axiom-clean, 3930
jobs); the Rust mirror is `StateConstraint::ObservedFieldEquals` +
`FinalizedRootAuthority` / `StaticFinalizedRootAuthority`
(`cell/src/predicate.rs`), the evaluator arm in `cell/src/program.rs`, the view
projection (`StateConstraintView::ObservedFieldEquals`), and the both-polarity
pin `observed_field_equals_reads_a_finalized_peer_value` (admit on match · reject
on mismatch · reject on a forged root · reject with no authority · reject with no
proof). Variant-index-APPENDED, so factory VKs / content addresses stay
byte-identical (§2). The cross-cell carrier is threaded as
`WitnessBundle::finalized_roots` (the host installs it like the witnessed
registry); when the executor does not supply it, the atom fails closed.

### 11.3 Richer composite leaves — `AnyOfBound` (witnessed branches under ⊔)

**The disease.** `AnyOf` today only carries `SimpleStateConstraint`s, so the
proof-bearing shapes (`SenderAuthorized`, `Witnessed`, `Custom`, the new
`ObservedFieldEquals`) cannot sit in a disjunction. A real app wants "release if
EITHER the timeout passed OR a credential proof verifies" — a witnessed branch
beside a cheap branch.

**Why the naive lift is unsound (and the fix).** An `AnyOf` branch that *fails
to verify a proof* must be distinguishable from one that *needs no proof*, or a
submitter strips the proof and slides down the cheap branch (§4). The fix is the
branch-witness binding §6.4 already sketched — make it concrete:

```rust
// StateConstraint
AnyOfBound {
    branches: Vec<BoundBranch>,   // admits iff ANY branch admits
}
enum BoundBranch {
    Simple(SimpleStateConstraint),               // no witness; the cheap leg
    Witnessed { wp: WitnessedPredicate },        // names its OWN proof blob
}
```

The key is that each witnessed branch names its blob *inside the branch*
(`wp.proof_witness_index`), and the global unique-blob scan (the audit-item-4
discipline) still binds each blob to exactly one consumer — so "this branch
needs proof `i`" is structural, and a stripped proof makes that branch *fail*
(it cannot masquerade as a no-proof branch). **Lean twin:** `Exec/Program.lean`
`anyOfBound (branches : List BoundBranch)` evaluating `branches.any` where a
witnessed branch consults the same `TurnCtx` witness carriers the standalone
atoms read; keystone `evalConstraint_anyOfBound_iff` = "admits IFF some branch
admits" PLUS the soundness pin `anyOfBound_stripped_proof_branch_fails` (a
witnessed branch with an absent/invalid proof carrier does NOT admit — the
anti-strip tooth). **Cost (§8):** the max of the branch costs (a disjunction is
as coordinated as its most-coordinated *taken* branch); disclosure is the union
of what the taken branch reveals. This is the rung that lets escrow/governance
ceremonies express genuine OR-of-conditions instead of being forced into a
single linear `Cases` ladder.

### 11.4 What each rung unlocks (the naturalness ledger)

| Rung | The toy shape today | The natural shape after |
|---|---|---|
| 11.1 name-keyed fields | council of 3; deal schema crammed into 8 slots | `approval[m]` for any member id `m`; an unbounded order book |
| 11.1 `SlotRange` (bridge) | N copied `MemberOf` constraints, one per approval slot | one `forAllSlots` over the approval window |
| 11.2 `ObservedFieldEquals` **(LANDED)** | constitution params copied at birth, frozen | "my threshold IS constitution v3's, at height H" — live, amendable, verified |
| 11.3 `AnyOfBound` | a linear `Cases` ladder; witnessed conditions can't disjoin | "release if timeout OR credential-proof" as one gate |
| 11.5 `GatedAffordance` **(LANDED)** | a button's visibility is cap-ONLY (`is_attenuation`); its state precondition lives in out-of-band app glue | "approve fires only if you HOLD the approver cap AND the proposal is PENDING" — caps ∧ live-state as ONE gate; the same viewer's button reacts to state |

### 11.5 Affordance-gating predicates — caps AND live state as one gate — **LANDED**

**The disease.** A deos affordance (`starbridge-web-surface/src/affordance.rs`
`CellAffordance`) gates *firing* on `is_attenuation` — `required ⊆ held`,
CAP-ONLY. Whether the button may fire *right now in this state* (the proposal is
`PENDING`, the deadline hasn't passed, the viewer hasn't already voted) is a
SEPARATE question the cell program (`RecordProgram.admitsCtx`) answers — and the
two never composed. A real app's "approve" button is BOTH: held authority AND a
live-state predicate over the same interaction. That conjunction had no home, so
app authors smuggled the state half into out-of-band glue (the exact "screaming
toy" shape).

**The design — `GatedAffordance` (the conjunction, proven).** A `GatedAffordance`
pairs the REAL cap-gate (`Deos.Affordance.fireGate`, the `is_attenuation` order
the cap crown proves) with a REAL state condition (`RecordProgram`, the cell
program the executor already enforces), threaded with the same `TurnCtx` the
context atoms read. `fireGated` commits IFF BOTH bite. **No new mathematics**: the
cap gate is the existing affordance gate; the state gate is the existing
`admitsCtx`; the rung is their `&&`. **Lean (LANDED):**
`Dregg2/Deos/GatedAffordance.lean` — keystone `fireGated_iff` (`isSome ↔ (required
⊆ held) ∧ admitsCtx`), the four cross-polarity teeth proving NEITHER gate alone
suffices (`fireGated_cap_fail_refuses` / `fireGated_state_fail_refuses` /
`fireGated_needs_both`), the htmx tooth `fireGated_reactive` (the SAME viewer's
button lights/darkens as the cell transitions), and the state-aware per-viewer
projection `projectGatedFor` (`projectGatedFor_monotone` — progressive
attenuation survives the state gate; `projectGatedFor_all_fireable` — no
offered-but-refused buttons). All `#assert_all_clean`, `#guard` non-vacuity in all
four cap×state quadrants. **Cost (§8):** the MAX of the two gates' classes — the
cap gate is free/i-confluent (a single-turn context predicate); the state gate
inherits its own constraints' classes (a monotone-status guard is free, a balance
ceiling is the ordering pole), exactly as if the `RecordProgram` were enforced
standalone. The conjunction adds no coordination beyond its parts. **Rust-mirror
(for the convergence):** a `GatedAffordance { affordance, state_cond, method }`
beside `CellAffordance` (`starbridge-web-surface/src/affordance.rs:90`) whose
`fire` runs the existing `authorized_for` (`affordance.rs:131`) AND THEN the
existing `evaluate_constraint_full` over the touched cell's `(old, new)` —
refusing with a new `FireError::StateConditionUnmet` (`affordance.rs:239`) unless
BOTH pass; plus a `project_gated_for` beside `project_for` (`affordance.rs:291`)
filtering on both. `cell/src/program.rs` needs NO change (the gate CALLS the
evaluator the executor already owns — LAW #1).

The throughline is the §8 honesty contract: every rung is pinned to its
confluence class, so an author reaching for `ObservedFieldEquals` knows it is
*free only because it observes finalized state*, and one reaching for a balance
ceiling knows it is an ordering guard the moment the topology widens past n=1.
Naturalness never costs a silent coordination surprise — the classifier is the
language's promise that the grammar tells the truth about what it makes you pay.
