# Program-enforced wake-on-transition (the notify weld)

## The seam this closes

dregg has two facts about a resolving turn that *should* be one:

1. **The state transition** — a cell program drives `state → RESOLVED` (or `RELEASED`, or any
   terminal value), gated by the cell's `RecordProgram`.
2. **The async wake** — the resolving turn fires a `notify` so the waiter (the counterparty, the
   subscriber, the poller) is woken. The notify authority is a held capability with its own proved
   cap-algebra (`metatheory/Dregg2/Firmament/NotifyAuthority.lean`: `NotifyCap`, `signalGated`, the
   badge-mask sub-lattice, non-amplification).

Until the `wakeOnResolve` atom, (1) and (2) lived in separate sections. The cell program enforced the
state transition; the notify algebra proved the wake was authorized *if* it fired; but **nothing
required the resolving turn to fire the wake**. "A turn driving state → RESOLVED also fires the wake"
was a documented intention, not a program clause. A correct-but-forgetful handler could resolve the
escrow and leave the waiter blocked forever — the dual of resolving the escrow and stranding its
balance.

The balance side of this is already welded: `anyOf [not (fieldEquals "state" RESOLVED), balanceLe 0]`
makes "resolve drains the balance" a program requirement. `wakeOnResolve` is the **notify dual** of
that drain tooth.

## The atom

```
SimpleConstraint.wakeOnResolve (stateField : FieldName) (resolvedValue : Int) (badge : Int)
```

Read: *"a turn that drives `new[stateField] = resolvedValue` MUST have emitted the async wake carrying
`badge`."*

It is a `SimpleConstraint`, so it composes under the Heyting fragment (`anyOf`/`not`) like every other
simple atom — it can sit in a conjunction beside the drain tooth, or under a method guard, or
disjoined with an escape clause.

## Semantics (`admitsCtx`)

The wake is witnessed in the turn context. `TurnCtx` carries an emitted-wake set:

```
emittedWakes : List Int := []
```

This is the per-turn log of badges the executor's cap-gated `signalGated` calls actually OR'd while
applying the turn's effects — the same seam by which `revealedHash` carries a §8 crypto-portal hash
and `exhibitedCommit` carries a sorted-set commitment, *without* the program layer importing the
firmament's notify object. The badge-OR accumulator and the cap-gating stay in
`Firmament/NotifyAuthority.lean`; the program layer only witnesses *that a wake with this badge was
emitted in this turn*.

The ctx-aware evaluator (`evalSimpleCtx`):

```
wakeOnResolve sf rv badge:
  match new.scalar sf with
  | some v => !(v == rv) || ctx.emittedWakes.contains badge
  | none   => true        -- state field absent ⇒ not resolving ⇒ dormant
```

So:

- **resolving** (`new[sf] = rv`): admits iff `badge ∈ emittedWakes`. The wake is *required*.
- **not resolving** (`new[sf] ≠ rv`, or absent): admits unconditionally. The clause is **dormant** —
  an ordinary turn that does not resolve is unconstrained.

The ctx-less evaluator (`evalSimple`) is the conservative-extension special case: a resolving
transition has no emitted-wake set to witness, so it **fails closed** (rejects); a non-resolving one is
dormant (admits). `evalSimpleCtx_empty` proves the empty context recovers exactly this, so the entire
ctx-less theorem family is untouched.

## Soundness

The weld is the pair of admit-characterizations, both proved and axiom-clean in
`metatheory/Dregg2/Exec/Program.lean`:

- **`evalSimpleCtx_wakeOnResolve_resolving_iff`** — on a resolving transition, the clause admits **iff**
  the turn emitted the required wake. This is the weld: state-reaches-resolved ⟺ wake-emitted (given
  the clause is in the program).
- **`wakeOnResolve_resolve_requires_wake`** (the teeth) — a resolving transition whose `emittedWakes`
  lacks the badge is **rejected**. You cannot drive the cell to RESOLVED without having fired the wake.
- **`evalSimpleCtx_wakeOnResolve_dormant`** — a non-resolving transition admits regardless of the wake
  set, so the weld fires only on the resolving edge (it does not encumber ordinary turns).

The escrow example, with both duals on the same resolving transition:

```
escrowResolveProgram :=
  predicate [ anyOf [not (fieldEquals "state" 2), balanceLe 0]   -- drain on resolve
            , simple (wakeOnResolve "state" 2 7) ]               -- wake on resolve
```

- resolve + drained + woke → **admits**;
- resolve + drained + forgot the wake → **rejected** (the notify weld bites where the drain alone
  would pass);
- resolve + woke + forgot the drain → **rejected** (the balance dual still bites independently).

Both polarities are pinned as `#guard` teeth and the soundness lemmas are `#assert_axioms`-clean.

## Staging — what carries the wake

The atom needs one addition to `TurnCtx`: the `emittedWakes : List Int` carrier. This is an **additive,
defaulted field** (`:= []`), so every existing `TurnCtx { … }` literal and the empty context are
unchanged; the conservative-extension keystones hold verbatim. No constructor was added to the heavy
`StateConstraint` inductive's cross-cell or circuit machinery; the atom is a `SimpleConstraint` member
that the existing `evalSimpleCtx`/`evalSimple` matchers handle.

The cost class (§8): `wakeOnResolve` is **free / i-confluent** — it is a predicate over the single
turn's own emitted-wake set and post-state, with no cross-turn invariant. The wake is a fact of *this*
turn (exactly the `senderIs` classification), so the clause never forces ordering against other turns.

## Correspondence (what the Rust executor must do)

The Lean atom is the specification; the deployed executor must populate `TurnCtx.emittedWakes` from the
real notify-emission log it accumulates while applying a turn's effects. Concretely: each cap-gated
`signalGated` that COMMITS contributes its (masked) badge to the turn's emitted-wake set, and the
program-check loop reads that set when evaluating a `wakeOnResolve` clause. This is the notify mirror of
how the executor already supplies `revealedHash` (the hashed preimage) and `delegationEpoch` (the
per-cell freshness stamp) to the program checker. Wiring it is a cutover-settle lockstep with the
firmament notify VK epoch (see the rotation/notify checklist); recorded as a follow-up so the spec and
the binary land together.

## Why this is more expressive *and* easier to reason about

Before the weld, "resolve implies wake" was an obligation a reviewer had to check by reading the
handler and the notify wiring separately — out of band, exactly the kind of premise the assurance case
names as a hazard. After the weld it is a single program clause whose violation is UNSAT, checked by the
same evaluator that checks every other guard, with a one-line soundness theorem. The async dual of the
synchronous drain becomes a first-class part of the cell's law, not a comment.
