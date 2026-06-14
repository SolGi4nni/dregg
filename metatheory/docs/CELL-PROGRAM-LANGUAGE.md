# The cell-program language

> *This is the formal, Lean-source-grounded reference — it cites the modules under `metatheory/Dregg2/`
> directly. For the gentler teaching introduction to the same language, see
> [`docs/CELL-PROGRAM-LANGUAGE.md`](../../docs/CELL-PROGRAM-LANGUAGE.md) at the repo root.*

A dregg cell's behaviour is a **program**: a decidable predicate over state transitions that the
verified executor evaluates on every turn. The program is the cell's *law* — it says which
`(old, new)` transitions, under which authorities, the cell admits. This document describes the
language those programs are written in: one coherent calculus of decidable relations over a cell's
named, content-addressed record state.

The whole language is formally modelled and proved in Lean. The grammar lives in
`metatheory/Dregg2/Exec/Program.lean`; the relational-closure view in
`metatheory/Dregg2/Authority/RelationalClosure.lean`; cross-cell provenance in
`metatheory/Dregg2/Authority/CrossCellImport.lean`. Every atom carries an *admit-characterization*
theorem (what it accepts, what it rejects) and a non-vacuity pair (it admits a real transition AND
rejects an adversarial one). Nothing in the language is a `True`-carrier.

## The substrate: named record state

A cell's state is a **record** — a list of named, typed fields (`Exec/Value.lean`), not a fixed array
of bit-positioned slots. Fields are read by name (`Value.scalar : Value → FieldName → Option Int`),
so adding a field can never silently rebind another, and a record flattens to a fixed-width field
vector whose length is a function of the *schema* alone (`flatten_width`) — which is what makes a
circuit over records well-defined.

Field reads are `Option`-valued and **fail closed**: a constraint that reads a missing or ill-typed
field is *unevaluable*, and an unevaluable constraint rejects. There is one principled exception
(`fieldOf`, the total reader that defaults an absent field to `0`, dregg1's `FIELD_ZERO`); the two
conventions and their precise relationship are unified below.

## The constraint catalog

A program is one of:

- `none` — the terminal program; every authorized transition is admissible.
- `predicate [c₁, …, cₙ]` — a conjunction of constraints (all must hold).
- `cases [⟨guard, constraints⟩, …]` — operation-scoped cases; **no matching case denies**
  (default-deny is the partial arrow's domain).
- `circuit hash` — an opaque AIR; admissibility is "carries a proof the circuit accepts".

The constraints (`StateConstraint`, with the `SimpleConstraint` sub-fragment that composes under the
Heyting connectives `anyOf`/`not`) cover:

**Single-field shape.** `fieldEquals` / `fieldGe` / `fieldLe` (absolute bounds); `immutable`
(read-only after init) / `writeOnce` (register-once) / `monotonic` (≥ old) / `strictMono` (> old);
`fieldDelta` (exact change); `memberOf` (value allowlist); `prefixOf` (namespace/path containment);
`inRangeTwoSided` (absolute band); `deltaBounded` (symmetric change magnitude).

**Cross-field / arithmetic.** `fieldLeField` (slot ≤ slot); `sumEquals` / `sumEqualsAcross`
(intra-cell conservation); `fieldDeltaInRange` (bounded growth); `allowedTransitions` (a state
machine); `affineLe` / `affineEq` (general affine relations `Σ cᵢ·new[fᵢ] {≤,=} c`); `affineDeltaLe`
(a multi-field rate gate on the per-field deltas `Σ cᵢ·(new[fᵢ] − old[fᵢ]) ≤ c`).

**Lattice / workflow.** `clearanceGe` (an SGM clearance mandate, wired to the proved-sound
`ClearanceGraph.dominatesD`); `reachable` (a DAG-prerequisite gate).

**The Heyting fragment.** `anyOf` is the disjunction `⊔` (single-level over simples); `not` is the
Boolean complement. Double negation collapses; disjunction is `∃`/`any`. These give the policy
combinators their algebra.

**Cross-cell (declared, discharged at the joint seam).** `boundDelta` declares a bilateral
relation between two cells' field deltas; the single-cell evaluator **fails closed** on it (a
single cell cannot see its peer's state), and the bilateral discharge happens in the JointTurn /
CoordinatedCaveat path.

### Turn-context atoms

Some atoms read the *turn context* — the slice of executor state a program-check sees beyond the
`(old, new)` records: the acting `sender`, the touched cell's sealed `balance` (and its pre-turn
`balanceBefore`), the revealed-preimage hash, the delegation epoch, the witness-exhibited element
set, and the emitted-wake set. These are carried in `TurnCtx`; the ctx-aware evaluators are
`evalSimpleCtx` / `evalConstraintCtx` / `RecordProgram.admitsCtx`.

The turn-context atoms: `senderIs` / `senderInField` / `senderMemberOf` (actor identity, single /
dynamic-owner / multi-admin board); `balanceGe` / `balanceLe` (the cell's own sealed balance);
`balanceDeltaLe` / `balanceDeltaGe` (per-turn balance rate, ceiling / floor); `preimageGate` (a
knowledge gate over a §8 crypto-portal hash); `delegationEpochEquals` (the capability-freshness
tie); `countGe` (an in-program M-of-N over a distinct exhibited set).

**The empty context recovers the ctx-less evaluator** (`evalSimpleCtx_empty`,
`admitsCtx_empty`): a context atom *fails closed* without its context, and every ctx-free atom
delegates definitionally. So the context layer is a conservative extension — it only ADDS
admissibility distinctions when a context is present; the entire ctx-less theorem family is
untouched.

### The actor-bound approval pattern

The composite `anyOf [immutable f, senderIs k]` is the per-slot **actor binding**: a turn that
leaves slot `f` alone is admitted for any sender (so propose/certify/other-members' turns stay
open), but FLIPPING `f` demands the turn's sender be `k`. Capability possession alone cannot flip
another member's slot. `senderMemberOf` generalizes this to a multi-admin board
(`anyOf [immutable f, senderMemberOf board]`).

## One affine vocabulary

The same affine arithmetic `Σ cᵢ·record[fᵢ]` is read by two layers — the cell-program catalog's
`affineLe`/`affineEq`/`affineDeltaLe` (over the fail-closed `Value.scalar` reader, `Option`-valued)
and the relational closure's `RelPred.affineLe` half-space (over the total `fieldOf` reader). The two
are the **same affine form over the same `Term = Int × FieldName` model**; the only difference is the
absent-field convention (`none`-propagation versus `0`-default).

`metatheory/Dregg2/Authority/AffineBridge.lean` proves they **coincide on the common domain** — when
every term field is present, `programAffineSum_eq_relClosure` shows the program reader's value equals
the relational-closure sum exactly (the `getD 0` default never fires). The comparison transports both
ways (`programAffineLe_iff_relClosureLe`, `programAffineLe_admits_relPredAffineLe`,
`relPredAffineLe_admits_programAffineLe`), so an affine fact proved in either layer — including one
proved through the closure's Boolean algebra — lifts to the other with no re-proof. The bridge also
pins *why* the qualifier is load-bearing (`bridge_conventions_differ_off_domain`: off the common
domain the two conventions genuinely differ), so the unification is honest about its scope rather than
asserting a false function equality.

## The relational closure

The general object behind the affine atoms is `RelPred` (`RelationalClosure.lean`): one
general affine half-space `Σ cᵢ·record[fᵢ] ≤ k` closed under the Boolean connectives
`.and`/`.or`/`.not` with `⊤`/`⊥`. It is a genuine Boolean algebra on the evaluator (De Morgan,
distributivity, complementation, double negation all hold pointwise), so an author may write *any*
decidable relation expressible by combining affine half-spaces, not a fixed menu. `FieldLteOther`,
`FieldLteField`, `AffineLe`, and `SumEquals` all fall out as instances; equality is `.and` of two
half-spaces, recovered for free.

The closure is the **bounded affine fragment over the post-record**: a `RelPred` of bounded size
compiles to a bounded number of circuit constraints (`relPred_constraints_bounded`). Three fragments
lie outside it and route to `witnessed(vk)` (a circuit verifier, the §8 oracle): unbounded
quantification over the record, non-affine relations (products, hashes, range proofs), and
causal/history-dependent guards that read the trace (`RelPred.eval` is a function of the post-record
alone). The boundary is stated as a theorem (`relPred_is_record_local`).

## Cross-cell reads as verified past-snapshot imports

A cell program cannot read another cell's *live* state, by design: a guard reading cell B's current
value makes every turn on A order against every turn on B — coordination, always. Instead, a cell
**imports** a value: an `Import` (`CrossCellImport.lean`) cites a receipt in the source cell's
append-only chain and the value the source field held in the state that receipt commits. Because
receipts are immutable, that reading never changes as the source advances — the import is
**i-confluent** (coordination-free), proved by `importValid_stable_under_source_advance` against the
contrast `liveRead_changes_under_source_advance`. Provenance is non-forgeable by inheritance from the
chain's tamper-evidence; staleness is faithful-but-visible (a stale import still reports the cited
past truthfully, and the provenance dates it, so supersession is detectable, never silent).

### First-class import binding

"This field IS this provenanced import" is a single construct, `ImportedEq`
(`metatheory/Dregg2/Authority/ImportBinding.lean`). It carries the `Import` — so the provenance
obligation `importValid` sits on the same object — and projects the cell-program constraint that
enforces it (`toConstraint`, an existing `affineEq [(1, localField)] value` atom). One keystone,
`importedEq_binds_provenanced_value`, fuses both legs: when the import is valid AND the cell admits
the binding, the local field holds exactly the value the source committed at the cited receipt. The
construct inherits the anti-lie (`importedEq_lying_import_rejected` — a lie cannot be cited) and the
i-confluence (`importedEq_stable_under_source_advance`) directly. A governed cell states one clause,
not two hand-threaded obligations.

## Field-valued rate bounds

A rate bound's limit can itself be governed state rather than a baked literal. `affineDeltaLeField
terms rateField` admits iff `Σ cᵢ·(new[fᵢ] − old[fᵢ]) ≤ new[rateField]`, and the turn-context twin
`balanceDeltaLeField rateField` admits iff `new.balance − old.balance ≤ new[rateField]`. A tier
upgrade that raises `new[rateField]` raises the allowed per-turn movement with **no program rewrite**
— the seam a plan needs when its rate lives in a slot a governance turn can lift. Both fail closed on
an absent rate field: a missing tier grants zero allowance, never an unbounded one
(`evalConstraint_affineDeltaLeField_iff`, `evalSimpleCtx_balanceDeltaLeField_iff`).

## Program-enforced wake-on-transition

A turn that drives a cell to a terminal state (a resolve/release) often must also fire an async
wake — but until the `wakeOnResolve` atom, that obligation was documented, not enforced: the notify
cap-algebra and the program ran in separate sections. `wakeOnResolve stateField resolvedValue badge`
welds them: a transition driving `new[stateField] = resolvedValue` must have emitted the wake
carrying `badge` (witnessed in `TurnCtx.emittedWakes`), or it is rejected. A non-resolving transition
is dormant. This is the notify dual of the balance-drain tooth (`anyOf [not (state = RESOLVED),
balanceLe 0]`); the two sit side by side on the same resolving transition. The full design is in
[`PROGRAM-NOTIFY-WELD.md`](PROGRAM-NOTIFY-WELD.md).

## Discipline

Every keystone in the language is axiom-clean — its proof depends only on the three standard kernel
axioms (`propext`, `Classical.choice`, `Quot.sound`), pinned by `#assert_axioms` / `#assert_all_clean`
so a leaked `sorry` fails the build. Every atom is proved non-vacuous: it admits a real transition AND
rejects an adversarial one. Conservation is never mistaken for correctness — a sufficient spec, not
merely a true one.
