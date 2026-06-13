/-
# Dregg2.Exec.Program — the RecordProgram as the coalgebra structure-map (over records).

`RecordProgram` is the coalgebra structure-map — the `AdmissibleTurn ⇒ Cell` arrow.
Faithfully transcribed from dregg1's ~21-variant `StateConstraint` catalog
(`cell/src/program.rs`), but **name-keyed** over the Preserves `Value`/`Schema` of
`Exec/Value.lean`, not bit-positioned over 8 fixed slots.

`RecordProgram.admits` is the admissibility filter: the *domain* of the structure-map. It is
decidable and computable. Every constraint reads specific named fields (`Value.scalar`), so
under `flatten` each constraint is a Boolean function of a known set of wires — exactly what
the circuit compiler (`RecordCircuit`) places onto `fieldOffset` columns.

The Heyting fragment (`anyOf` ⊔ / `not` ¬) realizes `Laws.predicate_heyting` (`dregg2 §1.5`).
Witnessed/sender/cross-cell (`boundDelta`) constraints are *declared* here and routed to their
seam downstream, exactly as dregg1's scalar evaluator defers `BoundDelta`/`Witnessed`.

Pure, computable, `#eval`-able; imports `Exec.Value` and the (already-proved) orphaned
`Authority.ClearanceGraph` lattice primitive so the predicate language can express SGM-style
clearance mandates inline (`clearanceGe`, wired to `dominatesD`).
-/
import Dregg2.Exec.Value
import Dregg2.Authority.ClearanceGraph

namespace Dregg2.Exec

open Dregg2.Authority.ClearanceGraph (ClearanceGraph Label dominatesD)

/-! ## Field access into a record `Value`. -/

/-- Look up a named field's value in a record (`none` if not a record / field absent). -/
def Value.field : Value → FieldName → Option Value
  | .record fs, f => (fs.find? (fun p => p.1 == f)).map (·.2)
  | _,          _ => none

/-- Read a named field as a scalar `Int` (`none` if absent or not an `int`). Constraints that
need a missing/ill-typed field **fail closed** (the `none` propagates to `false`). -/
def Value.scalar (v : Value) (f : FieldName) : Option Int :=
  match v.field f with
  | some (.int i) => some i
  | _             => none

/-- Sum the scalar values of named fields; `none` if any is absent/ill-typed (fail-closed). -/
def sumScalars (v : Value) (fields : List FieldName) : Option Int :=
  fields.foldr
    (fun f acc => match acc, v.scalar f with
                  | some s, some x => some (s + x)
                  | _,      _      => none)
    (some 0)

/-! ## The constraint catalog (name-keyed; the structural subset of dregg1's 21). -/

/-- **Simple (non-witnessed, non-recursive-except-`not`) constraints** — the fragment
admissible inside `anyOf` and under `not` (mirrors dregg1's `SimpleStateConstraint`, the
Heyting-liftable subset). -/
inductive SimpleConstraint where
  /-- `new[field] = value`. -/
  | fieldEquals (field : FieldName) (value : Int)
  /-- `new[field] ≥ value`. -/
  | fieldGe     (field : FieldName) (value : Int)
  /-- `new[field] ≤ value`. -/
  | fieldLe     (field : FieldName) (value : Int)
  /-- `new[field] = old[field]` (read-only after init; absent-old ⇒ first write allowed). -/
  | immutable   (field : FieldName)
  /-- `old[field] = 0/absent ⇒ any; else new[field] = old[field]` (register-once). -/
  | writeOnce   (field : FieldName)
  /-- `new[field] ≥ old[field]` (append-only / monotone counter). -/
  | monotonic   (field : FieldName)
  /-- `new[field] > old[field]` (strictly increasing — bids, sequence numbers, the channel-group
  epoch step). Mirrors `SimpleStateConstraint::StrictMonotonic { index }` /
  `StateConstraint::StrictMonotonic` (`cell/src/program.rs:703`/`:486`; eval `:1615` "requires
  new > old"; simple→full lift `:2687`) — the SAME alignment story as `monotonic` ↔ `Monotonic`.
  Fail-closed on an absent/ill-typed old OR new (the record-substrate strengthening of Rust's
  always-present 8-slot fields). Admit-char: `evalSimple_strictMono_iff`. -/
  | strictMono  (field : FieldName)
  /-- `new[field] = old[field] + delta`. -/
  | fieldDelta  (field : FieldName) (delta : Int)
  /-- **`memberOf field set`** — value allowlist: `new[field] ∈ set`. The one-sided
  value-set the pair-table `allowedTransitions` cannot express ("`new[role] ∈ {admin,editor,viewer}`"
  without enumerating every `(old,new)` pair). Decidable, fail-closed (absent/ill-typed ⇒ `false`). -/
  | memberOf    (field : FieldName) (set : List Int)
  /-- **`prefixOf segFields prefix`** — namespace/path prefix containment: the ordered scalar
  path read from `segFields` (e.g. `["seg0","seg1",…]`) STARTS WITH `prefix : List Int`. The canonical
  nameservice policy "a subdomain may only be registered under a namespace the actor owns" — a structural
  prefix over the record substrate (each path segment is a named scalar). Fail-closed: a missing segment
  shorter than `prefix` ⇒ `false`. Mirrors the Rust datalog `feature_glob` path-prefix
  (`token/src/datalog_verify.rs:1398`). -/
  | prefixOf    (segFields : List FieldName) (pre : List Int)
  /-- **`inRangeTwoSided field lo hi`** — two-sided absolute value band: `lo ≤ new[field] ≤ hi`
  (the existing `fieldDeltaInRange` is RELATIVE to `old`; this is the ABSOLUTE band). AMM/price-band
  cells. Fail-closed. -/
  | inRangeTwoSided (field : FieldName) (lo hi : Int)
  /-- **`deltaBounded field d`** — REAL two-sided delta: `|new[field] − old[field]| ≤ d`. The
  catalog's `boundDelta`/`FieldDeltaInRange` are one-sided or relative-range; this is the symmetric
  absolute bound on change magnitude. Fail-closed on absent old/new. -/
  | deltaBounded (field : FieldName) (d : Int)
  /-- **Negation** (the Heyting `¬`) — accept iff `inner` rejects. Unboxed inner ⇒ no
  unbounded nesting (`dregg2 §1.5` Heyting fragment). -/
  | not         : SimpleConstraint → SimpleConstraint
  /-- **`senderIs k`** — turn-context atom (`docs/CELL-PROGRAM-LANGUAGE.md` §3): the turn's
  SENDER (the acting cell's identity, carried in `TurnCtx.sender`) must equal `k`. Mirrors
  `SimpleStateConstraint::SenderIs { pk }` (`cell/src/program.rs`). Composing it under `anyOf`
  with `immutable f` yields the per-slot ACTOR BINDING (`anyOf [immutable f, senderIs k]`:
  slot `f` flips only in a turn sent by `k` — the polis council's approval-slot tooth).
  FAIL-CLOSED in the ctx-less evaluator (mirrors Rust `MissingContextField`). -/
  | senderIs    (k : Int)
  /-- **`senderInField f`** — the turn's sender must equal the identity HELD in `new[f]`
  (the dynamic-owner binding; pin `f` with `immutable`/`writeOnce` and the cell carries its
  own controller). Mirrors `SimpleStateConstraint::SenderInSlot`. Fail-closed without ctx. -/
  | senderInField (f : FieldName)
  /-- **`balanceGe v`** — the cell's OWN post-turn balance (the sealed kernel balance, NOT a
  record field) must be `≥ v`. Mirrors `SimpleStateConstraint::BalanceGte`. -/
  | balanceGe   (v : Int)
  /-- **`balanceLe v`** — the cell's own post-turn balance must be `≤ v`. `balanceLe 0` under
  a terminal-state guard is the "resolve drains the full balance" tooth. Mirrors
  `SimpleStateConstraint::BalanceLte`. -/
  | balanceLe   (v : Int)
  /-- **`preimageGate f`** — the turn must reveal a preimage whose HASH (computed by the §8
  crypto portal, carried as `TurnCtx.revealedHash`) equals the commitment held in `new[f]`.
  The `SimpleConstraint` placement is the point: the knowledge gate composes under
  `anyOf`/`not` (committed-escrow `state = RELEASED ⇒ reveal`). Mirrors
  `SimpleStateConstraint::PreimageGate`. -/
  | preimageGate (f : FieldName)
  /-- **`delegationEpochEquals f`** — the post-state slot `new[f]` equals the touched cell's
  own post-turn `delegation_epoch` (the R7 capability-freshness counter, carried in
  `TurnCtx.delegationEpoch`; Rust carrier: `TransitionMeta::delegation_epoch`, stamped PER
  CELL by the executor's program-check loop). THE atom that discharges the channel-group
  `DelegationEpochTie` premise (`Apps/ChannelGroup.lean`): the group's epoch slot ≡
  `delegation_epoch` becomes PROGRAM-ENFORCED, so forward-key darkness and capability
  staleness compose IN the program rather than via the canonical builders' out-of-band
  fail-closed checks (kept as defense-in-depth). FAIL-CLOSED on an absent stamp (legacy
  evaluators, ctx-less evaluation) and on an absent/ill-typed slot. Mirrors
  `SimpleStateConstraint::DelegationEpochEquals`. Admit-char:
  `evalSimpleCtx_delegationEpochEquals_iff`. -/
  | delegationEpochEquals (f : FieldName)
  /-- **`countGe m f`** — the count-≥ / order-statistic atom (in-program M-of-N): the turn's
  witness EXHIBITS an element set (`TurnCtx.exhibited`, the opaque-scalar reading of the
  unique Cleartext blob) whose §8-portal canonical sorted-set commitment
  (`TurnCtx.exhibitedCommit`, Rust `count_ge_set_commitment`) equals `new[f]`, and whose
  DISTINCT count (`List.eraseDups`) is `≥ m`.

  WHY THIS DOES NOT FAIL THE WAY THE POLIS `affineLe`-FLAG TRICK DID: summing flag slots
  breaks on unbounded counters — ONE slot inflated to `m` fakes the quorum arithmetic.
  Here NOTHING accumulates in state: the witness RE-EXHIBITS the full element set on every
  turn, distinctness is structural in the evaluator (`eraseDups` — a duplicate-padded
  exhibit collapses), and the set is bound to the slot commitment, so `m` cannot be
  counterfeited by arithmetic aliasing.

  HONEST SCOPE: the atom discharges "the committed set opens and has ≥ m distinct
  elements" — it does NOT bind each element to a live approver of THIS turn (per-element
  signatures are not in the scalar evaluator; the approval binding stays the polis
  actor-bound approval-slot ceremony feeding the committed set, and the commitment slot
  itself must be governance-written). FAIL-CLOSED on a missing/malformed witness (absent
  `exhibitedCommit`) and on an absent slot. Mirrors `SimpleStateConstraint::CountGe`.
  Admit-char: `evalSimpleCtx_countGe_iff`. -/
  | countGe (m : Nat) (f : FieldName)
  /-- **`senderMemberOf members`** (apps gap 3) — turn-context atom: the turn's SENDER
  (the acting cell's identity, carried in `TurnCtx.sender`) is a member of the literal id-set
  `members`. The CLEAN form of the `anyOf [senderIs a, senderIs b, …]` idiom a multi-admin board
  needs — one atom instead of a manually-enumerated disjunction (which an N-member board would have
  to widen by hand each time a member joins). Composing it under `anyOf` with `immutable f` gives
  the MULTI-admin actor binding: `anyOf [immutable f, senderMemberOf board]` — slot `f` flips only
  in a turn sent by SOMEONE on the board, the natural generalization of the single-key
  `anyOf [immutable f, senderIs k]` polis tooth. Mirrors `SimpleStateConstraint::SenderMemberOf
  { members }` (`cell/src/program.rs`); the Rust evaluator reads `ctx.sender` against the member
  list. COST (§8): FREE / i-confluent — a predicate over the single turn's own context with no
  cross-turn invariant (exactly the `senderIs` classification: a pk-equality, here a set-membership,
  decided entirely by the acting turn). FAIL-CLOSED in the ctx-less evaluator (`MissingContextField`)
  and on an empty/absent sender. Admit-char: `evalSimpleCtx_senderMemberOf_iff`. -/
  | senderMemberOf (members : List Int)
  /-- **`balanceDeltaLe max`** (apps gap 4) — turn-context atom: a RATE CEILING on the cell's
  OWN sealed kernel balance across the transition — `new.balance − old.balance ≤ max` (the delta
  twin of the absolute `balanceLe`). Reads BOTH the pre-turn balance (`TurnCtx.balanceBefore`) and
  the post-turn balance (`TurnCtx.balance`), the sealed kernel balances the executor holds at
  evaluation time — NOT record fields. A withdrawal-rate / spend-cap gate ("this cell may not GAIN
  more than `max` per turn"); paired with `balanceDeltaGe` it bounds the per-turn movement in both
  directions. Mirrors `SimpleStateConstraint::BalanceDeltaLte { max }` (`cell/src/program.rs`),
  reading `old_balance`/`new_balance` from the executor context. COST (§8): the BOUNDED / ordering
  pole — a rate-bound on a DECREMENTABLE quantity (the balance) is exactly the
  `bounded_resource_not_iconfluent` case the moment concurrent debits exist; single-cell serial
  execution makes it safe today (n=1 collapses the bound, per the single-machine principle), n>1
  forces ordering on the cell. NOT i-confluent. FAIL-CLOSED on an absent pre- OR post-balance.
  Admit-char: `evalSimpleCtx_balanceDeltaLe_iff`. -/
  | balanceDeltaLe (max : Int)
  /-- **`balanceDeltaGe min`** (apps gap 4) — turn-context atom: a RATE FLOOR on the cell's OWN
  sealed kernel balance across the transition — `new.balance − old.balance ≥ min` (the delta twin
  of the absolute `balanceGe`). Reads `TurnCtx.balanceBefore` and `TurnCtx.balance`. The lower-bound
  rate gate ("this cell may not LOSE more than `−min` per turn" when `min < 0`; "must gain at least
  `min`" when `min > 0`). Mirrors `SimpleStateConstraint::BalanceDeltaGte { min }`. COST (§8): the
  BOUNDED / ordering pole, same as `balanceDeltaLe` — a rate-bound on the decrementable balance,
  i-confluent only under the single serializer (n=1). NOT i-confluent. FAIL-CLOSED on an absent
  pre- OR post-balance. Admit-char: `evalSimpleCtx_balanceDeltaGe_iff`. -/
  | balanceDeltaGe (min : Int)
  deriving Repr

/-- **The full state-constraint catalog** — simple constraints plus the cross-slot,
conservation, state-machine, disjunction, and (declared-but-deferred) cross-cell variants. -/
inductive StateConstraint where
  /-- Lift a simple constraint. -/
  | simple        : SimpleConstraint → StateConstraint
  /-- `new[left] ≤ new[right]` (queue tail ≤ head). -/
  | fieldLeField  (left right : FieldName)
  /-- `Σ new[fields] = value` (intra-cell post-state sum). -/
  | sumEquals     (fields : List FieldName) (value : Int)
  /-- `Σ new[inputs] = Σ old[inputs] + Σ new[outputs]` (intra-cell conservation across the
  transition — dregg1 `SumEqualsAcross`). -/
  | sumEqualsAcross (inputs outputs : List FieldName)
  /-- `new[field] ∈ [old[field] + lo, old[field] + hi]` (bounded growth). -/
  | fieldDeltaInRange (field : FieldName) (lo hi : Int)
  /-- `(old[field], new[field]) ∈ allowed` (a bounded state machine). -/
  | allowedTransitions (field : FieldName) (allowed : List (Int × Int))
  /-- **Single-level disjunction** (the Heyting `⊔`) over simple constraints. -/
  | anyOf         (variants : List SimpleConstraint)
  /-- **Cross-cell binding (γ.2)** — `this[localField]` delta vs `peer[peerField]` delta.
  DECLARED here; the single-cell evaluator defers it (returns `true`), exactly like dregg1's
  scalar evaluator — it is discharged by the JointTurn aggregate (Build 4). `eqOpp = true` is
  `EqualAndOpposite` (bilateral conservation), `false` is `Equal`. -/
  | boundDelta    (localField : FieldName) (peer : Nat) (peerField : FieldName) (eqOpp : Bool)
  /-- **Clearance / lattice compare (SGM mandate)** — admits iff the actor's clearance label
  (read from `new[actorLabelField]` as a numeric `Label.id`) DOMINATES the slot's sensitivity
  label `boxLabel` in the clearance graph `g`. Wires the proved-sound `ClearanceGraph.dominatesD`
  (`Authority/ClearanceGraph.lean:53`, soundness `dominates_of_dominatesD :92`) into the predicate
  language: "a write to this slot is admitted only if the actor is cleared at least as high as the
  slot's sensitivity". Decidable, computable, FAIL-CLOSED (absent/ill-typed actor-label field ⇒
  `false`). This is what makes an SGM clearance mandate enforceable INLINE by the executor rather
  than precomputed into an `admitTable`. -/
  | clearanceGe   (g : ClearanceGraph) (actorLabelField : FieldName) (boxLabel : Label)
  /-- **`affineLe terms c`** — affine inequality `Σ kᵢ·new[fᵢ] ≤ c` over named scalar fields
  (`terms : List (Int × FieldName)`, each `(kᵢ, fᵢ)`). The general multi-field arithmetic relation the
  catalog lacked: subsumes `fieldLeField l r` as `[(1,l),(-1,r)] ≤ 0` and gives price-band / `a+b ≤ c`
  invariants. Maps to a PLONK linear gate. Fail-closed: any absent/ill-typed term field ⇒ `false`. -/
  | affineLe      (terms : List (Int × FieldName)) (c : Int)
  /-- **`affineEq terms c`** — affine equation `Σ kᵢ·new[fᵢ] = c`. Subsumes `sumEquals` (all `kᵢ=1`)
  and re-expresses conservation. Maps to a PLONK linear gate. Fail-closed. -/
  | affineEq      (terms : List (Int × FieldName)) (c : Int)
  /-- **`reachable g fromField toLabel`** — DAG-prerequisite / reachability: the label read from
  `new[fromField]` (as `Label.id`) reaches/dominates `toLabel` in the graph `g` (`dominatesD`). The
  workflow-prerequisite predicate "this step is admissible only if a prerequisite marker is reached"
  (CWM advance / SGM admit), reusing the proved-sound `ClearanceGraph.dominatesD`. Distinct from
  `clearanceGe`: that fixes the box-label and reads the ACTOR's label; `reachable` reads an arbitrary
  state field as the source. Fail-closed on absent/ill-typed `fromField`. -/
  | reachable     (g : ClearanceGraph) (fromField : FieldName) (toLabel : Label)
  /-- **`affineDeltaLe terms c`** (apps gap 2) — a genuine MULTI-FIELD DELTA gate across the
  `(old, new)` transition: `Σ cᵢ·(new[fᵢ] − old[fᵢ]) ≤ c`. Reads BOTH the old and new records and
  combines several field deltas in one affine bound — what the single-field `deltaBounded` /
  `fieldDelta` CANNOT express. The real budget-delta / rate gate: e.g. a treasury cell with two
  spend slots `out_a`, `out_b` bounds the COMBINED outflow per turn,
  `[(1,"out_a"),(1,"out_b")] ≤ budget` over the deltas; or a weighted basket `2·Δprice − Δindex ≤ k`.
  Distinct from the post-state-only `affineLe` (a band on the new record) and from `sumEqualsAcross`
  (an intra-cell conservation equation): this is a one-sided affine inequality on the DIFFERENCES.
  Maps to a PLONK linear gate over the `(old, new)` wire pair. FAIL-CLOSED: any absent/ill-typed
  term field on EITHER side ⇒ `false` (the delta is not evaluable). COST (§8): the BOUNDED /
  ordering pole — a bound on per-turn CHANGE of (generally decrementable) quantities is the
  `bounded_resource_not_iconfluent` case under concurrent writers; single-cell serial execution
  keeps it safe today (n=1), n>1 forces ordering. NOT i-confluent (a rate gate is never
  coordination-free in general). Admit-char: `evalConstraint_affineDeltaLe_iff`. -/
  | affineDeltaLe (terms : List (Int × FieldName)) (c : Int)
  deriving Repr

/-! ## Evaluation — the executable admissibility check. -/

/-- A decidable `Int` comparison as a `Bool`. -/
private def intLe (a b : Int) : Bool := decide (a ≤ b)
private def intLt (a b : Int) : Bool := decide (a < b)

/-- Read the ordered scalar path from a list of segment field-names (`none` if ANY segment is
absent/ill-typed — fail-closed, so a path shorter than a queried prefix cannot match). -/
def readPath (v : Value) (segFields : List FieldName) : Option (List Int) :=
  segFields.foldr
    (fun f acc => match v.scalar f, acc with
                  | some x, some xs => some (x :: xs)
                  | _,      _       => none)
    (some [])

/-- `Σ kᵢ·v[fᵢ]` over named scalar fields (`none` if ANY field is absent/ill-typed — fail-closed). -/
def affineSum (v : Value) (terms : List (Int × FieldName)) : Option Int :=
  terms.foldr
    (fun t acc => match acc, v.scalar t.2 with
                  | some s, some x => some (s + t.1 * x)
                  | _,      _      => none)
    (some 0)

/-- `Σ kᵢ·(new[fᵢ] − old[fᵢ])` over named scalar fields — the affine combination of the per-field
DELTAS across the `(old, new)` transition (`none` if ANY field is absent/ill-typed on EITHER side —
fail-closed, so a delta gate over a missing field cannot be satisfied). The reader behind
`affineDeltaLe` (apps gap 2): a multi-field rate gate `deltaBounded`/`fieldDelta` cannot express. -/
def affineDeltaSum (old new : Value) (terms : List (Int × FieldName)) : Option Int :=
  terms.foldr
    (fun t acc => match acc, old.scalar t.2, new.scalar t.2 with
                  | some s, some a, some b => some (s + t.1 * (b - a))
                  | _,      _,      _      => none)
    (some 0)

/-- Read a named field as a numeric clearance `Label` (`Label.id`), `none` if absent/ill-typed
(fail-closed: a `clearanceGe` over a missing actor-label field cannot be satisfied). The actor's
clearance level is stored as an `Int` scalar in the record and lifted to `Label.id`. -/
def actorLabelOf (v : Value) (f : FieldName) : Option Label :=
  (v.scalar f).map (fun i => Label.id i.toNat)

/-- **Evaluate a simple constraint** against `(old, new)`. Fail-closed on absent/ill-typed
fields (`none ⇒ false`). Recurses only through `not`. -/
def evalSimple : SimpleConstraint → Value → Value → Bool
  | .fieldEquals f val, _,   new => new.scalar f == some val
  | .fieldGe f val,     _,   new => match new.scalar f with | some x => intLe val x | none => false
  | .fieldLe f val,     _,   new => match new.scalar f with | some x => intLe x val | none => false
  | .immutable f,       old, new => match old.scalar f with
                                    | none   => true                        -- init: first write allowed
                                    | some a => new.scalar f == some a
  | .writeOnce f,       old, new => match old.scalar f with
                                    | none      => true
                                    | some 0    => true                     -- unwritten ⇒ any
                                    | some a    => new.scalar f == some a
  | .monotonic f,       old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLe a b | _, _ => false
  | .strictMono f,      old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLt a b | _, _ => false
  | .fieldDelta f d,    old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => b == a + d | _, _ => false
  | .memberOf f set,    _,   new => match new.scalar f with
                                    | some x => set.contains x | none => false
  | .prefixOf segs pre, _,   new => match readPath new segs with
                                    | some path => pre.isPrefixOf path | none => false
  | .inRangeTwoSided f lo hi, _, new => match new.scalar f with
                                    | some x => intLe lo x && intLe x hi | none => false
  | .deltaBounded f d,  old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLe (-d) (b - a) && intLe (b - a) d
                                    | _, _ => false
  | .not c,             old, new => !(evalSimple c old new)
  -- Turn-context atoms: the ctx-LESS evaluator has no sender / balance /
  -- revealed-hash in scope, so every context atom FAILS CLOSED here —
  -- exactly the Rust evaluator's `MissingContextField` rejection when no
  -- `EvalContext` is supplied. The ctx-aware semantics live in
  -- `evalSimpleCtx` below; `evalSimpleCtx_empty` proves the two agree.
  | .senderIs _,        _,   _   => false
  | .senderInField _,   _,   _   => false
  | .balanceGe _,       _,   _   => false
  | .balanceLe _,       _,   _   => false
  | .preimageGate _,    _,   _   => false
  | .delegationEpochEquals _, _, _ => false
  | .countGe _ _,       _,   _   => false
  | .senderMemberOf _,  _,   _   => false
  | .balanceDeltaLe _,  _,   _   => false
  | .balanceDeltaGe _,  _,   _   => false

/-- **Evaluate a full state constraint** against `(old, new)`. -/
def evalConstraint : StateConstraint → Value → Value → Bool
  | .simple c,              old, new => evalSimple c old new
  | .fieldLeField l r,      _,   new => match new.scalar l, new.scalar r with
                                        | some a, some b => intLe a b | _, _ => false
  | .sumEquals fs val,      _,   new => sumScalars new fs == some val
  | .sumEqualsAcross ins outs, old, new =>
      match sumScalars new ins, sumScalars old ins, sumScalars new outs with
      | some ni, some oi, some no => ni == oi + no
      | _, _, _ => false
  | .fieldDeltaInRange f lo hi, old, new =>
      match old.scalar f, new.scalar f with
      | some a, some b => intLe (a + lo) b && intLe b (a + hi)
      | _, _ => false
  | .allowedTransitions f allowed, old, new =>
      match old.scalar f, new.scalar f with
      | some a, some b => allowed.any (fun p => p.1 == a && p.2 == b)
      | _, _ => false
  | .anyOf variants,        old, new => variants.any (fun c => evalSimple c old new)
  | .boundDelta _ _ _ _,    _,   _   => false    -- FAIL-CLOSED: cross-cell delta is NOT evaluable in
                                                 -- the single-cell evaluator (no peer state in scope).
                                                 -- Matches dregg1's `evaluate` (`program.rs:1956`),
                                                 -- which returns `Err(BoundDeltaNotWired)` = REJECT here;
                                                 -- the bilateral discharge happens in the JointTurn /
                                                 -- CoordinatedCaveat path, NOT this gate. (Was `=> true`,
                                                 -- a fail-OPEN soundness hole — any program relying on a
                                                 -- `boundDelta` for safety had NO teeth.)
  | .clearanceGe g af box,  _,   new =>
      match actorLabelOf new af with
      | some actorLabel => dominatesD g actorLabel box
      | none            => false                 -- absent/ill-typed actor-label field ⇒ fail-closed
  | .affineLe terms c,      _,   new =>
      match affineSum new terms with
      | some s => intLe s c | none => false      -- absent/ill-typed term field ⇒ fail-closed
  | .affineEq terms c,      _,   new =>
      match affineSum new terms with
      | some s => s == c | none => false         -- absent/ill-typed term field ⇒ fail-closed
  | .reachable g ff toL,    _,   new =>
      match actorLabelOf new ff with
      | some fromLabel => dominatesD g fromLabel toL
      | none           => false                  -- absent/ill-typed source field ⇒ fail-closed
  | .affineDeltaLe terms c, old, new =>
      match affineDeltaSum old new terms with
      | some s => intLe s c | none => false       -- absent/ill-typed term field (either side) ⇒ fail-closed

/-! ## RecordProgram + TransitionGuard dispatch + default-deny. -/

/-- Guard naming which transitions a `Cases` arm applies to (`cell/src/program.rs`). -/
inductive TransitionGuard where
  | always
  | methodIs    (method : Nat)
  | slotChanged (field : FieldName)
  | anyOf       (children : List TransitionGuard)
  | allOf       (children : List TransitionGuard)
  deriving Repr

mutual
/-- Does a guard dispatch on the action's *method/effect* (vs being a pure state guard)?
Used for default-deny: a `Cases` value with a method-dispatching arm denies unknown methods. -/
def TransitionGuard.isMethodDispatching : TransitionGuard → Bool
  | .always         => false
  | .methodIs _     => true
  | .slotChanged _  => false
  | .anyOf cs       => anyDispatching cs
  | .allOf cs       => anyDispatching cs
def anyDispatching : List TransitionGuard → Bool
  | []        => false
  | g :: rest => g.isMethodDispatching || anyDispatching rest
end

mutual
/-- Evaluate a guard against `(method, old, new)`. -/
def TransitionGuard.matches : TransitionGuard → Nat → Value → Value → Bool
  | .always,        _,      _,   _   => true
  | .methodIs m,    method, _,   _   => m == method
  | .slotChanged f, _,      old, new => !(old.scalar f == new.scalar f)
  | .anyOf cs,      method, old, new => anyMatch cs method old new
  | .allOf cs,      method, old, new => allMatch cs method old new
def anyMatch : List TransitionGuard → Nat → Value → Value → Bool
  | [],        _,      _,   _   => false
  | g :: rest, method, old, new => g.matches method old new || anyMatch rest method old new
def allMatch : List TransitionGuard → Nat → Value → Value → Bool
  | [],        _,      _,   _   => true
  | g :: rest, method, old, new => g.matches method old new && allMatch rest method old new
end

/-- One operation-scoped case: a guard + the constraints that bind when it matches. -/
structure TransitionCase where
  guard       : TransitionGuard
  constraints : List StateConstraint
  deriving Repr

/-- **The RecordProgram** — the developer-authored coalgebra structure-map. -/
inductive RecordProgram where
  /-- Terminal program: every (authorized) transition admissible. -/
  | none
  /-- A conjunction of constraints (the legacy `Always`-case shape). -/
  | predicate (constraints : List StateConstraint)
  /-- Operation-scoped cases; **no matching case ⇒ default-deny**. -/
  | cases     (cases : List TransitionCase)
  /-- An opaque AIR; admissibility = "carries a proof the circuit accepts" (Build 3). -/
  | circuit   (hash : Nat)
  deriving Repr

/-- **`admits` — the admissibility filter (the structure-map's domain).** Decidable, computable,
fail-closed. `none` admits all; `predicate` ANDs its constraints; `cases` ANDs every *matching*
arm's constraints and **denies when no arm matches** (the partial, default-deny arrow); `circuit`
denies in the pure evaluator (it needs the proof — discharged in `RecordCircuit`, Build 3). -/
def RecordProgram.admits : RecordProgram → Nat → Value → Value → Bool
  | .none,           _,      _,   _   => true
  | .predicate cs,   _,      old, new => cs.all (fun c => evalConstraint c old new)
  | .cases tcs,      method, old, new =>
      match tcs.filter (fun tc => tc.guard.matches method old new) with
      | []      => false                                              -- default-deny on no match
      | m :: ms => (m :: ms).all (fun tc => tc.constraints.all (fun c => evalConstraint c old new))
  | .circuit _,      _,      _,   _   => false

/-! ## Basic laws (the structure-map is a genuine, Heyting-respecting, fail-closed filter). -/

/-- The terminal program admits every transition. -/
theorem admits_none (m : Nat) (o n : Value) : RecordProgram.admits .none m o n = true := rfl

/-- A `predicate` program is exactly the conjunction of its constraints (definitional). -/
theorem admits_predicate (cs : List StateConstraint) (m : Nat) (o n : Value) :
    RecordProgram.admits (.predicate cs) m o n = cs.all (fun c => evalConstraint c o n) := rfl

/-- **Default-deny.** An empty `Cases` (and any `Cases` with no matching arm) denies. -/
theorem admits_cases_nil (m : Nat) (o n : Value) :
    RecordProgram.admits (.cases []) m o n = false := rfl

/-- A `Circuit` program is never admitted by the *pure* evaluator (it needs its proof). -/
theorem admits_circuit (h : Nat) (m : Nat) (o n : Value) :
    RecordProgram.admits (.circuit h) m o n = false := rfl

/-- **Negation is the Boolean complement** (the Heyting `¬` on the predicate algebra). -/
theorem evalSimple_not (c : SimpleConstraint) (o n : Value) :
    evalSimple (.not c) o n = !(evalSimple c o n) := rfl

/-- **Double negation collapses** (`¬¬c = c` on the decidable predicate algebra). -/
theorem evalSimple_not_not (c : SimpleConstraint) (o n : Value) :
    evalSimple (.not (.not c)) o n = evalSimple c o n := by
  simp [evalSimple]

/-- **Disjunction is `∃`/`any`** (the Heyting `⊔`). -/
theorem evalConstraint_anyOf (vs : List SimpleConstraint) (o n : Value) :
    evalConstraint (.anyOf vs) o n = vs.any (fun c => evalSimple c o n) := rfl

/-- **`boundDelta` now FAILS CLOSED (the soundness fix).** The single-cell evaluator REJECTS
every `boundDelta` constraint (was the silent-`true` fail-OPEN hole `Program.lean:144`). The cross-cell
delta is discharged at the JointTurn/CoordinatedCaveat seam, never admitted here. Mirrors dregg1's
`evaluate` returning `Err(BoundDeltaNotWired)` (`program.rs:1956`). -/
theorem evalConstraint_boundDelta_fails (lf : FieldName) (p : Nat) (pf : FieldName) (e : Bool)
    (o n : Value) : evalConstraint (.boundDelta lf p pf e) o n = false := rfl

/-- **`clearanceGe` admit-characterization.** The gate admits IFF the actor's clearance
label (read from `new[af]`) is present AND DOMINATES the slot's sensitivity label `box` in the
clearance graph `g` (`dominatesD`). Wires the proved-sound lattice primitive into admission. -/
theorem evalConstraint_clearanceGe_iff (g : ClearanceGraph) (af : FieldName) (box : Label)
    (o n : Value) :
    evalConstraint (.clearanceGe g af box) o n = true ↔
      ∃ actorLabel, actorLabelOf n af = some actorLabel ∧ dominatesD g actorLabel box = true := by
  unfold evalConstraint
  cases h : actorLabelOf n af with
  | none   => simp [h]
  | some a => simp [h]

/-- **`clearanceGe` ⇒ semantic dominance (soundness of the new atom).** An ADMITTED
`clearanceGe` write means the actor's clearance label `dominates` the slot's sensitivity
label in `g` (the `Prop`-level reflexive-transitive closure) — reusing the orphaned-but-proved
`dominates_of_dominatesD` (`ClearanceGraph.lean:92`). So the predicate language now has REAL lattice
teeth, not a precomputed table. -/
theorem evalConstraint_clearanceGe_sound (g : ClearanceGraph) (af : FieldName) (box : Label)
    (o n : Value) (h : evalConstraint (.clearanceGe g af box) o n = true) :
    ∃ actorLabel, actorLabelOf n af = some actorLabel ∧
      Dregg2.Authority.ClearanceGraph.dominates g actorLabel box := by
  obtain ⟨a, ha, hd⟩ := (evalConstraint_clearanceGe_iff g af box o n).mp h
  exact ⟨a, ha, Dregg2.Authority.ClearanceGraph.dominates_of_dominatesD g hd⟩

/-! ## New atom admit-characterizations (the policy-combinator core) — each PROVED. -/

/-- **`memberOf` admit-char.** Admits IFF the field is present and its value is in the
allowlist. Real teeth: a value not in `set` is rejected. -/
theorem evalSimple_memberOf_iff (f : FieldName) (set : List Int) (o n : Value) :
    evalSimple (.memberOf f set) o n = true ↔
      ∃ x, n.scalar f = some x ∧ set.contains x = true := by
  unfold evalSimple
  cases h : n.scalar f with
  | none   => simp
  | some x => simp

/-- **`prefixOf` admit-char.** Admits IFF the path reads (all segments present) AND the
queried prefix is a list-prefix of it. The structural nameservice containment. -/
theorem evalSimple_prefixOf_iff (segs : List FieldName) (pre : List Int) (o n : Value) :
    evalSimple (.prefixOf segs pre) o n = true ↔
      ∃ path, readPath n segs = some path ∧ pre.isPrefixOf path = true := by
  unfold evalSimple
  cases h : readPath n segs with
  | none      => simp
  | some path => simp

/-- **`inRangeTwoSided` admit-char.** Admits IFF the field is present and lies in `[lo,hi]`. -/
theorem evalSimple_inRangeTwoSided_iff (f : FieldName) (lo hi : Int) (o n : Value) :
    evalSimple (.inRangeTwoSided f lo hi) o n = true ↔
      ∃ x, n.scalar f = some x ∧ lo ≤ x ∧ x ≤ hi := by
  unfold evalSimple
  cases h : n.scalar f with
  | none   => simp
  | some x => simp [intLe, decide_eq_true_eq]

/-- **`deltaBounded` admit-char (REAL two-sided).** Admits IFF both old and new are present
and `|new − old| ≤ d` (symmetric: `-d ≤ new−old ≤ d`). -/
theorem evalSimple_deltaBounded_iff (f : FieldName) (d : Int) (o n : Value) :
    evalSimple (.deltaBounded f d) o n = true ↔
      ∃ a b, o.scalar f = some a ∧ n.scalar f = some b ∧ -d ≤ b - a ∧ b - a ≤ d := by
  unfold evalSimple
  cases ha : o.scalar f with
  | none   => simp
  | some a =>
    cases hb : n.scalar f with
    | none   => simp
    | some b => simp [intLe, decide_eq_true_eq]

/-- **`strictMono` admit-char (the `StrictMonotonic` mirror).** Admits IFF both old and new are
present AND `old < new` — the strict twin of `evalSimple_monotonic_iff` (`Proof/WPCatalog.lean:144`),
with the same fail-closed reading: an absent/ill-typed field on EITHER side rejects. This is the
atom the channel-group epoch-unification triple disjoins against `immutable`
(`cell/src/blueprint.rs:853` `epoch_steps_when_changed`); `Apps/ChannelGroup.lean` consumes it. -/
theorem evalSimple_strictMono_iff (f : FieldName) (o n : Value) :
    evalSimple (.strictMono f) o n = true ↔
      ∃ a b, o.scalar f = some a ∧ n.scalar f = some b ∧ a < b := by
  unfold evalSimple
  cases ha : o.scalar f with
  | none   => simp
  | some a =>
    cases hb : n.scalar f with
    | none   => simp
    | some b => simp [intLt, decide_eq_true_eq]

-- strictMono non-vacuity pair (admit a strict step / reject a plateau — the equality edge
-- `monotonic` admits and `strictMono` must refuse).
example : evalSimple (.strictMono "n") (.record [("n", .int 1)]) (.record [("n", .int 2)]) = true := by decide
example : evalSimple (.strictMono "n") (.record [("n", .int 1)]) (.record [("n", .int 1)]) = false := by decide

/-- **`affineLe` admit-char.** Admits IFF every term-field reads AND the affine combination
`Σ kᵢ·new[fᵢ] ≤ c`. The general arithmetic relation. -/
theorem evalConstraint_affineLe_iff (terms : List (Int × FieldName)) (c : Int) (o n : Value) :
    evalConstraint (.affineLe terms c) o n = true ↔
      ∃ s, affineSum n terms = some s ∧ s ≤ c := by
  unfold evalConstraint
  cases h : affineSum n terms with
  | none   => simp [h]
  | some s => simp [h, intLe]

/-- **`affineEq` admit-char.** Admits IFF every term-field reads AND `Σ kᵢ·new[fᵢ] = c`. -/
theorem evalConstraint_affineEq_iff (terms : List (Int × FieldName)) (c : Int) (o n : Value) :
    evalConstraint (.affineEq terms c) o n = true ↔
      ∃ s, affineSum n terms = some s ∧ s = c := by
  unfold evalConstraint
  cases h : affineSum n terms with
  | none   => simp [h]
  | some s => simp [h]

/-- **`affineDeltaLe` admit-char (apps gap 2).** Admits IFF every term-field reads on BOTH the
old and new record AND the affine combination of the per-field deltas `Σ kᵢ·(new[fᵢ] − old[fᵢ]) ≤ c`.
The genuine multi-field rate gate: a missing field on either side (the `none` from `affineDeltaSum`)
fails closed. -/
theorem evalConstraint_affineDeltaLe_iff (terms : List (Int × FieldName)) (c : Int) (o n : Value) :
    evalConstraint (.affineDeltaLe terms c) o n = true ↔
      ∃ s, affineDeltaSum o n terms = some s ∧ s ≤ c := by
  unfold evalConstraint
  cases h : affineDeltaSum o n terms with
  | none   => simp [h]
  | some s => simp [h, intLe]

/-- **`reachable` ⇒ semantic dominance (soundness).** An admitted `reachable` means the
source-field's label `dominates`/reaches `toLabel` in `g` (lifting `dominatesD` to the
`Prop`-level closure via the proved-sound `dominates_of_dominatesD`). The DAG-prerequisite teeth. -/
theorem evalConstraint_reachable_sound (g : ClearanceGraph) (ff : FieldName) (toL : Label)
    (o n : Value) (h : evalConstraint (.reachable g ff toL) o n = true) :
    ∃ fromLabel, actorLabelOf n ff = some fromLabel ∧
      Dregg2.Authority.ClearanceGraph.dominates g fromLabel toL := by
  have hiff : evalConstraint (.reachable g ff toL) o n = true ↔
      ∃ fromLabel, actorLabelOf n ff = some fromLabel ∧ dominatesD g fromLabel toL = true := by
    unfold evalConstraint
    cases hf : actorLabelOf n ff with
    | none          => simp [hf]
    | some fromLabel => simp [hf]
  obtain ⟨fromLabel, hf, hd⟩ := hiff.mp h
  exact ⟨fromLabel, hf, Dregg2.Authority.ClearanceGraph.dominates_of_dominatesD g hd⟩

/-! ## It runs (`#eval`) — real programs admitting / denying real record transitions. -/

/-- A counter cell: one scalar field `count`, program = "count only ever increases". -/
def counterProgram : RecordProgram := .predicate [.simple (.monotonic "count")]

def counterOld : Value := .record [("count", .int 5)]
def counterUp  : Value := .record [("count", .int 7)]   -- 7 ≥ 5  → admitted
def counterDn  : Value := .record [("count", .int 3)]   -- 3 ≥ 5? → denied

#guard (counterProgram.admits 0 counterOld counterUp)  --  true
#guard (counterProgram.admits 0 counterOld counterDn) == false  --  false

/-- A bounded state machine on `status`: only Open(0)→Claimed(1)→Paid(2). -/
def smProgram : RecordProgram :=
  .predicate [.allowedTransitions "status" [(0, 1), (1, 2)]]

#guard (smProgram.admits 0 (.record [("status", .int 0)]) (.record [("status", .int 1)]))  --  true  (Open→Claimed)
#guard (smProgram.admits 0 (.record [("status", .int 0)]) (.record [("status", .int 2)])) == false  --  false (Open↛Paid)

/-- A `Cases` program: on method `1` (a "deposit"), balance must strictly increase; any other
method has no matching arm and is **default-denied**. -/
def depositOnly : RecordProgram :=
  .cases [⟨.methodIs 1, [.simple (.strictMono "balance")]⟩]

def balLo : Value := .record [("balance", .int 100)]
def balHi : Value := .record [("balance", .int 150)]

#guard (depositOnly.admits 1 balLo balHi)  --  true  (method 1, balance ↑)
#guard (depositOnly.admits 1 balHi balLo) == false  --  false (method 1, balance ↓)
#guard (depositOnly.admits 2 balLo balHi) == false  --  false (method 2: no matching case → default-deny)

/-- Intra-cell conservation: `Σ new[ins] = Σ old[ins] + Σ new[outs]` (a split). -/
def splitProgram : RecordProgram := .predicate [.sumEqualsAcross ["a"] ["b"]]
-- old a=10; new a=4, b=6  ⇒  4 = 10 + 6? no.  new a=16, b=6 ⇒ 16 = 10 + 6 ✓
#guard (splitProgram.admits 0 (.record [("a", .int 10)]) (.record [("a", .int 16), ("b", .int 6)]))  --  true

/-! ### `boundDelta` is FAIL-CLOSED (the soundness-fix non-vacuity).  A program guarded ONLY by a
`boundDelta` now REJECTS every single-cell transition (was a fail-OPEN `true`). -/
def boundDeltaProgram : RecordProgram :=
  .predicate [.boundDelta "amt" 1 "amt" true]
-- Every single-cell write is rejected: the cross-cell delta is not evaluable here (fail-closed).
#guard (boundDeltaProgram.admits 0 (.record [("amt", .int 5)]) (.record [("amt", .int 5)])) == false  --  false
#guard (boundDeltaProgram.admits 0 (.record [("amt", .int 5)]) (.record [("amt", .int 6)])) == false  --  false

/-! ### `clearanceGe` (the SGM clearance mandate) — non-vacuity over the demo clearance ladder.

A three-level clearance ladder `top ⊐ mid ⊐ low` (ids 3 ⊐ 2 ⊐ 1).  A cell slot has sensitivity
`mid` (id 2); a write is admitted ONLY when the actor's clearance label (carried in the `clearance`
field of `new`) dominates `mid`.  `top` (3) and `mid` (2) are admitted; `low` (1) is REJECTED. -/
def clearanceLadder : ClearanceGraph :=
  { edges :=
      [ (Label.id 3, Label.id 2)      -- top ⊐ mid
      , (Label.id 2, Label.id 1) ] }  -- mid ⊐ low

/-- A slot whose sensitivity label is `mid` (id 2): a write requires actor clearance ≥ mid. -/
def clearanceProgram : RecordProgram :=
  .predicate [.clearanceGe clearanceLadder "clearance" (Label.id 2)]

-- ADMITTED: actor carries clearance `top` (3) — 3 dominates 2 (top ⊐ mid, edge).
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 1)]) (.record [("clearance", .int 3)]))  --  true
-- ADMITTED: actor carries clearance `mid` (2) — reflexive dominance.
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 1)]) (.record [("clearance", .int 2)]))  --  true
-- REJECTED: actor carries clearance `low` (1) — low does NOT dominate mid (no upward edge).
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 2)]) (.record [("clearance", .int 1)])) == false  --  false
-- REJECTED: actor-label field absent — fail-closed.
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 2)]) (.record [("other", .int 3)])) == false  --  false

/-- Non-vacuity at the theorem layer: the ADMIT case witnesses `dominatesD` AND lifts to the
`Prop`-level `dominates` (the proved soundness reduction). -/
example : evalConstraint (.clearanceGe clearanceLadder "clearance" (Label.id 2))
    (.record [("clearance", .int 1)]) (.record [("clearance", .int 3)]) = true := by decide

example : evalConstraint (.clearanceGe clearanceLadder "clearance" (Label.id 2))
    (.record [("clearance", .int 2)]) (.record [("clearance", .int 1)]) = false := by decide

/-! ### Policy-combinator atom non-vacuity — each atom ADMITS a real transition AND REJECTS one.
(The mandatory anti-vacuity pair; all `by decide`, no `native_decide`.) -/

-- memberOf: a role slot admitting only {1 admin, 2 editor, 3 viewer}.
def roleProgram : RecordProgram := .predicate [.simple (.memberOf "role" [1, 2, 3])]
#guard (roleProgram.admits 0 (.record [("role", .int 0)]) (.record [("role", .int 2)]))          -- true  (editor ∈ set)
#guard (roleProgram.admits 0 (.record [("role", .int 0)]) (.record [("role", .int 9)])) == false  -- false (9 ∉ set)
example : evalSimple (.memberOf "role" [1,2,3]) (.record []) (.record [("role", .int 2)]) = true := by decide
example : evalSimple (.memberOf "role" [1,2,3]) (.record []) (.record [("role", .int 9)]) = false := by decide

-- prefixOf: a 2-segment path must register UNDER the namespace [10, 20] (owned by the actor).
def nsProgram : RecordProgram := .predicate [.simple (.prefixOf ["seg0", "seg1", "seg2"] [10, 20])]
-- ADMIT: path [10,20,7] starts with [10,20].
#guard (nsProgram.admits 0 (.record []) (.record [("seg0", .int 10), ("seg1", .int 20), ("seg2", .int 7)]))  -- true
-- REJECT: path [10,99,7] does NOT start with [10,20].
#guard (nsProgram.admits 0 (.record []) (.record [("seg0", .int 10), ("seg1", .int 99), ("seg2", .int 7)])) == false  -- false
-- REJECT: a segment missing ⇒ fail-closed.
#guard (nsProgram.admits 0 (.record []) (.record [("seg0", .int 10), ("seg1", .int 20)])) == false  -- false
example : evalSimple (.prefixOf ["a","b"] [10]) (.record []) (.record [("a", .int 10), ("b", .int 5)]) = true := by decide
example : evalSimple (.prefixOf ["a","b"] [10]) (.record []) (.record [("a", .int 11), ("b", .int 5)]) = false := by decide

-- inRangeTwoSided: a price slot constrained to the absolute band [100, 200].
def priceProgram : RecordProgram := .predicate [.simple (.inRangeTwoSided "price" 100 200)]
#guard (priceProgram.admits 0 (.record []) (.record [("price", .int 150)]))          -- true
#guard (priceProgram.admits 0 (.record []) (.record [("price", .int 250)])) == false  -- false (above band)
example : evalSimple (.inRangeTwoSided "p" 100 200) (.record []) (.record [("p", .int 100)]) = true := by decide
example : evalSimple (.inRangeTwoSided "p" 100 200) (.record []) (.record [("p", .int 99)])  = false := by decide

-- deltaBounded: a balance may move by at most ±5 per turn (REAL two-sided).
def jitterProgram : RecordProgram := .predicate [.simple (.deltaBounded "bal" 5)]
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 104)]))          -- true  (+4)
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 96)]))           -- true  (−4)
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 110)])) == false  -- false (+10)
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 90)]))  == false  -- false (−10)
example : evalSimple (.deltaBounded "x" 5) (.record [("x", .int 0)]) (.record [("x", .int 5)])  = true  := by decide
example : evalSimple (.deltaBounded "x" 5) (.record [("x", .int 0)]) (.record [("x", .int 6)])  = false := by decide
example : evalSimple (.deltaBounded "x" 5) (.record [("x", .int 0)]) (.record [("x", .int (-6))]) = false := by decide

-- affineLe: a price band `2·bid ≤ ask + 100`, i.e. 2·bid − ask ≤ 100.
def bandProgram : RecordProgram := .predicate [.affineLe [(2, "bid"), (-1, "ask")] 100]
#guard (bandProgram.admits 0 (.record []) (.record [("bid", .int 60), ("ask", .int 40)]))           -- true  (120−40=80 ≤ 100)
#guard (bandProgram.admits 0 (.record []) (.record [("bid", .int 90), ("ask", .int 40)])) == false   -- false (180−40=140 > 100)
example : evalConstraint (.affineLe [(2,"b"),(-1,"a")] 100) (.record []) (.record [("b", .int 60),("a", .int 40)]) = true := by decide
example : evalConstraint (.affineLe [(2,"b"),(-1,"a")] 100) (.record []) (.record [("b", .int 90),("a", .int 40)]) = false := by decide

-- affineEq: conservation `in = out0 + out1` re-expressed as `in − out0 − out1 = 0`.
def consvProgram : RecordProgram := .predicate [.affineEq [(1, "inp"), (-1, "o0"), (-1, "o1")] 0]
#guard (consvProgram.admits 0 (.record []) (.record [("inp", .int 10), ("o0", .int 6), ("o1", .int 4)]))          -- true  (10−6−4=0)
#guard (consvProgram.admits 0 (.record []) (.record [("inp", .int 10), ("o0", .int 6), ("o1", .int 3)])) == false  -- false (10−6−3=1)
example : evalConstraint (.affineEq [(1,"i"),(-1,"o")] 0) (.record []) (.record [("i", .int 7),("o", .int 7)]) = true := by decide
example : evalConstraint (.affineEq [(1,"i"),(-1,"o")] 0) (.record []) (.record [("i", .int 7),("o", .int 6)]) = false := by decide

-- affineDeltaLe (apps gap 2): a treasury cell bounds its COMBINED per-turn outflow across two
-- spend slots — Δout_a + Δout_b ≤ 5 (a budget-delta gate no single-field deltaBounded can express).
def budgetProgram : RecordProgram := .predicate [.affineDeltaLe [(1, "out_a"), (1, "out_b")] 5]
-- ADMIT: out_a 10→12 (+2), out_b 20→23 (+3) → combined +5 ≤ 5.
#guard (budgetProgram.admits 0
  (.record [("out_a", .int 10), ("out_b", .int 20)])
  (.record [("out_a", .int 12), ("out_b", .int 23)]))           -- true  (Σ delta = 5)
-- REJECT: out_a 10→14 (+4), out_b 20→23 (+3) → combined +7 > 5 (the over-budget withdrawal).
#guard (budgetProgram.admits 0
  (.record [("out_a", .int 10), ("out_b", .int 20)])
  (.record [("out_a", .int 14), ("out_b", .int 23)])) == false   -- false (Σ delta = 7)
-- REJECT: a term field absent on the new side ⇒ fail-closed (the delta is not evaluable).
#guard (budgetProgram.admits 0
  (.record [("out_a", .int 10), ("out_b", .int 20)])
  (.record [("out_a", .int 12)])) == false                       -- false (out_b missing)
example : evalConstraint (.affineDeltaLe [(1,"a"),(1,"b")] 5)
  (.record [("a", .int 0),("b", .int 0)]) (.record [("a", .int 2),("b", .int 3)]) = true := by decide
example : evalConstraint (.affineDeltaLe [(1,"a"),(1,"b")] 5)
  (.record [("a", .int 0),("b", .int 0)]) (.record [("a", .int 4),("b", .int 3)]) = false := by decide

-- reachable: a workflow `step` field must reach the prerequisite marker `done` (id 1) in the DAG.
-- DAG: step-id 2 (review) reaches 1 (drafted); step-id 3 (publish) reaches 2 reaches 1.
def workflowDag : ClearanceGraph :=
  { edges := [ (Label.id 3, Label.id 2), (Label.id 2, Label.id 1) ] }
def workflowProgram : RecordProgram := .predicate [.reachable workflowDag "step" (Label.id 1)]
-- ADMIT: step 3 (publish) reaches prerequisite 1.
#guard (workflowProgram.admits 0 (.record []) (.record [("step", .int 3)]))          -- true
-- REJECT: step 4 is not in the DAG ⇒ cannot reach 1.
#guard (workflowProgram.admits 0 (.record []) (.record [("step", .int 4)])) == false  -- false
example : evalConstraint (.reachable workflowDag "step" (Label.id 1)) (.record []) (.record [("step", .int 3)]) = true := by decide
example : evalConstraint (.reachable workflowDag "step" (Label.id 1)) (.record []) (.record [("step", .int 4)]) = false := by decide

#assert_axioms evalConstraint_boundDelta_fails
#assert_axioms evalConstraint_clearanceGe_iff
#assert_axioms evalConstraint_clearanceGe_sound
#assert_axioms evalSimple_memberOf_iff
#assert_axioms evalSimple_prefixOf_iff
#assert_axioms evalSimple_inRangeTwoSided_iff
#assert_axioms evalSimple_deltaBounded_iff
#assert_axioms evalSimple_strictMono_iff
#assert_axioms evalConstraint_affineLe_iff
#assert_axioms evalConstraint_affineEq_iff
#assert_axioms evalConstraint_affineDeltaLe_iff
#assert_axioms evalConstraint_reachable_sound

/-! ## Turn-context evaluation (`docs/CELL-PROGRAM-LANGUAGE.md` §3).

The Rust executor evaluates every cell program with an `EvalContext` (the turn's sender = the
acting cell's public key, the height, the epoch) and against the post-state `CellState`, whose
SEALED balance rides along. `TurnCtx` mirrors exactly the slice of that context the new
turn-context atoms read; `evalSimpleCtx` / `evalConstraintCtx` / `RecordProgram.admitsCtx` are
the ctx-aware evaluators (mirroring `evaluate_constraint_full` with `Some(ctx)`,
`cell/src/program.rs`). The ctx-less `evalSimple` above remains the `TurnCtx.empty` special
case — `evalSimpleCtx_empty` is the conservative-extension keystone, so every existing theorem
over `evalSimple`/`admits` (the guard-theorem family, `stateStepGuarded_*` via `caveatsAdmit`)
is untouched and the new atoms ONLY ADD admissibility distinctions when a context is present. -/

/-- The turn-context slice the context atoms read. `sender` = the acting cell's identity
(`EvalContext::sender`); `balance` = the touched cell's own post-turn sealed balance
(`CellState::balance`); `revealedHash` = the §8-portal hash of the turn's revealed preimage
(`WitnessKindTag::Preimage32` after hashing). Every field is `Option` — absence FAILS CLOSED. -/
structure TurnCtx where
  sender       : Option Int := none
  balance      : Option Int := none
  revealedHash : Option Int := none
  /-- The touched cell's OWN PRE-turn sealed kernel balance (`CellState::balance` BEFORE the
  effect applied), the `balance` field's old-side twin. The executor holds both the pre- and
  post-turn balance at program-check time (Rust carrier: the journal's pre-image / the cell's
  prior `balance`); the rate atoms `balanceDeltaLe`/`balanceDeltaGe` read `new.balance − old.balance`
  from `(balance, balanceBefore)`. APPENDED (so existing `TurnCtx { … }` literals and the empty
  context are unchanged — absence FAILS CLOSED, the delta atoms refuse). -/
  balanceBefore : Option Int := none
  /-- The TOUCHED cell's own post-turn `delegation_epoch` (the R7 capability-freshness
  counter), stamped PER CELL by the executor's program-check loop. Rust carrier:
  `TransitionMeta::delegation_epoch` (per-cell, unlike the per-action `EvalContext`) —
  this `TurnCtx` models exactly the slice of executor context the atoms read, so it lands
  here. Absence FAILS CLOSED (`delegationEpochEquals` refuses). -/
  delegationEpoch : Option Int := none
  /-- The witness-exhibited element set for `countGe` (the opaque-scalar reading of the
  unique Cleartext blob, Rust postcard `Vec<[u8;32]>`). RE-EXHIBITED on every turn —
  nothing accumulates in state (the anti-`affineLe`-flag design). -/
  exhibited : List Int := []
  /-- The §8-portal canonical sorted-set commitment of the DEDUPED exhibited set (Rust
  `count_ge_set_commitment` — BLAKE3 over the length-prefixed sorted elements). Like
  `revealedHash` for `preimageGate`, the hash binding itself is the crypto portal; the
  ordering/counting laws are proved here. Absence fails closed. -/
  exhibitedCommit : Option Int := none
  deriving Repr

/-- The empty context: every context atom fails closed under it. -/
def TurnCtx.empty : TurnCtx := {}

/-- **Ctx-aware simple-constraint evaluation.** Context atoms read `ctx`; every ctx-free atom
delegates to `evalSimple` (definitionally — the delegation IS the proof obligation discharged
by `evalSimpleCtx_empty`). Fail-closed throughout. -/
def evalSimpleCtx (ctx : TurnCtx) : SimpleConstraint → Value → Value → Bool
  | .senderIs k,        _,   _   => ctx.sender == some k
  | .senderInField f,   _,   new => match ctx.sender, new.scalar f with
                                    | some s, some v => s == v
                                    | _,      _      => false
  | .balanceGe v,       _,   _   => match ctx.balance with
                                    | some b => intLe v b
                                    | none   => false
  | .balanceLe v,       _,   _   => match ctx.balance with
                                    | some b => intLe b v
                                    | none   => false
  | .preimageGate f,    _,   new => match ctx.revealedHash, new.scalar f with
                                    | some h, some c => h == c
                                    | _,      _      => false
  | .delegationEpochEquals f, _, new => match ctx.delegationEpoch, new.scalar f with
                                    | some d, some v => d == v
                                    | _,      _      => false
  | .countGe m f,       _,   new => match ctx.exhibitedCommit, new.scalar f with
                                    | some c, some v =>
                                        c == v && decide (m ≤ ctx.exhibited.eraseDups.length)
                                    | _,      _      => false
  | .senderMemberOf ms, _,   _   => match ctx.sender with
                                    | some s => ms.contains s
                                    | none   => false
  | .balanceDeltaLe mx, _,   _   => match ctx.balanceBefore, ctx.balance with
                                    | some a, some b => intLe (b - a) mx
                                    | _,      _      => false
  | .balanceDeltaGe mn, _,   _   => match ctx.balanceBefore, ctx.balance with
                                    | some a, some b => intLe mn (b - a)
                                    | _,      _      => false
  | .not c,             old, new => !(evalSimpleCtx ctx c old new)
  | c,                  old, new => evalSimple c old new

/-- **Ctx-aware constraint evaluation**: `simple`/`anyOf` thread the context; every other
variant is context-free and delegates to `evalConstraint`. -/
def evalConstraintCtx (ctx : TurnCtx) : StateConstraint → Value → Value → Bool
  | .simple c,  old, new => evalSimpleCtx ctx c old new
  | .anyOf vs,  old, new => vs.any (fun c => evalSimpleCtx ctx c old new)
  | c,          old, new => evalConstraint c old new

/-- **Ctx-aware admissibility** — `RecordProgram.admits` with the turn context threaded
through every constraint evaluation. Same default-deny structure. -/
def RecordProgram.admitsCtx (p : RecordProgram) (ctx : TurnCtx) (method : Nat)
    (old new : Value) : Bool :=
  match p with
  | .none          => true
  | .predicate cs  => cs.all (fun c => evalConstraintCtx ctx c old new)
  | .cases tcs     =>
      match tcs.filter (fun tc => tc.guard.matches method old new) with
      | []      => false
      | m :: ms =>
          (m :: ms).all (fun tc => tc.constraints.all (fun c => evalConstraintCtx ctx c old new))
  | .circuit _     => false

/-! ### Conservative extension: the empty context recovers the ctx-less evaluator. -/

/-- **`evalSimpleCtx_empty`.** Under the empty context, the ctx-aware evaluator IS the
ctx-less one on every constraint: context atoms fail closed on both sides, ctx-free atoms
delegate definitionally, `not` recurses. The existing guard-theorem family is untouched. -/
theorem evalSimpleCtx_empty (c : SimpleConstraint) (o n : Value) :
    evalSimpleCtx TurnCtx.empty c o n = evalSimple c o n := by
  induction c with
  | not c ih => simp only [evalSimpleCtx, evalSimple]; rw [ih]
  | _ => rfl

/-- `evalConstraintCtx` under the empty context is `evalConstraint`. -/
theorem evalConstraintCtx_empty (c : StateConstraint) (o n : Value) :
    evalConstraintCtx TurnCtx.empty c o n = evalConstraint c o n := by
  cases c with
  | simple s =>
      simpa only [evalConstraintCtx, evalConstraint] using evalSimpleCtx_empty s o n
  | anyOf vs =>
      simp only [evalConstraintCtx, evalConstraint]
      exact congrArg vs.any (funext fun s => evalSimpleCtx_empty s o n)
  | _ => rfl

/-- `admitsCtx` under the empty context is `admits` — the guard-evaluation theorem family
(`admits_predicate`, default-deny, …) lifts to the ctx-aware gate verbatim. -/
theorem admitsCtx_empty (p : RecordProgram) (m : Nat) (o n : Value) :
    p.admitsCtx TurnCtx.empty m o n = p.admits m o n := by
  have h : (fun c => evalConstraintCtx TurnCtx.empty c o n)
         = (fun c => evalConstraint c o n) :=
    funext fun c => evalConstraintCtx_empty c o n
  cases p with
  | none        => rfl
  | predicate cs =>
      simp only [RecordProgram.admitsCtx, RecordProgram.admits, h]
  | cases tcs   =>
      simp only [RecordProgram.admitsCtx, RecordProgram.admits, h]
  | circuit hsh => rfl

/-! ### Context-atom admit characterizations (each PROVED, each non-vacuous). -/

/-- **`senderIs` admit-char.** Admits IFF the context carries EXACTLY the bound sender. -/
theorem evalSimpleCtx_senderIs_iff (ctx : TurnCtx) (k : Int) (o n : Value) :
    evalSimpleCtx ctx (.senderIs k) o n = true ↔ ctx.sender = some k := by
  simp [evalSimpleCtx]

/-- **`senderInField` admit-char.** Admits IFF the sender is present AND equals the identity
held in `new[f]` (fail-closed on either absence). -/
theorem evalSimpleCtx_senderInField_iff (ctx : TurnCtx) (f : FieldName) (o n : Value) :
    evalSimpleCtx ctx (.senderInField f) o n = true ↔
      ∃ s, ctx.sender = some s ∧ n.scalar f = some s := by
  unfold evalSimpleCtx
  cases hs : ctx.sender with
  | none   => simp
  | some s =>
    cases hv : n.scalar f with
    | none   => simp
    | some v =>
      simp only [beq_iff_eq, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨s, rfl, rfl⟩
      · rintro ⟨x, rfl, rfl⟩; rfl

/-- **`senderMemberOf` admit-char (apps gap 3).** Admits IFF the context carries a sender AND
that sender is in the literal member set — the multi-admin generalization of `senderIs`. A sender
not on the board, or no sender at all, is REJECTED (fail-closed). -/
theorem evalSimpleCtx_senderMemberOf_iff (ctx : TurnCtx) (ms : List Int) (o n : Value) :
    evalSimpleCtx ctx (.senderMemberOf ms) o n = true ↔
      ∃ s, ctx.sender = some s ∧ ms.contains s = true := by
  unfold evalSimpleCtx
  cases hs : ctx.sender with
  | none   => simp
  | some s => simp

/-- **`balanceGe` admit-char.** Admits IFF the cell's own balance is present and `≥ v`. -/
theorem evalSimpleCtx_balanceGe_iff (ctx : TurnCtx) (v : Int) (o n : Value) :
    evalSimpleCtx ctx (.balanceGe v) o n = true ↔
      ∃ b, ctx.balance = some b ∧ v ≤ b := by
  unfold evalSimpleCtx
  cases hb : ctx.balance with
  | none   => simp
  | some b => simp [intLe, decide_eq_true_eq]

/-- **`balanceLe` admit-char.** Admits IFF the cell's own balance is present and `≤ v`. -/
theorem evalSimpleCtx_balanceLe_iff (ctx : TurnCtx) (v : Int) (o n : Value) :
    evalSimpleCtx ctx (.balanceLe v) o n = true ↔
      ∃ b, ctx.balance = some b ∧ b ≤ v := by
  unfold evalSimpleCtx
  cases hb : ctx.balance with
  | none   => simp
  | some b => simp [intLe, decide_eq_true_eq]

/-- **`balanceDeltaLe` admit-char (apps gap 4).** Admits IFF BOTH the pre- and post-turn sealed
balances are present AND the per-turn change is at most `max`: `new.balance − old.balance ≤ max`.
The rate-ceiling twin of `balanceLe`; an absent pre- OR post-balance fails closed (a rate gate
cannot be satisfied without both endpoints). -/
theorem evalSimpleCtx_balanceDeltaLe_iff (ctx : TurnCtx) (mx : Int) (o n : Value) :
    evalSimpleCtx ctx (.balanceDeltaLe mx) o n = true ↔
      ∃ a b, ctx.balanceBefore = some a ∧ ctx.balance = some b ∧ b - a ≤ mx := by
  unfold evalSimpleCtx
  cases ha : ctx.balanceBefore with
  | none   => simp
  | some a =>
    cases hb : ctx.balance with
    | none   => simp
    | some b => simp [intLe, decide_eq_true_eq]

/-- **`balanceDeltaGe` admit-char (apps gap 4).** Admits IFF BOTH the pre- and post-turn sealed
balances are present AND the per-turn change is at least `min`: `new.balance − old.balance ≥ min`.
The rate-floor twin of `balanceGe`; an absent pre- OR post-balance fails closed. -/
theorem evalSimpleCtx_balanceDeltaGe_iff (ctx : TurnCtx) (mn : Int) (o n : Value) :
    evalSimpleCtx ctx (.balanceDeltaGe mn) o n = true ↔
      ∃ a b, ctx.balanceBefore = some a ∧ ctx.balance = some b ∧ mn ≤ b - a := by
  unfold evalSimpleCtx
  cases ha : ctx.balanceBefore with
  | none   => simp
  | some a =>
    cases hb : ctx.balance with
    | none   => simp
    | some b => simp [intLe, decide_eq_true_eq]

/-- **`preimageGate` admit-char.** Admits IFF a reveal was hashed AND the hash equals the
commitment held in `new[f]`. -/
theorem evalSimpleCtx_preimageGate_iff (ctx : TurnCtx) (f : FieldName) (o n : Value) :
    evalSimpleCtx ctx (.preimageGate f) o n = true ↔
      ∃ h, ctx.revealedHash = some h ∧ n.scalar f = some h := by
  unfold evalSimpleCtx
  cases hh : ctx.revealedHash with
  | none   => simp
  | some h =>
    cases hc : n.scalar f with
    | none   => simp
    | some c =>
      simp only [beq_iff_eq, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨h, rfl, rfl⟩
      · rintro ⟨x, rfl, rfl⟩; rfl

/-! ### The program-readable `delegation_epoch` atom (the channels closure lane). -/

/-- **`delegationEpochEquals` admit-char.** Admits IFF the executor stamped the touched
cell's delegation epoch AND the post-state slot holds exactly that value — the in-program
form of the channel-group `DelegationEpochTie` (`Apps/ChannelGroup.lean` consumes this to
DISCHARGE the premise on admitted turns). -/
theorem evalSimpleCtx_delegationEpochEquals_iff (ctx : TurnCtx) (f : FieldName) (o n : Value) :
    evalSimpleCtx ctx (.delegationEpochEquals f) o n = true ↔
      ∃ d, ctx.delegationEpoch = some d ∧ n.scalar f = some d := by
  unfold evalSimpleCtx
  cases hd : ctx.delegationEpoch with
  | none   => simp
  | some d =>
    cases hv : n.scalar f with
    | none   => simp
    | some v =>
      simp only [beq_iff_eq, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨d, rfl, rfl⟩
      · rintro ⟨x, rfl, rfl⟩; rfl

/-- **`delegationEpochEquals` fails closed on a missing stamp** — a legacy/ctx-less
evaluation (no executor in the loop) can never satisfy the tie. -/
theorem evalSimpleCtx_delegationEpochEquals_absent_epoch_refuses (ctx : TurnCtx)
    (f : FieldName) (o n : Value) (h : ctx.delegationEpoch = none) :
    evalSimpleCtx ctx (.delegationEpochEquals f) o n = false := by
  cases hv : n.scalar f <;> simp [evalSimpleCtx, h, hv]

/-- **`delegationEpochEquals` fails closed on an absent/ill-typed slot.** -/
theorem evalSimpleCtx_delegationEpochEquals_absent_slot_refuses (ctx : TurnCtx)
    (f : FieldName) (o n : Value) (h : n.scalar f = none) :
    evalSimpleCtx ctx (.delegationEpochEquals f) o n = false := by
  cases hd : ctx.delegationEpoch <;> simp [evalSimpleCtx, hd, h]

/-- The ctx-LESS evaluator fails closed on `delegationEpochEquals` (definitional). -/
theorem evalSimple_delegationEpochEquals_fails (f : FieldName) (o n : Value) :
    evalSimple (.delegationEpochEquals f) o n = false := rfl

/-! ### The count-≥ / order-statistic atom (in-program M-of-N). -/

/-- **`countGe` admit-char.** Admits IFF the witness commitment is present, binds to the
post-state slot, AND the exhibited set has at least `m` DISTINCT elements
(`List.eraseDups` — duplicates collapse, so a padded exhibit cannot fake the quorum;
contrast the polis `affineLe`-flag trick, which an unbounded counter defeats). -/
theorem evalSimpleCtx_countGe_iff (ctx : TurnCtx) (m : Nat) (f : FieldName) (o n : Value) :
    evalSimpleCtx ctx (.countGe m f) o n = true ↔
      ∃ c, ctx.exhibitedCommit = some c ∧ n.scalar f = some c ∧
        m ≤ ctx.exhibited.eraseDups.length := by
  unfold evalSimpleCtx
  cases hc : ctx.exhibitedCommit with
  | none   => simp
  | some c =>
    cases hv : n.scalar f with
    | none   => simp
    | some v =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.some.injEq]
      constructor
      · rintro ⟨rfl, hm⟩; exact ⟨c, rfl, rfl, hm⟩
      · rintro ⟨x, rfl, rfl, hm⟩; exact ⟨rfl, hm⟩

/-- **`countGe` fails closed on a missing/malformed witness** (no exhibited-set
commitment in context — the Rust missing/ambiguous/undecodable-blob refusals). -/
theorem evalSimpleCtx_countGe_absent_witness_refuses (ctx : TurnCtx) (m : Nat)
    (f : FieldName) (o n : Value) (h : ctx.exhibitedCommit = none) :
    evalSimpleCtx ctx (.countGe m f) o n = false := by
  cases hv : n.scalar f <;> simp [evalSimpleCtx, h, hv]

/-- **`countGe` fails closed on an absent/ill-typed commitment slot.** -/
theorem evalSimpleCtx_countGe_absent_slot_refuses (ctx : TurnCtx) (m : Nat)
    (f : FieldName) (o n : Value) (h : n.scalar f = none) :
    evalSimpleCtx ctx (.countGe m f) o n = false := by
  cases hc : ctx.exhibitedCommit <;> simp [evalSimpleCtx, hc, h]

/-- An admitted `countGe` yields the quorum bound on the DISTINCT count (the consumable
form for app keystones — `Apps/ChannelGroup.lean`'s council point). -/
theorem evalSimpleCtx_countGe_quorum (ctx : TurnCtx) (m : Nat) (f : FieldName) (o n : Value)
    (h : evalSimpleCtx ctx (.countGe m f) o n = true) :
    m ≤ ctx.exhibited.eraseDups.length := by
  obtain ⟨c, _, _, hm⟩ := (evalSimpleCtx_countGe_iff ctx m f o n).mp h
  exact hm

/-- The ctx-LESS evaluator fails closed on `countGe` (definitional). -/
theorem evalSimple_countGe_fails (m : Nat) (f : FieldName) (o n : Value) :
    evalSimple (.countGe m f) o n = false := rfl

/-! ### THE actor-bound approval keystone (polis gap 5 → dissolved).

`anyOf [immutable f, senderIs k]` is the per-slot actor binding the polis council installs per
member: a turn LEAVING slot `f` alone is admitted for any sender (propose / certify / other
members' approvals), but FLIPPING `f` demands the turn's sender BE `k`. Capability possession
alone can no longer flip another member's slot — mirrored end-to-end by the Rust e2e
`approval_slots_are_actor_bound` (`sdk/tests/polis_governance_e2e.rs`). -/

/-- The bound member flips their own slot: admitted (regardless of the slot delta). -/
theorem actorBound_owner_flips (k : Int) (f : FieldName) (ctx : TurnCtx) (o n : Value)
    (hs : ctx.sender = some k) :
    evalConstraintCtx ctx (.anyOf [.immutable f, .senderIs k]) o n = true := by
  simp [evalConstraintCtx, evalSimpleCtx, hs]

/-- **The negative tooth**: a turn that CHANGES slot `f` (the `immutable` disjunct rejects)
with any sender other than `k` (or no sender) is REJECTED. A stolen capability cannot vote. -/
theorem actorBound_flip_requires_sender (k : Int) (f : FieldName) (ctx : TurnCtx) (o n : Value)
    (hflip : evalSimple (.immutable f) o n = false)
    (hs : ctx.sender ≠ some k) :
    evalConstraintCtx ctx (.anyOf [.immutable f, .senderIs k]) o n = false := by
  have himm : evalSimpleCtx ctx (.immutable f) o n = false := hflip
  have hsend : evalSimpleCtx ctx (.senderIs k) o n = false := by
    show (ctx.sender == some k) = false
    exact beq_eq_false_iff_ne.mpr hs
  simp [evalConstraintCtx, himm, hsend]

/-- A turn leaving slot `f` untouched is admitted for ANY sender (the ceremony turns —
propose / certify / execute — stay open under the binding). -/
theorem actorBound_untouched_open (k : Int) (f : FieldName) (ctx : TurnCtx) (o n : Value)
    (huntouched : evalSimple (.immutable f) o n = true) :
    evalConstraintCtx ctx (.anyOf [.immutable f, .senderIs k]) o n = true := by
  have himm : evalSimpleCtx ctx (.immutable f) o n = true := huntouched
  simp [evalConstraintCtx, himm]

/-! ### It runs — non-vacuity pairs for every context atom (`by decide`-free `#guard`s). -/

/-- The polis approval binding: slot `approve_a` flips only for sender 17. -/
def councilBound : StateConstraint := .anyOf [.immutable "approve_a", .senderIs 17]

-- Member 17 flips their own slot: ADMITTED.
#guard evalConstraintCtx { sender := some 17 } councilBound
  (.record [("approve_a", .int 0)]) (.record [("approve_a", .int 1)])
-- Member 99 (a real identity, a real capability — NOT the bound one): REJECTED.
#guard evalConstraintCtx { sender := some 99 } councilBound
  (.record [("approve_a", .int 0)]) (.record [("approve_a", .int 1)]) == false
-- A turn that leaves the slot alone: ADMITTED for anyone (ceremony turns stay open).
#guard evalConstraintCtx { sender := some 99 } councilBound
  (.record [("approve_a", .int 0)]) (.record [("approve_a", .int 0)])
-- No sender in context while flipping: REJECTED (fail-closed).
#guard evalConstraintCtx {} councilBound
  (.record [("approve_a", .int 0)]) (.record [("approve_a", .int 1)]) == false

-- senderInField: the slot-held controller identity.
#guard evalSimpleCtx { sender := some 5 } (.senderInField "owner")
  (.record []) (.record [("owner", .int 5)])
#guard evalSimpleCtx { sender := some 6 } (.senderInField "owner")
  (.record []) (.record [("owner", .int 5)]) == false

/-- The drain tooth (blueprint gap 2): `state = 2 (RESOLVED) ⇒ balance ≤ 0`. -/
def drainTooth : StateConstraint := .anyOf [.not (.fieldEquals "state" 2), .balanceLe 0]

-- Resolved + drained: ADMITTED.
#guard evalConstraintCtx { balance := some 0 } drainTooth (.record []) (.record [("state", .int 2)])
-- Resolved while still holding value: REJECTED (value cannot be stranded).
#guard evalConstraintCtx { balance := some 40 } drainTooth
  (.record []) (.record [("state", .int 2)]) == false
-- Open: balance unconstrained.
#guard evalConstraintCtx { balance := some 40 } drainTooth (.record []) (.record [("state", .int 1)])

-- balanceGe: the solvency floor.
#guard evalSimpleCtx { balance := some 10 } (.balanceGe 10) (.record []) (.record [])
#guard evalSimpleCtx { balance := some 9 } (.balanceGe 10) (.record []) (.record []) == false
#guard evalSimpleCtx {} (.balanceGe 0) (.record []) (.record []) == false  -- fail-closed

-- senderMemberOf (apps gap 3): a board {17, 42, 99}. A member sender ADMITS; a stranger REJECTS;
-- no sender REJECTS (fail-closed). The clean form of anyOf [senderIs 17, senderIs 42, senderIs 99].
#guard evalSimpleCtx { sender := some 42 } (.senderMemberOf [17, 42, 99]) (.record []) (.record [])
#guard evalSimpleCtx { sender := some 7 } (.senderMemberOf [17, 42, 99]) (.record []) (.record []) == false
#guard evalSimpleCtx {} (.senderMemberOf [17, 42, 99]) (.record []) (.record []) == false  -- fail-closed

/-- The MULTI-admin actor binding (apps gap 3): slot `approve` flips only for a turn sent by
SOMEONE on the board `{17, 42}` — the N-member generalization of the single-key polis tooth
`anyOf [immutable f, senderIs k]`. -/
def boardBound : StateConstraint := .anyOf [.immutable "approve", .senderMemberOf [17, 42]]

-- A board member (42) flips the slot: ADMITTED.
#guard evalConstraintCtx { sender := some 42 } boardBound
  (.record [("approve", .int 0)]) (.record [("approve", .int 1)])
-- A non-member (99) — a real identity, possibly a real stolen capability — flipping: REJECTED.
#guard evalConstraintCtx { sender := some 99 } boardBound
  (.record [("approve", .int 0)]) (.record [("approve", .int 1)]) == false
-- A turn leaving the slot alone: ADMITTED for anyone (the ceremony stays open).
#guard evalConstraintCtx { sender := some 99 } boardBound
  (.record [("approve", .int 0)]) (.record [("approve", .int 0)])

-- balanceDeltaLe / balanceDeltaGe (apps gap 4): a withdrawal-RATE gate on the sealed balance.
-- The cell may not move more than +5 per turn (ceiling) and not lose more than 5 per turn (floor
-- min = −5). An over-rate withdrawal (the adversarial drain) REJECTS; a within-rate move ADMITS;
-- an absent endpoint REJECTS (fail-closed).
#guard evalSimpleCtx { balance := some 105, balanceBefore := some 100 } (.balanceDeltaLe 5)
  (.record []) (.record [])                                                            -- +5 ≤ 5
#guard evalSimpleCtx { balance := some 110, balanceBefore := some 100 } (.balanceDeltaLe 5)
  (.record []) (.record []) == false                                                   -- +10 > 5 (over-rate)
#guard evalSimpleCtx { balance := some 95, balanceBefore := some 100 } (.balanceDeltaGe (-5))
  (.record []) (.record [])                                                            -- −5 ≥ −5
#guard evalSimpleCtx { balance := some 90, balanceBefore := some 100 } (.balanceDeltaGe (-5))
  (.record []) (.record []) == false                                                   -- −10 < −5 (over-drain)
#guard evalSimpleCtx { balance := some 105 } (.balanceDeltaLe 5)
  (.record []) (.record []) == false                                                   -- no pre-balance ⇒ fail-closed
#guard evalSimpleCtx { balanceBefore := some 100 } (.balanceDeltaGe (-5))
  (.record []) (.record []) == false                                                   -- no post-balance ⇒ fail-closed

/-- The committed-escrow gate (blueprint gap 1): `state = 2 (RELEASED) ⇒ reveal the preimage
of the commitment held in `commit`.` Composable BECAUSE `preimageGate` is a simple atom. -/
def committedRelease : StateConstraint := .anyOf [.not (.fieldEquals "state" 2), .preimageGate "commit"]

-- Release with the correct reveal: ADMITTED.
#guard evalConstraintCtx { revealedHash := some 77 } committedRelease
  (.record []) (.record [("state", .int 2), ("commit", .int 77)])
-- Release without a reveal: REJECTED.
#guard evalConstraintCtx {} committedRelease
  (.record []) (.record [("state", .int 2), ("commit", .int 77)]) == false
-- Release with the WRONG reveal: REJECTED.
#guard evalConstraintCtx { revealedHash := some 5 } committedRelease
  (.record []) (.record [("state", .int 2), ("commit", .int 77)]) == false
-- Not releasing: the gate is dormant.
#guard evalConstraintCtx {} committedRelease
  (.record []) (.record [("state", .int 1), ("commit", .int 77)])

-- delegationEpochEquals: ADMIT when the slot equals the stamped epoch; REFUSE divergence
-- (the forged epoch slot); REFUSE an absent stamp (legacy evaluation); REFUSE an absent slot.
#guard evalSimpleCtx { delegationEpoch := some 2 } (.delegationEpochEquals "epoch")
  (.record []) (.record [("epoch", .int 2)])
#guard evalSimpleCtx { delegationEpoch := some 2 } (.delegationEpochEquals "epoch")
  (.record []) (.record [("epoch", .int 3)]) == false
#guard evalSimpleCtx {} (.delegationEpochEquals "epoch")
  (.record []) (.record [("epoch", .int 2)]) == false
#guard evalSimpleCtx { delegationEpoch := some 2 } (.delegationEpochEquals "epoch")
  (.record []) (.record []) == false

-- countGe: a 2-distinct exhibit meets threshold 2; a DUPLICATE-PADDED exhibit collapses
-- (THE anti-affineLe tooth: [7,7,7] is ONE approver, not three); a mismatched commitment
-- refuses; a missing witness refuses; threshold 3 over 2 distinct refuses.
#guard evalSimpleCtx { exhibited := [7, 9], exhibitedCommit := some 55 } (.countGe 2 "qc")
  (.record []) (.record [("qc", .int 55)])
#guard evalSimpleCtx { exhibited := [7, 7, 7], exhibitedCommit := some 55 } (.countGe 2 "qc")
  (.record []) (.record [("qc", .int 55)]) == false
#guard evalSimpleCtx { exhibited := [7, 9], exhibitedCommit := some 55 } (.countGe 2 "qc")
  (.record []) (.record [("qc", .int 66)]) == false
#guard evalSimpleCtx { exhibited := [7, 9] } (.countGe 2 "qc")
  (.record []) (.record [("qc", .int 55)]) == false
#guard evalSimpleCtx { exhibited := [7, 9], exhibitedCommit := some 55 } (.countGe 3 "qc")
  (.record []) (.record [("qc", .int 55)]) == false

-- The conservative extension, witnessed computably on a context atom and a legacy atom.
#guard evalSimpleCtx TurnCtx.empty (.senderIs 17) (.record []) (.record []) == evalSimple (.senderIs 17) (.record []) (.record [])
#guard evalSimpleCtx TurnCtx.empty (.monotonic "n") (.record [("n", .int 1)]) (.record [("n", .int 2)]) == evalSimple (.monotonic "n") (.record [("n", .int 1)]) (.record [("n", .int 2)])
-- ... and on the two NEW context atoms (both fail closed under the empty context).
#guard evalSimpleCtx TurnCtx.empty (.delegationEpochEquals "epoch") (.record []) (.record [("epoch", .int 0)]) == evalSimple (.delegationEpochEquals "epoch") (.record []) (.record [("epoch", .int 0)])
#guard evalSimpleCtx TurnCtx.empty (.countGe 1 "qc") (.record []) (.record [("qc", .int 55)]) == evalSimple (.countGe 1 "qc") (.record []) (.record [("qc", .int 55)])
-- ... and on the three NEWEST context atoms (senderMemberOf / balanceDeltaLe / balanceDeltaGe —
-- each fails closed under the empty context, so the conservative extension holds verbatim).
#guard evalSimpleCtx TurnCtx.empty (.senderMemberOf [17, 42]) (.record []) (.record []) == evalSimple (.senderMemberOf [17, 42]) (.record []) (.record [])
#guard evalSimpleCtx TurnCtx.empty (.balanceDeltaLe 5) (.record []) (.record []) == evalSimple (.balanceDeltaLe 5) (.record []) (.record [])
#guard evalSimpleCtx TurnCtx.empty (.balanceDeltaGe (-5)) (.record []) (.record []) == evalSimple (.balanceDeltaGe (-5)) (.record []) (.record [])

#assert_axioms evalSimpleCtx_delegationEpochEquals_iff
#assert_axioms evalSimpleCtx_delegationEpochEquals_absent_epoch_refuses
#assert_axioms evalSimpleCtx_delegationEpochEquals_absent_slot_refuses
#assert_axioms evalSimple_delegationEpochEquals_fails
#assert_axioms evalSimpleCtx_countGe_iff
#assert_axioms evalSimpleCtx_countGe_absent_witness_refuses
#assert_axioms evalSimpleCtx_countGe_absent_slot_refuses
#assert_axioms evalSimpleCtx_countGe_quorum
#assert_axioms evalSimple_countGe_fails
#assert_axioms evalSimpleCtx_empty
#assert_axioms evalConstraintCtx_empty
#assert_axioms admitsCtx_empty
#assert_axioms evalSimpleCtx_senderIs_iff
#assert_axioms evalSimpleCtx_senderInField_iff
#assert_axioms evalSimpleCtx_senderMemberOf_iff
#assert_axioms evalSimpleCtx_balanceGe_iff
#assert_axioms evalSimpleCtx_balanceLe_iff
#assert_axioms evalSimpleCtx_balanceDeltaLe_iff
#assert_axioms evalSimpleCtx_balanceDeltaGe_iff
#assert_axioms evalSimpleCtx_preimageGate_iff
#assert_axioms actorBound_owner_flips
#assert_axioms actorBound_flip_requires_sender
#assert_axioms actorBound_untouched_open

/-! ## Heap-keyed constraint atoms (THE ROTATION's app-state lane).

The rotation's register economics — "registers are the L1; apps live in the heap" — needs cell
programs that CONSTRAIN heap fields, not just the 8 reserved slots. The Rust executor already
ADMITS heap writes (`SetField` with index `≥ STATE_SLOTS` routes into `CellState.fields_map`,
commit `b133354fc`); this section gives the constraint language its heap-keyed atoms.

**The design is a LIFT, not a new vocabulary.** This record substrate is already name-keyed and
`Option`-valued (`Value.scalar : Value → FieldName → Option Int`), so a heap field IS a field:
the canonical encoding `heapKey k` (= `FieldsMap.userKey`, base-10; welded by
`FieldsMap.userKey_eq_heapKey`) names heap key `k`, and a heap-keyed constraint is the EXISTING
name-keyed atom instantiated at that name. `HeapAtom` is the index-free residue of the slot-atom
vocabulary; `HeapAtom.lift k` interprets it into `SimpleConstraint`. Consequences, all free:

  * every existing admit-characterization (`evalSimple_strictMono_iff`, `evalSimple_memberOf_iff`,
    …) applies to heap-keyed constraints VERBATIM (witnessed below by the one-line reuse proofs);
  * the Heyting fragment composes: `not (a.lift k)`, `anyOf [a.lift k, .senderIs pk]` — the
    per-HEAP-field actor binding reuses the `actorBound_*` theorems at `f := heapKey k`
    (`heapActorBound_flip_requires_sender`);
  * the WP/VCG catalog (`Proof/WPCatalog.lean`) and the circuit compiler consume heap-keyed
    programs with NO new cases (a lifted atom is a `.simple` constraint).

**Absence semantics are the record substrate's `Option` reads, now load-bearing** (the heap is
partial where slots are total): post-state atoms (`equals`/`ge`/`le`/`memberOf`/
`inRangeTwoSided`) FAIL CLOSED on an absent post-state key; relational atoms
(`monotonic`/`strictMono`/`deltaBounded`) FAIL CLOSED on an absent key on EITHER side — there is
NO init escape on the heap, unlike the Rust slot twins' `(old_state = None, nonce = 0)` carve-out;
`immutable` admits the FIRST write (absent-old) and then pins — including REFUSING erasure;
`writeOnce` admits on absent-old or zero-old, then freezes. Each clause is a THEOREM below
(`evalHeap_*_absent_*` / `_pinned` / `_frozen`), not a comment.

Rust mirror: `SimpleStateConstraint::HeapField`/`StateConstraint::HeapField { key, atom }` +
`evaluate_heap_atom` (`cell/src/program.rs`), reading `CellState::get_field_ext` (`Option`-valued,
exactly `Value.scalar` at `heapKey k`). -/

/-- **`heapKey k`** — the canonical `FieldName` for heap key `k` (base-10, the
`FieldsMap.userKey` encoding; `FieldsMap.userKey_eq_heapKey` is `rfl`). Keys `≥ reservedKeys`
are the user heap; low keys name the reserved registers under the same encoding. -/
def heapKey (k : Nat) : FieldName := toString k

/-- **`HeapAtom`** — the index-free residue of the slot-atom vocabulary, liftable over any heap
key. Deliberately NOT recursive: negation/disjunction come from lifting into the existing
Heyting fragment (`.not (a.lift k)`, `anyOf [a.lift k, …]`). Mirrors Rust
`cell/src/program.rs::HeapAtom` field-for-field. (Distinct from
`Substrate.HeapKernel.HeapAtom`, the heap-WRITE guard literals; these are cell-program
constraint atoms over the heap-backed fields of `(old, new)`.) -/
inductive HeapAtom where
  /-- `new[heap k] = v` (absent ⇒ refuse: absent ≠ present-zero on the heap). -/
  | equals (v : Int)
  /-- `new[heap k] ≥ v` (absent ⇒ refuse). -/
  | ge (v : Int)
  /-- `new[heap k] ≤ v` (absent ⇒ refuse). -/
  | le (v : Int)
  /-- First write free (absent-old admits), then pinned — erasure refused. -/
  | immutable
  /-- Absent-old or zero-old admits anything; a nonzero old freezes the key. -/
  | writeOnce
  /-- `old[heap k] ≤ new[heap k]`, BOTH present (no init escape on the heap). -/
  | monotonic
  /-- `old[heap k] < new[heap k]`, both present. -/
  | strictMono
  /-- `new[heap k] ∈ set` (absent ⇒ refuse). -/
  | memberOf (set : List Int)
  /-- `lo ≤ new[heap k] ≤ hi` (absent ⇒ refuse). -/
  | inRangeTwoSided (lo hi : Int)
  /-- `|new[heap k] − old[heap k]| ≤ d`, both present. -/
  | deltaBounded (d : Int)
  deriving Repr

/-- **THE LIFT** — a heap atom is the existing name-keyed atom at `heapKey k`. This definitional
equation is the whole design: heap-keyed constraints inherit the slot atoms' semantics,
characterizations, and composition with zero new evaluator cases. -/
def HeapAtom.lift (k : Nat) : HeapAtom → SimpleConstraint
  | .equals v            => .fieldEquals (heapKey k) v
  | .ge v                => .fieldGe (heapKey k) v
  | .le v                => .fieldLe (heapKey k) v
  | .immutable           => .immutable (heapKey k)
  | .writeOnce           => .writeOnce (heapKey k)
  | .monotonic           => .monotonic (heapKey k)
  | .strictMono          => .strictMono (heapKey k)
  | .memberOf s          => .memberOf (heapKey k) s
  | .inRangeTwoSided l h => .inRangeTwoSided (heapKey k) l h
  | .deltaBounded d      => .deltaBounded (heapKey k) d

/-- Evaluate a heap atom against `(old, new)` — BY DEFINITION the existing evaluator on the
lifted constraint (`evalHeap_eq_evalSimple` is `rfl`). -/
def evalHeap (k : Nat) (a : HeapAtom) (o n : Value) : Bool :=
  evalSimple (a.lift k) o n

/-- **The lift-preservation keystone (definitional).** Evaluating a heap atom IS evaluating the
lifted slot atom — so every `evalSimple` theorem transports to the heap by instantiation. -/
theorem evalHeap_eq_evalSimple (k : Nat) (a : HeapAtom) (o n : Value) :
    evalHeap k a o n = evalSimple (a.lift k) o n := rfl

/-! ### Characterizations transported by REUSE (the lift pays for itself).
Each of these is the existing admit-characterization instantiated at `heapKey k` — no new
proof content, which is exactly the point of the lifting design. -/

/-- `strictMono` over a heap key — `evalSimple_strictMono_iff` at `heapKey k`, verbatim. -/
theorem evalHeap_strictMono_iff (k : Nat) (o n : Value) :
    evalHeap k .strictMono o n = true ↔
      ∃ a b, o.scalar (heapKey k) = some a ∧ n.scalar (heapKey k) = some b ∧ a < b :=
  evalSimple_strictMono_iff (heapKey k) o n

/-- `memberOf` over a heap key — `evalSimple_memberOf_iff` at `heapKey k`, verbatim. -/
theorem evalHeap_memberOf_iff (k : Nat) (set : List Int) (o n : Value) :
    evalHeap k (.memberOf set) o n = true ↔
      ∃ x, n.scalar (heapKey k) = some x ∧ set.contains x = true :=
  evalSimple_memberOf_iff (heapKey k) set o n

/-- `inRangeTwoSided` over a heap key — the existing iff at `heapKey k`, verbatim. -/
theorem evalHeap_inRangeTwoSided_iff (k : Nat) (lo hi : Int) (o n : Value) :
    evalHeap k (.inRangeTwoSided lo hi) o n = true ↔
      ∃ x, n.scalar (heapKey k) = some x ∧ lo ≤ x ∧ x ≤ hi :=
  evalSimple_inRangeTwoSided_iff (heapKey k) lo hi o n

/-- `deltaBounded` over a heap key — the existing iff at `heapKey k`, verbatim. -/
theorem evalHeap_deltaBounded_iff (k : Nat) (d : Int) (o n : Value) :
    evalHeap k (.deltaBounded d) o n = true ↔
      ∃ a b, o.scalar (heapKey k) = some a ∧ n.scalar (heapKey k) = some b ∧
        -d ≤ b - a ∧ b - a ≤ d :=
  evalSimple_deltaBounded_iff (heapKey k) d o n

/-! ### Characterizations for the atoms that lacked standalone iffs (proved fresh, same shape). -/

/-- **`equals` admit-char.** Admits IFF the post-state key is present AND equal — on the heap,
absent ≠ present-zero (the Rust slot `FieldEquals{value: 0}` would pass on an all-zero slot;
the heap atom REFUSES an absent key even for `v = 0`). -/
theorem evalHeap_equals_iff (k : Nat) (v : Int) (o n : Value) :
    evalHeap k (.equals v) o n = true ↔ n.scalar (heapKey k) = some v := by
  simp [evalHeap, HeapAtom.lift, evalSimple]

/-- **`ge` admit-char.** Admits IFF present and `≥ v`. -/
theorem evalHeap_ge_iff (k : Nat) (v : Int) (o n : Value) :
    evalHeap k (.ge v) o n = true ↔
      ∃ x, n.scalar (heapKey k) = some x ∧ v ≤ x := by
  unfold evalHeap HeapAtom.lift evalSimple
  cases h : n.scalar (heapKey k) with
  | none   => simp
  | some x => simp [intLe, decide_eq_true_eq]

/-- **`le` admit-char.** Admits IFF present and `≤ v`. -/
theorem evalHeap_le_iff (k : Nat) (v : Int) (o n : Value) :
    evalHeap k (.le v) o n = true ↔
      ∃ x, n.scalar (heapKey k) = some x ∧ x ≤ v := by
  unfold evalHeap HeapAtom.lift evalSimple
  cases h : n.scalar (heapKey k) with
  | none   => simp
  | some x => simp [intLe, decide_eq_true_eq]

/-- **`monotonic` admit-char.** Admits IFF BOTH sides are present and `old ≤ new` — the heap
twin of `Proof/WPCatalog.evalSimple_monotonic_iff`, restated here at `heapKey k` (this file is
upstream of the catalog). NO init escape: an absent old key refuses (cf. the Rust slot
`Monotonic`'s `(old_state = None, nonce = 0)` carve-out, which the heap atom deliberately
does NOT inherit). -/
theorem evalHeap_monotonic_iff (k : Nat) (o n : Value) :
    evalHeap k .monotonic o n = true ↔
      ∃ a b, o.scalar (heapKey k) = some a ∧ n.scalar (heapKey k) = some b ∧ a ≤ b := by
  unfold evalHeap HeapAtom.lift evalSimple
  cases ho : o.scalar (heapKey k) with
  | none   => simp
  | some a =>
    cases hn : n.scalar (heapKey k) with
    | none   => simp
    | some b => simp [intLe, decide_eq_true_eq]

/-! ### Absence semantics AS THEOREMS (the heap is partial; every clause is pinned). -/

/-- **`immutable`, absent-old: the FIRST write is free.** An unborn heap key may be initialized
to anything (including being left absent). -/
theorem evalHeap_immutable_absent_old_admits (k : Nat) (o n : Value)
    (h : o.scalar (heapKey k) = none) :
    evalHeap k .immutable o n = true := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`immutable`, present-old: the key is PINNED** — admission is exactly "the post-state holds
the same value". Erasure (`new` absent) is therefore refused (`evalHeap_immutable_erase_refused`). -/
theorem evalHeap_immutable_pinned (k : Nat) (a : Int) (o n : Value)
    (h : o.scalar (heapKey k) = some a) :
    evalHeap k .immutable o n = (n.scalar (heapKey k) == some a) := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`immutable` refuses ERASURE**: a present key cannot be deleted out of the heap. -/
theorem evalHeap_immutable_erase_refused (k : Nat) (a : Int) (o n : Value)
    (h : o.scalar (heapKey k) = some a) (hn : n.scalar (heapKey k) = none) :
    evalHeap k .immutable o n = false := by
  rw [evalHeap_immutable_pinned k a o n h, hn]; rfl

/-- **`writeOnce`, absent-old admits** (the register-once first write). -/
theorem evalHeap_writeOnce_absent_admits (k : Nat) (o n : Value)
    (h : o.scalar (heapKey k) = none) :
    evalHeap k .writeOnce o n = true := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`writeOnce`, zero-old admits** (a present-but-zero key counts as unwritten — the slot
convention, kept so a key can be PRE-DECLARED at zero and written once later). -/
theorem evalHeap_writeOnce_zero_admits (k : Nat) (o n : Value)
    (h : o.scalar (heapKey k) = some 0) :
    evalHeap k .writeOnce o n = true := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`writeOnce`, written-old FREEZES**: once nonzero, admission is exactly "unchanged"
(erasure refused for the same reason as `immutable`). -/
theorem evalHeap_writeOnce_frozen (k : Nat) (a : Int) (ha : a ≠ 0) (o n : Value)
    (h : o.scalar (heapKey k) = some a) :
    evalHeap k .writeOnce o n = (n.scalar (heapKey k) == some a) := by
  -- `simp only` discharges the match's `a ≠ 0` side condition from `ha` in context.
  simp only [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`monotonic` fails closed on an absent OLD key** — no init escape on the heap. -/
theorem evalHeap_monotonic_absent_old_refuses (k : Nat) (o n : Value)
    (h : o.scalar (heapKey k) = none) :
    evalHeap k .monotonic o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`monotonic` fails closed on an absent NEW key** — a monotone key cannot be erased. -/
theorem evalHeap_monotonic_absent_new_refuses (k : Nat) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k .monotonic o n = false := by
  cases ho : o.scalar (heapKey k) <;> simp [evalHeap, HeapAtom.lift, evalSimple, ho, h]

/-- **`strictMono` fails closed on an absent OLD key.** -/
theorem evalHeap_strictMono_absent_old_refuses (k : Nat) (o n : Value)
    (h : o.scalar (heapKey k) = none) :
    evalHeap k .strictMono o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`strictMono` fails closed on an absent NEW key.** -/
theorem evalHeap_strictMono_absent_new_refuses (k : Nat) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k .strictMono o n = false := by
  cases ho : o.scalar (heapKey k) <;> simp [evalHeap, HeapAtom.lift, evalSimple, ho, h]

/-- **`deltaBounded` fails closed on an absent OLD key.** -/
theorem evalHeap_deltaBounded_absent_old_refuses (k : Nat) (d : Int) (o n : Value)
    (h : o.scalar (heapKey k) = none) :
    evalHeap k (.deltaBounded d) o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`deltaBounded` fails closed on an absent NEW key.** -/
theorem evalHeap_deltaBounded_absent_new_refuses (k : Nat) (d : Int) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k (.deltaBounded d) o n = false := by
  cases ho : o.scalar (heapKey k) <;> simp [evalHeap, HeapAtom.lift, evalSimple, ho, h]

/-- **`equals` fails closed on an absent NEW key** (absent ≠ present-zero on the heap). -/
theorem evalHeap_equals_absent_refuses (k : Nat) (v : Int) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k (.equals v) o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`ge` fails closed on an absent NEW key.** -/
theorem evalHeap_ge_absent_refuses (k : Nat) (v : Int) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k (.ge v) o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`le` fails closed on an absent NEW key.** -/
theorem evalHeap_le_absent_refuses (k : Nat) (v : Int) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k (.le v) o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`memberOf` fails closed on an absent NEW key.** -/
theorem evalHeap_memberOf_absent_refuses (k : Nat) (set : List Int) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k (.memberOf set) o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-- **`inRangeTwoSided` fails closed on an absent NEW key.** -/
theorem evalHeap_inRangeTwoSided_absent_refuses (k : Nat) (lo hi : Int) (o n : Value)
    (h : n.scalar (heapKey k) = none) :
    evalHeap k (.inRangeTwoSided lo hi) o n = false := by
  simp [evalHeap, HeapAtom.lift, evalSimple, h]

/-! ### Composition transports too: the per-HEAP-field actor binding is the slot theorem at
`heapKey k` — the polis `anyOf [immutable f, senderIs pk]` tooth now guards heap state. -/

/-- A turn that CHANGES heap key `k` with any sender other than `pk` is REJECTED — the
`actorBound_flip_requires_sender` theorem applied verbatim at `f := heapKey k` (the lift is
definitional, so the slot proof IS the heap proof). -/
theorem heapActorBound_flip_requires_sender (k : Nat) (pk : Int) (ctx : TurnCtx) (o n : Value)
    (hflip : evalSimple (HeapAtom.immutable.lift k) o n = false)
    (hs : ctx.sender ≠ some pk) :
    evalConstraintCtx ctx (.anyOf [HeapAtom.immutable.lift k, .senderIs pk]) o n = false :=
  actorBound_flip_requires_sender pk (heapKey k) ctx o n hflip hs

/-! ### It runs — non-vacuity BOTH polarities + the absence cases, per atom (heap key 42). -/

-- equals: admit the equal value / refuse another / refuse ABSENT even for v = 0.
#guard evalHeap 42 (.equals 5) (.record []) (.record [(heapKey 42, .int 5)])
#guard evalHeap 42 (.equals 5) (.record []) (.record [(heapKey 42, .int 6)]) == false
#guard evalHeap 42 (.equals 0) (.record []) (.record []) == false  -- absent ≠ zero
-- ge / le: band edges + absence.
#guard evalHeap 42 (.ge 10) (.record []) (.record [(heapKey 42, .int 10)])
#guard evalHeap 42 (.ge 10) (.record []) (.record [(heapKey 42, .int 9)]) == false
#guard evalHeap 42 (.ge 0)  (.record []) (.record []) == false
#guard evalHeap 42 (.le 10) (.record []) (.record [(heapKey 42, .int 10)])
#guard evalHeap 42 (.le 10) (.record []) (.record [(heapKey 42, .int 11)]) == false
#guard evalHeap 42 (.le 10) (.record []) (.record []) == false
-- immutable: first write free / pin holds / flip refused / ERASURE refused.
#guard evalHeap 42 .immutable (.record []) (.record [(heapKey 42, .int 7)])
#guard evalHeap 42 .immutable (.record [(heapKey 42, .int 7)]) (.record [(heapKey 42, .int 7)])
#guard evalHeap 42 .immutable (.record [(heapKey 42, .int 7)]) (.record [(heapKey 42, .int 8)]) == false
#guard evalHeap 42 .immutable (.record [(heapKey 42, .int 7)]) (.record []) == false
-- writeOnce: absent-old free / zero-old free / written freezes (change AND erase refused).
#guard evalHeap 42 .writeOnce (.record []) (.record [(heapKey 42, .int 9)])
#guard evalHeap 42 .writeOnce (.record [(heapKey 42, .int 0)]) (.record [(heapKey 42, .int 9)])
#guard evalHeap 42 .writeOnce (.record [(heapKey 42, .int 9)]) (.record [(heapKey 42, .int 9)])
#guard evalHeap 42 .writeOnce (.record [(heapKey 42, .int 9)]) (.record [(heapKey 42, .int 1)]) == false
#guard evalHeap 42 .writeOnce (.record [(heapKey 42, .int 9)]) (.record []) == false
-- monotonic: up admits / down refuses / ABSENT-old refuses (no heap init escape) / erase refuses.
#guard evalHeap 42 .monotonic (.record [(heapKey 42, .int 1)]) (.record [(heapKey 42, .int 2)])
#guard evalHeap 42 .monotonic (.record [(heapKey 42, .int 2)]) (.record [(heapKey 42, .int 1)]) == false
#guard evalHeap 42 .monotonic (.record []) (.record [(heapKey 42, .int 2)]) == false
#guard evalHeap 42 .monotonic (.record [(heapKey 42, .int 1)]) (.record []) == false
-- strictMono: strict step admits / plateau refuses / absence refuses both sides.
#guard evalHeap 42 .strictMono (.record [(heapKey 42, .int 1)]) (.record [(heapKey 42, .int 2)])
#guard evalHeap 42 .strictMono (.record [(heapKey 42, .int 1)]) (.record [(heapKey 42, .int 1)]) == false
#guard evalHeap 42 .strictMono (.record []) (.record [(heapKey 42, .int 2)]) == false
#guard evalHeap 42 .strictMono (.record [(heapKey 42, .int 1)]) (.record []) == false
-- memberOf: in-set admits / out-of-set refuses / absent refuses.
#guard evalHeap 42 (.memberOf [1, 2, 3]) (.record []) (.record [(heapKey 42, .int 2)])
#guard evalHeap 42 (.memberOf [1, 2, 3]) (.record []) (.record [(heapKey 42, .int 9)]) == false
#guard evalHeap 42 (.memberOf [1, 2, 3]) (.record []) (.record []) == false
-- inRangeTwoSided: in-band admits / out-of-band refuses / absent refuses.
#guard evalHeap 42 (.inRangeTwoSided 100 200) (.record []) (.record [(heapKey 42, .int 150)])
#guard evalHeap 42 (.inRangeTwoSided 100 200) (.record []) (.record [(heapKey 42, .int 99)]) == false
#guard evalHeap 42 (.inRangeTwoSided 100 200) (.record []) (.record []) == false
-- deltaBounded: ±d admits / beyond refuses / absence refuses both sides.
#guard evalHeap 42 (.deltaBounded 5) (.record [(heapKey 42, .int 100)]) (.record [(heapKey 42, .int 96)])
#guard evalHeap 42 (.deltaBounded 5) (.record [(heapKey 42, .int 100)]) (.record [(heapKey 42, .int 110)]) == false
#guard evalHeap 42 (.deltaBounded 5) (.record []) (.record [(heapKey 42, .int 3)]) == false
#guard evalHeap 42 (.deltaBounded 5) (.record [(heapKey 42, .int 3)]) (.record []) == false

-- Heyting composition: a lifted heap atom under `not` and under the actor-bound `anyOf`.
#guard evalSimple (.not (HeapAtom.lift 42 (.equals 5))) (.record []) (.record [(heapKey 42, .int 6)])
#guard evalConstraintCtx { sender := some 17 } (.anyOf [HeapAtom.immutable.lift 42, .senderIs 17])
  (.record [(heapKey 42, .int 0)]) (.record [(heapKey 42, .int 1)])
#guard evalConstraintCtx { sender := some 99 } (.anyOf [HeapAtom.immutable.lift 42, .senderIs 17])
  (.record [(heapKey 42, .int 0)]) (.record [(heapKey 42, .int 1)]) == false

/-- One program mixing a NAMED register field and a heap key — the slot/heap coexistence the
Rust blueprint test mirrors (`cell/src/blueprint.rs` channel + heap message counter). -/
def mixedHeapProgram : RecordProgram := .predicate
  [ .simple (.monotonic "epoch"),
    .simple (HeapAtom.monotonic.lift 64) ]

#guard mixedHeapProgram.admits 0
  (.record [("epoch", .int 1), (heapKey 64, .int 5)])
  (.record [("epoch", .int 1), (heapKey 64, .int 9)])
#guard mixedHeapProgram.admits 0
  (.record [("epoch", .int 1), (heapKey 64, .int 5)])
  (.record [("epoch", .int 1), (heapKey 64, .int 3)]) == false   -- heap tooth bites
#guard mixedHeapProgram.admits 0
  (.record [("epoch", .int 2), (heapKey 64, .int 5)])
  (.record [("epoch", .int 1), (heapKey 64, .int 9)]) == false   -- slot tooth still bites

#assert_axioms evalHeap_eq_evalSimple
#assert_axioms evalHeap_strictMono_iff
#assert_axioms evalHeap_memberOf_iff
#assert_axioms evalHeap_inRangeTwoSided_iff
#assert_axioms evalHeap_deltaBounded_iff
#assert_axioms evalHeap_equals_iff
#assert_axioms evalHeap_ge_iff
#assert_axioms evalHeap_le_iff
#assert_axioms evalHeap_monotonic_iff
#assert_axioms evalHeap_immutable_absent_old_admits
#assert_axioms evalHeap_immutable_pinned
#assert_axioms evalHeap_immutable_erase_refused
#assert_axioms evalHeap_writeOnce_absent_admits
#assert_axioms evalHeap_writeOnce_zero_admits
#assert_axioms evalHeap_writeOnce_frozen
#assert_axioms evalHeap_monotonic_absent_old_refuses
#assert_axioms evalHeap_monotonic_absent_new_refuses
#assert_axioms evalHeap_strictMono_absent_old_refuses
#assert_axioms evalHeap_strictMono_absent_new_refuses
#assert_axioms evalHeap_deltaBounded_absent_old_refuses
#assert_axioms evalHeap_deltaBounded_absent_new_refuses
#assert_axioms evalHeap_equals_absent_refuses
#assert_axioms evalHeap_ge_absent_refuses
#assert_axioms evalHeap_le_absent_refuses
#assert_axioms evalHeap_memberOf_absent_refuses
#assert_axioms evalHeap_inRangeTwoSided_absent_refuses
#assert_axioms heapActorBound_flip_requires_sender

end Dregg2.Exec
