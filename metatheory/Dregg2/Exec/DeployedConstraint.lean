/-
`Dregg2.Exec.DeployedConstraint` — THE single Lean source for the deployed
constraint evaluator's LEAN-EVALUATED subset: the pure (state/heap-only) arms
PLUS the bounded, explicitly-marshalled CONTEXT arms (block height / turn sender /
delegation epoch) PLUS the `AnyOf` / `AllOf` boolean combinators over them.

## Why this file exists (the reality-gate collapse)

`docs/audit/GAME-PROOF-LARP-AUDIT.md` + `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`
found that the game correctness proofs prove against a **hand-authored Lean copy**
of `cell/src/program/eval.rs` — a PARALLEL-DISCONNECTED evaluator that Rust never
calls, and that ALREADY DIVERGED from the deployed evaluator in two places:

  (a) `HeapAtom.immutable` — the tug copy `decide (new = old)` refuses the first
      write; the deployed `eval.rs:2382` admits the first write then freezes
      (`None => Ok(()) | Some a => new == Some a`).
  (b) `fieldGe` — the Exec copy `intLe val x` is a **signed unbounded `Int`**;
      the deployed `eval.rs:2842` `a >= b` is an **unsigned 256-bit big-endian**
      `[u8;32]` compare.

This module is the ONE evaluator, authored over the DEPLOYED substrate
(`[FieldElement;16]` registers + the unbounded-key heap, UNSIGNED 256-bit field
arithmetic with a low-64-bit lane for the counter reads), with BOTH divergences
reconciled to the **sound deployed semantics** (see `admits` / `heapAdmits`).
It is `@[export dregg_constraint_admits]`-ed (`admitsFFI`) so Rust CALLS it
instead of carrying its own `match`; `dregg-lean-ffi` links the compiled object
and the deployed admission decision is COMPUTED BY THIS FUNCTION.

## The substrate

A field value is the unsigned 256-bit big-endian integer a `[u8;32]` denotes, so
`DField := Nat` (invariant `< 2^256`, enforced by the 32-byte wire), unsigned
compare = `Nat` compare, and the deployed `field_to_u64` low lane = `n % 2^64`.
The cell BALANCE is a SIGNED `i64` (THE EPOCH §5), so it is modelled as `Int`.

## The three classes (`docs/audit/CIRCUIT-LEAN-BOUNDARY.md` widening)

* **(a) PURE** — reads only `(old, new)` registers / the heap / the balance.
  Evaluated HERE.
* **(b) CONTEXT** — additionally reads a SMALL, TYPED slice of `EvalContext` /
  `TransitionMeta`: `block_height : u64`, `sender : Option [u8;32]`,
  `delegation_epoch : Option u64`, `sender_epoch_count : u64`. That slice is
  marshalled EXPLICITLY onto the wire (`DCtx`) and each absence is a first-class
  token, so an absent context produces the deployed `MissingContextField` verdict
  — FAIL-CLOSED, never a silent admit. Evaluated HERE.
* **(c) WITNESS / CRYPTO** — dispatches to a hash, a proof verifier, a DSL
  runtime, or a peer cell: `SenderAuthorized`, `Renounced`, `PreimageGate`,
  `KeyRotationGate`, `Witnessed`, `TemporalPredicate`, `Custom`, `CountGe`,
  `ObservedFieldEquals`, `AnyOfBound`, `ClearanceDominates` — ELEVEN arms. These
  are NOT evaluated here; they are the NAMED TRUSTED-RUST SLOT, enumerated
  exhaustively in `exec-lean/src/constraint_oracle.rs::encode_constraint` (no
  wildcard arm — a new `StateConstraint` variant fails the BUILD until it is
  classified). ⚑ THE SLOT IS EXACTLY THE CRYPTO/WITNESS SURFACE: every remaining
  arm needs a hash recomputation, a proof verifier, a DSL runtime, or peer-cell
  state. Nothing "pure but unported" is left in it.

## What is Lean-evaluated at HEAD

58 of the 69 `StateConstraint` variants. Beyond the original pure/context set
this module now decides:

* the two EXECUTOR RATE COUNTERS (`RateLimit`, `RateLimitBySum`) over the
  marshalled `sender_epoch_count`;
* the three AGGREGATE arms (`FieldsCountEquals`, `CollectionAggregate`,
  `FieldsCollectionAggregate`) over a RESOLVED cell run — Rust resolves the KEYS,
  the truncation / element predicate / aggregate / council-distinctness live here;
* the two EXECUTOR-ONLY SENTINELS (`CapabilityUniqueness`, `BoundDelta`), whose
  fail-closed refusal is now Lean-authored rather than a Rust `Err(..)` a later
  edit could soften back into `Ok(())`.

## Import discipline

Imports NOTHING beyond core `Init` — no Mathlib. The `@[export]`ed object must
be self-contained so its leanc-emitted `.c` splices into `libdregg_lean.a` without
dragging a Mathlib-tactic initializer closure into the FFI link (same discipline
as `Dregg2.Grain.R3Verify` / the crypto FFI cores; see `lean_init.c`).
-/

namespace Dregg2.Exec.DeployedConstraint

/-- The number of fixed register slots (`STATE_SLOTS` in `cell/src/state.rs`). -/
def stateSlots : Nat := 16

/-- `2^64`, the modulus of the low field lane (`field_to_u64`). -/
def two64 : Nat := 18446744073709551616

/-- `2^30` — `FIELD_DELTA_RESULT_BITS`, the RESULT range that closes the
`FieldDelta` / `FieldDeltaInRange` underflow-wrap mint (`eval.rs:2938`). -/
def two30 : Nat := 1073741824

/-- A field value: the unsigned 256-bit big-endian integer a `[u8;32]` denotes. -/
abbrev DField := Nat

/-- `cell/src/program/eval.rs::field_to_u64` — the LOW 64-bit lane (bytes `[24..32]`
big-endian) of a field element. On the `Nat` model this is `n % 2^64`. -/
@[inline] def low64 (n : DField) : Nat := n % two64

/-- `eval.rs::field_add` — WRAPPING addition on the low 64-bit lane, with `a`'s
HIGH 24 bytes preserved verbatim (`out = *a; out[24..32] = wrapping_add`). On the
`Nat` model: keep `a`'s high limbs, replace the low lane. -/
@[inline] def fieldAdd (a b : DField) : DField :=
  (a / two64) * two64 + ((low64 a + low64 b) % two64)

/-- `eval.rs::field_result_in_range` — every byte above the low u64 lane is zero
AND the lane is `< 2^30`. On the `Nat` model that is exactly `n < 2^30`. -/
@[inline] def resultInRange (n : DField) : Bool := n < two30

/-- `u64::saturating_add`. -/
@[inline] def satAdd64 (a b : Nat) : Nat := if a + b ≥ two64 then two64 - 1 else a + b

/-- The pure heap-atom subset (`cell/src/program/types.rs::HeapAtom`,
`eval.rs::evaluate_heap_atom`). `equals`/`gte`/`lte` compare the FULL 256-bit
field; `memberOf`/`inRange`/`deltaBounded`/`deltaEquals` read the `field_to_u64`
low lane, exactly as the deployed evaluator does. -/
inductive DHeapAtom where
  | equals (v : DField)
  | gte (v : DField)
  | lte (v : DField)
  | memberOf (set : List Nat)
  | inRange (lo hi : Nat)
  | immutable
  | writeOnce
  | monotonic
  | strictMonotonic
  | deltaBounded (d : Nat)
  | deltaEquals (d : Int)
  deriving Repr, DecidableEq

/-! ## The COLLECTION fragment (`cell/src/program/collection.rs`)

The three aggregate arms (`FieldsCountEquals`, `CollectionAggregate`,
`FieldsCollectionAggregate`) read a RUN of heap / field-map cells. The Rust
marshaller resolves the KEYS (exactly the job it already does for `HeapField`) and
ships the resolved `Option FieldElement` run as `DInput.cells`; every bit of
SEMANTICS — the `readIndexed` anchor truncation, the per-element predicate, the
aggregate, the council's distinctness — lives HERE. -/

/-- `collection.rs::ElemPredAtom` — a per-element decision atom reading ONE
element-relative offset. Fail-closed: an absent cell is `false`. -/
inductive DElemPred where
  | fieldEquals (offset : Nat) (value : DField)
  | fieldGte (offset : Nat) (value : DField)
  | fieldLte (offset : Nat) (value : DField)
  | fieldInSet (offset : Nat) (set : List Nat)
  deriving Repr, DecidableEq

/-- `ElemPredAtom::anchor_offset`. -/
def DElemPred.anchorOffset : DElemPred → Nat
  | .fieldEquals o _ => o
  | .fieldGte o _ => o
  | .fieldLte o _ => o
  | .fieldInSet o _ => o

/-- Read one element-relative offset. An element is a `stride`-long run of cells;
an offset PAST the stride reads `none` (the Rust `elem.get(off).copied().flatten()`). -/
@[inline] def elemRead (elem : List (Option DField)) (off : Nat) : Option DField :=
  elem.getD off none

/-- `ElemPredAtom::eval` — EXACT. `fieldGte`/`fieldLte` are the UNSIGNED 256-bit
`field_gte`/`field_lte`; `fieldInSet` reads the `field_to_u64` low lane. -/
def DElemPred.eval (p : DElemPred) (elem : List (Option DField)) : Bool :=
  match p with
  | .fieldEquals off v =>
      match elemRead elem off with | some x => decide (x = v) | none => false
  | .fieldGte off v =>
      match elemRead elem off with | some x => decide (v ≤ x) | none => false
  | .fieldLte off v =>
      match elemRead elem off with | some x => decide (x ≤ v) | none => false
  | .fieldInSet off s =>
      match elemRead elem off with | some x => s.contains (low64 x) | none => false

/-- `collection.rs::CollPred` — the aggregate over the read-out collection. -/
inductive DCollPred where
  | countSatGe (m : Nat) (p : DElemPred)
  | sumOfLe (offset : Nat) (bound : Int)
  | sumOfGe (offset : Nat) (bound : Int)
  | allMembers (p : DElemPred)
  | existsMember (p : DElemPred)
  | mOfNDistinct (m : Nat) (keyOffset : Nat) (approved : DElemPred)
  deriving Repr, DecidableEq

/-- `CollPred::anchor_offset` — the offset whose PRESENCE anchors the read (drives
the truncation). For the council it is the KEY offset: an element with no identity
does not count. -/
def DCollPred.anchorOffset : DCollPred → Nat
  | .countSatGe _ p => p.anchorOffset
  | .allMembers p => p.anchorOffset
  | .existsMember p => p.anchorOffset
  | .sumOfLe o _ => o
  | .sumOfGe o _ => o
  | .mOfNDistinct _ k _ => k

/-- `collection.rs::coll_sum` — Σ of the element field at `off` over the low lanes,
an absent read contributing 0 (TOTAL, the Lean `sumOfField` `getD 0` discipline).
Rust folds in `i128`; the marshaller's cell-count envelope keeps the fold inside it. -/
def collSum (coll : List (List (Option DField))) (off : Nat) : Int :=
  coll.foldl (fun acc e =>
    acc + (match elemRead e off with | some x => (low64 x : Int) | none => 0)) 0

/-- `eraseDups` as a structurally-recursive accumulator fold — the `BTreeSet`
distinctness of `mOfNDistinct` (the duplicate-padded forge collapses to ONE key). -/
def dedupGo : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc => dedupGo xs (if acc.contains x then acc else x :: acc)

/-- The number of DISTINCT keys in `ks`. -/
@[inline] def distinctCount (ks : List Nat) : Nat := (dedupGo ks []).length

/-- `CollPred::eval` — EXACT, including the council lift `mOfNDistinct`
(filter to approving elements · read each key identity, DROPPING the keyless ·
dedup · compare to `m`). -/
def DCollPred.eval (q : DCollPred) (coll : List (List (Option DField))) : Bool :=
  match q with
  | .countSatGe m p => decide ((coll.filter (fun e => p.eval e)).length ≥ m)
  | .sumOfLe off b => decide (collSum coll off ≤ b)
  | .sumOfGe off b => decide (collSum coll off ≥ b)
  | .allMembers p => coll.all (fun e => p.eval e)
  | .existsMember p => coll.any (fun e => p.eval e)
  | .mOfNDistinct m k appr =>
      let keys := (coll.filter (fun e => appr.eval e)).filterMap
        (fun e => (elemRead e k).map low64)
      decide (distinctCount keys ≥ m)

/-- Element `i` of the resolved cell run: the `stride`-long slice starting at
`i * stride` (row-major, exactly the key layout `read_collection` walks). -/
def elemAt (cells : List (Option DField)) (stride i : Nat) : List (Option DField) :=
  (List.range stride).map (fun f => cells.getD (i * stride + f) none)

/-- `read_collection`'s truncation loop: the contiguous prefix of elements whose
ANCHOR cell is present, bounded by `fuel`.

⚑ FAITHFUL ASYMMETRY: the deployed anchor probe reads heap key
`i*stride + anchor` — NOT the element's `stride`-bounded slice — so an
`anchor ≥ stride` probes the NEXT element's territory while the PREDICATE read of
that same offset is absent (past the slice). Reproduced exactly. -/
def collTake (cells : List (Option DField)) (stride anchor : Nat) :
    Nat → Nat → List (List (Option DField))
  | 0, _ => []
  | n + 1, i =>
      match cells.getD (i * stride + anchor) none with
      | none => []
      | some _ => elemAt cells stride i :: collTake cells stride anchor n (i + 1)

/-- `read_collection` / `read_collection_fields` — `none` = NO COLLECTION
(`stride = 0`, an ill-formed shape; or element 0's anchor absent), which the
deployed evaluator turns into a fail-closed REFUSAL upstream. -/
def readCollection (cells : List (Option DField)) (stride fuel anchor : Nat) :
    Option (List (List (Option DField))) :=
  if stride = 0 then none
  else
    let coll := collTake cells stride anchor fuel 0
    if coll.isEmpty then none else some coll

/-- The BASE (non-combinator) `StateConstraint` subset this evaluator decides
(`cell/src/program/types.rs::StateConstraint`, `eval.rs::evaluate_constraint_full`).

Classes (a) PURE and (b) CONTEXT both live here; the context arms read `DInput.ctx`
(the explicitly-marshalled height/sender/epoch slice) and produce `missingContext`
exactly where the deployed evaluator raises `MissingContextField`. -/
inductive DConstraint where
  -- ── (a) PURE: registers ────────────────────────────────────────────────────
  | fieldEquals (index : Nat) (value : DField)
  | fieldGte (index : Nat) (value : DField)
  | fieldLte (index : Nat) (value : DField)
  | fieldLteField (left right : Nat)
  | fieldLteOther (index other : Nat) (delta : Int)
  | sumEquals (indices : List Nat) (value : DField)
  | immutable (index : Nat)
  | writeOnce (index : Nat)
  | monotonic (index : Nat)
  | strictMonotonic (index : Nat)
  | boundedBy (index witness : Nat)
  | fieldDelta (index : Nat) (delta : DField)
  | fieldDeltaInRange (index : Nat) (minDelta maxDelta : DField)
  | sumEqualsAcross (inputs outputs : List Nat)
  | monotonicSequence (index : Nat)
  | allowedTransitions (index : Nat) (allowed : List (DField × DField))
  | symEq (index : Nat) (sym : Nat)
  | symMemberOf (index : Nat) (set : List Nat)
  | digEq (index : Nat) (digest : DField)
  | digFieldEq (left right : Nat)
  | memberOf (index : Nat) (set : List Nat)
  | prefixOf (segs : List Nat) (pfx : List Nat)
  | inRangeTwoSided (index : Nat) (lo hi : Nat)
  | deltaBounded (index : Nat) (d : Nat)
  | affineLe (terms : List (Int × Nat)) (c : Int)
  | affineEq (terms : List (Int × Nat)) (c : Int)
  | affineDeltaLe (terms : List (Int × Nat)) (c : Int)
  | reachable (index : Nat) (toLabel : Nat) (edges : List (Nat × Nat))
  | settleEscrow (legA legB : Nat)
  | vaultDeposit (assets shares : Nat)
  | rateBound (index : Nat) (k : Nat)
  | untilEvent (index : Nat)
  | sinceEvent (index : Nat)
  -- ── (a) PURE: balance (the SIGNED `i64` sealed balance) ────────────────────
  | balanceGte (min : Nat)
  | balanceLte (max : Nat)
  | balanceDeltaLte (max : Int)
  | balanceDeltaGte (min : Int)
  -- ── (a) PURE: heap ─────────────────────────────────────────────────────────
  | heapField (atom : DHeapAtom)
  | heapFieldLteOther (delta : Int)
  -- ── (b) CONTEXT: height / sender / delegation epoch ────────────────────────
  | fieldGteHeight (index : Nat) (offset : Int)
  | fieldLteHeight (index : Nat) (offset : Int)
  | temporalGate (notBefore notAfter : Option Nat)
  | cooledSince (stagedAt period : Nat)
  | challengeWindow (index stagedAt period : Nat)
  | dischargeObligation (cursor due amount : Nat) (period amountBy : Nat)
  | senderIs (pk : DField)
  | senderInSlot (index : Nat)
  | senderMemberOf (members : List DField)
  | delegationEpochEquals (index : Nat)
  -- ── (b) CONTEXT: the executor's per-(cell, sender, epoch) counter ───────────
  | rateLimit (maxPerEpoch : Nat)
  | rateLimitBySum (index : Nat) (maxSumPerEpoch : Nat)
  -- ── (a) PURE: the resolved heap / field-map CELL RUN ───────────────────────
  | fieldsCountEquals (count : Nat) (value : DField) (countIndex : Nat)
  | collAggregate (stride fuel : Nat) (pred : DCollPred)
  -- ── (a) PURE: the executor-only SENTINELS (fail-closed by construction) ────
  | capabilityUniqueness (slot : Nat)
  | boundDelta
  deriving Repr, DecidableEq

/-- The TOP-LEVEL constraint: a base arm, or one of the two boolean combinators
over `SimpleStateConstraint` branches (`eval.rs`'s `AnyOf` / `AllOf`).

A branch is `(negated, atom)` — the PARITY of the peeled `Not` chain and the
`Not`-free atom underneath, exactly the shape
`eval.rs::evaluate_simple_constraint` reduces to before calling `lift_simple`.
Flat by construction (`SimpleStateConstraint` has no `AnyOf`/`AllOf`), so there
is no nested recursion and no fuel. -/
inductive DTop where
  | base (c : DConstraint)
  | anyOf (branches : List (Bool × DConstraint))
  | allOf (branches : List (Bool × DConstraint))
  deriving Repr

/-- The MARSHALLED CONTEXT slice — the ONLY part of `EvalContext` /
`TransitionMeta` this evaluator sees, each field's presence carried EXPLICITLY.

* `present` — `ctx: Option<&EvalContext>` was `Some`.
* `height` — `ctx.block_height` (meaningless when `present = false`).
* `senderPresent` / `sender` — `ctx.sender : Option<[u8;32]>`.
* `epochPresent` / `epoch` — `meta.delegation_epoch : Option<u64>`.

Everything else in `EvalContext` (`timestamp`, `current_epoch`,
`sender_epoch_count`, `revealed_preimage`) is DELIBERATELY NOT marshalled: the
arms that read it (`RateLimit`, `RateLimitBySum`, `PreimageGate`) are in the
trusted-Rust slot, and the marshaller REFUSES to encode them (falls through to
Rust) rather than shipping a half-context. -/
structure DCtx where
  present : Bool
  height : Nat
  senderPresent : Bool
  sender : DField
  epochPresent : Bool
  epoch : Nat
  /-- `ctx.sender_epoch_count` — the executor's AUTHORITATIVE per-(cell, sender,
  epoch) mutation counter (and, for `RateLimitBySum`, the per-(cell, slot, window)
  running sum). Meaningless when `present = false`; the arms that read it either
  raise `MissingContextField "sender_epoch_count"` (`RateLimit`) or read 0
  (`RateLimitBySum`), exactly as the deployed evaluator does. It is NOT
  submitter-controlled — the executor wires it in
  `execute_tree::state_constraint_context_count`. -/
  epochCount : Nat
  deriving Repr

/-- The `(old, new)` state slice one constraint eval sees over the deployed
substrate: 16 registers each side (always present — registers never "absent"),
the new nonce, an old-state presence flag (the executor's `old_state: Option`),
the SIGNED sealed balance on each side, the marshalled context slice, and the
heap `get_field_ext` `Option`s (the Rust marshaller resolves the keys; the ATOM
SEMANTICS live here). `heapOther` is the SECOND post-state key read by
`HeapFieldLteOther`. -/
structure DInput where
  oldPresent : Bool
  newNonce : Nat
  oldRegs : List DField
  newRegs : List DField
  heapOld : Option DField
  heapNew : Option DField
  heapOther : Option DField
  oldBalance : Int
  newBalance : Int
  ctx : DCtx
  /-- The RESOLVED heap / field-map cell run the aggregate arms read (row-major;
  `none` = the key is absent post-state). Rust resolves the KEYS; the truncation
  and the aggregate semantics live in this module. Empty for every other arm. -/
  cells : List (Option DField)
  deriving Repr

/-- The admission verdict, mirroring `Result<(), ProgramError>`:
`ok` = admit; `violated` = `ConstraintViolated` (incl. the SumEquals u64-overflow
which the deployed evaluator also raises as `ConstraintViolated`);
`needsOld idx` = `TransitionCheckRequiresOldState { index }`;
`badIndex idx` = `InvalidFieldIndex { index }` (the `check_index` failure);
`missingContext code` = `MissingContextField { field }` with
`0 = "block_height"`, `1 = "sender"`, `2 = "delegation_epoch"`,
`3 = "sender_epoch_count"`;
`capUniqRequiresExecutor` = `CapabilityUniquenessRequiresExecutor { .. }` and
`boundDeltaNotWired` = `BoundDeltaNotWired { .. }` — the two EXECUTOR-ONLY
sentinels. Their payloads (`cap_set_root_slot`, `peer_cell`) are re-attached by the
Rust decoder FROM THE CONSTRAINT, so no `CellId` needs a wire encoding. -/
inductive DAdmit where
  | ok
  | violated
  | needsOld (index : Nat)
  | badIndex (index : Nat)
  | missingContext (code : Nat)
  | capUniqRequiresExecutor
  | boundDeltaNotWired
  deriving Repr, DecidableEq

/-- Context-field codes (the `&'static str` the Rust decoder re-attaches). -/
def ctxHeight : Nat := 0
def ctxSender : Nat := 1
def ctxEpoch : Nat := 2
def ctxEpochCount : Nat := 3

/-- Read register `idx`, mirroring `eval.rs::check_index` (`idx >= STATE_SLOTS`
⇒ `InvalidFieldIndex`). The 16-length invariant on `regs` holds by the wire
(the parser fails closed otherwise), so `getD` never hits its default. -/
@[inline] def getReg (regs : List DField) (idx : Nat) : Option DField :=
  if idx ≥ stateSlots then none else some (regs.getD idx 0)

/-- `eval.rs::evaluate_heap_atom` — the deployed heap-atom teeth, EXACT.
`heapOld`/`heapNew` are `get_field_ext key` on each side (`None` = absent).

⚑ RECONCILED DIVERGENCE (a): `immutable` is the SOUND deployed semantics —
`none ⇒ ok` (the first write is free; heap keys start absent, so this is the write
that ESTABLISHES the sentinel) and `some a ⇒ new == some a` (frozen thereafter;
a flip OR an erasure refuses). The tug copy's `decide (new = old)` was the bug
(it refuses the establishing write, making the atom unusable). -/
def heapAdmits (atom : DHeapAtom) (oldV newV : Option DField) : DAdmit :=
  match atom with
  | .equals v =>
      match newV with
      | some x => if x = v then .ok else .violated
      | none => .violated
  | .gte v =>
      match newV with
      | some x => if v ≤ x then .ok else .violated   -- field_gte(x,v) = x >= v = v <= x (UNSIGNED)
      | none => .violated
  | .lte v =>
      match newV with
      | some x => if x ≤ v then .ok else .violated
      | none => .violated
  | .memberOf set =>
      match newV with
      | some x => if set.contains (low64 x) then .ok else .violated
      | none => .violated
  | .inRange lo hi =>
      match newV with
      | some x => let v := low64 x; if lo ≤ v ∧ v ≤ hi then .ok else .violated
      | none => .violated
  | .immutable =>
      match oldV with
      | none => .ok
      | some a => if newV = some a then .ok else .violated
  | .writeOnce =>
      match oldV with
      | none => .ok
      | some a => if a = 0 then .ok else (if newV = some a then .ok else .violated)
  | .monotonic =>
      match oldV, newV with
      | some a, some b => if a ≤ b then .ok else .violated
      | _, _ => .violated
  | .strictMonotonic =>
      match oldV, newV with
      | some a, some b => if a < b then .ok else .violated
      | _, _ => .violated
  | .deltaBounded d =>
      match oldV, newV with
      | some a, some b =>
          let delta : Int := (low64 b : Int) - (low64 a : Int)
          if delta.natAbs ≤ d then .ok else .violated
      | _, _ => .violated
  | .deltaEquals d =>
      match oldV, newV with
      | some a, some b =>
          let delta : Int := (low64 b : Int) - (low64 a : Int)
          if delta = d then .ok else .violated
      | _, _ => .violated

/-- SumEquals with faithful u64-overflow: accumulate the low-64 lanes; a partial
sum reaching `2^64` is the `checked_add` overflow the deployed evaluator raises as
`ConstraintViolated`; an out-of-range index is `InvalidFieldIndex` at the first
offending slot (iteration order, matching the Rust loop). -/
def sumEqualsAdmit (idxs : List Nat) (v : DField) (regs : List DField) : DAdmit :=
  let rec go (l : List Nat) (acc : Nat) : DAdmit :=
    match l with
    | [] => if acc = low64 v then .ok else .violated
    | idx :: rest =>
        if idx ≥ stateSlots then .badIndex idx
        else
          let s := acc + low64 (regs.getD idx 0)
          if s ≥ two64 then .violated else go rest s
  go idxs 0

/-- `SumEqualsAcross`'s INPUT loop: one pass accumulating BOTH the new-side and
old-side low lanes, first-bad-index and first-`checked_add`-overflow faithful. -/
def sumAcrossIn : List Nat → List DField → List DField → Nat → Nat →
    Except DAdmit (Nat × Nat)
  | [], _, _, an, ao => .ok (an, ao)
  | idx :: rest, newRegs, oldRegs, an, ao =>
      if idx ≥ stateSlots then .error (.badIndex idx)
      else
        let an' := an + low64 (newRegs.getD idx 0)
        if an' ≥ two64 then .error .violated
        else
          let ao' := ao + low64 (oldRegs.getD idx 0)
          if ao' ≥ two64 then .error .violated
          else sumAcrossIn rest newRegs oldRegs an' ao'

/-- `SumEqualsAcross`'s OUTPUT loop (new-side only). -/
def sumAcrossOut : List Nat → List DField → Nat → Except DAdmit Nat
  | [], _, acc => .ok acc
  | idx :: rest, newRegs, acc =>
      if idx ≥ stateSlots then .error (.badIndex idx)
      else
        let acc' := acc + low64 (newRegs.getD idx 0)
        if acc' ≥ two64 then .error .violated else sumAcrossOut rest newRegs acc'

/-- `eval.rs::affine_sum` — `Σ kᵢ·new[fᵢ]` over the low lanes, first bad index
wins. Exact over `Int`, and THIS is the referent: the Rust side accumulates
exactly too (`AffineAcc`, a signed 256-bit value), so the two agree on ALL
inputs.

⚠ This docstring used to rest the agreement on the MARSHALLER instead — "the
Rust side computes in `i128` and the marshaller declines any term list that
could leave the `i128` envelope, so within the encoded domain the two agree
exactly". True as far as it went, and load-bearing on nothing: the targets that
WRAPPED are wasm32 and the SP1 zkVM guest, which install no oracle and so never
reach a marshaller. On those, `eval.rs` IS the whole evaluator, and its `i128`
accumulator read a true sum of `2^128` as `0` and ADMITTED an `affineLe` with
`c = 0`. Measured 2026-07-28. The agreement is now a property of the Rust
arithmetic, not of an envelope in front of it. -/
def affineSum : List (Int × Nat) → List DField → Except DAdmit Int
  | [], _ => .ok 0
  | (k, idx) :: rest, regs =>
      if idx ≥ stateSlots then .error (.badIndex idx)
      else
        match affineSum rest regs with
        | .error e => .error e
        | .ok s => .ok (k * (low64 (regs.getD idx 0) : Int) + s)

/-- `eval.rs::affine_delta_sum` — `Σ kᵢ·(new[fᵢ] − old[fᵢ])` over the low lanes. -/
def affineDeltaSum : List (Int × Nat) → List DField → List DField →
    Except DAdmit Int
  | [], _, _ => .ok 0
  | (k, idx) :: rest, oldRegs, newRegs =>
      if idx ≥ stateSlots then .error (.badIndex idx)
      else
        match affineDeltaSum rest oldRegs newRegs with
        | .error e => .error e
        | .ok s =>
            let d : Int := (low64 (newRegs.getD idx 0) : Int) - (low64 (oldRegs.getD idx 0) : Int)
            .ok (k * d + s)

/-- `eval.rs::reachable_closure` — fuel-bounded reflexive-transitive reachability
over `(dominator, dominated)` edges, fuel checked BEFORE the reflexive hit
(exactly the Rust `go`). -/
def reachFuel (edges : List (Nat × Nat)) (a b : Nat) : Nat → Bool
  | 0 => false
  | f + 1 =>
      if a == b then true
      else edges.any (fun e => e.1 == a && reachFuel edges e.2 b f)

/-- `reachable_closure` with the deployed fuel (`edges.len() + 1`). -/
@[inline] def reachableClosure (edges : List (Nat × Nat)) (a b : Nat) : Bool :=
  reachFuel edges a b (edges.length + 1)

/-- `PrefixOf`'s loop: walk `prefix` against the slots named by `segs`,
`check_index` per step (first bad index wins). -/
def prefixGo : List Nat → List Nat → List DField → DAdmit
  | [], _, _ => .ok
  | _ :: _, [], _ => .violated   -- unreachable: the length guard fires first
  | want :: wrest, seg :: srest, regs =>
      if seg ≥ stateSlots then .badIndex seg
      else if low64 (regs.getD seg 0) ≠ want then .violated
      else prefixGo wrest srest regs

/-- `FieldsCountEquals`'s census loop over the RESOLVED key run (`eval.rs:1990`):
an ABSENT key is `none` — the fail-closed refusal, never a "0 matches" admit.
`checked_add` cannot overflow inside the marshaller's list envelope. -/
def fieldsCountGo : List (Option DField) → DField → Nat → Option Nat
  | [], _, acc => some acc
  | c :: rest, v, acc =>
      match c with
      | none => none
      | some x => fieldsCountGo rest v (if x = v then acc + 1 else acc)

/-- The GENESIS ESCAPE shared by the register transition arms: with `old` absent
and `newNonce = 0` the field may initialize (`ok`); with `old` absent and
`newNonce ≠ 0` the executor raises `TransitionCheckRequiresOldState`. -/
@[inline] def genesisEscape (i : DInput) (idx : Nat) : DAdmit :=
  if i.newNonce = 0 then .ok else .needsOld idx

/-- **THE deployed evaluator** — `eval.rs::evaluate_constraint_full`, EXACT, over
the deployed substrate.

⚑ RECONCILED DIVERGENCE (b): every full-field compare (`fieldGte`, `fieldLte`,
`fieldLteField`, `monotonic`, `strictMonotonic`, the heap atoms) is UNSIGNED `Nat`
compare — the deployed `[u8;32]` `a >= b` — never the signed-`Int` `intLe` of the
old Exec copy. The u64-LANE arms (`fieldLteOther`, the delta/affine/sym family)
read `field_to_u64` and compare over `Int`, exactly as the deployed `i128` path
does. -/
def admits (c : DConstraint) (i : DInput) : DAdmit :=
  match c with
  -- ── (a) registers ──────────────────────────────────────────────────────────
  | .fieldEquals idx v =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some x => if x = v then .ok else .violated
  | .fieldGte idx v =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some x => if v ≤ x then .ok else .violated
  | .fieldLte idx v =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some x => if x ≤ v then .ok else .violated
  | .fieldLteField l r =>
      match getReg i.newRegs l with
      | none => .badIndex l
      | some a =>
          match getReg i.newRegs r with
          | none => .badIndex r
          | some b => if a ≤ b then .ok else .violated
  | .fieldLteOther idx other delta =>
      match getReg i.newRegs idx with
      | none => .badIndex idx
      | some a =>
          match getReg i.newRegs other with
          | none => .badIndex other
          | some b =>
              let lhs : Int := (low64 a : Int)
              let rhs : Int := (low64 b : Int) + delta
              if lhs > rhs then .violated else .ok
  | .sumEquals idxs v => sumEqualsAdmit idxs v i.newRegs
  | .immutable idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        (if i.newRegs.getD idx 0 = i.oldRegs.getD idx 0 then .ok else .violated)
      else genesisEscape i idx
  | .writeOnce idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        let o := i.oldRegs.getD idx 0
        let n := i.newRegs.getD idx 0
        (if o = 0 ∨ n = o then .ok else .violated)
      else genesisEscape i idx
  | .monotonic idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        (if i.oldRegs.getD idx 0 ≤ i.newRegs.getD idx 0 then .ok else .violated)
      else genesisEscape i idx
  | .strictMonotonic idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        (if i.oldRegs.getD idx 0 < i.newRegs.getD idx 0 then .ok else .violated)
      else genesisEscape i idx
  | .boundedBy idx widx =>
      if idx ≥ stateSlots then .badIndex idx
      else if widx ≥ stateSlots then .badIndex widx
      else
        let n := i.newRegs.getD idx 0
        let changed := if i.oldPresent then n ≠ i.oldRegs.getD idx 0 else n ≠ 0
        if changed ∧ i.newRegs.getD widx 0 = 0 then .violated else .ok
  | .fieldDelta idx delta =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        let expected := fieldAdd (i.oldRegs.getD idx 0) delta
        let n := i.newRegs.getD idx 0
        if n ≠ expected then .violated
        else if ¬ resultInRange n then .violated
        else .ok
      else genesisEscape i idx
  | .fieldDeltaInRange idx mn mx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        let o := i.oldRegs.getD idx 0
        let lower := fieldAdd o mn
        let upper := fieldAdd o mx
        let n := i.newRegs.getD idx 0
        if ¬ (lower ≤ n ∧ n ≤ upper) then .violated
        else if ¬ resultInRange n then .violated
        else .ok
      else genesisEscape i idx
  | .sumEqualsAcross ins outs =>
      -- `eval.rs:612` — an absent old state short-circuits BEFORE any index
      -- check: nonce 0 ⇒ `Ok(())`, else `TransitionCheckRequiresOldState { 0 }`.
      if ¬ i.oldPresent then (if i.newNonce = 0 then .ok else .needsOld 0)
      else
        match sumAcrossIn ins i.newRegs i.oldRegs 0 0 with
        | .error e => e
        | .ok (newIn, oldIn) =>
            match sumAcrossOut outs i.newRegs 0 with
            | .error e => e
            | .ok newOut =>
                let rhs := oldIn + newOut
                if rhs ≥ two64 then .violated
                else if newIn ≠ rhs then .violated
                else .ok
  | .monotonicSequence idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        let o := low64 (i.oldRegs.getD idx 0)
        let n := low64 (i.newRegs.getD idx 0)
        if n ≠ (o + 1) % two64 then .violated else .ok
      else genesisEscape i idx
  | .allowedTransitions idx allowed =>
      if idx ≥ stateSlots then .badIndex idx
      else
        let n := i.newRegs.getD idx 0
        let o := if i.oldPresent then i.oldRegs.getD idx 0 else 0
        if allowed.any (fun p => p.1 == o && p.2 == n) then .ok else .violated
  | .symEq idx sym =>
      if idx ≥ stateSlots then .badIndex idx
      else if low64 (i.newRegs.getD idx 0) ≠ sym then .violated else .ok
  | .symMemberOf idx set =>
      if idx ≥ stateSlots then .badIndex idx
      else if set.contains (low64 (i.newRegs.getD idx 0)) then .ok else .violated
  | .digEq idx digest =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.newRegs.getD idx 0 ≠ digest then .violated else .ok
  | .digFieldEq l r =>
      if l ≥ stateSlots then .badIndex l
      else if r ≥ stateSlots then .badIndex r
      else if i.newRegs.getD l 0 ≠ i.newRegs.getD r 0 then .violated else .ok
  | .memberOf idx set =>
      if idx ≥ stateSlots then .badIndex idx
      else if set.contains (low64 (i.newRegs.getD idx 0)) then .ok else .violated
  | .prefixOf segs pfx =>
      if pfx.length > segs.length then .violated
      else prefixGo pfx segs i.newRegs
  | .inRangeTwoSided idx lo hi =>
      if idx ≥ stateSlots then .badIndex idx
      else
        let v := low64 (i.newRegs.getD idx 0)
        if lo ≤ v ∧ v ≤ hi then .ok else .violated
  | .deltaBounded idx d =>
      if idx ≥ stateSlots then .badIndex idx
      else if i.oldPresent then
        let delta : Int :=
          (low64 (i.newRegs.getD idx 0) : Int) - (low64 (i.oldRegs.getD idx 0) : Int)
        if delta.natAbs > d then .violated else .ok
      else genesisEscape i idx
  | .affineLe terms c =>
      match affineSum terms i.newRegs with
      | .error e => e
      | .ok s => if s > c then .violated else .ok
  | .affineEq terms c =>
      match affineSum terms i.newRegs with
      | .error e => e
      | .ok s => if s ≠ c then .violated else .ok
  | .affineDeltaLe terms c =>
      if ¬ i.oldPresent then .needsOld 0
      else
        match affineDeltaSum terms i.oldRegs i.newRegs with
        | .error e => e
        | .ok s => if s > c then .violated else .ok
  | .reachable idx toLabel edges =>
      if idx ≥ stateSlots then .badIndex idx
      else if reachableClosure edges (low64 (i.newRegs.getD idx 0)) toLabel then .ok
      else .violated
  | .settleEscrow a b =>
      if a ≥ stateSlots then .badIndex a
      else if b ≥ stateSlots then .badIndex b
      else if ¬ i.oldPresent then .needsOld a
      else
        let ba := low64 (i.oldRegs.getD a 0)
        let bb := low64 (i.oldRegs.getD b 0)
        let aa := low64 (i.newRegs.getD a 0)
        let ab := low64 (i.newRegs.getD b 0)
        if ba ≠ 1 ∨ bb ≠ 1 then .violated
        else if aa ≠ 2 ∨ ab ≠ 2 then .violated
        else .ok
  | .vaultDeposit assets shares =>
      if assets ≥ stateSlots then .badIndex assets
      else if shares ≥ stateSlots then .badIndex shares
      else if ¬ i.oldPresent then .needsOld assets
      else
        let beforeA := low64 (i.oldRegs.getD assets 0)
        let afterA := low64 (i.newRegs.getD assets 0)
        let beforeS := low64 (i.oldRegs.getD shares 0)
        let afterS := low64 (i.newRegs.getD shares 0)
        if afterA ≤ beforeA then .violated
        else
          let d := afterA - beforeA
          if afterS ≤ beforeS then .violated
          else
            let m := afterS - beforeS
            if beforeA * m > beforeS * d then .violated else .ok
  | .rateBound idx k =>
      if idx ≥ stateSlots then .badIndex idx
      else
        let count := if i.oldPresent then low64 (i.oldRegs.getD idx 0) else 0
        if count ≥ k then .violated else .ok
  | .untilEvent idx =>
      if idx ≥ stateSlots then .badIndex idx
      else
        let flag := if i.oldPresent then low64 (i.oldRegs.getD idx 0) else 0
        if flag ≠ 0 then .violated else .ok
  | .sinceEvent idx =>
      if idx ≥ stateSlots then .badIndex idx
      else
        let flag := if i.oldPresent then low64 (i.oldRegs.getD idx 0) else 0
        if flag = 0 then .violated else .ok
  -- ── (a) balance (SIGNED i64) ───────────────────────────────────────────────
  | .balanceGte min =>
      if i.newBalance < 0 then .violated
      else if i.newBalance < (min : Int) then .violated else .ok
  | .balanceLte max =>
      if i.newBalance ≥ 0 ∧ i.newBalance > (max : Int) then .violated else .ok
  | .balanceDeltaLte max =>
      if ¬ i.oldPresent then .needsOld 0
      else if i.newBalance - i.oldBalance > max then .violated else .ok
  | .balanceDeltaGte min =>
      if ¬ i.oldPresent then .needsOld 0
      else if i.newBalance - i.oldBalance < min then .violated else .ok
  -- ── (a) heap ───────────────────────────────────────────────────────────────
  | .heapField atom => heapAdmits atom i.heapOld i.heapNew
  | .heapFieldLteOther delta =>
      match i.heapNew with
      | none => .violated   -- absent `key` post-state fails CLOSED
      | some a =>
          match i.heapOther with
          | none => .violated   -- absent `other_key` post-state fails CLOSED
          | some b =>
              let lhs : Int := (low64 a : Int)
              let rhs : Int := (low64 b : Int) + delta
              if lhs > rhs then .violated else .ok
  -- ── (b) context ────────────────────────────────────────────────────────────
  | .fieldGteHeight idx offset =>
      if idx ≥ stateSlots then .badIndex idx
      else if ¬ i.ctx.present then .missingContext ctxHeight
      else
        let raw : Int := (i.ctx.height : Int) + offset
        let bound : Nat := (if raw < 0 then 0 else raw.toNat) % two64
        if low64 (i.newRegs.getD idx 0) < bound then .violated else .ok
  | .fieldLteHeight idx offset =>
      if idx ≥ stateSlots then .badIndex idx
      else if ¬ i.ctx.present then .missingContext ctxHeight
      else
        let raw : Int := (i.ctx.height : Int) + offset
        let bound : Nat := (if raw < 0 then 0 else raw.toNat) % two64
        if low64 (i.newRegs.getD idx 0) > bound then .violated else .ok
  | .temporalGate nb na =>
      if ¬ i.ctx.present then .missingContext ctxHeight
      else
        let belowNB : Bool := match nb with | some x => i.ctx.height < x | none => false
        let aboveNA : Bool := match na with | some x => i.ctx.height > x | none => false
        if belowNB then .violated else if aboveNA then .violated else .ok
  | .cooledSince stagedAt period =>
      if ¬ i.ctx.present then .missingContext ctxHeight
      else if i.ctx.height < satAdd64 stagedAt period then .violated else .ok
  | .challengeWindow idx stagedAt period =>
      if idx ≥ stateSlots then .badIndex idx
      else if ¬ i.ctx.present then .missingContext ctxHeight
      else if i.ctx.height < satAdd64 stagedAt period then .violated
      else
        let challenge := if i.oldPresent then low64 (i.oldRegs.getD idx 0) else 0
        if challenge ≠ 0 then .violated else .ok
  | .dischargeObligation cursor due amountSlot period amountBy =>
      if cursor ≥ stateSlots then .badIndex cursor
      else if due ≥ stateSlots then .badIndex due
      else if amountSlot ≥ stateSlots then .badIndex amountSlot
      else if ¬ i.oldPresent then .needsOld cursor
      else if ¬ i.ctx.present then .missingContext ctxHeight
      else
        let cursorBefore := low64 (i.oldRegs.getD cursor 0)
        let cursorAfter := low64 (i.newRegs.getD cursor 0)
        let dueBlock := low64 (i.oldRegs.getD due 0)
        let totalBefore := low64 (i.oldRegs.getD amountSlot 0)
        let totalAfter := low64 (i.newRegs.getD amountSlot 0)
        if i.ctx.height < dueBlock then .violated
        else
          let expectedCursor := cursorBefore + period
          if expectedCursor ≥ two64 then .violated
          else if cursorAfter ≠ expectedCursor then .violated
          else
            let expectedTotal := totalBefore + amountBy
            if expectedTotal ≥ two64 then .violated
            else if totalAfter ≠ expectedTotal then .violated
            else .ok
  | .senderIs pk =>
      if ¬ i.ctx.present then .missingContext ctxSender
      else if ¬ i.ctx.senderPresent then .missingContext ctxSender
      else if i.ctx.sender ≠ pk then .violated else .ok
  | .senderInSlot idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if ¬ i.ctx.present then .missingContext ctxSender
      else if ¬ i.ctx.senderPresent then .missingContext ctxSender
      else if i.ctx.sender ≠ i.newRegs.getD idx 0 then .violated else .ok
  | .senderMemberOf members =>
      if ¬ i.ctx.present then .missingContext ctxSender
      else if ¬ i.ctx.senderPresent then .missingContext ctxSender
      else if members.contains i.ctx.sender then .ok else .violated
  | .delegationEpochEquals idx =>
      if idx ≥ stateSlots then .badIndex idx
      else if ¬ i.ctx.epochPresent then .missingContext ctxEpoch
      else if i.newRegs.getD idx 0 ≠ i.ctx.epoch then .violated else .ok
  -- ── (b) context: the executor's rate counters ──────────────────────────────
  -- `eval.rs:817` — an ABSENT context is `MissingContextField "sender_epoch_count"`
  -- (fail-closed: there is NO submitter-controlled path to the count).
  | .rateLimit maxPerEpoch =>
      if ¬ i.ctx.present then .missingContext ctxEpochCount
      else if i.ctx.epochCount ≥ maxPerEpoch then .violated else .ok
  -- `eval.rs:848` — index check, then `saturating_sub` delta on the u64 lane and a
  -- `saturating_add` onto the prior window sum. An absent context reads prior = 0
  -- (NO refusal here; the deployed arm does not raise).
  | .rateLimitBySum idx maxSum =>
      if idx ≥ stateSlots then .badIndex idx
      else
        let newV := low64 (i.newRegs.getD idx 0)
        let oldV := if i.oldPresent then low64 (i.oldRegs.getD idx 0) else 0
        let delta := newV - oldV                      -- `Nat` sub IS saturating_sub
        let prior := if i.ctx.present then i.ctx.epochCount else 0
        if satAdd64 prior delta > maxSum then .violated else .ok
  -- ── (a) the resolved CELL RUN: the aggregate arms ──────────────────────────
  -- `eval.rs:1990` — `check_index` FIRST, then the census over the resolved keys;
  -- an ABSENT key refuses (fail-closed, never a "0 matches" admit).
  | .fieldsCountEquals n value countIdx =>
      if countIdx ≥ stateSlots then .badIndex countIdx
      else if i.cells.length < n then .violated   -- short wire ⇒ fail CLOSED
      else
        match fieldsCountGo (i.cells.take n) value 0 with
        | none => .violated                        -- an ABSENT key refuses
        | some cnt => if i.newRegs.getD countIdx 0 = cnt then .ok else .violated
  -- `eval.rs:2169` / `eval.rs:2212` — ONE semantics for BOTH aggregate arms: they
  -- differ only in WHERE the marshaller resolves the keys (the `(collection_id,
  -- key)` heap vs the `fields_map` tail), which is Rust's key-resolution job, not
  -- a semantic difference. An absent/ill-formed collection REFUSES.
  | .collAggregate stride fuel pred =>
      match readCollection i.cells stride fuel pred.anchorOffset with
      | none => .violated
      | some coll => if pred.eval coll then .ok else .violated
  -- ── (a) the executor-only SENTINELS ────────────────────────────────────────
  -- `eval.rs:791` — bounds-check the declared root slot, then ALWAYS refuse: the
  -- scalar evaluator cannot see the cell's real `CapabilitySet`, so the only sound
  -- answer off the executor path is a refusal. (The historic silent `Ok(())` let a
  -- cell DECLARE NFT-uniqueness while enforcing nothing.)
  | .capabilityUniqueness slot =>
      if slot ≥ stateSlots then .badIndex slot else .capUniqRequiresExecutor
  -- `eval.rs:1370` — cross-cell binding is the executor's γ.2 match loop; the
  -- per-cell evaluator surfaces the sentinel unconditionally.
  | .boundDelta => .boundDeltaNotWired

/-- One `AnyOf`/`AllOf` branch — `eval.rs::evaluate_simple_constraint`'s Heyting
`Not` under the peeled parity:

* inner ADMITS ⇒ `Not` REFUSES (`ConstraintViolated`);
* inner refuses ON ITS OWN TERMS (`ConstraintViolated`) ⇒ `Not` ADMITS;
* inner is UNEVALUABLE (`needsOld` / `badIndex` / `missingContext`) ⇒ the same
  error PROPAGATES. Fail-closed: an unevaluable predicate is unevaluable under
  negation, never vacuously satisfied. -/
def branchAdmits (b : Bool × DConstraint) (i : DInput) : DAdmit :=
  let inner := admits b.2 i
  if ¬ b.1 then inner
  else
    match inner with
    | .ok => .violated
    | .violated => .ok
    | e => e

/-- `AnyOf`'s fold: the FIRST admitting branch wins; otherwise the LAST branch's
error surfaces (`eval.rs:1381`'s `last_err`). -/
def anyOfGo : List (Bool × DConstraint) → DInput → DAdmit → DAdmit
  | [], _, last => last
  | b :: rest, i, _last =>
      match branchAdmits b i with
      | .ok => .ok
      | e => anyOfGo rest i e

/-- `AllOf`'s fold: the FIRST refusing branch's error surfaces. -/
def allOfGo : List (Bool × DConstraint) → DInput → DAdmit
  | [], _ => .ok
  | b :: rest, i =>
      match branchAdmits b i with
      | .ok => allOfGo rest i
      | e => e

/-- The TOP-LEVEL decision. `AnyOf` with no variants REFUSES (`eval.rs:1378`);
`AllOf` with no variants ADMITS (vacuous AND, `eval.rs:1646`). -/
def admitsTop (t : DTop) (i : DInput) : DAdmit :=
  match t with
  | .base c => admits c i
  | .anyOf branches =>
      match branches with
      | [] => .violated
      | _ => anyOfGo branches i .violated
  | .allOf branches => allOfGo branches i

/-! ## The `@[export]` wire codec (Rust → Lean)

Single-line, space-separated token stream; a malformed wire fails CLOSED
(`"1"` = refuse). Token order (17 header tokens, 32 register tokens, the resolved
cell run, then the constraint):

```
oldPresent(0|1)  newNonce(dec)
heapOldPresent(0|1) heapOldVal(hex)
heapNewPresent(0|1) heapNewVal(hex)
heapOtherPresent(0|1) heapOtherVal(hex)
oldBalance(signed dec) newBalance(signed dec)
ctxPresent(0|1) blockHeight(dec)
senderPresent(0|1) sender(hex)
epochPresent(0|1) delegationEpoch(dec)
senderEpochCount(dec)
R0..R15(hex, 16 tokens)              -- oldRegs
N0..N15(hex, 16 tokens)              -- newRegs
CELLS: <n>(dec) then n × (present(0|1) value(hex))   -- the RESOLVED heap run
CONSTRAINT: <TAG> <args…>
```

Field values are hex (the 32-byte `FieldElement`, big-endian); indices / nonce /
counts / u64 args are decimal; deltas / coefficients / balances are signed
decimal. Output: `"0"` ok · `"1"` violated · `"2 <idx>"` needsOld ·
`"3 <idx>"` badIndex · `"4 <code>"` missingContext · `"5"`
capUniqRequiresExecutor · `"6"` boundDeltaNotWired. -/

/-- One hex digit → `Nat`. -/
@[inline] def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if '0'.toNat ≤ n ∧ n ≤ '9'.toNat then some (n - '0'.toNat)
  else if 'a'.toNat ≤ n ∧ n ≤ 'f'.toNat then some (n - 'a'.toNat + 10)
  else if 'A'.toNat ≤ n ∧ n ≤ 'F'.toNat then some (n - 'A'.toNat + 10)
  else none

/-- Parse a big-endian hex string → `Nat` (fails closed on any non-hex char). -/
def parseHex (s : String) : Option Nat :=
  s.toList.foldl (fun acc c =>
    match acc, hexDigit? c with
    | some a, some d => some (a * 16 + d)
    | _, _ => none) (some 0)

/-- Parse an unsigned decimal token. -/
@[inline] def parseNat (s : String) : Option Nat := s.toNat?

/-- Parse a signed decimal token (`-…` allowed). -/
def parseInt (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(Int.ofNat n))
  else s.toNat?.map Int.ofNat

/-- Pop `n` tokens. -/
def popN : Nat → List String → Option (List String × List String)
  | 0, rest => some ([], rest)
  | _+1, [] => none
  | k+1, t :: rest =>
      match popN k rest with
      | some (hd, tl) => some (t :: hd, tl)
      | none => none

/-- Map a token run through a per-token parser, failing closed. -/
def mapAll (f : String → Option α) : List String → Option (List α)
  | [] => some []
  | t :: rest =>
      match f t, mapAll f rest with
      | some x, some tl => some (x :: tl)
      | _, _ => none

/-- Pop `n` tokens and parse each as a decimal `Nat`. -/
def popNats (n : Nat) (toks : List String) : Option (List Nat × List String) := do
  let (hd, tl) ← popN n toks
  let vs ← mapAll parseNat hd
  some (vs, tl)

/-- Pop `n` tokens and parse each as a big-endian hex field. -/
def popHexes (n : Nat) (toks : List String) : Option (List DField × List String) := do
  let (hd, tl) ← popN n toks
  let vs ← mapAll parseHex hd
  some (vs, tl)

/-- Pair up a `2k`-token run as `(signed, decimal)` — the affine `(k, slot)` terms. -/
def pairIntNat : List String → Option (List (Int × Nat))
  | [] => some []
  | a :: b :: rest =>
      match parseInt a, parseNat b, pairIntNat rest with
      | some k, some i, some tl => some ((k, i) :: tl)
      | _, _, _ => none
  | _ => none

/-- Pair up a `2k`-token run as `(decimal, decimal)` — the reachability edges. -/
def pairNatNat : List String → Option (List (Nat × Nat))
  | [] => some []
  | a :: b :: rest =>
      match parseNat a, parseNat b, pairNatNat rest with
      | some x, some y, some tl => some ((x, y) :: tl)
      | _, _, _ => none
  | _ => none

/-- Pair up a `2k`-token run as `(hex, hex)` — the `AllowedTransitions` pairs. -/
def pairHexHex : List String → Option (List (DField × DField))
  | [] => some []
  | a :: b :: rest =>
      match parseHex a, parseHex b, pairHexHex rest with
      | some x, some y, some tl => some ((x, y) :: tl)
      | _, _, _ => none
  | _ => none

/-- Parse an `Option Nat` carried as `present(0|1) value(dec)`. -/
def popOptNat : List String → Option (Option Nat × List String)
  | p :: v :: rest =>
      if p == "1" then (parseNat v).map (fun n => (some n, rest))
      else some (none, rest)
  | _ => none

/-- Parse a heap atom from its tokens, RETURNING the unconsumed tail. -/
def parseHeapAtom : List String → Option (DHeapAtom × List String)
  | "HEQ" :: v :: r => (parseHex v).map (fun x => (.equals x, r))
  | "HGE" :: v :: r => (parseHex v).map (fun x => (.gte x, r))
  | "HLE" :: v :: r => (parseHex v).map (fun x => (.lte x, r))
  | "HMEM" :: n :: r => do
      let k ← parseNat n
      let (vs, tl) ← popNats k r
      some (.memberOf vs, tl)
  | "HRANGE" :: lo :: hi :: r => do
      let a ← parseNat lo
      let b ← parseNat hi
      some (.inRange a b, r)
  | "HIM" :: r => some (.immutable, r)
  | "HWO" :: r => some (.writeOnce, r)
  | "HMON" :: r => some (.monotonic, r)
  | "HSMON" :: r => some (.strictMonotonic, r)
  | "HDB" :: d :: r => (parseNat d).map (fun x => (.deltaBounded x, r))
  | "HDE" :: d :: r => (parseInt d).map (fun x => (.deltaEquals x, r))
  | _ => none

/-- Parse an `ElemPredAtom`, RETURNING the unconsumed tail. -/
def parseElemPred : List String → Option (DElemPred × List String)
  | "EEQ" :: o :: v :: r => do
      let a ← parseNat o; let b ← parseHex v; some (.fieldEquals a b, r)
  | "EGE" :: o :: v :: r => do
      let a ← parseNat o; let b ← parseHex v; some (.fieldGte a b, r)
  | "ELE" :: o :: v :: r => do
      let a ← parseNat o; let b ← parseHex v; some (.fieldLte a b, r)
  | "EIN" :: o :: n :: r => do
      let a ← parseNat o; let k ← parseNat n
      let (vs, tl) ← popNats k r
      some (.fieldInSet a vs, tl)
  | _ => none

/-- Parse a `CollPred`, RETURNING the unconsumed tail. -/
def parseCollPred : List String → Option (DCollPred × List String)
  | "PCNT" :: m :: r => do
      let a ← parseNat m
      let (p, tl) ← parseElemPred r
      some (.countSatGe a p, tl)
  | "PSLE" :: o :: b :: r => do
      let a ← parseNat o; let bb ← parseInt b; some (.sumOfLe a bb, r)
  | "PSGE" :: o :: b :: r => do
      let a ← parseNat o; let bb ← parseInt b; some (.sumOfGe a bb, r)
  | "PALL" :: r => do
      let (p, tl) ← parseElemPred r
      some (.allMembers p, tl)
  | "PEX" :: r => do
      let (p, tl) ← parseElemPred r
      some (.existsMember p, tl)
  | "PMN" :: m :: k :: r => do
      let a ← parseNat m; let kk ← parseNat k
      let (p, tl) ← parseElemPred r
      some (.mOfNDistinct a kk p, tl)
  | _ => none

/-- Parse a BASE constraint, RETURNING the unconsumed tail. Consuming (not
prefix-matching) so branch runs can be parsed back-to-back inside `ANY` / `ALL`. -/
def parseConstraint : List String → Option (DConstraint × List String)
  -- ── (a) registers ──
  | "FE" :: i :: v :: r => do
      let a ← parseNat i; let b ← parseHex v; some (.fieldEquals a b, r)
  | "FG" :: i :: v :: r => do
      let a ← parseNat i; let b ← parseHex v; some (.fieldGte a b, r)
  | "FL" :: i :: v :: r => do
      let a ← parseNat i; let b ← parseHex v; some (.fieldLte a b, r)
  | "FLF" :: l :: rr :: r => do
      let a ← parseNat l; let b ← parseNat rr; some (.fieldLteField a b, r)
  | "FLO" :: i :: o :: d :: r => do
      let a ← parseNat i; let b ← parseNat o; let dd ← parseInt d
      some (.fieldLteOther a b dd, r)
  | "SE" :: v :: n :: r => do
      let vv ← parseHex v; let k ← parseNat n
      let (idxs, tl) ← popNats k r
      some (.sumEquals idxs vv, tl)
  | "IM" :: i :: r => (parseNat i).map (fun a => (.immutable a, r))
  | "WO" :: i :: r => (parseNat i).map (fun a => (.writeOnce a, r))
  | "MO" :: i :: r => (parseNat i).map (fun a => (.monotonic a, r))
  | "SM" :: i :: r => (parseNat i).map (fun a => (.strictMonotonic a, r))
  | "BB" :: i :: w :: r => do
      let a ← parseNat i; let b ← parseNat w; some (.boundedBy a b, r)
  | "FD" :: i :: d :: r => do
      let a ← parseNat i; let b ← parseHex d; some (.fieldDelta a b, r)
  | "FDR" :: i :: mn :: mx :: r => do
      let a ← parseNat i; let b ← parseHex mn; let c ← parseHex mx
      some (.fieldDeltaInRange a b c, r)
  | "SEA" :: n :: r => do
      let k ← parseNat n
      let (ins, tl) ← popNats k r
      match tl with
      | m :: tl2 => do
          let j ← parseNat m
          let (outs, tl3) ← popNats j tl2
          some (.sumEqualsAcross ins outs, tl3)
      | [] => none
  | "MSEQ" :: i :: r => (parseNat i).map (fun a => (.monotonicSequence a, r))
  | "AT" :: i :: n :: r => do
      let a ← parseNat i; let k ← parseNat n
      let (hd, tl) ← popN (2 * k) r
      let ps ← pairHexHex hd
      some (.allowedTransitions a ps, tl)
  | "SYE" :: i :: s :: r => do
      let a ← parseNat i; let b ← parseNat s; some (.symEq a b, r)
  | "SYM" :: i :: n :: r => do
      let a ← parseNat i; let k ← parseNat n
      let (vs, tl) ← popNats k r
      some (.symMemberOf a vs, tl)
  | "DGE" :: i :: d :: r => do
      let a ← parseNat i; let b ← parseHex d; some (.digEq a b, r)
  | "DGF" :: l :: rr :: r => do
      let a ← parseNat l; let b ← parseNat rr; some (.digFieldEq a b, r)
  | "MEM" :: i :: n :: r => do
      let a ← parseNat i; let k ← parseNat n
      let (vs, tl) ← popNats k r
      some (.memberOf a vs, tl)
  | "PRE" :: n :: r => do
      let k ← parseNat n
      let (segs, tl) ← popNats k r
      match tl with
      | m :: tl2 => do
          let j ← parseNat m
          let (pfx, tl3) ← popNats j tl2
          some (.prefixOf segs pfx, tl3)
      | [] => none
  | "IR" :: i :: lo :: hi :: r => do
      let a ← parseNat i; let b ← parseNat lo; let c ← parseNat hi
      some (.inRangeTwoSided a b c, r)
  | "DB" :: i :: d :: r => do
      let a ← parseNat i; let b ← parseNat d; some (.deltaBounded a b, r)
  | "ALE" :: n :: r => do
      let k ← parseNat n
      let (hd, tl) ← popN (2 * k) r
      let ts ← pairIntNat hd
      match tl with
      | c :: tl2 => (parseInt c).map (fun cc => (.affineLe ts cc, tl2))
      | [] => none
  | "AEQ" :: n :: r => do
      let k ← parseNat n
      let (hd, tl) ← popN (2 * k) r
      let ts ← pairIntNat hd
      match tl with
      | c :: tl2 => (parseInt c).map (fun cc => (.affineEq ts cc, tl2))
      | [] => none
  | "ADLE" :: n :: r => do
      let k ← parseNat n
      let (hd, tl) ← popN (2 * k) r
      let ts ← pairIntNat hd
      match tl with
      | c :: tl2 => (parseInt c).map (fun cc => (.affineDeltaLe ts cc, tl2))
      | [] => none
  | "RCH" :: i :: t :: n :: r => do
      let a ← parseNat i; let b ← parseNat t; let k ← parseNat n
      let (hd, tl) ← popN (2 * k) r
      let es ← pairNatNat hd
      some (.reachable a b es, tl)
  | "SETL" :: a :: b :: r => do
      let x ← parseNat a; let y ← parseNat b; some (.settleEscrow x y, r)
  | "VD" :: a :: s :: r => do
      let x ← parseNat a; let y ← parseNat s; some (.vaultDeposit x y, r)
  | "RB" :: i :: k :: r => do
      let a ← parseNat i; let b ← parseNat k; some (.rateBound a b, r)
  | "UE" :: i :: r => (parseNat i).map (fun a => (.untilEvent a, r))
  | "SEV" :: i :: r => (parseNat i).map (fun a => (.sinceEvent a, r))
  -- ── (a) balance ──
  | "BGE" :: m :: r => (parseNat m).map (fun a => (.balanceGte a, r))
  | "BLE" :: m :: r => (parseNat m).map (fun a => (.balanceLte a, r))
  | "BDL" :: m :: r => (parseInt m).map (fun a => (.balanceDeltaLte a, r))
  | "BDG" :: m :: r => (parseInt m).map (fun a => (.balanceDeltaGte a, r))
  -- ── (a) heap ──
  | "HLO" :: d :: r => (parseInt d).map (fun a => (.heapFieldLteOther a, r))
  -- ── (b) context ──
  | "FGH" :: i :: o :: r => do
      let a ← parseNat i; let b ← parseInt o; some (.fieldGteHeight a b, r)
  | "FLH" :: i :: o :: r => do
      let a ← parseNat i; let b ← parseInt o; some (.fieldLteHeight a b, r)
  | "TG" :: r => do
      let (nb, tl) ← popOptNat r
      let (na, tl2) ← popOptNat tl
      some (.temporalGate nb na, tl2)
  | "CS" :: s :: p :: r => do
      let a ← parseNat s; let b ← parseNat p; some (.cooledSince a b, r)
  | "CW" :: i :: s :: p :: r => do
      let a ← parseNat i; let b ← parseNat s; let c ← parseNat p
      some (.challengeWindow a b c, r)
  | "DO" :: c :: d :: a :: p :: m :: r => do
      let cc ← parseNat c; let dd ← parseNat d; let aa ← parseNat a
      let pp ← parseNat p; let mm ← parseNat m
      some (.dischargeObligation cc dd aa pp mm, r)
  | "SIS" :: pk :: r => (parseHex pk).map (fun a => (.senderIs a, r))
  | "SIL" :: i :: r => (parseNat i).map (fun a => (.senderInSlot a, r))
  | "SMO" :: n :: r => do
      let k ← parseNat n
      let (ms, tl) ← popHexes k r
      some (.senderMemberOf ms, tl)
  | "DEE" :: i :: r => (parseNat i).map (fun a => (.delegationEpochEquals a, r))
  -- ── (b) context: the executor rate counters ──
  | "RL" :: m :: r => (parseNat m).map (fun a => (.rateLimit a, r))
  | "RLS" :: i :: m :: r => do
      let a ← parseNat i; let b ← parseNat m; some (.rateLimitBySum a b, r)
  -- ── (a) the resolved CELL RUN ──
  | "FCE" :: n :: v :: c :: r => do
      let k ← parseNat n; let vv ← parseHex v; let ci ← parseNat c
      some (.fieldsCountEquals k vv ci, r)
  | "CAGG" :: s :: f :: r => do
      let st ← parseNat s; let fu ← parseNat f
      let (p, tl) ← parseCollPred r
      some (.collAggregate st fu p, tl)
  -- ── (a) the executor-only sentinels ──
  | "CAPU" :: s :: r => (parseNat s).map (fun a => (.capabilityUniqueness a, r))
  | "BDW" :: r => some (.boundDelta, r)
  -- ── heap atoms (the `HeapField` lift) ──
  | toks => (parseHeapAtom toks).map (fun p => (.heapField p.1, p.2))

/-- Parse `n` `AnyOf`/`AllOf` branches: each is `N0|N1` (the peeled `Not` parity)
followed by a BASE constraint run. -/
def parseBranches : Nat → List String → Option (List (Bool × DConstraint) × List String)
  | 0, toks => some ([], toks)
  | k + 1, p :: rest => do
      let neg := p == "N1"
      if p ≠ "N0" ∧ p ≠ "N1" then none
      else do
        let (c, tl) ← parseConstraint rest
        let (cs, tl2) ← parseBranches k tl
        some ((neg, c) :: cs, tl2)
  | _ + 1, [] => none

/-- Parse the TOP-LEVEL constraint (a combinator, or a base run). -/
def parseTop : List String → Option DTop
  | "ANY" :: n :: r => do
      let k ← parseNat n
      let (bs, _) ← parseBranches k r
      some (.anyOf bs)
  | "ALL" :: n :: r => do
      let k ← parseNat n
      let (bs, _) ← parseBranches k r
      some (.allOf bs)
  | toks => (parseConstraint toks).map (fun p => .base p.1)

/-- Parse a fixed run of `n` hex field tokens into a `List DField`. -/
def parseHexRun (n : Nat) (toks : List String) : Option (List DField × List String) :=
  popHexes n toks

/-- The number of HEADER tokens preceding the two 16-register runs. -/
def headerTokens : Nat := 17

/-- Parse the RESOLVED cell run: `<n>` then `n` × `present(0|1) value(hex)`. -/
def parseCells : Nat → List String → Option (List (Option DField) × List String)
  | 0, toks => some ([], toks)
  | k + 1, p :: v :: rest => do
      let cell ← if p == "1" then (parseHex v).map some
                 else if p == "0" then some none
                 else none
      let (cs, tl) ← parseCells k rest
      some (cell :: cs, tl)
  | _ + 1, _ => none

/-- Parse the 17 header tokens into a `DInput` skeleton (the register runs and the
cell run are filled by [`parse`]). Fails closed on any malformed token. -/
def parseHeader (hdr : List String) : Option DInput :=
  match hdr with
  | [op, nn, hop, hov, hnp, hnv, hxp, hxv, obal, nbal, cxp, hgt, sndp, sndv, epp, epv, cnt] =>
      match parseNat nn, parseInt obal, parseInt nbal, parseNat hgt, parseHex sndv,
            parseNat epv, parseNat cnt with
      | some newNonce, some oldBalance, some newBalance, some height, some sender,
        some epoch, some epochCount =>
          match (if hop == "1" then (parseHex hov).map some else some none),
                (if hnp == "1" then (parseHex hnv).map some else some none),
                (if hxp == "1" then (parseHex hxv).map some else some none) with
          | some heapOld, some heapNew, some heapOther =>
              some { oldPresent := op == "1"
                   , newNonce := newNonce
                   , oldRegs := [], newRegs := [], cells := []
                   , heapOld := heapOld, heapNew := heapNew, heapOther := heapOther
                   , oldBalance := oldBalance, newBalance := newBalance
                   , ctx := { present := cxp == "1", height := height
                            , senderPresent := sndp == "1", sender := sender
                            , epochPresent := epp == "1", epoch := epoch
                            , epochCount := epochCount } }
          | _, _, _ => none
      | _, _, _, _, _, _, _ => none
  | _ => none

/-- Parse the whole wire into `(constraint, input)`. Fails closed. -/
def parse (s : String) : Option (DTop × DInput) :=
  let toks := (s.splitOn " ").filter (· ≠ "")
  match popN headerTokens toks with
  | none => none
  | some (hdr, rest0) =>
      match parseHeader hdr with
      | none => none
      | some skel =>
          match parseHexRun stateSlots rest0 with
          | none => none
          | some (oldRegs, rest1) =>
              match parseHexRun stateSlots rest1 with
              | none => none
              | some (newRegs, rest2) =>
                  if oldRegs.length ≠ stateSlots ∨ newRegs.length ≠ stateSlots then none
                  else
                    match rest2 with
                    | [] => none
                    | ncell :: rest3 =>
                        match parseNat ncell with
                        | none => none
                        | some k =>
                            match parseCells k rest3 with
                            | none => none
                            | some (cells, rest4) =>
                                match parseTop rest4 with
                                | none => none
                                | some c =>
                                    some (c, { skel with oldRegs := oldRegs
                                                       , newRegs := newRegs
                                                       , cells := cells })

/-- Render a verdict to the wire code. -/
def render : DAdmit → String
  | .ok => "0"
  | .violated => "1"
  | .needsOld idx => "2 " ++ toString idx
  | .badIndex idx => "3 " ++ toString idx
  | .missingContext code => "4 " ++ toString code
  | .capUniqRequiresExecutor => "5"
  | .boundDeltaNotWired => "6"

/-- The whole String → String decision. A malformed wire refuses (`"1"`). -/
def admitsWire (s : String) : String :=
  match parse s with
  | none => "1"
  | some (c, i) => render (admitsTop c i)

/-- **`@[export dregg_constraint_admits]`** — the FFI entry Rust calls. Runs the
verified deployed evaluator over the wire slice; the deployed node's admission
decision for the Lean-evaluated subset is COMPUTED HERE. -/
@[export dregg_constraint_admits]
def admitsFFI (s : String) : String := admitsWire s

/-! ## Self-tests — the evaluator agrees with `eval.rs` on the pinned cases,
including the two reconciled divergence boundaries and the newly-widened arms.
`#guard` FAILS the Lean build on regression, so these are teeth, not comments. -/

-- 16 registers all zero except where noted; helper wire builders.
private def zeros16 : String := String.intercalate " " (List.replicate 16 "0")

/-- 17 header tokens: old present, nonce 0, no heap, zero balances, no context,
zero epoch count. -/
private def hdrPlain : String := "1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0"

/-- Build a wire with an all-zero old/new state (nonce 0, no heap, EMPTY cell run)
+ a constraint. -/
private def wire0 (c : String) : String :=
  hdrPlain ++ " " ++ zeros16 ++ " " ++ zeros16 ++ " 0 " ++ c

/-- Build a wire with explicit header, old regs, new regs and constraint (empty
cell run). -/
private def wireH (hdr : String) (oldR newR : String) (c : String) : String :=
  hdr ++ " " ++ oldR ++ " " ++ newR ++ " 0 " ++ c

/-- Build a wire carrying an explicit RESOLVED CELL RUN (`cells` = the already
`<n> (p v)*n` token run). -/
private def wireC (hdr : String) (oldR newR cells : String) (c : String) : String :=
  hdr ++ " " ++ oldR ++ " " ++ newR ++ " " ++ cells ++ " " ++ c

/-- 16 register tokens with `v` (hex) at slot `i`, zeros elsewhere. -/
private def regsAt (i : Nat) (v : String) : String :=
  String.intercalate " " ((List.range 16).map (fun k => if k = i then v else "0"))

/-- 16 register tokens with `a` at slot `i` and `b` at slot `j`. -/
private def regsAt2 (i : Nat) (a : String) (j : Nat) (b : String) : String :=
  String.intercalate " "
    ((List.range 16).map (fun k => if k = i then a else if k = j then b else "0"))

-- ── the original pinned cases ────────────────────────────────────────────────
#guard admitsWire (wire0 "FE 0 0") = "0"
#guard admitsWire (wire0 "FE 0 5") = "1"
#guard admitsWire (wire0 "FG 0 0") = "0"
#guard admitsWire (wire0 "FE 16 0") = "3 16"

-- ⚑ DIVERGENCE (b), UNSIGNED: a huge value in reg[0] must be >= a small threshold.
private def bigHex : String :=
  "8000000000000000000000000000000000000000000000000000000000000000"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 bigHex) "FG 0 1") = "0"

-- ⚑ DIVERGENCE (a), heap immutable: absent old ⇒ first write is FREE (ok).
#guard admitsWire (wireH "0 0 0 0 1 7 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "HIM") = "0"
#guard admitsWire (wireH "1 0 1 7 1 9 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "HIM") = "1"
#guard admitsWire (wireH "1 0 1 7 1 7 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "HIM") = "0"

-- Immutable register with old absent + nonce != 0 ⇒ needsOld; nonce == 0 ⇒ ok.
#guard admitsWire (wireH "0 5 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "IM 0") = "2 0"
#guard admitsWire (wireH "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "IM 0") = "0"

-- SumEquals over regs [0,1] = 0 with value 0 ⇒ ok.
#guard admitsWire (wire0 "SE 0 2 0 1") = "0"

-- ── (a) NEWLY WIDENED: registers ─────────────────────────────────────────────
-- BoundedBy: slot 0 changed 0→5 with witness slot 1 = 0 ⇒ violated; witness set ⇒ ok.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "5") "BB 0 1") = "1"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "5" 1 "1") "BB 0 1") = "0"
-- BoundedBy: unchanged slot needs no witness.
#guard admitsWire (wire0 "BB 0 1") = "0"

-- FieldDelta: old[0] = 10, delta = 5 ⇒ new must be 15 (and in [0,2^30)).
#guard admitsWire (wireH hdrPlain (regsAt 0 "a") (regsAt 0 "f") "FD 0 5") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "a") (regsAt 0 "e") "FD 0 5") = "1"
-- FieldDelta underflow-wrap MINT: old = 10, delta = -50 encoded as 2^64-50 ⇒ the
-- wrapped result 2^64-40 satisfies `new == old + delta` but FAILS the range tooth.
#guard admitsWire (wireH hdrPlain (regsAt 0 "a")
    (regsAt 0 "ffffffffffffffd8") "FD 0 ffffffffffffffce") = "1"

-- FieldDeltaInRange: old = 10, [+1, +5] ⇒ 13 ok, 20 violated.
#guard admitsWire (wireH hdrPlain (regsAt 0 "a") (regsAt 0 "d") "FDR 0 1 5") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "a") (regsAt 0 "14") "FDR 0 1 5") = "1"

-- SumEqualsAcross: in = {0}, out = {1}; new[0]=3, old[0]=1, new[1]=2 ⇒ 3 = 1+2 ok.
#guard admitsWire (wireH hdrPlain (regsAt 0 "1") (regsAt2 0 "3" 1 "2") "SEA 1 0 1 1") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "1") (regsAt2 0 "4" 1 "2") "SEA 1 0 1 1") = "1"
-- SumEqualsAcross with old absent + nonce != 0 ⇒ needsOld 0 (index 0, not the slot).
#guard admitsWire (wireH "0 7 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "SEA 1 0 1 1") = "2 0"

-- MonotonicSequence: old 4 → new 5 ok; 4 → 7 violated.
#guard admitsWire (wireH hdrPlain (regsAt 0 "4") (regsAt 0 "5") "MSEQ 0") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "4") (regsAt 0 "7") "MSEQ 0") = "1"

-- AllowedTransitions: (1 → 2) allowed, (1 → 3) not.
#guard admitsWire (wireH hdrPlain (regsAt 0 "1") (regsAt 0 "2") "AT 0 1 1 2") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "1") (regsAt 0 "3") "AT 0 1 1 2") = "1"

-- SymEq / SymMemberOf / DigEq / DigFieldEq / MemberOf / InRange / DeltaBounded.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "SYE 0 7") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "SYE 0 8") = "1"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "SYM 0 2 5 7") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "SYM 0 2 5 9") = "1"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 bigHex) ("DGE 0 " ++ bigHex)) = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "7" 1 "7") "DGF 0 1") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "7" 1 "8") "DGF 0 1") = "1"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "MEM 0 2 7 9") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "IR 0 5 9") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "IR 0 8 9") = "1"
#guard admitsWire (wireH hdrPlain (regsAt 0 "5") (regsAt 0 "7") "DB 0 3") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "5") (regsAt 0 "7") "DB 0 1") = "1"

-- PrefixOf: path = [slot0, slot1] = [3, 4]; prefix [3] matches, [4] does not.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "3" 1 "4") "PRE 2 0 1 1 3") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "3" 1 "4") "PRE 2 0 1 1 4") = "1"
-- Fail-closed: a prefix longer than the path refuses.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "3") "PRE 1 0 2 3 4") = "1"

-- AffineLe / AffineEq / AffineDeltaLe: 1·new[0] + 1·new[1] with new = (3, 4).
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "3" 1 "4") "ALE 2 1 0 1 1 7") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "3" 1 "4") "ALE 2 1 0 1 1 6") = "1"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt2 0 "3" 1 "4") "AEQ 2 1 0 1 1 7") = "0"
-- Negative coefficient: -1·new[0] = -3 <= 0.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "3") "ALE 1 -1 0 0") = "0"
-- AffineDeltaLe: delta = new − old = 5 − 2 = 3 <= 3 ok, <= 2 violated.
#guard admitsWire (wireH hdrPlain (regsAt 0 "2") (regsAt 0 "5") "ADLE 1 1 0 3") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "2") (regsAt 0 "5") "ADLE 1 1 0 2") = "1"
-- AffineDeltaLe with old absent ⇒ needsOld 0 (NO nonce escape).
#guard admitsWire (wireH "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "ADLE 1 1 0 3") = "2 0"

-- Reachable: edges 1→2, 2→3; label in slot 0 is 1, target 3 ⇒ reachable.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "1") "RCH 0 3 2 1 2 2 3") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "1") "RCH 0 4 2 1 2 2 3") = "1"
-- Reflexive.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "1") "RCH 0 1 0") = "0"

-- SettleEscrow: both legs Deposited(1) before, Consumed(2) after ⇒ ok.
#guard admitsWire (wireH hdrPlain (regsAt2 0 "1" 1 "1") (regsAt2 0 "2" 1 "2") "SETL 0 1") = "0"
-- Half-open settle (leg B left Deposited) ⇒ violated.
#guard admitsWire (wireH hdrPlain (regsAt2 0 "1" 1 "1") (regsAt2 0 "2" 1 "1") "SETL 0 1") = "1"
-- Old absent ⇒ needsOld leg_a (NO nonce escape).
#guard admitsWire (wireH "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "SETL 0 1") = "2 0"

-- VaultDeposit: assets 100→110 (d=10), shares 100→10 minted; no dilution
-- (before_assets·m = 100·10 = 1000 ≤ before_shares·d = 100·10 = 1000) ⇒ ok.
#guard admitsWire (wireH hdrPlain (regsAt2 0 "64" 1 "64") (regsAt2 0 "6e" 1 "6e") "VD 0 1") = "0"
-- THE INFLATION TOOTH: a positive deposit that mints ZERO shares ⇒ violated.
#guard admitsWire (wireH hdrPlain (regsAt2 0 "64" 1 "64") (regsAt2 0 "6e" 1 "64") "VD 0 1") = "1"
-- DILUTION: minting 20 shares for a deposit of 10 (100·20 > 100·10) ⇒ violated.
#guard admitsWire (wireH hdrPlain (regsAt2 0 "64" 1 "64") (regsAt2 0 "6e" 1 "78") "VD 0 1") = "1"

-- RateBound / UntilEvent / SinceEvent read the OLD (committed pre-state) register.
#guard admitsWire (wireH hdrPlain (regsAt 0 "2") zeros16 "RB 0 3") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "3") zeros16 "RB 0 3") = "1"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "1") "UE 0") = "0"
#guard admitsWire (wireH hdrPlain (regsAt 0 "1") zeros16 "UE 0") = "1"
#guard admitsWire (wireH hdrPlain (regsAt 0 "1") zeros16 "SEV 0") = "0"
#guard admitsWire (wireH hdrPlain zeros16 zeros16 "SEV 0") = "1"

-- ── (a) balance (SIGNED) ─────────────────────────────────────────────────────
-- newBalance = 10 (header slot 10) ⇒ BGE 5 ok, BGE 20 violated.
private def hdrBal (oldB newB : String) : String :=
  "1 0 0 0 0 0 0 0 " ++ oldB ++ " " ++ newB ++ " 0 0 0 0 0 0 0"
#guard admitsWire (wireH (hdrBal "0" "10") zeros16 zeros16 "BGE 5") = "0"
#guard admitsWire (wireH (hdrBal "0" "10") zeros16 zeros16 "BGE 20") = "1"
-- A NEGATIVE balance is below every u64 floor and under every u64 ceiling.
#guard admitsWire (wireH (hdrBal "0" "-3") zeros16 zeros16 "BGE 0") = "1"
#guard admitsWire (wireH (hdrBal "0" "-3") zeros16 zeros16 "BLE 0") = "0"
#guard admitsWire (wireH (hdrBal "0" "10") zeros16 zeros16 "BLE 5") = "1"
-- Balance deltas: 4 → 10 is +6.
#guard admitsWire (wireH (hdrBal "4" "10") zeros16 zeros16 "BDL 6") = "0"
#guard admitsWire (wireH (hdrBal "4" "10") zeros16 zeros16 "BDL 5") = "1"
#guard admitsWire (wireH (hdrBal "4" "10") zeros16 zeros16 "BDG 6") = "0"
#guard admitsWire (wireH (hdrBal "4" "10") zeros16 zeros16 "BDG 7") = "1"

-- ── (a) heap: the CROSS-KEY relation ─────────────────────────────────────────
-- heapNew (key) = 3, heapOther = 5, delta 0 ⇒ 3 <= 5 ok.
#guard admitsWire (wireH "1 0 0 0 1 3 1 5 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "HLO 0") = "0"
#guard admitsWire (wireH "1 0 0 0 1 7 1 5 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "HLO 0") = "1"
-- FAIL CLOSED: an absent `other_key` refuses even when the bound would hold.
#guard admitsWire (wireH "1 0 0 0 1 3 0 0 0 0 0 0 0 0 0 0 0" zeros16 zeros16 "HLO 0") = "1"

-- ── (b) context ──────────────────────────────────────────────────────────────
/-- Header with a context at `h`, no sender, no epoch. -/
private def hdrH (h : String) : String :=
  "1 0 0 0 0 0 0 0 0 0 1 " ++ h ++ " 0 0 0 0 0"
/-- Header with a context and a sender. -/
private def hdrHS (h sender : String) : String :=
  "1 0 0 0 0 0 0 0 0 0 1 " ++ h ++ " 1 " ++ sender ++ " 0 0 0"
/-- Header with a delegation epoch stamped (no `EvalContext`). -/
private def hdrEp (e : String) : String :=
  "1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 " ++ e ++ " 0"

-- FieldGteHeight: height 100, offset 0 ⇒ new[0] must be >= 100.
#guard admitsWire (wireH (hdrH "100") zeros16 (regsAt 0 "64") "FGH 0 0") = "0"
#guard admitsWire (wireH (hdrH "100") zeros16 (regsAt 0 "63") "FGH 0 0") = "1"
-- ⚑ FAIL-CLOSED: NO context ⇒ MissingContextField(block_height), never a silent admit.
#guard admitsWire (wire0 "FGH 0 0") = "4 0"
-- The bad-index check fires BEFORE the context check (eval.rs order).
#guard admitsWire (wire0 "FGH 16 0") = "3 16"
-- FieldLteHeight with a NEGATIVE offset that clamps at 0.
#guard admitsWire (wireH (hdrH "5") zeros16 (regsAt 0 "0") "FLH 0 -100") = "0"
#guard admitsWire (wireH (hdrH "5") zeros16 (regsAt 0 "1") "FLH 0 -100") = "1"

-- TemporalGate: [10, 20]; height 15 ok, 5 too early, 25 too late.
#guard admitsWire (wireH (hdrH "15") zeros16 zeros16 "TG 1 10 1 20") = "0"
#guard admitsWire (wireH (hdrH "5") zeros16 zeros16 "TG 1 10 1 20") = "1"
#guard admitsWire (wireH (hdrH "25") zeros16 zeros16 "TG 1 10 1 20") = "1"
-- Open-ended on both sides admits at any height.
#guard admitsWire (wireH (hdrH "25") zeros16 zeros16 "TG 0 0 0 0") = "0"
#guard admitsWire (wire0 "TG 0 0 0 0") = "4 0"

-- CooledSince: staged 10 + period 5 = 16 needed... boundary is 15.
#guard admitsWire (wireH (hdrH "15") zeros16 zeros16 "CS 10 5") = "0"
#guard admitsWire (wireH (hdrH "14") zeros16 zeros16 "CS 10 5") = "1"

-- ChallengeWindow: window elapsed AND the old challenge register reads 0.
#guard admitsWire (wireH (hdrH "15") zeros16 zeros16 "CW 0 10 5") = "0"
#guard admitsWire (wireH (hdrH "14") zeros16 zeros16 "CW 0 10 5") = "1"
#guard admitsWire (wireH (hdrH "15") (regsAt 0 "1") zeros16 "CW 0 10 5") = "1"

-- DischargeObligation: due 10 reached at height 12; cursor 10 → 15 (period 5);
-- total 100 → 130 (amount 30).
#guard admitsWire (wireH (hdrH "12")
    (String.intercalate " " ["a", "a", "64", "0", "0", "0", "0", "0",
                             "0", "0", "0", "0", "0", "0", "0", "0"])
    (String.intercalate " " ["f", "a", "82", "0", "0", "0", "0", "0",
                             "0", "0", "0", "0", "0", "0", "0", "0"])
    "DO 0 1 2 5 30") = "0"
-- NOT YET DUE (height 9 < due 10) ⇒ violated.
#guard admitsWire (wireH (hdrH "9")
    (String.intercalate " " ["a", "a", "64", "0", "0", "0", "0", "0",
                             "0", "0", "0", "0", "0", "0", "0", "0"])
    (String.intercalate " " ["f", "a", "82", "0", "0", "0", "0", "0",
                             "0", "0", "0", "0", "0", "0", "0", "0"])
    "DO 0 1 2 5 30") = "1"

-- SenderIs / SenderInSlot / SenderMemberOf.
#guard admitsWire (wireH (hdrHS "0" "abcd") zeros16 zeros16 "SIS abcd") = "0"
#guard admitsWire (wireH (hdrHS "0" "abcd") zeros16 zeros16 "SIS abce") = "1"
-- ⚑ FAIL-CLOSED: a context WITHOUT a sender ⇒ MissingContextField(sender).
#guard admitsWire (wireH (hdrH "0") zeros16 zeros16 "SIS abcd") = "4 1"
#guard admitsWire (wireH (hdrHS "0" "abcd") zeros16 (regsAt 0 "abcd") "SIL 0") = "0"
#guard admitsWire (wireH (hdrHS "0" "abcd") zeros16 (regsAt 0 "abce") "SIL 0") = "1"
#guard admitsWire (wireH (hdrHS "0" "abcd") zeros16 zeros16 "SMO 2 1234 abcd") = "0"
#guard admitsWire (wireH (hdrHS "0" "abcd") zeros16 zeros16 "SMO 2 1234 5678") = "1"

-- DelegationEpochEquals: epoch 7 stamped ⇒ slot 0 must hold 7.
#guard admitsWire (wireH (hdrEp "7") zeros16 (regsAt 0 "7") "DEE 0") = "0"
#guard admitsWire (wireH (hdrEp "7") zeros16 (regsAt 0 "8") "DEE 0") = "1"
-- ⚑ FAIL-CLOSED: no stamped epoch ⇒ MissingContextField(delegation_epoch).
#guard admitsWire (wire0 "DEE 0") = "4 2"

-- ── (b) context: the EXECUTOR RATE COUNTERS ──────────────────────────────────
/-- Header with a context present and `sender_epoch_count` = `n`. -/
private def hdrRL (n : String) : String :=
  "1 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 " ++ n

-- RateLimit: 2 mutations this epoch under a cap of 3 admits; 3 refuses (`>=`).
#guard admitsWire (wireH (hdrRL "2") zeros16 zeros16 "RL 3") = "0"
#guard admitsWire (wireH (hdrRL "3") zeros16 zeros16 "RL 3") = "1"
-- ⚑ FAIL-CLOSED: NO context ⇒ MissingContextField(sender_epoch_count). The count is
-- executor-held; there is no submitter-controlled path to it.
#guard admitsWire (wire0 "RL 3") = "4 3"

-- RateLimitBySum: slot 0 rises 2 → 5 (delta 3) on a prior window sum of 0 ⇒ 3 <= 10.
#guard admitsWire (wireH (hdrRL "0") (regsAt 0 "2") (regsAt 0 "5") "RLS 0 10") = "0"
-- Prior window sum 8 + delta 3 = 11 > 10 ⇒ violated.
#guard admitsWire (wireH (hdrRL "8") (regsAt 0 "2") (regsAt 0 "5") "RLS 0 10") = "1"
-- A DECREASE saturates to delta 0 (never a negative credit).
#guard admitsWire (wireH (hdrRL "10") (regsAt 0 "5") (regsAt 0 "2") "RLS 0 10") = "0"
-- An absent context reads prior = 0 (this arm does NOT raise MissingContextField).
#guard admitsWire (wireH hdrPlain (regsAt 0 "2") (regsAt 0 "5") "RLS 0 10") = "0"
#guard admitsWire (wire0 "RLS 16 10") = "3 16"

-- ── (a) the RESOLVED CELL RUN: FieldsCountEquals ─────────────────────────────
-- Three keys resolving to (5, 7, 5); the census of `value = 5` is 2, which slot 0
-- must equal.
private def cells3 : String := "3 1 5 1 7 1 5"
#guard admitsWire (wireC hdrPlain zeros16 (regsAt 0 "2") cells3 "FCE 3 5 0") = "0"
#guard admitsWire (wireC hdrPlain zeros16 (regsAt 0 "3") cells3 "FCE 3 5 0") = "1"
-- ⚑ FAIL-CLOSED: an ABSENT key refuses — it is never counted as a non-match.
#guard admitsWire (wireC hdrPlain zeros16 (regsAt 0 "2") "3 1 5 0 0 1 5" "FCE 3 5 0") = "1"
-- A SHORT cell run refuses (never a truncated census that happens to match).
#guard admitsWire (wireC hdrPlain zeros16 zeros16 "1 1 5" "FCE 3 5 0") = "1"
#guard admitsWire (wireC hdrPlain zeros16 zeros16 cells3 "FCE 3 5 16") = "3 16"

-- ── (a) the RESOLVED CELL RUN: the collection aggregates ─────────────────────
-- stride 2, fuel 3, `countSatGe 2 (elem[1] == 1)`; the ANCHOR is offset 1, so the
-- run truncates at the first element whose cell[i*2+1] is absent.
-- elems: (aa,1) (bb,1) (absent) ⇒ 2 approving elements ⇒ admit.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "6 1 aa 1 1 1 bb 1 1 0 0 0 0" "CAGG 2 3 PCNT 2 EEQ 1 1") = "0"
-- Second element's flag flipped to 2 ⇒ only 1 approving ⇒ violated.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "6 1 aa 1 1 1 bb 1 2 0 0 0 0" "CAGG 2 3 PCNT 2 EEQ 1 1") = "1"
-- ⚑ FAIL-CLOSED: element 0's anchor absent ⇒ NO collection ⇒ refuse (never a
-- vacuous ∀/`count ≥ 0` admit over an empty read).
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "6 1 aa 0 0 1 bb 1 1 1 cc 1 1" "CAGG 2 3 PALL EEQ 1 1") = "1"
-- A zero stride is an ill-formed shape ⇒ refuse.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "2 1 1 1 1" "CAGG 0 3 PALL EEQ 0 1") = "1"
-- ∀ / ∃ over the truncated prefix.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "4 1 1 1 1 0 0 0 0" "CAGG 1 4 PALL EEQ 0 1") = "0"
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "4 1 1 1 2 0 0 0 0" "CAGG 1 4 PALL EEQ 0 1") = "1"
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "4 1 1 1 2 0 0 0 0" "CAGG 1 4 PEX EEQ 0 2") = "0"
-- Σ over the low lane: 3 + 4 + 5 = 12.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "3 1 3 1 4 1 5" "CAGG 1 3 PSLE 0 12") = "0"
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "3 1 3 1 4 1 5" "CAGG 1 3 PSLE 0 11") = "1"
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "3 1 3 1 4 1 5" "CAGG 1 3 PSGE 0 12") = "0"
-- ⚑ THE COUNCIL TOOTH (`mOfNDistinct`): key offset 0, approved = elem[1] == 1,
-- m = 2. Two DISTINCT approving keys (7, 9) ⇒ admit.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "6 1 7 1 1 1 9 1 1 1 b 1 1" "CAGG 2 3 PMN 2 0 EEQ 1 1") = "0"
-- ⚑ THE DUPLICATE-PADDED FORGE: three approving elements, ALL key 7 — the
-- duplicates collapse to ONE distinct key ⇒ REFUSE. (A plain count would admit.)
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "6 1 7 1 1 1 7 1 1 1 7 1 1" "CAGG 2 3 PMN 2 0 EEQ 1 1") = "1"
-- The UNBOUND forge: a distinct key that does NOT approve is filtered out.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "6 1 7 1 1 1 9 1 0 1 b 1 0" "CAGG 2 3 PMN 2 0 EEQ 1 1") = "1"
-- `fieldInSet` reads the u64 LOW LANE of an element field.
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "2 1 5 1 9" "CAGG 1 2 PALL EIN 0 2 5 9") = "0"
#guard admitsWire (wireC hdrPlain zeros16 zeros16
    "2 1 5 1 8" "CAGG 1 2 PALL EIN 0 2 5 9") = "1"

-- ── (a) the EXECUTOR-ONLY SENTINELS ──────────────────────────────────────────
-- CapabilityUniqueness: bounds-check the declared root slot, then ALWAYS refuse
-- (the scalar evaluator cannot see the cell's real CapabilitySet).
#guard admitsWire (wire0 "CAPU 0") = "5"
#guard admitsWire (wire0 "CAPU 16") = "3 16"
-- BoundDelta: the cross-cell sentinel, unconditional.
#guard admitsWire (wire0 "BDW") = "6"

-- ── the AnyOf / AllOf combinators ────────────────────────────────────────────
-- AnyOf(FieldEquals(0,5), FieldEquals(0,7)) against new[0] = 7 ⇒ ok.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "ANY 2 N0 FE 0 5 N0 FE 0 7") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "9") "ANY 2 N0 FE 0 5 N0 FE 0 7") = "1"
-- AllOf(FieldGte(0,5), FieldLte(0,9)) against new[0] = 7 ⇒ ok; = 3 ⇒ violated.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "ALL 2 N0 FG 0 5 N0 FL 0 9") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "3") "ALL 2 N0 FG 0 5 N0 FL 0 9") = "1"
-- Empty AnyOf REFUSES; empty AllOf ADMITS (vacuous AND).
#guard admitsWire (wire0 "ANY 0") = "1"
#guard admitsWire (wire0 "ALL 0") = "0"
-- The Heyting `Not`: Not(FieldEquals(0,5)) admits exactly when the field is NOT 5.
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "7") "ALL 1 N1 FE 0 5") = "0"
#guard admitsWire (wireH hdrPlain zeros16 (regsAt 0 "5") "ALL 1 N1 FE 0 5") = "1"
-- ⚑ FAIL-CLOSED under negation: an UNEVALUABLE inner (bad index) PROPAGATES —
-- `Not` never turns "unevaluable" into "satisfied".
#guard admitsWire (wire0 "ALL 1 N1 FE 16 5") = "3 16"
-- Same for a missing context under negation.
#guard admitsWire (wire0 "ALL 1 N1 FGH 0 0") = "4 0"

-- A malformed / unknown tag fails CLOSED.
#guard admitsWire (wire0 "NOPE 1 2") = "1"
#guard admitsWire "garbage" = "1"

end Dregg2.Exec.DeployedConstraint
