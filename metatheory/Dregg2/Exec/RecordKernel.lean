/-
# Dregg2.Exec.RecordKernel — the kernel laws over a CONTENT-ADDRESSED record cell-state.

`Exec/Kernel.lean` is the verified *micro-core*: its `KernelState.bal : CellId → ℤ` is a single
scalar ledger, and `exec_conserves`/`exec_authorized`/`exec_unauthorized_fails` are PROVED over
that whole-state ℤ. But the concrete dregg2 cell is NOT a scalar — it is `Exec/Value.lean`'s
schema-keyed record `Value` (named fields, `flatten`/`width`/`conforms`, `flatten_width` PROVED).
The construction study's single-highest-leverage move (`docs/rebuild/PHASE-CONSTRUCTION.md §1`,
"The single highest-leverage next move") is to replace the toy scalar ledger with that
content-addressed record cell and re-prove the kernel laws over a NAMED FIELD (`balance`) rather
than the whole-state ℤ — aligning the conserved quantity with `Spec/Conservation`'s domain-typed
conservation (`conservedInDomain Domain.balance`).

This module does exactly that, as a SECOND, parallel kernel ALONGSIDE the scalar one (the
sanctioned fallback when a full in-place lift of `KernelState` ripples too far — here it ripples
across ~8 `Finset.sum`-heavy `Exec/*` files). The toy scalar kernel stays UNTOUCHED and green; we
add `RecordKernelState` + `recKExec` whose cell-state is a `Value` record, conserve the **`balance`
field**, and re-prove ALL THREE kernel laws + the four-conjunct `StepInv` over it. The conserved
quantity becomes a domain measure over a named field — the `Spec.conservedInDomain Domain.balance`
shape — so this is the concrete-instance seam between "verified micro-core" and "verified dregg".

`flatten_width` (from `Value.lean`) is the foundation lemma the *circuit* side rests on; the
*semantic* re-proof here rests on `Value.scalar "balance"` (the named-field read), reusing
`Exec/Kernel.lean`'s already-proved `sum_indicator` over the `balance`-field measure.

Pure, computable, `#eval`-able. Imports `Exec.Program` (for `Value.scalar`/`Value.field`) and
`Exec.Kernel` (for `CellId`/`Turn`/`authorizedB`/`Caps` + the reused `sum_indicator`).
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.Program

namespace Dregg2.Exec

open Dregg2.Authority Dregg2.Execution
open Dregg2.Authority.ClearanceGraph (ClearanceGraph dominatesD)
open scoped BigOperators

/-! ## The record cell-state and its `balance`-field measure. -/

/-- The canonical name of a cell's fungible balance field. The conserved quantity lives HERE —
not in the whole-state ℤ, but in this NAMED field of the content-addressed record. -/
def balanceField : FieldName := "balance"

/-- **An asset identity.** A dregg cell holds MANY assets, and conservation must be **per-asset**,
never one aggregate scalar (`EFFECT-ISA-DESIGN.md:315,320-323`; `dregg2 §2.1`). A turn that moves
5 of asset 0 must leave the supply of asset 1 *literally untouched* — folding all assets into one
sum would let a cell silently swap one asset for another while the aggregate stays put. The
conserved quantity is therefore a *family* indexed by `AssetId` (see `§MULTI-ASSET` below). -/
abbrev AssetId : Type := Nat

/-- **`balOf v`** — read a cell record's `balance` field as an `Int`, defaulting an
absent/ill-typed field to `0` (fail-soft on the *measure*: a malformed record contributes `0` to
the total, never crashes the sum — the data-tier shadow of `Value.flatten`'s zero-default). This
is the named-field measure that replaces `KernelState.bal`'s whole-state scalar. -/
def balOf (v : Value) : Int := (v.scalar balanceField).getD 0

/-! ### SLOT CAVEATS — the per-slot invariants a factory binds onto a cell's fields.

dregg1's `FactoryDescriptor` (`cell/src/factory.rs`) attaches a `program : RecordProgram` whose
`StateConstraint`s (`cell/src/program.rs:570`, "**21 variants**") are checked by the executor on
EVERY `SetField`/`CellProgram::Cases` transition (`evaluate`, `cell/src/program.rs:1314`+). This is
the foundation that makes a starbridge-app's published safety REAL: a `nameservice` slot bound
`Immutable` is *registered forever* because the EXECUTOR rejects any later rewrite, not because some
downstream theorem merely carries the wish.

`SlotCaveat` names the six transition caveats the executor checks PER FIELD — the actor-aware,
name-keyed transcription of the corresponding `StateConstraint` arms (`cell/src/program.rs`):
  * `immutable f`        — `Immutable { index }`        (`:624` / eval `:1314`): `new == old`.
  * `monotonicSeq f`     — `MonotonicSequence { seq }`  (`:719` / eval `:1862`): `new == old + 1`.
  * `monotonic f`        — `Monotonic { index }`        (`:639` / eval `:1364`): `new ≥ old`.
  * `writeOnce f`        — `WriteOnce { index }`         (`:619` / eval `:1337`): `old = 0 ∨ new = old`.
  * `senderAuthorized f authorized` — `SenderAuthorized { set }` (`:675` / eval `:1576`): the actor
    must be a member of the slot's authorized set (the membership-witness crypto is the §8 portal;
    here the set is the EXECUTABLE authorized list the executor checks `actor ∈`).
  * `boundedBy f lo hi`  — `BoundedBy`/`FieldDeltaInRange` family (`:489`/`:636`, eval `:1424`): the
    bounded-value caveat `lo ≤ new ≤ hi` (the executable shadow of the range gate).

`old` defaults to `0` for an absent/ill-typed slot — dregg1's `FIELD_ZERO` default for a fresh slot
(`old_state.map(|o| o.fields[idx]).unwrap_or(FIELD_ZERO)`, `cell/src/program.rs:1331`). The
evaluator is decidable, computable, and FAIL-CLOSED (a violated caveat ⇒ `false` ⇒ the write is
rejected). -/
inductive SlotCaveat where
  /-- `Immutable { index }` (`cell/src/program.rs:624`, eval `:1314`): the slot is read-only —
  `new == old` (no rewrite). A `nameservice` `owner` slot bound here is *registered forever*. -/
  | immutable        (field : FieldName)
  /-- `MonotonicSequence { seq_index }` (`:719`, eval `:1862`): `new == old + 1` — replay-safe
  sequencing (a subscription head/tail advances by exactly one). -/
  | monotonicSeq     (field : FieldName)
  /-- `Monotonic { index }` (`:639`, eval `:1364`): `new ≥ old` — append-only counter / expiry
  extension / nullifier-root growth. -/
  | monotonic        (field : FieldName)
  /-- `WriteOnce { index }` (`:619`, eval `:1337`): `old == FIELD_ZERO` (first write) OR `new == old`
  (unchanged); after the first non-zero write the slot is frozen. -/
  | writeOnce        (field : FieldName)
  /-- `SenderAuthorized { set }` (`:675`, eval `:1576`): the turn's actor must be a member of the
  slot's `authorized` set. (The Merkle/blinded membership *proof* is the §8 Prop-carrier portal; the
  EXECUTABLE check here is `actor ∈ authorized`.) -/
  | senderAuthorized (field : FieldName) (authorized : List CellId)
  /-- `BoundedBy`/`FieldDeltaInRange` range family (`:489`/`:636`, eval `:1424`): the new value must
  lie in `[lo, hi]` (a bounded-growth / windowed slot). -/
  | boundedBy        (field : FieldName) (lo hi : Int)
  /-- **`admitTable { index, transitions }`** — the EXECUTABLE realization of an arbitrary per-slot
  admission predicate the six prior caveats CANNOT express (op-allowlist, prefix-on-PUT,
  GET-clearance, DAG-prereqs, per-step-clearance). dregg1's general `RecordProgram::Cases`
  (`cell/src/program.rs`) lets a factory bind a finite *decision table* of admitted `(old, new)`
  scalar transitions on a slot; the executor admits a write iff its `(old, new)` is in the table —
  fail-closed otherwise. A mandate computes this table ONCE (from its clearance graph / DAG / op
  allowlist) and bakes it into the cell's program, so the SAME admission the off-line predicate
  decides is now decided BY THE EXECUTOR on every `SetField`. This is what makes `cwmAdvanceM` /
  `sgmAdmitM` load-bearing: a no-clearance step / out-of-DAG advance is simply NOT in the table, so
  the executor rejects it (where a `monotonicSeq`/`boundedBy` caveat would wrongly admit). -/
  | admitTable       (field : FieldName) (transitions : List (Int × Int))
  /-- **`clearanceGe { field, g, actorClearances, box }`** — the SGM clearance mandate, now
  enforceable INLINE by the live executor (not precomputed into an `admitTable`). A write to this
  slot is admitted iff the writing `actor`'s clearance label — looked up in the published
  `actorClearances : List (CellId × Int)` table, as a numeric `Label.id` — DOMINATES the slot's
  sensitivity label `box` in the clearance graph `g` (`ClearanceGraph.dominatesD`, the
  proved-sound primitive `Authority/ClearanceGraph.lean:53,92`). Fail-closed: an actor absent from
  the clearance table cannot write. This wires the orphaned-but-proved lattice into the
  executor-enforced caveat surface that `stateStepGuarded`/`setFieldA` consults — so an
  under-cleared actor's write is rejected BY THE EXECUTOR, not merely by an app mandate. -/
  | clearanceGe      (field : FieldName) (g : ClearanceGraph)
                     (actorClearances : List (CellId × Int))
                     (box : Dregg2.Authority.ClearanceGraph.Label)
  deriving Repr, DecidableEq

/-- The field a `SlotCaveat` guards. -/
def SlotCaveat.field : SlotCaveat → FieldName
  | .immutable f          => f
  | .monotonicSeq f       => f
  | .monotonic f          => f
  | .writeOnce f          => f
  | .senderAuthorized f _ => f
  | .boundedBy f _ _      => f
  | .admitTable f _       => f
  | .clearanceGe f _ _ _  => f

/-- **`SlotCaveat.eval cav actor old new`** — does writing `new` to the caveat's slot (whose
committed value is `old`, the actor being `actor`) SATISFY the caveat? Decidable, computable,
FAIL-CLOSED (a violated caveat returns `false`). Mirrors dregg1's `StateConstraint::evaluate`
arms (`cell/src/program.rs`) for the six transition caveats, with `old` defaulting to the fresh
`FIELD_ZERO = 0`. -/
def SlotCaveat.eval : SlotCaveat → CellId → Int → Int → Bool
  | .immutable _,             _,     old, new => decide (new = old)
  | .monotonicSeq _,          _,     old, new => decide (new = old + 1)
  | .monotonic _,             _,     old, new => decide (old ≤ new)
  | .writeOnce _,             _,     old, new => decide (old = 0) || decide (new = old)
  | .senderAuthorized _ auth, actor, _,   _   => auth.contains actor
  | .boundedBy _ lo hi,       _,     _,   new => decide (lo ≤ new) && decide (new ≤ hi)
  | .admitTable _ table,      _,     old, new => table.contains (old, new)
  | .clearanceGe _ g ac box,  actor, _,   _   =>
      match (ac.find? (fun p => p.1 == actor)).map (·.2) with
      | some lvl => dominatesD g (.id lvl.toNat) box   -- actor's clearance dominates the slot's sensitivity
      | none     => false                                   -- actor absent from the clearance table ⇒ fail-closed

/-- **`SlotCaveat.bornFresh cav new`** — does the caveat ADMIT a value `new` as a FRESH cell's genesis
state (dregg1's `None` / genesis arm, `cell/src/program.rs:1331`: a transition caveat permits the
FIRST write on a fresh cell `nonce==0`)? The four TRANSITION caveats (immutable/writeOnce/monotonic/
monotonicSeq) permit any first write (they only constrain SUBSEQUENT transitions); the ABSOLUTE
caveats (`boundedBy` value-range, `senderAuthorized` set-membership) still genuinely constrain the
genesis value — a `BoundedBy [0,10]` slot CANNOT be born at 99. Used by `FactoryEntry.conforms`. -/
def SlotCaveat.bornFresh : SlotCaveat → Int → Bool
  | .immutable _,        _   => true                                    -- first write permitted (genesis)
  | .monotonicSeq _,     _   => true
  | .monotonic _,        _   => true
  | .writeOnce _,        _   => true
  | .senderAuthorized _ _, _ => true                                    -- sender check is a turn-time gate, not genesis
  | .boundedBy _ lo hi,  new => decide (lo ≤ new) && decide (new ≤ hi)  -- value-range STILL binds at birth
  | .admitTable _ _,     _   => true                                    -- a TRANSITION table: first write permitted (genesis)
  | .clearanceGe _ _ _ _, _  => true                                    -- actor-clearance is a turn-time gate, not a genesis-value constraint

/-! ### The FACTORY DESCRIPTOR — a published contract that mints conforming, caveat-bound cells.

dregg1's `FactoryDescriptor` (`cell/src/factory.rs`) is a content-addressed contract: the executor
validates a `CreateCellFromFactory` against the factory's declared constraints
(`validate_and_record`, `apply_create_cell_from_factory`, `turn/src/executor/apply.rs:3112`+), then
mints a cell carrying the factory's `program` (its slot caveats), `initialFields`, and `programVk`.
`FactoryEntry` is the executable transcription: the published `(caveats, initialFields, programVk)`
every minted child carries for its WHOLE LIFE. -/
structure FactoryEntry where
  /-- The per-slot caveats the factory installs on every minted cell (its `program`). These become
  the cell's `slotCaveats`, so the published invariants are enforced over the cell's whole life. -/
  caveats       : List SlotCaveat
  /-- The factory's declared INITIAL field layout `(field, value)` for a fresh cell
  (`params.initial_fields`, `apply.rs:3185`). The cell is born carrying exactly these. -/
  initialFields : List (FieldName × Int)
  /-- The program verification-key hash the factory installs (`effective_vk`, `apply.rs:3197`). The
  crypto content of the VK is the §8 portal; here it is the recorded identifier. -/
  programVk     : Int
  deriving Repr, DecidableEq

/-- Factory initial fields may initialize application slots, but not the conserved legacy
`balance` field. The actual per-asset ledger is born empty separately, so allowing an initial
`"balance"` field would create a split-brain scalar view that the per-asset conservation theorems do
not track. -/
def FactoryEntry.initialFieldsNoBalance (e : FactoryEntry) : Bool :=
  e.initialFields.all (fun p => p.1 != balanceField)

/-- **`FactoryEntry.conforms e`** — does the factory's OWN declared initial state satisfy its OWN
caveats (read against a fresh slot, `old = 0`, by a privileged minter `actor = 0`) and avoid writing the
reserved conserved `balance` field? This is the creation-time constraint check (`validate_and_record`):
a well-formed factory cannot publish initial fields that already VIOLATE the invariants it claims to
enforce (e.g. a `BoundedBy [10,20]` slot born at `25`) or smuggle scalar balance into the record while
the per-asset ledger is born empty. Decidable, computable, FAIL-CLOSED. Each caveat reads its own field's
initial value (defaulting absent to `0`). -/
def FactoryEntry.conforms (e : FactoryEntry) : Bool :=
  e.initialFieldsNoBalance && e.caveats.all (fun cav =>
    let newVal := (e.initialFields.find? (fun p => p.1 == cav.field)).elim 0 (·.2)
    -- genesis: a fresh cell permits the first write of every TRANSITION caveat (dregg1's `None` arm,
    -- `cell/src/program.rs:1331`), but the ABSOLUTE value-range caveats STILL bind — a `BoundedBy
    -- [0,10]` slot cannot be born at 99 (`bornFresh`). This is what gives `conforms` real teeth.
    cav.bornFresh newVal)

/-- A conforming factory has no reserved `balance` initializer. -/
theorem FactoryEntry.conforms_no_balance (e : FactoryEntry) (h : e.conforms = true) :
    e.initialFieldsNoBalance = true := by
  unfold FactoryEntry.conforms at h
  cases hb : e.initialFieldsNoBalance
  · simp [hb] at h
  · rfl

/-- Look up a factory by its content-addressed VK in a registry list (the first match). -/
def findFactory (fs : List (Nat × FactoryEntry)) (vk : Nat) : Option FactoryEntry :=
  (fs.find? (fun p => p.1 == vk)).map (·.2)

/-! ### `EscrowRecord` — TRANSITIONAL wire-codec type (the kernel holding-store is GONE).

F1b removed the kernel escrow side-table (`RecordKernelState.escrows`) and its kernel ops —
escrow/obligation/bridge-LFC semantics live in proven factory cells
(`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`). The TYPE stays for the transitional
window ONLY: the FFI `WState` codec keeps its `escrows` field byte-identical (wire-compat with the
deployed Rust until the lockstep cutover, where these effects die wholesale) and the
`EffectVmEmitEscrowRoot` column model still hashes `EscrowRecord` leaves until the VK rotation. -/

/-- **`EscrowRecord`** — one entry of dregg1's off-ledger `escrows` side-table (`apply.rs:1773`),
keyed by `id`, carrying the locked `amount` of `asset`, the `creator` (refund target) and
`recipient` (release target), the `resolved` flag, the `bridge` tag (the bridge-shaped twin record),
and the queue deposit binding. TRANSITIONAL: kept ONLY for the FFI `WState` wire codec + the
deployed escrow-root column model (see the section note above). -/
structure EscrowRecord where
  /-- the escrow id (dregg1's `[u8;32]` escrow_id, modelled as a `Nat` key). -/
  id        : Nat
  /-- the creator cell whose balance was debited at create (the refund target). -/
  creator   : CellId
  /-- the recipient cell credited on release. -/
  recipient : CellId
  /-- the locked amount held off-ledger while unresolved. -/
  amount    : ℤ
  /-- false until released/refunded; an unresolved record holds `amount` off-ledger. -/
  resolved  : Bool
  /-- the asset class of the locked value. -/
  asset     : AssetId := 0
  /-- the BRIDGE tag — a cross-chain bridge lock parked in the shared store. -/
  bridge    : Bool := false
  /-- queue deposit binding: the deposit was tied to a specific FIFO message. -/
  queueDep  : Option Nat := none
  queueMsg  : Option Nat := none
deriving DecidableEq, Repr

/-! ### `QueueRecord` — TRANSITIONAL wire-codec type (the kernel queue side-table is GONE).

F2b removed the kernel queue side-table (`RecordKernelState.queues`) and its kernel ops
(`queueAllocateK`/`queueEnqueueK`/`queueDequeueK`/`queueResizeK` and the `qbuf*` FIFO buffer
spec) — queue/inbox/pubsub semantics live in proven factory cells
(`Apps/{QueueFactory,InboxFactory,PubsubFactory}.lean`): the queue is a minted CELL whose
head/tail/capacity/owner/sender_set/message_root are SLOTS, gated by `SlotCaveat`
(Immutable + MonotonicSequence + SenderAuthorized) plus the LIVE cross-slot relational caveat
`RelCaveat.fieldLteOther` (capacity / no-underflow). The FIFO-order shadow (`qbufEnqueue`/
`qbufDequeue` + `qbuf_fifo_order`) now lives with the factory story in `Apps/QueueFactory.lean`.
The TYPE stays for the transitional window ONLY: the FFI `WState` codec keeps its `queues` field
byte-identical (wire-compat with the deployed Rust until the lockstep cutover, where these
effects die wholesale — same `EscrowRecord` precedent above). -/

/-- **`QueueRecord`** — one entry of dregg1's off-ledger queue side-table, keyed by `id` (dregg1's
queue cell id, modelled as a `Nat` key), carrying the queue `owner`, the `capacity`, and the
ordered `buffer : List Nat` of message hashes in FIFO order. TRANSITIONAL: kept ONLY for the FFI
`WState` wire codec (see the section note above). -/
structure QueueRecord where
  /-- the queue id (dregg1's queue cell `CellId`, modelled as a `Nat` key). -/
  id       : Nat
  /-- the queue owner. -/
  owner    : CellId
  /-- the queue capacity. -/
  capacity : Nat
  /-- the ordered list of message hashes, front = head = next-to-dequeue. -/
  buffer   : List Nat := []
deriving DecidableEq, Repr

/-! ### The SWISS-TABLE side-table — a REAL CapTP export/enliven/handoff/GC registry (Wave-8 de-THIN).

dregg1's CapTP transport (`turn/src/action.rs` `ExportSturdyRef`/`EnlivenRef`/`ValidateHandoff`/`DropRef`;
`turn/src/executor/apply.rs:3879 apply_export_sturdy_ref` / `:3955 apply_enliven_ref` /
`:4035 apply_drop_ref` / `:4109 apply_validate_handoff`) keeps a swiss-table: an EXPORT mints an
unguessable swiss number → (target cell, exported permission tier) entry and bumps an export counter;
an ENLIVEN VALIDATES a presented swiss number against the committed table (membership, fail-closed if
absent) and bumps the entry's use-count; a HANDOFF binds a 3-vat introduce CERT to the entry; a DROP
GCs a reference (decrement-fail-closed-at-zero, `apply.rs:4051`). dregg1 scatters this across cell
state fields (field[5]=refcount, field[6]=use-count, field[7]=export-counter) + a federation mirror; we
model the REAL MECHANISM as a first-class swiss-table side-table keyed by swiss number, carrying the
exported `cap`'s rights + a REFCOUNT (the GC counter) + the bound handoff `cert`. This is NOT a
flag-shadow: export INSERTS, enliven LOOKS-UP-fail-closed-and-validates, handoff binds the cert, the
refcount tracks live references and the entry is GC'd at zero. The export/enliven NON-AMPLIFICATION
(claimed rights ⊆ entry rights) is the real CapTP soundness gate (`apply.rs:3917`, `:3999`). -/

/-- **`SwissRecord`** — one entry of the swiss-table side-table, keyed by the `swiss` number (dregg1's
32-byte unguessable swiss number, modelled as a `Nat` key). Carries the `exporter` cell (who minted the
ref), the `target` cell the sturdy ref points to, the exported `rights` (the permission tier a bearer
obtains on enliven — bound into the AIR's `EXPORT_PERMISSIONS`), the `refcount` (the GC counter — # of
LIVE references; the entry is GC'd when it hits 0, `apply.rs:4051`), and the bound handoff `cert`
(`none` until a 3-vat introduce cert is validated against this entry; `some h` once bound). -/
structure SwissRecord where
  /-- the swiss number key (dregg1's `[u8;32]`, modelled as a `Nat`). -/
  swiss    : Nat
  /-- the exporter cell — who minted this sturdy ref (`apply.rs:3879`). -/
  exporter : CellId
  /-- the target cell the sturdy ref grants access to (`ExportSturdyRef.target`). -/
  target   : CellId
  /-- the exported permission tier — the rights a bearer obtains on enliven. The enliven
  non-amplification gate checks the bearer's CLAIMED rights are `⊆` THESE (`apply.rs:3999`). -/
  rights   : List Auth
  /-- the GC refcount — number of LIVE references. Export mints `1`; enliven/handoff bump; drop
  decrements; the entry is GC'd (removed) when this hits `0` (`apply.rs:4051`). -/
  refcount : Nat
  /-- the bound 3-vat handoff cert hash (`none` until a `ValidateHandoff` binds one; `some h` after). -/
  cert     : Option Nat := none
deriving DecidableEq, Repr

/-- Look up a swiss-table entry by swiss number (the first match), `none` if absent. The MEMBERSHIP
primitive enliven/handoff/drop validate against — fail-closed when `none`. -/
def findSwiss (ss : List SwissRecord) (swiss : Nat) : Option SwissRecord :=
  ss.find? (fun e => e.swiss == swiss)

/-- Replace the swiss entry with the given `swiss` number by `e'` (the first match), leaving others
untouched. The update primitive shared by enliven/handoff (refcount bump + cert bind). -/
def replaceSwiss (ss : List SwissRecord) (swiss : Nat) (e' : SwissRecord) : List SwissRecord :=
  ss.map (fun e => if e.swiss == swiss then e' else e)

/-- Remove the swiss entry with the given `swiss` number (the GC drop when refcount hits 0). -/
def removeSwiss (ss : List SwissRecord) (swiss : Nat) : List SwissRecord :=
  ss.filter (fun e => !(e.swiss == swiss))

/-- **NARROWER-OR-EQUAL — the CapTP non-amplification predicate.** The bearer's CLAIMED `rights` must be
a SUBSET of the entry's exported `rights` — a sturdy ref must NOT grant authority the export did not hold
(`AuthRequired::is_narrower_or_equal`, `apply.rs:3917`, `:3999`). Modelled as list-subset over `Auth`. -/
def rightsNarrowerOrEqual (claimed entry : List Auth) : Bool :=
  claimed.all (fun a => entry.contains a)

/-! ## §SEAL — the sealed-box holding-store (Wave-3 de-shadow of `apply_seal`/`apply_unseal`).

dregg1's seal/unseal genuinely MOVE a capability through an AEAD box: `apply_create_seal_pair`
(`apply.rs:2675`) grants a sealer + unsealer cap; `apply_seal` (`apply.rs:2743`) seals a HELD `Cap`
into a box bound to the sealer key; `apply_unseal` (`apply.rs:2874`) opens it under the unsealer key
and GRANTS the recovered `Cap` to the recipient's c-list. The wave-6 model collapsed all three to a
field flag (`sealed_box := 1`) — NO capability ever moved. We de-shadow by carrying the box as a
first-class side-table entry whose payload is the SEALED `Cap`; the AEAD crypto is the §8 portal, but
the WHICH-cap binding and the c-list move are REAL. -/

/-- **`SealedBoxRecord`** — one entry of the sealed-box holding-store, keyed by `pairId` (dregg1's
`SealedBox.pair_id`). Carries the cell that SEALED it (the sealer-cap holder) and the `payload : Cap`
the box binds — the genuine capability that `unseal` will recover and grant. The AEAD ciphertext that
binds `payload` is the §8 portal; what is REAL here is that the box holds a SPECIFIC cap (not a flag),
so unseal moves THAT cap and no other. -/
structure SealedBoxRecord where
  /-- the seal-pair id key (dregg1's `[u8;32]`, modelled as a `Nat`). -/
  pairId  : Nat
  /-- the cell that sealed the box (held the sealer cap, `apply_seal`'s `actor`). -/
  sealer  : CellId
  /-- the SEALED capability the box binds — recovered and granted by `unseal` (`apply_unseal`'s
  `cap` from `pair.unseal(sealed_box)`, `apply.rs:2922`). The REAL payload, not a flag. -/
  payload : Cap
deriving DecidableEq, Repr

/-- Look up a sealed box by `pairId` in the holding-store (the first match), `none` if absent. The
membership primitive `unseal` validates against — fail-closed when `none`. -/
def findSealedBox (bs : List SealedBoxRecord) (pid : Nat) : Option SealedBoxRecord :=
  bs.find? (fun e => e.pairId == pid)

/-- **Record kernel state:** the finite set of live `accounts`, a per-cell **content-addressed
record** state (`cell : CellId → Value`, each a `Value.record` carrying at least a `balance`
field), and the capability table — PLUS dregg1's off-ledger side-tables, defaulting EMPTY so every
existing construction/proof that ignores them is unaffected (the additive extension):

  * `nullifiers` — the spent-note nullifier SET (`self.note_nullifiers`, `apply.rs:941`); a
    `NoteSpend` inserts its nullifier and is rejected fail-closed if already present (double-spend).

F1b: the kernel escrow holding-store (`escrows : List EscrowRecord`) is GONE — escrow/obligation/
bridge-LFC value parks in factory cells' OWN `bal` columns (`Apps/{EscrowFactory,ObligationFactory,
BridgeCell}.lean`), covered by the SAME per-asset cell-sum `recTotalAsset`. The `EscrowRecord` TYPE
survives only for the FFI wire codec + the deployed escrow-root column model (see its section note).

This is `KernelState` with `bal : CellId → ℤ` lifted to `cell : CellId → Value`, additively extended
with the side-tables — the concrete dregg2 cell + dregg1's real side-table accounting. -/
structure RecordKernelState where
  /-- The finite set of live cells whose balances are tracked / conserved. -/
  accounts : Finset CellId
  /-- Per-cell content-addressed record state (each carries a `balance` field). -/
  cell     : CellId → Value
  /-- The capability table (lift of l4v `Caps`). -/
  caps     : Caps
  /-- The spent-note nullifier SET (`self.note_nullifiers`); DEFAULTS EMPTY. -/
  nullifiers : List Nat := []
  /-- **The KERNEL-STATE REVOCATION REGISTRY** (`self.revocation_channel`, hole #3 / `#139`): the
  committed set of revoked credential nullifiers — the MDB/derivation-table root that `cap_revoke`
  tears down (single-machine ⇒ immediate revocation). A node's credential is revoked iff its
  `credNul` is in THIS set, read off committed state (NOT the wire-supplied, formerly-pinned
  `NodeAuth.rev`), so the fail-closed gate `gateOK` can finally honour revocation. Balance-NEUTRAL
  (`recTotalAsset` reads `bal`, never `revoked`). DEFAULTS EMPTY (the additive
  extension, exactly as `nullifiers`/`commitments` were added). -/
  revoked    : List Nat := []
  /-- **The note COMMITMENT SET** (`META-FILL C`, closing `#121`): the grow-only dual of
  `nullifiers`. dregg1's `apply_note_create` inserts a fresh Pedersen commitment into the off-ledger
  commitment tree (a §8 CryptoPortal-gated range proof guards the hidden value). A `noteCreate` grows
  THIS set (NOT `bal`, NOT `nullifiers`) — so it is bal-NEUTRAL and genuinely distinct
  from escrow/obligation/noteSpend (the `#121` de-conflation). DEFAULTS EMPTY (the additive
  extension, exactly as `nullifiers` was added). -/
  commitments : List Nat := []
  /-- **The genuine per-asset balance ledger** `bal c a` — the (ℤ-valued, debt-capable) amount of
  asset `a` held by cell `c`. dregg cells hold MANY assets; conservation is PER-ASSET
  (`EFFECT-ISA-DESIGN.md:315,320-323`), never one aggregate scalar. DEFAULTS to the empty ledger so
  every existing construction/proof that ignores it is unaffected (the additive extension, exactly
  as `nullifiers` were added). This is the destination conserved measure the per-asset
  transition (`§MULTI-ASSET`) preserves; the scalar `balance` field is its legacy asset-view, and
  the executable `FullAction` dispatch migrates onto `bal` (`DREGG2-GAP-MAP.md FILL 1`). -/
  bal        : CellId → AssetId → ℤ := fun _ _ => 0
  /-- **The SWISS-TABLE side-table** (Wave-8 de-THIN): the CapTP export/enliven/handoff/GC registry — a
  list of live `SwissRecord` entries, each keyed by its swiss number, carrying the exported cap's
  `rights` + a `refcount` (the GC counter) + the bound handoff `cert`. The swiss-table moves REFERENCES
  (capability routing), NOT balance — so it is balance-NEUTRAL (`recTotalAsset` is UNCHANGED
  ∀ asset; it reads `bal`, never `swiss`). DEFAULTS EMPTY (the additive extension, exactly as
  `nullifiers`/`commitments` were added). Export INSERTS, enliven LOOKS-UP-fail-closed
  + validates non-amplification, handoff binds the cert, the refcount tracks live refs (GC at 0) — the
  REAL mechanism a flag-shadow lacks. -/
  swiss      : List SwissRecord := []
  /-- **The PER-CELL SLOT-CAVEAT registry** (dregg1's `FactoryDescriptor.program` carried per minted
  cell, `cell/src/factory.rs`): the list of `SlotCaveat`s the executor checks on EVERY `SetField` to
  that cell (`apply_set_field` → `RecordProgram::evaluate`, `cell/src/program.rs:1314`+). A factory
  installs these at `createCellFromFactory` time; thereafter `stateStepGuarded` (the caveat-gated
  field write) rejects any write violating a caveat on the written slot. This is what makes a
  published app-safety REAL — `nameservice` `Immutable`-owner = *registered forever*, enforced BY THE
  EXECUTOR. Caveats touch NO balance, so this is balance-NEUTRAL (`recTotalAsset` reads
  `bal`, never `slotCaveats`). DEFAULTS EMPTY (the additive extension, exactly as
  `nullifiers`/`commitments`/`swiss` were added — a cell with no factory-bound
  caveats writes freely, recovering the prior unguarded semantics). -/
  slotCaveats : CellId → List SlotCaveat := fun _ => []
  /-- **The PUBLISHED FACTORY REGISTRY** (dregg1's `self.factory_registry`, `cell/src/factory.rs`):
  the content-addressed map from a factory's VK to its `FactoryEntry` (its published
  caveats/initial-fields/programVk). `apply_create_cell_from_factory` looks a factory up HERE
  (`validate_and_record`, `apply.rs:3140`), validates the creation, and mints a cell carrying the
  factory's program. Factories hold NO balance, so this is balance-NEUTRAL. DEFAULTS EMPTY (the
  additive extension). -/
  factories  : List (Nat × FactoryEntry) := []
  /-- **The PER-CELL LIFECYCLE registry** (Wave-3; dregg1's `Cell.lifecycle : CellLifecycle`,
  `cell/src/lifecycle.rs:37`). Modelled by the stable discriminant (`CellLifecycle::discriminant`,
  `lifecycle.rs:95`): `0` = Live, `1` = Sealed, `3` = Destroyed (the three states Wave-3 transitions
  cover; `2`/`4` Migrated/Archived are out of scope and keep their unused discriminants). A cell
  DEFAULTS Live (`0`), so every existing construction is unaffected. `cellSeal` does Live→Sealed
  (`seal`, `cell.rs:528`), `cellUnseal` Sealed→Live (`unseal`, `cell.rs:559`), `cellDestroy`
  non-terminal→Destroyed (`destroy`, `cell.rs:583`); `acceptsEffects` (= dregg1's
  `CellLifecycle::accepts_effects`, `lifecycle.rs:109`) gates which cells admit effects (Live here).
  Lifecycle touches NO balance, so this is balance-NEUTRAL (`recTotalAsset` reads
  `bal`, never `lifecycle`). DEFAULTS Live. -/
  lifecycle  : CellId → Nat := fun _ => 0
  /-- **The PER-CELL DEATH-CERTIFICATE binding** (Wave-3; dregg1's `CellLifecycle::Destroyed
  { death_certificate_hash, .. }`, `lifecycle.rs:63`). A destroyed cell binds the death-certificate
  hash into its FINAL state (`cell.rs:593`); we carry it keyed by cell. `0` until destruction, `h`
  once `cellDestroy` binds the disclosed `certHash`. Balance-NEUTRAL. DEFAULTS `0`. -/
  deathCert  : CellId → Nat := fun _ => 0
  /-- **The PER-CELL DELEGATION parent pointer + c-list snapshot** (Wave-3; dregg1's `Cell.delegate :
  Option<CellId>` parent pointer + `Cell.delegation : Option<DelegatedRef>` whose `clist` snapshots the
  parent's c-list, `apply_spawn_with_delegation`/`apply_refresh_delegation`, `apply.rs:2947`/`:2991`).
  `delegate c` is the parent of `c` (`none` = no parent; modelled as `Option CellId`, dregg1's
  `Option<CellId>` — so cell `0` is a legitimate PARENT, distinct from "no parent"); `delegations c` is
  the SNAPSHOT of the parent's c-list carried in `c`'s `DelegatedRef` (a `List Cap`, EMPTY when no
  delegation). `refreshDelegation` (`apply.rs:2991`) takes a FRESH snapshot of the parent's CURRENT
  `caps` into `delegations child`. Delegation snapshots touch NO balance, so this is balance-NEUTRAL.
  DEFAULTS `none`/empty. -/
  delegate    : CellId → Option CellId := fun _ => none
  delegations : CellId → List Cap := fun _ => []
  /-- **The SEALED-BOX holding-store** (Wave-3 de-shadow; dregg1's per-cell `state.fields[7]` seal
  commitment + the AEAD box, `apply_seal`/`apply_unseal`, `apply.rs:2743`/`:2874`). The list of live
  `SealedBoxRecord`s, each binding a `pairId` → the SEALED `Cap` payload. `seal` INSERTS a box binding a
  HELD cap; `unseal` LOOKS-UP-fail-closed + (under the §8 AEAD-open portal) GRANTS the recovered cap to
  the recipient. This carries a REAL capability (not a flag), so the cap genuinely MOVES through the box.
  The AEAD ciphertext is the §8 portal; the which-cap binding + c-list grant are REAL. Boxes hold
  capabilities, NOT balance — balance-NEUTRAL. DEFAULTS EMPTY. -/
  sealedBoxes : List SealedBoxRecord := []
  /-- **The PER-CELL DELEGATION EPOCH** (Wave-9 kernel-widen; dregg1's `CellState.delegation_epoch :
  u64`, `cell/src/state.rs:110`). The monotone revocation counter a cell carries AS A PARENT: dregg1's
  `apply_revoke_delegation` (`apply.rs:3067-3069`) bumps the PARENT cell's (`action_target`'s) epoch by
  `+1` via `bump_delegation_epoch` (`state.rs:630`), which is folded into the canonical state commitment
  (`commitment.rs:263` hashes `state.delegation_epoch`). EVERY child snapshot taken under an OLDER parent
  epoch (`delegationEpochAt child < delegationEpoch parent`) is thereby rendered STALE — this is the
  freshness mechanism a light client checks so a revoked delegation cannot be replayed (the "pale ghost"
  foil). `spawnWithDelegation`/`refreshDelegation` STAMP the child's snapshot with the parent's epoch AT
  SNAPSHOT TIME (`apply.rs:2963`/`:3024`, `delegation_epoch = parent.state.delegation_epoch()`); a revoke
  bumps the parent's, so the stamp falls behind. Epochs touch NO balance — balance-NEUTRAL. DEFAULTS `0`
  (the additive extension, exactly as `nullifiers`/`commitments`/`delegate`/`delegations` were
  added — every existing construction/proof that ignores it is unaffected by the `0` default). -/
  delegationEpoch   : CellId → Nat := fun _ => 0
  /-- **The PER-CHILD SNAPSHOT-EPOCH STAMP** (Wave-9 kernel-widen; dregg1's `DelegatedRef.delegation_epoch
  : u64`, `cell/src/delegation.rs:65`). When a child takes/refreshes its delegation snapshot, dregg1
  records the PARENT's CURRENT `delegation_epoch` into the child's `DelegatedRef` (`apply.rs:2977`/`:3035`,
  signed over by the parent, `delegation.rs:53`). `delegationEpochAt child` is that recorded stamp. The
  child's snapshot is FRESH iff its stamp is `≥` the parent's CURRENT `delegationEpoch` — a parent revoke
  (which bumps the parent epoch) leaves the stamp behind, marking the snapshot STALE (`delegationStale`).
  Refresh re-stamps it to the parent's current epoch. Epochs touch NO balance — balance-NEUTRAL. DEFAULTS
  `0` (the additive extension). -/
  delegationEpochAt : CellId → Nat := fun _ => 0

/-- **The `balance`-domain measure** over the record cell-state: the total `balance` field across
the live accounts. This is the conserved quantity — a domain measure over the named `balance`
field (the `Spec.conservedInDomain Domain.balance` shape), NOT the whole `Value`. -/
def recTotal (k : RecordKernelState) : ℤ := ∑ c ∈ k.accounts, balOf (k.cell c)

/-! ## The record-cell transfer: debit/credit the `balance` FIELD. -/

/-- Set the `balance` field of a record cell to `v` (overwriting in place; a non-record value
becomes a singleton `balance` record, keeping the update total). This is the named-field write
that the transfer uses — it touches ONLY the `balance` field, leaving every other field of the
content-addressed record intact. -/
def setBalance (cell : Value) (v : Int) : Value :=
  match cell with
  | .record fs => .record (setBalanceList fs v)
  | _          => .record [(balanceField, .int v)]
where
  setBalanceList : List (FieldName × Value) → Int → List (FieldName × Value)
  | [],            v => [(balanceField, .int v)]
  | (k, x) :: rest, v => if k == balanceField then (balanceField, .int v) :: rest
                         else (k, x) :: setBalanceList rest v

/-- After `setBalance cell v`, reading the `balance` field returns exactly `v` (the write/read
law for the named-field measure). -/
theorem setBalance_balOf (cell : Value) (v : Int) : balOf (setBalance cell v) = v := by
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (setBalance.setBalanceList fs v)).scalar balanceField) = some v := by
    intro fs
    induction fs with
    | nil => simp [setBalance.setBalanceList, Value.scalar, Value.field]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setBalance.setBalanceList]
        by_cases hk : (k == balanceField) = true
        · rw [if_pos hk]
          simp [Value.scalar, Value.field, balanceField]
        · have hkf : (k == balanceField) = false := by simpa using hk
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hkf)]
          exact ih
  unfold balOf setBalance
  cases cell with
  | record fs => rw [hlist fs]; rfl
  | int _  => simp [Value.scalar, Value.field, balanceField]
  | dig _  => simp [Value.scalar, Value.field, balanceField]
  | sym _  => simp [Value.scalar, Value.field, balanceField]

/-- The per-cell record after a transfer: debit `src`'s `balance`, credit `dst`'s, leave every
other cell's record untouched. The named-field analog of `Kernel.transferBal` — but it rewrites
the `balance` FIELD of a `Value` record, not a whole-state ℤ. -/
def recTransfer (cell : CellId → Value) (src dst : CellId) (amt : ℤ) : CellId → Value :=
  fun c =>
    if c = src then setBalance (cell c) (balOf (cell c) - amt)
    else if c = dst then setBalance (cell c) (balOf (cell c) + amt)
    else cell c

/-- **The executable record kernel transition.** Fail-closed: commits only when the actor is
authorized over `src` (reusing `Kernel.authorizedB` — same gate), the amount is non-negative and
available *in the `balance` field*, `src ≠ dst`, and both cells are live accounts. The post-state
rewrites the `balance` field of the two cells; the rest of each content-addressed record is
preserved. -/
def recKExec (k : RecordKernelState) (turn : Turn) : Option RecordKernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with cell := recTransfer k.cell turn.src turn.dst turn.amt }
  else
    none

/-! ## The record kernel satisfies the laws — re-proved over the `balance` FIELD. -/

/-- The `balance`-field delta of a transfer at a single cell, factored into a debit-indicator +
credit-indicator (the named-field analog of `Kernel.transfer_sum_conserve`'s pointwise step). -/
theorem recTransfer_balOf_delta (cell : CellId → Value) (src dst : CellId) (amt : ℤ)
    (hne : src ≠ dst) (c : CellId) :
    balOf (recTransfer cell src dst amt c) - balOf (cell c)
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
  unfold recTransfer
  rcases eq_or_ne c src with h1 | h1
  · have hcd : c ≠ dst := by rw [h1]; exact hne
    rw [if_pos h1, setBalance_balOf, if_pos h1, if_neg hcd]
    ring
  · rcases eq_or_ne c dst with h2 | h2
    · rw [if_neg h1, if_pos h2, setBalance_balOf, if_neg h1, if_pos h2]
      ring
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      ring

/-- **Conservation core (the `balance` field):** a transfer between two distinct live accounts
preserves the total `balance` (debit and credit cancel in the named field). Reuses
`Kernel.sum_indicator` over the `balance`-field measure — the same single-point-cancellation
argument the scalar kernel uses, lifted to the record's `balance` field. -/
theorem recTransfer_balanceSum_conserve (acc : Finset CellId) (cell : CellId → Value)
    (src dst : CellId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, balOf (recTransfer cell src dst amt c)) = ∑ c ∈ acc, balOf (cell c) := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, balOf (recTransfer cell src dst amt c) - balOf (cell c)
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) :=
    fun c _ => recTransfer_balOf_delta cell src dst amt hne c
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

/-- **Conservation (Law 1) — PROVED of the record kernel over the `balance` FIELD.** Every
committed record-cell turn preserves the total `balance` field across the live accounts. This is
`Kernel.exec_conserves` lifted from the whole-state ℤ to the named `balance` field of a
content-addressed `Value` record — the conserved quantity is now a domain measure over a field,
aligning with `Spec.conservedInDomain Domain.balance`. -/
theorem recKExec_conserves (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') : recTotal k' = recTotal k := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    simpa [recTotal] using
      recTransfer_balanceSum_conserve k.accounts k.cell turn.src turn.dst turn.amt hsrc hdst hne
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **No state change without authority — PROVED** (the integrity/confinement core for the record
kernel: it never moves a cell's `balance` field on behalf of an unauthorized actor). Same gate
(`authorizedB`) as the scalar kernel — authority is orthogonal to the state representation. -/
theorem recKExec_authorized (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') : authorizedB k.caps turn = true := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed — PROVED.** An unauthorized turn does NOT commit on the record kernel. -/
theorem recKExec_unauthorized_fails (k : RecordKernelState) (turn : Turn)
    (h : authorizedB k.caps turn = false) : recKExec k turn = none := by
  unfold recKExec
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-- **`recKExec` preserves the account set and cap table** (it rewrites only the `cell` records'
`balance` fields). The structural-frame fact the refinement square reads. PROVED. -/
theorem recKExec_frame (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') : k'.accounts = k.accounts ∧ k'.caps = k.caps := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §MULTI-ASSET — the per-asset `CONSERVATION_VECTOR` over the REAL executable state + gate.

`recKExec`/`recTotal` above conserve ONE scalar (the `balance` field). A dregg cell holds MANY
assets, and conservation must be PER-ASSET — a committed turn moving asset `a` must leave EVERY
other asset's supply *literally untouched*; folding all assets into one aggregate would let a cell
silently swap asset A for asset B while the scalar stays put (`EFFECT-ISA-DESIGN.md:315,320-323`;
`DREGG2-GAP-MAP.md FILL 1`, "the #1 soundness gap"). `Exec.MultiAsset` proved exactly this — but
over a deliberately PARALLEL `MACellId`/`maAuthorizedB` toy that "cannot clash with `Kernel.CellId`"
and is imported by nothing executable (a sibling law). Here we re-prove it over the REAL
`RecordKernelState.bal` ledger and the REAL `authorizedB k.caps` gate — the SAME state type and
authority the FFI's `execFullTurn` runs — so the per-asset law is no longer a sibling. (Migrating
the executable `FullAction` dispatch onto `bal` + the negative differential is the next phase.) -/

/-- The per-asset balance ledger after a transfer of asset `a`: debit `src`, credit `dst` in the
`a` column ONLY; every other cell and **every other asset** is returned unchanged. The named-field
`recTransfer`'s multi-asset analog, over the genuine `CellId → AssetId → ℤ` ledger. -/
def recTransferBal (bal : CellId → AssetId → ℤ) (src dst : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun c b =>
    if b = a then
      (if c = src then bal c b - amt else if c = dst then bal c b + amt else bal c b)
    else bal c b

/-- **The executable per-asset transition** over the real record state. Fail-closed: commits only
when the actor is authorized over `src` (the SAME `authorizedB k.caps` gate as the scalar kernel —
NOT `MultiAsset`'s `maAuthorizedB` toy), the amount is non-negative and available *in that asset*,
`src ≠ dst`, and both cells are live accounts. Rewrites ONLY the `bal` ledger's `a` column. -/
def recKExecAsset (k : RecordKernelState) (turn : Turn) (a : AssetId) : Option RecordKernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with bal := recTransferBal k.bal turn.src turn.dst a turn.amt }
  else
    none

/-- **Total supply of asset `a`** over the live accounts — the conserved family, indexed by
`AssetId` (NOT collapsed to one scalar). The per-asset analog of `recTotal`. -/
def recTotalAsset (k : RecordKernelState) (a : AssetId) : ℤ := ∑ c ∈ k.accounts, k.bal c a

/-- Per-asset conservation core (moved asset): for the moved asset `a`, a transfer between two
distinct live accounts preserves its column sum (debit and credit cancel). Reuses `sum_indicator`,
the same single-point-cancellation the scalar kernel uses. -/
theorem recTransferBal_sum_conserve_moved (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (src dst : CellId) (a : AssetId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, recTransferBal bal src dst a amt c a) = ∑ c ∈ acc, bal c a := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hg : ∀ c ∈ acc, recTransferBal bal src dst a amt c a - bal c a
      = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
    intro c _
    unfold recTransferBal
    rw [if_pos rfl]
    rcases eq_or_ne c src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne c dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

/-- Per-asset conservation core (untouched asset): for any asset `b ≠ a`, the transfer of asset `a`
leaves the entire `b` column literally unchanged — pointwise, hence the sum. -/
theorem recTransferBal_untouched (bal : CellId → AssetId → ℤ) (src dst : CellId)
    (a b : AssetId) (amt : ℤ) (hb : b ≠ a) (c : CellId) :
    recTransferBal bal src dst a amt c b = bal c b := by
  unfold recTransferBal; rw [if_neg hb]

/-- **THE KEYSTONE — per-asset conservation, PROVED of the EXECUTABLE record kernel over the REAL
gate.** Every committed per-asset transfer preserves `recTotalAsset k b` for EVERY asset `b`: the
moved asset by the debit/credit cancellation, every other asset because its column is untouched.
This is the `CONSERVATION_VECTOR` (`DREGG2-GAP-MAP.md FILL 1`) on the real executable
`RecordKernelState` — the multi-asset refinement of `recKExec_conserves`, no longer a `MultiAsset`
sibling toy. -/
theorem recKExecAsset_conserves_per_asset (k k' : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : recKExecAsset k turn a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    show (∑ c ∈ k.accounts, recTransferBal k.bal turn.src turn.dst a turn.amt c b)
        = ∑ c ∈ k.accounts, k.bal c b
    rcases eq_or_ne b a with hb | hb
    · subst hb
      exact recTransferBal_sum_conserve_moved k.accounts k.bal turn.src turn.dst b turn.amt
        hsrc hdst hne
    · exact Finset.sum_congr rfl
        (fun c _ => recTransferBal_untouched k.bal turn.src turn.dst a b turn.amt hb c)
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **No state change without authority — PROVED** for the per-asset kernel: it never moves a cell's
resource on behalf of an unauthorized actor. The REAL `authorizedB` gate, not `MultiAsset`'s
`maAuthorizedB` toy. -/
theorem recKExecAsset_authorized (k k' : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : recKExecAsset k turn a = some k') : authorizedB k.caps turn = true := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Fail-closed — PROVED.** An unauthorized per-asset turn does NOT commit. -/
theorem recKExecAsset_unauthorized_fails (k : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : authorizedB k.caps turn = false) : recKExecAsset k turn a = none := by
  unfold recKExecAsset
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-- **The cross-asset NON-LAUNDERING fact — PROVED.** A committed transfer of asset `a` CANNOT
change asset `b ≠ a`'s total supply. This is exactly what a SCALAR kernel cannot guarantee: a
scalar that sums one aggregate would accept a turn that mints asset B while burning an equal amount
of asset A (aggregate-conserving, per-asset-VIOLATING). The per-asset ledger makes that laundering
unrepresentable as a single conservative transfer — the soundness content of `CONSERVATION_VECTOR`. -/
theorem recKExecAsset_no_cross_asset_leak (k k' : RecordKernelState) (turn : Turn) (a b : AssetId)
    (h : recKExecAsset k turn a = some k') (_hb : b ≠ a) :
    recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k' turn a h b

/-! ## Per-asset ACCOUNT-GROWTH: a fresh cell, born EMPTY in every asset (`META-FILL C`).

dregg1's `Effect::CreateCell` (`turn/src/executor/apply.rs:748`) is a PRIVILEGED creation of a FRESH
cell that — per `apply_create_cell`'s `CreateCellNonZeroBalance` rejection (`apply.rs:757`) — is born
with `balance == 0` (`Cell::with_balance(.,.,0)`): conservation-NEUTRAL. We grow the per-asset ledger's
index set (`accounts`) while keeping the conserved measure `recTotalAsset` UNCHANGED, by INSERTING the
fresh cell AND resetting its `bal` column to `0` for every asset — so the new term in the sum is exactly
`0`. The `bal`-reset is LOAD-BEARING: a freshly-inserted id that had EVER been credited (a re-inserted
previously-credited id) would silently re-introduce supply on insert. Resetting unconditionally defends
against that (neutrality is PROVED, not assumed). -/

/-- Reset every per-cell indexed slot at `newCell` to born-empty defaults (closes stale side-table
resurrection when minting a fresh id that is not currently live). -/
def bornEmptyCellSlots (k : RecordKernelState) (newCell : CellId) : RecordKernelState :=
  { k with
    cell := fun c => if c = newCell then default else k.cell c
  , caps := fun l => if l = newCell then [] else k.caps l
  , delegate := fun c => if c = newCell then none else k.delegate c
  , delegations := fun c => if c = newCell then [] else k.delegations c
  , slotCaveats := fun c => if c = newCell then [] else k.slotCaveats c
  , lifecycle := fun c => if c = newCell then 0 else k.lifecycle c
  , deathCert := fun c => if c = newCell then 0 else k.deathCert c
  , bal := fun c a => if c = newCell then 0 else k.bal c a }

/-- **`createCellIntoAsset` — grow `accounts` by the fresh `newCell` AND reset ALL per-cell indexed
state at `newCell` to born-empty defaults (cell/caps/delegate/delegations/slotCaveats/lifecycle/
deathCert/bal).** The per-asset analog of `EffectsSupply.createCellInto`, over the `bal` ledger rather
than the named `balance` field. The fresh cell is born EMPTY in EVERY asset (dregg1-faithful
`balance == 0`), so it contributes exactly `0` to every `recTotalAsset b`. -/
def createCellIntoAsset (k : RecordKernelState) (newCell : CellId) : RecordKernelState :=
  { bornEmptyCellSlots k newCell with accounts := insert newCell k.accounts }

/-- **`recTotalAsset_insert_fresh` — ACCOUNT-GROWTH IS CONSERVATION-NEUTRAL (PROVED).** Growing
`accounts` by a FRESH `newCell` while resetting its `bal` column leaves `recTotalAsset k b` UNCHANGED
for EVERY asset `b`. NON-VACUOUS: the conclusion is an equality of sums over a STRICTLY LARGER index set
(`insert newCell k.accounts`) — it asserts the fresh cell contributes EXACTLY `0` (not that `accounts`
is unchanged: it genuinely grew). The fresh term is `0` because the `bal`-reset wrote it `0`; every OLD
cell is unchanged because `c ≠ newCell` (`hfresh`). Mirrors `EffectsSupply.createCellInto_recTotal`:
`Finset.sum_insert hfresh` for the fresh term + `Finset.sum_congr` for the old cells. Without the
`bal`-reset, a re-inserted previously-credited id would make this FALSE (the supply-amplification hole),
so the reset is load-bearing. -/
theorem recTotalAsset_insert_fresh (k : RecordKernelState) (newCell : CellId) (b : AssetId)
    (hfresh : newCell ∉ k.accounts) :
    recTotalAsset (createCellIntoAsset k newCell) b = recTotalAsset k b := by
  unfold recTotalAsset createCellIntoAsset bornEmptyCellSlots
  rw [Finset.sum_insert hfresh]
  -- the fresh cell's reset column is `0` (the structure projection beta-reduces the `if`):
  simp only [if_pos, zero_add]
  -- every OLD cell is unchanged (`c ≠ newCell`):
  apply Finset.sum_congr rfl
  intro c hc
  have hcne : c ≠ newCell := fun heq => hfresh (heq ▸ hc)
  simp only [if_neg hcne]

/-- **`createCellIntoAsset_grows_accounts` — the GROWTH has teeth (PROVED).** After `createCellIntoAsset`,
the new cell IS a live account: `newCell ∈ accounts`. Witnesses that the neutrality theorem is NOT a
no-op — the index set genuinely grew. -/
theorem createCellIntoAsset_grows_accounts (k : RecordKernelState) (newCell : CellId) :
    newCell ∈ (createCellIntoAsset k newCell).accounts := by
  unfold createCellIntoAsset; exact Finset.mem_insert_self _ _

/-- **`createCellIntoAsset_born_empty_caps` — the fresh id's cap slot is empty (PROVED).** -/
theorem createCellIntoAsset_born_empty_caps (k : RecordKernelState) (newCell : CellId) :
    (createCellIntoAsset k newCell).caps newCell = [] := by
  dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_pos]

/-! ## Whole-execution conservation (the userspace-program layer). -/

/-- The record kernel as an `Execution.System`: a step is any committed record turn. -/
def recKernelSystem : System where
  Config := RecordKernelState
  Step k k' := ∃ turn, recKExec k turn = some k'

/-- **Conservation across an ENTIRE record-kernel run — PROVED** (`Execution.invariant_run`
lifting `recKExec_conserves`); the record-cell analog of `Kernel.kernel_run_conserves`. -/
theorem recKernel_run_conserves {k k' : RecordKernelState} (hrun : Run recKernelSystem k k') :
    recTotal k' = recTotal k := by
  have hpres : StepInvariant recKernelSystem (fun c => recTotal c = recTotal k) := by
    intro a b ha hstep
    obtain ⟨turn, hturn⟩ := hstep
    rw [recKExec_conserves a b turn hturn]; exact ha
  exact invariant_run hpres hrun rfl

/-! ## The four `StepInv` conjuncts over the record cell (the chained record kernel). -/

/-- The record kernel state plus its **receipt chain** (the append-only audit log). The record-cell
analog of `StepComplete.ChainedState`. -/
structure RecChainedState where
  kernel : RecordKernelState
  log    : List Turn

/-- The chained record executor: run `recKExec`, and on success extend the receipt chain. -/
def recCexec (s : RecChainedState) (t : Turn) : Option RecChainedState :=
  match recKExec s.kernel t with
  | some k' => some { kernel := k', log := t :: s.log }
  | none    => none

/-- **The full per-step invariant over the record cell** — all four `StepInv` conjuncts
(Conservation over the `balance` field ∧ Authority ∧ ChainLink ∧ ObsAdvance). The record-cell
realization of `StepComplete.fullStepInv`. -/
def recFullStepInv (s : RecChainedState) (t : Turn) (s' : RecChainedState) : Prop :=
  recTotal s'.kernel = recTotal s.kernel ∧
  authorizedB s.kernel.caps t = true ∧
  s'.log = t :: s.log ∧
  s'.log.length = s.log.length + 1

/-- **`recCexec_attests` — the record kernel is STEP-COMPLETE (PROVED).** Every committed chained
record-cell step attests the FULL `StepInv` over the content-addressed cell: Conservation (of the
`balance` field) ∧ Authority ∧ ChainLink ∧ ObsAdvance. This is `StepComplete.cexec_attests` lifted
to the record cell-state — step-completeness holds BY CONSTRUCTION over the concrete cell, not just
the toy scalar. -/
theorem recCexec_attests {s s' : RecChainedState} {t : Turn} (h : recCexec s t = some s') :
    recFullStepInv s t s' := by
  unfold recCexec at h
  split at h
  · next k' heq =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, rfl, rfl⟩
    · exact recKExec_conserves s.kernel k' t heq           -- Conservation (balance field)
    · exact recKExec_authorized s.kernel k' t heq          -- Authority
  · exact absurd h (by simp)

/-- The chained record kernel as a transition system. -/
def recChainedSystem : System where
  Config := RecChainedState
  Step s s' := ∃ t, recCexec s t = some s'

/-- **Soundness along any record-cell execution — PROVED.** Any state-predicate `Good` preserved by
every step that attests `recFullStepInv` holds at every reachable configuration of the whole chained
record-kernel execution — `Boundary.stepComplete_preserves` realized for the record cell. -/
theorem recChained_sound (Good : RecChainedState → Prop)
    (hpres : ∀ s t s', Good s → recFullStepInv s t s' → Good s')
    {s s' : RecChainedState} (hrun : Run recChainedSystem s s') (hs : Good s) : Good s' := by
  refine invariant_run (S := recChainedSystem) (I := Good) ?_ hrun hs
  intro a b ha hstep
  obtain ⟨t, ht⟩ := hstep
  exact hpres a t b ha (recCexec_attests ht)

/-- **Conservation of the `balance` field across the entire record-cell execution — PROVED**
(the headline instance of `recChained_sound`). -/
theorem recChained_run_conserves {s s' : RecChainedState} (hrun : Run recChainedSystem s s') :
    recTotal s'.kernel = recTotal s.kernel := by
  have : (fun c => recTotal c.kernel = recTotal s.kernel) s' :=
    recChained_sound (fun c => recTotal c.kernel = recTotal s.kernel)
      (by intro a b _ ha hinv; rw [hinv.1]; exact ha) hrun rfl
  exact this

/-! ## §SINGLE-CELL MOVES — the one-cell credit/debit primitives.

`recKExec` above is the balance-CONSERVING two-cell transfer (Σδ = 0). These are the SINGLE-cell
named-field credit/debit moves (dregg1's `set_balance(old ± amount)`) — the building blocks the
coordinated cross-forest bridge (`CoordinatedForestGLift`/`CoordinatedTurnEmit`) still uses. F1b:
the kernel escrow holding-store that used to ride on them is GONE — escrow/obligation/bridge-LFC
semantics live in factory cells (`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`), where
the parked value sits in the factory cell's OWN `bal` column. -/

/-- **Single-cell credit** — add `amt` to one cell's `balance` field, leaving all other cells and the
side-tables untouched. The named-field realization of dregg1's `set_balance(old + amount)`
(`apply.rs:1964`/`:2035`) — a SINGLE-cell move, NOT a two-cell transfer. -/
def recCredit (cell : CellId → Value) (c : CellId) (amt : ℤ) : CellId → Value :=
  fun x => if x = c then setBalance (cell x) (balOf (cell x) + amt) else cell x

/-- **Single-cell debit** — subtract `amt` from one cell's `balance` field. dregg1's
`set_balance(old − amount)` (`apply.rs:1766`) at create — a SINGLE-cell move. -/
def recDebit (cell : CellId → Value) (c : CellId) (amt : ℤ) : CellId → Value :=
  fun x => if x = c then setBalance (cell x) (balOf (cell x) - amt) else cell x

/-- A single-cell credit shifts the cell-ledger total by `+amt` (the live account `c`'s `balance`
rises by `amt`; every other account is untouched). PROVED. -/
theorem recCredit_recTotal (acc : Finset CellId) (cell : CellId → Value) (c : CellId) (amt : ℤ)
    (hc : c ∈ acc) :
    (∑ x ∈ acc, balOf (recCredit cell c amt x)) = (∑ x ∈ acc, balOf (cell x)) + amt := by
  have key : (∑ x ∈ acc, balOf (recCredit cell c amt x)) - (∑ x ∈ acc, balOf (cell x)) = amt := by
    rw [← Finset.sum_sub_distrib]
    have hg : ∀ x ∈ acc, balOf (recCredit cell c amt x) - balOf (cell x)
        = (if x = c then amt else 0) := by
      intro x _
      unfold recCredit
      by_cases hx : x = c
      · rw [if_pos hx, setBalance_balOf, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    rw [Finset.sum_congr rfl hg, sum_indicator acc c amt hc]
  omega

/-- A single-cell debit shifts the cell-ledger total by `−amt`. PROVED. -/
theorem recDebit_recTotal (acc : Finset CellId) (cell : CellId → Value) (c : CellId) (amt : ℤ)
    (hc : c ∈ acc) :
    (∑ x ∈ acc, balOf (recDebit cell c amt x)) = (∑ x ∈ acc, balOf (cell x)) - amt := by
  have key : (∑ x ∈ acc, balOf (recDebit cell c amt x)) - (∑ x ∈ acc, balOf (cell x)) = -amt := by
    rw [← Finset.sum_sub_distrib]
    have hg : ∀ x ∈ acc, balOf (recDebit cell c amt x) - balOf (cell x)
        = (if x = c then (-amt) else 0) := by
      intro x _
      unfold recDebit
      by_cases hx : x = c
      · rw [if_pos hx, setBalance_balOf, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    rw [Finset.sum_congr rfl hg, sum_indicator acc c (-amt) hc]
  omega


/-! ### §NULLIFIER — the spent-note SET (faithful to dregg1's `note_nullifiers`, `apply.rs:941`).

dregg1's `apply_note_spend` does NOT set a `"nullifier_spent"=1` scalar field. It inserts the
nullifier into an off-ledger SET `self.note_nullifiers` with DOUBLE-SPEND REJECTION: if the nullifier
is already present, the turn fails-closed ("double-spend: nullifier already in note_nullifiers set",
`apply.rs:945`). We model that set faithfully and prove no nullifier can be spent twice. -/

/-- **`noteSpendNullifier` (executable, fail-closed).** Insert `nf` into the nullifier set IF it is
NOT already present; reject (fail-closed `none`) on a double-spend (`apply.rs:942`). The crypto
(STARK spending proof + nullifier derivation) is the §8 portal carried at the effect layer; here we
model the ledger-side double-spend gate, which is what prevents replay. -/
def noteSpendNullifier (k : RecordKernelState) (nf : Nat) : Option RecordKernelState :=
  if nf ∈ k.nullifiers then none
  else some { k with nullifiers := nf :: k.nullifiers }

/-- **`note_no_double_spend` — PROVED.** A nullifier already in the spent set CANNOT be spent again:
`noteSpendNullifier` fails-closed. This is the real anti-replay invariant (the SET prevents it), NOT
a scalar flag. -/
theorem note_no_double_spend (k : RecordKernelState) (nf : Nat) (h : nf ∈ k.nullifiers) :
    noteSpendNullifier k nf = none := by
  unfold noteSpendNullifier; rw [if_pos h]

/-- **`note_spend_inserts` — PROVED.** A committed `noteSpendNullifier` actually inserts `nf` into the
set (so a SUBSEQUENT spend of the same `nf` is rejected by `note_no_double_spend`). -/
theorem note_spend_inserts {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : nf ∈ k'.nullifiers := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; subst h; simp

/-- **`note_spend_then_reject` — PROVED (the composed anti-replay).** After a committed spend of `nf`,
a second spend of the SAME `nf` on the resulting state fails-closed. Double-spend is impossible. -/
theorem note_spend_then_reject {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : noteSpendNullifier k' nf = none :=
  note_no_double_spend k' nf (note_spend_inserts h)

/-! ## §PER-ASSET SINGLE-CELL MOVE — `recBalCreditCell` on the GENUINE per-asset `bal` ledger.

The single-cell, single-asset credit/debit primitive (dregg1's `set_balance`, at a NAMED asset column
rather than the scalar field). F1b: the per-asset escrow lifecycle that used to ride on it
(`createEscrowKAsset`/`releaseEscrowKAsset`/`refundEscrowKAsset`, the bridge-LFC twins, and the
off-ledger held-sum measure `escrowHeldAsset`/`recTotalAsset`) is GONE — those guarantees
live in the factory contracts (`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`), where the
parked value sits in the factory cell's OWN `bal` column and the per-asset conserved measure is the
plain cell-sum `recTotalAsset`. -/

/-- **`recBalCreditCell` — single-cell, single-asset credit on the per-asset `bal` ledger.** Add `amt`
to cell `c`'s asset `a` column, leaving every other (cell, asset) pair literally untouched. The
per-asset analog of `recCredit` (which moved the scalar `balance` FIELD); `recBalCreditCell c a (-amt)`
is the per-asset DEBIT (dregg1's `set_balance`, but at a NAMED asset column rather than the scalar
field). Lives HERE in `RecordKernel` (upstream of both `TurnExecutorFull` and `EffectsPaired`) so the
executed dispatch can use it; it is definitionally the same shape as `TurnExecutorFull.recBalCredit`. -/
def recBalCreditCell (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun x b => if x = c ∧ b = a then bal x b + amt else bal x b

/-- **The per-asset single-cell credit delta — PROVED.** A `recBalCreditCell c a amt` raises asset
`a`'s supply by `amt` (when `c` is live) and leaves EVERY OTHER asset literally untouched. The
per-asset analog of `recCredit_recTotal`, reusing `sum_indicator`. -/
theorem recBalCreditCell_recTotalAsset (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (c : CellId) (a : AssetId) (amt : ℤ) (hc : c ∈ acc) (b : AssetId) :
    (∑ x ∈ acc, recBalCreditCell bal c a amt x b)
      = (∑ x ∈ acc, bal x b) + (if b = a then amt else 0) := by
  by_cases hb : b = a
  · rw [if_pos hb]
    have key : (∑ x ∈ acc, recBalCreditCell bal c a amt x b) - (∑ x ∈ acc, bal x b) = amt := by
      rw [← Finset.sum_sub_distrib]
      have hg : ∀ x ∈ acc, recBalCreditCell bal c a amt x b - bal x b = (if x = c then amt else 0) := by
        intro x _
        unfold recBalCreditCell
        by_cases hx : x = c
        · rw [if_pos ⟨hx, hb⟩, if_pos hx]; ring
        · rw [if_neg (by rintro ⟨h, _⟩; exact hx h), if_neg hx]; ring
      rw [Finset.sum_congr rfl hg, sum_indicator acc c amt hc]
    omega
  · rw [if_neg hb, add_zero]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold recBalCreditCell; rw [if_neg (by rintro ⟨_, h⟩; exact hb h)]

/-- `bal_neutral` — the balance-NEUTRAL finisher (the fourth effect-arm combinator; the other
three live in `Dregg2/Tactics.lean`). A caps/log-only edit leaves the per-asset conserved measure
`recTotalAsset` (the `bal`-ledger cell-sum) FIXED: unfold the measure and close by `ring`. Defined
HERE (not in the generic `Tactics.lean`) so macro hygiene resolves the measure's simp-lemma names
against THIS scope. For arms that first need their step def unfolded, do that simp beforehand
(`simp only [recKRevokeTarget] …; bal_neutral`). -/
macro "bal_neutral" : tactic =>
  `(tactic| (simp only [recTotalAsset]; ring))

/-- **`cellLifecycleLive k c` — the kernel-level lifecycle-LIVENESS predicate.**
Does cell `c`'s lifecycle admit new effects (a credit/debit landing on it)? `true` only for the Live
discriminant (`0`); a Sealed (`1`) or Destroyed (`3`) cell is fail-closed REJECTED. This is the
kernel-twin of `TurnExecutorFull.acceptsEffects`/`EffectsState.cellLive` (both read the SAME `lifecycle`
side-table and check `== 0`), defined HERE in `RecordKernel` (imported BY `TurnExecutorFull`, so
kernel-level gates can use it without a cycle). `acceptsEffects k c = cellLifecycleLive k c`
definitionally (`acceptsEffects_eq_cellLifecycleLive`), so the two are interchangeable. -/
def cellLifecycleLive (k : RecordKernelState) (c : CellId) : Bool := k.lifecycle c == 0

/-! ### §NOTE-CREATE — the grow-only COMMITMENT SET (faithful to dregg1's `apply_note_create`).

dregg1's `apply_note_create` inserts a fresh Pedersen commitment into the off-ledger commitment tree;
the §8 crypto (range proof on the hidden value) is a `CryptoPortal` carried at the effect layer. The
note's hidden value's ASSET is OUT OF SCOPE here (behind the CryptoPortal) — `noteCreate` is
bal-NEUTRAL: it grows the `commitments` SET only, NOT `bal`/`nullifiers`. (A fresh commitment is
always fresh, so — unlike `noteSpend`'s double-spend gate — there is no rejection; the grow-only
insert is the dual of the nullifier set.) -/

/-- **`noteCreateCommitment` (executable)** — insert a fresh note commitment `cm` into the off-ledger
commitment SET (the grow-only dual of `noteSpendNullifier`). bal-NEUTRAL: it touches NEITHER `bal` NOR
`nullifiers`. Always commits (a fresh commitment cannot conflict). -/
def noteCreateCommitment (k : RecordKernelState) (cm : Nat) : RecordKernelState :=
  { k with commitments := cm :: k.commitments }

/-- **`noteCreate_inserts` — PROVED.** A `noteCreateCommitment` actually inserts `cm` into the
commitment set. -/
theorem noteCreate_inserts (k : RecordKernelState) (cm : Nat) :
    cm ∈ (noteCreateCommitment k cm).commitments := by
  unfold noteCreateCommitment; simp

/-- **`noteCreate_recTotalAsset` — PROVED (bal-NEUTRALITY).** A `noteCreateCommitment` leaves
`recTotalAsset b` UNCHANGED for EVERY asset `b`: it grows only the commitment SET, never the `bal`
ledger. -/
theorem noteCreate_recTotalAsset (k : RecordKernelState) (cm : Nat) (b : AssetId) :
    recTotalAsset (noteCreateCommitment k cm) b = recTotalAsset k b := rfl

/-! ## §SWISS — the kernel-level CapTP export/enliven/handoff/GC swiss-table transitions (Wave-8 de-THIN).

The swiss-table side-table transitions, each FAIL-CLOSED exactly where dregg1 fails closed: export
INSERTS a fresh swiss→cap entry with `refcount := 1` (rejecting a duplicate swiss number AND a rights
amplification — the exported tier must be `⊆` the exporter's own `held` rights, `apply.rs:3917`); enliven
LOOKS UP the swiss number (fail-closed if absent, `apply.rs:3955`), VALIDATES the bearer's claimed rights
are `⊆` the entry's exported rights (the non-amplification gate, `apply.rs:3999`), and BUMPS the refcount
(a new live reference); handoff binds a 3-vat introduce CERT to the entry + bumps the refcount
(`apply.rs:4109`); drop DECREMENTS the refcount and GCs the entry when it hits 0 (rejecting a drop on a
zero/absent entry, `apply.rs:4051`). ALL FOUR are balance-NEUTRAL — they touch ONLY `swiss`, never
`bal` (CapTP moves references, not balance). -/

/-- **`heldAuths` — the exporter's REAL committed rights, read from the executed state.** The authority
the `exporter` cell GENUINELY holds is the union of the auths conferred by every cap in its committed
c-list `k.caps exporter` (`capAuthConferred` per cap, `apply.rs` reads the holder's own permission tier).
This is adversary-UNCONTROLLABLE: it is a function of committed kernel state, NOT a free action/proof
parameter, so the export non-amplification gate cannot be inflated by a lying prover. -/
def heldAuths (k : RecordKernelState) (exporter : CellId) : List Auth :=
  (k.caps exporter).flatMap capAuthConferred

/-- **`swissExportK`** — INSERT a fresh swiss-table entry: swiss number `sw` → (`target`, `rights`),
exported by `exporter`, with `refcount := 1` (the bearer holds one live ref) and no bound cert.
Fail-closed if the swiss number is already in use (no duplicate export) OR the exported `rights` are NOT
`⊆` the exporter's REAL committed rights `heldAuths k exporter` (amplification denied, `apply.rs:3917`).

**SOUNDNESS FIX (capability-amplification hole closed):** the bound is now read from the
adversary-UNCONTROLLABLE committed state `k.caps exporter` — NOT a caller/prover-supplied `held`
parameter. A bare-authority actor can no longer mint a sturdy ref carrying rights its cell never held by
claiming `held = everything`; the exported `rights` must be `⊆` the rights the exporter GENUINELY holds.
balance-NEUTRAL. -/
def swissExportK (k : RecordKernelState) (sw : Nat) (exporter target : CellId) (rights : List Auth) :
    Option RecordKernelState :=
  match findSwiss k.swiss sw with
  | some _ => none
  | none   =>
      if rightsNarrowerOrEqual rights (heldAuths k exporter) then
        some { k with swiss := { swiss := sw, exporter := exporter, target := target,
                                 rights := rights, refcount := 1, cert := none } :: k.swiss }
      else none

/-- **`swissEnlivenK`** — VALIDATE a presented swiss number `sw` against the committed swiss-table and
grant a live reference. Fail-closed if the swiss number is ABSENT (`apply.rs:3955`) OR the bearer's
`claimed` rights are NOT `⊆` the entry's exported `rights` (the non-amplification gate, `apply.rs:3999`).
On success BUMPS the entry's `refcount` (a new live reference). balance-NEUTRAL. -/
def swissEnlivenK (k : RecordKernelState) (sw : Nat) (claimed : List Auth) :
    Option RecordKernelState :=
  match findSwiss k.swiss sw with
  | none   => none
  | some e =>
      if rightsNarrowerOrEqual claimed e.rights then
        some { k with swiss := replaceSwiss k.swiss sw { e with refcount := e.refcount + 1 } }
      else none

/-- **`swissHandoffK`** — bind a 3-vat introduce CERT `certHash` to the swiss entry `sw` and grant the
recipient a live reference (`apply.rs:4109`). Fail-closed if the swiss number is ABSENT. On success binds
`cert := some certHash` AND BUMPS the `refcount` (the recipient's new live ref). balance-NEUTRAL. -/
def swissHandoffK (k : RecordKernelState) (sw certHash : Nat) :
    Option RecordKernelState :=
  match findSwiss k.swiss sw with
  | none   => none
  | some e =>
      let e' : SwissRecord := { e with cert := some certHash, refcount := e.refcount + 1 }
      some { k with swiss := replaceSwiss k.swiss sw e' }

/-- **`swissDropK`** — GC a reference: DECREMENT the swiss entry `sw`'s `refcount`. Fail-closed if the
swiss number is ABSENT OR the `refcount` is already `0` (`apply.rs:4051`, "refcount is already zero").
When the decremented refcount hits `0` the entry is REMOVED (GC'd from the table); otherwise the entry
stays with the lower count. balance-NEUTRAL. -/
def swissDropK (k : RecordKernelState) (sw : Nat) : Option RecordKernelState :=
  match findSwiss k.swiss sw with
  | none   => none
  | some e =>
      if e.refcount = 0 then none
      else if e.refcount - 1 = 0 then
        some { k with swiss := removeSwiss k.swiss sw }
      else
        some { k with swiss := replaceSwiss k.swiss sw { e with refcount := e.refcount - 1 } }

/-! ### The swiss-table is balance-NEUTRAL (touches only `swiss`). -/

/-- **`swissExportK_balNeutral` — PROVED.** Export touches only `swiss`, never `bal`. -/
theorem swissExportK_balNeutral {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold swissExportK at h
  cases hf : findSwiss k.swiss sw with
  | some e => simp only [hf] at h; exact absurd h (by simp)
  | none   =>
      simp only [hf] at h
      by_cases hr : rightsNarrowerOrEqual rights (heldAuths k exporter)
      · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissEnlivenK_balNeutral` — PROVED.** Enliven touches only `swiss`. -/
theorem swissEnlivenK_balNeutral {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold swissEnlivenK at h
  cases hf : findSwiss k.swiss sw with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some e =>
      simp only [hf] at h
      by_cases hr : rightsNarrowerOrEqual claimed e.rights
      · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissHandoffK_balNeutral` — PROVED.** Handoff touches only `swiss`. -/
theorem swissHandoffK_balNeutral {k k' : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold swissHandoffK at h
  cases hf : findSwiss k.swiss sw with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some e => simp only [hf, Option.some.injEq] at h; subst h; rfl

/-- **`swissDropK_balNeutral` — PROVED.** Drop (refcount decrement / GC) touches only `swiss`. -/
theorem swissDropK_balNeutral {k k' : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold swissDropK at h
  cases hf : findSwiss k.swiss sw with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some e =>
      simp only [hf] at h
      by_cases hz : e.refcount = 0
      · rw [if_pos hz] at h; exact absurd h (by simp)
      · rw [if_neg hz] at h
        by_cases hone : e.refcount - 1 = 0
        · rw [if_pos hone] at h; simp only [Option.some.injEq] at h; subst h; rfl
        · rw [if_neg hone] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-! ### The REAL mechanism — fail-closed gates + the refcount lifecycle (the de-THIN non-vacuity). -/

/-- **`swissExportK_inserts` — PROVED (export INSERTS a real entry, refcount 1).** A committed export
puts a swiss-table entry for `sw` whose lookup returns the exported (target, rights) with `refcount = 1`.
The de-THIN content a flag could not state. -/
theorem swissExportK_inserts {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') :
    findSwiss k'.swiss sw = some { swiss := sw, exporter := exporter, target := target,
                                   rights := rights, refcount := 1, cert := none } := by
  unfold swissExportK at h
  cases hf : findSwiss k.swiss sw with
  | some e => simp only [hf] at h; exact absurd h (by simp)
  | none   =>
      simp only [hf] at h
      by_cases hr : rightsNarrowerOrEqual rights (heldAuths k exporter)
      · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; subst h
        simp only [findSwiss, List.find?_cons, beq_self_eq_true]
      · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissExportK_amplification_rejects` — PROVED (the NON-AMPLIFICATION gate, fail-closed).** An
export whose declared `rights` are NOT `⊆` the exporter's REAL committed rights `heldAuths k exporter`
is REJECTED — a sturdy ref must not grant authority the exporter never held (`apply.rs:3917`). The bound
is read from adversary-UNCONTROLLABLE committed state, so a lying prover cannot inflate it. The CapTP
soundness gate, NOT `True`. -/
theorem swissExportK_amplification_rejects (k : RecordKernelState) (sw : Nat) (exporter target : CellId)
    (rights : List Auth) (hf : findSwiss k.swiss sw = none)
    (hamp : rightsNarrowerOrEqual rights (heldAuths k exporter) = false) :
    swissExportK k sw exporter target rights = none := by
  simp only [swissExportK, hf]; rw [if_neg (by simp [hamp])]

/-- **`swissExportK_real_held_bounds` — PROVED (the KEYSTONE: the export is bounded by the exporter's REAL
held rights).** A COMMITTED export's declared `rights` are `⊆` the rights the exporter GENUINELY holds in
committed state (`heldAuths k exporter` = ⋃ `capAuthConferred` over `k.caps exporter`). Because this bound
is a function of the EXECUTED state — not a free prover-supplied `held` — the non-amplification guarantee
is REAL: no sturdy ref can carry authority the exporter's c-list never conferred. This is the proof the
capability-amplification hole is CLOSED (the old gate's bound was adversary-controllable). -/
theorem swissExportK_real_held_bounds {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') :
    rightsNarrowerOrEqual rights (heldAuths k exporter) = true := by
  unfold swissExportK at h
  cases hf : findSwiss k.swiss sw with
  | some e => simp only [hf] at h; exact absurd h (by simp)
  | none   =>
      simp only [hf] at h
      by_cases hr : rightsNarrowerOrEqual rights (heldAuths k exporter)
      · exact hr
      · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissExportK_overbroad_rejects` — PROVED (the TEETH, NON-VACUOUS).** An exporter whose committed
c-list confers ONLY `[read]` (a single `endpoint t [read]` cap) that tries to export a ref carrying
`[read, write]` is REJECTED — the OVER-BROAD export (amplification) the OLD `held`-parameter gate would
have ADMITTED (just claim `held = [read, write]`) now FAILS, because `heldAuths` reads the cell's REAL
rights and `write ∉ [read]`. The concrete amplification attempt closed. -/
theorem swissExportK_overbroad_rejects (k : RecordKernelState) (sw : Nat) (exporter target t : CellId)
    (hf : findSwiss k.swiss sw = none) (hcaps : k.caps exporter = [Cap.endpoint t [Auth.read]]) :
    swissExportK k sw exporter target [Auth.read, Auth.write] = none := by
  apply swissExportK_amplification_rejects k sw exporter target [Auth.read, Auth.write] hf
  have hheld : heldAuths k exporter = [Auth.read] := by
    simp only [heldAuths, hcaps, List.flatMap_cons, List.flatMap_nil, capAuthConferred,
      List.append_nil]
  rw [hheld]; decide

/-- **`swissEnlivenK_absent_rejects` — PROVED (the MEMBERSHIP gate, fail-closed).** An enliven of an
ABSENT swiss number is REJECTED (`apply.rs:3955`: validate membership against the committed table). The
look-up-fail-closed a flag-shadow lacks. -/
theorem swissEnlivenK_absent_rejects (k : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (hf : findSwiss k.swiss sw = none) : swissEnlivenK k sw claimed = none := by
  simp only [swissEnlivenK, hf]

/-- **`swissEnlivenK_amplification_rejects` — PROVED (the non-amplification gate, fail-closed).** An
enliven whose CLAIMED rights exceed the entry's exported rights is REJECTED (`apply.rs:3999`). -/
theorem swissEnlivenK_amplification_rejects (k : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (e : SwissRecord) (hf : findSwiss k.swiss sw = some e)
    (hamp : rightsNarrowerOrEqual claimed e.rights = false) :
    swissEnlivenK k sw claimed = none := by
  simp only [swissEnlivenK, hf]; rw [if_neg (by simp [hamp])]

/-- **`findSwiss_swiss_eq` — PROVED.** A found swiss entry has its key equal to the lookup key. -/
theorem findSwiss_swiss_eq {ss : List SwissRecord} {sw : Nat} {e : SwissRecord}
    (hf : findSwiss ss sw = some e) : e.swiss = sw := by
  unfold findSwiss at hf
  induction ss with
  | nil => simp [List.find?] at hf
  | cons hd tl ih =>
      simp only [List.find?_cons] at hf
      by_cases hhd : (hd.swiss == sw) = true
      · simp only [hhd, if_true, Option.some.injEq] at hf; subst hf; simpa using hhd
      · simp only [hhd, Bool.false_eq_true, if_false] at hf; exact ih hf

/-- **`findSwiss_replaceSwiss_self` — PROVED (the side-table read/write law).** If `sw` is present and
the replacement `e'` keeps the swiss number (`e'.swiss = sw`), then looking `sw` up after the replace
returns exactly `e'`. The membership-map read/write law the refcount lifecycle reads off. -/
theorem findSwiss_replaceSwiss_self (ss : List SwissRecord) (sw : Nat) (e e' : SwissRecord)
    (hf : findSwiss ss sw = some e) (hsw : e'.swiss = sw) :
    findSwiss (replaceSwiss ss sw e') sw = some e' := by
  have he'sw : (e'.swiss == sw) = true := by simp [hsw]
  induction ss with
  | nil => simp [findSwiss, List.find?] at hf
  | cons hd tl ih =>
      simp only [findSwiss, List.find?_cons] at hf
      simp only [findSwiss, replaceSwiss, List.map_cons, List.find?_cons]
      by_cases hhd : (hd.swiss == sw) = true
      · simp only [hhd, if_true] at hf ⊢
        simp only [he'sw, if_true]
      · simp only [hhd, Bool.false_eq_true, if_false] at hf ⊢
        simp only [findSwiss, replaceSwiss] at ih
        exact ih hf

/-- **`swissEnlivenK_bumps_refcount` — PROVED (the refcount LIFECYCLE: a live ref is added).** A
committed enliven RAISES the entry's refcount by one (a new live reference). -/
theorem swissEnlivenK_bumps_refcount {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    {e : SwissRecord} (hf : findSwiss k.swiss sw = some e)
    (h : swissEnlivenK k sw claimed = some k') :
    findSwiss k'.swiss sw = some { e with refcount := e.refcount + 1 } := by
  unfold swissEnlivenK at h
  simp only [hf] at h
  by_cases hr : rightsNarrowerOrEqual claimed e.rights
  · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; subst h
    exact findSwiss_replaceSwiss_self k.swiss sw e { e with refcount := e.refcount + 1 } hf
      (by show e.swiss = sw; exact findSwiss_swiss_eq hf)
  · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissDropK_zero_rejects` — PROVED (the GC gate, fail-closed).** A drop on an entry whose refcount
is already `0` is REJECTED (`apply.rs:4051`: "refcount is already zero"). -/
theorem swissDropK_zero_rejects (k : RecordKernelState) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss k.swiss sw = some e) (hz : e.refcount = 0) :
    swissDropK k sw = none := by
  simp only [swissDropK, hf, if_pos hz]

/-- **`findSwiss_removeSwiss_self` — PROVED.** After removing the `sw` entry, looking `sw` up returns
`none` — every surviving entry has `swiss ≠ sw` (the filter dropped exactly the `sw`-matching ones). -/
theorem findSwiss_removeSwiss_self (ss : List SwissRecord) (sw : Nat) :
    findSwiss (removeSwiss ss sw) sw = none := by
  unfold findSwiss removeSwiss
  apply List.find?_eq_none.mpr
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨_, hx2⟩ := hx
  simpa using hx2

/-- **`swissDropK_gc_at_one` — PROVED (the GC: dropping the LAST ref REMOVES the entry).** Dropping a
ref when `refcount = 1` GCs the entry — the subsequent lookup returns `none`. The de-THIN GC content. -/
theorem swissDropK_gc_at_one {k k' : RecordKernelState} {sw : Nat} {e : SwissRecord}
    (hf : findSwiss k.swiss sw = some e) (hone : e.refcount = 1)
    (h : swissDropK k sw = some k') : findSwiss k'.swiss sw = none := by
  unfold swissDropK at h
  simp only [hf] at h
  rw [if_neg (by omega : ¬ e.refcount = 0)] at h
  rw [if_pos (by omega : e.refcount - 1 = 0)] at h
  simp only [Option.some.injEq] at h; subst h
  exact findSwiss_removeSwiss_self k.swiss sw

/-! ## §SWISS runs (`#guard`) — export INSERTS, enliven LOOKS-UP-fail-closed + validates, refcount GCs. -/

/-- A kernel with an EMPTY swiss-table; cell 0 GENUINELY holds `[read, call]` rights — via a real
`endpoint`-cap c-list entry (`capAuthConferred (.endpoint 1 [read, call]) = [read, call]`), so `heldAuths
ksw0 0 = [read, call]`. The export non-amplification gate reads THESE committed rights, not a caller
parameter. -/
def ksw0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.endpoint 1 [Auth.read, Auth.call]] else []
    swiss := [] }

-- The REAL committed rights cell 0 holds, read from the c-list (NOT a caller parameter):
#guard (heldAuths ksw0 0 == [Auth.read, Auth.call])  --  [read, call] — the adversary-uncontrollable bound the export gate uses
-- EXPORT INSERTS: export swiss 42 → target 1 with rights [read] (⊆ REAL-held [read,call]) ⇒ entry present, refcount 1.
#guard ((swissExportK ksw0 42 0 1 [Auth.read]).bind
        (fun k => (findSwiss k.swiss 42).map (fun e => (e.target, e.refcount)))) == some (1, 1)  --  some (1, 1) — INSERTED
-- AMPLIFICATION DENIED on export: exporting [grant] when only [read,call] is REALLY held ⇒ none.
#guard ((swissExportK ksw0 42 0 1 [Auth.grant]).isSome) == false  --  false — amplification denied (grant ∉ real-held)
-- THE TEETH — OVER-BROAD EXPORT REJECTED: an exporter REALLY holding only [read,call] CANNOT mint a ref
-- carrying [read,write] — the amplification the OLD caller-supplied-`held` gate would have ADMITTED.
#guard ((swissExportK ksw0 42 0 1 [Auth.read, Auth.write]).isSome) == false  --  false — write ∉ real-held ⇒ REJECTED
-- CONTRAST — within-rights export COMMITS: [read,call] ⊆ real-held [read,call] ⇒ inserted.
#guard ((swissExportK ksw0 42 0 1 [Auth.read, Auth.call]).bind
        (fun k => (findSwiss k.swiss 42).map (·.rights))) == some [Auth.read, Auth.call]  --  some [read, call] — within rights, COMMITS
-- A cell holding NOTHING (caps = []) cannot export ANY non-empty ref (heldAuths = []):
#guard ((swissExportK ksw0 99 5 1 [Auth.read]).isSome) == false  --  false — cell 5 holds no caps ⇒ real-held [] ⇒ REJECTED
-- ENLIVEN LOOKS-UP-fail-closed: enliven an ABSENT swiss number ⇒ none.
#guard ((swissEnlivenK ksw0 99 [Auth.read]).isSome) == false  --  false — absent ⇒ none (membership gate)
-- ENLIVEN BUMPS refcount: export then enliven (claiming ⊆ rights) ⇒ refcount 1 → 2.
#guard ((((swissExportK ksw0 42 0 1 [Auth.read]).bind
        (fun k => swissEnlivenK k 42 [Auth.read]))).bind
        (fun k => (findSwiss k.swiss 42).map (·.refcount))) == some 2  --  some 2 — a new live reference
-- ENLIVEN amplification denied: claiming [grant] against an entry exporting only [read] ⇒ none.
#guard (((swissExportK ksw0 42 0 1 [Auth.read]).bind
        (fun k => swissEnlivenK k 42 [Auth.grant])).isSome) == false  --  false — claim exceeds export
-- HANDOFF binds the cert + bumps refcount: export then handoff cert 7 ⇒ cert = some 7, refcount 2.
#guard (((swissExportK ksw0 42 0 1 [Auth.read]).bind
        (fun k => swissHandoffK k 42 7)).bind
        (fun k => (findSwiss k.swiss 42).map (fun e => (e.cert, e.refcount)))) == some (some 7, 2)  --  some (some 7, 2)
-- DROP GCs at zero: export (refcount 1) then drop ⇒ entry REMOVED (refcount hit 0 ⇒ GC).
#guard (((swissExportK ksw0 42 0 1 [Auth.read]).bind
        (fun k => swissDropK k 42)).map (fun k => (findSwiss k.swiss 42).isSome)) == some false  --  some false — GC'd
-- DROP fail-closed at zero: a 2nd drop after GC ⇒ none (absent).
#guard (((swissExportK ksw0 42 0 1 [Auth.read]).bind
        (fun k => (swissDropK k 42).bind (fun k => swissDropK k 42))).isSome) == false  --  false
-- balance-NEUTRAL: the combined measure is UNTOUCHED by export (and the rest).
#guard ((swissExportK ksw0 42 0 1 [Auth.read]).map (fun k => recTotalAsset k 0)) == some 0  --  some 0

#assert_axioms swissExportK_inserts
#assert_axioms swissExportK_amplification_rejects
#assert_axioms swissExportK_real_held_bounds
#assert_axioms swissExportK_overbroad_rejects
#assert_axioms swissEnlivenK_absent_rejects
#assert_axioms swissEnlivenK_amplification_rejects
#assert_axioms swissEnlivenK_bumps_refcount
#assert_axioms swissDropK_zero_rejects
#assert_axioms swissDropK_gc_at_one
#assert_axioms swissExportK_balNeutral
#assert_axioms swissEnlivenK_balNeutral
#assert_axioms swissHandoffK_balNeutral
#assert_axioms swissDropK_balNeutral

/-! ## §NOTE runs (`#eval`) — the commitment/nullifier sets move; double-spend fail-closed. -/

/-- A 2-cell, 2-asset ledger fixture: cell 0 holds 100 of asset 1 (and 0 of asset 0); cell 1 holds
0 of everything. -/
def res0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

-- noteCreate round-trip + noteSpend independence; double-spend fail-closed.
#guard ((noteCreateCommitment res0 42).commitments) == [42]  --  [42]
#guard ((noteSpendNullifier res0 7).map (fun k => k.nullifiers)) == some [7]  --  some [7]
#guard (((noteSpendNullifier res0 7).bind (fun k => noteSpendNullifier k 7)).isSome) == false  --  false

/-! ## Axiom-hygiene tripwires — pin the re-proved keystones over the content-addressed cell. -/

#assert_axioms setBalance_balOf
#assert_axioms recTransfer_balanceSum_conserve
#assert_axioms recKExec_conserves
#assert_axioms recKExec_authorized
#assert_axioms recKExec_unauthorized_fails
#assert_axioms recKExec_frame
#assert_axioms recKernel_run_conserves
#assert_axioms recCexec_attests
#assert_axioms recChained_sound
#assert_axioms recChained_run_conserves
-- The faithful escrow holding-store + nullifier-set keystones:
#assert_axioms recCredit_recTotal
#assert_axioms recDebit_recTotal
#assert_axioms note_no_double_spend
#assert_axioms note_spend_inserts
#assert_axioms note_spend_then_reject
-- The per-asset CONSERVATION_VECTOR keystones (FILL 1) over the REAL executable state + gate:
#assert_axioms recTransferBal_sum_conserve_moved
#assert_axioms recTransferBal_untouched
#assert_axioms recKExecAsset_conserves_per_asset
#assert_axioms recKExecAsset_authorized
#assert_axioms recKExecAsset_unauthorized_fails
#assert_axioms recKExecAsset_no_cross_asset_leak
-- The per-asset COMBINED escrow measure + note-commitment keystones (META-FILL C):
#assert_axioms recBalCreditCell_recTotalAsset
#assert_axioms noteCreate_inserts
#assert_axioms noteCreate_recTotalAsset

/-! ## It runs (`#eval`) — an account cell as a record. -/

/-- Cell 0's record: balance 100, nonce 0. Cell 1's record: balance 5. -/
def rs0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 0)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else .record [("balance", .int 0)]
    caps := fun _ => [] }

/-- Actor 0 transfers 30 to cell 1 (owns src 0). -/
def rt1 : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
/-- Actor 2 attempts the same — unauthorized. -/
def rtBad : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }

#guard ((recKExec rs0 rt1).isSome)  --  true
#guard ((recKExec rs0 rtBad).isSome) == false  --  false
#guard ((recKExec rs0 rt1).map recTotal) == some 105  --  some 105 (conserved: 70 + 35)
#guard (recTotal rs0) == 105  --  105
-- The non-balance field (`nonce`) survives the transfer on the content-addressed record:
#guard ((recKExec rs0 rt1).map (fun k => (k.cell 0).scalar "nonce")) == some (some 0)  --  some (some 0)
#guard ((recKExec rs0 rt1).map (fun k => balOf (k.cell 0))) == some 70  --  some 70

/-! ### §MULTI-ASSET runs (`#eval`) — the per-asset ledger conserves each asset class. -/

/-- A 2-cell, 2-asset ledger: cell 0 holds 100 of asset 0 and 7 of asset 1; cell 1 holds 5 of
asset 0. (The `cell`/`caps` carry trivially; `bal` is the genuine per-asset ledger.) -/
def rms0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

#guard (recTotalAsset rms0 0) == 105  --  105 (asset 0 supply)
#guard (recTotalAsset rms0 1) == 7  --  7   (asset 1 supply)
#guard ((recKExecAsset rms0 rt1 0).map (fun k => recTotalAsset k 0)) == some 105  --  some 105 (asset 0 conserved)
#guard ((recKExecAsset rms0 rt1 0).map (fun k => recTotalAsset k 1)) == some 7  --  some 7   (asset 1 UNTOUCHED)
#guard ((recKExecAsset rms0 rtBad 0).isSome) == false  --  false   (unauthorized)
-- moving asset 0 cannot inflate asset 1's supply — the scalar-laundering attack is unrepresentable:
#guard ((recKExecAsset rms0 rt1 0).map (fun k => (k.bal 0 0, k.bal 0 1, k.bal 1 0, k.bal 1 1))) == some (70, 7, 35, 0)  -- some (70, 7, 35, 0)

/-! ## §VALUE-UNIFY — `ExactConservation`: THE per-asset value law of the kernel (W1, DREGG3 R2).

The R2 probe (`Dregg2/Substrate/IssuerSupplyProbe.lean`, standalone) established the issuer-supply
value law: `AssetId := issuer CellId`, the issuer carries −supply in a negative-capable well, and
conservation is `∀ a, Σ_{c ∈ accounts} bal c a = 0` EXACTLY — no modulo-burn, no bridge-outflow
exemption, no mint inflation. `Substrate/IssuerLedger.lean` promoted it to the canonical forward
model. THIS section lands the law in the REAL kernel (in the anchor, over the real step functions).

F1b COLLAPSED the transitional form: the kernel escrow holding-store is GONE, so the law is the PURE
cell-sum — NO off-ledger term, NO exemptions. Escrow/obligation/bridge-LFC value parks in factory
cells' OWN `bal` columns (`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`), covered by the
SAME sum; the bridge outflow dies in the bridge cell's pot column (the `BridgeCell` contract), which
is exactly the S3 pot-cell ending the old transitional doc promised.

Mint/burn-as-issuer-moves land beside the executor (`Dregg2/Exec/IssuerMove.lean`); the per-asset fee
quadruple lands on the turn wrapper (`Dregg2/Circuit/Argus/Turn.lean §6'`); the E4 shielded
value-binding lands in `Dregg2/Exec/ShieldedValue.lean`. -/

/-- **THE VALUE LAW (W1).** Per asset: the cell-ledger sum is 0. The issuer of each asset is an
ordinary live account whose well runs NEGATIVE by exactly the circulating supply
(`IssuerSupplyProbe.issuerView_exact` proves the issuer-supply view satisfies this BY CONSTRUCTION).
F1b: the transitional off-ledger escrow term is GONE — value formerly parked in the kernel
holding-store lives in factory cells' own `bal` columns, which this SAME sum covers. -/
def ExactConservation (k : RecordKernelState) : Prop :=
  ∀ a : AssetId, recTotalAsset k a = 0

/-- **GENESIS is exact.** Any state with the empty `bal` ledger satisfies the law — `Σ 0 = 0` at
every asset. Live accounts (issuers, pots, users) may already exist; only value must not. -/
theorem genesis_exactConservation (k : RecordKernelState) (hbal : k.bal = fun _ _ => 0) :
    ExactConservation k := by
  intro a
  unfold recTotalAsset
  rw [hbal]
  simp

/-- **Gate + shape of a committed per-asset transfer (the public peel).** A committed
`recKExecAsset` proves its full admission conjunction AND pins the post-state to exactly the
`recTransferBal` write on `bal` (every other component untouched). The bridge every downstream
value-law proof reuses. -/
theorem recKExecAsset_committed {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') :
    (authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts)
    ∧ k' = { k with bal := recTransferBal k.bal t.src t.dst a t.amt } := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- Shape of a committed per-asset transfer (gate-peeled): the post-state is the `recTransferBal`
write on `bal`, every other component untouched. -/
theorem recKExecAsset_shape {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') :
    k' = { k with bal := recTransferBal k.bal t.src t.dst a t.amt } :=
  (recKExecAsset_committed h).2

/-- **TRANSFER preserves the value law** — instantiates `recKExecAsset_conserves_per_asset` (the
per-asset keystone): the moved column's debit/credit cancel; every other column is untouched. -/
theorem recKExecAsset_preserves_exact {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') (hex : ExactConservation k) : ExactConservation k' := by
  intro b
  rw [recKExecAsset_conserves_per_asset k k' t a h b]
  exact hex b

/-- **FRESH-CELL CREATION preserves the value law** — instantiates `recTotalAsset_insert_fresh`
(account-growth neutrality). Creating issuer cells / pot cells / user cells before circulation keeps
the invariant; born-empty is load-bearing. -/
theorem createCellIntoAsset_preserves_exact (k : RecordKernelState) (newCell : CellId)
    (hfresh : newCell ∉ k.accounts) (hex : ExactConservation k) :
    ExactConservation (createCellIntoAsset k newCell) := by
  intro b
  rw [recTotalAsset_insert_fresh k newCell b hfresh]
  exact hex b


/-- **NOTE CREATE preserves the value law** — the commitment insert is bal-NEUTRAL
(`noteCreate_recTotalAsset`). -/
theorem noteCreateCommitment_preserves_exact (k : RecordKernelState) (cm : Nat)
    (hex : ExactConservation k) : ExactConservation (noteCreateCommitment k cm) := fun b => by
  rw [noteCreate_recTotalAsset k cm b]
  exact hex b

/-- **NOTE SPEND (nullifier insert) preserves the value law** — it touches only `nullifiers`. -/
theorem noteSpendNullifier_preserves_exact {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') (hex : ExactConservation k) :
    ExactConservation k' := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h
    exact absurd h (by simp)
  · rw [if_neg hin] at h
    simp only [Option.some.injEq] at h
    subst h
    exact hex


/-! ### §VALUE-UNIFY — axiom hygiene. -/

#assert_axioms genesis_exactConservation
#assert_axioms recKExecAsset_preserves_exact
#assert_axioms createCellIntoAsset_preserves_exact
#assert_axioms noteCreateCommitment_preserves_exact
#assert_axioms noteSpendNullifier_preserves_exact


end Dregg2.Exec
