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

/-! ### The OFF-LEDGER holding-store: the escrow side-table (dregg1's `self.escrows`).

dregg1's `apply_create_escrow` (`turn/src/executor/apply.rs:1674`) does NOT do a balance-conserving
two-cell transfer. It does a SINGLE-cell debit (`set_balance(creator − amount)`, :1766) and inserts
an `EscrowRecord` into an **off-ledger side-table** `self.escrows` (:1770), keyed by `escrow_id`,
carrying `{creator, recipient, amount, resolved}`. `apply_release_escrow` (:1959) credits the
recipient single-handedly and marks the record `resolved`; `apply_refund_escrow` (:2030) credits the
creator single-handedly and marks resolved. So per-effect Σδ ≠ 0 on the cell ledger — conservation
holds only ACROSS the create+release/refund PAIR, with the side-table accounting for the in-flight
amount. We model that side-table faithfully here. -/

/-- **`EscrowRecord`** — one entry of dregg1's off-ledger `escrows` side-table (`apply.rs:1773`),
keyed by `id`, carrying the locked `amount`, the `creator` (refund target) and `recipient` (release
target), and the `resolved` flag (set true once released/refunded). An UNRESOLVED record holds
`amount` of value OUT of the cell ledger — that is the holding-store value the pair conserves. -/
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
  /-- **The asset class of the locked value** (`META-FILL C`). dregg cells hold MANY assets, so an
  escrow lock parks `amount` of a SPECIFIC asset — and the combined per-asset measure must move at
  THAT asset only (`recTotalAssetWithEscrow r.asset`), every other asset literally untouched. Added
  ADDITIVELY (`:= 0`) so every existing 5-field `EscrowRecord` literal stays compiling (the default
  fills the 6th); the Wave-4 non-vacuity guard `#eval` LOCKS at a NON-ZERO asset to prove the default
  does NOT collapse to a single-asset shadow. -/
  asset     : AssetId := 0
  /-- **The BRIDGE tag** (Wave-5 `PHASE-BRIDGE`). A cross-chain bridge lock shares the SAME off-ledger
  holding-store as escrow — dregg1's `pending_bridges` is the bridge-shaped twin of `escrows`
  (`cell/src/note_bridge.rs`: a `PendingBridge` parks `value`/`asset_type` while `Locked`, AWAITING the
  other-chain confirmation). We reuse the escrow store with THIS additive tag (`:= false`, so every
  existing 6-field `EscrowRecord` literal stays compiling — the default fills the 7th) rather than a
  parallel side-table (least new machinery). The tag separates the two RESOLUTION semantics: an escrow
  release/refund SETTLES back onto the ledger (combined CONSERVED), whereas a bridge FINALIZE BURNS the
  locked value — it genuinely LEFT for the other chain, a disclosed outflow, so the COMBINED measure
  DROPS by the bridged amount (modelled honestly as a no-credit resolve). A bridge CANCEL
  (timeout/failure) refunds the originator (combined conserved, like escrow refund). -/
  bridge    : Bool := false
  /-- **Queue deposit binding** (P0-1-full). When set, this deposit is tied to a specific FIFO message
  in queue `queueDep` with hash `queueMsg` — dequeue must pop THAT head and name THIS `depId`. -/
  queueDep  : Option Nat := none
  queueMsg  : Option Nat := none
deriving DecidableEq, Repr

/-! ### The QUEUE side-table: a REAL ring-buffer FIFO automaton (dregg1's `MerkleQueue` / `CapInbox`).

dregg1's queue (`turn/src/executor/apply.rs:3310 apply_queue_enqueue` / `:3420 apply_queue_dequeue`;
the data-structure substrate `storage/src/queue.rs:16 MerkleQueue`) is a FIFO buffer: enqueue APPENDS a
message hash to the tail and REJECTS fail-closed when `current_len >= capacity` (`apply.rs:3348`);
dequeue REMOVES-FROM-FRONT in FIFO order and REJECTS fail-closed when `current_len == 0`
(`apply.rs:3444`). dregg1's *cell-field* encoding stores only a head pointer + a tail pointer (two
`[u8;32]` slots), and EXPLICITLY DOCUMENTS a FIFO-advancement GAP — "the head cannot be advanced to the
next message hash without out-of-band knowledge of the message sequence … head lags by one until the
queue drains" (`apply.rs:3466-3481`). The `MerkleQueue` substrate (`queue.rs:16`) carries the FULL
ordered `Vec<QueueEntry>` + a `head: usize`, which IS the real FIFO, but its `verify_dequeue_proof` is
flagged a non-real prototype in the Rust itself (`queue.rs:416-426`). We model the REAL mechanism that
substrate intends — the de-THIN requirement — by carrying the FULL ordered `buffer : List Nat` of
message hashes (front = head = next-to-dequeue, back = tail = most-recently-enqueued). A `List` is a
ring-buffer up to representation; its head/tail give us exactly the FIFO order to PROVE (no advancement
gap, no two-pointer approximation). The queue holds MESSAGES (content hashes / capability invocations,
`CapInbox`), NOT balance — so it is balance-NEUTRAL (`recTotalAssetWithEscrow` UNCHANGED ∀ asset). -/

/-- **`QueueRecord`** — one entry of the queue side-table, keyed by `id` (dregg1's queue cell id,
modelled as a `Nat` key), carrying the queue `owner` (only the owner may dequeue — `apply.rs:3433`), the
`capacity` (the max occupancy — `apply.rs:3324`), and the REAL `buffer : List Nat` of message hashes in
FIFO order (front = head = next-to-dequeue). The occupancy is `buffer.length`; the capacity bound is
`buffer.length ≤ capacity`. dregg1's anti-spam `deposit` lives on the cell ledger (the `EffectsPaired`
deposit flow) — orthogonal to the ORDER mechanism modelled here. -/
structure QueueRecord where
  /-- the queue id (dregg1's queue cell `CellId`, modelled as a `Nat` key). -/
  id       : Nat
  /-- the queue owner — only the owner may dequeue (`apply.rs:3433`). -/
  owner    : CellId
  /-- the queue capacity — enqueue rejects fail-closed when occupancy reaches it (`apply.rs:3348`). -/
  capacity : Nat
  /-- **The REAL FIFO buffer**: the ordered list of message hashes, front = head = next-to-dequeue, back
  = tail = most-recently-enqueued. Enqueue APPENDS to the back; dequeue REMOVES the front. The occupancy
  is `buffer.length`. This is the de-THIN content — a flag/no-op model would have NO order and NO bound. -/
  buffer   : List Nat := []
deriving DecidableEq, Repr

/-- **Enqueue into the buffer (the FIFO APPEND).** `buffer ++ [m]` — the new message goes to the BACK
(tail), behind every message already waiting. Fail-closed at capacity is enforced at the kernel
transition (`queueEnqueueK`); this is the raw order operation. -/
def qbufEnqueue (buf : List Nat) (m : Nat) : List Nat := buf ++ [m]

/-- **Dequeue from the buffer (the FIFO REMOVE-FROM-FRONT).** Returns `(head, rest)` — the FRONT message
(the oldest waiting) and the remaining buffer. `none` when empty (fail-closed at the kernel transition). -/
def qbufDequeue (buf : List Nat) : Option (Nat × List Nat) :=
  match buf with
  | []      => none
  | m :: ms => some (m, ms)

/-- **FIFO ORDER — PROVED (the load-bearing non-vacuity).** Enqueue `a` then `b` into ANY buffer, then
dequeue: the FIRST dequeue returns `a` (the older), and dequeuing the remainder returns `b`. Order is
PRESERVED — `a` before `b` — exactly because enqueue appends to the back and dequeue removes the front.
A flag/no-op model could not state this (no order); a two-pointer cell-field model (dregg1's
`apply.rs`) cannot prove it past the 0→1 transition (the documented advancement gap). The full `List`
buffer can. -/
theorem qbuf_fifo_order (buf : List Nat) (a b : Nat) :
    qbufDequeue (qbufEnqueue (qbufEnqueue buf a) b) =
      (match qbufDequeue buf with
       | some (h, rest) => some (h, qbufEnqueue (qbufEnqueue rest a) b)
       | none           => some (a, [b])) := by
  cases buf with
  | nil      => rfl
  | cons h t => rfl

/-- **FIFO ORDER on the EMPTY buffer — PROVED (the witnessed `a`-then-`b` instance).** Starting empty,
enqueue `a` then `b`, dequeue → `a` (the older) with `[b]` remaining; dequeue the remainder → `b`. The
concrete order witness the `#eval` exhibits. -/
theorem qbuf_fifo_empty (a b : Nat) :
    qbufDequeue (qbufEnqueue (qbufEnqueue [] a) b) = some (a, [b]) ∧
      qbufDequeue [b] = some (b, []) := ⟨rfl, rfl⟩

/-- **EMPTY DEQUEUE fail-closed — PROVED.** Dequeue on the empty buffer is rejected (`none`). The
emptiness gate that the kernel transition lifts to `none`. -/
theorem qbuf_empty_dequeue : qbufDequeue ([] : List Nat) = none := rfl

/-- **ENQUEUE grows occupancy by one — PROVED.** The occupancy `buffer.length` after an enqueue is
exactly one more than before (the counter the capacity bound tracks). -/
theorem qbuf_enqueue_length (buf : List Nat) (m : Nat) :
    (qbufEnqueue buf m).length = buf.length + 1 := by
  simp [qbufEnqueue]

/-- **DEQUEUE shrinks occupancy by one — PROVED.** When dequeue succeeds, the occupancy drops by one. -/
theorem qbuf_dequeue_length {buf : List Nat} {h : Nat} {rest : List Nat}
    (heq : qbufDequeue buf = some (h, rest)) : buf.length = rest.length + 1 := by
  cases buf with
  | nil      => simp [qbufDequeue] at heq
  | cons x t => simp only [qbufDequeue, Option.some.injEq, Prod.mk.injEq] at heq
                obtain ⟨_, hr⟩ := heq; subst hr; simp

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

/-- Look up a queue record by id in the side-table (the first match), `none` if absent. -/
def findQueue (qs : List QueueRecord) (id : Nat) : Option QueueRecord :=
  qs.find? (fun q => q.id == id)

/-- Replace the queue record with the given `id` by `q'` (the first match), leaving others untouched.
The side-table update primitive shared by enqueue/dequeue/resize. -/
def replaceQueue (qs : List QueueRecord) (id : Nat) (q' : QueueRecord) : List QueueRecord :=
  qs.map (fun q => if q.id == id then q' else q)

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
field), and the capability table — PLUS dregg1's two off-ledger side-tables, both DEFAULTING EMPTY
so every existing construction/proof that ignores them is unaffected (the additive extension):

  * `escrows` — the off-ledger escrow holding-store (`self.escrows`); unresolved records hold value
    out of the cell ledger (`apply.rs:1770`);
  * `nullifiers` — the spent-note nullifier SET (`self.note_nullifiers`, `apply.rs:941`); a
    `NoteSpend` inserts its nullifier and is rejected fail-closed if already present (double-spend).

This is `KernelState` with `bal : CellId → ℤ` lifted to `cell : CellId → Value`, additively extended
with the two holding stores — the concrete dregg2 cell + dregg1's real side-table accounting. -/
structure RecordKernelState where
  /-- The finite set of live cells whose balances are tracked / conserved. -/
  accounts : Finset CellId
  /-- Per-cell content-addressed record state (each carries a `balance` field). -/
  cell     : CellId → Value
  /-- The capability table (lift of l4v `Caps`). -/
  caps     : Caps
  /-- The off-ledger escrow holding-store (`self.escrows`); DEFAULTS EMPTY. -/
  escrows    : List EscrowRecord := []
  /-- The spent-note nullifier SET (`self.note_nullifiers`); DEFAULTS EMPTY. -/
  nullifiers : List Nat := []
  /-- **The KERNEL-STATE REVOCATION REGISTRY** (`self.revocation_channel`, hole #3 / `#139`): the
  committed set of revoked credential nullifiers — the MDB/derivation-table root that `cap_revoke`
  tears down (single-machine ⇒ immediate revocation). A node's credential is revoked iff its
  `credNul` is in THIS set, read off committed state (NOT the wire-supplied, formerly-pinned
  `NodeAuth.rev`), so the fail-closed gate `gateOK` can finally honour revocation. Balance-NEUTRAL
  (`recTotalAssetWithEscrow` reads `bal`+`escrows`, never `revoked`). DEFAULTS EMPTY (the additive
  extension, exactly as `nullifiers`/`commitments` were added). -/
  revoked    : List Nat := []
  /-- **The note COMMITMENT SET** (`META-FILL C`, closing `#121`): the grow-only dual of
  `nullifiers`. dregg1's `apply_note_create` inserts a fresh Pedersen commitment into the off-ledger
  commitment tree (a §8 CryptoPortal-gated range proof guards the hidden value). A `noteCreate` grows
  THIS set (NOT `bal`, NOT `nullifiers`, NOT `escrows`) — so it is bal-NEUTRAL and genuinely distinct
  from escrow/obligation/noteSpend (the `#121` de-conflation). DEFAULTS EMPTY (the additive
  extension, exactly as `nullifiers` was added). -/
  commitments : List Nat := []
  /-- **The genuine per-asset balance ledger** `bal c a` — the (ℤ-valued, debt-capable) amount of
  asset `a` held by cell `c`. dregg cells hold MANY assets; conservation is PER-ASSET
  (`EFFECT-ISA-DESIGN.md:315,320-323`), never one aggregate scalar. DEFAULTS to the empty ledger so
  every existing construction/proof that ignores it is unaffected (the additive extension, exactly
  as `escrows`/`nullifiers` were added). This is the destination conserved measure the per-asset
  transition (`§MULTI-ASSET`) preserves; the scalar `balance` field is its legacy asset-view, and
  the executable `FullAction` dispatch migrates onto `bal` (`DREGG2-GAP-MAP.md FILL 1`). -/
  bal        : CellId → AssetId → ℤ := fun _ _ => 0
  /-- **The QUEUE side-table** (Wave-7 de-THIN): the list of live queue records, each carrying its REAL
  ordered FIFO `buffer : List Nat` of message hashes (`QueueRecord`). Queues hold MESSAGES, NOT balance,
  so this is balance-NEUTRAL — `recTotalAssetWithEscrow` is UNCHANGED ∀ asset (it reads `bal`+`escrows`,
  never `queues`). DEFAULTS EMPTY (the additive extension, exactly as `escrows`/`nullifiers`/
  `commitments` were added). The FIFO ORDER + capacity bound + empty-fail-closed are PROVED off
  `qbufEnqueue`/`qbufDequeue` (the de-THIN non-vacuity a flag-only model lacks). -/
  queues     : List QueueRecord := []
  /-- **The SWISS-TABLE side-table** (Wave-8 de-THIN): the CapTP export/enliven/handoff/GC registry — a
  list of live `SwissRecord` entries, each keyed by its swiss number, carrying the exported cap's
  `rights` + a `refcount` (the GC counter) + the bound handoff `cert`. The swiss-table moves REFERENCES
  (capability routing), NOT balance — so it is balance-NEUTRAL (`recTotalAssetWithEscrow` is UNCHANGED
  ∀ asset; it reads `bal`+`escrows`, never `swiss`). DEFAULTS EMPTY (the additive extension, exactly as
  `escrows`/`nullifiers`/`commitments`/`queues` were added). Export INSERTS, enliven LOOKS-UP-fail-closed
  + validates non-amplification, handoff binds the cert, the refcount tracks live refs (GC at 0) — the
  REAL mechanism a flag-shadow lacks. -/
  swiss      : List SwissRecord := []
  /-- **The PER-CELL SLOT-CAVEAT registry** (dregg1's `FactoryDescriptor.program` carried per minted
  cell, `cell/src/factory.rs`): the list of `SlotCaveat`s the executor checks on EVERY `SetField` to
  that cell (`apply_set_field` → `RecordProgram::evaluate`, `cell/src/program.rs:1314`+). A factory
  installs these at `createCellFromFactory` time; thereafter `stateStepGuarded` (the caveat-gated
  field write) rejects any write violating a caveat on the written slot. This is what makes a
  published app-safety REAL — `nameservice` `Immutable`-owner = *registered forever*, enforced BY THE
  EXECUTOR. Caveats touch NO balance, so this is balance-NEUTRAL (`recTotalAssetWithEscrow` reads
  `bal`+`escrows`, never `slotCaveats`). DEFAULTS EMPTY (the additive extension, exactly as
  `escrows`/`nullifiers`/`commitments`/`queues`/`swiss` were added — a cell with no factory-bound
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
  Lifecycle touches NO balance, so this is balance-NEUTRAL (`recTotalAssetWithEscrow` reads
  `bal`+`escrows`, never `lifecycle`). DEFAULTS Live. -/
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

/-! ## §ESCROW — the OFF-LEDGER holding-store semantics (faithful to dregg1's `apply.rs`).

The `recKExec` transfer above is balance-CONSERVING (the `transfer` effect, Σδ = 0). But dregg1's
escrow is NOT a transfer: `apply_create_escrow` debits ONE cell and parks the value in the off-ledger
`escrows` side-table; `apply_release_escrow`/`apply_refund_escrow` credit ONE cell and mark the
record resolved. So per-effect Σδ ≠ 0 on the cell ledger; the conserved quantity is the COMBINED
total (cell-ledger + the value held by unresolved escrows). This section models that faithfully and
proves the REAL invariant: value is conserved ACROSS the create+release/refund pair, with the
side-table accounting for the in-flight amount. -/

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

/-! ### The holding-store value measure + the COMBINED conserved total. -/

/-- **`escrowHeld k`** — the total value currently parked in the off-ledger holding-store: the sum of
`amount` over the UNRESOLVED escrow records. This is the value held OUT of the cell ledger between a
create and its release/refund. -/
def escrowHeld (k : RecordKernelState) : ℤ :=
  (k.escrows.filter (fun r => !r.resolved)).foldr (fun r acc => r.amount + acc) 0

/-- **`recTotalWithEscrow k`** — the COMBINED conserved quantity: the cell-ledger `balance` total
PLUS the value held off-ledger by unresolved escrows. This — not the per-cell `recTotal` — is what
the create+release/refund pair conserves, exactly as dregg1's side-table accounting demands. -/
def recTotalWithEscrow (k : RecordKernelState) : ℤ := recTotal k + escrowHeld k

/-- Prepending an UNRESOLVED record raises `escrowHeld` by its `amount`. PROVED (definitional unfold
of the filtered fold). -/
theorem escrowHeld_cons_unresolved (k : RecordKernelState) (r : EscrowRecord) (hr : r.resolved = false) :
    escrowHeld { k with escrows := r :: k.escrows } = escrowHeld k + r.amount := by
  unfold escrowHeld
  simp only [List.filter_cons, show (!r.resolved) = true from by simp [hr],
             Bool.false_eq_true, if_true, List.foldr_cons]
  omega

/-! ### The faithful escrow lifecycle: create (debit + park), release/refund (credit + resolve). -/

/-- **`createEscrowRaw`** — dregg1's `apply_create_escrow` (`apply.rs:1674`) at the state level:
a SINGLE-cell debit of `amount` from `creator` PLUS an insert of an unresolved `EscrowRecord` into the
off-ledger holding-store. NOT a two-cell transfer. The cell-ledger total DROPS by `amount`; the
holding-store value RISES by `amount`; the COMBINED total is preserved. -/
def createEscrowRaw (k : RecordKernelState) (id creator recipient : CellId) (amount : ℤ) :
    RecordKernelState :=
  { k with cell := recDebit k.cell creator amount
           escrows := { id := id, creator := creator, recipient := recipient,
                        amount := amount, resolved := false } :: k.escrows }

/-- Mark the FIRST unresolved escrow record with the given `id` resolved (dregg1's
`escrows.get_mut(escrow_id).resolved = true`, `apply.rs:1969`/`:2040` — a HashMap keyed by id, so
exactly ONE entry is mutated). Records before it, after it, and with other ids are untouched. -/
def markResolved (escrows : List EscrowRecord) (id : Nat) : List EscrowRecord :=
  match escrows with
  | []      => []
  | r :: rs => if r.id = id ∧ r.resolved = false then { r with resolved := true } :: rs
               else r :: markResolved rs id

/-- **`settleEscrowRaw`** — the shared body of `apply_release_escrow`/`apply_refund_escrow`: a
SINGLE-cell credit of `amount` to the settlement target (`recipient` on release, `creator` on refund)
PLUS marking the record resolved. The cell-ledger total RISES by `amount`; the holding-store value
DROPS by `amount` (the record leaves the unresolved set); the COMBINED total is preserved. -/
def settleEscrowRaw (k : RecordKernelState) (id target : CellId) (amount : ℤ) : RecordKernelState :=
  { k with cell := recCredit k.cell target amount
           escrows := markResolved k.escrows id }

/-- **`createEscrow` (executable, fail-closed).** Commits only when the actor is authorized over the
`creator` cell (same `authorizedB` gate as `transfer`), the amount is non-negative and available in
the creator's `balance`, the creator is a live account, and the `id` is NOT already in use (dregg1's
"escrow_id already exists" check, `apply.rs:1736`). On commit: single-cell debit + park the record. -/
def createEscrowK (k : RecordKernelState) (id : Nat) (actor creator recipient : CellId) (amount : ℤ) :
    Option RecordKernelState :=
  if authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (k.cell creator) ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id) then
    some (createEscrowRaw k id creator recipient amount)
  else none

/-- **`releaseEscrow` (executable, fail-closed).** Looks up the unresolved record by `id`; on success
single-cell credits the `recipient` and marks resolved. Rejects a missing or already-resolved record
(dregg1's "escrow not found" / "already resolved", `apply.rs:1812`/`:1820`). The crypto/condition
check (proof/signatures) is the §8 portal carried at the effect layer — here we model the state move
gated on the record being present-and-unresolved. -/
def releaseEscrowK (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => some (settleEscrowRaw k id r.recipient r.amount)
  | none   => none

/-- **`refundEscrow` (executable, fail-closed).** Looks up the unresolved record by `id`; on success
single-cell credits the `creator` (refund target) and marks resolved (dregg1's `apply_refund_escrow`,
`apply.rs:1976`). The timeout gate is carried at the effect layer. -/
def refundEscrowK (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => some (settleEscrowRaw k id r.creator r.amount)
  | none   => none

/-! ### The REAL escrow invariants. -/

/-- **`escrow_create_debits` — PROVED.** A committed `createEscrow` is a SINGLE-cell debit: the
cell-ledger total `recTotal` DROPS by exactly `amount`, and the holding-store grows by the new
record (it is NOT a balance-conserving transfer on the cell ledger). This is the faithful contrast
with the old paired shadow. -/
theorem escrow_create_debits {k k' : RecordKernelState} {id : Nat} {actor creator recipient : CellId}
    {amount : ℤ} (h : createEscrowK k id actor creator recipient amount = some k') :
    recTotal k' = recTotal k - amount ∧
      k'.escrows = { id := id, creator := creator, recipient := recipient,
                     amount := amount, resolved := false } :: k.escrows := by
  unfold createEscrowK at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (k.cell creator) ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    refine ⟨?_, rfl⟩
    simp only [recTotal, createEscrowRaw]
    exact recDebit_recTotal k.accounts k.cell creator amount hlive
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`escrow_create_conserves_combined` — PROVED.** A committed `createEscrow` PRESERVES the COMBINED
total (cell-ledger + holding-store): the `−amount` cell-ledger debit is exactly offset by the
`+amount` rise in the off-ledger holding-store. Value MOVES into the side-table; nothing is created
or destroyed. -/
theorem escrow_create_conserves_combined {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {amount : ℤ}
    (h : createEscrowK k id actor creator recipient amount = some k') :
    recTotalWithEscrow k' = recTotalWithEscrow k := by
  unfold createEscrowK at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ balOf (k.cell creator) ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    set newRec : EscrowRecord := { id := id, creator := creator, recipient := recipient,
                                   amount := amount, resolved := false } with hnewRec
    show recTotalWithEscrow (createEscrowRaw k id creator recipient amount)
       = recTotalWithEscrow k
    unfold recTotalWithEscrow createEscrowRaw
    -- The post-state's cell-ledger total: a single-cell debit.
    have hcell : recTotal { k with cell := recDebit k.cell creator amount,
                                   escrows := newRec :: k.escrows }
        = recTotal k - amount := by
      show (∑ x ∈ k.accounts, balOf (recDebit k.cell creator amount x)) = _
      simpa [recTotal] using recDebit_recTotal k.accounts k.cell creator amount hlive
    -- The post-state's holding-store value: the parked record raises it.
    have hheld : escrowHeld { k with cell := recDebit k.cell creator amount,
                                     escrows := newRec :: k.escrows }
        = escrowHeld k + amount := by
      have hc := escrowHeld_cons_unresolved
        { k with cell := recDebit k.cell creator amount } newRec rfl
      simpa [hnewRec] using hc
    rw [hcell, hheld]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The raw escrow-list filtered-sum (the unfolded `escrowHeld`). -/
def heldSum (es : List EscrowRecord) : ℤ :=
  (es.filter (fun r => !r.resolved)).foldr (fun r acc => r.amount + acc) 0

theorem escrowHeld_eq_heldSum (k : RecordKernelState) : escrowHeld k = heldSum k.escrows := rfl

/-- **The pair-conservation CORE (PROVED by list induction).** Marking the FIRST unresolved record
whose id matches `id` as resolved drops the unresolved-held sum by exactly that record's `amount`.
The faithful side-table accounting: when a release/refund resolves the in-flight record, the value it
held leaves the off-ledger store by precisely its amount. `markResolved` and `find?` walk the list in
lockstep on the same `id ∧ unresolved` predicate, so the dropped amount is exactly the found record's. -/
theorem heldSum_markResolved_found (id : Nat) (r : EscrowRecord) :
    ∀ (es : List EscrowRecord),
      es.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      heldSum (markResolved es id) = heldSum es - r.amount := by
  intro es
  induction es with
  | nil => intro hfind; simp [List.find?] at hfind
  | cons hd tl ih =>
      intro hfind
      simp only [List.find?_cons] at hfind
      by_cases hmatch : (hd.id = id ∧ hd.resolved = false)
      · -- head matches the predicate: it IS the found, unresolved record.
        obtain ⟨hid, hres⟩ := hmatch
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = true from by simp [hid, hres]] at hfind
        simp only [Option.some.injEq] at hfind
        -- hfind : hd = r ; rewrite the goal's `r` back to `hd`.
        subst hfind
        unfold heldSum markResolved
        rw [if_pos ⟨hid, hres⟩]
        -- LHS: head now resolved ⇒ filtered OUT; RHS: head was unresolved ⇒ filtered IN.
        simp only [List.filter_cons,
                   show (!({hd with resolved := true} : EscrowRecord).resolved) = false from by simp,
                   show (!hd.resolved) = true from by simp [hres],
                   Bool.false_eq_true, if_false, if_true, List.foldr_cons]
        omega
      · -- head does NOT match the predicate: carried unchanged; recurse on the tail.
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = false from by
              simp [decide_eq_false_iff_not, hmatch]] at hfind
        have ihr := ih hfind
        -- markResolved (hd::tl) id = hd :: markResolved tl id (head doesn't match).
        have hmr : markResolved (hd :: tl) id = hd :: markResolved tl id := by
          conv_lhs => rw [markResolved]
          rw [if_neg hmatch]
        rw [hmr]
        -- Both heldSums share the same head `hd`; the tail delta is `ihr`.
        unfold heldSum
        simp only [List.filter_cons]
        by_cases hhdres : hd.resolved = false
        · rw [show (!hd.resolved) = true from by simp [hhdres]]
          simp only [Bool.false_eq_true, if_true, List.foldr_cons]
          have ihr' : (List.filter (fun r => !r.resolved) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (fun r => !r.resolved) tl).foldr (fun r acc => r.amount + acc) 0
                - r.amount := ihr
          rw [ihr']; ring
        · rw [show (!hd.resolved) = false from by simp [hhdres]]
          simp only [Bool.false_eq_true, if_false]
          have ihr' : (List.filter (fun r => !r.resolved) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (fun r => !r.resolved) tl).foldr (fun r acc => r.amount + acc) 0
                - r.amount := ihr
          rw [ihr']

/-- **`escrow_settle_conserves_combined` — PROVED.** A release/refund that settles the found record
to `target` (`recipient` on release, `creator` on refund) PRESERVES the COMBINED total: the `+amount`
single-cell credit is exactly offset by the holding-store DROP as the record leaves the unresolved
set. Value moves OUT of the side-table back onto the ledger; the combined total is fixed. -/
theorem escrow_settle_conserves_combined (k : RecordKernelState) (id target : CellId) (r : EscrowRecord)
    (htgt : target ∈ k.accounts)
    (hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r) :
    recTotalWithEscrow (settleEscrowRaw k id target r.amount) = recTotalWithEscrow k := by
  have hcell : recTotal (settleEscrowRaw k id target r.amount) = recTotal k + r.amount := by
    show (∑ x ∈ k.accounts, balOf (recCredit k.cell target r.amount x)) = _
    simpa [recTotal] using recCredit_recTotal k.accounts k.cell target r.amount htgt
  have hheld : escrowHeld (settleEscrowRaw k id target r.amount) = escrowHeld k - r.amount := by
    show heldSum (markResolved k.escrows id) = heldSum k.escrows - r.amount
    exact heldSum_markResolved_found id r k.escrows hfind
  show recTotal (settleEscrowRaw k id target r.amount) + escrowHeld (settleEscrowRaw k id target r.amount)
     = recTotal k + escrowHeld k
  rw [hcell, hheld]; ring

/-- **`releaseEscrow` PRESERVES the COMBINED total — PROVED** (the headline pair-conservation fact for
release). Reads off `escrow_settle_conserves_combined`. -/
theorem releaseEscrow_conserves_combined {k k' : RecordKernelState} {id : Nat}
    (htgt : ∀ r, k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.recipient ∈ k.accounts)
    (h : releaseEscrowK k id = some k') :
    recTotalWithEscrow k' = recTotalWithEscrow k := by
  unfold releaseEscrowK at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_settle_conserves_combined k id r.recipient r (htgt r hfind) hfind

/-- **`refundEscrow` PRESERVES the COMBINED total — PROVED** (the headline pair-conservation fact for
refund: value returns to the creator, combined fixed). -/
theorem refundEscrow_conserves_combined {k k' : RecordKernelState} {id : Nat}
    (htgt : ∀ r, k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      r.creator ∈ k.accounts)
    (h : refundEscrowK k id = some k') :
    recTotalWithEscrow k' = recTotalWithEscrow k := by
  unfold refundEscrowK at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_settle_conserves_combined k id r.creator r (htgt r hfind) hfind

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

/-! ## §ESCROW-PER-ASSET — the off-ledger holding-store on the GENUINE per-asset `bal` ledger (`META-FILL C`).

The scalar escrow above (`createEscrowRaw`/`settleEscrowRaw`, `escrowHeld`/`recTotalWithEscrow`)
moves the named `balance` FIELD — ONE asset. But dregg cells hold MANY assets, so an escrow lock
parks `amount` of a SPECIFIC asset (`EscrowRecord.asset`), and the COMBINED conserved quantity must
be PER-ASSET: a lock DROPS that asset's `bal`-ledger supply by `amount` AND RAISES the per-asset
holding-store by `amount` (combined fixed AT that asset), with EVERY OTHER asset literally untouched.
Folding all assets into one combined scalar would let an escrow swap asset A for asset B while the
aggregate stays put — the cross-asset-laundering hole at the holding-store boundary.

We re-found the escrow lifecycle onto the per-asset `bal` ledger via the single-cell `recBalCreditCell`
(the per-asset analog of `recCredit`/`recDebit` — a single-cell, single-asset move), define the
per-asset held sum + combined measure, and re-prove the four conserves-combined facts PER-ASSET as
DROP-IN swaps of the scalar decomposition (the find?/markResolved list lockstep is ASSET-AGNOSTIC; we
narrow the matched-record drop by `r.asset = b`). The scalar escrow stays as the legacy `cell`-view;
these are NEW per-asset SIBLINGS, never a re-proof of the same statement. -/

/-- **`recBalCreditCell` — single-cell, single-asset credit on the per-asset `bal` ledger.** Add `amt`
to cell `c`'s asset `a` column, leaving every other (cell, asset) pair literally untouched. The
per-asset analog of `recCredit` (which moved the scalar `balance` FIELD); `recBalCreditCell c a (-amt)`
is the per-asset DEBIT. This is the per-asset escrow's single-cell move (dregg1's `set_balance`, but
at a NAMED asset column rather than the scalar field). Lives HERE in `RecordKernel` (upstream of both
`TurnExecutorFull` and `EffectsPaired`) so both the executed dispatch and the chained escrow can use
it; it is definitionally the same shape as `TurnExecutorFull.recBalCredit`. -/
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

/-- The per-asset UNRESOLVED-record predicate: unresolved AND of asset `b` (a `Bool`, so it drives
`List.filter` directly). The asset-filtered refinement of `fun r => !r.resolved`. -/
def heldAssetPred (b : AssetId) (r : EscrowRecord) : Bool := !r.resolved && decide (r.asset = b)

/-- **`escrowHeldAsset k b`** — the per-asset holding-store value: the sum of `amount` over the
UNRESOLVED escrow records WHOSE `asset = b`. The per-asset analog of `escrowHeld`, indexed by
`AssetId` (NEVER one combined scalar) — value parked off the `bal` ledger AT asset `b`. -/
def escrowHeldAsset (k : RecordKernelState) (b : AssetId) : ℤ :=
  (k.escrows.filter (heldAssetPred b)).foldr (fun r acc => r.amount + acc) 0

/-- **`recTotalAssetWithEscrow k b`** — THE COMBINED PER-ASSET conserved quantity: asset `b`'s
`bal`-ledger supply PLUS the value held off-ledger by unresolved escrows AT asset `b`. This — the
per-asset refinement of `recTotalWithEscrow` — is what the per-asset create+settle pair conserves AT
EACH ASSET independently. -/
def recTotalAssetWithEscrow (k : RecordKernelState) (b : AssetId) : ℤ :=
  recTotalAsset k b + escrowHeldAsset k b

/-- `bal_neutral` — the balance-NEUTRAL finisher (the fourth effect-arm combinator; the other
three live in `Dregg2/Tactics.lean`). A caps/log-only edit leaves the per-asset COMBINED measure
`recTotalAssetWithEscrow = bal-ledger + holding-store` FIXED: unfold the measure and close by
`ring`. Defined HERE (not in the generic `Tactics.lean`) so macro hygiene resolves the measure's
simp-lemma names against THIS scope. For arms that first need their step def unfolded, do that
simp beforehand (`simp only [recKRevokeTarget] …; bal_neutral`). -/
macro "bal_neutral" : tactic =>
  `(tactic| (simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]; ring))

/-- The raw per-asset escrow-list filtered-sum (the unfolded `escrowHeldAsset`). -/
def heldSumAsset (es : List EscrowRecord) (b : AssetId) : ℤ :=
  (es.filter (heldAssetPred b)).foldr (fun r acc => r.amount + acc) 0

theorem escrowHeldAsset_eq_heldSumAsset (k : RecordKernelState) (b : AssetId) :
    escrowHeldAsset k b = heldSumAsset k.escrows b := rfl

/-- **`escrowHeldAsset_cons_unresolved` — PROVED (the per-asset prepend delta).** Prepending an
UNRESOLVED record raises `escrowHeldAsset b` by `r.amount` IFF `r.asset = b`, and by `0` otherwise.
NON-VACUOUS: the `if r.asset = b` discriminant has teeth — prepending an asset-A record raises
`escrowHeldAsset A` but leaves `escrowHeldAsset B` (B≠A) literally FIXED. The scalar `escrowHeld_cons`
cannot state the b-indexed version (it has no asset to filter on). -/
theorem escrowHeldAsset_cons_unresolved (k : RecordKernelState) (r : EscrowRecord) (b : AssetId)
    (hr : r.resolved = false) :
    escrowHeldAsset { k with escrows := r :: k.escrows } b
      = escrowHeldAsset k b + (if r.asset = b then r.amount else 0) := by
  unfold escrowHeldAsset
  simp only [List.filter_cons]
  by_cases hab : r.asset = b
  · rw [show heldAssetPred b r = true from by simp [heldAssetPred, hr, hab]]
    simp only [if_true, List.foldr_cons, if_pos hab]
    omega
  · rw [show heldAssetPred b r = false from by simp [heldAssetPred, hab]]
    simp only [Bool.false_eq_true, if_false, if_neg hab, add_zero]

/-- **`heldSumAsset_markResolved_found` — THE PER-ASSET PAIR-CONSERVATION CORE (PROVED by list
induction).** Marking the FIRST unresolved record whose id matches `id` as resolved drops the per-asset
held sum AT asset `b` by `r.amount` IFF the found record's `asset = b`, and by `0` otherwise. The
find?/markResolved lockstep is ASSET-AGNOSTIC (it walks the same `id ∧ unresolved` predicate); the
matched-record drop is narrowed by `r.asset = b`. NON-VACUOUS: settling an asset-A record drops
`escrowHeldAsset A` by its amount and leaves every OTHER asset's held sum literally FIXED. Mirrors
`heldSum_markResolved_found` with `heldSum` → `heldSumAsset · b` and the drop guarded by `r.asset = b`. -/
theorem heldSumAsset_markResolved_found (id : Nat) (r : EscrowRecord) (b : AssetId) :
    ∀ (es : List EscrowRecord),
      es.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r →
      heldSumAsset (markResolved es id) b = heldSumAsset es b - (if r.asset = b then r.amount else 0) := by
  intro es
  induction es with
  | nil => intro hfind; simp [List.find?] at hfind
  | cons hd tl ih =>
      intro hfind
      simp only [List.find?_cons] at hfind
      by_cases hmatch : (hd.id = id ∧ hd.resolved = false)
      · -- head matches: it IS the found, unresolved record.
        obtain ⟨hid, hres⟩ := hmatch
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = true from by simp [hid, hres]] at hfind
        simp only [Option.some.injEq] at hfind
        subst hfind
        unfold heldSumAsset markResolved
        rw [if_pos ⟨hid, hres⟩]
        simp only [List.filter_cons,
                   show heldAssetPred b ({hd with resolved := true} : EscrowRecord) = false from by
                     simp [heldAssetPred]]
        by_cases hab : hd.asset = b
        · -- found record is OF asset b: LHS drops it (now resolved ⇒ filtered OUT), RHS subtracts amount.
          rw [show heldAssetPred b hd = true from by simp [heldAssetPred, hres, hab]]
          simp only [Bool.false_eq_true, if_false, if_true, List.foldr_cons, if_pos hab]
          omega
        · -- found record is of ANOTHER asset: it was never IN `heldSumAsset b`, so no change.
          rw [show heldAssetPred b hd = false from by simp [heldAssetPred, hab]]
          simp only [Bool.false_eq_true, if_false, if_neg hab, sub_zero]
      · -- head does NOT match: carried unchanged; recurse on the tail.
        rw [show (decide (hd.id = id ∧ hd.resolved = false)) = false from by
              simp [hmatch]] at hfind
        have ihr := ih hfind
        have hmr : markResolved (hd :: tl) id = hd :: markResolved tl id := by
          conv_lhs => rw [markResolved]; rw [if_neg hmatch]
        rw [hmr]
        unfold heldSumAsset
        simp only [List.filter_cons]
        by_cases hhd : heldAssetPred b hd = true
        · rw [hhd]
          simp only [if_true, List.foldr_cons]
          have ihr' : (List.filter (heldAssetPred b) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (heldAssetPred b) tl).foldr (fun r acc => r.amount + acc) 0
                - (if r.asset = b then r.amount else 0) := ihr
          rw [ihr']; ring
        · rw [show heldAssetPred b hd = false from by simpa using hhd]
          simp only [Bool.false_eq_true, if_false]
          have ihr' : (List.filter (heldAssetPred b) (markResolved tl id)).foldr
              (fun r acc => r.amount + acc) 0
              = (List.filter (heldAssetPred b) tl).foldr (fun r acc => r.amount + acc) 0
                - (if r.asset = b then r.amount else 0) := ihr
          rw [ihr']

/-! ### The faithful PER-ASSET escrow lifecycle (over the `bal` ledger). -/

/-- **`cellLifecycleLive k c` — the kernel-level lifecycle-LIVENESS predicate (the D3 settle-target gate).**
Does cell `c`'s lifecycle admit new effects (a credit/debit landing on it)? `true` only for the Live
discriminant (`0`); a Sealed (`1`) or Destroyed (`3`) cell is fail-closed REJECTED. This is the
kernel-twin of `TurnExecutorFull.acceptsEffects`/`EffectsState.cellLive` (both read the SAME `lifecycle`
side-table and check `== 0`), defined HERE because the escrow/bridge SETTLE-target gates live in
`RecordKernel` (imported BY `TurnExecutorFull`, so it cannot import `acceptsEffects` back without a cycle).
`acceptsEffects k c = cellLifecycleLive k c` definitionally (`acceptsEffects_eq_cellLifecycleLive`), so the
two are interchangeable at the cutover. -/
def cellLifecycleLive (k : RecordKernelState) (c : CellId) : Bool := k.lifecycle c == 0

/-- **`createEscrowRawAsset`** — the per-asset create: a SINGLE-cell, single-asset DEBIT of `amount`
from `creator`'s asset `asset` column PLUS an insert of an unresolved `EscrowRecord` (carrying `asset`)
into the off-ledger holding-store. The `bal`-ledger supply of `asset` DROPS by `amount`; the per-asset
holding-store at `asset` RISES by `amount`; the COMBINED per-asset total at `asset` is preserved, every
other asset untouched. The per-asset analog of `createEscrowRaw` (which moved the scalar `cell` field). -/
def createEscrowRawAsset (k : RecordKernelState) (id creator recipient : CellId) (asset : AssetId)
    (amount : ℤ) : RecordKernelState :=
  { k with bal := recBalCreditCell k.bal creator asset (-amount)
           escrows := { id := id, creator := creator, recipient := recipient,
                        amount := amount, resolved := false, asset := asset } :: k.escrows }

/-- Park a queue-bound deposit: tags the escrow record with `(queueDep, queueMsg)` so dequeue cannot
refund a deposit parked for a different message in the same queue. -/
def createEscrowRawAssetQueue (k : RecordKernelState) (id creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (queueId msgHash : Nat) : RecordKernelState :=
  { k with bal := recBalCreditCell k.bal creator asset (-amount)
           escrows := { id := id, creator := creator, recipient := recipient,
                        amount := amount, resolved := false, asset := asset,
                        queueDep := some queueId, queueMsg := some msgHash } :: k.escrows }

/-- **`settleEscrowRawAsset`** — the per-asset settle (release/refund body): a SINGLE-cell,
single-asset CREDIT of `amount` to the settlement target at asset `asset` PLUS marking the record
resolved. The `bal`-ledger supply of `asset` RISES by `amount`; the per-asset holding-store at `asset`
DROPS by `amount`; the COMBINED per-asset total at `asset` is preserved. -/
def settleEscrowRawAsset (k : RecordKernelState) (id target : CellId) (asset : AssetId) (amount : ℤ) :
    RecordKernelState :=
  { k with bal := recBalCreditCell k.bal target asset amount
           escrows := markResolved k.escrows id }

/-- **`createEscrowKAsset` (executable, fail-closed).** Commits only when the actor is authorized over
the `creator` cell (same `authorizedB` gate as `transfer`), the amount is non-negative and available
*in asset `asset`* (`amount ≤ k.bal creator asset`), the creator is a live account, and the `id` is
NOT already in use. On commit: single-cell, single-asset debit + park the asset-typed record. -/
def createEscrowKAsset (k : RecordKernelState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecordKernelState :=
  if authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id) then
    some (createEscrowRawAsset k id creator recipient asset amount)
  else none

/-- **`releaseEscrowKAsset` (executable, fail-closed).** Looks up the unresolved record by `id`; on
success single-cell credits the `recipient` AT the record's asset and marks resolved. **SETTLE-LIVENESS
GATE** (`META-FILL C`, decision (7) hardened to a fail-closed gate rather than a carried hypothesis):
the settlement target MUST be a LIVE account (`r.recipient ∈ k.accounts`) — crediting a non-account
would silently DESTROY value (it vanishes from `recTotalAsset`, breaking combined conservation). This
is dregg1-faithful (you cannot credit a non-existent cell) and makes the per-asset combined-conservation
hold UNCONDITIONALLY (the keystone needs no carried `htgt`). -/
def releaseEscrowKAsset (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => if r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true then
                some (settleEscrowRawAsset k id r.recipient r.asset r.amount)
              else none
  | none   => none

/-- **`refundEscrowKAsset` (executable, fail-closed).** Looks up the unresolved record by `id`; on
success single-cell credits the `creator` (refund target) AT the record's asset and marks resolved.
**SETTLE-LIVENESS GATE** (the creator/refund target MUST be a LIVE account) — same rationale as
`releaseEscrowKAsset`: unconditional combined-conservation, dregg1-faithful. -/
def refundEscrowKAsset (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r => if r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true then
                some (settleEscrowRawAsset k id r.creator r.asset r.amount)
              else none
  | none   => none

/-! ### The REAL per-asset combined-conservation invariants. -/

/-- **`escrow_create_conserves_combined_per_asset` — THE HEADLINE (PROVED).** A committed per-asset
`createEscrowKAsset` PRESERVES the COMBINED per-asset total `recTotalAssetWithEscrow b` for EVERY asset
`b`: at the locked asset, the `bal`-ledger DROPS by `amount` (a real per-asset debit) while the
holding-store RISES by `amount` (combined fixed); at every OTHER asset BOTH terms are literally
unchanged. NON-VACUOUS: lock asset A and `recTotalAsset A` is genuinely lower while
`recTotalAssetWithEscrow A` is unchanged; `recTotalAssetWithEscrow B` (B≠A) unchanged with A's held
value non-zero — the no-cross-asset-laundering content at the escrow boundary. The per-asset drop-in of
`escrow_create_conserves_combined`: `recDebit_recTotal` → `recBalCreditCell_recTotalAsset`;
`escrowHeld_cons_unresolved` → `escrowHeldAsset_cons_unresolved`. -/
theorem escrow_create_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    set newRec : EscrowRecord := { id := id, creator := creator, recipient := recipient,
                                   amount := amount, resolved := false, asset := asset } with hnewRec
    show recTotalAssetWithEscrow (createEscrowRawAsset k id creator recipient asset amount) b
       = recTotalAssetWithEscrow k b
    unfold recTotalAssetWithEscrow createEscrowRawAsset
    have hbal : recTotalAsset { k with bal := recBalCreditCell k.bal creator asset (-amount),
                                       escrows := newRec :: k.escrows } b
        = recTotalAsset k b + (if b = asset then (-amount) else 0) := by
      show (∑ x ∈ k.accounts, recBalCreditCell k.bal creator asset (-amount) x b) = _
      exact recBalCreditCell_recTotalAsset k.accounts k.bal creator asset (-amount) hlive b
    have hheld : escrowHeldAsset { k with bal := recBalCreditCell k.bal creator asset (-amount),
                                          escrows := newRec :: k.escrows } b
        = escrowHeldAsset k b + (if asset = b then amount else 0) := by
      have hc := escrowHeldAsset_cons_unresolved
        { k with bal := recBalCreditCell k.bal creator asset (-amount) } newRec b rfl
      simpa [hnewRec] using hc
    rw [hbal, hheld]
    by_cases hba : b = asset
    · subst hba; simp only [if_true, if_pos rfl]; ring
    · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`escrow_settle_conserves_combined_per_asset` — PROVED (the settle half, completing the pair).** A
release/refund that settles the found record to `target` PRESERVES the COMBINED per-asset total
`recTotalAssetWithEscrow b` for EVERY asset `b`: at the record's asset the `+amount` single-cell credit
is offset by the holding-store DROP; every other asset is literally unchanged. NON-VACUOUS: the
`target ∈ accounts` hypothesis has TEETH — a credit to a non-account vanishes from `recTotalAsset`,
breaking conservation. The per-asset drop-in of `escrow_settle_conserves_combined`: `recCredit_recTotal`
→ `recBalCreditCell_recTotalAsset`; `heldSum_markResolved_found` → `heldSumAsset_markResolved_found`. -/
theorem escrow_settle_conserves_combined_per_asset (k : RecordKernelState) (id target : CellId)
    (r : EscrowRecord) (b : AssetId) (htgt : target ∈ k.accounts)
    (hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r) :
    recTotalAssetWithEscrow (settleEscrowRawAsset k id target r.asset r.amount) b
      = recTotalAssetWithEscrow k b := by
  unfold recTotalAssetWithEscrow settleEscrowRawAsset
  have hbal : recTotalAsset { k with bal := recBalCreditCell k.bal target r.asset r.amount,
                                     escrows := markResolved k.escrows id } b
      = recTotalAsset k b + (if b = r.asset then r.amount else 0) := by
    show (∑ x ∈ k.accounts, recBalCreditCell k.bal target r.asset r.amount x b) = _
    exact recBalCreditCell_recTotalAsset k.accounts k.bal target r.asset r.amount htgt b
  have hheld : escrowHeldAsset { k with bal := recBalCreditCell k.bal target r.asset r.amount,
                                        escrows := markResolved k.escrows id } b
      = escrowHeldAsset k b - (if r.asset = b then r.amount else 0) := by
    show heldSumAsset (markResolved k.escrows id) b = heldSumAsset k.escrows b - _
    exact heldSumAsset_markResolved_found id r b k.escrows hfind
  rw [hbal, hheld]
  by_cases hba : b = r.asset
  · subst hba; simp only [if_true, if_pos rfl]; ring
  · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring

/-- **`releaseEscrowKAsset` PRESERVES the COMBINED per-asset total — PROVED (UNCONDITIONAL).** The
settle-liveness obligation is DISCHARGED by the fail-closed gate (`r.recipient ∈ k.accounts` is checked
in the executor), so no carried `htgt` is needed — a committed release conserves the COMBINED per-asset
total at EVERY asset. Reads off `escrow_settle_conserves_combined_per_asset` with the gate supplying the
liveness premise. -/
theorem releaseEscrowKAsset_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    (b : AssetId) (h : releaseEscrowKAsset k id = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold releaseEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
      · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h; subst h
        exact escrow_settle_conserves_combined_per_asset k id r.recipient r b hlive.1 hfind
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-- **`refundEscrowKAsset` PRESERVES the COMBINED per-asset total — PROVED (UNCONDITIONAL).** The refund
half: value returns to the (LIVE, gate-checked) creator, the COMBINED per-asset total fixed at EVERY
asset; no carried `htgt`. -/
theorem refundEscrowKAsset_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    (b : AssetId) (h : refundEscrowKAsset k id = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold refundEscrowKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hlive : r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
      · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h; subst h
        exact escrow_settle_conserves_combined_per_asset k id r.creator r b hlive.1 hfind
      · rw [if_neg hlive] at h; exact absurd h (by simp)

/-- **`escrow_create_debits_per_asset` — PROVED.** A committed per-asset create DROPS asset `asset`'s
`bal`-ledger supply by `amount` (a real per-asset debit) and grows the holding-store by the asset-typed
record. The per-asset contrast with the combined-conservation: the BARE per-asset ledger genuinely
moves; only the COMBINED measure is fixed. -/
theorem escrow_create_debits_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    recTotalAsset k' asset = recTotalAsset k asset - amount ∧
      k'.escrows = { id := id, creator := creator, recipient := recipient,
                     amount := amount, resolved := false, asset := asset } :: k.escrows := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _⟩ := hg
    refine ⟨?_, rfl⟩
    show (∑ x ∈ k.accounts, recBalCreditCell k.bal creator asset (-amount) x asset) = _
    have := recBalCreditCell_recTotalAsset k.accounts k.bal creator asset (-amount) hlive asset
    simpa [recTotalAsset] using this
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`createEscrowKAsset_authorized` — PROVED.** A committed per-asset create required the actor to be
authorized over the `creator` cell. -/
theorem createEscrowKAsset_authorized {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §BRIDGE — the cross-chain bridge lock/finalize/cancel on the SHARED escrow holding-store (Wave-5).

dregg1's two-phase bridge (`turn/src/action.rs` `BridgeLock`/`BridgeFinalize`/`BridgeCancel`,
`turn/src/executor/apply.rs:1258`/`:1290`/`:1317`, lowered to `cell/src/note_bridge.rs`
`initiate_bridge`/`finalize_bridge`/`cancel_bridge`) is the bridge-shaped TWIN of escrow:

  * **bridgeLock** (Phase 1, `initiate_bridge`): DEBIT the originator + PARK the value in a `Locked`
    `PendingBridge` record — value inaccessible, AWAITING the other-chain confirmation. The off-ledger
    record is the SAME holding-store as escrow (`PendingBridgeSet` ≈ `escrows`), so we reuse the escrow
    store with a `bridge := true` tag. Double-lock REJECTED (`AlreadyLocked` — dregg1's `is_locked`).
    Combined per-asset CONSERVED (the debit is offset by the held rise) — IDENTICAL to `createEscrow`.
  * **bridgeFinalize** (Phase 3, `finalize_bridge`): the §8 confirmation receipt arrived and verified
    (the destination-federation signature over the nullifier — `verify_bridge_receipt`, the §8 portal);
    the lock resolves and the value LEAVES for the other chain. dregg1 marks the record `Finalized` AND
    makes the nullifier permanent (a real BURN on this side). On the COMBINED measure this is a
    no-credit resolve: the bare `bal` is untouched (the value already left the ledger at lock) but the
    held value DROPS — so `recTotalAssetWithEscrow` DROPS by the bridged amount, a DISCLOSED OUTFLOW
    (like burn). This is the ONE place the holding-store pair does NOT conserve — and honestly so.
  * **bridgeCancel** (Phase 4, `cancel_bridge`): the timeout was reached without a receipt; the note is
    UNLOCKED and the value REFUNDED to the originator. dregg1 marks the record `Cancelled`; the value
    returns to the locker. On the COMBINED measure this is a SETTLE back to the creator (credit + resolve)
    — combined per-asset CONSERVED, IDENTICAL to `refundEscrow`.

We reuse `createEscrowRawAsset` (tagged `bridge := true`), `settleEscrowRawAsset` (for cancel/refund),
`markResolved` (for finalize), and the per-asset held-sum lemmas verbatim — the bridge tag is INERT to
the find?/markResolved lockstep (it filters on `id ∧ unresolved`, not on `bridge`), so all the proof
spine carries. The §8 receipt is carried as a `Prop`-carrier hypothesis exactly as `bridgeMint`'s
foreign finality. -/

/-- **`createBridgeRawAsset`** — the per-asset bridge LOCK: a SINGLE-cell, single-asset DEBIT of `amount`
from the originator's asset `asset` column PLUS an insert of an UNRESOLVED, `bridge := true`-tagged
`EscrowRecord` into the SHARED off-ledger holding-store. The `bal`-ledger supply of `asset` DROPS by
`amount`; the per-asset holding-store at `asset` RISES by `amount`; the COMBINED per-asset total at
`asset` is preserved — IDENTICAL shape to `createEscrowRawAsset`, only the `bridge` tag differs. -/
def createBridgeRawAsset (k : RecordKernelState) (id originator destination : CellId) (asset : AssetId)
    (amount : ℤ) : RecordKernelState :=
  { k with bal := recBalCreditCell k.bal originator asset (-amount)
           escrows := { id := id, creator := originator, recipient := destination,
                        amount := amount, resolved := false, asset := asset, bridge := true } :: k.escrows }

/-- **`bridgeFinalizeRawAsset`** — the bridge FINALIZE body: mark the found record resolved WITHOUT a
credit. The `bal`-ledger is LEFT UNTOUCHED (the value already left the ledger at lock and now leaves for
the other chain — a BURN), but the per-asset holding-store DROPS by `amount` as the record leaves the
unresolved set. So the COMBINED per-asset total DROPS by `amount` — a disclosed OUTFLOW (NOT a settle
back onto the ledger). The honest contrast with `settleEscrowRawAsset` (which credits, conserving). -/
def bridgeFinalizeRawAsset (k : RecordKernelState) (id : Nat) : RecordKernelState :=
  { k with escrows := markResolved k.escrows id }

/-- **`bridgeLockKAsset` (executable, fail-closed).** Commits only when the actor is authorized over the
originator cell (same `authorizedB` gate as `transfer`/escrow-create), the amount is non-negative and
available *in asset `asset`*, the originator is a live account, and the `id` is NOT already in use
(dregg1's `AlreadyLocked` double-lock rejection — `is_locked`). On commit: single-cell debit + park the
bridge-tagged record. The §8 spending proof is carried at the theorem layer. -/
def bridgeLockKAsset (k : RecordKernelState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) : Option RecordKernelState :=
  if authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ cellLifecycleLive k originator = true
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id) then
    some (createBridgeRawAsset k id originator destination asset amount)
  else none

/-- **`bridgeFinalizeKAsset` (executable, fail-closed).** Looks up the first unresolved record by `id`,
requires it to be a BRIDGE record, and checks the parked record's `(asset, amount)` MATCH the
receipt-DISCLOSED `(asset, amount)` (dregg1's finalize verifies the receipt against the pending bridge
— `finalize_bridge` checks nullifier/destination consistency); on a match, marks it resolved WITHOUT a
credit — the value LEFT for the other chain (the burn). The §8 confirmation receipt (the
destination-federation signature, `verify_bridge_receipt`) is the THEOREM-level portal — here we model
the LEDGER move gated on the record being present-and-unresolved, bridge-tagged (`Locked` bridge state),
and matching the disclosed outflow. Rejects a missing/already-resolved/non-bridge/mismatched record. -/
def bridgeFinalizeKAsset (k : RecordKernelState) (id : Nat) (asset : AssetId) (amount : ℤ) :
    Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r =>
      if r.bridge = true ∧ r.asset = asset ∧ r.amount = amount then
        some (bridgeFinalizeRawAsset k id)
      else none
  | none   => none

/-- **`bridgeCancelKAsset` (executable, fail-closed).** Looks up the first unresolved record by `id` and
requires it to be a BRIDGE record; on success single-cell credits the `creator` (the ORIGINATOR — the
refund target) AT the record's asset and marks resolved (dregg1's `cancel_bridge` — note unlocked,
value returned to the owner). **SETTLE-LIVENESS GATE** (the originator MUST be a LIVE account) — same
rationale as `refundEscrowKAsset`: crediting a non-account would silently DESTROY value, breaking
combined conservation; this makes the per-asset combined-conservation hold UNCONDITIONALLY. The
timeout gate is carried at the effect/theorem layer. Non-bridge escrow records reject. -/
def bridgeCancelKAsset (k : RecordKernelState) (id : Nat) : Option RecordKernelState :=
  match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some r =>
      if r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true then
        some (settleEscrowRawAsset k id r.creator r.asset r.amount)
      else none
  | none   => none

/-! ### The REAL bridge combined-measure invariants. -/

/-- **`bridge_lock_conserves_combined_per_asset` — PROVED (the LOCK half).** A committed bridge LOCK
PRESERVES the COMBINED per-asset total `recTotalAssetWithEscrow b` for EVERY asset `b`: at the locked
asset the `bal`-ledger DROPS by `amount` while the holding-store RISES by `amount` (combined fixed); at
every OTHER asset BOTH terms are unchanged. The bridge tag is INERT to the measure (`recTotalAssetWithEscrow`
sums on `resolved`/`asset`, not `bridge`), so this is the per-asset escrow-create proof verbatim with
`bridge := true` carried through. NON-VACUOUS: lock asset A and `recTotalAsset A` is genuinely lower while
`recTotalAssetWithEscrow A` is unchanged — the value moved into the holding-store, not destroyed. -/
theorem bridge_lock_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ} (b : AssetId)
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ cellLifecycleLive k originator = true
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _, _⟩ := hg
    set newRec : EscrowRecord := { id := id, creator := originator, recipient := destination,
                                   amount := amount, resolved := false, asset := asset, bridge := true } with hnewRec
    show recTotalAssetWithEscrow (createBridgeRawAsset k id originator destination asset amount) b
       = recTotalAssetWithEscrow k b
    unfold recTotalAssetWithEscrow createBridgeRawAsset
    have hbal : recTotalAsset { k with bal := recBalCreditCell k.bal originator asset (-amount),
                                       escrows := newRec :: k.escrows } b
        = recTotalAsset k b + (if b = asset then (-amount) else 0) := by
      show (∑ x ∈ k.accounts, recBalCreditCell k.bal originator asset (-amount) x b) = _
      exact recBalCreditCell_recTotalAsset k.accounts k.bal originator asset (-amount) hlive b
    have hheld : escrowHeldAsset { k with bal := recBalCreditCell k.bal originator asset (-amount),
                                          escrows := newRec :: k.escrows } b
        = escrowHeldAsset k b + (if asset = b then amount else 0) := by
      have hc := escrowHeldAsset_cons_unresolved
        { k with bal := recBalCreditCell k.bal originator asset (-amount) } newRec b rfl
      simpa [hnewRec] using hc
    rw [hbal, hheld]
    by_cases hba : b = asset
    · subst hba; simp only [if_true, if_pos rfl]; ring
    · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridge_lock_debits_per_asset` — PROVED.** A committed bridge LOCK DROPS the locked asset's
`bal`-ledger supply by `amount` (a real per-asset debit) and grows the holding-store by the bridge-tagged
record — the bare per-asset ledger genuinely MOVES (the contrast with the combined-conservation; the
value is now INACCESSIBLE in the lock, AWAITING the other chain). -/
theorem bridge_lock_debits_per_asset {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    recTotalAsset k' asset = recTotalAsset k asset - amount ∧
      k'.escrows = { id := id, creator := originator, recipient := destination,
                     amount := amount, resolved := false, asset := asset, bridge := true } :: k.escrows := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ cellLifecycleLive k originator = true
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hlive, _, _⟩ := hg
    refine ⟨?_, rfl⟩
    show (∑ x ∈ k.accounts, recBalCreditCell k.bal originator asset (-amount) x asset) = _
    have := recBalCreditCell_recTotalAsset k.accounts k.bal originator asset (-amount) hlive asset
    simpa [recTotalAsset] using this
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridgeLockKAsset_authorized` — PROVED.** A committed bridge LOCK required the actor to be
authorized over the debited originator cell (the SAME `authorizedB` gate as `transfer`). -/
theorem bridgeLockKAsset_authorized {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true := by
  unfold bridgeLockKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
      ∧ cellLifecycleLive k originator = true
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`bridge_finalize_moves_combined_per_asset` — THE BRIDGE HEADLINE (PROVED, the FINALIZE half).** A
committed bridge FINALIZE MOVES the COMBINED per-asset total `recTotalAssetWithEscrow b` by EXACTLY the
disclosed `-amount` at the bridged asset (`-r.amount` when `r.asset = b`), and leaves EVERY OTHER asset
LITERALLY FIXED. The bare `bal` is untouched (no credit), and the held value DROPS as the record leaves
the unresolved set (`heldSumAsset_markResolved_found`) — so the COMBINED measure drops by the bridged
amount. This is the value genuinely LEAVING for the other chain — a disclosed OUTFLOW (like burn), NOT a
conservation claim. The ONE holding-store resolution that does NOT conserve, and honestly so. NON-VACUOUS:
the drop is GUARDED by `r.asset = b`, so the bridged asset falls by exactly `r.amount` while the OTHER
asset is fixed — no cross-asset laundering at the bridge boundary. -/
theorem bridge_finalize_moves_combined_per_asset (k : RecordKernelState) (id : Nat) (r : EscrowRecord)
    (b : AssetId)
    (hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r) :
    recTotalAssetWithEscrow (bridgeFinalizeRawAsset k id) b
      = recTotalAssetWithEscrow k b - (if r.asset = b then r.amount else 0) := by
  unfold recTotalAssetWithEscrow bridgeFinalizeRawAsset
  -- the `bal` ledger is untouched (no credit on finalize):
  have hbal : recTotalAsset { k with escrows := markResolved k.escrows id } b = recTotalAsset k b := rfl
  -- the held value drops by the found record's amount IFF its asset is `b`:
  have hheld : escrowHeldAsset { k with escrows := markResolved k.escrows id } b
      = escrowHeldAsset k b - (if r.asset = b then r.amount else 0) := by
    show heldSumAsset (markResolved k.escrows id) b = heldSumAsset k.escrows b - _
    exact heldSumAsset_markResolved_found id r b k.escrows hfind
  rw [hbal, hheld]; ring

/-- **`bridgeFinalizeKAsset_moves_combined_per_asset` — THE BRIDGE HEADLINE (PROVED).** A committed bridge
finalize MOVES the COMBINED per-asset measure by EXACTLY the DISCLOSED `-amount` at the disclosed `asset`
(`-amount` when `b = asset`, `0` elsewhere) — a function of the ACTION's disclosed `(asset, amount)`, NOT
of the hidden record (the executor's match-gate ties them). The bridged value LEFT for the other chain: a
disclosed OUTFLOW, no cross-asset laundering (the OTHER asset is literally fixed). The match-gate
(`r.asset = asset ∧ r.amount = amount`) rewrites the record-amount drop of
`bridge_finalize_moves_combined_per_asset` into the disclosed-amount drop. -/
theorem bridgeFinalizeKAsset_moves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    {asset : AssetId} {amount : ℤ} (b : AssetId) (h : bridgeFinalizeKAsset k id asset amount = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b - (if b = asset then amount else 0) := by
  unfold bridgeFinalizeKAsset at h
  cases hfind : k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hm : r.bridge = true ∧ r.asset = asset ∧ r.amount = amount
      · rw [if_pos hm] at h; simp only [Option.some.injEq] at h
        obtain ⟨_, hra, hrm⟩ := hm
        rw [← h, bridge_finalize_moves_combined_per_asset k id r b hfind]
        -- rewrite the record's (asset, amount) into the disclosed (asset, amount):
        rw [hra, hrm]
        -- the remaining `if asset = b` vs `if b = asset` differ only by symmetry of `=`:
        by_cases hba : b = asset
        · rw [if_pos hba, if_pos hba.symm]
        · rw [if_neg hba, if_neg (fun heq => hba heq.symm)]
      · rw [if_neg hm] at h; exact absurd h (by simp)

/-- **`bridge_cancel_conserves_combined_per_asset` — PROVED (the CANCEL half, the refund round-trip).** A
committed bridge CANCEL PRESERVES the COMBINED per-asset total at EVERY asset: the value returns to the
(LIVE, gate-checked) originator — the `+amount` credit is offset by the holding-store drop. The timeout
having been reached is the effect-layer gate; here the LEDGER move conserves. UNCONDITIONAL (the
settle-liveness obligation is discharged by the fail-closed `r.creator ∈ accounts` gate). Reads off
`escrow_settle_conserves_combined_per_asset` (the bridge tag is inert to the settle). -/
theorem bridge_cancel_conserves_combined_per_asset {k k' : RecordKernelState} {id : Nat}
    (b : AssetId) (h : bridgeCancelKAsset k id = some k') :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold bridgeCancelKAsset at h
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some r =>
      rw [hfind] at h; simp only at h
      by_cases hg : r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
        have hlive : r.creator ∈ k.accounts := hg.2.1
        exact escrow_settle_conserves_combined_per_asset k id r.creator r b hlive hfind
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §D3 — SECONDARY-CELL LIFECYCLE-LIVENESS TEETH (the credited/debited cell must be Live).

The R6 fix (`EffectsState.cellLive`/`acceptsEffects`) gated the FIELD-WRITE target. D3 cascades the SAME
lifecycle-liveness discriminant to the SECONDARY cells these holding-store effects credit/debit WITHOUT a
prior liveness check: the escrow RELEASE/REFUND RECIPIENT/CREATOR, the bridge LOCK ORIGINATOR, and the
bridge CANCEL ORIGINATOR. Previously each gated only on MEMBERSHIP (`∈ accounts`) — a Sealed/Destroyed but
still-member cell would be credited/debited, smuggling value onto a cell that `cellSeal` had frozen.
The `cellLifecycleLive` conjunct closes that: a settle into a non-Live cell now FAILS CLOSED (`none`),
matching the field-write gate. Each is a fail-closed teeth theorem + a non-vacuity #guard below. -/

/-- **`releaseEscrowKAsset_nonlive_fails` — PROVED (FAIL-CLOSED, the D3 escrow-release teeth).** A
release whose found record's RECIPIENT is NOT lifecycle-live (`cellLifecycleLive = false`: Sealed/Destroyed)
does NOT commit — even if the recipient is still a member. Crediting a frozen cell is rejected. -/
theorem releaseEscrowKAsset_nonlive_fails {k : RecordKernelState} {id : Nat} {r : EscrowRecord}
    (hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive k r.recipient = false) :
    releaseEscrowKAsset k id = none := by
  unfold releaseEscrowKAsset
  rw [hfind]
  simp only [hdead, Bool.false_eq_true, and_false, if_false]

/-- **`refundEscrowKAsset_nonlive_fails` — PROVED (FAIL-CLOSED, the D3 escrow-refund teeth).** A refund
whose found record's CREATOR (the refund target) is NOT lifecycle-live does NOT commit. -/
theorem refundEscrowKAsset_nonlive_fails {k : RecordKernelState} {id : Nat} {r : EscrowRecord}
    (hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive k r.creator = false) :
    refundEscrowKAsset k id = none := by
  unfold refundEscrowKAsset
  rw [hfind]
  simp only [hdead, Bool.false_eq_true, and_false, if_false]

/-- **`bridgeLockKAsset_nonlive_fails` — PROVED (FAIL-CLOSED, the D3 bridge-lock teeth).** A bridge lock
whose ORIGINATOR (the debited cell) is NOT lifecycle-live does NOT commit — a Sealed/Destroyed cell cannot
have value locked out of it (it is frozen). -/
theorem bridgeLockKAsset_nonlive_fails {k : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (hdead : cellLifecycleLive k originator = false) :
    bridgeLockKAsset k id actor originator destination asset amount = none := by
  unfold bridgeLockKAsset
  simp only [hdead, Bool.false_eq_true, and_false, false_and, if_false]

/-- **`bridgeCancelKAsset_nonlive_fails` — PROVED (FAIL-CLOSED, the D3 bridge-cancel teeth).** A bridge
cancel whose found record's ORIGINATOR/CREATOR (the refund target) is NOT lifecycle-live does NOT commit. -/
theorem bridgeCancelKAsset_nonlive_fails {k : RecordKernelState} {id : Nat} {r : EscrowRecord}
    (hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive k r.creator = false) :
    bridgeCancelKAsset k id = none := by
  unfold bridgeCancelKAsset
  rw [hfind]
  simp only [hdead, Bool.false_eq_true, and_false, if_false]

#assert_axioms releaseEscrowKAsset_nonlive_fails
#assert_axioms refundEscrowKAsset_nonlive_fails
#assert_axioms bridgeLockKAsset_nonlive_fails
#assert_axioms bridgeCancelKAsset_nonlive_fails

/-! ### §BRIDGE runs (`#eval`) — the lock/finalize/cancel triple has teeth on the combined measure. -/

/-- A 2-cell, 2-asset bridge fixture: cell 0 holds 100 of asset 1; cell 1 holds 0. Actor 0 owns cell 0
(`node 1` self-cap is not needed — ownership authorizes the lock over src 0). -/
def brg0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

/-- Lock 30 of asset 1 from originator 0 → destination 1, bridge id 9. -/
def brgLocked : Option RecordKernelState := bridgeLockKAsset brg0 9 0 0 1 1 30

-- LOCK: bare ledger DROPS at asset 1 (100→70), held RISES to 30, COMBINED CONSERVED at (100, 0).
#guard ((recTotalAssetWithEscrow brg0 1, recTotalAssetWithEscrow brg0 0)) == (100, 0)  --  (100, 0)
#guard (brgLocked.map (fun k => (recTotalAsset k 1, escrowHeldAsset k 1))) == some (70, 30)  --  some (70, 30) — bare DOWN, held UP
#guard (brgLocked.map (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0))) == some (100, 0)  --  some (100, 0) — CONSERVED both
-- the parked record carries the bridge tag (it is in the SHARED escrow store, tagged):
#guard (brgLocked.map (fun k => k.escrows.map (fun r => (r.id, r.amount, r.asset, r.bridge)))) == some [(9, 30, 1, true)]  --  some [(9, 30, 1, true)]
-- LOCK then CANCEL (refund to originator 0): COMBINED stays (100, 0), held returns to 0, bal back to 100.
#guard ((brgLocked.bind (fun k => bridgeCancelKAsset k 9)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))) == some (100, 0, 0, 100)  --  some (100, 0, 0, 100) — REFUND round-trip CONSERVED
-- LOCK then FINALIZE (value LEFT for the other chain): COMBINED DROPS by 30 at asset 1 (100→70),
--   asset 0 FIXED at 0; held drops to 0; the bare bal STAYS at 70 (the value already left, now burned).
--   The finalize DISCLOSES the bridged (asset 1, amount 30) — the executor gates on the record matching.
#guard ((brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 1 30)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))) == some (70, 0, 0, 70)  --  some (70, 0, 0, 70) — COMBINED -30 at asset 1, asset 0 FIXED
-- double-finalize fail-closed (the record is already resolved):
#guard (((brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 1 30)).bind
        (fun k => bridgeFinalizeKAsset k 9 1 30)).isSome) == false  --  false
-- MISMATCHED finalize fail-closed (disclosed amount 99 ≠ parked 30, the receipt-vs-pending check):
#guard ((brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 1 99)).isSome) == false  --  false
-- MISMATCHED-asset finalize fail-closed (disclosed asset 0 ≠ parked 1):
#guard ((brgLocked.bind (fun k => bridgeFinalizeKAsset k 9 0 30)).isSome) == false  --  false
-- double-lock fail-closed (the id is already in use):
#guard ((brgLocked.bind (fun k => bridgeLockKAsset k 9 0 0 1 1 10)).isSome) == false  --  false
-- unauthorized lock fail-closed (actor 5 owns nothing):
#guard ((bridgeLockKAsset brg0 9 5 0 1 1 30).isSome) == false  --  false
-- ORDINARY escrow rows in the shared holding-store are NOT bridge rows: finalize/cancel reject them.
def brgOrdinaryEscrowSameId : RecordKernelState :=
  { brg0 with
    escrows := [{ id := 9, creator := 0, recipient := 1, amount := 30, resolved := false,
                  asset := 1, bridge := false }] }

#guard ((bridgeFinalizeKAsset brgOrdinaryEscrowSameId 9 1 30).isSome) == false  --  false
#guard ((bridgeCancelKAsset brgOrdinaryEscrowSameId 9).isSome) == false  --  false

/-! ### §D3-TEETH non-vacuity: the SECONDARY cell being Sealed REJECTS the credit/debit (was committing).

A bridge LOCK from a SEALED originator (cell 0 flipped to lifecycle `1`) is now REJECTED — was `true`
(value locked out of a frozen cell). A bridge CANCEL refunding a SEALED originator is REJECTED. An escrow
RELEASE into a SEALED recipient is REJECTED. Each LIVE counterpart still COMMITS — the gate only tightens
the non-live case. -/

/-- `brg0` with cell 0 flipped to Sealed (lifecycle `1`); cell 0 still EXISTS + actor 0 still OWNS it. -/
def brgSealed0 : RecordKernelState := { brg0 with lifecycle := fun c => if c = 0 then 1 else 0 }

-- A bridge LOCK debiting the now-SEALED originator 0 is REJECTED (D3 CLOSED) — was `true` (the live HOLE):
#guard ((bridgeLockKAsset brgSealed0 9 0 0 1 1 30).isSome) == false  --  false (D3 CLOSED)
-- ...even though authority + membership + balance STILL hold (the cell exists, the actor owns it, funded):
#guard (decide (0 ∈ brgSealed0.accounts) && decide (30 ≤ brgSealed0.bal 0 1))  --  true
-- A LIVE originator (the default brg0, lifecycle 0) still locks — the gate only tightens the sealed case:
#guard ((bridgeLockKAsset brg0 9 0 0 1 1 30).isSome)  --  true (live originator ok)

-- An escrow RELEASE/REFUND into a SEALED recipient/creator is REJECTED. Park a record on brg0 (live),
-- then SEAL the settle target before settling. The parked record id 7 has creator 0, RECIPIENT 1:
def escParked : Option RecordKernelState := createEscrowKAsset brg0 7 0 0 1 1 30  -- creator 0, recipient 1
/-- The parked state with the RECIPIENT (cell 1) flipped to Sealed (the release target). -/
def escParkedRecipSealed : Option RecordKernelState :=
  escParked.map (fun k => { k with lifecycle := fun c => if c = 1 then 1 else 0 })
/-- The parked state with the CREATOR (cell 0) flipped to Sealed (the refund target). -/
def escParkedCreatorSealed : Option RecordKernelState :=
  escParked.map (fun k => { k with lifecycle := fun c => if c = 0 then 1 else 0 })
-- RELEASE into the now-SEALED recipient (cell 1) is REJECTED (D3 CLOSED); the LIVE parked release commits:
#guard ((escParkedRecipSealed.bind (fun k => releaseEscrowKAsset k 7)).isSome) == false  --  false (D3 CLOSED)
#guard ((escParked.bind (fun k => releaseEscrowKAsset k 7)).isSome)  --  true (live recipient ok)
-- REFUND to the now-SEALED creator (cell 0) is REJECTED (D3 CLOSED); the LIVE parked refund commits:
#guard ((escParkedCreatorSealed.bind (fun k => refundEscrowKAsset k 7)).isSome) == false  --  false (D3 CLOSED)
#guard ((escParked.bind (fun k => refundEscrowKAsset k 7)).isSome)  --  true (live creator ok)
-- A bridge CANCEL refunding the now-SEALED originator is REJECTED; the LIVE locked cancel commits:
#guard ((brgLocked.map (fun k => { k with lifecycle := fun c => if c = 0 then 1 else 0 })).bind
        (fun k => bridgeCancelKAsset k 9)).isSome == false  --  false (D3 CLOSED)
#guard ((brgLocked.bind (fun k => bridgeCancelKAsset k 9)).isSome)  --  true (live originator ok)

#assert_axioms bridge_lock_conserves_combined_per_asset
#assert_axioms bridge_lock_debits_per_asset
#assert_axioms bridgeLockKAsset_authorized
#assert_axioms bridge_finalize_moves_combined_per_asset
#assert_axioms bridgeFinalizeKAsset_moves_combined_per_asset
#assert_axioms bridge_cancel_conserves_combined_per_asset

/-! ### §NOTE-CREATE — the grow-only COMMITMENT SET (faithful to dregg1's `apply_note_create`).

dregg1's `apply_note_create` inserts a fresh Pedersen commitment into the off-ledger commitment tree;
the §8 crypto (range proof on the hidden value) is a `CryptoPortal` carried at the effect layer. The
note's hidden value's ASSET is OUT OF SCOPE here (behind the CryptoPortal) — `noteCreate` is
bal-NEUTRAL: it grows the `commitments` SET only, NOT `bal`/`nullifiers`/`escrows`. (A fresh
commitment is always fresh, so — unlike `noteSpend`'s double-spend gate — there is no rejection; the
grow-only insert is the dual of the nullifier set.) -/

/-- **`noteCreateCommitment` (executable)** — insert a fresh note commitment `cm` into the off-ledger
commitment SET (the grow-only dual of `noteSpendNullifier`). bal-NEUTRAL: it touches NEITHER `bal` NOR
`nullifiers` NOR `escrows`. Always commits (a fresh commitment cannot conflict). -/
def noteCreateCommitment (k : RecordKernelState) (cm : Nat) : RecordKernelState :=
  { k with commitments := cm :: k.commitments }

/-- **`noteCreate_inserts` — PROVED.** A `noteCreateCommitment` actually inserts `cm` into the
commitment set. -/
theorem noteCreate_inserts (k : RecordKernelState) (cm : Nat) :
    cm ∈ (noteCreateCommitment k cm).commitments := by
  unfold noteCreateCommitment; simp

/-- **`noteCreate_recTotalAsset` — PROVED (bal-NEUTRALITY).** A `noteCreateCommitment` leaves
`recTotalAsset b` and `escrowHeldAsset b` (hence `recTotalAssetWithEscrow b`) UNCHANGED for EVERY asset
`b`: it grows only the commitment SET, never the `bal` ledger nor the `escrows` store. -/
theorem noteCreate_recTotalAsset (k : RecordKernelState) (cm : Nat) (b : AssetId) :
    recTotalAsset (noteCreateCommitment k cm) b = recTotalAsset k b
      ∧ escrowHeldAsset (noteCreateCommitment k cm) b = escrowHeldAsset k b := ⟨rfl, rfl⟩

/-! ## §QUEUE — the kernel-level ring-buffer FIFO transitions (Wave-7 de-THIN).

The queue side-table transitions, each FAIL-CLOSED exactly where dregg1 fails closed: allocate creates a
fresh record (rejecting a duplicate id); enqueue APPENDS to the tail and REJECTS at capacity
(`apply.rs:3348`); dequeue REMOVES-FROM-FRONT and REJECTS when empty (`apply.rs:3444`); resize grows the
capacity (rejecting a shrink below the current occupancy, `apply.rs` `QueueResize` "can't shrink below
current occupancy"). All FOUR are balance-NEUTRAL — they touch ONLY `queues`, never `bal`/`escrows`. -/

/-- **`queueAllocateK`** — create a fresh queue `id` with `owner`/`capacity` and an EMPTY buffer.
Fail-closed if the id already exists (no duplicate queue). dregg1's `apply_queue_allocate` derives a
fresh queue cell. balance-NEUTRAL. -/
def queueAllocateK (k : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat) :
    Option RecordKernelState :=
  match findQueue k.queues id with
  | some _ => none
  | none   => some { k with queues := { id := id, owner := owner, capacity := capacity, buffer := [] } :: k.queues }

/-- **`queueEnqueueK`** — APPEND `m` to the tail of queue `id`'s buffer. Fail-closed if the queue is
absent OR FULL (`buffer.length ≥ capacity`, dregg1 `apply.rs:3348`). balance-NEUTRAL. -/
def queueEnqueueK (k : RecordKernelState) (id : Nat) (m : Nat) : Option RecordKernelState :=
  match findQueue k.queues id with
  | none   => none
  | some q =>
      if q.buffer.length < q.capacity then
        some { k with queues := replaceQueue k.queues id { q with buffer := qbufEnqueue q.buffer m } }
      else
        none

/-- **`queueDequeueK`** — REMOVE-FROM-FRONT of queue `id`'s buffer, gated on `actor = owner` (only the
owner may dequeue, dregg1 `apply.rs:3433`). Fail-closed if the queue is absent, the actor is not the
owner, OR the queue is EMPTY (`apply.rs:3444`). Returns the post-state AND the dequeued head message (the
FIFO order witness). balance-NEUTRAL. -/
def queueDequeueK (k : RecordKernelState) (id : Nat) (actor : CellId) :
    Option (RecordKernelState × Nat) :=
  match findQueue k.queues id with
  | none   => none
  | some q =>
      if actor = q.owner then
        match qbufDequeue q.buffer with
        | none            => none
        | some (m, rest)  =>
            some ({ k with queues := replaceQueue k.queues id { q with buffer := rest } }, m)
      else
        none

/-- **`queueResizeK`** — change queue `id`'s capacity to `newCap`. Fail-closed if the queue is absent OR
the new capacity is below the current occupancy ("can't shrink below current occupancy",
`apply.rs:3534`). balance-NEUTRAL. -/
def queueResizeK (k : RecordKernelState) (id : Nat) (newCap : Nat) : Option RecordKernelState :=
  match findQueue k.queues id with
  | none   => none
  | some q =>
      if q.buffer.length ≤ newCap then
        some { k with queues := replaceQueue k.queues id { q with capacity := newCap } }
      else
        none

/-- **`queueAllocateK_balNeutral` — PROVED.** Allocate leaves `recTotalAsset`/`escrowHeldAsset` (hence
`recTotalAssetWithEscrow`) UNCHANGED ∀ asset: it grows only `queues`, never `bal`/`escrows`. -/
theorem queueAllocateK_balNeutral {k k' : RecordKernelState} {id : Nat} {owner : CellId} {capacity : Nat}
    (h : queueAllocateK k id owner capacity = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold queueAllocateK at h
  cases hf : findQueue k.queues id with
  | some q => simp only [hf] at h; exact absurd h (by simp)
  | none   => simp only [hf] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- **`queueEnqueueK_balNeutral` — PROVED.** Enqueue is balance-NEUTRAL (touches only `queues`). -/
theorem queueEnqueueK_balNeutral {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold queueEnqueueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **`queueDequeueK_balNeutral` — PROVED.** Dequeue is balance-NEUTRAL (touches only `queues`). -/
theorem queueDequeueK_balNeutral {k k' : RecordKernelState} {id : Nat} {actor : CellId} {m : Nat}
    (h : queueDequeueK k id actor = some (k', m)) (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none           => rw [hd] at h; exact absurd h (by simp)
        | some hr        =>
            obtain ⟨hm, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk; exact ⟨rfl, rfl⟩
      · rw [if_neg ho] at h; exact absurd h (by simp)

/-- **`queueResizeK_balNeutral` — PROVED.** Resize is balance-NEUTRAL (touches only `queues`). -/
theorem queueResizeK_balNeutral {k k' : RecordKernelState} {id newCap : Nat}
    (h : queueResizeK k id newCap = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold queueResizeK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length ≤ newCap
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · rw [if_neg hc] at h; exact absurd h (by simp)

/-! ## §QUEUE-DEPOSIT — the REFUNDABLE ANTI-SPAM DEPOSIT (Wave-8 residual close).

dregg1's `apply_queue_enqueue` (`turn/src/executor/apply.rs:3372-3386`) does TWO things: it appends the
message hash to the FIFO buffer AND it moves a REFUNDABLE DEPOSIT — `set_balance(actor - deposit)` +
`set_balance(queue + deposit)`, gated on `actor_cell.state.balance() >= deposit` (`:3361`, fail-closed
`InsufficientBalance`). `apply_queue_dequeue` (`:3483-3501`) REFUNDS the per-message deposit to the
dequeuer (`set_balance(queue - refund)` + `set_balance(dequeuer + refund)`). Wave-7 installed the
message-ORDER but left the deposit unmodeled (`queueEnqueueK`/`queueDequeueK` bal-NEUTRAL). We CLOSE
that residual: the deposit is a REFUNDABLE PARK — value leaves the sender's `bal` ledger and is held
OFF-ledger (in the SHARED escrow holding-store, tagged to the queue) until the dequeuer claims its
refund. This is IDENTICAL in shape to `createEscrowRawAsset`/`settleEscrowRawAsset` (the proven
combined-conservation pair) — so `recTotalAsset` GENUINELY MOVES at enqueue (the deposit leaves the
ledger), while the COMBINED `recTotalAssetWithEscrow` is CONSERVED (the parked value is counted in the
holding-store). The dequeuer's refund settles it back (combined conserved again). The deposit record
reuses `EscrowRecord` with `creator := sender` (refund-on-fail target), `recipient := queueOwner`,
keyed by the deposit `id`; it lives in `escrows`, INERT to the FIFO buffer / queue side-table.

We COMPOSE the FIFO transition (`queueEnqueueK`/`queueDequeueK`, carrying ALL the order/capacity/owner/
emptiness gates UNCHANGED) with the escrow PARK/SETTLE (carrying the deposit + the combined-conservation
spine UNCHANGED): the two operate on DISJOINT state slices (`queues` vs `bal`+`escrows`), so they
commute and BOTH bodies of proof carry verbatim. -/

/-- **`queueEnqueueDepositK`** — APPEND `m` to the tail of queue `id`'s FIFO buffer (the Wave-7
order op, fail-closed if absent OR FULL) AND PARK a refundable anti-spam `deposit` of asset `dAsset`
from `sender` into the SHARED holding-store, keyed by the deposit-record id `depId`, with
`creator := sender` (refund target) and `recipient := owner` (the queue owner). Fail-closed if the FIFO
gate rejects, if the deposit is negative, if `sender` lacks the deposit IN that asset
(`apply.rs:3361`), if `sender` is not a live account, or if the deposit-record `depId` is already in
use. The `bal` ledger of `dAsset` DROPS by `deposit` (a real per-asset debit — `recTotalAsset` MOVES)
while the holding-store at `dAsset` RISES by `deposit` (COMBINED conserved), EXACTLY like
`createEscrowRawAsset`. -/
def queueEnqueueDepositK (k : RecordKernelState) (id m : Nat) (sender owner : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ) : Option RecordKernelState :=
  match queueEnqueueK k id m with
  | none    => none
  | some k₁ =>
      if 0 ≤ deposit ∧ deposit ≤ k₁.bal sender dAsset ∧ sender ∈ k₁.accounts
          ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId) then
        some (createEscrowRawAssetQueue k₁ depId sender owner dAsset deposit id m)
      else none

/-- Look up an unresolved deposit record by `depId` in the global `escrows` table. -/
def findUnresolvedDeposit (k : RecordKernelState) (depId : Nat) : Option EscrowRecord :=
  k.escrows.find? (fun r => decide (r.id = depId ∧ r.resolved = false))

/-- **P0-1 recipient gate.** The named deposit must be DESTINED to the dequeuer. -/
def dequeueRecipientBindB (k : RecordKernelState) (actor : CellId) (depId : Nat) : Bool :=
  match findUnresolvedDeposit k depId with
  | some r => decide (r.recipient = actor)
  | none   => false

/-- **P0-1-full message gate.** The deposit must be bound to queue `queueId` and the dequeued head
`msgHash` — closing cross-message drain within the same queue. Unbound escrows (`queueDep = none`)
fail this gate. -/
def dequeueMsgBindB (k : RecordKernelState) (actor : CellId) (depId : Nat) (queueId msgHash : Nat) :
    Bool :=
  match findUnresolvedDeposit k depId with
  | some r =>
      decide (r.recipient = actor)
        && decide (r.queueDep == some queueId)
        && decide (r.queueMsg == some msgHash)
  | none => false

/-- **P0-1 binding gate** (recipient-only; the pre-dequeue admission analogue). -/
def dequeueBindB (k : RecordKernelState) (actor : CellId) (depId : Nat) : Bool :=
  dequeueRecipientBindB k actor depId

/-- **`queueDequeueHeadB` — PRE-dequeue P0-1-full gate (devnet atomicity).** Peeks the FIFO head and
requires the named deposit to bind to `(queueId, msgHash, recipient)` BEFORE any pop runs. The chained
executor and handler WRAPs cite this gate so a failed binding cannot consume the buffer. -/
def queueDequeueHeadB (k : RecordKernelState) (id : Nat) (actor : CellId) (depId : Nat) : Bool :=
  match findQueue k.queues id with
  | none   => false
  | some q =>
      if actor = q.owner then
        match q.buffer with
        | []      => false
        | mh :: _ => dequeueMsgBindB k actor depId id mh
      else false

/-- **`queueDequeueRefundK`** — REMOVE-FROM-FRONT of queue `id`'s FIFO buffer (the Wave-7 order op,
gated on `actor = owner`, fail-closed if absent / not-owner / EMPTY) AND REFUND the deposit-record
`depId` to the dequeuer `actor` (`apply.rs:3483`: the dequeuer reclaims the per-message deposit). The
refund single-cell CREDITS `actor` at the record's asset and marks the deposit record resolved — value
RETURNS to the ledger (`recTotalAsset` rises) while the holding-store DROPS (COMBINED conserved),
EXACTLY like `settleEscrowRawAsset`. Fail-closed if the FIFO gate rejects, the deposit record is
absent/already-resolved, OR the message-binding gate fails. Returns the post-state AND the dequeued
head message (the FIFO witness).

**NOTE:** production callers (`queueDequeueChainA`, `dequeueBindStep`) also require `queueDequeueHeadB`
on the pre-state so binding failure cannot pop the head. -/
def queueDequeueRefundK (k : RecordKernelState) (id : Nat) (actor : CellId) (depId : Nat) :
    Option (RecordKernelState × Nat) :=
  match queueDequeueK k id actor with
  | none          => none
  | some (k₁, mh) =>
      if dequeueMsgBindB k₁ actor depId id mh then
        match findUnresolvedDeposit k₁ depId with
        | some r => if actor ∈ k₁.accounts then
                      some (settleEscrowRawAsset k₁ depId actor r.asset r.amount, mh)
                    else none
        | none   => none
      else none

/-- **`dequeueRefundAmount`** — the REAL refunded amount of a dequeue: the `amount` of the named
unresolved deposit record `depId` (the value `queueDequeueRefundK` actually credits to the dequeuer via
`settleEscrowRawAsset … r.amount`), or `0` if no such record exists. The receipt MUST read this, not a
caller-supplied number, so a committed dequeue's receipt amount equals the value that genuinely moved.
`queueDequeueK` touches only `queues`, so the pre-state lookup agrees with the post-pop lookup. -/
def dequeueRefundAmount (k : RecordKernelState) (depId : Nat) : ℤ :=
  match findUnresolvedDeposit k depId with
  | some r => r.amount
  | none   => 0

/-- **`queueEnqueueDepositK_conserves_combined` — THE RESIDUAL CLOSED (PROVED).** A committed
deposit-enqueue PRESERVES the COMBINED per-asset total `recTotalAssetWithEscrow b` for EVERY asset `b`:
the FIFO append is escrow/bal-neutral (it touches only `queues`), and the PARK is the proven
combined-conserving escrow-create. NON-VACUOUS: the deposit GENUINELY moves the bare `recTotalAsset` at
the deposit asset (witnessed by `queueEnqueueDepositK_debits`) — only the COMBINED measure is fixed. -/
theorem queueEnqueueDepositK_conserves_combined {k k' : RecordKernelState} {id m : Nat}
    {sender owner : CellId} {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') (b : AssetId) :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold queueEnqueueDepositK at h
  cases hq : queueEnqueueK k id m with
  | none    => simp only [hq] at h; exact absurd h (by simp)
  | some k₁ =>
      simp only [hq] at h
      by_cases hg : 0 ≤ deposit ∧ deposit ≤ k₁.bal sender dAsset ∧ sender ∈ k₁.accounts
          ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨_, _, hlive, _⟩ := hg
        -- PARK conserves the combined measure (escrow-create RAW body), and the FIFO step was
        -- bal/escrow-neutral. We inline the combined-conservation of `createEscrowRawAsset` (the gate-free
        -- core of `escrow_create_conserves_combined_per_asset`): the locked asset's bal-debit is offset by
        -- the holding-store rise; every other asset is literally untouched.
        have hpark : recTotalAssetWithEscrow
              (createEscrowRawAssetQueue k₁ depId sender owner dAsset deposit id m) b
            = recTotalAssetWithEscrow k₁ b := by
          set newRec : EscrowRecord := { id := depId, creator := sender, recipient := owner,
                                         amount := deposit, resolved := false, asset := dAsset,
                                         queueDep := some id, queueMsg := some m } with hnewRec
          unfold recTotalAssetWithEscrow createEscrowRawAssetQueue
          have hbal : recTotalAsset { k₁ with bal := recBalCreditCell k₁.bal sender dAsset (-deposit),
                                              escrows := newRec :: k₁.escrows } b
              = recTotalAsset k₁ b + (if b = dAsset then (-deposit) else 0) := by
            show (∑ x ∈ k₁.accounts, recBalCreditCell k₁.bal sender dAsset (-deposit) x b) = _
            exact recBalCreditCell_recTotalAsset k₁.accounts k₁.bal sender dAsset (-deposit) hlive b
          have hheld : escrowHeldAsset { k₁ with bal := recBalCreditCell k₁.bal sender dAsset (-deposit),
                                                 escrows := newRec :: k₁.escrows } b
              = escrowHeldAsset k₁ b + (if dAsset = b then deposit else 0) := by
            have hc := escrowHeldAsset_cons_unresolved
              { k₁ with bal := recBalCreditCell k₁.bal sender dAsset (-deposit) } newRec b rfl
            simpa [hnewRec] using hc
          rw [hbal, hheld]
          by_cases hba : b = dAsset
          · subst hba; simp only [if_true, if_pos rfl]; ring
          · rw [if_neg hba, if_neg (fun h => hba h.symm)]; ring
        obtain ⟨hbal, hheld⟩ := queueEnqueueK_balNeutral hq b
        rw [hpark]; simp only [recTotalAssetWithEscrow, hbal, hheld]
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`queueEnqueueDepositK_debits` — PROVED (the NON-VACUITY: the deposit GENUINELY moves the ledger).**
A committed deposit-enqueue DROPS the bare `recTotalAsset dAsset` by `deposit` (the parked value left
the ledger). The combined measure is fixed (above); the BARE ledger genuinely moves — a flag/no-op
shadow could not state this. -/
theorem queueEnqueueDepositK_debits {k k' : RecordKernelState} {id m : Nat}
    {sender owner : CellId} {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    recTotalAsset k' dAsset = recTotalAsset k dAsset - deposit := by
  unfold queueEnqueueDepositK at h
  cases hq : queueEnqueueK k id m with
  | none    => simp only [hq] at h; exact absurd h (by simp)
  | some k₁ =>
      simp only [hq] at h
      by_cases hg : 0 ≤ deposit ∧ deposit ≤ k₁.bal sender dAsset ∧ sender ∈ k₁.accounts
          ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨_, _, hlive, _⟩ := hg
        -- the bare debit at `dAsset`, plus the FIFO step left `recTotalAsset` fixed at every asset.
        have hbare :
            recTotalAsset (createEscrowRawAssetQueue k₁ depId sender owner dAsset deposit id m) dAsset
            = recTotalAsset k₁ dAsset - deposit := by
          show (∑ x ∈ k₁.accounts, recBalCreditCell k₁.bal sender dAsset (-deposit) x dAsset) = _
          have := recBalCreditCell_recTotalAsset k₁.accounts k₁.bal sender dAsset (-deposit) hlive dAsset
          simpa [recTotalAsset] using this
        obtain ⟨hbal, _⟩ := queueEnqueueK_balNeutral hq dAsset
        rw [hbare, hbal]
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`queueDequeueRefundK_conserves_combined` — PROVED (the REFUND half, completing the pair).** A
committed deposit-dequeue PRESERVES the COMBINED per-asset total `recTotalAssetWithEscrow b` for EVERY
asset `b`: the FIFO remove is bal/escrow-neutral, and the REFUND is the proven combined-conserving
escrow-settle (the dequeuer `actor` is the LIVE settlement target — gate-checked). -/
theorem queueDequeueK_preserves_escrows {k k' : RecordKernelState} {id : Nat} {actor : CellId} {m : Nat}
    (h : queueDequeueK k id actor = some (k', m)) : k'.escrows = k.escrows := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none => simp [hf] at h
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none => simp [hd] at h
        | some hr =>
            obtain ⟨hm, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk; rfl
      · rw [if_neg ho] at h; exact absurd h (by simp)

theorem dequeueMsgBindB_queueDequeue_unchanged {k k' : RecordKernelState} {id : Nat}
    {actor : CellId} {depId m : Nat} (h : queueDequeueK k id actor = some (k', m)) :
    dequeueMsgBindB k' actor depId id m = dequeueMsgBindB k actor depId id m := by
  unfold dequeueMsgBindB findUnresolvedDeposit
  simp [queueDequeueK_preserves_escrows h]

theorem queueDequeueRefundK_imp_dequeue {k k' : RecordKernelState} {id : Nat}
    {actor : CellId} {depId mh : Nat}
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) :
    ∃ k₁, queueDequeueK k id actor = some (k₁, mh) := by
  unfold queueDequeueRefundK at h
  cases hq : queueDequeueK k id actor with
  | none => simp [hq] at h
  | some kr =>
      obtain ⟨k₁, m⟩ := kr
      simp only [hq] at h
      have hmh : m = mh := by
        by_cases hbind : dequeueMsgBindB k₁ actor depId id m
        · rw [if_pos hbind] at h
          cases hfind : findUnresolvedDeposit k₁ depId with
          | none => simp only [hfind] at h; exact absurd h (by simp)
          | some r =>
              simp only [hfind] at h
              by_cases hlive : actor ∈ k₁.accounts
              · rw [if_pos hlive] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, hm⟩ := h; exact hm
              · rw [if_neg hlive] at h; exact absurd h (by simp)
        · rw [if_neg hbind] at h; exact absurd h (by simp)
      refine ⟨k₁, ?_⟩
      simpa [hmh] using hq

theorem queueDequeueRefundK_conserves_combined {k k' : RecordKernelState} {id : Nat}
    {actor : CellId} {depId mh : Nat}
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) (b : AssetId) :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  unfold queueDequeueRefundK at h
  cases hq : queueDequeueK k id actor with
  | none          => simp only [hq] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k₁, m⟩ := kr
      simp only [hq] at h
      by_cases hbind : dequeueMsgBindB k₁ actor depId id m
      · rw [if_pos hbind] at h
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none   => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
          simp only [hfind] at h
          by_cases hlive : actor ∈ k₁.accounts
          · rw [if_pos hlive] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk
            have hset : recTotalAssetWithEscrow (settleEscrowRawAsset k₁ depId actor r.asset r.amount) b
                = recTotalAssetWithEscrow k₁ b :=
              escrow_settle_conserves_combined_per_asset k₁ depId actor r b hlive
                (by simpa [findUnresolvedDeposit] using hfind)
            obtain ⟨hbal, hheld⟩ := queueDequeueK_balNeutral hq b
            rw [hset]; simp only [recTotalAssetWithEscrow, hbal, hheld]
          · rw [if_neg hlive] at h; exact absurd h (by simp)
      · rw [if_neg hbind] at h; exact absurd h (by simp)

/-- **`queueEnqueueDepositK_insufficient_rejects` — PROVED (the DEPOSIT GATE, fail-closed).** An
enqueue whose `sender` lacks the `deposit` in asset `dAsset` (`deposit > sender's balance`) is REJECTED
even when the FIFO append would succeed — dregg1's `InsufficientBalance` (`apply.rs:3361`). The gate a
flag-only deposit could not enforce. -/
theorem queueEnqueueDepositK_insufficient_rejects (k k₁ : RecordKernelState) (id m : Nat)
    (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
    (hq : queueEnqueueK k id m = some k₁) (hpoor : k₁.bal sender dAsset < deposit) :
    queueEnqueueDepositK k id m sender owner depId dAsset deposit = none := by
  simp only [queueEnqueueDepositK, hq]
  rw [if_neg (by rintro ⟨_, hle, _, _⟩; omega)]

/-- **`queueDequeueRefundK_no_deposit_rejects` — PROVED (fail-closed).** A dequeue whose deposit
record `depId` is absent/already-resolved is REJECTED even when the FIFO remove would succeed. -/
theorem dequeueMsgBindB_absent (k : RecordKernelState) (actor : CellId) (depId queueId msgHash : Nat)
    (habsent : findUnresolvedDeposit k depId = none) :
    dequeueMsgBindB k actor depId queueId msgHash = false := by
  unfold dequeueMsgBindB
  rw [habsent]

/-- **`queueDequeueHeadB_false_rejects` — PROVED (devnet atomicity).** When the peeked FIFO head fails
the message-binding gate, the pre-dequeue admission gate is false — production wrappers reject before
`queueDequeueRefundK` runs. -/
theorem queueDequeueHeadB_false_rejects (k : RecordKernelState) (id : Nat) (actor : CellId)
    (depId head : Nat) (rest : List Nat) (q : QueueRecord)
    (hf : findQueue k.queues id = some q) (ho : actor = q.owner) (hb : q.buffer = head :: rest)
    (hbind : dequeueMsgBindB k actor depId id head = false) :
    queueDequeueHeadB k id actor depId = false := by
  unfold queueDequeueHeadB
  simp only [hf, if_pos ho, hb]
  exact hbind

theorem queueDequeueRefundK_no_deposit_rejects (k k₁ : RecordKernelState) (id : Nat) (actor : CellId)
    (depId m : Nat) (hq : queueDequeueK k id actor = some (k₁, m))
    (habsent : findUnresolvedDeposit k₁ depId = none) :
    queueDequeueRefundK k id actor depId = none := by
  have hbind := dequeueMsgBindB_absent k₁ actor depId id m habsent
  unfold queueDequeueRefundK
  rw [hq]
  by_cases hb : dequeueMsgBindB k₁ actor depId id m
  · cases hbind ▸ hb
  · simp [hb]

/-- **`queueEnqueueK_full_rejects` — PROVED (the CAPACITY BOUND, fail-closed).** Enqueue into a FULL
queue (`buffer.length ≥ capacity`) returns `none`. The bound a flag-only model could not enforce. -/
theorem queueEnqueueK_full_rejects (k : RecordKernelState) (id m : Nat) (q : QueueRecord)
    (hf : findQueue k.queues id = some q) (hfull : q.capacity ≤ q.buffer.length) :
    queueEnqueueK k id m = none := by
  simp only [queueEnqueueK, hf]; rw [if_neg (by omega)]

/-- **`queueDequeueK_empty_rejects` — PROVED (EMPTY fail-closed).** Dequeue from an EMPTY queue
(`buffer = []`), by its owner, returns `none`. The emptiness gate. -/
theorem queueDequeueK_empty_rejects (k : RecordKernelState) (id : Nat) (q : QueueRecord)
    (hf : findQueue k.queues id = some q) (hempty : q.buffer = []) :
    queueDequeueK k id q.owner = none := by
  simp only [queueDequeueK, hf, if_pos, hempty, qbufDequeue]

/-- **`queueDequeueK_wrong_owner_rejects` — PROVED (the AUTHORITY gate, fail-closed).** A non-owner
dequeue returns `none` (dregg1 `apply.rs:3433`: only the queue owner may dequeue). REAL gate, not `True`. -/
theorem queueDequeueK_wrong_owner_rejects (k : RecordKernelState) (id : Nat) (actor : CellId)
    (q : QueueRecord) (hf : findQueue k.queues id = some q) (hne : actor ≠ q.owner) :
    queueDequeueK k id actor = none := by
  simp only [queueDequeueK, hf]; rw [if_neg hne]

/-! ## §QUEUE runs (`#eval`) — the FIFO order + capacity + emptiness have TEETH. -/

/-- A kernel with one queue (id 7, owner 0, capacity 2, empty). -/
def kq0 : RecordKernelState :=
  { accounts := {0}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    queues := [{ id := 7, owner := 0, capacity := 2, buffer := [] }] }

-- FIFO ORDER WITNESS: enqueue 111 then 222; dequeue → 111 (the OLDER); dequeue remainder → 222.
#guard ((queueEnqueueK kq0 7 111).bind (fun k => queueEnqueueK k 7 222) |>.map (fun k =>
        (findQueue k.queues 7).map (·.buffer))) == some (some [111, 222])  --  some (some [111, 222]) — FIFO order, tail-appended
#guard (((queueEnqueueK kq0 7 111).bind (fun k => queueEnqueueK k 7 222)).bind
        (fun k => (queueDequeueK k 7 0).map Prod.snd)) == some 111  --  some 111 — head dequeued FIRST (the older)
#guard ((((queueEnqueueK kq0 7 111).bind (fun k => queueEnqueueK k 7 222)).bind
        (fun k => (queueDequeueK k 7 0).map Prod.fst)).bind
        (fun k => (queueDequeueK k 7 0).map Prod.snd)) == some 222  --  some 222 — then the younger (FIFO preserved)
-- CAPACITY BOUND: a 3rd enqueue into the (cap-2) full queue is REJECTED.
#guard ((((queueEnqueueK kq0 7 111).bind (fun k => queueEnqueueK k 7 222)).bind
        (fun k => queueEnqueueK k 7 333)).isSome) == false  --  false — full ⇒ none (capacity bound)
-- EMPTY fail-closed: dequeue the empty queue ⇒ none.
#guard ((queueDequeueK kq0 7 0).isSome) == false  --  false — empty ⇒ none
-- AUTHORITY gate: a non-owner (cell 1) dequeue ⇒ none even when non-empty.
#guard (((queueEnqueueK kq0 7 111).bind (fun k => (queueDequeueK k 7 1).map Prod.snd))).isNone  --  none — wrong owner ⇒ none
-- bal-NEUTRAL: the combined per-asset measure is UNTOUCHED by enqueue (and dequeue).
#guard (((queueEnqueueK kq0 7 111).map (fun k => recTotalAssetWithEscrow k 0))) == some 0  --  some 0 — UNCHANGED (queues hold messages, not balance)

#assert_axioms qbuf_fifo_order
#assert_axioms qbuf_fifo_empty
#assert_axioms qbuf_empty_dequeue
#assert_axioms queueEnqueueK_full_rejects
#assert_axioms queueDequeueK_empty_rejects
#assert_axioms queueDequeueK_wrong_owner_rejects
#assert_axioms queueEnqueueK_balNeutral
#assert_axioms queueDequeueK_balNeutral

/-! ## §QUEUE-DEPOSIT runs (`#eval`) — the REFUNDABLE DEPOSIT has TEETH (Wave-8 residual close).

The deposit GENUINELY moves the bare `recTotalAsset` (the parked value leaves the ledger) while the
COMBINED `recTotalAssetWithEscrow` is CONSERVED — the residual a bal-NEUTRAL shadow could not state. -/

/-- A kernel with one queue (id 7, owner 0, cap 2, empty) AND a SENDER cell 5 holding `100` of asset 0.
Both 0 and 5 are live accounts (so the deposit park/refund have live source + target). -/
def kqd0 : RecordKernelState :=
  { accounts := {0, 5}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c _ => if c = 5 then 100 else 0
    queues := [{ id := 7, owner := 0, capacity := 2, buffer := [] }] }

-- DEPOSIT MOVES the bare ledger: enqueue 111 from sender 5 with deposit 30 (record id 9) ⇒ bare
-- `recTotalAsset 0` DROPS 100 → 70 (the deposit left the sender's ledger and is PARKED).
#guard ((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).map (fun k => recTotalAsset k 0)) == some 70  --  some 70 — bare ledger MOVED
-- COMBINED CONSERVED: the parked deposit is counted in the holding-store, so the COMBINED measure is FIXED.
#guard ((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).map (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100 — COMBINED conserved
-- FIFO buffer ALSO advanced (the order op composed with the deposit): the message is in the buffer.
#guard ((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).bind (fun k => (findQueue k.queues 7).map (·.buffer))) == some [111]  --  some [111]
-- REFUND on dequeue: enqueue-with-deposit then dequeue (owner 0 reclaims deposit) ⇒ bare ledger RETURNS to 100.
#guard (((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).bind
        (fun k => (queueDequeueRefundK k 7 0 9).map (fun p => recTotalAsset p.1 0)))) == some 100  --  some 100 — refund RETURNED the deposit
-- ROUND-TRIP combined: still conserved after enqueue+dequeue.
#guard (((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).bind
        (fun k => (queueDequeueRefundK k 7 0 9).map (fun p => recTotalAssetWithEscrow p.1 0)))) == some 100  --  some 100 — combined conserved
-- DEPOSIT GATE fail-closed: a deposit of 200 (> sender's 100) is REJECTED even though the FIFO append would succeed.
#guard ((queueEnqueueDepositK kqd0 7 111 5 0 9 0 200).isSome) == false  --  false — InsufficientBalance (deposit gate)
-- REFUND fail-closed: dequeue with a deposit-record id that was never parked ⇒ none.
#guard (((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).bind
        (fun k => (queueDequeueRefundK k 7 0 999).map Prod.snd)).isSome) == false  --  false — no such deposit record
-- ATOMICITY: wrong depId fails the pre-dequeue head gate — buffer stays [111], kernel dequeue not reached.
#guard (((queueEnqueueDepositK kqd0 7 111 5 0 9 0 30).bind
        (fun k => (queueDequeueHeadB k 7 0 999 == false) &&
                  ((findQueue k.queues 7).map (·.buffer)) == some [111]))) == some true  --  some true

#assert_axioms queueEnqueueDepositK_conserves_combined
#assert_axioms queueEnqueueDepositK_debits
#assert_axioms queueDequeueRefundK_conserves_combined
#assert_axioms queueEnqueueDepositK_insufficient_rejects
#assert_axioms queueDequeueRefundK_no_deposit_rejects

/-! ## §SWISS — the kernel-level CapTP export/enliven/handoff/GC swiss-table transitions (Wave-8 de-THIN).

The swiss-table side-table transitions, each FAIL-CLOSED exactly where dregg1 fails closed: export
INSERTS a fresh swiss→cap entry with `refcount := 1` (rejecting a duplicate swiss number AND a rights
amplification — the exported tier must be `⊆` the exporter's own `held` rights, `apply.rs:3917`); enliven
LOOKS UP the swiss number (fail-closed if absent, `apply.rs:3955`), VALIDATES the bearer's claimed rights
are `⊆` the entry's exported rights (the non-amplification gate, `apply.rs:3999`), and BUMPS the refcount
(a new live reference); handoff binds a 3-vat introduce CERT to the entry + bumps the refcount
(`apply.rs:4109`); drop DECREMENTS the refcount and GCs the entry when it hits 0 (rejecting a drop on a
zero/absent entry, `apply.rs:4051`). ALL FOUR are balance-NEUTRAL — they touch ONLY `swiss`, never
`bal`/`escrows` (CapTP moves references, not balance). -/

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

/-- **`swissExportK_balNeutral` — PROVED.** Export touches only `swiss`, never `bal`/`escrows`. -/
theorem swissExportK_balNeutral {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold swissExportK at h
  cases hf : findSwiss k.swiss sw with
  | some e => simp only [hf] at h; exact absurd h (by simp)
  | none   =>
      simp only [hf] at h
      by_cases hr : rightsNarrowerOrEqual rights (heldAuths k exporter)
      · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissEnlivenK_balNeutral` — PROVED.** Enliven touches only `swiss`. -/
theorem swissEnlivenK_balNeutral {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold swissEnlivenK at h
  cases hf : findSwiss k.swiss sw with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some e =>
      simp only [hf] at h
      by_cases hr : rightsNarrowerOrEqual claimed e.rights
      · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · rw [if_neg hr] at h; exact absurd h (by simp)

/-- **`swissHandoffK_balNeutral` — PROVED.** Handoff touches only `swiss`. -/
theorem swissHandoffK_balNeutral {k k' : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold swissHandoffK at h
  cases hf : findSwiss k.swiss sw with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some e => simp only [hf, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- **`swissDropK_balNeutral` — PROVED.** Drop (refcount decrement / GC) touches only `swiss`. -/
theorem swissDropK_balNeutral {k k' : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold swissDropK at h
  cases hf : findSwiss k.swiss sw with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some e =>
      simp only [hf] at h
      by_cases hz : e.refcount = 0
      · rw [if_pos hz] at h; exact absurd h (by simp)
      · rw [if_neg hz] at h
        by_cases hone : e.refcount - 1 = 0
        · rw [if_pos hone] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
        · rw [if_neg hone] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

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
#guard ((swissExportK ksw0 42 0 1 [Auth.read]).map (fun k => recTotalAssetWithEscrow k 0)) == some 0  --  some 0

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

/-! ## §ESCROW-PER-ASSET runs (`#eval`) — the combined measure has teeth + the asset-isolation guard. -/

/-- A 2-cell, 2-asset ledger for the per-asset escrow guard: cell 0 holds 100 of asset 1 (and 0 of
asset 0); cell 1 holds 0 of everything. Cell 0 will lock 30 of asset 1 into escrow id 9 → recipient 1. -/
def res0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

/-- Lock 30 of asset 1 from cell 0 to recipient 1, escrow id 9. -/
def resLocked : Option RecordKernelState := createEscrowKAsset res0 9 0 0 1 1 30

-- NON-VACUITY GUARD (locked at asset≠0): the held value MOVES at asset 1 ONLY.
#guard ((escrowHeldAsset res0 1, escrowHeldAsset res0 0)) == (0, 0)  --  (0, 0) before
#guard (resLocked.map (fun k => (escrowHeldAsset k 1, escrowHeldAsset k 0))) == some (30, 0)  --  some (30, 0) — held GENUINELY non-zero at asset 1, asset 0 UNTOUCHED
-- the BARE per-asset ledger DROPS at asset 1 (a real debit); asset 0 untouched:
#guard (resLocked.map (fun k => (recTotalAsset k 1, recTotalAsset k 0))) == some (70, 0)  --  some (70, 0)
-- the COMBINED per-asset measure is CONSERVED at asset 1 AND asset 0:
#guard ((recTotalAssetWithEscrow res0 1, recTotalAssetWithEscrow res0 0)) == (100, 0)  --  (100, 0)
#guard (resLocked.map (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0))) == some (100, 0)  -- some (100, 0) — CONSERVED both assets
-- SETTLE (release to recipient 1): mirror — combined stays (100,0), held returns to 0, bal back to 100 at asset 1.
#guard ((resLocked.bind (fun k => releaseEscrowKAsset k 9)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))) == some (100, 0, 0, 100)  --  some (100, 0, 0, 100)
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
#assert_axioms escrowHeld_cons_unresolved
#assert_axioms escrow_create_debits
#assert_axioms escrow_create_conserves_combined
#assert_axioms heldSum_markResolved_found
#assert_axioms escrow_settle_conserves_combined
#assert_axioms releaseEscrow_conserves_combined
#assert_axioms refundEscrow_conserves_combined
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
#assert_axioms escrowHeldAsset_cons_unresolved
#assert_axioms heldSumAsset_markResolved_found
#assert_axioms escrow_create_conserves_combined_per_asset
#assert_axioms escrow_settle_conserves_combined_per_asset
#assert_axioms releaseEscrowKAsset_conserves_combined_per_asset
#assert_axioms refundEscrowKAsset_conserves_combined_per_asset
#assert_axioms escrow_create_debits_per_asset
#assert_axioms createEscrowKAsset_authorized
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

end Dregg2.Exec
