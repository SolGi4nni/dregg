/-
# Dregg2.Circuit.DescriptorIR2 — descriptor IR v2: the multi-table constraint grammar (EPOCH keystone).

`Emit/EffectVmEmit.lean` (v1) is a SINGLE-table IR: per-row gates / transitions / boundary pins /
PI bindings / in-row Poseidon2 hash sites / in-row range teeth over one fixed-width trace. The EPOCH
design (`docs/EPOCH-DESIGN.md`) makes hashing a BOUNDARY phenomenon: interiors ride lookup arguments
into shared tables, so v2 adds exactly the four kinds that blocked the graduation cohort and carry
the measured 85% lever:

  * **`TableDef`** — a declared table (id, column arity, row semantics) per the five EPOCH tables
    (main · poseidon2 chip · range · memory · map-ops);
  * **`Lookup`** — a tuple of column expressions asserted to be a row of a named table
    (the LogUp/grand-product argument's per-occurrence face);
  * **`MemOp`** — a read/write multiset row (kind, addr, value, claimed prev value, claimed prev
    serial, + selector guard): the offline-memory-checking instrumentation. Intra-proof state pays
    ZERO hashing — consistency is the multiset balance plus **Blum's theorem**, which is a PROVED
    import (`Dregg2.Crypto.MemoryChecking.memcheck_sound` — the weld landed; no named hypothesis
    remains — see §5);
  * **`MapOp`** — a boundary reconciliation `(root, key, value, op) → new_root` whose denotation is
    an OPENING of the proven sorted-Poseidon2 map (`Dregg2.Substrate.Heap`: `root_injective`,
    `get_none_of_gap` — the cap-root machinery with a generic leaf).

A v2 descriptor DENOTES a multi-table constraint system: `Satisfied2` (§6) quantifies the per-row
forms over the whole main trace, requires every lookup tuple to be a row of its table, requires the
gathered memory log to be serial-ordered and multiset-balanced (the certificate the memory table's
LogUp argument enforces), and requires every map-op to open against a genuine sorted heap.

v1 EMBEDS losslessly (`embedV1`, faithfulness `embedV1_satisfied_iff`): the registry carries both
during the epoch. The wire form is versioned (`"ir":2`, §9); v1 descriptors remain parseable — the
v1 emitter (`emitVmJson`, no `"ir"` key ⇒ version 1) is untouched.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as
the named `Poseidon2SpongeCR` hypothesis; memory consistency is the PROVED
`MemoryChecking.memcheck_sound` (unconditional combinatorics — no crypto, no hypothesis). No
`sorry`, no `native_decide`. NEW file; imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Lookup
import Dregg2.Substrate.Heap
import Dregg2.Crypto.MemoryChecking
import Mathlib.Data.Multiset.Basic

namespace Dregg2.Circuit.DescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR babyBearD4W16)
open Dregg2.Substrate
open Dregg2.Crypto

/-! ## §1 — Table identities and definitions (the five EPOCH tables).

A table is identified by a stable wire id, carries a fixed column arity, and a ROW-SEMANTICS tag
saying what a row MEANS (the Rust multi-table assembly is generic; the meaning lives here). -/

/-- The table identity: the five EPOCH tables plus an escape hatch for future collection ids
(the universal-map forward-shape: a future state component is a new collection id, never a new
column — and likewise a new table is a new id, never a new grammar). -/
inductive TableId where
  | main | poseidon2 | range | memory | mapOps
  | custom (n : Nat)
  deriving Repr, DecidableEq

/-- The stable wire id (the JSON `"table"` / `"id"` field). -/
def TableId.wireId : TableId → Nat
  | .main      => 0
  | .poseidon2 => 1
  | .range     => 2
  | .memory    => 3
  | .mapOps    => 4
  | .custom n  => 5 + n

/-- Wire ids are collision-free: the JSON id determines the table. -/
theorem TableId.wireId_injective : Function.Injective TableId.wireId := by
  intro a b h
  cases a <;> cases b <;> simp_all [TableId.wireId] <;> omega

/-- What a row of the table MEANS (the semantic tag the Lean denotation dispatches on). -/
inductive RowSemantics where
  /-- One row per effect: selectors, register deltas, PI bindings (the thin post-LogUp main). -/
  | mainRow
  /-- One row per Poseidon2 permutation: an `(arity, padded inputs, output)` tuple of the REAL
  `babyBearD4W16` permutation — every hash site becomes a lookup here (the 85% lever). -/
  | permutation
  /-- The limb table: rows are exactly `[v]` for `v ∈ [0, 2^bits)` — range checks by lookup. -/
  | rangeLimb (bits : Nat)
  /-- One row per state access: the offline-memory-checking read/write multiset entry. -/
  | memAccess
  /-- One row per boundary reconciliation: a `(root, key, value, op, new_root)` sorted-map opening. -/
  | mapReconcile
  deriving Repr, DecidableEq

/-- A declared table: id, display name, column arity, row semantics. -/
structure TableDef where
  id    : TableId
  name  : String
  arity : Nat
  sem   : RowSemantics
  deriving Repr, DecidableEq

/-! ### The Poseidon2 chip shape (pinned to the REAL parameters the v1 emitters already carry).

The chip row is `(arity-tag, inputs padded to the sponge RATE, output)`. The rate is derived from
the SAME `babyBearD4W16` record (`Circuit/Poseidon2Binding.lean`) that pins the deployed
p3-poseidon2-circuit-air permutation — field, width, S-box, rounds, and the round-constant /
internal-diagonal SOURCES (`BABYBEAR_POSEIDON2_RC_16_{EXTERNAL_INITIAL,INTERNAL,EXTERNAL_FINAL}`,
`INTERNAL_DIAG` — the literal arrays live in p3-baby-bear and `circuit/src/poseidon2.rs` reads the
same source; the Lean emission pins them BY NAME exactly as `Poseidon2RealParams` documents). -/

/-- The chip lookup rate in BASE field elements: `babyBearD4W16.rate = rate_ext · d = 8`. -/
def CHIP_RATE : Nat := babyBearD4W16.rate

/-- The canonical limb width for the shared range table: the two-limb signed-well discipline
(the deployed balance limbs are 30-bit — `EffectVmEmitTransfer`'s `VmRange ⟨…, 30⟩` teeth). -/
def BAL_LIMB_BITS : Nat := 30

/-- main table (per-descriptor width — the v2 main is thin; during the epoch it carries the
descriptor's own trace width). -/
def mainTableDef (width : Nat) : TableDef := ⟨.main, "main", width, .mainRow⟩

/-- The Poseidon2 chip table: `1 (arity tag) + CHIP_RATE (padded inputs) + 1 (output)` columns. -/
def poseidon2ChipTableDef : TableDef := ⟨.poseidon2, "poseidon2_chip", CHIP_RATE + 2, .permutation⟩

/-- The range (limb) table: one column, rows `[0, 2^bits)`. -/
def rangeTableDef (bits : Nat) : TableDef := ⟨.range, "range", 1, .rangeLimb bits⟩

/-- The memory table: `(addr, value, prev_value, prev_serial, kind)` — one row per state access
(the instrumented offline-checking row: the prover's claimed prior tuple rides as witness
columns; the op's OWN serial is its trace position, not a column). -/
def memTableDef : TableDef := ⟨.memory, "memory", 5, .memAccess⟩

/-- The map-ops table: `(root, key, value, op, new_root)` — one row per boundary reconciliation. -/
def mapOpsTableDef : TableDef := ⟨.mapOps, "map_ops", 5, .mapReconcile⟩

/-- The shared (descriptor-independent) tables. -/
def sharedTableDefs : List TableDef :=
  [poseidon2ChipTableDef, rangeTableDef BAL_LIMB_BITS, memTableDef, mapOpsTableDef]

/-- The full five-table family for a descriptor of the given main width. -/
def v2Tables (width : Nat) : List TableDef := mainTableDef width :: sharedTableDefs

/-! ## §2 — The v2 constraint kinds.

Everything v1 has (`VmConstraint`, embedded whole) PLUS lookup / mem-op / map-op. The mem/map ops
carry a selector GUARD expression (active iff `guard = 1` on the row) — the same selector-gating
discipline the v1 per-row gates use, so NoOp pad rows contribute nothing to the multisets. -/

/-- A lookup: the tuple of column expressions is asserted to be a ROW of the named table. -/
structure Lookup where
  table : TableId
  tuple : List EmittedExpr
  deriving Repr

/-- The wire code of a memory access kind (the memory table's `kind` column value; the kind
type itself is the PROVED memory-checking model's `MemoryChecking.Kind`). -/
def kindCode : MemoryChecking.Kind → ℤ
  | .read => 0 | .write => 1

/-- The kind wire tag. -/
def kindTag : MemoryChecking.Kind → String
  | .read => "read" | .write => "write"

/-- A read/write multiset row: the offline-memory-checking INSTRUMENTATION, as column expressions
over the emitting main row. `value` is the value returned (read) / installed (write);
`prevValue`/`prevSerial` are the untrusted memory's CLAIMED latest prior tuple (the witness
columns the per-op discipline checks); the op's OWN serial is positional. `guard` gates the
contribution (selector discipline — pad rows contribute nothing). -/
structure MemOp where
  guard      : EmittedExpr
  addr       : EmittedExpr
  value      : EmittedExpr
  prevValue  : EmittedExpr
  prevSerial : EmittedExpr
  kind       : MemoryChecking.Kind
  deriving Repr

/-- Map reconciliation kind: a membership read, a non-membership read, or a (sorted insert-or-
update) write. -/
inductive MapOpKind where
  | read | write | absent
  deriving Repr, DecidableEq, BEq

/-- The wire code of a map-op kind (the map-ops table's `op` column value). -/
def MapOpKind.code : MapOpKind → ℤ
  | .read => 0 | .write => 1 | .absent => 2

/-- A boundary reconciliation `(root, key, value, op) → new_root`, as column expressions over the
emitting main row. `guard` gates the contribution. -/
structure MapOp where
  guard   : EmittedExpr
  root    : EmittedExpr
  key     : EmittedExpr
  value   : EmittedExpr
  newRoot : EmittedExpr
  op      : MapOpKind
  deriving Repr

/-- The v2 constraint: v1 embedded whole, plus the three new kinds. -/
inductive VmConstraint2 where
  | base   (c : VmConstraint)
  | lookup (l : Lookup)
  | memOp  (m : MemOp)
  | mapOp  (m : MapOp)
  deriving Repr

/-- The v2 descriptor: name, main-trace width, PI count, the declared tables, the constraints,
plus the v1 hash-site / range carriers (legal during the epoch; a graduated v2 descriptor moves
them onto chip/range lookups — §7/§8 prove the replacements sound). -/
structure EffectVmDescriptor2 where
  name        : String
  traceWidth  : Nat
  piCount     : Nat
  tables      : List TableDef
  constraints : List VmConstraint2
  hashSites   : List VmHashSite
  ranges      : List VmRange

/-- The wire IR version this module emits. -/
def IR_VERSION : Nat := 2

/-- Embed a v1 descriptor: same name/width/PI/sites/ranges, constraints wrapped, no tables, no
lookups, no mem/map ops. The registry carries both shapes during the epoch. -/
def embedV1 (d : EffectVmDescriptor) : EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth
  , piCount     := d.piCount
  , tables      := []
  , constraints := d.constraints.map .base
  , hashSites   := d.hashSites
  , ranges      := d.ranges }

/-! ## §3 — The denotation carriers: tables, trace family, per-row environments. -/

/-- A table's contents: a list of rows, each a tuple of field values. -/
abbrev Table := List (List ℤ)

/-- The multi-table trace: contents for every table id. -/
abbrev TraceFamily := TableId → Table

/-- The whole multi-table witness: the main rows, the public inputs, the auxiliary tables. -/
structure VmTrace where
  rows : List Assignment
  pub  : Assignment
  tf   : TraceFamily

/-- The all-zero assignment (off-the-end default; never semantically load-bearing on a
well-formed trace). -/
def zeroAsg : Assignment := fun _ => 0

/-- The row window at main-row `i`: current row, next row, public inputs. -/
def envAt (t : VmTrace) (i : Nat) : VmRowEnv :=
  { loc := t.rows.getD i zeroAsg, nxt := t.rows.getD (i + 1) zeroAsg, pub := t.pub }

/-- A lookup holds on a row iff its evaluated tuple IS a row of its table. (The LogUp argument
the Rust assembly runs proves exactly this multiset-supported membership for every occurrence.) -/
def Lookup.holdsAt (tf : TraceFamily) (env : VmRowEnv) (l : Lookup) : Prop :=
  l.tuple.map (·.eval env.loc) ∈ tf l.table

/-! ## §4 — Map-op semantics: openings of the PROVEN sorted-Poseidon2 map.

The denotation is an EXISTENTIAL opening of `Dregg2.Substrate.Heap`'s sorted map — the prover
witnesses a sorted heap behind the root. Under the one named CR floor the opening is FUNCTIONAL
(`root_injective` pins the heap), so the root + key determine the value/new-root: the map-op row
cannot lie. Non-membership reuses the gap bracketing (`get_none_of_gap`). -/

/-- `opensTo hash r k o` — some sorted heap behind root `r` reads `o` at `k`. -/
def opensTo (hash : List ℤ → ℤ) (r k : ℤ) (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ Heap.root hash h = r ∧ Heap.get h k = o

/-- `writesTo hash r k v r'` — some sorted heap behind root `r` produces root `r'` under the
sorted insert-or-update of `(k, v)`. -/
def writesTo (hash : List ℤ → ℤ) (r k v r' : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ Heap.root hash h = r ∧
    r' = Heap.root hash (Heap.set h k v)

/-- **Openings are FUNCTIONAL (the anti-ghost).** Under CR, the root + key determine the read:
two openings of the same root at the same key agree. A map-op row cannot claim a tampered value. -/
theorem opensTo_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensTo hash r k o₁) (h₂ : opensTo hash r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, _, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, hr₂, hg₂⟩ := h₂
  have hm : m₁ = m₂ := Heap.root_injective hash hCR (hr₁.trans hr₂.symm)
  rw [← hg₁, ← hg₂, hm]

/-- Membership and non-membership at the same root/key EXCLUDE each other (the tooth the
nullifier/cap non-membership argument needs from the map-ops table). -/
theorem opensTo_some_excludes_none (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k v : ℤ} (h₁ : opensTo hash r k (some v)) (h₂ : opensTo hash r k none) : False := by
  have := opensTo_functional hash hCR h₁ h₂
  simp at this

/-- **Writes are FUNCTIONAL.** Under CR, root + key + value determine the new root: the map-op
row's `new_root` column cannot be forged. -/
theorem writesTo_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k v r₁ r₂ : ℤ}
    (h₁ : writesTo hash r k v r₁) (h₂ : writesTo hash r k v r₂) : r₁ = r₂ := by
  obtain ⟨m₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, _, hr₂, he₂⟩ := h₂
  have hm : m₁ = m₂ := Heap.root_injective hash hCR (hr₁.trans hr₂.symm)
  rw [he₁, he₂, hm]

/-- Non-membership openings are CONSTRUCTIBLE from the proven gap bracketing — completeness of
the `absent` kind (the `sorted_gap_excludes` machinery, via `Heap.get_none_of_gap`). -/
theorem opensTo_none_of_gap (hash : List ℤ → ℤ) {h : Heap.FeltHeap} {r lo hi k : ℤ}
    (hs : Heap.SortedKeys h) (hr : Heap.root hash h = r)
    (hadj : Dregg2.Crypto.NonMembership.Adjacent (Heap.keys h) lo hi)
    (hlo : lo < k) (hhi : k < hi) : opensTo hash r k none :=
  ⟨h, hs, hr, Heap.get_none_of_gap h lo hi k hs hadj hlo hhi⟩

/-- The map-op's per-row denotation: when the guard fires, the evaluated `(root, key, value,
new_root)` columns are a genuine opening per the op kind. -/
def MapOp.holdsAt (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) : Prop :=
  m.guard.eval env.loc = 1 →
    match m.op with
    | .read   => opensTo hash (m.root.eval env.loc) (m.key.eval env.loc)
                   (some (m.value.eval env.loc))
                 ∧ m.newRoot.eval env.loc = m.root.eval env.loc
    | .absent => opensTo hash (m.root.eval env.loc) (m.key.eval env.loc) none
                 ∧ m.newRoot.eval env.loc = m.root.eval env.loc
    | .write  => writesTo hash (m.root.eval env.loc) (m.key.eval env.loc)
                   (m.value.eval env.loc) (m.newRoot.eval env.loc)

/-! ## §5 — Memory-op semantics: the read/write multiset, WELDED to the proved Blum theorem.

Hot intra-proof state has NO structure: each access is an instrumented row in the memory table;
the table's LogUp argument certifies MULTISET BALANCE (`MemCheck`: init + writes = reads + final),
and the per-row circuit checks the LOCAL discipline (`Disciplined`: the claimed prior serial is in
the past; a read returns its claimed value). The SEMANTIC contract — balance ⇒ every read returns
the latest prior write — is **Blum's theorem**, PROVED in `Dregg2.Crypto.MemoryChecking`
(`memcheck_sound`, unconditional combinatorics). This section just instantiates that model at the
IR (`Addr := ℤ`, `Val := ℤ`, felt prev-serial via `Int.toNat`): NO named hypothesis remains. -/

/-- A gathered memory-log operation: the proved model's instrumented op over felts. -/
abbrev MemTraceOp := MemoryChecking.Op ℤ ℤ

/-- The memory-table row of an op: `[addr, value, prev_value, prev_serial, kind]`. -/
def opRow (op : MemTraceOp) : List ℤ :=
  [op.addr, op.val, op.prevVal, (op.prevSerial : ℤ), kindCode op.kind]

/-- Evaluate a `MemOp` on a row: `some` instrumented op when the guard fires, `none` on a pad
row. The claimed prev serial is a felt column; the model's `Nat` serial is its `toNat` (the
deployment's range discipline keeps it small and non-negative). -/
def MemOp.opAt? (a : Assignment) (m : MemOp) : Option MemTraceOp :=
  if m.guard.eval a = 1 then
    some ⟨m.kind, m.addr.eval a, m.value.eval a, m.prevValue.eval a,
          (m.prevSerial.eval a).toNat⟩
  else none

/-! ## §6 — `Satisfied2`: the multi-table denotation. -/

/-- The mem ops a descriptor declares. -/
def memOpsOf (d : EffectVmDescriptor2) : List MemOp :=
  d.constraints.filterMap fun c => match c with | .memOp m => some m | _ => none

/-- The map ops a descriptor declares. -/
def mapOpsOf (d : EffectVmDescriptor2) : List MapOp :=
  d.constraints.filterMap fun c => match c with | .mapOp m => some m | _ => none

/-- The gathered memory log: every main row's guarded mem-op entries, in trace order (the
model's positional serials number EXACTLY this order). -/
def memLog (d : EffectVmDescriptor2) (t : VmTrace) : List MemTraceOp :=
  t.rows.flatMap fun a => (memOpsOf d).filterMap (MemOp.opAt? a)

/-- The map-ops table row of a `MapOp` on a row: `[root, key, value, op, new_root]`. -/
def MapOp.rowAt (a : Assignment) (m : MapOp) : List ℤ :=
  [m.root.eval a, m.key.eval a, m.value.eval a, m.op.code, m.newRoot.eval a]

/-- The gathered map-ops log (the rows the map-ops table must carry), in trace order. -/
def mapLog (d : EffectVmDescriptor2) (t : VmTrace) : Table :=
  t.rows.flatMap fun a =>
    (mapOpsOf d).filterMap fun m =>
      if m.guard.eval a = 1 then some (m.rowAt a) else none

/-- Per-row meaning of one v2 constraint. (`memOp` is `True` here: its content is the GLOBAL
multiset legs of `Satisfied2`, not a row-local equation.) -/
def VmConstraint2.holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : VmConstraint2 → Prop
  | .base c   => c.holdsVm env isFirst isLast
  | .lookup l => l.holdsAt tf env
  | .memOp _  => True
  | .mapOp m  => m.holdsAt hash env

/-- **The v2 denotation.** A multi-table witness satisfies a v2 descriptor (relative to the
declared memory boundary: initial image `minit`, claimed final image `mfin`, declared address
list `maddrs`) iff: every constraint holds on every row window; every v1 hash site / range tooth
holds on every row; the gathered memory log is per-op disciplined, address-closed over a
duplicate-free boundary, and multiset-balanced (`MemCheck` — the LogUp certificate); and the
memory / map-ops tables carry EXACTLY the gathered logs (table faithfulness — the assembly's
binding of table to trace). -/
structure Satisfied2 (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop where
  rowConstraints : ∀ i < t.rows.length, ∀ c ∈ d.constraints,
    c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
  rowHashes : ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) d.hashSites
  rowRanges : ∀ i < t.rows.length, ∀ r ∈ d.ranges, r.holds (envAt t i)
  memAddrsNodup : maddrs.Nodup
  memClosed : ∀ op ∈ memLog d t, op.addr ∈ maddrs
  memDisciplined : MemoryChecking.Disciplined (memLog d t)
  memBalanced : MemoryChecking.MemCheck minit mfin maddrs (memLog d t)
  memTableFaithful : t.tf .memory = (memLog d t).map opRow
  mapTableFaithful : t.tf .mapOps = mapLog d t

/-- **Memory consistency of a satisfying witness — BLUM'S THEOREM APPLIED (no hypothesis).**
A v2-satisfying trace's memory log is CONSISTENT against the boundary image: every read returns
the latest prior write. The whole proof is the imported `memcheck_sound` — registers, heap ops,
cap checks, nullifier touches ride this with ZERO intra-proof hashing. -/
theorem satisfied2_mem_consistent (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash d minit mfin maddrs t) :
    MemoryChecking.Consistent minit (memLog d t) :=
  MemoryChecking.memcheck_sound h.memAddrsNodup h.memClosed h.memDisciplined h.memBalanced

/-! ### The v1 embedding is FAITHFUL. -/

/-- `filterMap` over embedded-v1 constraints yields nothing for any v2-only selector. -/
theorem filterMap_base_none {α : Type} (f : VmConstraint2 → Option α)
    (hf : ∀ c, f (.base c) = none) (cs : List VmConstraint) :
    (cs.map VmConstraint2.base).filterMap f = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [hf, ih]

/-- An embedded v1 descriptor declares no mem ops. -/
theorem memOpsOf_embedV1 (d : EffectVmDescriptor) : memOpsOf (embedV1 d) = [] :=
  filterMap_base_none _ (fun _ => rfl) d.constraints

/-- An embedded v1 descriptor declares no map ops. -/
theorem mapOpsOf_embedV1 (d : EffectVmDescriptor) : mapOpsOf (embedV1 d) = [] :=
  filterMap_base_none _ (fun _ => rfl) d.constraints

/-- An embedded v1 descriptor's memory log is empty. -/
theorem memLog_embedV1 (d : EffectVmDescriptor) (t : VmTrace) : memLog (embedV1 d) t = [] := by
  unfold memLog
  rw [memOpsOf_embedV1]
  simp

/-- An embedded v1 descriptor's map-ops log is empty. -/
theorem mapLog_embedV1 (d : EffectVmDescriptor) (t : VmTrace) : mapLog (embedV1 d) t = [] := by
  unfold mapLog
  rw [mapOpsOf_embedV1]
  simp

/-- The empty boundary + empty log trivially pass the balance check. -/
theorem memCheck_nil (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    MemoryChecking.MemCheck minit mfin ([] : List ℤ) [] := by
  simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]

/-- **`embedV1_satisfied_iff` — the embedding is FAITHFUL.** On a trace whose memory / map-ops
tables are empty (no v2 content; empty declared memory boundary), satisfying the embedded
descriptor is EXACTLY the v1 denotation `satisfiedVm` on every row window. Nothing is gained or
lost in the version bump: the v1 registry rides the v2 wire unchanged. -/
theorem embedV1_satisfied_iff (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (t : VmTrace)
    (hmem : t.tf .memory = []) (hmap : t.tf .mapOps = []) :
    Satisfied2 hash (embedV1 d) minit mfin [] t ↔
      ∀ i < t.rows.length,
        satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  constructor
  · intro h i hi
    refine ⟨?_, h.rowHashes i hi, h.rowRanges i hi⟩
    intro c hc
    have hmem' : VmConstraint2.base c ∈ (embedV1 d).constraints :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    exact h.rowConstraints i hi (.base c) hmem'
  · intro h
    refine ⟨?_, fun i hi => (h i hi).2.1, fun i hi => (h i hi).2.2,
      List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi c hc
      simp only [embedV1, List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact (h i hi).1 c₀ hc₀
    · rw [memLog_embedV1]
      simp
    · rw [memLog_embedV1]
      trivial
    · rw [memLog_embedV1]
      exact memCheck_nil minit mfin
    · rw [memLog_embedV1, hmem]
      rfl
    · rw [mapLog_embedV1, hmap]

/-! ## §7 — The Poseidon2 chip table: hash sites become lookups (the 85% lever).

A chip row is `(arity-tag, inputs padded to CHIP_RATE, output)` of the REAL permutation. The
arity tag disambiguates padding (an arity-2 absorb of `[a, b]` is NOT the arity-3 absorb of
`[a, b, 0]`). `chip_lookup_sound` is the lever theorem: against a SOUND chip table, the lookup
ENFORCES the hash equation — exactly what a v1 in-row hash site enforced, at lookup cost. -/

/-- Pad a value tuple to `n` with zeros. -/
def padTo (n : Nat) (xs : List ℤ) : List ℤ := xs ++ List.replicate (n - xs.length) 0

/-- Pad an expression tuple to `n` with literal zeros. -/
def padToE (n : Nat) (es : List EmittedExpr) : List EmittedExpr :=
  es ++ List.replicate (n - es.length) (.const 0)

theorem padTo_length {n : Nat} {xs : List ℤ} (h : xs.length ≤ n) : (padTo n xs).length = n := by
  simp [padTo]
  omega

/-- Padding is injective on tuples of equal length. -/
theorem padTo_inj {n : Nat} {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (h : padTo n xs = padTo n ys) : xs = ys :=
  (List.append_inj h hlen).1

/-- Evaluation commutes with padding. -/
theorem map_eval_padToE (n : Nat) (es : List EmittedExpr) (a : Assignment) :
    (padToE n es).map (·.eval a) = padTo n (es.map (·.eval a)) := by
  simp [padToE, padTo, List.map_append, List.map_replicate, EmittedExpr.eval]

/-- The chip ROW of an absorb: `(arity, padded inputs, hash inputs)`. -/
def chipRow (hash : List ℤ → ℤ) (ins : List ℤ) : List ℤ :=
  (ins.length : ℤ) :: padTo CHIP_RATE ins ++ [hash ins]

/-- The chip LOOKUP tuple of an absorb: `(arity, padded input exprs, digest column)`. -/
def chipLookupTuple (ins : List EmittedExpr) (digestCol : Nat) : List EmittedExpr :=
  (.const (ins.length : ℤ)) :: padToE CHIP_RATE ins ++ [.var digestCol]

/-- A chip table is SOUND when every row is a genuine `(arity, padded inputs, output)` tuple of
the permutation (the chip AIR's own faithfulness — the per-permutation constraint family). -/
def ChipTableSound (hash : List ℤ → ℤ) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ ins : List ℤ, ins.length ≤ CHIP_RATE ∧ r = chipRow hash ins

/-- **THE LEVER (`chip_lookup_sound`).** Against a sound chip table, a chip lookup ENFORCES the
hash equation: the digest column carries the genuine hash of the evaluated inputs. The arity tag
+ equal-length padding make the row decomposition unique, so no padding confusion survives. -/
theorem chip_lookup_sound (hash : List ℤ → ℤ) (tbl : Table) (hSound : ChipTableSound hash tbl)
    (a : Assignment) (ins : List EmittedExpr) (digestCol : Nat)
    (hlen : ins.length ≤ CHIP_RATE)
    (hmem : (chipLookupTuple ins digestCol).map (·.eval a) ∈ tbl) :
    a digestCol = hash (ins.map (·.eval a)) := by
  obtain ⟨ws, hwlen, hrow⟩ := hSound _ hmem
  have hev : (chipLookupTuple ins digestCol).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a)) ++ [a digestCol] := by
    simp [chipLookupTuple, List.map_cons, List.map_append, map_eval_padToE, EmittedExpr.eval]
  rw [hev] at hrow
  unfold chipRow at hrow
  injection hrow with hl htail
  have hlens : (ins.map (·.eval a)).length = ws.length := by
    have hcast : (ins.length : ℤ) = (ws.length : ℤ) := hl
    have := Int.natCast_inj.mp hcast
    simpa [List.length_map] using this
  have hlenm : (ins.map (·.eval a)).length ≤ CHIP_RATE := by
    simpa [List.length_map] using hlen
  have hpads := List.append_inj htail
    (by rw [padTo_length hlenm, padTo_length hwlen])
  have hins : ins.map (·.eval a) = ws := padTo_inj hlens hpads.1
  have hd : a digestCol = hash ws := by
    have := hpads.2
    simpa using this
  rw [hins]
  exact hd

/-! ### Translating a v1 hash site to a chip lookup. -/

instance : Inhabited VmHashSite := ⟨⟨0, [], 0⟩⟩

/-- Translate a hash-site input to a column expression. A `digest k` reference reads the EARLIER
site's RESULT COLUMN (every site binds its digest to a named column — `siteHoldsAll`'s invariant),
so the cross-site dataflow survives the move into lookup form. -/
def HashInput.toExpr (sites : List VmHashSite) : HashInput → EmittedExpr
  | .col c    => .var c
  | .digest k => .var ((sites.getD k default).digestCol)
  | .zero     => .const 0

/-- The chip lookup replacing site `s` of the ordered family `sites`. -/
def siteLookup (sites : List VmHashSite) (s : VmHashSite) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTuple (s.inputs.map (HashInput.toExpr sites)) s.digestCol }

/-- **The site-to-lookup replacement is SOUND.** If the earlier sites' digest columns carry the
resolved digests (the `siteHoldsAll` invariant, hypothesis `hdig`) and the chip table is sound,
then the translated lookup enforces EXACTLY the site equation `loc digestCol = hash (resolved
inputs)` — the v1 in-row Poseidon2 constraint, at lookup cost. -/
theorem siteLookup_replaces_site (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (env : VmRowEnv)
    (sites : List VmHashSite) (s : VmHashSite) (digs : List ℤ)
    (hdig : ∀ k, env.loc ((sites.getD k default).digestCol) = digs.getD k 0)
    (hlen : s.inputs.length ≤ CHIP_RATE)
    (hmem : (siteLookup sites s).tuple.map (·.eval env.loc) ∈ tbl) :
    env.loc s.digestCol = hash (s.resolvedInputs env digs) := by
  have h := chip_lookup_sound hash tbl hSound env.loc
    (s.inputs.map (HashInput.toExpr sites)) s.digestCol
    (by simpa [List.length_map] using hlen) hmem
  rw [h]
  congr 1
  rw [List.map_map]
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro i _
  cases i with
  | col c    => rfl
  | digest k =>
    have hk := hdig k
    simp only [List.getD_eq_getElem?_getD] at hk
    simp [HashInput.toExpr, HashInput.resolve, EmittedExpr.eval, hk]
  | zero     => rfl

/-! ## §8 — The range table: range checks by lookup (kills the range-bit columns). -/

/-- The range table's rows: `[v]` for `v ∈ [0, 2^bits)` (the proven `Lookup.rangeTable`). -/
def rangeRows (bits : Nat) : Table := _root_.Dregg2.Circuit.Lookup.rangeTable bits

/-- Singleton-row membership in a mapped range, in closed form (the `rw`-driven proof routes
around Mathlib's singleton-`List.map` membership normalization — the annoyance `Lookup.lean`
documented when it deferred this). -/
theorem mem_singleton_map_range {m : Nat} (v : ℤ) :
    [v] ∈ (List.range m).map (fun n => [(n : ℤ)]) ↔ ∃ n, n < m ∧ (n : ℤ) = v := by
  rw [List.mem_map]
  simp only [List.cons.injEq, and_true, bind_pure_comp, List.map_eq_map, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨a, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨↑n, ⟨n, hn, rfl⟩, rfl⟩

/-- Range-row membership ↔ the interval bound (the closed form `Lookup.lean` deferred). -/
theorem range_row_mem_iff (v : ℤ) (k : Nat) :
    [v] ∈ rangeRows k ↔ 0 ≤ v ∧ v < (2 : ℤ) ^ k := by
  have hM : ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by push_cast; ring
  rw [show rangeRows k = (List.range (2 ^ k)).map (fun n => [(n : ℤ)]) from rfl,
      mem_singleton_map_range]
  constructor
  · rintro ⟨n, hn, hv⟩
    constructor
    · rw [← hv]; exact Int.natCast_nonneg n
    · rw [← hv, ← hM]; exact_mod_cast hn
  · rintro ⟨h0, hlt⟩
    refine ⟨v.toNat, ?_, Int.toNat_of_nonneg h0⟩
    have hc : ((v.toNat : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0, hM]
      exact hlt
    exact_mod_cast hc

/-- **A range lookup REPLACES a v1 `VmRange` tooth.** Against the faithful range table, looking
up `[col w]` enforces exactly `VmRange.holds` — the wire lies in `[0, 2^bits)`. The per-row
range-bit aux columns die; the signed wells get their two-limb discipline by lookup. -/
theorem lookup_replaces_range (bits : Nat) (tf : TraceFamily)
    (hr : tf .range = rangeRows bits) (env : VmRowEnv) (w : Nat)
    (h : Lookup.holdsAt tf env ⟨.range, [.var w]⟩) :
    VmRange.holds env ⟨w, bits⟩ := by
  unfold Lookup.holdsAt at h
  rw [hr] at h
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at h
  exact (range_row_mem_iff _ bits).mp h

/-- Completeness: an in-range wire's lookup row IS in the table. -/
theorem lookup_range_complete (bits : Nat) (tf : TraceFamily)
    (hr : tf .range = rangeRows bits) (env : VmRowEnv) (w : Nat)
    (h : VmRange.holds env ⟨w, bits⟩) :
    Lookup.holdsAt tf env ⟨.range, [.var w]⟩ := by
  unfold Lookup.holdsAt
  rw [hr]
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval]
  exact (range_row_mem_iff _ bits).mpr h

/-! ## §9 — Wire rendering: the versioned (`"ir":2`) JSON.

v1 (`emitVmJson`, untouched, NO `"ir"` key ⇒ version 1) and v2 coexist in the registry during the
epoch; the Rust decoder dispatches on the key's presence. -/

/-- Render a list as a JSON array under an element renderer. -/
def jsonArray {α : Type} (f : α → String) : List α → String
  | []      => "[]"
  | x :: xs => "[" ++ f x ++ (xs.foldl (fun acc y => acc ++ "," ++ f y) "") ++ "]"

/-- The chip parameter object: the REAL `babyBearD4W16` pins (same record the v1 emitters carry —
`Poseidon2Binding`), with the round-constant / internal-diagonal sources named (the literal arrays
are p3-baby-bear's published constants; `circuit/src/poseidon2.rs` reads the same source). -/
def chipParamsJson : String :=
  "{\"field_modulus\":" ++ toString babyBearD4W16.fieldModulus ++
  ",\"d\":" ++ toString babyBearD4W16.d ++
  ",\"width\":" ++ toString babyBearD4W16.width ++
  ",\"sbox_degree\":" ++ toString babyBearD4W16.sboxDegree ++
  ",\"sbox_registers\":" ++ toString babyBearD4W16.sboxRegisters ++
  ",\"half_full_rounds\":" ++ toString babyBearD4W16.halfFullRounds ++
  ",\"partial_rounds\":" ++ toString babyBearD4W16.partialRounds ++
  ",\"rate\":" ++ toString CHIP_RATE ++
  ",\"rc_source\":\"BABYBEAR_POSEIDON2_RC_16\"" ++
  ",\"internal_diag_source\":\"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16\"}"

/-- The row-semantics wire tag. -/
def RowSemantics.tag : RowSemantics → String
  | .mainRow      => "main"
  | .permutation  => "poseidon2_chip"
  | .rangeLimb _  => "range"
  | .memAccess    => "memory"
  | .mapReconcile => "map_ops"

/-- Render one table definition (range carries its `bits`; the chip carries its params). -/
def TableDef.toJson (td : TableDef) : String :=
  "{\"id\":" ++ toString td.id.wireId ++ ",\"name\":\"" ++ td.name ++
  "\",\"arity\":" ++ toString td.arity ++ ",\"sem\":\"" ++ td.sem.tag ++ "\"" ++
  (match td.sem with
   | .rangeLimb bits => ",\"bits\":" ++ toString bits
   | .permutation    => ",\"params\":" ++ chipParamsJson
   | _ => "") ++ "}"

/-- The map-op kind wire strings. -/
def MapOpKind.tag : MapOpKind → String
  | .read => "read" | .write => "write" | .absent => "absent"

/-- Render one lookup. -/
def Lookup.toJson (l : Lookup) : String :=
  "{\"t\":\"lookup\",\"table\":" ++ toString l.table.wireId ++
  ",\"tuple\":" ++ jsonArray (·.toJson) l.tuple ++ "}"

/-- Render one mem op (the instrumented offline-checking row). -/
def MemOp.toJson (m : MemOp) : String :=
  "{\"t\":\"mem_op\",\"kind\":\"" ++ kindTag m.kind ++ "\",\"guard\":" ++ m.guard.toJson ++
  ",\"addr\":" ++ m.addr.toJson ++ ",\"value\":" ++ m.value.toJson ++
  ",\"prev_value\":" ++ m.prevValue.toJson ++
  ",\"prev_serial\":" ++ m.prevSerial.toJson ++ "}"

/-- Render one map op (the `(root, key, value, op) → new_root` opening). -/
def MapOp.toJson (m : MapOp) : String :=
  "{\"t\":\"map_op\",\"op\":\"" ++ m.op.tag ++ "\",\"guard\":" ++ m.guard.toJson ++
  ",\"root\":" ++ m.root.toJson ++ ",\"key\":" ++ m.key.toJson ++
  ",\"value\":" ++ m.value.toJson ++ ",\"new_root\":" ++ m.newRoot.toJson ++ "}"

/-- Render one v2 constraint (the v1 forms reuse the v1 renderer byte-for-byte). -/
def VmConstraint2.toJson : VmConstraint2 → String
  | .base c   => c.toJson
  | .lookup l => l.toJson
  | .memOp m  => m.toJson
  | .mapOp m  => m.toJson

/-- **`emitVmJson2`** — the canonical v2 wire string: versioned (`"ir":2`), tables declared,
constraints in v2 grammar, v1 hash-site/range carriers preserved. -/
def emitVmJson2 (d : EffectVmDescriptor2) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"ir\":" ++ toString IR_VERSION ++
  ",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.piCount ++
  ",\"tables\":" ++ jsonArray TableDef.toJson d.tables ++
  ",\"constraints\":" ++ jsonArray VmConstraint2.toJson d.constraints ++
  ",\"hash_sites\":" ++ hashSitesToJson d.hashSites ++
  ",\"ranges\":" ++ rangesToJson d.ranges ++ "}"

/-- The shared-tables wire string (the registry's table manifest: chip + range + memory +
map-ops; main is per-descriptor). -/
def sharedTablesJson : String := jsonArray TableDef.toJson sharedTableDefs

/-! ## §10 — Tripwires: shape pins + non-vacuity (TRUE and FALSE witnesses). -/

/-- A small descriptor exercising every v2 constraint kind (the wire-grammar golden's subject). -/
def demoV2 : EffectVmDescriptor2 :=
  { name := "demo-v2", traceWidth := 2, piCount := 1
  , tables := v2Tables 2
  , constraints :=
      [ .base (.transition 0 0)
      , .lookup ⟨.range, [.var 0]⟩
      , .memOp ⟨.const 1, .var 0, .var 1, .var 1, .const 0, .read⟩
      , .mapOp ⟨.const 1, .var 0, .var 1, .const 0, .var 1, .write⟩ ]
  , hashSites := [], ranges := [] }

-- THE WIRE GOLDEN: the canonical v2 JSON, byte-pinned (versioned `"ir":2`; every v2 constraint
-- kind exercised; the chip params are the REAL babyBearD4W16 pins). The Rust v2 decoder's
-- grammar is THIS string's grammar; v1 strings (no `"ir"` key) parse as version 1 unchanged.
#guard emitVmJson2 demoV2 ==
  "{\"name\":\"demo-v2\",\"ir\":2,\"trace_width\":2,\"public_input_count\":1,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":2,\"sem\":\"main\"},{\"id\":1,\"name\":\"poseidon2_chip\",\"arity\":10,\"sem\":\"poseidon2_chip\",\"params\":{\"field_modulus\":2013265921,\"d\":4,\"width\":16,\"sbox_degree\":7,\"sbox_registers\":1,\"half_full_rounds\":4,\"partial_rounds\":13,\"rate\":8,\"rc_source\":\"BABYBEAR_POSEIDON2_RC_16\",\"internal_diag_source\":\"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16\"}},{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30},{\"id\":3,\"name\":\"memory\",\"arity\":5,\"sem\":\"memory\"},{\"id\":4,\"name\":\"map_ops\",\"arity\":5,\"sem\":\"map_ops\"}],\"constraints\":[{\"t\":\"transition\",\"hi\":0,\"lo\":0},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"mem_op\",\"kind\":\"read\",\"guard\":{\"t\":\"const\",\"v\":1},\"addr\":{\"t\":\"var\",\"v\":0},\"value\":{\"t\":\"var\",\"v\":1},\"prev_value\":{\"t\":\"var\",\"v\":1},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"map_op\",\"op\":\"write\",\"guard\":{\"t\":\"const\",\"v\":1},\"root\":{\"t\":\"var\",\"v\":0},\"key\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"const\",\"v\":0},\"new_root\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}"

-- The chip rate is the REAL babyBearD4W16 base rate (8); the chip row is 10 wide.
#guard CHIP_RATE == 8
#guard poseidon2ChipTableDef.arity == CHIP_RATE + 2
#guard (chipRow (fun _ => 0) [1, 2]).length == CHIP_RATE + 2
-- The five table ids are distinct on the wire.
#guard ([TableId.main, .poseidon2, .range, .memory, .mapOps].map TableId.wireId).dedup.length == 5

-- Range-by-lookup: in-range row PRESENT, out-of-range row ABSENT (the rangeTable for 2 bits).
#guard ([3] : List ℤ) ∈ rangeRows 2
#guard ¬ (([4] : List ℤ) ∈ rangeRows 2)
#guard ¬ (([-1] : List ℤ) ∈ rangeRows 2)

-- Memory non-vacuity at the IR instantiation (the model's own polarity demos live in
-- `Crypto/MemoryChecking.lean`): the honest write-then-read trace at felt addr 1 (init 5) is
-- disciplined, BALANCES, and is consistent; a tampered read is INCONSISTENT.
#guard decide (MemoryChecking.Disciplined
  ([⟨.write, 1, 9, 5, 0⟩, ⟨.read, 1, 9, 9, 1⟩] : List MemTraceOp))
#guard decide (MemoryChecking.MemCheck (fun _ => (5 : ℤ))
  (fun a => if a = 1 then ((9 : ℤ), 2) else ((5 : ℤ), 0)) [(1 : ℤ)]
  ([⟨.write, 1, 9, 5, 0⟩, ⟨.read, 1, 9, 9, 1⟩] : List MemTraceOp))
#guard decide (MemoryChecking.Consistent (fun _ => (5 : ℤ))
  ([⟨.write, 1, 9, 5, 0⟩, ⟨.read, 1, 9, 9, 1⟩] : List MemTraceOp))
#guard decide (¬ MemoryChecking.Consistent (fun _ => (5 : ℤ))
  ([⟨.read, 1, 7, 7, 0⟩] : List MemTraceOp))

-- Padding discipline: the arity tag disambiguates ([1] at rate 8 vs [1,0] at rate 8 share the
-- padded block but NOT the tag).
#guard padTo 4 [1, 2] == [1, 2, 0, 0]
#guard (chipRow (fun _ => 99) [1]).head? == some 1
#guard (chipRow (fun _ => 99) [1, 0]).head? == some 2

-- The embedded-v1 face is inert: no mem ops, no map ops.
#guard (memOpsOf (embedV1 { name := "n", traceWidth := 1, piCount := 0, constraints := [.transition 0 0], hashSites := [], ranges := [] })).length == 0

#assert_axioms TableId.wireId_injective
#assert_axioms opensTo_functional
#assert_axioms opensTo_some_excludes_none
#assert_axioms writesTo_functional
#assert_axioms opensTo_none_of_gap
#assert_axioms satisfied2_mem_consistent
#assert_axioms memOpsOf_embedV1
#assert_axioms memLog_embedV1
#assert_axioms memCheck_nil
#assert_axioms embedV1_satisfied_iff
#assert_axioms padTo_inj
#assert_axioms map_eval_padToE
#assert_axioms chip_lookup_sound
#assert_axioms siteLookup_replaces_site
#assert_axioms range_row_mem_iff
#assert_axioms lookup_replaces_range
#assert_axioms lookup_range_complete

end Dregg2.Circuit.DescriptorIR2
