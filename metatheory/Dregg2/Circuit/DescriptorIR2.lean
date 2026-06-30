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
`MemoryChecking.memcheck_sound` (unconditional combinatorics — no crypto, no hypothesis).
NEW file; imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Lookup
import Dregg2.Substrate.Heap
import Dregg2.Circuit.MapMerkleRoot
import Dregg2.Crypto.MemoryChecking
import Dregg2.Crypto.UniversalMemory
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
  /-- One row per UNIVERSAL state access: the domain-tagged `Option`-valued offline-checking
  entry (`docs/UNIVERSAL-MEMORY.md` — the one Blum multiset over `Domain × κ`). -/
  | umemAccess
  /-- One row per declared universal address: the `(domain, key)` boundary image
  (init/final `Option` cells), domain-major strictly increasing. -/
  | umemBoundaryRow
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

/-- The chip's INPUT-LANE COUNT: how many base-field input felts ONE chip row (= one Poseidon2
permutation) seeds. This is DISTINCT from the Poseidon2 sponge rate ([`CHIP_SPONGE_RATE`] = 8):
one permutation can SEED up to `width − capacity` lanes regardless of the multi-block sponge
rate. Phase B-GATE-INPUT widened it `8 → 11` so a single permutation can absorb an 8-felt
commitment carrier + 3 new limbs (the wide Merkle–Damgård step of the faithful 8-felt
commitment, Phase B-ROTATION). Phase H3 (native-8-felt Merkle root weld) widened it `11 → 16` =
full `width`: the `node8` arity-16 row compresses two 8-felt child digests `L8 ‖ R8` in ONE
permutation (no capacity — fixed-length compression domain-separated by the arity tag), reading
lanes `0..8` for the node's 8-felt digest. (`16 = width`, the full-width seed.) -/
def CHIP_RATE : Nat := 16

/-- The Poseidon2 SPONGE RATE in base field elements (`babyBearD4W16.rate = rate_ext · d = 8`) —
the REAL multi-block-sponge absorb width, a cryptographic parameter pinned in
`circuit/src/poseidon2.rs`. Emitted as the chip `params.rate`. NOT the chip's input-lane count
([`CHIP_RATE`] = 11, the single-permutation seed width). -/
def CHIP_SPONGE_RATE : Nat := babyBearD4W16.rate

/-- The number of permutation-output lanes the chip exposes on the bus tuple. Phase B-GATE
widened the output block `1 → 8`: the chip row carries `state[0..8]` of the SAME already
fully-constrained final permutation. Lane 0 is the squeezed digest every single-output site
binds (`hash`); lanes 1..7 are the genuine distinct lanes the 8-felt commitment sponge will use
(Phase B-ROTATION). The deployed commitment STAYS 1-felt (lane0) after this phase — the extra
lanes are CARRIED (made available + bound to the genuine permutation by the Rust chip AIR) but
NOT yet folded into any commitment. -/
def CHIP_OUT_LANES : Nat := 8

/-- The canonical limb width for the shared range table: the two-limb signed-well discipline
(the deployed balance limbs are 30-bit — `EffectVmEmitTransfer`'s `VmRange ⟨…, 30⟩` teeth). -/
def BAL_LIMB_BITS : Nat := 30

/-- main table (per-descriptor width — the v2 main is thin; during the epoch it carries the
descriptor's own trace width). -/
def mainTableDef (width : Nat) : TableDef := ⟨.main, "main", width, .mainRow⟩

/-- The Poseidon2 chip table: `1 (arity tag) + CHIP_RATE (padded inputs) + CHIP_OUT_LANES (output
lanes)` columns (Phase B-GATE widened the output block `1 → 8`). -/
def poseidon2ChipTableDef : TableDef :=
  ⟨.poseidon2, "poseidon2_chip", CHIP_RATE + 1 + CHIP_OUT_LANES, .permutation⟩

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

/-! ### The UNIVERSAL memory op (`docs/UNIVERSAL-MEMORY.md` — the one Blum multiset).

A `UMemOp` is a state access against the unified `Domain × κ` address space
(`Dregg2.Crypto.UniversalMemory.UAddr`): the address is the PAIR `(domain, key)` — the domain
tag is carried as its own bus coordinate, so the abstract injectivity `(d, a) = (d, b) ↔ a = b`
is wire-literal (no hashing at all, not even the boundary `addr = hash[domain, coll, key]`
realization — strictly stronger). Cells are `Option`-valued: `(present, value)` with the
canonical encoding `none ↦ (0, 0)`, `some v ↦ (1, v)` — which is what makes nullifier freshness
ONE read row returning `none` (`nullifier_fresh_sound`), Merkle-path-free. -/

/-- The wire code of a state domain (`UniversalMemory.Domain`): the five committed collections
of the commitment layout, plus `working` (transient scratch, wire code `5`, IDENTICAL to the Rust
`UDomain::Working` at `turn/src/umem.rs:118`). A FUTURE state component is a new code, never a new
table. -/
def domainCode : UniversalMemory.Domain → ℤ
  | .registers => 0 | .heap => 1 | .caps => 2 | .nullifiers => 3 | .index => 4
  | .working => 5

/-- Domain codes are collision-free on the wire. -/
theorem domainCode_injective : Function.Injective domainCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [domainCode]

/-- A universal-memory access row: the offline-checking instrumentation against the
domain-tagged address space, with `Option`-valued cells as `(present, value)` pairs.
`guard` gates the contribution; the op's own serial is positional (like `MemOp`). -/
structure UMemOp where
  guard       : EmittedExpr
  domain      : UniversalMemory.Domain
  key         : EmittedExpr
  present     : EmittedExpr
  value       : EmittedExpr
  prevPresent : EmittedExpr
  prevValue   : EmittedExpr
  prevSerial  : EmittedExpr
  kind        : MemoryChecking.Kind
  deriving Repr

/-- Map reconciliation kind: a membership read, a non-membership read, a (sorted insert-or-
update at an EXISTING key) write, or a (sorted insert at a FRESH key) insert. The `write` and
`insert` denotations are both `writesTo` (sorted insert-or-update); they differ ONLY in the wire
`op` column so the deployed map-ops table picks the right opening procedure (an update opens the
old leaf's path; a fresh insert opens against the NEW tree). Freshness for `insert` is established
SEPARATELY by a paired `absent` op against the same pre-root (the noteSpend double-spend tooth). -/
inductive MapOpKind where
  | read | write | absent | insert
  deriving Repr, DecidableEq, BEq

/-- The wire code of a map-op kind (the map-ops table's `op` column value; matches the Rust
`MapKind::code`). -/
def MapOpKind.code : MapOpKind → ℤ
  | .read => 0 | .write => 1 | .absent => 2 | .insert => 3

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

/-! ### The accumulator / recursive-proof-binding op (`docs/EPOCH-DESIGN.md` — the Custom leg).

The four `Lookup`/`MemOp`/`MapOp`/`UMemOp` kinds are all ROW-LOCAL: a lookup is a table
membership, a mem/map/umem op is one entry in an offline-checking multiset. NONE can fold in
another STARK proof. `Custom` (effect selector 8) dispatches a cell program whose domain
constraints are proven EXTERNALLY: the row binds to that external sub-proof via its
`custom_proof_commitment` (the params columns `circuit/src/effect_vm/columns.rs` calls
`CUSTOM_PROOF_COMMIT_BASE`). Today the AIR only RECORDS that commitment in the public inputs and
TRUSTS it (`circuit/src/effect_vm/air.rs` Gap-5: "the Effect VM circuit does NOT verify the
external proof"). `ProofBind` closes that: the row commits to the VERIFICATION of the external
proof — the bound sub-proof's public-input commitment must MATCH the row's commitment column
(and its program VK the row's vk column), against a verifying sub-proof.

This is the recursion/IVC boundary the rest of the stack already names (`Dregg2.Circuit.Recursive-
Aggregation.EngineSound.recursive_sound`, `circuit/src/joint_turn_recursive.rs`'s leaf verifier,
`ivc_turn_chain.rs`'s aggregate prover): an opaque `Proof` carrier + a `verify : Proof → Bool`,
with the in-circuit-verifier soundness supplied as a NAMED, REALIZABLE hypothesis (the one FRI
obligation outside Lean). `ProofBind.holdsAt` is `True` row-locally — exactly like `memOp`/`umemOp`
— and the binding content is the SEPARATE `Satisfied2Custom` leg (§6c), whose keystone
`proofBind_determined` is the anti-ghost: under the named engine binding, a row's commitment is
the GENUINE commitment of a verifying sub-proof — a forged one no sub-proof attests is
UNSATISFIABLE. -/

/-- An accumulator / recursive-proof-binding op: the row's `custom_proof_commitment` column
(`commit`) and `custom_program_vk_hash` column (`vk`), gated by `guard`. The denotation
(§6c) binds them to a VERIFYING external sub-proof — the row commits to the verification of the
external proof, rather than trusting it. -/
structure ProofBind where
  guard  : EmittedExpr
  commit : EmittedExpr
  vk     : EmittedExpr
  deriving Repr

/-! ### §2.5 — `WindowExpr`: a two-row arithmetic expression (the cumulative-sum primitive).

The base `EmittedExpr` (`Dregg2.Exec.CircuitEmit`) reads ONE row (`Assignment`), so a `gate`
body cannot express a cross-row relation like the aggregation AIR's running cumulative
`next[cum] = local[cum] + next[contribution]`. `WindowExpr` adds the missing primitive: a
polynomial over BOTH the current row (`loc c`) and the next row (`nxt c`). It is a strict
generalization — `EmittedExpr.var c` is `WindowExpr.loc c`. The denotation reads the
`VmRowEnv`'s `loc`/`nxt` slices exactly as the Rust `builder.when_transition()` arm does
(`next[..]` / `local[..]`), so this is the faithful Lean twin of a windowed `assert_zero`. -/
inductive WindowExpr where
  /-- Current-row column `c`. -/
  | loc   (c : Nat)
  /-- Next-row column `c`. -/
  | nxt   (c : Nat)
  /-- A field constant. -/
  | const (k : ℤ)
  | add   (a b : WindowExpr)
  | mul   (a b : WindowExpr)
  deriving Repr

/-- Evaluate a `WindowExpr` against a row window (`loc`/`nxt` assignments). -/
def WindowExpr.eval (env : VmRowEnv) : WindowExpr → ℤ
  | .loc c   => env.loc c
  | .nxt c   => env.nxt c
  | .const k => k
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env

/-- Wire-render a `WindowExpr` (the Rust decoder mirrors this: `loc`/`nxt` carry a row tag, the
arithmetic nodes reuse the `EmittedExpr` shape). -/
def WindowExpr.toJson : WindowExpr → String
  | .loc c   => "{\"t\":\"loc\",\"c\":" ++ toString c ++ "}"
  | .nxt c   => "{\"t\":\"nxt\",\"c\":" ++ toString c ++ "}"
  | .const k => "{\"t\":\"const\",\"v\":" ++ (if k < 0 then "-" ++ toString (-k) else toString k) ++ "}"
  | .add l r => "{\"t\":\"add\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"
  | .mul l r => "{\"t\":\"mul\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"

/-- A windowed constraint: the polynomial `body` (over the current+next row) must vanish.
`onTransition = true` ⇒ asserted only on the transition (every row but the last, the Rust
`when_transition()` arm); `false` ⇒ asserted on every row (a row-local two-row gate that also
fires on the last row, where `nxt` is the wrap row). The aggregation AIR's cumulative
transitions are `onTransition = true`. -/
structure WindowConstraint where
  body         : WindowExpr
  onTransition : Bool
  deriving Repr

/-- The windowed constraint holds on a row window. On `onTransition`, the body need only vanish
when this is NOT the last row (`isLast = false`); otherwise it vanishes on every row. -/
def WindowConstraint.holdsAt (env : VmRowEnv) (isLast : Bool) (w : WindowConstraint) : Prop :=
  if w.onTransition then
    isLast = false → w.body.eval env = 0
  else
    w.body.eval env = 0

/-- Wire-render a `WindowConstraint`. -/
def WindowConstraint.toJson (w : WindowConstraint) : String :=
  "{\"t\":\"window_gate\",\"on_transition\":" ++ (if w.onTransition then "true" else "false") ++
  ",\"body\":" ++ w.body.toJson ++ "}"

/-- The v2 constraint: v1 embedded whole, plus the three new ROW-LOCAL kinds, the UNIVERSAL memory
op (`umemOp`, additive: no shipped descriptor emits it until the rotation), the accumulator /
recursive-proof-binding op (`proofBind`, the Custom leg), and the two-row `windowGate` (the
aggregation-AIR cumulative-sum primitive — additive, carried exactly like the rest of IR-v2). -/
inductive VmConstraint2 where
  | base       (c : VmConstraint)
  | lookup     (l : Lookup)
  | memOp      (m : MemOp)
  | mapOp      (m : MapOp)
  | umemOp     (m : UMemOp)
  | proofBind  (m : ProofBind)
  | windowGate (w : WindowConstraint)
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

/-! ## §4 — Map-op semantics: openings of the PROVEN sorted-Poseidon2 map, committed by the
DEPLOYED depth-16 BINARY MERKLE root (`MapMerkleRoot.mapRoot` — `heap_root.rs::CanonicalHeapTree`).

The denotation is an EXISTENTIAL opening of `Dregg2.Substrate.Heap`'s sorted map — the prover witnesses
a sorted heap behind the root. The COMMITMENT is the deployed depth-`HEAP_TREE_DEPTH` BINARY MERKLE fold
(`MapMerkleRoot.mapRoot`: arity-2 `leafOf` leaves, arity-2 `mapNode` nodes), NOT the flat sponge — the
fixed-depth tree the `Ir2Air::MapOps` AIR (`descriptor_ir2.rs:2213`) recomposes by its `mix` closure. The
deployment pins every heap as the `2^HEAP_TREE_DEPTH`-leaf padded vector; the opening carries that
`length = 2^HEAP_TREE_DEPTH` discipline. Under the one named CR floor the opening is FUNCTIONAL
(`MapMerkleRoot.mapRoot_injective` — the binary fold pins the heap via `perfectRoot_injective` /
`mapNode_injective`, NOT the sponge `root_injective`), so the root + key determine the value / new-root:
the map-op row cannot lie. Non-membership reuses the gap bracketing (`get_none_of_gap`). -/

/-- The deployed map-tree depth (`heap_root.rs::HEAP_TREE_DEPTH = 16`). -/
abbrev MAP_TREE_DEPTH : Nat := MapMerkleRoot.HEAP_TREE_DEPTH

/-- `opensTo hash r k o` — some sorted, depth-`MAP_TREE_DEPTH` `2^d`-leaf heap behind the DEPLOYED
BINARY-MERKLE root `r` reads `o` at `k`. The denotation of the deployed `Ir2Air::MapOps` opening. -/
def opensTo (hash : List ℤ → ℤ) (r k : ℤ) (o : Option ℤ) : Prop :=
  MapMerkleRoot.opensToMerkle hash MAP_TREE_DEPTH r k o

/-- `writesTo hash r k v r'` — some sorted, depth-`MAP_TREE_DEPTH` `2^d`-leaf heap behind binary root
`r` produces root `r'` under the sorted insert-or-update of `(k, v)` (the post-heap still `2^d`-leaf). -/
def writesTo (hash : List ℤ → ℤ) (r k v r' : ℤ) : Prop :=
  MapMerkleRoot.writesToMerkle hash MAP_TREE_DEPTH r k v r'

/-- **Openings are FUNCTIONAL (the anti-ghost).** Under CR, the BINARY-MERKLE root + key determine the
read: two openings of the same root at the same key agree. Re-proved against the deployed binary fold
(`MapMerkleRoot.opensToMerkle_functional` → `mapRoot_injective` → `perfectRoot_injective` /
`mapNode_injective`), NOT the flat-sponge `root_injective`. A map-op row cannot claim a tampered value. -/
theorem opensTo_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensTo hash r k o₁) (h₂ : opensTo hash r k o₂) : o₁ = o₂ :=
  MapMerkleRoot.opensToMerkle_functional hash hCR MAP_TREE_DEPTH h₁ h₂

/-- Membership and non-membership at the same root/key EXCLUDE each other (the tooth the
nullifier/cap non-membership argument needs from the map-ops table). -/
theorem opensTo_some_excludes_none (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k v : ℤ} (h₁ : opensTo hash r k (some v)) (h₂ : opensTo hash r k none) : False :=
  MapMerkleRoot.opensToMerkle_some_excludes_none hash hCR MAP_TREE_DEPTH h₁ h₂

/-- **Writes are FUNCTIONAL.** Under CR, the BINARY-MERKLE root + key + value determine the new root:
the map-op row's `new_root` column cannot be forged. Re-proved against the deployed binary fold
(`MapMerkleRoot.writesToMerkle_functional` → `mapRoot_injective`), NOT the flat-sponge `root_injective`. -/
theorem writesTo_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {r k v r₁ r₂ : ℤ}
    (h₁ : writesTo hash r k v r₁) (h₂ : writesTo hash r k v r₂) : r₁ = r₂ :=
  MapMerkleRoot.writesToMerkle_functional hash hCR MAP_TREE_DEPTH h₁ h₂

/-- Non-membership openings are CONSTRUCTIBLE from the proven gap bracketing — completeness of the
`absent` kind (the `sorted_gap_excludes` machinery, via `Heap.get_none_of_gap`), over a depth-`d`
`2^d`-leaf heap (the deployed fixed-depth tree). -/
theorem opensTo_none_of_gap (hash : List ℤ → ℤ) {h : Heap.FeltHeap} {r lo hi k : ℤ}
    (hs : Heap.SortedKeys h) (hlen : h.length = 2 ^ MAP_TREE_DEPTH)
    (hr : MapMerkleRoot.mapRoot hash MAP_TREE_DEPTH h = r)
    (hadj : Dregg2.Crypto.NonMembership.Adjacent (Heap.keys h) lo hi)
    (hlo : lo < k) (hhi : k < hi) : opensTo hash r k none :=
  ⟨h, hs, hlen, hr, Heap.get_none_of_gap h lo hi k hs hadj hlo hhi⟩

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
    | .insert => writesTo hash (m.root.eval env.loc) (m.key.eval env.loc)
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

/-- Per-row meaning of one v2 constraint. `memOp`/`umemOp`/`proofBind` are `True` here because they
are not row-local equations — but their DEPLOYED status differs and the difference is load-bearing:
* `memOp` — REAL: the content is the GLOBAL leg of `Satisfied2` (`memBalanced`), and that leg IS
  deployed-enforced (the LogUp bus + Blum multiset balance + the verifier's zero-sum check). (One
  open seam: the flat-memory `minit` boundary is not yet anchored to the committed pre-state root —
  umem already closes this pattern via `whole_image_fold`.)
* `umemOp` — its global leg lives in `Satisfied2U` (staged), with the boundary anchored to the
  committed root.
* `proofBind` — its content lives in `Satisfied2Custom`, which is NOT the deployed `Satisfied2`, and
  the deployed prover does not yet fold the custom sub-proof leaf. So this arm is VACUOUS for a pure
  light client as-shipped (`CustomCarrierAttack.deployed_admits_unbacked`); the real binding is the
  FOLD (`CustomBindingFromFold` + `joint_turn_recursive.prove_custom_binding_node`), whose premise
  (a verifying aggregate that folds the custom leaf) is met only once that node is on the deployed
  prove path. Do NOT read this `True` as "compensated like memOp". -/
def VmConstraint2.holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : VmConstraint2 → Prop
  | .base c       => c.holdsVm env isFirst isLast
  | .lookup l     => l.holdsAt tf env
  | .memOp _      => True
  | .mapOp m      => m.holdsAt hash env
  | .umemOp _     => True
  | .proofBind _  => True
  | .windowGate w => w.holdsAt env isLast

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

/-! ## §6a' — the FLAT memory boundary is BOUND to committed pre/post-state (the anchor that
CLOSES the flat-`minit` hole). The EXACT structural mirror of §6b's `satisfied2U_init_root`
family, instantiated at the TOTAL flat image `minit : ℤ → ℤ`. A flat boundary declares every
address PRESENT, so its boundary view is `boundaryCells (some ∘ minit) maddrs` — the same
sorted-Poseidon2 leaf list the universal init side folds, with `Option`-wrap saturated to `some`.

The hole these legs close: `Satisfied2` takes `minit`/`mfin` as FREE witness parameters with only
`memBalanced` (the Blum balance RELATIVE to the prover's chosen `minit`). Nothing forced the
declared `minit` to be the COMMITTED pre-state, so a prover could declare a forged `minit[a]` for
an untouched address `a`, the balance still closes, and `verify_batch` accepted an image that was
never committed prior state. These legs pin the flat boundary's init/fin root to a committed
pre/post-state root (the `minit_root`/`mfin_root` PIs the emitter publishes); the `root_injective`
forge tooth then REFUSES any boundary whose image differs from the committed state. The umem legs
already carry the proofs — these re-state them at the flat denotation. -/

/-- **The flat INIT boundary is BOUND to committed pre-state — `boundary_init_root_derived`
applied.** If the committed PRE-state heap `mpre` has the lookup semantics of the declared flat
init image `minit` over the declared, sorted addresses `as` (present at every declared address,
absent off the list), then the committed pre-state root EQUALS the sorted-Poseidon2 root of the
boundary view derived from `minit`. Pinning that derived root to the committed pre-state root (the
`minit_root` PI) forces the declared init image to be the committed pre-state. The flat analog of
`satisfied2U_init_root`; `minit` is the GIVEN, so no memcheck pinning is needed (it is even simpler
than the universal side). -/
theorem satisfied2_init_root (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {mpre : Heap.FeltHeap} {as : List ℤ}
    (_h : Satisfied2 hash d minit mfin maddrs t)
    (hs : Heap.SortedKeys mpre) (has : as.Pairwise (· < ·))
    (hsem : ∀ a, Heap.get mpre a = if a ∈ as then some (minit a) else none) :
    Heap.root hash mpre
      = Heap.root hash (UniversalMemory.boundaryCells (fun a => some (minit a)) as) :=
  UniversalMemory.boundary_init_root_derived hash hs has hsem

/-- **The flat FINAL boundary is BOUND to committed post-state — `boundary_init_root_derived`
applied to the final image.** The post-state companion of `satisfied2_init_root`: if the committed
POST-state heap `mpost` has the lookup semantics of the claimed final image `(mfin ·).1` over the
declared sorted addresses, then the committed post-state root EQUALS the sorted-Poseidon2 root of
the boundary view derived from `mfin`. Pinning that to the `mfin_root` PI binds the carried-forward
post-state. (That the claimed `mfin` is the GENUINE fold of `minit` + the log writes is the
SEPARATE `memBalanced` leg — `satisfied2_mem_consistent`; this leg binds the published post-state
ROOT to the claimed image, exactly as the init leg binds the pre-state root to `minit`.) -/
theorem satisfied2_fin_root (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {mpost : Heap.FeltHeap} {as : List ℤ}
    (_h : Satisfied2 hash d minit mfin maddrs t)
    (hs : Heap.SortedKeys mpost) (has : as.Pairwise (· < ·))
    (hsem : ∀ a, Heap.get mpost a = if a ∈ as then some (mfin a).1 else none) :
    Heap.root hash mpost
      = Heap.root hash (UniversalMemory.boundaryCells (fun a => some (mfin a).1) as) :=
  UniversalMemory.boundary_init_root_derived hash hs has hsem

/-- **The flat boundary binding is SOUND (the anti-forgery tooth) — `Heap.root_injective` under
`Poseidon2SpongeCR`.** A committed pre-state map `mcommitted` and the prover's declared init heap
`mdeclared` carry the SAME root iff they ARE the same map. So pinning the `minit_root` PI to the
committed pre-state root forces the declared flat init image to be the committed pre-state — a
forged `minit` (a tampered value at a declared address, the exploit the diagnosis confirmed)
CANNOT keep the published root. The flat analog of `boundary_init_root_bound`. -/
theorem satisfied2_init_root_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {mcommitted mdeclared : Heap.FeltHeap}
    (hroot : Heap.root hash mdeclared = Heap.root hash mcommitted) :
    mdeclared = mcommitted :=
  Heap.root_injective hash hCR hroot

/-- **THE WHOLE-IMAGE flat init binding — `boundary_whole_image_sem` applied.** The no-extra-cells
direction: if the committed pre-state root EQUALS the sorted-Poseidon2 fold of the ENTIRE declared
flat boundary image `boundaryCells (some ∘ minit) as` — the obligation the in-circuit whole-image
root-fold discharges (the `whole_image_fold` sorted-insert chip cross-bound to the `MemBoundary`
table) — then under the named CR floor the committed heap agrees with the declared init image at
EVERY address: declared cells open to `minit a`, and every address OFF the declared list is ABSENT.
So a committed pre-state holding any value the boundary did not declare CANNOT keep the published
root; the flat boundary image is the WHOLE committed pre-state. This is what rejects a forged
`minit[a]=999` at an UNTOUCHED declared field: that forged image folds to a DIFFERENT root, so the
`minit_root` PI pin against the committed pre-state root REFUSES. The flat companion of
`satisfied2U_init_whole_image`. -/
theorem satisfied2_init_whole_image (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {mcommitted : Heap.FeltHeap} {minit : ℤ → ℤ} {as : List ℤ}
    (has : as.Pairwise (· < ·))
    (hpin : Heap.root hash mcommitted
      = Heap.root hash (UniversalMemory.boundaryCells (fun a => some (minit a)) as)) :
    ∀ a, Heap.get mcommitted a = if a ∈ as then some (minit a) else none :=
  UniversalMemory.boundary_whole_image_sem hash hCR has hpin

/-! ## §6b — `Satisfied2U`: the UNIVERSAL-memory denotation (the one-Blum-multiset leg).

`docs/UNIVERSAL-MEMORY.md`, realized at the IR: a descriptor's `umemOp`s gather into ONE log
over the `Domain × κ` address space with `Option ℤ` cells, certified by ONE balance against a
declared universal boundary `(uinit, ufin, uaddrs)`. The keystones are direct applications of
the PROVED `Dregg2.Crypto.UniversalMemory` results:

  * `satisfied2U_umem_sound` — `universal_memory_sound`: the whole log is consistent AND every
    domain's projection is a consistent standalone memory (registers + heap + caps +
    nullifiers + index, one argument, zero intra-proof hashing);
  * `satisfied2U_pins_final` — `memcheck_pins_final`: the claimed final column is FORCED;
  * `satisfied2U_boundary_root` — `boundary_root_from_memcheck`: the per-domain map root
    derived from the (pinned) final column EQUALS today's committed map root — the map roots
    are DERIVED BOUNDARY VIEWS, by canonicity, no crypto;
  * `satisfied2U_nullifier_fresh` — `nullifier_fresh_sound`: a read returning `none` at
    `(nullifiers, x)` proves initial absence AND no intra-proof insert — NO Merkle path, NO gap
    opening, NO hashing intra-proof. (The gap machinery survives exactly at the boundary: the
    `absent` map-op authenticates the loaded initial view against the incoming root, once per
    touched address per proof — `nullifier_fresh_binds_root`'s composition.)

The insert-only discipline (`InsertOnlyAt` — nobody un-spends) is a DENOTATION leg
(`umemNullifierInsertOnly`), realized in-table by the interpreter: a nullifier-domain write
installing `none` is refused in-circuit. -/

/-- Decode a `(present, value)` column pair to the `Option` cell: `present = 1 ↦ some value`,
anything else `↦ none` (the table AIR pins `present` boolean and `none ↦ value = 0`). -/
def optOf (p v : ℤ) : Option ℤ := if p = 1 then some v else none

/-- The present bit of the canonical `Option` encoding. -/
def presentBit : Option ℤ → ℤ
  | none => 0 | some _ => 1

/-- The payload of the canonical `Option` encoding (`none ↦ 0`). -/
def payloadOf : Option ℤ → ℤ
  | none => 0 | some v => v

@[simp] theorem optOf_roundtrip (o : Option ℤ) : optOf (presentBit o) (payloadOf o) = o := by
  cases o <;> simp [optOf, presentBit, payloadOf]

/-- A gathered universal-memory operation: the proved model's op over the domain-tagged
address space with `Option` cells. -/
abbrev UMemTraceOp := MemoryChecking.Op (UniversalMemory.UAddr ℤ) (Option ℤ)

/-- Evaluate a `UMemOp` on a row: `some` instrumented op when the guard fires. The address is
the literal pair `(domain, key)` — the tag is a separate coordinate, injective for free. -/
def UMemOp.opAt? (a : Assignment) (m : UMemOp) : Option UMemTraceOp :=
  if m.guard.eval a = 1 then
    some ⟨m.kind, (m.domain, m.key.eval a),
          optOf (m.present.eval a) (m.value.eval a),
          optOf (m.prevPresent.eval a) (m.prevValue.eval a),
          (m.prevSerial.eval a).toNat⟩
  else none

/-- The universal-memory ops a descriptor declares. -/
def umemOpsOf (d : EffectVmDescriptor2) : List UMemOp :=
  d.constraints.filterMap fun c => match c with | .umemOp m => some m | _ => none

/-- The gathered universal-memory log: every main row's guarded `umemOp` entries, in trace
order (positional serials number EXACTLY this order). -/
def umemLog (d : EffectVmDescriptor2) (t : VmTrace) : List UMemTraceOp :=
  t.rows.flatMap fun a => (umemOpsOf d).filterMap (UMemOp.opAt? a)

/-- The universal-memory table row of an op:
`[domain, key, present, value, prev_present, prev_value, prev_serial, kind]`. -/
def uopRow (op : UMemTraceOp) : List ℤ :=
  [domainCode op.addr.1, op.addr.2,
   presentBit op.val, payloadOf op.val,
   presentBit op.prevVal, payloadOf op.prevVal,
   (op.prevSerial : ℤ), kindCode op.kind]

/-- The trace-family slot of the universal memory table (`custom 1`, wire id 6; the submask
table is `custom 0`, wire id 5). -/
def UMEM_TID : Nat := 1

/-- **The universal-memory denotation** — `Satisfied2` PLUS the one-Blum-multiset legs against
the declared universal boundary (initial image `uinit`, claimed final image `ufin`, declared
address list `uaddrs`, all over `Domain × κ`). -/
structure Satisfied2U (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (uinit : UniversalMemory.UAddr ℤ → Option ℤ)
    (ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat)
    (uaddrs : List (UniversalMemory.UAddr ℤ)) (t : VmTrace) : Prop
    extends Satisfied2 hash d minit mfin maddrs t where
  umemAddrsNodup : uaddrs.Nodup
  umemClosed : ∀ op ∈ umemLog d t, op.addr ∈ uaddrs
  umemDisciplined : MemoryChecking.Disciplined (umemLog d t)
  umemBalanced : MemoryChecking.MemCheck uinit ufin uaddrs (umemLog d t)
  umemNullifierInsertOnly : ∀ op ∈ umemLog d t,
    op.addr.1 = UniversalMemory.Domain.nullifiers → op.kind = .write → op.val ≠ none
  umemTableFaithful : t.tf (.custom UMEM_TID) = (umemLog d t).map uopRow

/-- **ONE balance covers every domain — `universal_memory_sound` applied.** A `Satisfied2U`
witness's universal log is consistent, and EVERY domain's projection — stripped to a standalone
κ-addressed memory — is consistent from that domain's slice of the initial image. Registers,
heap, caps, nullifiers, index: one memory argument, zero intra-proof hashing. -/
theorem satisfied2U_umem_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UniversalMemory.UAddr ℤ → Option ℤ}
    {ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UniversalMemory.UAddr ℤ)} {t : VmTrace}
    (h : Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t) :
    MemoryChecking.Consistent uinit (umemLog d t) ∧
      ∀ dm : UniversalMemory.Domain,
        MemoryChecking.Consistent (fun a => uinit (dm, a))
          ((UniversalMemory.domTrace dm (umemLog d t)).map UniversalMemory.stripOp) :=
  UniversalMemory.universal_memory_sound
    h.umemAddrsNodup h.umemClosed h.umemDisciplined h.umemBalanced

/-- **The claimed final column is FORCED — `memcheck_pins_final` applied.** Every declared
universal address's final claim equals the genuine fold of the log: the boundary views are
derived from a forced column, not a chosen one. -/
theorem satisfied2U_pins_final (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UniversalMemory.UAddr ℤ → Option ℤ}
    {ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UniversalMemory.UAddr ℤ)} {t : VmTrace}
    (h : Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t) :
    ∀ a ∈ uaddrs, (ufin a).1 = ((umemLog d t).foldl MemoryChecking.step uinit) a :=
  UniversalMemory.memcheck_pins_final
    h.umemAddrsNodup h.umemClosed h.umemDisciplined h.umemBalanced

/-- **The map roots are DERIVED boundary views — `boundary_root_from_memcheck` applied.** For
any map domain `dm`: if today's committed map `hmap` has the lookup semantics of the genuine
post-state over the touched keys `as` (declared, sorted), then today's root EQUALS the
sorted-Poseidon2 root of the boundary view derived from the prover's claimed final column —
because the claims are pinned. Materializing roots at the boundary is a refactor, not a
semantic change. -/
theorem satisfied2U_boundary_root (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (dm : UniversalMemory.Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UniversalMemory.UAddr ℤ → Option ℤ}
    {ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UniversalMemory.UAddr ℤ)} {t : VmTrace}
    {hmap : Heap.FeltHeap} {as : List ℤ}
    (h : Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t)
    (hs : Heap.SortedKeys hmap) (has : as.Pairwise (· < ·))
    (hda : ∀ a ∈ as, (dm, a) ∈ uaddrs)
    (hsem : ∀ a : ℤ, Heap.get hmap a
      = if a ∈ as then ((umemLog d t).foldl MemoryChecking.step uinit) (dm, a) else none) :
    Heap.root hash hmap
      = Heap.root hash (UniversalMemory.boundaryCells (fun a => (ufin (dm, a)).1) as) :=
  UniversalMemory.boundary_root_from_memcheck hash dm
    h.umemAddrsNodup h.umemClosed h.umemDisciplined h.umemBalanced hs has hda hsem

/-- **The INIT boundary is BOUND to committed pre-state — `boundary_init_root_derived` applied.**
The companion of `satisfied2U_boundary_root` for the *init* column: for any map domain `dm`, if
the committed PRE-state map `hpre` has the lookup semantics of the declared init image `uinit`
over the touched keys `as` (declared, sorted), then today's committed pre-state root EQUALS the
sorted-Poseidon2 root of the boundary view derived from `uinit`. This is what makes the universal
boundary's init column TRUSTWORTHY: pinning that derived root to the committed pre-state root (the
PI-v3 ride-along) forces the declared init image to be the committed pre-state — a tampered init
CANNOT keep the published root (`boundary_init_root_bound`, under `Poseidon2SpongeCR`). The init
side needs NO memcheck pinning: `uinit` is the given, not a prover-chosen final column. -/
theorem satisfied2U_init_root (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (dm : UniversalMemory.Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UniversalMemory.UAddr ℤ → Option ℤ}
    {ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UniversalMemory.UAddr ℤ)} {t : VmTrace}
    {hpre : Heap.FeltHeap} {as : List ℤ}
    (_h : Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t)
    (hs : Heap.SortedKeys hpre) (has : as.Pairwise (· < ·))
    (hsem : ∀ a : ℤ, Heap.get hpre a = if a ∈ as then uinit (dm, a) else none) :
    Heap.root hash hpre
      = Heap.root hash (UniversalMemory.boundaryCells (fun a => uinit (dm, a)) as) :=
  UniversalMemory.boundary_init_root_derived hash hs has hsem

/-- **THE WHOLE-IMAGE init binding at the IR — `boundary_whole_image_sem` applied (no extra
cells).** The no-extra-cells direction `satisfied2U_init_root` could not reach by per-cell
membership: if the committed pre-state root EQUALS the sorted-Poseidon2 fold of the ENTIRE
declared boundary image (`boundaryCells (uinit dm·) as`) — the obligation the in-circuit
whole-boundary root-fold discharges, riding the universal-map rotation — then under the named CR
floor the committed heap agrees with the declared init image at EVERY address: declared cells
open to their declared value AND every address OFF the declared list is ABSENT in the committed
pre-state. So a committed heap holding any cell the boundary never declared CANNOT keep the
published root; the boundary image is the WHOLE committed pre-state, not merely a subset. This is
the init-side whole-image companion of `satisfied2U_init_root`; it ASSUMES the fold-root pin
(`hpin`) rather than a per-cell `hsem`, which is exactly the in-circuit obligation that remains. -/
theorem satisfied2U_init_whole_image (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (d : EffectVmDescriptor2)
    (dm : UniversalMemory.Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UniversalMemory.UAddr ℤ → Option ℤ}
    {ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UniversalMemory.UAddr ℤ)} {t : VmTrace}
    {hpre : Heap.FeltHeap} {as : List ℤ}
    (_h : Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t)
    (has : as.Pairwise (· < ·))
    (hpin : Heap.root hash hpre
      = Heap.root hash (UniversalMemory.boundaryCells (fun a => uinit (dm, a)) as)) :
    ∀ a : ℤ, Heap.get hpre a = if a ∈ as then uinit (dm, a) else none :=
  UniversalMemory.boundary_whole_image_sem hash hCR has hpin

/-- **THE NULLIFIER WIN at the IR — `nullifier_fresh_sound` applied.** In a `Satisfied2U`
witness whose universal log splits around a guarded read returning `none` at
`(nullifiers, x)`, the read PROVES: `x` was absent from the proof's initial nullifier view,
and no earlier op in this proof inserted it. The insert-only side condition is the
denotation's own `umemNullifierInsertOnly` leg, restricted to the prefix. ONE memory-read row;
no Merkle path, no gap opening, no hashing intra-proof. -/
theorem satisfied2U_nullifier_fresh (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UniversalMemory.UAddr ℤ → Option ℤ}
    {ufin : UniversalMemory.UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UniversalMemory.UAddr ℤ)} {t : VmTrace}
    {pre post : List UMemTraceOp} {rop : UMemTraceOp} {x : ℤ}
    (h : Satisfied2U hash d minit mfin maddrs uinit ufin uaddrs t)
    (hsplit : umemLog d t = pre ++ rop :: post)
    (hread : rop.kind = .read)
    (haddr : rop.addr = (UniversalMemory.Domain.nullifiers, x))
    (hnone : rop.val = none) :
    uinit (UniversalMemory.Domain.nullifiers, x) = none ∧
      ∀ op ∈ pre, op.addr = (UniversalMemory.Domain.nullifiers, x) → op.kind ≠ .write := by
  have hio : UniversalMemory.InsertOnlyAt (UniversalMemory.Domain.nullifiers, x) pre := by
    intro op hop haddr' hk
    exact h.umemNullifierInsertOnly op
      (by rw [hsplit]; exact List.mem_append_left _ hop) (by rw [haddr']) hk
  have hcons : MemoryChecking.Consistent uinit (pre ++ rop :: post) := by
    rw [← hsplit]
    exact (satisfied2U_umem_sound hash d h).1
  exact UniversalMemory.nullifier_fresh_sound hcons hread haddr hnone hio

/-! ## §6c — `Satisfied2Custom`: the accumulator / recursive-proof-binding denotation (the Custom leg).

`Custom` (effect selector 8) dispatches a cell program whose domain constraints are proven
EXTERNALLY. The row binds to that external sub-proof via its `custom_proof_commitment` column. The
FOUR row-local kinds cannot fold in another STARK proof; this leg does — by NAMING the recursion
engine exactly as `Dregg2.Circuit.RecursiveAggregation` does (an opaque `Proof` carrier + a
`verify : Proof → Bool` + the in-circuit-verifier soundness as a realizable hypothesis), and
requiring the row's commitment to be the GENUINE public-input commitment of a VERIFYING sub-proof.

The shape MIRRORS the map-op story (`§4`): there, a row's `(root, key, value)` columns are an
EXISTENTIAL opening of a proven sorted heap, FUNCTIONAL under the named CR floor
(`opensTo_functional` — a forged value is excluded). Here, a row's `(commit, vk)` columns are an
EXISTENTIAL binding to a verifying sub-proof, FUNCTIONAL under the named engine soundness
(`proofBind_determined` — a forged commitment is excluded). The verification itself is the
recursion boundary the stack already carries (`recursive_sound`); the row constraint COMMITS to
it. -/

/-- **The recursion engine** (the §4-analog of `hash`): an opaque sub-proof carrier `Proof`, the
native verifier `verify`, the public-input COMMITMENT `piCommit` a proof exposes (the value the
Custom row's `custom_proof_commitment` must match — the leaf wrap's bound PI digest in
`circuit/src/joint_turn_recursive.rs`), and the program VK `vkOf` a proof attests (the
`custom_program_vk_hash` it was proven against). We treat all four as OPAQUE — the whole point is
the row never inspects a proof's internals; the binding is the public commitment alone. -/
structure ProofEngine where
  Proof    : Type
  verify   : Proof → Bool
  piCommit : Proof → ℤ
  vkOf     : Proof → ℤ

/-- `boundTo E commit vk` — some sub-proof VERIFIES under engine `E`, with public-input
commitment `commit` and program VK `vk`. The existential the Custom row's columns must witness
(the §4-analog of `opensTo`: "some heap behind root reads … "). -/
def ProofEngine.boundTo (E : ProofEngine) (commit vk : ℤ) : Prop :=
  ∃ p : E.Proof, E.verify p = true ∧ E.piCommit p = commit ∧ E.vkOf p = vk

/-- **The named engine soundness — `EngineBinding` (the realizable boundary).** The recursion
engine's in-circuit verifier is sound: the public-input commitment is COLLISION-FREE across
VERIFYING proofs — two verifying sub-proofs exposing the same `piCommit` agree on their program VK
(the wrap binds the program identity to the commitment digest). This is the EXACT shape of
`RecursiveAggregation.EngineSound.recursive_sound` / the leaf-verifier's soundness — the one FRI
obligation `DESIGN-recursion-aggregation-private-joint-turns.md` §H1 argues is bounded for
plonky3's single fixed verifier AIR. It is a hypothesis the keystones TAKE (a `structure` field,
never an axiom); §10c witnesses it non-vacuously BOTH ways. -/
structure EngineBinding (E : ProofEngine) : Prop where
  /-- The PI commitment determines the attested program VK across verifying proofs. -/
  commit_determines_vk : ∀ p q : E.Proof, E.verify p = true → E.verify q = true →
    E.piCommit p = E.piCommit q → E.vkOf p = E.vkOf q

/-- The row's `(commit, vk)` denotation: when the guard fires, the columns are a genuine binding
to a verifying sub-proof — the row COMMITS to the verification of the external proof. (The §4-analog
of `MapOp.holdsAt`.) -/
def ProofBind.boundAt (E : ProofEngine) (env : VmRowEnv) (m : ProofBind) : Prop :=
  m.guard.eval env.loc = 1 → E.boundTo (m.commit.eval env.loc) (m.vk.eval env.loc)

/-- The proof-binding ops a descriptor declares. -/
def proofBindsOf (d : EffectVmDescriptor2) : List ProofBind :=
  d.constraints.filterMap fun c => match c with | .proofBind m => some m | _ => none

/-- **The custom-binding denotation** — `Satisfied2` PLUS the accumulator leg: every declared
`proofBind` op binds its row's commitment/vk columns to a VERIFYING sub-proof of the named engine
`E` (the §6b-analog: `Satisfied2U` adds the universal-memory leg; this adds the recursion leg). -/
structure Satisfied2Custom (hash : List ℤ → ℤ) (E : ProofEngine) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop
    extends Satisfied2 hash d minit mfin maddrs t where
  proofBound : ∀ i < t.rows.length, ∀ m ∈ proofBindsOf d, m.boundAt E (envAt t i)

/-- **`proofBind_bound` — the Custom row IS bound to a verifying sub-proof.** On an active
proof-binding row of a `Satisfied2Custom` witness, there EXISTS a sub-proof that VERIFIES, whose
public-input commitment EQUALS the row's `custom_proof_commitment` column and whose program VK
equals the row's `custom_program_vk_hash` column. The row does not trust the commitment — it
commits to a verification of it. -/
theorem proofBind_bound (hash : List ℤ → ℤ) (E : ProofEngine) (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Custom hash E d minit mfin maddrs t)
    {m : ProofBind} (hm : m ∈ proofBindsOf d)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : m.guard.eval (envAt t i).loc = 1) :
    E.boundTo (m.commit.eval (envAt t i).loc) (m.vk.eval (envAt t i).loc) :=
  h.proofBound i hi m hm hactive

/-- **`proofBind_determined` — THE ANTI-GHOST (forged commitment REJECTS).** Under the named
engine binding, the program VK attested by a Custom row is DETERMINED by its commitment column: if
the row's `custom_proof_commitment` is the commitment of SOME verifying sub-proof, then ANY
verifying sub-proof exposing that same commitment attests the SAME program VK. A forged row that
claims a `custom_proof_commitment` no verifying sub-proof exposes makes `boundAt` FALSE — its
`Satisfied2Custom` cannot exist. (The recursion analog of `opensTo_functional`: the binding cannot
lie.) -/
theorem proofBind_determined (hash : List ℤ → ℤ) (E : ProofEngine) (hE : EngineBinding E)
    (d : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Custom hash E d minit mfin maddrs t)
    {m : ProofBind} (hm : m ∈ proofBindsOf d)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : m.guard.eval (envAt t i).loc = 1)
    (q : E.Proof) (hq : E.verify q = true)
    (hqc : E.piCommit q = m.commit.eval (envAt t i).loc) :
    E.vkOf q = m.vk.eval (envAt t i).loc := by
  obtain ⟨p, hp, hpc, hpv⟩ := proofBind_bound hash E d h hm i hi hactive
  have : E.vkOf q = E.vkOf p := hE.commit_determines_vk q p hq hp (by rw [hqc, hpc])
  rw [this, hpv]

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

/-- The chip ROW of an absorb (Phase B-GATE, 17-wide): `(arity, padded inputs, hash inputs ::
lanes)`. The output BLOCK is `hash ins :: lanes`, where `lanes` are the `CHIP_OUT_LANES - 1`
exposed permutation lanes 1..7 (genuine distinct felts the chip AIR binds; their VALUES are not
a function of `hash` alone, so they ride existentially in the table-soundness predicate). Lane 0
is the squeezed digest `hash ins` — the single felt every single-output site binds, UNCHANGED. -/
def chipRow (hash : List ℤ → ℤ) (ins : List ℤ) (lanes : List ℤ) : List ℤ :=
  (ins.length : ℤ) :: padTo CHIP_RATE ins ++ (hash ins :: lanes)

/-- The chip LOOKUP tuple of an absorb (Phase B-GATE, 17-wide): `(arity, padded input exprs,
digest column :: lane columns)`. `digestCol` is out0 (the bound digest, UNCHANGED meaning);
`laneCols` are the `CHIP_OUT_LANES - 1` columns carrying the exposed lanes 1..7 (witnessed = the
genuine permutation lanes, so the lookup matches the 17-wide chip row, then NOT constrained by
the single-output site denotation). -/
def chipLookupTuple (ins : List EmittedExpr) (digestCol : Nat) (laneCols : List Nat) :
    List EmittedExpr :=
  (.const (ins.length : ℤ)) :: padToE CHIP_RATE ins ++ (.var digestCol :: laneCols.map .var)

/-- A chip table is SOUND when every row is a genuine `(arity, padded inputs, hash inputs ::
lanes)` tuple of the permutation (the chip AIR's own faithfulness — the per-permutation
constraint family). The `lanes` ride existentially: their VALUES are the genuine permutation
lanes 1..7 (bound by the Rust chip AIR's `out[i] == lane[i]` equalities), but they are not a
function of `hash`, so the `hash`-parameterized soundness predicate quantifies over them. -/
def ChipTableSound (hash : List ℤ → ℤ) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ (ins lanes : List ℤ),
    ins.length ≤ CHIP_RATE ∧ lanes.length = CHIP_OUT_LANES - 1 ∧ r = chipRow hash ins lanes

/-- **THE LEVER (`chip_lookup_sound`).** Against a sound chip table, a chip lookup ENFORCES the
hash equation: the digest column (out0, the HEAD of the output block) carries the genuine hash of
the evaluated inputs. The arity tag + equal-length input padding make the input/output split
unique, so no padding confusion survives; the lanes 1..7 ride along (matched existentially) and
do NOT enter the single-output denotation — the commitment STAYS 1-felt (out0). -/
theorem chip_lookup_sound (hash : List ℤ → ℤ) (tbl : Table) (hSound : ChipTableSound hash tbl)
    (a : Assignment) (ins : List EmittedExpr) (digestCol : Nat) (laneCols : List Nat)
    (hlen : ins.length ≤ CHIP_RATE)
    (hmem : (chipLookupTuple ins digestCol laneCols).map (·.eval a) ∈ tbl) :
    a digestCol = hash (ins.map (·.eval a)) := by
  obtain ⟨ws, lanes, hwlen, _hlanes, hrow⟩ := hSound _ hmem
  have hev : (chipLookupTuple ins digestCol laneCols).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a))
          ++ (a digestCol :: laneCols.map a) := by
    simp [chipLookupTuple, List.map_cons, List.map_append, map_eval_padToE, EmittedExpr.eval,
      List.map_map, Function.comp_def]
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
  -- the output blocks are equal lists; their HEADS give the digest equation
  have hblock : a digestCol :: laneCols.map a = hash ws :: lanes := hpads.2
  have hd : a digestCol = hash ws := (List.cons.injEq _ _ _ _).mp hblock |>.1
  rw [hins]
  exact hd

/-! ### §7w — the WIDE chip lever: force ALL `W` squeezed permutation columns.

The legacy lever (`chip_lookup_sound`) forces ONE output column — the single squeezed felt that
`hash_many` exposes (`state[0]`). The light-client-faithful state commitment needs the chip to
expose a WIDE digest: the `W` genuinely-distinct squeezed felts of the real Poseidon2 permutation
(`hash_many_8` → `W = 8`; the chip AIR already constrains the FULL 16-lane permutation and merely
returns `state[0]`, so exposing `W` columns is "expose more of an already-constrained AIR").

`permOut : List ℤ → List ℤ` is the wide squeeze: `permOut ins` is the `W`-felt output of the
genuine permutation on the absorbed inputs. The wide row appends the WHOLE `permOut ins` block (not
a single felt). `chip_lookup_sound_N` proves a wide lookup forces EVERY one of the `W` digest
columns to its genuine permutation output — the exact widening the commitment binds through.

The proof MIRRORS the legacy structure: arity tag + equal-length padding ⇒ a unique row
decomposition (`padTo_inj` / `List.append_inj`); the only change is the tail is a `W`-felt block
read column-by-column instead of a single felt. No new crypto enters — `permOut` is a parameter,
exactly as `hash` is for the legacy lever; the crypto floor is the SAME `Poseidon2SpongeCR` at full
width, supplied downstream where the wide digest is bound. -/

/-- The WIDE chip ROW: `(arity, padded inputs, permOut inputs)`, where `permOut ins` is the full
`W`-felt squeezed output of the genuine permutation. (The legacy `chipRow hash` is the `W = 1`
instance with `permOut := fun xs => [hash xs]`.) -/
def chipRowN (permOut : List ℤ → List ℤ) (ins : List ℤ) : List ℤ :=
  (ins.length : ℤ) :: padTo CHIP_RATE ins ++ permOut ins

/-- The WIDE chip LOOKUP tuple: `(arity, padded input exprs, W digest columns)`. The `W` digest
columns are read as variables `digestCols.map (.var)`; the wide soundness forces each one. -/
def chipLookupTupleN (ins : List EmittedExpr) (digestCols : List Nat) : List EmittedExpr :=
  (.const (ins.length : ℤ)) :: padToE CHIP_RATE ins ++ digestCols.map .var

/-- A WIDE chip table is SOUND when every row is a genuine `(arity, padded inputs, W-felt output)`
tuple of the permutation — the chip AIR's faithfulness at full squeeze width. -/
def ChipTableSoundN (permOut : List ℤ → List ℤ) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ ins : List ℤ, ins.length ≤ CHIP_RATE ∧ r = chipRowN permOut ins

/-- **THE WIDE LEVER (`chip_lookup_sound_N`).** Against a sound WIDE chip table, a wide chip lookup
ENFORCES the FULL permutation output: the `W` digest columns carry the genuine `W`-felt squeezed
output of the evaluated inputs. The arity tag + equal-length input padding make the row
decomposition unique, so no padding confusion survives, and the whole `permOut`-block tail is
forced column-for-column — NOT just its head. The width-faithfulness floor (`permOut` is the REAL
wide squeeze) is the parameter, mirroring the legacy lever's `hash`. -/
theorem chip_lookup_sound_N (permOut : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permOut tbl)
    (a : Assignment) (ins : List EmittedExpr) (digestCols : List Nat)
    (hlen : ins.length ≤ CHIP_RATE)
    (hmem : (chipLookupTupleN ins digestCols).map (·.eval a) ∈ tbl) :
    digestCols.map a = permOut (ins.map (·.eval a)) := by
  obtain ⟨ws, hwlen, hrow⟩ := hSound _ hmem
  have hev : (chipLookupTupleN ins digestCols).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a)) ++ digestCols.map a := by
    simp [chipLookupTupleN, List.map_cons, List.map_append, map_eval_padToE, EmittedExpr.eval,
      List.map_map, Function.comp_def]
  rw [hev] at hrow
  unfold chipRowN at hrow
  injection hrow with hl htail
  -- arity tag ⇒ equal input lengths
  have hlens : (ins.map (·.eval a)).length = ws.length := by
    have hcast : (ins.length : ℤ) = (ws.length : ℤ) := hl
    have := Int.natCast_inj.mp hcast
    simpa [List.length_map] using this
  have hlenm : (ins.map (·.eval a)).length ≤ CHIP_RATE := by
    simpa [List.length_map] using hlen
  -- equal-length padded blocks ⇒ split the tail uniquely (inputs vs the W-felt output block)
  have hpads := List.append_inj htail
    (by rw [padTo_length hlenm, padTo_length hwlen])
  have hins : ins.map (·.eval a) = ws := padTo_inj hlens hpads.1
  -- the output block: `digestCols.map a = permOut ws`, then rewrite ws ↦ evaluated inputs
  have hd : digestCols.map a = permOut ws := hpads.2
  rw [hins]
  exact hd

/-- **The legacy lever IS the head of the wide instance.** The deployed `chipRow hash`/
`chip_lookup_sound` (Phase B-GATE) are themselves 17-wide: the output block is `hash ins ::
lanes`, and `chip_lookup_sound` forces its HEAD (out0). The `permOut`-parametric wide lever
(`chip_lookup_sound_N`) is the general statement that ALSO forces lanes 1..7 — used when the
8-felt commitment binds the whole block (Phase B-ROTATION). The two agree on out0: a wide row
whose `permOut` has head `hash` carries `chipRow hash ins (permOut ins).tail` in its tail, so the
single-output binding is exactly `chip_lookup_sound`'s conclusion. (Phase B-GATE keeps the
commitment 1-felt — only out0 is bound — so the deployed soundness rides `chip_lookup_sound`.) -/
theorem chipRowN_head_eq_hash (permOut : List ℤ → List ℤ) (ins : List ℤ) (out0 : ℤ)
    (lanes : List ℤ) (hsplit : permOut ins = out0 :: lanes) :
    chipRowN permOut ins = chipRow (fun _ => out0) ins lanes := by
  unfold chipRowN chipRow
  rw [hsplit]

/-! ### Translating a v1 hash site to a chip lookup. -/

instance : Inhabited VmHashSite := ⟨⟨0, [], 0⟩⟩

/-- Translate a hash-site input to a column expression. A `digest k` reference reads the EARLIER
site's RESULT COLUMN (every site binds its digest to a named column — `siteHoldsAll`'s invariant),
so the cross-site dataflow survives the move into lookup form. -/
def HashInput.toExpr (sites : List VmHashSite) : HashInput → EmittedExpr
  | .col c    => .var c
  | .digest k => .var ((sites.getD k default).digestCol)
  | .zero     => .const 0

/-- The 7 lane columns (`CHIP_OUT_LANES - 1`) carrying a site's exposed permutation lanes 1..7.
Phase B-GATE allocates them as a contiguous block at `[base, base+1, …, base+6]` — `graduateV1`
threads `base = traceWidth + 7·i` for the `i`-th site, appending the lane block past the v1 trace
width. (The values are the genuine permutation lanes, filled by the Rust producer; lane0 stays
the chained `digestCol`.) -/
def siteLaneCols (base : Nat) : List Nat :=
  (List.range (CHIP_OUT_LANES - 1)).map (base + ·)

/-- The chip lookup replacing site `s` of the ordered family `sites`. Phase B-GATE: the 17-wide
tuple `[arity, padded inputs, digestCol :: laneCols base]`. `digestCol` is out0 (the bound
digest, UNCHANGED meaning); the 7 lane columns at `base..base+6` carry the exposed lanes 1..7
(matched to the chip row, NOT constrained by the single-output denotation). -/
def siteLookup (sites : List VmHashSite) (s : VmHashSite) (base : Nat) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTuple (s.inputs.map (HashInput.toExpr sites)) s.digestCol (siteLaneCols base) }

/-- **The site-to-lookup replacement is SOUND.** If the earlier sites' digest columns carry the
resolved digests (the `siteHoldsAll` invariant, hypothesis `hdig`) and the chip table is sound,
then the translated lookup enforces EXACTLY the site equation `loc digestCol = hash (resolved
inputs)` — the v1 in-row Poseidon2 constraint, at lookup cost. -/
theorem siteLookup_replaces_site (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (env : VmRowEnv)
    (sites : List VmHashSite) (s : VmHashSite) (base : Nat) (digs : List ℤ)
    (hdig : ∀ k, env.loc ((sites.getD k default).digestCol) = digs.getD k 0)
    (hlen : s.inputs.length ≤ CHIP_RATE)
    (hmem : (siteLookup sites s base).tuple.map (·.eval env.loc) ∈ tbl) :
    env.loc s.digestCol = hash (s.resolvedInputs env digs) := by
  have h := chip_lookup_sound hash tbl hSound env.loc
    (s.inputs.map (HashInput.toExpr sites)) s.digestCol (siteLaneCols base)
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
  ",\"rate\":" ++ toString CHIP_SPONGE_RATE ++
  ",\"rc_source\":\"BABYBEAR_POSEIDON2_RC_16\"" ++
  ",\"internal_diag_source\":\"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16\"}"

/-- The row-semantics wire tag. -/
def RowSemantics.tag : RowSemantics → String
  | .mainRow         => "main"
  | .permutation     => "poseidon2_chip"
  | .rangeLimb _     => "range"
  | .memAccess       => "memory"
  | .mapReconcile    => "map_ops"
  | .umemAccess      => "umemory"
  | .umemBoundaryRow => "umem_boundary"

/-- The universal memory table: one row per universal state access
(`[domain, key, present, value, prev_present, prev_value, prev_serial, kind]` = `uopRow`). -/
def umemTableDef : TableDef := ⟨.custom UMEM_TID, "umemory", 8, .umemAccess⟩

/-- The universal boundary table: one row per declared `(domain, key)` address
(`[domain, key, init_present, init_value, fin_present, fin_value, fin_serial]`). -/
def umemBoundaryTableDef : TableDef := ⟨.custom 2, "umem_boundary", 7, .umemBoundaryRow⟩

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
  | .read => "read" | .write => "write" | .absent => "absent" | .insert => "insert"

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

/-- Render one universal-memory op (the domain-tagged `Option`-valued instrumented row). -/
def UMemOp.toJson (m : UMemOp) : String :=
  "{\"t\":\"umem_op\",\"kind\":\"" ++ kindTag m.kind ++
  "\",\"domain\":" ++ toString (domainCode m.domain) ++
  ",\"guard\":" ++ m.guard.toJson ++ ",\"key\":" ++ m.key.toJson ++
  ",\"present\":" ++ m.present.toJson ++ ",\"value\":" ++ m.value.toJson ++
  ",\"prev_present\":" ++ m.prevPresent.toJson ++
  ",\"prev_value\":" ++ m.prevValue.toJson ++
  ",\"prev_serial\":" ++ m.prevSerial.toJson ++ "}"

/-- Render one proof-binding op (the accumulator / recursive-proof binding: the row's
`custom_proof_commitment` + `custom_program_vk_hash` columns, gated). -/
def ProofBind.toJson (m : ProofBind) : String :=
  "{\"t\":\"proof_bind\",\"guard\":" ++ m.guard.toJson ++
  ",\"commit\":" ++ m.commit.toJson ++ ",\"vk\":" ++ m.vk.toJson ++ "}"

/-- Render one v2 constraint (the v1 forms reuse the v1 renderer byte-for-byte). -/
def VmConstraint2.toJson : VmConstraint2 → String
  | .base c       => c.toJson
  | .lookup l     => l.toJson
  | .memOp m      => m.toJson
  | .mapOp m      => m.toJson
  | .umemOp m     => m.toJson
  | .proofBind m  => m.toJson
  | .windowGate w => w.toJson

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
  "{\"name\":\"demo-v2\",\"ir\":2,\"trace_width\":2,\"public_input_count\":1,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":2,\"sem\":\"main\"},{\"id\":1,\"name\":\"poseidon2_chip\",\"arity\":25,\"sem\":\"poseidon2_chip\",\"params\":{\"field_modulus\":2013265921,\"d\":4,\"width\":16,\"sbox_degree\":7,\"sbox_registers\":1,\"half_full_rounds\":4,\"partial_rounds\":13,\"rate\":8,\"rc_source\":\"BABYBEAR_POSEIDON2_RC_16\",\"internal_diag_source\":\"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16\"}},{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30},{\"id\":3,\"name\":\"memory\",\"arity\":5,\"sem\":\"memory\"},{\"id\":4,\"name\":\"map_ops\",\"arity\":5,\"sem\":\"map_ops\"}],\"constraints\":[{\"t\":\"transition\",\"hi\":0,\"lo\":0},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"mem_op\",\"kind\":\"read\",\"guard\":{\"t\":\"const\",\"v\":1},\"addr\":{\"t\":\"var\",\"v\":0},\"value\":{\"t\":\"var\",\"v\":1},\"prev_value\":{\"t\":\"var\",\"v\":1},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"map_op\",\"op\":\"write\",\"guard\":{\"t\":\"const\",\"v\":1},\"root\":{\"t\":\"var\",\"v\":0},\"key\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"const\",\"v\":0},\"new_root\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}"

-- The chip's INPUT-LANE COUNT is 16 (Phase H3 widened it 11 → 16 = full width for the node8 L8‖R8
-- Merkle compression); the sponge rate stays the REAL babyBearD4W16 base rate (8). The chip row is
-- 25 wide: `1 (arity) + 16 (inputs) + 8 (output lanes)`.
#guard CHIP_RATE == 16
#guard CHIP_SPONGE_RATE == 8
#guard CHIP_OUT_LANES == 8
#guard poseidon2ChipTableDef.arity == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard poseidon2ChipTableDef.arity == 25
#guard (chipRow (fun _ => 0) [1, 2] [0, 0, 0, 0, 0, 0, 0]).length == CHIP_RATE + 1 + CHIP_OUT_LANES
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
#guard (chipRow (fun _ => 99) [1] [0, 0, 0, 0, 0, 0, 0]).head? == some 1
#guard (chipRow (fun _ => 99) [1, 0] [0, 0, 0, 0, 0, 0, 0]).head? == some 2

/-! ### §10w — the WIDE chip lever: faithful at full squeeze width + the ANTI-LAUNDERING tooth. -/

-- The wide `chipRowN` (output BLOCK = the whole `permOut ins`) at W=8 IS the deployed 17-wide
-- shape: head = out0 (the bound digest), tail = the 7 carried lanes. The deployed `chipRow`'s
-- output block `hash ins :: lanes` is exactly `chipRowN`'s block split at the head.
#guard chipRowN (fun _ => [10, 11, 12, 13, 14, 15, 16, 17]) [1, 2]
  == chipRow (fun _ => 10) [1, 2] [11, 12, 13, 14, 15, 16, 17]
#guard (chipRowN (fun _ => [10, 11, 12, 13, 14, 15, 16, 17]) [1, 2]).length == 1 + CHIP_RATE + 8
#guard (chipRow (fun _ => 10) [1, 2] [11, 12, 13, 14, 15, 16, 17]).length == 1 + CHIP_RATE + CHIP_OUT_LANES
-- the wide tuple carries W=8 distinct digest columns (here cols 40..47), not one.
#guard (chipLookupTupleN [.var 0, .var 1] [40, 41, 42, 43, 44, 45, 46, 47]).length == 1 + CHIP_RATE + 8

-- THE ANTI-LAUNDERING `#guard`: a laundered "wide" digest would be `[h]×8` (eight copies of one
-- felt) or a stub — its squeeze would NOT depend on the full input past felt 0. Two inputs that
-- agree on `output[0]` but differ on a HIGH output felt (the light-client near-collision shape) are
-- DISTINGUISHED by the wide row's output block, while a 1-felt digest's forced value (`head`)
-- coincides. Here `pA`/`pB` model two cell-states' genuine wide squeezes: equal head, different tail.
private def pA : List ℤ → List ℤ := fun _ => [7, 100, 200, 300, 400, 500, 600, 700]
private def pB : List ℤ → List ℤ := fun _ => [7, 100, 200, 300, 400, 500, 600, 999]  -- ← only felt 7 differs

-- 1-felt (legacy) lever sees only `output[0]` = 7 for BOTH → cannot distinguish (the 31-bit hole):
#guard (pA [1, 2]).head? == (pB [1, 2]).head?
-- 8-felt (wide) lever forces the WHOLE block → the rows DIFFER (the near-collision is caught):
#guard ¬ (chipRowN pA [1, 2] == chipRowN pB [1, 2])
#guard (chipRowN pA [1, 2]).drop (1 + CHIP_RATE) == [7, 100, 200, 300, 400, 500, 600, 700]
#guard (chipRowN pB [1, 2]).drop (1 + CHIP_RATE) == [7, 100, 200, 300, 400, 500, 600, 999]

/-- **The anti-laundering THEOREM (the wide output is genuinely wider than 1 felt).** Whenever two
genuine wide squeezes agree on `output[0]` but differ somewhere in the full `W`-felt block, then
SIMULTANEOUSLY: (1) the legacy 1-felt lever is BLIND — the single forced felt (`output[0]`) is the
SAME for both, so the narrow lever cannot tell the cell-states apart (the 31-bit collision a light
client suffers); and (2) the WIDE rows DIFFER — the wide lever forces the whole block, catching the
near-collision. So the widening is load-bearing, not `[output[0]]×W` and not a stub: it
distinguishes EXACTLY where the narrow lever fails. (The light-client collision-distinguishing bite
— the reason 8 felts replaces 1.) -/
theorem chipRowN_distinguishes_wide
    {permA permB : List ℤ → List ℤ} {ins : List ℤ}
    (hhead : (permA ins).head? = (permB ins).head?)   -- legacy lever is blind: same `output[0]`
    (hfull : permA ins ≠ permB ins) :                  -- but the full squeeze differs
    -- (1) the legacy single-felt digest (`output[0]`) coincides (the narrow lever is blind), AND
    -- (2) the WIDE chip rows DIFFER (the wide lever catches the near-collision).
    (permA ins).head? = (permB ins).head? ∧ chipRowN permA ins ≠ chipRowN permB ins := by
  refine ⟨hhead, ?_⟩
  intro hrow
  unfold chipRowN at hrow
  injection hrow with _ htail
  exact hfull (List.append_cancel_left htail)

-- The embedded-v1 face is inert: no mem ops, no map ops.
#guard (memOpsOf (embedV1 { name := "n", traceWidth := 1, piCount := 0, constraints := [.transition 0 0], hashSites := [], ranges := [] })).length == 0

/-! ### §10b — the UNIVERSAL-memory demo: wire golden + non-vacuity + the keystone fired.

`demoU` exercises the `umemOp` kind across TWO domains in ONE table: a nullifier insert, a
nullifier FRESHNESS read (present = 0 — `none`, no Merkle path), and a register write. The
trace, boundary and `Satisfied2U` witness are constructed CONCRETELY below, and
`satisfied2U_nullifier_fresh` fires on them end-to-end — nothing vacuous in the pipeline. -/

/-- The umem demo descriptor: nullifier insert (key `col 0`) · nullifier freshness read
(key `col 1`) · register write (key `col 2`, value `col 3`). -/
def demoU : EffectVmDescriptor2 :=
  { name := "demo-umem", traceWidth := 4, piCount := 0
  , tables := [mainTableDef 4, umemTableDef, umemBoundaryTableDef]
  , constraints :=
      [ .umemOp ⟨.const 1, .nullifiers, .var 0, .const 1, .const 1,
                 .const 0, .const 0, .const 0, .write⟩
      , .umemOp ⟨.const 1, .nullifiers, .var 1, .const 0, .const 0,
                 .const 0, .const 0, .const 0, .read⟩
      , .umemOp ⟨.const 1, .registers, .var 2, .const 1, .var 3,
                 .const 0, .const 0, .const 0, .write⟩ ]
  , hashSites := [], ranges := [] }

-- THE UMEM WIRE GOLDEN: the canonical JSON of the umem grammar, byte-pinned (the Rust
-- `descriptor_ir2.rs` decoder's `umem_op` arm + `umemory`/`umem_boundary` table sems parse
-- THIS string's grammar; mirrored as `DEMO_UMEM` in its tests).
#guard emitVmJson2 demoU ==
  "{\"name\":\"demo-umem\",\"ir\":2,\"trace_width\":4,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":4,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":3,\"guard\":{\"t\":\"const\",\"v\":1},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"const\",\"v\":1},\"value\":{\"t\":\"const\",\"v\":1},\"prev_present\":{\"t\":\"const\",\"v\":0},\"prev_value\":{\"t\":\"const\",\"v\":0},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"umem_op\",\"kind\":\"read\",\"domain\":3,\"guard\":{\"t\":\"const\",\"v\":1},\"key\":{\"t\":\"var\",\"v\":1},\"present\":{\"t\":\"const\",\"v\":0},\"value\":{\"t\":\"const\",\"v\":0},\"prev_present\":{\"t\":\"const\",\"v\":0},\"prev_value\":{\"t\":\"const\",\"v\":0},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":0,\"guard\":{\"t\":\"const\",\"v\":1},\"key\":{\"t\":\"var\",\"v\":2},\"present\":{\"t\":\"const\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":3},\"prev_present\":{\"t\":\"const\",\"v\":0},\"prev_value\":{\"t\":\"const\",\"v\":0},\"prev_serial\":{\"t\":\"const\",\"v\":0}}],\"hash_sites\":[],\"ranges\":[]}"

-- The new table ids stay collision-free with the five EPOCH ids + the submask table (5).
#guard ([TableId.main, .poseidon2, .range, .memory, .mapOps, .custom 0,
         .custom UMEM_TID, .custom 2].map TableId.wireId).dedup.length == 8

-- The Option cell encoding round-trips, both polarities.
#guard optOf (presentBit (some (42 : ℤ))) (payloadOf (some 42)) == some 42
#guard optOf (presentBit (none : Option ℤ)) (payloadOf (none : Option ℤ)) == none
#guard optOf 0 0 == (none : Option ℤ)
#guard optOf 1 0 == some (0 : ℤ)

/-- The demo main row: nullifier 7 inserted, nullifier 9 freshness-checked, register 0 ← 42. -/
def demoURow : Assignment := fun i =>
  if i = 0 then 7 else if i = 1 then 9 else if i = 2 then 0 else if i = 3 then 42 else 0

/-- The demo multi-table witness: one main row; the umem table carries exactly the gathered
log's rows; every other table empty. -/
def demoUTrace : VmTrace :=
  { rows := [demoURow], pub := zeroAsg
  , tf := fun tid => match tid with
      | .custom 1 => [[3, 7, 1, 1, 0, 0, 0, 1], [3, 9, 0, 0, 0, 0, 0, 0],
                      [0, 0, 1, 42, 0, 0, 0, 1]]
      | _ => [] }

/-- The demo universal boundary: everything starts absent/unset. -/
def uinitU : UniversalMemory.UAddr ℤ → Option ℤ := fun _ => none

/-- The demo final claims (value, last-touch serial). -/
def ufinU : UniversalMemory.UAddr ℤ → Option ℤ × Nat := fun a =>
  if a = (UniversalMemory.Domain.nullifiers, 7) then (some 1, 1)
  else if a = (UniversalMemory.Domain.nullifiers, 9) then (none, 2)
  else if a = (UniversalMemory.Domain.registers, 0) then (some 42, 3)
  else (none, 0)

/-- The demo declared universal addresses. -/
def uaddrsU : List (UniversalMemory.UAddr ℤ) :=
  [(.nullifiers, 7), (.nullifiers, 9), (.registers, 0)]

-- The gathered umem log balances (ONE check), is disciplined, and is consistent — and its
-- nullifier projection too (the executable shadow of the keystones, AT the IR).
#guard decide (MemoryChecking.Disciplined (umemLog demoU demoUTrace))
#guard decide (MemoryChecking.MemCheck uinitU ufinU uaddrsU (umemLog demoU demoUTrace))
#guard decide (MemoryChecking.Consistent uinitU (umemLog demoU demoUTrace))
#guard decide (MemoryChecking.Consistent (fun a => uinitU (.nullifiers, a))
  ((UniversalMemory.domTrace .nullifiers (umemLog demoU demoUTrace)).map
    UniversalMemory.stripOp))

-- NEGATIVE polarity at the IR: re-keying the freshness read onto the INSERTED nullifier
-- (col 1 ↦ 7) is the intra-proof double spend — the gathered log is INCONSISTENT, and no
-- final claim can balance it (`UniversalMemory.lean` §6 carries the balance refusals).
def demoURowDouble : Assignment := fun i =>
  if i = 0 then 7 else if i = 1 then 7 else if i = 2 then 0 else if i = 3 then 42 else 0
#guard decide (¬ MemoryChecking.Consistent uinitU
  (umemLog demoU { demoUTrace with rows := [demoURowDouble] }))

/-- The demo `Satisfied2U` witness, fully constructed — every leg discharged concretely (the
row constraints are the global-content kinds; the multiset legs are `decide`-level facts). -/
theorem demoU_satisfied :
    Satisfied2U (fun _ => 0) demoU (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      uinitU ufinU uaddrsU demoUTrace := by
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints: every constraint is an `umemOp` (global content ⇒ row-locally True)
    intro i hi c hc
    simp only [demoU, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> trivial
  · -- rowHashes: no hash sites
    intro i hi
    trivial
  · -- rowRanges: no ranges
    intro i hi r hr
    simp [demoU] at hr
  · -- memClosed: the flat memory log is empty
    intro op hop
    rw [show memLog demoU demoUTrace = [] from rfl] at hop
    cases hop
  · -- memDisciplined
    rw [show memLog demoU demoUTrace = [] from rfl]
    exact by decide
  · -- memBalanced
    rw [show memLog demoU demoUTrace = [] from rfl]
    exact memCheck_nil _ _
  · -- memTableFaithful
    rfl
  · -- mapTableFaithful
    rfl
  · -- umemAddrsNodup
    exact by decide
  · -- umemClosed
    exact by decide
  · -- umemDisciplined
    exact by decide
  · -- umemBalanced
    exact by decide
  · -- umemNullifierInsertOnly
    exact by decide
  · -- umemTableFaithful
    rfl

-- THE NULLIFIER KEYSTONE, fired end-to-end on the demo witness: the freshness read (log
-- position 2) PROVES nullifier 9 absent from the initial view AND never inserted in the
-- prefix — one memory row, no Merkle path, every hypothesis concrete.
example :
    uinitU (UniversalMemory.Domain.nullifiers, 9) = none ∧
      ∀ op ∈ ([⟨.write, (.nullifiers, 7), some 1, none, 0⟩] : List UMemTraceOp),
        op.addr = (UniversalMemory.Domain.nullifiers, 9) → op.kind ≠ .write :=
  satisfied2U_nullifier_fresh (fun _ => 0) demoU demoU_satisfied
    (pre := [⟨.write, (.nullifiers, 7), some 1, none, 0⟩])
    (post := [⟨.write, (.registers, 0), some 42, none, 0⟩])
    (rop := ⟨.read, (.nullifiers, 9), none, none, 0⟩)
    rfl rfl rfl rfl

/-! ### §10c — the PROOF-BINDING (Custom accumulator) demo: wire golden + non-vacuity + the
keystone fired BOTH ways.

`demoC` exercises the `proofBind` kind: one Custom row binding `custom_proof_commitment` (col 0) +
`custom_program_vk_hash` (col 1) to a verifying sub-proof. The realizing engine is a TOY
(`Bool`-carriered) recursion engine: a verifying proof exposes a FIXED commitment/vk, so the
`Satisfied2Custom` witness is constructed CONCRETELY and `proofBind_determined` fires end-to-end
(forged-commitment rejection witnessed). -/

/-- The proof-binding demo descriptor: one Custom row binding (commit = col 0, vk = col 1), gated
by the (toy) custom selector at col 2. -/
def demoC : EffectVmDescriptor2 :=
  { name := "demo-custom", traceWidth := 3, piCount := 0
  , tables := [mainTableDef 3]
  , constraints := [ .proofBind ⟨.var 2, .var 0, .var 1⟩ ]
  , hashSites := [], ranges := [] }

-- THE PROOF-BIND WIRE GOLDEN: the canonical JSON of the `proof_bind` grammar, byte-pinned (the
-- Rust `descriptor_ir2.rs` decoder's `proof_bind` arm parses THIS string's grammar; mirrored as
-- `DEMO_CUSTOM` in its tests).
#guard emitVmJson2 demoC ==
  "{\"name\":\"demo-custom\",\"ir\":2,\"trace_width\":3,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":3,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"proof_bind\",\"guard\":{\"t\":\"var\",\"v\":2},\"commit\":{\"t\":\"var\",\"v\":0},\"vk\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}"

/-- A TOY recursion engine: the proof carrier is `Bool` (`true` = the one honest sub-proof), the
verifier accepts exactly `true`, and a verifying proof exposes commitment `123` / vk `45`. (The
realizing instance only needs the structure + the binding implication; the REAL engine is
plonky3's leaf verifier, named not modeled.) -/
def demoEngine : ProofEngine :=
  { Proof := Bool, verify := fun b => b, piCommit := fun _ => 123, vkOf := fun _ => 45 }

-- The toy engine satisfies the named `EngineBinding` (its commitment trivially determines its vk).
theorem demoEngine_binding : EngineBinding demoEngine :=
  { commit_determines_vk := fun _ _ _ _ _ => rfl }

/-- The proof-binding demo row: commit 123 (col 0), vk 45 (col 1), selector ON (col 2). -/
def demoCRow : Assignment := fun i =>
  if i = 0 then 123 else if i = 1 then 45 else if i = 2 then 1 else 0

/-- The demo custom witness: one main row; no auxiliary tables (proof binding rides the named
engine, not a committed table). -/
def demoCTrace : VmTrace := { rows := [demoCRow], pub := zeroAsg, tf := fun _ => [] }

/-- The demo `Satisfied2Custom` witness, fully constructed: the row constraint is global-content
(row-locally `True`); the proof-binding leg supplies the honest sub-proof (`true`). -/
theorem demoC_satisfied :
    Satisfied2Custom (fun _ => 0) demoEngine demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      demoCTrace := by
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi c hc
    simp only [demoC, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; trivial
  · intro i hi; trivial
  · intro i hi r hr; simp [demoC] at hr
  · intro op hop; rw [show memLog demoC demoCTrace = [] from rfl] at hop; cases hop
  · rw [show memLog demoC demoCTrace = [] from rfl]; exact by decide
  · rw [show memLog demoC demoCTrace = [] from rfl]; exact memCheck_nil _ _
  · rfl
  · rfl
  · -- proofBound: the one declared proofBind op binds to the honest `true` sub-proof.
    intro i hi m hm hactive
    have hm' : m = ⟨.var 2, .var 0, .var 1⟩ := by
      simpa [proofBindsOf, demoC] using hm
    subst hm'
    -- row 0 is the only row; commit col evaluates to 123, vk col to 45.
    have hlen : demoCTrace.rows.length = 1 := rfl
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨true, rfl, rfl, rfl⟩

-- THE ANTI-GHOST FIRED end-to-end on the demo: a forged sub-proof claiming the row's commitment
-- (123) attests EXACTLY the row's vk (45) — a forgery exposing a DIFFERENT vk cannot verify at
-- that commitment (the determinism the named `EngineBinding` supplies, AT the IR).
example (q : Bool) (hq : demoEngine.verify q = true)
    (hqc : demoEngine.piCommit q = (EmittedExpr.var 0).eval (envAt demoCTrace 0).loc) :
    demoEngine.vkOf q = (EmittedExpr.var 1).eval (envAt demoCTrace 0).loc :=
  proofBind_determined (fun _ => 0) demoEngine demoEngine_binding demoC demoC_satisfied
    (m := ⟨.var 2, .var 0, .var 1⟩) (by simp [proofBindsOf, demoC])
    0 (by decide) (by decide) q hq hqc

-- NON-VACUITY of `EngineBinding`, BOTH polarities: the toy engine satisfies it (above), and a
-- BROKEN engine that exposes the SAME commitment for vk 45 and vk 99 across verifying proofs
-- FAILS it (the hypothesis has content — it is not `True`).
def brokenEngine : ProofEngine :=
  { Proof := Bool, verify := fun _ => true, piCommit := fun _ => 7
  , vkOf := fun b => if b then 45 else 99 }
#guard ¬ decide (brokenEngine.vkOf true = brokenEngine.vkOf false)

#assert_axioms TableId.wireId_injective
#assert_axioms domainCode_injective
-- §7 chip lever (the deployed 17-wide single-output head lever + the §7w WIDE generalization):
#assert_axioms chip_lookup_sound
#assert_axioms chip_lookup_sound_N
#assert_axioms chipRowN_head_eq_hash
#assert_axioms chipRowN_distinguishes_wide
#assert_axioms optOf_roundtrip
#assert_axioms satisfied2U_umem_sound
#assert_axioms satisfied2U_pins_final
#assert_axioms satisfied2U_boundary_root
#assert_axioms satisfied2U_init_root
#assert_axioms satisfied2U_init_whole_image
#assert_axioms satisfied2U_nullifier_fresh
#assert_axioms demoU_satisfied
#assert_axioms proofBind_bound
#assert_axioms proofBind_determined
#assert_axioms demoEngine_binding
#assert_axioms demoC_satisfied
#assert_axioms opensTo_functional
#assert_axioms opensTo_some_excludes_none
#assert_axioms writesTo_functional
#assert_axioms opensTo_none_of_gap
#assert_axioms satisfied2_mem_consistent
#assert_axioms satisfied2_init_root
#assert_axioms satisfied2_fin_root
#assert_axioms satisfied2_init_root_bound
#assert_axioms satisfied2_init_whole_image
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
