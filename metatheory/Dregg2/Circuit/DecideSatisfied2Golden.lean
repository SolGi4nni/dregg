/-
# Dregg2.Circuit.DecideSatisfied2Golden — THE KERNEL-CHECKED GOLDEN CORPUS that wires the Rust
exhaustive structural enumerator (`circuit/tests/ir2_denotational_differential.rs`) to the
kernel-proven decider `DecideSatisfied2.decideSatisfied2` (whose `decideSatisfied2_iff_Satisfied2`
is `= true ↔ Satisfied2`).

## What this closes (the bridge seam)

The Rust enumerator runs TWO oracles on a shared corpus: `eval_enforces` (a transcription of the
deployed `Ir2Air::eval`) and `denote_satisfied2` (a transcription of the Lean `Satisfied2`
denotation). Its Lean side was a HAND-TRANSCRIPTION — faithful, but a parallel re-implementation
that could itself drift from the kernel object. This module makes that transcription a
PROVEN-EQUAL mirror of the kernel decider: it constructs the SAME structural corpus the Rust
generator covers (every constraint arm × the row-position boundary × both polarities × every forge
path), runs the kernel-proven `decideSatisfied2` over each case with a finite-table `mapDec` oracle
that mirrors the Rust `Openings`, and `#guard`s every verdict. The Rust test
`pinned_against_decideSatisfied2_goldens` builds the identical literal corpus + asserts its
`denote_satisfied2` decides the SAME verdict, case-for-case. So:

  * a drift in the kernel decider flips a `#guard` here (red `lake build`);
  * a drift in the Rust transcription flips the Rust assertion (red `cargo test`);
  * the shared anchor is the explicit literal corpus + the verdict each `#guard` PROVES.

## The map-op leg (the SAME finite oracle on both sides)

`decideSatisfied2` takes `mapDec : VmRowEnv → MapOp → Bool` — the supplied openings oracle. Here it
is a finite-table membership check (`mapDecOf`) over the SAME `(root,key,value,newRoot)` openings the
Rust case carries; the Rust `denote_satisfied2`'s `mapOp` arm does the identical finite-set check. So
both sides decide the map leg by the SAME oracle, exactly as the differential supplies it. The
`holdsAt`-faithfulness of that oracle (oracle ⟺ a real depth-16 heap opening) is the SEPARATELY-named
heap-opening floor of `DecideSatisfied2.lean` (`hmapDec`) — not re-litigated per case; what this
golden pins is the DECIDER VERDICT on the supplied oracle.

## Axiom hygiene

Pure `#guard` (kernel reduction); no `sorry`, no `native_decide`. NEW file; imports read-only.
-/
import Dregg2.Circuit.DecideSatisfied2

namespace Dregg2.Circuit.DecideSatisfied2Golden

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv STATE_BEFORE_BASE STATE_AFTER_BASE)
open Dregg2.Circuit.DecideSatisfied2

set_option autoImplicit false

/-! ## §1 — case carriers (the Lean twins of the Rust generator's case shape).

A `Case` bundles the descriptor, the multi-table witness, the supplied map openings (as finite
tables), the memory boundary (as finite `minit`/`mfin`/`maddrs`), and the verdict the kernel decider
returns. Every field is constructed by explicit literals so the corpus is the SHARED anchor with the
Rust mirror. -/

/-- A row = an `Assignment` built from an explicit prefix list (off-the-end = 0). Mirrors the Rust
`Row` (a `Vec<i128>`, default 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

/-- A `TraceFamily` built from explicit per-id tables (every other id empty). Mirrors the Rust
`VmTraceC.tf` HashMap. -/
def tfOf (range memory mapOps : Table) (capId : Nat) (cap : Table) : TraceFamily := fun id =>
  match id with
  | .range    => range
  | .memory   => memory
  | .mapOps   => mapOps
  | .custom n => if n == capId then cap else []
  | _         => []

/-- A finite map-openings oracle: `mapDec env m = true` iff the evaluated `(root,key,value,newRoot)`
of `m` is supported by the supplied finite opening tables, per the op kind — the EXACT shape the Rust
`Openings` (members / absents / writes) carries, decided identically.

  * `.read`   ⇒ `(root,key,value) ∈ members ∧ newRoot = root`
  * `.absent` ⇒ `(root,key) ∈ absents ∧ newRoot = root`
  * `.write`/`.insert` ⇒ `(root,key,value,newRoot) ∈ writes`

Guard off ⇒ vacuously `true` (the `holdsAt` antecedent is `guard = 1`). -/
def mapDecOf
    (members : List (ℤ × ℤ × ℤ)) (absents : List (ℤ × ℤ)) (writes : List (ℤ × ℤ × ℤ × ℤ)) :
    VmRowEnv → MapOp → Bool := fun env m =>
  if m.guard.eval env.loc == 1 then
    let r := m.root.eval env.loc
    let k := m.key.eval env.loc
    let v := m.value.eval env.loc
    let nr := m.newRoot.eval env.loc
    match m.op with
    | .read           => members.contains (r, k, v) && nr == r
    | .absent         => absents.contains (r, k) && nr == r
    | .write | .insert => writes.contains (r, k, v, nr)
  else
    true

/-- The trivial oracle: no openings (for cases with no map ops). -/
def noOpen : VmRowEnv → MapOp → Bool := mapDecOf [] [] []

/-- The abstract hash never enters a verdict here (no hash site / no `holdsAt` inversion — the map
leg rides the supplied oracle), so any concrete value serves. -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- Build a descriptor with only constraints (the differential exercises no hash sites / ranges /
declared tables — the table family carries content directly). -/
def descOf (cs : List VmConstraint2) : EffectVmDescriptor2 :=
  { name := "dregg-decide-sat2-golden", traceWidth := 90, piCount := 0,
    tables := [], constraints := cs, hashSites := [], ranges := [] }

/-- Run the kernel decider on a fully-explicit case. -/
def verdict
    (cs : List VmConstraint2) (rows : List (List ℤ))
    (range memory mapOps : Table) (capId : Nat) (cap : Table)
    (members : List (ℤ × ℤ × ℤ)) (absents : List (ℤ × ℤ)) (writes : List (ℤ × ℤ × ℤ × ℤ))
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) : Bool :=
  decideSatisfied2 (mapDecOf members absents writes) hash0 (descOf cs)
    minit mfin maddrs
    { rows := rows.map rowOf, pub := zeroAsg, tf := tfOf range memory mapOps capId cap }

/-! ## §2 — constraint constructors (mirroring the Rust `Constraint` arms). -/

open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-- `var i`. -/ def ev (i : Nat) : EmittedExpr := .var i
/-- `const c`. -/ def ec (c : ℤ) : EmittedExpr := .const c
/-- `a + b`. -/ def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
/-- `-1 * e` (the Rust `neg`). -/ def eneg (e : EmittedExpr) : EmittedExpr := .mul (.const (-1)) e
/-- `a - b`. -/ def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)

/-- A `.base (.gate body)` constraint. -/
def cGate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)
/-- A `.base (.transition hi lo)` constraint. -/
def cTrans (hi lo : Nat) : VmConstraint2 := .base (.transition hi lo)
/-- A `.lookup` into a table. -/
def cLookup (table : TableId) (tuple : List EmittedExpr) : VmConstraint2 := .lookup ⟨table, tuple⟩

/-- A window-expr constructors (mirroring the Rust `WinExpr`). -/
def wloc (c : Nat) : WindowExpr := .loc c
def wnxt (c : Nat) : WindowExpr := .nxt c
def wconst (k : ℤ) : WindowExpr := .const k
def wadd (a b : WindowExpr) : WindowExpr := .add a b
def wmul (a b : WindowExpr) : WindowExpr := .mul a b

/-- A `.windowGate`. -/
def cWindow (body : WindowExpr) (onTransition : Bool) : VmConstraint2 :=
  .windowGate ⟨body, onTransition⟩

/-- The `[0, 2^bits)` range rows (Lean `rangeRows`, Rust `range_rows`). -/
def rngRows (bits : Nat) : Table := (List.range (2 ^ bits)).map (fun n => [(n : ℤ)])

/-! ## §3 — THE GOLDEN CORPUS.

Each `#guard` is one case from the Rust enumerator's structural axes, with the verdict the kernel
decider returns. The Rust test `pinned_against_decideSatisfied2_goldens` mirrors the SAME literals
and asserts `denote_satisfied2` returns the SAME verdict. Both the accept (true) and reject (false)
polarity of every arm is pinned. Column offsets: `STATE_BEFORE_BASE = 54`, `STATE_AFTER_BASE = 76`. -/

-- The base column offsets the transition arm addresses (54 / 76), pinned (the Rust mirror uses the
-- same literals; this `#guard` catches any drift in either system's state-block layout).
#guard STATE_BEFORE_BASE == 54
#guard STATE_AFTER_BASE == 76

/-- A 90-wide row with `state_after[0] = state_before[0] = 42` and cols 0,1 set — the gate+transition
satisfying shape. -/
def gtRow (c0 c1 : ℤ) : List ℤ :=
  (List.range 90).map (fun i =>
    if i == 0 then c0 else if i == 1 then c1
    else if i == STATE_AFTER_BASE then 42 else if i == STATE_BEFORE_BASE then 42 else 0)

/-! ### gate + transition (the v1 forms, on the transition domain). -/

-- gate body = col0 - col1 ; transition ties state_after[0] of a row to state_before[0] of the next.
def gtCs : List VmConstraint2 := [cGate (esub (ev 0) (ev 1)), cTrans 0 0]

-- ACCEPT: 2 rows, col0==col1 on both, continuity holds.
#guard verdict gtCs [gtRow 7 7, gtRow 7 7] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT (gate forge): col1 ≠ col0 on row 0 (a transition row).
#guard verdict gtCs [gtRow 7 8, gtRow 7 7] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == false
-- REJECT (transition forge): next.before[0] = 43 ≠ local.after[0] = 42.
#guard verdict gtCs
    [gtRow 7 7, (gtRow 7 7).set STATE_BEFORE_BASE 43] [] [] [] 0 [] [] [] []
    (fun _ => 0) (fun _ => (0,0)) []
  == false
-- ACCEPT on a 1-ROW trace even with a broken gate (the wrap row, `when_transition` skips it).
#guard verdict gtCs [gtRow 5 6] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == true

/-! ### lookup into the range table `[0, 2^4)`. -/

def lrCs : List VmConstraint2 := [cLookup .range [ev 0]]

-- ACCEPT: col0 = 9 ∈ [0,16) on every row (heights 1, 2, 3).
#guard verdict lrCs [[9]] (rngRows 4) [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) [] == true
#guard verdict lrCs [[9],[9]] (rngRows 4) [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == true
#guard verdict lrCs [[9],[9],[9]] (rngRows 4) [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT: col0 = 16 ∉ [0,16) on some row.
#guard verdict lrCs [[9],[16],[9]] (rngRows 4) [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == false

/-! ### lookup into a generic committed cap-family table (TableId.custom 4 = wire id 9). -/

-- cap leaf face [7, key, digest]; capId 4 ⇒ wire id 9 (matches the Rust TID_CAP = 9).
def lgCs : List VmConstraint2 := [cLookup (.custom 4) [ec 7, ev 0, ev 1]]
def capTbl : Table := [[7, 11, 22], [7, 12, 23]]

-- ACCEPT: row [11, 22] = a committed leaf.
#guard verdict lgCs [[11, 22]] [] [] [] 4 capTbl [] [] [] (fun _ => 0) (fun _ => (0,0)) [] == true
-- REJECT: digest forged (22 + 1234), not a committed leaf.
#guard verdict lgCs [[11, 1256]] [] [] [] 4 capTbl [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == false

/-! ### a transfer-shaped memOp pair (write then read at the same address). -/

-- addr=col0, write value=col1 over (prev=col2, serial=col3); read value=col4 over (prev=col5,
-- serial=col6). A range lookup on col0 guards the address. The mem op fields are
-- guard, addr, value, prevValue, prevSerial, kind.
def memCs' : List VmConstraint2 :=
  [ cLookup .range [ev 0],
    .memOp ⟨ec 1, ev 0, ev 1, ev 2, ev 3, .write⟩,
    .memOp ⟨ec 1, ev 0, ev 4, ev 5, ev 6, .read⟩ ]

-- addr 5, init 7, write 9 over (7,0), read 9 over (9,1) ⇒ final (9, 2).
-- row = [addr, written, init, 0, read_val, read_prev, read_serial] = [5,9,7,0,9,9,1].
-- memLog = [⟨write,5,9,7,0⟩, ⟨read,5,9,9,1⟩]; opRow = [addr,val,prevVal,prevSerial,kind].
def memTable : Table := [[5, 9, 7, 0, 1], [5, 9, 9, 1, 0]]
def memRow : List ℤ := [5, 9, 7, 0, 9, 9, 1]
def memMinit : ℤ → ℤ := fun a => if a == 5 then 7 else 0
def memMfin : ℤ → ℤ × Nat := fun a => if a == 5 then (9, 2) else (0, 0)

-- ACCEPT.
#guard verdict memCs' [memRow] (rngRows 4) memTable [] 0 [] [] [] []
    memMinit memMfin [5]
  == true
-- REJECT (mem balance): claim final value 99 the log doesn't produce.
#guard verdict memCs' [memRow] (rngRows 4) memTable [] 0 [] [] [] []
    memMinit (fun a => if a == 5 then (99, 2) else (0,0)) [5]
  == false
-- REJECT (mem discipline): read value 8 ≠ prev_value 9 (row col4 = 8), with the faithful table.
#guard verdict memCs' [[5, 9, 7, 0, 8, 9, 1]] (rngRows 4) [[5, 9, 7, 0, 1], [5, 8, 9, 1, 0]] [] 0 []
    [] [] [] memMinit memMfin [5]
  == false
-- REJECT (mem table unfaithful): drop the sent rows (empty memory table ≠ the log).
#guard verdict memCs' [memRow] (rngRows 4) [] [] 0 [] [] [] []
    memMinit memMfin [5]
  == false

/-! ### map-op WRITE (cell-seal shape). -/

def mwCs : List VmConstraint2 := [.mapOp ⟨ec 1, ev 0, ev 1, ev 2, ev 3, .write⟩]
-- row [root,key,value,new_root] = [100,7,42,200]; mapLog row = [root,key,value,op,new_root].
def mwRow : List ℤ := [100, 7, 42, 200]
def mwTable : Table := [[100, 7, 42, 1, 200]]

-- ACCEPT: the opening (100,7,42,200) ∈ writes.
#guard verdict mwCs [mwRow] [] [] mwTable 0 [] [] [] [(100, 7, 42, 200)]
    (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT (forged opening): new_root 201, no writesTo supports it (table follows the row).
#guard verdict mwCs [[100, 7, 42, 201]] [] [] [[100, 7, 42, 1, 201]] 0 [] [] [] [(100, 7, 42, 200)]
    (fun _ => 0) (fun _ => (0,0)) []
  == false
-- REJECT (map table unfaithful): drop the sent map row.
#guard verdict mwCs [mwRow] [] [] [] 0 [] [] [] [(100, 7, 42, 200)]
    (fun _ => 0) (fun _ => (0,0)) []
  == false

/-! ### map-op READ (membership, root preserved). -/

def mrCs : List VmConstraint2 := [.mapOp ⟨ec 1, ev 0, ev 1, ev 2, ev 3, .read⟩]
def mrRow : List ℤ := [100, 7, 42, 100]  -- new_root == root
def mrTable : Table := [[100, 7, 42, 0, 100]]

-- ACCEPT: (100,7,42) ∈ members ∧ new_root = root.
#guard verdict mrCs [mrRow] [] [] mrTable 0 [] [(100, 7, 42)] [] []
    (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT (forged read value): value 43, no member supports it.
#guard verdict mrCs [[100, 7, 43, 100]] [] [] [[100, 7, 43, 0, 100]] 0 [] [(100, 7, 42)] [] []
    (fun _ => 0) (fun _ => (0,0)) []
  == false

/-! ### map-op ABSENT (non-membership, root preserved). -/

def maCs : List VmConstraint2 := [.mapOp ⟨ec 1, ev 0, ev 1, ec 0, ev 3, .absent⟩]
def maRow : List ℤ := [100, 9, 0, 100]  -- key 9 absent under root 100
def maTable : Table := [[100, 9, 0, 2, 100]]

-- ACCEPT: (100,9) ∈ absents ∧ new_root = root.
#guard verdict maCs [maRow] [] [] maTable 0 [] [] [(100, 9)] []
    (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT (key not absent): claim key 7 absent, not supported.
#guard verdict maCs [[100, 7, 0, 100]] [] [] [[100, 7, 0, 2, 100]] 0 [] [] [(100, 9)] []
    (fun _ => 0) (fun _ => (0,0)) []
  == false

/-! ### windowGate on the TRANSITION (cumulative sum: next cum = local cum + next contribution). -/

-- body = Nxt(1) - Loc(1) - Nxt(0).
def wtBody : WindowExpr := wadd (wadd (wnxt 1) (wmul (wconst (-1)) (wloc 1))) (wmul (wconst (-1)) (wnxt 0))
def wtCs : List VmConstraint2 := [cWindow wtBody true]

-- ACCEPT: rows [contrib, cum]; cum0 = 5; row1 contrib 3 ⇒ cum1 = 8; row2 contrib 4 ⇒ cum2 = 12.
#guard verdict wtCs [[0, 5], [3, 8], [4, 12]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT: break a transition step (cum1 off by one).
#guard verdict wtCs [[0, 5], [3, 9], [4, 13]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == false
-- ACCEPT on a 1-ROW trace (the only row is the wrap row; `onTransition` skips it).
#guard verdict wtCs [[0, 5]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) [] == true

/-! ### windowGate on EVERY row (incl. the wrap row): body = Loc(0) - Loc(1). -/

def weBody : WindowExpr := wadd (wloc 0) (wmul (wconst (-1)) (wloc 1))
def weCs : List VmConstraint2 := [cWindow weBody false]

-- ACCEPT: col0 == col1 on every row (heights 1, 2, 3).
#guard verdict weCs [[5, 5]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) [] == true
#guard verdict weCs [[5, 5], [5, 5]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) [] == true
#guard verdict weCs [[5, 5], [5, 5], [5, 5]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == true
-- REJECT: break the equality on the LAST row — the every-row gate binds there.
#guard verdict weCs [[5, 5], [5, 5], [5, 6]] [] [] [] 0 [] [] [] [] (fun _ => 0) (fun _ => (0,0)) []
  == false

end Dregg2.Circuit.DecideSatisfied2Golden
