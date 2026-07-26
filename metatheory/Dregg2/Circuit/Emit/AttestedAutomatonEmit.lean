/-

⚠⚠⚠ FELT-WIDTH WOUND AT THE ATTESTATION BOUNDARY — an adversarial verify caught this and the file's
own prose claimed the opposite. READ BEFORE CITING `root_binds_automaton`.

`attTransitionOpen` sets `root := fun _ => .var ROOT` and `newRoot := fun _ => .var ROOT` —
definitionally `EffectVmEmitRotationV3.scalarRootGroup ROOT`, whose own IR doc says: "A
not-yet-8-felt-welded root … the root stays ~31-bit until that family's own weld" (contrast
`beforeCapRootGroup`/`beforeHeapRootGroup`, which carry the real 8 lanes plus an after-spine keystone).
The DEPLOYED map-log tuple is 19 felts `[root8, key, value, op, new_root8]`
(circuit/src/descriptor_ir2.rs:2165-2185); this descriptor feeds ONE column into all eight lanes.

CONSEQUENCE, stated at full resolution: `root_binds_automaton` / `attested_refines_committed` /
`forged_edge_refused` consume `Poseidon2SpongeCR hash` for `hash : List ℤ → ℤ` — an UNBOUNDED codomain,
where the hypothesis is reasonable. The DEPLOYED instantiation has a BabyBear codomain,
p = 2013265921 ≈ 2^31, where CR is simply FALSE: a birthday search finds `d'` with
`autoRoot hash d' = autoRoot hash d` in ~2^15.5 work. So "the root determines the machine" holds
against the MODELLED hash and NOT against the deployed one. The attestation is real as a construction
and as a Lean theorem; it is NOT yet a deployed security property.

THE FIX IS THE SAME ONE THE FELT-WIDTH CAMPAIGN NAMES: weld the root to 8 felts (mirror
`beforeCapRootGroup`/`beforeHeapRootGroup` — the real lanes plus the after-spine keystone) so the
committed digest carries ~124 bits rather than ~31. Until then every theorem here that consumes
`Poseidon2SpongeCR` is conditional on a hypothesis the deployment refutes.

(Unaffected: `attWit_satisfies` / `prodAttWit_satisfies` — the WITNESS legs take NO crypto hypothesis,
because the opening is CONSTRUCTED (`autoHeap`/`autoRoot`/`autoRoot_commits` build a genuine 2^16-leaf
sorted heap). The satisfiability and cost results stand; only the BINDING claim is width-wounded.)
# Dregg2.Circuit.Emit.AttestedAutomatonEmit — CLOSING THE ATTESTATION GAP of the run-table
discipline: the run's edges are bound to a COMMITTED automaton by an OPENING, not by declaring
the automaton's edges.

**This is Lean-authored AIR.** The descriptor is an `EffectVmDescriptor2` authored here; the
witness is a concrete `VmTrace`; satisfaction and soundness are theorems over the EMITTED object.
Rust parses the emitted IR2 bytes and supplies witnesses; it authors nothing.

## The gap this file closes

`TinyAutomataSatisfiable.lean` proves `prodRunWit_satisfies`: a real `Satisfied2Public` witness for
a COMPOSED descriptor at area `3·|w|`, flat in `k`. Its stated, unrepaired price (§7, last
paragraph):

> a run table commits the edges TRAVERSED, not the automaton, so "which product automaton ran"
> must be bound elsewhere.

The whole-graph declaration WOULD bind it, at area 12/36/72/150 (reachability-minimised, `k = 1…4`)
and with NO witness in hand — `exact_lookup_perm` + `forced_trace_length` force the run to be an
EULERIAN path through every declared edge. That route is both expensive AND unsatisfiable.

## What is built here instead

The automaton rides as ONE FELT — a `mapRoot` commitment of its whole transition function — and
each step is a MAP-OP READ against that root:

  * `attestedDesc` declares NO table rows at all. Its wire bytes are CONSTANT in `|w|` and in
    `|Q|·|Σ|`: 4 columns, 3 PIs, 6 constraints, 2 range teeth, ZERO declared rows.
  * `CommitsAutomaton hash R d` says the root `R` opens, at every in-domain key `2s + y`, to
    `d.step s y`. `autoRoot_commits` CONSTRUCTS such a root for any `d` (§1), so the predicate is
    inhabited, not a wish.
  * `attWit_satisfies` (§3) is a real `Satisfied2Public` witness — GENERAL in the automaton, the
    start state and the (non-empty, in-alphabet) word.
  * `root_binds_automaton` (§4) is the ATTESTATION: under CR, two automata committed by the SAME
    root AGREE on the whole declared key domain. The root determines the machine.
  * `attested_refines_committed` (§5) is the soundness leg: a satisfying trace's every row is a
    genuine step of the COMMITTED automaton, and the exposed public `final_state` IS
    `classifyFrom d q₀` of the word the trace reads.
  * §6 lands it on the `k`-fold PRODUCT of the independent family — the same composed object
    `TinyAutomataSatisfiable` measured, now ATTESTED.

## The honest price, measured in §7

Attestation is NOT free, and the free axis is not the one the IR cost counters see:

  * `costOf` axes: `4` columns (vs `3`), `6` constraints (vs `4`), `3` PIs (vs `2`), `0` declared
    rows (vs `|w|`), `0` nonlinear mults (same). Main-trace area `4·|w|` vs `3·|w|`.
  * The map-ops table carries `|w|` rows of arity 5 — the aux trace the run-table route does not pay.
  * ⚠ AND THE COST THE IR DOES NOT COUNT: the IR denotation of a map-op read is an EXISTENTIAL
    opening (`opensTo`); the DEPLOYED AIR realizes it as a depth-`MAP_TREE_DEPTH = 16` binary-Merkle
    path, i.e. 16 `mapNode` permutations per opened row — `16·|w|` chip rows. That is the real bill,
    it is stated here rather than hidden, and it is INDEPENDENT of `|Q|·|Σ|`.

So: attestation costs `+1` main column, `+2` constraints, `5·|w|` map-op rows and `16·|w|` chip
rows; it buys a bound automaton WITH A WITNESS, at a descriptor that is ONE object for every
automaton and every word length (1190 bytes, measured). In wire bytes it is LARGER than the
run-table descriptor for short words and SMALLER from `|w| = 61` on — the crossover is measured at
`|w| = 60`, not claimed. The whole-graph alternative costs `O(|Q|·|Σ|)` declared rows, grows with
the automaton, and has NO witness at any `k`.

## Residuals (named, not laundered)

  * **The CR floor.** `root_binds_automaton` and `attested_refines_committed` consume
    `Poseidon2SpongeCR hash` — the standing named collision-resistance hypothesis of every sibling
    map-opening theorem. The witness (§3) needs NO crypto hypothesis.
  * **Field canonicality.** The root column is pinned to `pi[root]` on the FIRST row and threaded by
    a constancy window; both are field CONGRUENCES, so collapsing them to ℤ equality needs the
    standing canonical-representative discipline (`hcanonRoot` / `hRcanon`: cells in `[0, p)`), the
    same hypothesis shape `tableRouting_refines_classify` carries as `hq0`/`hfN`. A root is a felt,
    so it CANNOT be range-collapsed instead without truncating a digest — that would be the
    felt-width sin, and it is refused here.
  * **Key domain.** The declared domain is `s < 2^15`, `y < 2` (key `= 2s + y < 2^16` = the deployed
    map's leaf count). The range teeth `⟨CURRENT, 15⟩`, `⟨SYMBOL, 1⟩` enforce it on every row.
  * The `Satisfied2Public` model-vs-deployed-field status is the standing one shared by every
    sibling refinement; a STARK proves the TRACE, and the FRI floor is undischarged.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem (§8). NEW file; imports
read-only. Every `#guard` is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`; it pins
measured numbers and nothing more.
-/
import Dregg2.Circuit.Emit.TinyAutomataSatisfiable

namespace Dregg2.Circuit.Emit.AttestedAutomatonEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv VmRange holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Substrate
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom lastNext_eq_classifyFrom symbols)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT PI_INITIAL PI_FINAL contWindowBody ofNat_eq_of_modEq cont_eq mkRowN
   traceRowsN continuous_of_chain envAt_loc envAt_nxt tableRoutingDesc)
open Dregg2.Circuit.Emit.TinyAutomataCompose
open Dregg2.Circuit.Emit.TinyAutomataSatisfiable

set_option autoImplicit false

/-! ## §1 — THE COMMITMENT INSTRUMENT: an automaton committed by ONE felt.

The deployed map (`DescriptorIR2.opensTo` = `MapMerkleRoot.opensToMerkle` at depth
`MAP_TREE_DEPTH = 16`) is a sorted `2^16`-leaf heap behind a binary-Merkle root. We commit an
automaton's WHOLE transition function into one: key `2s + y ↦ d.step s y`, TOTAL over the
`2^16`-key domain. Nothing here is ever evaluated — the root stays abstract in `hash`. -/

/-- The alphabet bound the descriptor's `SYMBOL` range tooth enforces (`Σ = {0, 1}`). -/
def ASYM : Nat := 2

/-- The state bound the descriptor's `CURRENT` range tooth enforces (`2^15`), chosen so every key
`2s + y` lands strictly inside the deployed map's `2^16` leaves. -/
def ASTATES : Nat := 32768

/-- The committed map's key of the edge `(s, y)`. -/
def keyOf (s y : Nat) : Nat := 2 * s + y

/-- The number of keys the committed map carries: the deployed leaf count `2 ^ MAP_TREE_DEPTH`. -/
def NKEYS : Nat := 65536

/-- `kvRows g n b` — the `n` consecutive entries `(b, g b), (b+1, g (b+1)), …`, keys cast to felts.
The canonical strictly-key-increasing block the sorted-heap discipline wants. -/
def kvRows (g : Nat → ℤ) : Nat → Nat → Heap.FeltHeap
  | 0,     _ => []
  | n + 1, b => ((b : ℤ), g b) :: kvRows g n (b + 1)

theorem kvRows_length (g : Nat → ℤ) : ∀ (n b : Nat), (kvRows g n b).length = n
  | 0,     _ => rfl
  | n + 1, b => by
    show (kvRows g n (b + 1)).length + 1 = n + 1
    rw [kvRows_length g n (b + 1)]

/-- Every key of a block is one of the block's naturals. -/
theorem kvRows_key_mem (g : Nat → ℤ) :
    ∀ (n b : Nat) (x : ℤ), x ∈ Heap.keys (kvRows g n b) → ∃ i : Nat, b ≤ i ∧ x = (i : ℤ)
  | 0,     _, _, hx => absurd hx (by simp [kvRows, Heap.keys])
  | n + 1, b, x, hx => by
    rw [show kvRows g (n + 1) b = ((b : ℤ), g b) :: kvRows g n (b + 1) from rfl,
      Heap.keys_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨b, Nat.le_refl b, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := kvRows_key_mem g n (b + 1) x hx
      exact ⟨i, by omega, rfl⟩

/-- A block's keys are STRICTLY increasing — the heap invariant, by construction. -/
theorem kvRows_sorted (g : Nat → ℤ) : ∀ (n b : Nat), Heap.SortedKeys (kvRows g n b)
  | 0,     _ => by simp [kvRows, Heap.SortedKeys, Heap.keys]
  | n + 1, b => by
    rw [show kvRows g (n + 1) b = ((b : ℤ), g b) :: kvRows g n (b + 1) from rfl,
      Heap.SortedKeys, Heap.keys_cons, List.pairwise_cons]
    refine ⟨?_, kvRows_sorted g n (b + 1)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := kvRows_key_mem g n (b + 1) x hx
    exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hi

/-- A block READS its generator at every key it covers. -/
theorem kvRows_get (g : Nat → ℤ) :
    ∀ (n b k : Nat), b ≤ k → k < b + n → Heap.get (kvRows g n b) (k : ℤ) = some (g k)
  | 0,     b, k, h1, h2 => by omega
  | n + 1, b, k, h1, h2 => by
    rw [show kvRows g (n + 1) b = ((b : ℤ), g b) :: kvRows g n (b + 1) from rfl]
    by_cases hb : k = b
    · subst hb
      simp [Heap.get]
    · have hne : ((k : ℤ)) ≠ ((b : ℤ)) := by exact_mod_cast hb
      show (if ((k : ℤ)) = ((b : ℤ)) then some (g b) else Heap.get (kvRows g n (b + 1)) (k : ℤ))
        = some (g k)
      rw [if_neg hne]
      exact kvRows_get g n (b + 1) k (by omega) (by omega)

/-- **The committed automaton heap**: key `j ↦ d.step (j / 2) (j % 2)`, TOTAL over the deployed
`2 ^ MAP_TREE_DEPTH` leaves. Every edge of `d` inside the declared domain is present. -/
def autoHeap (d : TableDfa Nat Nat) : Heap.FeltHeap :=
  kvRows (fun j => ((d.step (j / 2) (j % 2) : Nat) : ℤ)) NKEYS 0

theorem autoHeap_length (d : TableDfa Nat Nat) : (autoHeap d).length = 2 ^ MAP_TREE_DEPTH := by
  rw [autoHeap, kvRows_length]
  rfl

theorem autoHeap_sorted (d : TableDfa Nat Nat) : Heap.SortedKeys (autoHeap d) :=
  kvRows_sorted _ _ _

/-- **The automaton's commitment — ONE FELT.** The deployed binary-Merkle root of the committed
heap; abstract in `hash`, never evaluated. -/
def autoRoot (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) : ℤ :=
  MapMerkleRoot.mapRoot hash MAP_TREE_DEPTH (autoHeap d)

/-- **`CommitsAutomaton hash R d`** — the root `R` COMMITS the automaton `d`: at every declared key
`2s + y` it opens to `d.step s y`. This is the whole attestation content, and it is ONE felt wide:
no edge is declared anywhere in the descriptor. -/
def CommitsAutomaton (hash : List ℤ → ℤ) (R : ℤ) (d : TableDfa Nat Nat) : Prop :=
  ∀ s y : Nat, s < ASTATES → y < ASYM →
    opensTo hash R ((keyOf s y : Nat) : ℤ) (some ((d.step s y : Nat) : ℤ))

/-- ⚑ **The predicate is INHABITED for every automaton** — `autoRoot` is a commitment of `d`.
(This is what keeps §4/§5 from being a hypothesis about an empty set.) -/
theorem autoRoot_commits (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) :
    CommitsAutomaton hash (autoRoot hash d) d := by
  intro s y hs hy
  refine ⟨autoHeap d, autoHeap_sorted d, autoHeap_length d, rfl, ?_⟩
  have hk : keyOf s y < 0 + NKEYS := by
    have h1 : s < 32768 := by simpa [ASTATES] using hs
    have h2 : y < 2 := by simpa [ASYM] using hy
    show keyOf s y < 0 + 65536
    unfold keyOf
    omega
  have hget := kvRows_get (fun j => ((d.step (j / 2) (j % 2) : Nat) : ℤ)) NKEYS 0 (keyOf s y)
    (Nat.zero_le _) hk
  rw [autoHeap, hget]
  have hy2 : y < 2 := by simpa [ASYM] using hy
  have hdiv : keyOf s y / 2 = s := by unfold keyOf; omega
  have hmod : keyOf s y % 2 = y := by unfold keyOf; omega
  show some ((d.step (keyOf s y / 2) (keyOf s y % 2) : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ)
  rw [hdiv, hmod]

/- ⚑ THE OPAQUENESS BARRIER. Past this point `autoRoot`/`autoHeap` are IRREDUCIBLE: no
elaboration step may unfold a root into its `2^16`-leaf heap (it cannot terminate in any useful
time, and nothing below needs it). Everything after §1 treats a commitment as one opaque felt —
which is also exactly how the verifier sees it. -/
attribute [irreducible] autoHeap autoRoot

/-! ## §2 — THE EMITTED DESCRIPTOR: 4 columns, 6 constraints, ZERO declared rows.

`CURRENT`/`SYMBOL`/`NEXT` are the same columns `DfaRoutingTableEmit` uses (0/1/2), so the model
reading (`mkRowN`, `traceRowsN`) and the continuity body (`contWindowBody`) are reused verbatim.
Column 3 carries the automaton's ROOT; `pi[2]` exposes it. -/

/-- `automaton_root` — the committed automaton's root, carried per row. -/
def ROOT : Nat := 3
/-- Total main-trace width. -/
def AW_WIDTH : Nat := 4

/-- pi[2] `automaton_root` (pi[0] `initial_state`, pi[1] `final_state` are inherited). -/
def PI_ROOT : Nat := 2
/-- Number of public inputs. -/
def AW_PI_COUNT : Nat := 3

/-- **THE ATTESTATION TOOTH**: the row's `(current, symbol) → next` is an OPENING of the committed
map at key `2·current + symbol` under the row's root. No edge is declared; the automaton is bound
by its root. -/
def attTransitionOpen : VmConstraint2 :=
  .mapOp { guard   := .const 1
         , root    := fun _ => .var ROOT
         , key     := .add (.mul (.const 2) (.var CURRENT)) (.var SYMBOL)
         , value   := .var NEXT
         , newRoot := fun _ => .var ROOT
         , op      := .read }

/-- C2 continuity (the same body `DfaRoutingTableEmit` emits): `Nxt(current) − Loc(next)`. -/
def attContinuity : VmConstraint2 := .windowGate ⟨contWindowBody, true⟩

/-- C3 root constancy: `Nxt(root) − Loc(root)` — one automaton for the whole run. -/
def attRootBody : WindowExpr := .add (.nxt ROOT) (.mul (.const (-1)) (.loc ROOT))

/-- The root-constancy window. -/
def attRootConst : VmConstraint2 := .windowGate ⟨attRootBody, true⟩

/-- B1: first row `current_state == pi[initial_state]`. -/
def attB1 : VmConstraint2 := .base (.piBinding VmRow.first CURRENT PI_INITIAL)
/-- B2: last row `next_state == pi[final_state]` (the classification). -/
def attB2 : VmConstraint2 := .base (.piBinding VmRow.last NEXT PI_FINAL)
/-- B3: first row `automaton_root == pi[automaton_root]` (the attestation's public face). -/
def attB3 : VmConstraint2 := .base (.piBinding VmRow.first ROOT PI_ROOT)

/-- **`attestedDesc name`** — the ATTESTED DFA-routing descriptor. Declares the map-ops table (the
deployed opening chip) and NO table rows whatsoever: its wire bytes are constant in `|w|` and in
`|Q|·|Σ|`. The range teeth pin the key domain (`current < 2^15`, `symbol < 2`). -/
def attestedDesc (name : String) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := AW_WIDTH
  , piCount     := AW_PI_COUNT
  , tables      := [mapOpsTableDef]
  , constraints := [attTransitionOpen, attContinuity, attRootConst, attB1, attB2, attB3]
  , hashSites   := []
  , ranges      := [⟨CURRENT, 15⟩, ⟨SYMBOL, 1⟩] }

/-- The canonical pinned instance name — ONE descriptor for EVERY automaton and EVERY word length
(the automaton rides in `pi[2]`, the word length is free). -/
def ATT_NAME : String := "dregg-attested-automaton::map-committed-v1"

/-- The pinned instance. -/
def attestedInstance : EffectVmDescriptor2 := attestedDesc ATT_NAME

theorem attOpen_mem (name : String) : attTransitionOpen ∈ (attestedDesc name).constraints :=
  List.mem_cons_self
theorem attCont_mem (name : String) : attContinuity ∈ (attestedDesc name).constraints :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem attRootConst_mem (name : String) : attRootConst ∈ (attestedDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem attB1_mem (name : String) : attB1 ∈ (attestedDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem attB2_mem (name : String) : attB2 ∈ (attestedDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
theorem attB3_mem (name : String) : attB3 ∈ (attestedDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- The descriptor declares no memory ops … -/
theorem att_memOps (name : String) : memOpsOf (attestedDesc name) = [] := rfl
theorem att_memLog (name : String) (t : VmTrace) : memLog (attestedDesc name) t = [] := by
  simp [memLog, att_memOps]

/-- … exactly one map op … -/
theorem att_mapOps (name : String) :
    mapOpsOf (attestedDesc name)
      = [{ guard   := .const 1
         , root    := fun _ => .var ROOT
         , key     := .add (.mul (.const 2) (.var CURRENT)) (.var SYMBOL)
         , value   := .var NEXT
         , newRoot := fun _ => .var ROOT
         , op      := .read }] := rfl

/-- The map-ops row a trace row contributes: `[root, key, next, op-code 0, root]`. -/
def attMapRow (a : Assignment) : List ℤ :=
  [a ROOT, 2 * a CURRENT + a SYMBOL, a NEXT, 0, a ROOT]

/-- … and its map log is exactly one row per trace row. -/
theorem att_mapLog (name : String) (t : VmTrace) :
    mapLog (attestedDesc name) t = t.rows.map attMapRow := by
  show t.rows.flatMap _ = _
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih]; rfl

/-! ## §3 — ⚑ THE GATE: a real `Satisfied2Public` WITNESS for the attested descriptor.

GENERAL over the automaton, the start state and the (non-empty, in-domain) word. The attestation
tooth is discharged by `autoRoot_commits` — the witness's root is a GENUINE commitment of the
automaton it runs, so the opening exists by construction rather than by assumption. -/

/-- One 4-column trace row: `(current, symbol, next, root)`. -/
def asg4 (s y n : Nat) (R : ℤ) : Assignment :=
  fun c => if c = 0 then Int.ofNat s else if c = 1 then Int.ofNat y
           else if c = 2 then Int.ofNat n else if c = 3 then R else 0

@[simp] theorem asg4_current (s y n : Nat) (R : ℤ) : asg4 s y n R CURRENT = Int.ofNat s := rfl
@[simp] theorem asg4_symbol (s y n : Nat) (R : ℤ) : asg4 s y n R SYMBOL = Int.ofNat y := rfl
@[simp] theorem asg4_next (s y n : Nat) (R : ℤ) : asg4 s y n R NEXT = Int.ofNat n := rfl
@[simp] theorem asg4_root (s y n : Nat) (R : ℤ) : asg4 s y n R ROOT = R := rfl

/-- **The run's trace rows**, carrying the committed root on every row. -/
def attRows (d : TableDfa Nat Nat) (R : ℤ) (q : Nat) : List Nat → List Assignment
  | []      => []
  | y :: ys => asg4 q y (d.step q y) R :: attRows d R (d.step q y) ys

theorem attRows_length (d : TableDfa Nat Nat) (R : ℤ) :
    ∀ (w : List Nat) (q : Nat), (attRows d R q w).length = w.length
  | [],      _ => rfl
  | y :: ys, q => by
    show (attRows d R (d.step q y) ys).length + 1 = ys.length + 1
    rw [attRows_length d R ys (d.step q y)]

/-- **The shape of every row**: an in-domain edge of `d` carrying the root. This one lemma
discharges BOTH the attestation tooth and the two range teeth. -/
theorem attRows_shape (d : TableDfa Nat Nat) (hstep : ∀ s y, d.step s y < ASTATES) (R : ℤ) :
    ∀ (w : List Nat) (q : Nat), q < ASTATES → (∀ y ∈ w, y < ASYM) →
      ∀ (i : Nat) (h : i < (attRows d R q w).length),
        ∃ s y : Nat, s < ASTATES ∧ y < ASYM ∧ (attRows d R q w)[i]'h = asg4 s y (d.step s y) R := by
  intro w
  induction w with
  | nil => intro q _ _ i h; simp [attRows] at h
  | cons y ys ih =>
    intro q hq hy i h
    cases i with
    | zero => exact ⟨q, y, hq, hy y List.mem_cons_self, rfl⟩
    | succ j =>
      have h' : j < (attRows d R (d.step q y) ys).length := by simpa [attRows] using h
      obtain ⟨s, y', hs, hy', hrow⟩ :=
        ih (d.step q y) (hstep q y) (fun z hz => hy z (List.mem_cons_of_mem _ hz)) j h'
      exact ⟨s, y', hs, hy', hrow⟩

/-- Adjacent rows CHAIN (the continuity window's whole content). -/
theorem attRows_chain (d : TableDfa Nat Nat) (R : ℤ) :
    ∀ (w : List Nat) (q i : Nat) (h : i + 1 < (attRows d R q w).length),
      ((attRows d R q w)[i + 1]'h) CURRENT
        = ((attRows d R q w)[i]'(Nat.lt_of_succ_lt h)) NEXT := by
  intro w
  induction w with
  | nil => intro q i h; simp [attRows] at h
  | cons y ys ih =>
    intro q i h
    cases i with
    | zero =>
      cases ys with
      | nil => simp [attRows] at h
      | cons y' ys' => rfl
    | succ j => exact ih (d.step q y) j (by simpa [attRows] using h)

/-- Every row carries the SAME root (the constancy window's content). -/
theorem attRows_root (d : TableDfa Nat Nat) (R : ℤ) :
    ∀ (w : List Nat) (q i : Nat) (h : i < (attRows d R q w).length),
      ((attRows d R q w)[i]'h) ROOT = R := by
  intro w
  induction w with
  | nil => intro q i h; simp [attRows] at h
  | cons y ys ih =>
    intro q i h
    cases i with
    | zero => rfl
    | succ j => exact ih (d.step q y) j (by simpa [attRows] using h)

/-- The FIRST row's `current` is the start state. -/
theorem attRows_head_current (d : TableDfa Nat Nat) (R : ℤ) (q : Nat) (w : List Nat) (hw : w ≠ [])
    (h : 0 < (attRows d R q w).length) : ((attRows d R q w)[0]'h) CURRENT = Int.ofNat q := by
  cases w with
  | nil => exact absurd rfl hw
  | cons y ys => rfl

/-- The LAST row's `next` IS the classification of the whole word. -/
theorem attRows_last_next (d : TableDfa Nat Nat) (R : ℤ) :
    ∀ (w : List Nat) (q i : Nat) (h : i < (attRows d R q w).length),
      i + 1 = (attRows d R q w).length →
      ((attRows d R q w)[i]'h) NEXT = Int.ofNat (classifyFrom d q w) := by
  intro w
  induction w with
  | nil => intro q i h _; simp [attRows] at h
  | cons y ys ih =>
    intro q i h hlast
    cases i with
    | zero =>
      have hys : ys = [] := by
        have h0 : (attRows d R (d.step q y) ys).length = 0 := by
          simp only [attRows, List.length_cons] at hlast
          omega
        rw [attRows_length d R ys (d.step q y)] at h0
        exact List.eq_nil_of_length_eq_zero h0
      subst hys
      rfl
    | succ j =>
      exact ih (d.step q y) j (by simpa [attRows] using h) (by simpa [attRows] using hlast)

/-- The word the witness's symbol column reads IS `w`. -/
theorem attRows_symbols (d : TableDfa Nat Nat) (R : ℤ) :
    ∀ (w : List Nat) (q : Nat), (attRows d R q w).map (fun a => (a SYMBOL).toNat) = w
  | [],      _ => rfl
  | y :: ys, q => by
    show (asg4 q y (d.step q y) R SYMBOL).toNat
        :: (attRows d R (d.step q y) ys).map (fun a => (a SYMBOL).toNat) = y :: ys
    rw [attRows_symbols d R ys (d.step q y)]
    rfl

/-- The witness's public inputs: `(initial_state, final_state, automaton_root)`. -/
def attPub (q f : Nat) (R : ℤ) : Assignment :=
  fun k => if k = 0 then Int.ofNat q else if k = 1 then Int.ofNat f else R

/-- The witness's table family: the map-ops log at `.mapOps`, empty elsewhere. -/
def attTf (rows : List Assignment) : TraceFamily :=
  fun id => if id = TableId.mapOps then rows.map attMapRow else []

/-- **THE WITNESS**: the trace that runs `d` from `q` on `w` against a root `R`. `R` is a
PARAMETER — the witness is parametric in ANY commitment of `d`, so no proof below ever reduces a
root into its heap. -/
def attWit (d : TableDfa Nat Nat) (R : ℤ) (q : Nat) (w : List Nat) : VmTrace :=
  { rows := attRows d R q w
  , pub  := attPub q (classifyFrom d q w) R
  , tf   := attTf (attRows d R q w) }

theorem attWit_rows_ne (d : TableDfa Nat Nat) (R : ℤ) (q : Nat) {w : List Nat}
    (hw : w ≠ []) : (attWit d R q w).rows ≠ [] := by
  intro h
  apply hw
  have h0 : (attRows d R q w).length = 0 := by
    rw [show attRows d R q w = [] from h]
    rfl
  rw [attRows_length d R w q] at h0
  exact List.eq_nil_of_length_eq_zero h0

/-- ⚑ **THE GATE — a real `Satisfied2Public` witness for the ATTESTED descriptor.** General in the
automaton, the start state, the word and the descriptor name; needs NO crypto hypothesis (the
opening is CONSTRUCTED, §1). -/
theorem attWit_satisfies (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (R : ℤ)
    (hcommit : CommitsAutomaton hash R d)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Public hash (attestedDesc name)
      (fun _ => 0) (fun _ => (0, 0)) [] (attWit d R q w) where
  rowConstraints := by
    intro i hi c hc
    have hi' : i < (attRows d (R) q w).length := hi
    have hloc : (envAt (attWit d R q w) i).loc = (attRows d (R) q w)[i]'hi' :=
      envAt_loc (t := attWit d R q w) hi
    obtain ⟨s, y, hs, hy, hrow⟩ :=
      attRows_shape d hstep (R) w q hq hsym i hi'
    simp only [attestedDesc, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · -- the ATTESTATION tooth: the edge opens against the committed root
      show ((1 : ℤ) = 1 → _)
      intro _
      rw [hloc, hrow]
      constructor
      · show opensTo hash (R) (2 * Int.ofNat s + Int.ofNat y)
          (some (Int.ofNat (d.step s y)))
        have hkey : (2 : ℤ) * Int.ofNat s + Int.ofNat y = ((keyOf s y : Nat) : ℤ) := by
          simp only [keyOf, Int.ofNat_eq_natCast]
          push_cast
          ring
        rw [hkey]
        exact hcommit s y hs hy
      · rfl
    · -- continuity: adjacent rows chain
      show WindowConstraint.holdsAt (envAt (attWit d R q w) i)
        (i + 1 == (attWit d R q w).rows.length) ⟨contWindowBody, true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt : i + 1 < (attRows d (R) q w).length := by
        have hne' : ¬ (i + 1 = (attRows d (R) q w).length) := by
          intro hEq
          rw [show (attWit d R q w).rows = attRows d (R) q w from rfl, hEq] at hnl
          simp at hnl
        omega
      have hnxt : (envAt (attWit d R q w) i).nxt = (attRows d (R) q w)[i + 1]'hlt :=
        envAt_nxt (t := attWit d R q w) hlt
      have hch : ((attRows d (R) q w)[i + 1]'hlt) CURRENT
          = ((attRows d (R) q w)[i]'hi') NEXT :=
        attRows_chain d (R) w q i hlt
      show (WindowExpr.add (.nxt CURRENT) (.mul (.const (-1)) (.loc NEXT))).eval
        (envAt (attWit d R q w) i) ≡ 0 [ZMOD 2013265921]
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, hch]
      have hz : ((attRows d (R) q w)[i]'hi') NEXT
          + (-1) * ((attRows d (R) q w)[i]'hi') NEXT = 0 := by ring
      rw [hz]
    · -- root constancy: every row carries the same root
      show WindowConstraint.holdsAt (envAt (attWit d R q w) i)
        (i + 1 == (attWit d R q w).rows.length) ⟨attRootBody, true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt : i + 1 < (attRows d (R) q w).length := by
        have hne' : ¬ (i + 1 = (attRows d (R) q w).length) := by
          intro hEq
          rw [show (attWit d R q w).rows = attRows d (R) q w from rfl, hEq] at hnl
          simp at hnl
        omega
      have hnxt : (envAt (attWit d R q w) i).nxt = (attRows d (R) q w)[i + 1]'hlt :=
        envAt_nxt (t := attWit d R q w) hlt
      show (WindowExpr.add (.nxt ROOT) (.mul (.const (-1)) (.loc ROOT))).eval
        (envAt (attWit d R q w) i) ≡ 0 [ZMOD 2013265921]
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, attRows_root d (R) w q (i + 1) hlt,
        attRows_root d (R) w q i hi']
      have hz : R + (-1) * R = 0 := by ring
      rw [hz]
    · -- B1: the FIRST row's `current` IS `pi[initial_state]`
      show (i == 0) = true → (envAt (attWit d R q w) i).loc CURRENT
        ≡ (envAt (attWit d R q w) i).pub PI_INITIAL [ZMOD 2013265921]
      intro hf
      have hi0 : i = 0 := by simpa using hf
      subst hi0
      rw [hloc, attRows_head_current d (R) q w hw hi']
      exact Int.ModEq.refl _
    · -- B2: the LAST row's `next` IS `pi[final_state]`
      show (i + 1 == (attWit d R q w).rows.length) = true →
        (envAt (attWit d R q w) i).loc NEXT
          ≡ (envAt (attWit d R q w) i).pub PI_FINAL [ZMOD 2013265921]
      intro hl
      have hlast : i + 1 = (attRows d (R) q w).length := by simpa using hl
      rw [hloc, attRows_last_next d (R) w q i hi' hlast]
      exact Int.ModEq.refl _
    · -- B3: the FIRST row's root IS `pi[automaton_root]` — the attestation's public face
      show (i == 0) = true → (envAt (attWit d R q w) i).loc ROOT
        ≡ (envAt (attWit d R q w) i).pub PI_ROOT [ZMOD 2013265921]
      intro hf
      have hi0 : i = 0 := by simpa using hf
      subst hi0
      rw [hloc, attRows_root d (R) w q 0 hi']
      exact Int.ModEq.refl _
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i hi r hr
    have hi' : i < (attRows d (R) q w).length := hi
    have hloc : (envAt (attWit d R q w) i).loc = (attRows d (R) q w)[i]'hi' :=
      envAt_loc (t := attWit d R q w) hi
    obtain ⟨s, y, hs, hy, hrow⟩ :=
      attRows_shape d hstep (R) w q hq hsym i hi'
    simp only [attestedDesc, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · show 0 ≤ (envAt (attWit d R q w) i).loc CURRENT
        ∧ (envAt (attWit d R q w) i).loc CURRENT < (2 : ℤ) ^ 15
      rw [hloc, hrow]
      refine ⟨?_, ?_⟩
      · show (0 : ℤ) ≤ Int.ofNat s
        exact Int.natCast_nonneg s
      · show Int.ofNat s < (2 : ℤ) ^ 15
        have hlt : s < 2 ^ 15 := by simpa [ASTATES] using hs
        rw [Int.ofNat_eq_natCast]
        exact_mod_cast hlt
    · show 0 ≤ (envAt (attWit d R q w) i).loc SYMBOL
        ∧ (envAt (attWit d R q w) i).loc SYMBOL < (2 : ℤ) ^ 1
      rw [hloc, hrow]
      refine ⟨?_, ?_⟩
      · show (0 : ℤ) ≤ Int.ofNat y
        exact Int.natCast_nonneg y
      · show Int.ofNat y < (2 : ℤ) ^ 1
        have hlt : y < 2 ^ 1 := by simpa [ASYM] using hy
        rw [Int.ofNat_eq_natCast]
        exact_mod_cast hlt
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [att_memLog]; simp
  memDisciplined := by rw [att_memLog]; trivial
  memBalanced := by rw [att_memLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [att_memLog]; rfl
  mapTableFaithful := by
    rw [att_mapLog]
    rfl
  publicTablesFaithful := by
    intro td htd
    simp only [attestedDesc, List.mem_singleton] at htd
    subst htd
    trivial
  publicLookupBalanced := by
    intro td htd
    simp only [attestedDesc, List.mem_singleton] at htd
    subst htd
    trivial

/-! ## §4 — ⚑ THE ATTESTATION: the root DETERMINES the automaton.

This is the property the run-table discipline does not have at any price. Under the standing CR
hypothesis, two automata committed by the SAME root agree on the ENTIRE declared key domain — so
"which automaton ran" is pinned by one public felt. -/

/-- ⚑ **`root_binds_automaton`** — a root commits AT MOST ONE transition function on the declared
domain. Pure consequence of `opensToMerkle_functional` (the deployed binary-Merkle anti-ghost). -/
theorem root_binds_automaton (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (R : ℤ)
    (d e : TableDfa Nat Nat) (hd : CommitsAutomaton hash R d) (he : CommitsAutomaton hash R e) :
    ∀ s y : Nat, s < ASTATES → y < ASYM → d.step s y = e.step s y := by
  intro s y hs hy
  have h := opensTo_functional hash hCR (hd s y hs hy) (he s y hs hy)
  simp only [Option.some.injEq] at h
  exact_mod_cast h

/-! ## §5 — ⚑ SOUNDNESS: acceptance ⇒ the trace is a run OF THE COMMITTED AUTOMATON.

The descriptor leg, mirroring `DfaRoutingTableEmit.tableRouting_refines_classify` with the declared
table replaced by the committed root. The `row_reads` step is where the attestation bites: the
row's `next` is not merely "some declared edge" — it is THE committed automaton's step. -/

/-- Two ℤ values, canonical (`[0, p)`) and congruent mod `p`, are EQUAL. (A root is a felt; it
cannot be range-collapsed without truncating a digest, so canonicality is carried explicitly.) -/
theorem int_eq_of_modEq {a b : ℤ} (ha : 0 ≤ a) (ha' : a < 2013265921)
    (hb : 0 ≤ b) (hb' : b < 2013265921) (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  omega

section Sound

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
variable {name : String} {t : VmTrace}

/-- The root column carries the PUBLIC root on EVERY row (the first-row pin threaded by the
constancy window, collapsed under canonicality). -/
theorem att_root_const (R : ℤ) (hRlo : 0 ≤ R) (hRhi : R < 2013265921)
    (hsat : Satisfied2Public hash (attestedDesc name) minit mfin maddrs t)
    (hroot : t.pub PI_ROOT = R)
    (hcanon : ∀ (i : Nat) (h : i < t.rows.length),
      0 ≤ (t.rows[i]'h) ROOT ∧ (t.rows[i]'h) ROOT < 2013265921) :
    ∀ (i : Nat) (h : i < t.rows.length), (t.rows[i]'h) ROOT = R := by
  intro i
  induction i with
  | zero =>
    intro h
    have hrc := hsat.rowConstraints 0 h _ (attB3_mem name)
    have hb3 : (envAt t 0).loc ROOT ≡ (envAt t 0).pub PI_ROOT [ZMOD 2013265921] :=
      (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) ROOT PI_ROOT).mp hrc
    rw [envAt_loc h] at hb3
    have hp : (envAt t 0).pub PI_ROOT = R := hroot
    rw [hp] at hb3
    exact int_eq_of_modEq (hcanon 0 h).1 (hcanon 0 h).2 hRlo hRhi hb3
  | succ j ih =>
    intro h
    have hj : j < t.rows.length := Nat.lt_of_succ_lt h
    have hrc := hsat.rowConstraints j hj _ (attRootConst_mem name)
    have hnl : (j + 1 == t.rows.length) = false := by
      have : j + 1 ≠ t.rows.length := Nat.ne_of_lt h
      simpa using this
    have hbody : attRootBody.eval (envAt t j) ≡ 0 [ZMOD 2013265921] := by
      simp only [VmConstraint2.holdsAt, attRootConst, WindowConstraint.holdsAt, if_true] at hrc
      exact hrc hnl
    simp only [attRootBody, WindowExpr.eval] at hbody
    rw [envAt_nxt h, envAt_loc hj] at hbody
    have hcong : (t.rows[j + 1]'h) ROOT ≡ (t.rows[j]'hj) ROOT [ZMOD 2013265921] := by
      obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hbody
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨k, by omega⟩)
    have hprev := ih hj
    rw [hprev] at hcong
    exact int_eq_of_modEq (hcanon (j + 1) h).1 (hcanon (j + 1) h).2 hRlo hRhi hcong

/-- **Every row is a genuine step of the COMMITTED automaton.** The range teeth make the row's
`current`/`symbol` canonical in-domain naturals; the map-op opening plus `opensTo_functional`
against the commitment forces `next = d.step current symbol` EXACTLY. -/
theorem att_row_reads (hCR : Poseidon2SpongeCR hash) (d : TableDfa Nat Nat) (R : ℤ)
    (hcommit : CommitsAutomaton hash R d)
    (hsat : Satisfied2Public hash (attestedDesc name) minit mfin maddrs t)
    (hrootAll : ∀ (i : Nat) (h : i < t.rows.length), (t.rows[i]'h) ROOT = R)
    {i : Nat} (hi : i < t.rows.length) :
    ∃ s y : Nat, s < ASTATES ∧ y < ASYM
      ∧ (t.rows[i]'hi) CURRENT = Int.ofNat s
      ∧ (t.rows[i]'hi) SYMBOL = Int.ofNat y
      ∧ (t.rows[i]'hi) NEXT = Int.ofNat (d.step s y) := by
  -- the two range teeth make the key columns canonical in-domain naturals
  have hrC := hsat.rowRanges i hi ⟨CURRENT, 15⟩ (by simp [attestedDesc])
  have hrS := hsat.rowRanges i hi ⟨SYMBOL, 1⟩ (by simp [attestedDesc])
  simp only [VmRange.holds] at hrC hrS
  rw [envAt_loc hi] at hrC hrS
  norm_num at hrC hrS
  refine ⟨((t.rows[i]'hi) CURRENT).toNat, ((t.rows[i]'hi) SYMBOL).toNat, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ASTATES]; omega
  · simp only [ASYM]; omega
  · rw [Int.ofNat_eq_natCast]; omega
  · rw [Int.ofNat_eq_natCast]; omega
  · -- the ATTESTATION tooth bites: the opening is against the COMMITTED root
    have hrc := hsat.rowConstraints i hi _ (attOpen_mem name)
    have hopen : opensTo hash ((envAt t i).loc ROOT)
        (2 * (envAt t i).loc CURRENT + (envAt t i).loc SYMBOL)
        (some ((envAt t i).loc NEXT)) := (hrc rfl).1
    rw [envAt_loc hi, hrootAll i hi] at hopen
    have hkey : 2 * ((t.rows[i]'hi) CURRENT) + ((t.rows[i]'hi) SYMBOL)
        = ((keyOf ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat : Nat) : ℤ) := by
      simp only [keyOf]
      push_cast
      omega
    rw [hkey] at hopen
    have hc := hcommit ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat
      (by simp only [ASTATES]; omega) (by simp only [ASYM]; omega)
    have hval := opensTo_functional hash hCR hopen hc
    simp only [Option.some.injEq] at hval
    rw [hval]
    rfl

/-- ⚑ **`attested_refines_committed` — THE SOUNDNESS THEOREM.** A trace satisfying the emitted
attested descriptor reads a genuine ℕ-word off its symbol column, EVERY row of it is a step of the
automaton COMMITTED by the public root, and the exposed public `final_state` IS
`classifyFrom d initial_state` of that word. The automaton is bound by ONE felt; no edge is
declared anywhere. -/
theorem attested_refines_committed (hCR : Poseidon2SpongeCR hash) (d : TableDfa Nat Nat) (R : ℤ)
    (hcommit : CommitsAutomaton hash R d)
    (hdom : ∀ s y, s < ASTATES → y < ASYM → d.step s y < ASTATES)
    (hRlo : 0 ≤ R) (hRhi : R < 2013265921)
    (hsat : Satisfied2Public hash (attestedDesc name) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hcanon : ∀ (i : Nat) (h : i < t.rows.length),
      0 ≤ (t.rows[i]'h) ROOT ∧ (t.rows[i]'h) ROOT < 2013265921)
    (hroot : t.pub PI_ROOT = R)
    (q0 : ℕ) (hstart : t.pub PI_INITIAL = Int.ofNat q0) (hq0 : q0 < 2013265921)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    t.rows.map (fun a => a SYMBOL)
        = (t.rows.map (fun a => (a SYMBOL).toNat)).map Int.ofNat
      ∧ fN = classifyFrom d q0 (t.rows.map (fun a => (a SYMBOL).toNat)) := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrootAll := att_root_const R hRlo hRhi hsat hroot hcanon
  have reads := fun {i : Nat} (hi : i < t.rows.length) =>
    att_row_reads hCR d R hcommit hsat hrootAll hi
  -- (i) the symbol column is a genuine ℕ-word
  have hcol : t.rows.map (fun a => a SYMBOL)
      = (t.rows.map (fun a => (a SYMBOL).toNat)).map Int.ofNat := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨s, y, _, _, _, hsym, _⟩ := reads hi
    simp [Function.comp, hsym]
  refine ⟨hcol, ?_⟩
  -- (ii) every read row is a genuine step of the COMMITTED automaton
  have htable : ∀ r ∈ traceRowsN t, r.next = d.step r.state r.sym := by
    intro r hr
    simp only [traceRowsN, List.mem_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨s, y, _, _, hcur, hsym, hnext⟩ := reads hi
    simp [mkRowN, hcur, hsym, hnext]
  -- (iii) continuity threads the read naturals
  have hcont : Dregg2.Crypto.DfaAcceptanceAir.Continuous (traceRowsN t) := by
    apply continuous_of_chain
    intro i hi1
    have hi : i < t.rows.length := Nat.lt_of_succ_lt hi1
    have hnl : i + 1 ≠ t.rows.length := Nat.ne_of_lt hi1
    obtain ⟨s', y', hs', _, hcur', _, _⟩ := reads hi1
    obtain ⟨s, y, hs, hy, _, _, hnext⟩ := reads hi
    have hrc := hsat.rowConstraints i hi _ (attCont_mem name)
    have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
    have hw : contWindowBody.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
      simp only [VmConstraint2.holdsAt, attContinuity, WindowConstraint.holdsAt, if_true] at hrc
      exact hrc hlf
    have hx : (envAt t i).nxt CURRENT = Int.ofNat s' := by rw [envAt_nxt hi1]; exact hcur'
    have hy2 : (envAt t i).loc NEXT = Int.ofNat (d.step s y) := by rw [envAt_loc hi]; exact hnext
    have hs'p : s' < 2013265921 := by simp only [ASTATES] at hs'; omega
    have hstepp : d.step s y < 2013265921 := by
      have := hdom s y hs hy
      simp only [ASTATES] at this
      omega
    have heq := cont_eq hw hx hy2 hs'p hstepp
    rw [hcur', hnext]
    simpa using heq
  -- (iv) the head starts at the public initial state
  have hhead : ∀ r₀, (traceRowsN t).head? = some r₀ → r₀.state = q0 := by
    intro r₀ hr₀
    simp only [traceRowsN, List.head?_map, Option.map_eq_some_iff] at hr₀
    obtain ⟨a, hah, rfl⟩ := hr₀
    have h0 : t.rows[0]'hpos = a := by
      rw [List.head?_eq_some_head hne] at hah
      have : t.rows.head hne = a := Option.some.inj hah
      rw [← this, List.head_eq_getElem hne]
    obtain ⟨s, y, hs, _, hcur, _, _⟩ := reads hpos
    have hrc := hsat.rowConstraints 0 hpos _ (attB1_mem name)
    have hpf : (envAt t 0).loc CURRENT ≡ t.pub PI_INITIAL [ZMOD 2013265921] :=
      (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) CURRENT PI_INITIAL).mp hrc
    rw [envAt_loc hpos, hcur, hstart] at hpf
    have hsq : s = q0 := ofNat_eq_of_modEq (by simp only [ASTATES] at hs; omega) hq0 hpf
    show (a CURRENT).toNat = q0
    rw [← h0, hcur, hsq]
    rfl
  -- (v) the last row's next IS classifyFrom of the read word, exposed as pi[final]
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hlast? : (traceRowsN t).getLast? = some (mkRowN (t.rows.getLast hne)) := by
    rw [traceRowsN, List.getLast?_map, List.getLast?_eq_some_getLast hne]
    rfl
  have hclass := lastNext_eq_classifyFrom d q0 (traceRowsN t) htable hcont hhead _ hlast?
  have hsymbols : symbols (traceRowsN t) = t.rows.map (fun a => (a SYMBOL).toNat) := by
    simp only [symbols, traceRowsN, List.map_map]
    rfl
  obtain ⟨sL, yL, hsL, hyL, _, _, hnextL⟩ := reads hlt
  have hrcL := hsat.rowConstraints (t.rows.length - 1) hlt _ (attB2_mem name)
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrcL
  have hpl : (envAt t (t.rows.length - 1)).loc NEXT ≡ t.pub PI_FINAL [ZMOD 2013265921] :=
    (holdsVm_piLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) NEXT PI_FINAL).mp
      hrcL
  rw [envAt_loc hlt, hnextL, hfin] at hpl
  have hstepBound : d.step sL yL < 2013265921 := by
    have := hdom sL yL hsL hyL
    simp only [ASTATES] at this
    omega
  have hfEq : d.step sL yL = fN := ofNat_eq_of_modEq hstepBound hfN hpl
  have hlastRow : (mkRowN (t.rows.getLast hne)).next = d.step sL yL := by
    show ((t.rows.getLast hne) NEXT).toNat = d.step sL yL
    rw [List.getLast_eq_getElem hne, hnextL]
    rfl
  rw [hsymbols] at hclass
  rw [← hfEq, ← hlastRow]
  exact hclass

end Sound

/-! ## §6 — ⚑ THE COMPOSED, ATTESTED OBJECT: the `k`-fold PRODUCT, now BOUND.

The same composed family `TinyAutomataSatisfiable` measured (four pairwise non-isomorphic machines,
reachable product space 2 → 6 → 12 → 25 over `k = 1…4`), now carried by the attested descriptor:
one satisfying trace, one committed root, every component's verdict exposed. -/

/-- The `k`-fold product's step stays inside the declared state domain (`4^k ≤ 256 < 2^15`). -/
theorem prodI_step_lt (k : Nat) : ∀ s y, (prodI k).step s y < ASTATES := by
  intro s y
  have hlen : (famI k).length ≤ 4 := by
    have h : (famI k).length = min k indep.length := by simp [famI, List.length_take]
    have h4 : indep.length = 4 := rfl
    omega
  have h : (prodI k).step s y < IRADIX ^ (famI k).length :=
    prodListDfa_step_lt IRADIX (famI k) (famI_step_lt k) s y
  have hpow : IRADIX ^ (famI k).length ≤ IRADIX ^ 4 :=
    Nat.pow_le_pow_right (by norm_num [IRADIX]) hlen
  have h256 : IRADIX ^ 4 = 256 := by norm_num [IRADIX]
  simp only [ASTATES]
  omega

/-- The probe word is in-alphabet. -/
theorem probeW_sym : ∀ y ∈ probeW, y < ASYM := by decide

/-- **The ATTESTED composed witness** at `k`: the product automaton's own commitment. -/
def prodAttWit (hash : List ℤ → ℤ) (k : Nat) (w : List Nat) : VmTrace :=
  attWit (prodI k) (autoRoot hash (prodI k)) 0 w

/-- ⚑ **THE GATE, FIRED ON THE COMPOSED OBJECT** — a real `Satisfied2Public` witness for the
attested descriptor at the `k`-fold product, against a root that GENUINELY COMMITS that product;
general in `k` and in the (in-alphabet, non-empty) word. -/
theorem prodAttWit_satisfies (hash : List ℤ → ℤ) (k : Nat) (w : List Nat) (hw : w ≠ [])
    (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Public hash (attestedDesc name) (fun _ => 0) (fun _ => (0, 0)) []
      (prodAttWit hash k w) :=
  attWit_satisfies hash (prodI k) (autoRoot hash (prodI k)) (autoRoot_commits hash (prodI k))
    (prodI_step_lt k) 0 (by norm_num [ASTATES]) w hw hsym name

/-- ⚑ **THE COMPOSITION, ATTESTED.** A trace satisfying the attested descriptor against a root that
commits the `k`-fold product exposes, in its public `final_state`, the mixed-radix packing of EVERY
component automaton's classification of the word it reads — and "which product automaton ran" is
pinned by the public root (§4), not assumed. -/
theorem attested_exposes_components (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {name : String} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (k : Nat) (hlen : (famI k).length = k) (R : ℤ)
    (hcommit : CommitsAutomaton hash R (prodI k))
    (hRlo : 0 ≤ R) (hRhi : R < 2013265921)
    (hsat : Satisfied2Public hash (attestedDesc name) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hcanon : ∀ (i : Nat) (h : i < t.rows.length),
      0 ≤ (t.rows[i]'h) ROOT ∧ (t.rows[i]'h) ROOT < 2013265921)
    (hroot : t.pub PI_ROOT = R)
    (hstart : t.pub PI_INITIAL = Int.ofNat 0)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    fN = encodeDigits IRADIX (List.zipWith
      (fun d q => classifyFrom d q (t.rows.map (fun a => (a SYMBOL).toNat)))
      (famI k) (List.replicate k 0)) := by
  have hbase := attested_refines_committed hCR (prodI k) R hcommit
    (fun s y _ _ => prodI_step_lt k s y) hRlo hRhi hsat hne hcanon hroot
    0 hstart (by norm_num) fN hfin hfN
  have hproj := classify_prodList IRADIX (by norm_num [IRADIX]) (famI k) (List.replicate k 0)
    (by rw [hlen, List.length_replicate]) (famI_step_lt k)
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; norm_num [IRADIX])
    (t.rows.map (fun a => (a SYMBOL).toNat))
  rw [encodeDigits_replicate_zero IRADIX k] at hproj
  rw [hbase.2, show prodI k = prodListDfa IRADIX (famI k) from rfl, hproj]

/-! ## §6a — ⚑ THE CANARY: an edge the committed automaton does NOT have is REFUSED.

The other polarity of the attestation. `attWit_satisfies` shows a genuine run of the committed
automaton is satisfiable; this shows a trace claiming ANY other edge is UNSATISFIABLE — which is
exactly "the traversed edges are edges OF THE COMMITTED AUTOMATON", the conjunct the run-table
discipline cannot state at all. -/

/-- A one-row trace claiming the edge `(q, y) → n`. -/
def forgedTrace (R : ℤ) (q y n : Nat) : VmTrace :=
  { rows := [asg4 q y n R]
  , pub  := attPub q n R
  , tf   := attTf [asg4 q y n R] }

/-- ⚑ **A NON-EDGE OF THE COMMITTED AUTOMATON PROVABLY FAILS `Satisfied2Public`.** No declared
table is involved: the map-op opening against the committed root, plus opening functionality,
forces the row's `next` to be the committed automaton's step. -/
theorem forged_edge_refused (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : TableDfa Nat Nat) (R : ℤ) (hcommit : CommitsAutomaton hash R d) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (q y n : Nat)
    (hbad : n ≠ d.step q y) :
    ¬ Satisfied2Public hash (attestedDesc name) minit mfin maddrs (forgedTrace R q y n) := by
  intro h
  have hlen : 0 < (forgedTrace R q y n).rows.length := Nat.zero_lt_one
  have hrootAll : ∀ (i : Nat) (hi : i < (forgedTrace R q y n).rows.length),
      ((forgedTrace R q y n).rows[i]'hi) ROOT = R := by
    intro i hi
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [forgedTrace] using hi
      omega
    subst hi0
    rfl
  obtain ⟨s, y', _, _, hcur, hsym, hnext⟩ := att_row_reads hCR d R hcommit h hrootAll hlen
  have hc : Int.ofNat q = Int.ofNat s := hcur
  have hy : Int.ofNat y = Int.ofNat y' := hsym
  have hn : Int.ofNat n = Int.ofNat (d.step s y') := hnext
  have hqs : q = s := Int.ofNat_inj.mp hc
  have hyy : y = y' := Int.ofNat_inj.mp hy
  have hnn : n = d.step s y' := Int.ofNat_inj.mp hn
  exact hbad (by rw [hnn, hqs, hyy])

/-! ## §7 — ⚑ THE MEASURED PRICE OF ATTESTATION.

⚠ Every `#guard` below is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`. The
`Prop`-level content is `attWit_satisfies` / `prodAttWit_satisfies` (the witnesses),
`root_binds_automaton` (the attestation), `attested_refines_committed` (soundness) and
`forged_edge_refused` (the canary).

⚠ AND: both descriptors measured here are SATISFIABLE — the attested one by `attWit_satisfies`, the
run-table baseline by `TinyAutomataSatisfiable.prodRunWit_satisfies`. The whole-graph numbers are
re-quoted from that file's §7 and carry NO witness there; they are the price of the attestation the
run table does not buy, never a crossover. -/

/-- A word of `n` in-alphabet symbols (the length axis of the measurement). -/
def wordN (n : Nat) : List Nat := List.replicate n 1

-- ⚑ THE ATTESTED DESCRIPTOR'S SHAPE: 4 columns, 3 PIs, 6 constraints, ONE table (the map-ops chip),
-- ZERO declared rows, ZERO nonlinear multiplications. The same object for EVERY automaton and
-- EVERY word length — the automaton rides in pi[2], the length is free.
#guard costOf attestedInstance ==
  { traceWidth := 4, piCount := 3, constraints := 6, tables := 1
  , declaredRows := 0, forcedTraceRows := .unpinned, nonlinearMults := 0 }

-- Its wire size, pinned: 1190 bytes, of which the two 8-lane digest groups (`root`, `new_root` —
-- the deployed `MapOpSpec.root : Vec<LeanExpr>` shape) are the bulk.
#guard jsonBytes attestedInstance == 1190

-- ⚑ THE BYTES, MEASURED AGAINST THE RUN-TABLE BASELINE at k = 4. The attested descriptor is FLAT;
-- the run-table descriptor grows ~10 bytes per symbol because it SHIPS THE RUN to the verifier.
-- They TIE at |w| = 60 (1190 = 1190); the attested object is strictly smaller from |w| = 61 on,
-- and strictly larger below. This is the honest byte crossover, not a claimed win.
#guard (List.map (fun n => (jsonBytes attestedInstance, jsonBytes (prodRunDesc 4 (wordN n))))
    [8, 32, 60, 61, 128])
  == [(1190, 669), (1190, 909), (1190, 1190), (1190, 1199), (1190, 1869)]

-- At the FIXED 8-symbol probe word the run-table descriptor is the smaller object (654–670 vs
-- 1190) — but it is a DIFFERENT object for each k AND each word, and it binds no automaton.
#guard (List.map (fun k => (jsonBytes attestedInstance, jsonBytes (prodRunDesc k probeW)))
    [1, 2, 3, 4]) == [(1190, 654), (1190, 654), (1190, 665), (1190, 670)]

-- ⚑ MAIN-TRACE AREA (columns × trace rows): attested 4·|w| vs the unbound run table's 3·|w|.
-- The +|w| is the root column.
#guard (List.map (fun n => (AW_WIDTH * n, 3 * n)) [8, 16, 32]) == [(32, 24), (64, 48), (128, 96)]

-- ⚑ THE AUX BILL THE IR COUNTERS DO **NOT** SEE. The map-ops table carries one arity-5 row per
-- opened trace row (5·|w|), and the DEPLOYED AIR realizes each opening as a depth-16 binary-Merkle
-- path — `MAP_TREE_DEPTH` permutations per opened row, 16·|w| chip rows. This is the real price of
-- attestation, and it is INDEPENDENT of |Q|·|Σ| and of k.
#guard (List.map (fun n => (5 * n, MAP_TREE_DEPTH * n)) [8, 16, 32])
  == [(40, 128), (80, 256), (160, 512)]

-- The whole-graph alternative, re-quoted from TinyAutomataSatisfiable §7 (⚠ NO witness exists for
-- any of them — the Eulerian obstruction is unresolved): area 12, 36, 72, 150 at k = 1…4, GROWING
-- with the automaton. The attested route's bill does not depend on k at all.
#guard (List.map (fun k => (costOf (tableRoutingDesc "wg" (reachTable (prodI k) 24))).area)
    [1, 2, 3, 4]) == [some 12, some 36, some 72, some 150]

-- The committed map's key domain: 2^15 states × 2 symbols = the deployed 2^16 leaves, exactly.
#guard ASTATES * ASYM == NKEYS
#guard NKEYS == 2 ^ MAP_TREE_DEPTH

/-! ### The law, stated

At word length `|w|`, over descriptors that HAVE WITNESSES:

  * **run table, UNBOUND** (`TinyAutomataSatisfiable.prodRunWit_satisfies`) — 3 columns, 4
    constraints, 2 PIs, ONE declared table of `|w|` rows, main area `3·|w|`, no aux chip rows,
    descriptor bytes GROWING ~10 per symbol (629 at `|w| = 4` → 1869 at `|w| = 128`) and re-issued
    per automaton AND per word. Binds: the edges TRAVERSED. Does NOT bind: which automaton ran.
  * **attested, BOUND** (`attWit_satisfies`) — 4 columns, 6 constraints, 3 PIs, ZERO declared rows,
    main area `4·|w|`, `5·|w|` map-op rows, `16·|w|` deployed chip rows, descriptor bytes CONSTANT
    at 1190 and IDENTICAL for every automaton and every word length. Binds: the automaton, by ONE
    public felt (`root_binds_automaton`), every row as a step OF it
    (`attested_refines_committed`), and every non-edge as UNSATISFIABLE (`forged_edge_refused`).
  * **whole graph, BOUND, UNSATISFIABLE** — area 12/36/72/150 at `k = 1…4` even reachability-
    minimised, growing with `|Q|·|Σ|`, and NO witness at any `k`.

Read at the resolution the numbers support: the attestation gap closes at `+1` main column, `+2`
constraints, `+1` PI, `5·|w|` map-op rows and `16·|w|` chip rows. The descriptor becomes
automaton-generic and word-length-generic, and crosses BELOW the run-table descriptor in wire bytes
at `|w| = 60`. Below that length the run-table object is smaller — and unbound. The `16·|w|` chip
rows are the real bill; they are stated here rather than hidden, and they are the reason this is a
TRADE, not a free lunch.

⚑ What the IR vocabulary DID support, and what it did NOT. The subset check "the run's edges are
edges of the committed automaton" IS achievable at `O(|w|)` in this IR — but NOT by a `lookup`. A
`lookup` targets a `TableDef`, and the only content-committing row semantics is
`exactPublicRows`, whose contents are the DESCRIPTOR'S OWN BYTES: any lookup-based binding must
therefore declare every edge (`O(|Q|·|Σ|)`) and additionally inherits the unit-capacity
exact-multiset receive, i.e. the Eulerian obstruction. There is NO table semantics in
`RowSemantics` whose contents are committed by a ROOT rather than listed. The instrument that DOES
exist is the `MapOp` — whose denotation is already an opening of a root-committed sorted map — and
that is what this file uses. The precise IR gap, if a lookup-shaped binding is ever wanted: a
`RowSemantics.committedRows (root : EmittedExpr)` whose faithfulness leg is `mapRoot`-of-the-table
rather than a literal row list. -/

/-! ## §8 — axiom tripwires. -/

#assert_all_clean [forged_edge_refused,
  kvRows_length, kvRows_key_mem, kvRows_sorted, kvRows_get,
  autoHeap_length, autoHeap_sorted, autoRoot_commits,
  att_memLog, att_mapOps, att_mapLog,
  attRows_length, attRows_shape, attRows_chain, attRows_root, attRows_head_current,
  attRows_last_next, attRows_symbols, attWit_rows_ne, attWit_satisfies,
  root_binds_automaton, int_eq_of_modEq, att_root_const, att_row_reads,
  attested_refines_committed, prodI_step_lt, prodAttWit_satisfies, attested_exposes_components]

end Dregg2.Circuit.Emit.AttestedAutomatonEmit
