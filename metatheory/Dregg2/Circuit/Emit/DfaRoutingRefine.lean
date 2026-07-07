/-
# Dregg2.Circuit.Emit.DfaRoutingRefine — the RUNG-1 functional-correctness refinement for the
emitted DFA-routing descriptor (`dfaRoutingDesc`).

## What this file IS

`DfaRoutingEmit.lean` proves only PER-GATE faithfulness lemmas (`transition_body_zero_iff`,
`continuity_window_zero_iff`, `copyforward_window_zero_iff` — each one gate poly = 0 ↔ its local
relation). This file proves the missing WHOLE-DESCRIPTOR bridge: an assignment/trace SATISFYING the
emitted `dfaRoutingDesc` (via the deployed acceptance predicate `Satisfied2`) corresponds to a
GENUINE run of the pinned toggle automaton, and its exposed final-state public input equals
`classify(input)` — welded to the already-proven, `#assert_axioms`-clean semantic model
`Dregg2.Crypto.DfaAcceptanceAir` (`TableDfa`, `classify`, `lastNext_eq_classifyFrom`).

The pinned automaton is the descriptor's own toggle DFA: state/symbol on the grid `{0,1}`, transition
`step s y = s + y - 2·s·y` (the XOR interpolant `toggleInterp` that `transitionBody` pins). We
instantiate the model at `State = Sym = Digest = ℤ` and read a `Row` off each trace row's
`(current, symbol, next, entry_hash, running_hash)` columns.

## The terminal-step obligation (a REAL property of the deployed AIR, named honestly)

The deployed STARK divides EVERY per-row constraint by the TRANSITION zerofier
`Z_T = (xⁿ − 1)/(x − ωⁿ⁻¹)` (`circuit/src/stark.rs:20`, `:1108`), so the per-row toggle gate is
enforced on rows `0 … n−2` only — NOT the last row (this is the `when_transition` lowering; the Lean
`.base (.gate …)` denotation is faithful: `holdsVm … (.gate _)` is `True` on `isLast`). The last
row's `next` is pinned to the public `final_state` by the boundary constraint B2, and its
`(current, symbol, next)` triple is bound into the route commitment by the running-hash chip lookups
(the Poseidon2 half, `route_commitment_binds_trace`). So `final = classify(FULL input)` requires the
last row to ALSO be a genuine transition — an obligation the honest prover discharges but the gate
lowering does not re-assert. We name it as the explicit hypothesis `hterm` (exactly the transition
gate on the last row), and prove the whole bridge under it. Without `hterm` the state ENTERING the
last row is already forced to be the genuine classification of the consumed prefix — that fragment
needs no extra hypothesis (it is `htable`/`hcont`/`hhead`, established purely from `Satisfied2`).

## Non-vacuity

`witTrace` (§6): a concrete 2-row toggle run `IDLE=0 →1 1 →1 0` that PROVABLY `Satisfied2 dfaRoutingDesc`
AND satisfies `hterm`; feeding it the bridge recovers `final = 0 = classify (pinnedDfa 0) [1,1]`
(`witness_refines`). `badTrace`: the same run with row-0 `next` claiming the forbidden edge
`step(0,1)=0`, which PROVABLY fails `Satisfied2` (`badTrace_not_satisfied`) — the transition gate on
the non-last row rejects it. And `classify` genuinely discriminates (`classify [1,1] = 0 ≠ 1 =
classify [1]`), so the conclusion is not a constant.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The classification bridge is CRYPTO-FREE:
`air_final_state_is_classification`/`lastNext_eq_classifyFrom` use no hash carrier (the running-hash
Poseidon2 CR carrier `CollisionFree` is needed only for the SEPARATE binding half
`route_commitment_binds_trace`, and is NOT consumed here). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.DfaRoutingEmit
import Dregg2.Crypto.DfaAcceptanceAir

namespace Dregg2.Circuit.Emit.DfaRoutingRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv holdsVm_gate_of_notLast holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingEmit
open Dregg2.Crypto.DfaAcceptanceAir
  (TableDfa Row classify classifyFrom symbols lastNext_eq_classifyFrom)

set_option autoImplicit false

/-! ## §1 — The pinned toggle DFA and the trace→run reading. -/

/-- The descriptor's transition function: the toggle interpolant `step s y = s + y − 2·s·y`, which is
`XOR` on the grid `{0,1}`. This is EXACTLY the RHS of `transitionBody`'s faithfulness lemma
`DfaRoutingEmit.transition_body_zero_iff`. -/
def toggleStep (s y : ℤ) : ℤ := s + y - 2 * (s * y)

/-- The pinned table DFA over `ℤ`: the toggle transition, start `q0` (bound to `pi[initial_state]`),
accept set `{LOCAL = 1}` (unused by the classification bridge; makes accept/reject demonstrable). -/
def pinnedDfa (q0 : ℤ) : TableDfa ℤ ℤ where
  step := toggleStep
  start := q0
  accepts := fun s => s = 1

/-- The model `Row` read off one trace row: its `(current, symbol, next, entry_hash, running_hash)`
columns are exactly `Row.state/sym/next/entryHash/running`. -/
def mkRow (a : Assignment) : Row ℤ ℤ ℤ where
  state := a CURRENT
  sym := a SYMBOL
  next := a NEXT
  entryHash := a ENTRY_HASH
  running := a RUNNING_HASH

/-- The whole trace as a model run: the `Row` list. `symbols (traceRows t)` is the symbol column —
the DFA's input. -/
def traceRows (t : VmTrace) : List (Row ℤ ℤ ℤ) := t.rows.map mkRow

/-- The input the trace reads is its symbol column. -/
theorem symbols_traceRows (t : VmTrace) :
    symbols (traceRows t) = t.rows.map (fun a => a SYMBOL) := by
  simp only [symbols, traceRows, List.map_map, Function.comp_def, mkRow]

/-! ## §2 — The constraints of `dfaRoutingDesc` we consume are genuinely present. -/

/-- Peel `List.mem_cons` until the named constraint's position is reached. -/
theorem mem_transitionGate :
    VmConstraint2.base (.gate transitionBody) ∈ dfaRoutingDesc.constraints := by
  show transitionGate ∈ dfaRoutingDesc.constraints
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_continuityWindow :
    VmConstraint2.windowGate ⟨contWindowBody, true⟩ ∈ dfaRoutingDesc.constraints := by
  show continuityWindow ∈ dfaRoutingDesc.constraints
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_b1InitialPin :
    VmConstraint2.base (.piBinding .first CURRENT PI_INITIAL) ∈ dfaRoutingDesc.constraints := by
  show b1InitialPin ∈ dfaRoutingDesc.constraints
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

theorem mem_b2FinalPin :
    VmConstraint2.base (.piBinding .last NEXT PI_FINAL) ∈ dfaRoutingDesc.constraints := by
  show b2FinalPin ∈ dfaRoutingDesc.constraints
  simp only [dfaRoutingDesc]
  repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-! ## §3 — Extraction: reading the per-row facts out of a `Satisfied2` witness. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- `getD` on an in-bounds index is `getElem`. -/
theorem getD_row {i : Nat} (hi : i < t.rows.length) : t.rows.getD i zeroAsg = t.rows[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The current-row environment's `loc` is the trace row (in-bounds). -/
theorem envAt_loc {i : Nat} (hi : i < t.rows.length) : (envAt t i).loc = t.rows[i]'hi :=
  getD_row hi

/-- The current-row environment's `nxt` is the next trace row (in-bounds). -/
theorem envAt_nxt {i : Nat} (hi : i + 1 < t.rows.length) : (envAt t i).nxt = t.rows[i + 1]'hi :=
  getD_row hi

/-- **Any base-gate constraint of `dfaRoutingDesc` forces its body to vanish on a NON-LAST row.**
(On the last row a `.gate` is vacuous — the transition-zerofier lowering.) -/
theorem gate_forces (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {g : EmittedExpr} (hg : VmConstraint2.base (.gate g) ∈ dfaRoutingDesc.constraints) :
    g.eval (t.rows[i]'hi) = 0 := by
  have hrc := hsat.rowConstraints i hi _ hg
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  rw [← envAt_loc hi]
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **Any `onTransition` window constraint forces its body to vanish on a NON-LAST row.** -/
theorem window_forces (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {w : WindowConstraint} (hw : VmConstraint2.windowGate w ∈ dfaRoutingDesc.constraints)
    (honT : w.onTransition = true) :
    w.body.eval (envAt t i) = 0 := by
  have hrc := hsat.rowConstraints i hi _ hw
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, honT, if_true] at hrc
  exact hrc hlf

/-- **B1 fires on the first row.** -/
theorem piFirst_forces (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .first col k) ∈ dfaRoutingDesc.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrc := hsat.rowConstraints 0 hpos _ hb
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) col k).mp hrc

/-- **B2 fires on the last row.** -/
theorem piLast_forces (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .last col k) ∈ dfaRoutingDesc.constraints) :
    (envAt t (t.rows.length - 1)).loc col = t.pub k := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ hb
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_piLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) col k).mp hrc

end Extract

/-! ## §4 — `Continuous` of the read run from index-adjacency (the model's own predicate). -/

/-- If consecutive trace rows chain (`rowsᵢ₊₁.current = rowsᵢ.next`), the read `Row` list is
`Continuous` in the model's sense. -/
theorem continuous_map : ∀ (l : List Assignment),
    (∀ i (_ : i + 1 < l.length), l[i + 1] CURRENT = l[i] NEXT) →
    Dregg2.Crypto.DfaAcceptanceAir.Continuous (l.map mkRow)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h => by
      refine ⟨?_, continuous_map (b :: rest) (fun i hi => ?_)⟩
      · have h0 := h 0 (by simp)
        simpa [mkRow] using h0
      · have hh := h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa using hh

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE. -/

/-- **`dfaRouting_refines_classify` — the Rung-1 functional-correctness refinement.**

A trace `t` that SATISFIES the emitted descriptor `dfaRoutingDesc` (via the deployed acceptance
predicate `Satisfied2`), is non-empty, and whose LAST row is also a genuine transition (`hterm`, the
terminal-step obligation the transition-zerofier lowering leaves to B2 + the route commitment), IS a
genuine run of the pinned toggle DFA:

  * every row is a real table transition (`next = step current symbol`);
  * the run starts at the public `initial_state`;
  * the exposed public `final_state` (`pi[PI_FINAL]`) equals `classify(input)` — the genuine
    deterministic classification of the trace's symbol column.

This is `air_run_is_table_run` / `air_final_state_is_classification` transported onto the EMITTED
descriptor's `Satisfied2` accept-set, via the per-gate teeth of `DfaRoutingEmit` and the pure model
lemma `lastNext_eq_classifyFrom`. No crypto carrier is consumed. -/
theorem dfaRouting_refines_classify {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hterm : transitionBody.eval (t.rows.getD (t.rows.length - 1) zeroAsg) = 0) :
    (∀ r ∈ traceRows t, r.next = (pinnedDfa (t.pub PI_INITIAL)).step r.state r.sym) ∧
    (∀ r₀, (traceRows t).head? = some r₀ → r₀.state = t.pub PI_INITIAL) ∧
    t.pub PI_FINAL = classify (pinnedDfa (t.pub PI_INITIAL)) (symbols (traceRows t)) := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  -- (i) every row a genuine transition (last row via hterm, others via the transition gate)
  have htable : ∀ r ∈ traceRows t,
      r.next = (pinnedDfa (t.pub PI_INITIAL)).step r.state r.sym := by
    intro r hr
    simp only [traceRows, List.mem_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    show a NEXT = toggleStep (a CURRENT) (a SYMBOL)
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    subst hia
    by_cases hnl : i + 1 = t.rows.length
    · have hi_eq : t.rows.length - 1 = i := by omega
      rw [hi_eq, getD_row hi] at hterm
      exact (transition_body_zero_iff (t.rows[i]'hi)).mp hterm
    · exact (transition_body_zero_iff (t.rows[i]'hi)).mp
        (gate_forces hsat hi hnl mem_transitionGate)
  -- (ii) continuity threads the run
  have hcont : Dregg2.Crypto.DfaAcceptanceAir.Continuous (traceRows t) := by
    apply continuous_map
    intro i hi1
    have hi : i < t.rows.length := Nat.lt_of_succ_lt hi1
    have hnl : i + 1 ≠ t.rows.length := Nat.ne_of_lt hi1
    have hw := window_forces hsat hi hnl mem_continuityWindow rfl
    have hc := (continuity_window_zero_iff (envAt t i)).mp hw
    rw [envAt_nxt hi1, envAt_loc hi] at hc
    exact hc
  -- (iii) the head starts at the public initial state
  have hhead : ∀ r₀, (traceRows t).head? = some r₀ → r₀.state = t.pub PI_INITIAL := by
    intro r₀ hr₀
    simp only [traceRows, List.head?_map, Option.map_eq_some_iff] at hr₀
    obtain ⟨a, hah, rfl⟩ := hr₀
    show a CURRENT = t.pub PI_INITIAL
    have h0 : t.rows[0]'hpos = a := by
      rw [List.head?_eq_some_head hne] at hah
      have : t.rows.head hne = a := Option.some.inj hah
      rw [← this, List.head_eq_getElem hne]
    have hpf := piFirst_forces hsat hne mem_b1InitialPin
    rw [envAt_loc hpos, h0] at hpf
    exact hpf
  -- (iv) the last row's next is classifyFrom of the whole input; B2 exposes it as pi[FINAL]
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hlasteq : (traceRows t).getLast? = some (mkRow (t.rows.getLast hne)) := by
    rw [traceRows, List.getLast?_map, List.getLast?_eq_some_getLast hne]; rfl
  have hclass := lastNext_eq_classifyFrom (pinnedDfa (t.pub PI_INITIAL)) (t.pub PI_INITIAL)
    (traceRows t) htable hcont hhead (mkRow (t.rows.getLast hne)) hlasteq
  have hfinal := piLast_forces hsat hne mem_b2FinalPin
  rw [envAt_loc hlt] at hfinal
  rw [List.getLast_eq_getElem hne] at hclass
  refine ⟨htable, hhead, ?_⟩
  -- hclass : (t.rows[last]).next-column = classifyFrom d (pub INITIAL) (symbols …)
  -- hfinal : (t.rows[last]).next-column = pub FINAL
  have hkey : t.pub PI_FINAL
      = classifyFrom (pinnedDfa (t.pub PI_INITIAL)) (t.pub PI_INITIAL) (symbols (traceRows t)) := by
    rw [← hfinal]; exact hclass
  rw [hkey]
  rfl

/-- **The genuine-run CORE, UNCONDITIONAL (no terminal hypothesis).** From `Satisfied2` ALONE the
descriptor forces: the run starts at `pi[initial_state]` (B1), every NON-LAST row is a genuine toggle
transition, and the state threads across each window (continuity). This is the largest fragment the
descriptor's transition-zerofier lowering forces without a terminal obligation; the exposed final PI
= `classify(FULL input)` additionally needs `hterm` (the last row's transition gate), because that
gate is by design not re-asserted on the last row (`dfaRouting_refines_classify`). -/
theorem dfaRouting_genuine_prefix {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash dfaRoutingDesc minit mfin maddrs t) (hne : t.rows ≠ []) :
    (∀ r₀, (traceRows t).head? = some r₀ → r₀.state = t.pub PI_INITIAL) ∧
    (∀ i (hi : i < t.rows.length), i + 1 ≠ t.rows.length →
        (t.rows[i]'hi) NEXT = toggleStep ((t.rows[i]'hi) CURRENT) ((t.rows[i]'hi) SYMBOL)) ∧
    (∀ i (hi1 : i + 1 < t.rows.length),
        (t.rows[i + 1]'hi1) CURRENT = (t.rows[i]'(Nat.lt_of_succ_lt hi1)) NEXT) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r₀ hr₀
    simp only [traceRows, List.head?_map, Option.map_eq_some_iff] at hr₀
    obtain ⟨a, hah, rfl⟩ := hr₀
    show a CURRENT = t.pub PI_INITIAL
    have hpos := List.length_pos_of_ne_nil hne
    have h0 : t.rows[0]'hpos = a := by
      rw [List.head?_eq_some_head hne] at hah
      have hha : t.rows.head hne = a := Option.some.inj hah
      rw [← hha, List.head_eq_getElem hne]
    have hpf := piFirst_forces hsat hne mem_b1InitialPin
    rw [envAt_loc hpos, h0] at hpf; exact hpf
  · intro i hi hnl
    exact (transition_body_zero_iff (t.rows[i]'hi)).mp (gate_forces hsat hi hnl mem_transitionGate)
  · intro i hi1
    have hi : i < t.rows.length := Nat.lt_of_succ_lt hi1
    have hnl : i + 1 ≠ t.rows.length := Nat.ne_of_lt hi1
    have hc := (continuity_window_zero_iff (envAt t i)).mp
      (window_forces hsat hi hnl mem_continuityWindow rfl)
    rw [envAt_nxt hi1, envAt_loc hi] at hc; exact hc

/-! ## §6 — Non-vacuity: a concrete satisfying witness, a wrong run that fails, a discriminating
`classify`. -/

/-- A row from an explicit column-prefix list (off-the-end = 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

/-- Row 0: `IDLE=0 →symbol=1 1` (`current=0, symbol=1, next=1`, seed selector `is_first=1`; the hash
columns are `0`, and the chip lookups are witnessed by `witTf`). -/
def wr0 : Assignment := rowOf [0, 1, 1, 0, 0, 1, 0, 0]

/-- Row 1 (the last row): `1 →symbol=1 0` (`current=1` chains row 0's `next`, `symbol=1, next=0`). -/
def wr1 : Assignment := rowOf [1, 1, 0, 0, 0, 0, 0, 0]

/-- The evaluated entry-hash chip tuple of a row (what the lookup asserts is a table member). -/
def entryTupleAt (a : Assignment) : List ℤ :=
  (chipLookupTuple [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE] ENTRY_HASH ENTRY_LANES).map
    (·.eval a)

/-- The evaluated running-hash chip tuple of a row. -/
def runTupleAt (a : Assignment) : List ℤ :=
  (chipLookupTuple [.var ACC, .var ENTRY_HASH] RUNNING_HASH RUNNING_LANES).map (·.eval a)

/-- The witness trace family: the Poseidon2 chip table carries EXACTLY the two rows' entry/running
tuples (so both lookups hold on both rows); every other table is empty (no mem/map content). -/
def witTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [entryTupleAt wr0, runTupleAt wr0, entryTupleAt wr1, runTupleAt wr1]
  | _ => []

/-- The concrete 2-row toggle run `IDLE=0 →1 1 →1 0`, all public inputs `0`. -/
def witTrace : VmTrace := { rows := [wr0, wr1], pub := zeroAsg, tf := witTf }

/-- The abstract hash never enters the denotation (no hash sites / map ops), so any value serves. -/
def hash0 : List ℤ → ℤ := fun _ => 0

theorem memOpsOf_dfa : memOpsOf dfaRoutingDesc = [] := rfl
theorem mapOpsOf_dfa : mapOpsOf dfaRoutingDesc = [] := rfl
theorem memLog_dfa (t : VmTrace) : memLog dfaRoutingDesc t = [] := by
  simp [memLog, memOpsOf_dfa]
theorem mapLog_dfa (t : VmTrace) : mapLog dfaRoutingDesc t = [] := by
  simp [mapLog, mapOpsOf_dfa]

/-- **The witness PROVABLY satisfies the emitted descriptor.** Every row constraint holds (the two
lookups by membership in `witTf`, the per-row gates / windows on the non-last row, vacuous on the
last; the boundary pins), and the memory legs are the empty-log balance. -/
theorem witTrace_satisfies :
    Satisfied2 hash0 dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    clear hi
    rw [show witTrace.rows.length = 2 from rfl]
    simp only [dfaRoutingDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        WindowConstraint.holdsAt, entryHashLookup, runningHashLookup, zeroLaneGate, isFirstBoolGate,
        stateGridGate, symbolGridGate, transitionGate, continuityWindow, copyForwardWindow,
        b1InitialPin, isFirstPinned, seedAccPin, b2FinalPin, b3RoutePin, witTrace,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [dfaRoutingDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_dfa]; simp
  memDisciplined := by rw [memLog_dfa]; trivial
  memBalanced := by rw [memLog_dfa]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_dfa]; rfl
  mapTableFaithful := by rw [mapLog_dfa]; rfl

/-- The witness satisfies the terminal-step obligation: row 1 (the last row) IS a genuine toggle
transition `step(1,1) = 0`. -/
theorem witTrace_hterm :
    transitionBody.eval (witTrace.rows.getD (witTrace.rows.length - 1) zeroAsg) = 0 := by
  decide

/-- `classify` genuinely discriminates: `[1,1]` toggles `0→1→0` (LOCAL-reject), `[1]` toggles `0→1`
(accept) — so the bridge's conclusion is not a constant. -/
theorem classify_discriminates :
    classify (pinnedDfa 0) [1, 1] = 0 ∧ classify (pinnedDfa 0) [1] = 1 ∧
      classify (pinnedDfa 0) [1, 1] ≠ classify (pinnedDfa 0) [1] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The bridge FIRES on the witness (the true half of non-vacuity).** Feeding the concrete
satisfying trace + its terminal step to `dfaRouting_refines_classify` recovers the genuine
classification: the exposed final state `pi[FINAL] = 0` equals `classify (pinnedDfa 0) [1,1]`. -/
theorem witness_refines :
    witTrace.pub PI_FINAL = classify (pinnedDfa (witTrace.pub PI_INITIAL)) (symbols (traceRows witTrace)) :=
  (dfaRouting_refines_classify witTrace_satisfies (by decide) witTrace_hterm).2.2

/-- The recovered value is the concrete REMOTE-of-toggle endpoint `0`, over the read input `[1,1]`. -/
theorem witness_value : witTrace.pub PI_FINAL = 0 ∧ symbols (traceRows witTrace) = [1, 1] := by
  refine ⟨rfl, by decide⟩

/-- The wrong run: row 0 claims the FORBIDDEN toggle edge `step(0,1) = 0` (`next = 0`, not `1`). -/
def badRow0 : Assignment := rowOf [0, 1, 0, 0, 0, 1, 0, 0]

def badTrace : VmTrace :=
  { rows := [badRow0, wr1],
    pub := zeroAsg,
    tf := fun id => match id with
      | .poseidon2 => [entryTupleAt badRow0, runTupleAt badRow0, entryTupleAt wr1, runTupleAt wr1]
      | _ => [] }

/-- **A WRONG run PROVABLY fails the hypothesis (the false half of non-vacuity).** The row-0
transition gate (a non-last row) forces `next = step(0,1) = 1`, but `badTrace` claims `next = 0`, so
no `Satisfied2` witness exists — the descriptor's toggle tooth rejects the lie. -/
theorem badTrace_not_satisfied :
    ¬ Satisfied2 hash0 dfaRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  have h2 : transitionBody.eval badRow0 = 0 :=
    gate_forces (i := 0) h (by decide) (by decide) mem_transitionGate
  exact absurd h2 (by decide)

/-! ## §7 — Axiom tripwires. -/

#assert_axioms dfaRouting_refines_classify
#assert_axioms dfaRouting_genuine_prefix
#assert_axioms witTrace_satisfies
#assert_axioms witness_refines
#assert_axioms badTrace_not_satisfied
#assert_axioms classify_discriminates

end Dregg2.Circuit.Emit.DfaRoutingRefine
