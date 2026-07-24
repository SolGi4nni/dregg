/-
# Dregg2.Circuit.Emit.DfaRoutingTableEmit — the TABLE-AS-INPUT DFA-routing descriptor family,
with a refinement GENERAL over an arbitrary transition table (the M1 general DFA-refine).

**This is Lean-authored AIR.** The descriptor family is authored here; the wire bytes of the
concrete instance are byte-pinned by an `emitVmJson2` `#guard`; the refinement is a
`Satisfied2Public <emitted-descriptor> ⟹ classify` theorem over the EMITTED object, general over
the table. Rust parses the emitted IR2 bytes (`descriptor_ir2.rs::parse`, the
`exact_public_rows` arm) and supplies witnesses; it authors nothing.

## Why this file exists (the M0 finding it closes)

The emitted DFA-routing descriptors `DfaRoutingEmit.lean` (toggle) and `DfaRoutingGeneralEmit.lean`
(injection) HARDCODE a per-automaton transition-interpolant gate, and their refinements
(`DfaRoutingRefine.dfaRouting_refines_classify:322`) are per-automaton. No refinement existed that
is general over an ARBITRARY table — which is exactly what welding a guard-DFA leg under an
arbitrary template guard `g` needs (`GuardedHidingSpanRefine.lean` §"The guard obligation": the
hGuard floor). This file supplies the general object:

  * **`tableRoutingDesc name tbl`** — a descriptor FAMILY taking the transition table as INPUT
    (the Lean counterpart of `circuit/src/dsl/dfa_routing.rs::dfa_routing_descriptor`'s
    table-as-input shape): the table rides as a DECLARED `exactPublicRows` table (its complete
    row list is committed by the descriptor bytes themselves — stronger identity-binding than the
    single-felt `compute_table_commitment` seed, which is the narrow lane-0 legacy), and the
    transition tooth is ONE table-generic lookup `(current, symbol, next) ∈ table` — no
    per-automaton interpolant at all.

  * **`tableRouting_refines_classify`** — the GENERAL refinement: for ANY table `tbl` whose rows
    are graph entries of a step function `d.step` (`htbl`), a trace satisfying the emitted
    descriptor (via the deployed exact-public acceptance predicate `Satisfied2Public`) reads a
    genuine ℕ-word off its symbol column and its exposed public `final_state` IS
    `classifyFrom d initial_state` of that word. Welded to the untouched model
    `Dregg2.Crypto.DfaAcceptanceAir.lastNext_eq_classifyFrom`.

## Why the lookup carrier needs NO terminal-step hypothesis and NO grid gates

`DfaRoutingRefine` carries `hterm` (the transition-zerofier lowering leaves the LAST row's gate
unasserted) and a canonicality envelope + grid gates (gates pin only `≡ 0 [ZMOD p]`). The lookup
carrier is stronger on both axes: a `lookup` is enforced on EVERY row including the last
(`VmConstraint2.holdsAt` has no `isLast` guard on lookups — the LogUp argument is row-uniform),
and membership in `exactPublicTable tbl` is an EXACT ℤ equality with `Int.ofNat` images, so the
three DFA cells are genuine naturals with no mod-`p` reading needed. Only the two boundary PI pins
and the continuity window remain field congruences; they collapse to ℕ equalities under the
table-entry bound `hsmall : entries < p` and the PI canonicality bounds (`hq0`/`hfN`).

## Honest residuals (named, not laundered)

  * **Exact-multiset completeness.** `exactPublicRows` is a UNIT-CAPACITY LogUp receive
    (`PublicLookupBalanced`): a satisfying witness must consume the declared row multiset
    EXACTLY. A run that reuses a transition (or skips one) has no witness unless the declared
    multiset matches its usage. This restricts witness EXISTENCE, not soundness (the refinement
    consumes only `rowConstraints` + `publicTablesFaithful`); a multiplicity-liberal public
    membership table semantics is the named deployment gap for multi-use words.
  * **Wire width of ids.** The Rust side parses table rows as BabyBear, so ids `≥ p` alias on the
    wire. The refinement carries `hsmall` (all entries `< p`) to stay like-for-like; an encoder
    whose ids exceed `p` (e.g. the proven-injective `Poseidon2Binding.Reference.encV`) is NOT
    wire-faithful — see `GuardedHidingSpanGuardWeld.lean`'s residual note.
  * The `Satisfied2Public` model-vs-deployed-field status is the standing one shared by every
    sibling refinement (the Lean denotation is the model of the deployed LogUp/AIR; no claim past
    that resolution — a STARK proves the TRACE, and the FRI floor is undischarged).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Crypto.DfaAcceptanceAir

namespace Dregg2.Circuit.Emit.DfaRoutingTableEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.DfaAcceptanceAir
  (TableDfa Row classifyFrom symbols lastNext_eq_classifyFrom)

set_option autoImplicit false

/-! ## §1 — the trace column layout (3 columns) and PI slots (2). -/

/-- `current_state` — the DFA state entering this step. -/
def CURRENT : Nat := 0
/-- `symbol` — the input symbol id read at this step. -/
def SYMBOL : Nat := 1
/-- `next_state` — the DFA state after this step. -/
def NEXT : Nat := 2
/-- Total main-trace width. -/
def TRT_WIDTH : Nat := 3

/-- pi[0] `initial_state`. -/
def PI_INITIAL : Nat := 0
/-- pi[1] `final_state` (the classification). -/
def PI_FINAL : Nat := 1
/-- Number of public inputs. -/
def TRT_PI_COUNT : Nat := 2

/-- The declared transition table's id (`.custom 30`, wire id `35` — unclaimed in the tree). -/
def TRT_TID : TableId := .custom 30

/-! ## §2 — the constraints: ONE table-generic lookup + continuity + the two boundary pins. -/

/-- The declared transition table: arity-3 rows `(state, symbol, next)`, its COMPLETE row list
committed by the descriptor bytes (`exactPublicRows` — the verifier-known finite multiset). -/
def transitionTableDef (tbl : List (List Nat)) : TableDef :=
  ⟨TRT_TID, "dfa_transition_table", 3, .exactPublicRows tbl⟩

/-- **THE table-as-input transition tooth**: `(current, symbol, next)` is a ROW of the declared
table. Table-generic — no per-automaton interpolant; enforced on EVERY row (lookups carry no
transition-zerofier guard). -/
def transitionLookup : VmConstraint2 :=
  .lookup ⟨TRT_TID, [.var CURRENT, .var SYMBOL, .var NEXT]⟩

/-- C2 continuity body: `Nxt(current) − Loc(next)`. -/
def contWindowBody : WindowExpr := .add (.nxt CURRENT) (.mul (.const (-1)) (.loc NEXT))

/-- The C2 continuity `WindowGate`, asserted on the transition (every row but the last). -/
def continuityWindow : VmConstraint2 := .windowGate ⟨contWindowBody, true⟩

/-- B1: first row `current_state == pi[initial_state]`. -/
def b1InitialPin : VmConstraint2 := .base (.piBinding VmRow.first CURRENT PI_INITIAL)

/-- B2: last row `next_state == pi[final_state]` (the classification). -/
def b2FinalPin : VmConstraint2 := .base (.piBinding VmRow.last NEXT PI_FINAL)

/-- **`tableRoutingDesc name tbl`** — the table-as-input DFA-routing descriptor family: the
transition table declared as an `exactPublicRows` table, one table-generic transition lookup, the
continuity window, and the two boundary pins. -/
def tableRoutingDesc (name : String) (tbl : List (List Nat)) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := TRT_WIDTH
  , piCount     := TRT_PI_COUNT
  , tables      := [transitionTableDef tbl]
  , constraints := [transitionLookup, continuityWindow, b1InitialPin, b2FinalPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — constraint presence + the pinned table contents. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
variable {name : String} {tbl : List (List Nat)} {t : VmTrace}

theorem mem_transitionLookup : transitionLookup ∈ (tableRoutingDesc name tbl).constraints :=
  List.mem_cons_self

theorem mem_continuityWindow : continuityWindow ∈ (tableRoutingDesc name tbl).constraints :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_b1InitialPin : b1InitialPin ∈ (tableRoutingDesc name tbl).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem mem_b2FinalPin : b2FinalPin ∈ (tableRoutingDesc name tbl).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- `getD` on an in-bounds index is `getElem`. -/
theorem getD_row {i : Nat} (hi : i < t.rows.length) : t.rows.getD i zeroAsg = t.rows[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The current-row environment's `loc` is the trace row (in-bounds). -/
theorem envAt_loc {i : Nat} (hi : i < t.rows.length) : (envAt t i).loc = t.rows[i]'hi :=
  getD_row hi

/-- The current-row environment's `nxt` is the next trace row (in-bounds). -/
theorem envAt_nxt {i : Nat} (hi : i + 1 < t.rows.length) : (envAt t i).nxt = t.rows[i + 1]'hi :=
  getD_row hi

/-- **The declared table is the trace's table** — the exact-public faithfulness leg pins the
prover-supplied `tf` at `TRT_TID` to the DESCRIPTOR-committed rows. -/
theorem tf_pinned (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t) :
    t.tf TRT_TID = exactPublicTable tbl := by
  have h := hsat.publicTablesFaithful (transitionTableDef tbl)
    (by simp [tableRoutingDesc])
  simpa [TableDef.publicContentsFaithful, transitionTableDef] using h

/-- **Every row's `(current, symbol, next)` is a declared table row** — the transition lookup +
the pinned table contents, on EVERY row (no last-row exemption: lookups carry no zerofier). -/
theorem row_triple (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    [(t.rows[i]'hi) CURRENT, (t.rows[i]'hi) SYMBOL, (t.rows[i]'hi) NEXT]
      ∈ exactPublicTable tbl := by
  have hrow := hsat.rowConstraints i hi _ mem_transitionLookup
  rw [← tf_pinned hsat]
  have hl : (envAt t i).loc = t.rows[i]'hi := envAt_loc hi
  simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, transitionLookup, List.map,
    EmittedExpr.eval, hl] using hrow

/-- **Every row reads a genuine step-graph entry**: under `htbl` (every declared row is a graph
entry of `d.step`), the row's cells are `Int.ofNat` images of `(s, y, d.step s y)` — EXACT ℤ
equalities, no mod-`p` envelope. -/
theorem row_reads (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s, y, d.step s y])
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    ∃ s y : ℕ, [s, y, d.step s y] ∈ tbl
      ∧ (t.rows[i]'hi) CURRENT = Int.ofNat s
      ∧ (t.rows[i]'hi) SYMBOL = Int.ofNat y
      ∧ (t.rows[i]'hi) NEXT = Int.ofNat (d.step s y) := by
  have h := row_triple hsat hi
  simp only [exactPublicTable, List.mem_map] at h
  obtain ⟨r, hr, hmap⟩ := h
  obtain ⟨s, y, rfl⟩ := htbl r hr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
  exact ⟨s, y, hr, hmap.1.symm, hmap.2.1.symm, hmap.2.2.symm⟩

/-- The continuity window forces its body ≡ 0 mod `p` on a NON-LAST row. -/
theorem window_forces (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length) :
    contWindowBody.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i hi _ mem_continuityWindow
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, continuityWindow, WindowConstraint.holdsAt, if_true] at hrc
  exact hrc hlf

/-- B1 fires on the first row (mod `p` — the field-faithful pin). -/
theorem piFirst_forces (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    (envAt t 0).loc CURRENT ≡ t.pub PI_INITIAL [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrc := hsat.rowConstraints 0 hpos _ mem_b1InitialPin
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) CURRENT PI_INITIAL).mp hrc

/-- B2 fires on the last row (mod `p` — the field-faithful pin). -/
theorem piLast_forces (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    (envAt t (t.rows.length - 1)).loc NEXT ≡ t.pub PI_FINAL [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ mem_b2FinalPin
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_piLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0)
    NEXT PI_FINAL).mp hrc

end Extract

/-! ## §4 — collapsing the two remaining congruences: canonical naturals below `p` are equal. -/

/-- Two naturals `< p`, congruent as integers mod `p`, are EQUAL. -/
theorem ofNat_eq_of_modEq {a b : ℕ} (ha : a < 2013265921) (hb : b < 2013265921)
    (h : (Int.ofNat a) ≡ (Int.ofNat b) [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  simp only [Int.ofNat_eq_natCast] at hk
  omega

/-- The continuity congruence over two ℕ-valued cells `< p` IS the ℕ equality. -/
theorem cont_eq {env : VmRowEnv} (h : contWindowBody.eval env ≡ 0 [ZMOD 2013265921])
    {x y : ℕ} (hx : env.nxt CURRENT = Int.ofNat x) (hy : env.loc NEXT = Int.ofNat y)
    (hxlt : x < 2013265921) (hylt : y < 2013265921) : x = y := by
  simp only [contWindowBody, WindowExpr.eval] at h
  rw [hx, hy] at h
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
  simp only [Int.ofNat_eq_natCast] at hk
  omega

/-! ## §5 — the model reading and the GENERAL refinement. -/

/-- One trace row read as a model `Row ℕ ℕ` (digest fields inert). -/
def mkRowN (a : Assignment) : Row Nat Nat ℤ :=
  { state := (a CURRENT).toNat, sym := (a SYMBOL).toNat, next := (a NEXT).toNat
  , entryHash := 0, running := 0 }

/-- The whole trace as a model run. -/
def traceRowsN (t : VmTrace) : List (Row Nat Nat ℤ) := t.rows.map mkRowN

/-- Index-adjacent chaining of the read naturals gives the model's `Continuous`. -/
theorem continuous_of_chain : ∀ (l : List Assignment),
    (∀ i (_ : i + 1 < l.length), ((l[i + 1]) CURRENT).toNat = ((l[i]) NEXT).toNat) →
    Dregg2.Crypto.DfaAcceptanceAir.Continuous (l.map mkRowN)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h => by
      refine ⟨?_, continuous_of_chain (b :: rest) (fun i hi => ?_)⟩
      · have h0 := h 0 (by simp)
        simpa [mkRowN] using h0
      · have hh := h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa using hh

/-- **`tableRouting_refines_classify` — the GENERAL table-as-input refinement (the object the M0
report found missing).** For ANY declared table `tbl` whose rows are step-graph entries of `d`
(`htbl`), with all entries `< p` (`hsmall`): a trace satisfying the emitted
`tableRoutingDesc name tbl` (deployed exact-public acceptance `Satisfied2Public`), non-empty, with
canonical public `initial_state = q0` and `final_state = fN`, reads a genuine ℕ-word `ws` off its
symbol column (the column IS `ws.map Int.ofNat` — exact, no envelope) and

    `fN = classifyFrom d q0 ws`

— the exposed final state is the genuine deterministic classification. NO terminal-step
hypothesis (lookups have no last-row exemption) and NO grid/canonicality envelope on trace cells
(table membership is exact). General over `tbl`, `d`, `name`. -/
theorem tableRouting_refines_classify
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s, y, d.step s y])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (q0 : ℕ) (hstart : t.pub PI_INITIAL = Int.ofNat q0) (hq0 : q0 < 2013265921)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    t.rows.map (fun a => a SYMBOL)
        = (t.rows.map (fun a => (a SYMBOL).toNat)).map Int.ofNat
      ∧ fN = classifyFrom d q0 (t.rows.map (fun a => (a SYMBOL).toNat)) := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  -- (i) the symbol column is a genuine ℕ-word
  have hcol : t.rows.map (fun a => a SYMBOL)
      = (t.rows.map (fun a => (a SYMBOL).toNat)).map Int.ofNat := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨s, y, _, _, hsym, _⟩ := row_reads d htbl hsat hi
    simp [Function.comp, hsym]
  refine ⟨hcol, ?_⟩
  -- (ii) every read row is a genuine table transition
  have htable : ∀ r ∈ traceRowsN t, r.next = d.step r.state r.sym := by
    intro r hr
    simp only [traceRowsN, List.mem_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨s, y, _, hcur, hsym, hnext⟩ := row_reads d htbl hsat hi
    simp [mkRowN, hcur, hsym, hnext]
  -- (iii) continuity threads the read naturals across each window
  have hcont : Dregg2.Crypto.DfaAcceptanceAir.Continuous (traceRowsN t) := by
    apply continuous_of_chain
    intro i hi1
    have hi : i < t.rows.length := Nat.lt_of_succ_lt hi1
    have hnl : i + 1 ≠ t.rows.length := Nat.ne_of_lt hi1
    obtain ⟨s', y', hmem', hcur', _, _⟩ := row_reads d htbl hsat hi1
    obtain ⟨s, y, hmem, _, _, hnext⟩ := row_reads d htbl hsat hi
    have hw := window_forces hsat hi hnl
    have hx : (envAt t i).nxt CURRENT = Int.ofNat s' := by rw [envAt_nxt hi1]; exact hcur'
    have hy : (envAt t i).loc NEXT = Int.ofNat (d.step s y) := by rw [envAt_loc hi]; exact hnext
    have heq := cont_eq hw hx hy
      (hsmall _ hmem' _ (by simp)) (hsmall _ hmem _ (by simp))
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
    obtain ⟨s, y, hmem, hcur, _, _⟩ := row_reads d htbl hsat hpos
    have hpf := piFirst_forces hsat hne
    rw [envAt_loc hpos, hcur, hstart] at hpf
    have hs : s = q0 := ofNat_eq_of_modEq (hsmall _ hmem _ (by simp)) hq0 hpf
    show (a CURRENT).toNat = q0
    rw [← h0, hcur, hs]
    rfl
  -- (v) the last row's next is classifyFrom of the whole read word; B2 exposes it as pi[FINAL]
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hlast? : (traceRowsN t).getLast? = some (mkRowN (t.rows.getLast hne)) := by
    rw [traceRowsN, List.getLast?_map, List.getLast?_eq_some_getLast hne]
    rfl
  have hclass := lastNext_eq_classifyFrom d q0 (traceRowsN t) htable hcont hhead _ hlast?
  have hsymbols : symbols (traceRowsN t) = t.rows.map (fun a => (a SYMBOL).toNat) := by
    simp only [symbols, traceRowsN, List.map_map]
    rfl
  obtain ⟨sL, yL, hmemL, _, _, hnextL⟩ := row_reads d htbl hsat hlt
  have hpl := piLast_forces hsat hne
  rw [envAt_loc hlt, hnextL, hfin] at hpl
  have hfEq : d.step sL yL = fN :=
    ofNat_eq_of_modEq (hsmall _ hmemL _ (by simp)) hfN hpl
  have hlastRow : (mkRowN (t.rows.getLast hne)).next = d.step sL yL := by
    show ((t.rows.getLast hne) NEXT).toNat = d.step sL yL
    rw [List.getLast_eq_getElem hne, hnextL]
    rfl
  rw [hsymbols] at hclass
  rw [← hfEq, ← hlastRow]
  exact hclass

/-! ## §6 — the concrete pinned instance (the byte-pinned wire golden the demo + the guard weld
ride). One transition `(0, 1, 1)`. -/

/-- The concrete demo table: the single transition `state 0 --symbol 1--> state 1`. -/
def demoTbl : List (List Nat) := [[0, 1, 1]]

/-- The pinned instance name. -/
def DEMO_NAME : String := "dregg-dfa-routing-table::exact-public-v1"

/-- The pinned concrete descriptor instance. -/
def demoRoutingDesc : EffectVmDescriptor2 := tableRoutingDesc DEMO_NAME demoTbl

-- THE WIRE GOLDEN: byte-pinned (the Rust `parse` ingests THIS string; `exact_public_rows` arm).
#guard emitVmJson2 demoRoutingDesc ==
  "{\"name\":\"dregg-dfa-routing-table::exact-public-v1\",\"ir\":2,\"trace_width\":3,\"public_input_count\":2,\"tables\":[{\"id\":35,\"name\":\"dfa_transition_table\",\"arity\":3,\"sem\":\"exact_public_rows\",\"rows\":[[0,1,1]]}],\"constraints\":[{\"t\":\"lookup\",\"table\":35,\"tuple\":[{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

-- Shape pins.
#guard demoRoutingDesc.traceWidth == TRT_WIDTH
#guard demoRoutingDesc.piCount == TRT_PI_COUNT
#guard demoRoutingDesc.constraints.length == 4
#guard demoRoutingDesc.tables.length == 1

/-! ## §7 — NON-VACUITY: a concrete satisfying witness FIRES the general refinement; two tamper
canaries REFUSE. -/

/-- The step function whose graph `demoTbl` samples (`step 0 1 = 1`; total). -/
def demoDfa : TableDfa Nat Nat :=
  { step := fun _ _ => 1, start := 0, accepts := fun s => s = 1 }

theorem demoTbl_graph : ∀ r ∈ demoTbl, ∃ s y, r = [s, y, demoDfa.step s y] := by
  intro r hr
  simp only [demoTbl, List.mem_singleton] at hr
  exact ⟨0, 1, hr⟩

theorem demoTbl_small : ∀ r ∈ demoTbl, ∀ v ∈ r, v < 2013265921 := by decide

/-- The single witness row: `(current, symbol, next) = (0, 1, 1)`. -/
def wRow : Assignment := fun c => if c = 1 then 1 else if c = 2 then 1 else 0

/-- The witness public inputs: `initial_state = 0`, `final_state = 1`. -/
def wPub : Assignment := fun k => if k = 1 then 1 else 0

/-- The witness trace family: the declared table at `TRT_TID`, empty elsewhere. -/
def wTf : TraceFamily := fun id => if id = TRT_TID then exactPublicTable demoTbl else []

/-- The one-row witness trace. -/
def routeWitTrace : VmTrace := { rows := [wRow], pub := wPub, tf := wTf }

theorem memOpsOf_trt : memOpsOf demoRoutingDesc = [] := rfl
theorem mapOpsOf_trt : mapOpsOf demoRoutingDesc = [] := rfl
theorem memLog_trt (t : VmTrace) : memLog demoRoutingDesc t = [] := by
  simp [memLog, memOpsOf_trt]
theorem mapLog_trt (t : VmTrace) : mapLog demoRoutingDesc t = [] := by
  simp [mapLog, mapOpsOf_trt]

/-- The abstract hash never enters this descriptor's denotation (no hash sites / map ops). -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- **The witness PROVABLY satisfies the emitted instance** under the exact-public acceptance:
the lookup by declared membership, the window vacuous on the last row, both pins by equality,
empty memory legs, the declared table faithful, and the LogUp exact-multiset balanced (the one
declared row consumed exactly once). -/
theorem routeWit_satisfies :
    Satisfied2Public hash0 demoRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] routeWitTrace where
  rowConstraints := by
    intro i hi c hc
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [routeWitTrace] using hi
      omega
    subst hi0
    simp only [demoRoutingDesc, tableRoutingDesc, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · show _ ∈ routeWitTrace.tf TRT_TID
      decide
    · show WindowConstraint.holdsAt _ (0 + 1 == routeWitTrace.rows.length) _
      simp only [WindowConstraint.holdsAt, if_true]
      intro h
      exact absurd h (by decide)
    · exact (holdsVm_piFirst_true (envAt routeWitTrace 0)
        (0 + 1 == routeWitTrace.rows.length) CURRENT PI_INITIAL).mpr rfl
    · have h := (holdsVm_piLast_true (envAt routeWitTrace 0) (0 == 0) NEXT PI_FINAL).mpr rfl
      exact h
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [demoRoutingDesc, tableRoutingDesc,
    List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_trt]; simp
  memDisciplined := by rw [memLog_trt]; trivial
  memBalanced := by rw [memLog_trt]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_trt]; rfl
  mapTableFaithful := by rw [mapLog_trt]; rfl
  publicTablesFaithful := by
    intro td htd
    simp only [demoRoutingDesc, tableRoutingDesc, List.mem_singleton] at htd
    subst htd
    show routeWitTrace.tf TRT_TID = exactPublicTable demoTbl
    rfl
  publicLookupBalanced := by
    intro td htd
    simp only [demoRoutingDesc, tableRoutingDesc, List.mem_singleton] at htd
    subst htd
    show (lookupLog demoRoutingDesc routeWitTrace TRT_TID).Perm (exactPublicTable demoTbl)
    have h : lookupLog demoRoutingDesc routeWitTrace TRT_TID = exactPublicTable demoTbl := by
      decide
    rw [h]

/-- **The refinement FIRES on the witness (the true half of non-vacuity):** the exposed
`final_state = 1` IS `classifyFrom demoDfa 0 [1]` — the genuine one-step classification of the
read word. -/
theorem witness_classifies :
    (1 : ℕ) = classifyFrom demoDfa 0 (routeWitTrace.rows.map (fun a => (a SYMBOL).toNat)) :=
  (tableRouting_refines_classify demoDfa demoTbl_graph demoTbl_small routeWit_satisfies
    (List.cons_ne_nil _ _) 0 rfl (by decide) 1 rfl (by decide)).2

/-- Sanity: the read word is `[1]` and `classifyFrom demoDfa 0 [1] = 1`. -/
theorem witness_word : routeWitTrace.rows.map (fun a => (a SYMBOL).toNat) = [1]
    ∧ classifyFrom demoDfa 0 [1] = 1 := by
  exact ⟨rfl, rfl⟩

/-! ### Canary 1 — a claimed transition NOT in the declared table is REFUSED. -/

/-- The forged row: claims `(0, 1) → 0`, an edge the declared table does not carry. -/
def badRow : Assignment := fun c => if c = 1 then 1 else 0

def badTrace : VmTrace := { rows := [badRow], pub := wPub, tf := wTf }

/-- **A non-table transition PROVABLY fails `Satisfied2Public`.** The table-as-input lookup
forces the row's triple `(0,1,0)` to be a DECLARED row; `demoTbl` carries only `(0,1,1)` — the
tooth bites on the last (here: only) row, with no zerofier exemption. -/
theorem badTrace_not_satisfied :
    ¬ Satisfied2Public (fun _ => 0) demoRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  have hm := row_triple h (i := 0) (by decide)
  revert hm
  decide

/-! ### Canary 2 — a forged public `final_state` is REFUSED. -/

/-- The honest row with a FORGED `final_state` public input (`pi[1] = 0`, genuine next = 1). -/
def mutFinTrace : VmTrace := { rows := [wRow], pub := fun _ => 0, tf := wTf }

/-- **A forged `final_state` PROVABLY fails `Satisfied2Public`.** B2 pins the genuine last-row
`next = 1` to the forged `pi[final_state] = 0`; `1 ≢ 0 [ZMOD p]`. -/
theorem mutFin_not_satisfied :
    ¬ Satisfied2Public (fun _ => 0) demoRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] mutFinTrace := by
  intro h
  have hpl := piLast_forces h (List.cons_ne_nil _ _)
  have he : (envAt mutFinTrace (mutFinTrace.rows.length - 1)).loc NEXT = 1 := rfl
  have hp : mutFinTrace.pub PI_FINAL = 0 := rfl
  rw [he, hp] at hpl
  obtain ⟨k, hk⟩ := hpl.dvd
  omega

/-! ## §8 — axiom tripwires. -/

#assert_axioms tableRouting_refines_classify
#assert_axioms row_reads
#assert_axioms routeWit_satisfies
#assert_axioms witness_classifies
#assert_axioms badTrace_not_satisfied
#assert_axioms mutFin_not_satisfied

end Dregg2.Circuit.Emit.DfaRoutingTableEmit
