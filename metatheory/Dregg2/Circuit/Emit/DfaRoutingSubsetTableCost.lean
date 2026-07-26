/-
# Dregg2.Circuit.Emit.DfaRoutingSubsetTableCost — the table-routing refinement holds over the
CHEAP (multiplicity-carrying, shared) table acceptance, not just the exact-multiset one.

**This is Lean-authored AIR metatheory.** It authors no new descriptor: it re-proves the EXISTING
emitted object's refinement (`DfaRoutingTableEmit.tableRouting_refines_classify`) from a STRICTLY
WEAKER acceptance predicate, which is what licenses a strictly cheaper prover shape.

## Why this file exists (the measured prover-cost finding it discharges)

The deployed `RowSemantics.exactPublicRows` carrier is a UNIT-CAPACITY LogUp receive per declared
row (`DescriptorIR2.PublicLookupBalanced`). The Rust assembly realizes that literally: every
declared manifest row becomes its OWN batch instance (`descriptor_ir2.rs::instance_airs`, the
`Ir2Air::ExactPublicRow` arm; `MAX_EXACT_PUBLIC_ROWS = 128`). Exact-multiset ⇒ the manifest must be
the exact multiset of queries ⇒ for a `k`-fold automaton over an `n`-symbol word the batch carries
`1 + k·n` instances. MEASURED (`circuit/tests/tiny_automata_prover_shape_measure.rs`, production
`ir2_config`): +1.76 KiB of wire and +0.15 ms of single-thread prover CPU per declared row, so
composition costs +28.1 KiB and +2.43 ms per additional automaton at `n = 16` — and `k·n ≤ 128`
is a hard wall.

A shared, multiplicity-carrying table (the mechanism the byte/range table already uses:
ONE table AIR of height `2^⌈log₂|T|⌉`, `LookupBus::table_entry(.., multiplicity)`, and one
unit-capacity `lookup_key` per query) costs instead +1.06 KiB and +0.26 ms per additional
automaton — 26x / 9x cheaper, with no cap.

The question this file answers is the SOUNDNESS question that switch raises: the cheap table gives
up `PublicLookupBalanced` (exact multiset) and keeps only membership + contents-commitment. Is the
refinement still true? **Yes, and the existing proof never used the exactness leg.** So the
weakening is free: `tableRouting_refines_classify_subset` derives the SAME conclusion (`final_state
= classifyFrom d q0 word`) from `Satisfied2Subset`, and `tableRouting_refines_classify` falls out as
a corollary. Both tamper canaries still REFUSE under the weaker hypothesis, so the weakening is not
a laundering: the transition tooth and the boundary pin both still bite.

What `PublicLookupBalanced` does buy is WITNESS EXISTENCE bookkeeping (a run that reuses a
transition has no witness unless the manifest matches its usage) — the residual
`DfaRoutingTableEmit` already names. That bookkeeping is exactly what the measured cost is paid
for, and this file shows nothing in the refinement rests on it.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports are
read-only, and it is deliberately NOT registered in `Dregg2.lean` (a cost-analysis leaf).
-/
import Dregg2.Circuit.Emit.DfaRoutingTableEmit

namespace Dregg2.Circuit.Emit.DfaRoutingSubsetTableCost

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
open Dregg2.Crypto.DfaAcceptanceAir
  (TableDfa Row classifyFrom symbols lastNext_eq_classifyFrom)

set_option autoImplicit false

/-! ## §1 — the CHEAP acceptance predicate.

`Satisfied2Subset` is `Satisfied2` plus table-contents commitment ONLY: every declared table's
contents are exactly the descriptor-carried rows, and every row-local lookup is a MEMBER of that
table (`Satisfied2.rowConstraints` at a `.lookup`). It drops `PublicLookupBalanced` — the
exact-multiset permutation leg that forces one unit-capacity receive per declared row.

This is the denotation of the cheap deployed shape: one shared table AIR whose rows are pinned to
the descriptor bytes and whose LogUp `table_entry` carries a MULTIPLICITY column (any number of
queries may hit the same row), which is precisely the byte/range table's mechanism. -/
structure Satisfied2Subset (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Prop extends Satisfied2 hash d minit mfin maddrs t where
  publicTablesFaithful : PublicTablesFaithful d t

/-- The DEPLOYED exact-public acceptance IMPLIES the cheap one: `Satisfied2Subset` is a genuine
weakening, so every theorem proved over it is at least as strong as the same theorem over
`Satisfied2Public`. -/
theorem ofPublic {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Public hash d minit mfin maddrs t) :
    Satisfied2Subset hash d minit mfin maddrs t :=
  { toSatisfied2 := h.toSatisfied2, publicTablesFaithful := h.publicTablesFaithful }

/-! ## §2 — the extraction lemmas, restated over the WEAKER hypothesis.

Each is the `DfaRoutingTableEmit` lemma with `Satisfied2Public` replaced by `Satisfied2Subset`.
The proofs are unchanged, which is the point: not one of them ever mentioned
`publicLookupBalanced`. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
variable {name : String} {tbl : List (List Nat)} {t : VmTrace}

/-- The declared table is the trace's table (contents commitment alone). -/
theorem tf_pinned (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t) :
    t.tf TRT_TID = exactPublicTable tbl := by
  have h := hsat.publicTablesFaithful (transitionTableDef tbl)
    (by simp [tableRoutingDesc])
  simpa [TableDef.publicContentsFaithful, transitionTableDef] using h

/-- Every row's `(current, symbol, next)` is a declared table row — MEMBERSHIP, on every row. -/
theorem row_triple (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    [(t.rows[i]'hi) CURRENT, (t.rows[i]'hi) SYMBOL, (t.rows[i]'hi) NEXT]
      ∈ exactPublicTable tbl := by
  have hrow := hsat.rowConstraints i hi _ mem_transitionLookup
  rw [← tf_pinned hsat]
  have hl : (envAt t i).loc = t.rows[i]'hi := envAt_loc hi
  simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, transitionLookup, List.map,
    EmittedExpr.eval, hl] using hrow

/-- Every row reads a genuine step-graph entry (exact ℤ equalities, no mod-`p` envelope). -/
theorem row_reads (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s, y, d.step s y])
    (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t)
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
theorem window_forces
    (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length) :
    contWindowBody.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i hi _ mem_continuityWindow
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, continuityWindow, WindowConstraint.holdsAt, if_true] at hrc
  exact hrc hlf

/-- B1 fires on the first row. -/
theorem piFirst_forces
    (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    (envAt t 0).loc CURRENT ≡ t.pub PI_INITIAL [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrc := hsat.rowConstraints 0 hpos _ mem_b1InitialPin
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) CURRENT PI_INITIAL).mp hrc

/-- B2 fires on the last row. -/
theorem piLast_forces
    (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t)
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

/-! ## §3 — THE REFINEMENT OVER THE CHEAP ACCEPTANCE. -/

/-- **`tableRouting_refines_classify_subset` — the refinement needs only MEMBERSHIP + CONTENTS
COMMITMENT.** For ANY declared table `tbl` whose rows are step-graph entries of `d`, with all
entries `< p`: a trace satisfying the emitted `tableRoutingDesc name tbl` under the CHEAP
acceptance `Satisfied2Subset` (no exact-multiset leg — the shared, multiplicity-carrying table
shape) reads a genuine ℕ-word off its symbol column and its exposed public `final_state` IS
`classifyFrom d initial_state` of that word.

The proof is the `DfaRoutingTableEmit` proof verbatim against the restated §2 lemmas: the
exact-multiset leg was never load-bearing for soundness. -/
theorem tableRouting_refines_classify_subset
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s, y, d.step s y])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (hsat : Satisfied2Subset hash (tableRoutingDesc name tbl) minit mfin maddrs t)
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

/-- **Nothing is lost**: the DEPLOYED exact-public refinement is a COROLLARY of the cheap one.
So moving the emit path onto a shared multiplicity-carrying table strictly weakens the
prover's obligation while preserving the classification theorem word for word. -/
theorem tableRouting_refines_classify_of_public
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s, y, d.step s y])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (q0 : ℕ) (hstart : t.pub PI_INITIAL = Int.ofNat q0) (hq0 : q0 < 2013265921)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    fN = classifyFrom d q0 (t.rows.map (fun a => (a SYMBOL).toNat)) :=
  (tableRouting_refines_classify_subset d htbl hsmall (ofPublic hsat) hne q0 hstart hq0
    fN hfin hfN).2

/-! ## §4 — the weakening keeps BOTH teeth (it is not a laundering).

The concrete witness still satisfies the cheap acceptance and still FIRES the refinement; both
`DfaRoutingTableEmit` tamper canaries still REFUSE under the WEAKER hypothesis. A forged
transition and a forged `final_state` are both excluded WITHOUT the exact-multiset leg. -/

/-- The concrete witness satisfies the CHEAP acceptance. -/
theorem routeWit_satisfies_subset :
    Satisfied2Subset hash0 demoRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] routeWitTrace :=
  ofPublic routeWit_satisfies

/-- The refinement FIRES on the witness under the CHEAP acceptance. -/
theorem witness_classifies_subset :
    (1 : ℕ) = classifyFrom demoDfa 0 (routeWitTrace.rows.map (fun a => (a SYMBOL).toNat)) :=
  (tableRouting_refines_classify_subset demoDfa demoTbl_graph demoTbl_small
    routeWit_satisfies_subset (List.cons_ne_nil _ _) 0 rfl (by decide) 1 rfl (by decide)).2

/-- **Canary 1 still bites**: a claimed transition NOT in the declared table is refused by the
CHEAP acceptance too — membership + contents commitment alone suffice. -/
theorem badTrace_not_subset_satisfied :
    ¬ Satisfied2Subset (fun _ => 0) demoRoutingDesc (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  have hm := row_triple h (i := 0) (by decide)
  revert hm
  decide

/-- **Canary 2 still bites**: a forged public `final_state` is refused by the CHEAP acceptance
too — B2 is a row constraint, untouched by the multiset leg. -/
theorem mutFin_not_subset_satisfied :
    ¬ Satisfied2Subset (fun _ => 0) demoRoutingDesc (fun _ => 0) (fun _ => (0, 0)) []
        mutFinTrace := by
  intro h
  have hpl := piLast_forces h (List.cons_ne_nil _ _)
  have he : (envAt mutFinTrace (mutFinTrace.rows.length - 1)).loc NEXT = 1 := rfl
  have hp : mutFinTrace.pub PI_FINAL = 0 := rfl
  rw [he, hp] at hpl
  obtain ⟨k, hk⟩ := hpl.dvd
  omega

/-! ## §5 — axiom tripwires. -/

#assert_axioms tableRouting_refines_classify_subset
#assert_axioms tableRouting_refines_classify_of_public
#assert_axioms ofPublic
#assert_axioms row_reads
#assert_axioms witness_classifies_subset
#assert_axioms badTrace_not_subset_satisfied
#assert_axioms mutFin_not_subset_satisfied

end Dregg2.Circuit.Emit.DfaRoutingSubsetTableCost
