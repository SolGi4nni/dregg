/-

⚠ SCOPE CORRECTION — "THE DEPLOYED TEMPLATER BRACE-BAN" IS AN OVERCLAIM (adversarial verify caught it).
`noDoubleBraceRE` is the LEAN GUARDED-TEMPLATER's brace-ban: a `PredRE` over `Exec.Value`, consumed by
`HandlebarsGuarded`/`HandlebarsGuardDecision`. That is a real object and everything below is true of it.

It is NOT the guard that runs in the shipped services. That one is
`zkoracle-prove/src/injection.rs:47  pub fn injection_free(field: &[u8]) -> bool`
= `injection_template().not().matches(field)` — the SAME PATTERN (a `neg`-of-template acceptance test,
mirroring `ZkOracle.lean`) but a DIFFERENT OBJECT over a DIFFERENT ALPHABET (bytes, not `Value`), with
its own template. So this file arithmetizes a real Lean guard, not the deployed byte guard.

WHAT IT WOULD TAKE to reach the shipped one: instantiate this same pipeline at the byte alphabet against
`injectionTemplate` — the machinery is alphabet-parametric (the cover/minterm step is the only alphabet-
specific leg, and `der_factors_over` is stated generically), so this is plausibly cheap. It has NOT been
done, so do not read the results below as covering `injection_free`.
# Dregg2.Crypto.GuardToAutomatonCircuit — a template GUARD becomes a WITNESSED CIRCUIT.

**This is Lean-authored AIR.** The descriptor is an `EffectVmDescriptor2` produced by
`DfaRoutingTableEmit.tableRoutingDesc`; the witness is a concrete `VmTrace`; satisfaction is a
theorem over the EMITTED object. Nothing is hand-written in Rust.

## The pipeline this file closes

    PredRE guard  ──(Brzozowski derivatives, ≅-dedup)──▶  a tiny TABLE DFA
                  ──(run-table routing descriptor)─────▶  a Satisfied2Public WITNESS

Both ends were already committed and neither reached the other:

  * SOURCE — `Crypto/HandlebarsGuardDecision.lean` + `Deriv/{SymbolicFixpoint,EquivalenceFixpoint}`:
    the DEPLOYED templater brace-ban `noDoubleBraceRE` is a `PredRE` over `Exec.Value`, in the
    cheapest (pin/minterm) cover, with emptiness and equivalence DECIDED, and `reachFix` computing
    the `≅`-class frontier of its derivatives.
  * SINK — `Circuit/Emit/TinyAutomataSatisfiable.lean`: `runWit_satisfies` builds a satisfying
    `VmTrace` for the run-table descriptor of ANY `TableDfa Nat Nat`.

⚑ **THE FRONTIER IS THE DFA.** `reachFix`'s saturated `seen` list IS a state set: its elements are
`≅`-classes of derivatives, and `der a ·` is the transition. §2 turns that list into a
`TableDfa Nat Nat` by INDEXING it (`idxOf` = "which class is this derivative in", decided by
`simDecide`), §3 proves the emitted automaton decides the guard's language, §5 fires the circuit
gate on it, §6 composes two real guards into ONE descriptor.

## ⚠ THE ALPHABET ABSTRACTION — named, and SOUND (this was the escape hatch to check)

`Value` is INFINITE; a `TableDfa Nat Nat` reads finitely many symbols. The bridge is the MINTERM
cover, and it is sound for a precise, already-proven reason: `SymbolicMinterms.der_factors_over`
says two frames with the same `L`-leaf signature have the SAME derivative on any regex whose
leaves read a frame only through `L`. So "two `Value`s in one minterm take different transitions"
CANNOT happen inside `SymbolicOver L` — the failure mode the escape hatch worried about is
excluded by a theorem, not by hope.

What the circuit therefore reads is a word of MINTERM INDICES (`enc`), not raw `Value`s; §3's
`guardDfa_decides` quantifies over ARBITRARY `Value` words and inserts `enc` explicitly, so the
abstraction is visible in the statement rather than hidden in a coercion. The residual this leaves
is stated in §8: a verifier that wants "this trace read THIS `Value` word" must bind the
`Value → minterm-index` map itself; the circuit binds only the index word.

## ⚠ SIGNATURE NOTE — why this is not `guardDfa : PredRE → TableDfa Nat Nat`

A TOTAL function from a bare `PredRE` to a table would have to invent a table when the `≅`-fixpoint
does NOT saturate within its fuel — i.e. it would silently return garbage exactly where the
determinisation failed, and its correctness theorem would need a saturation hypothesis anyway.
`SymbolicFixpoint`'s termination note still lacks the counting step that would bound the fuel a
priori, so that hypothesis cannot be discharged in general today. The carrier here is therefore
`GuardAut C` — a guard PLUS a saturated frontier and the four facts about it — and `ofFix` turns a
`reachFixAux … = some seen` into one. At the deployed guard the saturation is discharged by a
kernel `rfl` (§5), so nothing is assumed: `guardDfa` is total on the objects that HAVE a DFA.

## Axiom hygiene

`#assert_all_clean` on every theorem; `sorry`-free. Every `#guard` is COMPILED EVALUATION of a
closed `Bool` — it proves NO `Prop`; the `Prop`-level content is the theorems.
-/
import Dregg2.Crypto.HandlebarsGuardDecision
import Dregg2.Circuit.Emit.TinyAutomataSatisfiable

namespace Dregg2.Crypto.GuardToAutomatonCircuit

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
  (der null derives derList derives_eq_null_derList Sim sim_der sim_null
   simDecide simDecide_correct rigidRE RigidFull)
open Dregg2.Crypto.HandlebarsGuarded (noDoubleBraceRE braceVal dataVal braceP)
open Dregg2.Crypto.HandlebarsGuardDecision (nodbExactly deployed_rejects_sep refactor_admits_sep)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (SYMBOL PI_INITIAL PI_FINAL tableRoutingDesc hash0)
open Dregg2.Circuit.Emit.TinyAutomataCompose
  (runTable runTable_graph costOf jsonBytes prod2 classify_prod2 productDesc_binary_components)
open Dregg2.Circuit.Emit.TinyAutomataSatisfiable (runWit runWit_satisfies runRows_symbols)

set_option autoImplicit false

/-! ## §1 — `GuardAut`: the data a determinised guard actually needs.

A `GuardAut C` is exactly what `reachFix` returns, with its four load-bearing facts kept: the
frontier is rigid (so `simDecide` decides `≅` on it), it `≅`-represents the root, and it is CLOSED
under `der a ·` for every cover frame `a`. Nothing else about how the frontier was built matters —
this is the table-opaque discipline of `Deriv/TableDfa.lean`, one level up. -/

/-- In-range `getD` is `getElem` (the core API only simplifies `getD` through `getElem?`). -/
theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i]'h := (List.getElem_eq_getD d).symm

/-- The `y`-th cover frame (out-of-range indices land on a harmless default; §3 only ever quantifies
over in-range indices). -/
def coverSym {L : List Pred} (C : MintermCover L) (y : Nat) : Value := C.cands.getD y (.int 0)

theorem coverSym_mem {L : List Pred} (C : MintermCover L) {y : Nat} (hy : y < C.cands.length) :
    coverSym C y ∈ C.cands := by
  rw [coverSym, getD_of_lt _ hy]
  exact List.getElem_mem hy

/-- **`GuardAut C`** — a guard together with a saturated `≅`-class frontier for it, over the
minterm cover `C`. -/
structure GuardAut {L : List Pred} (C : MintermCover L) where
  /-- The guard itself (the DFA's language). -/
  root : PredRE
  /-- The `≅`-class representatives — the DFA's states, indexed by position. -/
  states : List PredRE
  /-- The guard reads a frame only through its `L`-minterm (what makes the finite alphabet sound). -/
  root_sym : SymbolicOver L root
  /-- The guard is rigid (so `simDecide` decides `≅` from it). -/
  root_rig : rigidRE root = true
  /-- Every state is rigid — `simDecide`'s left-argument obligation, everywhere. -/
  states_rig : ∀ s ∈ states, rigidRE s = true
  /-- The root has a representative among the states (the start state exists). -/
  root_rep : ∃ u ∈ states, u ≅ root
  /-- The frontier is CLOSED under cover-frame derivatives (the transition function is total). -/
  closed : ∀ s ∈ states, ∀ a ∈ C.cands, ∃ u ∈ states, u ≅ der a s

namespace GuardAut

variable {L : List Pred} {C : MintermCover L}

/-- The state count. -/
def size (G : GuardAut C) : Nat := G.states.length

/-- The `≅`-class representative at index `s` (out of range: `bot`, which is rigid and empty). -/
def stateAt (G : GuardAut C) (s : Nat) : PredRE := G.states.getD s (.sym .ff)

/-- **`idxOf G t`** — the index of the state `≅`-representing `t`, decided by `simDecide`. This is
the determinisation: a derivative is not a new state if it is `≅` to one we have. Returns `G.size`
(a junk sink) when nothing matches, so the function is TOTAL and bounded by `G.size`. -/
def idxOf (G : GuardAut C) (t : PredRE) : Nat := G.states.findIdx (fun u => simDecide u t)

/-- The transition: derive the current class by the `y`-th cover frame, then re-index. -/
def step (G : GuardAut C) (s y : Nat) : Nat := G.idxOf (der (coverSym C y) (G.stateAt s))

/-- The start state: the index of the root's class. -/
def start (G : GuardAut C) : Nat := G.idxOf G.root

/-- ⚑ **`guardDfa`** — the guard, DETERMINISED into a tiny table DFA over `ℕ` states and `ℕ`
(minterm-index) symbols. This is the object the circuit routes. -/
def guardDfa (G : GuardAut C) : TableDfa Nat Nat :=
  { step    := G.step
  , start   := G.start
  , accepts := fun s => null (G.stateAt s) = true }

theorem stateAt_mem (G : GuardAut C) {s : Nat} (h : s < G.size) : G.stateAt s ∈ G.states := by
  rw [stateAt, getD_of_lt _ h]
  exact List.getElem_mem h

/-- Every index the automaton can be in is `≤ G.size` — so `G.size + 1` bounds the state space
(the radix the product composition of §6 needs). -/
theorem idxOf_le (G : GuardAut C) (t : PredRE) : G.idxOf t ≤ G.size := List.findIdx_le_length

/-- ⚑ The state space is bounded by `G.size + 1` — `hstep` for the product construction. -/
theorem step_lt (G : GuardAut C) (s y : Nat) : G.guardDfa.step s y < G.size + 1 :=
  Nat.lt_succ_of_le (G.idxOf_le _)

theorem start_lt (G : GuardAut C) : G.guardDfa.start < G.size + 1 :=
  Nat.lt_succ_of_le (G.idxOf_le _)

/-- If some state `≅`-represents `t`, the index found is in range… -/
theorem idxOf_lt (G : GuardAut C) {t : PredRE} (h : ∃ u ∈ G.states, u ≅ t) : G.idxOf t < G.size := by
  obtain ⟨u, hu, hsim⟩ := h
  exact List.findIdx_lt_length_of_exists
    ⟨u, hu, (simDecide_correct (G.states_rig u hu)).mpr hsim⟩

/-- …and the state AT that index really is `≅ t` (`simDecide` is a decision, not a heuristic —
whatever `findIdx` lands on is a genuine `≅`). -/
theorem idxOf_sim (G : GuardAut C) {t : PredRE} (h : ∃ u ∈ G.states, u ≅ t) :
    G.stateAt (G.idxOf t) ≅ t := by
  have hlt : G.idxOf t < G.size := G.idxOf_lt h
  have hdec : simDecide (G.states[G.idxOf t]'hlt) t = true := List.findIdx_getElem (w := hlt)
  have hmem : G.states[G.idxOf t]'hlt ∈ G.states := List.getElem_mem hlt
  rw [stateAt, getD_of_lt _ hlt]
  exact (simDecide_correct (G.states_rig _ hmem)).mp hdec

/-! ## §2 — The simulation invariant: an index TRACKS a derivative class. -/

/-- **`Good G s t`** — index `s` is a real state and its class is `≅ t`. -/
def Good (G : GuardAut C) (s : Nat) (t : PredRE) : Prop := s < G.size ∧ G.stateAt s ≅ t

theorem good_start (G : GuardAut C) : G.Good G.guardDfa.start G.root :=
  ⟨G.idxOf_lt G.root_rep, G.idxOf_sim G.root_rep⟩

/-- ONE STEP of the simulation: the emitted transition tracks `der`. This is where `closed` (the
frontier really is closed) and `simDecide_correct` (the dedup really is `≅`) both cash in. -/
theorem good_step (G : GuardAut C) {s : Nat} {t : PredRE} (hg : G.Good s t)
    {y : Nat} (hy : y < C.cands.length) :
    G.Good (G.guardDfa.step s y) (der (coverSym C y) t) := by
  have hex : ∃ u ∈ G.states, u ≅ der (coverSym C y) (G.stateAt s) :=
    G.closed _ (G.stateAt_mem hg.1) _ (coverSym_mem C hy)
  refine ⟨G.idxOf_lt hex, ?_⟩
  exact Sim.trans (G.idxOf_sim hex) (sim_der hg.2 _)

/-- The whole run: reading a word of in-range minterm indices tracks `derList` along the
corresponding cover frames. -/
theorem good_classify (G : GuardAut C) :
    ∀ (ys : List Nat), (∀ y ∈ ys, y < C.cands.length) →
      ∀ {s : Nat} {t : PredRE}, G.Good s t →
        G.Good (classifyFrom G.guardDfa s ys) (derList (ys.map (coverSym C)) t) := by
  intro ys
  induction ys with
  | nil => intro _ s t hg; exact hg
  | cons y ys ih =>
      intro hys s t hg
      have hy : y < C.cands.length := hys y (List.mem_cons_self ..)
      have hrest : ∀ z ∈ ys, z < C.cands.length := fun z hz => hys z (List.mem_cons_of_mem _ hz)
      exact ih hrest (G.good_step hg hy)

/-! ## §3 — ⚑ THE CORRECTNESS THEOREM: the emitted automaton decides the GUARD's language. -/

/-- **The automaton decides the guard, on cover words.** Over any word of in-range minterm indices,
the emitted DFA accepts iff the guard `derives` the corresponding frame word. -/
theorem guardDfa_decides_cover (G : GuardAut C) (ys : List Nat)
    (hys : ∀ y ∈ ys, y < C.cands.length) :
    G.guardDfa.accepts (classifyFrom G.guardDfa G.guardDfa.start ys)
      ↔ derives (ys.map (coverSym C)) G.root = true := by
  have hg := G.good_classify ys hys (G.good_start)
  show null (G.stateAt (classifyFrom G.guardDfa G.guardDfa.start ys)) = true ↔ _
  rw [sim_null hg.2, ← derives_eq_null_derList]

/-! ### The alphabet abstraction, made explicit.

`enc C a` is the index of `a`'s minterm representative. `der_factors_over` — same signature ⇒ same
derivative — is what makes replacing `a` by that representative a NO-OP on the whole derivative
walk. This is the sound restriction the escape hatch asked for, and it needs no restriction at all
inside `SymbolicOver L`. -/

/-- The minterm index of a frame: the first candidate sharing its `L`-signature. -/
def enc (C : MintermCover L) (a : Value) : Nat :=
  C.cands.findIdx (fun c => leafSig L c == leafSig L a)

theorem enc_lt (C : MintermCover L) (a : Value) : enc C a < C.cands.length := by
  obtain ⟨c, hc, hsig⟩ := C.covers a
  exact List.findIdx_lt_length_of_exists ⟨c, hc, by simp [hsig]⟩

/-- ⚑ The abstraction step: the frame the circuit actually reads has the SAME leaf signature as the
frame the template author wrote. -/
theorem leafSig_coverSym_enc (C : MintermCover L) (a : Value) :
    leafSig L (coverSym C (enc C a)) = leafSig L a := by
  have hlt : enc C a < C.cands.length := enc_lt C a
  have hdec : (fun c => leafSig L c == leafSig L a) (C.cands[enc C a]'hlt) = true :=
    List.findIdx_getElem (w := hlt)
  rw [coverSym, getD_of_lt _ hlt]
  exact eq_of_beq (by simpa using hdec)

/-- …hence reading the ENCODED word is the same derivative walk as reading the original word.
`der_factors_over` at every step; `der_symbolicOver` carries the hypothesis along. -/
theorem derList_enc (C : MintermCover L) :
    ∀ (w : List Value) {R : PredRE}, SymbolicOver L R →
      derList ((w.map (enc C)).map (coverSym C)) R = derList w R := by
  intro w
  induction w with
  | nil => intro R _; rfl
  | cons a as ih =>
      intro R hR
      show derList ((as.map (enc C)).map (coverSym C)) (der (coverSym C (enc C a)) R)
        = derList as (der a R)
      rw [der_factors_over (leafSig_coverSym_enc C a) hR]
      exact ih (der_symbolicOver hR)

/-- ⚑⚑ **THE CORRECTNESS THEOREM.** For EVERY `Value` word — arbitrary, over the infinite alphabet —
the emitted table DFA, run on the word's minterm-index encoding, accepts EXACTLY when the guard
accepts the word. The circuit's verdict IS the guard's verdict. -/
theorem guardDfa_decides (G : GuardAut C) (w : List Value) :
    G.guardDfa.accepts (classifyFrom G.guardDfa G.guardDfa.start (w.map (enc C)))
      ↔ derives w G.root = true := by
  rw [G.guardDfa_decides_cover (w.map (enc C))
        (fun y hy => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy; exact enc_lt C a),
      derives_eq_null_derList, derives_eq_null_derList, derList_enc C w G.root_sym]

/-! ## §4 — Building a `GuardAut` from the committed `reachFix` run. -/

/-- **`ofFix`** — a saturated `reachFixAux` run IS a `GuardAut`. Rigidity comes from
`reachFixAux_sound` (every seen state is a real `derList w root`) plus `rigidRE_derList`; the root
representation and the closure are the two halves of `reachFixAux_closed`. -/
def ofFix (C : MintermCover L) (R : PredRE) (fuel : Nat) (seen : List PredRE)
    (hsym : SymbolicOver L R) (hrig : rigidRE R = true)
    (hfix : reachFixAux C.cands fuel [] [R] = some seen) : GuardAut C where
  root := R
  states := seen
  root_sym := hsym
  root_rig := hrig
  states_rig := by
    have hsound : ∀ s ∈ seen, ∃ w, derList w R = s := by
      refine reachFixAux_sound (V := C.cands) (P := fun s => ∃ w, derList w R = s) ?_
        fuel [] [R] seen hfix (by intro x hx; cases hx) ?_
      · rintro t ⟨w, rfl⟩ t' ht'
        simp only [satStepG, List.mem_map] at ht'
        obtain ⟨a, _, rfl⟩ := ht'
        exact ⟨w ++ [a], by rw [derList_append]; rfl⟩
      · intro x hx
        rw [List.mem_singleton.mp hx]
        exact ⟨[], rfl⟩
    intro s hs
    obtain ⟨w, rfl⟩ := hsound s hs
    exact rigidRE_derList w hrig
  root_rep := by
    obtain ⟨hrep, _⟩ := reachFixAux_closed fuel [] [R] seen hfix (by intro x hx; cases hx)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hrig) (by intro x hx; cases hx)
    exact hrep R (Or.inr (List.mem_singleton.mpr rfl))
  closed := by
    obtain ⟨_, hcl⟩ := reachFixAux_closed fuel [] [R] seen hfix (by intro x hx; cases hx)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hrig) (by intro x hx; cases hx)
    intro s hs a ha
    exact hcl s hs (der a s) (by simp only [satStepG, List.mem_map]; exact ⟨a, ha, rfl⟩)

end GuardAut

open GuardAut

/-! ## §5 — ⚑ THE GATE: the DEPLOYED brace-ban, as a proof-carrying circuit.

`noDoubleBraceRE` is the guard `Crypto/HandlebarsGuarded.lean` puts at EVERY hole of the committed
`Handlebars` family. Here it is determinised (§5a), routed (§5b) and WITNESSED (§5c). -/

section Deployed

/-- The deployed guard's pin set, computed (`HandlebarsGuardDecision` §1 pins this too). -/
theorem nodb_atoms :
    atomsOfLeaves? (leavesOf noDoubleBraceRE) = some [("t", AtomVal.sym 0), ("t", AtomVal.sym 0)] :=
  rfl

/-- The cover the committed decision itself runs on (`fixCands`'s `coverOfSymbolic` arm). -/
def nodbCover : MintermCover (leavesOf noDoubleBraceRE) := coverOfSymbolic nodb_atoms

/-- The `≅`-fixpoint SATURATES at fuel 64 — kernel-checked (this `rfl` is the worklist running). -/
theorem nodbFix_isSome :
    (reachFixAux nodbCover.cands 64 [] [noDoubleBraceRE]).isSome = true := rfl

/-- The saturated frontier — the DFA's state list. -/
def nodbSeen : List PredRE :=
  (reachFixAux nodbCover.cands 64 [] [noDoubleBraceRE]).get nodbFix_isSome

theorem nodbFix : reachFixAux nodbCover.cands 64 [] [noDoubleBraceRE] = some nodbSeen :=
  (Option.some_get nodbFix_isSome).symm

/-- ⚑ **The deployed guard, determinised.** -/
def nodbAut : GuardAut nodbCover :=
  GuardAut.ofFix nodbCover noDoubleBraceRE 64 nodbSeen (symbolicOver_leavesOf _) rfl nodbFix

/-- The deployed guard's DFA. -/
def nodbDfa : TableDfa Nat Nat := nodbAut.guardDfa

/-- ⚑ The correctness theorem, at the DEPLOYED guard: for every `Value` word, the emitted
automaton's verdict is the templater guard's verdict. -/
theorem nodbDfa_decides (w : List Value) :
    nodbDfa.accepts (classifyFrom nodbDfa nodbDfa.start (w.map (enc nodbCover)))
      ↔ derives w noDoubleBraceRE = true :=
  nodbAut.guardDfa_decides w

/-! ### §5b — the words, and what the automaton says about them. -/

/-- The `{{`-bearing datum `HandlebarsGuardDecision` §3 exhibits as the injection the refactor
would admit: the deployed guard REJECTS it. -/
def sepWord : List Value := [dataVal, braceVal, braceVal]

/-- A `{{`-free datum the deployed guard ACCEPTS. -/
def okWord : List Value := [dataVal, braceVal, dataVal]

/-- The encoded (minterm-index) words the circuit actually reads. -/
def sepSyms : List Nat := sepWord.map (enc nodbCover)
/-- …and the accepted one. -/
def okSyms : List Nat := okWord.map (enc nodbCover)

theorem sepSyms_ne : sepSyms ≠ [] := by
  intro h
  rw [sepSyms, sepWord, List.map_cons] at h
  exact List.cons_ne_nil _ _ h

theorem okSyms_ne : okSyms ≠ [] := by
  intro h
  rw [okSyms, okWord, List.map_cons] at h
  exact List.cons_ne_nil _ _ h

/-- The guard accepts the `{{`-free datum (`derives`, evaluated). -/
theorem okWord_accepted_by_guard : derives okWord noDoubleBraceRE = true := rfl

/-- ⚑ The emitted automaton REJECTS the injection word — because the deployed guard does
(`deployed_rejects_sep`, a committed theorem). -/
theorem nodbDfa_rejects_sep :
    ¬ nodbDfa.accepts (classifyFrom nodbDfa nodbDfa.start sepSyms) := by
  intro h
  have := (nodbDfa_decides sepWord).mp h
  rw [show derives sepWord noDoubleBraceRE = false from deployed_rejects_sep] at this
  exact Bool.noConfusion this

/-- …and ACCEPTS the safe datum. -/
theorem nodbDfa_accepts_ok :
    nodbDfa.accepts (classifyFrom nodbDfa nodbDfa.start okSyms) :=
  (nodbDfa_decides okWord).mpr okWord_accepted_by_guard

/-! ### §5c — ⚑ THE WITNESS: a `Satisfied2Public` trace for the deployed guard's circuit. -/

/-- The emitted descriptor's name. -/
def NODB_NAME : String := "handlebars-no-double-brace-guard-run::exact-public-v1"

/-- **The emitted descriptor**: the run-table routing descriptor of the deployed guard's DFA on the
index word `ys`. 3 columns, 4 constraints, 2 PIs, one table of `|ys|` rows. -/
def nodbRunDesc (ys : List Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc NODB_NAME (runTable nodbDfa nodbDfa.start ys)

/-- **The witness trace**. -/
def nodbRunWit (ys : List Nat) : VmTrace := runWit nodbDfa nodbDfa.start ys

/-- ⚑ **THE GATE FIRES** — a real `Satisfied2Public` witness for the DEPLOYED templater guard's
circuit, at any non-empty index word. -/
theorem nodbRunWit_satisfies (ys : List Nat) (hys : ys ≠ []) :
    Satisfied2Public hash0 (nodbRunDesc ys) (fun _ => 0) (fun _ => (0, 0)) [] (nodbRunWit ys) :=
  runWit_satisfies nodbDfa nodbDfa.start ys hys NODB_NAME

/-- The witness's exposed public `final_state` IS the automaton's classification, and the symbol
column IS the index word. -/
theorem nodbRunWit_public (ys : List Nat) :
    (nodbRunWit ys).pub PI_FINAL = Int.ofNat (classifyFrom nodbDfa nodbDfa.start ys)
      ∧ (nodbRunWit ys).rows.map (fun a => (a SYMBOL).toNat) = ys :=
  ⟨rfl, runRows_symbols nodbDfa ys nodbDfa.start⟩

/-- ⚑⚑ **THE PIPELINE, CLOSED.** For an arbitrary `Value` word: the emitted descriptor HAS a
satisfying trace, that trace reads exactly the word's minterm encoding, its public `final_state` is
the state the automaton reaches, and that state is accepting EXACTLY when the deployed templater
guard accepts the word. A guard has become a proof-carrying circuit. -/
theorem nodb_pipeline (w : List Value) (hw : w.map (enc nodbCover) ≠ []) :
    Satisfied2Public hash0 (nodbRunDesc (w.map (enc nodbCover))) (fun _ => 0) (fun _ => (0, 0)) []
        (nodbRunWit (w.map (enc nodbCover)))
      ∧ (nodbRunWit (w.map (enc nodbCover))).rows.map (fun a => (a SYMBOL).toNat)
          = w.map (enc nodbCover)
      ∧ (nodbRunWit (w.map (enc nodbCover))).pub PI_FINAL
          = Int.ofNat (classifyFrom nodbDfa nodbDfa.start (w.map (enc nodbCover)))
      ∧ (nodbDfa.accepts (classifyFrom nodbDfa nodbDfa.start (w.map (enc nodbCover)))
          ↔ derives w noDoubleBraceRE = true) :=
  ⟨nodbRunWit_satisfies _ hw, (nodbRunWit_public _).2, (nodbRunWit_public _).1,
   nodbDfa_decides w⟩

/-- The pipeline at the INJECTION word, concretely: the circuit exists, and its verdict is
REJECT — the same verdict `deployed_rejects_sep` gives. -/
theorem nodb_pipeline_sep :
    Satisfied2Public hash0 (nodbRunDesc sepSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (nodbRunWit sepSyms)
      ∧ ¬ nodbDfa.accepts (classifyFrom nodbDfa nodbDfa.start sepSyms) :=
  ⟨nodbRunWit_satisfies sepSyms sepSyms_ne, nodbDfa_rejects_sep⟩

/-- …and at the SAFE word: the circuit exists and its verdict is ACCEPT. -/
theorem nodb_pipeline_ok :
    Satisfied2Public hash0 (nodbRunDesc okSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (nodbRunWit okSyms)
      ∧ nodbDfa.accepts (classifyFrom nodbDfa nodbDfa.start okSyms) :=
  ⟨nodbRunWit_satisfies okSyms okSyms_ne, nodbDfa_accepts_ok⟩

/-! ### §5d — MEASUREMENT of the witnessed object.

⚠ Every `#guard` below is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`. Each one
measures the descriptor that `nodbRunWit_satisfies` has just PROVED satisfiable, so the standing
gate ("never quote a cost without a `Satisfied2Public` witness") is met by construction. -/

-- |states| of the deployed guard's DFA, and the cover size (the symbol alphabet):
#guard nodbAut.states.length == 11
#guard nodbCover.cands.length == 3

-- The encoded words: `dataVal` and `braceVal` land in DIFFERENT minterms (indices 0 and 1), so the
-- abstraction is not collapsing the alphabet to a point.
#guard sepSyms == [0, 1, 1]
#guard okSyms == [0, 1, 0]

-- The reached states, and the verdicts (the `Prop`s are §5b's two theorems):
#guard classifyFrom nodbDfa nodbDfa.start sepSyms == 6
#guard classifyFrom nodbDfa nodbDfa.start okSyms == 5
#guard null (nodbAut.stateAt (classifyFrom nodbDfa nodbDfa.start sepSyms)) == false
#guard null (nodbAut.stateAt (classifyFrom nodbDfa nodbDfa.start okSyms)) == true

-- ⚑ THE WITNESSED COST of the deployed guard's circuit at |w| = 3: 3 columns, 4 constraints, 2 PIs,
-- ONE table of 3 rows, 3 forced trace rows, ZERO nonlinear multiplications — AREA 9.
#guard costOf (nodbRunDesc sepSyms) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 3, forcedTraceRows := 3, nonlinearMults := 0 }
#guard (costOf (nodbRunDesc sepSyms)).area == 9
#guard jsonBytes (nodbRunDesc sepSyms) == 616

end Deployed

/-! ## §6 — ⚑ COMPOSITION: two REAL guards, one descriptor, both verdicts.

The pair is the deployed brace-ban and `HandlebarsGuardDecision`'s REFACTOR BUG #2
(`nodbExactly` = "just check the datum isn't literally `{{`") — the spelling the equivalence
decision proved is a real WEAKENING. Composing them in ONE circuit exposes both verdicts from one
public output, and on the injection word THEY DISAGREE: the bug is visible in the emitted object.

⚠ Both automata must read the SAME symbol column, so both are built over ONE cover — the cover of
`alt g₁ g₂`, whose leaf list is `leavesOf g₁ ++ leavesOf g₂`. Each guard is `SymbolicOver` that
larger list, so §3's correctness applies to both unchanged. -/

section Pair

/-- The pair's alternation — its leaf list is the union, so its cover serves both guards. -/
def pairRE : PredRE := .alt noDoubleBraceRE nodbExactly

theorem pair_atoms :
    atomsOfLeaves? (leavesOf pairRE)
      = some [("t", AtomVal.sym 0), ("t", AtomVal.sym 0), ("t", AtomVal.sym 0),
              ("t", AtomVal.sym 0)] := rfl

/-- The SHARED cover. -/
def pairCover : MintermCover (leavesOf pairRE) := coverOfSymbolic pair_atoms

theorem g1_sym : SymbolicOver (leavesOf pairRE) noDoubleBraceRE :=
  symbolicOver_of_leaves_mem (fun _ hφ => List.mem_append.mpr (Or.inl hφ))

theorem g2_sym : SymbolicOver (leavesOf pairRE) nodbExactly :=
  symbolicOver_of_leaves_mem (fun _ hφ => List.mem_append.mpr (Or.inr hφ))

theorem g1Fix_isSome :
    (reachFixAux pairCover.cands 64 [] [noDoubleBraceRE]).isSome = true := rfl
theorem g2Fix_isSome :
    (reachFixAux pairCover.cands 64 [] [nodbExactly]).isSome = true := rfl

/-- The brace-ban's frontier over the SHARED cover. -/
def g1Seen : List PredRE := (reachFixAux pairCover.cands 64 [] [noDoubleBraceRE]).get g1Fix_isSome
/-- The weakened spelling's frontier over the shared cover. -/
def g2Seen : List PredRE := (reachFixAux pairCover.cands 64 [] [nodbExactly]).get g2Fix_isSome

theorem g1Fix : reachFixAux pairCover.cands 64 [] [noDoubleBraceRE] = some g1Seen :=
  (Option.some_get g1Fix_isSome).symm
theorem g2Fix : reachFixAux pairCover.cands 64 [] [nodbExactly] = some g2Seen :=
  (Option.some_get g2Fix_isSome).symm

/-- The deployed guard, over the shared cover. -/
def g1Aut : GuardAut pairCover :=
  GuardAut.ofFix pairCover noDoubleBraceRE 64 g1Seen g1_sym rfl g1Fix
/-- The WEAKENED spelling, over the shared cover. -/
def g2Aut : GuardAut pairCover :=
  GuardAut.ofFix pairCover nodbExactly 64 g2Seen g2_sym rfl g2Fix

/-- The composition radix: the second machine's state space (`+1` for the junk sink). -/
def PAIR_M : Nat := g2Aut.size + 1

/-- ⚑ **The composed automaton**: both guards step on ONE symbol column, the state packing
`s = q₁ * M + q₂`. -/
def pairDfa : TableDfa Nat Nat := prod2 g1Aut.guardDfa g2Aut.guardDfa PAIR_M

/-- The composed start state. -/
def pairStart : Nat := g1Aut.guardDfa.start * PAIR_M + g2Aut.guardDfa.start

theorem pairStart_eq : pairDfa.start = pairStart := rfl

/-- The encoded words over the SHARED cover (a different cover ⇒ different indices than §5). -/
def sepSyms2 : List Nat := sepWord.map (enc pairCover)

theorem sepSyms2_ne : sepSyms2 ≠ [] := by
  intro h
  rw [sepSyms2, sepWord, List.map_cons] at h
  exact List.cons_ne_nil _ _ h

/-- The composed descriptor's name. -/
def PAIR_NAME : String := "handlebars-guard-pair-braceban-x-weakened-run::exact-public-v1"

/-- **The composed descriptor** — ONE table-routing descriptor over the product's run table. -/
def pairRunDesc (ys : List Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc PAIR_NAME (runTable pairDfa pairStart ys)

/-- **The composed witness**. -/
def pairRunWit (ys : List Nat) : VmTrace := runWit pairDfa pairStart ys

/-- ⚑ **THE COMPOSED GATE FIRES** — a real `Satisfied2Public` witness for the two-guard circuit. -/
theorem pairRunWit_satisfies (ys : List Nat) (hys : ys ≠ []) :
    Satisfied2Public hash0 (pairRunDesc ys) (fun _ => 0) (fun _ => (0, 0)) [] (pairRunWit ys) :=
  runWit_satisfies pairDfa pairStart ys hys PAIR_NAME

/-- ⚑ **BOTH VERDICTS ARE EXPOSED BY THE ONE PUBLIC OUTPUT.** The satisfying trace's public
`final_state`, divided and remaindered by the radix, is exactly each guard's own classification of
the word the trace reads — and the composed `accepts` implies both guards accept. -/
theorem pair_exposes_both (ys : List Nat) (hys : ys ≠ [])
    (hsmall : ∀ row ∈ runTable pairDfa pairStart ys, ∀ v ∈ row, v < 2013265921)
    (hq0 : pairStart < 2013265921)
    (fN : Nat) (hfin : (pairRunWit ys).pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    fN / PAIR_M = classifyFrom g1Aut.guardDfa g1Aut.guardDfa.start ys
      ∧ fN % PAIR_M = classifyFrom g2Aut.guardDfa g2Aut.guardDfa.start ys
      ∧ (pairDfa.accepts fN →
          g1Aut.guardDfa.accepts (classifyFrom g1Aut.guardDfa g1Aut.guardDfa.start ys)
            ∧ g2Aut.guardDfa.accepts (classifyFrom g2Aut.guardDfa g2Aut.guardDfa.start ys)) := by
  have hword : (pairRunWit ys).rows.map (fun a => (a SYMBOL).toNat) = ys :=
    runRows_symbols pairDfa ys pairStart
  have h := productDesc_binary_components (hash := hash0) (t := pairRunWit ys)
    g1Aut.guardDfa g2Aut.guardDfa PAIR_M
    (fun s y => g2Aut.step_lt s y)
    g1Aut.guardDfa.start g2Aut.guardDfa.start (g2Aut.start_lt)
    (runTable_graph pairDfa ys pairStart)
    hsmall
    (pairRunWit_satisfies ys hys)
    (Dregg2.Circuit.Emit.TinyAutomataSatisfiable.runWit_rows_ne pairDfa pairStart hys)
    rfl hq0 fN hfin hfN
  rw [hword] at h
  exact h

/-- ⚑⚑ **THE REFACTOR BUG, VISIBLE IN ONE EMITTED CIRCUIT.** On the injection word: the composed
descriptor has a satisfying trace; its public output decodes to the two guards' own states; the
DEPLOYED guard's half REJECTS and the WEAKENED spelling's half ACCEPTS. The disagreement
`HandlebarsGuardDecision` §3 decided is now a property of a proof-carrying circuit. -/
theorem pair_circuit_exposes_the_weakening :
    Satisfied2Public hash0 (pairRunDesc sepSyms2) (fun _ => 0) (fun _ => (0, 0)) []
        (pairRunWit sepSyms2)
      ∧ classifyFrom pairDfa pairStart sepSyms2 / PAIR_M
          = classifyFrom g1Aut.guardDfa g1Aut.guardDfa.start sepSyms2
      ∧ classifyFrom pairDfa pairStart sepSyms2 % PAIR_M
          = classifyFrom g2Aut.guardDfa g2Aut.guardDfa.start sepSyms2
      ∧ ¬ g1Aut.guardDfa.accepts (classifyFrom g1Aut.guardDfa g1Aut.guardDfa.start sepSyms2)
      ∧ g2Aut.guardDfa.accepts (classifyFrom g2Aut.guardDfa g2Aut.guardDfa.start sepSyms2) := by
  have hdec := pair_exposes_both sepSyms2 sepSyms2_ne (by decide) (by decide)
    (classifyFrom pairDfa pairStart sepSyms2) rfl (by decide)
  refine ⟨pairRunWit_satisfies sepSyms2 sepSyms2_ne, hdec.1, hdec.2.1, ?_, ?_⟩
  · intro hacc
    have hthis := (g1Aut.guardDfa_decides sepWord).mp hacc
    rw [show g1Aut.root = noDoubleBraceRE from rfl,
      show derives sepWord noDoubleBraceRE = false from deployed_rejects_sep] at hthis
    exact Bool.noConfusion hthis
  · exact (g2Aut.guardDfa_decides sepWord).mpr
      (show derives sepWord g2Aut.root = true from refactor_admits_sep)

/-! ### §6a — MEASUREMENT of the COMPOSED witnessed object.

⚠ compiled evaluation; proves no `Prop`. Each number is read off the descriptor
`pairRunWit_satisfies` has proved satisfiable. -/

-- The shared cover is coarser-indexed than §5's (4 duplicate pins ⇒ 5 candidate frames), and the
-- two frontiers have different sizes — the composition does NOT need them equal.
#guard pairCover.cands.length == 5
#guard g1Aut.states.length == 11
#guard g2Aut.states.length == 5
#guard PAIR_M == 6
#guard sepSyms2 == [0, 1, 1]

-- The composed run's decoded verdicts: the packed final state 37 = 6·6 + 1 splits into the
-- deployed guard's class 6 (REJECTING) and the weakened spelling's class 1 (ACCEPTING) — one
-- public output, two guard verdicts (the `Prop` is `pair_circuit_exposes_the_weakening`).
#guard classifyFrom pairDfa pairStart sepSyms2 == 37
#guard (classifyFrom pairDfa pairStart sepSyms2 / PAIR_M,
        classifyFrom pairDfa pairStart sepSyms2 % PAIR_M) == (6, 1)
#guard (null (g1Aut.stateAt (classifyFrom g1Aut.guardDfa g1Aut.guardDfa.start sepSyms2)),
        null (g2Aut.stateAt (classifyFrom g2Aut.guardDfa g2Aut.guardDfa.start sepSyms2)))
       == (false, true)

-- ⚑ THE COMPOSED COST — IDENTICAL to the single guard's on every axis: 3 columns, 4 constraints,
-- 2 PIs, one table of |w| rows, AREA 9, ZERO nonlinear multiplications. Composition is FREE in
-- circuit area; only the wire bytes move (the longer name and the larger packed states).
#guard costOf (pairRunDesc sepSyms2) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 3, forcedTraceRows := 3, nonlinearMults := 0 }
#guard (costOf (pairRunDesc sepSyms2)).area == 9
#guard jsonBytes (pairRunDesc sepSyms2) == 628

end Pair

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  getD_of_lt, coverSym_mem,
  GuardAut.stateAt_mem, GuardAut.idxOf_le, GuardAut.step_lt,
  GuardAut.start_lt, GuardAut.idxOf_lt, GuardAut.idxOf_sim,
  GuardAut.good_start, GuardAut.good_step, GuardAut.good_classify,
  GuardAut.guardDfa_decides_cover, enc_lt, leafSig_coverSym_enc, derList_enc,
  GuardAut.guardDfa_decides, GuardAut.ofFix,
  nodb_atoms, nodbFix, nodbDfa_decides, okWord_accepted_by_guard,
  nodbDfa_rejects_sep, nodbDfa_accepts_ok,
  nodbRunWit_satisfies, nodbRunWit_public, nodb_pipeline, nodb_pipeline_sep, nodb_pipeline_ok,
  pair_atoms, g1_sym, g2_sym, g1Fix, g2Fix, pairStart_eq,
  pairRunWit_satisfies, pair_exposes_both, pair_circuit_exposes_the_weakening
]

/-! ## §8 — RESIDUALS, named precisely.

* **(the alphabet binding)** The circuit reads MINTERM INDICES. `guardDfa_decides` is a theorem
  about `w.map (enc C)` for an arbitrary `Value` word `w`, so the abstraction is sound and visible
  — but a verifier who wants "this trace read THIS `Value` word" must bind the `Value → index` map
  outside this descriptor (a commitment to `enc`'s output, or an in-circuit re-derivation of the
  leaf signature). Nothing here claims that binding.

* **(what a RUN table commits)** Inherited verbatim from `TinyAutomataSatisfiable` §7: a run table
  declares the edges TRAVERSED, not the automaton. So "which guard ran" must be bound elsewhere;
  the whole-graph declaration that would buy it has no witness (the Eulerian obstruction), and this
  file does not repair that. Both descriptors here are run tables.

* **(the frontier is DATA, its size is not a theorem)** `nodbAut.states.length = 11` is compiled
  evaluation, and `SymbolicFixpoint`'s termination note still lacks the counting step that would
  bound the fuel a priori. Saturation at fuel 64 is kernel-WITNESSED (`nodbFix_isSome` is a `rfl`),
  not proven in general — a bigger guard must be measured, not assumed.

* **(in-slot, as always)** Every verdict is about ONE hole's guard language; the cross-junction
  breakout of `HandlebarsGuarded` §7 is a property of the concatenation and no per-guard automaton
  can see it.
-/

end Dregg2.Crypto.GuardToAutomatonCircuit
