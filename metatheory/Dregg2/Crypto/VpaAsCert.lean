/-
# Dregg2.Crypto.VpaAsCert — the VISIBLY-PUSHDOWN / nested-word rung of the certificate substrate.

`Crypto/Hypergraph` proved a RELATION-PARAMETRIC certificate: for ANY reduction relation
`R : α → α → Prop`, a locally-checkable CHAIN certificate `Cert R start goal c` exists IFF
`ReflTransGen R start goal` (`Hypergraph.bridge`). `Crypto/DfaAsCert` landed the REGULAR rung on it
(`R := delta`, a stackless step relation over configs); `Hypergraph.cfg_parse_via_reduction` lands the
CONTEXT-FREE rung (`R := g.Produces`, prover-chosen rule stack action). This file adds the THIRD sibling —
the VISIBLY-PUSHDOWN rung — so the regular/visibly-pushdown/context-free levels of the Chomsky hierarchy
all ride the SAME `Hypergraph.Cert` object, differing only in `R`:

    REGULAR       Cert delta        (no stack)                          -- DfaAsCert
    VISIBLY-PD    Cert R_vpa        (stack action = f(symbol CLASS))    -- THIS FILE
    CONTEXT-FREE  Cert g.Produces   (prover-chosen rule stack action)   -- Hypergraph

The visibly-pushdown discipline (Alur–Madhusudan): the input alphabet is partitioned
`Σ = Σ_call ⊎ Σ_return ⊎ Σ_internal`. The stack action is a function of the symbol's CLASS, not the
state: a call pushes exactly one symbol, a return pops exactly one, an internal touches nothing. Over a
FINITE alphabet (here the bracket grid `{op, cl, dat}`, `op = call`, `cl = return`, `dat = internal`)
classical VPL theory applies cleanly. The decisive consequence — proved here as `run_height` /
`stack_height_input_determined` — is that the STACK HEIGHT at every input position is a function of the
INPUT WORD ALONE (the running count of unmatched calls), INDEPENDENT of the run. That is the property the
regular rung (no stack) and the context-free rung (sentential-form length is NOT input-determined) both
lack, and it is the root of VPL's boolean closure, determinizability, and DECIDABLE EQUIVALENCE.

Objects:
    stepValid                     : the class-driven stack discipline (call push / return pop / internal none)
    R_vpa                         : the delta-shaped chaining relation over `(state, stack)` configs
    vchained_iff_chain            : `vchained` IS `Hypergraph.chain R_vpa` (definitional bridge)
    vpaAccepts_as_cert            : a VPA run IS a `Hypergraph.Cert R_vpa` + acceptance boundaries
    vpaAccepts_reduces            : an accepting run ⇒ `ReflTransGen R_vpa` (via `Hypergraph.bridge`)
    three_rungs_share_substrate   : regular ⊗ visibly-pushdown ⊗ context-free = ONE `Hypergraph.bridge`
    step_stack_length / run_height / stack_height_input_determined : the root VPL property

## Honest scope (per `docs/DESIGN-visibly-pushdown-reframe.md`)

This rung NAMES the templater's `Separated`/`Excludes` class as the visibly-nested boundary — it does NOT
dissolve the uniqueness / inverse wall. VPA determinism yields a unique RUN; unique DATA recovery still
needs the boundary-at-forced-position argument (`split_unique`), whose precondition — the delimiter is a
genuine return symbol, never hole content — IS `Excludes`, renamed not removed (assessment §2). What the
rung genuinely BUYS is (a) the substrate rung itself and (b) the PATH to a capability the general-CFG
substrate provably cannot have: **decidable template equivalence / inclusion** on the visibly-nested
fragment (CFL equivalence is undecidable; VPL equivalence is EXPTIME-decidable). Decidable equivalence is
NAMED here as the precisely-stated follow-on `run_height` enables — it is NOT proved in this lane, and
NOT sorry'd; see the residual note at the foot of the file.
-/
import Dregg2.Crypto.DfaAsCert
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.VpaAsCert

open Dregg2.Crypto ContextFreeGrammar

universe u

/-! ## The finite visibly-pushdown alphabet + its class partition.

The bracket grid the Dyck circuit already pins (`dyck_stack.rs`, `symbol_grid`): `op` (opening `[`) is a
CALL, `cl` (closing `]`) is a RETURN, `dat` is INTERNAL data. FINITE alphabet ⇒ classical VPL theory
applies (the assessment §4.1: the marquee VPL wins transfer cleanly only to the finite fragment, which is
exactly the Dyck level). -/

/-- The finite input alphabet: opening delimiter `op`, closing delimiter `cl`, internal data `dat`. -/
inductive Sym | op | cl | dat
  deriving DecidableEq, Repr

/-- The visibly-pushdown alphabet partition classes. -/
inductive SymClass | call | ret | internal
  deriving DecidableEq, Repr

/-- **`classOf`** — the partition `Σ = Σ_call ⊎ Σ_return ⊎ Σ_internal`. This is a property of the
ALPHABET, uniform across positions (assessment §0.1): `op ↦ call`, `cl ↦ return`, `dat ↦ internal`. -/
def classOf : Sym → SymClass
  | .op => .call
  | .cl => .ret
  | .dat => .internal

/-- **`heightDelta`** — the per-symbol stack-height change, a function of the symbol's CLASS: a call
adds one to the stack height, a return removes one, an internal leaves it unchanged. THIS is what makes
the stack height a function of the input word alone (`run_height`). -/
def heightDelta : Sym → ℤ
  | .op => 1
  | .cl => -1
  | .dat => 0

/-! ## Configs, the VPA, and the class-driven step discipline. -/

/-- A VPA configuration: a control `state` together with a `stack` over `Gamma`. -/
structure Config (State Gamma : Type u) where
  /-- The control state. -/
  state : State
  /-- The pushdown stack (top at the head). -/
  stack : List Gamma
  deriving Repr

/-- A run step: the `pre` config, the `sym` read, and the resulting `post` config. Mirrors the trace-row
`Step` shape `DfaAsCert` threads its `delta` over — a config the chain relation connects end-to-end. -/
structure VStep (State Gamma : Type u) where
  /-- The configuration BEFORE reading `sym`. -/
  pre : Config State Gamma
  /-- The input symbol read on this step. -/
  sym : Sym
  /-- The configuration AFTER reading `sym`. -/
  post : Config State Gamma
  deriving Repr

/-- **`Vpa`** — a visibly-pushdown automaton (Alur–Madhusudan), faithful: the `call` transition pushes a
stack symbol `γ` of the transition's choosing; the `ret` transition READS and pops the top stack symbol
`γ`; the `int` transition never touches the stack. The stack ACTION is fixed by the symbol class; only
the control target (and, for returns, the read of the popped symbol) is the automaton's. -/
structure Vpa (State Gamma : Type u) where
  /-- Call transition: read a call symbol in `state`, go to `state'`, PUSH `γ`. -/
  call : State → Sym → State → Gamma → Prop
  /-- Return transition: read a return symbol in `state`, POP `γ` (read it), go to `state'`. -/
  ret : State → Sym → State → Gamma → Prop
  /-- Internal transition: read an internal symbol in `state`, go to `state'`, stack untouched. -/
  int : State → Sym → State → Prop

variable {State Gamma : Type u}

/-- **`stepValid M s`** — the visibly-pushdown discipline for one step, dispatched on the symbol's CLASS
(NOT its state): a CALL pushes exactly one symbol (`post.stack = γ :: pre.stack`); a RETURN pops exactly
one (`pre.stack = γ :: rest`, `post.stack = rest`); an INTERNAL leaves the stack (`post.stack =
pre.stack`). This is the entire content of "visibly pushdown": the stack shape is class-driven, so it is
enforced regardless of how permissive the underlying transition relations are. -/
def stepValid (M : Vpa State Gamma) (s : VStep State Gamma) : Prop :=
  match classOf s.sym with
  | .call => ∃ γ, M.call s.pre.state s.sym s.post.state γ ∧ s.post.stack = γ :: s.pre.stack
  | .ret => ∃ γ rest, M.ret s.pre.state s.sym s.post.state γ ∧
      s.pre.stack = γ :: rest ∧ s.post.stack = rest
  | .internal => M.int s.pre.state s.sym s.post.state ∧ s.post.stack = s.pre.stack

/-- **`R_vpa`** — the visibly-pushdown chaining relation over configs-carrying steps: `a` reduces to `b`
iff `b` begins where `a` ended (`b.pre = a.post`). Exactly the `delta`-shape `DfaAsCert` uses (regular
control), but the config it threads carries a STACK whose push/pop is class-driven (per-step `stepValid`).
The visibly-pushdown rung is `Hypergraph.Cert R_vpa` + the `stepValid` wrapper. -/
def R_vpa (a b : VStep State Gamma) : Prop := b.pre = a.post

/-- **`vchained`** — a VPA run's chaining predicate: consecutive steps connect end-to-end. DEFINED as
the generic `Hypergraph.chain` (`Crypto/Chain.lean`) at `R_vpa` — the same delegation `Dfa.chained`
makes at `fun a b => b.state = a.next`, so the identification with the substrate's chain is `Iff.rfl`
(`vchained_iff_chain`), not a re-rolled recursion with an induction to bridge it. -/
def vchained : List (VStep State Gamma) → Prop :=
  Hypergraph.chain R_vpa

/-- **`VpaAccepts M q₀ accept run`** — the VPA acceptance STATEMENT: a NON-EMPTY, well-chained run that
starts in `q₀` with EMPTY stack, ends in an `accept` state with EMPTY stack (well-matched), and whose
every step obeys the class-driven `stepValid` discipline. The empty-stack boundaries encode "every call
matched by a return" — the nested-word acceptance condition. -/
def VpaAccepts (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop)
    (run : List (VStep State Gamma)) : Prop :=
  ∃ first last : VStep State Gamma,
    run.head? = some first ∧
    run.getLast? = some last ∧
    first.pre.state = q₀ ∧
    first.pre.stack = [] ∧
    accept last.post.state ∧
    last.post.stack = [] ∧
    (∀ s ∈ run, stepValid M s) ∧
    vchained run

/-! ## The rung — a VPA run IS a `Hypergraph.Cert` over `R_vpa`. -/

/-- **`vchained_iff_chain`** — the DEFINITIONAL heart: `vchained` IS `Hypergraph.chain R_vpa`. Since
`vchained` is DEFINED as `Hypergraph.chain R_vpa`, the identification is `Iff.rfl` — a VPA chain and a
`Hypergraph` reduction chain over `R_vpa` are the same predicate, by definition. Exactly the form
`DfaAsCert.chained_iff_chain` takes for the regular rung. -/
theorem vchained_iff_chain :
    ∀ run : List (VStep State Gamma), vchained run ↔ Hypergraph.chain R_vpa run :=
  fun _ => Iff.rfl

/-- **`vpaAccepts_as_cert`** — THE RUNG. `VpaAccepts M q₀ accept run` holds IFF there exist endpoint steps
`first`/`last` such that the run is a genuine `Hypergraph.Cert R_vpa first last run` TOGETHER WITH the VPA
acceptance wrapper (initial `q₀` + empty stack, accepting state + empty stack, per-step `stepValid`). The
`Cert` conjunct is bit-for-bit the SAME certificate object `Crypto/Hypergraph` uses for CFG / hypergraph /
DFA reductions — only the relation is visibly-pushdown-specific (`R_vpa`). Proof: reassociate the
conjuncts and swap `vchained` for `Hypergraph.chain R_vpa` via `vchained_iff_chain`. -/
theorem vpaAccepts_as_cert (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop)
    (run : List (VStep State Gamma)) :
    VpaAccepts M q₀ accept run ↔
      ∃ first last : VStep State Gamma,
        first.pre.state = q₀ ∧
        first.pre.stack = [] ∧
        accept last.post.state ∧
        last.post.stack = [] ∧
        (∀ s ∈ run, stepValid M s) ∧
        Hypergraph.Cert R_vpa first last run := by
  constructor
  · rintro ⟨first, last, hhead, hlast, hq0, hstk0, hacc, hstkf, hval, hchain⟩
    exact ⟨first, last, hq0, hstk0, hacc, hstkf, hval,
      hhead, hlast, (vchained_iff_chain run).mp hchain⟩
  · rintro ⟨first, last, hq0, hstk0, hacc, hstkf, hval, hhead, hlast, hchain⟩
    exact ⟨first, last, hhead, hlast, hq0, hstk0, hacc, hstkf, hval,
      (vchained_iff_chain run).mpr hchain⟩

/-- **`vpaAccepts_reduces`** — feeding the `Cert` half of `vpaAccepts_as_cert` through the GENERIC
`Hypergraph.bridge`: an accepting VPA run witnesses a reflexive-transitive `R_vpa`-reduction from its
first to its last step. The VPA run is literally a reduction in the shared substrate. -/
theorem vpaAccepts_reduces (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop)
    (run : List (VStep State Gamma)) (h : VpaAccepts M q₀ accept run) :
    ∃ first last : VStep State Gamma,
      first.pre.state = q₀ ∧
      first.pre.stack = [] ∧
      accept last.post.state ∧
      last.post.stack = [] ∧
      Relation.ReflTransGen R_vpa first last := by
  obtain ⟨first, last, hq0, hstk0, hacc, hstkf, _hval, hcert⟩ :=
    (vpaAccepts_as_cert M q₀ accept run).mp h
  exact ⟨first, last, hq0, hstk0, hacc, hstkf,
    (Hypergraph.bridge R_vpa first last).mp ⟨run, hcert⟩⟩

#assert_axioms vchained_iff_chain
#assert_axioms vpaAccepts_as_cert
#assert_axioms vpaAccepts_reduces

/-! ## The unification — regular ⊗ visibly-pushdown ⊗ context-free, ONE substrate. -/

/-- **`three_rungs_share_substrate`** — the `regex ⊗ VPL ⊗ CFG` picture made explicit: DFA acceptance,
VPA acceptance, and CFG parsing are ALL the generic `Hypergraph.bridge`, instantiated at `delta`, at
`R_vpa`, and at `g.Produces` respectively. The three bridges sit literally side by side; the ONLY
difference is the reduction relation `R`. This extends `DfaAsCert.regular_and_cf_share_substrate` (which
paired regular + context-free) with the visibly-pushdown rung slotted BETWEEN them. -/
theorem three_rungs_share_substrate {Y : Type u}
    (dfirst dlast : Dfa.Step State Y) (vfirst vlast : VStep State Gamma)
    {T : Type} (g : ContextFreeGrammar T) (input : List T) :
    -- REGULAR: the chain certificate over `delta` bridges to a reflexive-transitive DFA reduction.
    ((∃ c, Hypergraph.Cert DfaAsCert.delta dfirst dlast c)
        ↔ Relation.ReflTransGen DfaAsCert.delta dfirst dlast)
    ∧
    -- VISIBLY-PUSHDOWN: the chain certificate over `R_vpa` bridges to a reflexive-transitive VPA reduction.
    ((∃ c, Hypergraph.Cert R_vpa vfirst vlast c) ↔ Relation.ReflTransGen R_vpa vfirst vlast)
    ∧
    -- CONTEXT-FREE: the chain certificate over `g.Produces` bridges to grammar membership.
    ((∃ c, Hypergraph.Cert g.Produces
        [Symbol.nonterminal g.initial] (input.map Symbol.terminal) c) ↔ input ∈ g.language) :=
  ⟨Hypergraph.bridge DfaAsCert.delta dfirst dlast,
   Hypergraph.bridge R_vpa vfirst vlast,
   Hypergraph.cfg_parse_via_reduction g input⟩

#check @Hypergraph.bridge          -- the shared substrate: `∀ R start goal, (∃ c, Cert R start goal c) ↔ …`
#check @three_rungs_share_substrate

#assert_axioms three_rungs_share_substrate

/-! ## The KEY VPL PROPERTY — the stack height is a function of the INPUT WORD alone.

This is the defining visibly-pushdown fact and the ROOT of VPL's boolean closure, determinizability, and
decidable equivalence. The DFA rung (no stack) and the CFG rung (sentential-form length is NOT
input-determined) do NOT have it. -/

/-- **`runDelta run`** — the net stack-height change of a run, the sum of its per-symbol `heightDelta`s.
By construction it depends ONLY on the symbols the run reads (its input word), not on the states or the
pushed stack symbols. -/
def runDelta : List (VStep State Gamma) → ℤ
  | [] => 0
  | s :: rest => heightDelta s.sym + runDelta rest

/-- **`step_stack_length`** — the per-step law: a valid step changes the stack HEIGHT (length) by exactly
`heightDelta` of the symbol read — `+1` on a call, `-1` on a return, `0` on an internal. This holds
BECAUSE the stack action is class-driven (`stepValid`), independent of the control state. -/
theorem step_stack_length (M : Vpa State Gamma) (s : VStep State Gamma) (h : stepValid M s) :
    (s.post.stack.length : ℤ) = (s.pre.stack.length : ℤ) + heightDelta s.sym := by
  cases hsym : s.sym with
  | op =>
    simp only [stepValid, classOf, hsym] at h
    obtain ⟨γ, _, hst⟩ := h
    simp only [heightDelta, hst, List.length_cons]
    omega
  | cl =>
    simp only [stepValid, classOf, hsym] at h
    obtain ⟨γ, rest, _, hpre, hpost⟩ := h
    simp only [heightDelta, hpre, hpost, List.length_cons]
    omega
  | dat =>
    simp only [stepValid, classOf, hsym] at h
    obtain ⟨_, hst⟩ := h
    simp only [heightDelta, hst]
    omega

/-- **`run_height`** — the aggregate: for ANY valid, well-chained run, the FINAL stack height equals the
INITIAL stack height plus `runDelta` (the input-word sum). Since the right side depends only on the start
height and the symbols read, the final height is a FUNCTION OF THE INPUT WORD ALONE — independent of the
states visited or the stack symbols pushed. This is the visibly-pushdown root property. -/
theorem run_height (M : Vpa State Gamma) :
    ∀ (run : List (VStep State Gamma)),
      (∀ s ∈ run, stepValid M s) → vchained run →
      ∀ first last : VStep State Gamma, run.head? = some first → run.getLast? = some last →
        (last.post.stack.length : ℤ) = (first.pre.stack.length : ℤ) + runDelta run := by
  intro run
  induction run with
  | nil => intro _ _ first _ hh _; exact absurd hh (by simp)
  | cons a tl ih =>
    intro hval hchain first last hhead hlast
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases tl with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      have hs := step_stack_length M a (hval a (by simp))
      have hd : runDelta [a] = heightDelta a.sym + 0 := rfl
      rw [hd]; linarith [hs]
    | cons b rest =>
      obtain ⟨hab, htail⟩ := hchain
      have hab' : b.pre = a.post := hab
      have hval' : ∀ s ∈ b :: rest, stepValid M s :=
        fun s hs => hval s (List.mem_cons_of_mem a hs)
      have ihres := ih hval' htail b last rfl
        (by rw [List.getLast?_cons_cons] at hlast; exact hlast)
      have hs := step_stack_length M a (hval a (by simp))
      have hbp : (b.pre.stack.length : ℤ) = (a.post.stack.length : ℤ) := by rw [hab']
      have hd : runDelta (a :: b :: rest) = heightDelta a.sym + runDelta (b :: rest) := rfl
      rw [hd]; linarith [ihres, hs, hbp]

/-- **`stack_height_input_determined`** — the property spelled out: two valid runs with the SAME input
word and the SAME initial stack height end at the SAME stack height — the height is determined by the
input, NOT the run. This is what the DFA rung (no stack) and the CFG rung (length not input-determined)
provably lack, and it is the root of VPL's determinizability + boolean closure + decidable equivalence. -/
theorem stack_height_input_determined (M : Vpa State Gamma)
    (run₁ run₂ : List (VStep State Gamma))
    (hval₁ : ∀ s ∈ run₁, stepValid M s) (hch₁ : vchained run₁)
    (hval₂ : ∀ s ∈ run₂, stepValid M s) (hch₂ : vchained run₂)
    (f₁ l₁ f₂ l₂ : VStep State Gamma)
    (hh₁ : run₁.head? = some f₁) (hl₁ : run₁.getLast? = some l₁)
    (hh₂ : run₂.head? = some f₂) (hl₂ : run₂.getLast? = some l₂)
    (hword : run₁.map (fun s => s.sym) = run₂.map (fun s => s.sym))
    (hinit : f₁.pre.stack.length = f₂.pre.stack.length) :
    l₁.post.stack.length = l₂.post.stack.length := by
  have e₁ := run_height M run₁ hval₁ hch₁ f₁ l₁ hh₁ hl₁
  have e₂ := run_height M run₂ hval₂ hch₂ f₂ l₂ hh₂ hl₂
  -- `runDelta` is a function of the input word alone, so equal words ⇒ equal deltas.
  have hdelta : runDelta run₁ = runDelta run₂ := by
    clear e₁ e₂ hval₁ hval₂ hch₁ hch₂ hh₁ hl₁ hh₂ hl₂ hinit f₁ l₁ f₂ l₂
    induction run₁ generalizing run₂ with
    | nil =>
      cases run₂ with
      | nil => rfl
      | cons b rest => simp at hword
    | cons a tl ih =>
      cases run₂ with
      | nil => simp at hword
      | cons b rest =>
        simp only [List.map_cons, List.cons.injEq] at hword
        obtain ⟨hsym, htl⟩ := hword
        simp only [runDelta, hsym, ih rest htl]
  have hi : (f₁.pre.stack.length : ℤ) = (f₂.pre.stack.length : ℤ) := by exact_mod_cast hinit
  have : (l₁.post.stack.length : ℤ) = (l₂.post.stack.length : ℤ) := by
    rw [e₁, e₂, hdelta, hi]
  exact_mod_cast this

#assert_axioms step_stack_length
#assert_axioms run_height
#assert_axioms stack_height_input_determined

/-! ## Non-vacuity — the bracket-chain `{op^n cl^n}` (the Dyck circuit's language) as a `Cert R_vpa`. -/

namespace Reference

/-- A concrete VPA for the one-pair bracket language over `{op, cl}`: single control state `0`, a
single-symbol stack marker `()`. A call `op` pushes a marker; a return `cl` pops one. Starting and
accepting with the empty stack recognizes balanced bracket strings — the Dyck circuit's language. -/
def chainVpa : Vpa Nat Unit where
  call := fun q s q' _ => q = 0 ∧ s = Sym.op ∧ q' = 0
  ret := fun q s q' _ => q = 0 ∧ s = Sym.cl ∧ q' = 0
  int := fun _ _ _ => False

/-- The run for `op op cl cl` (`n = 2`): the stack grows to genuine height 2, then unwinds to empty. -/
def run2 : List (VStep Nat Unit) :=
  [ ⟨⟨0, []⟩, Sym.op, ⟨0, [()]⟩⟩,
    ⟨⟨0, [()]⟩, Sym.op, ⟨0, [(), ()]⟩⟩,
    ⟨⟨0, [(), ()]⟩, Sym.cl, ⟨0, [()]⟩⟩,
    ⟨⟨0, [()]⟩, Sym.cl, ⟨0, []⟩⟩ ]

-- The run's input word IS `op op cl cl` — a member of the bracket chain `{op^n cl^n}` (`n = 2`),
-- the Dyck circuit's language.
#guard (run2.map (fun s => s.sym)) = [Sym.op, Sym.op, Sym.cl, Sym.cl]

/-- **`run2_accepts`** — `op op cl cl` is genuinely accepted by `chainVpa`: a well-chained run from the
empty stack back to the empty stack, every step obeying the class-driven `stepValid` discipline. -/
theorem run2_accepts : VpaAccepts chainVpa 0 (· = 0) run2 := by
  refine ⟨⟨⟨0, []⟩, Sym.op, ⟨0, [()]⟩⟩, ⟨⟨0, [()]⟩, Sym.cl, ⟨0, []⟩⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro s hs
    fin_cases hs
    · exact ⟨(), ⟨rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨(), ⟨rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨(), [()], ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
    · exact ⟨(), [], ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, trivial⟩

/-- **`run2_as_cert`** — the reference `op op cl cl` run routed through the RUNG: its genuine acceptance
yields, via `vpaAccepts_as_cert`, a `Hypergraph.Cert R_vpa`-shaped certificate. The bracket-chain VPA
really does go through the shared `Hypergraph` certificate object, on a concrete automaton, no `sorry`. -/
theorem run2_as_cert :
    ∃ first last : VStep Nat Unit,
      first.pre.state = 0 ∧
      first.pre.stack = [] ∧
      last.post.state = 0 ∧
      last.post.stack = [] ∧
      (∀ s ∈ run2, stepValid chainVpa s) ∧
      Hypergraph.Cert R_vpa first last run2 :=
  (vpaAccepts_as_cert chainVpa 0 (· = 0) run2).mp run2_accepts

/-- And the concrete run witnesses a genuine reflexive-transitive `R_vpa`-reduction (the shared
substrate's reduction reading), from the first step to the accepting last step. -/
theorem run2_reduces :
    ∃ first last : VStep Nat Unit,
      first.pre.state = 0 ∧ first.pre.stack = [] ∧
      (last.post.state = 0) ∧ last.post.stack = [] ∧
      Relation.ReflTransGen R_vpa first last :=
  vpaAccepts_reduces chainVpa 0 (· = 0) run2 run2_accepts

#assert_axioms run2_accepts
#assert_axioms run2_as_cert

end Reference

/-! ## Residual — decidable template equivalence (NAMED, not proved here).

`run_height` / `stack_height_input_determined` are the ROOT property. The follow-on they enable, stated
precisely so it is a named seam and not a hole:

    For the FINITE-alphabet visibly-nested fragment (this file's `Sym` grid), template equivalence and
    inclusion — "do VPAs `M₁`, `M₂` accept the same nested-word language?", "is L(M₁) ⊆ L(M₂)?" — are
    DECIDABLE (EXPTIME-complete, Alur–Madhusudan), because input-determined stack height gives boolean
    closure (union / intersection / COMPLEMENT) + determinization, and determinized VPAs have decidable
    emptiness. The general-CFG rung (`g.Produces` for arbitrary `g`) PROVABLY cannot have this: CFL
    equivalence is undecidable.

That is the one genuinely new capability the rung opens (assessment §3). It is NOT proved in this lane —
it needs the determinization construction and the emptiness decision procedure — and it is NOT sorry'd.
It is the precisely-stated frontier this rung's root property unlocks.
-/

end Dregg2.Crypto.VpaAsCert
