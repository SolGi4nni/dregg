/-
# Dregg2.Crypto.VpaDecidable — boolean closure on the visibly-pushdown rung: the first slice of
DECIDABLE template equivalence.

`Crypto/VpaAsCert` landed the visibly-pushdown rung of the certificate substrate and proved the ROOT
VPL property (`run_height` / `stack_height_input_determined`): the stack height at every input
position is a function of the INPUT WORD ALONE. Its residual note names the one genuinely new
capability that property opens — decidable template equivalence on the finite visibly-nested
fragment (CFL equivalence is undecidable; VPL equivalence is EXPTIME-decidable, Alur–Madhusudan).
The route is boolean closure: `L(M₁) = L(M₂)` iff both `L(M₁) ∩ ∁L(M₂)` and `L(M₂) ∩ ∁L(M₁)` are
empty, and VPL emptiness is decidable. This file lands the tractable first step of that route.

PROVED here (finite `Sym` grid, no `sorry`):
    Lang                    : the nested-word language of a VPA (words of accepting runs)
    prodVpa / prodVpa_lang  : INTERSECTION — the product VPA recognizes exactly `L(M₁) ∩ L(M₂)`,
                              both directions. The backward (zip) direction is where the
                              visibly-pushdown discipline earns its keep: because the stack ACTION
                              is class-driven, two VPAs reading the SAME word push and pop in
                              lockstep, so their stacks zip into ONE product stack with no height
                              bookkeeping — the constructive face of
                              `stack_height_input_determined`.
    lang_wordDelta_zero     : every accepted word has net height 0 (all calls matched)
    lang_wellMatched        : every accepted word is WELL-MATCHED (net 0 AND every prefix ≥ 0) —
                              pinning the correct universe for relative complement
    lang_not_nil            : the empty word is NEVER accepted (runs are non-empty by
                              `VpaAccepts`) — which is why the complement target below carries a
                              `w ≠ []` guard
    equiv_iff_symmDiff_empty: the (pure-logic) reduction of equivalence to two emptiness checks

NAMED (precisely stated, NOT proved — the remaining steps toward decidable equivalence):
    ComplementClosure       : complement on the FINITE fragment, relative to the non-empty
                              well-matched universe (see the def's docstring for why each guard is
                              forced)
    emptiness decision      : deliberately NOT stated as a `Prop` — every Prop-level phrasing we
                              found is a classical tautology; see the closing note for the analysis
                              and for what the genuine artifact must be.

Honest scope: this is the FINITE-alphabet fragment (the `Sym = {op, cl, dat}` bracket grid the Dyck
circuit pins). The templater's infinite `Value` data alphabet is out of scope here — classical VPL
theory (and hence this decidability route) transfers cleanly only to the finite fragment.
-/
import Dregg2.Crypto.VpaAsCert
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.VpaDecidable

open Dregg2.Crypto.VpaAsCert

universe u

variable {S₁ S₂ G₁ G₂ : Type u}

/-! ## The language of a VPA — the words its accepting runs read. -/

/-- **`Lang M q₀ accept w`** — the nested-word LANGUAGE of a VPA: `w` is accepted iff some run
accepted per `VpaAccepts` (non-empty, chained, class-disciplined, empty stack at both ends) reads
exactly `w`. This is the object boolean closure and decidable equivalence are about. -/
def Lang {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop)
    (w : List Sym) : Prop :=
  ∃ run : List (VStep State Gamma), VpaAccepts M q₀ accept run ∧ run.map (fun s => s.sym) = w

/-- **`wordDelta`** — the net stack-height change of a WORD (sum of per-symbol `heightDelta`s):
`runDelta` freed of the run. -/
def wordDelta : List Sym → ℤ
  | [] => 0
  | s :: rest => heightDelta s + wordDelta rest

/-- `runDelta` genuinely factors through the input word — the definitional face of "the height
change depends on the symbols alone". -/
theorem runDelta_eq_wordDelta {State Gamma : Type u} :
    ∀ run : List (VStep State Gamma), runDelta run = wordDelta (run.map (fun s => s.sym))
  | [] => rfl
  | s :: rest => by
    simp only [runDelta, List.map_cons, wordDelta]
    rw [runDelta_eq_wordDelta rest]

/-- **`WellMatched w`** — the word universe empty-stack acceptance lives in: net height 0 (every
call matched) and every prefix non-negative (no return ever fires on an empty stack). This is the
universe RELATIVE complement must be stated against (`lang_wellMatched` shows every `Lang` is
contained in it, so an absolute complement is unreachable by ANY VPA of this acceptance shape). -/
def WellMatched (w : List Sym) : Prop :=
  wordDelta w = 0 ∧ ∀ p : List Sym, p <+: w → 0 ≤ wordDelta p

/-! ## The product construction — INTERSECTION.

States pair, stack symbols pair. The class-driven discipline means the two machines' stacks move in
lockstep over a shared input, so ONE product stack of pairs simulates both — the construction that
is IMPOSSIBLE for general PDAs (whose stacks desynchronize) and is exactly what
`stack_height_input_determined` licenses. -/

/-- **`prodVpa M₁ M₂`** — the product VPA: run both machines in parallel; a transition fires iff
BOTH components fire on the same symbol. Note `Fintype (S₁ × S₂)` is automatic, so the product
never leaves the finite fragment. -/
def prodVpa (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) : Vpa (S₁ × S₂) (G₁ × G₂) where
  call q s q' γ := M₁.call q.1 s q'.1 γ.1 ∧ M₂.call q.2 s q'.2 γ.2
  ret q s q' γ := M₁.ret q.1 s q'.1 γ.1 ∧ M₂.ret q.2 s q'.2 γ.2
  int q s q' := M₁.int q.1 s q'.1 ∧ M₂.int q.2 s q'.2

/-- First projection of a product step: keep the left state, `map Prod.fst` the stack. -/
def projStep₁ (s : VStep (S₁ × S₂) (G₁ × G₂)) : VStep S₁ G₁ :=
  ⟨⟨s.pre.state.1, s.pre.stack.map Prod.fst⟩, s.sym, ⟨s.post.state.1, s.post.stack.map Prod.fst⟩⟩

/-- Second projection of a product step. -/
def projStep₂ (s : VStep (S₁ × S₂) (G₁ × G₂)) : VStep S₂ G₂ :=
  ⟨⟨s.pre.state.2, s.pre.stack.map Prod.snd⟩, s.sym, ⟨s.post.state.2, s.post.stack.map Prod.snd⟩⟩

/-- **`zipStep`** — the converse: one step of each machine on the same symbol zips into a product
step, stacks zipped pointwise. -/
def zipStep (a : VStep S₁ G₁) (b : VStep S₂ G₂) : VStep (S₁ × S₂) (G₁ × G₂) :=
  ⟨⟨(a.pre.state, b.pre.state), a.pre.stack.zip b.pre.stack⟩, a.sym,
   ⟨(a.post.state, b.post.state), a.post.stack.zip b.post.stack⟩⟩

/-- A valid product step projects to a valid left-component step. -/
theorem projStep₁_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (s : VStep (S₁ × S₂) (G₁ × G₂))
    (h : stepValid (prodVpa M₁ M₂) s) : stepValid M₁ (projStep₁ s) := by
  cases hs : s.sym with
  | op =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, ⟨h₁, _⟩, hst⟩ := h
    simp only [stepValid, projStep₁, classOf, hs]
    exact ⟨γ.1, h₁, by rw [hst, List.map_cons]⟩
  | cl =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, rest, ⟨h₁, _⟩, hpre, hpost⟩ := h
    simp only [stepValid, projStep₁, classOf, hs]
    exact ⟨γ.1, rest.map Prod.fst, h₁, by rw [hpre, List.map_cons], by rw [hpost]⟩
  | dat =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    simp only [stepValid, projStep₁, classOf, hs]
    exact ⟨h.1.1, by rw [h.2]⟩

/-- A valid product step projects to a valid right-component step. -/
theorem projStep₂_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (s : VStep (S₁ × S₂) (G₁ × G₂))
    (h : stepValid (prodVpa M₁ M₂) s) : stepValid M₂ (projStep₂ s) := by
  cases hs : s.sym with
  | op =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, ⟨_, h₂⟩, hst⟩ := h
    simp only [stepValid, projStep₂, classOf, hs]
    exact ⟨γ.2, h₂, by rw [hst, List.map_cons]⟩
  | cl =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    obtain ⟨γ, rest, ⟨_, h₂⟩, hpre, hpost⟩ := h
    simp only [stepValid, projStep₂, classOf, hs]
    exact ⟨γ.2, rest.map Prod.snd, h₂, by rw [hpre, List.map_cons], by rw [hpost]⟩
  | dat =>
    simp only [stepValid, classOf, hs, prodVpa] at h
    simp only [stepValid, projStep₂, classOf, hs]
    exact ⟨h.1.2, by rw [h.2]⟩

/-- **`zipStep_valid`** — THE synchronization lemma: two valid component steps on the SAME symbol
zip into a valid product step. No stack-height side condition is needed — on a call both push (the
zipped stack gains one pair), on a return both pop (it loses one), on an internal both stand still.
The class-driven discipline forces the lockstep; this is `stack_height_input_determined` acting
constructively. -/
theorem zipStep_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (a : VStep S₁ G₁) (b : VStep S₂ G₂)
    (hsym : a.sym = b.sym) (ha : stepValid M₁ a) (hb : stepValid M₂ b) :
    stepValid (prodVpa M₁ M₂) (zipStep a b) := by
  cases hs : a.sym with
  | op =>
    have hs' : b.sym = Sym.op := by rw [← hsym]; exact hs
    simp only [stepValid, classOf, hs] at ha
    simp only [stepValid, classOf, hs'] at hb
    obtain ⟨γ₁, hc₁, hst₁⟩ := ha
    obtain ⟨γ₂, hc₂, hst₂⟩ := hb
    simp only [stepValid, zipStep, classOf, hs, prodVpa]
    exact ⟨(γ₁, γ₂), ⟨hc₁, hc₂⟩, by rw [hst₁, hst₂, List.zip_cons_cons]⟩
  | cl =>
    have hs' : b.sym = Sym.cl := by rw [← hsym]; exact hs
    simp only [stepValid, classOf, hs] at ha
    simp only [stepValid, classOf, hs'] at hb
    obtain ⟨γ₁, r₁, hr₁, hpre₁, hpost₁⟩ := ha
    obtain ⟨γ₂, r₂, hr₂, hpre₂, hpost₂⟩ := hb
    simp only [stepValid, zipStep, classOf, hs, prodVpa]
    exact ⟨(γ₁, γ₂), r₁.zip r₂, ⟨hr₁, hr₂⟩, by rw [hpre₁, hpre₂, List.zip_cons_cons],
      by rw [hpost₁, hpost₂]⟩
  | dat =>
    have hs' : b.sym = Sym.dat := by rw [← hsym]; exact hs
    simp only [stepValid, classOf, hs] at ha
    simp only [stepValid, classOf, hs'] at hb
    simp only [stepValid, zipStep, classOf, hs, prodVpa]
    exact ⟨⟨ha.1, hb.1⟩, by rw [ha.2, hb.2]⟩

/-- Projections preserve the chaining relation. -/
theorem projStep₁_R {a b : VStep (S₁ × S₂) (G₁ × G₂)} (h : R_vpa a b) :
    R_vpa (projStep₁ a) (projStep₁ b) := by
  have h' : b.pre = a.post := h
  show (projStep₁ b).pre = (projStep₁ a).post
  simp only [projStep₁]
  rw [h']

/-- Projections preserve the chaining relation (right). -/
theorem projStep₂_R {a b : VStep (S₁ × S₂) (G₁ × G₂)} (h : R_vpa a b) :
    R_vpa (projStep₂ a) (projStep₂ b) := by
  have h' : b.pre = a.post := h
  show (projStep₂ b).pre = (projStep₂ a).post
  simp only [projStep₂]
  rw [h']

/-- Zipping preserves the chaining relation. -/
theorem zipStep_R {a₁ a₂ : VStep S₁ G₁} {b₁ b₂ : VStep S₂ G₂}
    (ha : R_vpa a₁ a₂) (hb : R_vpa b₁ b₂) : R_vpa (zipStep a₁ b₁) (zipStep a₂ b₂) := by
  have ha' : a₂.pre = a₁.post := ha
  have hb' : b₂.pre = b₁.post := hb
  show (zipStep a₂ b₂).pre = (zipStep a₁ b₁).post
  simp only [zipStep]
  rw [ha', hb']

/-- Mapping a chain-preserving function over a run preserves `vchained`. -/
theorem vchained_map {State Gamma State' Gamma' : Type u}
    (f : VStep State Gamma → VStep State' Gamma')
    (hf : ∀ a b : VStep State Gamma, R_vpa a b → R_vpa (f a) (f b)) :
    ∀ run : List (VStep State Gamma), vchained run → vchained (run.map f) := by
  intro run
  induction run with
  | nil => intro _; trivial
  | cons a t ih =>
    intro h
    cases t with
    | nil => trivial
    | cons b rest =>
      obtain ⟨hab, htl⟩ := h
      exact ⟨hf a b hab, ih htl⟩

/-- Zipping two chained runs yields a chained run. -/
theorem vchained_zipWith :
    ∀ (r₁ : List (VStep S₁ G₁)) (r₂ : List (VStep S₂ G₂)),
      vchained r₁ → vchained r₂ → vchained (List.zipWith zipStep r₁ r₂) := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ _ _; trivial
  | cons a₁ t₁ ih =>
    intro r₂ h₁ h₂
    cases r₂ with
    | nil => trivial
    | cons b₁ u =>
      cases t₁ with
      | nil => trivial
      | cons a₂ t =>
        cases u with
        | nil => trivial
        | cons b₂ v =>
          obtain ⟨hra, hta⟩ := h₁
          obtain ⟨hrb, htb⟩ := h₂
          exact ⟨zipStep_R hra hrb, ih (b₂ :: v) hta htb⟩

/-- Zipping two valid runs on the same word yields a valid run. -/
theorem zipWith_valid (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) :
    ∀ (r₁ : List (VStep S₁ G₁)) (r₂ : List (VStep S₂ G₂)),
      r₁.map (fun s => s.sym) = r₂.map (fun s => s.sym) →
      (∀ s ∈ r₁, stepValid M₁ s) → (∀ s ∈ r₂, stepValid M₂ s) →
      ∀ s ∈ List.zipWith zipStep r₁ r₂, stepValid (prodVpa M₁ M₂) s := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ _ _ _ s hs; simp at hs
  | cons a t ih =>
    intro r₂ hword hv₁ hv₂ s hs
    cases r₂ with
    | nil => simp at hs
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at hword
      rw [List.zipWith_cons_cons] at hs
      rcases List.mem_cons.mp hs with h | h
      · subst h
        exact zipStep_valid M₁ M₂ a b hword.1 (hv₁ a (by simp)) (hv₂ b (by simp))
      · exact ih u hword.2 (fun x hx => hv₁ x (List.mem_cons_of_mem a hx))
          (fun x hx => hv₂ x (List.mem_cons_of_mem b hx)) s h

/-- The zipped run reads the left run's word. -/
theorem zipWith_map_sym :
    ∀ (r₁ : List (VStep S₁ G₁)) (r₂ : List (VStep S₂ G₂)),
      r₁.length = r₂.length →
      (List.zipWith zipStep r₁ r₂).map (fun s => s.sym) = r₁.map (fun s => s.sym) := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ _; rfl
  | cons a t ih =>
    intro r₂ hlen
    cases r₂ with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | cons b u =>
      have hlen' : t.length = u.length := by
        simp only [List.length_cons] at hlen; omega
      simp only [List.zipWith_cons_cons, List.map_cons, zipStep, ih u hlen']

/-- `getLast?` commutes with `zipWith` on equal-length lists (both `some`). -/
theorem getLast?_zipWith {A B C : Type u} (f : A → B → C) :
    ∀ (r₁ : List A) (r₂ : List B) (a : A) (b : B),
      r₁.length = r₂.length → r₁.getLast? = some a → r₂.getLast? = some b →
      (List.zipWith f r₁ r₂).getLast? = some (f a b) := by
  intro r₁
  induction r₁ with
  | nil => intro r₂ a b _ ha _; simp at ha
  | cons x t ih =>
    intro r₂ a b hlen ha hb
    cases r₂ with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons y u =>
      cases t with
      | nil =>
        cases u with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at ha hb
          subst ha; subst hb
          simp
        | cons z v => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons p q =>
        cases u with
        | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
        | cons z v =>
          have hlen' : (p :: q).length = (z :: v).length := by
            simp only [List.length_cons] at hlen ⊢; omega
          rw [List.getLast?_cons_cons] at ha hb
          rw [List.zipWith_cons_cons, List.zipWith_cons_cons, List.getLast?_cons_cons,
            ← List.zipWith_cons_cons]
          exact ih (z :: v) a b hlen' ha hb

/-- **`prodVpa_lang`** — INTERSECTION, both directions: the product VPA's language is exactly
`L(M₁) ∩ L(M₂)`. Forward: project the product run componentwise. Backward: the two accepting runs
read the same word, so the class-driven discipline moves their stacks in lockstep and the runs ZIP
into one product run — no height side conditions, the visibly-pushdown synchronization at work.
(For general PDAs this direction is FALSE: CFLs are not closed under intersection.) -/
theorem prodVpa_lang (M₁ : Vpa S₁ G₁) (M₂ : Vpa S₂ G₂) (q₁ : S₁) (q₂ : S₂)
    (acc₁ : S₁ → Prop) (acc₂ : S₂ → Prop) (w : List Sym) :
    Lang (prodVpa M₁ M₂) (q₁, q₂) (fun p => acc₁ p.1 ∧ acc₂ p.2) w ↔
      (Lang M₁ q₁ acc₁ w ∧ Lang M₂ q₂ acc₂ w) := by
  constructor
  · rintro ⟨run, ⟨first, last, hh, hl, hq0, hs0, hacc, hsf, hval, hch⟩, hw⟩
    constructor
    · refine ⟨run.map projStep₁,
        ⟨projStep₁ first, projStep₁ last, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [List.head?_map, hh]; rfl
      · rw [List.getLast?_map, hl]; rfl
      · simp only [projStep₁, hq0]
      · simp only [projStep₁, hs0, List.map_nil]
      · exact hacc.1
      · simp only [projStep₁, hsf, List.map_nil]
      · intro s hs
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        exact projStep₁_valid M₁ M₂ s' (hval s' hs')
      · exact vchained_map projStep₁ (fun a b h => projStep₁_R h) run hch
      · rw [List.map_map]
        exact hw
    · refine ⟨run.map projStep₂,
        ⟨projStep₂ first, projStep₂ last, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [List.head?_map, hh]; rfl
      · rw [List.getLast?_map, hl]; rfl
      · simp only [projStep₂, hq0]
      · simp only [projStep₂, hs0, List.map_nil]
      · exact hacc.2
      · simp only [projStep₂, hsf, List.map_nil]
      · intro s hs
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        exact projStep₂_valid M₁ M₂ s' (hval s' hs')
      · exact vchained_map projStep₂ (fun a b h => projStep₂_R h) run hch
      · rw [List.map_map]
        exact hw
  · rintro ⟨⟨r₁, ⟨f₁, l₁, hh₁, hl₁, hq₁, hs₁, ha₁, hsf₁, hv₁, hc₁⟩, hw₁⟩,
            ⟨r₂, ⟨f₂, l₂, hh₂, hl₂, hq₂, hs₂, ha₂, hsf₂, hv₂, hc₂⟩, hw₂⟩⟩
    have hword : r₁.map (fun s => s.sym) = r₂.map (fun s => s.sym) := by rw [hw₁, hw₂]
    have hlen : r₁.length = r₂.length := by
      simpa using congrArg List.length hword
    refine ⟨List.zipWith zipStep r₁ r₂,
      ⟨zipStep f₁ f₂, zipStep l₁ l₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · cases r₁ with
      | nil => simp at hh₁
      | cons x t =>
        cases r₂ with
        | nil => simp at hh₂
        | cons y u =>
          simp only [List.head?_cons, Option.some.injEq] at hh₁ hh₂
          subst hh₁; subst hh₂
          rfl
    · exact getLast?_zipWith zipStep r₁ r₂ l₁ l₂ hlen hl₁ hl₂
    · simp only [zipStep, hq₁, hq₂]
    · simp only [zipStep, hs₁, hs₂, List.zip_nil_right]
    · exact ⟨ha₁, ha₂⟩
    · simp only [zipStep, hsf₁, hsf₂, List.zip_nil_right]
    · exact zipWith_valid M₁ M₂ r₁ r₂ hword hv₁ hv₂
    · exact vchained_zipWith r₁ r₂ hc₁ hc₂
    · rw [zipWith_map_sym r₁ r₂ hlen, hw₁]

#assert_axioms prodVpa_lang

/-! ## The universe of acceptance — every accepted word is non-empty and well-matched.

These pin the RELATIVE universe the named complement must live in. -/

/-- The empty word is never accepted: `VpaAccepts` demands a non-empty run. -/
theorem lang_not_nil {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State)
    (accept : State → Prop) : ¬ Lang M q₀ accept ([] : List Sym) := by
  rintro ⟨run, ⟨first, last, hh, _, _, _, _, _, _, _⟩, hw⟩
  cases run with
  | nil => simp at hh
  | cons a t => simp at hw

/-- Every accepted word has net height 0 — all calls matched. Direct corollary of `run_height`
with empty stacks at both ends. -/
theorem lang_wordDelta_zero {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State)
    (accept : State → Prop) (w : List Sym) (h : Lang M q₀ accept w) : wordDelta w = 0 := by
  obtain ⟨run, ⟨first, last, hh, hl, hq0, hs0, haccs, hsf, hval, hch⟩, hw⟩ := h
  have hgt := run_height M run hval hch first last hh hl
  rw [hs0, hsf] at hgt
  simp only [List.length_nil, Nat.cast_zero, zero_add] at hgt
  rw [← hw, ← runDelta_eq_wordDelta run]
  omega

/-- `vchained` survives `take` — a prefix of a chained run is chained. -/
theorem vchained_take {State Gamma : Type u} :
    ∀ (run : List (VStep State Gamma)) (n : ℕ), vchained run → vchained (run.take n) := by
  intro run
  induction run with
  | nil => intro n _; rw [List.take_nil]; trivial
  | cons a t ih =>
    intro n h
    cases n with
    | zero => trivial
    | succ m =>
      cases t with
      | nil => rw [List.take_succ_cons, List.take_nil]; trivial
      | cons b rest =>
        cases m with
        | zero => trivial
        | succ k =>
          obtain ⟨hab, htl⟩ := h
          exact ⟨hab, ih (k + 1) htl⟩

/-- A non-empty prefix of a run keeps the run's head. -/
theorem head?_take {A : Type u} : ∀ (l : List A) (k : ℕ), l.take k ≠ [] → (l.take k).head? = l.head?
  | [], k, h => by rw [List.take_nil] at h; exact absurd rfl h
  | _ :: _, 0, h => absurd rfl h
  | _ :: _, _ + 1, _ => rfl

/-- Every non-empty list has a `getLast?`. -/
theorem exists_getLast? {A : Type u} : ∀ (l : List A), l ≠ [] → ∃ a, l.getLast? = some a
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.getLast?_singleton⟩
  | a :: b :: t, _ =>
    let ⟨x, hx⟩ := exists_getLast? (b :: t) (List.cons_ne_nil b t)
    ⟨x, by rw [List.getLast?_cons_cons]; exact hx⟩

/-- **`lang_wellMatched`** — every accepted word is WELL-MATCHED: net height 0 AND every prefix
non-negative. The prefix bound is `run_height` on the truncated run: the height after any prefix IS
a stack length, hence ≥ 0. So `Lang M ⊆ WellMatched` for EVERY machine of this acceptance shape —
absolute complement is unreachable, and the complement target below is stated relative to
`WellMatched`. -/
theorem lang_wellMatched {State Gamma : Type u} (M : Vpa State Gamma) (q₀ : State)
    (accept : State → Prop) (w : List Sym) (h : Lang M q₀ accept w) : WellMatched w := by
  refine ⟨lang_wordDelta_zero M q₀ accept w h, ?_⟩
  obtain ⟨run, ⟨first, last, hh, hl, hq0, hs0, haccs, hsf, hval, hch⟩, hw⟩ := h
  intro p hp
  obtain ⟨tail, ht⟩ := hp
  have hpk : w.take p.length = p := by rw [← ht, List.take_left]
  rw [← hpk]
  by_cases hnil : run.take p.length = []
  · have hwn : w.take p.length = [] := by
      rw [← hw, ← List.map_take, hnil, List.map_nil]
    rw [hwn]
    simp [wordDelta]
  · obtain ⟨lastk, hlk⟩ := exists_getLast? (run.take p.length) hnil
    have hheadk : (run.take p.length).head? = some first :=
      (head?_take run p.length hnil).trans hh
    have hvalk : ∀ s ∈ run.take p.length, stepValid M s :=
      fun s hs => hval s (List.take_subset p.length run hs)
    have hchk := vchained_take run p.length hch
    have hgt := run_height M (run.take p.length) hvalk hchk first lastk hheadk hlk
    rw [hs0] at hgt
    simp only [List.length_nil, Nat.cast_zero, zero_add] at hgt
    have hde : runDelta (run.take p.length) = wordDelta (w.take p.length) := by
      rw [runDelta_eq_wordDelta (run.take p.length), List.map_take, hw]
    rw [hde] at hgt
    omega

#assert_axioms lang_not_nil
#assert_axioms lang_wordDelta_zero
#assert_axioms lang_wellMatched

/-! ## The decision pipeline — equivalence reduces to two emptiness checks. -/

/-- **`equiv_iff_symmDiff_empty`** — pure-logic glue (no automaton content, stated to fix the
pipeline's SHAPE): two languages agree iff both one-sided differences are empty. With `prodVpa_lang`
(intersection, PROVED above) and `ComplementClosure` (named below), each one-sided difference
`L(M₁) ∩ ∁L(M₂)` is again a VPL on the finite fragment — so decidable equivalence needs exactly the
two named seams: complement and emptiness. -/
theorem equiv_iff_symmDiff_empty (P₁ P₂ : List Sym → Prop) :
    (∀ w, P₁ w ↔ P₂ w) ↔ (¬ ∃ w, P₁ w ∧ ¬ P₂ w) ∧ (¬ ∃ w, P₂ w ∧ ¬ P₁ w) := by
  constructor
  · intro h
    exact ⟨fun ⟨w, h₁, h₂⟩ => h₂ ((h w).mp h₁), fun ⟨w, h₁, h₂⟩ => h₂ ((h w).mpr h₁)⟩
  · rintro ⟨h₁, h₂⟩ w
    constructor
    · intro hw
      by_contra hc
      exact h₁ ⟨w, hw, hc⟩
    · intro hw
      by_contra hc
      exact h₂ ⟨w, hw, hc⟩

#assert_axioms equiv_iff_symmDiff_empty

/-! ## NAMED SEAM 1 — complement on the finite fragment.

Each guard in the statement is FORCED, not stylistic:
  * `Fintype S`/`Fintype G` on BOTH sides — over unrestricted (infinite-state, `Prop`-transition)
    machines every subset of the accepted-word universe is some machine's language, so unrestricted
    "closure" would be classically trivial. The finite fragment is where the statement has content
    (and is where Alur–Madhusudan prove it, via determinization over summary-pair state spaces —
    which stays finite).
  * relative to `WellMatched` — `lang_wellMatched`: NO machine of this acceptance shape accepts an
    ill-matched word, so an absolute complement (which would have to) is unreachable.
  * `w ≠ []` — `lang_not_nil`: NO machine accepts the empty word (runs are non-empty), and `[]` is
    well-matched, so the empty word must be exempted or the target is falsified at `w = []`. -/

/-- **`ComplementClosure`** (NOT proved here) — the precisely-stated complement target: for every
finite-fragment VPA there is a finite-fragment VPA recognizing exactly the non-empty well-matched
words the original rejects. The known route is determinization (subset construction over summary
pairs, Alur–Madhusudan) + accept-flip relative to the well-matched universe; that construction is
the genuinely remaining work toward decidable equivalence, together with the emptiness decision
(see the closing note). -/
def ComplementClosure : Prop :=
  ∀ (S G : Type) (_ : Fintype S) (_ : Fintype G) (M : Vpa S G) (q₀ : S) (acc : S → Prop),
    ∃ (S' G' : Type) (_ : Fintype S') (_ : Fintype G') (M' : Vpa S' G') (q₀' : S')
      (acc' : S' → Prop),
      ∀ w : List Sym, w ≠ [] →
        (Lang M' q₀' acc' w ↔ (WellMatched w ∧ ¬ Lang M q₀ acc w))

/-! ## NAMED SEAM 2 — the emptiness decision (deliberately NOT a `Prop`).

Every Prop-level phrasing of "emptiness is decidable" we examined is a CLASSICAL TAUTOLOGY, so
stating one and later "proving" it would launder vacuity as progress:

  * `∀ M, (∃ w, Lang M … w) ∨ ¬(∃ w, Lang M … w)` — excluded middle.
  * `∀ M, ∃ b : Bool, b = true ↔ (∃ w, Lang M … w)` — `by_cases` on the right side.
  * `∀ M, ∃ B : ℕ, (∃ w, Lang M … w) → ∃ w, Lang M … w ∧ w.length ≤ B` — if the language is
    non-empty, classically pick any accepted word and let `B` be its length.
  * even `∃ f : ℕ → ℕ → ℕ, ∀ M, …bound by f (card S) (card G)…` — for fixed finite cards there
    are (classically) only finitely many transition relations, so a sup exists without content.

The genuine remaining artifact is therefore one of:
  (a) a CONCRETE bound function `f` (from the VPA→CFG translation's derivation-length pumping
      bound) with its proof — real combinatorial content, usable with a bounded search; or
  (b) a COMPUTABLE `Decidable` instance for `∃ w, Lang M q₀ acc w` (for `DecidableEq`/decidable-
      transition machines), via the standard reachable-summary saturation — real algorithmic
      content.
Either, combined with `prodVpa_lang` (proved) + `ComplementClosure` (named) +
`equiv_iff_symmDiff_empty` (proved), yields DECIDABLE TEMPLATE EQUIVALENCE on the finite
visibly-nested fragment — the capability the general-CFG rung provably cannot have. -/

/-! ## Non-vacuity — the intersection theorem on the concrete Dyck reference machine. -/

namespace Reference

open Dregg2.Crypto.VpaAsCert.Reference

/-- `op op cl cl` (the Dyck circuit's `n = 2` bracket chain) is in the language of the PRODUCT of
the reference bracket VPA with itself — routed through `prodVpa_lang`'s backward (zip) direction on
the concrete `run2`, so the synchronized product construction is exercised on a real machine. -/
theorem word2_in_prod :
    Lang (prodVpa chainVpa chainVpa) (0, 0) (fun p => p.1 = 0 ∧ p.2 = 0)
      [Sym.op, Sym.op, Sym.cl, Sym.cl] :=
  (prodVpa_lang chainVpa chainVpa 0 0 (· = 0) (· = 0) _).mpr
    ⟨⟨run2, run2_accepts, rfl⟩, ⟨run2, run2_accepts, rfl⟩⟩

/-- And forward: the product membership projects back to membership in each component. -/
theorem word2_components :
    Lang chainVpa 0 (· = 0) [Sym.op, Sym.op, Sym.cl, Sym.cl] ∧
    Lang chainVpa 0 (· = 0) [Sym.op, Sym.op, Sym.cl, Sym.cl] :=
  (prodVpa_lang chainVpa chainVpa 0 0 (· = 0) (· = 0) _).mp word2_in_prod

#assert_axioms word2_in_prod
#assert_axioms word2_components

end Reference

/-! ## Residual (recap)

PROVED: intersection (`prodVpa_lang`, both directions, finiteness-preserving since
`Fintype (S₁ × S₂)` is automatic) · the acceptance universe (`lang_wellMatched`,
`lang_wordDelta_zero`, `lang_not_nil`) · the equivalence→emptiness reduction
(`equiv_iff_symmDiff_empty`).

NAMED, with the precise statement and the known route: `ComplementClosure` (determinization +
accept-flip, relative to non-empty `WellMatched`, finite fragment) and the emptiness decision (a
concrete pumping bound or a computable `Decidable` instance — NOT a Prop, per the vacuity analysis
above). Union needs no separate seam: `∁(∁L₁ ∩ ∁L₂)` via the two named pieces, or directly by a
disjoint-sum construction. All of this is the FINITE `Sym` fragment; the templater's infinite
`Value` alphabet stays out of scope, exactly as in `VpaAsCert`'s honest-scope note.
-/

end Dregg2.Crypto.VpaDecidable
