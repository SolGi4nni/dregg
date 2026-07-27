/-
Route.RegexMatch — regular-expression route matching, modelled as a
deterministic finite automaton (DFA) with an anchored, longest/most-specific
dispatch.

Motivation. The flat precedence router (`Route.Match`) and the host/glob router
(`RouteAdvanced`) match by exact / prefix / `*` / `**` segment classes. A regex
route (a `~ pattern` style location) matches a request PATH against a compiled
regular expression. Two hazards distinguish a correct regex router from a naive
one:

  * catastrophic backtracking (ReDoS): a backtracking NFA engine can take time
    exponential in the input on adversarial patterns. The defence is to run a
    DETERMINISTIC automaton — one transition per input character, no backtrack —
    so match time is LINEAR in the path length regardless of the pattern.
  * unanchored matching: substring semantics let `^/api$` also fire on
    `/api/secret`, a route-confusion / auth-bypass hazard. The defence is to
    ANCHOR — acceptance requires the automaton to consume the ENTIRE path and
    land in an accepting state; a proper prefix or a longer extension does not
    match.

This file models the matcher as a DFA over `Char` and proves both defences, plus
the dispatch contract shared with `Route.Match`: among the routes whose anchored
matcher accepts the path, the most-specific (highest `spec`) wins, ties broken by
earliest table index — and the chosen route is one the table declares.

Theorems:
  * `regex_route_no_catastrophic` — the matcher performs EXACTLY `path.length`
    transitions: linear, no backtracking, no ReDoS (bounded independent of the
    automaton / pattern).
  * `regex_route_anchored` — the exact-string matcher accepts a path IFF the path
    equals the pattern in full: no proper-prefix and no proper-extension false
    match (anchored at both ends).
  * `regex_route_matches` — `bestRegex` selects a route whose matcher accepts the
    path, that the table declares, and than which no matching route is more
    specific (longest/most-specific wins; earliest index on ties).

Everything is a leaf model: it imports only the Lean core and depends on no other
project module, so it verifies in isolation.
-/

namespace Route.RegexMatch

/-! ## A deterministic finite automaton over `Char`

State type `σ` is a parameter: the compiled matcher chooses its own state
encoding (a `Nat` index, a residual-language value, …). The three theorems hold
for every `σ`. -/

/-- A DFA: a start state, a total accepting predicate, and a total transition. -/
structure DFA (σ : Type) where
  start : σ
  accept : σ → Bool
  step : σ → Char → σ

variable {σ : Type}

/-- Run the automaton from state `s`, consuming the input left to right. Each
input character advances the state exactly once — there is no backtracking. -/
def DFA.runFrom (d : DFA σ) (s : σ) : List Char → σ
  | [] => s
  | c :: cs => d.runFrom (d.step s c) cs

/-- Run from the start state. -/
def DFA.run (d : DFA σ) (input : List Char) : σ := d.runFrom d.start input

/-- Anchored acceptance: the WHOLE input is consumed and the final state accepts.
There is no substring / prefix acceptance — the run must cover every character. -/
def DFA.accepts (d : DFA σ) (input : List Char) : Bool := d.accept (d.run input)

/-- The number of transitions taken by a run from `s`: one per input character. -/
def DFA.runSteps (d : DFA σ) (s : σ) : List Char → Nat
  | [] => 0
  | c :: cs => 1 + d.runSteps (d.step s c) cs

/-! ## No catastrophic backtracking (linearity)

A run takes exactly one transition per input character — the work is `O(len)`,
independent of the automaton and hence of the source pattern. This is the formal
content of "the matcher is a DFA / proven-bounded": no exponential blow-up, no
ReDoS. -/

/-- The transition count of a run from any state equals the input length. -/
theorem runSteps_eq_length (d : DFA σ) (s : σ) (input : List Char) :
    d.runSteps s input = input.length := by
  induction input generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp [DFA.runSteps, List.length_cons, ih (d.step s c), Nat.add_comm]

/-- **No catastrophic backtracking.** Matching a path against a DFA route runs in
time LINEAR in the path length — exactly `path.length` transitions, bounded
independently of the pattern. A backtracking engine has no such bound; a DFA does
by construction. -/
theorem regex_route_no_catastrophic (d : DFA σ) (path : List Char) :
    d.runSteps d.start path = path.length :=
  runSteps_eq_length d d.start path

/-! ## Anchored exact-string matcher

`strDFA w` is the compiled automaton for the anchored literal pattern `^w$`. Its
state is the remaining expected suffix (`some rem`), or a dead sink (`none`). It
accepts only when the entire input has been matched (`some []`); a mismatch or a
surplus character sinks to `none` forever. -/

/-- The anchored automaton for the literal string `w`. -/
def strDFA (w : List Char) : DFA (Option (List Char)) where
  start := some w
  accept := fun s => match s with
    | some [] => true
    | _       => false
  step := fun s c => match s with
    | some (e :: rest) => if e == c then some rest else none
    | some []          => none   -- full match already consumed; a surplus char sinks
    | none             => none   -- dead sink is absorbing

/-! Transition/accept equations for `strDFA`, proven by definitional unfolding so
later proofs never expose the raw structure literal. -/

theorem strDFA_step_none (w : List Char) (c : Char) :
    (strDFA w).step none c = none := rfl

theorem strDFA_step_nil (w : List Char) (c : Char) :
    (strDFA w).step (some []) c = none := rfl

theorem strDFA_step_eq (w : List Char) (e c : Char) (rest : List Char) (h : e = c) :
    (strDFA w).step (some (e :: rest)) c = some rest := by
  show (if e == c then some rest else none) = some rest
  have : (e == c) = true := by rw [beq_iff_eq]; exact h
  rw [if_pos this]

theorem strDFA_step_ne (w : List Char) (e c : Char) (rest : List Char) (h : e ≠ c) :
    (strDFA w).step (some (e :: rest)) c = none := by
  show (if e == c then some rest else none) = none
  have : ¬ ((e == c) = true) := by rw [beq_iff_eq]; exact h
  rw [if_neg this]

theorem strDFA_runFrom_cons (w : List Char) (s : Option (List Char)) (c : Char)
    (cs : List Char) :
    (strDFA w).runFrom s (c :: cs) = (strDFA w).runFrom ((strDFA w).step s c) cs := rfl

/-- Once dead, a run stays dead and never accepts. -/
theorem strDFA_run_none (w input : List Char) :
    (strDFA w).accept ((strDFA w).runFrom none input) = false := by
  induction input with
  | nil => rfl
  | cons c cs ih =>
    rw [strDFA_runFrom_cons, strDFA_step_none]; exact ih

/-- Core run characterisation: from a residual suffix `rem`, the run accepts the
input iff the input equals `rem` exactly. -/
theorem strDFA_run_some (w : List Char) :
    ∀ (rem input : List Char),
      (strDFA w).accept ((strDFA w).runFrom (some rem) input) = decide (input = rem) := by
  intro rem input
  induction input generalizing rem with
  | nil =>
    cases rem with
    | nil => rfl
    | cons e rest => rfl
  | cons c cs ih =>
    rw [strDFA_runFrom_cons]
    cases rem with
    | nil =>
      rw [strDFA_step_nil, strDFA_run_none]
      rfl
    | cons e rest =>
      by_cases hec : e = c
      · rw [strDFA_step_eq w e c rest hec, ih rest]
        subst hec
        simp [List.cons.injEq]
      · rw [strDFA_step_ne w e c rest hec, strDFA_run_none]
        have hne : ¬ (c :: cs = e :: rest) := by
          intro hh; injection hh with h1 _; exact hec h1.symm
        simp [hne]

/-- **Anchored matching.** The exact-string route matcher accepts a path IFF the
path equals the pattern in full. Consequences: a proper prefix of `w` is rejected
(no under-consumption), and any proper extension `w ++ (c :: _)` is rejected (no
substring / over-match). This is the anti-route-confusion property: `^w$` fires on
`w` and on nothing else. -/
theorem regex_route_anchored (w path : List Char) :
    (strDFA w).accepts path = true ↔ path = w := by
  unfold DFA.accepts DFA.run
  show (strDFA w).accept ((strDFA w).runFrom (strDFA w).start path) = true ↔ path = w
  have hstart : (strDFA w).start = some w := rfl
  rw [hstart, strDFA_run_some w w path]
  exact decide_eq_true_iff

/-- No proper-extension false match: appending any nonempty suffix to a matched
path breaks the anchored match. (A direct corollary of `regex_route_anchored`,
spelled out as the concrete auth-bypass hazard it rules out.) -/
theorem regex_route_no_extension_match (w suf : List Char) (hsuf : suf ≠ []) :
    (strDFA w).accepts (w ++ suf) = false := by
  have h := regex_route_anchored w (w ++ suf)
  have hne : w ++ suf ≠ w := by
    intro heq
    apply hsuf
    have hlen : (w ++ suf).length = w.length := by rw [heq]
    rw [List.length_append] at hlen
    have hz : suf.length = 0 := by omega
    exact List.length_eq_zero_iff.mp hz
  cases hb : (strDFA w).accepts (w ++ suf) with
  | false => rfl
  | true => exact absurd (h.mp hb) hne

/-! ## Longest / most-specific dispatch

A regex route table is `List (RegexRoute σ H)`. `bestRegex` selects, among the
routes whose anchored matcher accepts the path, the one with the greatest `spec`
(specificity), breaking ties toward the earliest table index — mirroring
`Route.Match.bestMatch`'s class-precedence + least-index discipline. -/

/-- A regex route: a compiled matcher, a specificity score, and a handler. -/
structure RegexRoute (σ : Type) (H : Type) where
  matcher : DFA σ
  spec : Nat
  handler : H

variable {H : Type}

/-- The route's anchored matcher accepts the path. -/
def RegexRoute.hits (path : List Char) (r : RegexRoute σ H) : Bool :=
  r.matcher.accepts path

/-- Keep the more specific of the running best and a candidate; on a tie (equal or
lower spec) keep the running best, which — folded left to right — is the earlier
table entry. -/
def pickMax : Option (RegexRoute σ H) → RegexRoute σ H → Option (RegexRoute σ H)
  | none,   r => some r
  | some b, r => if b.spec < r.spec then some r else some b

/-- Select the winning route: among those whose matcher accepts `path`, the
highest `spec`, earliest index on ties. -/
def bestRegex (rt : List (RegexRoute σ H)) (path : List Char) : Option (RegexRoute σ H) :=
  (rt.filter (RegexRoute.hits path)).foldl pickMax none

/-- The dispatched handler: the winning route's handler, if any route matches. -/
def dispatch (rt : List (RegexRoute σ H)) (path : List Char) : Option H :=
  (bestRegex rt path).map RegexRoute.handler

/-- The fold result is either the seed or an element of the folded list. -/
theorem foldl_pickMax_mem :
    ∀ (l : List (RegexRoute σ H)) (acc : Option (RegexRoute σ H)) {r},
      l.foldl pickMax acc = some r → r ∈ l ∨ acc = some r := by
  intro l
  induction l with
  | nil => intro acc r h; exact Or.inr h
  | cons x xs ih =>
    intro acc r h
    simp only [List.foldl_cons] at h
    rcases ih (pickMax acc x) h with hxs | hacc
    · exact Or.inl (List.mem_cons_of_mem _ hxs)
    · -- pickMax acc x = some r ⇒ r = x, or r = the running best (= acc)
      cases acc with
      | none =>
        simp only [pickMax, Option.some.injEq] at hacc
        subst hacc; exact Or.inl (List.mem_cons_self)
      | some b =>
        simp only [pickMax] at hacc
        by_cases hlt : b.spec < x.spec
        · rw [if_pos hlt, Option.some.injEq] at hacc
          subst hacc; exact Or.inl (List.mem_cons_self)
        · rw [if_neg hlt] at hacc
          exact Or.inr hacc

/-- The fold result dominates every folded element and the seed in `spec`. -/
theorem foldl_pickMax_ge :
    ∀ (l : List (RegexRoute σ H)) (acc : Option (RegexRoute σ H)) {r},
      l.foldl pickMax acc = some r →
        (∀ x ∈ l, x.spec ≤ r.spec) ∧ (∀ a, acc = some a → a.spec ≤ r.spec) := by
  intro l
  induction l with
  | nil =>
    intro acc r h
    simp only [List.foldl_nil] at h
    refine ⟨(by intro x hx; cases hx), ?_⟩
    intro a ha; rw [ha] at h; injection h with h'; subst h'; exact Nat.le_refl _
  | cons x xs ih =>
    intro acc r h
    simp only [List.foldl_cons] at h
    obtain ⟨hxs, hacc'⟩ := ih (pickMax acc x) h
    have hx_le : x.spec ≤ r.spec := by
      cases acc with
      | none => exact hacc' x (by simp [pickMax])
      | some b =>
        by_cases hlt : b.spec < x.spec
        · exact hacc' x (by simp [pickMax, hlt])
        · exact Nat.le_trans (Nat.le_of_not_lt hlt) (hacc' b (by simp [pickMax, hlt]))
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with hzx | hzxs
      · exact hzx ▸ hx_le
      · exact hxs z hzxs
    · intro a ha
      cases acc with
      | none => simp at ha
      | some b =>
        rw [Option.some.injEq] at ha
        by_cases hlt : b.spec < x.spec
        · rw [← ha]; exact Nat.le_trans (Nat.le_of_lt hlt) hx_le
        · rw [← ha]; exact hacc' b (by simp [pickMax, hlt])

/-- **Longest / most-specific dispatch.** If `bestRegex` selects `r`, then `r` is
declared by the table, its anchored matcher accepts the path (so control
dispatches to `r.handler`), and no route whose matcher also accepts the path is
strictly more specific — the winner is a highest-specificity match, ties broken
toward the earliest index. -/
theorem regex_route_matches {rt : List (RegexRoute σ H)} {path : List Char}
    {r : RegexRoute σ H} (h : bestRegex rt path = some r) :
    r ∈ rt ∧ RegexRoute.hits path r = true ∧
      ∀ r' ∈ rt, RegexRoute.hits path r' = true → r'.spec ≤ r.spec := by
  unfold bestRegex at h
  have hmem := foldl_pickMax_mem (rt.filter (RegexRoute.hits path)) none h
  have hin : r ∈ rt.filter (RegexRoute.hits path) := by
    rcases hmem with hm | hnone
    · exact hm
    · exact absurd hnone (by simp)
  have hrt : r ∈ rt ∧ RegexRoute.hits path r = true := List.mem_filter.mp hin
  refine ⟨hrt.1, hrt.2, ?_⟩
  intro r' hr'mem hr'hit
  have hge := (foldl_pickMax_ge (rt.filter (RegexRoute.hits path)) none h).1
  exact hge r' (List.mem_filter.mpr ⟨hr'mem, hr'hit⟩)

/-- Handler-level corollary: a dispatched handler belongs to a declared route
whose anchored matcher accepts the path. -/
theorem regex_route_dispatch {rt : List (RegexRoute σ H)} {path : List Char}
    {hd : H} (h : dispatch rt path = some hd) :
    ∃ r ∈ rt, r.handler = hd ∧ RegexRoute.hits path r = true := by
  unfold dispatch at h
  cases hb : bestRegex rt path with
  | none => rw [hb] at h; simp at h
  | some r =>
    rw [hb] at h
    obtain ⟨hmem, hhit, _⟩ := regex_route_matches hb
    exact ⟨r, hmem, by simpa using h, hhit⟩

end Route.RegexMatch
