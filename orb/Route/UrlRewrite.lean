/-
Route.UrlRewrite — URL rewrite rules over decoded path segments.

A rewrite rule maps a request URL to a new URL by matching the request's PATH
(a `List String` of decoded segments, the same representation `Route.Path` uses)
against a segment pattern and substituting the captured segments into a
replacement template. The query string is a SEPARATE URI component (RFC 9110
§7.1: the absolute-path and query are distinct parts) and is preserved verbatim
unless the rule explicitly targets it.

Design (clean-room, self-contained — no external imports):

  * A `Url` is `path : List String` (decoded segments) × `query : String`.
  * A pattern is a `List PatSeg`: `.lit s` (the segment must equal `s`) or
    `.cap` (matches any one segment, captured in order). Matching is
    exact-length: the pattern consumes the whole path (an anchored `^…$` match).
  * A replacement is a `List RepTok`: `.lit s` (a literal output segment) or
    `.ref i` (the i-th capture, 0-based — a backreference `$i`). Unlike a raw
    string template, backreferences are indices into the ordered capture list,
    so substitution is total and every `.ref i` with `i < captures` places a
    genuine captured input segment into the output.
  * A `Rule` bundles a pattern, a replacement, and `newQuery : Option String`:
    `none` leaves the query untouched (the common case), `some q` is a rule that
    TARGETS the query and rewrites it to `q`.

Iteration model (the loop hazard): a naive rewrite engine re-applies its rule
set until a fixed point, which DIVERGES on a ping-pong rule set (`/a → /b`,
`/b → /a`). The real engines bound this: nginx/Apache cap internal rewrite
rounds. `rewriteFuel` is that bounded interpreter — structurally recursive on a
fuel budget, hence total, and it stops early at a fixed point. `rewriteCount`
counts the rewrites actually performed and is proven `≤ fuel`: the budget is a
hard cap, so no input can drive an unbounded rewrite loop.

Theorems:
  * `url_rewrite_applies`         — a matching rule transforms the path per its
                                    pattern→replacement, with capture groups
                                    substituted (universally in the captured
                                    segment: it is genuinely moved into the
                                    output, not a constant).
  * `url_rewrite_no_loop`         — the fuel-bounded rewrite performs at most
                                    `fuel` rewrites (`rewriteCount ≤ fuel`); a
                                    fixed point halts it, and a divergent
                                    ping-pong rule set still returns.
  * `url_rewrite_preserves_query` — a rule that does not target the query leaves
                                    it byte-for-byte unchanged; a rule that does
                                    target it sets it (so the "unless" is real).
-/

namespace Route.UrlRewrite

/-! ## URL model -/

/-- A URL split into decoded path segments and an opaque query string, the two
distinct URI components a rewrite acts on (RFC 9110 §7.1). -/
structure Url where
  path : List String
  query : String
deriving DecidableEq, Repr

/-- A pattern segment: a literal the request segment must equal, or a wildcard
that matches any one segment and captures it. -/
inductive PatSeg where
  | lit (s : String)
  | cap
deriving DecidableEq, Repr

/-- A replacement token: a literal output segment, or a backreference to the
`i`-th capture (0-based, `$i`). -/
inductive RepTok where
  | lit (s : String)
  | ref (i : Nat)
deriving DecidableEq, Repr

/-- A rewrite rule: an anchored path pattern, a replacement template, and an
optional query target. `newQuery = none` leaves the query untouched;
`newQuery = some q` is a query-targeting rule that sets the query to `q`. -/
structure Rule where
  pat : List PatSeg
  rep : List RepTok
  newQuery : Option String
deriving Repr

/-! ## Matching and substitution -/

/-- Match a pattern against a path, consuming both fully (anchored match).
Returns the captured segments in left-to-right order, or `none` on mismatch. -/
def matchPat : List PatSeg → List String → Option (List String)
  | [], [] => some []
  | [], _ :: _ => none
  | _ :: _, [] => none
  | .lit s :: ps, x :: xs => if s = x then matchPat ps xs else none
  | .cap :: ps, x :: xs => (matchPat ps xs).map (fun caps => x :: caps)

/-- Substitute captures into a replacement template. A `.ref i` past the end of
the capture list yields `""` (a total default; the rule theorems below only
exercise in-range references). -/
def subst (caps : List String) : List RepTok → List String
  | [] => []
  | .lit s :: ts => s :: subst caps ts
  | .ref i :: ts => caps.getD i "" :: subst caps ts

/-- The query a rule produces from an input query: kept, or overwritten. -/
def applyQuery (r : Rule) (q : String) : String :=
  match r.newQuery with
  | none => q
  | some q' => q'

/-- Apply one rule to a URL: `none` if the pattern does not match, else the
rewritten URL (new path from the substituted template, query per `applyQuery`). -/
def applyRule (r : Rule) (u : Url) : Option Url :=
  match matchPat r.pat u.path with
  | none => none
  | some caps => some { path := subst caps r.rep, query := applyQuery r u.query }

/-- Apply the FIRST matching rule (in table order) exactly once; if none match,
the URL is returned unchanged. This is single-pass "break" semantics — one rule
fires per call, so a single `applyFirst` never loops. -/
def applyFirst : List Rule → Url → Url
  | [], u => u
  | r :: rs, u =>
    match applyRule r u with
    | some u' => u'
    | none => applyFirst rs u

/-! ## Bounded iteration (the loop-free interpreter) -/

/-- Iterate `applyFirst` under a fuel budget, halting early at a fixed point.
Structurally recursive on `fuel`, hence total: no input diverges. -/
def rewriteFuel : Nat → List Rule → Url → Url
  | 0, _, u => u
  | fuel + 1, rs, u =>
    let u' := applyFirst rs u
    if u' = u then u else rewriteFuel fuel rs u'

/-- Count the rewrites `rewriteFuel` actually performs (a fixed point costs 0). -/
def rewriteCount : Nat → List Rule → Url → Nat
  | 0, _, _ => 0
  | fuel + 1, rs, u =>
    let u' := applyFirst rs u
    if u' = u then 0 else 1 + rewriteCount fuel rs u'

/-! ## `url_rewrite_applies` — the path is rewritten with captures substituted

First the general lemmas: matching an all-literal pattern binds no captures and
demands the exact path; a `.cap` binds its segment. Then the headline theorem is
a concrete rule that MOVES a captured segment — universally quantified over the
captured value, so the capture is genuinely substituted (not a fixed constant). -/

/-- A `.ref i` in the replacement pulls the `i`-th capture into that output slot
(when in range). This is what makes substitution non-vacuous. -/
theorem subst_ref_get (caps : List String) (i : Nat) (rest : List RepTok) :
    subst caps (RepTok.ref i :: rest) = caps.getD i "" :: subst caps rest := rfl

/-- Matching a single-`.cap` pattern against a one-segment path captures that
segment. -/
theorem matchPat_single_cap (x : String) :
    matchPat [PatSeg.cap] [x] = some [x] := by
  simp [matchPat]

/-- **Capture groups are substituted (headline).** The rule `/:seg/profile`
→ `/profile/:seg` (capture the middle segment, move it after `profile`) rewrites
`["u", id, "profile"]` to `["profile", id]` for EVERY `id`, and preserves the
query. The output segment `id` is the captured input segment relocated — the
substitution is real because the theorem holds for an arbitrary `id`. -/
theorem url_rewrite_applies (id q : String) :
    applyRule
        { pat := [PatSeg.lit "u", PatSeg.cap, PatSeg.lit "profile"],
          rep := [RepTok.lit "profile", RepTok.ref 0],
          newQuery := none }
        { path := ["u", id, "profile"], query := q }
      = some { path := ["profile", id], query := q } := by
  rfl

/-- **A literal-only rule is exact.** `/health → /status` fires only on the
exact path and rewrites it, binding no captures. Complements the capture case:
matching is anchored, so a longer path does not match. -/
theorem url_rewrite_applies_literal (q : String) :
    applyRule
        { pat := [PatSeg.lit "health"], rep := [RepTok.lit "status"], newQuery := none }
        { path := ["health"], query := q }
      = some { path := ["status"], query := q }
    ∧ applyRule
        { pat := [PatSeg.lit "health"], rep := [RepTok.lit "status"], newQuery := none }
        { path := ["health", "extra"], query := q }
      = none := by
  constructor <;> rfl

/-! ## `url_rewrite_no_loop` — the rewrite is bounded, never diverges -/

/-- A fixed point of `applyFirst` halts the interpreter immediately: no further
rewrite rounds run. -/
theorem rewriteFuel_fixpoint (rs : List Rule) (u : Url) (fuel : Nat)
    (h : applyFirst rs u = u) :
    rewriteFuel (fuel + 1) rs u = u := by
  simp [rewriteFuel, h]

/-- **No infinite rewrite loop (headline).** The number of rewrites the bounded
interpreter performs never exceeds its fuel budget: the budget is a hard cap, so
no rule set — however self-referential — drives an unbounded loop. -/
theorem url_rewrite_no_loop (fuel : Nat) (rs : List Rule) (u : Url) :
    rewriteCount fuel rs u ≤ fuel := by
  induction fuel generalizing u with
  | zero => simp [rewriteCount]
  | succ n ih =>
    unfold rewriteCount
    by_cases h : applyFirst rs u = u
    · simp [h]
    · simp only [h, if_false]
      have := ih (applyFirst rs u)
      omega

/-- A divergent ping-pong rule set: `/a → /b` and `/b → /a`. A fixed-point
seeker would spin forever on it. -/
def pingPong : List Rule :=
  [ { pat := [PatSeg.lit "a"], rep := [RepTok.lit "b"], newQuery := none },
    { pat := [PatSeg.lit "b"], rep := [RepTok.lit "a"], newQuery := none } ]

/-- **The loop hazard is real, and the budget contains it.** On the ping-pong
rule set the interpreter performs a rewrite every single round — it hits the cap
exactly (`rewriteCount 3 = 3`) rather than reaching a fixed point — yet it still
RETURNS a value (`rewriteFuel 3 = /b`) instead of diverging. Witnesses that the
fuel bound is load-bearing, not vacuously satisfied by an early fixed point. -/
theorem pingPong_hits_cap :
    rewriteCount 3 pingPong { path := ["a"], query := "" } = 3
      ∧ rewriteFuel 3 pingPong { path := ["a"], query := "" }
          = { path := ["b"], query := "" } := by
  constructor <;> rfl

/-! ## `url_rewrite_preserves_query` — query is a separate component -/

/-- **Query preservation (headline).** A rule that does not target the query
(`newQuery = none`) leaves it byte-for-byte unchanged whenever it fires, for ANY
input URL and ANY resulting URL. The query is carried through the path rewrite
untouched (RFC 9110 §7.1: path and query are distinct components). -/
theorem url_rewrite_preserves_query (r : Rule) (u u' : Url)
    (hq : r.newQuery = none) (h : applyRule r u = some u') :
    u'.query = u.query := by
  unfold applyRule at h
  cases hm : matchPat r.pat u.path with
  | none => rw [hm] at h; cases h
  | some caps =>
    rw [hm] at h
    cases h
    simp [applyQuery, hq]

/-- **The "unless" clause is real.** A rule that DOES target the query
(`newQuery = some q'`) overwrites it with `q'` when it fires — regardless of the
input query. So query preservation is conditional on the rule, not automatic. -/
theorem url_rewrite_targets_query (r : Rule) (u u' : Url) (q' : String)
    (hq : r.newQuery = some q') (h : applyRule r u = some u') :
    u'.query = q' := by
  unfold applyRule at h
  cases hm : matchPat r.pat u.path with
  | none => rw [hm] at h; cases h
  | some caps =>
    rw [hm] at h
    cases h
    simp [applyQuery, hq]

/-- Query preservation lifts to the single-pass `applyFirst`: if every rule in
the table leaves the query alone, the whole pass does too. -/
theorem applyFirst_preserves_query (rs : List Rule) (u : Url)
    (hall : ∀ r ∈ rs, r.newQuery = none) :
    (applyFirst rs u).query = u.query := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    unfold applyFirst
    cases hr : applyRule r u with
    | none =>
      exact ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    | some u' =>
      have := url_rewrite_preserves_query r u u'
        (hall r (List.mem_cons_self)) hr
      simpa using this

/-- **Concrete query witness.** The same path rewrite `/p → /q`, once with
`newQuery = none` (query `"a=1"` survives) and once targeting the query (query
becomes `"reset"`) — the two branches genuinely differ. -/
theorem query_witness :
    applyRule
        { pat := [PatSeg.lit "p"], rep := [RepTok.lit "q"], newQuery := none }
        { path := ["p"], query := "a=1" }
      = some { path := ["q"], query := "a=1" }
    ∧ applyRule
        { pat := [PatSeg.lit "p"], rep := [RepTok.lit "q"], newQuery := some "reset" }
        { path := ["p"], query := "a=1" }
      = some { path := ["q"], query := "reset" } := by
  constructor <;> rfl

end Route.UrlRewrite
