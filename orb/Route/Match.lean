import RouteAdvanced

/-
Route.Match — host/route matching as a total function with a precedence order.

A route table is a `List (Route H)`. Each route carries a path pattern that is
exactly one of three precedence classes:

  * `exact`   — the request segment list equals the pattern (rank 2, highest);
  * `prefix`  — the pattern is a prefix of the request (rank 1);
  * `default` — matches unconditionally (rank 0, the explicit catch-all).

Matching selects with two rules, in order:

  1. **class precedence** — exact beats prefix beats default;
  2. **least index** — among routes of the winning class, the earliest in the
     table wins (the first-match tie-break, no ambiguity).

`bestMatch` realizes this as `find?`-first per class, tried highest-class-first,
so both rules hold by construction.

Theorems:
  * `bestMatch_total`     — a table containing a default always matches (totality:
                            always some route, never a stuck request).
  * `bestMatch_sound`     — the chosen route actually matches the request.
  * `bestMatch_mem`       — the chosen route is in the table.
  * `bestMatch_class_max` — determinism: no matching route outranks the chosen
                            one (the chosen route is a highest-precedence match).
  * `bestMatch_is_first_of_class` — determinism: the chosen route is the FIRST
                            route of the winning class (least-index tie-break).
-/

namespace Route.Match

/-- A compiled path pattern over segment lists, one per precedence class. -/
inductive Pat where
  | exact (segs : List String)
  | «prefix» (segs : List String)
  | «default»
deriving Repr

/-- A route: a pattern plus a handler of arbitrary type `H`. -/
structure Route (H : Type) where
  pat : Pat
  handler : H

variable {H : Type}

/-- Precedence rank of a class: exact (2) > prefix (1) > default (0). -/
def classRank : Pat → Nat
  | .exact _ => 2
  | .prefix _ => 1
  | .default => 0

/-! ### Per-class match predicates (Bool, one true per route at most) -/

/-- The route is an exact route whose pattern equals the request. -/
def matchesExact (req : List String) : Route H → Bool :=
  fun r => match r.pat with | .exact s => decide (req = s) | _ => false

/-- The route is a prefix route whose pattern is a prefix of the request. -/
def matchesPrefix (req : List String) : Route H → Bool :=
  fun r => match r.pat with | .prefix s => s.isPrefixOf req | _ => false

/-- The route is the default route. -/
def matchesDefault : Route H → Bool :=
  fun r => match r.pat with | .default => true | _ => false

/-- The route matches the request in some class. -/
def matchesAny (req : List String) (r : Route H) : Bool :=
  matchesExact req r || matchesPrefix req r || matchesDefault r

/-- **Route selection.** Try the highest class first; within a class take the
first (least-index) match. -/
def bestMatch (rt : List (Route H)) (req : List String) : Option (Route H) :=
  match rt.find? (matchesExact req) with
  | some r => some r
  | none =>
    match rt.find? (matchesPrefix req) with
    | some r => some r
    | none => rt.find? matchesDefault

/-! ### Small list helpers (kept local to avoid core-API name drift) -/

theorem find?_isSome_of_mem {α} {p : α → Bool} {a : α} {l : List α}
    (hmem : a ∈ l) (hp : p a = true) : (l.find? p).isSome := by
  induction l with
  | nil => cases hmem
  | cons b rest ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp [List.find?, hp]
    · cases hb : p b with
      | true => simp [List.find?, hb]
      | false => simp only [List.find?, hb]; exact ih h

theorem find?_all_false_of_none {α} {p : α → Bool} {l : List α}
    (h : l.find? p = none) : ∀ a ∈ l, p a = false := by
  induction l with
  | nil => intro a ha; cases ha
  | cons b rest ih =>
    intro a ha
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h
    | false =>
      rw [List.find?, hb] at h
      rcases List.mem_cons.mp ha with h' | h'
      · subst h'; exact hb
      · exact ih h a h'

theorem find?_pred_true {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; exact hb
    | false => rw [List.find?, hb] at h; exact ih h

theorem find?_mem {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; exact List.mem_cons_self _ _
    | false => rw [List.find?, hb] at h; exact List.mem_cons_of_mem _ (ih h)

/-! ### Pattern classification -/

theorem matchesExact_exact {req : List String} {r : Route H}
    (h : matchesExact req r = true) : ∃ s, r.pat = Pat.exact s := by
  unfold matchesExact at h
  cases hp : r.pat with
  | exact s => exact ⟨s, rfl⟩
  | «prefix» s => rw [hp] at h; simp at h
  | «default» => rw [hp] at h; simp at h

theorem matchesPrefix_prefix {req : List String} {r : Route H}
    (h : matchesPrefix req r = true) : ∃ s, r.pat = Pat.prefix s := by
  unfold matchesPrefix at h
  cases hp : r.pat with
  | exact s => rw [hp] at h; simp at h
  | «prefix» s => exact ⟨s, rfl⟩
  | «default» => rw [hp] at h; simp at h

theorem matchesDefault_default {r : Route H}
    (h : matchesDefault r = true) : r.pat = Pat.default := by
  unfold matchesDefault at h
  cases hp : r.pat with
  | exact s => rw [hp] at h; simp at h
  | «prefix» s => rw [hp] at h; simp at h
  | «default» => rfl

/-- If a route matches in any class, its own class is the one that fired: the
Bool `matchesAny` collapses to the single predicate its constructor allows. -/
theorem matchesAny_exact {req : List String} {r : Route H} {s : List String}
    (hp : r.pat = Pat.exact s) : matchesAny req r = matchesExact req r := by
  unfold matchesAny matchesPrefix matchesDefault
  rw [hp]; simp

theorem matchesAny_prefix {req : List String} {r : Route H} {s : List String}
    (hp : r.pat = Pat.prefix s) : matchesAny req r = matchesPrefix req r := by
  unfold matchesAny matchesExact matchesDefault
  rw [hp]; simp

theorem matchesAny_default {req : List String} {r : Route H}
    (hp : r.pat = Pat.default) : matchesAny req r = matchesDefault r := by
  unfold matchesAny matchesExact matchesPrefix
  rw [hp]; simp

/-! ### Totality -/

/-- **Match totality.** A route table that contains a default route always
returns some route (the request is never stuck). -/
theorem bestMatch_total {rt : List (Route H)} {req : List String}
    (hdef : ∃ r ∈ rt, matchesDefault r = true) :
    (bestMatch rt req).isSome := by
  obtain ⟨rd, hmem, hd⟩ := hdef
  unfold bestMatch
  cases he : rt.find? (matchesExact req) with
  | some r => simp
  | none =>
    cases hpf : rt.find? (matchesPrefix req) with
    | some r => simp
    | none => simpa using find?_isSome_of_mem hmem hd

/-! ### Soundness + membership -/

/-- **Soundness.** The chosen route matches the request. -/
theorem bestMatch_sound {rt : List (Route H)} {req : List String} {r : Route H}
    (h : bestMatch rt req = some r) : matchesAny req r = true := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re =>
    rw [he] at h; cases h
    have hx := find?_pred_true he
    obtain ⟨s, hp⟩ := matchesExact_exact hx
    rw [matchesAny_exact hp]; exact hx
  | none =>
    rw [he] at h
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp =>
      rw [hpf] at h; cases h
      have hx := find?_pred_true hpf
      obtain ⟨s, hp⟩ := matchesPrefix_prefix hx
      rw [matchesAny_prefix hp]; exact hx
    | none =>
      rw [hpf] at h
      have hx := find?_pred_true h
      have hp := matchesDefault_default hx
      rw [matchesAny_default hp]; exact hx

/-- **Membership.** The chosen route is drawn from the table. -/
theorem bestMatch_mem {rt : List (Route H)} {req : List String} {r : Route H}
    (h : bestMatch rt req = some r) : r ∈ rt := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re => rw [he] at h; cases h; exact find?_mem he
  | none =>
    rw [he] at h
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp => rw [hpf] at h; cases h; exact find?_mem hpf
    | none => rw [hpf] at h; exact find?_mem h

/-! ### Determinism -/

/-- **Determinism (class precedence).** No route matching the request has a
strictly higher precedence class than the chosen one — the chosen route is a
highest-precedence match. -/
theorem bestMatch_class_max {rt : List (Route H)} {req : List String} {r : Route H}
    (h : bestMatch rt req = some r) :
    ∀ r' ∈ rt, matchesAny req r' = true → classRank r'.pat ≤ classRank r.pat := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re =>
    -- winner is exact (rank 2 = maximum)
    rw [he] at h; cases h
    obtain ⟨s, hp⟩ := matchesExact_exact (find?_pred_true he)
    intro r' _ _
    rw [hp]; cases r'.pat <;> simp [classRank]
  | none =>
    rw [he] at h
    have hnoExact := find?_all_false_of_none he
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp =>
      -- winner is prefix (rank 1); no exact match exists, so rank ≤ 1
      rw [hpf] at h; cases h
      obtain ⟨s, hp⟩ := matchesPrefix_prefix (find?_pred_true hpf)
      intro r' hmem hany
      rw [hp]
      -- goal: classRank r'.pat ≤ 1
      cases hp' : r'.pat with
      | exact s' =>
        exfalso
        have : matchesExact req r' = true := by
          have := matchesAny_exact (req := req) (r := r') hp'
          rw [this] at hany; exact hany
        rw [hnoExact r' hmem] at this; cases this
      | «prefix» s' => simp [classRank]
      | «default» => simp [classRank]
    | none =>
      -- winner is default (rank 0); neither exact nor prefix matches exist
      rw [hpf] at h
      have hnoPrefix := find?_all_false_of_none hpf
      obtain hp := matchesDefault_default (find?_pred_true h)
      intro r' hmem hany
      rw [hp]
      cases hp' : r'.pat with
      | exact s' =>
        exfalso
        have : matchesExact req r' = true := by
          have := matchesAny_exact (req := req) (r := r') hp'
          rw [this] at hany; exact hany
        rw [hnoExact r' hmem] at this; cases this
      | «prefix» s' =>
        exfalso
        have : matchesPrefix req r' = true := by
          have := matchesAny_prefix (req := req) (r := r') hp'
          rw [this] at hany; exact hany
        rw [hnoPrefix r' hmem] at this; cases this
      | «default» => simp [classRank]

/-- **Determinism (least-index within class).** The chosen route is the first
route of the winning class in table order: every earlier route fails the
winning class's predicate. Phrased on the winning-class `find?`, which is what
`bestMatch` returns. -/
theorem bestMatch_is_first_of_class {rt : List (Route H)} {req : List String}
    {r : Route H} (h : bestMatch rt req = some r) :
    (rt.find? (matchesExact req) = some r)
      ∨ (rt.find? (matchesExact req) = none ∧ rt.find? (matchesPrefix req) = some r)
      ∨ (rt.find? (matchesExact req) = none ∧ rt.find? (matchesPrefix req) = none
          ∧ rt.find? matchesDefault = some r) := by
  unfold bestMatch at h
  cases he : rt.find? (matchesExact req) with
  | some re => rw [he] at h; cases h; exact Or.inl rfl
  | none =>
    rw [he] at h
    cases hpf : rt.find? (matchesPrefix req) with
    | some rp => rw [hpf] at h; cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | none => rw [hpf] at h; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)

/-! ## Host- and glob-aware dispatch (RFC 9110 §7.2 authority selection + `*`/`**`)

The flat `bestMatch` table above matches path segments only. Virtual-host routing
needs two further dimensions: authority (Host / SNI) selection, and glob path
patterns (`*` = one segment, `**` = any suffix). Both are already proven in the
sibling `RouteAdvanced` router (two-level host-block → first-match route dispatch,
with `*`/`**` globs and RFC 9110 §7.4 host isolation). Rather than re-derive them,
this section composes that router with the flat precedence table as a fallback and
exposes the pair as one handler-returning dispatch the application layer drives.

`dispatchHandler blocks flat r`:
  1. try the virtual-host blocks (`RouteAdvanced.dispatch`: pick the first block
     whose host pattern matches the request authority, then that block's first
     matching route, glob included);
  2. on no host-block match, fall back to the flat exact/prefix/default table
     (`bestMatch`) — preserving the existing host-agnostic behavior exactly.
-/

/-- Unified host/glob dispatch: the proven virtual-host router first, else the
flat precedence table. Returns the winning route's handler. -/
def dispatchHandler
    (blocks : List (RouteAdvanced.ServerBlock H)) (flat : List (Route H))
    (r : RouteAdvanced.Req) : Option H :=
  match RouteAdvanced.dispatch blocks r with
  | some rt => some rt.handler
  | none    => (bestMatch flat r.segs).map (fun x => x.handler)

/-- **Conservative extension.** With no virtual-host blocks the unified dispatch
is exactly the flat `bestMatch` over the same request path: the existing
host-agnostic routing is preserved byte-for-byte when host routing is unused. -/
theorem dispatchHandler_no_blocks (flat : List (Route H)) (r : RouteAdvanced.Req) :
    dispatchHandler [] flat r = (bestMatch flat r.segs).map (fun x => x.handler) := by
  unfold dispatchHandler RouteAdvanced.dispatch RouteAdvanced.selectBlock
  simp [List.find?]

/-- **Host isolation (RFC 9110 §7.4).** A request whose authority is not `hB` is
never served by a virtual-host block bound to the exact host `hB`: `selectBlock`
cannot return that block, so its handler is unreachable for this request. Wired
straight from `RouteAdvanced.route_host_isolation`. -/
theorem dispatchHandler_host_isolation
    {blocks : List (RouteAdvanced.ServerBlock H)} {r : RouteAdvanced.Req}
    {b : RouteAdvanced.ServerBlock H} {hB : List String}
    (hb : b.host = RouteAdvanced.HostPat.exact hB) (hne : r.host ≠ hB) :
    RouteAdvanced.selectBlock blocks r ≠ some b :=
  RouteAdvanced.route_host_isolation hb hne

/-- **Glob soundness.** A `**`-suffix route whose explicit segments match a prefix
`front` matches `front ++ suf` for ANY suffix `suf`: the trailing `**` absorbs the
rest of the path. Wired from `RouteAdvanced.matchPrefixSegs_append`. -/
theorem glob_matches_suffix {ps : List RouteAdvanced.SegPat} {front : List String}
    (h : RouteAdvanced.matchAll ps front = true) (suf : List String) :
    RouteAdvanced.pathMatch { segs := ps, globstar := true } (front ++ suf) = true := by
  unfold RouteAdvanced.pathMatch
  simp only [if_pos rfl]
  exact RouteAdvanced.matchPrefixSegs_append h suf

/-- **Totality.** When no virtual-host block matches but the flat table carries a
default route, the unified dispatch always returns a handler (never stuck). Rides
on `bestMatch_total`. -/
theorem dispatchHandler_isSome_of_default
    {blocks : List (RouteAdvanced.ServerBlock H)} {flat : List (Route H)}
    {r : RouteAdvanced.Req}
    (hdef : ∃ rr ∈ flat, matchesDefault rr = true)
    (hno : RouteAdvanced.dispatch blocks r = none) :
    (dispatchHandler blocks flat r).isSome := by
  unfold dispatchHandler
  rw [hno]
  have hsome := bestMatch_total (rt := flat) (req := r.segs) hdef
  cases hb : bestMatch flat r.segs with
  | none => rw [hb] at hsome; simp at hsome
  | some x => simp

/-- **Declared-exposure generalization of `bestMatch_mem`.** Every handler the
unified host/glob dispatch can select is a *declared* handler: it is either the
handler of some route in some virtual-host block, or the handler of some route in
the flat precedence table. This lifts `bestMatch_mem` — the tenant-isolation
exposure argument, "a served route is drawn from the declared table" — from the
flat matcher to the full host+glob matcher: a served route is one the matcher
selects from the declared tables, host-block or not. So routing over host-blocks
does not escape the declared surface, and the exposure accounting the isolation
model builds on `bestMatch_mem` generalizes to `dispatchHandler`. -/
theorem dispatchHandler_mem_declared
    {blocks : List (RouteAdvanced.ServerBlock H)} {flat : List (Route H)}
    {r : RouteAdvanced.Req} {h : H}
    (hd : dispatchHandler blocks flat r = some h) :
    (∃ b ∈ blocks, ∃ rt ∈ b.routes, rt.handler = h)
      ∨ (∃ fr ∈ flat, fr.handler = h) := by
  unfold dispatchHandler at hd
  cases hdisp : RouteAdvanced.dispatch blocks r with
  | some rt =>
    rw [hdisp] at hd
    simp only [Option.some.injEq] at hd
    obtain ⟨b, hsel, hmem, _⟩ := RouteAdvanced.dispatch_block hdisp
    exact Or.inl ⟨b, RouteAdvanced.find?_mem hsel, rt, hmem, hd⟩
  | none =>
    rw [hdisp] at hd
    cases hb : bestMatch flat r.segs with
    | none => rw [hb] at hd; simp at hd
    | some fr =>
      rw [hb] at hd
      simp only [Option.map_some', Option.some.injEq] at hd
      exact Or.inr ⟨fr, bestMatch_mem hb, hd⟩

/-! ### Concrete witness — host discrimination and glob are real (`H := Nat`)

These execute the unified dispatch on concrete inputs so neither feature is
vacuous: the SAME path `/health` under two different authorities selects two
DIFFERENT handlers, and a `/assets/**` glob route matches a multi-segment suffix. -/

/-- Two virtual-host blocks — `a.example` and `b.example` — each with a `/health`
route returning a DIFFERENT handler id; the `a.example` block also carries an
`/assets/**` glob route. -/
def demoBlocks : List (RouteAdvanced.ServerBlock Nat) :=
  [ { host := .exact ["a", "example"],
      routes :=
        [ { method := .anyMethod, path := { segs := [.lit "health"], globstar := false },
            guards := [], handler := 1 },
          { method := .anyMethod, path := { segs := [.lit "assets"], globstar := true },
            guards := [], handler := 2 } ] },
    { host := .exact ["b", "example"],
      routes :=
        [ { method := .anyMethod, path := { segs := [.lit "health"], globstar := false },
            guards := [], handler := 3 } ] } ]

/-- Build a `RouteAdvanced.Req` from split host labels and path segments. -/
def reqOf (host segs : List String) : RouteAdvanced.Req :=
  { host := host, method := "GET", segs := segs, headers := [], query := [] }

/-- **Host discrimination is real.** Same path `/health`, different `Host` → a
different handler fires. -/
theorem demo_host_discriminates :
    dispatchHandler demoBlocks [] (reqOf ["a", "example"] ["health"]) = some 1
      ∧ dispatchHandler demoBlocks [] (reqOf ["b", "example"] ["health"]) = some 3 := by
  constructor <;> decide

/-- **Glob is real.** The `/assets/**` route matches a multi-segment suffix. -/
theorem demo_glob_matches :
    dispatchHandler demoBlocks [] (reqOf ["a", "example"] ["assets", "img", "logo.png"])
      = some 2 := by decide

/-! ### Concrete witness — method matching is real (`H := Nat`)

The method dimension is `RouteAdvanced.MethodPat` (`anyMethod` / `exact m`), matched
by `RouteAdvanced.routeMatches` (`methodMatch r.method req.method`) — already proven,
and composed into `dispatchHandler` through `RouteAdvanced.dispatch`. This witness
executes it on concrete inputs so method-scoped routing is not vacuous: the SAME path
`/x` under two different methods selects two DIFFERENT handlers — a `GET`-guarded route
fires for `GET`, and a `POST` falls through to the block's catch-all. -/

/-- One `anyHost` block: a `GET`-only `/x` route (handler `10`) ahead of a catch-all
(handler `20`). -/
def demoMethodBlocks : List (RouteAdvanced.ServerBlock Nat) :=
  [ { host := .anyHost,
      routes :=
        [ { method := .exact "GET", path := { segs := [.lit "x"], globstar := false },
            guards := [], handler := 10 },
          RouteAdvanced.catchAllRoute 20 ] } ]

/-- Build a `RouteAdvanced.Req` at an explicit method. -/
def reqOfMethod (method : String) (host segs : List String) : RouteAdvanced.Req :=
  { host := host, method := method, segs := segs, headers := [], query := [] }

/-- **Method discrimination is real.** Same path `/x`, different method → a different
handler fires: `GET /x` hits the method-guarded route (`10`), `POST /x` misses it and
falls to the block's catch-all (`20`). -/
theorem demo_method_discriminates :
    dispatchHandler demoMethodBlocks [] (reqOfMethod "GET" ["h"] ["x"]) = some 10
      ∧ dispatchHandler demoMethodBlocks [] (reqOfMethod "POST" ["h"] ["x"]) = some 20 := by
  constructor <;> decide

end Route.Match
