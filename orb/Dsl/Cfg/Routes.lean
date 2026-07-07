import Reactor.App
import Dsl.Component

/-!
# Dsl.Cfg.Routes — the *rich* routing dimension of a deployment

`Dsl.Cfg.Route` (singular) is the seed routing dimension: a flat `(pattern,
handler)` table over `Route.Match`'s three precedence classes (exact / prefix /
default). This file **grows that dimension to the full declarative surface** a
production router configuration language (pkl-style) exposes, without weakening
or re-deriving anything already proven:

  * **ordered first-match** — a two-level table (virtual-host blocks → routes),
    each level a `List.find?`, so first-match determinism holds by construction
    (`RouteAdvanced.dispatch`);
  * **path match** by exact / prefix / `*`-glob / `**`-globstar / abstract regex
    (`RouteAdvanced.SegPat` + `PathPat`);
  * **host / vhost match** (`RouteAdvanced.HostPat`: any / exact / `*.rest`);
  * **method match** (`RouteAdvanced.MethodPat`);
  * **header match** and **query match** (`RouteAdvanced.headerPresent` /
    `headerEquals` / `queryPresent` / `queryEquals` guards);
  * **path rewrite / prefix strip** — the one capability the proven matcher did
    NOT carry, added here as a total, proven transform (`Rewrite`).

Everything above the rewrite is a *reuse* of the already-proven `RouteAdvanced`
router: the richer matcher does not re-implement selection, it wraps the proven
one, so host isolation (RFC 9110 §7.4), first-match determinism, glob soundness,
and guard enforcement transfer with no re-proof (re-exposed below).

## What this file adds over the flat seed

* `Rewrite` + `applyRewrite` — declarative prefix-strip / prefix-replace, with
  the exactness theorems (`stripPrefix_recovers`, `replacePrefix_recovers`): the
  rewrite recovers exactly the upstream-facing path.
* `refines_precedence` — the richer first-match matcher **refines** the flat
  RFC exact>prefix>default precedence: with the virtual-host surface unused it
  reproduces `Route.Match.bestMatch` on the nose (conservative extension), and
  the class-ordered lift `liftFlatBlock` of a flat table dispatches to exactly
  the handler `bestMatch` selects (`lift_refines_bestMatch`).
* `Router` (a `Dsl.Component`) — the routing dimension AS a component whose
  well-formedness invariant is *totality* (every request selects a handler),
  preserved as blocks are added (`Router.reachable_total`) and preserved by the
  parallel product of two routers (`twoRouters_total`) — the composition
  calculus of `Dsl.Component`, instantiated for routing.
* `lowerApp` + `lowerApp_handle` — the rich config LOWERED to the deployed
  `Reactor.App.AppConfig`, with the proof that the deployed `Reactor.App.handle`
  answers a request by exactly this dimension's rich `RouteAdvanced.dispatch`.
  This is how `instantiate` honors the dimension (see the welding note at the
  end): the rich table rides the `hostGlob` handler the proven `handle` already
  drives, so method / header / query / glob / regex discrimination becomes
  observable on the deployed wire — none of which the hardcoded `demoVhBlocks`
  (host + one glob, fixed bodies) could express.
-/

namespace Dsl.Cfg

open Reactor (Response)

/-! ## Path rewrite / prefix strip — the one new matcher-adjacent capability -/

/-- A declarative path rewrite applied to the matched request's segment list
before it reaches the (upstream / file) handler. `keep` is identity; `stripPrefix
n` drops the leading `n` segments (the classic `/api` strip before proxying);
`replacePrefix d add` drops the leading `d` and prepends `add` (a mount-point
remap). Total on every input — dropping past the end yields `[]`. -/
inductive Rewrite where
  | keep
  | stripPrefix (n : Nat)
  | replacePrefix (drop : Nat) (add : List String)
deriving Repr, DecidableEq

/-- Apply a rewrite to a request's path segments. -/
def applyRewrite : Rewrite → List String → List String
  | .keep, segs => segs
  | .stripPrefix n, segs => segs.drop n
  | .replacePrefix d add, segs => add ++ segs.drop d

@[simp] theorem applyRewrite_keep (segs : List String) :
    applyRewrite .keep segs = segs := rfl

@[simp] theorem applyRewrite_stripPrefix (n : Nat) (segs : List String) :
    applyRewrite (.stripPrefix n) segs = segs.drop n := rfl

@[simp] theorem applyRewrite_replacePrefix (d : Nat) (add segs : List String) :
    applyRewrite (.replacePrefix d add) segs = add ++ segs.drop d := rfl

/-- Dropping exactly a prefix's length off a `prefix ++ rest` recovers `rest`. -/
theorem drop_len_append (pfx rest : List String) :
    (pfx ++ rest).drop pfx.length = rest := by
  induction pfx with
  | nil => rfl
  | cons a as ih => exact ih

/-- **Prefix-strip is exact.** Stripping the matched prefix off `prefix ++ rest`
yields exactly `rest` — the upstream sees precisely the un-prefixed path, nothing
of the mount point leaks. -/
theorem stripPrefix_recovers (pfx rest : List String) :
    applyRewrite (.stripPrefix pfx.length) (pfx ++ rest) = rest := by
  simp [drop_len_append]

/-- **Prefix-replace is exact.** Replacing the matched prefix remaps the mount
point to `add` and preserves the tail `rest` verbatim. -/
theorem replacePrefix_recovers (pfx add rest : List String) :
    applyRewrite (.replacePrefix pfx.length add) (pfx ++ rest) = add ++ rest := by
  simp [drop_len_append]

/-! ## The rich routing configuration

The dimension's data is a `VHostConfig`: an ordered list of virtual-host blocks,
each a host pattern + an ordered route list, over the proven `RouteAdvanced`
surface (method / path-glob / regex / header+query guards). Selection is the
proven `RouteAdvanced.dispatch`; this dimension only *names* it. -/

/-- The rich routing dimension: the two-level ordered virtual-host table. `H` is
the per-route handler payload (`Nat` for the crisp discrimination witnesses; the
deployed instantiation uses `Nat × Proto.Bytes`, the status+body the proven
`hostGlob` handler renders). -/
structure VHostConfig (H : Type) where
  blocks : List (RouteAdvanced.ServerBlock H)

variable {H : Type}

/-- The route this dimension selects for a request (the proven first-match
virtual-host dispatch). -/
def VHostConfig.route (c : VHostConfig H) (req : RouteAdvanced.Req) :
    Option (RouteAdvanced.Route H) :=
  RouteAdvanced.dispatch c.blocks req

/-- The handler this dimension selects for a request. -/
def VHostConfig.handler? (c : VHostConfig H) (req : RouteAdvanced.Req) : Option H :=
  (RouteAdvanced.dispatch c.blocks req).map (·.handler)

/-! ### Inherited guarantees (reuse, not re-derivation)

The richer matcher IS `RouteAdvanced.dispatch`; every guarantee proven there is a
guarantee of this dimension. These wrappers make that transfer explicit. -/

/-- **Soundness (inherited).** A selected route actually matches the request. -/
theorem VHostConfig.route_sound {c : VHostConfig H} {req : RouteAdvanced.Req}
    {r : RouteAdvanced.Route H} (h : c.route req = some r) :
    RouteAdvanced.routeMatches req r = true :=
  RouteAdvanced.dispatch_sound h

/-- **First-match determinism (inherited).** The selected route is the earliest
matching route of the selected block; every earlier route fails to match. -/
theorem VHostConfig.route_first_match {c : VHostConfig H} {req : RouteAdvanced.Req}
    {r : RouteAdvanced.Route H} (h : c.route req = some r) :
    ∃ b, RouteAdvanced.selectBlock c.blocks req = some b ∧ ∃ pre suf,
      b.routes = pre ++ r :: suf
      ∧ (∀ r' ∈ pre, RouteAdvanced.routeMatches req r' = false)
      ∧ RouteAdvanced.routeMatches req r = true :=
  RouteAdvanced.dispatch_first_match h

/-- **Host isolation (inherited, RFC 9110 §7.4).** A request whose authority is
not `hB` is never served by a block bound to the exact host `hB`. -/
theorem VHostConfig.host_isolation {blocks : List (RouteAdvanced.ServerBlock H)}
    {req : RouteAdvanced.Req} {b : RouteAdvanced.ServerBlock H} {hB : List String}
    (hexact : b.host = RouteAdvanced.HostPat.exact hB) (hne : req.host ≠ hB) :
    RouteAdvanced.selectBlock blocks req ≠ some b :=
  RouteAdvanced.route_host_isolation hexact hne

/-- **Header-required is enforced (inherited).** A route guarded by a required
header cannot match a request lacking it. -/
theorem VHostConfig.header_required {req : RouteAdvanced.Req} {r : RouteAdvanced.Route H}
    {name : String} (hg : RouteAdvanced.headerPresent name ∈ r.guards)
    (habsent : RouteAdvanced.headerPresent name req = false) :
    RouteAdvanced.routeMatches req r ≠ true :=
  RouteAdvanced.headerRequired_blocks hg habsent

/-- **Query-required is enforced (inherited).** A route guarded by a required
query key cannot match a request lacking it. -/
theorem VHostConfig.query_required {req : RouteAdvanced.Req} {r : RouteAdvanced.Route H}
    {key : String} (hg : RouteAdvanced.queryPresent key ∈ r.guards)
    (habsent : RouteAdvanced.queryPresent key req = false) :
    RouteAdvanced.routeMatches req r ≠ true :=
  RouteAdvanced.queryRequired_blocks hg habsent

/-! ## Refinement of the flat RFC precedence

Two statements. First, the *conservative extension*: with no virtual-host blocks
the rich dispatch reduces to the flat `Route.Match.bestMatch` precedence exactly
(`Route.Match.dispatchHandler_no_blocks`). Second, the *substantive* refinement:
a flat table lifted into a single virtual-host block — with its routes re-ordered
by class (exact, then prefix, then default) as pkl authoring requires — dispatches
to exactly the handler `bestMatch` selects. Together: the richer first-match
matcher refines the exact>prefix>default class precedence. -/

/-- **Conservative extension.** With the virtual-host surface unused, the rich
host/glob dispatch is byte-for-byte the flat exact>prefix>default `bestMatch`
precedence over the same path. (Re-exposed from the proven `Route.Match`.) -/
theorem refines_precedence (flat : List (Route.Match.Route H)) (req : RouteAdvanced.Req) :
    Route.Match.dispatchHandler [] flat req
      = (Route.Match.bestMatch flat req.segs).map (·.handler) :=
  Route.Match.dispatchHandler_no_blocks flat req

/-! ### The class-ordered lift and its refinement -/

/-- Lift one flat route to the rich surface: an exact pattern becomes an all-`lit`
path of the same length (`globstar := false`, so it matches only that exact
segment list); a prefix pattern becomes an all-`lit` path with `globstar := true`
(the `**` absorbs any suffix — exactly `isPrefixOf`); a default becomes the
`RouteAdvanced` catch-all. Method is `anyMethod` and there are no guards, so a
lifted route matches purely on its path — the flat semantics. -/
def liftRoute (r : Route.Match.Route H) : RouteAdvanced.Route H :=
  match r.pat with
  | .exact segs =>
      { method := .anyMethod, path := { segs := segs.map .lit, globstar := false },
        guards := [], handler := r.handler }
  | .«prefix» segs =>
      { method := .anyMethod, path := { segs := segs.map .lit, globstar := true },
        guards := [], handler := r.handler }
  | .«default» => RouteAdvanced.catchAllRoute r.handler

/-- An all-`lit` path (no globstar) matches iff the request equals the pattern:
`matchAll` of `map .lit segs` is decided equality. -/
theorem matchAll_lit (segs req : List String) :
    RouteAdvanced.matchAll (segs.map .lit) req = decide (req = segs) := by
  induction segs generalizing req with
  | nil =>
    cases req with
    | nil => rfl
    | cons x xs => rfl
  | cons s ss ih =>
    cases req with
    | nil => rfl
    | cons x xs =>
      simp only [List.map_cons, RouteAdvanced.matchAll, RouteAdvanced.segMatch, ih,
        List.cons.injEq]
      exact (Bool.decide_and (x = s) (xs = ss)).symm

/-- An all-`lit` globstar path matches iff the pattern is a prefix of the request:
`matchPrefixSegs` of `map .lit segs` is `isPrefixOf`. -/
theorem matchPrefixSegs_lit (segs req : List String) :
    RouteAdvanced.matchPrefixSegs (segs.map .lit) req = segs.isPrefixOf req := by
  induction segs generalizing req with
  | nil => simp [RouteAdvanced.matchPrefixSegs, List.isPrefixOf]
  | cons s ss ih =>
    cases req with
    | nil => simp [List.map_cons, RouteAdvanced.matchPrefixSegs, List.isPrefixOf]
    | cons x xs =>
      simp only [List.map_cons, RouteAdvanced.matchPrefixSegs, RouteAdvanced.segMatch,
        ih, List.isPrefixOf_cons₂]
      -- goal: `(decide (x = s) && ss.isPrefixOf xs) = (s == x && ss.isPrefixOf xs)`
      congr 1
      have hb : (s == x) = decide (s = x) := rfl
      rw [hb, decide_eq_decide]; exact eq_comm

/-- A lifted route matches a request (as a `RouteAdvanced` route) iff the flat
route matches the request's path in its class (as a `Route.Match` route). -/
theorem liftRoute_matches (r : Route.Match.Route H) (req : RouteAdvanced.Req) :
    RouteAdvanced.routeMatches req (liftRoute r)
      = Route.Match.matchesAny req.segs r := by
  unfold liftRoute RouteAdvanced.routeMatches
  cases hp : r.pat with
  | exact segs =>
    simp only [RouteAdvanced.methodMatch, RouteAdvanced.pathMatch, List.all_nil,
      Bool.and_true, Bool.true_and]
    rw [matchAll_lit]
    unfold Route.Match.matchesAny Route.Match.matchesExact Route.Match.matchesPrefix
      Route.Match.matchesDefault
    rw [hp]; simp
  | «prefix» segs =>
    simp only [RouteAdvanced.methodMatch, RouteAdvanced.pathMatch, List.all_nil,
      Bool.and_true, Bool.true_and]
    rw [matchPrefixSegs_lit]
    unfold Route.Match.matchesAny Route.Match.matchesExact Route.Match.matchesPrefix
      Route.Match.matchesDefault
    rw [hp]; simp
  | «default» =>
    have := RouteAdvanced.catchAllRoute_matches r.handler req
    unfold RouteAdvanced.routeMatches at this
    rw [this]
    unfold Route.Match.matchesAny Route.Match.matchesExact Route.Match.matchesPrefix
      Route.Match.matchesDefault
    rw [hp]; simp

/-! ### The full-table lift and its precedence refinement

`liftFlatBlock` lifts a whole flat table into ONE virtual-host block, re-ordering
its routes by class (all exacts, then all prefixes, then the defaults) — the
"specific routes first" discipline a first-match config language requires to
encode class precedence. The proven `RouteAdvanced.dispatch` over that single
anyHost block then selects exactly the handler the flat `Route.Match.bestMatch`
selects: the richer first-match matcher **refines** the exact>prefix>default
class precedence. -/

/-- Route is in the exact precedence class (pattern-only, request-independent). -/
def isExactCls (r : Route.Match.Route H) : Bool :=
  match r.pat with | .exact _ => true | _ => false

/-- Route is in the prefix precedence class. -/
def isPrefixCls (r : Route.Match.Route H) : Bool :=
  match r.pat with | .«prefix» _ => true | _ => false

/-- The class partition of a flat table, order-preserving within each class:
exacts first, then prefixes, then defaults (right-associated so `find?` nests
exactly as `bestMatch`). -/
def classOrder (flat : List (Route.Match.Route H)) : List (Route.Match.Route H) :=
  flat.filter isExactCls
    ++ (flat.filter isPrefixCls ++ flat.filter Route.Match.matchesDefault)

/-- Lift a flat table into a single anyHost virtual-host block, class-ordered. -/
def liftFlatBlock (flat : List (Route.Match.Route H)) :
    List (RouteAdvanced.ServerBlock H) :=
  [ { host := .anyHost, routes := (classOrder flat).map liftRoute } ]

/-! #### Self-contained `List.find?` lemmas (core only) -/

/-- `find?` over a `map f` picks the `f`-image of the first `p∘f`-match. -/
theorem find?_map {α β} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).find? p = (l.find? (fun a => p (f a))).map f := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.find?, List.find?]
    cases hp : p (f a) with
    | true => rfl
    | false => exact ih

/-- `find?` respects pointwise-equal predicates on the list. -/
theorem find?_congr {α} {p q : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, p x = q x) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have ha := h a (List.mem_cons_self a t)
    cases hqa : q a with
    | true => rw [List.find?, ha.trans hqa, List.find?, hqa]
    | false =>
      rw [List.find?, ha.trans hqa, List.find?, hqa]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- `find?` over `l1 ++ l2` is the first match of `l1`, else of `l2`. -/
theorem find?_append {α} (p : α → Bool) : ∀ (l1 l2 : List α),
    (l1 ++ l2).find? p
      = match l1.find? p with | some a => some a | none => l2.find? p := by
  intro l1 l2
  induction l1 with
  | nil => rfl
  | cons a t ih =>
    rw [List.cons_append, List.find?, List.find?]
    cases p a with
    | true => rfl
    | false => exact ih

/-- Dropping predicate-false elements (here: whole classes) does not change
`find?` when the predicate can only hold on kept elements. -/
theorem find?_filter_pred {α} {p q : α → Bool} (himp : ∀ x, p x = true → q x = true) :
    ∀ {l : List α}, (l.filter q).find? p = l.find? p := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filter_cons]
    split
    · rw [List.find?, List.find?]
      cases p a with
      | true => rfl
      | false => exact ih
    · rename_i hqa
      have hpa : p a = false := by
        cases hh : p a with
        | false => rfl
        | true => exact absurd (himp a hh) hqa
      rw [List.find?, hpa]; exact ih

/-! #### The precedence-refinement theorem -/

/-- On the exact-class filter, `matchesAny` collapses to `matchesExact`. -/
theorem find?_exacts (flat : List (Route.Match.Route H)) (segs : List String) :
    (flat.filter isExactCls).find? (Route.Match.matchesAny segs)
      = flat.find? (Route.Match.matchesExact segs) := by
  rw [find?_congr (p := Route.Match.matchesAny segs) (q := Route.Match.matchesExact segs)
      (fun r hr => by
        obtain ⟨_, hcls⟩ := List.mem_filter.mp hr
        unfold isExactCls at hcls
        cases hp : r.pat with
        | exact s => exact Route.Match.matchesAny_exact hp
        | «prefix» s => rw [hp] at hcls; exact absurd hcls Bool.noConfusion
        | «default» => rw [hp] at hcls; exact absurd hcls Bool.noConfusion)]
  exact find?_filter_pred (fun x hx => by
    obtain ⟨s, hp⟩ := Route.Match.matchesExact_exact hx
    unfold isExactCls; rw [hp])

/-- On the prefix-class filter, `matchesAny` collapses to `matchesPrefix`. -/
theorem find?_prefixes (flat : List (Route.Match.Route H)) (segs : List String) :
    (flat.filter isPrefixCls).find? (Route.Match.matchesAny segs)
      = flat.find? (Route.Match.matchesPrefix segs) := by
  rw [find?_congr (p := Route.Match.matchesAny segs) (q := Route.Match.matchesPrefix segs)
      (fun r hr => by
        obtain ⟨_, hcls⟩ := List.mem_filter.mp hr
        unfold isPrefixCls at hcls
        cases hp : r.pat with
        | exact s => rw [hp] at hcls; exact absurd hcls Bool.noConfusion
        | «prefix» s => exact Route.Match.matchesAny_prefix hp
        | «default» => rw [hp] at hcls; exact absurd hcls Bool.noConfusion)]
  exact find?_filter_pred (fun x hx => by
    obtain ⟨s, hp⟩ := Route.Match.matchesPrefix_prefix hx
    unfold isPrefixCls; rw [hp])

/-- On the default-class filter, `matchesAny` collapses to `matchesDefault`. -/
theorem find?_defaults (flat : List (Route.Match.Route H)) (segs : List String) :
    (flat.filter Route.Match.matchesDefault).find? (Route.Match.matchesAny segs)
      = flat.find? Route.Match.matchesDefault := by
  rw [find?_congr (p := Route.Match.matchesAny segs) (q := Route.Match.matchesDefault)
      (fun r hr => by
        obtain ⟨_, hcls⟩ := List.mem_filter.mp hr
        exact Route.Match.matchesAny_default (Route.Match.matchesDefault_default hcls))]
  exact find?_filter_pred (fun _ hx => hx)

/-- **The class-ordered first-match reproduces `bestMatch`.** Threading a request
through the class-ordered flat table with a single `matchesAny` first-match scan
selects exactly the route `Route.Match.bestMatch` selects with its
exact>prefix>default class precedence. -/
theorem find?_classOrder_eq_bestMatch (flat : List (Route.Match.Route H))
    (segs : List String) :
    (classOrder flat).find? (Route.Match.matchesAny segs)
      = Route.Match.bestMatch flat segs := by
  unfold classOrder Route.Match.bestMatch
  rw [find?_append, find?_append, find?_exacts, find?_prefixes, find?_defaults]
  cases flat.find? (Route.Match.matchesExact segs) <;>
    cases flat.find? (Route.Match.matchesPrefix segs) <;> rfl

/-- Dispatch over the class-ordered lift is the first `matchesAny`-match of the
class-ordered flat table, mapped through `liftRoute`. -/
theorem dispatch_liftFlatBlock (flat : List (Route.Match.Route H))
    (req : RouteAdvanced.Req) :
    RouteAdvanced.dispatch (liftFlatBlock flat) req
      = ((classOrder flat).find? (Route.Match.matchesAny req.segs)).map liftRoute := by
  unfold RouteAdvanced.dispatch liftFlatBlock RouteAdvanced.selectBlock
  rw [List.find?, show RouteAdvanced.hostMatch RouteAdvanced.HostPat.anyHost req.host = true from rfl]
  show ((classOrder flat).map liftRoute).find? (RouteAdvanced.routeMatches req) = _
  rw [find?_map liftRoute (RouteAdvanced.routeMatches req) (classOrder flat)]
  apply congrArg (Option.map liftRoute)
  exact find?_congr (fun r _ => liftRoute_matches r req)

/-- **The richer matcher refines the RFC exact>prefix>default precedence.** The
proven `RouteAdvanced.dispatch`, run over the class-ordered single-block lift of a
flat table, selects the SAME handler `Route.Match.bestMatch` selects for every
request — the richer first-match router is a faithful refinement of the flat
class-precedence router. -/
theorem lift_refines_bestMatch (flat : List (Route.Match.Route H))
    (req : RouteAdvanced.Req) :
    (RouteAdvanced.dispatch (liftFlatBlock flat) req).map (·.handler)
      = (Route.Match.bestMatch flat req.segs).map (·.handler) := by
  rw [dispatch_liftFlatBlock, find?_classOrder_eq_bestMatch]
  cases Route.Match.bestMatch flat req.segs with
  | none => rfl
  | some r =>
    simp only [Option.map_some']
    -- handlers agree: `liftRoute` preserves the handler field
    unfold liftRoute
    cases r.pat <;> rfl

/-! ## The routing dimension AS a component — totality is a preserved invariant

The `Dsl.Component` calculus (state space + well-formedness invariant + labelled
step, with `reachable_inv` and the parallel-product `prod_preserves`) applies to
routing: the state is the virtual-host table, the well-formedness invariant is
**totality** (every request selects a handler — the table is never stuck), and the
step ADDS a virtual-host block. Totality is preserved because appending a block
never removes an earlier match; so every reachable router table is total
(`Router.reachable_total`), and two routers composed by the product keep both
totalities (`twoRouters_total`). This is the totality guarantee of the routing
dimension expressed as an invariant maintained across configuration edits. -/

/-- A router table is **total** when every request selects a handler. -/
def Total (blocks : List (RouteAdvanced.ServerBlock Nat)) : Prop :=
  ∀ req, ∃ r, RouteAdvanced.dispatch blocks req = some r

/-- `find?` returning `some` is stable under appending more list: the earliest
match is unchanged. -/
theorem find?_append_some {α} {p : α → Bool} :
    ∀ {l : List α} {a : α}, l.find? p = some a → ∀ more, (l ++ more).find? p = some a := by
  intro l
  induction l with
  | nil => intro a h _; simp [List.find?] at h
  | cons b t ih =>
    intro a h more
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; rw [List.cons_append, List.find?, hb]
    | false => rw [List.find?, hb] at h; rw [List.cons_append, List.find?, hb]; exact ih h more

/-- Dispatch is stable under appending more virtual-host blocks: an existing
match is preserved (the appended blocks sit strictly after the selected one). -/
theorem dispatch_append {blocks : List (RouteAdvanced.ServerBlock H)}
    {req : RouteAdvanced.Req} {r : RouteAdvanced.Route H}
    (h : RouteAdvanced.dispatch blocks req = some r) (more : List (RouteAdvanced.ServerBlock H)) :
    RouteAdvanced.dispatch (blocks ++ more) req = some r := by
  unfold RouteAdvanced.dispatch at h ⊢
  cases hs : RouteAdvanced.selectBlock blocks req with
  | none => rw [hs] at h; cases h
  | some b =>
    rw [hs] at h
    have hs' : RouteAdvanced.selectBlock (blocks ++ more) req = some b := by
      unfold RouteAdvanced.selectBlock at hs ⊢; exact find?_append_some hs more
    rw [hs']; exact h

/-- The routing dimension as a `Dsl.Component`: state is the virtual-host table,
the invariant is totality, and the step appends a block. -/
def Router : Component where
  State := List (RouteAdvanced.ServerBlock Nat)
  Input := RouteAdvanced.ServerBlock Nat
  Output := Unit
  inv := Total
  init := [RouteAdvanced.catchAllBlock 0]
  step := fun blocks nb => (blocks ++ [nb], [])
  init_wf := fun req => ⟨_, RouteAdvanced.route_catchall 0 req⟩
  step_wf := fun _blocks nb h req =>
    let ⟨r, hr⟩ := h req; ⟨r, dispatch_append hr [nb]⟩

/-- **Totality is preserved on every reachable router.** Starting from the
catch-all router and adding blocks in any order, every reachable table is total —
`dispatch` never gets stuck. This instantiates `Dsl.Component.reachable_inv` for
routing. -/
theorem Router.reachable_total (s : Router.State) (h : Router.Reachable s) :
    ∀ req, ∃ r, RouteAdvanced.dispatch s req = some r :=
  Router.reachable_inv h

/-- Two routers composed by the parallel product. -/
def twoRouters : Component := Router.prod Router

/-- **Composition preserves both totalities.** A reachable state of the product
of two routers is total in each factor — the component calculus's `prod` law,
instantiated: composing routing configurations does not break totality. -/
theorem twoRouters_total (s : twoRouters.State) (h : twoRouters.Reachable s) :
    Total s.1 ∧ Total s.2 :=
  twoRouters.reachable_inv h

/-! ## Lowering the rich dimension into the deployed serve

The proven `Reactor.App.handle` already drives `RouteAdvanced.dispatch` inside the
`hostGlob` handler. So the rich table lowers into an `AppConfig` whose default
handler IS this dimension's virtual-host table: `handle` then answers every
request by exactly this dimension's dispatch. This is how `instantiate` honors the
grown dimension (see the welding note). -/

open Proto (Bytes Request)

/-- Lower a rich virtual-host table (widened `VHandler` answers) into the deployed
`Reactor.App.AppConfig`: no flat routes, the rich table riding the proven
`hostGlob` handler as the default. -/
def lowerApp (cfg : VHostConfig Reactor.App.VHandler) (lid : Nat) (pol : Policy.Running)
    (rk : Route.Match.Route Reactor.App.Handler → Policy.RouteKey) : Reactor.App.AppConfig :=
  { routes := []
    defaultHandler := .hostGlob cfg.blocks
    lid := lid
    policy := pol
    routeKeyOf := rk }

/-- `bestMatch` over a lone default route selects that route. -/
theorem bestMatch_only_default (h : Reactor.App.Handler) (segs : List String) :
    Route.Match.bestMatch [⟨Route.Match.Pat.«default», h⟩] segs
      = some ⟨Route.Match.Pat.«default», h⟩ := by
  simp [Route.Match.bestMatch, Route.Match.matchesExact, Route.Match.matchesPrefix,
    Route.Match.matchesDefault, List.find?]

/-- **The deployed serve answers by this dimension's rich dispatch.** For the
lowered config, the proven `Reactor.App.handle` selects the response by exactly
`RouteAdvanced.dispatch` over this dimension's virtual-host table (host / method /
glob / regex / header / query discrimination and all), clamped to a genuine final
by `vhResponse`. The composition is correct via the already-proven router. -/
theorem lowerApp_handle (cfg : VHostConfig Reactor.App.VHandler) (lid : Nat)
    (pol : Policy.Running) (rk : Route.Match.Route Reactor.App.Handler → Policy.RouteKey)
    (req : Request) :
    Reactor.App.handle (lowerApp cfg lid pol rk) req
      = (match RouteAdvanced.dispatch cfg.blocks (Reactor.App.hostReqOf req) with
         | some rt => Reactor.App.vhandlerResponse req rt.handler
         | none => Reactor.App.vhandlerResponse req (.respond 404 "not found".toUTF8.toList)) := by
  unfold Reactor.App.handle
  have ht : (lowerApp cfg lid pol rk).table
      = [⟨Route.Match.Pat.«default», Reactor.App.Handler.hostGlob cfg.blocks⟩] := by
    simp [Reactor.App.AppConfig.table, lowerApp]
  rw [ht, bestMatch_only_default]
  rfl

/-- The deployed response is always a genuine final (non-1xx) — the rich dispatch
rides `vhandlerResponse`'s clamp, so whatever route the request selects the served
status is `≥ 200`. -/
theorem lowerApp_status_final (cfg : VHostConfig Reactor.App.VHandler) (lid : Nat)
    (pol : Policy.Running) (rk : Route.Match.Route Reactor.App.Handler → Policy.RouteKey)
    (req : Request) :
    200 ≤ (Reactor.App.handle (lowerApp cfg lid pol rk) req).status := by
  rw [lowerApp_handle]
  cases RouteAdvanced.dispatch cfg.blocks (Reactor.App.hostReqOf req) with
  | some rt => exact Reactor.App.vhandlerResponse_status_final req rt.handler
  | none    => exact Reactor.App.vhandlerResponse_status_final req _

/-! ## Concrete witnesses — expressing what the hardcoded serve could not

`Reactor.App.demoVhBlocks` discriminated on host + one glob only, with `anyMethod`
catch-all routes and fixed bodies. These configs discriminate on **method**,
**header**, **query**, and **regex** segments, and carry a **prefix-strip
rewrite** — none expressible by the hardcoded literal. Every claim is
kernel-checked by `decide`. -/

/-- A rich table (handlers as ids) discriminating on method / header / query /
regex — impossible for the host-only hardcoded blocks. -/
def demoRich : VHostConfig Nat :=
  ⟨[ { host := .exact ["shop", "example"],
       routes :=
         [ { method := .exact "GET",  path := ⟨[.lit "api"], false⟩, guards := [], handler := 10 },
           { method := .exact "POST", path := ⟨[.lit "api"], false⟩, guards := [], handler := 11 },
           { method := .anyMethod, path := ⟨[.lit "admin"], false⟩,
             guards := [RouteAdvanced.headerEquals "x-admin" "1"], handler := 20 },
           { method := .anyMethod, path := ⟨[.lit "admin"], false⟩, guards := [], handler := 21 },
           { method := .anyMethod, path := ⟨[.lit "search"], false⟩,
             guards := [RouteAdvanced.queryPresent "q"], handler := 30 },
           { method := .anyMethod, path := ⟨[.lit "search"], false⟩, guards := [], handler := 31 },
           { method := .anyMethod,
             path := ⟨[.lit "user", .rx (fun s => decide (s = "42" ∨ s = "7"))], false⟩,
             guards := [], handler := 40 },
           RouteAdvanced.catchAllRoute 99 ] } ]⟩

private def reqOf (host : List String) (method : String) (segs : List String)
    (headers query : List (String × String)) : RouteAdvanced.Req :=
  { host := host, method := method, segs := segs, headers := headers, query := query }

/-- **Method discrimination.** Same host, same path `/api`, different method →
different handler. The hardcoded serve (anyMethod blocks) could not do this. -/
theorem demo_method :
    demoRich.handler? (reqOf ["shop","example"] "GET" ["api"] [] []) = some 10
      ∧ demoRich.handler? (reqOf ["shop","example"] "POST" ["api"] [] []) = some 11 := by
  constructor <;> decide

/-- **Header-match discrimination.** `/admin` with the required header selects the
admin handler; without it, falls through to the public handler. -/
theorem demo_header :
    demoRich.handler? (reqOf ["shop","example"] "GET" ["admin"] [("x-admin","1")] []) = some 20
      ∧ demoRich.handler? (reqOf ["shop","example"] "GET" ["admin"] [] []) = some 21 := by
  constructor <;> decide

/-- **Query-match discrimination.** `/search?q=…` selects the search handler; a
bare `/search` falls through. -/
theorem demo_query :
    demoRich.handler? (reqOf ["shop","example"] "GET" ["search"] [] [("q","x")]) = some 30
      ∧ demoRich.handler? (reqOf ["shop","example"] "GET" ["search"] [] []) = some 31 := by
  constructor <;> decide

/-- **Regex-segment discrimination.** `/user/42` matches the id regex `(42|7)`;
`/user/abc` does not and falls through to the catch-all. -/
theorem demo_regex :
    demoRich.handler? (reqOf ["shop","example"] "GET" ["user","42"] [] []) = some 40
      ∧ demoRich.handler? (reqOf ["shop","example"] "GET" ["user","abc"] [] []) = some 99 := by
  constructor <;> decide

/-- A rich table whose handlers carry a **prefix-strip rewrite**: `/api/v1/**`
strips its two-segment mount before the (upstream) handler sees the path. -/
def demoProxy : VHostConfig (Nat × Rewrite) :=
  ⟨[ { host := .anyHost,
       routes :=
         [ { method := .anyMethod, path := ⟨[.lit "api", .lit "v1"], true⟩, guards := [],
             handler := (50, .stripPrefix 2) },
           RouteAdvanced.catchAllRoute (99, .keep) ] } ]⟩

/-- **Path-rewrite is real.** The `/api/v1/**` route is selected, and its declared
prefix-strip rewrites `/api/v1/users/42` down to the upstream-facing `/users/42`.
No rewrite exists anywhere in the hardcoded serve. -/
theorem demo_rewrite :
    (demoProxy.handler? (reqOf [] "GET" ["api","v1","users","42"] [] [])).map
        (fun hw => applyRewrite hw.2 ["api","v1","users","42"])
      = some ["users","42"] := by decide

/-- A deployed `(status, body)` table discriminating on host AND method: `b.example`
answers `POST` with `201 created` but `GET` with `200`; `a.example` answers all with
`200 A`. Host + method discrimination the host-only hardcoded blocks lacked. -/
def demoDeployed : VHostConfig (Nat × Bytes) :=
  ⟨[ { host := .exact ["a","example"],
       routes := [ RouteAdvanced.catchAllRoute (200, "A".toUTF8.toList) ] },
     { host := .exact ["b","example"],
       routes :=
         [ { method := .exact "POST", path := ⟨[], true⟩, guards := [],
             handler := (201, "created".toUTF8.toList) },
           RouteAdvanced.catchAllRoute (200, "B-get".toUTF8.toList) ] } ]⟩

/-!
## Welding note (for the seed-owner of `Dsl/Deployment.lean`)

`instantiate` currently folds `Cfg.RouteCfg` (the flat seed dimension) into
`AppConfig.routes`/`defaultHandler`. To honor this grown dimension, extend the
routing dimension to carry an optional rich virtual-host table and fold it into
the `hostGlob` default handler exactly as `lowerApp` does here:

```
-- in Dsl.Cfg.Route (or a `richRouting : Option (VHostConfig (Nat × Bytes))` field):
--   defaultHandler := match cfg.routing.rich with
--     | some vh => Reactor.App.Handler.hostGlob vh.blocks
--     | none    => cfg.routing.defaultHandler
```

Then `Dsl.Cfg.lowerApp_handle` is exactly the correctness lemma for the
`some vh` branch: the deployed `Reactor.App.handle` answers by
`RouteAdvanced.dispatch` over the rich table. The flat `none` branch is unchanged,
so the existing `defaultDeployment` byte-identical no-regression theorem is
untouched.
-/

end Dsl.Cfg
