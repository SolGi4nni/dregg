/-
  Dsl/Config/PredSpecData.lean — the request-predicate DATA algebra for the config
  surface.

  The router's guard type is `RouteAdvanced.Guard := Req → Bool` — a FUNCTION value.
  A config file cannot denote an arbitrary `Req → Bool`; the ENUMERABLE guards the
  grammar actually admits (method-exact, header-present, header-equals,
  query-present, query-equals, and the unconditional guards) are the data-denotable
  subset. This file makes that subset FIRST-CLASS DATA:

   * `PredSpec` — an inductive with one constructor per enumerable guard;
   * `denotePred : PredSpec → Req → Bool` — the denotation, landing each `PredSpec`
     on the SAME predicate the hand-written `RouteAdvanced` guard constructor
     computes;
   * `*_default_eq` — the NO-REGRESSION anchors: each fixed guard constructor
     (`headerPresent`, `headerEquals`, `queryPresent`, `queryEquals`, and the
     method match) is DEFINITIONALLY the denotation of its `PredSpec` — so the
     current guard vocabulary IS a `PredSpec` instance, proven, and the router
     keeps computing exactly today's predicate.

  This is ADDITIVE: it introduces the data algebra and proves it subsumes the
  deployed guard vocabulary WITHOUT rewiring `Route.guards : List Guard` or the
  config parser (`Dsl/Config/Parse.lean`) — carrying `PredSpec` THROUGH
  `MwClause`/`Route` (so the parse/render/roundtrip stack ranges over the data, not
  the function) is the named follow-on, kept off the deployed serve's proof stack.

  Header-VALUE / body-reading guards beyond this vocabulary stay a NAMED boundary,
  not smuggled in as opaque `Req → Bool`.
-/
import RouteAdvanced

namespace ConfigPredSpec

open RouteAdvanced

/-! ## 1. `PredSpec` — the enumerable request predicates, as DATA -/

/-- **`PredSpec`** — the config-denotable request predicates. One constructor per
enumerable guard the grammar admits; `always`/`never` are the unconditional guards.
This is DATA (an inductive), not a `Req → Bool` function value, so a config file can
name it, a parser can build it, and a renderer can print it back. -/
inductive PredSpec where
  | methodExact   (m : String)
  | headerPresent (name : String)
  | headerEquals  (name value : String)
  | queryPresent  (key : String)
  | queryEquals   (key value : String)
  | always
  | never
  deriving Repr, DecidableEq

/-- **`denotePred`** — a `PredSpec` IS a `Req → Bool` guard: its denotation lands on
exactly the predicate the corresponding hand-written `RouteAdvanced` guard computes
(see the `*_default_eq` anchors below). -/
def denotePred : PredSpec → Req → Bool
  | .methodExact m,       req => decide (req.method = m)
  | .headerPresent name,  req => req.headers.any (fun kv => decide (kv.1 = name))
  | .headerEquals n v,    req => req.headers.any (fun kv => decide (kv.1 = n ∧ kv.2 = v))
  | .queryPresent key,    req => req.query.any (fun kv => decide (kv.1 = key))
  | .queryEquals k v,     req => req.query.any (fun kv => decide (kv.1 = k ∧ kv.2 = v))
  | .always,              _   => true
  | .never,               _   => false

/-- A `PredSpec` embeds into the router's `Guard` type — the vocabulary is a genuine
subset of `Req → Bool`, ready to slot into `Route.guards`. -/
def toGuard (spec : PredSpec) : Guard := denotePred spec

/-! ## 2. `*_default_eq` — the fixed guard vocabulary IS a `PredSpec` instance

Each anchor shows the deployed guard constructor is DEFINITIONALLY the denotation of
its `PredSpec` — so replacing a baked `Guard` by `denotePred spec` changes NOTHING
the router computes. -/

/-- `headerPresent` is the denotation of `.headerPresent`. -/
theorem headerPresent_default_eq (name : String) :
    headerPresent name = denotePred (.headerPresent name) := rfl

/-- `headerEquals` is the denotation of `.headerEquals`. -/
theorem headerEquals_default_eq (name value : String) :
    headerEquals name value = denotePred (.headerEquals name value) := rfl

/-- `queryPresent` is the denotation of `.queryPresent`. -/
theorem queryPresent_default_eq (key : String) :
    queryPresent key = denotePred (.queryPresent key) := rfl

/-- `queryEquals` is the denotation of `.queryEquals`. -/
theorem queryEquals_default_eq (key value : String) :
    queryEquals key value = denotePred (.queryEquals key value) := rfl

/-- The method match is the denotation of `.methodExact` (the guard-shaped view of
`methodMatch (.exact m)`). -/
theorem methodExact_default_eq (m : String) (req : Req) :
    denotePred (.methodExact m) req = methodMatch (.exact m) req.method := rfl

/-- The embedding agrees with each fixed guard on every request (the `toGuard`
form of the anchors). -/
theorem toGuard_headerPresent (name : String) :
    toGuard (.headerPresent name) = headerPresent name := rfl
theorem toGuard_queryPresent (key : String) :
    toGuard (.queryPresent key) = queryPresent key := rfl

/-! ## 3. Non-vacuity — the denotation genuinely decides -/

/-- A concrete request: `GET /a?q=1` with header `X: y`. -/
def sampleReq : Req :=
  { host := ["h"], method := "GET", segs := ["a"],
    headers := [("X", "y")], query := [("q", "1")] }

#guard denotePred (.methodExact "GET") sampleReq = true
#guard denotePred (.methodExact "POST") sampleReq = false
#guard denotePred (.headerPresent "X") sampleReq = true
#guard denotePred (.headerPresent "Z") sampleReq = false
#guard denotePred (.headerEquals "X" "y") sampleReq = true
#guard denotePred (.headerEquals "X" "z") sampleReq = false
#guard denotePred (.queryPresent "q") sampleReq = true
#guard denotePred (.queryEquals "q" "1") sampleReq = true
#guard denotePred .always sampleReq = true
#guard denotePred .never  sampleReq = false

end ConfigPredSpec

#print axioms ConfigPredSpec.headerPresent_default_eq
#print axioms ConfigPredSpec.methodExact_default_eq
#print axioms ConfigPredSpec.queryEquals_default_eq
