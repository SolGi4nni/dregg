import Cgi
import Reactor.App
import Reactor.Deploy

/-!
# Route.QueryRouteProven — query-string routing is path-only; the query is preserved

PROVE-WHAT-RUNS lane for the deployed **query-string routing / handling** behaviour
(ledger row `rt.query`). The property, in two halves:

  * **`query_no_route_confusion`** — appending `?a=b` to a request target does **not**
    change which route matches versus the bare path. The query component is not part
    of the path the router keys on.
  * **`query_preserved`** — the query string is carried through to the handler
    verbatim (it is not dropped), while being absent from the path-match.

## RFC ground truth

RFC 3986 §3.4 (Query): *"The query component is indicated by the first question mark
('?') character and terminated by a number sign ('#') character or by the end of the
URI."* So the path component ends at the **first** `?`, and everything from that `?`
onward is the query — it never participates in path resolution (§3.3, §5.2.4 operate on
the path component alone).

RFC 3875 §4.1.13 (`SCRIPT_NAME`) / §4.1.7 (`QUERY_STRING`): the gateway splits the
request-target at the first `?`; `SCRIPT_NAME` is the path portion (excluding the
query) and `QUERY_STRING` is the substring after the first `?` (without the `?`).

## The two deployed surfaces this file pins

1. **The RFC first-`?` split, value-level (`Cgi.splitTarget`).** This is the boundary
   `Reactor.WireRest.deployCgiReq` wires into the deployed CGI environment
   (`Cgi.targetPath`→`SCRIPT_NAME`, `Cgi.targetQuery`→`QUERY_STRING`, pinned by
   `deployCgi_scriptName` / `deployCgi_queryString`). It is implemented over
   `List.takeWhile`/`dropWhile`, so its value semantics are **fully proven, generally**,
   here: the path drops the query and the query is preserved verbatim.

2. **The deployed HTTP route surface (`Reactor.App.targetSegments` /
   `queryPairsOf` / `Reactor.Deploy.routeKeyOfReq`).** This is the split that the live
   `/health` router keys on. Its path/query split uses `String.splitOn "?"`, which is
   `@[extern]`-opaque and does **not** reduce in the kernel (the same boundary
   `Reactor.Deploy` itself brackets — "kernel-opaque; the branch fact is supplied").
   So this file pins the surface by **factorisation (`rfl`)**: the router input is a
   function of the head (pre-`?`) projection **alone**, the handler's query pairs a
   function of the tail (post-`?`) projection — two disjoint reads of the same target.
   From the factorisation, route selection is *constant across a head-equivalence class*
   (`query_no_route_confusion_route`, `decision_query_independent`), so no query can
   perturb it. The one link the kernel cannot take — that `splitOn "?"` of
   `"/health?probe=1"` has head `"/health"` — is exactly the RFC first-`?` semantics
   proven generally on surface (1) and demonstrated on the wire by the deployed curl.

No `sorry`, no `native_decide`; axioms stay within `{propext, Quot.sound,
Classical.choice}`.
-/

namespace Route.QueryRouteProven

open Proto (Bytes)

/-! ## 0. "no query delimiter" — a path component carries no `?` -/

/-- A path component contains no `?` — i.e. it is a genuine path with the query already
absent (RFC 3986 §3.3: the path never contains a `?`, which delimits the query). -/
@[reducible] def NoQuery (p : String) : Prop := '?' ∉ p.toList

/-- A concrete deployed path is query-free (the curl's bare path). -/
theorem noQuery_health : NoQuery "/health" := by decide

/-- Elementwise form: every character of a query-free path is `≠ '?'` (as the `Bool`
`takeWhile`/`dropWhile` predicate demands). -/
theorem noQuery_pred {p : String} (h : NoQuery p) :
    ∀ a ∈ p.toList, decide (a ≠ '?') = true := by
  intro a ha
  exact decide_eq_true (fun heq => h (heq ▸ ha))

/-- On a query-free path the split is a no-op: the whole string is the path. -/
theorem targetPath_of_noQuery {p : String} (h : NoQuery p) : Cgi.targetPath p = p := by
  unfold Cgi.targetPath Cgi.splitTarget
  have htw : p.toList.takeWhile (fun x => decide (x ≠ '?')) = p.toList := by
    rw [show p.toList = p.toList ++ [] from (List.append_nil _).symm,
        List.takeWhile_append_of_pos (noQuery_pred h)]; simp
  have hdw : p.toList.dropWhile (fun x => decide (x ≠ '?')) = [] := by
    rw [show p.toList = p.toList ++ [] from (List.append_nil _).symm,
        List.dropWhile_append_of_pos (noQuery_pred h)]; simp
  simp only [htw, hdw]
  -- `String.mk` is now the deprecated spelling of `String.ofList`, and the
  -- round-trip is the lemma `String.ofList_toList` rather than `rfl`.
  exact String.ofList_toList

/-! ## 1. RFC 3986 §3.4 first-`?` split — value semantics, proven generally

The split is `Cgi.splitTarget` (`takeWhile`/`dropWhile` at the first `?`), the deployed
`SCRIPT_NAME` / `QUERY_STRING` boundary. These are general theorems over ANY query-free
path `p` and ANY query `q`. -/

/-- **The path drops the query.** Splitting `p?q` (with `p` query-free) yields path `p` —
the query is excluded from the path portion the router/gateway keys on (RFC 3986 §3.4,
RFC 3875 §4.1.13). -/
theorem targetPath_drops_query (p q : String) (h : NoQuery p) :
    Cgi.targetPath (p ++ "?" ++ q) = p := by
  unfold Cgi.targetPath Cgi.splitTarget
  have hlist : (p ++ "?" ++ q).toList = p.toList ++ ('?' :: q.toList) := by simp
  simp only [hlist]
  rw [List.takeWhile_append_of_pos (noQuery_pred h)]
  simp only [List.takeWhile_cons]
  -- `String.mk` is now the deprecated spelling of `String.ofList`; the round-trip
  -- that used to be `rfl` is the lemma `String.ofList_toList`.
  split <;> simp <;> exact String.ofList_toList

/-- **The query is preserved verbatim.** Splitting `p?q` (with `p` query-free) yields
query `q` — the whole substring after the first `?`, unchanged (RFC 3875 §4.1.7). -/
theorem targetQuery_preserved (p q : String) (h : NoQuery p) :
    Cgi.targetQuery (p ++ "?" ++ q) = q := by
  unfold Cgi.targetQuery Cgi.splitTarget
  have hlist : (p ++ "?" ++ q).toList = p.toList ++ ('?' :: q.toList) := by simp
  simp only [hlist]
  rw [List.dropWhile_append_of_pos (noQuery_pred h)]
  simp
  exact String.ofList_toList

/-- **`query_preserved` — the split carries the query to the handler and keeps it out of
the path-match.** For a query-free path `p` and any query `q`, `splitTarget (p ++ "?" ++ q)`
is exactly `(p, q)`: the FIRST component (what `SCRIPT_NAME` / the route keys on) is the
bare path `p` — the query is NOT part of the path-match — and the SECOND component (what
`QUERY_STRING` / the handler receives) is exactly `q` — preserved verbatim. -/
theorem query_preserved (p q : String) (h : NoQuery p) :
    Cgi.splitTarget (p ++ "?" ++ q) = (p, q) := by
  have h1 : (Cgi.splitTarget (p ++ "?" ++ q)).1 = p := targetPath_drops_query p q h
  have h2 : (Cgi.splitTarget (p ++ "?" ++ q)).2 = q := targetQuery_preserved p q h
  exact Prod.ext h1 h2

/-- **`query_no_route_confusion` — `?a=b` does not change which route matches versus the
bare path.** For a query-free path `p`, the path the router keys on for `p ++ "?" ++ q`
is identical to the one for the bare `p` — appending any query leaves route selection
unchanged (route selection is a function of the path component alone, RFC 3986 §3.4). -/
theorem query_no_route_confusion (p q : String) (h : NoQuery p) :
    Cgi.targetPath (p ++ "?" ++ q) = Cgi.targetPath p := by
  rw [targetPath_drops_query p q h, targetPath_of_noQuery h]

/-! ## 2. The deployed HTTP route surface — factorisation (the live `/health` router)

`Reactor.App.targetSegments` (the segments `Route.Match.bestMatch` /
`Reactor.Deploy.routeKeyOfSegs` match on) and `Reactor.App.queryPairsOf` (the query
pairs the handler-guards read) both split the target with `String.splitOn "?"`. That
`splitOn` is `@[extern]`-opaque, so we pin the surface by FACTORISATION: the two reads
are disjoint projections of the single `splitOn "?"` result — the route reads the head,
the query reads the tail. -/

/-- The deployed target's split at `?` (the `String.splitOn "?"` the route surface uses). -/
def qsplit (t : Bytes) : List String := (Reactor.App.bytesToString t).splitOn "?"

/-- The path→segments projection: slash-split the head (pre-`?`) and normalise. -/
def pathSegs (ps : String) : List String :=
  Route.Path.normalize ((ps.splitOn "/").filter (fun seg => seg != ""))

/-- The query→pairs projection over the split parts (the tail, post-`?`). -/
def queryOfParts : List String → List (String × String)
  | _ :: rest =>
    let qs := String.intercalate "?" rest
    (qs.splitOn "&").filterMap (fun kv =>
      match kv.splitOn "=" with
      | []      => none
      | k :: vs => if k = "" then none else some (k, String.intercalate "=" vs))
  | [] => []

/-- **The router reads the pre-`?` head ONLY.** `targetSegments` — the segments the
deployed router matches on — is a function of the `splitOn "?"` HEAD alone; the query
bytes (everything from the first `?`) are structurally discarded before the match. -/
theorem route_reads_path_head_only (t : Bytes) :
    Reactor.App.targetSegments t = pathSegs ((qsplit t).headD "") := rfl

/-- **The handler reads the post-`?` tail.** `queryPairsOf` — the query pairs the
handler-guards consult — is a function of the `splitOn "?"` parts (the tail carries the
query), disjoint from the head the router reads. -/
theorem query_reads_tail (req : Proto.Request) :
    Reactor.App.queryPairsOf req = queryOfParts (qsplit req.target) := rfl

/-- The deployed admission decision keys on the route derived from `targetSegments`
(hence on the pre-`?` head alone) — definitional. -/
theorem routeKey_factors (req : Proto.Request) :
    Reactor.Deploy.routeKeyOfReq req
      = Reactor.Deploy.routeKeyOfSegs (Reactor.App.targetSegments req.target) := rfl

/-- **`query_no_route_confusion_route` — the deployed route surface, no confusion.** Two
targets that agree on their pre-`?` head produce the SAME matched segments — so the query
(the tail, which the head ignores) cannot change which route matches. This is the live
`/health` router: its input is constant across a head-equivalence class. -/
theorem query_no_route_confusion_route (t1 t2 : Bytes)
    (h : (qsplit t1).headD "" = (qsplit t2).headD "") :
    Reactor.App.targetSegments t1 = Reactor.App.targetSegments t2 := by
  rw [route_reads_path_head_only, route_reads_path_head_only, h]

/-- **`decision_query_independent` — the deployed ADMISSION decision is query-blind.**
Requests whose targets agree on the pre-`?` head map to the same deployed `routeKeyOfReq`
(and hence the same `Reactor.Deploy.deployDecisionOf`) — the query never reaches the
admission key. -/
theorem decision_query_independent (req1 req2 : Proto.Request)
    (h : (qsplit req1.target).headD "" = (qsplit req2.target).headD "") :
    Reactor.Deploy.routeKeyOfReq req1 = Reactor.Deploy.routeKeyOfReq req2 := by
  rw [routeKey_factors, routeKey_factors,
      query_no_route_confusion_route req1.target req2.target h]

/-! ## 3. Concrete, kernel-checked witnesses for the deployed curl `/health?probe=1`

These `decide` on the reducible surfaces — the wire the verifier re-curls. -/

/-- **The curl's exact split.** `/health?probe=1` splits (RFC 3986 §3.4) to path
`/health` (the route input — the SAME as the bare `/health`) and query `probe=1` (carried
to the handler). Kernel-evaluated. -/
theorem health_probe_split :
    Cgi.splitTarget "/health?probe=1" = ("/health", "probe=1") := by decide

/-- The path portion of `/health?probe=1` is byte-identical to the bare `/health` target:
no route confusion at the concrete curl. -/
theorem health_probe_path_eq_bare :
    Cgi.targetPath "/health?probe=1" = Cgi.targetPath "/health" := by decide

/-- The query portion is preserved non-empty (`probe=1` reaches the handler). -/
theorem health_probe_query_nonempty :
    Cgi.targetQuery "/health?probe=1" = "probe=1" ∧ Cgi.targetQuery "/health?probe=1" ≠ "" := by
  decide

/-- **The deployed route decision on the `/health` segments admits.** This is the REAL
`Reactor.Deploy.decisionOfSegs` (the admission the live serve runs) on the segments a
`/health` target — with or without `?probe=1` — normalises to (`["health"]`, since the
router drops the query before matching). Kernel-checked. -/
theorem health_segments_admit :
    (Reactor.Deploy.decisionOfSegs ["health"]).isSome = true := by decide

/-- The `/health` segments carry no traversal escape (non-vacuity: the admitted branch is
a real route, not a refusal). -/
theorem health_segments_no_escape :
    Reactor.Deploy.escapesSegs ["health"] = false := by decide

end Route.QueryRouteProven
