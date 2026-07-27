/-
# IntrospectLive — driving the PROVEN config→route-table projection over the byte level

The declarative deployment surface (`Dsl.DeploymentConfig`) already proves that a
parsed textual config DENOTES a deterministic deployment: its flat route table is
exactly the operator's declared routes (`Dsl.Config.denoteOn_routes`), its dial
chain the declared LB policy (`Dsl.Config.denoteOn_dialChain`), its proxy virtual
hosts the declared `proxy`-block hostnames (`Dsl.Config.proxyVHostNames`). The
running host cannot hold a Lean `DeploymentConfig` across the FFI boundary, so at
boot it crosses `drorb_deployment_of_config` once, which projects the denotation to
a small tab-tagged text blob:

```
lb\t<byte>
routes\t<count>
vproxy\t<host>        (one per proxy vhost)
bind\t<pool>\t<mode>\t<ids>   (one per L4 listener)
```

The dataplane (`crates/dataplane/src/config.rs :: parse_from_path`) scans that blob
line-by-line with `str::strip_prefix`, and the operator-facing admin listener
(`crates/dataplane/src/admin.rs :: config_json`, `GET /admin/config`) reports the
scanned `lb_policy` / `routes` count / `vhosts` back as JSON. **This is the config
introspection surface** (LEDGER row `ad.introspect`): inert, no-crypto, a pure
read of the projection the proven core emitted.

This lane isolates that inert layer and proves it faithful. It mirrors both ends —
the EMIT (`drorb_deployment_of_config`, over the PROVEN `Dsl.Config.policyByteN` /
`renderNat` / `proxyVHostNames`) and the SCAN (`parse_from_path`'s `strip_prefix`
loop) — as pure Lean over the byte level (`List Char`), and proves the scanned
report EQUALS the config's denotation (`introspect_faithful`): the reported route
count is the length of the DENOTED route table (plus declared vhost items — the
`has_routes` gate the host reads), the reported LB byte is the denoted policy, the
reported vhosts are the denoted proxy hosts. A `selftest` drives the whole EMIT →
`\n`-join → SCAN chain on a concrete config with NO crypto whatsoever, so it runs
under `lake env lean --run`.

## Honesty / realization boundary (the NetmapLive / DnsResolveLive discipline)

This is **drorb-native** and **pure**: the emitter and the scanner are our own
spec-conformant peers speaking the modelled tab/newline projection framing (NOT a
network wire, NOT a JSON schema). No socket, no FFI call: the reused C objects are
linked only to satisfy the shared executable link line. The projection codecs are
the PROVEN `Dsl.Config` decimal/splitter algebra (`renderNat`/`parseNat`,
`splitOn1`) and the PROVEN denotation (`denoteOn`, `denoteOn_routes`,
`proxyVHostNames`, `policyByteN`). The gap the selftest discharges by construction
(not by proof) is that this exe faithfully CALLS the proven functions on real
bytes; the faithfulness of the emit→scan chain ITSELF is proven below as
`introspect_faithful`.

## Realized vs named residual

* REALIZED (proven + run here): a config's denoted route table / LB policy / proxy
  vhosts round-trip through the tab-tagged projection blob and are recovered exactly
  by the strip-prefix scan — the value `GET /admin/config` reports.
* NAMED residual: the JSON *serialization* of the scanned report
  (`admin.rs :: config_json`'s `{"active":…,"generation":…,…}` string) and the
  admin listener's HTTP framing are Rust-side string formatting, not modelled here;
  `/admin/config` reports a route *count*, not a full route *table* (there is no
  `/admin/routes` endpoint — see the run note). The `generation` counter and
  `active` flag are host runtime state, outside the pure denotation.

Usage:
  introspect-live selftest
-/
import Dsl.Config.Parse
import Reactor.Deploy

namespace IntrospectLive

open Dsl.Config
open Dsl (DeploymentConfig)

/-! ## §1  The tab-tagged projection wire (mirrors `drorb_deployment_of_config`) -/

/-- The tab separator between a projection tag and its payload (the `\t` in
`lb\t…` / `routes\t…` / `vproxy\t…`). -/
def tab : Char := '\t'

def tagLb     : List Char := ['l','b']
def tagRoutes : List Char := ['r','o','u','t','e','s']
def tagVproxy : List Char := ['v','p','r','o','x','y']

/-- One tagged projection line: `<tag>\t<payload>`. -/
def taggedLine (tag payload : List Char) : List Char := tag ++ tab :: payload

/-- `lb\t<byte>` — the parsed pool's LB policy byte (`Dsl.Config.policyByteN`),
rendered decimal by the PROVEN `Dsl.Config.renderNat`. -/
def lbLine (pc : ParsedConfig) : List Char :=
  taggedLine tagLb (renderNat (policyByteN pc.lb.toProxy))

/-- The route-directive count the host reads as the `has_routes` gate: flat routes
PLUS declared virtual-host items (a vhost-only config also routes through the
config serve). Exactly `drorb_deployment_of_config`'s `pc.routes.length +
pc.vitems.length`. -/
def routeCount (pc : ParsedConfig) : Nat := pc.routes.length + pc.vitems.length

/-- `routes\t<count>`. -/
def routesLine (pc : ParsedConfig) : List Char :=
  taggedLine tagRoutes (renderNat (routeCount pc))

/-- `vproxy\t<host>`. -/
def vproxyLine (h : List Char) : List Char := taggedLine tagVproxy h

/-- The full projection line list `drorb_deployment_of_config` emits, restricted to
the fields `/admin/config` reports: `lb`, `routes`, then one `vproxy` line per proxy
vhost. (The `bind\t…` L4 lines are scanned into a separate `l4_binds` field the
config-introspection report does not read.) -/
def emitLines (pc : ParsedConfig) : List (List Char) :=
  lbLine pc :: routesLine pc :: (proxyVHostNames pc.vitems).map (fun s => vproxyLine s.data)

/-! ## §2  The strip-prefix scanner (mirrors `config.rs :: parse_from_path`) -/

/-- Strip a literal prefix; `some suffix` iff `pre` is a prefix of `l`. The
`List Char` analogue of Rust `str::strip_prefix`. -/
def stripPref : List Char → List Char → Option (List Char)
  | [],      l       => some l
  | _ :: _,  []      => none
  | p :: ps, c :: cs => if p = c then stripPref ps cs else none

/-- Stripping a prefix off `pre ++ rest` recovers `rest`. -/
theorem stripPref_append (pre rest : List Char) : stripPref pre (pre ++ rest) = some rest := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp [stripPref, ih]

/-- `some payload` iff `l = <tag>\t<payload>` — the tag's `strip_prefix("<tag>\t")`. -/
def tagged (tag l : List Char) : Option (List Char) := stripPref (tag ++ [tab]) l

/-- A tagged line strips back to its payload. -/
theorem tagged_taggedLine (tag payload : List Char) :
    tagged tag (taggedLine tag payload) = some payload := by
  unfold tagged taggedLine
  rw [show tag ++ tab :: payload = (tag ++ [tab]) ++ payload by rw [List.append_assoc]; rfl]
  exact stripPref_append (tag ++ [tab]) payload

/-- The scanned report — the three fields `GET /admin/config` reads. -/
structure Report where
  lbPolicy : Nat := 0
  routes   : Nat := 0
  vhosts   : List (List Char) := []
deriving Repr, DecidableEq

/-- One scan step, mirroring `parse_from_path`'s `if let Some(_) = line.strip_prefix(..)`
cascade: `lb` sets the policy byte, `routes` the count, `vproxy` appends a host. -/
def step (a : Report) (l : List Char) : Report :=
  match tagged tagLb l with
  | some p => { a with lbPolicy := (parseNat p).getD a.lbPolicy }
  | none =>
    match tagged tagRoutes l with
    | some p => { a with routes := (parseNat p).getD a.routes }
    | none =>
      match tagged tagVproxy l with
      | some p => { a with vhosts := a.vhosts ++ [p] }
      | none => a

/-- Fold the scan over the projection lines (the `for line in s.lines()` loop). -/
def scanReport (lines : List (List Char)) : Report := lines.foldl step {}

/-- **The introspection read**: emit the projection for `pc`, scan it back. This is
what the running host computes between `drorb_deployment_of_config` and `GET
/admin/config`. -/
def introspect (pc : ParsedConfig) : Report := scanReport (emitLines pc)

/-! ## §3  Per-line scan lemmas -/

theorem step_lbLine (a : Report) (pc : ParsedConfig) :
    step a (lbLine pc) = { a with lbPolicy := policyByteN pc.lb.toProxy } := by
  have h1 : tagged tagLb (lbLine pc) = some (renderNat (policyByteN pc.lb.toProxy)) :=
    tagged_taggedLine tagLb _
  simp only [step, h1, parseNat_render, Option.getD_some]

theorem step_routesLine (a : Report) (pc : ParsedConfig) :
    step a (routesLine pc) = { a with routes := routeCount pc } := by
  have h0 : tagged tagLb (routesLine pc) = none := rfl
  have h1 : tagged tagRoutes (routesLine pc) = some (renderNat (routeCount pc)) :=
    tagged_taggedLine tagRoutes _
  simp only [step, h0, h1, parseNat_render, Option.getD_some]

theorem step_vproxyLine (a : Report) (h : List Char) :
    step a (vproxyLine h) = { a with vhosts := a.vhosts ++ [h] } := by
  have h0 : tagged tagLb (vproxyLine h) = none := rfl
  have h1 : tagged tagRoutes (vproxyLine h) = none := rfl
  have h2 : tagged tagVproxy (vproxyLine h) = some h := tagged_taggedLine tagVproxy h
  simp only [step, h0, h1, h2]

/-- Folding the scan over a run of `vproxy` lines appends exactly their payloads,
leaving the `lb` / `routes` fields untouched (they never match a `vproxy` line). -/
theorem foldl_vproxy (payloads : List (List Char)) (a : Report) :
    (payloads.map vproxyLine).foldl step a = { a with vhosts := a.vhosts ++ payloads } := by
  induction payloads generalizing a with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.foldl_cons, step_vproxyLine, ih, List.append_assoc,
      List.cons_append, List.nil_append]

/-! ## §4  The faithfulness theorem -/

/-- **The introspection read is a deterministic projection of the config.** Scanning
back the emitted projection recovers exactly: the denoted LB policy byte, the
route-directive count, and the denoted proxy virtual hosts. -/
theorem introspect_eq (pc : ParsedConfig) :
    introspect pc =
      { lbPolicy := policyByteN pc.lb.toProxy
        routes := routeCount pc
        vhosts := (proxyVHostNames pc.vitems).map String.data } := by
  unfold introspect scanReport emitLines
  rw [show ((proxyVHostNames pc.vitems).map (fun s => vproxyLine s.data))
        = ((proxyVHostNames pc.vitems).map String.data).map vproxyLine by
        rw [List.map_map]; rfl]
  simp only [List.foldl_cons, step_lbLine, step_routesLine, foldl_vproxy, List.nil_append]

/-- The reported LB policy byte is the config's denoted dial policy. -/
theorem introspect_lb (pc : ParsedConfig) :
    (introspect pc).lbPolicy = policyByteN pc.lb.toProxy := by rw [introspect_eq]

/-- The reported vhosts are the config's denoted proxy virtual hosts. -/
theorem introspect_vhosts (pc : ParsedConfig) :
    (introspect pc).vhosts = (proxyVHostNames pc.vitems).map String.data := by rw [introspect_eq]

/-- The reported route count is the number of route directives the config declares
(flat routes plus vhost items — the `has_routes` gate). -/
theorem introspect_routes (pc : ParsedConfig) :
    (introspect pc).routes = pc.routes.length + pc.vitems.length := by rw [introspect_eq]; rfl

/-- **`introspect_faithful` — the reported routes ARE the denoted route table.** For
a config that declares flat routes, the count `GET /admin/config` reports equals the
length of the DENOTED route table (`(denoteOn base pc).routing.routes`) plus the
declared vhost items, the reported LB byte is the denoted policy, and the reported
vhosts are the denoted proxy hosts. The route hypothesis is REAL (`pc.routes ≠ []`):
it selects the branch of `denoteRoutes` that installs the operator's table, so the
equation is a genuine statement about the denotation, not a tautology. -/
theorem introspect_faithful (base : DeploymentConfig) (pc : ParsedConfig)
    (h : pc.routes ≠ []) :
    (introspect pc).routes = (denoteOn base pc).routing.routes.length + pc.vitems.length
    ∧ (introspect pc).lbPolicy = policyByteN pc.lb.toProxy
    ∧ (introspect pc).vhosts = (proxyVHostNames pc.vitems).map String.data := by
  refine ⟨?_, introspect_lb pc, introspect_vhosts pc⟩
  rw [introspect_routes pc, denoteOn_routes base pc h, List.length_map]

/-! ## §5  The full-bytes `\n`-framing round-trip -/

/-- Join projection lines with `\n` (the blob `drorb_deployment_of_config` emits). -/
def joinNl : List (List Char) → List Char
  | []      => []
  | [l]     => l
  | l :: ls => l ++ '\n' :: joinNl ls

/-- Splitting the `\n`-join of newline-free lines recovers the lines — the framing
`config.rs`'s `s.lines()` inverts (over the PROVEN `Dsl.Config.splitOn1`). -/
theorem splitOn1_joinNl : ∀ (lines : List (List Char)), lines ≠ [] →
    (∀ l ∈ lines, '\n' ∉ l) → splitOn1 '\n' (joinNl lines) = lines := by
  intro lines
  induction lines with
  | nil => intro h _; exact absurd rfl h
  | cons l ls ih =>
    intro _ hmem
    have hl : '\n' ∉ l := hmem l (List.mem_cons_self)
    cases ls with
    | nil => exact splitOn1_no_sep '\n' l hl
    | cons u us =>
      have hmemts : ∀ x ∈ u :: us, '\n' ∉ x := fun x hx => hmem x (List.mem_cons_of_mem _ hx)
      show splitOn1 '\n' (l ++ '\n' :: joinNl (u :: us)) = l :: (u :: us)
      rw [splitOn1_append '\n' l (joinNl (u :: us)) hl, ih (by simp) hmemts]

/-- **The introspection read over the full blob equals the direct read.** Framing
the projection as a single `\n`-joined blob and re-splitting it (as the host does)
yields the same scan as reading the lines directly — so the byte-level path realizes
`introspect_faithful`. The hypothesis is REAL: the emitter's lines are newline-free
(tags and decimal counts by construction; hostnames by config well-formedness). -/
theorem introspect_over_blob (pc : ParsedConfig) (hnl : ∀ l ∈ emitLines pc, '\n' ∉ l) :
    scanReport (splitOn1 '\n' (joinNl (emitLines pc))) = introspect pc := by
  rw [splitOn1_joinNl (emitLines pc) (by simp [emitLines]) hnl]; rfl

/-! ## §6  Byte helpers (pure; mirrors NetmapLive) -/

def sc (l : List Char) : String := String.mk l

/-! ## §7  The selftest — the config introspection read over the byte level, NO crypto -/

/-- A concrete operator config: three flat routes (a static root, a redirect, a
proxy) and a `jelly.home` virtual host carrying a proxy route. -/
def demoPc : ParsedConfig :=
  { addr := "127.0.0.1".data
    port := 8443
    poolName := "webpool".data
    lb := Dsl.Cfg.LbPolicy.leastConn
    l4 := none
    zeroRtt := false
    routes :=
      [ { pathTok := "/".data,    handler := .static }
      , { pathTok := "/old".data, handler := .redirect 301 "/new".data }
      , { pathTok := "/api".data, handler := .proxy "webpool".data } ]
    vitems :=
      [ .host "jelly.home".data
      , .route { method := none, pathTok := "/".data, middleware := [],
                 headerGuard := none, queryGuard := none, handler := .proxy "jellypool".data } ] }

def selftest : IO UInt32 := do
  IO.println "== introspect-live selftest : config→route-table introspection, byte-level, NO crypto =="

  let pc := demoPc

  -- ── EMIT the projection the running host crosses at boot (drorb_deployment_of_config) ──
  let lines := emitLines pc
  let blob  := joinNl lines
  IO.println s!"\n-- projection blob (drorb_deployment_of_config) --"
  for l in lines do IO.println s!"  {sc l}"
  IO.println s!"blob bytes             : {blob.length}B"

  -- ── SCAN it back (config.rs :: parse_from_path strip-prefix loop) ──
  let rep := scanReport (splitOn1 '\n' blob)
  IO.println s!"\n-- scanned report (GET /admin/config reads) --"
  IO.println s!"lb_policy              : {rep.lbPolicy}"
  IO.println s!"routes                 : {rep.routes}"
  IO.println s!"vhosts                 : {rep.vhosts.map sc}"

  -- ── the denoted ground truth ──
  let denotedRoutes := (denoteOn Reactor.Deploy.defaultDeployment pc).routing.routes.length
  let denotedLb     := policyByteN pc.lb.toProxy
  let denotedVhosts := (proxyVHostNames pc.vitems).map String.data
  IO.println s!"\n-- denoted ground truth (denoteOn defaultDeployment) --"
  IO.println s!"denoted route table len : {denotedRoutes}   (+ {pc.vitems.length} vhost items)"
  IO.println s!"denoted lb policy byte  : {denotedLb}"
  IO.println s!"denoted proxy vhosts    : {denotedVhosts.map sc}"

  -- ── the faithfulness cross-check (realizes introspect_faithful) ──
  let blobEqDirect := rep == introspect pc
  let routesFaithful := rep.routes == denotedRoutes + pc.vitems.length
  let lbFaithful   := rep.lbPolicy == denotedLb
  let vhostFaithful := rep.vhosts == denotedVhosts
  let routesExpected := rep.routes == 5       -- 3 flat + 2 vhost items
  let lbExpected     := rep.lbPolicy == 1     -- leastConn → leastConnections → byte 1
  let vhostExpected  := rep.vhosts.map sc == ["jelly.home"]

  IO.println s!"\n-- cross-check (realizes introspect_faithful) --"
  IO.println s!"blob scan == direct scan          : {blobEqDirect}"
  IO.println s!"reported routes == denoted+vitems : {routesFaithful}"
  IO.println s!"reported lb == denoted policy      : {lbFaithful}"
  IO.println s!"reported vhosts == denoted vhosts  : {vhostFaithful}"
  IO.println s!"routes == 5 (3 flat + 2 vhost)     : {routesExpected}"
  IO.println s!"lb == 1 (leastConnections)         : {lbExpected}"
  IO.println s!"vhosts == [jelly.home]             : {vhostExpected}"

  if blobEqDirect && routesFaithful && lbFaithful && vhostFaithful
      && routesExpected && lbExpected && vhostExpected then do
    IO.println "\nPASS — config projected, blob emitted, scanned back; the reported"
    IO.println "       lb / route-count / vhosts equal the denoted config."
    IO.println "CONFIG INTROSPECTION LIVE-WIRED (drorb-native, byte-level, NO crypto, verified projection)."
    return 0
  else do
    IO.eprintln "\nFAIL — a field of the introspection read did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: introspect-live selftest"
    return 1

end IntrospectLive

def main (args : List String) : IO UInt32 := IntrospectLive.main args
