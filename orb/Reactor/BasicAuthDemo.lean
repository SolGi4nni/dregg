import Reactor.App
import Reactor.RouteMiddleware
import Dsl.Config.Gateway

/-!
Native my-hand demonstration of the config-full `basic_auth` gate: drives the REAL
compiled `Reactor.App.vhandlerResponse` (-> `Reactor.RouteMw.runChain` -> the proven
`BasicAuth.authenticate`, with the `verify` boundary backed by the AUDITED ADAPTIVE
PBKDF2-HMAC-SHA256 KDF `Crypto.pbkdf2Verify`) against the actual
`pbkdf2_sha256$600000$…` hash on the `admin.example.test /admin` route from
`Dsl.Config.Gateway.dreggNet`. No creds / wrong creds => realm 401; correct simbi
credential => the inner handler. The 600 000-round KDF is a real work factor (the
verify takes measurable time). AWS-LC backing (audited) — no bcrypt, no openssl.
-/

open Reactor.App (VHandler vhandlerResponse)
open Reactor.RouteMw (RouteMw)
open Proto (Request)

/-- The actual config route for the gated vhost (selected from the replicated dregg.net config). -/
def dreggAdminRoute : Dsl.Config.Gateway.GwRoute :=
  match Dsl.Config.Gateway.selectRoute Dsl.Config.Gateway.dreggNet
          (Dsl.Config.Gateway.GwReq.mk ["dreggnet","fg-goose","online"] "GET" ["admin"]) with
  | some r => r
  | none   => { path := .anyPath, action := .respond 500 "no-route" }

/-- The gate middleware EXACTLY as `routeVHandler` wires it, built from the real config data. -/
def gateMw : RouteMw :=
  match dreggAdminRoute.basicAuth with
  | some ba => .basicAuth ba.realm ba.users
  | none    => .deny "x".toUTF8.toList

/-- The credential store from the real config. -/
def storeUsers : List (String × String) := (dreggAdminRoute.basicAuth.map (fun ba => ba.users)).getD []

/-- The gated answer with a clean 200 inner, so the PASS is unambiguous. -/
def demoVH : VHandler := .guarded [gateMw] (.respond 200 "admin-ok\n".toUTF8.toList)

def mkReq (auth : Option String) : Request :=
  { method := "GET".toUTF8.toList, target := "/admin/panel".toUTF8.toList, version := []
    headers := match auth with
      | none   => []
      | some v => [("Authorization".toUTF8.toList, v.toUTF8.toList)] }

def bytesToStr (b : List UInt8) : String := String.ofList (b.map (fun x => Char.ofNat x.toNat))

def wwwAuth (r : Reactor.Response) : String :=
  match r.headers.find? (fun p => bytesToStr p.1 == "WWW-Authenticate") with
  | some p => bytesToStr p.2
  | none   => "(none)"

def showCase (label : String) (auth : Option String) : IO Unit := do
  let r := vhandlerResponse (mkReq auth) demoVH
  IO.println s!"  {label} : status={r.status}  WWW-Authenticate={wwwAuth r}  body={bytesToStr r.body}"

def main : IO Unit := do
  IO.println "== config-full basic_auth gate demo (admin.example.test /admin) =="
  IO.println s!"  config route handlerTag = {Dsl.Config.Gateway.handlerTag (Dsl.Config.Gateway.routeVHandler dreggAdminRoute)} (must be: guarded)"
  IO.println s!"  gate middleware         = {repr gateMw}"
  let vGood := Reactor.RouteMw.basicVerify "dreggnet" storeUsers "simbi" "orbtender-2026"
  let vBad  := Reactor.RouteMw.basicVerify "dreggnet" storeUsers "simbi" "wrongpass"
  IO.println "-- adaptive PBKDF2 verify boundary (Crypto.pbkdf2Verify, AWS-LC, 600000 rounds) --"
  IO.println s!"  verify simbi:orbtender-2026 (correct) = {vGood}"
  IO.println s!"  verify simbi:wrongpass       (wrong) = {vBad}"
  -- Work-factor timing. Each iteration verifies a DISTINCT password string
  -- (`orbtender-2026-{i}`), so the compiler cannot CSE/hoist the call: the full
  -- 600000-round PBKDF2 derivation genuinely runs n times. The KDF cost is identical
  -- for a right or wrong password (the work is in deriving the key from the
  -- stored salt+iterations), so this is a faithful measure of the deployed verify's cost.
  let n := 8
  let t0 ← IO.monoMsNow
  let mut matched := 0
  for i in [0:n] do
    -- the `if` observes each result, so the call cannot be dead-code-eliminated
    if Reactor.RouteMw.basicVerify "dreggnet" storeUsers "simbi" s!"orbtender-2026-{i}" then
      matched := matched + 1
  let t1 ← IO.monoMsNow
  IO.println s!"  work factor: {n}x 600000-round PBKDF2 verify ({matched} matched, all distinct pw) in {t1 - t0} ms total (~{(t1 - t0) / n} ms each) — a real KDF cost"
  IO.println "-- the served gate (vhandlerResponse -> runChain -> BasicAuth.authenticate) --"
  showCase "no creds       " none
  showCase "correct simbi  " (some "Basic c2ltYmk6b3JidGVuZGVyLTIwMjY=")
  showCase "wrong password " (some "Basic c2ltYmk6d3JvbmdwYXNz")
