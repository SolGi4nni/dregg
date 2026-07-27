import Control.Routes
import Control.Join
import Control.Policy

/-!
# Control.RoutesServe — the subnet-route seam, end to end

This module ties the three route-approval pieces together and drives the GATE at
the **wire** (`Control.Join.servedNetMapWire`) level:

* `Control.Policy.parseAutoApprovers` parses the HuJSON `autoApprovers` section
  into `(routes : [(Cidr, approvers)], exitNode : [approvers])`;
* `cfgToRoutes` bridges each `IpFilter.Cidr` to the coordination core's `Prefix`
  (`Control.Join.cidrToPrefix`) and wraps the result in
  `Control.Routes.AutoApprovers`;
* `Control.Routes.autoApproves` / `approveState` decide auto-approval and rewrite
  every registration's `allowedIPs` to carry exactly the *approved* routes;
* `Control.Join.servedNetMapWire` projects that into the real `tailcfg.MapResponse`
  a stock client receives — so an **approved** subnet route appears in a peer's
  wire `AllowedIPs`, an **unapproved** advertised route does **not** (fail-closed),
  and an approved exit node's `0.0.0.0/0` reaches the peer (it can select it).

Route provenance is public Tailscale/headscale (kb/1337 autoApprovers; kb/1019
subnet routers + exit nodes `0.0.0.0/0`+`::/0`; `tailcfg.Node.AllowedIPs`;
`headscale nodes approve-routes` = the Store `routeApproved` operator event).
-/

namespace Control.RoutesServe

open Control

/-! ## §1  Parse → `Routes.AutoApprovers` bridge, and the decision tie -/

/-- Bridge the parsed `(Cidr, approvers)` route config to `Routes.AutoApprovers`,
converting each `IpFilter.Cidr` to the core `Prefix` the netmap speaks
(`Control.Join.cidrToPrefix`). -/
def cfgToRoutes (t : List (IpFilter.Cidr × List String) × List String) :
    Control.Routes.AutoApprovers :=
  { routes := t.1.map (fun ca => (Control.Join.cidrToPrefix ca.1, ca.2))
  , exitNode := t.2 }

/-- The homelab autoApprovers, parsed from HuJSON and bridged. -/
def parsedAA : Control.Routes.AutoApprovers :=
  cfgToRoutes ((Control.Policy.parseAutoApprovers Control.Policy.sampleAAJson).toOption.getD ([], []))

/-- **The parsed config bridges to the expected core-`Prefix` autoApprovers** —
`192.168.50.0/24 ↦ [tag:home]`, `exitNode ↦ [tag:exit]`. -/
theorem parsedAA_eq :
    parsedAA = { routes := [(Control.Routes.route5024, ["tag:home"])], exitNode := ["tag:exit"] } := by
  native_decide

/-- **★ Parse → decision (auto-approved).** The parsed config auto-approves
`192.168.50.0/24` for a node bearing `tag:home` — HuJSON text all the way to
`Control.Routes.autoApproves`. -/
theorem parsed_aa_approves_home :
    Control.Routes.autoApproves parsedAA ["tag:home"] Control.Routes.route5024 = true := by
  native_decide

/-- **★ Parse → decision (denied, fail-closed).** A route the config does not
cover (`10.0.0.0/24`) is NOT auto-approved. -/
theorem parsed_aa_denies_unlisted :
    Control.Routes.autoApproves parsedAA ["tag:home"] ⟨[10, 0, 0, 0], 24⟩ = false := by
  native_decide

/-- **★ Parse → decision (wrong identity, fail-closed).** Even the right route is
not auto-approved for a node lacking the approver tag. -/
theorem parsed_aa_denies_wrong_tag :
    Control.Routes.autoApproves parsedAA ["tag:guest"] Control.Routes.route5024 = false := by
  native_decide

/-- **★ Parse → decision (exit node).** The parsed config auto-approves the
`0.0.0.0/0` exit route for a node bearing `tag:exit`. -/
theorem parsed_aa_approves_exit :
    Control.Routes.autoApproves parsedAA ["tag:exit"] Control.Routes.exitV4 = true := by
  native_decide

/-! ## §2  ★THE GATE (wire) — an approved route reaches a peer's `AllowedIPs`

The laptop polls; we inspect the **router-peer's wire `AllowedIPs`** in the
`tailcfg.MapResponse` `Control.Join.servedNetMapWire` produces. `Control.Routes`
supplies the tailnet (`stRoute`: router `100.64.0.5` advertising `192.168.50.0/24`
+ laptop `100.64.0.6`), the autoApprovers, and the operator-approval set. -/

open Control.Routes (approveState AutoApprovers stRoute regLaptop kLaptop kExit aaHome opRouter
  noExtra noOp exitAddr exitV4 mkRNode strBytes)

/-- The router-peer's wire `AllowedIPs` (CIDR strings) in the laptop's served
`MapResponse`, under a state transform. -/
def servedPeerAllowed (st : ControlState) : Option (List (Option (List String))) :=
  (Control.Join.servedNetMapWire st kLaptop).peers.map (·.map (·.allowedIPs))

/-- **Unapproved ⇒ the subnet is NOT in the peer's wire `AllowedIPs` (fail-closed).**
With no operator approval and no autoApprovers, the router peer carries only its
own `100.64.0.5/32`; `192.168.50.0/24` never reaches the stock client. -/
theorem served_wire_unapproved :
    servedPeerAllowed (approveState AutoApprovers.empty noExtra noOp stRoute)
      = some [some ["100.64.0.5/32"]] := by native_decide

/-- **Operator-approved ⇒ the subnet IS served.** After the operator's Store
`routeApproved` event, `192.168.50.0/24` is in the router peer's wire `AllowedIPs`. -/
theorem served_wire_operator :
    servedPeerAllowed (approveState AutoApprovers.empty noExtra opRouter stRoute)
      = some [some ["100.64.0.5/32", "192.168.50.0/24"]] := by native_decide

/-- **autoApprover-approved ⇒ the subnet IS served (no operator action).** With
`192.168.50.0/24 ↦ tag:home` and the router bearing `tag:home`, the subnet reaches
the laptop's wire `AllowedIPs` automatically. -/
theorem served_wire_autoapprover :
    servedPeerAllowed (approveState aaHome noExtra noOp stRoute)
      = some [some ["100.64.0.5/32", "192.168.50.0/24"]] := by native_decide

/-! ### Exit node (v4) — `0.0.0.0/0` reaches the peer, which can select it -/

/-- A v4 exit node (`--advertise-exit-node`'s `0.0.0.0/0`; the `::/0` v6 render is
`Control.Join.prefixToWire`'s documented v4-only residual, exercised at the core
level in `Control.Routes.gate_exit_present`). -/
def exitNode4 : Node :=
  mkRNode 9 (strBytes "exit") exitAddr [exitAddr, exitV4] kExit [strBytes "tag:exit"]
def regExit4 : Registration := { nodeKey := kExit, node := exitNode4, status := .authorized }
def stExit4 : ControlState := { nodes := [regExit4, regLaptop], filter := [], dns := DnsConfig.empty }
/-- autoApprovers: an exit node approvable by `tag:exit`. -/
def aaExit4 : AutoApprovers := { routes := [], exitNode := ["tag:exit"] }

/-- **Exit node approved ⇒ `0.0.0.0/0` in the peer's wire `AllowedIPs`.** The
laptop receives the exit node's default route and can select it as its exit. -/
theorem served_wire_exit :
    servedPeerAllowed (approveState aaExit4 noExtra noOp stExit4)
      = some [some ["100.64.0.9/32", "0.0.0.0/0"]] := by native_decide

/-- **Exit unapproved ⇒ `0.0.0.0/0` withheld (fail-closed).** Without the
autoApprover (or an operator approval), the default route is not served. -/
theorem served_wire_exit_unapproved :
    servedPeerAllowed (approveState AutoApprovers.empty noExtra noOp stExit4)
      = some [some ["100.64.0.9/32"]] := by native_decide

/-! ### My-hand inspection — the actual served wire `AllowedIPs` (`#eval`) -/

-- unapproved: router peer carries only its own /32
#eval servedPeerAllowed (approveState AutoApprovers.empty noExtra noOp stRoute)
-- autoApprover (tag:home): 192.168.50.0/24 now present
#eval servedPeerAllowed (approveState aaHome noExtra noOp stRoute)
-- operator (Store routeApproved): 192.168.50.0/24 present
#eval servedPeerAllowed (approveState AutoApprovers.empty noExtra opRouter stRoute)
-- exit node (tag:exit): 0.0.0.0/0 present → laptop can select it
#eval servedPeerAllowed (approveState aaExit4 noExtra noOp stExit4)

end Control.RoutesServe

#print axioms Control.RoutesServe.parsedAA_eq
#print axioms Control.RoutesServe.parsed_aa_approves_home
#print axioms Control.RoutesServe.parsed_aa_denies_unlisted
#print axioms Control.RoutesServe.parsed_aa_denies_wrong_tag
#print axioms Control.RoutesServe.parsed_aa_approves_exit
#print axioms Control.RoutesServe.served_wire_unapproved
#print axioms Control.RoutesServe.served_wire_operator
#print axioms Control.RoutesServe.served_wire_autoapprover
#print axioms Control.RoutesServe.served_wire_exit
#print axioms Control.RoutesServe.served_wire_exit_unapproved
