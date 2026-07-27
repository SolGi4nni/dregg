import Control
import Control.Distribute
/-!
# Control.Routes — subnet-route advertisement and approval

A **subnet router** is a mesh node that offers connectivity to IP prefixes
*beyond its own addresses* — a whole LAN behind it, say. In the public Tailscale
model this is `--advertise-routes` on the client (`tailcfg` carries the extra
prefixes in the node's `allowedIPs`) and route *approval* on the coordination
server (headscale's `nodes approve-routes` / the admin's route-approval step):
the server distributes a subnet route to peers **only after an operator approves
it**. An unapproved advertised route is never handed out, so cryptokey routing
never carries traffic toward the router for it.

This module models the two operations and ties them to the already-verified
netmap→WireGuard seam in `Control.Distribute`:

* `advertisedRoutes` — the subnet routes a node *offers* (its `allowedIPs`
  minus its own `addresses`): the prefixes an operator would see pending
  approval.
* `approveRoutes` — the node as *distributed* after approval: its own addresses
  (always self-routable) plus exactly the advertised routes the operator
  approved. This is the `Node` the netmap carries onward to `Node.toWgPeer`.

The headline (`route_needs_approval`) closes the loop with cryptokey routing:
after approval, WireGuard admits a destination toward the node only via one of
its own addresses or an operator-approved subnet route — never via an
advertised-but-unapproved one.
-/

namespace Control.Routes

open Control

/-- The **subnet routes** a node advertises: the entries of its `allowedIPs` that
are not among its own `addresses`. These are the prefixes reachable *through*
the node (a LAN behind a subnet router), as opposed to the node itself — exactly
the set an operator reviews for approval. -/
def advertisedRoutes (n : Node) : List Prefix :=
  n.allowedIPs.filter (fun p => ! n.addresses.contains p)

/-- The node **as distributed after route approval**. Its own `addresses` are
always retained (self-routing is never subject to approval); of the advertised
subnet routes, only those in `approved` are kept. This is the `Node` the
coordination server folds into peers' netmaps, and thence into WireGuard via
`Node.toWgPeer`. -/
def approveRoutes (approved : List Prefix) (n : Node) : Node :=
  { n with allowedIPs := n.addresses ++ (advertisedRoutes n).filter (fun p => approved.contains p) }

/-- **Self-routing survives approval.** Every one of the node's own addresses is
still in the distributed `allowedIPs` — route approval can only ever remove
advertised subnet routes, never the node's own reachability. -/
theorem own_addresses_kept (approved : List Prefix) (n : Node) :
    ∀ a ∈ n.addresses, a ∈ (approveRoutes approved n).allowedIPs := by
  intro a ha
  simp only [approveRoutes]
  exact List.mem_append.mpr (Or.inl ha)

/-- **Nothing enters the distributed set but own addresses and approved routes.**
Every prefix in the post-approval `allowedIPs` is either one of the node's own
addresses or an advertised subnet route the operator approved. No unapproved
advertised route is ever distributed. -/
theorem approved_or_own (approved : List Prefix) (n : Node) :
    ∀ p ∈ (approveRoutes approved n).allowedIPs,
      p ∈ n.addresses ∨ (p ∈ advertisedRoutes n ∧ approved.contains p = true) := by
  intro p hp
  simp only [approveRoutes] at hp
  rcases List.mem_append.mp hp with hown | hfilt
  · exact Or.inl hown
  · rw [List.mem_filter] at hfilt
    exact Or.inr hfilt

/-- **An unapproved advertised route is dropped.** A subnet route the node
advertises but the operator did not approve (and which is not one of the node's
own addresses) is absent from the distributed `allowedIPs` — hence unroutable
toward the node. -/
theorem unapproved_route_dropped (approved : List Prefix) (n : Node) (r : Prefix)
    (_hadv : r ∈ advertisedRoutes n) (hunapp : approved.contains r = false)
    (hown : r ∉ n.addresses) :
    r ∉ (approveRoutes approved n).allowedIPs := by
  intro hmem
  rcases approved_or_own approved n r hmem with h | ⟨_, happ⟩
  · exact hown h
  · rw [happ] at hunapp; exact Bool.noConfusion hunapp

/-- **Cryptokey routing admits a destination only via an own address or an
approved route** — the composition with the verified netmap→WireGuard seam.

Take the node as distributed after approval, `n' := approveRoutes approved n`. If
WireGuard cryptokey routing over `n'`'s translated allowed set admits `ip` (best
prefix length `k`), then there is a prefix in `n'`'s distributed `allowedIPs`
that matches `ip` — and by `approved_or_own` that prefix is either one of the
node's own addresses or an operator-approved advertised route. So after approval,
WireGuard carries traffic toward the node only for self-routing or approved
subnet routes; an unapproved advertised route can never be the admitting
prefix. -/
theorem route_needs_approval (approved : List Prefix) (n : Node) (ip : Bytes) (k : Nat)
    (h : Wireguard.Peer.bestPlen (Node.toWgPeer (approveRoutes approved n)).allowed ip = some k) :
    ∃ p ∈ (approveRoutes approved n).allowedIPs,
      p.matches ip = true ∧
        (p ∈ n.addresses ∨ (p ∈ advertisedRoutes n ∧ approved.contains p = true)) := by
  obtain ⟨p, hpmem, hpmatch, _⟩ :=
    Control.Distribute.wg_route_needs_allowed (approveRoutes approved n) ip k h
  exact ⟨p, hpmem, hpmatch, approved_or_own approved n p hpmem⟩

/-! ## §2  A route that IS approved lands in the distributed `allowedIPs`

The dual of `unapproved_route_dropped`: the *forward* direction the gate needs —
an advertised subnet route the operator (or an autoApprover) approved is present
in the node's distributed `allowedIPs`, so peers route toward it. -/

/-- **An approved advertised route is kept.** A subnet route the node advertises
and `approved` contains is in the distributed `allowedIPs` — hence handed to peers
and routable toward the node. -/
theorem approved_route_kept (approved : List Prefix) (n : Node) (r : Prefix)
    (hadv : r ∈ advertisedRoutes n) (happ : approved.contains r = true) :
    r ∈ (approveRoutes approved n).allowedIPs := by
  simp only [approveRoutes]
  refine List.mem_append.mpr (Or.inr ?_)
  rw [List.mem_filter]
  exact ⟨hadv, happ⟩

/-! ## §3  `autoApprovers` — policy-driven auto-approval of advertised routes

Public Tailscale ACL syntax (kb/1337, cross-checked; headscale mirrors it):

```
"autoApprovers": {
  "routes":   { "192.168.0.0/24": ["tag:router", "group:eng"] },
  "exitNode": ["tag:exit"]
}
```

`routes` maps a CIDR to the **approver identities** (tags / groups / users /
autogroups) permitted to advertise a route within it; `exitNode` lists the
approvers permitted to advertise an exit node. Headscale: *"the route
`192.168.0.0/24` is automatically approved once announced by a subnet router that
advertises the tag `tag:router`"*, and *"approval of either exit route
automatically approves the other"* (`0.0.0.0/0` ⇔ `::/0`).

A node's **approver identities** are resolved from the netmap (its ACL tags — the
`tag:` names copied onto the node at registration — plus user/group memberships).
Tags are carried on the `Control.Node` (`tags`, from the pre-auth key); user/group
membership resolution is the *node-registry residual* documented in
`Control.Policy` (`tag:`/user selectors resolve at serve time against data the
self-contained model does not own). This module resolves the **tag** identities
concretely and takes any further identities as an explicit input. -/

/-- The exit-node routes: `0.0.0.0/0` (all IPv4) and `::/0` (all IPv6) — the
default routes `--advertise-exit-node` announces (kb/1019; headscale routes ref). -/
def exitV4 : Prefix := ⟨[0, 0, 0, 0], 0⟩
def exitV6 : Prefix := ⟨List.replicate 16 0, 0⟩

/-- Is `p` one of the two exit-node default routes? -/
def isExitRoute (p : Prefix) : Bool := p == exitV4 || p == exitV6

/-- The parsed `autoApprovers` policy section: per configured CIDR, the approver
identity tokens that may auto-approve a route *within* it; plus the exit-node
approver tokens. (`Control.Policy.parseAutoApprovers` produces this from HuJSON.) -/
structure AutoApprovers where
  routes   : List (Prefix × List String)
  exitNode : List String
deriving Repr, DecidableEq

/-- No auto-approval configured. -/
def AutoApprovers.empty : AutoApprovers := { routes := [], exitNode := [] }

/-- `cfg` **covers** `r`: `r` is equal to or a subnet of `cfg` (same family, `cfg`
no longer than `r`, and `r`'s leading `cfg.bits` bits match `cfg`). This is the
headscale autoApprover match — an advertised route is auto-approved if it falls
within a configured prefix. -/
def covers (cfg r : Prefix) : Bool :=
  decide (cfg.bits ≤ r.bits) && cfg.matches r.addr

/-- **Does the policy auto-approve advertised route `r`** for a node bearing
approver identities `ids`? Either some configured route-prefix covers `r` and one
of *its* approvers is an identity of the node, or `r` is an exit route and one of
the `exitNode` approvers is. -/
def autoApproves (aa : AutoApprovers) (ids : List String) (r : Prefix) : Bool :=
  aa.routes.any (fun cfg => covers cfg.1 r && cfg.2.any (fun a => ids.contains a))
    || (isExitRoute r && aa.exitNode.any (fun a => ids.contains a))

/-- A node's approver identities: its ACL tags decoded to `tag:`-strings. (Group /
user memberships are the node-registry residual — passed as `extra`.) -/
def tagStr (bs : Bytes) : String := String.ofList (bs.map (fun b => Char.ofNat b.toNat))
def nodeIdentities (extra : List String) (n : Node) : List String :=
  n.tags.map tagStr ++ extra

/-- The advertised routes of `n` that end up **approved**: operator-approved
(a Store `routeApproved` event — `Control.Store`) **or** policy-auto-approved. -/
def approvedRoutes (aa : AutoApprovers) (ids : List String)
    (operatorApproved : List Prefix) (n : Node) : List Prefix :=
  (advertisedRoutes n).filter
    (fun r => operatorApproved.contains r || autoApproves aa ids r)

/-- The node **as distributed** after the combined (operator ∪ autoApprover)
approval — its `allowedIPs` carry its own addresses plus exactly the approved
advertised routes. This is what folds into peers' netmaps. -/
def approveNode (aa : AutoApprovers) (extra : List String)
    (operatorApproved : List Prefix) (n : Node) : Node :=
  approveRoutes (approvedRoutes aa (nodeIdentities extra n) operatorApproved n) n

/-- **Auto/operator approval keeps an approved route.** An advertised route that
is operator-approved or auto-approved is in the distributed `allowedIPs`. -/
theorem approveNode_keeps (aa : AutoApprovers) (extra : List String)
    (op : List Prefix) (n : Node) (r : Prefix)
    (hadv : r ∈ advertisedRoutes n)
    (happ : (op.contains r || autoApproves aa (nodeIdentities extra n) r) = true) :
    r ∈ (approveNode aa extra op n).allowedIPs := by
  refine approved_route_kept _ n r hadv ?_
  simp only [approvedRoutes]
  rw [List.contains_eq_mem, decide_eq_true_eq, List.mem_filter]
  exact ⟨hadv, happ⟩

/-- **Fail-closed: an unapproved advertised route is dropped.** A subnet route the
node advertises but which is *neither* operator-approved *nor* auto-approved (and
is not one of the node's own addresses) is absent from the distributed
`allowedIPs` — no unapproved routing, ever. -/
theorem approveNode_drops (aa : AutoApprovers) (extra : List String)
    (op : List Prefix) (n : Node) (r : Prefix)
    (hadv : r ∈ advertisedRoutes n)
    (hop : op.contains r = false)
    (hauto : autoApproves aa (nodeIdentities extra n) r = false)
    (hown : r ∉ n.addresses) :
    r ∉ (approveNode aa extra op n).allowedIPs := by
  have hc : (approvedRoutes aa (nodeIdentities extra n) op n).contains r = false := by
    simp only [approvedRoutes]
    rw [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_filter]
    rintro ⟨_, hpred⟩
    rw [hop, hauto] at hpred
    simp at hpred
  exact unapproved_route_dropped _ n r hadv hc hown

/-- **An approved exit route admits every address.** After approval, the exit
node's distributed `allowedIPs` contains `0.0.0.0/0` (bits 0 — matches every v4
address), so a peer selecting it routes *all* its traffic through the node: exit
selection. -/
theorem exitV4_matches_all (ip : Bytes) (h : ip.length = 4) :
    exitV4.matches ip = true := by
  simp [Prefix.matches, exitV4, h]

/-- **Exit-node selectability.** If `n` advertises the v4 exit route and it is
approved, then after approval `n`'s `allowedIPs` carries a prefix matching *every*
v4 address — a peer can select `n` as its exit node. -/
theorem exit_route_selectable (aa : AutoApprovers) (extra : List String)
    (op : List Prefix) (n : Node) (ip : Bytes) (h4 : ip.length = 4)
    (hadv : exitV4 ∈ advertisedRoutes n)
    (happ : (op.contains exitV4 || autoApproves aa (nodeIdentities extra n) exitV4) = true) :
    ∃ p ∈ (approveNode aa extra op n).allowedIPs, p.matches ip = true :=
  ⟨exitV4, approveNode_keeps aa extra op n exitV4 hadv happ, exitV4_matches_all ip h4⟩

/-! ## §4  The state transform: approve every registration's advertised routes

`approveState` rewrites each registration's node through `approveNode`, so the
coordination state a poll is served from already carries every node's *approved*
`allowedIPs`. `Control.buildNetMap` / `Control.Join.servedNetMapWire` then serve
those `allowedIPs` to peers unchanged — the approval decision is applied once,
before distribution. -/

/-- Rewrite every registration's node with its approved routes. `op` is the
per-node-key operator-approved set (the projection of the Store `routeApproved`
event log); `extra` supplies any non-tag approver identities per node key. -/
def approveState (aa : AutoApprovers) (extra : NodeKey → List String)
    (op : NodeKey → List Prefix) (st : ControlState) : ControlState :=
  { st with nodes := st.nodes.map (fun r =>
      { r with node := approveNode aa (extra r.nodeKey) (op r.nodeKey) r.node }) }

/-! ## §5  ★THE GATE (core netmap) — a node advertises `192.168.50.0/24`

A subnet router `100.64.0.5` advertises `192.168.50.0/24`; a laptop peer
`100.64.0.6` polls. We drive `approveState` + `buildNetMap` and inspect the
**router-peer's `allowedIPs`** in the laptop's served netmap: unapproved ⇒ the
subnet is absent; operator- or autoApprover-approved ⇒ present. Then an exit node
advertising `0.0.0.0/0` + `::/0`, approved, is selectable. -/

/-- ASCII string → bytes (for building tag literals). -/
def strBytes (s : String) : Bytes := s.toList.map (fun c => UInt8.ofNat c.toNat)

def route5024 : Prefix := ⟨[192, 168, 50, 0], 24⟩
def routerAddr : Prefix := ⟨[100, 64, 0, 5], 32⟩
def laptopAddr : Prefix := ⟨[100, 64, 0, 6], 32⟩
def exitAddr : Prefix := ⟨[100, 64, 0, 9], 32⟩

def kRouter : NodeKey := ⟨List.replicate 32 0x51⟩
def kLaptop : NodeKey := ⟨List.replicate 32 0x62⟩
def kExit : NodeKey := ⟨List.replicate 32 0x93⟩

/-- A netmap node with the given own address, advertised `allowedIPs`, and tags. -/
def mkRNode (id : Nat) (nm : Bytes) (own : Prefix) (allowed : List Prefix)
    (k : NodeKey) (tags : List Bytes) : Node :=
  { id := id, stableID := nm, name := nm, user := 1, key := k
  , machine := ⟨List.replicate 32 0⟩, disco := ⟨List.replicate 32 0⟩
  , addresses := [own], allowedIPs := allowed, endpoints := []
  , derp := 1, online := true, keyExpiry := 0, authorized := true, tags := tags }

/-- The router advertises `192.168.50.0/24` (in `allowedIPs`) and carries `tag:home`. -/
def routerNode : Node :=
  mkRNode 5 (strBytes "router") routerAddr [routerAddr, route5024] kRouter [strBytes "tag:home"]
def laptopNode : Node :=
  mkRNode 6 (strBytes "laptop") laptopAddr [laptopAddr] kLaptop []
/-- The exit node advertises `0.0.0.0/0` + `::/0` and carries `tag:exit`. -/
def exitNode : Node :=
  mkRNode 9 (strBytes "exit") exitAddr [exitAddr, exitV4, exitV6] kExit [strBytes "tag:exit"]

def regRouter : Registration := { nodeKey := kRouter, node := routerNode, status := .authorized }
def regLaptop : Registration := { nodeKey := kLaptop, node := laptopNode, status := .authorized }
def regExit   : Registration := { nodeKey := kExit,   node := exitNode,   status := .authorized }

/-- The subnet-router tailnet (router + laptop). -/
def stRoute : ControlState := { nodes := [regRouter, regLaptop], filter := [], dns := DnsConfig.empty }
/-- The exit-node tailnet (exit node + laptop). -/
def stExit  : ControlState := { nodes := [regExit,   regLaptop], filter := [], dns := DnsConfig.empty }

/-- autoApprovers: `192.168.50.0/24` approvable by `tag:home`. -/
def aaHome : AutoApprovers := { routes := [(route5024, ["tag:home"])], exitNode := [] }
/-- autoApprovers: an exit node approvable by `tag:exit`. -/
def aaExit : AutoApprovers := { routes := [], exitNode := ["tag:exit"] }

/-- No approver identities beyond tags, no operator approvals. -/
def noExtra : NodeKey → List String := fun _ => []
def noOp : NodeKey → List Prefix := fun _ => []
/-- The operator approved the router's `192.168.50.0/24` (a Store `routeApproved`). -/
def opRouter : NodeKey → List Prefix := fun k => if k = kRouter then [route5024] else []

/-- The router-peer's `allowedIPs` in the laptop's served netmap, under a transform. -/
def routerPeerAllowed (st : ControlState) : List (List Prefix) :=
  (buildNetMap st regLaptop).peers.map (·.allowedIPs)

/-- **Unapproved ⇒ the subnet is NOT served (fail-closed).** With no operator
approval and no autoApprovers, the router peer's `allowedIPs` carries only its own
`/32` — `192.168.50.0/24` never reaches the laptop. -/
theorem gate_unapproved_absent :
    routerPeerAllowed (approveState AutoApprovers.empty noExtra noOp stRoute) = [[routerAddr]] := by
  native_decide

/-- **Operator-approved ⇒ the subnet IS served.** After the operator's
`routeApproved` event, the router peer's `allowedIPs` carries the subnet route. -/
theorem gate_operator_present :
    routerPeerAllowed (approveState AutoApprovers.empty noExtra opRouter stRoute)
      = [[routerAddr, route5024]] := by native_decide

/-- **autoApprover-approved ⇒ the subnet IS served.** With `192.168.50.0/24`
auto-approved for `tag:home` (which the router bears), the subnet reaches the
laptop with *no* operator action. -/
theorem gate_autoapprover_present :
    routerPeerAllowed (approveState aaHome noExtra noOp stRoute)
      = [[routerAddr, route5024]] := by native_decide

/-- **Exit node approved ⇒ `0.0.0.0/0` + `::/0` served.** With `tag:exit`
auto-approved, the exit node's served `allowedIPs` carries both default routes. -/
theorem gate_exit_present :
    routerPeerAllowed (approveState aaExit noExtra noOp stExit)
      = [[exitAddr, exitV4, exitV6]] := by native_decide

/-- **The exit node is selectable.** In the served netmap the exit route matches
`8.8.8.8` (indeed every v4 address) — the laptop can route all traffic through it. -/
theorem gate_exit_selectable :
    ∃ p ∈ (approveNode aaExit [] [] exitNode).allowedIPs, p.matches [8, 8, 8, 8] = true :=
  exit_route_selectable aaExit [] [] exitNode [8, 8, 8, 8] rfl (by decide)
    (by native_decide)

end Control.Routes

#print axioms Control.Routes.own_addresses_kept
#print axioms Control.Routes.approved_or_own
#print axioms Control.Routes.unapproved_route_dropped
#print axioms Control.Routes.route_needs_approval
#print axioms Control.Routes.approved_route_kept
#print axioms Control.Routes.approveNode_keeps
#print axioms Control.Routes.approveNode_drops
#print axioms Control.Routes.exit_route_selectable
#print axioms Control.Routes.gate_unapproved_absent
#print axioms Control.Routes.gate_operator_present
#print axioms Control.Routes.gate_autoapprover_present
#print axioms Control.Routes.gate_exit_present
#print axioms Control.Routes.gate_exit_selectable
