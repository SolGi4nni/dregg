import Control
import Control.Acl

/-!
# Control.Tags — node tags as ACL principals, and who may apply them

`Control/Acl.lean` gives `tag:x` a first-class `Selector` and proves the default-deny
compilation over it. This module supplies the **other half**: where a tag's addresses
come from, and the ownership gate that decides whether a node's tag counts at all.

  registry (`List Control.Node`, each carrying `Node.tags` + `Node.user`)
      │  effectiveTags   — drop every tag the node's OWNER may not apply
      ▼
  tagBindings : List (String × List Cidr)        -- tag:x ↦ addresses of its bearers
      │  withTagBindings — the ONLY writer of `Acl.Policy.tags`
      ▼
  Acl.compile  →  FilterRule[]  →  the served `MapResponse.PacketFilters["base"]`

## What is PROVEN here (general `∀`-statements, not an enumeration)

* `tagBindings_owned` — **every** binding the projection emits names a tag that some
  registry node bears AND that node's owner is permitted to apply. An unowned tag can
  never contribute an address.
* `tag_admits_iff` — the ACL's `.tag` test on an address holds **iff** some node bears
  that tag effectively and one of its own prefixes contains the address. This is the
  semantic content of "a tag denotes its bearers".
* `unowned_tag_denies` — if no registry node's owner may apply `t`, the `.tag t`
  selector admits nothing, for every address.
* `no_owned_bearer_dropped` — ★the tag security property: a packet whose source is not
  an address of any legitimate bearer of `t` is DROPPED by a policy whose entries are
  sourced at `tag:t`. Proved through `Acl.policy_default_deny`, restated — not around it.
* `tagBindings_ownerless_empty` — with an EMPTY `tagOwners` the projection is empty:
  forgetting the section fails closed.

## What is NOT proven (named, not hidden)

* **Expiry ∩ tags.** `Control.Expiry` drops an expired node from every served peer list
  at serve time (`expired_peer_not_served`), but the tag projection is over the replayed
  registry, so a node whose `keyExpiry` has passed *without* a recorded `nodeExpired`
  event still contributes its address to a tag binding. `ControlLive.servedFrom` only
  projects `.authorized` registrations, so an operator-expired node (which replay marks
  `.expired`) IS excluded; the clock-only case is the residual. It is not a reachability
  hole — an expired node is served to nobody and has no WireGuard path — but the filter
  bytes are wider than they need to be.
* **Tag assignment at enrolment is checked at PROJECTION time, not only at mint time.**
  `Control.PreAuth.registerWithPreAuth` still stamps whatever tags the key carried; the
  ownership gate is applied here, where the ACL is compiled. That is deliberate: the
  policy hot-reloads, so a tag that LOSES its owner must stop conferring reach without
  re-enrolling anything. Minting a key with an unowned tag is therefore not an error —
  the tag simply never binds. `Control.Tags.mintable` exposes the check for the CLI so
  the operator is told at mint time too.
-/

namespace Control.Tags

open Control
open IpFilter (Cidr Addr matchCidr)

/-! ## §1  `Control.Prefix`/bytes → `IpFilter.Cidr`/`Addr` (MSB-first bits)

The coordination core speaks byte-addressed `Control.Prefix`; the ACL compiler speaks
`IpFilter.Cidr` (an MSB-first bit list + a family tag). Same bridge as
`Control.Join.cidrToPrefix`, in the other direction. -/

/-- One byte to its 8 bits, most-significant first. -/
def bitsOfByte (b : UInt8) : List Bool :=
  (List.range 8).map (fun i => (b.toNat >>> (7 - i)) % 2 == 1)

/-- A byte string to its bits, MSB-first (matches `IpFilter.Addr.bits`). -/
def bitsOfBytes (bs : List UInt8) : List Bool := bs.flatMap bitsOfByte

/-- v6 iff 16 bytes, else v4 (the modeled dual stack). -/
def famOf (bs : List UInt8) : IpFilter.Family := if bs.length == 16 then .v6 else .v4

/-- A coordination-core `Prefix` to the ACL compiler's `IpFilter.Cidr`. -/
def prefixToCidr (p : Prefix) : Cidr :=
  { family := famOf p.addr, net := bitsOfBytes p.addr, len := p.bits }

/-- A byte address to an `IpFilter.Addr` (for evaluating packets). -/
def addrOfBytes (bs : List UInt8) : Addr :=
  { family := famOf bs, bits := bitsOfBytes bs }

/-- Decode a tag stored as UTF-8 bytes (`Node.tags`, the `tailcfg.Node.Tags` wire
field) to its `tag:<name>` string. -/
def tagName (t : List UInt8) : String := (String.fromUTF8? ⟨t.toArray⟩).getD ""

/-- The tag names a node CLAIMS (before the ownership gate). -/
def claimedTags (n : Node) : List String := n.tags.map tagName

/-! ## §2  The ownership gate and the registry projection -/

/-- **The tags a node may actually carry.** A claimed tag counts only if the node's
owning user is permitted to apply it per `tagOwners`. An unowned (or undeclared) tag
is DROPPED — fail-closed. -/
def effectiveTags (ow : Acl.TagOwners) (n : Node) : List String :=
  (claimedTags n).filter (fun t => Acl.tagOwnedBy ow t n.user)

/-- A node's own addresses as ACL CIDRs (its `/32` and any v6 prefix). -/
def nodeCidrs (n : Node) : List Cidr := n.addresses.map prefixToCidr

/-- **The tag→CIDR binding table.** Each node contributes, for every tag it may
legitimately carry, the addresses it holds. This is the ONLY producer of
`Acl.Policy.tags`; a policy file cannot write it. -/
def tagBindings (ow : Acl.TagOwners) (nodes : List Node) : List (String × List Cidr) :=
  nodes.flatMap (fun n => (effectiveTags ow n).map (fun t => (t, nodeCidrs n)))

/-- **Bind an operator policy's tags against the registry.** `pol` comes from the
HuJSON file (with `tags = []`, `Control.Policy.parsePolicy_tags_empty`); this is the
step that makes `tag:x` denote anything at all, and it uses the policy's OWN
`tagOwners` declaration, so editing `tagOwners` re-decides every binding on reload. -/
def withTagBindings (pol : Acl.Policy) (nodes : List Node) : Acl.Policy :=
  { pol with tags := tagBindings pol.tagOwners nodes }

/-- The mint-time advisory: may user `u` be handed a key bearing tag `t`? Same
predicate the projection enforces; exposed so `drorb-ctl` can warn at mint time
instead of the operator discovering a silent deny later. -/
def mintable (ow : Acl.TagOwners) (u : Nat) (t : List UInt8) : Bool :=
  Acl.tagOwnedBy ow (tagName t) u

/-! ## §3  Theorems — the general statements

Every statement below quantifies over an arbitrary `tagOwners`, an arbitrary node
list and an arbitrary address. They are NOT enumerations of call sites. -/

/-- A membership fact about the projection, in the form the later proofs consume. -/
theorem mem_tagBindings_iff (ow : Acl.TagOwners) (nodes : List Node)
    (b : String × List Cidr) :
    b ∈ tagBindings ow nodes
      ↔ ∃ n ∈ nodes, ∃ t ∈ effectiveTags ow n, b = (t, nodeCidrs n) := by
  simp [tagBindings, List.mem_flatMap, List.mem_map, eq_comm]

/-- ★**OWNERSHIP SOUNDNESS.** Every binding the projection emits comes from a node
that (a) claims the tag and (b) whose owning user is permitted to apply it, and binds
exactly that node's own addresses. An unowned tag contributes NOTHING, ever. -/
theorem tagBindings_owned (ow : Acl.TagOwners) (nodes : List Node)
    (b : String × List Cidr) (h : b ∈ tagBindings ow nodes) :
    ∃ n ∈ nodes, b.1 ∈ claimedTags n
      ∧ Acl.tagOwnedBy ow b.1 n.user = true
      ∧ b.2 = nodeCidrs n := by
  rw [mem_tagBindings_iff] at h
  obtain ⟨n, hn, t, ht, rfl⟩ := h
  rw [effectiveTags, List.mem_filter] at ht
  exact ⟨n, hn, ht.1, by simpa using ht.2, rfl⟩

/-- **An ownerless tailnet binds nothing.** With `tagOwners = []` every tag is
undeclared, so the projection is empty regardless of what tags nodes claim: forgetting
the `tagOwners` section fails CLOSED. -/
theorem tagBindings_ownerless_empty (nodes : List Node) :
    tagBindings [] nodes = [] := by
  have he : ∀ n : Node, effectiveTags [] n = [] := by
    intro n
    simp [effectiveTags, Acl.tagOwnedBy]
  simp [tagBindings, he]

/-- The CIDRs a tag resolves to are the concatenation of its legitimate bearers'
address sets — the lookup unfolded to node terms. -/
theorem lookup_tagBindings_iff (ow : Acl.TagOwners) (nodes : List Node)
    (t : String) (c : Cidr) :
    c ∈ Acl.lookupGroup (tagBindings ow nodes) t
      ↔ ∃ n ∈ nodes, t ∈ effectiveTags ow n ∧ c ∈ nodeCidrs n := by
  simp only [Acl.lookupGroup, List.mem_flatMap, List.mem_filter, mem_tagBindings_iff]
  constructor
  · rintro ⟨b, ⟨⟨n, hn, t', ht', rfl⟩, hb⟩, hc⟩
    simp only [decide_eq_true_eq] at hb
    subst hb
    exact ⟨n, hn, ht', hc⟩
  · rintro ⟨n, hn, ht, hc⟩
    exact ⟨(t, nodeCidrs n), ⟨⟨n, hn, t, ht, rfl⟩, by simp⟩, hc⟩

/-- ★**TAG RESOLUTION SEMANTICS.** The ACL's `.tag t` source test admits address `a`
**iff** some registry node legitimately bears `t` and one of that node's own prefixes
contains `a`. This is what makes `tag:` a principal rather than a string. -/
theorem tag_admits_iff (groups : List (String × List Cidr)) (ow : Acl.TagOwners)
    (nodes : List Node) (t : String) (a : Addr) :
    Acl.selAdmitsSrc groups (tagBindings ow nodes) (.tag t) a = true
      ↔ ∃ n ∈ nodes, t ∈ effectiveTags ow n
          ∧ ∃ p ∈ n.addresses, matchCidr (prefixToCidr p) a = true := by
  rw [Acl.tag_admitsSrc_iff]
  constructor
  · rintro ⟨c, hc, hm⟩
    obtain ⟨n, hn, ht, hcn⟩ := (lookup_tagBindings_iff ow nodes t c).mp hc
    rw [nodeCidrs, List.mem_map] at hcn
    obtain ⟨p, hp, rfl⟩ := hcn
    exact ⟨n, hn, ht, p, hp, hm⟩
  · rintro ⟨n, hn, ht, p, hp, hm⟩
    exact ⟨prefixToCidr p,
      (lookup_tagBindings_iff ow nodes t (prefixToCidr p)).mpr
        ⟨n, hn, ht, List.mem_map.mpr ⟨p, hp, rfl⟩⟩, hm⟩

/-- ★**AN UNOWNED TAG CONFERS NOTHING.** If no registry node's owner may apply `t`,
the `.tag t` selector admits no address at all. (The nodes may freely *claim* `t` —
`Node.tags` is client-influenced data; ownership is what makes it count.) -/
theorem unowned_tag_denies (groups : List (String × List Cidr)) (ow : Acl.TagOwners)
    (nodes : List Node) (t : String) (a : Addr)
    (hno : ∀ n ∈ nodes, Acl.tagOwnedBy ow t n.user = false) :
    Acl.selAdmitsSrc groups (tagBindings ow nodes) (.tag t) a = false := by
  cases hb : Acl.selAdmitsSrc groups (tagBindings ow nodes) (.tag t) a with
  | false => rfl
  | true =>
    obtain ⟨n, hn, ht, _⟩ := (tag_admits_iff groups ow nodes t a).mp hb
    rw [effectiveTags, List.mem_filter] at ht
    have := ht.2
    rw [hno n hn] at this
    exact absurd this (by decide)

/-- ★**THE TAG SECURITY PROPERTY.** Take any policy whose ACL entries are all sourced
at `tag:t` (the shape a `"src": ["tag:t"]` file compiles to). If NO legitimate bearer
of `t` holds an address containing the packet's source, the packet is DROPPED.

General over the policy, the owners table, the registry and the packet — this is the
statement that a node which does not (legitimately) carry the tag cannot use a
`tag:`-sourced rule. It is proved THROUGH `Acl.policy_default_deny` restated over the
tag-extended language, not around it. -/
theorem no_owned_bearer_dropped (pol : Acl.Policy) (nodes : List Node)
    (t : String) (pkt : Acl.Packet)
    (hsrc : ∀ e ∈ pol.acls, e.src = [Acl.Selector.tag t])
    (hno : ∀ n ∈ nodes, t ∈ effectiveTags pol.tagOwners n →
             ∀ p ∈ n.addresses, matchCidr (prefixToCidr p) pkt.srcIP = false) :
    Acl.evalPolicy (withTagBindings pol nodes) pkt = Acl.Verdict.drop := by
  apply Acl.policy_default_deny
  intro e he
  have hsel : Acl.selAdmitsSrc pol.groups (tagBindings pol.tagOwners nodes)
      (.tag t) pkt.srcIP = false := by
    cases hb : Acl.selAdmitsSrc pol.groups (tagBindings pol.tagOwners nodes)
        (.tag t) pkt.srcIP with
    | false => rfl
    | true =>
      obtain ⟨n, hn, ht, p, hp, hm⟩ :=
        (tag_admits_iff pol.groups pol.tagOwners nodes t pkt.srcIP).mp hb
      rw [hno n hn ht p hp] at hm
      exact absurd hm (by decide)
  have hsrcE : Acl.entrySrcAdmits pol.groups (tagBindings pol.tagOwners nodes)
      e pkt.srcIP = false := by
    simp [Acl.entrySrcAdmits, hsrc e he, hsel]
  simp [Acl.entryAdmits, withTagBindings, hsrcE]

/-- **The binding step touches nothing else.** `withTagBindings` rewrites only the
`tags` field: the operator's groups, ACL entries and `tagOwners` are carried through
verbatim, so the policy the compiler sees is the parsed one plus a registry table. -/
theorem withTagBindings_preserves (pol : Acl.Policy) (nodes : List Node) :
    (withTagBindings pol nodes).groups = pol.groups
    ∧ (withTagBindings pol nodes).acls = pol.acls
    ∧ (withTagBindings pol nodes).tagOwners = pol.tagOwners
    ∧ (withTagBindings pol nodes).tags = tagBindings pol.tagOwners nodes :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Restated soundness, with tags bound.** The end-to-end `iff` of
`Acl.policy_allow_iff_entry`, phrased over the registry-bound policy: the served
filter Allows a packet iff some ACL entry admits it, resolving `.tag` selectors
through the registry projection. The tag extension goes THROUGH the soundness
theorem. -/
theorem bound_allow_iff_entry (pol : Acl.Policy) (nodes : List Node) (pkt : Acl.Packet) :
    Acl.evalPolicy (withTagBindings pol nodes) pkt = Acl.Verdict.allow
      ↔ ∃ e ∈ pol.acls,
          Acl.entryAdmits pol.groups (tagBindings pol.tagOwners nodes) e pkt = true :=
  Acl.policy_allow_iff_entry (withTagBindings pol nodes) pkt

/-- **Restated default-deny, with tags bound.** -/
theorem bound_default_deny (pol : Acl.Policy) (nodes : List Node) (pkt : Acl.Packet)
    (h : ∀ e ∈ pol.acls,
          Acl.entryAdmits pol.groups (tagBindings pol.tagOwners nodes) e pkt = false) :
    Acl.evalPolicy (withTagBindings pol nodes) pkt = Acl.Verdict.drop :=
  Acl.policy_default_deny (withTagBindings pol nodes) pkt h

/-! ## §4  Non-vacuity on real registry values

The theorems above are `∀`-statements; these are witnesses that they are not
vacuously satisfiable — a concrete registry where the ownership gate flips the verdict
on the SAME packet.

★HONEST LABEL: `nv_owned_binds` / `nv_unowned_binds_nothing` /
`nv_ownership_flips_verdict` are `native_decide` (compiler-evaluated, so they carry
`Lean.ofReduceBool` + `Lean.trustCompiler`), because `tagName` goes through
`String.fromUTF8?` on a `ByteArray`, which the kernel cannot reduce. They are
WITNESSES, not the safety argument: the safety argument is the `∀`-theorems in §3,
which are kernel-checked on the standard axioms. `nv_no_owners_denies` IS kernel
`decide`. -/

/-- `tag:server`, as the bytes a node's `Node.tags` actually carries. -/
def serverTag : List UInt8 := "tag:server".toUTF8.toList

/-- A node claiming `tag:server`, owned by user 7, at `100.64.0.9/32`. -/
def nodeOwned : Node :=
  { id := 9, stableID := [], name := [], user := 7, key := ⟨List.replicate 32 0xC1⟩,
    machine := ⟨[]⟩, disco := ⟨[]⟩, addresses := [⟨[100, 64, 0, 9], 32⟩],
    allowedIPs := [⟨[100, 64, 0, 9], 32⟩], endpoints := [], derp := 0,
    online := true, keyExpiry := 0, authorized := true, tags := [serverTag] }

/-- The SAME node claiming the SAME tag, but owned by user 8. -/
def nodeUnowned : Node := { nodeOwned with user := 8 }

/-- `tagOwners: { "tag:server": ["user:7"] }`. -/
def demoOwners : Acl.TagOwners := [("tag:server", [Acl.Owner.user 7])]

/-- `accept src=tag:server dst=*:0-65535` — the operator's file, tags unbound. -/
def demoPol : Acl.Policy :=
  { groups := []
  , acls := [ { src := [Acl.Selector.tag "tag:server"]
              , dst := [(Acl.Selector.cidr ⟨.v4, [], 0⟩, ⟨0, 65535⟩)]
              , protos := [] } ]
  , tagOwners := demoOwners }

def demoPkt : Acl.Packet :=
  { srcIP := addrOfBytes [100, 64, 0, 9], dstIP := addrOfBytes [100, 64, 0, 10],
    dstPort := 443, proto := 6 }

/-- **The owned tag binds to the bearer's address.** -/
theorem nv_owned_binds :
    tagBindings demoOwners [nodeOwned]
      = [("tag:server", [prefixToCidr ⟨[100, 64, 0, 9], 32⟩])] := by native_decide

/-- **The unowned claim binds NOTHING** — user 8 may not apply `tag:server`, so the
identical `Node.tags` yields an empty table. -/
theorem nv_unowned_binds_nothing : tagBindings demoOwners [nodeUnowned] = [] := by
  native_decide

/-- ★**The ownership gate flips the served verdict on the SAME packet.** With the
legitimately-tagged node in the registry the packet is ALLOWED; with the node that
merely *claims* the tag it is DROPPED. Ownership is load-bearing, not decoration. -/
theorem nv_ownership_flips_verdict :
    Acl.evalPolicy (withTagBindings demoPol [nodeOwned]) demoPkt = Acl.Verdict.allow
    ∧ Acl.evalPolicy (withTagBindings demoPol [nodeUnowned]) demoPkt = Acl.Verdict.drop := by
  native_decide

set_option maxRecDepth 8000 in
/-- **An empty `tagOwners` denies even the legitimately-claimed tag** — the
fail-closed default, on a real node. (This one IS kernel-`decide`: with no owners the
projection short-circuits before `tagName` is forced.) -/
theorem nv_no_owners_denies :
    Acl.evalPolicy (withTagBindings { demoPol with tagOwners := [] } [nodeOwned]) demoPkt
      = Acl.Verdict.drop := by decide

#eval tagBindings demoOwners [nodeOwned]
#eval tagBindings demoOwners [nodeUnowned]
#eval Acl.evalPolicy (withTagBindings demoPol [nodeOwned]) demoPkt
#eval Acl.evalPolicy (withTagBindings demoPol [nodeUnowned]) demoPkt

/-! ## §5  Axiom audit -/

#print axioms mem_tagBindings_iff
#print axioms tagBindings_owned
#print axioms tagBindings_ownerless_empty
#print axioms lookup_tagBindings_iff
#print axioms tag_admits_iff
#print axioms unowned_tag_denies
#print axioms no_owned_bearer_dropped
#print axioms withTagBindings_preserves
#print axioms bound_allow_iff_entry
#print axioms bound_default_deny
#print axioms nv_owned_binds
#print axioms nv_unowned_binds_nothing
#print axioms nv_ownership_flips_verdict
#print axioms nv_no_owners_denies

end Control.Tags
