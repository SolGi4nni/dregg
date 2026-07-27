import IpFilter
import IpFilterCorrect

/-!
# Control.Acl — a verified ACL / packet-filter for the mesh control plane

The control plane (a Tailscale-style coordination server) distributes, to every
node, a **packet filter** compiled from a central access-control policy. The node
consults that filter to decide, per inbound packet, `Allow` or `Drop`. This module
builds that pipeline and makes its two safety properties **proof obligations**:

  * **default-deny** — a packet matching *no* compiled allow rule is Dropped
    (`filter_default_deny`, `policy_default_deny`); and
  * **soundness** — the filter Allows a packet **iff** some compiled allow rule
    matches it (`filter_allow_iff_rule`, `policy_allow_iff_entry`): no packet slips
    through un-allowed, and no allowed packet is wrongly dropped.

The design mirrors the public Tailscale/headscale model (BSD): a policy of `accept`
rules (`src` selectors → `dst` CIDR:port ranges, resolved through named groups),
compiled to `tailcfg.FilterRule`s, evaluated by a `wgengine/filter`-style
default-drop matcher over dual-stack CIDR prefixes.

## Tags (`tag:server`) — a first-class principal, added 2026-07-25

Real tailnet ACLs are written against **tags**, not hosts: `tag:server`, `tag:ci`,
`tag:exit`. A tag is also how a node gets a stable identity *independent of the user
who enrolled it*. So `Selector` carries a `.tag` constructor of its own, and a
`Policy` carries two new fields:

  * `tagOwners : TagOwners` — who may APPLY each tag (kb/1337 `tagOwners`). drorb's
    owner principals are **numeric user ids** (`user:<N>`) or `*` — see the users-scope
    note below. An undeclared tag is owned by nobody (`tagOwnedBy_undeclared`).
  * `tags : List (String × List Cidr)` — the tag→address BINDING, which is a projection
    of the NODE REGISTRY (`Control.Tags.tagBindings`), never of the policy file.

Keeping `.tag` distinct from `.group` is a safety property, not tidiness: the two
namespaces resolve through different tables (`resolveSel_tag` / `resolveSel_group`),
so a HuJSON file cannot forge a tag→IP binding by declaring a *group* called
`tag:web` (`tt_tag_group_namespace_disjoint`), and `Control.Policy.parsePolicy` is
proved to leave `tags` empty (`parsePolicy_tags_empty`).

★The default-deny soundness theorems are **restated over the extended language and
re-proved** — `policy_default_deny` / `policy_allow_iff_entry` now quantify over the
tag table as well, and every tagged policy goes through them. Nothing is bypassed.

## Users — the scope decision (stated, not hidden)

drorb models a user as the bare `Nat` that `Control.Node.user` / `KeyAttrs.user`
already carry. There is **no user directory, no email identity, no OIDC, no admin
role** — inventing one for a single-operator homelab would be a model nobody runs.
What tags *need* is an owner concept, and the numeric id is a real one: it is stamped
on the node by the pre-auth key that admitted it and it is what `tagOwners` is checked
against. Consequently `tagOwners` values are `user:<N>` or `*`; a `group:`/
`autogroup:`/email owner token is REJECTED at parse (loudly), never silently mapped.

## The FilterRule type shape (for reconciliation with the control core)

`FilterRule` here is the shape of `tailcfg.FilterRule` (public tailscale):

  `FilterRule = { srcs : List Cidr            -- tailcfg SrcIPs (CIDR set)`
  `             , dsts : List NetPortRange    -- tailcfg DstPorts`
  `             , protos : List Nat }         -- tailcfg IPProto ([] ⇒ any)`
  `NetPortRange = { dst : Cidr, ports : PortRange }`   -- tailcfg NetPortRange {IP, Ports}
  `PortRange    = { first last : Nat }`                -- inclusive [first, last]

This is the SAME tailcfg shape that a `Control.NetMap.packetFilter` (the sibling
control-plane foundation lane) carries. When the two lanes integrate there must be
**one canonical `FilterRule`**; this file's definition is written to that shape so
the reconciliation is a name-merge, not a re-model.

## Dual-stack CIDR matching (reused, not re-proved)

Address/CIDR/prefix matching is `IpFilter` (`Addr`, `Cidr`, `matchCidr`): an address
is in a CIDR iff same family and the top `len` bits agree (RFC 4632, generalized to
v6). Its correctness against an *independent* indexed spec is `IpFilterCorrect`
(`matchCidr_iff_spec`, `SpecMatch`). We lift that here: `srcMatch_iff_spec` /
`dstMatch_iff_spec` say the filter's per-field CIDR test agrees with the RFC spec —
so the family tag keeps v4 and v6 disjoint for free (a v6 packet never matches a
v4 rule; grounded in `tt_v6_dropped`).

## Residual (named, not hidden)

The textual HuJSON policy *parse* (headscale's `policy` package: dotted-quad / `::`
compression, `group:`/`tag:`/host resolution from JSON text) is not modeled; the
policy enters as an already-tokenized `Policy` (selectors + a group→CIDR table).
Group *resolution* (the compile step that expands selectors to CIDRs) **is** modeled
and proved (`ruleMatches_compileEntry`). Textual parse is the residual boundary,
exactly as `IpFilter`'s address-text parse is; the filter — the object the safety
proof is about — is closed end-to-end.
-/

namespace Control.Acl

open IpFilter
open IpFilterCorrect

/-! ## tailcfg-shaped filter types -/

/-- An inclusive port range `[first, last]` (public `tailcfg.PortRange`). -/
structure PortRange where
  first : Nat
  last : Nat
deriving DecidableEq, Repr

/-- Is port `p` inside the range? -/
def PortRange.contains (r : PortRange) (p : Nat) : Bool :=
  decide (r.first ≤ p ∧ p ≤ r.last)

/-- A destination CIDR paired with an allowed port range (public
`tailcfg.NetPortRange` = `{IP, Ports}`, with `IP` a CIDR). -/
structure NetPortRange where
  dst : Cidr
  ports : PortRange
deriving Repr

/-- A compiled allow rule (public `tailcfg.FilterRule`). `protos = []` means "any
protocol" (tailscale's empty `IPProto`). Allow-only: there is no deny action in the
packet filter — denial is by *absence* of a matching allow, which is what makes the
default-deny obligation meaningful. -/
structure FilterRule where
  srcs : List Cidr
  dsts : List NetPortRange
  protos : List Nat
deriving Repr

/-- A packet presented to the filter: source/destination address, destination port,
and IP protocol number. -/
structure Packet where
  srcIP : Addr
  dstIP : Addr
  dstPort : Nat
  proto : Nat
deriving Repr

/-- The filter verdict. -/
inductive Verdict where
  | allow
  | drop
deriving DecidableEq, Repr

/-! ## The packet-filter evaluator (wgengine/filter-style, default-drop) -/

/-- Does the packet's source address fall in one of the rule's source CIDRs? -/
def srcMatch (r : FilterRule) (pkt : Packet) : Bool :=
  r.srcs.any (fun c => matchCidr c pkt.srcIP)

/-- Does the packet's destination address+port match this `NetPortRange`? -/
def dstMatch (npr : NetPortRange) (pkt : Packet) : Bool :=
  matchCidr npr.dst pkt.dstIP && npr.ports.contains pkt.dstPort

/-- Does the packet match one of the rule's destination CIDR:port ranges? -/
def anyDstMatch (r : FilterRule) (pkt : Packet) : Bool :=
  r.dsts.any (fun npr => dstMatch npr pkt)

/-- Does the packet's protocol satisfy the rule? Empty `protos` = any protocol. -/
def protoMatch (r : FilterRule) (pkt : Packet) : Bool :=
  r.protos.isEmpty || r.protos.contains pkt.proto

/-- **A single rule matches a packet** iff its source, protocol, and some
destination:port clause all match. -/
def ruleMatches (r : FilterRule) (pkt : Packet) : Bool :=
  srcMatch r pkt && protoMatch r pkt && anyDstMatch r pkt

/-- **The packet filter** (default-drop): `Allow` iff some allow rule matches;
otherwise `Drop`. This is the fail-closed core — there is no fall-through to admit. -/
def evalFilter (rules : List FilterRule) (pkt : Packet) : Verdict :=
  if rules.any (fun r => ruleMatches r pkt) then Verdict.allow else Verdict.drop

/-! ## Policy → FilterRule compilation (headscale-style)

A policy is a list of `accept` ACL entries over `Selector`s (a named group or a
literal CIDR), plus a group→CIDR table. Compilation resolves every selector to
CIDRs and emits one `FilterRule` per entry. Only `accept` exists (headscale's ACL
action), so default-deny is structural. -/

/-- A source/destination selector: a literal CIDR, a named group (`group:eng`, a
host alias — resolved through the policy's group table), or a **node tag**
(`tag:server` — resolved through the policy's *tag-binding* table, which is a
projection of the NODE REGISTRY, never of the policy file; see `Control.Tags`).

Tags are a SEPARATE constructor from groups on purpose: the two tables have
different provenance and different trust. `groups` is authored in the operator's
HuJSON file; `tags` is derived from which nodes actually bear an *owned* tag. A
policy file therefore cannot fabricate a tag→address binding — it can only *name*
a tag (`Control.Policy.parsePolicy_tags_empty`). -/
inductive Selector where
  | cidr (c : Cidr)
  | group (name : String)
  | tag (name : String)
deriving DecidableEq, Repr

/-! ### Tag ownership (`tagOwners`)

Public Tailscale ACL syntax (kb/1337): `"tagOwners": { "tag:web": [owner…] }`
names who may APPLY a tag. A tag is a node identity independent of the user who
enrolled the node, so the ability to hand one out is itself a privilege.

**drorb's owner principals are numeric user ids.** `Control.Node.user` and
`Control.PreAuth.KeyAttrs.user` are `Nat`s; drorb has no user directory, no email
identity and no OIDC (see the users-scope note in the module header). So an owner
is `user:<N>` or `*`, and nothing else — a `group:`/`autogroup:`/email owner token
is *rejected at parse* (`Control.Policy.parseTagOwners`), loudly, rather than
silently resolving to "nobody" or, worse, "anybody". -/

/-- A principal permitted to apply a tag. -/
inductive Owner where
  /-- A specific numeric user id (`user:7`). -/
  | user (id : Nat)
  /-- `*` — any user of this tailnet may apply the tag. -/
  | anyUser
deriving DecidableEq, Repr

/-- The `tagOwners` table: tag name → the principals permitted to apply it. -/
abbrev TagOwners := List (String × List Owner)

/-- Does this owner principal cover user id `u`? -/
def ownerAdmits : Owner → Nat → Bool
  | .user i, u => i == u
  | .anyUser, _ => true

/-- **May user `u` apply tag `t`?** An UNDECLARED tag is owned by nobody: the
`.any` over an empty filter is `false`, so a tag absent from `tagOwners` can never
be applied. This is the fail-closed direction (`tagOwnedBy_undeclared`). -/
def tagOwnedBy (ow : TagOwners) (t : String) (u : Nat) : Bool :=
  (ow.filter (fun e => decide (e.1 = t))).any (fun e => e.2.any (fun o => ownerAdmits o u))

/-- A raw (pre-compilation) `accept` ACL entry: source selectors, destination
selectors each with a port range, and an optional protocol set. -/
structure RawEntry where
  src : List Selector
  dst : List (Selector × PortRange)
  protos : List Nat
deriving Repr

/-- A policy: a group alias table (`group:name → CIDRs`), the list of `accept` ACL
entries, the `tagOwners` declaration, and the tag→CIDR **binding** table. Default-deny
is implicit (no rule ⇒ drop).

`tagOwners` and `tags` default to empty so every pre-tag `{ groups := …, acls := … }`
literal still elaborates — and so the *fail-closed* policy is the one you get by
forgetting a field: no owners ⇒ no tag may be applied; no bindings ⇒ every `tag:`
selector resolves to the empty CIDR set ⇒ default-deny. -/
structure Policy where
  groups : List (String × List Cidr)
  acls : List RawEntry
  /-- Who may apply each tag (parsed from the HuJSON `tagOwners` section). Also the
  set of DECLARED tags: `Control.Acl.selDeclared` rejects a `.tag` selector naming
  a tag absent here, so a typo'd `tag:` is a parse ERROR, not a silent deny. -/
  tagOwners : TagOwners := []
  /-- The tag→CIDR binding table: `tag:x ↦ the addresses of registry nodes that bear
  `x` and whose owner is permitted to. Populated ONLY by `Control.Tags.withTagBindings`
  (a registry projection); `Control.Policy.parsePolicy` always leaves it empty. -/
  tags : List (String × List Cidr) := []
deriving Repr

/-- Look up all CIDRs bound to a name in an alias table (`groups` or `tags`). -/
def lookupGroup (groups : List (String × List Cidr)) (name : String) : List Cidr :=
  (groups.filter (fun g => decide (g.1 = name))).flatMap (fun g => g.2)

/-- Resolve a selector to the concrete CIDRs it denotes. Groups resolve through the
file-authored `groups` table; tags through the registry-derived `tags` table. -/
def resolveSel (groups tags : List (String × List Cidr)) (s : Selector) : List Cidr :=
  match s with
  | .cidr c => [c]
  | .group n => lookupGroup groups n
  | .tag t => lookupGroup tags t

/-- Compile the source selectors of an entry to a flat CIDR set. -/
def compileSrcs (groups tags : List (String × List Cidr)) (src : List Selector) : List Cidr :=
  src.flatMap (resolveSel groups tags)

/-- Compile the destination selectors (each carrying a port range) to
`NetPortRange`s. -/
def compileDsts (groups tags : List (String × List Cidr))
    (dst : List (Selector × PortRange)) : List NetPortRange :=
  dst.flatMap (fun sp => (resolveSel groups tags sp.1).map (fun c => { dst := c, ports := sp.2 }))

/-- Compile one ACL entry to a `tailcfg.FilterRule`. -/
def compileEntry (groups tags : List (String × List Cidr)) (e : RawEntry) : FilterRule :=
  { srcs := compileSrcs groups tags e.src
  , dsts := compileDsts groups tags e.dst
  , protos := e.protos }

/-- **Compile the whole policy** to the node's packet filter. -/
def compile (p : Policy) : List FilterRule :=
  p.acls.map (compileEntry p.groups p.tags)

/-- **Evaluate a packet against a policy**: compile, then run the default-drop
filter. This is the full policy → filter-rules → verdict pipeline. -/
def evalPolicy (p : Policy) (pkt : Packet) : Verdict :=
  evalFilter (compile p) pkt

/-! ### Spec-level "an entry admits a packet"

The independent characterization of when an ACL entry should admit a packet:
some source selector resolves to a CIDR containing the source, the protocol is
allowed, and some destination selector resolves to a CIDR containing the
destination with the port in range. Written over `resolveSel`, not over the
compiled rule. -/

/-- Some CIDR that source selector `s` resolves to contains `a`. -/
def selAdmitsSrc (groups tags : List (String × List Cidr)) (s : Selector) (a : Addr) : Bool :=
  (resolveSel groups tags s).any (fun c => matchCidr c a)

/-- Some source selector of the entry admits the address. -/
def entrySrcAdmits (groups tags : List (String × List Cidr)) (e : RawEntry) (a : Addr) : Bool :=
  e.src.any (fun s => selAdmitsSrc groups tags s a)

/-- Some CIDR that dst selector `sp.1` resolves to contains `dstIP`, with the port
in `sp.2`. -/
def selAdmitsDst (groups tags : List (String × List Cidr)) (sp : Selector × PortRange)
    (pkt : Packet) : Bool :=
  (resolveSel groups tags sp.1).any (fun c => matchCidr c pkt.dstIP && sp.2.contains pkt.dstPort)

/-- Some dst selector of the entry admits the packet's destination:port. -/
def entryDstAdmits (groups tags : List (String × List Cidr)) (e : RawEntry) (pkt : Packet) : Bool :=
  e.dst.any (fun sp => selAdmitsDst groups tags sp pkt)

/-- The entry's protocol constraint. -/
def entryProtoAdmits (e : RawEntry) (pkt : Packet) : Bool :=
  e.protos.isEmpty || e.protos.contains pkt.proto

/-- **The independent verdict for one ACL entry**: source admitted, protocol ok,
destination:port admitted — all phrased over selector resolution, never over the
compiled `FilterRule`. -/
def entryAdmits (groups tags : List (String × List Cidr)) (e : RawEntry) (pkt : Packet) : Bool :=
  entrySrcAdmits groups tags e pkt.srcIP && entryProtoAdmits e pkt
    && entryDstAdmits groups tags e pkt

/-! ## List helper lemmas (no implementation content) -/

/-- `any` distributes over `flatMap`. -/
theorem any_flatMap {α β} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).any p = l.any (fun x => (f x).any p) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, List.any_append, List.any_cons, ih]

/-- `any` over a `map` pushes the map into the predicate. -/
theorem any_map {α β} (l : List α) (f : α → β) (p : β → Bool) :
    (l.map f).any p = l.any (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.map_cons, List.any_cons, ih]

/-! ## The proofs — default-deny, soundness, compile-correctness, spec bridges -/

/-- **DEFAULT-DENY (filter level).** A packet that matches no compiled allow rule is
Dropped. The fail-closed core: absence of an allow ⇒ drop. -/
theorem filter_default_deny (rules : List FilterRule) (pkt : Packet)
    (h : ∀ r ∈ rules, ruleMatches r pkt = false) :
    evalFilter rules pkt = Verdict.drop := by
  have hn : rules.any (fun r => ruleMatches r pkt) = false := by
    cases hb : rules.any (fun r => ruleMatches r pkt) with
    | false => rfl
    | true =>
      rw [List.any_eq_true] at hb
      obtain ⟨r, hr, hm⟩ := hb
      rw [h r hr] at hm
      exact absurd hm (by decide)
  simp [evalFilter, hn]

/-- **SOUNDNESS (filter level).** The filter Allows a packet **iff** some compiled
allow rule matches it. No un-allowed packet is admitted; no matching packet is
dropped. -/
theorem filter_allow_iff_rule (rules : List FilterRule) (pkt : Packet) :
    evalFilter rules pkt = Verdict.allow ↔ ∃ r ∈ rules, ruleMatches r pkt = true := by
  unfold evalFilter
  rw [← List.any_eq_true]
  cases hb : rules.any (fun r => ruleMatches r pkt) <;> simp [hb]

/-- **CIDR match correctness (source), lifted from `IpFilter`.** The source test
agrees with the independent RFC prefix-match spec: the source matches iff some rule
CIDR *specifies* containment of the source address. Family separation (v4 vs v6) is
carried by `SpecMatch`'s family clause. -/
theorem srcMatch_iff_spec (r : FilterRule) (pkt : Packet) :
    srcMatch r pkt = true ↔ ∃ c ∈ r.srcs, SpecMatch c pkt.srcIP := by
  unfold srcMatch
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hm⟩; exact ⟨c, hc, (matchCidr_iff_spec c pkt.srcIP).mp hm⟩
  · rintro ⟨c, hc, hm⟩; exact ⟨c, hc, (matchCidr_iff_spec c pkt.srcIP).mpr hm⟩

/-- **CIDR match correctness (destination), lifted from `IpFilter`.** A destination
clause matches iff its CIDR *specifies* containment of the destination address and
the port is in range. -/
theorem dstMatch_iff_spec (npr : NetPortRange) (pkt : Packet) :
    dstMatch npr pkt = true ↔ SpecMatch npr.dst pkt.dstIP ∧ npr.ports.contains pkt.dstPort = true := by
  unfold dstMatch
  rw [Bool.and_eq_true, matchCidr_iff_spec]

/-- **Compile-correctness.** Matching the *compiled* rule for an entry equals the
independent per-entry admission spec — group resolution (selector → CIDR expansion)
preserves the matching relation exactly. -/
theorem ruleMatches_compileEntry (groups tags : List (String × List Cidr))
    (e : RawEntry) (pkt : Packet) :
    ruleMatches (compileEntry groups tags e) pkt = entryAdmits groups tags e pkt := by
  simp only [ruleMatches, entryAdmits, compileEntry, srcMatch, anyDstMatch, protoMatch,
    compileSrcs, compileDsts, entrySrcAdmits, entryProtoAdmits, entryDstAdmits,
    selAdmitsSrc, selAdmitsDst, dstMatch, any_flatMap, any_map]

/-- **DEFAULT-DENY (policy level).** A packet admitted by no ACL entry is Dropped by
the compiled policy filter. ★RESTATED over the tag-extended language: the entry
admission spec now resolves `.tag` selectors through `p.tags` as well as `.group`
selectors through `p.groups`, and the theorem is proved over that — not bypassed for
tagged policies. -/
theorem policy_default_deny (p : Policy) (pkt : Packet)
    (h : ∀ e ∈ p.acls, entryAdmits p.groups p.tags e pkt = false) :
    evalPolicy p pkt = Verdict.drop := by
  unfold evalPolicy
  apply filter_default_deny
  intro r hr
  unfold compile at hr
  rw [List.mem_map] at hr
  obtain ⟨e, he, rfl⟩ := hr
  rw [ruleMatches_compileEntry]
  exact h e he

/-- **SOUNDNESS (policy level) — the end-to-end obligation.** The compiled policy
Allows a packet **iff** some ACL entry admits it (with group AND tag resolution).
This chains compile-correctness with the filter soundness: nothing the policy forbids
is admitted, and everything it permits is admitted. ★RESTATED over the tag-extended
language. -/
theorem policy_allow_iff_entry (p : Policy) (pkt : Packet) :
    evalPolicy p pkt = Verdict.allow ↔ ∃ e ∈ p.acls, entryAdmits p.groups p.tags e pkt = true := by
  unfold evalPolicy
  rw [filter_allow_iff_rule]
  unfold compile
  constructor
  · rintro ⟨r, hr, hm⟩
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    exact ⟨e, he, by rw [← ruleMatches_compileEntry]; exact hm⟩
  · rintro ⟨e, he, hm⟩
    exact ⟨compileEntry p.groups p.tags e, List.mem_map.mpr ⟨e, he, rfl⟩, by
      rw [ruleMatches_compileEntry]; exact hm⟩

/-! ## Tag semantics — general lemmas about the new principal

These are `∀`-statements over arbitrary tables and addresses, not an enumeration of
call sites. `Control.Tags` builds on them to connect a tag to the NODES that bear it. -/

/-- A `.tag` selector resolves through the tag-binding table, and NOTHING else — in
particular the file-authored `groups` table cannot contribute to it. -/
theorem resolveSel_tag (groups tags : List (String × List Cidr)) (t : String) :
    resolveSel groups tags (.tag t) = lookupGroup tags t := rfl

/-- A `.group` selector resolves through the group table, and NOTHING else — the
registry-derived `tags` table cannot contribute to it. The two namespaces are
disjoint by construction, so a node bearing `tag:x` can never satisfy `group:x`. -/
theorem resolveSel_group (groups tags : List (String × List Cidr)) (n : String) :
    resolveSel groups tags (.group n) = lookupGroup groups n := rfl

/-- **A tag admits a source iff some CIDR bound to it contains the address.** -/
theorem tag_admitsSrc_iff (groups tags : List (String × List Cidr)) (t : String) (a : Addr) :
    selAdmitsSrc groups tags (.tag t) a = true ↔ ∃ c ∈ lookupGroup tags t, matchCidr c a = true := by
  simp [selAdmitsSrc, resolveSel_tag, List.any_eq_true]

/-- **An UNBOUND tag admits nothing.** If a tag has no binding, every `.tag` test on
it is `false` — so a policy naming a tag no node legitimately bears cannot admit any
packet through that selector. Fail-closed, generally. -/
theorem unbound_tag_admits_nothing (groups tags : List (String × List Cidr))
    (t : String) (a : Addr) (h : lookupGroup tags t = []) :
    selAdmitsSrc groups tags (.tag t) a = false := by
  simp [selAdmitsSrc, resolveSel_tag, h]

/-- **A policy whose every entry is sourced at an unbound tag drops everything.**
The composition of `unbound_tag_admits_nothing` with `policy_default_deny`: general
over the policy, the tables, and the packet. -/
theorem unbound_tag_policy_denies (p : Policy) (t : String) (pkt : Packet)
    (hsrc : ∀ e ∈ p.acls, e.src = [Selector.tag t])
    (hub : lookupGroup p.tags t = []) :
    evalPolicy p pkt = Verdict.drop := by
  apply policy_default_deny
  intro e he
  have : entrySrcAdmits p.groups p.tags e pkt.srcIP = false := by
    simp [entrySrcAdmits, hsrc e he, unbound_tag_admits_nothing _ _ t pkt.srcIP hub]
  simp [entryAdmits, this]

/-- **An undeclared tag is owned by NOBODY.** A tag absent from `tagOwners` cannot be
applied by any user — the fail-closed direction of ownership, general over the table
and the user. -/
theorem tagOwnedBy_undeclared (ow : TagOwners) (t : String) (u : Nat)
    (h : ∀ e ∈ ow, e.1 ≠ t) : tagOwnedBy ow t u = false := by
  have : ow.filter (fun e => decide (e.1 = t)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [h e he]
  simp [tagOwnedBy, this]

/-- **Ownership is exactly membership.** `tagOwnedBy` holds iff some declaration of
that tag lists an owner principal covering the user. -/
theorem tagOwnedBy_iff (ow : TagOwners) (t : String) (u : Nat) :
    tagOwnedBy ow t u = true
      ↔ ∃ e ∈ ow, e.1 = t ∧ ∃ o ∈ e.2, ownerAdmits o u = true := by
  simp only [tagOwnedBy, List.any_eq_true, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, ht⟩, ho⟩
    exact ⟨e, he, ht, ho⟩
  · rintro ⟨e, he, ht, ho⟩
    exact ⟨e, ⟨he, ht⟩, ho⟩

/-! ## Non-vacuity — a grounded truth table on real inputs

A concrete headscale-style policy: group `group:eng` = `10.0.0.0/8`; one `accept`
entry `src group:eng → dst 10.0.0.0/8 : port 22`, any protocol. We prove the four
corners of the safety table on real packets, plus that the default-deny and the port
check are *load-bearing* (a wrong evaluator disagrees). -/

/-- `10.0.0.0/8`: family v4, 8-bit network prefix `00001010` = decimal 10. -/
def cidr10_8 : Cidr := ⟨.v4, [false, false, false, false, true, false, true, false], 8⟩

/-- A v4 source in `10.0.0.0/8` (top byte `10`). -/
def srcIn : Addr := ⟨.v4, [false, false, false, false, true, false, true, false]⟩

/-- A v4 source NOT in `10.0.0.0/8` (top byte `11000000` = 192). -/
def srcOut : Addr := ⟨.v4, [true, true, false, false, false, false, false, false]⟩

/-- A v4 destination in `10.0.0.0/8`. -/
def dstIn : Addr := ⟨.v4, [false, false, false, false, true, false, true, false]⟩

/-- A v6 source whose bits happen to match `10`'s prefix — must STILL be dropped by
the v4-only policy (family separation). -/
def srcV6 : Addr := ⟨.v6, [false, false, false, false, true, false, true, false]⟩

/-- The demo policy: `group:eng = 10.0.0.0/8`; `accept src group:eng dst 10.0.0.0/8:22`. -/
def demoPolicy : Policy :=
  { groups := [("group:eng", [cidr10_8])]
  , acls :=
    [ { src := [Selector.group "group:eng"]
      , dst := [(Selector.cidr cidr10_8, ⟨22, 22⟩)]
      , protos := [] } ] }

/-- In-policy packet: `10.x → 10.x : 22`. -/
def pktInPolicy : Packet := ⟨srcIn, dstIn, 22, 6⟩
/-- Out-of-policy source: `192.x → 10.x : 22`. -/
def pktOutSrc : Packet := ⟨srcOut, dstIn, 22, 6⟩
/-- Wrong port: `10.x → 10.x : 80` (policy only opens 22). -/
def pktWrongPort : Packet := ⟨srcIn, dstIn, 80, 6⟩
/-- v6 source against the v4-only policy. -/
def pktV6 : Packet := ⟨srcV6, dstIn, 22, 6⟩

/-- **Corner 1 — in-policy src→dst:port is Allowed.** -/
theorem tt_in_policy_allowed : evalPolicy demoPolicy pktInPolicy = Verdict.allow := by decide

/-- **Corner 2 — out-of-policy source is Dropped** (default-deny fires). -/
theorem tt_out_of_policy_src_dropped : evalPolicy demoPolicy pktOutSrc = Verdict.drop := by decide

/-- **Corner 3 — right src/dst but wrong port is Dropped.** -/
theorem tt_wrong_port_dropped : evalPolicy demoPolicy pktWrongPort = Verdict.drop := by decide

/-- **Corner 4 — a v6 packet is Dropped by the v4-only policy** (dual-stack
separation: the v6 source never matches a v4 CIDR). -/
theorem tt_v6_dropped : evalPolicy demoPolicy pktV6 = Verdict.drop := by decide

/-- A deliberately-broken *default-allow* filter (fall-through admits) — exhibited
only to witness that default-deny is a real constraint. -/
def evalFilterOpen (rules : List FilterRule) (pkt : Packet) : Verdict :=
  if rules.any (fun r => ruleMatches r pkt) then Verdict.allow else Verdict.allow

/-- **Default-deny is not vacuous.** On the out-of-policy packet the real filter
Drops where the default-allow variant would Admit — so an implementation that failed
closed-by-default would violate `tt_out_of_policy_src_dropped`. -/
theorem default_deny_not_vacuous :
    evalFilter (compile demoPolicy) pktOutSrc = Verdict.drop
    ∧ evalFilterOpen (compile demoPolicy) pktOutSrc = Verdict.allow := by decide

/-- A deliberately-broken matcher that ignores the port — exhibited only to witness
that the port check is load-bearing. -/
def ruleMatchesNoPort (r : FilterRule) (pkt : Packet) : Bool :=
  srcMatch r pkt && protoMatch r pkt && r.dsts.any (fun npr => matchCidr npr.dst pkt.dstIP)

/-- **The port check is not vacuous.** On the wrong-port packet the port-blind matcher
admits where the real rule rejects — so dropping the port comparison would violate
`tt_wrong_port_dropped`. -/
theorem port_check_not_vacuous :
    (compile demoPolicy).any (fun r => ruleMatchesNoPort r pktWrongPort) = true
    ∧ (compile demoPolicy).any (fun r => ruleMatches r pktWrongPort) = false := by decide

/-! ### The tag principal is load-bearing, on real inputs

The same `10.0.0.0/8` shape, but sourced at `tag:server` instead of `group:eng`.
Three corners: the tag BOUND admits; the tag UNBOUND denies the identical packet;
and the tag namespace is DISJOINT from the group namespace (binding the *group*
table under the name `tag:server` does NOT satisfy a `.tag` selector). -/

/-- `accept src=tag:server dst=10.0.0.0/8:22` — a policy whose source is a tag. -/
def tagDemoAcls : List RawEntry :=
  [ { src := [Selector.tag "tag:server"]
    , dst := [(Selector.cidr cidr10_8, ⟨22, 22⟩)]
    , protos := [] } ]

/-- `tag:server` bound to `10.0.0.0/8` (what a registry projection would produce for
a tagged node sitting in that range). -/
def tagBoundPolicy : Policy :=
  { groups := [], acls := tagDemoAcls
  , tagOwners := [("tag:server", [Owner.user 7])]
  , tags := [("tag:server", [cidr10_8])] }

/-- The SAME policy with no tag binding — the tag names nobody. -/
def tagUnboundPolicy : Policy := { tagBoundPolicy with tags := [] }

/-- The same policy with the binding put in the FILE-authored `groups` table instead
of the registry-derived `tags` table. -/
def tagMisplacedPolicy : Policy :=
  { tagBoundPolicy with groups := [("tag:server", [cidr10_8])], tags := [] }

/-- **Tag corner 1 — a bound tag admits.** -/
theorem tt_tag_bound_allowed : evalPolicy tagBoundPolicy pktInPolicy = Verdict.allow := by decide

/-- **Tag corner 2 — the SAME packet is Dropped when the tag is unbound.** The tag
binding is the only thing that changed, so it is load-bearing. -/
theorem tt_tag_unbound_dropped : evalPolicy tagUnboundPolicy pktInPolicy = Verdict.drop := by decide

/-- **Tag corner 3 — the namespaces are DISJOINT.** Binding `tag:server` in the
file-authored `groups` table does NOT satisfy a `.tag` selector: a policy file cannot
forge a tag binding by naming a group `tag:…`. -/
theorem tt_tag_group_namespace_disjoint :
    evalPolicy tagMisplacedPolicy pktInPolicy = Verdict.drop := by decide

/-- **Ownership is decidable and fail-closed on real inputs**: user 7 owns
`tag:server`, user 8 does not, and the undeclared `tag:ci` is owned by nobody. -/
theorem tt_tag_ownership :
    tagOwnedBy tagBoundPolicy.tagOwners "tag:server" 7 = true
    ∧ tagOwnedBy tagBoundPolicy.tagOwners "tag:server" 8 = false
    ∧ tagOwnedBy tagBoundPolicy.tagOwners "tag:ci" 7 = false := by decide

/-! ## Axiom audit — the ACL pipeline closes on the standard axioms only -/

#print axioms filter_default_deny
#print axioms filter_allow_iff_rule
#print axioms srcMatch_iff_spec
#print axioms dstMatch_iff_spec
#print axioms ruleMatches_compileEntry
#print axioms policy_default_deny
#print axioms policy_allow_iff_entry
#print axioms tt_in_policy_allowed
#print axioms tt_out_of_policy_src_dropped
#print axioms tt_wrong_port_dropped
#print axioms tt_v6_dropped
#print axioms default_deny_not_vacuous
#print axioms port_check_not_vacuous
#print axioms resolveSel_tag
#print axioms resolveSel_group
#print axioms tag_admitsSrc_iff
#print axioms unbound_tag_admits_nothing
#print axioms unbound_tag_policy_denies
#print axioms tagOwnedBy_undeclared
#print axioms tagOwnedBy_iff
#print axioms tt_tag_bound_allowed
#print axioms tt_tag_unbound_dropped
#print axioms tt_tag_group_namespace_disjoint
#print axioms tt_tag_ownership

end Control.Acl
