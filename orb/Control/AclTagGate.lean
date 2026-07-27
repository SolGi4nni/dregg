import Control
import Control.Acl
import Control.Tags
import Control.Policy
import Control.PreAuthKey
import Control.Tailcfg
import Control.TailcfgWire

/-!
# The TAG GATE — enrolment → netmap → HuJSON policy → served filter, end to end

`Control/Acl.lean` makes `tag:x` a first-class ACL principal and restates default-deny
over it; `Control/Tags.lean` proves the registry projection and the ownership gate in
general; `Control/Policy.lean` parses `tagOwners` and `tag:` selectors from the operator's
HuJSON. This file is the **end-to-end instance** that all of it composes on real objects:

1. mint a reusable pre-auth key carrying `["tag:web"]`, owned by **user 7**;
2. register a node with it → the admitted node carries `Node.tags = ["tag:web"]` and
   `Node.user = 7` (`Control.PreAuth.preauth_admit`, proven for arbitrary keys);
3. IPAM gives it `100.64.0.9/32`; build a *different* node's netmap → the tagged node
   appears as a peer, tags intact, and survives the binary netmap wire and the tailcfg
   JSON wire a stock client parses;
4. the OPERATOR's HuJSON file (`Control.Policy.sampleHuJSON`) names `tag:web` in a `dst`
   and declares `tagOwners: {"tag:web": ["user:7"]}`;
5. `Control.Tags.withTagBindings` binds `tag:web` to the tagged peer's `/32` — and the
   compiled filter permits the LAN→tagged:443 packet;
6. change ONE THING — the owning user id — and the identical claim binds nothing, so the
   identical packet is default-DROPPED.

★These are **instances**, deliberately labelled as such. The `∀`-statements are
`Control.Tags.tagBindings_owned` / `tag_admits_iff` / `unowned_tag_denies` /
`no_owned_bearer_dropped` and `Control.Acl.policy_default_deny` restated over the tag
language. This file exists to show they are about the objects drorb actually serves.
-/

namespace Control.AclTagGate

open Control Control.PreAuth

/-! ## §1  Mint → register → the tag is stamped on the node -/

/-- A demonstration content hash (identity); the security is in `preauth_admit`,
proved for an arbitrary hash. Kept axiom-free for `#print axioms`. -/
def hash0 : List UInt8 → List UInt8 := id

def webTag : List UInt8 := "tag:web".toUTF8.toList
def secret : List UInt8 := "tskey-web-demo".toUTF8.toList

/-- The tailnet's ownership declaration, as `Control.Policy.sampleHuJSON` states it:
only **user 7** may apply `tag:web`. -/
def tailnetOwners : Acl.TagOwners := [("tag:web", [Acl.Owner.user 7])]

/-- A reusable pre-auth key minted with owner `user = 7` and ACL tag `tag:web`. -/
def webAttrs : KeyAttrs :=
  { reusable := true, ephemeral := false, expiry := 0, tags := [webTag], user := 7 }

/-- The same key, but owned by user 8 — who `tailnetOwners` does NOT authorize. -/
def imposterAttrs : KeyAttrs := { webAttrs with user := 8 }

def store0 : Store := [mint hash0 secret webAttrs]
def storeImposter : Store := [mint hash0 secret imposterAttrs]

def taggedKey : NodeKey := ⟨List.replicate 32 0xC1⟩
def taggedIP : List UInt8 := [100, 64, 0, 9]

def regReq : RegisterRequest :=
  { version := 1, nodeKey := taggedKey, oldNodeKey := ⟨[]⟩,
    machineKey := ⟨List.replicate 32 0xD2⟩, authKey := secret, expiry := 0,
    ephemeral := false, followup := false }

/-- Drive the register request through the pre-auth admission gate. -/
def admit : AdmitResult := registerWithPreAuth hash0 store0 ControlState.init 0 regReq
/-- The same, with the imposter-owned key. -/
def admitImposter : AdmitResult :=
  registerWithPreAuth hash0 storeImposter ControlState.init 0 regReq

/-- The admitted node, recovered from the produced coordination state. It already
carries `tags = [webTag]` and `user = 7` (both stamped from the key by
`registerWithPreAuth`). -/
def nodeOfAdmit (a : AdmitResult) : Node :=
  match lookupReg a.state'.nodes taggedKey with
  | some r => r.node
  | none   => nodeOf regReq false

/-- IPAM (a separate coordinator step, not part of registration) assigns the node its
`/32`. The tags and the owning user stamped at admission are untouched. -/
def withAddr (n : Node) : Node :=
  { n with addresses := [⟨taggedIP, 32⟩], allowedIPs := [⟨taggedIP, 32⟩] }

def taggedNode : Node := withAddr (nodeOfAdmit admit)
def imposterNode : Node := withAddr (nodeOfAdmit admitImposter)

/-- A second, tagless node that will poll and receive the netmap. -/
def selfKey : NodeKey := ⟨List.replicate 32 0x01⟩
def selfNode : Node :=
  { nodeOf { regReq with nodeKey := selfKey } true with
      addresses := [⟨[100, 64, 0, 1], 32⟩] }

def taggedReg : Registration := { nodeKey := taggedKey, node := taggedNode, status := .authorized }
def imposterReg : Registration :=
  { nodeKey := taggedKey, node := imposterNode, status := .authorized }
def selfReg   : Registration := { nodeKey := selfKey,   node := selfNode,   status := .authorized }

def coordSt : ControlState := { ControlState.init with nodes := [taggedReg, selfReg] }
def coordStImposter : ControlState :=
  { ControlState.init with nodes := [imposterReg, selfReg] }

/-- The netmap the tagless self node receives: its authorized peers. -/
def selfNetmap : NetMap := buildNetMap coordSt selfReg
def selfNetmapImposter : NetMap := buildNetMap coordStImposter selfReg

/-! ## §2  The OPERATOR's HuJSON policy, bound against the netmap peers

The policy is not invented here: it is `Control.Policy.sampleHuJSON` — the same bytes
`Control/testdata/policy_homelab.hujson` holds — whose third ACL entry is
`src 192.168.1.0/24 → dst tag:web:443` and whose `tagOwners` names `user:7`. -/

/-- The parsed operator policy (tag bindings still EMPTY —
`Control.Policy.parsePolicy_tags_empty`). -/
def filePolicy : Acl.Policy := Control.Policy.gp

/-- The SERVED policy: the operator's file, with `tag:` bound against the peers the
netmap actually carries. This is the composition `ControlLive.servedFrom` performs. -/
def servedPolicy : Acl.Policy := Control.Tags.withTagBindings filePolicy selfNetmap.peers
/-- The same, against the imposter-owned peer. -/
def servedPolicyImposter : Acl.Policy :=
  Control.Tags.withTagBindings filePolicy selfNetmapImposter.peers

def compiledFilter : List Acl.FilterRule := Acl.compile servedPolicy

/-- The `/32` CIDR of the tagged node — what `tag:web` must resolve to. -/
def taggedCidr : IpFilter.Cidr := Control.Tags.prefixToCidr ⟨taggedIP, 32⟩

/-- A LAN host reaching the tagged node on 443 — what the `tag:web` rule permits. -/
def demoPkt : Acl.Packet :=
  { srcIP := Control.Tags.addrOfBytes [192, 168, 1, 5]
  , dstIP := Control.Tags.addrOfBytes taggedIP, dstPort := 443, proto := 6 }

/-- The same source and destination on **22** — the tag rule opens only 443. -/
def demoPktSsh : Acl.Packet := { demoPkt with dstPort := 22 }

/-! ## §3  The GATE theorems (instances of the general statements) -/

/-- **(1) The key's tag AND owning user reached the peer's netmap.** The peer the self
node sees carries exactly the ACL tag and the user id copied from the pre-auth key —
this is `Control.PreAuth.preauth_admit` (proved for arbitrary keys) on real objects. -/
theorem gate_peer_has_tag_and_user :
    selfNetmap.peers.map (fun p => (p.tags, p.user)) = [([webTag], 7)] := by native_decide

/-- **(2) The imposter's netmap entry is INDISTINGUISHABLE except for the user id.**
Same node key, same address, same `Node.tags`, same authorized status — only `user`
differs. That is what makes gate (5) a clean ownership experiment. -/
theorem gate_imposter_differs_only_in_user :
    selfNetmapImposter.peers.map (fun p => (p.tags, p.user)) = [([webTag], 8)]
    ∧ selfNetmapImposter.peers.map (·.addresses) = selfNetmap.peers.map (·.addresses) := by
  native_decide

/-- **(3) The served policy resolves `tag:web` to the tagged peer's `/32`.** The binding
is the registry projection, not anything the file could have written. -/
theorem gate_tag_resolves_to_ip :
    servedPolicy.tags = [("tag:web", [taggedCidr])] := by native_decide

/-- **(3b) …and the compiled `FilterRule` for the tag entry carries that `/32` as a
destination.** The tag reached the actual `tailcfg.FilterRule` values. -/
theorem gate_tag_in_compiled_rule :
    ∃ r ∈ compiledFilter, ∃ npr ∈ r.dsts, npr.dst = taggedCidr := by native_decide

/-- **(4) ★A real allowed connection.** The LAN packet to the tagged node on 443 is
ALLOWED by the served policy. -/
theorem gate_tagged_pkt_allowed :
    Acl.evalPolicy servedPolicy demoPkt = Acl.Verdict.allow := by native_decide

/-- **(5) ★A real denied connection — and OWNERSHIP is the only difference.** The
imposter node claims the identical `tag:web`, at the identical address, authorized
identically; but user 8 is not a `tagOwner`, so `tag:web` binds nothing and the
identical packet is DROPPED. This is `Control.Tags.unowned_tag_denies` on real
objects. -/
theorem gate_imposter_pkt_dropped :
    servedPolicyImposter.tags = []
    ∧ Acl.evalPolicy servedPolicyImposter demoPkt = Acl.Verdict.drop := by native_decide

/-- **(6) The tag rule is still port-scoped.** Same source, same tagged destination,
port 22 → DROPPED. A tag widens *who*, never *what*. -/
theorem gate_tagged_wrong_port_dropped :
    Acl.evalPolicy servedPolicy demoPktSsh = Acl.Verdict.drop := by native_decide

/-- **(7) The FILE alone confers nothing.** Before the registry projection, the very
same operator policy drops the very same packet — the binding, not the file, is what
opened the port. -/
theorem gate_file_alone_denies :
    Acl.evalPolicy filePolicy demoPkt = Acl.Verdict.drop := by native_decide

/-- **(8) The tagged node survives the netmap binary wire.** `putNetMap`/`getNetMap`
round-trip the whole netmap — tags included — via the proven codec. -/
theorem gate_netmap_wire_roundtrip :
    getNetMap (putNetMap selfNetmap ++ []) = some (selfNetmap, []) :=
  getNetMap_put selfNetmap []

/-! ## §4  The tailcfg JSON wire (what a stock client parses) carries `Tags` -/

/-- A `tailcfg.Node` for the tagged node, with `Tags = ["tag:web"]`. -/
def wireNodeTagged : Tailcfg.Node :=
  { id := 9, name := "tagged.example.ts.net", user := 7,
    key := "nodekey:c1c1", addresses := ["100.64.0.9/32"],
    tags := some ["tag:web"] }

/-- **(9) The `Tags` JSON field round-trips** through the proven tailcfg codec. -/
theorem gate_tailcfg_tags_roundtrip :
    Tailcfg.Node.fromJson? (Tailcfg.Node.toJson wireNodeTagged) = some wireNodeTagged :=
  Tailcfg.Node.fromJson?_toJson wireNodeTagged

/-- **(9b) …and through the null-omitting (real) wire renderer.** -/
theorem gate_tailcfg_tags_skipnone_roundtrip :
    Tailcfg.Node.fromJson? (TailcfgWire.dropNulls (Tailcfg.Node.toJson wireNodeTagged))
      = some wireNodeTagged :=
  TailcfgWire.Node.fromJson?_dropNulls wireNodeTagged

/-! ## §5  Executable demonstration -/

-- the emitted `Tags` JSON key (omitempty: present iff non-empty)
#eval TailcfgWire.renderStr (TailcfgWire.Node.toJsonSkipNone wireNodeTagged)
#eval selfNetmap.peers.map (fun p => (p.tags.map Control.Tags.tagName, p.user))
#eval servedPolicy.tags                                     -- tag:web ↦ the /32
#eval servedPolicyImposter.tags                             -- []  (wrong owner)
#eval Acl.evalPolicy filePolicy demoPkt                     -- drop (file alone)
#eval Acl.evalPolicy servedPolicy demoPkt                   -- allow
#eval Acl.evalPolicy servedPolicyImposter demoPkt           -- drop
#eval Acl.evalPolicy servedPolicy demoPktSsh                -- drop (port-scoped)

/-! ## §6  Axiom audit

The `gate_*` instance theorems are `native_decide` (compiler-evaluated: `tagName` goes
through `String.fromUTF8?`, which the kernel cannot reduce) — they are WITNESSES. The
safety argument is the kernel-checked `∀`-theorems in `Control.Tags` and `Control.Acl`,
listed here too so the reader can see which axioms each rests on. -/

#print axioms gate_peer_has_tag_and_user
#print axioms gate_imposter_differs_only_in_user
#print axioms gate_tag_resolves_to_ip
#print axioms gate_tag_in_compiled_rule
#print axioms gate_tagged_pkt_allowed
#print axioms gate_imposter_pkt_dropped
#print axioms gate_tagged_wrong_port_dropped
#print axioms gate_file_alone_denies
#print axioms gate_netmap_wire_roundtrip
#print axioms gate_tailcfg_tags_roundtrip
#print axioms gate_tailcfg_tags_skipnone_roundtrip
-- the general statements this file instantiates:
#print axioms Control.Tags.tagBindings_owned
#print axioms Control.Tags.tag_admits_iff
#print axioms Control.Tags.unowned_tag_denies
#print axioms Control.Tags.no_owned_bearer_dropped
#print axioms Control.Acl.policy_default_deny
#print axioms Control.Policy.parsePolicy_tags_empty

end Control.AclTagGate
