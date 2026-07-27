import Control

/-!
# Control.Dns — MagicDNS server-side record generation

The coordination server does not just *resolve* MagicDNS names; it first
*builds* the `DnsConfig` it distributes in each node's netmap. This module models
that fan-out: given the search domains and the authorized peer set, the server
emits one MagicDNS record per peer that has both a name and an overlay address,
mapping `name ↦ first overlay address`.

This is the producer side of the MagicDNS seam `Control` fixes: `Control` gives
`DnsConfig.resolve` and its soundness (`dns_resolve_sound`); here we give
`buildDns`, the function whose output that resolver runs over. The headline
property composes the two: a name that resolves in a built config resolves to a
genuine peer's record — the server never synthesizes a name→address mapping that
no authorized peer justifies.

Faithful to headscale's MagicDNS: each node's fully-qualified name answers to
that node's overlay (Tailscale) address, and the record set the server hands out
is exactly the current authorized peers, nothing else.
-/

namespace Control.Dns

open Control

/-- The MagicDNS record a single node contributes, if any.

A node earns a record only when it has *both* a MagicDNS `name` (non-empty
FQDN bytes) *and* at least one assigned overlay address. When both hold, the
record is `name ↦ (first address's bytes)` — the node's primary overlay
address, matching how MagicDNS answers a node's name with its Tailscale IP. A
node missing either half contributes nothing (`none`), so nameless or
address-less nodes never appear in the distributed DNS. -/
def nodeRecord (n : Node) : Option (Bytes × Bytes) :=
  match n.name, n.addresses with
  | [], _ => none
  | _, [] => none
  | name@(_ :: _), a :: _ => some (name, a.addr)

/-- Build the `DnsConfig` the coordination server distributes in the netmap: the
given search `domains`, and one MagicDNS record per peer that has a name and an
address (`filterMap nodeRecord` over the authorized peer set). This is what the
server places in `ControlState.dns` / `NetMap.dns`. -/
def buildDns (domains : List Bytes) (peers : List Node) : DnsConfig :=
  { domains := domains, records := peers.filterMap nodeRecord }

/-- **Records are peer-derived.** Every record in a built config comes from some
peer in the input set via `nodeRecord` — the server synthesizes no name→address
mapping of its own. -/
theorem dns_record_from_peer (domains : List Bytes) (peers : List Node)
    (name addr : Bytes) (h : (name, addr) ∈ (buildDns domains peers).records) :
    ∃ p ∈ peers, nodeRecord p = some (name, addr) := by
  simp only [buildDns] at h
  rw [List.mem_filterMap] at h
  obtain ⟨p, hp, hrec⟩ := h
  exact ⟨p, hp, hrec⟩

/-- **MagicDNS resolution is peer-sound (headline).** If a name resolves to an
address in a config the server built, that mapping is justified by an actual
peer: some peer in the set has `nodeRecord p = some (name, addr)`. Composes this
module's `dns_record_from_peer` with the foundation's `dns_resolve_sound`, so a
resolved answer is never a fabricated name→address pair. -/
theorem dns_resolve_to_peer (domains : List Bytes) (peers : List Node)
    (name addr : Bytes) (h : (buildDns domains peers).resolve name = some addr) :
    ∃ p ∈ peers, nodeRecord p = some (name, addr) :=
  dns_record_from_peer domains peers name addr
    (dns_resolve_sound (buildDns domains peers) name addr h)

/-- **Search domains pass through untouched.** The built config's domains are
exactly the ones handed in — the fan-out touches only the record set. -/
theorem dns_domains_preserved (domains : List Bytes) (peers : List Node) :
    (buildDns domains peers).domains = domains := rfl

/-- **No peers ⇒ no records.** With an empty authorized set the server emits the
domains and an empty record set. -/
theorem dns_empty_peers (domains : List Bytes) :
    buildDns domains [] = { domains := domains, records := [] } := rfl

/-! ## MagicDNS name derivation — hostname + base domain, collision-handled

The `tailcfg.Node.Name` a node answers to is its DNS-normalized hostname joined to
the tailnet base domain (headscale `GetFQDN` = `GivenName ++ "." ++ baseDomain`,
`hscontrol/types/node.go`; tailcfg: `Node.Name` "is the FQDN of the node … the
MagicDNS name for the node", `tailscale/tailcfg/tailcfg.go`). tailcfg documents a
trailing dot on `Node.Name`; drorb omits it, matching the FQDNs the live
coordinator already serves — a benign deviation the stock client tolerates. -/

/-- The ASCII `.` byte. -/
def dotByte : UInt8 := 0x2e

/-- The MagicDNS FQDN for a host: `hostname ++ "." ++ domain`. -/
def magicName (hostname domain : Bytes) : Bytes := hostname ++ [dotByte] ++ domain

/-- Decimal ASCII digits of a Nat (a collision suffix). -/
def natAscii (n : Nat) : Bytes := (Nat.toDigits 10 n).map (fun c => UInt8.ofNat c.toNat)

/-- A hostname with a deterministic collision suffix `-k`. -/
def suffixed (hostname : Bytes) (k : Nat) : Bytes := hostname ++ [0x2d] ++ natAscii k

/-- Deterministically de-duplicate hostnames: the first occurrence keeps its bare
hostname; the k-th repeat (k ≥ 1) becomes `hostname-k`, order preserved. (headscale
appends a suffix on collision — a random DNS-safe string; the deterministic
occurrence index here makes the assignment reproducible and machine-checkable.) -/
def dedupe (hs : List Bytes) : List Bytes :=
  (hs.foldl (fun (acc : List Bytes × List Bytes) h =>
      let c := (acc.1.filter (· == h)).length
      (acc.1 ++ [h], acc.2 ++ [if c == 0 then h else suffixed h c])) ([], [])).2

/-- Sample host `"laptop"`. -/
def hLaptop : Bytes := [0x6c, 0x61, 0x70, 0x74, 0x6f, 0x70]

/-- **Collision handled.** Two nodes with the SAME hostname get distinct MagicDNS
labels: `laptop`, `laptop-1`. -/
theorem dedupe_collision : dedupe [hLaptop, hLaptop] = [hLaptop, suffixed hLaptop 1] := by
  native_decide

/-- **…and the de-duplicated names are distinct.** -/
theorem dedupe_collision_nodup : (dedupe [hLaptop, hLaptop]).Nodup := by native_decide

/-- **Distinct hostnames pass through unchanged.** -/
theorem dedupe_passthrough :
    dedupe [[0x6e, 0x6f, 0x64, 0x65, 0x2d, 0x61], [0x6e, 0x6f, 0x64, 0x65, 0x2d, 0x62]]
      = [[0x6e, 0x6f, 0x64, 0x65, 0x2d, 0x61], [0x6e, 0x6f, 0x64, 0x65, 0x2d, 0x62]] := by
  native_decide

/-- **The FQDN embeds the hostname and the domain.** -/
theorem magicName_split (host dom : Bytes) : magicName host dom = host ++ [dotByte] ++ dom := rfl

end Control.Dns

#print axioms Control.Dns.dns_record_from_peer
#print axioms Control.Dns.dns_resolve_to_peer
#print axioms Control.Dns.dns_domains_preserved
#print axioms Control.Dns.dns_empty_peers
#print axioms Control.Dns.dedupe_collision
#print axioms Control.Dns.dedupe_collision_nodup
#print axioms Control.Dns.dedupe_passthrough
