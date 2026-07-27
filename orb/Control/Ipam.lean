import Control

/-!
# Control.Ipam — deterministic, collision-free IP address allocation (IPAM)

`Control.registerWithPreAuth` admits a node but `nodeOf` sets `addresses := []`, so a
registered node has no tailnet IP and an empty WireGuard `AllowedIPs`. This module is the
**IP address manager**: it hands each newly-registered node a unique overlay address from
the tailnet prefix, stamps it onto the node (`addresses` + the `/32` that becomes the
node's `AllowedIPs` in peers' netmaps), and persists the allocation as a resolved event
so a restart replays the SAME addresses — a node never loses or changes its IP.

## Ground truth (cited PUBLIC sources — headscale, BSD-3; never invented)

Modelled on headscale's `IPAllocator` (`github.com/juanfont/headscale`):

* `hscontrol/types/config.go:1118` — the default IPv4 prefix is
  `parsePrefixConfig("prefixes.v4", tsaddr.CGNATRange(), ...)`, i.e. **100.64.0.0/10**
  (the Tailscale CGNAT range); `:1143-1144` names the standard ranges
  "100.64.0.0/10 for IPv4, fd7a:115c:a1e0::/48 for IPv6". The default strategy is
  `IPAllocationStrategySequential` (`config.go:494`).
* `hscontrol/db/ip.go` — `type IPAllocator` is "a singleton responsible for allocating IP
  addresses for nodes and making sure the **same address is not handed out twice**"; it
  keeps `usedIPs netipx.IPSetBuilder` (the set of all IPs handed out) and, in
  `NewIPAllocator`, adds the prefix's **network and broadcast** addresses to `usedIPs` so
  they are never allocated, plus every address already in the database.
* `hscontrol/db/ip.go func (i *IPAllocator) next` — the walk: `ip = prev.Next()`, then
  `for { if prefix.Contains(ip) && !set.Contains(ip) && !isTailscaleReservedIP(ip) { … return } ; ip = ip.Next() }`. Sequential "never wraps: walking past the end of the
  prefix means the pool is exhausted" → `ErrCouldNotAllocateIP`.
* `hscontrol/db/ip.go func isTailscaleReservedIP` — skips `tsaddr.ChromeOSVMRange()`
  (100.115.92.0/23), `tsaddr.TailscaleServiceIP()` (100.100.100.100) and its v6 form.

## What this model proves (vs. headscale, which unit-tests these)

* **Range + exclusions** (`usable`): an allocated address is strictly inside the prefix
  (network + broadcast excluded) and not Tailscale-reserved — headscale's
  `prefix.Contains && !network && !broadcast && !isTailscaleReservedIP`, as a theorem.
* **Collision-free** (`registerAll_used_nodup`): no two nodes ever receive the same
  address — headscale's "same address is not handed out twice" invariant, PROVEN for an
  arbitrary sequence of registrations (not case-tested).
* **Replay-stable** (`restart_sound`): the allocation is persisted as a *resolved* event
  carrying the chosen address (never a re-run of the allocator — `replay` takes no
  `Pool`), so a restart replays the identical addresses. This is the `Control.Store`
  discipline (events carry outcomes, not environmental inputs) applied to IPAM.

The allocator here picks the **least free usable address**; on a fresh tailnet with no
freed holes this coincides address-for-address with headscale's sequential cursor (both
hand out …/.1, …/.2, …/.3), demonstrated in §6. The used-set + walk-forward + network/
broadcast/reserved exclusions are exactly headscale's; the "least free" refinement
additionally reclaims freed addresses, and is what makes collision-freeness a one-line
consequence (`alloc_sound`: the returned address is not in the used set).
-/

namespace Control
namespace Ipam

open Control

/-! ## §1  The address pool — a prefix with excluded endpoints and reserved ranges

An address is modelled as its integer value (32-bit for v4, 128-bit for v6 — `Nat` covers
both). A `Pool` is a prefix given by its network address and size (`2 ^ hostBits`) plus a
`reserved` predicate; the usable addresses are those strictly between network and
broadcast and not reserved. -/

/-- An address pool: a CIDR prefix as `net` (network address) + `size` (`2 ^ hostBits`
addresses), with a `reserved` predicate for Tailscale's reserved IPs. -/
structure Pool where
  /-- The network address (the all-host-bits-zero address; excluded from allocation). -/
  net      : Nat
  /-- Number of addresses in the prefix (`2 ^ (addrBits - prefixBits)`). -/
  size     : Nat
  /-- Tailscale-reserved addresses (`isTailscaleReservedIP`): never allocated. -/
  reserved : Nat → Bool

/-- The broadcast (all-host-bits-one) address — the last address of the prefix, excluded
from allocation exactly as headscale adds it to `usedIPs`. -/
def Pool.broadcast (p : Pool) : Nat := p.net + p.size - 1

/-- An address is **usable** iff it is strictly inside the prefix (so neither the network
nor the broadcast address) and not Tailscale-reserved — headscale's
`prefix.Contains(ip) && !isTailscaleReservedIP(ip)` with network/broadcast pre-added to
the used set. -/
def Pool.usable (p : Pool) (n : Nat) : Bool :=
  decide (p.net < n ∧ n < p.broadcast) && ! p.reserved n

theorem Pool.usable_range {p : Pool} {n : Nat} (h : p.usable n = true) :
    p.net < n ∧ n < p.broadcast := by
  unfold Pool.usable at h
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1

/-! ## §2  The allocator — least free usable address (bounded forward scan)

`scan` walks forward from a candidate, returning the first usable address not already in
the used set — headscale's `for { if prefix.Contains && !set.Contains && !reserved … }`.
The `fuel` bounds the walk to the prefix size (sequential "never wraps"); an exhausted
pool returns `none` (headscale's `ErrCouldNotAllocateIP`). -/

/-- Forward scan for the least free usable address ≥ `cand`, bounded by `fuel`. -/
def scan (p : Pool) (used : List Nat) : Nat → Nat → Option Nat
  | _,    0        => none
  | cand, fuel + 1 =>
      if p.usable cand = true ∧ cand ∉ used then some cand
      else scan p used (cand + 1) fuel

/-- Allocate the next address: the least free usable address in the prefix. The scan
starts at `net + 1` (the network address is excluded) and is bounded by `size`. -/
def Pool.alloc (p : Pool) (used : List Nat) : Option Nat :=
  scan p used (p.net + 1) p.size

/-- **Scan soundness.** Whatever `scan` returns is usable and not already in the used
set. -/
theorem scan_sound (p : Pool) (used : List Nat) (fuel : Nat) :
    ∀ cand ip, scan p used cand fuel = some ip → p.usable ip = true ∧ ip ∉ used := by
  induction fuel with
  | zero => intro cand ip h; simp [scan] at h
  | succ n ih =>
      intro cand ip h
      rw [scan] at h
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h
        subst h
        exact hg
      · exact ih _ _ h

/-- **Allocation soundness (the collision-free core).** An allocated address is usable
(in-range, not network/broadcast, not reserved) and **not already handed out** — the
address the used set forbids twice. -/
theorem alloc_sound (p : Pool) (used : List Nat) (ip : Nat) (h : p.alloc used = some ip) :
    p.usable ip = true ∧ ip ∉ used :=
  scan_sound p used p.size (p.net + 1) ip h

/-- **An allocated address is inside the prefix**, strictly between network and broadcast
— never the network or broadcast address. -/
theorem alloc_in_prefix (p : Pool) (used : List Nat) (ip : Nat) (h : p.alloc used = some ip) :
    p.net < ip ∧ ip < p.broadcast :=
  Pool.usable_range (alloc_sound p used ip h).1

/-! ## §3  The live IPAM state + its persisted event log

The coordinator holds the set of handed-out addresses and an append-only log of resolved
allocation events. Each `Event` carries the node key and the **chosen address** — a
resolved fact, never a callback into the allocator — so `replay` is a pure function of the
log (it takes no `Pool`), mirroring `Control.Store`. -/

/-- A resolved allocation event: node key `nk` was assigned address `ip`. -/
inductive Event where
  | alloc (nk : NodeKey) (ip : Nat)
deriving Repr, DecidableEq

/-- The address an event records. -/
def Event.ip : Event → Nat | .alloc _ ip => ip
/-- The (key, address) binding an event records. -/
def Event.binding : Event → NodeKey × Nat | .alloc nk ip => (nk, ip)

/-- The live IPAM state: the addresses handed out, and the append-only allocation log. -/
structure St where
  /-- The set of addresses already handed out (headscale `usedIPs`). -/
  used : List Nat
  /-- The append-only, resolved allocation log the store persists. -/
  log  : List Event
deriving Repr

/-- The empty IPAM: nothing allocated, empty log. -/
def St.init : St := { used := [], log := [] }

/-- **Register a node's address.** Allocate the next free address from pool `p`, record it
in the used set and append a resolved `alloc` event to the log. An exhausted pool is a
no-op (the node gets no address — headscale returns an error). -/
def St.register (p : Pool) (st : St) (nk : NodeKey) : St :=
  match p.alloc st.used with
  | some ip => { used := st.used ++ [ip], log := st.log ++ [Event.alloc nk ip] }
  | none    => st

/-! ## §4  Replay — reconstruct the addresses from the log alone (no reallocation)

`replay` reads the addresses straight out of the resolved log; it takes **no** `Pool`, so
it can never re-run the allocator and hand a node a different address on restart. This is
the property that keeps a node's IP stable across a coordinator restart. -/

/-- Reconstruct the used-address set from the persisted log. Takes only the log — never
the allocator — so restart cannot reassign. -/
def replay (log : List Event) : List Nat := log.map Event.ip
/-- Reconstruct the (key ↦ address) bindings from the persisted log. -/
def replayBindings (log : List Event) : List (NodeKey × Nat) := log.map Event.binding

/-- The live coherence invariant: the in-memory used set is exactly the replay of the log
(mirrors `Control.Store.Coherent`). -/
def St.Coherent (st : St) : Prop := st.used = replay st.log

/-- **Boot is coherent.** -/
theorem coherent_init : St.init.Coherent := by
  simp [St.Coherent, St.init, replay]

/-- **A registration preserves coherence.** The used set stays equal to the replay of the
(extended) log — the allocated address is appended to both in lockstep. -/
theorem register_coherent (p : Pool) (st : St) (nk : NodeKey) (h : st.Coherent) :
    (st.register p nk).Coherent := by
  unfold St.Coherent replay at h ⊢
  unfold St.register
  split
  · rename_i ip _
    simp only [List.map_append, List.map_cons, List.map_nil, Event.ip]
    rw [← h]
  · exact h

/-- Appending a fresh element to a duplicate-free list keeps it duplicate-free. -/
theorem nodup_snoc {l : List Nat} {a : Nat} (h : l.Nodup) (ha : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons x t ih =>
      rw [List.nodup_cons] at h
      simp only [List.mem_cons, not_or] at ha
      rw [List.cons_append, List.nodup_cons]
      refine ⟨?_, ih h.2 ha.2⟩
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨h.1, fun he => ha.1 he.symm⟩

/-- **A registration preserves distinctness.** If the used set had no duplicates, it still
has none after allocating one more address — the freshly allocated address is not already
in the set (`alloc_sound`). This is headscale's "same address is not handed out twice",
step by step. -/
theorem register_nodup (p : Pool) (st : St) (nk : NodeKey) (h : st.used.Nodup) :
    (st.register p nk).used.Nodup := by
  unfold St.register
  split
  · rename_i ip hip
    exact nodup_snoc h (alloc_sound p st.used ip hip).2
  · exact h

/-- **Restart soundness.** Replaying the persisted log reconstructs *exactly* the
pre-restart used-address set — no node loses or changes its IP. `replay` takes no `Pool`,
so this is reassignment-free by construction. -/
theorem restart_sound (st : St) (h : st.Coherent) : replay st.log = st.used := h.symm

/-! ## §5  Registering a whole tailnet — the top-level guarantees

Folding `register` over a list of node keys from `init`: the resulting addresses are all
distinct (collision-free) and the log replays to exactly those addresses (restart-stable),
for an **arbitrary** pool and **arbitrary** sequence of nodes. -/

/-- Register a sequence of nodes, each getting the next free address. -/
def registerAll (p : Pool) (ks : List NodeKey) : St := ks.foldl (St.register p) St.init

/-- The fold invariant: from any distinct+coherent state, registering more nodes keeps the
used set distinct and coherent. -/
theorem registerAll_from (p : Pool) (ks : List NodeKey) :
    ∀ st, st.used.Nodup → st.Coherent →
      (ks.foldl (St.register p) st).used.Nodup ∧ (ks.foldl (St.register p) st).Coherent := by
  induction ks with
  | nil => intro st h1 h2; exact ⟨h1, h2⟩
  | cons k ks ih =>
      intro st h1 h2
      simp only [List.foldl_cons]
      exact ih (st.register p k)
        (register_nodup p st k h1) (register_coherent p st k h2)

/-- **COLLISION-FREE (distinctness).** After registering any list of nodes, no two of them
share an address — the used set has no duplicates. This is headscale's
`IPAllocator` invariant "the same address is not handed out twice", proven for every run,
not sampled. -/
theorem registerAll_used_nodup (p : Pool) (ks : List NodeKey) :
    (registerAll p ks).used.Nodup :=
  (registerAll_from p ks St.init (by simp [St.init]) coherent_init).1

/-- **REPLAY-STABLE.** After registering any list of nodes, replaying the persisted log
reconstructs exactly the addresses that were handed out — a restart returns every node its
same IP. -/
theorem registerAll_replay_stable (p : Pool) (ks : List NodeKey) :
    replay (registerAll p ks).log = (registerAll p ks).used :=
  restart_sound _ (registerAll_from p ks St.init (by simp [St.init]) coherent_init).2

/-- One registration keeps every used address inside the prefix. -/
theorem register_in_prefix (p : Pool) (st : St) (nk : NodeKey)
    (h : ∀ ip ∈ st.used, p.net < ip ∧ ip < p.broadcast) :
    ∀ ip ∈ (st.register p nk).used, p.net < ip ∧ ip < p.broadcast := by
  intro ip hip
  unfold St.register at hip
  cases hAlloc : p.alloc st.used with
  | none => simp only [hAlloc] at hip; exact h ip hip
  | some ip0 =>
      simp only [hAlloc, List.mem_append, List.mem_singleton] at hip
      rcases hip with h1 | h1
      · exact h ip h1
      · rw [h1]; exact alloc_in_prefix p st.used ip0 hAlloc

/-- The fold version of `register_in_prefix`. -/
theorem registerAll_from_prefix (p : Pool) (ks : List NodeKey) :
    ∀ (st : St), (∀ ip ∈ st.used, p.net < ip ∧ ip < p.broadcast) →
      ∀ ip ∈ (ks.foldl (St.register p) st).used, p.net < ip ∧ ip < p.broadcast := by
  induction ks with
  | nil => intro st h; exact h
  | cons k ks ih =>
      intro st h
      simp only [List.foldl_cons]
      exact ih (st.register p k) (register_in_prefix p st k h)

/-- **Every allocated address is in the prefix.** Each address in the used set of any run
lies strictly between the pool's network and broadcast addresses. -/
theorem registerAll_in_prefix (p : Pool) (ks : List NodeKey) :
    ∀ ip ∈ (registerAll p ks).used, p.net < ip ∧ ip < p.broadcast :=
  registerAll_from_prefix p ks St.init (by simp [St.init])

/-! ## §6  The v4 CGNAT pool + v6 ULA pool, and address ↔ bytes

The concrete tailnet ranges (headscale defaults, cited §top). Addresses convert to the
byte-addressed `Control.Prefix` used by `Node.addresses` / `Node.allowedIPs`. -/

/-- Tailscale's `TailscaleServiceIP()` — 100.100.100.100. -/
def tsServiceIP : Nat := 0x64646464
/-- `tsaddr.ChromeOSVMRange()` low — 100.115.92.0. -/
def chromeVMLo : Nat := 0x64735c00
/-- `tsaddr.ChromeOSVMRange()` high — 100.115.93.255 (a /23). -/
def chromeVMHi : Nat := 0x64735dff

/-- `isTailscaleReservedIP` for the v4 range: the service IP or the ChromeOS VM /23. -/
def cgnatReserved (n : Nat) : Bool :=
  (n == tsServiceIP) || decide (chromeVMLo ≤ n ∧ n ≤ chromeVMHi)

/-- **The IPv4 CGNAT pool: 100.64.0.0/10** (headscale default `prefixes.v4 =
tsaddr.CGNATRange()`, `config.go:1118`). Network 100.64.0.0 = `0x64400000`; `2^22`
addresses (host bits `32 - 10`); broadcast 100.127.255.255. -/
def cgnatPool : Pool := { net := 0x64400000, size := 2 ^ 22, reserved := cgnatReserved }

/-- The IPv6 ULA base: fd7a:115c:a1e0:: = `0xfd7a115ca1e0` shifted into the top 48 bits of
a 128-bit address. -/
def ulaBase : Nat := 0xfd7a115ca1e0 * 2 ^ 80
/-- Tailscale's `TailscaleServiceIPv6()` — fd7a:115c:a1e0::53. -/
def tsServiceIPv6 : Nat := ulaBase + 0x53

/-- **The IPv6 ULA pool: fd7a:115c:a1e0::/48** (headscale default `prefixes.v6`,
`config.go:1143-1144`). `2^80` addresses (host bits `128 - 48`). -/
def ulaPool : Pool := { net := ulaBase, size := 2 ^ 80, reserved := fun n => n == tsServiceIPv6 }

/-- The `k`-th big-endian octet (`k = 0` is the least-significant byte). -/
def byteAt (n k : Nat) : UInt8 := UInt8.ofNat (n / 2 ^ (8 * k) % 256)

/-- A 32-bit address value as 4 big-endian octets — the `Control.Prefix.addr` shape. -/
def natToV4 (n : Nat) : Bytes := [byteAt n 3, byteAt n 2, byteAt n 1, byteAt n 0]

/-- The inverse of `natToV4`: read 4 big-endian octets back to the integer address value
(the `Control.Prefix.addr` shape → `Nat`). Recovers the used-set integers a live
coordinator reads back off already-stamped node addresses (`usedOf`). -/
def v4ToNat (bs : Bytes) : Nat :=
  (bs.getD 0 0).toNat * 16777216 + (bs.getD 1 0).toNat * 65536
    + (bs.getD 2 0).toNat * 256 + (bs.getD 3 0).toNat

/-- **`v4ToNat` inverts `natToV4`** on any 32-bit value — the address ↔ bytes round-trip
the live used-set reconstruction (`usedOf ∘ stamp`) depends on. -/
theorem v4ToNat_natToV4 (n : Nat) (h : n < 2 ^ 32) : v4ToNat (natToV4 n) = n := by
  simp only [v4ToNat, natToV4, List.getD_cons_zero, List.getD_cons_succ, byteAt,
    Nat.reduceMul, Nat.reducePow, UInt8.toNat_ofNat']
  omega
/-- A 128-bit address value as 16 big-endian octets. -/
def natToV6 (n : Nat) : Bytes := (List.range 16).reverse.map (byteAt n)

/-- The `/32` prefix of a v4 address value — a node's own address / `AllowedIP`. -/
def v4Prefix (ip : Nat) : Prefix := { addr := natToV4 ip, bits := 32 }
/-- The `/128` prefix of a v6 address value. -/
def v6Prefix (ip : Nat) : Prefix := { addr := natToV6 ip, bits := 128 }

/-! ## §7  Stamping the address onto the node

Give a registered node its address: `addresses := [/32 (+ /128)]`, and the same prefixes
become its `AllowedIPs` — exactly the routes peers accept toward it (tailscale/headscale:
a node's self address is its `/32`+`/128` AllowedIP). This fixes `nodeOf`'s empty
`addresses`/`allowedIPs`. -/

/-- Stamp a v4 address onto a node: it becomes the node's sole address and its `/32`
`AllowedIP`. -/
def stampV4 (nd : Node) (ip : Nat) : Node :=
  { nd with addresses := [v4Prefix ip], allowedIPs := [v4Prefix ip] }

/-- Stamp a dual-stack v4+v6 pair onto a node: `/32` and `/128`, both as `AllowedIPs`. -/
def stampDual (nd : Node) (ip4 ip6 : Nat) : Node :=
  { nd with addresses := [v4Prefix ip4, v6Prefix ip6],
            allowedIPs := [v4Prefix ip4, v6Prefix ip6] }

/-- **The stamped `/32` is the node's `AllowedIP`.** -/
theorem stampV4_allowedIPs (nd : Node) (ip : Nat) :
    (stampV4 nd ip).allowedIPs = [v4Prefix ip] := rfl

/-- **The stamped address survives translation to the WireGuard peer.** The node's
cryptokey-routing `allowed` set (via `Node.toWgPeer`) is exactly its stamped `/32` — a
peer accepts traffic to this node for precisely the allocated address. -/
theorem stampV4_wg_allowed (nd : Node) (ip : Nat) :
    (stampV4 nd ip).toWgPeer.allowed = [(v4Prefix ip).toWgCidr] := by
  rw [wgpeer_allowed_preserved, stampV4_allowedIPs]; rfl

/-! ## §7.5  The LIVE used-set — read back off the registry, allocate the next free

A live coordinator that persists each allocation as a stamped node address (`stampV4`)
reconstructs its used-address set by reading the `/32` off every registered node
(`usedOf`), then hands the next node the least free address NOT in that set
(`cgnatPool.alloc (usedOf regs)`). `alloc_sound` makes the fresh address distinct from
every already-served one — the cross-connection "distinct nodes get distinct addresses"
guarantee at the live allocation site (as opposed to the batch `registerAll`). -/

/-- The set of addresses already handed out, read back off the registry's stamped node
`/32`s. The live analogue of `St.used`, reconstructed from the durable ControlState. -/
def usedOf (regs : List Control.Registration) : List Nat :=
  regs.filterMap (fun r => (r.node.addresses.head?).map (fun p => v4ToNat p.addr))

/-- **LIVE DISTINCTNESS.** The address the coordinator allocates for the next node
(`cgnatPool.alloc (usedOf regs)`) is NOT among the addresses already served to the
registered nodes — so a fresh registration never collides with an existing one. This is
headscale's "same address is not handed out twice" at the live, one-node-at-a-time
allocation site (`alloc_sound`). -/
theorem liveAlloc_distinct (regs : List Control.Registration) (ip : Nat)
    (h : cgnatPool.alloc (usedOf regs) = some ip) : ip ∉ usedOf regs :=
  (alloc_sound cgnatPool (usedOf regs) ip h).2

/-! ## §8  The GATE — register 3 nodes, distinct 100.64.x.x, in each other's netmap,
kill + replay ⇒ same addresses. Driven through the REAL allocator and the REAL
`Control.buildNetMap`. -/

def keyA : NodeKey := ⟨List.replicate 32 0xA1⟩
def keyB : NodeKey := ⟨List.replicate 32 0xB2⟩
def keyC : NodeKey := ⟨List.replicate 32 0xC3⟩

/-- The three concrete addresses the fresh CGNAT pool hands out: 100.64.0.1/.2/.3. -/
def ip1 : Nat := 0x64400001   -- 100.64.0.1
def ip2 : Nat := 0x64400002   -- 100.64.0.2
def ip3 : Nat := 0x64400003   -- 100.64.0.3

/-- The IPAM state after registering the three nodes (through the real allocator). -/
def demoIpam : St := registerAll cgnatPool [keyA, keyB, keyC]

/-- A netmap node bearing an already-stamped address. -/
def mkNode (id : Nat) (nm : Bytes) (k : NodeKey) (ip : Nat) : Node :=
  stampV4
    { id := id, stableID := nm, name := nm, user := 1, key := k,
      machine := ⟨List.replicate 32 0⟩, disco := ⟨List.replicate 32 0⟩,
      addresses := [], allowedIPs := [], endpoints := [], derp := 1,
      online := true, keyExpiry := 0, authorized := true } ip

def nodeA : Node := mkNode 1 [0x61] keyA ip1
def nodeB : Node := mkNode 2 [0x62] keyB ip2
def nodeC : Node := mkNode 3 [0x63] keyC ip3

def regA : Registration := { nodeKey := keyA, node := nodeA, status := .authorized }
def regB : Registration := { nodeKey := keyB, node := nodeB, status := .authorized }
def regC : Registration := { nodeKey := keyC, node := nodeC, status := .authorized }

/-- The coordination state for the 3-node tailnet (deny-all filter / empty DNS: this gate
is about addressing, not ACLs — `Control.Join` covers the filter). -/
def demoCoord : ControlState := { nodes := [regA, regB, regC], filter := [], dns := DnsConfig.empty }

/-- The netmap node A is served by the REAL `Control.buildNetMap`. -/
def servedNetMapA : NetMap := buildNetMap demoCoord regA

/-! ### Distinctness — the three addresses are pairwise distinct 100.64.x.x -/

/-- **The three registered nodes get distinct addresses** — an instance of the general
`registerAll_used_nodup` theorem, and (below) the concrete `[.1, .2, .3]`. -/
theorem demo_distinct : demoIpam.used.Nodup := registerAll_used_nodup cgnatPool [keyA, keyB, keyC]

/-- **Replay stability** — killing and replaying reconstructs the same addresses, from the
general `registerAll_replay_stable`. -/
theorem demo_replay_stable : replay demoIpam.log = demoIpam.used :=
  registerAll_replay_stable cgnatPool [keyA, keyB, keyC]

/-- **Every demo address is inside 100.64.0.0/10.** -/
theorem demo_in_prefix : ∀ ip ∈ demoIpam.used, cgnatPool.net < ip ∧ ip < cgnatPool.broadcast :=
  registerAll_in_prefix cgnatPool [keyA, keyB, keyC]

/-! ### Netmap — peers appear with those addresses as AllowedIPs (real `buildNetMap`) -/

/-- **Peer B is served to A with its `/32` AllowedIP.** Node B is a peer in A's served
netmap, and its `AllowedIPs` are exactly `[100.64.0.2/32]`. -/
theorem served_peer_B_allowedIPs :
    ∃ p ∈ servedNetMapA.peers, p.id = 2 ∧ p.allowedIPs = [{ addr := [100, 64, 0, 2], bits := 32 }] := by
  refine ⟨nodeB, by decide, rfl, by decide⟩

/-- **Peer C is served to A with its `/32` AllowedIP** — `[100.64.0.3/32]`. -/
theorem served_peer_C_allowedIPs :
    ∃ p ∈ servedNetMapA.peers, p.id = 3 ∧ p.allowedIPs = [{ addr := [100, 64, 0, 3], bits := 32 }] := by
  refine ⟨nodeC, by decide, rfl, by decide⟩

/-- **A's own record carries its `/32`** — self address 100.64.0.1/32. -/
theorem served_self_A_address :
    servedNetMapA.self.addresses = [{ addr := [100, 64, 0, 1], bits := 32 }] := by decide

/-! ## §9  Runtime evidence (`#guard`) — the concrete allocator run + kill/replay -/

-- The fresh CGNAT pool hands out 100.64.0.1, then .2, then .3 (headscale sequential too):
#guard cgnatPool.alloc [] = some ip1
#guard cgnatPool.alloc [ip1] = some ip2
#guard cgnatPool.alloc [ip1, ip2] = some ip3
-- The three registered nodes' addresses, as 100.64.x.x bytes:
#guard demoIpam.used = [ip1, ip2, ip3]
#guard demoIpam.used.map natToV4 = [[100, 64, 0, 1], [100, 64, 0, 2], [100, 64, 0, 3]]
-- The persisted bindings (which node got which address):
#guard replayBindings demoIpam.log = [(keyA, ip1), (keyB, ip2), (keyC, ip3)]
-- KILL + REPLAY: replaying the log reconstructs the SAME addresses (no reassignment):
#guard replay demoIpam.log = [ip1, ip2, ip3]
#guard replay demoIpam.log = demoIpam.used
-- Address ↔ bytes round-trips at the stamping boundary:
#guard natToV4 ip1 = [100, 64, 0, 1]
-- `v4ToNat` inverts `natToV4`, and reads the used-set back off stamped node addresses:
#guard v4ToNat (natToV4 ip2) = ip2
#guard v4ToNat [100, 64, 0, 3] = ip3
#guard usedOf [regA, regB, regC] = [ip1, ip2, ip3]
#guard cgnatPool.alloc (usedOf [regA, regB]) = some ip3
#guard natToV4 cgnatPool.broadcast = [100, 127, 255, 255]
#guard natToV6 (ulaBase + 1) = [0xfd, 0x7a, 0x11, 0x5c, 0xa1, 0xe0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
-- The v6 ULA pool hands out fd7a:115c:a1e0::1 first:
#guard ulaPool.alloc [] = some (ulaBase + 1)
-- Peers carry their addresses as AllowedIPs in the real served netmap:
#guard servedNetMapA.peers.map (·.id) = [2, 3]
#guard servedNetMapA.peers.map (·.allowedIPs) =
  [[{ addr := [100, 64, 0, 2], bits := 32 }], [{ addr := [100, 64, 0, 3], bits := 32 }]]

end Ipam
end Control

#print axioms Control.Ipam.scan_sound
#print axioms Control.Ipam.alloc_sound
#print axioms Control.Ipam.alloc_in_prefix
#print axioms Control.Ipam.register_coherent
#print axioms Control.Ipam.register_nodup
#print axioms Control.Ipam.restart_sound
#print axioms Control.Ipam.registerAll_used_nodup
#print axioms Control.Ipam.registerAll_replay_stable
#print axioms Control.Ipam.registerAll_in_prefix
#print axioms Control.Ipam.v4ToNat_natToV4
#print axioms Control.Ipam.liveAlloc_distinct
#print axioms Control.Ipam.stampV4_wg_allowed
#print axioms Control.Ipam.demo_distinct
#print axioms Control.Ipam.demo_replay_stable
#print axioms Control.Ipam.demo_in_prefix
#print axioms Control.Ipam.served_peer_B_allowedIPs
#print axioms Control.Ipam.served_peer_C_allowedIPs
#print axioms Control.Ipam.served_self_A_address
