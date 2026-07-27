import Control
import Control.Register
import Control.Routes
import Control.PreAuthKey
import Control.Ipam
import Hygiene

/-!
# Control.Store — a durable, replayable log for the coordination state

The coordination server's state (`Control.ControlState`: the node registry, the
compiled ACL filter, the DNS config) — plus the minted pre-auth keys the store
tracks alongside it — lives in memory. A process restart drops it, and every
node must re-register: a restart is a tailnet outage.

This module makes a restart *safe*. It records every state-changing operation as
an **event** in an append-only **log**, and reconstructs the state by **replaying**
the log from empty. The design has three verified pieces:

1. **A total, round-tripping log codec.** `encodeLog`/`decodeLog` over `Bytes`,
   built from the exact self-delimiting codec algebra of `Control` (LEB128
   length-prefixes, `putSeq`/`getSeq`), with a proven
   `decodeLog (encodeLog log) = some (log, [])`. The bytes on disk decode back to
   the same event list — the total-parser discipline of `Control.TailcfgWire`.

2. **A deterministic state fold.** `applyEvent : CoordState → Event → CoordState`
   replays one event; `replay := foldl applyEvent init`. It takes **no** `Policy`
   and **no** clock — the environmental/non-deterministic inputs (the signature
   check, wall-clock expiry) are *resolved at record time* and captured in the
   event (e.g. `nodeRegistered` carries the authorization **decision**, not the
   policy). So `replay` is a pure function of the log alone.

3. **Replay soundness.** The live coordinator maintains the invariant
   `state = replay log` (`Coherent`): it starts coherent (`init = replay []`) and
   every step preserves it (append the event, apply it — `coherent_step`). Hence a
   restart that replays the persisted log recovers *exactly* the pre-restart state
   (`restart_sound`). The bridge `register_event_matches_step` shows the persisted
   `nodeRegistered` event reproduces the live `Control.step` register transition —
   so the invariant is one the *real* coordinator actually maintains, not a fiction.

Persistence itself (the `write`/`fsync`/read of the encoded bytes) is host I/O,
out of the trusted core; the state machine and the replay theorem are the Lean.
-/

namespace Control.Store

open Control

/-! ## §1  A minted pre-auth key

A pre-auth key lets a node register non-interactively (`RegisterRequest.authKey`).
The pre-auth lane owns the *cryptographic* key model; the store tracks the minted
keys as coordination state so a restart does not forget which keys exist. This is
the minimal record the store persists — an opaque key id, whether it is reusable,
and whether it has been consumed. -/
structure PreauthKey where
  /-- The stored key identity — the SHA-256 **hash** of the pre-auth secret
  (hashed at rest; matched against `hash RegisterRequest.authKey`). Named `key`
  because the live coord persists `Control.PreAuth.KeyRecord.keyHash` here. -/
  key       : Bytes
  /-- Reusable keys survive their first use; single-use keys are consumed. -/
  reusable  : Bool
  /-- Spent by a one-shot registration (headscale `Used`). -/
  used      : Bool
  /-- Registers ephemeral (auto-reaped) nodes (headscale `Ephemeral`). -/
  ephemeral : Bool := false
  /-- Unix-seconds expiry; `0` = never (headscale `Expiration`). -/
  expiry    : Nat := 0
  /-- ACL tags stamped on the node at registration (headscale `Tags`). -/
  tags      : List Bytes := []
  /-- Owning user id (headscale `UserID`). -/
  user      : Nat := 0
  /-- Operator-revoked (headscale `Revoked`). -/
  revoked   : Bool := false
deriving Repr, DecidableEq

/-- The **lossless** view of a persisted key as the admission gate's `KeyRecord`
(`Control.PreAuth`). Every persisted field maps across — no attribute is dropped,
so a replayed key validates *exactly* as the live one did (`spendKey_toRecord`,
`oneShot_rejected_after_restart`). -/
def PreauthKey.toRecord (pk : PreauthKey) : Control.PreAuth.KeyRecord :=
  { keyHash := pk.key
    attrs := { reusable := pk.reusable, ephemeral := pk.ephemeral,
               expiry := pk.expiry, tags := pk.tags, user := pk.user }
    used := pk.used, revoked := pk.revoked }

/-! ## §2  The coordination state the store reconstructs

`ControlState` (registry + filter + DNS) plus the minted pre-auth keys. This is
the whole of the coordinator's durable state; nothing else needs to survive a
restart (the TS2021 record layer's counters are per-connection and owned by
`Control.Channel`, not persisted here). -/
structure CoordState where
  control : ControlState
  preauth : List PreauthKey
deriving Repr

/-- The empty coordinator: empty registry, deny-all filter, empty DNS, no keys. -/
def CoordState.init : CoordState :=
  { control := ControlState.init, preauth := [] }

/-! ## §3  The event algebra

One constructor per state-changing operation the coordinator performs. Each is a
*resolved* fact — an event carries the outcome, never a callback or an
environmental input — so replaying is deterministic. -/
inductive Event where
  /-- A registration was processed. `authorized` is the **decision the policy
  returned at record time** — replay does not re-run the policy. Mirrors the
  register branch of `Control.step`. -/
  | nodeRegistered  (req : RegisterRequest) (authorized : Bool)
  /-- The clock advanced to `now`; expired node keys were marked `.expired`. -/
  | nodeExpired     (now : Nat)
  /-- An operator SET a node's key expiry (headscale `nodes expire --expiry` /
  `set-expiry`, and `--disable-expiry` ⇒ `expiry = 0`, tailscale's "the zero value
  if this node does not expire"). Stamps `keyExpiry := expiry` onto node `nk`; the
  clock-driven `nodeExpired` then demotes it once the wall clock passes it. -/
  | nodeExpirySet   (nk : NodeKey) (expiry : Nat)
  /-- A node re-keyed from `old` to `new` (identity-preserving rename). -/
  | keyRotated      (old new : NodeKey)
  /-- An ephemeral node disconnected and was reaped from the registry. -/
  | nodeReaped      (nk : NodeKey)
  /-- A pre-auth key was minted (with its FULL attributes: reusable/ephemeral/
  expiry/tags/user/revoked). -/
  | keyMinted       (pk : PreauthKey)
  /-- A one-shot pre-auth key was spent by a registration — carries the *resolved*
  `keyHash` (headscale `Used := true`). Replay re-applies the spend, so a used
  one-shot key stays used across a restart (no double-spend). -/
  | keyConsumed     (keyHash : Bytes)
  /-- A node advertised subnet routes (recorded pending operator approval). -/
  | routesAdvertised (nk : NodeKey) (routes : List Prefix)
  /-- An operator approved a set of the node's advertised subnet routes. -/
  | routeApproved   (nk : NodeKey) (approved : List Prefix)
  /-- The compiled ACL packet filter was replaced. -/
  | filterSet       (pf : PacketFilter)
  /-- The DNS config was replaced. -/
  | dnsSet          (d : DnsConfig)
  /-- **An IPAM address was allocated to a node.** `nk` was assigned the overlay
  address `ip` (a resolved fact — the allocator ran at record time; replay never
  re-runs it, exactly as `Control.Ipam.Event.alloc`). Replay STAMPS `ip` onto `nk`'s
  registration (`Ipam.stampV4`: `addresses` + the `/32` `AllowedIP`), so the SAME node
  re-connecting — or the coordinator after a restart-replay — keeps its SAME address, and
  a DIFFERENT node (allocated `alloc (usedOf …)`) gets the NEXT free one. -/
  | addrAllocated   (nk : NodeKey) (ip : Nat)
  /-- **An operator SET a node's ACL tags** (`drorb-ctl nodes tag <node> tag:a,tag:b`;
  headscale `nodes tag -t`). Replaces `Node.tags` wholesale — the *resolved* tag list is
  in the event, so replay is deterministic. Whether a tag then CONFERS anything is a
  separate, policy-time decision: `Control.Tags.tagBindings` drops any tag the node's
  owning user is not a `tagOwner` of, so a stamped tag is a claim, never an authority. -/
  | nodeTagsSet     (nk : NodeKey) (tags : List Bytes)
  /-- **A node's owning user was resolved to `user`.** Emitted alongside
  `nodeRegistered` when a pre-auth key admitted the node, carrying the key's `user` —
  a RESOLVED fact, so replay reconstructs the owner without re-running the gate.
  ★Why it exists: `nodeRegistered` replays through `Control.nodeOf`, which builds the
  node with `user := 0` and `tags := []`; without these two events the owner and tags a
  pre-auth key stamped were lost on every restart (and on every serve, since the served
  state IS a replay), which silently disabled tag ownership. -/
  | nodeUserSet     (nk : NodeKey) (user : Nat)
deriving Repr, DecidableEq

/-- Map a function over the node record of the registration keyed by `nk`,
leaving every other registration untouched. -/
def mapNode (nk : NodeKey) (f : Node → Node) (s : ControlState) : ControlState :=
  { s with nodes := s.nodes.map (fun r => if r.nodeKey = nk then { r with node := f r.node } else r) }

/-- Spend the one-shot key with the resolved `keyHash`: mark the matching
non-reusable persisted key `used`. The replay image of `Control.PreAuth.consume`
(`spendKey_toRecord`). Reusable keys and non-matching keys are untouched. -/
def spendKey (keyHash : Bytes) (ks : List PreauthKey) : List PreauthKey :=
  ks.map (fun pk => if pk.key = keyHash ∧ pk.reusable = false then { pk with used := true } else pk)

/-- **Apply one event.** The deterministic replay step. Each branch is exactly the
already-modelled pure transition on `ControlState` (from `Control`, `Register`,
`Routes`) or a pre-auth-key insertion. -/
def applyEvent (st : CoordState) : Event → CoordState
  | .nodeRegistered req ok =>
      let status := if ok then NodeStatus.authorized else NodeStatus.registered
      let reg : Registration := { nodeKey := req.nodeKey, node := nodeOf req ok, status }
      { st with control := { st.control with nodes := upsertReg st.control.nodes reg } }
  | .nodeExpired now =>
      { st with control := Register.expire now st.control }
  | .nodeExpirySet nk expiry =>
      { st with control := mapNode nk (fun n => { n with keyExpiry := expiry }) st.control }
  | .keyRotated old new =>
      { st with control := Register.rotateKey old new st.control }
  | .nodeReaped nk =>
      { st with control := Register.reapEphemeral nk st.control }
  | .keyMinted pk =>
      { st with preauth := pk :: st.preauth }
  | .keyConsumed keyHash =>
      { st with preauth := spendKey keyHash st.preauth }
  | .routesAdvertised nk routes =>
      { st with control := mapNode nk (fun n => { n with allowedIPs := n.addresses ++ routes }) st.control }
  | .routeApproved nk approved =>
      { st with control := mapNode nk (Routes.approveRoutes approved) st.control }
  | .filterSet pf =>
      { st with control := { st.control with filter := pf } }
  | .dnsSet d =>
      { st with control := { st.control with dns := d } }
  | .addrAllocated nk ip =>
      { st with control := mapNode nk (fun n => Control.Ipam.stampV4 n ip) st.control }
  | .nodeTagsSet nk tags =>
      { st with control := mapNode nk (fun n => { n with tags := tags }) st.control }
  | .nodeUserSet nk user =>
      { st with control := mapNode nk (fun n => { n with user := user }) st.control }

/-- **Replay a log from empty.** Fold every event, in order, over the empty
coordinator. This is the state a fresh process reconstructs on startup. -/
def replay (log : List Event) : CoordState :=
  log.foldl applyEvent CoordState.init

/-! ## §4  Replay soundness

The live coordinator holds `state = replay log` as an invariant. It is trivially
true at boot and preserved by every step, so a restart's `replay log` equals the
pre-restart `state`. -/

/-- The live invariant: the in-memory state equals the replay of the persisted log. -/
def Coherent (st : CoordState) (log : List Event) : Prop := st = replay log

/-- **Appending an event = applying it to the prior replay.** The fold coherence
that underwrites the whole scheme (`List.foldl_concat`). -/
theorem replay_append (log : List Event) (e : Event) :
    replay (log ++ [e]) = applyEvent (replay log) e := by
  simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Boot is coherent.** A fresh coordinator with an empty log is in sync. -/
theorem coherent_init : Coherent CoordState.init [] := rfl

/-- **A step preserves coherence.** If the state was the replay of the log, then
after appending event `e` to the log and applying `e` to the state, the state is
still the replay of the (extended) log. This is what the live coordinator does on
every state change: append, then apply. -/
theorem coherent_step (st : CoordState) (log : List Event) (e : Event)
    (h : Coherent st log) : Coherent (applyEvent st e) (log ++ [e]) := by
  unfold Coherent at h ⊢
  rw [replay_append, ← h]

/-- **Restart soundness.** Replaying the persisted log reconstructs *exactly* the
pre-restart in-memory state. This is the property that makes a restart safe: no
node loses its registration, no key or approved route is forgotten. -/
theorem restart_sound (st : CoordState) (log : List Event) (h : Coherent st log) :
    replay log = st := h.symm

/-- **Coherence is preserved along any run.** Folding a batch of events into a
coherent state stays coherent — the invariant is maintained across an arbitrary
sequence of operations, not just one step. -/
theorem coherent_run (st : CoordState) (log evs : List Event) (h : Coherent st log) :
    Coherent (evs.foldl applyEvent st) (log ++ evs) := by
  induction evs generalizing st log with
  | nil => simpa using h
  | cons e es ih =>
      have hstep := coherent_step st log e h
      have hrun := ih (applyEvent st e) (log ++ [e]) hstep
      simpa [List.foldl_cons, List.append_assoc] using hrun

/-! **Where determinism actually lives.** `replay log = replay log` is
congruence, not a property of `replay`, so it is not stated here. The claim the
name makes — *two replays of the same persisted bytes agree* — is
`replay_deterministic` at the bottom of this file, over `encodeLog`: it needs the
codec to be injective and would FAIL for a lossy one. -/

/-! ### The live-transition bridge

The persisted `nodeRegistered` event reproduces the live `Control.step` register
transition, so `Coherent` is an invariant the *real* coordinator maintains. -/

/-- **The persisted register event matches the live step.** Recording
`nodeRegistered req (pol.authorizes …)` and replaying it produces exactly the
`ControlState` the live `Control.step` register transition produces. So the
coordinator can, on each register, append this event and update its state by
`step` and stay coherent. -/
theorem register_event_matches_step (pol : Policy) (st : CoordState)
    (req : RegisterRequest) :
    (applyEvent st (.nodeRegistered req (pol.authorizes req.nodeKey req.authKey))).control
      = (step pol st.control (.register req)).1 := by
  simp only [applyEvent, step]

/-- **The persisted expiry event matches `Register.expire`.** -/
theorem expired_event_matches (st : CoordState) (now : Nat) :
    (applyEvent st (.nodeExpired now)).control = Register.expire now st.control := rfl

/-- **The persisted reap event matches `Register.reapEphemeral`.** -/
theorem reap_event_matches (st : CoordState) (nk : NodeKey) :
    (applyEvent st (.nodeReaped nk)).control = Register.reapEphemeral nk st.control := rfl

/-! ### Rich pre-auth key recovery (the lossy-schema gap, closed)

The persisted key schema carries the FULL pre-auth attributes
(`keyHash`/`reusable`/`ephemeral`/`expiry`/`tags`/`user`/`revoked`) plus the
one-shot `used` spend bit, so a restart recovers a key with every attribute
intact and a spent one-shot key stays spent — no double-spend across a restart. -/

/-- **A minted rich key is recovered verbatim.** Replaying a `keyMinted` event
reconstructs the key with EVERY attribute (tags, expiry, user, ephemeral,
revoked) intact — the old lossy `{key,reusable,used}` schema is gone. -/
theorem replay_recovers_key (pk : PreauthKey) :
    (replay [.keyMinted pk]).preauth = [pk] := by
  simp [replay, CoordState.init, applyEvent]

/-- **The Store spend is the admission gate's `consume`, under the record view.**
Applying a `keyConsumed keyHash` and viewing the persisted keys as `KeyRecord`s
equals `Control.PreAuth.consumeHash` on the record view — so what replay marks
spent is exactly what the live admission gate spent. -/
theorem spendKey_toRecord (keyHash : Bytes) (ks : List PreauthKey) :
    (spendKey keyHash ks).map PreauthKey.toRecord
      = Control.PreAuth.consumeHash keyHash (ks.map PreauthKey.toRecord) := by
  unfold spendKey Control.PreAuth.consumeHash
  simp only [List.map_map]
  apply List.map_congr_left
  intro pk _
  by_cases h : pk.key = keyHash ∧ pk.reusable = false
  · simp [Function.comp, PreauthKey.toRecord, h]
  · simp [Function.comp, PreauthKey.toRecord, h]

/-- **No double-spend across a restart.** The durable log mints a live one-shot
key and records its spend (`keyConsumed`). A restarted coordinator that replays
this log recovers a store in which the key — viewed through the admission gate's
`KeyRecord` model — validates to `reject .exhausted`: a second registration with
the same secret is REJECTED. The one-shot property survives the restart. -/
theorem oneShot_rejected_after_restart
    (hash : Control.Bytes → Control.Bytes) (secret : Control.Bytes)
    (pk : PreauthKey) (now : Nat)
    (hkey : pk.key = hash secret) (hone : pk.reusable = false)
    (hrev : pk.revoked = false) (hlive : pk.expiry = 0 ∨ now ≤ pk.expiry) :
    Control.PreAuth.validate hash
        ((replay [.keyMinted pk, .keyConsumed pk.key]).preauth.map PreauthKey.toRecord)
        now secret
      = .reject .exhausted := by
  have hst : (replay [.keyMinted pk, .keyConsumed pk.key]).preauth = [{ pk with used := true }] := by
    simp [replay, CoordState.init, applyEvent, spendKey, hone]
  rw [hst]
  simp only [List.map_cons, List.map_nil]
  have hkh : ({ pk with used := true } : PreauthKey).toRecord.keyHash = hash secret := by
    simp [PreauthKey.toRecord, hkey]
  rw [Control.PreAuth.validate_cons_self hash secret now _ hkh]
  have hexp : ¬(0 < pk.expiry ∧ pk.expiry < now) := by
    rcases hlive with h | h <;> rintro ⟨h0, hlt⟩ <;> omega
  simp [Control.PreAuth.validateRec, PreauthKey.toRecord, hone, hrev, hexp]

/-- **The recovered one-shot key rejects a second registration.** Feeding the
replayed store to `registerWithPreAuth` (the proven admission gate) with the same
secret yields `MachineAuthorized = false` — the gate demonstrated end-to-end
across the restart. -/
theorem oneShot_register_rejected_after_restart
    (hash : Control.Bytes → Control.Bytes) (secret : Control.Bytes)
    (pk : PreauthKey) (s : ControlState) (now : Nat) (req : RegisterRequest)
    (hauth : req.authKey = secret)
    (hkey : pk.key = hash secret) (hone : pk.reusable = false)
    (hrev : pk.revoked = false) (hlive : pk.expiry = 0 ∨ now ≤ pk.expiry) :
    (Control.PreAuth.registerWithPreAuth hash
        ((replay [.keyMinted pk, .keyConsumed pk.key]).preauth.map PreauthKey.toRecord)
        s now req).response.machineAuthorized = false := by
  have hv : Control.PreAuth.validate hash
      ((replay [.keyMinted pk, .keyConsumed pk.key]).preauth.map PreauthKey.toRecord)
      now req.authKey = .reject .exhausted := by
    rw [hauth]; exact oneShot_rejected_after_restart hash secret pk now hkey hone hrev hlive
  exact (Control.PreAuth.preauth_reject hash _ s now req .exhausted hv).1

/-! ### §4.5  IPAM address stability across reconnect / restart-replay

The `addrAllocated` event carries the *resolved* address, and `applyEvent` stamps it onto
the node's registration. Replay therefore restores every node's SAME address — a node
never changes its IP across its separate register+map connections or a coordinator
restart. Distinctness across nodes is `Control.Ipam.liveAlloc_distinct` at the allocation
site; here we close the persistence half: what was allocated is what replays. -/

/-- **ADDRESS STABILITY (single node).** Registering a node and allocating it `ip`, then
replaying the log, restores a registration whose address is exactly the stamped `/32`
`ip` — for an ARBITRARY request and address. The node keeps its IP across a
restart-replay (and, live, across its separate register/map connections which each replay
this same durable log). -/
theorem addrAllocated_stable (req : RegisterRequest) (ip : Nat) :
    (lookupReg (replay [.nodeRegistered req true, .addrAllocated req.nodeKey ip]).control.nodes
        req.nodeKey).map (fun r => r.node.addresses)
      = some [Control.Ipam.v4Prefix ip] := by
  simp [replay, CoordState.init, ControlState.init, applyEvent, mapNode, upsertReg,
    lookupReg, Control.Ipam.stampV4]

/-! A concrete two-node run — distinct keys, distinct allocated addresses — witnesses that
BOTH nodes keep their DISTINCT addresses after both register+allocate and a replay: the
multi-node stability the live coordinator relies on (driven through the REAL `replay`). -/

/-- Two distinct node keys and the two addresses a fresh CGNAT pool hands them. -/
def dkeyX : NodeKey := ⟨List.replicate 32 0x11⟩
def dkeyY : NodeKey := ⟨List.replicate 32 0x22⟩
def dReqX : RegisterRequest :=
  { version := 1, nodeKey := dkeyX, oldNodeKey := ⟨[]⟩, machineKey := ⟨List.replicate 32 0x1a⟩,
    authKey := [], expiry := 0, ephemeral := false, followup := false }
def dReqY : RegisterRequest :=
  { version := 1, nodeKey := dkeyY, oldNodeKey := ⟨[]⟩, machineKey := ⟨List.replicate 32 0x2b⟩,
    authKey := [], expiry := 0, ephemeral := false, followup := false }

/-- The durable log of a 2-node tailnet: each node registered then IPAM-allocated its
address (X→100.64.0.1, Y→100.64.0.2, the fresh-pool sequence). -/
def dLog : List Event :=
  [ .nodeRegistered dReqX true, .addrAllocated dkeyX Control.Ipam.ip1,
    .nodeRegistered dReqY true, .addrAllocated dkeyY Control.Ipam.ip2 ]

/-- **TWO NODES, DISTINCT + STABLE ADDRESSES.** After both register and both allocate,
replaying the durable log gives X its `100.64.0.1/32` and Y its `100.64.0.2/32` — distinct
and each stable — through the REAL `replay`. -/
theorem dLog_distinct_stable :
    ((lookupReg (replay dLog).control.nodes dkeyX).map (fun r => r.node.addresses)
      = some [{ addr := [100, 64, 0, 1], bits := 32 }])
    ∧ ((lookupReg (replay dLog).control.nodes dkeyY).map (fun r => r.node.addresses)
      = some [{ addr := [100, 64, 0, 2], bits := 32 }]) := by decide

/-! ## §5  The log codec — total encode/decode with a round-trip

Reuses `Control`'s self-delimiting field codecs. Each event is a one-byte tag
followed by its fields' self-delimiting encodings; the log is a length-prefixed
sequence (`putSeq`/`getSeq`). -/

/-- A pre-auth key codec — the FULL rich schema (keyHash + reusable/ephemeral/
expiry/tags/user + the used/revoked bits), self-delimiting field by field. -/
def putPreauth (pk : PreauthKey) : Bytes :=
  putBytes pk.key ++ putBool pk.reusable ++ putBool pk.used ++
    putBool pk.ephemeral ++ putNat pk.expiry ++ putSeq putBytes pk.tags ++
    putNat pk.user ++ putBool pk.revoked
def getPreauth (bs : Bytes) : Option (PreauthKey × Bytes) := do
  let (key, r) ← getBytes bs
  let (reusable, r) ← getBool r
  let (used, r) ← getBool r
  let (ephemeral, r) ← getBool r
  let (expiry, r) ← getNat r
  let (tags, r) ← getSeq getBytes r
  let (user, r) ← getNat r
  let (revoked, r) ← getBool r
  some (⟨key, reusable, used, ephemeral, expiry, tags, user, revoked⟩, r)
theorem getPreauth_put (pk : PreauthKey) (t : Bytes) :
    getPreauth (putPreauth pk ++ t) = some (pk, t) := by
  obtain ⟨key, reusable, used, ephemeral, expiry, tags, user, revoked⟩ := pk
  simp [putPreauth, getPreauth, List.append_assoc, getBytes_putBytes, getBool_putBool,
    getNat_putNat, getSeq_putSeq putBytes getBytes getBytes_putBytes]

/-- Encode one event: tag byte + fields. -/
def putEvent : Event → Bytes
  | .nodeRegistered req ok  => (0 : UInt8) :: (putRegReq req ++ putBool ok)
  | .nodeExpired now        => (1 : UInt8) :: putNat now
  | .nodeExpirySet nk exp    => (11 : UInt8) :: (putNodeKey nk ++ putNat exp)
  | .keyRotated old new     => (2 : UInt8) :: (putNodeKey old ++ putNodeKey new)
  | .nodeReaped nk          => (3 : UInt8) :: putNodeKey nk
  | .keyMinted pk           => (4 : UInt8) :: putPreauth pk
  | .keyConsumed kh         => (9 : UInt8) :: putBytes kh
  | .routesAdvertised nk rs => (5 : UInt8) :: (putNodeKey nk ++ putSeq putPrefix rs)
  | .routeApproved nk ap    => (6 : UInt8) :: (putNodeKey nk ++ putSeq putPrefix ap)
  | .filterSet pf           => (7 : UInt8) :: putFilter pf
  | .dnsSet d               => (8 : UInt8) :: putDns d
  | .addrAllocated nk ip    => (10 : UInt8) :: (putNodeKey nk ++ putNat ip)
  | .nodeTagsSet nk tags    => (12 : UInt8) :: (putNodeKey nk ++ putSeq putBytes tags)
  | .nodeUserSet nk user    => (13 : UInt8) :: (putNodeKey nk ++ putNat user)

/-- Decode one event off the front of the byte stream. Total: an unknown tag or a
truncated field yields `none`. -/
def getEvent : Bytes → Option (Event × Bytes)
  | [] => none
  | tag :: rest =>
    match tag with
    | 0 => do let (req, r) ← getRegReq rest; let (ok, r) ← getBool r; some (.nodeRegistered req ok, r)
    | 1 => do let (now, r) ← getNat rest; some (.nodeExpired now, r)
    | 11 => do let (nk, r) ← getNodeKey rest; let (exp, r) ← getNat r; some (.nodeExpirySet nk exp, r)
    | 2 => do let (old, r) ← getNodeKey rest; let (new, r) ← getNodeKey r; some (.keyRotated old new, r)
    | 3 => do let (nk, r) ← getNodeKey rest; some (.nodeReaped nk, r)
    | 4 => do let (pk, r) ← getPreauth rest; some (.keyMinted pk, r)
    | 5 => do let (nk, r) ← getNodeKey rest; let (rs, r) ← getSeq getPrefix r; some (.routesAdvertised nk rs, r)
    | 6 => do let (nk, r) ← getNodeKey rest; let (ap, r) ← getSeq getPrefix r; some (.routeApproved nk ap, r)
    | 7 => do let (pf, r) ← getFilter rest; some (.filterSet pf, r)
    | 8 => do let (d, r) ← getDns rest; some (.dnsSet d, r)
    | 9 => do let (kh, r) ← getBytes rest; some (.keyConsumed kh, r)
    | 10 => do let (nk, r) ← getNodeKey rest; let (ip, r) ← getNat r; some (.addrAllocated nk ip, r)
    | 12 => do let (nk, r) ← getNodeKey rest; let (ts, r) ← getSeq getBytes r; some (.nodeTagsSet nk ts, r)
    | 13 => do let (nk, r) ← getNodeKey rest; let (u, r) ← getNat r; some (.nodeUserSet nk u, r)
    | _ => none

/-- **Per-event round-trip.** Encoding an event then decoding recovers it and
leaves the trailing bytes untouched. -/
theorem getEvent_put (e : Event) (t : Bytes) : getEvent (putEvent e ++ t) = some (e, t) := by
  cases e <;>
    simp [putEvent, getEvent, List.cons_append, List.append_assoc,
      getRegReq_put, getBool_putBool, getNat_putNat, getNodeKey_put, getPreauth_put,
      getBytes_putBytes, getFilter_put, getDns_put,
      getSeq_putSeq putPrefix getPrefix getPrefix_put,
      getSeq_putSeq putBytes getBytes getBytes_putBytes]

/-- Encode the whole log: a length-prefixed sequence of events. -/
def encodeLog (log : List Event) : Bytes := putSeq putEvent log
/-- Decode the whole log. -/
def decodeLog (bs : Bytes) : Option (List Event × Bytes) := getSeq getEvent bs

/-- **Log round-trip (with trailing bytes).** -/
theorem decodeLog_encodeLog_tail (log : List Event) (t : Bytes) :
    decodeLog (encodeLog log ++ t) = some (log, t) :=
  getSeq_putSeq putEvent getEvent getEvent_put log t

/-- **Log round-trip.** The bytes written to disk decode back to the same event
list — the encode/decode round-trip the store's durability rests on. -/
theorem decodeLog_encodeLog (log : List Event) :
    decodeLog (encodeLog log) = some (log, []) := by
  have := decodeLog_encodeLog_tail log []
  simpa using this

/-- **Replay is deterministic in the PERSISTED BYTES.** Two logs that serialize
to the same bytes replay to the same state. This is the real content behind
"replay is deterministic": it rests on `encodeLog` being INJECTIVE (via the
round-trip), so the state a restart reconstructs is a function of the disk
contents alone. A lossy encoder — one that dropped a field of an event — would
make this FALSE, which is exactly why `replay log = replay log` was not it. -/
theorem replay_deterministic {log log' : List Event}
    (h : encodeLog log = encodeLog log') : replay log = replay log' := by
  have h1 := decodeLog_encodeLog log
  have h2 := decodeLog_encodeLog log'
  rw [h] at h1
  have := h1.symm.trans h2
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact congrArg replay this.1

/-- **Replay survives a disk round-trip.** Encoding the log, persisting it,
reading it back, decoding, and replaying reconstructs the identical state. This
composes the codec round-trip with `restart_sound`: what is on disk replays to the
pre-restart state. -/
theorem replay_after_roundtrip (st : CoordState) (log : List Event)
    (h : Coherent st log) :
    (decodeLog (encodeLog log)).map (fun p => replay p.1) = some st := by
  rw [decodeLog_encodeLog]
  exact congrArg some (restart_sound st log h)

/-! ## §6  The APPEND-ONLY, torn-tail-tolerant on-disk format

`encodeLog` is a **count-prefixed** sequence: the number of events is written
first, so growing the log rewrites the whole file, and `decodeLog` is
all-or-nothing — one missing byte makes it `none`, the coordinator starts EMPTY,
and every node loses its address. That is measurably true of a live plane: a
435-byte store truncated to 434 bytes replays as `NODES (0)`. It is not what an
append-only log should do, and it is the state logic, not host glue, that decides
what a torn file means.

This section defines the format the coordinator actually persists:

* `putFrame` — one event as a **self-delimiting frame** (`putBytes (putEvent e)`:
  a length prefix, then the event's bytes). Appending an event to the file is
  literally appending its frame; nothing already written is rewritten, so the
  bytes at risk in a crash are the bytes of the event being appended.
* `recoverFrames` — a **total** recovery decoder. It consumes frames greedily and
  stops at the first one that does not decode *in full*. A torn tail costs
  exactly the torn frame and nothing before it.
* `encodeStore` / `recoverStore` — the same behind an 8-byte magic, with the
  pre-existing count-prefixed encoding still readable, so a store written by an
  older drorb loads unchanged (`recoverStore_legacy`).

The load-bearing theorems:

* `recoverFrames_encodeLogAppend` — round-trip: the tolerant decoder is **not**
  weaker than the strict one on well-formed input.
* `getFrame_take_lt` — **any** strict truncation of a frame fails to decode. This
  is why a tear is *detected* rather than mis-parsed into a bogus event; it rests
  on `readUvarint_take_lt`, that a strict prefix of a varint never reads.
* `recover_torn_write` / `replay_torn_write` — a coordinator SIGKILLed part-way
  through appending an event replays to **exactly** the state it had before that
  append. This is `restart_sound` extended over a torn tail, not weakened.
-/

/-- One event as a self-delimiting frame: a length prefix, then the event. -/
def putFrame (e : Event) : Bytes := putBytes (putEvent e)

/-- Read one frame: the length-prefixed blob must decode as an event with
**nothing left over**. A blob that is short, long, or carries an unknown tag is
`none` — the decoder never guesses. -/
def getFrame (bs : Bytes) : Option (Event × Bytes) :=
  match getBytes bs with
  | some (blob, rest) =>
      match getEvent blob with
      | some (e, []) => some (e, rest)
      | _ => none
  | none => none

/-- The append-only body: the frames, concatenated. No count prefix — appending
event `e` to a log on disk is appending `putFrame e`, full stop. -/
def encodeLogAppend (log : List Event) : Bytes := log.flatMap putFrame

/-- **A frame round-trips**, leaving the trailing bytes untouched. -/
theorem getFrame_putFrame (e : Event) (t : Bytes) :
    getFrame (putFrame e ++ t) = some (e, t) := by
  have he : getEvent (putEvent e) = some (e, []) := by
    simpa using getEvent_put e []
  simp [getFrame, putFrame, getBytes_putBytes, he]

/-- No bytes, no frame. -/
theorem getFrame_nil : getFrame ([] : Bytes) = none := rfl

/-! ### Termination: every decoded frame strictly shortens the input -/

/-- Reading a varint consumes at least one byte. -/
theorem readUvarint_shorter : ∀ (bs : Bytes) (n : Nat) (r : Bytes),
    readUvarint bs = some (n, r) → r.length < bs.length := by
  intro bs
  induction bs with
  | nil => intro n r h; simp [readUvarint] at h
  | cons b rest ih =>
    intro n r h
    simp only [readUvarint] at h
    by_cases hb : b.toNat < 128
    · rw [if_pos hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp
    · rw [if_neg hb] at h
      cases hr : readUvarint rest with
      | none => rw [hr] at h; simp at h
      | some p =>
        obtain ⟨m, rest'⟩ := p
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := ih m rest' hr
        simp only [List.length_cons]
        omega

/-- Reading a length-prefixed blob consumes at least one byte. -/
theorem getBytes_shorter (bs : Bytes) (blob rest : Bytes) :
    getBytes bs = some (blob, rest) → rest.length < bs.length := by
  intro h
  unfold getBytes at h
  cases hr : readUvarint bs with
  | none => rw [hr] at h; simp at h
  | some p =>
    obtain ⟨n, r⟩ := p
    rw [hr] at h
    dsimp only at h
    by_cases hn : n ≤ r.length
    · rw [if_pos hn] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have h1 := readUvarint_shorter bs n r hr
      have h2 : (r.drop n).length ≤ r.length := by
        simp only [List.length_drop]; omega
      omega
    · rw [if_neg hn] at h; simp at h

/-- Reading a frame consumes at least one byte — the measure `recoverFrames`
recurses on. -/
theorem getFrame_shorter (bs : Bytes) (e : Event) (rest : Bytes) :
    getFrame bs = some (e, rest) → rest.length < bs.length := by
  intro h
  unfold getFrame at h
  cases hb : getBytes bs with
  | none => rw [hb] at h; simp at h
  | some p =>
    obtain ⟨blob, r⟩ := p
    rw [hb] at h
    dsimp only at h
    cases he : getEvent blob with
    | none => rw [he] at h; simp at h
    | some q =>
      obtain ⟨ev, tl⟩ := q
      rw [he] at h
      cases tl with
      | nil =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact getBytes_shorter bs blob r hb
      | cons _ _ => simp at h

/-- **The recovery decoder.** Consume frames greedily; stop at the first one that
does not decode in full. Total, and defined for *every* byte string — including a
torn one. -/
def recoverFrames (bs : Bytes) : List Event :=
  match hm : getFrame bs with
  | none => []
  | some (e, rest) =>
      have : rest.length < bs.length := getFrame_shorter bs e rest hm
      e :: recoverFrames rest
termination_by bs.length

theorem recoverFrames_none {bs : Bytes} (h : getFrame bs = none) :
    recoverFrames bs = [] := by
  rw [recoverFrames]; split <;> simp_all

theorem recoverFrames_some {bs rest : Bytes} {e : Event}
    (h : getFrame bs = some (e, rest)) :
    recoverFrames bs = e :: recoverFrames rest := by
  rw [recoverFrames]; split <;> simp_all

/-! ### Torn tails: a strict truncation of a frame never decodes -/

/-- **A strict prefix of a varint never reads.** The continuation bit is what
makes this true: every byte but the last has its high bit set, so a truncated
varint runs off the end of the input. -/
theorem readUvarint_take_lt : ∀ (n k : Nat), k < (uvarint n).length →
    readUvarint ((uvarint n).take k) = none := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    rw [uvarint] at hk ⊢
    by_cases h : n < 128
    · rw [if_pos h] at hk ⊢
      have hk1 : k < 1 := by simpa using hk
      have : k = 0 := by omega
      subst this
      simp [readUvarint]
    · rw [if_neg h] at hk ⊢
      cases k with
      | zero => simp [readUvarint]
      | succ j =>
        simp only [List.length_cons] at hk
        have hlt : n % 128 < 128 := Nat.mod_lt _ (by omega)
        have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
          rw [UInt8.toNat_ofNat']; omega
        have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
        simp only [List.take_succ_cons, readUvarint, hb]
        rw [if_neg (by omega), ih (n / 128) hdiv j (by omega)]

/-- `take` past a prefix: proved locally, so no core lemma name is guessed. -/
theorem take_append_le {α} (l1 l2 : List α) (k : Nat) (h : k ≤ l1.length) :
    (l1 ++ l2).take k = l1.take k := by
  induction l1 generalizing k with
  | nil => have : k = 0 := Nat.le_zero.mp (by simpa using h); subst this; simp
  | cons a as ih =>
      cases k with
      | zero => simp
      | succ j =>
          simp only [List.cons_append, List.take_succ_cons, List.length_cons] at *
          rw [ih j (by omega)]

theorem take_append_ge {α} (l1 l2 : List α) (k : Nat) (h : l1.length ≤ k) :
    (l1 ++ l2).take k = l1 ++ l2.take (k - l1.length) := by
  induction l1 generalizing k with
  | nil => simp
  | cons a as ih =>
      cases k with
      | zero => simp only [List.length_cons] at h; omega
      | succ j =>
          simp only [List.cons_append, List.take_succ_cons, List.length_cons] at *
          rw [ih j (by omega)]
          simp

/-- **A strict truncation of a length-prefixed blob never reads.** Either the
length varint itself is cut (nothing reads) or the declared length exceeds what
is left (the `n ≤ rest.length` guard fails). -/
theorem getBytes_take_lt (b : Bytes) (k : Nat) (hk : k < (putBytes b).length) :
    getBytes ((putBytes b).take k) = none := by
  simp only [putBytes, List.length_append] at hk ⊢
  by_cases h : k < (uvarint b.length).length
  · have hsplit : (uvarint b.length ++ b).take k = (uvarint b.length).take k := by
      exact take_append_le _ _ k (Nat.le_of_lt h)
    rw [hsplit]
    unfold getBytes
    rw [readUvarint_take_lt b.length k h]
  · have hge : (uvarint b.length).length ≤ k := by omega
    have hsplit : (uvarint b.length ++ b).take k
        = uvarint b.length ++ b.take (k - (uvarint b.length).length) := by
      exact take_append_ge _ _ k hge
    rw [hsplit]
    unfold getBytes
    rw [uvarint_roundtrip b.length (b.take (k - (uvarint b.length).length))]
    dsimp only
    have hlen : (b.take (k - (uvarint b.length).length)).length < b.length := by
      simp only [List.length_take]; omega
    rw [if_neg (Nat.not_le.mpr hlen)]

/-- **A strict truncation of a frame never decodes.** The torn tail is *detected*,
never mis-parsed into a spurious event. -/
theorem getFrame_take_lt (e : Event) (k : Nat) (hk : k < (putFrame e).length) :
    getFrame ((putFrame e).take k) = none := by
  have h := getBytes_take_lt (putEvent e) k (by simpa [putFrame] using hk)
  simp [getFrame, putFrame, h]

/-! ### The recovery theorems -/

/-- **Recovery over a well-framed log plus an unreadable tail.** Everything framed
before the tail is recovered, in order. -/
theorem recoverFrames_append (log : List Event) (t : Bytes) (ht : getFrame t = none) :
    recoverFrames (encodeLogAppend log ++ t) = log := by
  induction log with
  | nil => simpa [encodeLogAppend] using recoverFrames_none ht
  | cons e es ih =>
      have hsplit : encodeLogAppend (e :: es) ++ t
          = putFrame e ++ (encodeLogAppend es ++ t) := by
        simp [encodeLogAppend, List.append_assoc]
      rw [hsplit, recoverFrames_some (getFrame_putFrame e (encodeLogAppend es ++ t)), ih]

/-- **Round-trip.** The tolerant decoder is not weaker than the strict one: on a
complete file it returns exactly the log that was written. -/
theorem recoverFrames_encodeLogAppend (log : List Event) :
    recoverFrames (encodeLogAppend log) = log := by
  simpa using recoverFrames_append log [] getFrame_nil

/-- ★**TORN WRITE.** A coordinator killed part-way through appending event `e` —
`k` bytes of `putFrame e` reached the disk, for **any** `k` short of the whole
frame — recovers exactly the log it had before that append. Nothing already
written is lost, and the half-written event is not invented. -/
theorem recover_torn_write (log : List Event) (e : Event) (k : Nat)
    (hk : k < (putFrame e).length) :
    recoverFrames (encodeLogAppend log ++ (putFrame e).take k) = log :=
  recoverFrames_append log _ (getFrame_take_lt e k hk)

/-- ★**TORN WRITE, at the state level.** Composing `recover_torn_write` with
`restart_sound`: the state a coordinator reconstructs after being SIGKILLed
mid-append is *exactly* its pre-append in-memory state. Every node keeps the
address it was durably allocated. -/
theorem replay_torn_write (st : CoordState) (log : List Event) (h : Coherent st log)
    (e : Event) (k : Nat) (hk : k < (putFrame e).length) :
    replay (recoverFrames (encodeLogAppend log ++ (putFrame e).take k)) = st := by
  rw [recover_torn_write log e k hk]
  exact restart_sound st log h

/-! ### The on-disk store: magic + framed body, with the legacy format still read -/

/-- The 8-byte store magic: `FF FF D R O R B 1`. A leading `FF FF` cannot begin
any log the legacy count-prefixed encoder would ever emit at a realistic size, so
the two formats are told apart by the first bytes alone. -/
def storeMagic : Bytes := [0xFF, 0xFF, 0x44, 0x52, 0x4F, 0x52, 0x42, 0x31]

/-- The bytes a coordinator writes: magic, then the append-only frames. -/
def encodeStore (log : List Event) : Bytes := storeMagic ++ encodeLogAppend log

/-- **What a file on disk means.** A magic-prefixed file is recovered frame by
frame (torn-tail tolerant); anything else is read with the legacy
count-prefixed decoder, so an old store still loads; an undecodable legacy file
is the empty log, as before. -/
def recoverStore (bs : Bytes) : List Event :=
  if storeMagic.isPrefixOf bs then recoverFrames (bs.drop storeMagic.length)
  else match decodeLog bs with
       | some (log, _) => log
       | none => []

/-- **Store round-trip.** -/
theorem recoverStore_encodeStore (log : List Event) :
    recoverStore (encodeStore log) = log := by
  have hpre : storeMagic.isPrefixOf (encodeStore log) = true := by
    simp [encodeStore, storeMagic, List.isPrefixOf]
  have hdrop : (encodeStore log).drop storeMagic.length = encodeLogAppend log := by
    simp [encodeStore, storeMagic]
  simp only [recoverStore, hpre, if_true, hdrop, recoverFrames_encodeLogAppend]

/-- ★**A torn store still loads.** The magic survives the tear (it is written
first and never rewritten), so the file is read as frames and everything durably
appended before the tear is recovered. -/
theorem recoverStore_torn_write (log : List Event) (e : Event) (k : Nat)
    (hk : k < (putFrame e).length) :
    recoverStore (encodeStore log ++ (putFrame e).take k) = log := by
  have hpre : storeMagic.isPrefixOf (encodeStore log ++ (putFrame e).take k) = true := by
    simp [encodeStore, storeMagic, List.isPrefixOf]
  have hdrop : (encodeStore log ++ (putFrame e).take k).drop storeMagic.length
      = encodeLogAppend log ++ (putFrame e).take k := by
    simp [encodeStore, storeMagic]
  simp only [recoverStore, hpre, if_true, hdrop, recover_torn_write log e k hk]

/-- **The legacy format still loads.** A store written by the count-prefixed
encoder (no magic) is read by `decodeLog`, unchanged. -/
theorem recoverStore_legacy (log : List Event)
    (h : storeMagic.isPrefixOf (encodeLog log) = false) :
    recoverStore (encodeLog log) = log := by
  simp [recoverStore, h, decodeLog_encodeLog]

/-- ★**The state after a torn write.** The end-to-end statement the operator
cares about: SIGKILL the coordinator mid-append, restart it, and the registry it
serves is the one it had before the append — the same conclusion `restart_sound`
gives for a clean stop. -/
theorem restart_sound_torn (st : CoordState) (log : List Event) (h : Coherent st log)
    (e : Event) (k : Nat) (hk : k < (putFrame e).length) :
    replay (recoverStore (encodeStore log ++ (putFrame e).take k)) = st := by
  rw [recoverStore_torn_write log e k hk]
  exact restart_sound st log h

/-! ### §7  What the COMMIT PATH actually writes (`Control.Durable`)

Every theorem above is stated over `encodeStore log` — the whole store as one
blob. The coordinator never writes that blob. After the one-off migration at
startup it has a store holding `prior` on disk and it APPENDS only the new
frames (`ControlLive.storeAppend` -> `Control.Durable.commitAppend`), so the byte
string it produces is `encodeStore prior ++ encodeLogAppend new` — a shape none
of the recovery theorems mentioned. These lemmas close that gap, so the
durability argument (which bytes are on stable storage) and the replay argument
(what those bytes mean) are about the same object.

They also fix what a POWER CUT is allowed to do. `Control.Durable.commitAppend`
forces the file, so once it returns the appended frames are on stable storage; a
cut DURING it leaves a PREFIX of the frames it was writing, which is the `take k`
hypothesis below. That the interrupted state is a prefix and not arbitrary
garbage is a property of the filesystem (an ordered-data journal writes the data
blocks before the size that exposes them), not something proved here — it is
named as the assumption it is in `Control.Durable`.
-/

/-- **Appending frames to a store IS the store of the appended log.** The one
rewriting step that lets an `O_APPEND` commit be read by the whole-store theorems. -/
theorem encodeStore_append (prior new : List Event) :
    encodeStore prior ++ encodeLogAppend new = encodeStore (prior ++ new) := by
  simp [encodeStore, encodeLogAppend, List.append_assoc]

/-- **THE APPEND COMMIT.** A store holding `prior` with `encodeLogAppend new`
appended to it — exactly the bytes `Control.Durable.commitAppend` adds, and
exactly the bytes that are on stable storage when it returns — recovers as
`prior ++ new`. -/
theorem recoverStore_append (prior new : List Event) :
    recoverStore (encodeStore prior ++ encodeLogAppend new) = prior ++ new := by
  rw [encodeStore_append]; exact recoverStore_encodeStore _

/-- **THE APPEND COMMIT, INTERRUPTED.** A cut part-way through the append — `k`
bytes of the frame it was writing reached the disk, for any `k` short of the
whole — still recovers every event committed before it. This is the statement the
`fsync` makes worth having: what came before the tear is not merely "written",
it is DURABLE. -/
theorem recoverStore_append_torn (prior new : List Event) (e : Event) (k : Nat)
    (hk : k < (putFrame e).length) :
    recoverStore (encodeStore prior ++ encodeLogAppend new ++ (putFrame e).take k)
      = prior ++ new := by
  rw [encodeStore_append]; exact recoverStore_torn_write (prior ++ new) e k hk

/-- **STATE AFTER AN INTERRUPTED APPEND COMMIT.** The operator-level conclusion:
a coordinator coherent at `prior`, which appended the batch `new` and was then
cut off mid-way through a further frame, comes back up in exactly the state it
would have reached by applying `new` — no more, no less. -/
theorem restart_sound_append_torn (st : CoordState) (prior new : List Event)
    (h : Coherent st prior) (e : Event) (k : Nat) (hk : k < (putFrame e).length) :
    replay (recoverStore (encodeStore prior ++ encodeLogAppend new ++ (putFrame e).take k))
      = new.foldl applyEvent st := by
  rw [recoverStore_append_torn prior new e k hk, h]
  simp [replay, List.foldl_append]

end Control.Store

/-! ## Axiom / vacuity audit

`replay_deterministic` used to read `replay log = replay log`. It is now
determinism in the PERSISTED BYTES, which rests on `encodeLog` being injective.
`#assert_nonvacuous` keeps it that way. -/

#assert_nonvacuous Control.Store.replay_deterministic

#print axioms Control.Store.decodeLog_encodeLog
#print axioms Control.Store.restart_sound
#print axioms Control.Store.replay_recovers_key
#print axioms Control.Store.spendKey_toRecord
#print axioms Control.Store.oneShot_rejected_after_restart
#print axioms Control.Store.oneShot_register_rejected_after_restart
#print axioms Control.Store.getPreauth_put
#print axioms Control.Store.getEvent_put
#print axioms Control.Store.addrAllocated_stable
#print axioms Control.Store.dLog_distinct_stable

-- §6: the append-only, torn-tail-tolerant on-disk format.
#print axioms Control.Store.getFrame_putFrame
#print axioms Control.Store.readUvarint_take_lt
#print axioms Control.Store.getFrame_take_lt
#print axioms Control.Store.recoverFrames_encodeLogAppend
#print axioms Control.Store.recover_torn_write
#print axioms Control.Store.replay_torn_write
#print axioms Control.Store.recoverStore_encodeStore
#print axioms Control.Store.recoverStore_torn_write
#print axioms Control.Store.recoverStore_legacy
#print axioms Control.Store.restart_sound_torn

-- §7: the shape the DURABLE commit path (`Control.Durable`) actually writes.
#print axioms Control.Store.encodeStore_append
#print axioms Control.Store.recoverStore_append
#print axioms Control.Store.recoverStore_append_torn
#print axioms Control.Store.restart_sound_append_torn
#assert_nonvacuous Control.Store.recoverStore_append
#assert_nonvacuous Control.Store.restart_sound_append_torn

-- Runtime evidence: the durable 2-node log replays to distinct, stable addresses, and the
-- addr event survives the disk codec round-trip.
#guard (Control.lookupReg (Control.Store.replay Control.Store.dLog).control.nodes Control.Store.dkeyX).map (fun r => r.node.addresses)
  == some [{ addr := [100, 64, 0, 1], bits := 32 }]
#guard (Control.lookupReg (Control.Store.replay Control.Store.dLog).control.nodes Control.Store.dkeyY).map (fun r => r.node.addresses)
  == some [{ addr := [100, 64, 0, 2], bits := 32 }]
#guard Control.Store.decodeLog (Control.Store.encodeLog Control.Store.dLog) == some (Control.Store.dLog, [])

-- ★TORN TAIL, as runtime evidence on the real 2-node durable log.
-- What the OLD count-prefixed format did with a ONE-byte tear: lose EVERYTHING.
-- (This is the live failure: a 435-byte store truncated to 434 replayed as NODES (0).)
#guard Control.Store.decodeLog
    ((Control.Store.encodeLog Control.Store.dLog).take
      ((Control.Store.encodeLog Control.Store.dLog).length - 1)) == none
-- What the framed store does with the same tear: lose EXACTLY the torn last frame,
-- and keep every event before it.
#guard Control.Store.recoverStore (Control.Store.encodeStore Control.Store.dLog) == Control.Store.dLog
#guard Control.Store.recoverStore
    ((Control.Store.encodeStore Control.Store.dLog).take
      ((Control.Store.encodeStore Control.Store.dLog).length - 1)) == Control.Store.dLog.dropLast
-- A half-written APPEND of a further event costs exactly that event: `nodeExpired 7`
-- frames to 3 bytes, so 2 of them on disk is a torn append and replays to dLog.
#guard (Control.Store.putFrame (Control.Store.Event.nodeExpired 7)).length == 3
#guard Control.Store.recoverStore (Control.Store.encodeStore Control.Store.dLog
    ++ (Control.Store.putFrame (Control.Store.Event.nodeExpired 7)).take 2) == Control.Store.dLog
-- ... and the COMPLETE append is of course kept.
#guard Control.Store.recoverStore (Control.Store.encodeStore Control.Store.dLog
    ++ Control.Store.putFrame (Control.Store.Event.nodeExpired 7))
  == Control.Store.dLog ++ [Control.Store.Event.nodeExpired 7]
-- And a store written by an older drorb still loads unchanged.
#guard Control.Store.recoverStore (Control.Store.encodeLog Control.Store.dLog) == Control.Store.dLog
