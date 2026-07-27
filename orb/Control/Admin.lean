import Control.Store
import Control.PreAuthKey
import Control.Register

/-!
# Control.Admin — the operator admin surface (a headscale-style control plane)

A homelab operator running a drorb tailnet needs the same day-to-day controls a
headscale operator has: *list the nodes*, *expire* or *delete* one, *mint* and
*list* pre-auth keys, *list* advertised subnet routes, *list* users. This module
models each of those operations over the coordinator's durable state
(`Control.Store.CoordState` — the replayed event log: registry + minted keys),
cross-checked against the PUBLIC headscale CLI:

  | drorb-ctl                    | headscale (`cmd/headscale/cli`)                     |
  |------------------------------|-----------------------------------------------------|
  | `nodes list`                 | `headscale nodes list` (`nodes.go`, aliases ls/show)|
  | `nodes register --key ...`   | `headscale nodes register --user --key` (`nodes.go`)|
  | `nodes expire <key>`         | `headscale nodes expire -i` (`nodes.go`, alias exp) |
  | `nodes delete <key>`         | `headscale nodes delete -i` (`nodes.go`, alias del) |
  | `preauthkeys create ...`     | `headscale preauthkeys create --reusable --ephemeral --expiration --tags --user` (`preauthkeys.go`) |
  | `preauthkeys list`           | `headscale preauthkeys list` (`preauthkeys.go`)     |
  | `routes list`                | `headscale routes list` / `nodes list-routes`       |
  | `users list`                 | `headscale users list`                              |

## Durability

Every **mutation** is modelled as a `Control.Store.Event`, so an admin action is
recorded in the same append-only log the live coordinator replays: an admin
change survives a restart exactly like a registration does (`Store.restart_sound`).
This file NEVER edits the Store schema — it only *reads* the state and *emits*
events already in the `Store.Event` algebra:

  * `expireNode`  ↦ `Event.nodeExpired now`   (the clock-driven key-expiry model:
    a node whose key expiry has passed is `.expired` and must re-auth — the
    drorb analogue of headscale setting a node's `Expiry` to now);
  * `deleteNode`  ↦ `Event.nodeReaped nk`     (drop the registration);
  * `mintPreAuthKey` ↦ `Event.keyMinted pk`   (reuses `Control.PreAuth.mint`);

`listNodes` / `listKeys` / `listRoutes` / `listUsers` are pure **reads** of the
replayed `CoordState` — no event.

## Auth gate (IN SPIRIT — enforced at the transport, documented here)

The admin surface is PRIVILEGED: it mints credentials and expires nodes. It MUST
NOT be exposed unauthenticated. The intended deployment sits it behind the same
PBKDF2 (`PbkdfHashTool` / `Control.BasicAuth`) basic-auth the operator API uses,
or a bearer token — never open. `drorb-ctl` is the *local* CLI (it reads/writes
the store log on the operator's host, a filesystem-permission boundary); any
*network* exposure of these operations inherits the basic-auth/token gate. See
`AdminAuthNote` below.
-/

namespace Control.Admin

open Control Control.Store Control.PreAuth

/-! ## §-1  Advertised subnet routes (mirrors `advertisedRoutes`)

Inlined here — verbatim the `advertisedRoutes` formula (a node's
`allowedIPs` minus its own `addresses`) — so the admin surface does not import the
route-approval lane's file (kept decoupled from that lane's in-flight work). The
approval theorems (`Control.Routes.route_needs_approval`) still govern which of
these are ever *distributed*; `routes list` reports what a node *advertises*. -/
def advertisedRoutes (n : Node) : List Prefix :=
  n.allowedIPs.filter (fun p => ! n.addresses.contains p)

/-! ## §0  The auth-gate obligation (documentation as a proposition)

A machine-checkable reminder that the admin surface is privileged. This is not a
runtime enforcement (that lives at the transport, `Control.BasicAuth`); it records
the contract that a deployment must satisfy before serving any admin operation. -/

/-- The deployment contract for the admin surface: it is only ever served behind
an authenticator. Instantiated by a concrete deployment with its PBKDF2 basic-auth
or token check; kept abstract here so the model does not presuppose one scheme. -/
structure AdminAuthNote where
  /-- Is the caller authenticated (PBKDF2 basic-auth verified, or a valid token)? -/
  authenticated : Bool
  /-- The contract: no admin operation runs unless the caller is authenticated. -/
  gated : authenticated = true

/-! ## §1  A small registry-lookup toolkit

`lookupReg` (in `Control`) is first-match by node key. We need two facts about it
that the foundation did not export: a successful lookup's target is in the list,
and a key-preserving map commutes with lookup. -/

/-- A successful `lookupReg` returns a registration that is actually a member. -/
theorem lookupReg_mem : ∀ (l : List Registration) (nk : NodeKey) (r : Registration),
    lookupReg l nk = some r → r ∈ l := by
  intro l
  induction l with
  | nil => intro nk r h; simp [lookupReg] at h
  | cons a t ih =>
    intro nk r h
    simp only [lookupReg] at h
    by_cases ha : a.nodeKey = nk
    · rw [if_pos ha] at h
      simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · rw [if_neg ha] at h; exact List.mem_cons_of_mem _ (ih nk r h)

/-- **Lookup commutes with a key-preserving map.** If `f` never changes a
registration's node key, then looking a key up in `l.map f` finds `f` applied to
whatever the same key found in `l`. This is the shape both `expire` (status-only)
and any per-node rewrite share. -/
theorem lookupReg_map_keyPreserving (f : Registration → Registration)
    (hf : ∀ r, (f r).nodeKey = r.nodeKey) :
    ∀ (l : List Registration) (nk : NodeKey) (r : Registration),
      lookupReg l nk = some r → lookupReg (l.map f) nk = some (f r) := by
  intro l
  induction l with
  | nil => intro nk r h; simp [lookupReg] at h
  | cons a t ih =>
    intro nk r h
    simp only [lookupReg] at h
    simp only [List.map_cons, lookupReg]
    by_cases ha : a.nodeKey = nk
    · rw [if_pos ha] at h
      simp only [Option.some.injEq] at h; subst h
      rw [if_pos (by rw [hf a]; exact ha)]
    · rw [if_neg ha] at h
      rw [if_neg (by rw [hf a]; exact ha)]
      exact ih nk r h

/-! ## §2  `nodes list` — read the registry off the replayed state

headscale `nodes list` (`cmd/headscale/cli/nodes.go`, aliases `ls`/`show`). -/

/-- One row of `nodes list`: the operator-visible view of a registration
(the columns headscale prints — node key, addresses, tags, user, status, key
expiry, online — plus the advertised subnet routes, `Control.Routes`). -/
structure NodeView where
  nodeKey          : NodeKey
  addresses        : List Prefix
  tags             : List Bytes
  user             : Nat
  status           : NodeStatus
  keyExpiry        : Nat
  online           : Bool
  advertisedRoutes : List Prefix
deriving Repr

/-- The view of a single registration. -/
def viewOf (r : Registration) : NodeView :=
  { nodeKey := r.nodeKey, addresses := r.node.addresses, tags := r.node.tags,
    user := r.node.user, status := r.status, keyExpiry := r.node.keyExpiry,
    online := r.node.online, advertisedRoutes := advertisedRoutes r.node }

/-- **`nodes list`** — every registration, as an operator row, read from the
replayed coordination state. -/
def listNodes (st : CoordState) : List NodeView :=
  st.control.nodes.map viewOf

/-- **The listing is faithful.** Every registered node appears as exactly one
row carrying its own key/status/addresses/tags — `listNodes` neither drops nor
invents a node. -/
theorem listNodes_sound (st : CoordState) (nk : NodeKey) (r : Registration)
    (h : lookupReg st.control.nodes nk = some r) :
    viewOf r ∈ listNodes st
      ∧ (viewOf r).nodeKey = nk
      ∧ (viewOf r).status = r.status
      ∧ (viewOf r).addresses = r.node.addresses := by
  refine ⟨List.mem_map.mpr ⟨r, lookupReg_mem _ _ _ h, rfl⟩, ?_, rfl, rfl⟩
  exact Control.Register.lookupReg_nodeKey st.control.nodes nk r h

/-- **The listing has one row per registration.** -/
theorem listNodes_length (st : CoordState) :
    (listNodes st).length = st.control.nodes.length := by
  simp [listNodes]

/-! ## §3  `nodes register` — admit a node key (headscale `nodes register`)

headscale `nodes register --user --key` (`nodes.go`, deprecated in favour of
`auth register`, but the operator affordance). Emits the durable
`Event.nodeRegistered` — the SAME event the live coordinator records — with the
authorization decision resolved to `true` (the operator is admitting the key). -/

/-- The register event an operator-driven admit emits. -/
def registerNodeEvent (req : RegisterRequest) : Event :=
  .nodeRegistered req true

/-- The address-allocation event that stamps `ip` onto the just-registered node
(`Control.Ipam` — the operator hands the node its overlay `/32`). -/
def allocEvent (nk : NodeKey) (ip : Nat) : Event :=
  .addrAllocated nk ip

/-- **A registered node is listed, authorized.** After applying the register
event, the node key resolves to a row with status `.authorized` — it now shows in
`nodes list` as an admitted node. -/
theorem registerNodeEvent_lists_authorized (st : CoordState) (req : RegisterRequest) :
    (lookupReg (applyEvent st (registerNodeEvent req)).control.nodes req.nodeKey).map (·.status)
      = some .authorized := by
  simp [applyEvent, registerNodeEvent, upsertReg, lookupReg, nodeOf]

/-! ## §4  `nodes expire` — drop a node's authorization (headscale `nodes expire`)

headscale `nodes expire -i` (`nodes.go`, aliases `logout`/`exp`) expires a node's
key so it must re-authenticate. drorb models key expiry as clock-driven
(`tailcfg.Node.KeyExpiry`): once wall-clock `now` passes a node's nonzero
`keyExpiry`, `Register.expire` marks it `.expired`, and an `.expired` node gets NO
netmap (`Register.expired_gets_no_netmap`, composing `control_netmap_needs_authorized`).
The durable event is `Event.nodeExpired now`.

TARGETING: `expireNode` advances the clock past the target's own key expiry. A
node's expiry is per-node (`keyExpiry`), so a never-expiring node (`keyExpiry = 0`)
and any node whose expiry is still in the future are UNTOUCHED — the expire hits
exactly the keys that have passed. -/

/-- The durable expire event: advance the coordinator clock to `now`. -/
def expireNodeEvent (now : Nat) : Event :=
  .nodeExpired now

/-- `expireReg` never changes a registration's node key (it only flips status). -/
theorem expireReg_nodeKey (now : Nat) (r : Registration) :
    (Control.Register.expireReg now r).nodeKey = r.nodeKey := by
  simp only [Control.Register.expireReg]; split <;> rfl

/-- **The target is expired.** After `expireNodeEvent now`, a node whose key had a
nonzero expiry strictly before `now` resolves to status `.expired` — its
authorization is gone (`.expired.isAuthorized = false`), so it receives no
netmap. -/
theorem expireNode_target_expired (st : CoordState) (now : Nat) (nk : NodeKey)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r)
    (hexp : 0 < r.node.keyExpiry) (hlt : r.node.keyExpiry < now) :
    (lookupReg (applyEvent st (expireNodeEvent now)).control.nodes nk).map (·.status)
      = some .expired := by
  have hlk := lookupReg_map_keyPreserving (Control.Register.expireReg now)
    (expireReg_nodeKey now) st.control.nodes nk r h
  have hstatus : Control.Register.expireReg now r = { r with status := .expired } := by
    simp only [Control.Register.expireReg, if_pos (And.intro hexp hlt)]
  simp only [applyEvent, expireNodeEvent, Control.Register.expire]
  rw [hlk, hstatus]
  rfl

/-- **Expire is targeted: a never-expiring node is untouched.** A node with
`keyExpiry = 0` (headscale's "never expires") is returned unchanged by the very
same `expireNodeEvent now` — the operator expiring one node does not silently
expire the never-expiring ones. -/
theorem expireNode_preserves_never (st : CoordState) (now : Nat) (nk : NodeKey)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r)
    (h0 : r.node.keyExpiry = 0) :
    lookupReg (applyEvent st (expireNodeEvent now)).control.nodes nk = some r := by
  have hlk := lookupReg_map_keyPreserving (Control.Register.expireReg now)
    (expireReg_nodeKey now) st.control.nodes nk r h
  have hid : Control.Register.expireReg now r = r := by
    simp only [Control.Register.expireReg, h0]
    rw [if_neg]; rintro ⟨h1, _⟩; exact absurd h1 (by decide)
  simp only [applyEvent, expireNodeEvent, Control.Register.expire]
  rw [hlk, hid]

/-! ## §4.5  `nodes set-expiry` / `--disable-expiry` (headscale `nodes expire
--expiry` / `--disable`)

headscale `nodes expire` with `--expiry <rfc3339>` SETS a node's key expiry (and
`--disable`/`-d` sets it to "never"). drorb records this as `Event.nodeExpirySet nk
expiry`, stamping `keyExpiry := expiry` onto the node (`expiry = 0` ⇒
`--disable-expiry`, tailscale's zero-value "does not expire"). Combined with the
clock-driven `expireNodeEvent`, the operator can schedule, force, or disable expiry. -/

/-- The durable set-expiry event: stamp `expiry` (unix seconds; `0` = never) onto
node `nk`'s key. `--disable-expiry` is `setExpiryEvent nk 0`. -/
def setExpiryEvent (nk : NodeKey) (expiry : Nat) : Event :=
  .nodeExpirySet nk expiry

/-- `mapNode`'s per-registration function never changes a node key. -/
theorem setExpiry_mapNode_nodeKey (nk : NodeKey) (expiry : Nat) (x : Registration) :
    (if x.nodeKey = nk then { x with node := { x.node with keyExpiry := expiry } } else x).nodeKey
      = x.nodeKey := by
  split <;> rfl

/-- **set-expiry stamps the key expiry.** After `setExpiryEvent nk expiry`, node
`nk`'s `keyExpiry` is exactly `expiry` — so `setExpiryEvent nk 0` disables expiry
(never), and any nonzero value schedules a clock-driven expiry. -/
theorem setExpiryEvent_sets (st : CoordState) (nk : NodeKey) (expiry : Nat)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r) :
    (lookupReg (applyEvent st (setExpiryEvent nk expiry)).control.nodes nk).map (·.node.keyExpiry)
      = some expiry := by
  have hrk : r.nodeKey = nk := Control.Register.lookupReg_nodeKey st.control.nodes nk r h
  have hlk := lookupReg_map_keyPreserving
    (fun x => if x.nodeKey = nk then { x with node := { x.node with keyExpiry := expiry } } else x)
    (setExpiry_mapNode_nodeKey nk expiry) st.control.nodes nk r h
  simp only [applyEvent, setExpiryEvent, Control.Store.mapNode]
  rw [hlk]
  simp [hrk]

/-- **A never-expiring node is exactly `setExpiryEvent nk 0`.** The `--disable-expiry`
surface: after it, the node's `keyExpiry = 0`, so `Register.expire` leaves it
untouched at every clock (`expire_preserves_live`). -/
theorem setExpiryEvent_disable (st : CoordState) (nk : NodeKey)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r) :
    (lookupReg (applyEvent st (setExpiryEvent nk 0)).control.nodes nk).map (·.node.keyExpiry)
      = some 0 :=
  setExpiryEvent_sets st nk 0 r h

/-! ## §4b  `nodes tag` — SET a node's ACL tags (headscale `nodes tag -t`)

headscale `nodes tag --identifier <id> --tags tag:a,tag:b` (`cmd/headscale/cli/nodes.go`)
replaces a node's ACL tags. drorb records `Event.nodeTagsSet nk tags` — the resolved tag
list, so replay is deterministic and the tags survive a restart
(`Control.Store.restart_sound`).

★A stamped tag is a CLAIM, not an authority. Whether `tag:x` on this node lets anyone
reach it is decided at ACL-compile time by `Control.Tags.tagBindings`, which drops every
tag the node's OWNING USER is not a `tagOwner` of (`Control.Tags.tagBindings_owned`). So
this command cannot grant reachability the policy did not authorize — which is exactly
why the operator surface is allowed to be this blunt. -/

/-- The durable set-tags event: replace node `nk`'s ACL tags with `tags`. -/
def setTagsEvent (nk : NodeKey) (tags : List Bytes) : Event :=
  .nodeTagsSet nk tags

/-- `mapNode`'s per-registration function never changes a node key. -/
theorem setTags_mapNode_nodeKey (nk : NodeKey) (tags : List Bytes) (x : Registration) :
    (if x.nodeKey = nk then { x with node := { x.node with tags := tags } } else x).nodeKey
      = x.nodeKey := by
  split <;> rfl

/-- **`nodes tag` stamps exactly the given tags.** After `setTagsEvent nk tags`, node
`nk`'s `Node.tags` is `tags` — which is what `nodes list` prints and what the netmap and
the ACL tag projection read. -/
theorem setTagsEvent_sets (st : CoordState) (nk : NodeKey) (tags : List Bytes)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r) :
    (lookupReg (applyEvent st (setTagsEvent nk tags)).control.nodes nk).map (·.node.tags)
      = some tags := by
  have hrk : r.nodeKey = nk := Control.Register.lookupReg_nodeKey st.control.nodes nk r h
  have hlk := lookupReg_map_keyPreserving
    (fun x => if x.nodeKey = nk then { x with node := { x.node with tags := tags } } else x)
    (setTags_mapNode_nodeKey nk tags) st.control.nodes nk r h
  simp only [applyEvent, setTagsEvent, Control.Store.mapNode]
  rw [hlk]
  simp [hrk]

/-- **…and `nodes list` shows them.** The operator sees what was stamped: the
`NodeView` for `nk` carries exactly `tags` after the event. -/
theorem setTagsEvent_listed (st : CoordState) (nk : NodeKey) (tags : List Bytes)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r) :
    ∃ v ∈ listNodes (applyEvent st (setTagsEvent nk tags)), v.nodeKey = nk ∧ v.tags = tags := by
  have hset := setTagsEvent_sets st nk tags r h
  cases hl : lookupReg (applyEvent st (setTagsEvent nk tags)).control.nodes nk with
  | none => rw [hl] at hset; simp at hset
  | some r' =>
    rw [hl] at hset
    have hmem : r' ∈ (applyEvent st (setTagsEvent nk tags)).control.nodes :=
      lookupReg_mem _ nk r' hl
    have hrk : r'.nodeKey = nk :=
      Control.Register.lookupReg_nodeKey _ nk r' hl
    exact ⟨viewOf r', List.mem_map.mpr ⟨r', hmem, rfl⟩, by simpa [viewOf] using hrk,
      by simpa [viewOf] using (by simpa using hset : r'.node.tags = tags)⟩

/-- **Setting an EMPTY tag list untags the node.** The `drorb-ctl nodes tag <n> -`
surface: after it the node claims nothing, so it binds to no `tag:` selector at all. -/
theorem setTagsEvent_clear (st : CoordState) (nk : NodeKey)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r) :
    (lookupReg (applyEvent st (setTagsEvent nk [])).control.nodes nk).map (·.node.tags)
      = some [] :=
  setTagsEvent_sets st nk [] r h

/-! ### `nodeUserSet` — the resolved owning user (the other half of enrolment)

`Event.nodeRegistered` replays through `Control.nodeOf`, which zeroes `user` and `tags`.
The live coordinator therefore emits `nodeUserSet` + `nodeTagsSet` alongside it with the
attributes the admitting pre-auth key carried. Together they make the *replayed* node
carry the owner and tags that `Control.PreAuth.preauth_admit` proves the in-memory
admission stamps — which is what `Control.Tags.tagBindings` then gates on. -/

/-- The durable set-user event. -/
def setUserEvent (nk : NodeKey) (user : Nat) : Event :=
  .nodeUserSet nk user

/-- `mapNode`'s per-registration function never changes a node key. -/
theorem setUser_mapNode_nodeKey (nk : NodeKey) (user : Nat) (x : Registration) :
    (if x.nodeKey = nk then { x with node := { x.node with user := user } } else x).nodeKey
      = x.nodeKey := by
  split <;> rfl

/-- **`nodeUserSet` stamps the owning user.** -/
theorem setUserEvent_sets (st : CoordState) (nk : NodeKey) (user : Nat)
    (r : Registration) (h : lookupReg st.control.nodes nk = some r) :
    (lookupReg (applyEvent st (setUserEvent nk user)).control.nodes nk).map (·.node.user)
      = some user := by
  have hrk : r.nodeKey = nk := Control.Register.lookupReg_nodeKey st.control.nodes nk r h
  have hlk := lookupReg_map_keyPreserving
    (fun x => if x.nodeKey = nk then { x with node := { x.node with user := user } } else x)
    (setUser_mapNode_nodeKey nk user) st.control.nodes nk r h
  simp only [applyEvent, setUserEvent, Control.Store.mapNode]
  rw [hlk]
  simp [hrk]

/-- A per-node rewrite, seen through `lookupReg`: looking the same key up after
`mapNode nk f` finds the SAME registration with `f` applied to its node. The one lemma
the enrolment-triple proof needs. -/
theorem lookupReg_mapNode (nk : NodeKey) (f : Node → Node) (st : Control.ControlState)
    (r : Registration) (h : lookupReg st.nodes nk = some r) :
    lookupReg (Control.Store.mapNode nk f st).nodes nk = some { r with node := f r.node } := by
  have hrk : r.nodeKey = nk := Control.Register.lookupReg_nodeKey st.nodes nk r h
  have hlk := lookupReg_map_keyPreserving
    (fun x => if x.nodeKey = nk then { x with node := f x.node } else x)
    (fun x => by dsimp only; split <;> rfl) st.nodes nk r h
  simpa [Control.Store.mapNode, hrk] using hlk

/-- ★**THE ENROLMENT FACT SURVIVES REPLAY.** Applying the admission triple a pre-auth
registration records — `nodeRegistered req true`, then `nodeUserSet` and `nodeTagsSet`
with the key's resolved attributes — leaves the node carrying exactly that owner and
those tags.

This is what makes the *served* (replayed) state agree with what
`Control.PreAuth.preauth_admit` proves the in-memory gate stamped, and hence what makes
`Control.Tags.tagBindings` see a real owner to check. Before the triple existed, replay
rebuilt the node through `Control.nodeOf` (`user := 0`, `tags := []`) and the ownership
gate had nothing to gate on. -/
theorem admissionTriple_carries_attrs (st : CoordState) (req : RegisterRequest)
    (a : KeyAttrs) :
    (lookupReg (applyEvent (applyEvent (applyEvent st (.nodeRegistered req true))
        (setUserEvent req.nodeKey a.user)) (setTagsEvent req.nodeKey a.tags)).control.nodes
      req.nodeKey).map (fun r => (r.node.user, r.node.tags))
      = some (a.user, a.tags) := by
  have h0 : lookupReg (applyEvent st (.nodeRegistered req true)).control.nodes req.nodeKey
      = some { nodeKey := req.nodeKey, node := nodeOf req true, status := .authorized } := by
    simp [applyEvent, upsertReg, lookupReg]
  have h1 := lookupReg_mapNode req.nodeKey (fun n => { n with user := a.user })
    (applyEvent st (.nodeRegistered req true)).control _ h0
  have h2 := lookupReg_mapNode req.nodeKey (fun n => { n with tags := a.tags })
    (Control.Store.mapNode req.nodeKey (fun n => { n with user := a.user })
      (applyEvent st (.nodeRegistered req true)).control) _ h1
  show ((lookupReg (Control.Store.mapNode req.nodeKey (fun n => { n with tags := a.tags })
      (Control.Store.mapNode req.nodeKey (fun n => { n with user := a.user })
        (applyEvent st (.nodeRegistered req true)).control)).nodes req.nodeKey).map
      (fun r => (r.node.user, r.node.tags))) = some (a.user, a.tags)
  rw [h2]
  simp

/-! ## §5  `nodes delete` — remove a node (headscale `nodes delete`)

headscale `nodes delete -i` (`nodes.go`, alias `del`). Emits `Event.nodeReaped nk`
(the registry-removal transition, `Register.reapEphemeral`): the node is dropped
from the registry and can never again be distributed as a peer. -/

/-- The durable delete event. -/
def deleteNodeEvent (nk : NodeKey) : Event :=
  .nodeReaped nk

/-- **A deleted node is gone.** After `deleteNodeEvent nk`, looking the node up by
its key yields `none` — it is absent from `nodes list` and from every netmap
(`Register.reap_removes`). -/
theorem deleteNode_removes (st : CoordState) (nk : NodeKey) :
    lookupReg (applyEvent st (deleteNodeEvent nk)).control.nodes nk = none := by
  simp only [applyEvent, deleteNodeEvent]
  exact Control.Register.reap_removes nk st.control

/-! ## §6  `preauthkeys create` / `list` — mint & enumerate pre-auth keys

headscale `preauthkeys create --reusable --ephemeral --expiration --tags --user`
and `preauthkeys list` (`cmd/headscale/cli/preauthkeys.go`). Minting reuses the
proven `Control.PreAuth.mint` (HASHED AT REST — only `hash secret` is stored; the
secret is handed to the operator as the `--authkey` string and is never a field
of the stored record). The durable event is `Event.keyMinted pk`. -/

/-- The persisted key a mint produces — the FULL rich schema the Store tracks,
built from the CSPRNG secret's hash and the requested attributes. -/
def mintedKey (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) : PreauthKey :=
  { key := hash secret, reusable := a.reusable, used := false,
    ephemeral := a.ephemeral, expiry := a.expiry, tags := a.tags,
    user := a.user, revoked := false }

/-- The durable mint event. -/
def mintKeyEvent (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) : Event :=
  .keyMinted (mintedKey hash secret a)

/-- **`preauthkeys list`** — the minted keys, read from the replayed state. -/
def listKeys (st : CoordState) : List PreauthKey :=
  st.preauth

/-- **The minted key IS `Control.PreAuth.mint`.** Viewed through the admission
gate's `KeyRecord` lens, the key the operator mints is exactly what the proven
`PreAuth.mint` produces — so it validates precisely as the live gate's key. -/
theorem mintedKey_toRecord_eq_mint (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) :
    (mintedKey hash secret a).toRecord = Control.PreAuth.mint hash secret a := by
  simp only [mintedKey, PreauthKey.toRecord, Control.PreAuth.mint]

/-- **A minted key is listed.** After `mintKeyEvent`, the new key is at the head
of `listKeys` — `preauthkeys create` then `preauthkeys list` shows it. -/
theorem mintKeyEvent_listed (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs)
    (st : CoordState) :
    listKeys (applyEvent st (mintKeyEvent hash secret a))
      = mintedKey hash secret a :: st.preauth := rfl

/-- **A freshly minted, live key ADMITS its secret.** Feeding the just-minted key
(as the admission store) to the proven `PreAuth.validate` with the secret the
operator handed out yields `.admit a` — the minted key actually works — provided
it has not expired (`expiry = 0` never-expiry, or `now ≤ expiry`). Independent of
reusable/one-shot. -/
theorem mintedKey_admits (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat)
    (hlive : a.expiry = 0 ∨ now ≤ a.expiry) :
    Control.PreAuth.validate hash [(mintedKey hash secret a).toRecord] now secret = .admit a := by
  have hexp : ¬(0 < a.expiry ∧ a.expiry < now) := by
    rcases hlive with h | h <;> rintro ⟨h0, hlt⟩ <;> omega
  have hfind : Control.PreAuth.findByHash hash [(mintedKey hash secret a).toRecord] secret
      = some (mintedKey hash secret a).toRecord := by
    simp [Control.PreAuth.findByHash, mintedKey, PreauthKey.toRecord]
  unfold Control.PreAuth.validate
  rw [hfind]
  show Control.PreAuth.validateRec now (mintedKey hash secret a).toRecord = .admit a
  unfold Control.PreAuth.validateRec
  have hrev : ((mintedKey hash secret a).toRecord).revoked = false := rfl
  have hattr : ((mintedKey hash secret a).toRecord).attrs = a := rfl
  have hused : ((mintedKey hash secret a).toRecord).used = false := rfl
  rw [hrev, hattr, hused]
  simp only [if_neg (by decide : ¬ (false = true)), if_neg hexp]
  split <;> rfl

/-! ## §7  `routes list` — advertised subnet routes (headscale `routes list`)

headscale `routes list` (older) / `nodes list-routes` (newer): the subnet routes
each node advertises. In drorb a node's advertised routes are
`advertisedRoutes` (its `allowedIPs` minus its own addresses); only
operator-approved ones are ever distributed (`Routes.route_needs_approval`). -/

/-- One row of `routes list`: a node and the subnet routes it advertises. -/
structure RouteView where
  nodeKey : NodeKey
  routes  : List Prefix
deriving Repr

/-- **`routes list`** — every node with a non-empty advertised-route set. -/
def listRoutes (st : CoordState) : List RouteView :=
  st.control.nodes.filterMap (fun r =>
    let rs := advertisedRoutes r.node
    if rs.isEmpty then none else some { nodeKey := r.nodeKey, routes := rs })

/-- **Route rows are faithful.** Every row of `routes list` comes from a real
registration and reports exactly that node's advertised routes — no invented
route. -/
theorem listRoutes_sound (st : CoordState) (v : RouteView) (h : v ∈ listRoutes st) :
    ∃ r ∈ st.control.nodes,
      r.nodeKey = v.nodeKey ∧ v.routes = advertisedRoutes r.node := by
  simp only [listRoutes, List.mem_filterMap] at h
  obtain ⟨r, hmem, hval⟩ := h
  refine ⟨r, hmem, ?_, ?_⟩ <;>
    · by_cases he : (advertisedRoutes r.node).isEmpty
      · rw [if_pos he] at hval; exact absurd hval (by simp)
      · rw [if_neg he] at hval
        simp only [Option.some.injEq] at hval
        subst hval <;> rfl

/-! ## §8  `users list` — the owning users (headscale `users list`)

drorb tracks a user id on each node and each key. `listUsers` returns the distinct
user ids present in the coordination state. -/

/-- **`users list`** — the distinct owning user ids across nodes and keys. -/
def listUsers (st : CoordState) : List Nat :=
  (st.control.nodes.map (·.node.user) ++ st.preauth.map (·.user)).eraseDups

/-- **User listing is faithful.** Every listed user id owns a node or a key —
`listUsers` invents no user. -/
theorem listUsers_sound (st : CoordState) (u : Nat) (h : u ∈ listUsers st) :
    (∃ r ∈ st.control.nodes, r.node.user = u) ∨ (∃ k ∈ st.preauth, k.user = u) := by
  simp only [listUsers, List.mem_eraseDups, List.mem_append, List.mem_map] at h
  rcases h with ⟨r, hr, hru⟩ | ⟨k, hk, hku⟩
  · exact Or.inl ⟨r, hr, hru⟩
  · exact Or.inr ⟨k, hk, hku⟩

end Control.Admin

#print axioms Control.Admin.listNodes_sound
#print axioms Control.Admin.registerNodeEvent_lists_authorized
#print axioms Control.Admin.expireNode_target_expired
#print axioms Control.Admin.expireNode_preserves_never
#print axioms Control.Admin.setExpiryEvent_sets
#print axioms Control.Admin.setExpiryEvent_disable
#print axioms Control.Admin.deleteNode_removes
#print axioms Control.Admin.mintedKey_toRecord_eq_mint
#print axioms Control.Admin.mintKeyEvent_listed
#print axioms Control.Admin.mintedKey_admits
#print axioms Control.Admin.listRoutes_sound
#print axioms Control.Admin.listUsers_sound
