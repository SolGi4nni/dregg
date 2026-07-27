/-
# drorb-ctl — the homelab operator CLI (a headscale-style admin surface)

A local operator tool over the drorb coordination store (`Control.Store`, the
durable event log). It READS the log off disk, REPLAYS it to the coordination
state, runs one admin command (`Control.Admin`), and — for mutations — APPENDS the
resulting `Store.Event` and rewrites the log. Each invocation is a fresh process
that reconstructs the whole state from the log, so persistence across commands IS
the restart-replay guarantee (`Control.Store.restart_sound`) demonstrated live.

  drorb-ctl nodes list
  drorb-ctl nodes register --key <hex> [--user N] [--expiry UNIX] [--tag t]...
  drorb-ctl nodes expire <keyhexprefix>
  drorb-ctl nodes set-expiry <keyhexprefix> <duration-seconds|--disable-expiry>
  drorb-ctl nodes delete <keyhexprefix>
  drorb-ctl nodes tag <keyhexprefix> <tag:a,tag:b|->
  drorb-ctl policy tags
  drorb-ctl preauthkeys create [--reusable] [--ephemeral] [--expiry UNIX] [--user N] [--tag t]...
  drorb-ctl preauthkeys list
  drorb-ctl routes list
  drorb-ctl users list

Store path: env `DRORB_STORE` (default `./drorb-store.bin`).

Cross-checked against the PUBLIC headscale CLI (github.com/juanfont/headscale,
`cmd/headscale/cli`): `nodes list/register/expire/delete`, `preauthkeys
create/list`, `routes list`, `users list`. See `Control.Admin` for the citations.

AUTH GATE: this admin surface is PRIVILEGED (it mints credentials, expires nodes).
As a *local* CLI it is bounded by filesystem permissions on the store log. Any
NETWORK exposure of these operations MUST sit behind the PBKDF2 basic-auth
(`PbkdfHashTool` / `Control.BasicAuth`) or a bearer token — never unauthenticated
(`Control.Admin.AdminAuthNote`).

Audited primitives only: AWS-LC CSPRNG for the pre-auth secret, HACL*/EverCrypt
SHA-256 for the hash-at-rest. NEVER `rand`, NEVER openssl.
-/
import Control.Store
import Control.Durable
import Control.PreAuthKey
import Control.Admin
import Control.Ipam
import Control.Tags
import Control.Policy
import Crypto

open Control Control.Store Control.PreAuth Control.Admin

/-! ## Audited crypto seams -/

/-- Audited AWS-LC CSPRNG (`aws_lc_rs::rand::fill`) via `ffi/crypto_shim.c`. NOT
`rand`. Fail-closed: empty ByteArray on error. -/
@[extern "drorb_rand_bytes"]
opaque randBytes (len : UInt32) : IO ByteArray

/-- The model's abstract `hash`, instantiated with HACL*/EverCrypt SHA-256. -/
def sha256Bytes (b : Bytes) : Bytes := (Crypto.sha256 ⟨b.toArray⟩).toList

/-! ## hex / rendering helpers -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)

def toHex (b : Bytes) : String :=
  String.ofList (b.foldr (fun x acc =>
    hexDigit (x.toNat / 16) :: hexDigit (x.toNat % 16) :: acc) [])

def hexVal? (c : Char) : Option Nat :=
  let n := c.toNat
  if n ≥ 48 ∧ n ≤ 57 then some (n - 48)          -- 0-9
  else if n ≥ 97 ∧ n ≤ 102 then some (n - 87)    -- a-f
  else if n ≥ 65 ∧ n ≤ 70 then some (n - 55)     -- A-F
  else none

/-- Parse an even-length hex string to bytes; `none` on a bad digit or odd length. -/
def fromHex (s : String) : Option Bytes :=
  let cs := s.toList
  let rec go : List Char → Option Bytes
    | [] => some []
    | [_] => none
    | a :: b :: t => do
      let hi ← hexVal? a
      let lo ← hexVal? b
      let rest ← go t
      some (UInt8.ofNat (hi * 16 + lo) :: rest)
  go cs

/-- A tag's bytes rendered as a string (tags are ASCII like `tag:server`). -/
def tagStr (t : Bytes) : String := String.ofList (t.map (fun x => Char.ofNat x.toNat))

def tagsStr (ts : List Bytes) : String := String.intercalate "," (ts.map tagStr)

/-- Render a CIDR prefix: dotted-decimal for v4, hex for v6, with `/bits`. -/
def prefixStr (p : Prefix) : String :=
  let body :=
    if p.addr.length == 4 then String.intercalate "." (p.addr.map (fun x => toString x.toNat))
    else toHex p.addr
  s!"{body}/{p.bits}"

def prefixesStr (ps : List Prefix) : String :=
  if ps.isEmpty then "-" else String.intercalate "," (ps.map prefixStr)

def statusStr : NodeStatus → String
  | .registered => "registered"
  | .authorized => "authorized"
  | .expired    => "expired"

/-! ## store I/O — read/replay + append(rewrite) -/

def storePath : IO String := do
  match (← IO.getEnv "DRORB_STORE") with
  | some p => return p
  | none   => return "./drorb-store.bin"

/-- Operator wall clock (unix seconds), read via `date +%s`. This is the record-time
`now` for `set-expiry <duration>` (the resolved expiry is stamped into the event, so
replay stays deterministic — the store carries the fact, never re-reads the clock).
Out of the trusted core, exactly like the file I/O. Fail-closed to 0 on error. -/
def nowUnix : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "date", args := #["+%s"] }
    match out.stdout.trimAscii.toNat? with
    | some n => return n
    | none   => return 0
  catch _ => return 0

/-- Read the durable log off disk (empty if the file does not exist), through the
PROVEN torn-tail-tolerant `recoverStore`: a framed store is recovered frame by frame
(everything appended before a torn tail survives — `recoverStore_torn_write`), and a
store written by an older drorb still reads through the legacy count-prefixed decoder
(`recoverStore_legacy`). -/
def readLog (path : String) : IO (List Event) := do
  if ← System.FilePath.pathExists path then
    let raw ← IO.FS.readBinFile path
    return recoverStore raw.toList
  else
    return []

/-- Rewrite the whole log ATOMICALLY **and DURABLY** in the framed append-only format
(`Control.Durable.commitAtomic`): temp file, force it, `rename`, force the containing
directory. An interrupted CLI can never leave a half-written live store behind, and a
`drorb-ctl` command that has PRINTED "[persisted]" cannot have its effect undone by a
power cut — the same guarantee the coordinator's own commit path now carries, on the
same file. -/
def writeLog (path : String) (events : List Event) : IO Unit :=
  Control.Durable.commitAtomic path ⟨(encodeStore events).toArray⟩

/-- Append events durably and report. -/
def appendEvents (path : String) (existing new : List Event) : IO Unit := do
  writeLog path (existing ++ new)
  IO.println s!"[persisted] +{new.length} event(s) -> {path} ({(existing ++ new).length} total)"

/-! ## command implementations -/

def cmdNodesList (st : CoordState) : IO Unit := do
  let rows := listNodes st
  IO.println s!"NODES ({rows.length})"
  IO.println "  nodekey            user  status      addresses          keyExpiry  online  tags                routes"
  for v in rows do
    let tg := if v.tags.isEmpty then "-" else tagsStr v.tags
    IO.println s!"  {(toHex v.nodeKey.pub).take 16}  {v.user}     {statusStr v.status}  {prefixesStr v.addresses}  {v.keyExpiry}         {v.online}   {tg}  {prefixesStr v.advertisedRoutes}"

def cmdKeysList (st : CoordState) : IO Unit := do
  let ks := listKeys st
  IO.println s!"PREAUTH KEYS ({ks.length})"
  IO.println "  keyhash(sha256)    reusable  ephemeral  used  expiry  user  tags"
  for k in ks do
    IO.println s!"  {(toHex k.key).take 16}  {k.reusable}     {k.ephemeral}      {k.used}  {k.expiry}       {k.user}     {tagsStr k.tags}"

def cmdRoutesList (st : CoordState) : IO Unit := do
  let rs := listRoutes st
  IO.println s!"ROUTES ({rs.length} node(s) advertising)"
  for v in rs do
    IO.println s!"  {(toHex v.nodeKey.pub).take 16}  advertises  {prefixesStr v.routes}"

def cmdUsersList (st : CoordState) : IO Unit := do
  let us := listUsers st
  IO.println s!"USERS ({us.length}): {String.intercalate ", " (us.map toString)}"

/-- Find a registration whose node-key hex STARTS WITH the given prefix. -/
def findByPrefix (st : CoordState) (pfx : String) : Option Registration :=
  st.control.nodes.find? (fun r => (toHex r.nodeKey.pub).startsWith pfx)

structure RegArgs where
  key    : Option Bytes := none
  user   : Nat := 0
  expiry : Nat := 0
  tags   : List Bytes := []
  noIp   : Bool := false

partial def parseReg (as : List String) (acc : RegArgs) : Option RegArgs :=
  match as with
  | [] => some acc
  | "--key" :: v :: t => do let b ← fromHex v; parseReg t { acc with key := some b }
  | "--user" :: v :: t => do let n ← v.toNat?; parseReg t { acc with user := n }
  | "--expiry" :: v :: t => do let n ← v.toNat?; parseReg t { acc with expiry := n }
  | "--tag" :: v :: t => parseReg t { acc with tags := acc.tags ++ [v.toUTF8.toList] }
  | "--no-ip" :: t => parseReg t { acc with noIp := true }
  | _ => none

def cmdNodesRegister (path : String) (existing : List Event) (st : CoordState)
    (m : RegArgs) : IO UInt32 := do
  match m.key with
  | none => IO.eprintln "usage: nodes register --key <hex> [--user N] [--expiry UNIX] [--tag t]... [--no-ip]"; return 1
  | some kb =>
    let nk : NodeKey := ⟨kb⟩
    -- headscale nodes register: manual operator admit -> nodeRegistered true.
    -- We stamp user/expiry onto the request; the node materialises via nodeOf.
    let req : RegisterRequest :=
      { version := 1, nodeKey := nk, oldNodeKey := ⟨[]⟩,
        machineKey := ⟨List.replicate 32 0⟩, authKey := [], expiry := m.expiry,
        ephemeral := false, followup := false }
    let regEv := registerNodeEvent req
    -- IPAM: hand the node the next free 100.64/10 address (Control.Ipam allocator).
    let ipEvs : List Event :=
      if m.noIp then []
      else match Control.Ipam.cgnatPool.alloc (Control.Ipam.usedOf st.control.nodes) with
           | some ip => [allocEvent nk ip]
           | none    => []
    let evs := regEv :: ipEvs
    IO.println s!"[register] node {(toHex kb).take 16} admitted (authorized), user={m.user}, keyExpiry={m.expiry}"
    appendEvents path existing evs
    return 0

/-- A PENDING registration: interactively enrolled (`.registered`), no address yet —
awaiting `drorb-ctl nodes approve <nonce>`. (An authorized-by-pre-auth or already
operator-approved node is `.authorized` WITH an address, so it is NOT pending.) -/
def isPending (r : Registration) : Bool :=
  match r.status with | .registered => true | _ => false

/-- **`nodes pending`** — list the PENDING (interactively enrolled, keyless) nodes with
their NONCE (the node-key hex prefix a stock `tailscale up` was handed in its AuthURL,
`<DRORB_CONTROL_URL>/register/<nonce>`). This is exactly the value `nodes approve <nonce>`
matches (`findByPrefix`). These nodes registered WITHOUT a valid pre-auth key and are held
`.registered` (no address, absent from every peer's netmap) until an operator approves. -/
def cmdNodesPending (st : CoordState) : IO Unit := do
  let pend := st.control.nodes.filter isPending
  IO.println s!"PENDING ({pend.length}) — awaiting `drorb-ctl nodes approve <nonce>`"
  IO.println "  nonce (nodekey hex)  user  keyExpiry"
  for r in pend do
    IO.println s!"  {(toHex r.nodeKey.pub).take 16}  {r.node.user}     {r.node.keyExpiry}"

/-- **`nodes approve <nonce>`** — admit a PENDING interactively-enrolled node. Finds the
pending registration whose node-key hex STARTS WITH `<nonce>` (`findByPrefix`, the same
prefix `nodes pending` prints and the AuthURL carried), then emits the SAME durable events
as an operator `nodes register --key`: `nodeRegistered … true` (flip `.registered` ->
`.authorized`) + `addrAllocated` (the next free 100.64/10 address, if it has none yet). The
running coord's `approvalWatcher` adopts the grown log live and pushes the node its Self
address on its open map-stream; the node reaches Running WITH an IP without a coord restart. -/
def cmdNodesApprove (path : String) (existing : List Event) (st : CoordState)
    (nonce : String) : IO UInt32 := do
  match findByPrefix st nonce with
  | none => IO.eprintln s!"error: no node with nonce (key prefix) {nonce}"; return 1
  | some r =>
    if r.status.isAuthorized then
      IO.println s!"[approve] node {(toHex r.nodeKey.pub).take 16} already authorized — no-op"
      return 0
    let nk := r.nodeKey
    -- Reconstruct the register request from the pending node's own record (its machine
    -- key + key expiry are preserved); the decision is resolved to `true` (operator admit).
    let req : RegisterRequest :=
      { version := 1, nodeKey := nk, oldNodeKey := ⟨[]⟩,
        machineKey := r.node.machine, authKey := [], expiry := r.node.keyExpiry,
        ephemeral := false, followup := false }
    let regEv := registerNodeEvent req
    -- IPAM: hand it the next free CGNAT /32 iff it is still address-less (idempotent —
    -- an already-addressed node keeps its stable address).
    let ipEvs : List Event :=
      if r.node.addresses.isEmpty then
        match Control.Ipam.cgnatPool.alloc (Control.Ipam.usedOf st.control.nodes) with
        | some ip => [allocEvent nk ip]
        | none    => []
      else []
    IO.println s!"[approve] node {(toHex nk.pub).take 16}: PENDING -> authorized (nodeRegistered(true){if ipEvs.isEmpty then "" else " + addrAllocated"})"
    appendEvents path existing (regEv :: ipEvs)
    return 0

structure KeyArgs where
  reusable  : Bool := false
  ephemeral : Bool := false
  expiry    : Nat := 0
  user      : Nat := 0
  tags      : List Bytes := []

partial def parseKey (as : List String) (acc : KeyArgs) : Option KeyArgs :=
  match as with
  | [] => some acc
  | "--reusable" :: t => parseKey t { acc with reusable := true }
  | "--ephemeral" :: t => parseKey t { acc with ephemeral := true }
  | "--expiry" :: v :: t => do let n ← v.toNat?; parseKey t { acc with expiry := n }
  | "--user" :: v :: t => do let n ← v.toNat?; parseKey t { acc with user := n }
  | "--tags" :: v :: t => parseKey t { acc with tags := acc.tags ++ (v.splitOn ",").map (·.toUTF8.toList) }
  | "--tag" :: v :: t => parseKey t { acc with tags := acc.tags ++ [v.toUTF8.toList] }
  | _ => none

/-- The key STRING an operator copies into `tailscale up --authkey=…`.

★FIXED 2026-07-25. This used to store `sha256(<the 32 raw CSPRNG bytes>)` while printing
`drorb-authkey-<hex>` for the operator to paste. A stock client presents that STRING in
`RegisterRequest.Auth.AuthKey`, and the coordinator hashes exactly what it was presented
— so the two could never match and EVERY operator-minted pre-auth key was silently
un-usable by a real client (only the built-in demo key, whose stored hash is of its own
ASCII string, worked). The stored hash is now `sha256(keyString)`: the hash of precisely
the bytes the client will present. Same shape as headscale, whose stored bcrypt hash is
of the key text the client sends (`db/preauth_keys.go:106-126`).

★Keys minted before this fix do not admit; re-mint them. -/
def keyStringOf (secret : Bytes) : String := s!"drorb-authkey-{toHex secret}"

def cmdKeysCreate (path : String) (existing : List Event) (m : KeyArgs) : IO UInt32 := do
  let secretBA ← randBytes 32
  if secretBA.size ≠ 32 then IO.eprintln "error: AWS-LC CSPRNG failed"; return 1
  -- the SECRET is the key string the operator hands the device; its hash is what is
  -- stored, so `hash (presented authKey) = stored keyHash` holds by construction.
  let keyStr := keyStringOf secretBA.toList
  let secret : Bytes := keyStr.toUTF8.toList
  let a : KeyAttrs := { reusable := m.reusable, ephemeral := m.ephemeral,
                        expiry := m.expiry, tags := m.tags, user := m.user }
  let ev := mintKeyEvent sha256Bytes secret a
  IO.println s!"key    : {keyStr}"
  IO.println s!"stored : sha256={toHex (sha256Bytes secret)} (hashed at rest — the key string is NOT stored)"
  IO.println s!"attrs  : reusable={m.reusable} ephemeral={m.ephemeral} expiry={m.expiry} user={m.user} tags={tagsStr m.tags}"
  IO.println s!"use    : tailscale up --login-server=<front> --authkey={keyStr}"
  appendEvents path existing [ev]
  return 0

def cmdNodesExpire (path : String) (existing : List Event) (st : CoordState)
    (pfx : String) : IO UInt32 := do
  match findByPrefix st pfx with
  | none => IO.eprintln s!"error: no node with key prefix {pfx}"; return 1
  | some r =>
    if r.node.keyExpiry == 0 then
      -- FORCE-expire a never-expiring node (headscale `nodes expire` with no --expiry
      -- = expire immediately): set a past keyExpiry (Event.nodeExpirySet nk 1) then
      -- advance the clock past it (Event.nodeExpired 2). Both facts persisted; other
      -- nodes untouched (setExpiryEvent targets nk; expire only hits past keys).
      IO.println s!"[expire] node {(toHex r.nodeKey.pub).take 16}: --force (was never-expiring); keyExpiry->1 (past) + clock->2 => .expired (re-auth required)"
      appendEvents path existing [setExpiryEvent r.nodeKey 1, expireNodeEvent 2]
      return 0
    else
      -- clock-driven expire: advance past this node's keyExpiry (Event.nodeExpired).
      -- Never-expiring nodes (keyExpiry=0) are untouched (expireNode_preserves_never).
      let now := r.node.keyExpiry + 1
      IO.println s!"[expire] node {(toHex r.nodeKey.pub).take 16}: advancing clock to {now} (past keyExpiry={r.node.keyExpiry}) -> .expired"
      appendEvents path existing [expireNodeEvent now]
      return 0

/-- `nodes set-expiry <keyprefix> <duration-seconds | --disable-expiry>` — set (or
disable) a node's key expiry (headscale `nodes expire --expiry` / `--disable`).
`<duration>` seconds from now schedules the expiry (stamped as `now + duration`, a
resolved fact); `--disable-expiry` sets `keyExpiry = 0` (never expires). Persisted
as `Event.nodeExpirySet`, replay-stable. -/
def cmdNodesSetExpiry (path : String) (existing : List Event) (st : CoordState)
    (pfx spec : String) : IO UInt32 := do
  match findByPrefix st pfx with
  | none => IO.eprintln s!"error: no node with key prefix {pfx}"; return 1
  | some r =>
    if spec == "--disable-expiry" || spec == "disable" then
      IO.println s!"[set-expiry] node {(toHex r.nodeKey.pub).take 16}: --disable-expiry (keyExpiry -> 0, never expires)"
      appendEvents path existing [setExpiryEvent r.nodeKey 0]
      return 0
    else
      match spec.toNat? with
      | none => do
          IO.eprintln "usage: nodes set-expiry <keyhexprefix> <duration-seconds|--disable-expiry>"
          return 1
      | some dur => do
          let now ← nowUnix
          let exp := now + dur
          IO.println s!"[set-expiry] node {(toHex r.nodeKey.pub).take 16}: keyExpiry -> {exp} (now={now} + {dur}s)"
          appendEvents path existing [setExpiryEvent r.nodeKey exp]
          return 0

/-! ### `nodes tag` — set a node's ACL tags (headscale `nodes tag -t`)

`drorb-ctl nodes tag <keyhexprefix> tag:a,tag:b` replaces the node's `Node.tags`, and
`... -` clears them. Persisted as `Event.nodeTagsSet` (`Control.Admin.setTagsEvent`,
`setTagsEvent_sets` / `setTagsEvent_listed`), so it survives a restart.

★A stamped tag is a CLAIM. Whether it CONFERS reachability is decided when the ACL is
compiled: `Control.Tags.tagBindings` drops every tag whose bearer's owning user is not a
`tagOwners` principal. `drorb-ctl policy tags` shows exactly which claims survive. -/
def cmdNodesTag (path : String) (existing : List Event) (st : CoordState)
    (pfx spec : String) : IO UInt32 := do
  match findByPrefix st pfx with
  | none => IO.eprintln s!"error: no node with key prefix {pfx}"; return 1
  | some r =>
    let tags : List Bytes :=
      if spec == "-" || spec == "" then []
      else ((spec.splitOn ",").filter (fun t => t != "")).map (·.toUTF8.toList)
    let shown := if tags.isEmpty then "(none)" else tagsStr tags
    IO.println s!"[tag] node {(toHex r.nodeKey.pub).take 16}: tags -> {shown}"
    appendEvents path existing [setTagsEvent r.nodeKey tags]
    IO.println "  (a tag is a CLAIM; it binds in the ACL only if the node's owning user"
    IO.println "   is a tagOwner of it — check with `drorb-ctl policy tags`)"
    return 0

/-! ### `policy tags` — WHICH claimed tags actually bind, and why

The operator question a tag model must answer is "I tagged the box, why is it still
denied?". This reads `DRORB_POLICY` through the PROVEN parser
(`Control.Policy.parseHuPolicy`), then applies the SAME projection the coordinator
serves (`Control.Tags.effectiveTags` / `tagBindings`) to the replayed registry, and
prints claimed-vs-effective per node. -/
def loadPolicyForCtl : IO (Option Control.Acl.Policy) := do
  match (← IO.getEnv "DRORB_POLICY") with
  | none => IO.eprintln "policy: DRORB_POLICY not set (the coord would serve deny-all)"; return none
  | some path =>
    match ← (do try pure (some (← IO.FS.readFile path)) catch _ => pure none) with
    | none => IO.eprintln s!"policy: cannot read '{path}'"; return none
    | some text =>
      match Control.Policy.parseHuPolicy text with
      | .ok p => return some p
      | .error e => IO.eprintln s!"policy: '{path}' REJECTED ({e})"; return none

def ownerStr : Control.Acl.Owner → String
  | .user i => s!"user:{i}"
  | .anyUser => "*"

def cmdPolicyTags (st : CoordState) : IO UInt32 := do
  let pol? ← loadPolicyForCtl
  let ow := match pol? with | some p => p.tagOwners | none => []
  IO.println s!"TAG OWNERS ({ow.length})  — who may apply each tag (drorb identities are numeric user ids)"
  if ow.isEmpty then
    IO.println "  (none declared — every claimed tag binds to NOTHING; fail-closed)"
  for e in ow do
    IO.println s!"  {e.1}  <- {String.intercalate ", " (e.2.map ownerStr)}"
  let regs := st.control.nodes
  IO.println s!"NODE TAGS ({regs.length} node(s))"
  IO.println "  nodekey            user  status      claimed              effective (binds in the ACL)"
  for r in regs do
    let claimed := Control.Tags.claimedTags r.node
    let eff := Control.Tags.effectiveTags ow r.node
    let cs := if claimed.isEmpty then "-" else String.intercalate "," claimed
    let es := if eff.isEmpty then "-" else String.intercalate "," eff
    IO.println s!"  {(toHex r.nodeKey.pub).take 16}  {r.node.user}     {statusStr r.status}  {cs}  {es}"
  let authorized := (regs.filter (fun r => decide (r.status = NodeStatus.authorized))).map (·.node)
  let binds := Control.Tags.tagBindings ow authorized
  IO.println s!"ACL TAG BINDINGS ({binds.length}) — what a `tag:` selector resolves to"
  if binds.isEmpty then
    IO.println "  (none — every `tag:` selector resolves to the empty CIDR set => default-deny)"
  for b in binds do
    IO.println s!"  {b.1}  ->  {b.2.length} CIDR(s)"
  return 0

def cmdNodesDelete (path : String) (existing : List Event) (st : CoordState)
    (pfx : String) : IO UInt32 := do
  match findByPrefix st pfx with
  | none => IO.eprintln s!"error: no node with key prefix {pfx}"; return 1
  | some r =>
    IO.println s!"[delete] node {(toHex r.nodeKey.pub).take 16} removed from registry"
    appendEvents path existing [deleteNodeEvent r.nodeKey]
    return 0

def usage : IO UInt32 := do
  IO.eprintln "usage: drorb-ctl <command>"
  IO.eprintln "  nodes list"
  IO.eprintln "  nodes pending"
  IO.eprintln "  nodes approve <nonce>"
  IO.eprintln "  nodes register --key <hex> [--user N] [--expiry UNIX] [--tag t]... [--no-ip]"
  IO.eprintln "  nodes expire <keyhexprefix>"
  IO.eprintln "  nodes set-expiry <keyhexprefix> <duration-seconds|--disable-expiry>"
  IO.eprintln "  nodes delete <keyhexprefix>"
  IO.eprintln "  nodes tag <keyhexprefix> <tag:a,tag:b|->"
  IO.eprintln "  policy tags      (which claimed tags actually bind, per DRORB_POLICY)"
  IO.eprintln "  preauthkeys create [--reusable] [--ephemeral] [--expiry UNIX] [--user N] [--tags a,b]"
  IO.eprintln "  preauthkeys list"
  IO.eprintln "  routes list"
  IO.eprintln "  users list"
  return 1

def main (args : List String) : IO UInt32 := do
  let path ← storePath
  let events ← readLog path
  let st := replay events
  match args with
  | ["nodes", "list"] => do cmdNodesList st; return 0
  | ["nodes", "pending"] => do cmdNodesPending st; return 0
  | ["nodes", "approve", nonce] => cmdNodesApprove path events st nonce
  | "nodes" :: "register" :: rest =>
      match parseReg rest {} with
      | some m => cmdNodesRegister path events st m
      | none => usage
  | ["nodes", "expire", pfx] => cmdNodesExpire path events st pfx
  | ["nodes", "set-expiry", pfx, spec] => cmdNodesSetExpiry path events st pfx spec
  | ["nodes", "delete", pfx] => cmdNodesDelete path events st pfx
  | ["nodes", "tag", pfx, spec] => cmdNodesTag path events st pfx spec
  | ["policy", "tags"] => cmdPolicyTags st
  | "preauthkeys" :: "create" :: rest =>
      match parseKey rest {} with
      | some m => cmdKeysCreate path events m
      | none => usage
  | ["preauthkeys", "list"] => do cmdKeysList st; return 0
  | ["routes", "list"] => do cmdRoutesList st; return 0
  | ["users", "list"] => do cmdUsersList st; return 0
  | _ => usage
