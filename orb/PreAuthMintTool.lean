/-
# preauth-mint — mint a drorb pre-auth key + drive the registration gate

`preauth-mint mint [--reusable] [--ephemeral] [--expiry <unix>] [--user <id>]
[--tag <t>]...` draws a 256-bit secret from the AUDITED AWS-LC CSPRNG
(`aws_lc_rs::rand::fill` — NEVER `rand`), prints the key string a client passes
to `tailscale up --authkey=<key>`, and prints the STORED record (only the
HACL*/EverCrypt SHA-256 hash of the secret — the secret itself is never stored).

`preauth-mint demo` drives the whole gate MY-HAND end to end with REAL
`RegisterRequest` wire bytes (`Control.putRegReq`/`getRegReq`): mint → a request
bearing the key is ADMITTED (`MachineAuthorized`, right user/tags); an
expired / unknown / one-shot-exhausted / revoked key is REJECTED; and the store
holds only the hash. Exits nonzero if any check fails.

This is the operator helper for §1 of the homelab completeness spec. It draws no
deployed config and, apart from the audited crypto seam, touches only the pure
`Control.PreAuth` model. Audited primitives only: `Crypto.sha256` (HACL*) for the
hash at rest, AWS-LC CSPRNG for the secret.
-/
import Control.PreAuthKey
import Crypto

open Control Control.PreAuth

/-- Audited AWS-LC CSPRNG (`aws_lc_rs::rand::fill`) via `ffi/crypto_shim.c`
`drorb_rand_bytes`. NOT `rand`. Fail-closed: an empty ByteArray on CSPRNG error
(the gate rejects a zero-length key). -/
@[extern "drorb_rand_bytes"]
opaque randBytes (len : UInt32) : IO ByteArray

/-- The model's abstract `hash`, instantiated with HACL*/EverCrypt SHA-256. -/
def sha256Bytes (b : Bytes) : Bytes := (Crypto.sha256 ⟨b.toArray⟩).toList

/-! ## hex helpers (the key string a client presents) -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)

def toHex (b : Bytes) : String :=
  String.ofList (b.foldr (fun x acc =>
    hexDigit (x.toNat / 16) :: hexDigit (x.toNat % 16) :: acc) [])

/-! ## mint -/

structure MintArgs where
  reusable  : Bool := false
  ephemeral : Bool := false
  expiry    : Nat := 0
  user      : Nat := 0
  tags      : List String := []

partial def parseMint (as : List String) (acc : MintArgs) : Option MintArgs :=
  match as with
  | [] => some acc
  | "--reusable" :: t => parseMint t { acc with reusable := true }
  | "--ephemeral" :: t => parseMint t { acc with ephemeral := true }
  | "--expiry" :: v :: t => do let n ← v.toNat?; parseMint t { acc with expiry := n }
  | "--user" :: v :: t => do let n ← v.toNat?; parseMint t { acc with user := n }
  | "--tag" :: v :: t => parseMint t { acc with tags := acc.tags ++ [v] }
  | _ => none

def attrsOf (m : MintArgs) : KeyAttrs :=
  { reusable := m.reusable, ephemeral := m.ephemeral, expiry := m.expiry,
    tags := m.tags.map (·.toUTF8.toList), user := m.user }

def doMint (m : MintArgs) : IO UInt32 := do
  let secretBA ← randBytes 32
  if secretBA.size ≠ 32 then
    IO.eprintln "error: AWS-LC CSPRNG failed (empty secret)"; return 1
  let secret : Bytes := secretBA.toList
  let a := attrsOf m
  let stored := mint sha256Bytes secret a
  IO.println s!"key    : drorb-authkey-{toHex secret}"
  IO.println s!"stored : sha256={toHex stored.keyHash}"
  IO.println s!"attrs  : reusable={a.reusable} ephemeral={a.ephemeral} expiry={a.expiry} user={a.user} tags={m.tags}"
  IO.println "(the secret is NOT stored — only the SHA-256 hash above)"
  return 0

/-! ## demo — drive the gate MY-HAND with real Register bytes -/

/-- Build a RegisterRequest bearing `secret` as the `Auth.AuthKey` field. -/
def mkReq (secret : Bytes) : RegisterRequest :=
  { version := 1, nodeKey := ⟨List.replicate 32 7⟩, oldNodeKey := ⟨[]⟩,
    machineKey := ⟨List.replicate 32 9⟩, authKey := secret, expiry := 0,
    ephemeral := false, followup := false }

/-- Real-bytes roundtrip: serialize then parse the RegisterRequest off the wire,
so the gate is driven by the DECODED request, not the in-memory one. -/
def wireReq (secret : Bytes) : Option RegisterRequest :=
  (getRegReq (putRegReq (mkReq secret))).map (·.1)

def check (name : String) (ok : Bool) : IO Bool := do
  let tag := if ok then "PASS" else "FAIL"
  IO.println s!"[{tag}] {name}"
  return ok

def doDemo : IO UInt32 := do
  let now := 1000
  -- audited-CSPRNG secret + a tagged, user-owned, one-shot key
  let secretBA ← randBytes 32
  if secretBA.size ≠ 32 then IO.eprintln "CSPRNG failed"; return 1
  let secret : Bytes := secretBA.toList
  let tags : List Bytes := ["tag:server".toUTF8.toList]
  let attrs : KeyAttrs := { reusable := false, ephemeral := false, expiry := 0,
                            tags := tags, user := 42 }
  let store : Store := [mint sha256Bytes secret attrs]
  let s0 := ControlState.init
  let mut oks : List Bool := []

  -- (0) real Register wire bytes roundtrip
  let some req := wireReq secret
    | do IO.eprintln "wire roundtrip failed"; return 1
  oks := oks ++ [(← check "RegisterRequest wire roundtrip (putRegReq/getRegReq)" (req.authKey == secret))]

  -- (1) valid key ADMITTED with right user + tags
  let r1 := registerWithPreAuth sha256Bytes store s0 now req
  let admittedTags := match r1.admitted with | some a => a.tags | none => []
  oks := oks ++ [(← check "valid key -> MachineAuthorized" (r1.response.machineAuthorized == true))]
  oks := oks ++ [(← check "admitted user = 42" (r1.response.user == 42))]
  oks := oks ++ [(← check "admitted tags = [tag:server]" (admittedTags == tags))]
  let nodeAuthed := match lookupReg r1.state'.nodes req.nodeKey with
    | some reg => reg.status == .authorized ∧ reg.node.user == 42
    | none => false
  oks := oks ++ [(← check "registry: node .authorized with user 42" nodeAuthed)]

  -- (2) HASHED AT REST: store holds only sha256(secret), never the secret
  let storedHash := (store.head?.map (·.keyHash)).getD []
  oks := oks ++ [(← check "stored keyHash = sha256(secret)" (storedHash == sha256Bytes secret))]
  oks := oks ++ [(← check "stored keyHash != secret (hashed, not plaintext)" (storedHash != secret))]

  -- (3) UNKNOWN key rejected
  let bad : Bytes := (secret.map (· + 1))
  let rUnknown := registerWithPreAuth sha256Bytes store s0 now (mkReq bad)
  oks := oks ++ [(← check "unknown key -> rejected (no MachineAuthorized)" (rUnknown.response.machineAuthorized == false))]

  -- (4) EXPIRED key rejected
  let eSecretBA ← randBytes 32
  let eSecret : Bytes := eSecretBA.toList
  let eAttrs : KeyAttrs := { attrs with expiry := 500 }  -- 500 < now=1000
  let eStore : Store := [mint sha256Bytes eSecret eAttrs]
  let rExp := registerWithPreAuth sha256Bytes eStore s0 now (mkReq eSecret)
  oks := oks ++ [(← check "expired key -> rejected" (rExp.response.machineAuthorized == false))]

  -- (5) ONE-SHOT exhaustion: first admit, spend, second reject
  let firstAdmit := (validate sha256Bytes store now secret).isAdmit
  let spent := consume sha256Bytes secret store
  let secondReject := (validate sha256Bytes spent now secret) == Verdict.reject Reason.exhausted
  oks := oks ++ [(← check "one-shot: first use admits" (firstAdmit == true))]
  oks := oks ++ [(← check "one-shot: second use -> exhausted" secondReject)]

  -- (6) REVOKED key rejected
  let revStore : Store := [{ mint sha256Bytes secret attrs with revoked := true }]
  let rRev := registerWithPreAuth sha256Bytes revStore s0 now (mkReq secret)
  oks := oks ++ [(← check "revoked key -> rejected" (rRev.response.machineAuthorized == false))]

  let passed := oks.foldl (· && ·) true
  IO.println ""
  IO.println s!"{oks.filter id |>.length}/{oks.length} checks passed"
  return (if passed then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | "demo" :: _ => doDemo
  | "mint" :: rest =>
    match parseMint rest {} with
    | some m => doMint m
    | none => IO.eprintln "usage: preauth-mint mint [--reusable] [--ephemeral] [--expiry <unix>] [--user <id>] [--tag <t>]..."; return 1
  | _ =>
    IO.eprintln "usage: preauth-mint (mint [opts] | demo)"; return 1
