import Control.Store
import Control.PreAuthKey

/-!
# Control.StoreKeyDemo — the one-shot-key-across-restart gate, my-hand

Mint a NON-reusable (one-shot) pre-auth key carrying **tags + a future expiry** ->
a node registers with it (the key is spent, a `keyConsumed` durable event) ->
persist the log -> KILL (fresh process) -> replay from disk -> the key is
recovered WITH its tags + expiry AND marked consumed, so a SECOND registration
with the same secret is REJECTED (`reject .exhausted`).

This is the runnable witness of `Control.Store.oneShot_rejected_after_restart`
(no double-spend across a restart) over the on-disk wire codec.

  lake env lean --run Control/StoreKeyDemo.lean drive  /tmp/keylog.bin
  lake env lean --run Control/StoreKeyDemo.lean replay /tmp/keylog.bin
-/

open Control Control.Store

/-- A stand-in audited-hash for the demo (identity), to keep the persisted
`keyHash` legible. The live coord instantiates `hash` with `Crypto.sha256`
(`ControlLive.sha256Bytes`); the schema/replay/spend logic exercised here is
identical for any `hash`. -/
def demoHash (b : Bytes) : Bytes := b

/-- The pre-auth secret the operator hands the node (`--authkey`). -/
def demoSecret : Bytes := [0x5e, 0xc5, 0xe7, 0x00, 0x01, 0x02, 0x03]

/-- Two ACL tags copied to the node on registration. -/
def demoTags : List Bytes := [[0x74, 0x61, 0x67], [0x64, 0x62]]   -- "tag", "db"

/-- The persisted one-shot key: hashed-at-rest identity + tags + a future expiry. -/
def demoKey : PreauthKey :=
  { key := demoHash demoSecret, reusable := false, used := false,
    ephemeral := false, expiry := 1000, tags := demoTags, user := 7, revoked := false }

/-- The durable log: mint the one-shot key, then a registration spends it. -/
def demoLog : List Event :=
  [ .keyMinted demoKey, .keyConsumed demoKey.key ]

/-- Wall clock at the second (post-restart) registration attempt: before expiry. -/
def demoNow : Nat := 500

def renderKeys (st : CoordState) : String := Id.run do
  let mut out := s!"preauthKeys = {st.preauth.length}\n"
  for pk in st.preauth do
    out := out ++ s!"  key(hash)={repr pk.key} reusable={pk.reusable} used={pk.used}" ++
      s!" ephemeral={pk.ephemeral} expiry={pk.expiry} user={pk.user}" ++
      s!" tags={repr pk.tags} revoked={pk.revoked}\n"
  return out

def main (args : List String) : IO Unit := do
  match args with
  | ["drive", path] => do
      let bytes : ByteArray := ⟨(encodeLog demoLog).toArray⟩
      IO.FS.writeBinFile path bytes
      IO.println s!"[drive] minted one-shot key (tags+expiry), spent it on register, persisted {bytes.size} bytes"
      IO.print (renderKeys (replay demoLog))
  | ["replay", path] => do
      let raw ← IO.FS.readBinFile path
      IO.println s!"[replay] read {raw.size} bytes from {path} (fresh process, empty memory)"
      match decodeLog raw.toList with
      | some (events, []) => do
          let st := replay events
          IO.println s!"[replay] decoded {events.length} events, replayed from empty"
          IO.print (renderKeys st)
          let paStore : Control.PreAuth.Store := st.preauth.map PreauthKey.toRecord
          let verdict := Control.PreAuth.validate demoHash paStore demoNow demoSecret
          IO.println s!"[replay] second-register verdict on recovered key = {repr verdict}"
          match verdict with
          | .reject .exhausted =>
              IO.println "[replay] GATE PASS: one-shot key REJECTED as exhausted after restart (no double-spend); tags+expiry recovered above"
          | _ => IO.println "[replay] GATE FAIL: key was not exhausted after restart"
      | some (_, _ :: _) => IO.println "[replay] ERROR: trailing bytes after log"
      | none => IO.println "[replay] ERROR: log failed to decode"
  | _ => IO.println "usage: (drive|replay) <logfile>"
