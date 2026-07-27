import Control.Store

/-!
# Control.StoreDemo — the persist → kill → replay gate, my-hand

A standalone runnable (`lake env lean --run Control/StoreDemo.lean <mode> <logfile>`).

* `drive <logfile>` — a fresh coordinator processes a scenario (register 2 nodes,
  mint a pre-auth key, advertise + approve a subnet route), persists the event log
  to `<logfile>` as the length-prefixed binary `encodeLog` bytes, prints the live
  reconstructed state, then exits (the process is killed — nothing in memory).
* `replay <logfile>` — a brand-new process reads ONLY `<logfile>` off disk,
  `decodeLog`s it, `replay`s the events from empty, and prints the reconstructed
  state.

The gate: `drive`'s printed state and `replay`'s printed state are byte-identical
(diff them), demonstrating that a restart recovers the exact pre-restart
coordination state from the durable log — the content of `restart_sound`.
-/

open Control Control.Store

/-- 32-byte key filled with one repeated byte (a stand-in identity key). -/
def key32 (b : UInt8) : NodeKey := ⟨List.replicate 32 b⟩

def mkReq (k : NodeKey) : RegisterRequest :=
  { version := 1, nodeKey := k, oldNodeKey := ⟨[]⟩,
    machineKey := ⟨List.replicate 32 (9 : UInt8)⟩,
    authKey := [], expiry := 0, ephemeral := false, followup := false }

def k1 : NodeKey := key32 1
def k2 : NodeKey := key32 2

/-- A /24 subnet route behind k1 (advertised, then approved). -/
def route : Prefix := { addr := [10, 0, 0, 0], bits := 24 }

def demoPreauth : PreauthKey :=
  { key := [0xDE, 0xAD, 0xBE, 0xEF], reusable := false, used := false }

/-- The scenario: 2 registrations, a minted key, an advertised + approved route. -/
def demoLog : List Event :=
  [ .nodeRegistered (mkReq k1) true,
    .nodeRegistered (mkReq k2) true,
    .keyMinted demoPreauth,
    .routesAdvertised k1 [route],
    .routeApproved k1 [route] ]

/-- A stable, human-diffable rendering of the reconstructed coordination state:
per-node (key head, status, allowedIPs) and the pre-auth key set. -/
def renderState (st : CoordState) : String := Id.run do
  let mut out := s!"nodes = {st.control.nodes.length}, preauthKeys = {st.preauth.length}\n"
  for r in st.control.nodes do
    out := out ++ s!"  node key[0]={r.nodeKey.pub.headD 0} status={repr r.status} " ++
      s!"allowedIPs={repr r.node.allowedIPs}\n"
  for pk in st.preauth do
    out := out ++ s!"  preauth key={repr pk.key} reusable={pk.reusable} used={pk.used}\n"
  out := out ++ s!"filter.rules={st.control.filter.length} dns.records={st.control.dns.records.length}\n"
  return out

def main (args : List String) : IO Unit := do
  match args with
  | ["drive", path] => do
      let st := replay demoLog
      let bytes : ByteArray := ⟨(encodeLog demoLog).toArray⟩
      IO.FS.writeBinFile path bytes
      IO.println s!"[drive] processed {demoLog.length} events, persisted {bytes.size} bytes to {path}"
      IO.println "[drive] --- live coordination state ---"
      IO.print (renderState st)
  | ["replay", path] => do
      let bytes ← IO.FS.readBinFile path
      IO.println s!"[replay] read {bytes.size} bytes from {path} (fresh process, empty memory)"
      match decodeLog bytes.toList with
      | some (events, []) => do
          let st := replay events
          IO.println s!"[replay] decoded {events.length} events, replayed from empty"
          IO.println "[replay] --- reconstructed coordination state ---"
          IO.print (renderState st)
      | some (_, _ :: _) => IO.println "[replay] ERROR: trailing bytes after log"
      | none => IO.println "[replay] ERROR: log failed to decode"
  | _ => IO.println "usage: (drive|replay) <logfile>"
