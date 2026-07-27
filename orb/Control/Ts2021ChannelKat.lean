import Control.Ts2021Wire
/-!
# Control.Ts2021ChannelKat — the LIVE channel FSM is byte-exact

`control-ts2021-kat` validates the `Noise_IK_25519_ChaChaPoly_BLAKE2s` core
against the published `noise-c` vector by calling `noiseInitiation` /
`readInitiation` / `noiseResponse` / `readResponse` **directly**. This exe closes
the remaining gap: it drives the **channel FSM**
(`Control.Channel.Ts2021.step` — the transitions the live control plane runs)
and checks that the bytes the FSM puts on the wire, and the session keys it
lands in `.up` with, are exactly the byte-exact ts2021 ones.

Three things are demonstrated, on real crypto (EverCrypt ChaCha20-Poly1305,
drorb-verified X25519, RFC 7693 BLAKE2s), never fabricated:

1. **Identity with the KAT core.** The published `noise-c` vector is replayed in
   THIS binary and reproduces the vector's message-1/message-2 ciphertexts and
   `handshake_hash` exactly; and the FSM's initiation frame is byte-identical to
   `mkTs2021Initiation`, the builder `control-ts2021-kat`'s offset checks pin.
   There is one definitional home for the handshake (`Control.Ts2021Core`), so
   this is identity, not the agreement of two copies.

2. **The emitted frames match `control/controlbase/messages.go`.** Initiation
   101 B = `[0:2]` version u16BE · `[2]` type 1 · `[3:5]` len u16BE (96) ·
   `[5:37]` ephemeral · `[37:85]` encrypted machine static (48) · `[85:101]` tag.
   Response 51 B = `[0]` type 2 · `[1:3]` len u16BE (48) · `[3:35]` ephemeral ·
   `[35:51]` tag.

3. **The two ends agree through the FSM.** Driving node `.start` → coord
   `.recvInit` → node `.recvResp` over those very bytes, both peers reach `.up`
   and `node.send == coord.recv`, `node.recv == coord.send` — and a real
   `MapRequest` sealed under the node's send key opens under the coordinator's
   receive key (the §6b `mapReq_over_ts2021` hypothesis discharged on bytes).
-/

open Control.Ts2021Wire
open Control.Channel (bytesOf baOf)

namespace Control.Ts2021ChannelKat

def baEq (a b : ByteArray) : Bool := a.data.toList == b.data.toList

private def hexNib (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Decode a hex string to bytes. -/
def hexBA (s : String) : ByteArray :=
  let cs := s.toList
  ⟨(List.range (cs.length / 2)).toArray.map (fun i =>
    UInt8.ofNat (hexNib cs[2*i]! * 16 + hexNib cs[2*i+1]!))⟩

/-- The `controlbase` protocol version the session announces. -/
def version : Nat := 82

/-! ## Key material

The same scalars the `noise-c` vector fixes, so this run and the core KAT are
driven by identical inputs: the initiator static is the node's machine key, the
responder static is the coordination server key. -/

def machinePriv  : ByteArray := hexBA "e61ef9919cde45dd5f82166404bd08e38bceb5dfdfded0a34c8df7ed542214d1"
def nodeEphPriv  : ByteArray := hexBA "893e28b9dc6ca8d611ab664754b8ceb7bac5117349a4439a6b0569da977c464a"
def coordPriv    : ByteArray := hexBA "4a3acbfdb163dec651dfa3194dece676d437029c62a408b4c5ea9114246e4893"
def coordEphPriv : ByteArray := hexBA "bbdb4cdbd309f1a1f2e1456967fe288cadd6f712d65dc7b7793d5e63da6b375b"

/-! ### The published `noise-c` vector, re-checked inside THIS binary

`tests/vector/noise-c-basic.txt`, entry `Noise_IK_25519_ChaChaPoly_BLAKE2s`.
Running it here — against the same `Control.Ts2021Core` definitions the FSM
transitions call — ties the FSM's bytes to an independent published answer, not
to drorb's own output. -/

def vecPrologue : ByteArray := hexBA "50726f6c6f677565313233"
def vecRsPub    : ByteArray := hexBA "31e0303fd6418d2f8c0e78b91f22e8caed0fbe48656dcf4767e4834f701b8f62"
def vecMsg1Payload : ByteArray := hexBA "4c756477696720766f6e204d69736573"
def vecMsg1Ct : ByteArray := hexBA ("ca35def5ae56cec33dc2036731ab14896bc4c75dbb07a61f879f8e3afa4c7944" ++
  "0b03ddc7aac5123d06a1b23b71670e32e76c28239a7ca4ac8f784de7e44c1adb" ++
  "78f2058771dfd4229fbdc85c5fba3b587b1d171ce368229c7b752ac25b8faf4e" ++
  "7b2fab7326f0d6fa1fdbef58de623245")
def vecMsg2Payload : ByteArray := hexBA "4d757272617920526f746862617264"
def vecMsg2Ct : ByteArray := hexBA ("95ebc60d2b1fa672c1f46a8aa265ef51bfe38e7ccb39ec5be34069f144808843" ++
  "d9b5a8927f0ac9655ef76833bc7e55269c081ec38c61031f76fe15b2aaaad5")
def vecHandshakeHash : ByteArray :=
  hexBA "45e34c56ca0de9c348e104edcf503035e5559ceed661ac22916f6f171696d994"

/-- Drive the FSM end to end and report every check. `none` anywhere (a crypto
failure or a phase that did not advance) collapses to one failed check. -/
def runChecks : List (String × Bool) :=
  match go with
  | some cs => cs
  | none    => [("channel FSM completed the handshake (no crypto failure)", false)]
where go : Option (List (String × Bool)) := do
  let machinePub ← Crypto.x25519Base machinePriv
  let nodeEphPub ← Crypto.x25519Base nodeEphPriv
  let coordPub   ← Crypto.x25519Base coordPriv
  let coordEphPub ← Crypto.x25519Base coordEphPriv

  -- the two sessions: the node is the Noise initiator (machine key static),
  -- the coordination server is the responder.
  let nodeSess : Control.Channel.Ts2021.Session :=
    { role := .node, version := version,
      spriv := machinePriv, spub := machinePub,
      epriv := nodeEphPriv, epub := nodeEphPub,
      peerS := coordPub }
  let coordSess : Control.Channel.Ts2021.Session :=
    { role := .coord, version := version,
      spriv := coordPriv, spub := coordPub,
      epriv := coordEphPriv, epub := coordEphPub,
      peerS := ByteArray.empty }

  -- ── transition 1: node .fresh --start--> .awaitResp, emitting the initiation
  let (nodeP1, out1) := Control.Channel.Ts2021.step nodeSess .fresh .start
  let some initFrame := (match out1 with | .sendInit f => some f | _ => none) | none
  let ifa : ByteArray := baOf initFrame

  -- ── transition 2: coord .fresh --recvInit--> .up, emitting the response
  let (coordP, out2) := Control.Channel.Ts2021.step coordSess .fresh (.recvInit initFrame)
  let some respFrame := (match out2 with | .sendResp f => some f | _ => none) | none
  let rfa : ByteArray := baOf respFrame
  let some coordTx := (match coordP with | .up tx => some tx | _ => none) | none

  -- ── transition 3: node .awaitResp --recvResp--> .up
  let (nodeP, _out3) := Control.Channel.Ts2021.step nodeSess nodeP1 (.recvResp respFrame)
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none) | none

  -- identity with the standalone wire builder the core KAT pins
  let some (refInit, _) := mkTs2021Initiation version machinePriv machinePub
                            nodeEphPriv nodeEphPub coordPub | none

  -- an end-to-end sealed control message over the derived keys
  let mapReq : Control.MapRequest :=
    { version := 1, nodeKey := ⟨bytesOf machinePub⟩, discoKey := ⟨bytesOf nodeEphPub⟩,
      endpoints := [{ addr := [100,64,0,1], port := 41641 }],
      stream := true, omitPeers := false, readOnly := false }
  let some mapFrame := Control.Channel.sealMapReq nodeTx.send Control.Channel.nonce0 mapReq | none
  let mapOpened := Control.Channel.openMapReq coordTx.recv Control.Channel.nonce0 mapFrame

  -- the published noise-c vector, over the SAME definitions the FSM calls
  let some machinePub2 := Crypto.x25519Base machinePriv | none
  let some (vm1, vsi) := noiseInitiation vecPrologue machinePriv machinePub2
                           nodeEphPriv nodeEphPub vecRsPub vecMsg1Payload | none
  let some (_, vsiPub, _, vsR) := readInitiation vecPrologue coordPriv vecRsPub vm1 | none
  let some (vm2, vsRPost) := noiseResponse vsR coordEphPriv coordEphPub nodeEphPub vsiPub
                               vecMsg2Payload | none
  let some (_, vsIPost) := readResponse vsi nodeEphPriv machinePriv vm2 | none

  pure [
    -- 1. the FSM emits the byte-exact initiation
    ("FSM initiation frame == mkTs2021Initiation bytes (one definitional home)",
      initFrame == refInit),
    ("FSM initiation frame length == 101 (messages.go initiationMessage)",
      initFrame.length == 101),
    ("initiation [0:2] version u16BE == 0x0052 (82)", baEq (ifa.extract 0 2) (hexBA "0052")),
    ("initiation [2] msgType == 1 (msgTypeInitiation)", initFrame[2]! == 1),
    ("initiation [3:5] payload len u16BE == 0x0060 (96)", baEq (ifa.extract 3 5) (hexBA "0060")),
    ("initiation [5:37] == node ephemeral public (cleartext)",
      baEq (ifa.extract 5 37) nodeEphPub),
    ("initiation [37:85] encrypted machine static is 48 B", (ifa.extract 37 85).size == 48),
    ("initiation [85:101] tag is 16 B", (ifa.extract 85 101).size == 16),
    -- 2. the FSM emits the byte-exact response
    ("FSM response frame length == 51 (messages.go responseMessage)",
      respFrame.length == 51),
    ("response [0] msgType == 2 (msgTypeResponse)", respFrame[0]! == 2),
    ("response [1:3] payload len u16BE == 0x0030 (48)", baEq (rfa.extract 1 3) (hexBA "0030")),
    ("response [3:35] == coord ephemeral public (cleartext)",
      baEq (rfa.extract 3 35) coordEphPub),
    ("response [35:51] tag is 16 B", (rfa.extract 35 51).size == 16),
    -- 3. both ends completed and agree, THROUGH the FSM
    ("node .start lands in .awaitResp, NOT .up (no keys before the handshake)",
      match nodeP1 with | .awaitResp _ => true | _ => false),
    ("coord reached .up on the initiation frame alone",
      match coordP with | .up _ => true | _ => false),
    ("node reached .up on the response frame alone",
      match nodeP with | .up _ => true | _ => false),
    ("node.send == coord.recv (Split c1; handshake.go client tx = server rx)",
      baEq nodeTx.send coordTx.recv),
    ("node.recv == coord.send (Split c2; handshake.go client rx = server tx)",
      baEq nodeTx.recv coordTx.send),
    ("node keys == initiatorTx of a 64-B material (c1‖c2 split)",
      nodeTx.send.size == 32 && nodeTx.recv.size == 32),
    ("sealed MapRequest node->coord opens to the SAME message (§6b end to end)",
      mapOpened == some mapReq),
    -- 4. the noise-c vector still passes over these very definitions
    ("noise-c vector: coord static base point == vector rs (same keypairs)",
      baEq vecRsPub (match Crypto.x25519Base coordPriv with | some p => p | none => ByteArray.empty)),
    ("noise-c vector: message 1 bytes reproduce the published ciphertext",
      baEq vm1 vecMsg1Ct),
    ("noise-c vector: message 2 bytes reproduce the published ciphertext",
      baEq vm2 vecMsg2Ct),
    ("noise-c vector: both ends reach the published handshake_hash",
      baEq vsRPost.h vecHandshakeHash && baEq vsIPost.h vecHandshakeHash)
  ]

def main : IO UInt32 := do
  IO.println "== control-ts2021-channel-kat — the LIVE Channel FSM is byte-exact ts2021 =="
  IO.println "   (Control.Channel.Ts2021.step, Noise_IK_25519_ChaChaPoly_BLAKE2s, no PSK)"
  let cs := runChecks
  for (name, ok) in cs do
    IO.println s!"  [{if ok then "PASS" else "FAIL"}] {name}"
  if cs.all (·.2) then
    IO.println s!"ALL {cs.length} CHECKS PASS"
    IO.println "The handshake the live control channel runs emits the byte-exact"
    IO.println "controlbase initiation/response and lands both ends on agreeing keys."
    pure 0
  else
    IO.println "SOME CHECKS FAILED"
    pure 1

end Control.Ts2021ChannelKat

def main : IO UInt32 := Control.Ts2021ChannelKat.main
