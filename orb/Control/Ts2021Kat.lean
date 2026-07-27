import Control.Ts2021Wire
/-!
# Control.Ts2021Kat — the byte-exact Noise_IK known-answer test

A REAL known-answer test for the `Control.Ts2021Wire` Noise_IK handshake against
a **public, independent** test vector: the `Noise_IK_25519_ChaChaPoly_BLAKE2s`
entry from `github.com/rweather/noise-c` `tests/vector/noise-c-basic.txt` (the
canonical Noise reference test vectors; the same protocol ts2021 speaks). The
vector fixes the static/ephemeral keypairs, the prologue and the payloads, and
gives the exact ciphertext bytes of handshake messages 1 and 2 plus the final
`handshake_hash`. This exe drives `noiseInitiation` / `readInitiation` /
`noiseResponse` / `readResponse` with those inputs and checks that drorb's
transcript reproduces the published bytes **exactly** — validating the whole
`Noise_IK` core (InitializeSymmetric ‖ prologue ‖ rs ‖ e ‖ es ‖ s ‖ ss ‖ ee ‖ se ‖
encrypt) over the audited/verified primitives (X25519 · ChaCha20-Poly1305
EverCrypt · BLAKE2s). It links the same crypto shim as `Crypto.SelfTest`.
-/

open Control.Ts2021Wire

namespace Control.Ts2021Kat

/-- ByteArray equality by contents. -/
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

/-- Encode bytes as a lowercase hex string (for diagnostics). -/
def baHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList
  String.join (b.data.toList.map (fun x =>
    String.mk [d[x.toNat / 16]!, d[x.toNat % 16]!]))

/-! ## The noise-c vector: `Noise_IK_25519_ChaChaPoly_BLAKE2s` -/

def initPrologue : ByteArray := hexBA "50726f6c6f677565313233"
def siPriv : ByteArray := hexBA "e61ef9919cde45dd5f82166404bd08e38bceb5dfdfded0a34c8df7ed542214d1"
def eiPriv : ByteArray := hexBA "893e28b9dc6ca8d611ab664754b8ceb7bac5117349a4439a6b0569da977c464a"
def rsPub  : ByteArray := hexBA "31e0303fd6418d2f8c0e78b91f22e8caed0fbe48656dcf4767e4834f701b8f62"
def srPriv : ByteArray := hexBA "4a3acbfdb163dec651dfa3194dece676d437029c62a408b4c5ea9114246e4893"
def erPriv : ByteArray := hexBA "bbdb4cdbd309f1a1f2e1456967fe288cadd6f712d65dc7b7793d5e63da6b375b"
def msg1Payload : ByteArray := hexBA "4c756477696720766f6e204d69736573"
def msg1Ct : ByteArray := hexBA ("ca35def5ae56cec33dc2036731ab14896bc4c75dbb07a61f879f8e3afa4c7944" ++
  "0b03ddc7aac5123d06a1b23b71670e32e76c28239a7ca4ac8f784de7e44c1adb" ++
  "78f2058771dfd4229fbdc85c5fba3b587b1d171ce368229c7b752ac25b8faf4e" ++
  "7b2fab7326f0d6fa1fdbef58de623245")
def msg2Payload : ByteArray := hexBA "4d757272617920526f746862617264"
def msg2Ct : ByteArray := hexBA ("95ebc60d2b1fa672c1f46a8aa265ef51bfe38e7ccb39ec5be34069f144808843" ++
  "d9b5a8927f0ac9655ef76833bc7e55269c081ec38c61031f76fe15b2aaaad5")
def handshakeHash : ByteArray :=
  hexBA "45e34c56ca0de9c348e104edcf503035e5559ceed661ac22916f6f171696d994"

/-! ## The KAT run -/

/-- Run the full Noise_IK handshake on the vector inputs and return per-check
results. `none` anywhere (X25519 low-order point, AEAD auth failure) collapses to
a single failed check. -/
def runKat : List (String × Bool) :=
  match go with
  | some cs => cs
  | none    => [("handshake completed (no crypto failure)", false)]
where go : Option (List (String × Bool)) := do
  let siPub ← Crypto.x25519Base siPriv
  let eiPub ← Crypto.x25519Base eiPriv
  let erPub ← Crypto.x25519Base erPriv
  let srPub ← Crypto.x25519Base srPriv
  -- initiator builds message 1
  let (m1, si) ← noiseInitiation initPrologue siPriv siPub eiPriv eiPub rsPub msg1Payload
  -- responder reads message 1
  let (eiPub2, siPub2, pl1, sR) ← readInitiation initPrologue srPriv srPub m1
  -- responder builds message 2
  let (m2, sRespPost) ← noiseResponse sR erPriv erPub eiPub2 siPub2 msg2Payload
  -- initiator reads message 2
  let (pl2, sIPost) ← readResponse si eiPriv siPriv m2
  let (rk1, rk2) := sRespPost.split
  let (ik1, ik2) := sIPost.split
  -- ts2021 wire-framing offset demonstration (empty payload, version 82)
  let (frame, _) ← mkTs2021Initiation 82 siPriv siPub eiPriv eiPub rsPub
  let fa : ByteArray := ⟨frame.toArray⟩
  pure [
    ("responder derives srPub == rsPub (public static)", baEq srPub rsPub),
    ("message 1 bytes == noise-c vector ciphertext (byte-exact)", baEq m1 msg1Ct),
    ("responder recovers e_i public", baEq eiPub2 eiPub),
    ("responder decrypts initiator static s_i (== derived pub)", baEq siPub2 siPub),
    ("responder recovers msg-1 payload", baEq pl1 msg1Payload),
    ("message 2 bytes == noise-c vector ciphertext (byte-exact)", baEq m2 msg2Ct),
    ("initiator recovers msg-2 payload", baEq pl2 msg2Payload),
    ("responder final transcript hash == vector handshake_hash", baEq sRespPost.h handshakeHash),
    ("initiator final transcript hash == vector handshake_hash", baEq sIPost.h handshakeHash),
    ("derived transport keys agree (k1)", baEq rk1 ik1),
    ("derived transport keys agree (k2)", baEq rk2 ik2),
    ("ts2021 initiation frame length == 101", frame.length == 101),
    ("ts2021 frame [0:2] version == 0x0052 (82)", baEq (fa.extract 0 2) (hexBA "0052")),
    ("ts2021 frame [2] msgType == 1 (initiation)", frame[2]! == 1),
    ("ts2021 frame [3:5] payload len == 0x0060 (96)", baEq (fa.extract 3 5) (hexBA "0060")),
    ("ts2021 frame [5:37] ephemeral == e_i public (offset)", baEq (fa.extract 5 37) eiPub),
    ("ts2021 frame [37:85] encrypted-static is 48 bytes (offset)", (fa.extract 37 85).size == 48),
    ("ts2021 frame [85:101] payload tag is 16 bytes (offset)", (fa.extract 85 101).size == 16)
  ]

def main : IO UInt32 := do
  IO.println "== Control.Ts2021Wire — Noise_IK_25519_ChaChaPoly_BLAKE2s KAT (noise-c vector) =="
  let cs := runKat
  for (name, ok) in cs do
    IO.println s!"  [{if ok then "PASS" else "FAIL"}] {name}"
  if cs.all (·.2) then
    IO.println s!"ALL {cs.length} CHECKS PASS"
    pure 0
  else
    IO.println "SOME CHECKS FAILED"
    pure 1

end Control.Ts2021Kat

def main : IO UInt32 := Control.Ts2021Kat.main
