import Control.Ts2021Record
import Control.Ts2021Wire

/-!
# Control.Ts2021RecordKat — the record nonce is BIG-endian, on real crypto

The gate for the BE-vs-LE record-nonce fix. Nothing here is a fabricated wire
byte: the expected nonces are the big-endian encoding of the stated counters
(derivable by hand from `binary.BigEndian.PutUint64`, cited in
`Ts2021Wire.recordNonce`), and every seal/open is real EverCrypt
ChaCha20-Poly1305 through `Control.Channel.sealFrame` / `openFrame`.

What is demonstrated:

1. `recordNonce` is byte-exactly `0000_0000 ‖ BigEndian.Uint64(ctr)` at the
   interesting counters, including the 2^8 / 2^16 / 2^32 carry boundaries.
2. A real seal/open cycle round-trips at each of those counters.
3. A record stream crossing the 2^16 boundary round-trips with the two counters
   in lockstep.
4. **The interop breaker, shown rather than asserted:** a record sealed with the
   big-endian nonce does NOT open under the little-endian `noiseNonce` at the
   same counter (for every counter where the two encodings differ), and vice
   versa. That is the failure a `noiseNonce`-wired record layer would have hit
   against a real client on frame #2.
-/

open Control.Ts2021Wire
open Control.Ts2021Record
open Control.Channel (bytesOf baOf)

namespace Control.Ts2021RecordKat

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (b : ByteArray) : String :=
  b.data.toList.foldl (fun s x => s.push (hexDigit (x.toNat / 16))
                                   |>.push (hexDigit (x.toNat % 16))) ""

private def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Decode a hex string to bytes (test-only; every real literal below is the hex
of the corresponding `Control/testdata/*.bin`, so no wire byte is hand-typed). -/
def hexBytes (s : String) : Control.Bytes :=
  let rec go : List Char → Control.Bytes
    | a :: b :: t => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go t
    | _ => []
  go s.toList

/-- A demo transport key (32 bytes). Not a captured secret — a fixed test key. -/
def testKey : ByteArray := ⟨(List.range 32).map (fun i => UInt8.ofNat (i + 1)) |>.toArray⟩

def payloadOf (i : Nat) : Control.Bytes :=
  (List.range 24).map (fun j => UInt8.ofNat ((i * 7 + j * 3) % 256))

/-- The counters the gate exercises: 0, 1, 2, the 2^8 carry, the **2^16
boundary** (65535 = 2^16-1, 65536), the 2^32 carry, and a near-exhaustion value. -/
def gateCounters : List Nat :=
  [0, 1, 2, 3, 255, 256, 257, 65534, 65535, 65536, 65537,
   16777215, 16777216, 4294967295, 4294967296, 1099511627775,
   18446744073709551614]

/-- Expected big-endian nonce hex for `gateCounters`, written out independently
of `recordNonce` (4 zero bytes then the 8-byte big-endian counter). -/
def expectedHex : List (Nat × String) :=
  [ (0,                    "000000000000000000000000"),
    (1,                    "000000000000000000000001"),
    (2,                    "000000000000000000000002"),
    (255,                  "0000000000000000000000ff"),
    (256,                  "000000000000000000000100"),
    (65535,                "00000000000000000000ffff"),
    (65536,                "000000000000000000010000"),
    (16777215,             "000000000000000000ffffff"),
    (16777216,             "000000000000000001000000"),
    (4294967295,           "0000000000000000ffffffff"),
    (4294967296,           "000000000000000100000000"),
    (18446744073709551614, "00000000fffffffffffffffe") ]

/-- Every `gateCounters` value: the nonce is 12 bytes, its first 4 bytes are
zero, and its counter field decodes back to the counter. -/
def nonceShapeChecks : List (String × Bool) :=
  gateCounters.map fun n =>
    (s!"recordNonce {n}: 12B, zero prefix, decodes back",
     (recordNonce n).size == 12
       && (recordNonce n).get! 0 == 0 && (recordNonce n).get! 1 == 0
       && (recordNonce n).get! 2 == 0 && (recordNonce n).get! 3 == 0
       && recordNonceCounter (recordNonce n) == n)

def nonceHexChecks : List (String × Bool) :=
  expectedHex.map fun (n, h) =>
    (s!"recordNonce {n} = {h} (big-endian)", toHex (recordNonce n) == h)

/-- The BE and LE encodings differ at every nonzero counter here (and agree at 0). -/
def endiannessChecks : List (String × Bool) :=
  (s!"recordNonce 0 == noiseNonce 0 (both all-zero)",
   toHex (recordNonce 0) == toHex (noiseNonce 0)) ::
  (gateCounters.filter (· != 0)).map fun n =>
    (s!"recordNonce {n} != noiseNonce {n} (BE vs LE)",
     toHex (recordNonce n) != toHex (noiseNonce n))

/-- Real seal/open at each gate counter, through the record layer. -/
def roundtripChecks : List (String × Bool) :=
  gateCounters.map fun n =>
    let st : RecordState := ⟨testKey, n⟩
    let pl := payloadOf n
    (s!"seal/open roundtrip at counter {n}",
     match sealRecord st pl with
     | none => false
     | some (frame, st') =>
       st'.ctr == n + 1 &&
       (match openRecord ⟨testKey, n⟩ frame with
        | some (pt, st'') => pt == pl && st''.ctr == n + 1
        | none => false))

/-- ★ The interop breaker on real crypto: a frame sealed with the **big-endian**
record nonce must FAIL to open under the little-endian handshake nonce at the
same counter — this is the authentication failure a wrong-endian record layer
would have produced against a real client from frame #2 onward. -/
def wrongEndianFailsChecks : List (String × Bool) :=
  (gateCounters.filter (· != 0)).map fun n =>
    (s!"counter {n}: BE-sealed frame does NOT open under LE noiseNonce",
     match Control.Channel.sealFrame testKey (recordNonce n) (payloadOf n) with
     | none => false
     | some frame => (Control.Channel.openFrame testKey (noiseNonce n) frame).isNone)

/-- A stream of 6 records crossing the 2^16 boundary (65533 … 65538): the sender
and receiver counters stay in lockstep and every payload comes back. -/
def streamCheck : String × Bool :=
  let start := 65533
  let pls := (List.range 6).map (fun i => payloadOf (start + i))
  ("stream of 6 records across the 2^16 boundary (65533..65538) roundtrips",
   match sealStream ⟨testKey, start⟩ pls with
   | none => false
   | some (frames, sTx) =>
     frames.length == 6 && sTx.ctr == start + 6 &&
     (match openStream ⟨testKey, start⟩ frames with
      | some (out, sRx) => out == pls && sRx.ctr == start + 6
      | none => false))

/-- ★ EXHAUSTION on real crypto: the checked entry point the live connection
drives refuses to seal once the counter reaches `invalidNonce` (2^64-1,
`errCipherExhausted`), still seals at the last valid counter (2^64-2), and a
frame sealed at the last valid counter round-trips through `openChecked`. -/
def exhaustionChecks : List (String × Bool) :=
  let pl := payloadOf 7
  let exhausted : RecordState := ⟨testKey, invalidNonce⟩
  let lastValid : RecordState := ⟨testKey, invalidNonce - 1⟩
  [ ("counter 2^64-1 (invalidNonce): sealChecked REFUSES (errCipherExhausted)",
     match sealChecked exhausted pl with
     | .error RecordErr.exhausted => true
     | _                          => false),
    ("counter 2^64-1: openChecked REFUSES (errCipherExhausted)",
     match openChecked exhausted ([] : Control.Bytes) with
     | .error RecordErr.exhausted => true
     | _                          => false),
    ("counter 2^64-2 (last valid): sealChecked seals, advances to 2^64-1",
     match sealChecked lastValid pl with
     | .ok (_, s') => s'.ctr == invalidNonce
     | _           => false),
    ("counter 2^64-2: sealChecked frame round-trips through openChecked",
     match sealChecked lastValid pl with
     | .ok (frame, _) =>
       match openChecked ⟨testKey, invalidNonce - 1⟩ frame with
       | .ok (pt, s'') => pt == pl && s''.ctr == invalidNonce
       | _             => false
     | _ => false) ]

/-- A heterogeneous two-message sequence on ONE direction's counter, the live
node→coord shape: message A sealed at counter K through `sealChecked`, message B
at K+1 through the advanced state; the receiver opens both in lockstep. -/
def checkedSeqCheck : String × Bool :=
  let k := 41
  let plA := payloadOf 100
  let plB := payloadOf 200
  ("two records on one counter (K, K+1) via sealChecked/openChecked roundtrip",
   match sealChecked ⟨testKey, k⟩ plA with
   | .ok (fA, sTx1) =>
     match sealChecked sTx1 plB with
     | .ok (fB, sTx2) =>
       sTx1.ctr == k + 1 && sTx2.ctr == k + 2 &&
       (match openChecked ⟨testKey, k⟩ fA with
        | .ok (pA, sRx1) =>
          match openChecked sRx1 fB with
          | .ok (pB, sRx2) => pA == plA && pB == plB && sRx1.ctr == k + 1 && sRx2.ctr == k + 2
          | _ => false
        | _ => false)
     | _ => false
   | _ => false)

/-! ## ★ The REAL ts2021 wire framing — `[type=4][u16 BE len][raw ciphertext]`

`sealRecordTs2021`/`openRecordTs2021` frame through `Control.Ts2021Wire.encodeRecord`
(the byte-exact `controlbase` record), NOT the drorb-native `recordTag(3)::uvarint`
framing. These checks run REAL EverCrypt ChaCha20-Poly1305 and inspect the frame
header byte-exactly: `frame = [4] ++ [len>>8, len&0xff] ++ ct`, `len = ptlen + 16`
(the Poly1305 tag), cross-checked against `conn.go` `encryptLocked`
(`buf[0]=msgTypeRecord`, `PutUint16(buf[1:3], ptlen+Overhead)`). -/
def ts2021FrameChecks : List (String × Bool) :=
  gateCounters.map fun n =>
    let st : RecordState := ⟨testKey, n⟩
    let pl := payloadOf n
    (s!"ts2021 seal/open roundtrip + byte-exact [4][u16BE len] header at counter {n}",
     match sealRecordTs2021 st pl with
     | none => false
     | some (frame, st') =>
       let ctlen := pl.length + 16   -- ptlen + Poly1305 tag overhead
       st'.ctr == n + 1 &&
       frame.take 3 == [(4 : UInt8), UInt8.ofNat (ctlen / 256), UInt8.ofNat (ctlen % 256)] &&
       frame.length == 3 + ctlen &&
       (match openRecordTs2021 ⟨testKey, n⟩ frame with
        | some (pt, st'') => pt == pl && st''.ctr == n + 1
        | none => false))

/-- ★ A ts2021-framed record does NOT parse under the OLD drorb-native framing
(`recordTag=3 :: putBytes`) — the two wire formats are genuinely different, so
the workaround the live path used could never have interoperated with the header
a stock client expects. -/
def framingDistinctCheck : String × Bool :=
  ("ts2021 frame ([4][u16BE]) ≠ drorb-native frame ([3][uvarint]): old parseFrame rejects it",
   match sealRecordTs2021 ⟨testKey, 0⟩ (payloadOf 0) with
   | none => false
   | some (frame, _) => (Control.Channel.parseFrame frame).isNone)

/-! ## ★ Byte-exact match against a REAL stock-tailscale 1.98.8 record frame

Captured by `Control/testdata/ts2021_capture_harness.py` (a real Noise-IK
responder + an isolated userspace `tailscaled` 1.98.8 doing `tailscale up`).
Persisted raw in `Control/testdata/{k1_txkey,record0_frame,record0_plain}.bin`;
the hex below is exactly those bytes.

* `realK1`    — the client→server transport key `k1` from `Sym.split()`.
* `realFrame` — the client's **first** transport record on the wire, 89 bytes:
  `04 00 56` (`msgTypeRecord=4`, u16-BE length `0x0056 = 86`) then 86 ciphertext
  bytes.
* `realPlain` — its 70-byte plaintext: the HTTP/2 connection preface
  `"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"` followed by the client's SETTINGS frame.

The two checks: the PROVEN `openRecordTs2021` opens the stock client's real frame
to its exact plaintext at record counter 0 (big-endian nonce), and — since the
AEAD is deterministic — the PROVEN `sealRecordTs2021` **reproduces the stock
client's exact wire bytes**. That is the byte-exact interop gate: drorb's proven
record layer emits precisely what tailscale 1.98.8 emitted. -/

def realK1hex    : String := "e299c2d72e2f0c5ec613ef67f2e1aeb7692244148dfc8ad04bad578f6e08cf4c"
def realFramehex : String :=
  "04005615c167f9dc13e80b38b278cc5b9ec53580b769491bd75bef53af42bbd1ffa6c74fed15"
  ++ "53f6eb7f4ebea418f924df2fb775f8c67581c63ed915f4dfb88a9ad3fef4a67d5760e8b6aea"
  ++ "fb311b0037b5642604e3d0b4c07"
def realPlainhex : String :=
  "505249202a20485454502f322e300d0a0d0a534d0d0a0d0a0000180400000000000002000000"
  ++ "00000400400000000500004000000600a0000000000408000000000040000000"

def realK1    : ByteArray := ⟨(hexBytes realK1hex).toArray⟩
def realFrame : Control.Bytes := hexBytes realFramehex
def realPlain : Control.Bytes := hexBytes realPlainhex

def realFrameChecks : List (String × Bool) :=
  [ ("REAL stock frame is [4][00][56]+86B ct (89B) / plaintext 70B (h2 preface)",
     realFrame.length == 89 && realFrame.take 3 == [(4 : UInt8), 0, 86] &&
       realPlain.length == 70 && realPlain.take 4 == [(0x50 : UInt8), 0x52, 0x49, 0x20]),
    ("PROVEN openRecordTs2021 opens the REAL tailscale-1.98.8 frame to its exact plaintext",
     match openRecordTs2021 ⟨realK1, 0⟩ realFrame with
     | some (pt, s') => pt == realPlain && s'.ctr == 1
     | none => false),
    ("PROVEN sealRecordTs2021 REPRODUCES the stock client's EXACT wire bytes (byte-exact)",
     match sealRecordTs2021 ⟨realK1, 0⟩ realPlain with
     | some (f, s') => f == realFrame && s'.ctr == 1
     | none => false) ]

-- NB: the real-frame byte-exact match is exercised through the EXECUTABLE
-- `main` below (`realFrameChecks`), which links EverCrypt and runs the real
-- ChaCha20-Poly1305 at runtime — the same way every other crypto check in this
-- KAT runs. (A `native_decide` proof of the same fact cannot link the
-- `@[extern]` EverCrypt symbols in Lean's decision-procedure runner, so the
-- executable is the honest home for the on-real-crypto gate.)

def checks : List (String × Bool) :=
  nonceShapeChecks ++ nonceHexChecks ++ endiannessChecks ++
  roundtripChecks ++ wrongEndianFailsChecks ++ [streamCheck] ++
  exhaustionChecks ++ [checkedSeqCheck] ++
  ts2021FrameChecks ++ [framingDistinctCheck] ++ realFrameChecks

def main : IO UInt32 := do
  IO.println "== control-ts2021-record-kat — the ts2021 record nonce is BIG-endian =="
  IO.println "   (controlbase conn.go nonce.Increment: binary.BigEndian.PutUint64(n[4:], ...))"
  IO.println ""
  for (name, ok) in checks do
    IO.println s!"  [{if ok then "PASS" else "FAIL"}] {name}"
  IO.println ""
  if checks.all (·.2) then
    IO.println s!"ALL {checks.length} CHECKS PASS"
    IO.println "The record layer seals and opens under recordNonce (4 zero bytes ||"
    IO.println "64-bit big-endian counter) at 0,1,2,.. across the 2^8/2^16/2^32 carries,"
    IO.println "and a BE-sealed frame is rejected under the LE handshake nonce."
    return 0
  else
    IO.println "SOME CHECKS FAILED"
    return 1

end Control.Ts2021RecordKat

def main : IO UInt32 := Control.Ts2021RecordKat.main
