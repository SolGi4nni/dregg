import Stun
import Ice
/-!
# RFC 5769 test vectors driven through the STUN codec and server

The four sample messages RFC 5769 publishes, checked byte-for-byte against
`Stun.parse`, `Stun.fingerprintOk`, `Stun.messageIntegrityOk`, and the
authenticated server step `Stun.serve` — plus the RFC 5389 §10.1.2 error
paths, the RFC 5389 §15.4 long-term key derivation (RFC 1321 MD5, computed
in-core), RFC 5780 CHANGE-REQUEST handling, and the RFC 8445 §7.2.2 / §7.3.1.1
connectivity-check messages. Each line of output is `PASS`/`FAIL` plus the
check name, then a summary count.

Run from the repository root: `lake env lean --run conformance/stun/vectors.lean`
-/

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

partial def fromHex (s : String) : List UInt8 :=
  let cs := s.data.filter fun c => c ≠ ' ' ∧ c ≠ '\n'
  let rec go : List Char → List UInt8
    | hi :: lo :: rest => UInt8.ofNat (hexVal hi * 16 + hexVal lo) :: go rest
    | _ => []
  go cs

/-- RFC 5769 §2.1 — sample Binding request (short-term credentials,
software "STUN test client", PRIORITY, ICE-CONTROLLED, USERNAME,
MESSAGE-INTEGRITY, FINGERPRINT). -/
def req21 : List UInt8 := fromHex
  ("000100582112a442b7e7a701bc34d686fa87dfae" ++
   "802200105354554e207465737420636c69656e74" ++
   "002400046e0001ff" ++
   "80290008932ff9b151263b36" ++
   "000600096576746a3a683676592020" ++ "20" ++
   "000800149aeaa70cbfd8cb56781ef2b5b2d3f249c1b571a2" ++
   "80280004e57a3bcf")

/-- RFC 5769 §2.2 — sample IPv4 Binding success response. -/
def resp22 : List UInt8 := fromHex
  ("0101003c2112a442b7e7a701bc34d686fa87dfae" ++
   "8022000b7465737420766563746f7220" ++
   "002000080001a147e112a643" ++
   "000800142b91f599fd9e90c38c7489f92af9ba53f06be7d7" ++
   "80280004c07d4c96")

/-- RFC 5769 §2.3 — sample IPv6 Binding success response. -/
def resp23 : List UInt8 := fromHex
  ("010100482112a442b7e7a701bc34d686fa87dfae" ++
   "8022000b7465737420766563746f7220" ++
   "002000140002a1470113a9faa5d3f179bc25f4b5bed2b9d9" ++
   "00080014a382954e4be67bf11784c97c8292c275bfe3ed41" ++
   "80280004c8fb0b4c")

/-- RFC 5769 §2.4 — sample request with long-term credentials
(key = MD5(username:realm:password)). -/
def req24 : List UInt8 := fromHex
  ("000100602112a44278ad3433c6ad72c029da412e" ++
   "00060012e3839ee38388e383aae38383e382afe382b90000" ++
   "0015001c662f2f3439396b3935346436" ++
   "4f4c33346f4c394653547679" ++ "36347341" ++
   "0014000b6578616d706c652e6f726700" ++
   "00080014f67024656dd64a3e02b8e0712e85c9a28ca89666")

/-- The §2.1/§2.2/§2.3 short-term key: the password. -/
def keyShort : List UInt8 := "VOkJxbRl1RmTxUk/WvJxBt".data.map fun c => UInt8.ofNat c.toNat

/-- The §2.1 USERNAME value: "evtj:h6vY". -/
def user21 : List UInt8 := "evtj:h6vY".data.map fun c => UInt8.ofNat c.toNat

/-- The §2.4 long-term key as RFC 5769 states it:
MD5("<username>:realm:password") with the SASLprep-processed password
"TheMatrIX" (RFC 5389 §15.4). -/
def keyLong : List UInt8 := fromHex "e8ca7ad59d5eb0518e312911d2dab2a9"

/-- The §2.4 USERNAME value (UTF-8). -/
def user24 : List UInt8 := fromHex "e3839ee38388e383aae38383e382afe382b9"

/-- The §2.4 REALM value: "example.org". -/
def realm24 : List UInt8 := "example.org".data.map fun c => UInt8.ofNat c.toNat

/-- The §2.4 SASLprep-processed password: "TheMatrIX". -/
def pass24 : List UInt8 := "TheMatrIX".data.map fun c => UInt8.ofNat c.toNat

/-- Error-code class and number carried by a response (§15.6). -/
def errorCodeOf (r : List UInt8) : Option (Nat × Nat) :=
  (Stun.parse r).bind fun m =>
    (Stun.findAttr Stun.attrErrorCode m.attrs).bind fun a =>
      match a.value with
      | _ :: _ :: cls :: num :: _ => some (cls.toNat, num.toNat)
      | _ => none

def check (counter : IO.Ref (Nat × Nat)) (name : String) (b : Bool) : IO Unit := do
  counter.modify fun (p, t) => (if b then p + 1 else p, t + 1)
  IO.println s!"{if b then "PASS" else "FAIL"} {name}"

def main : IO Unit := do
  let c ← IO.mkRef ((0, 0) : Nat × Nat)
  let check := check c
  -- §2.1 request
  check "2.1 parse request" (Stun.parse req21).isSome
  check "2.1 fingerprint verifies" (Stun.fingerprintOk req21)
  check "2.1 message-integrity verifies (short-term)"
    (Stun.messageIntegrityOk keyShort req21)
  -- server behavior on the §2.1 request: the ICE-flavored request carries
  -- short-term credentials, so drive the authenticated server step
  -- (RFC 5389 §10.1.2 / RFC 8445 §7.3)
  let src : Stun.Endpoint := { family := 1, port := 34059, addr := [192,0,2,1] }
  let cfg21 : Stun.Config := { auth := some { username := user21, key := keyShort } }
  let served := Stun.serve cfg21 (false, false) req21 src
  let resp := served.map (·.2)
  check "2.1 respond answers the ICE-flavored request" resp.isSome
  -- RFC 5389 §10.1.2 / RFC 8445 §7.3: the response to an integrity-protected
  -- request must itself carry MESSAGE-INTEGRITY
  let respHasMi := (resp.bind Stun.parse).map
    (fun m => m.attrs.any fun a => a.type == Stun.attrMessageIntegrity)
  check "2.1 response carries MESSAGE-INTEGRITY" (respHasMi.getD false)
  check "2.1 response MESSAGE-INTEGRITY verifies (same short-term key)"
    ((resp.map (Stun.messageIntegrityOk keyShort ·)).getD false)
  check "2.1 response FINGERPRINT verifies"
    ((resp.map Stun.fingerprintOk).getD false)
  let xored21 := ((resp.bind Stun.parse).bind fun m =>
    (Stun.findAttr Stun.attrXorMappedAddress m.attrs).bind fun a =>
      Stun.decodeXorMapped m.txid a.value)
  check "2.1 response XOR-MAPPED-ADDRESS reflects the source"
    (xored21 == some src)
  -- §10.1.2 error paths, driven with the same real vector
  let cfgWrongKey : Stun.Config :=
    { auth := some { username := user21,
                     key := "wrongwrongwrongwrong".data.map fun ch => UInt8.ofNat ch.toNat } }
  check "2.1 wrong key draws 401 Unauthorized (RFC 5389 10.1.2)"
    (((Stun.serve cfgWrongKey (false, false) req21 src).map (·.2)).bind errorCodeOf
      == some (4, 1))
  let cfgWrongUser : Stun.Config :=
    { auth := some { username := "other:user".data.map fun ch => UInt8.ofNat ch.toNat,
                     key := keyShort } }
  check "2.1 wrong username draws 401 Unauthorized (RFC 5389 10.1.2)"
    (((Stun.serve cfgWrongUser (false, false) req21 src).map (·.2)).bind errorCodeOf
      == some (4, 1))
  let bareReq := Stun.encode Stun.bindingRequest (req21.drop 8 |>.take 12) []
  check "credential-less request draws 400 Bad Request (RFC 5389 10.1.2)"
    (((Stun.serve cfg21 (false, false) bareReq src).map (·.2)).bind errorCodeOf
      == some (4, 0))
  -- §2.2 IPv4 response
  check "2.2 parse IPv4 response" (Stun.parse resp22).isSome
  check "2.2 fingerprint verifies" (Stun.fingerprintOk resp22)
  check "2.2 message-integrity verifies" (Stun.messageIntegrityOk keyShort resp22)
  let xored22 := ((Stun.parse resp22).bind fun m =>
    (m.attrs.find? fun a => a.type == Stun.attrXorMappedAddress).bind fun a =>
      Stun.decodeXorMapped m.txid a.value)
  check "2.2 XOR-MAPPED-ADDRESS decodes to 192.0.2.1:32853"
    (xored22 == some { family := 1, port := 32853, addr := [192,0,2,1] })
  -- §2.3 IPv6 response
  check "2.3 parse IPv6 response" (Stun.parse resp23).isSome
  check "2.3 fingerprint verifies" (Stun.fingerprintOk resp23)
  check "2.3 message-integrity verifies" (Stun.messageIntegrityOk keyShort resp23)
  let xored23 := ((Stun.parse resp23).bind fun m =>
    (m.attrs.find? fun a => a.type == Stun.attrXorMappedAddress).bind fun a =>
      Stun.decodeXorMapped m.txid a.value)
  let want23 : Stun.Endpoint :=
    { family := 2, port := 32853, addr := fromHex "20010db8123456780011223344556677" }
  check "2.3 XOR-MAPPED-ADDRESS decodes to [2001:db8:1234:5678:11:2233:4455:6677]:32853"
    (xored23 == some want23)
  -- §2.4 long-term request
  check "2.4 parse long-term request" (Stun.parse req24).isSome
  check "2.4 message-integrity verifies (long-term MD5 key)"
    (Stun.messageIntegrityOk keyLong req24)
  -- RFC 5389 §15.4 key derivation, computed in-core (RFC 1321 MD5)
  check "2.4 long-term key derives in-core: MD5(username:realm:password)"
    (Stun.longTermKey user24 realm24 pass24 == keyLong)
  check "2.4 message-integrity verifies under the derived key"
    (Stun.messageIntegrityOk (Stun.longTermKey user24 realm24 pass24) req24)
  check "RFC 1321 MD5 test-suite vector: md5(\"abc\")"
    (Stun.md5 ([0x61, 0x62, 0x63] : List UInt8)
      == fromHex "900150983cd24fb0d6963f7d28e17f72")
  -- RFC 5780 NAT-behavior discovery, driven through the server step
  let primary : Stun.Endpoint := { family := 1, port := 3478, addr := [127,0,0,1] }
  let alternate : Stun.Endpoint := { family := 1, port := 3479, addr := [127,0,0,1] }
  let cfg5780 : Stun.Config := { primary := some primary, alternate := some alternate }
  let txid := req21.drop 8 |>.take 12
  let crReq := Stun.encode Stun.bindingRequest txid
    [{ type := Stun.attrChangeRequest, value := [0, 0, 0, 2] }]
  let crServed := Stun.serve cfg5780 (false, false) crReq src
  check "5780 CHANGE-REQUEST change-port honored (response from alternate port)"
    ((crServed.map (·.1)) == some (false, true))
  let crAttrs := ((crServed.map (·.2)).bind Stun.parse).map (·.attrs)
  check "5780 response carries OTHER-ADDRESS (alternate 127.0.0.1:3479)"
    ((crAttrs.bind (Stun.findAttr Stun.attrOtherAddress ·)).map (·.value)
      == some (Stun.mappedValue alternate))
  check "5780 response carries RESPONSE-ORIGIN of the sending socket"
    ((crAttrs.bind (Stun.findAttr Stun.attrResponseOrigin ·)).map (·.value)
      == some (Stun.mappedValue { primary with port := 3479 }))
  -- RFC 8445 connectivity-check wire messages
  let icePwd := keyShort
  let iceReq := Ice.checkRequest icePwd txid user21 (UInt32.ofNat 1845494271)
    true 12345678901 true
  check "8445 7.2.2 connectivity-check request self-verifies (MI + FINGERPRINT)"
    (Stun.messageIntegrityOk icePwd iceReq && Stun.fingerprintOk iceReq)
  check "8445 7.2.2 check request parses as a Binding request with USERNAME/PRIORITY/USE-CANDIDATE"
    (((Stun.parse iceReq).map fun m =>
      m.typ == Stun.bindingRequest &&
      (Stun.findAttr Stun.attrUsername m.attrs).isSome &&
      (Stun.findAttr Stun.attrPriority m.attrs).isSome &&
      (Stun.findAttr Ice.attrIceControlling m.attrs).isSome &&
      (Stun.findAttr Stun.attrUseCandidate m.attrs).isSome).getD false)
  let ice487 := Ice.conflict487Response icePwd txid
  check "8445 7.3.1.1 role-conflict 487 is authenticated and carries ERROR-CODE 487"
    (Stun.messageIntegrityOk icePwd ice487 &&
     (errorCodeOf ice487 == some (4, 87)))
  -- the served ICE check draws an authenticated answer end-to-end in-core
  let cfgIce : Stun.Config := { auth := some { username := user21, key := icePwd } }
  let iceAnswer := (Stun.serve cfgIce (false, false) iceReq src).map (·.2)
  check "8445 7.3 in-core check/answer round-trip: answer MI verifies"
    ((iceAnswer.map (Stun.messageIntegrityOk icePwd ·)).getD false)
  let (pass, total) ← c.get
  IO.println s!"{pass}/{total} PASS"
