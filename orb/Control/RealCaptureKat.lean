import Control.Ts2021Core
import Control.TailcfgWire

/-!
# Real stock-client capture (ground truth)

Every literal in this file was **captured from a stock `tailscale` client**, not
hand-written. Provenance:

* Client: `tailscale` / `tailscaled` **1.98.8**
  (`1.98.8-t1241b225b-g0520dfda5`, go1.26.3), the distro binary on the build box.
* Method: an isolated second `tailscaled` (own socket/state/port,
  `--tun=userspace-networking`) was pointed with
  `tailscale up --login-server=http://127.0.0.1:8099` at a capture harness that
  serves `GET /key` and `POST /ts2021` and implements the **responder** half of
  `Noise_IK_25519_ChaChaPoly_BLAKE2s`. The harness completed a real handshake
  (it decrypted the client's static machine key, which only a correct responder
  can do) and then decrypted the transport records, recovering the client's
  HTTP/2 `POST /machine/register` body in cleartext.
* Raw artifacts: `Control/testdata/{initiation_frame.bin,response_frame.bin,
  register_request.json,handshake_meta.json}`.

All artifacts here come from a SINGLE connection: the initiation frame below
is the one that actually carried the RegisterRequest body below.

The client advertised capability version **138** in both the
`GET /key?v=` query and the initiation frame header.
-/

namespace Control.RealCaptureKat

open Control.Ts2021Wire
open Control.TailcfgWire

/-! ## Hex helper (test-only) -/

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexBytes (s : String) : Control.Bytes :=
  let rec go : List Char → Control.Bytes
    | a :: b :: t => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go t
    | _ => []
  go s.toList

/-! ## §1  The REAL Noise_IK initiation frame (101 bytes, captured) -/

/-- The exact 101-byte `X-Tailscale-Handshake` payload sent by tailscale 1.98.8. -/
def realInitiationHex : String :=
  "008a0100607f46b5f8ddacc00384dfff058c5f95f1392c579e9b21d52c8751e07797fbc1498f6ead2f89de38a3567578a952940a624d8bca7df9bb0253917f010be0895ea81753c977fe5f076bb3e78a791478aef27be6377a0d67c9a27380b0b95437f034"

def realInitiation : Control.Bytes := hexBytes realInitiationHex

/-- The client ephemeral (cleartext `[5:37]` of the frame), from the capture. -/
def realClientEphemeralHex : String := "7f46b5f8ddacc00384dfff058c5f95f1392c579e9b21d52c8751e07797fbc149"

/-- The client static/machine key the harness **decrypted** out of the frame. -/
def realClientMachineKeyHex : String := "beb52fdd53efa9412b93528cb115575e0a2c39522b1236b40369a69392bc5108"

-- Frame length is exactly `initiationMessage`'s 101 bytes:
#eval realInitiation.length                            -- expect: 101

-- drorb's parser ACCEPTS the real frame, and recovers (version, |noise|, |rest|):
#eval (parseInitiation realInitiation).map
        (fun t => (t.1, t.2.1.length, t.2.2.length))   -- expect: some (138, 96, 0)

/-- **drorb's `parseInitiation` accepts the real stock-client frame** and returns
capability version 138, a 96-byte Noise payload and no trailing bytes. -/
theorem parseInitiation_real :
    (parseInitiation realInitiation).map (fun t => (t.1, t.2.1.length, t.2.2.length))
      = some (138, 96, 0) := by
  native_decide

/-- The cleartext ephemeral sits at frame offset `[5:37]`, exactly as
`messages.go`'s `initiationMessage` lays it out. -/
theorem realInitiation_ephemeral_offset :
    (realInitiation.drop 5).take 32 = hexBytes realClientEphemeralHex := by
  native_decide

/-! ## §2  The REAL RegisterRequest JSON (captured, decrypted from the ts2021 channel) -/

/-- The exact `POST /machine/register` body sent by tailscale 1.98.8, recovered
from the HTTP/2 DATA frame inside the decrypted Noise transport records. -/
def realRegisterRequest : String :=
  "{\"Version\":138,\"NodeKey\":\"nodekey:d9f10b0868919cff75f09504a2f480b6443a57efdecf38b507e958e8"
  ++ "13c0ea31\",\"OldNodeKey\":\"nodekey:0000000000000000000000000000000000000000000000000000000000"
  ++ "000000\",\"NLKey\":\"nlpub:e08d879b602335e5fb743e02999aed328d6e9599e9d10993a09ee621a529646c\",\""
  ++ "Expiry\":\"0001-01-01T00:00:00Z\",\"Followup\":\"\",\"Hostinfo\":{\"IPNVersion\":\"1.98.8-t1241b225b-g"
  ++ "0520dfda5\",\"BackendLogID\":\"b623891acb2bf89bb4bd027bb6230967bdd80ee04990b15816570876c69ad9a"
  ++ "b\",\"OS\":\"linux\",\"OSVersion\":\"6.11.0-29-generic\",\"Container\":false,\"Distro\":\"ubuntu\",\"Distr"
  ++ "oVersion\":\"24.10\",\"DistroCodeName\":\"oracular\",\"Desktop\":true,\"Hostname\":\"captest\",\"Machine"
  ++ "\":\"x86_64\",\"GoArch\":\"amd64\",\"GoArchVar\":\"v1\",\"GoVersion\":\"go1.26.3\",\"Services\":[{\"Proto\":\""
  ++ "peerapi-dns-proxy\",\"Port\":1}],\"Userspace\":true,\"UserspaceRouter\":true,\"AppConnector\":false"
  ++ ",\"StateEncrypted\":false},\"NodeKeySignature\":null}"

-- drorb's TOTAL tailcfg parser INGESTS the real body:
#eval (RegisterRequest.wireDecode realRegisterRequest).isSome   -- expect: true

-- …and the decoded message re-renders and re-parses to itself (the proven
-- roundtrip, exercised on REAL captured bytes):
#eval (match RegisterRequest.wireDecode realRegisterRequest with
       | some m => RegisterRequest.wireDecode (RegisterRequest.wireEncode m) == some m
       | none => false)                                          -- expect: true

-- Field-by-field evidence that the real body landed in the right places:
#eval (RegisterRequest.wireDecode realRegisterRequest).map (·.version)
#eval (RegisterRequest.wireDecode realRegisterRequest).map (·.nodeKey)
#eval (RegisterRequest.wireDecode realRegisterRequest).bind (·.hostinfo) |>.map (·.hostname)
#eval (RegisterRequest.wireDecode realRegisterRequest).bind (·.hostinfo) |>.map (·.os)
#eval (RegisterRequest.wireDecode realRegisterRequest).bind (·.hostinfo) |>.map (·.ipnVersion)

/-- **drorb decodes the real stock-client RegisterRequest.** -/
theorem wireDecode_real_isSome :
    (RegisterRequest.wireDecode realRegisterRequest).isSome = true := by
  native_decide

/-- The real body's `Version` is the client's advertised capability version. -/
theorem real_version :
    (RegisterRequest.wireDecode realRegisterRequest).map (·.version) = some 138 := by
  native_decide

#print axioms parseInitiation_real
#print axioms wireDecode_real_isSome
#print axioms real_version

end Control.RealCaptureKat
