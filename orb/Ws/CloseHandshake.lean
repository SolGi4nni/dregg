import Ws.Close

/-!
# WebSocket Close handshake body & echo (RFC 6455 §5.5.1, §7)

`Ws.Frame` fixes the decoded frame and the frame-level well-formedness the
control-frame rules impose (a length-1 Close is a protocol error). `Ws.Close`
fixes the open/closing/closed state machine with the status-code echo rule. This
module joins the two at the *Close body*: the payload of a Close frame is, per
RFC 6455 §5.5.1,

* the **2-octet big-endian status code** (present iff the body is non-empty), then
* an **optional UTF-8 reason** phrase (the remaining octets).

and adds the wire-level validity §7.4.1/§7.4.2 impose on the status code (the
`1000–4999` range) and the UTF-8 well-formedness §5.5.1 imposes on the reason.

The theorems:

* `ws_close_code` — a well-formed Close with a body decodes to a 2-octet
  big-endian status code followed by the (optional) reason octets.
* `ws_close_echo` — a Close received while open is echoed with the *same* status
  code (moving to `closing`), and the matching reply completes the handshake to
  `closed`.
* `ws_close_no_data_after` — once our Close has been sent, a data send is a
  protocol error (§7.1.1), and `closed` emits nothing but `error`.
* `invalid_code_reject` / `closeWf_reject_999` — a Close whose status code is
  outside `1000–4999` fails Close-body well-formedness.
* `closeWf_normal` — a normal-closure (`1000`) Close *is* well-formed (the
  predicate is not vacuously false).

Deliberately out of scope: negotiated extensions, permessage-deflate.
-/

namespace Ws
namespace CloseHandshake

/-! ## Close-body decode (RFC 6455 §5.5.1) -/

/-- Decode a Close-frame payload: the first two octets are the big-endian status
code and the remaining octets are the reason phrase. An empty payload carries no
status code (`none`); a one-octet payload is malformed (`none`) — and is already
rejected at the frame layer by `Frame.Wf`. -/
def decode (p : Bytes) : Option (Nat × Bytes) :=
  match p with
  | b0 :: b1 :: rest => some (b0.toNat * 256 + b1.toNat, rest)
  | _ => none

/-- The valid on-the-wire status-code range (RFC 6455 §7.4.1/§7.4.2): `1000–4999`.
Codes `0–999` are unused; `5000+` are out of range. (Sub-ranges `1000–2999`
protocol, `3000–3999` IANA-registered, `4000–4999` private use.) -/
def validCode (c : Nat) : Bool := decide (1000 ≤ c ∧ c ≤ 4999)

/-! ## UTF-8 reason well-formedness (RFC 6455 §5.5.1 → RFC 3629)

A pure, kernel-reducible structural validator for the reason phrase. `fuel` is a
decreasing measure (any value `≥ length` suffices; each group consumes at least
one octet while `fuel` drops by one). It encodes the RFC 3629 leading/continuation
byte automaton with the overlong-form and surrogate exclusions. -/

/-- `b` is a UTF-8 continuation octet (`10xxxxxx`, i.e. `0x80–0xBF`). -/
def isCont (b : UInt8) : Bool := decide (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF)

/-- `lo ≤ b ≤ hi` on the numeric value of an octet. -/
def inRange (b : UInt8) (lo hi : Nat) : Bool := decide (lo ≤ b.toNat ∧ b.toNat ≤ hi)

/-- Fuel-driven RFC 3629 structural check (see the section note). -/
def validUtf8Aux : Nat → Bytes → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, b0 :: rest =>
    if b0.toNat ≤ 0x7F then
      validUtf8Aux fuel rest
    else if inRange b0 0xC2 0xDF then
      match rest with
      | b1 :: rest2 => isCont b1 && validUtf8Aux fuel rest2
      | [] => false
    else if inRange b0 0xE0 0xEF then
      match rest with
      | b1 :: b2 :: rest2 =>
        let lo := if b0.toNat = 0xE0 then 0xA0 else 0x80
        let hi := if b0.toNat = 0xED then 0x9F else 0xBF
        inRange b1 lo hi && isCont b2 && validUtf8Aux fuel rest2
      | _ => false
    else if inRange b0 0xF0 0xF4 then
      match rest with
      | b1 :: b2 :: b3 :: rest2 =>
        let lo := if b0.toNat = 0xF0 then 0x90 else 0x80
        let hi := if b0.toNat = 0xF4 then 0x8F else 0xBF
        inRange b1 lo hi && isCont b2 && isCont b3 && validUtf8Aux fuel rest2
      | _ => false
    else
      false

/-- Reason-phrase validity (RFC 6455 §5.5.1): the reason octets are well-formed
UTF-8 (RFC 3629). An absent reason (empty octet string) is valid. -/
def validReason (r : Bytes) : Bool := validUtf8Aux (r.length + 1) r

/-! ## Close-body well-formedness -/

/-- Close-frame well-formedness (RFC 6455 §5.5.1): well-formed at the frame layer
(`Frame.Wf`, which already forbids the length-1 Close), and — when the frame is a
Close carrying a body — the decoded status code is in `1000–4999` and the reason
is valid UTF-8. A Close carrying no body (`none`, i.e. empty payload) is
well-formed. -/
def CloseWf (f : Frame) : Prop :=
  f.Wf ∧
    (f.opcode = Opcode.close →
      match decode f.payload with
      | some (code, reason) => validCode code = true ∧ validReason reason = true
      | none => f.payload = [])

/-! ## A list-decomposition helper -/

/-- A list of length at least two splits off its first two elements. -/
theorem two_le_length {α : Type _} :
    ∀ {l : List α}, 2 ≤ l.length → ∃ a b r, l = a :: b :: r
  | [], h => by simp only [List.length_nil] at h; omega
  | [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | a :: b :: r, _ => ⟨a, b, r, rfl⟩

/-! ## §5.5.1 — the Close body is a 2-octet code + optional reason -/

/-- **A well-formed Close carrying a body carries a 2-octet status code.** Its
payload decomposes as `b0 :: b1 :: reason`, and `decode` reads the big-endian
code `b0*256 + b1` with the remaining octets as the (optional) reason. -/
theorem ws_close_code {f : Frame} (hc : f.opcode = Opcode.close)
    (hwf : f.Wf) (hne : f.payload ≠ []) :
    ∃ b0 b1 reason,
      f.payload = b0 :: b1 :: reason ∧
      decode f.payload = some (b0.toNat * 256 + b1.toNat, reason) := by
  have h2 : 2 ≤ f.payload.length := Frame.close_body_ge_two hc hne hwf
  obtain ⟨b0, b1, reason, hp⟩ := two_le_length h2
  exact ⟨b0, b1, reason, hp, by rw [hp]; rfl⟩

/-- The status code a well-formed Close body carries is exactly the big-endian
reading of its first two octets — the decode is deterministic. -/
theorem ws_close_code_value {f : Frame} (hc : f.opcode = Opcode.close)
    (hwf : f.Wf) (hne : f.payload ≠ []) :
    ∃ code reason, decode f.payload = some (code, reason) ∧ code < 65536 := by
  obtain ⟨b0, b1, reason, _, hd⟩ := ws_close_code hc hwf hne
  refine ⟨b0.toNat * 256 + b1.toNat, reason, hd, ?_⟩
  have h0 : b0.toNat < 256 := u8_toNat_lt b0
  have h1 : b1.toNat < 256 := u8_toNat_lt b1
  omega

/-! ## §7 — echo the received code, then close -/

/-- **A Close received while open is echoed with the same status code, then the
matching reply closes the connection.** The first transition emits `echoClose c`
(the peer's own code) and moves `opened → closing`; the reply Close completes the
handshake `closing → closed`. -/
theorem ws_close_echo (c : Nat) :
    Close.step .opened (.recvClose c) = (.closing, .echoClose c) ∧
    Close.step .closing (.sendClose c) = (.closed, .emitClose) :=
  ⟨rfl, rfl⟩

/-- The decode and the echo compose: a well-formed Close carrying a body decodes
to some status `code`, and receiving it while open echoes *that* code. Ties the
§5.5.1 body decode to the §7 echo rule end to end. -/
theorem close_frame_echoed {f : Frame} (hc : f.opcode = Opcode.close)
    (hwf : f.Wf) (hne : f.payload ≠ []) :
    ∃ code reason, decode f.payload = some (code, reason) ∧
      Close.step .opened (.recvClose code) = (.closing, .echoClose code) := by
  obtain ⟨b0, b1, reason, _, hd⟩ := ws_close_code hc hwf hne
  exact ⟨b0.toNat * 256 + b1.toNat, reason, hd, rfl⟩

/-! ## §7.1.1 — no data after Close -/

/-- **No data may be sent after our Close.** Sending a Close moves `opened →
closing`, and from `closing` a data send is a protocol `error`. -/
theorem ws_close_no_data_after (c : Nat) :
    (Close.step .opened (.sendClose c)).1 = .closing ∧
    (Close.step (Close.step .opened (.sendClose c)).1 .sendData).2 = .error :=
  ⟨rfl, rfl⟩

/-- Once the handshake is `closed`, every event yields `(closed, error)`: nothing
is emitted and the state never leaves `closed`. -/
theorem ws_closed_only_error (e : Close.Event) :
    Close.step .closed e = (.closed, .error) := by
  cases e <;> rfl

/-! ## §7.4 — invalid status codes are rejected -/

/-- **An out-of-range status code fails Close-body well-formedness.** A Close
whose body decodes to a code outside `1000–4999` is not `CloseWf`. -/
theorem invalid_code_reject {f : Frame} (hc : f.opcode = Opcode.close)
    {code : Nat} {reason : Bytes} (hd : decode f.payload = some (code, reason))
    (hbad : validCode code = false) : ¬ CloseWf f := by
  intro hcw
  have hclose := hcw.2 hc
  rw [hd] at hclose
  simp [hbad] at hclose

/-- A concrete out-of-range Close (code `999`, octets `0x03 0xE7`) is rejected. -/
theorem closeWf_reject_999 :
    ¬ CloseWf { fin := true, opcode := Opcode.close, payload := [3, 231] } := by
  apply invalid_code_reject (f := { fin := true, opcode := Opcode.close, payload := [3, 231] })
    (code := 999) (reason := [])
  · rfl
  · rfl
  · decide

/-- A normal-closure Close (code `1000`, octets `0x03 0xE8`, no reason) *is*
well-formed — the predicate is not vacuously false. -/
theorem closeWf_normal :
    CloseWf { fin := true, opcode := Opcode.close, payload := [3, 232] } := by
  refine ⟨by decide, ?_⟩
  intro _
  exact ⟨by decide, by decide⟩

end CloseHandshake
end Ws
