import Ws.Decode
import Ws.Utf8

/-!
# The Close-body verdict (RFC 6455 §5.5.1, §7.1.4, §7.4) — in the core

`Ws.CloseHandshake` proves the Close-body decode (2-octet big-endian status
code + optional UTF-8 reason) and the §7 echo rule; `Ws.Decode.closeCodeOk`
proves the §7.4 wire registry; `Ws.Utf8` proves the RFC 3629 validator. The
host's message engine composes those pieces into ONE decision when a complete
close frame is in hand: reply in kind to an empty body, refuse a 1-octet body
(1002), refuse an unregistered code (1002), refuse a malformed reason (1007),
otherwise echo the peer's code (§7.1.4 handshake reply). Until now that
composition lived only in the host.

`closeBody` is that decision as one **total** function of the close payload.
The theorems:

* `echo_inv` — an `echo` verdict certifies everything: the body decodes
  (`CloseHandshake.decode`) to exactly the echoed code, the code is
  registry-admitted (`Decode.closeCodeOk`), and the reason satisfies the
  whole-string UTF-8 spec (`validReason`).
* `echo_closeWf` — an echoed frame is Close-well-formed
  (`CloseHandshake.CloseWf`): the verdict admits no frame the proven
  handshake layer would refuse.
* `echo_complete` — and every registry-valid, UTF-8-clean body IS echoed:
  the verdict refuses nothing the spec admits.
* `fail_*_inv` — each refusal pins its cause: 1002 is a short body or an
  unregistered code, 1007 is exactly a spec-invalid reason.
* `echo_code_lt` — an echoed code fits 16 bits (it came off two octets), so
  the packed ABI cannot truncate.
* Kernel-checked vectors: the host's own close test cases, octet-exact.

`drorb_ws_close_body` (`@[export]`) is the C-ABI seam: the reassembled
control payload in, the packed verdict out. The host keeps only the 125-byte
control buffering (§5.5, enforced by the proven header verdict); every close
validation and echo decision it reports is this module's.
-/

namespace Ws
namespace ReassemblyClose

/-- Invalid frame payload data (RFC 6455 §7.4.1). -/
def closeInvalidPayload : Nat := 1007

/-- The verdict on a complete close-frame payload. -/
inductive Verdict where
  /-- Empty body: reply in kind with an empty close, then close (§5.5.1). -/
  | echoEmpty
  /-- Valid body: echo the peer's status code, then close (§7.1.4). -/
  | echo (code : Nat)
  /-- Protocol/payload failure: close with this code (§7.1.7). -/
  | fail (code : Nat)
deriving Repr, DecidableEq

/-- **The Close-body verdict**: one total function from the reassembled close
payload to the reply decision, in the host's check order — empty body echoes
in kind; a 1-octet body cannot carry the status code (1002, §5.5.1); an
unregistered code is refused (1002, §7.4); a reason that is not UTF-8 is
refused (1007, §5.5.1); otherwise the peer's code is echoed (§7.1.4). -/
def closeBody (p : Bytes) : Verdict :=
  match p with
  | [] => .echoEmpty
  | [_] => .fail closeProtocolError
  | b0 :: b1 :: reason =>
    let code := b0.toNat * 256 + b1.toNat
    if Decode.closeCodeOk code = false then .fail closeProtocolError
    else if ¬ Utf8.run .ready reason = some .ready then
      .fail closeInvalidPayload
    else .echo code

/-! ## What an `echo` verdict certifies -/

/-- **Inversion.** An echoed close pins every gate it passed: the body is at
least two octets, `CloseHandshake.decode` reads exactly the echoed code with
the remaining octets the reason, the code is registry-admitted, and the
reason satisfies the whole-string UTF-8 spec. -/
theorem echo_inv {p : Bytes} {code : Nat} (h : closeBody p = .echo code) :
    ∃ b0 b1 reason, p = b0 :: b1 :: reason
      ∧ CloseHandshake.decode p = some (code, reason)
      ∧ code = b0.toNat * 256 + b1.toNat
      ∧ Decode.closeCodeOk code = true
      ∧ CloseHandshake.validReason reason = true := by
  match p with
  | [] => exact Verdict.noConfusion h
  | [_] => exact Verdict.noConfusion h
  | b0 :: b1 :: reason =>
    refine ⟨b0, b1, reason, rfl, ?_⟩
    simp only [closeBody] at h
    by_cases hc : Decode.closeCodeOk (b0.toNat * 256 + b1.toNat) = false
    · rw [if_pos hc] at h; exact Verdict.noConfusion h
    rw [if_neg hc] at h
    by_cases hu : ¬ Utf8.run .ready reason = some .ready
    · rw [if_pos hu] at h; exact Verdict.noConfusion h
    rw [if_neg hu] at h
    injection h with hcode
    subst hcode
    refine ⟨rfl, rfl, ?_, ?_⟩
    · cases hok : Decode.closeCodeOk (b0.toNat * 256 + b1.toNat)
      · exact absurd hok hc
      · rfl
    · rw [Utf8.validReason_iff_run]
      by_cases hr : Utf8.run .ready reason = some .ready
      · exact hr
      · exact absurd hr (by simpa using hu)

/-- The registry (`closeCodeOk`, §7.4 on-the-wire) is contained in the
handshake layer's valid range (`validCode`, 1000–4999). -/
theorem closeCodeOk_validCode {c : Nat} (h : Decode.closeCodeOk c = true) :
    CloseHandshake.validCode c = true := by
  rw [Decode.closeCodeOk_iff] at h
  simp only [CloseHandshake.validCode, decide_eq_true_eq]
  omega

/-- **An echoed frame is Close-well-formed.** The frame assembled from an
echoed body (its ≤ 125-octet length enforced by the proven header verdict,
`Ws.Decode.done_valid`) satisfies `CloseHandshake.CloseWf` — the verdict
admits no close the proven handshake layer would refuse. -/
theorem echo_closeWf {p : Bytes} {code : Nat} (h : closeBody p = .echo code)
    (hlen : p.length ≤ 125) :
    CloseHandshake.CloseWf { fin := true, opcode := .close, payload := p } := by
  obtain ⟨b0, b1, reason, hp, hdec, -, hok, hreason⟩ := echo_inv h
  constructor
  · -- Frame.Wf: control shape + the §5.5.1 length-1 exclusion.
    refine ⟨fun _ => ⟨rfl, hlen⟩, fun _ => ?_⟩
    subst hp
    simp
  · intro _
    show (match CloseHandshake.decode p with
          | some (code, reason) =>
            CloseHandshake.validCode code = true
              ∧ CloseHandshake.validReason reason = true
          | none => p = [])
    rw [hdec]
    exact ⟨closeCodeOk_validCode hok, hreason⟩

/-- **Completeness.** Every registry-valid, UTF-8-clean close body IS echoed
(with exactly its own code): the verdict refuses nothing the spec admits. -/
theorem echo_complete {b0 b1 : UInt8} {reason : Bytes}
    (hok : Decode.closeCodeOk (b0.toNat * 256 + b1.toNat) = true)
    (hreason : CloseHandshake.validReason reason = true) :
    closeBody (b0 :: b1 :: reason) = .echo (b0.toNat * 256 + b1.toNat) := by
  have hrun := (Utf8.validReason_iff_run reason).mp hreason
  simp [closeBody, hok, hrun]

/-! ## What each refusal pins -/

/-- An empty body answers `echoEmpty` (reply in kind, §5.5.1). -/
theorem empty_echoes : closeBody [] = .echoEmpty := rfl

/-- A 1-octet body — refused at the frame layer by `Frame.Wf` too
(`Frame.not_wf_close_len_one`) — fails 1002. -/
theorem fail_len_one (b : UInt8) :
    closeBody [b] = .fail closeProtocolError := rfl

/-- **1007 inversion.** A 1007 refusal is exactly a spec-invalid reason: the
code was registry-admitted but the reason fails `validReason`. -/
theorem fail_1007_inv {p : Bytes} (h : closeBody p = .fail closeInvalidPayload) :
    ∃ b0 b1 reason, p = b0 :: b1 :: reason
      ∧ Decode.closeCodeOk (b0.toNat * 256 + b1.toNat) = true
      ∧ CloseHandshake.validReason reason = false := by
  match p with
  | [] => exact Verdict.noConfusion h
  | [_] =>
    exact absurd (Verdict.fail.inj h) (by decide)
  | b0 :: b1 :: reason =>
    refine ⟨b0, b1, reason, rfl, ?_⟩
    simp only [closeBody] at h
    by_cases hc : Decode.closeCodeOk (b0.toNat * 256 + b1.toNat) = false
    · rw [if_pos hc] at h
      exact absurd (Verdict.fail.inj h) (by decide)
    rw [if_neg hc] at h
    by_cases hu : ¬ Utf8.run .ready reason = some .ready
    · refine ⟨?_, ?_⟩
      · cases hok : Decode.closeCodeOk (b0.toNat * 256 + b1.toNat)
        · exact absurd hok hc
        · rfl
      · cases hv : CloseHandshake.validReason reason
        · rfl
        · exact absurd ((Utf8.validReason_iff_run reason).mp hv)
            (by simpa using hu)
    · rw [if_neg hu] at h
      exact Verdict.noConfusion h

/-- **1002-with-body inversion.** A 1002 refusal of a ≥ 2-octet body is
exactly an unregistered status code. -/
theorem fail_1002_body_inv {b0 b1 : UInt8} {reason : Bytes}
    (h : closeBody (b0 :: b1 :: reason) = .fail closeProtocolError) :
    Decode.closeCodeOk (b0.toNat * 256 + b1.toNat) = false := by
  simp only [closeBody] at h
  by_cases hc : Decode.closeCodeOk (b0.toNat * 256 + b1.toNat) = false
  · exact hc
  rw [if_neg hc] at h
  by_cases hu : ¬ Utf8.run .ready reason = some .ready
  · rw [if_pos hu] at h
    exact absurd (Verdict.fail.inj h) (by decide)
  · rw [if_neg hu] at h
    exact Verdict.noConfusion h

/-- An echoed code fits 16 bits (it came off two wire octets): the packed
ABI encoding cannot truncate it. -/
theorem echo_code_lt {p : Bytes} {code : Nat} (h : closeBody p = .echo code) :
    code < 65536 := by
  obtain ⟨b0, b1, -, -, -, hcode, -, -⟩ := echo_inv h
  have h0 : b0.toNat < 256 := u8_toNat_lt b0
  have h1 : b1.toNat < 256 := u8_toNat_lt b1
  omega

/-! ## Kernel-checked vectors (non-vacuity — the host's own close cases) -/

/-- Normal closure `03 E8` (1000), no reason: echoed. -/
theorem vec_normal_echoed : closeBody [0x03, 0xE8] = .echo 1000 := by decide

/-- A UTF-8 reason rides along: still echoed. -/
theorem vec_reason_echoed :
    closeBody [0x03, 0xE8, 0x62, 0x79, 0x65] = .echo 1000 := by decide

/-- Empty body: replied in kind. -/
theorem vec_empty : closeBody [] = .echoEmpty := by decide

/-- A 1-octet body: 1002. -/
theorem vec_one_octet : closeBody [0x03] = .fail 1002 := by decide

/-- Reserved code 1005 (`03 ED`): 1002. -/
theorem vec_reserved_1005 : closeBody [0x03, 0xED] = .fail 1002 := by decide

/-- Out-of-registry code 999 (`03 E7`): 1002. -/
theorem vec_out_of_range_999 : closeBody [0x03, 0xE7] = .fail 1002 := by decide

/-- Valid code, non-UTF-8 reason (`FF`): 1007. -/
theorem vec_bad_reason :
    closeBody [0x03, 0xE8, 0xFF] = .fail 1007 := by decide

/-! ## The host-facing C-ABI seam -/

/-- **`drorb_ws_close_body`.** The seam the host's message engine crosses
with a complete close payload instead of validating it itself: payload in,
packed verdict out. Bits 16–31: `0` = echo an empty close, `1` = echo the
code in bits 0–15, `2` = fail the connection with the code in bits 0–15. -/
@[export drorb_ws_close_body]
def closeBodyExport (payload : ByteArray) : UInt32 :=
  match closeBody payload.toList with
  | .echoEmpty => 0
  | .echo code => ((1 : UInt32) <<< 16) ||| UInt32.ofNat code
  | .fail code => ((2 : UInt32) <<< 16) ||| UInt32.ofNat code

/-- **ABI vectors.** The packed encodings, octet-exact, for whatever byte
array carries each payload. -/
theorem vec_abi (a : ByteArray) :
    (a.toList = [0x03, 0xE8]
      → closeBodyExport a = ((1 : UInt32) <<< 16) ||| 1000)
    ∧ (a.toList = [] → closeBodyExport a = 0)
    ∧ (a.toList = [0x03]
      → closeBodyExport a = ((2 : UInt32) <<< 16) ||| 1002)
    ∧ (a.toList = [0x03, 0xE8, 0xFF]
      → closeBodyExport a = ((2 : UInt32) <<< 16) ||| 1007) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp only [closeBodyExport, h] <;> decide

end ReassemblyClose
end Ws
