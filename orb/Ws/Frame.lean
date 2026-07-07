import Ws.Basic

/-!
# WebSocket frames (RFC 6455 §5.2) — the decoded logical frame

The byte-level header decode composes `Ws.Length` (the payload-length ladder)
and `Ws.Mask` (the unmasking transform), both proven in their own modules. This
module fixes the *decoded* frame — FIN, the classified opcode, and the unmasked
application payload — plus the frame-level well-formedness the control-frame
rules (§5.5) impose. The reassembly and close state machines are stated over
this logical frame.
-/

namespace Ws

/-- A decoded WebSocket frame: the FIN bit, the classified opcode, and the
already-unmasked application payload. RSV bits carry no meaning without a
negotiated extension (none modeled), so a decoder validates them zero and this
record does not retain them. -/
structure Frame where
  fin : Bool
  opcode : Opcode
  payload : Bytes
deriving Repr, DecidableEq

namespace Frame

/-- Frame-level well-formedness (RFC 6455 §5.5, §5.5.1): a control frame must not
be fragmented and carries at most 125 octets of payload; and a Close control
frame that carries a body must carry a status code, so its payload is either
empty or **at least two octets** — a Close whose payload length is exactly one is
a protocol error (§5.5.1). Data frames are unconstrained at this layer.

This is the frame-validation predicate a conformant deployment runs before the
frame reaches the reassembly/close machinery, and it is the layer that still has
the raw payload in hand: `Ws.Close.step` downstream only ever sees an
already-decoded status code (`Event.recvClose`), so the length-1 rejection can
only be made here. -/
def Wf (f : Frame) : Prop :=
  (f.opcode.isControl = true → (f.fin = true ∧ f.payload.length ≤ 125)) ∧
  (f.opcode = Opcode.close → f.payload.length ≠ 1)

instance (f : Frame) : Decidable f.Wf := by unfold Wf; infer_instance

/-- A data frame is trivially well-formed at this layer (the control constraints,
including the §5.5.1 Close-length rule, do not apply). -/
theorem wf_of_data {f : Frame} (h : f.opcode.isData = true) : f.Wf := by
  unfold Wf
  refine ⟨fun hc => absurd ⟨h, hc⟩ (Opcode.not_data_and_control f.opcode), ?_⟩
  intro hclose
  rw [hclose] at h
  simp [Opcode.isData] at h

/-- **§5.5.1 — a length-1 Close is a protocol error.** A Close control frame
whose payload is exactly one octet fails frame well-formedness: a Close body must
carry the full 2-octet status code (or be absent entirely). -/
theorem not_wf_close_len_one {f : Frame} (hc : f.opcode = Opcode.close)
    (h1 : f.payload.length = 1) : ¬ f.Wf := by
  intro hwf
  exact (hwf.2 hc) h1

/-- Conversely, a Close frame whose body is present is well-formed only if it is
at least two octets: an accepted Close carrying any payload carries a full status
code, so the downstream decode to `Event.recvClose` is sound. -/
theorem close_body_ge_two {f : Frame} (hc : f.opcode = Opcode.close)
    (hne : f.payload ≠ []) (hwf : f.Wf) : 2 ≤ f.payload.length := by
  have h1 : f.payload.length ≠ 1 := hwf.2 hc
  have hpos : 0 < f.payload.length := List.length_pos.mpr hne
  omega

end Frame

end Ws
