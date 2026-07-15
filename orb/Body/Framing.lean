import Body.Smuggling
import Body.ContentLength

/-!
# Request-framing faithfulness — the boundary is machine-checked, not trusted

`Body/Smuggling.lean` proves the framing *decision* is smuggling-safe: a
`Content-Length` that conflicts with a `Transfer-Encoding: chunked`, a duplicate
`Content-Length`, or a malformed chunk is **rejected**, never resolved to a
fixed-length body that a downstream peer would split (`no_desync`,
`reject_dup_cl`, `reject_bad_chunk`). That fixes *which framing* is chosen.

This file adds the piece the decision alone does not give: the request
**boundary** — *where the request ends and the next one begins* — and proves it
faithful. The trusted Rust `next_request` (`crates/dataplane/src/http.rs`) scans
an accumulation buffer, finds the head/body split (`CRLFCRLF`), frames the body
(`Content-Length` / chunked), and reports `Frame::Complete(total)`; the host then
hands `buf[..total]` to the proven serve and drains it, keeping `buf[total..]` as
the next (pipelined) request. A framing bug there is a request-smuggling desync
in the trusted surface. Here that boundary computation is modelled and proven:

* `framing_faithful` — a fixed-length (`Content-Length`) framing consumes
  **exactly** `head ++ body`, where the body is the head-declared `n` octets, and
  the remainder is the next request **verbatim**: no octet of the body leaks past
  the boundary and no octet of the next request is swallowed. The boundary is a
  function of the *head* alone (`headEnd + n`), never of body content, so no
  attacker-supplied body byte can shift it.
* `framing_faithful_empty` — the same for a request with no body: the boundary is
  the head end; the whole remainder is the next request verbatim.
* `framing_faithful_chunked` — a chunked framing consumes `head ++ chunked-section`
  and leaves the remainder verbatim, with the chunked section's length taken from
  the proven `Chunked.decodeStreamExt` — the framing-grade decode of the full
  RFC 7230 §4.1 wire (chunk extensions parsed and ignored, the trailer section
  after the last-chunk consumed; a recipient MUST accept both).
* `frame_bounded` — a `complete` boundary never runs past the buffer (no
  overread): `consumed ≤ buf.length`.
* `frame_no_smuggle` — a `Content-Length` present **together with** a chunked
  `Transfer-Encoding` is framed `reject`, **never** `complete` — so the framer
  never consumes only the `Content-Length` octets while leaving the chunked tail
  as a smuggled second request. This is the boundary-level statement of
  `Body.Smuggling.no_desync`.

The smuggling surface is the CL-vs-chunked *body-length* decision; `frameFixed`
takes that decision from `Body.Smuggling.decide` (the proven-safe classifier), so
the boundary it computes inherits the smuggling safety. Non-vacuity is witnessed
against the concrete `clteVector` (`Content-Length: 6` + `Transfer-Encoding:
chunked`): the proven framer rejects it, and a naive length-only framer would
have consumed 6 body octets and admitted the smuggled tail.
-/

namespace Body
namespace Framing

open Body Body.Smuggling

/-- The framing outcome for the request at the front of a buffer. -/
inductive Outcome where
  /-- Not enough bytes yet; read more and rescan. -/
  | needMore
  /-- Ambiguous or malformed framing (CL/TE conflict, duplicate CL, bad chunk):
  a single, unsplittable fate — the host closes the connection. -/
  | reject (r : Smuggling.Reason)
  /-- A complete request occupies the first `consumed` octets of the buffer. -/
  | complete (consumed : Nat)
deriving Repr, DecidableEq

/-- Frame the request at the front of `buf`, given the head-block length
`headEnd` (the index just past `CRLFCRLF`) and the parsed head `req`. The body
length is taken from `Body.Smuggling.decide` — the proven smuggling-safe
classifier over the head's framing headers — so the boundary is a function of the
head, never of body content. Each `complete` boundary is guarded by
`≤ buf.length`, so the framer never claims bytes the buffer does not hold. -/
def frameFixed (buf : Bytes) (headEnd : Nat) (req : Smuggling.Request) : Outcome :=
  match Smuggling.decide req with
  | .reject r => .reject r
  | .length n =>
      if headEnd + n ≤ buf.length then .complete (headEnd + n) else .needMore
  | .empty =>
      if headEnd ≤ buf.length then .complete headEnd else .needMore
  | .chunked =>
      -- The framing-grade decode of the full RFC 7230 §4.1 wire: chunk
      -- extensions are parsed and ignored (§4.1.1) and the trailer section
      -- after the last-chunk is consumed (§4.1.2), as a recipient MUST.
      match Chunked.decodeStreamExt (buf.drop headEnd) with
      | .complete _ c =>
          if headEnd + c ≤ buf.length then .complete (headEnd + c) else .needMore
      | .incomplete => .needMore
      -- a malformed chunk (e.g. a non-hex size token) is rejected (closed),
      -- never silently truncated — `Body.Smuggling.reject_bad_chunk`.
      | .error => .reject .unsupportedTransferEncoding

/-! ## No overread: a complete boundary stays inside the buffer -/

/-- **`frame_bounded`.** A `complete` framing never runs past the buffer: the
consumed count is at most the buffer length. Every `complete` arm of `frameFixed`
is guarded by `_ ≤ buf.length`, so there is no overread. -/
theorem frame_bounded (buf : Bytes) (headEnd c : Nat) (req : Smuggling.Request)
    (h : frameFixed buf headEnd req = .complete c) : c ≤ buf.length := by
  unfold frameFixed at h
  repeat' split at h
  all_goals first
    | exact Outcome.noConfusion h
    | (injection h with h; omega)

/-! ## Faithfulness: the consumed prefix is exactly head ++ body -/

/-- **`framing_faithful` (headline).** When the head frames a fixed
`Content-Length` body of `n` octets and the buffer is `head ++ body ++ rest` with
`head` the header block (length `headEnd`) and `body` exactly `n` octets, the
framer reports `complete (headEnd + n)`, and that boundary splits the buffer
*exactly*:

* the consumed prefix is `head ++ body` — the head plus precisely the declared
  `n` body octets, nothing more, nothing less;
* the remainder is `rest` — the next request **verbatim**, with no octet of this
  body leaking into it and no octet of it swallowed by this body.

The boundary `headEnd + n` is a function of the *head* alone, so no attacker
choice of `body`/`rest` content can shift it. -/
theorem framing_faithful (head body rest : Bytes) (headEnd n : Nat)
    (req : Smuggling.Request)
    (hhead : head.length = headEnd) (hbody : body.length = n)
    (hdec : Smuggling.decide req = .length n) :
    frameFixed (head ++ body ++ rest) headEnd req = .complete (headEnd + n)
    ∧ (head ++ body ++ rest).take (headEnd + n) = head ++ body
    ∧ (head ++ body ++ rest).drop (headEnd + n) = rest := by
  have hlen : (head ++ body).length = headEnd + n := by
    rw [List.length_append, hhead, hbody]
  have hassoc : head ++ body ++ rest = (head ++ body) ++ rest := by
    rw [List.append_assoc]
  have htake : (head ++ body ++ rest).take (headEnd + n) = head ++ body := by
    rw [hassoc, ← hlen]; exact List.take_left _ _
  have hdrop : (head ++ body ++ rest).drop (headEnd + n) = rest := by
    rw [hassoc, ← hlen]; exact List.drop_left _ _
  have hbound : headEnd + n ≤ (head ++ body ++ rest).length := by
    rw [hassoc, List.length_append, hlen]; omega
  refine ⟨?_, htake, hdrop⟩
  simp only [frameFixed, hdec]
  rw [if_pos hbound]

/-- **`framing_faithful_empty`.** A request with no body (`decide = .empty`)
consumes exactly the head; the whole remainder is the next request verbatim. -/
theorem framing_faithful_empty (head rest : Bytes) (headEnd : Nat)
    (req : Smuggling.Request)
    (hhead : head.length = headEnd) (hdec : Smuggling.decide req = .empty) :
    frameFixed (head ++ rest) headEnd req = .complete headEnd
    ∧ (head ++ rest).take headEnd = head
    ∧ (head ++ rest).drop headEnd = rest := by
  have htake : (head ++ rest).take headEnd = head := by
    rw [← hhead]; exact List.take_left _ _
  have hdrop : (head ++ rest).drop headEnd = rest := by
    rw [← hhead]; exact List.drop_left _ _
  have hbound : headEnd ≤ (head ++ rest).length := by
    rw [List.length_append, hhead]; omega
  refine ⟨?_, htake, hdrop⟩
  simp only [frameFixed, hdec]
  rw [if_pos hbound]

/-- **`framing_faithful_chunked`.** A chunked framing consumes `head ++ section`,
where `section` is the chunked body region the proven `Chunked.decodeStreamExt`
delimits (`consumed = c`), and leaves the remainder verbatim. The chunked
section's length is taken from the proven decoder, not from body content past the
region; the boundary reassembly is exact. -/
theorem framing_faithful_chunked (head rest tail : Bytes) (headEnd c : Nat)
    (body : Bytes) (req : Smuggling.Request)
    (hhead : head.length = headEnd) (hdec : Smuggling.decide req = .chunked)
    (hsec : rest.length = c)
    (hds : Chunked.decodeStreamExt ((head ++ rest ++ tail).drop headEnd)
              = .complete body c) :
    frameFixed (head ++ rest ++ tail) headEnd req = .complete (headEnd + c)
    ∧ (head ++ rest ++ tail).take (headEnd + c) = head ++ rest
    ∧ (head ++ rest ++ tail).drop (headEnd + c) = tail := by
  have hlen : (head ++ rest).length = headEnd + c := by
    rw [List.length_append, hhead, hsec]
  have hassoc : head ++ rest ++ tail = (head ++ rest) ++ tail := by
    rw [List.append_assoc]
  have htake : (head ++ rest ++ tail).take (headEnd + c) = head ++ rest := by
    rw [hassoc, ← hlen]; exact List.take_left _ _
  have hdrop : (head ++ rest ++ tail).drop (headEnd + c) = tail := by
    rw [hassoc, ← hlen]; exact List.drop_left _ _
  have hbound : headEnd + c ≤ (head ++ rest ++ tail).length := by
    rw [hassoc, List.length_append, hlen]; omega
  refine ⟨?_, htake, hdrop⟩
  simp only [frameFixed, hdec, hds]
  rw [if_pos hbound]

/-! ## No smuggling: a CL/TE conflict is never framed as a length boundary -/

/-- **`frame_no_smuggle` (headline).** If the head frames *both* a valid
`Content-Length` (`present n`) and a chunked `Transfer-Encoding`, the framer
**rejects** — it is never `complete`. In particular it never consumes only the
`Content-Length` octets while leaving the chunked tail as a smuggled second
request: there is a single, unsplittable fate (rejection), so no two servers can
disagree on the boundary. Boundary-level form of `Body.Smuggling.no_desync`. -/
theorem frame_no_smuggle (buf : Bytes) (headEnd n : Nat) (req : Smuggling.Request)
    (hcl : Smuggling.clStatus req = .present n) (hte : Smuggling.teStatus req = .chunked) :
    frameFixed buf headEnd req = .reject .bothClAndTe
    ∧ (∀ c, frameFixed buf headEnd req ≠ .complete c) := by
  have hdec : Smuggling.decide req = .reject .bothClAndTe := by
    simp only [Smuggling.decide, hcl, hte, Smuggling.decideOn]
  have hf : frameFixed buf headEnd req = .reject .bothClAndTe := by
    unfold frameFixed; rw [hdec]
  exact ⟨hf, by intro c h; rw [hf] at h; exact Outcome.noConfusion h⟩

/-- **`frame_no_smuggle_general`.** Whenever *any* `Content-Length` header is
present (valid, invalid, or duplicated) together with a chunked
`Transfer-Encoding`, the framer rejects and is never `complete`. The full
guarantee that a CL/TE overlap can never be resolved to a fixed-length boundary. -/
theorem frame_no_smuggle_general (buf : Bytes) (headEnd : Nat) (req : Smuggling.Request)
    (hcl : Smuggling.clStatus req ≠ .absent) (hte : Smuggling.teStatus req = .chunked) :
    (∃ r, frameFixed buf headEnd req = .reject r)
    ∧ (∀ c, frameFixed buf headEnd req ≠ .complete c) := by
  obtain ⟨⟨r, hr⟩, _⟩ := Smuggling.no_desync_general req hcl hte
  have hf : frameFixed buf headEnd req = .reject r := by
    unfold frameFixed; rw [hr]
  exact ⟨⟨r, hf⟩, by intro c h; rw [hf] at h; exact Outcome.noConfusion h⟩

/-! ## Non-vacuity: the concrete CL.TE smuggling probe is rejected -/

/-- The CL.TE vector (`Content-Length: 6` + `Transfer-Encoding: chunked`) is
framed `reject`, at **any** buffer and head length: the proven framer never
computes a boundary for it, so the `SMUGGLED` tail is never split off as a
separate request. -/
theorem clte_frame_rejected (buf : Bytes) (headEnd : Nat) :
    frameFixed buf headEnd Smuggling.clteVector = .reject .bothClAndTe :=
  (frame_no_smuggle buf headEnd 6 Smuggling.clteVector Smuggling.clte_cl Smuggling.clte_te).1

/-- The CL.TE vector is never framed `complete (headEnd + 6)` — the exact desync a
length-only framer would produce (consume 6 body octets, leave `SMUGGLED` as the
next request). -/
theorem clte_frame_not_length (buf : Bytes) (headEnd : Nat) :
    frameFixed buf headEnd Smuggling.clteVector ≠ .complete (headEnd + 6) :=
  (frame_no_smuggle buf headEnd 6 Smuggling.clteVector Smuggling.clte_cl Smuggling.clte_te).2 _

/-! ## The mutant the boundary proof buys -/

/-- A naive length-only framer that consults only `Content-Length`, ignoring
`Transfer-Encoding` — the vulnerable behaviour `frameFixed` replaces. -/
def frameNaive (buf : Bytes) (headEnd : Nat) (req : Smuggling.Request) : Outcome :=
  match Smuggling.clStatus req with
  | .present n => if headEnd + n ≤ buf.length then .complete (headEnd + n) else .needMore
  | _ => .needMore

/-- **The mutant desyncs at the boundary.** On the CL.TE vector, with a buffer
long enough to hold the `Content-Length` body, the naive framer computes a
6-octet-body boundary (`complete (headEnd + 6)`) — precisely the split the proven
framer refuses (`clte_frame_rejected`). The two disagree, so the contract is not
vacuous: a natural mutant violates it. -/
theorem naive_would_smuggle (headEnd : Nat) (buf : Bytes) (hbuf : headEnd + 6 ≤ buf.length) :
    frameNaive buf headEnd Smuggling.clteVector = .complete (headEnd + 6)
    ∧ frameFixed buf headEnd Smuggling.clteVector ≠ frameNaive buf headEnd Smuggling.clteVector := by
  have hcl : Smuggling.clStatus Smuggling.clteVector = .present 6 := Smuggling.clte_cl
  have hn : frameNaive buf headEnd Smuggling.clteVector = .complete (headEnd + 6) := by
    simp only [frameNaive, hcl]; rw [if_pos hbuf]
  refine ⟨hn, ?_⟩
  rw [hn, clte_frame_rejected]
  intro h; exact Outcome.noConfusion h

end Framing
end Body
