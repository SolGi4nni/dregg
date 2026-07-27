import Reactor.ServeStep
import Reactor.ProxyForwardHead
import Proto.Kernel.Shortcuts

/-!
# Reactor.ProxyStreamHead — the CL-trust head-independence lemma (native passthrough streaming)

The whole-reply proxy resume (`Reactor.ServeStep.proxyRespTransform`) feeds the ENTIRE
upstream reply into one continuation, so a native path must buffer the whole body before
it can emit the transformed head — the head carries the derived `Content-Length`, and the
head/body split (`proxyRespTransform_split`) proves head-FIRST delivery is faithful but not
head-BEFORE-body emission.

This file closes that residual for the **non-gzip passthrough** case. It proves the head is
computable from `(input, upstream-head-bytes, body-LENGTH)` alone — never from the body
BYTES — so a native io_uring proxy can compute+emit the transformed head the moment the
upstream head completes and then forward the body straight through, RSS-bounded, without
ever buffering it whole.

The genuine mathematical content is **body-content-independence of the non-gzip transform
stages** (`proxyTransform_body_subst`): for `acceptsGzip (ctxOf input).req = false`, the
four response-transform stages (`deployCorsStage` / `gzipStage` / `securityheadersStage` /
`headerStage`) touch only request-keyed headers + the status/reason — none reads the body
bytes, and none rewrites the body (the gzip re-encode is gated OFF). Combined with the
serializer deriving `Content-Length = body.length`, the transformed head factors through
`body.length`.

`proxyStreamHead` is the exported head computation; `proxyRespHead_factors` is the head-
independence lemma; `proxyStream_bytes_faithful` proves the streamed output
(`head ++ body`) is byte-identical to the buffered `proxyRespTransform`.

**gzip stays honestly open.** When `acceptsGzip` is true, `gzipStage` re-encodes the body,
so the transformed head genuinely depends on the body bytes (its length changes). That case
needs chunked transfer-encoding — a different, deeper residual — and is NOT closed here; the
native path keeps buffering it (`drive_proxy_refines`).
-/

namespace Reactor.ServeStep

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Stage runPipeline ResponseBuilder build_addHeader build_addHeaders
  build_mapResp build_ofResponse)

/-! ## splitHeadBody append-stability

Once `splitHeadBody` has found the first CRLF-CRLF inside a delimiter-terminated head,
appending more bytes only extends the already-decided body tail — the head split point
never moves. This lets a shell that has received the upstream head (through `\r\n\r\n`)
reason about the full reply it has NOT yet received. -/

/-- One-step reduction of `splitHeadBody` once four leading bytes are exposed: it takes the
delimiter branch iff the four bytes are `13,10,13,10`, otherwise peels one byte. -/
theorem splitHeadBody_four (b r0 r1 r2 : UInt8) (tail : Bytes) :
    splitHeadBody (b :: r0 :: r1 :: r2 :: tail)
      = if b = 13 ∧ r0 = 10 ∧ r1 = 13 ∧ r2 = 10 then ([], tail)
        else (b :: (splitHeadBody (r0 :: r1 :: r2 :: tail)).1,
              (splitHeadBody (r0 :: r1 :: r2 :: tail)).2) := by
  by_cases h : b = 13 ∧ r0 = 10 ∧ r1 = 13 ∧ r2 = 10
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rw [splitHeadBody.eq_1]; simp
  · rw [if_neg h, splitHeadBody.eq_def]
    split
    · rename_i he; simp only [List.cons.injEq] at he
      exact absurd ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1⟩ h
    · rename_i b' rest' he; rw [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; rfl
    · rename_i he; simp at he

/-- **Split-append stability.** For a head of the form `pre ++ CRLFCRLF`, appending a body
distributes: the head component is unchanged and the body component gains the appended
bytes. (Holds unconditionally — a straddling early delimiter is accounted for identically
on both sides.) -/
theorem splitHeadBody_append (pre body : Bytes) :
    splitHeadBody (pre ++ [13,10,13,10] ++ body)
      = ((splitHeadBody (pre ++ [13,10,13,10])).1,
         (splitHeadBody (pre ++ [13,10,13,10])).2 ++ body) := by
  induction pre using splitHeadBody.induct with
  | case1 rest => simp only [List.cons_append, splitHeadBody, List.append_assoc]
  | case2 b rest _ _ _ _ ihr =>
      rcases rest with _|⟨r0,_|⟨r1,_|⟨r2,rr⟩⟩⟩
      · simp [splitHeadBody_four]
      · simp only [List.nil_append, List.cons_append, splitHeadBody_four]
        by_cases h : b = 13 ∧ r0 = 10 <;> simp [h]
      · simp only [List.nil_append, List.cons_append, splitHeadBody_four]
        by_cases h : r0 = 13 ∧ r1 = 10 <;> simp [h]
      · have e1 : (b::r0::r1::r2::rr) ++ [13,10,13,10] ++ body
                = b::r0::r1::r2::(rr ++ [13,10,13,10] ++ body) := by simp
        have e2 : (b::r0::r1::r2::rr) ++ [13,10,13,10]
                = b::r0::r1::r2::(rr ++ [13,10,13,10]) := by simp
        rw [e1, e2, splitHeadBody_four b r0 r1 r2 (rr ++ [13,10,13,10] ++ body),
            splitHeadBody_four b r0 r1 r2 (rr ++ [13,10,13,10])]
        by_cases hc : b = 13 ∧ r0 = 10 ∧ r1 = 13 ∧ r2 = 10
        · simp only [if_pos hc, List.append_assoc]
        · rw [if_neg hc, if_neg hc]
          have e3 : r0::r1::r2::(rr ++ [13,10,13,10] ++ body)
                  = (r0::r1::r2::rr) ++ [13,10,13,10] ++ body := by simp
          have e4 : r0::r1::r2::(rr ++ [13,10,13,10])
                  = (r0::r1::r2::rr) ++ [13,10,13,10] := by simp
          rw [e3, e4, ihr]
  | case3 => simp only [List.nil_append, List.cons_append, splitHeadBody]

/-! ## parseUpstream factors through the head bytes -/

/-- `splitCRLFLines` is never empty (its base case is `[[]]`). Kills the dead `[]`
branch of `parseUpstream`. -/
theorem splitCRLFLines_ne_nil (h : Bytes) : splitCRLFLines h ≠ [] := by
  rw [splitCRLFLines.eq_def]
  split
  · simp
  · simp
  · split <;> simp

/-- **`parseUpstream` factors through the head bytes.** For a delimiter-terminated head
`pre ++ CRLFCRLF` (whose first CRLF-CRLF is the terminal one, `hclean`), parsing the full
reply `pre ++ CRLFCRLF ++ body` yields exactly the parse of the head bytes with the body
field swapped in. The status/reason/headers depend ONLY on the head bytes. -/
theorem parseUpstream_split (pre body : Bytes)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    parseUpstream (pre ++ [13,10,13,10] ++ body)
      = { parseUpstream (pre ++ [13,10,13,10]) with body := body } := by
  have hfull : splitHeadBody (pre ++ [13,10,13,10] ++ body) = (pre, body) := by
    rw [splitHeadBody_append, hclean]; rfl
  unfold parseUpstream
  rw [hfull, hclean]
  dsimp only
  rcases hc : splitCRLFLines pre with _ | ⟨sl, hl⟩
  · exact absurd hc (splitCRLFLines_ne_nil pre)
  · rfl

/-! ## The non-gzip transform is body-content-independent (the REAL lemma) -/

/-- The proxy response transform as a `Response → Response`: run the four response-transform
stages over `r` keyed on the original request context. `proxyBuiltResp input upstream`
is exactly `proxyTransform input (parseUpstream upstream)`. -/
def proxyTransform (input : Bytes) (r : Response) : Response :=
  (runPipeline proxyRespStages (fun _ => r) (Reactor.Deploy.ctxOf input)).build

theorem proxyTransform_of_parse (input upstream : Bytes) :
    proxyBuiltResp input upstream = proxyTransform input (parseUpstream upstream) := rfl

/-- **Body-content-independence of the non-gzip transform.** When the request does NOT
accept gzip, running the response-transform stages over `{ r with body := b }` produces the
SAME status/reason/headers as running them over `r`, with the body simply threaded through.
No stage reads the body bytes, and no stage rewrites the body (the gzip re-encode is gated
OFF). This is the load-bearing fact: the transformed HEAD is a function of the request +
the parsed upstream head, not of the body content. -/
theorem proxyTransform_body_subst (input : Bytes) (r : Response) (body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false) :
    proxyTransform input { r with body := body }
      = { proxyTransform input r with body := body } := by
  unfold proxyTransform proxyRespStages
  simp only [runPipeline, Reactor.Deploy.deployCorsStage, Reactor.Stage.Gzip.gzipStage,
    Reactor.Stage.SecurityHeaders.securityheadersStage, Reactor.Stage.Header.headerStage, hgz]
  split <;>
    simp only [build_addHeader, build_addHeaders, build_mapResp, build_ofResponse,
      Reactor.Stage.Header.rewriteResp, List.append_assoc]

/-- **The transformed proxy response over the full reply splits off its body.** For a clean,
non-gzip reply `pre ++ CRLFCRLF ++ body`, the built transformed response is exactly the one
built over the head-only bytes with the real body swapped in — so its status/reason/headers
are body-content-independent and its body is exactly `body`. -/
theorem proxyBuiltResp_split (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyBuiltResp input (pre ++ [13,10,13,10] ++ body)
      = { proxyBuiltResp input (pre ++ [13,10,13,10]) with body := body } := by
  rw [proxyTransform_of_parse, proxyTransform_of_parse,
      parseUpstream_split pre body hclean, proxyTransform_body_subst input _ body hgz]

/-! ## The exported streaming head + the head-independence lemma -/

/-- **The transformed proxy response HEAD, computed from `(input, upstream-head, body-len)`
WITHOUT the body bytes.** Parse the head-only bytes (the body parses empty), run the
non-gzip transform (which keeps the body empty), then render the head — status line, the
transformed header block, and the derived `Content-Length` set to the KNOWN `bodyLen` (from
the upstream `Content-Length`), followed by the blank-line separator. This is the head the
native streaming proxy emits the moment the upstream head completes; the body then streams
through. -/
def proxyStreamHead (input upHead : Bytes) (bodyLen : Nat) : Bytes :=
  let R := proxyBuiltResp input upHead
  Reactor.statusLineOf R ++ Reactor.crlf
    ++ Reactor.renderHeaders (R.headers ++ [(Reactor.clName, Reactor.natToDec bodyLen)])
    ++ Reactor.crlf ++ Reactor.crlf

/-- **THE CL-TRUST HEAD-INDEPENDENCE LEMMA.** For a request that does NOT accept gzip and a
clean upstream head `pre ++ CRLFCRLF`, the transformed proxy response HEAD over the full
reply `pre ++ CRLFCRLF ++ body` equals `proxyStreamHead input (pre ++ CRLFCRLF) body.length`
— a function of `(input, upstream-head-bytes, body.length)` that NEVER inspects the body
BYTES. The head factors through the body's LENGTH. -/
theorem proxyRespHead_factors (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyRespHead input (pre ++ [13,10,13,10] ++ body)
      = proxyStreamHead input (pre ++ [13,10,13,10]) body.length := by
  unfold proxyRespHead proxyStreamHead
  rw [proxyBuiltResp_split input pre body hgz hclean]
  simp only [Reactor.statusLineOf, Reactor.headerBlockOf, Reactor.allHeaders, Reactor.build,
    Reactor.statusLine]

/-- **Body-content-independence (the two-body witness that the head factors through
length).** Two non-gzip replies with the SAME head and EQUAL body lengths produce the SAME
transformed head — regardless of body content. Non-vacuous corollary of
`proxyRespHead_factors`. -/
theorem proxyRespHead_body_content_indep (input pre b1 b2 : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, []))
    (hlen : b1.length = b2.length) :
    proxyRespHead input (pre ++ [13,10,13,10] ++ b1)
      = proxyRespHead input (pre ++ [13,10,13,10] ++ b2) := by
  rw [proxyRespHead_factors input pre b1 hgz hclean,
      proxyRespHead_factors input pre b2 hgz hclean, hlen]

/-- **Byte-identity of the streamed output to the buffered transform.** The streamed
non-gzip output — the body-free head `proxyStreamHead` followed by the raw body streamed
through — is byte-for-byte the buffered `proxyRespTransform input (full reply)`. So the
native streaming path (compute head on head-complete, forward body chunks) produces exactly
the bytes the buffered oracle produces, while never holding the body whole. -/
theorem proxyStream_bytes_faithful (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyStreamHead input (pre ++ [13,10,13,10]) body.length ++ body
      = proxyRespTransform input (pre ++ [13,10,13,10] ++ body) := by
  rw [proxyRespTransform_split, ← proxyRespHead_factors input pre body hgz hclean,
      proxyBuiltResp_split input pre body hgz hclean]

#print axioms splitHeadBody_append
#print axioms proxyTransform_body_subst
#print axioms proxyRespHead_factors
#print axioms proxyStream_bytes_faithful

end Reactor.ServeStep

/-! # ★ The SEAM's bare-LF upstream-response gate: what it buys (RFC 9112 §2.2)

`Reactor.ServeStep.proxyRespGate` refuses an upstream reply whose HEAD BLOCK carries a
bare LF, and the seam's proxy continuation crosses `proxyRespTransformGated` instead of
`proxyRespTransform`. That re-points the two CL-trust theorems above
(`proxyRespHead_factors`, `proxyStream_bytes_faithful`) off the deployed path: they are
stated over the UNGATED transform, which is no longer what the resume emits.

They are **not deleted and not weakened**. Both are RESTATED here over the object the
seam now crosses, with the gate's own admission hypothesis (`noBareLF pre`) added — the
hypothesis under which the gated and ungated transforms are byte-identical
(`seamGate_bytes_clean`). Nothing about the CL-trust argument changes; the streaming
native proxy simply inherits the refusal for the heads the gate refuses.
-/

namespace Reactor.ServeStep

open Proto (Bytes)
open Body.FrameRaw (noBareLF)

/-! ## The gate's condition on a delimiter-terminated reply -/

/-- For a reply of the shape the CL-trust lemmas take (`pre ++ CRLFCRLF ++ body`, whose
first CRLFCRLF is the terminal one), the gate's head block IS `pre`. So the gate decides
on exactly the head bytes these lemmas already reason about — never on the body, which
may legitimately carry bare LFs. -/
theorem upstreamHeadBlock_append (pre body : Bytes)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    upstreamHeadBlock (pre ++ [13,10,13,10] ++ body) = pre := by
  unfold upstreamHeadBlock
  rw [splitHeadBody_append, hclean]

/-- The gate ADMITS a clean delimiter-terminated reply. -/
theorem proxyRespGate_clean_append (input pre body : Bytes)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, []))
    (hlf : noBareLF pre = true) :
    proxyRespGate input (pre ++ [13,10,13,10] ++ body)
      = .forward (proxyRespTransform input (pre ++ [13,10,13,10] ++ body)) :=
  seamGate_clean input _ (by rw [upstreamHeadBlock_append pre body hclean]; exact hlf)

/-! ## ★ The two CL-trust theorems, RESTATED under the gate -/

/-- **`proxyStream_bytes_faithful`, RESTATED UNDER THE GATE.** For a non-gzip reply whose
head block has unambiguous line terminators (`noBareLF pre` — exactly what the gate
admits on), the streamed non-gzip output — the body-free head `proxyStreamHead` followed
by the raw body streamed through — is byte-for-byte what the GATED seam transform emits.
So the native streaming path still produces exactly the bytes the deployed (now gated)
oracle produces, while never holding the body whole.

Nothing was weakened: the conclusion is the same byte equality, over the gated object,
with the gate's admission condition as an added hypothesis. On a head the gate refuses
there are no streamed bytes to be faithful to — `proxyStreamGated_rejects` below says
what the seam emits instead. -/
theorem proxyStreamGated_bytes_faithful (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, []))
    (hlf : noBareLF pre = true) :
    proxyStreamHead input (pre ++ [13,10,13,10]) body.length ++ body
      = proxyRespTransformGated input (pre ++ [13,10,13,10] ++ body) := by
  rw [seamGate_bytes_clean input _
    (by rw [upstreamHeadBlock_append pre body hclean]; exact hlf)]
  exact proxyStream_bytes_faithful input pre body hgz hclean

/-- **`proxyRespHead_factors`, RESTATED UNDER THE GATE.** For an admitted reply the gate's
verdict is `forward`, and the bytes it forwards are exactly
`proxyStreamHead input upHead body.length ++ body` — a head computed from
`(input, upstream-head-bytes, body.LENGTH)` alone, never from the body BYTES, followed by
the body streamed through. The head-independence the native streaming proxy needs
survives the gate verbatim; the gate only decides WHETHER there is a head to compute. -/
theorem proxyRespHeadGated_factors (input pre body : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, []))
    (hlf : noBareLF pre = true) :
    proxyRespGate input (pre ++ [13,10,13,10] ++ body)
      = .forward (proxyStreamHead input (pre ++ [13,10,13,10]) body.length ++ body) := by
  rw [proxyRespGate_clean_append input pre body hclean hlf,
      proxyStreamGated_bytes_faithful input pre body hgz hclean hlf,
      seamGate_bytes_clean input _
        (by rw [upstreamHeadBlock_append pre body hclean]; exact hlf)]

/-- **★ The refusal, at the CL-trust interface.** A reply whose head block carries a bare
LF is refused: the seam emits the `502 Bad Gateway` bytes, and NOT the streamed head —
so a native streaming proxy that respects the gate must not begin emitting a head for a
refused reply. -/
theorem proxyStreamGated_rejects (input pre body : Bytes)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, []))
    (hbare : noBareLF pre = false) :
    proxyRespTransformGated input (pre ++ [13,10,13,10] ++ body) = gatewayError false :=
  seamGate_bytes_rejected input _
    (by rw [upstreamHeadBlock_append pre body hclean]; exact hbare)

/-! ## ★ What the gate admits, this hop and its client parse the same way -/

/-- **The seam analogue of `Reactor.ProxyForward.respGate_forward_parses_agree`.** For an
upstream reply the seam gate admitted, the LF-tolerant parse an RFC 9112 §2.2 recipient
may take of the head block equals the CRLF-only parse `parseUpstream` took of it. The
disagreement the live demonstration exploited cannot arise on a reply the gate admits. -/
theorem seamGate_forward_parses_agree (input upstream out : Bytes)
    (h : proxyRespGate input upstream = .forward out) :
    Reactor.ProxyForward.splitLFLines (upstreamHeadBlock upstream)
      = splitCRLFLines (upstreamHeadBlock upstream) :=
  Reactor.ProxyForward.splitLFLines_eq_splitCRLFLines _
    (seamGate_forward_noBareLF input upstream out h)

/-! ## ★ Non-vacuity: the crafted upstream reply the deployed SEAM leaked

The exact bytes `conformance/proxy/respsplit_probe.py` serves at `/api/cookie`. With
`PROXY_SEAM=1 PROXY_IO=uring` the shipped io_uring reactor threaded this reply through
`proxyRespTransform` and `curl -D -` read a `Set-Cookie` field out of the result that
this proxy never saw as a field (measured 2026-07-25, this lane). -/

/-- The crafted upstream REPLY (head + `CRLFCRLF` + body `ok\n`) the hostile upstream
returns — the whole thing, as the seam receives it. -/
def seamBareLFUpstream : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 67, 111, 110, 116,
   101, 110, 116, 45, 84, 121, 112, 101, 58, 32, 116, 101, 120, 116, 47, 112, 108, 97, 105,
   110, 13, 10, 88, 45, 84, 97, 103, 58, 32, 97, 10, 83, 101, 116, 45, 67, 111, 111, 107,
   105, 101, 58, 32, 115, 101, 115, 115, 61, 69, 86, 73, 76, 59, 32, 80, 97, 116, 104, 61,
   47, 13, 10, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32,
   51, 13, 10, 13, 10, 111, 107, 10]

/-- `X-Tag` — the header name the injected field hid behind. -/
def xTagName : Bytes := [88, 45, 84, 97, 103]

/-- `a LF Set-Cookie: sess=EVIL; Path=/` — the VALUE `parseUpstream` assigned to `X-Tag`
on the crafted reply. The whole injected field-line sits INSIDE it. -/
def xTagInjectedValue : Bytes :=
  [97, 10, 83, 101, 116, 45, 67, 111, 111, 107, 105, 101, 58, 32, 115, 101, 115, 115, 61,
   69, 86, 73, 76, 59, 32, 80, 97, 116, 104, 61, 47]

/-- The seam's head block for the crafted reply is EXACTLY the default path's witness
head (`Reactor.ProxyForward.bareLFRespHead`) — the two paths were leaking the same bytes,
so they are now refusing the same bytes. -/
theorem seamHeadBlock_is_default_witness :
    upstreamHeadBlock seamBareLFUpstream = Reactor.ProxyForward.bareLFRespHead := by decide

/-- **★ THE NON-VACUITY WITNESS: the PRE-gate seam really did admit the crafted head.**
Machine-checked, all on the ungated objects the seam used to cross:

1. `parseUpstream` ADMITTED the reply and produced a header whose VALUE is
   `a LF Set-Cookie: sess=EVIL; Path=/` — the injected field-line, swallowed whole into
   `X-Tag`'s value. The serializer renders header values VERBATIM
   (`Reactor.serialize_response_splitting` is the standing finding), so those bytes —
   bare LF and all — go straight onto the wire.
2. The two admissible parses of that head DISAGREE, and the disagreement is a whole
   field-line: the LF-tolerant parse (what `curl` took) carries
   `Set-Cookie: sess=EVIL; Path=/` as a field of its own; the CRLF-only parse (what this
   core took, and therefore what every header decision ran on) does not contain it.
3. The gate REFUSES it, for every request — so the refusal changes a real verdict on a
   real vector.

Points 1–2 are the pre-fix behaviour, machine-checked, not a reconstruction. -/
theorem seamBareLF_gate_not_vacuous :
    (xTagName, xTagInjectedValue) ∈ (parseUpstream seamBareLFUpstream).headers
    ∧ Reactor.ProxyForward.splitLFLines (upstreamHeadBlock seamBareLFUpstream)
        ≠ splitCRLFLines (upstreamHeadBlock seamBareLFUpstream)
    ∧ Reactor.ProxyForward.setCookieLine
        ∈ Reactor.ProxyForward.splitLFLines (upstreamHeadBlock seamBareLFUpstream)
    ∧ Reactor.ProxyForward.setCookieLine
        ∉ splitCRLFLines (upstreamHeadBlock seamBareLFUpstream)
    ∧ noBareLF (upstreamHeadBlock seamBareLFUpstream) = false := by decide

/-- **The gate refuses the crafted reply, for EVERY request.** The seam's wire answer is
the `502`, whatever the client asked for. -/
theorem seamBareLF_refused (input : Bytes) :
    proxyRespGate input seamBareLFUpstream = .reject
    ∧ proxyRespTransformGated input seamBareLFUpstream = gatewayError false :=
  ⟨(seamGate_bareLF_rejected input seamBareLFUpstream (by decide)).1,
   seamGate_bytes_rejected input seamBareLFUpstream (by decide)⟩

/-- **Regression guard on the seam.** The ungated transform and the gate do not merely
differ as verdicts — anyone who re-points the seam's continuation back at
`proxyRespTransform` changes the crafted reply's answer from "reject, 502" to "forward
the transformed head", and this inequality is what says so. -/
theorem seamGate_ungated_differs (input : Bytes) :
    UpstreamOutcome.forward (proxyRespTransform input seamBareLFUpstream)
      ≠ proxyRespGate input seamBareLFUpstream := by
  rw [(seamBareLF_refused input).1]
  exact fun h => UpstreamOutcome.noConfusion h

#print axioms upstreamHeadBlock_append
#print axioms proxyStreamGated_bytes_faithful
#print axioms proxyRespHeadGated_factors
#print axioms proxyStreamGated_rejects
#print axioms seamGate_forward_parses_agree
#print axioms seamHeadBlock_is_default_witness
#print axioms seamBareLF_gate_not_vacuous
#print axioms seamBareLF_refused
#print axioms seamGate_ungated_differs

end Reactor.ServeStep

/-! # ★ …and the head the SEAM EMITS has one parse too

`seamGate_forward_parses_agree` is about the head that came IN. The client is handed what
goes OUT — and unlike the default path (which filters the upstream's own lines and rejoins
them), the seam PARSES the upstream reply into a `Response` and RE-SERIALIZES it. That is
not automatically safer: `Reactor.serialize` renders a header value VERBATIM (the standing
egress finding `Reactor.serialize_response_splitting`), so a bare LF that reached a header
value would forge a field line on the wire — which is exactly how the live leak worked
(`seamBareLF_gate_not_vacuous` (1): the injected `Set-Cookie` line was sitting inside
`X-Tag`'s VALUE).

It cannot happen on an admitted reply. The gate's `noBareLF` on the head block forces
something strictly stronger than "no bare LF" on every piece the serializer renders: the
lines of a bare-LF-free CRLF block contain **no LF octet at all** (`noLF`), because any LF
in a line would have to be CR-preceded — and a `CRLF` inside a line is impossible, that is
where `splitCRLFLines` cut. `noLF`, unlike `noBareLF`, IS closed under the sublists a parse
takes (name before the colon, value after it), so it survives parse-and-re-serialize. Every
other piece of the emitted head is a fixed constant or a decimal number.
-/

namespace Reactor.ServeStep

open Proto (Bytes)
open Body.FrameRaw (noBareLF)

/-! ## `noLF` — no LF octet at all -/

/-- **No `LF` octet anywhere.** Strictly stronger than `noBareLF`, and — unlike it — closed
under taking sublists. That closure is the whole point: a parse cuts field names and values
OUT of a line, and `noBareLF` is not preserved by cutting (dropping the `CR` of a `CRLF`
manufactures a bare LF), while `noLF` is. -/
def noLF (bs : Bytes) : Prop := (10 : UInt8) ∉ bs

instance instDecidableNoLF (bs : Bytes) : Decidable (noLF bs) := by unfold noLF; infer_instance

theorem noLF_nil : noLF ([] : Bytes) := by simp [noLF]

theorem noLF_cons {b : UInt8} {bs : Bytes} (hb : (10 : UInt8) ≠ b) (h : noLF bs) :
    noLF (b :: bs) := by
  simp only [noLF, List.mem_cons, not_or]
  exact ⟨hb, h⟩

theorem noLF_head {b : UInt8} {bs : Bytes} (h : noLF (b :: bs)) : (10 : UInt8) ≠ b := by
  simp only [noLF, List.mem_cons, not_or] at h
  exact h.1

theorem noLF_tail {b : UInt8} {bs : Bytes} (h : noLF (b :: bs)) : noLF bs := by
  simp only [noLF, List.mem_cons, not_or] at h
  exact h.2

theorem noLF_append {a b : Bytes} (ha : noLF a) (hb : noLF b) : noLF (a ++ b) := by
  simp only [noLF, List.mem_append, not_or]
  exact ⟨ha, hb⟩

/-- **`noLF` for an ASCII string constant.** `String.toUTF8`-derived byte constants are
opaque to `decide` (`ByteArray.toList` is well-founded), so the deployed header CONSTANTS
go through `Proto.Kernel.Shortcuts.toUTF8_toList_ascii`, which rewrites them to a
structural `map` the kernel does reduce. No `native_decide`. -/
theorem noLF_of_ascii (s : String)
    (h : ∀ c ∈ s.toList, c.val ≤ 0x7f ∧ c.val.toUInt8 ≠ 10) : noLF s.toUTF8.toList := by
  rw [Proto.Kernel.Shortcuts.toUTF8_toList_ascii s (fun c hc => (h c hc).1)]
  intro hmem
  simp only [List.mem_map] at hmem
  obtain ⟨c, hc, hce⟩ := hmem
  exact (h c hc).2 hce

/-- `noLF` implies `noBareLF`: with no LF at all there is certainly no *bare* LF. -/
theorem noLF_noBareLF : ∀ (bs : Bytes), noLF bs → noBareLF bs = true := by
  intro bs
  induction bs using Body.FrameRaw.noBareLF.induct with
  | case1 => intro _; rfl
  | case2 rest _ => intro h; exact absurd (by simp) h
  | case3 x => intro h; exact absurd (by simp) h
  | case4 b rest h1 h2 ih =>
    intro h
    rw [Body.FrameRaw.noBareLF_cons_step b rest h2 h1]
    exact ih (noLF_tail h)

/-! ## The lines of a bare-LF-free block carry NO LF at all -/

/-- **★ The strengthening the gate buys.** Every line `splitCRLFLines` cuts out of a block
with no bare LF contains no `LF` octet whatsoever. (An LF inside a line would have to be
CR-preceded — the block is `noBareLF` — but a `CRLF` inside a line is impossible: that is
precisely where `splitCRLFLines` cuts.) This is what makes the guarantee survive the
seam's parse-and-re-serialize, where the default path only needed `noBareLF`. -/
theorem splitCRLFLines_lines_noLF : ∀ (bs : Bytes), noBareLF bs = true →
    ∀ l ∈ splitCRLFLines bs, noLF l := by
  intro bs
  induction bs using Body.FrameRaw.noBareLF.induct with
  | case1 =>
    intro _ l hl
    rw [show splitCRLFLines ([] : Bytes) = [[]] from rfl] at hl
    rcases List.mem_singleton.mp hl with rfl
    exact noLF_nil
  | case2 rest ih =>
    intro h l hl
    have hr : noBareLF rest = true := by simpa [Body.FrameRaw.noBareLF] using h
    rw [show splitCRLFLines (13 :: 10 :: rest) = [] :: splitCRLFLines rest from rfl] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact noLF_nil
    · exact ih hr l hl'
  | case3 x => intro h; simp [Body.FrameRaw.noBareLF] at h
  | case4 b rest h1 h2 ih =>
    intro h l hl
    have hr : noBareLF rest = true := by
      rwa [Body.FrameRaw.noBareLF_cons_step b rest h2 h1] at h
    rw [Reactor.ProxyForward.splitCRLFLines_cons b rest h1] at hl
    rcases hs : splitCRLFLines rest with _ | ⟨l0, ls⟩
    · exact absurd hs (splitCRLFLines_ne_nil rest)
    · rw [hs] at hl
      simp only at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · refine noLF_cons (fun hc => h2 hc.symm) (ih hr l0 ?_)
        rw [hs]; exact List.mem_cons_self ..
      · exact ih hr l (by rw [hs]; exact List.mem_cons_of_mem l0 hl')

/-! ## The parse helpers cut sublists, so they preserve `noLF` -/

theorem afterFirstSpace_cons (b : UInt8) (rest : Bytes) (hb : b = 32 → False) :
    afterFirstSpace (b :: rest) = afterFirstSpace rest := by
  rw [afterFirstSpace.eq_def]; split <;> simp_all

theorem afterColon_cons (b : UInt8) (rest : Bytes) (hb : b = 58 → False) :
    afterColon (b :: rest) = afterColon rest := by
  rw [afterColon.eq_def]; split <;> simp_all

theorem beforeColon_cons (b : UInt8) (rest : Bytes) (hb : b = 58 → False) :
    beforeColon (b :: rest) = b :: beforeColon rest := by
  rw [beforeColon.eq_def]; split <;> simp_all

theorem trimLeadingSpace_cons (b : UInt8) (rest : Bytes) (hb : b = 32 → False) :
    trimLeadingSpace (b :: rest) = b :: rest := by
  rw [trimLeadingSpace.eq_def]; split <;> simp_all

theorem noLF_afterFirstSpace : ∀ (l : Bytes), noLF l → noLF (afterFirstSpace l) := by
  intro l
  induction l using afterFirstSpace.induct with
  | case1 => intro _; exact noLF_nil
  | case2 rest => intro h; exact noLF_tail h
  | case3 b rest hb ih => intro h; rw [afterFirstSpace_cons b rest hb]; exact ih (noLF_tail h)

theorem noLF_afterColon : ∀ (l : Bytes), noLF l → noLF (afterColon l) := by
  intro l
  induction l using afterColon.induct with
  | case1 => intro _; exact noLF_nil
  | case2 rest => intro h; exact noLF_tail h
  | case3 b rest hb ih => intro h; rw [afterColon_cons b rest hb]; exact ih (noLF_tail h)

theorem noLF_beforeColon : ∀ (l : Bytes), noLF l → noLF (beforeColon l) := by
  intro l
  induction l using beforeColon.induct with
  | case1 => intro _; exact noLF_nil
  | case2 rest => intro _; exact noLF_nil
  | case3 b rest hb ih =>
    intro h
    rw [beforeColon_cons b rest hb]
    exact noLF_cons (noLF_head h) (ih (noLF_tail h))

theorem noLF_trimLeadingSpace : ∀ (l : Bytes), noLF l → noLF (trimLeadingSpace l) := by
  intro l
  induction l using trimLeadingSpace.induct with
  | case1 rest ih => intro h; exact ih (noLF_tail h)
  | case2 l hb =>
    intro h
    rw [trimLeadingSpace.eq_def]
    split <;> simp_all

/-! ## The parsed upstream `Response` is LF-free where it matters -/

/-- Both the reason phrase and every parsed header name/value of an ADMITTED upstream reply
carry no LF at all. -/
theorem parseUpstream_noLF (bs : Bytes) (h : noBareLF (upstreamHeadBlock bs) = true) :
    noLF (parseUpstream bs).reason
    ∧ ∀ nv ∈ (parseUpstream bs).headers, noLF nv.1 ∧ noLF nv.2 := by
  have hlines := splitCRLFLines_lines_noLF (upstreamHeadBlock bs) h
  obtain ⟨sl, hls, hsl⟩ : ∃ sl hls, splitCRLFLines (upstreamHeadBlock bs) = sl :: hls := by
    cases hc : splitCRLFLines (upstreamHeadBlock bs) with
    | nil => exact absurd hc (splitCRLFLines_ne_nil _)
    | cons a b => exact ⟨a, b, rfl⟩
  have hslLF : noLF sl := hlines sl (by rw [hsl]; exact List.mem_cons_self ..)
  have hred : parseUpstream bs
      = { status := parseNat (beforeFirstSpace (afterFirstSpace sl)),
          reason := afterFirstSpace (afterFirstSpace sl),
          headers := hls.filterMap (fun line =>
            if hasColon line then
              if isContentLength (beforeColon line) then none
              else some (beforeColon line, trimLeadingSpace (afterColon line))
            else none),
          body := (splitHeadBody bs).2 } := by
    unfold parseUpstream
    cases hsb : splitHeadBody bs with
    | mk head body =>
      have hh : head = upstreamHeadBlock bs := by unfold upstreamHeadBlock; rw [hsb]
      subst hh
      dsimp only
      rw [hsl]
  rw [hred]
  refine ⟨noLF_afterFirstSpace _ (noLF_afterFirstSpace _ hslLF), ?_⟩
  intro nv hnv
  simp only [List.mem_filterMap] at hnv
  obtain ⟨line, hline, heq⟩ := hnv
  have hlineLF : noLF line :=
    hlines line (by rw [hsl]; exact List.mem_cons_of_mem sl hline)
  by_cases hc : hasColon line
  · rw [if_pos hc] at heq
    by_cases hcl : isContentLength (beforeColon line)
    · rw [if_pos hcl] at heq; exact absurd heq (by simp)
    · rw [if_neg hcl, Option.some.injEq] at heq
      subst heq
      exact ⟨noLF_beforeColon _ hlineLF,
             noLF_trimLeadingSpace _ (noLF_afterColon _ hlineLF)⟩
  · rw [if_neg hc] at heq; exact absurd heq (by simp)

/-! ## The four transform stages add only LF-free constants -/

/-- The header rewrite (`Header.run [hopDyn, set Server reactor]`) only DELETES fields and
adds one literal: every field of the output is a field of the input or the `Server` line. -/
theorem run_rewriteProg_mem (hs : _root_.Header.Headers) (f : _root_.Header.Field)
    (hf : f ∈ _root_.Header.run Reactor.Stage.Header.rewriteProg hs) :
    f ∈ hs ∨ f = ⟨Reactor.Stage.Header.serverName, Reactor.Stage.Header.serverVal⟩ := by
  have hrun : _root_.Header.run Reactor.Stage.Header.rewriteProg hs
      = _root_.Header.remove Reactor.Stage.Header.serverName
          (_root_.Header.strip (_root_.Header.dynHopSet hs) hs)
        ++ [⟨Reactor.Stage.Header.serverName, Reactor.Stage.Header.serverVal⟩] := rfl
  rw [hrun, List.mem_append] at hf
  rcases hf with hf | hf
  · exact Or.inl (List.mem_filter.mp (List.mem_filter.mp hf).1).1
  · exact Or.inr (List.mem_singleton.mp hf)

theorem rewriteResp_noLF (r : Reactor.Response)
    (h : ∀ nv ∈ r.headers, noLF nv.1 ∧ noLF nv.2) :
    ∀ nv ∈ (Reactor.Stage.Header.rewriteResp r).headers, noLF nv.1 ∧ noLF nv.2 := by
  intro nv hnv
  simp only [Reactor.Stage.Header.rewriteResp, Reactor.Stage.Header.fromFields,
    List.mem_map] at hnv
  obtain ⟨f, hf, rfl⟩ := hnv
  rcases run_rewriteProg_mem _ f hf with hf' | rfl
  · simp only [Reactor.Stage.Header.toFields, List.mem_map] at hf'
    obtain ⟨p, hp, rfl⟩ := hf'
    exact h p hp
  · exact ⟨by decide, by decide⟩

/-- The deployed security-header set is a fixed table of literals: LF-free by computation. -/
theorem wireHeaders_noLF :
    ∀ nv ∈ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy,
      noLF nv.1 ∧ noLF nv.2 := by
  have hascii : ∀ kv ∈ _root_.SecurityHeaders.render Reactor.Stage.SecurityHeaders.policy,
      (∀ c ∈ kv.1.toList, c.val ≤ 0x7f ∧ c.val.toUInt8 ≠ 10)
      ∧ (∀ c ∈ kv.2.toList, c.val ≤ 0x7f ∧ c.val.toUInt8 ≠ 10) := by decide
  intro nv hnv
  simp only [Reactor.Stage.SecurityHeaders.wireHeaders, List.mem_map] at hnv
  obtain ⟨kv, hkv, rfl⟩ := hnv
  simp only [Reactor.Stage.SecurityHeaders.toWireHeader]
  exact ⟨noLF_of_ascii kv.1 (hascii kv hkv).1, noLF_of_ascii kv.2 (hascii kv hkv).2⟩

/-- **The deployed CORS policy emits a CONSTANT value.** `corsPolicy` has
`allowAnyOrigin := false` and `allowCredentials := false` and exactly one allowed origin,
so the only `Access-Control-Allow-Origin` value it can ever emit is that literal — the
request's `Origin` bytes are never echoed unless they ARE the literal. So the one
request-derived header on this path is in fact request-INDEPENDENT, and LF-free. -/
theorem acaoValue_const {o v : String}
    (h : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy o = some v) :
    v = "https://app.example.com" := by
  by_cases hb : o = "https://app.example.com"
  · subst hb
    simp only [_root_.Cors.acaoValue, _root_.Cors.originAllowed, Reactor.Stage.Cors.corsPolicy,
      Option.some.injEq] at h
    simp at h
    exact h.symm
  · exfalso
    simp only [_root_.Cors.acaoValue, _root_.Cors.originAllowed, Reactor.Stage.Cors.corsPolicy]
      at h
    simp [hb] at h

theorem acao_noLF {o v : String}
    (h : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy o = some v) :
    noLF Reactor.Stage.Cors.acaoName ∧ noLF (Reactor.Stage.Cors.strBytes v) := by
  rw [acaoValue_const h]
  exact ⟨noLF_of_ascii "Access-Control-Allow-Origin" (by decide),
         noLF_of_ascii "https://app.example.com" (by decide)⟩

/-! ## The built proxy response: reason + headers are LF-free -/

theorem proxyBuiltResp_reason (input upstream : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false) :
    (proxyBuiltResp input upstream).reason = (parseUpstream upstream).reason := by
  unfold proxyBuiltResp proxyRespStages
  simp only [Reactor.Pipeline.runPipeline, Reactor.Deploy.deployCorsStage,
    Reactor.Stage.Gzip.gzipStage, Reactor.Stage.SecurityHeaders.securityheadersStage,
    Reactor.Stage.Header.headerStage, hgz]
  split <;>
    simp [Reactor.Pipeline.build_addHeader, Reactor.Pipeline.build_addHeaders,
      Reactor.Pipeline.build_mapResp, Reactor.Pipeline.build_ofResponse,
      Reactor.Stage.Header.rewriteResp]

theorem proxyBuiltResp_headers (input upstream : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false) :
    (proxyBuiltResp input upstream).headers
      = (Reactor.Stage.Header.rewriteResp (parseUpstream upstream)).headers
        ++ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy
        ++ (match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
                (Reactor.Deploy.corsOriginOf (Reactor.Deploy.ctxOf input)) with
            | some v => [(Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)]
            | none   => ([] : List (Bytes × Bytes))) := by
  unfold proxyBuiltResp proxyRespStages
  rcases hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
      (Reactor.Deploy.corsOriginOf (Reactor.Deploy.ctxOf input)) with _ | v <;>
    simp [Reactor.Pipeline.runPipeline, Reactor.Deploy.deployCorsStage,
      Reactor.Stage.Gzip.gzipStage, Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage, hgz, hv, Reactor.Pipeline.build_addHeader,
      Reactor.Pipeline.build_addHeaders, Reactor.Pipeline.build_mapResp,
      Reactor.Pipeline.build_ofResponse, List.append_assoc]

/-- **Every header the emitted head carries is LF-free, on an ADMITTED upstream reply.** -/
theorem proxyBuiltResp_noLF (input upstream : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hup : noBareLF (upstreamHeadBlock upstream) = true) :
    noLF (proxyBuiltResp input upstream).reason
    ∧ ∀ nv ∈ (proxyBuiltResp input upstream).headers, noLF nv.1 ∧ noLF nv.2 := by
  obtain ⟨hreason, hhdrs⟩ := parseUpstream_noLF upstream hup
  refine ⟨by rw [proxyBuiltResp_reason input upstream hgz]; exact hreason, ?_⟩
  intro nv hnv
  rw [proxyBuiltResp_headers input upstream hgz, List.mem_append, List.mem_append] at hnv
  rcases hnv with (hnv | hnv) | hnv
  · exact rewriteResp_noLF (parseUpstream upstream) hhdrs nv hnv
  · exact wireHeaders_noLF nv hnv
  · rcases hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
        (Reactor.Deploy.corsOriginOf (Reactor.Deploy.ctxOf input)) with _ | v
    · rw [hv] at hnv; simp at hnv
    · rw [hv] at hnv
      simp only [List.mem_singleton] at hnv
      subst hnv
      exact acao_noLF hv

/-! ## The serializer turns LF-free fields into a head with only structural CRLFs -/

/-- Every byte of a decimal rendering is an ASCII digit (`Proto.Dec.natToDec_isDigit`), so
it is never an `LF`. -/
theorem natToDec_noLF (n : Nat) : noLF (Reactor.natToDec n) := by
  intro hc
  have hd := Proto.Dec.natToDec_isDigit n (10 : UInt8)
    (by exact hc : (10 : UInt8) ∈ Proto.Dec.natToDec n)
  exact absurd hd.1 (by decide)

theorem headerLine_noLF (nv : Bytes × Bytes) (h1 : noLF nv.1) (h2 : noLF nv.2) :
    noLF (Reactor.headerLine nv) := by
  unfold Reactor.headerLine
  exact noLF_append (noLF_append h1 (by decide)) h2

/-- **The rendered header block has only structural line terminators.** Joining LF-free
`name: value` lines with CRLF cannot produce a bare LF. -/
theorem renderHeaders_noBareLF : ∀ (hs : List (Bytes × Bytes)),
    (∀ nv ∈ hs, noLF nv.1 ∧ noLF nv.2) → noBareLF (Reactor.renderHeaders hs) = true := by
  intro hs
  induction hs using Reactor.renderHeaders.induct with
  | case1 => intro _; decide
  | case2 hd =>
    intro hall
    have := hall hd (List.mem_singleton.mpr rfl)
    exact noLF_noBareLF _ (headerLine_noLF hd this.1 this.2)
  | case3 hd tl htl ih =>
    intro hall
    have hhd := hall hd (List.mem_cons_self ..)
    have hred : Reactor.renderHeaders (hd :: tl)
        = Reactor.headerLine hd ++ Reactor.crlf ++ Reactor.renderHeaders tl := by
      rw [Reactor.renderHeaders.eq_def]; split <;> simp_all
    rw [hred]
    exact Reactor.ProxyForward.noBareLF_append _ _
      (Reactor.ProxyForward.noBareLF_append _ _
        (noLF_noBareLF _ (headerLine_noLF hd hhd.1 hhd.2))
        (show noBareLF Reactor.crlf = true by decide))
      (ih (fun nv hnv => hall nv (List.mem_cons_of_mem hd hnv)))

/-- **★ THE EMITTED-HEAD PROPERTY.** The response head the seam SENDS for an admitted
upstream reply carries no bare LF: its only `LF` octets are the `CRLF`s the serializer
itself writes. Nothing an upstream can put in a header value or a reason phrase survives
the gate as an `LF`, so the client cannot cut the emitted head anywhere this proxy did
not.

Scope, stated honestly: this is the head `Reactor.serialize` emits (status line, header
block, blank-line separator). The host still stamps its own `Connection:` disposition onto
the result (`http::annotate_connection`) — host marshalling, outside this theorem, and the
same caveat the default path carries. -/
theorem seamGate_out_head_clean (input upstream out : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hfwd : proxyRespGate input upstream = .forward out) :
    noBareLF (proxyRespHead input upstream) = true := by
  have hup : noBareLF (upstreamHeadBlock upstream) = true :=
    seamGate_forward_noBareLF input upstream out hfwd
  obtain ⟨hreason, hhdrs⟩ := proxyBuiltResp_noLF input upstream hgz hup
  have hcrlf : noBareLF Reactor.crlf = true := by decide
  have hsp : noLF ([32] : Bytes) := by decide
  have hstat : noBareLF (Reactor.statusLineOf (proxyBuiltResp input upstream)) = true := by
    refine noLF_noBareLF _ ?_
    unfold Reactor.statusLineOf Reactor.statusLine
    exact noLF_append (noLF_append (noLF_append (noLF_append
      (show noLF Reactor.http11 by decide) hsp)
      (natToDec_noLF (Reactor.build (proxyBuiltResp input upstream)).status)) hsp) hreason
  have hhdr : noBareLF (Reactor.headerBlockOf (proxyBuiltResp input upstream)) = true := by
    unfold Reactor.headerBlockOf
    refine renderHeaders_noBareLF _ ?_
    intro nv hnv
    rw [show Reactor.allHeaders (Reactor.build (proxyBuiltResp input upstream))
        = (proxyBuiltResp input upstream).headers
          ++ [(Reactor.clName,
               Reactor.natToDec (proxyBuiltResp input upstream).body.length)] from rfl,
      List.mem_append] at hnv
    rcases hnv with hnv | hnv
    · exact hhdrs nv hnv
    · rcases List.mem_singleton.mp hnv with rfl
      exact ⟨show noLF Reactor.clName by decide,
             natToDec_noLF (proxyBuiltResp input upstream).body.length⟩
  unfold proxyRespHead
  exact Reactor.ProxyForward.noBareLF_append _ _
    (Reactor.ProxyForward.noBareLF_append _ _
      (Reactor.ProxyForward.noBareLF_append _ _
        (Reactor.ProxyForward.noBareLF_append _ _ hstat hcrlf) hhdr) hcrlf) hcrlf

/-- **★ The client cannot read a field out of our head that we did not put there.** For an
upstream reply the seam gate admitted, the LF-tolerant parse an RFC 9112 §2.2 client may
take of the EMITTED head equals the CRLF-only parse this proxy took of it. The exact
disagreement `seamBareLF_gate_not_vacuous` exhibits on the pre-gate bytes is impossible on
any reply the gate admits. This is the seam analogue of
`Reactor.ProxyForward.respGate_client_parses_agree`. -/
theorem seamGate_client_parses_agree (input upstream out : Bytes)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf input).req = false)
    (hfwd : proxyRespGate input upstream = .forward out) :
    Reactor.ProxyForward.splitLFLines (proxyRespHead input upstream)
      = splitCRLFLines (proxyRespHead input upstream) :=
  Reactor.ProxyForward.splitLFLines_eq_splitCRLFLines _
    (seamGate_out_head_clean input upstream out hgz hfwd)

#print axioms splitCRLFLines_lines_noLF
#print axioms parseUpstream_noLF
#print axioms proxyBuiltResp_headers
#print axioms proxyBuiltResp_noLF
#print axioms renderHeaders_noBareLF
#print axioms seamGate_out_head_clean
#print axioms seamGate_client_parses_agree

end Reactor.ServeStep

/-! ## ★ The STREAMING head seam is gated too — and cannot bypass the buffered gate

The io_uring reactor does not always reach the buffered resume: for a fixed-`Content-Length`
non-gzip reply it takes the native passthrough-streaming path, crossing
`drorb_serve_proxy_stream_head` (`proxyStreamHead`) and emitting the transformed head the
moment the upstream head completes. Measured on the shipped reactor (2026-07-25, this lane):
gating only `serveStep`'s continuation left `PROXY_SEAM=1 PROXY_IO=uring` STILL leaking,
because the resume never ran.

The streaming seam already has a host-visible refusal surface — the host reads an EMPTY reply
as "this reply does not stream; fall back to the buffered `drorb_serve_resume` path" (it is
how the gzip case is declined). The gate reuses exactly that surface, so no host code changes
and the two paths cannot disagree: a refused head streams nothing and lands on the buffered
resume, which refuses it. -/

namespace Reactor.ServeStep

open Proto (Bytes)
open Body.FrameRaw (noBareLF)

/-- **The gated CL-trust streaming head.** An upstream head with ambiguous line terminators
(RFC 9112 §2.2) streams NOTHING — the host falls back to the buffered path, which answers
`502`. `upHead` here is the raw upstream reply THROUGH its terminal `CRLFCRLF`, which is what
the host hands the seam. -/
def proxyStreamHeadGated (req upHead : Bytes) (bodyLen : Nat) : Bytes :=
  if noBareLF upHead then proxyStreamHead req upHead bodyLen else []

/-- The gate refuses to stream a bare-LF upstream head. -/
theorem proxyStreamHeadGated_bareLF_empty (req upHead : Bytes) (bodyLen : Nat)
    (h : noBareLF upHead = false) : proxyStreamHeadGated req upHead bodyLen = [] := by
  simp [proxyStreamHeadGated, h]

/-- **No regression.** On a clean upstream head the streamed head is byte-identical to the
pre-gate one, so `proxyStream_bytes_faithful` applies unchanged. -/
theorem proxyStreamHeadGated_clean (req upHead : Bytes) (bodyLen : Nat)
    (h : noBareLF upHead = true) :
    proxyStreamHeadGated req upHead bodyLen = proxyStreamHead req upHead bodyLen := by
  simp [proxyStreamHeadGated, h]

/-- **★ THE TWO PATHS CANNOT DISAGREE.** For an upstream head `pre ++ CRLFCRLF` the streaming
seam refuses, the buffered resume the host falls back to ALSO refuses, and answers `502 Bad
Gateway`. A bare LF in `pre ++ CRLFCRLF` is a bare LF in `pre` (appending a `CRLFCRLF` cannot
create or destroy one), and `pre` is exactly the block `proxyRespGate` decides on. So the
streaming path is not a way around the buffered gate, and the fallback is not a way around
the streaming gate. -/
theorem streamGate_falls_back_to_reject (input pre body : Bytes) (bodyLen : Nat)
    (hbare : noBareLF (pre ++ [13,10,13,10]) = false)
    (hclean : splitHeadBody (pre ++ [13,10,13,10]) = (pre, [])) :
    proxyStreamHeadGated input (pre ++ [13,10,13,10]) bodyLen = []
    ∧ proxyRespTransformGated input (pre ++ [13,10,13,10] ++ body) = gatewayError false := by
  have hpre : noBareLF pre = false := by
    cases hc : noBareLF pre with
    | true =>
      exact absurd
        (Reactor.ProxyForward.noBareLF_append pre [13,10,13,10] hc (by decide))
        (by rw [hbare]; exact Bool.false_ne_true)
    | false => rfl
  exact ⟨proxyStreamHeadGated_bareLF_empty _ _ _ hbare,
         proxyStreamGated_rejects input pre body hclean hpre⟩

/-- **★ Non-vacuity for the streaming gate.** The crafted upstream head the live probe
served — the pre-gate streaming path computed and EMITTED a transformed head for it — now
streams nothing. -/
theorem seamBareLF_stream_refused (req : Bytes) (bodyLen : Nat) :
    proxyStreamHeadGated req (Reactor.ProxyForward.bareLFRespHead ++ [13,10,13,10]) bodyLen = []
    ∧ proxyStreamHead req (Reactor.ProxyForward.bareLFRespHead ++ [13,10,13,10]) bodyLen ≠ [] := by
  refine ⟨proxyStreamHeadGated_bareLF_empty _ _ _ (by decide), ?_⟩
  intro hc
  have : (Reactor.statusLineOf
      (proxyBuiltResp req (Reactor.ProxyForward.bareLFRespHead ++ [13,10,13,10]))).length
      + 1 ≤ (proxyStreamHead req
          (Reactor.ProxyForward.bareLFRespHead ++ [13,10,13,10]) bodyLen).length := by
    unfold proxyStreamHead
    simp [Reactor.crlf, List.length_append]
  rw [hc] at this
  simp at this

#print axioms proxyStreamHeadGated_bareLF_empty
#print axioms proxyStreamHeadGated_clean
#print axioms streamGate_falls_back_to_reject
#print axioms seamBareLF_stream_refused

end Reactor.ServeStep
