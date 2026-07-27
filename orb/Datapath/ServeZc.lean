import Datapath.ServeConformantFast

/-!
# Datapath.ServeZc — the zero-copy-body split of the fused conformant serve

`serveConformantFastIdx` (`DRORB_SPAN=22`) reduced the wrapper to ONE body attach,
but a `GET /bulk` hit still moves the 1 MiB body three times in userspace: the
inner dense serve's `head ++ body` append, the fused wrapper's `copySlice` body
attach, and the host's copy of the returned `ByteArray` into its send buffer.
All three are avoidable: the body is a CONSTANT (`bulkBodyDense`), so the host
can keep one process-lifetime copy and gather-write `head` + that static buffer
to the socket — the body then never crosses the seam and is never copied again.

This module supplies the seam for that split (`DRORB_SPAN=23`):

* `serveConformantZcIdx` (`@[export drorb_serve_conformant_zc]`) returns a
  1-byte-TAGGED response: `0x01 :: head` when the fast `/bulk` arm fires (the
  head already carries the fused `Date`-splice + `x-corr`-scrub; the host
  appends the static body by reference), else `0x00 :: full` where `full` is
  byte-for-byte `serveConformantFastIdx input`.
* `bulkBodyForHost` (`@[export drorb_bulk_body]`) hands the host the constant
  body ONCE at boot for its process-static buffer.

## Honest scope

The split-arm decision mirrors `conformantServeFast`'s control flow gate for
gate (head-size 431 gate, parse, validation, framing, target rewrite,
conditional-request, `HEAD`-strip, h2c fork, dense-arm probe); the head-only
fast branch additionally requires the standard head shape the fused wrapper's
own fast branch requires (a CRLF inside the blank scan, and the head's blank
scan consuming exactly the whole head — every serialized response head does).
Reassembly identity `untag(zc) [++ bulkBodyDense] = serveConformantFastIdx` is
pinned by the `#guard` battery below (the real 1 MiB `/bulk` arm, off-arm,
`HEAD`, reject, conditional, unparsable), same discipline as `=22`'s fusion
guards; the general theorem rides the same named next rung as the `=22` fusion
proof. `DRORB_SPAN=20` remains the proven conformant-dense serve.
-/

namespace Datapath.ServeZc

open Datapath.ServeConformantFast
open Reactor.ServeConformant
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation (validationStage)
open Reactor.Stage.StrictValidation (strictStage)
open Reactor.Stage.FramingValidation (framingValidationStage)
open Reactor.Stage.RequestHeadLimit (headGate)
open Datapath.ServeDenseIdx (hasH2PrefaceB denseArmB denseHeadBytesIdx prefixAtB)
open Datapath.ServeDenseFullReal (bulkBodyDense)

/-- The constant `/bulk` body, exported so the host can materialize its
process-static send buffer ONCE at boot. The argument is ignored (uniform
`ByteArray -> ByteArray` marshalling). -/
@[export drorb_bulk_body]
def bulkBodyForHost (_ : ByteArray) : ByteArray := bulkBodyDense

/-- The request-line opener every dense-arm request carries (`GET /bulk`): the
one-probe-per-byte prefilter that lets every other request decline in ≤9 index
probes. -/
def bulkProbe : List UInt8 := "GET /bulk".toUTF8.toList

/-- The fused response HEAD of the fast `/bulk` arm, when EVERY gate of
`conformantServeFast`'s accepted non-conditional dense-arm path fires — the
exact bytes `serveConformantFastIdx` would put before the constant body. `none`
whenever any gate declines; the caller then serves the full fused response. -/
def zcBulkHead (input : ByteArray) : Option ByteArray :=
  -- Cheapest first: one ≤9-byte index probe filters the whole off-arm world. The
  -- dense arm requires method `GET` and target `/bulk`, so a request line that
  -- does not open `GET /bulk` can never fire it (a necessary condition only — a
  -- false negative just serves the byte-identical full path). Off-arm requests
  -- decline here without the index head parse `denseArmB` runs, and without ever
  -- touching the List-based gates below.
  if !prefixAtB (Datapath.SpanBytes.full input) bulkProbe 0 then none
  else if hasH2PrefaceB input then none
  else if !denseArmB input then none
  else if (headGate input).isSome then none
  else if isHeadReq input then none
  else
    match Proto.RequestSerialize.parse (reqBytes input) with
    | none => none
    | some req =>
      if hasConditional req then none
      else
        match strictStage.onRequest (mkCtx input req) with
        | .respond _ => none
        | .continue c' =>
          match framingValidationStage.onRequest c' with
          | .respond _ => none
          | .continue c'' =>
            -- Only the unrewritten-target path serves the borrowed input.
            if c''.req.target == req.target then
              -- The dense arm: full response = scrubDateBA (head ++ body).
              -- Both wrapper transforms rewrite only the head; take the fused
              -- fast branch head-only, requiring the head shape it requires.
              let headL := denseHeadBytesIdx input
              let head := ByteArray.mk headL.toArray
              let blank := blankTakeFrom head 0
              if crIdxFrom head 0 + 2 ≤ blank then
                if blank == head.size then
                  some (ByteArray.mk (scrubLines (injectDate headL)).toArray)
                else none
              else none
            else none

/-- **The exported tagged zero-copy-split serve** (`DRORB_SPAN=23`):
`0x01 :: fused head` on the fast `/bulk` arm (the host attaches the static
constant body by reference), `0x00 :: serveConformantFastIdx input` everywhere
else. -/
@[export drorb_serve_conformant_zc]
def serveConformantZcIdx (input : ByteArray) : ByteArray :=
  match zcBulkHead input with
  | some head => ByteArray.mk #[1] ++ head
  | none => ByteArray.mk #[0] ++ serveConformantFastIdx input

/-- Undo the tagging exactly as the host does: strip the tag byte; a `0x01` tag
means the constant body follows the head. The reassembly the guards pin. -/
def reassemble (tagged : ByteArray) : ByteArray :=
  if tagged.size == 0 then tagged
  else if tagged.get! 0 == 1 then
    tagged.extract 1 tagged.size ++ bulkBodyDense
  else
    tagged.extract 1 tagged.size

/-! ## The split arm declines off `/bulk` — and the `=22` bytes come back verbatim

The module's `#guard` battery pins the reassembly on a fixed request battery.
What it did NOT state is the GENERAL fact every other span asserts about itself:
that off its own fast arm this span is byte-for-byte the serve it claims to
twin. Without it, a control-flow arm added to `conformantServeFast` (the ACME
HTTP-01 route was exactly such an arm, and its absence from the fused twin was a
live certificate-renewal outage on `DRORB_SPAN=22`) could be lost here with no
build-time signal. These theorems supply it: the `/bulk` prefilter is the FIRST
gate, so any request whose line does not open `GET /bulk` takes the `0x00` arm
and carries `serveConformantFastIdx`'s bytes unchanged — whatever arms that
serve grows. -/

/-- The `/bulk` request-line prefilter computes the deployed `List` prefix test
on the request bytes — the `List` appears only on the spec side. -/
theorem bulkProbeB_eq (input : ByteArray) :
    prefixAtB (Datapath.SpanBytes.full input) bulkProbe 0
      = List.isPrefixOf bulkProbe input.toList := by
  rw [Datapath.ServeDenseIdx.prefixAtB_eq, List.drop_zero,
    Datapath.SpanBytes.read_eq_denote _ (Datapath.SpanBytes.full_wf _),
    Datapath.SpanBytes.denote_full, ← Reactor.ServeConformant.ba_toList_eq]

/-- **The split arm cannot fire off `GET /bulk`.** The cheapest gate is first, so
a request line that does not open `GET /bulk` declines in ≤9 index probes. An
ACME HTTP-01 fetch opens `GET /.well-known/`, so it always declines here. -/
theorem zcBulkHead_none_of_not_bulk (input : ByteArray)
    (h : List.isPrefixOf bulkProbe input.toList = false) :
    zcBulkHead input = none := by
  unfold zcBulkHead
  rw [bulkProbeB_eq, h]
  rfl

/-- **THE MISSING EQUALITY: off `/bulk`, `=23` IS `=22`.** For every request whose
line does not open `GET /bulk`, the tagged split serve emits the `0x00` tag
followed by exactly `serveConformantFastIdx input` — the bytes the host serves
after stripping the tag (`serve_zc_into` in `crates/dataplane/src/serve.rs`). So
every arm of the fused conformant serve (RFC gate, `Date` finisher, `HEAD` strip,
and the ACME HTTP-01 challenge route) reaches the wire through this span, and a
future arm cannot be silently dropped here. -/
theorem serveConformantZcIdx_eq_fast_of_not_bulk (input : ByteArray)
    (h : List.isPrefixOf bulkProbe input.toList = false) :
    serveConformantZcIdx input = ByteArray.mk #[0] ++ serveConformantFastIdx input := by
  unfold serveConformantZcIdx
  rw [zcBulkHead_none_of_not_bulk input h]

/-! ## Byte-identity guards — reassembled zc serve = the fused serve (`=22`)

Same request battery as the `=22` fusion guards: the REAL 1 MiB `/bulk` arm
(and that the split arm actually FIRES on it), off-arm `/health`, `HEAD` strip,
reject (missing `Host`), conditional, unparsable. -/

open Datapath.ServeDenseReal (bulkDemoReqAnyHost)
open Datapath.ServeDenseIdx (healthReq)

private def headBulkReq : ByteArray := "HEAD /bulk HTTP/1.1\r\nHost: example.net\r\n\r\n".toUTF8
private def noHostReq : ByteArray := "GET /bulk HTTP/1.1\r\n\r\n".toUTF8
private def condReq : ByteArray :=
  "GET /bulk HTTP/1.1\r\nHost: example.net\r\nIf-None-Match: \"abc\"\r\n\r\n".toUTF8
private def garbageReq : ByteArray := "garbage".toUTF8

-- The split arm fires on the real `/bulk` request, and reassembles to `=22`.
#guard (serveConformantZcIdx bulkDemoReqAnyHost).get! 0 == 1
#guard (reassemble (serveConformantZcIdx bulkDemoReqAnyHost)).data.toList
        == (serveConformantFastIdx bulkDemoReqAnyHost).data.toList
-- Off-arm, HEAD-strip, reject, conditional, unparsable: tag 0, payload = `=22`.
#guard (serveConformantZcIdx healthReq).get! 0 == 0
#guard (reassemble (serveConformantZcIdx healthReq)).data.toList
        == (serveConformantFastIdx healthReq).data.toList
#guard (serveConformantZcIdx headBulkReq).get! 0 == 0
#guard (reassemble (serveConformantZcIdx headBulkReq)).data.toList
        == (serveConformantFastIdx headBulkReq).data.toList
#guard (serveConformantZcIdx noHostReq).get! 0 == 0
#guard (reassemble (serveConformantZcIdx noHostReq)).data.toList
        == (serveConformantFastIdx noHostReq).data.toList
#guard (serveConformantZcIdx condReq).get! 0 == 0
#guard (reassemble (serveConformantZcIdx condReq)).data.toList
        == (serveConformantFastIdx condReq).data.toList
#guard (serveConformantZcIdx garbageReq).get! 0 == 0
#guard (reassemble (serveConformantZcIdx garbageReq)).data.toList
        == (serveConformantFastIdx garbageReq).data.toList
-- The exported body constant is the body the reassembly (and the host) splices.
#guard (bulkBodyForHost ByteArray.empty).data.toList == bulkBodyDense.data.toList

/-! ## The ACME HTTP-01 challenge fetch, driven through this span

A real CA validation fetch declines the `/bulk` prefilter, so by
`serveConformantZcIdx_eq_fast_of_not_bulk` it takes the `0x00` arm and the
payload the host unwraps is exactly `serveConformantFastIdx`'s bytes — the key
authorization, by `Datapath.AcmeSpanAudit.serveConformantZcIdx_servesAcme_off_bulk`.

Honest scope on the guard below: the challenge RESPONSE cannot be `#guard`-ed
here the way the `/bulk` battery above is. `Pki.Acme.keyAuthorization` runs the
REAL `Crypto.sha256`, which is an `@[extern]` to the C shim with no interpreter
symbol, so the elaborator cannot evaluate the served body (`Could not find native
implementation of external declaration 'Crypto.sha256'` — the same reason
`Reactor.Stage.AcmeChallenge` proves `demo_fires` structurally instead of
guarding it). The challenge behaviour on this span is therefore pinned by the
KERNEL theorems above, plus a live `curl` against the running dataplane under
`DRORB_SPAN=23` (see `docs/gateway/ACME-SPAN-AUDIT.md`). What IS guarded here is
the prefilter decision the theorems take as hypothesis. -/

private def acmeChallengeReq : ByteArray :=
  "GET /.well-known/acme-challenge/tok0LmNkMsdN HTTP/1.1\r\nHost: example.test\r\n\r\n".toUTF8

#guard List.isPrefixOf bulkProbe acmeChallengeReq.toList == false

/-! ## Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound} -/

#print axioms bulkProbeB_eq
#print axioms zcBulkHead_none_of_not_bulk
#print axioms serveConformantZcIdx_eq_fast_of_not_bulk

end Datapath.ServeZc
