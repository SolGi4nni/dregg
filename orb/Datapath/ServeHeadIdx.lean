import Datapath.HeadIdx
import Reactor.Stage.ProxyProtocol

/-!
# Datapath.ServeHeadIdx — the serve with the WHOLE HEAD read index-native

`Datapath.ServeDenseIdx.serveDenseIdx` (the current dense serve) decides its two
dense arms off `parseIndexNative` — but each guard call exits the parse through
`Reactor.Config.arenaToProto`, which MATERIALIZES the whole head as `List`s
(method, target, version, every header name/value — `protoReqOf`), plus the
keep-alive fold. And the two guards each parse: a `/health` request pays the parse
AND the head materialization TWICE; every request pays the materialization at
least once just to be routed.

`serveHeadIdx` removes both:

* ONE parse per request (`parseArr` off the borrowed window — the arena head of
  spans), shared by both arm decisions;
* NO `arenaToProto`/`protoReqOf` on the deciding path at all: the arms are decided
  directly on the arena head by `Datapath.HeadIdx.bulkIdxB`/`healthIdxB` — header
  names compared by index probes (never consed), header values and the target
  resolved on demand only where a predicate genuinely reads bytes;
* the arm bodies are the PROVEN dense emitters of `ServeDenseIdx`
  (`denseHeadBytesIdx`/`healthHeadBytesIdx` + the dense bodies), unchanged.

Off both arms (and on the h2c preface) it is the deployed serve verbatim — the
deployed `List` pipeline still re-parses there (`servePipelineFull2`), which is the
standing off-arm residual, not this module's scope.

`serveHeadIdx_refines` proves byte-identity to
`Datapath.ServeFlatFull.deployedServeRef` (= `Dataplane.drorbServe`) for EVERY
input, through decision-equality with `serveDenseIdx` (`bulkIdxB_eq`/`healthIdxB_eq`
give the SAME arm decisions, so this is not a sound-but-narrower guard) and the
proven `serveDenseIdx_refines`.
-/

namespace Datapath.ServeHeadIdx

open Proto (Bytes)
open Reactor.Deploy
open Reactor.Config (protoReqOf arenaToProto)
open Datapath.SpanBytes (full full_wf parseArr spanArr parseIndexNative)
open Datapath.ServeDenseIdx (hasH2PrefaceB hasH2PrefaceB_eq denseArmB healthArmB
  denseHeadBytesIdx healthHeadBytesIdx healthBodyDense serveDenseIdx
  serveDenseIdx_refines ReqArm ReqArmHealth)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.HeadIdx (bulkIdxB healthIdxB bulkIdxB_eq healthIdxB_eq)

/-! ## 1. The single index-native head read, and both arm decisions on it -/

/-- The in-budget gate the dense guards share: non-empty, within the deployed
head budget — O(1) field reads. -/
def gateB (input : ByteArray) : Bool :=
  decide (0 < input.size) && decide (¬ input.size > deployConfig.maxHeaderBytes)

/-- **The `/bulk` guard through the shared head view** — the arena parse exits
into `bulkIdxB` (index-native conjuncts), never into `arenaToProto`. -/
def bulkArmOf : Arena.Parse.Outcome → Bool
  | .complete areq => bulkIdxB areq
  | _ => false

/-- **The `/health` guard through the shared head view.** -/
def healthArmOf : Arena.Parse.Outcome → Bool
  | .complete areq => healthIdxB areq
  | _ => false

/-- The deployed `/bulk` guard IS the index-native decision on the arena head:
`denseArmB` (which materializes the head through `arenaToProto` to decide) equals
the gate + `bulkArmOf` on the SAME parse — via `bulkIdxB_eq` (decision equality,
both directions). -/
theorem denseArmB_headIdx (input : ByteArray) :
    denseArmB input = (gateB input && bulkArmOf (parseArr (spanArr (full input)))) := by
  unfold Datapath.ServeDenseIdx.denseArmB gateB bulkArmOf
  show (decide (0 < input.size) && decide (¬ input.size > deployConfig.maxHeaderBytes)
      && (match arenaToProto (parseArr (spanArr (full input))) with
          | .request _ req _ => decide (ReqArm req)
          | _ => false)) = _
  cases parseArr (spanArr (full input)) with
  | complete areq =>
    show (_ && decide (ReqArm (protoReqOf areq))) = (_ && bulkIdxB areq)
    rw [bulkIdxB_eq]
  | incomplete => rfl
  | error e d => rfl

/-- The deployed `/health` guard IS the index-native decision on the arena head. -/
theorem healthArmB_headIdx (input : ByteArray) :
    healthArmB input = (gateB input && healthArmOf (parseArr (spanArr (full input)))) := by
  unfold Datapath.ServeDenseIdx.healthArmB gateB healthArmOf
  show (decide (0 < input.size) && decide (¬ input.size > deployConfig.maxHeaderBytes)
      && (match arenaToProto (parseArr (spanArr (full input))) with
          | .request _ req _ => decide (ReqArmHealth req)
          | _ => false)) = _
  cases parseArr (spanArr (full input)) with
  | complete areq =>
    show (_ && decide (ReqArmHealth (protoReqOf areq))) = (_ && healthIdxB areq)
    rw [healthIdxB_eq]
  | incomplete => rfl
  | error e d => rfl

/-! ## 2. THE SERVE — one head read, both arms decided on it, no head-list -/

/-- **The index-native-head serve.** The h2c fork by index probes; then ONE
index-native head parse (`parseArr` — spans into the flat window, no
`arenaToProto`, no `protoReqOf`), off which BOTH dense arms are decided
(`bulkIdxB`/`healthIdxB` — names probed, values/target resolved only on demand).
The `/bulk` arm emits the proven dense head + dense 1 MiB body, the `/health` arm
the dense head + constant body; everything else is the deployed serve verbatim. -/
@[export drorb_serve_head_idx]
def serveHeadIdx (input : ByteArray) : ByteArray :=
  if hasH2PrefaceB input then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else if gateB input then
    match parseArr (spanArr (full input)) with
    | .complete areq =>
        if bulkIdxB areq then
          ByteArray.mk (denseHeadBytesIdx input).toArray ++ bulkBodyDense
        else if healthIdxB areq then
          ByteArray.mk (healthHeadBytesIdx input).toArray ++ healthBodyDense
        else
          ByteArray.mk (servePipelineFull2 input.toList).toArray
    | _ => ByteArray.mk (servePipelineFull2 input.toList).toArray
  else
    ByteArray.mk (servePipelineFull2 input.toList).toArray

/-- The single-parse serve takes exactly the branches the double-parse
`serveDenseIdx` takes — decision equality, arm by arm. -/
theorem serveHeadIdx_eq_denseIdx (input : ByteArray) :
    serveHeadIdx input = serveDenseIdx input := by
  unfold serveHeadIdx Datapath.ServeDenseIdx.serveDenseIdx
  by_cases h2 : hasH2PrefaceB input
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2, denseArmB_headIdx, healthArmB_headIdx]
    cases hg : gateB input with
    | false =>
      rw [Bool.false_and, Bool.false_and, if_neg Bool.false_ne_true,
        if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    | true =>
      rw [Bool.true_and, Bool.true_and, if_pos rfl]
      cases hp : parseArr (spanArr (full input)) with
      | complete areq =>
        show (if bulkIdxB areq then
                ByteArray.mk (denseHeadBytesIdx input).toArray ++ bulkBodyDense
              else if healthIdxB areq then
                ByteArray.mk (healthHeadBytesIdx input).toArray ++ healthBodyDense
              else ByteArray.mk (servePipelineFull2 input.toList).toArray) = _
        rw [show bulkArmOf (Arena.Parse.Outcome.complete areq) = bulkIdxB areq from rfl,
          show healthArmOf (Arena.Parse.Outcome.complete areq) = healthIdxB areq from rfl]
      | incomplete =>
        show ByteArray.mk (servePipelineFull2 input.toList).toArray = _
        rw [show bulkArmOf Arena.Parse.Outcome.incomplete = false from rfl,
          show healthArmOf Arena.Parse.Outcome.incomplete = false from rfl,
          if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      | error e d =>
        show ByteArray.mk (servePipelineFull2 input.toList).toArray = _
        rw [show bulkArmOf (Arena.Parse.Outcome.error e d) = false from rfl,
          show healthArmOf (Arena.Parse.Outcome.error e d) = false from rfl,
          if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]

/-- **THE BYTE-IDENTITY.** For EVERY input, the index-native-head serve produces
the IDENTICAL bytes to the deployed serve
(`Datapath.ServeFlatFull.deployedServeRef` = `Dataplane.drorbServe`): decision
equality to `serveDenseIdx` + the proven `serveDenseIdx_refines`. -/
theorem serveHeadIdx_refines (input : ByteArray) :
    serveHeadIdx input = Datapath.ServeFlatFull.deployedServeRef input := by
  rw [serveHeadIdx_eq_denseIdx]
  exact serveDenseIdx_refines input

/-! ## 3. Non-vacuity — the arms fire (and refuse) on the real requests,
byte-identical to the deployed serve on every shape: on-arm, HEAD, conditional,
off-arm, h2c, malformed. -/

open Datapath.ServeDenseReal (bulkDemoReq bulkDemoReqAnyHost)
open Datapath.ServeDenseIdx (bulkGzipReq bulkCorsReq healthReq healthGzipReq)

/-- A HEAD-method `/bulk` request — the deployed route ignores the method, so the
dense arm fires and must still be byte-identical. -/
def bulkHeadReq : ByteArray := "HEAD /bulk HTTP/1.1\r\nHost: localhost\r\n\r\n".toUTF8

/-- A conditional `/health` request (`If-None-Match`) — the deployed pipeline has
no conditional stage on this route; the extra header must not change the arm or
the bytes. -/
def healthCondReq : ByteArray :=
  "GET /health HTTP/1.1\r\nHost: x\r\nIf-None-Match: \"abc\"\r\n\r\n".toUTF8

/-- An off-arm POST with a body — falls back to the deployed serve verbatim. -/
def echoPostReq : ByteArray :=
  "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello".toUTF8

/-- The redirect-rule target — the deployed redirect arm answers; off both dense
arms. -/
def oldReq : ByteArray := "GET /old HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The guards agree with the deployed double-parse guards on every demo shape.
#guard (gateB bulkDemoReq && bulkArmOf (parseArr (spanArr (full bulkDemoReq))))
        == denseArmB bulkDemoReq
#guard (gateB healthReq && healthArmOf (parseArr (spanArr (full healthReq))))
        == healthArmB healthReq
#guard (gateB bulkGzipReq && bulkArmOf (parseArr (spanArr (full bulkGzipReq))))
        == denseArmB bulkGzipReq
#guard (gateB bulkCorsReq && bulkArmOf (parseArr (spanArr (full bulkCorsReq))))
        == denseArmB bulkCorsReq
-- The serve is byte-identical to the deployed serve on every shape.
#guard (serveHeadIdx bulkDemoReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReq).data.toList
#guard (serveHeadIdx bulkDemoReqAnyHost).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReqAnyHost).data.toList
#guard (serveHeadIdx bulkHeadReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkHeadReq).data.toList
#guard (serveHeadIdx healthReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef healthReq).data.toList
#guard (serveHeadIdx healthCondReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef healthCondReq).data.toList
#guard (serveHeadIdx healthGzipReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef healthGzipReq).data.toList
#guard (serveHeadIdx bulkGzipReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkGzipReq).data.toList
#guard (serveHeadIdx bulkCorsReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkCorsReq).data.toList
#guard (serveHeadIdx echoPostReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef echoPostReq).data.toList
#guard (serveHeadIdx oldReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef oldReq).data.toList
-- The dense arms genuinely fire: 1 MiB bulk body, tiny health body.
#guard (serveHeadIdx bulkDemoReq).size > 1048576
#guard (serveHeadIdx healthReq).size > 2

/-! ## 4. The preamble-free probe — ONE index read, for the stamped dense arms

A connection-preamble header (the client-address recovery format the deployed
`proxyProtoStage` reads) can only begin with `0x50` (`'P'` — the v1 text prefix)
or `0x0D` (CR — the first byte of the v2 binary signature): both deployed
preamble parsers refuse any other first byte outright, before reading further.
So ONE bounds-checked index probe decides "no preamble here", and a dense arm
guarded by it may use `recoverClient input.toList = none` (`noPreambleB_sound`)
— the PROXY stage is then a proven pass-through on BOTH phases — without ever
materializing the input to scan it. This is the guard extension the stamped
dense `/bulk` arm (`Datapath.DenseStamps`) needs: the nine-edge fold's only
input-reading stage is discharged by the probe, so the whole edge-stamp chain
becomes a pure function of the response head. -/

/-- The first byte of the input (`0` when empty) — one bounds-checked read. -/
def headByteB (input : ByteArray) : UInt8 :=
  if h : 0 < input.size then input[0] else 0

/-- **The preamble-free probe**: non-empty, and the first byte is neither `'P'`
(v1 text) nor CR (v2 binary) — O(1) field reads, no `toList`. -/
def noPreambleB (input : ByteArray) : Bool :=
  decide (0 < input.size) && !(headByteB input == 0x50) && !(headByteB input == 0x0D)

/-- A non-empty input reads back as its probed head byte consed on a tail. -/
theorem headByteB_cons (input : ByteArray) (h : 0 < input.size) :
    ∃ t, input.toList = headByteB input :: t := by
  have hlen : 0 < input.toList.length := by
    rw [Reactor.ServeConformant.ba_toList_length]; exact h
  cases hl : input.toList with
  | nil => rw [hl] at hlen; exact absurd hlen (by simp)
  | cons a t =>
    refine ⟨t, ?_⟩
    have hd : input.data.toList = a :: t := by
      rw [← Reactor.ServeConformant.ba_toList_eq]; exact hl
    have ha : a = input.data[0]'h := by
      have h0 : input.data.toList[0]? = input.data[0]? := Array.getElem?_toList
      rw [hd, Array.getElem?_eq_getElem h, List.getElem?_cons_zero] at h0
      exact Option.some.inj h0
    congr 1
    unfold headByteB
    rw [dif_pos h]
    exact ha

/-- The v1 text parser never completes on a line whose first byte is not `'P'`,
and the v2 binary parser never completes when it is not CR — so the deployed
client recovery yields nothing (list level). -/
theorem recoverClient_cons_none (b : UInt8) (t : List UInt8)
    (hP : (b == 0x50) = false) (hCR : (b == 0x0D) = false) :
    Reactor.Stage.ProxyProtocol.recoverClient (b :: t) = none := by
  have hbP : b ≠ 0x50 := by
    intro he; rw [he] at hP; simp at hP
  have hbCR : b ≠ 0x0D := by
    intro he; rw [he] at hCR; simp at hCR
  have h50b : ((0x50 : UInt8) == b) = false := by
    cases hbe : ((0x50 : UInt8) == b) with
    | false => rfl
    | true => exact absurd (eq_of_beq hbe).symm hbP
  have hCRb : ((0x0D : UInt8) == b) = false := by
    cases hbe : ((0x0D : UInt8) == b) with
    | false => rfl
    | true => exact absurd (eq_of_beq hbe).symm hbCR
  -- v1: first byte is not `'P'` → `.invalid` (mismatched prefix, never a prefix
  -- of the incomplete-detection window either).
  have h1 : Proxy.ProxyProtocol.parseV1 (b :: t)
      = .invalid .invalidV1Format := by
    unfold Proxy.ProxyProtocol.parseV1
    have hne : (b :: t).take 6 ≠ Proxy.ProxyProtocol.v1Prefix := by
      intro he
      rw [show (b :: t).take 6 = b :: t.take 5 from rfl,
          show Proxy.ProxyProtocol.v1Prefix
            = 0x50 :: [0x52, 0x4F, 0x58, 0x59, 0x20] from rfl] at he
      exact hbP (List.cons.injEq .. ▸ he).1
    rw [if_pos hne]
    have hpre : (Proxy.ProxyProtocol.v1Prefix.take (b :: t).length == (b :: t)) = false := by
      show (Proxy.ProxyProtocol.v1Prefix.take (t.length + 1) == (b :: t)) = false
      rw [show Proxy.ProxyProtocol.v1Prefix.take (t.length + 1)
            = 0x50 :: [0x52, 0x4F, 0x58, 0x59, 0x20].take t.length from rfl,
          show ((0x50 :: [0x52, 0x4F, 0x58, 0x59, 0x20].take t.length : List UInt8)
              == (b :: t))
            = (((0x50 : UInt8) == b) && ([0x52, 0x4F, 0x58, 0x59, 0x20].take t.length == t))
            from rfl,
          h50b, Bool.false_and]
    rw [if_neg (by rw [hpre]; exact Bool.false_ne_true)]
  -- v2: first byte is not CR → `.invalid` on both the short and the long branch.
  have h2 : Proxy.ProxyProtocol.parseV2 (b :: t)
      = .invalid .invalidV2Signature := by
    unfold Proxy.ProxyProtocol.parseV2
    by_cases hlen : (b :: t).length < 16
    · rw [if_pos hlen]
      have hk : (Proxy.ProxyProtocol.v2Signature.take (min (b :: t).length 12)
          == (b :: t).take (min (b :: t).length 12)) = false := by
        have hmin : min (b :: t).length 12 = min t.length 11 + 1 := by
          show min (t.length + 1) 12 = min t.length 11 + 1
          omega
        rw [hmin,
            show Proxy.ProxyProtocol.v2Signature.take (min t.length 11 + 1)
              = 0x0D :: [0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54,
                  0x0A].take (min t.length 11) from rfl,
            show (b :: t).take (min t.length 11 + 1)
              = b :: t.take (min t.length 11) from rfl,
            show ((0x0D :: [0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54,
                  0x0A].take (min t.length 11) : List UInt8)
                == (b :: t.take (min t.length 11)))
              = (((0x0D : UInt8) == b)
                  && ([0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54,
                      0x0A].take (min t.length 11) == t.take (min t.length 11)))
              from rfl,
            hCRb, Bool.false_and]
      rw [if_neg (by rw [hk]; exact Bool.false_ne_true)]
    · rw [if_neg hlen]
      have hne : (b :: t).take 12 ≠ Proxy.ProxyProtocol.v2Signature := by
        intro he
        rw [show (b :: t).take 12 = b :: t.take 11 from rfl,
            show Proxy.ProxyProtocol.v2Signature
              = 0x0D :: [0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54,
                  0x0A] from rfl] at he
        exact hbCR (List.cons.injEq .. ▸ he).1
      rw [if_pos hne]
  have hph : Reactor.Stage.ProxyProtocol.parseHeader (b :: t) = none := by
    unfold Reactor.Stage.ProxyProtocol.parseHeader
    rw [h1, h2]
  unfold Reactor.Stage.ProxyProtocol.recoverClient
  rw [hph]

/-- **Probe soundness.** A passing probe means the deployed preamble recovery
yields nothing — so a stage keyed on `recoverClient` is a pass-through, decided
by ONE index read. -/
theorem noPreambleB_sound (input : ByteArray) (h : noPreambleB input = true) :
    Reactor.Stage.ProxyProtocol.recoverClient input.toList = none := by
  unfold noPreambleB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hpos, hp50⟩, hp0D⟩ := h
  obtain ⟨t, hl⟩ := headByteB_cons input (of_decide_eq_true hpos)
  rw [hl]
  exact recoverClient_cons_none _ t
    (by cases hbe : (headByteB input == 0x50) with
        | false => rfl
        | true => rw [hbe] at hp50; simp at hp50)
    (by cases hbe : (headByteB input == 0x0D) with
        | false => rfl
        | true => rw [hbe] at hp0D; simp at hp0D)

-- The probe fires on the real dense-arm requests and refuses both preamble forms.
#guard noPreambleB bulkDemoReq
#guard noPreambleB bulkDemoReqAnyHost
#guard noPreambleB healthReq
#guard !(noPreambleB ("PROXY TCP4 192.168.1.1 10.0.0.1 12345 80\r\n".toUTF8))
#guard !(noPreambleB (ByteArray.mk #[0x0D, 0x0A, 0x0D, 0x0A, 0x00]))
#guard !(noPreambleB (ByteArray.mk #[]))

/-! ## 5. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denseArmB_headIdx
#print axioms healthArmB_headIdx
#print axioms serveHeadIdx_eq_denseIdx
#print axioms serveHeadIdx_refines
#print axioms noPreambleB_sound

end Datapath.ServeHeadIdx
