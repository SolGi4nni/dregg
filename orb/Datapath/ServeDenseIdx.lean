import Datapath.ServeDenseReal
import Datapath.IndexParse
import Reactor.ServeConformant

/-!
# Datapath.ServeDenseIdx — the runtime-dense serve with the ARM DECIDED INDEX-NATIVE

`Datapath.ServeDenseReal.serveDenseReal` (DRORB_SPAN=18) fixed the deployed `/bulk`
body-cliff: on the `BulkArm` it emits the DENSE head + DENSE 1 MiB body. But its arm
DECISION still runs the `List` machinery on every request: the guard evaluates
`BulkArm (ctxOf input.toList)` — a full `input.toList` cons PLUS the whole
`deploySubs` reactor step (`Proto.step` → `h1ParseFn` over the `List`) just to
DECIDE whether the dense arm fires. And the h2c preface fork conses `input.toList`
a second time before a single byte is compared.

This module re-decides both forks INDEX-NATIVELY:

* `hasH2PrefaceB` — the h2c preface check as `getByteOr0` index probes over the
  borrowed window (24 loads against the `h2Preface` literal), proven equal to the
  deployed `Reactor.Ingress.hasH2Preface input.toList`;
* `denseArmB` — the `/bulk`-arm guard decided off `parseIndexNative` (the
  index-native head parse, `Datapath.IndexParse`) + the decidable request-level arm
  `ReqArm`. Soundness (`denseArmB_sound`) is proven through a NEW dispatch bridge
  `deploySubs_dispatch`: a successful in-budget head parse IS the request the
  deployed reactor step dispatches — so the ctx the deployed pipeline folds over
  carries exactly the request the index-native parse produced, and `BulkArm
  (ctxOf input.toList)` holds. The `List`-side parse is never computed to decide.

`serveDenseIdx` then forks on the two index-native decisions and, on the dense arm,
emits the SCALAR-COLLAPSED dense head (`denseHeadBytesIdx`: constant `x-upstream`,
index-native `x-corr` — proven equal to SPAN=18's `denseHeadBytes input.toList` on
the arm) + the SPAN=18 dense body; off-arm and on h2c it is the deployed serve
verbatim. `serveDenseIdx_refines` proves byte-identity to
`Datapath.ServeFlatFull.deployedServeRef` (= `Dataplane.drorbServe`) for EVERY input.

## ★ HONEST SCOPE — what is dense here and what still isn't

* DENSE (new): the h2c preface fork and the WHOLE arm decision (parse by index off
  the borrowed window; the request-level conjuncts decided on the parsed head).
  The deciding path materializes NO `input.toList` and runs NO `deploySubs`.
* DENSE (inherited, SPAN=18): the `/bulk` head fold (`denseHeadersBlock`) and the
  1 MiB body (`bulkBodyDense`, bulk-append).
* DENSE (new, the head-scalar collapse): the dense arm's HEAD SCALARS —
  `x-upstream` is the TOP-LEVEL CONSTANT `uvBulk` (the proxy plans off the first
  dispatch only, the router off the segments only, the LB off neither — `uv_arm`),
  and `x-corr` is `corrValB` (index probes; the O(request) dotted-decimal LIST it
  builds is the response header's own content, not an input view). The dense arm
  no longer calls `deploySubs`, `corrVal`, or `input.toList` at all.
* DENSE (new, §3c — the off-arm widened): the `/health` route is a SECOND dense
  arm — index-decided guard (`healthArmB`), constant `x-upstream` (`uvHealth`),
  index-native `x-corr`, CONSTANT dense body (`healthBodyDense`). Its arm equality
  is proven via a GENERALIZED `builtScalarsGen` (any constant-body admitted route
  whose body the html-rewrite fixes) + the route-generic
  `ServeDenseReal.denseHeadersUnknown` — the kit the remaining routes can reuse.
* STILL `List` (named residuals, NOT fixed here):
  - the parsed `Proto.Request`'s own fields are `List`-typed (O(head) small lists —
    `IndexParse`'s standing residual);
  - the REMAINING off-arm routes (the 404 catch-all, the `a.example`/`b.example`
    vhost bodies, `/static` files, `/cgi-bin`, the glob route, the gated/redirect/
    admin/CORS/gzip answers) and the h2c engine are still the deployed `List`
    serves — each constant-body one is now a `builtScalarsGen` instantiation away,
    but the guard/arm/scalar work is per-route and NOT done here;
  - re-expressing the full 14-stage fold densely for EVERY arm stays the open
    multi-file re-proof `ServePolyFull` names.
-/

namespace Datapath.ServeDenseIdx

open Proto (Bytes)
open Reactor.Pipeline (Ctx)
open Reactor.Deploy
open Datapath.SpanBytes (full full_wf read_eq_denote denote_full length_read
  getByteOr0 getByteOr0_eq_readGetD parseIndexNative parseIndexNative_refines)
open Datapath.ServeDenseReal (BulkArm denseHeadBytes denseArm_eq bulkDemoReq bulkDemoReqAnyHost)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Reactor.ServeConformant (ba_toList_eq ba_toList_length)

/-! ## 1. The index-native h2c preface fork -/

/-- Match the pattern list at index `i` of the span by INDEX probes (`getByteOr0`,
no list materialized). The pattern is the fixed 24-byte `h2Preface` literal — a
top-level constant, consed once at initialization, never per request. -/
def prefixAtB (s : Datapath.SpanBytes) : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: rest, i => decide (i < s.len) && (b == getByteOr0 s i) && prefixAtB s rest (i + 1)

/-- The index probe computes the deployed `List.isPrefixOf` against the read
window suffix — the `List` appears only on the spec side. -/
theorem prefixAtB_eq (s : Datapath.SpanBytes) (l : List UInt8) (i : Nat) :
    prefixAtB s l i = l.isPrefixOf (s.read.drop i) := by
  induction l generalizing i with
  | nil => simp [prefixAtB, List.isPrefixOf]
  | cons b rest ih =>
    by_cases hlt : i < s.len
    · have hi : i < s.read.length := by rw [length_read]; exact hlt
      rw [prefixAtB, ih, List.drop_eq_getElem_cons hi]
      show (decide (i < s.len) && (b == getByteOr0 s i)
              && rest.isPrefixOf (s.read.drop (i + 1)))
          = (b == s.read[i] && rest.isPrefixOf (s.read.drop (i + 1)))
      rw [decide_eq_true hlt, getByteOr0_eq_readGetD,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      show (true && (b == s.read[i]) && _) = _
      rw [Bool.true_and]
    · have hnil : s.read.drop i = [] :=
        List.drop_eq_nil_of_le (by rw [length_read]; omega)
      rw [prefixAtB, hnil]
      show (decide (i < s.len) && _ && _) = ((b :: rest).isPrefixOf [])
      rw [decide_eq_false hlt, Bool.false_and, Bool.false_and]
      rfl

/-- **The index-native h2c preface check** — 24 index probes, no `input.toList`. -/
def hasH2PrefaceB (input : ByteArray) : Bool :=
  prefixAtB (full input) Reactor.Ingress.h2Preface 0

/-- The index-native preface check decides exactly the deployed fork. -/
theorem hasH2PrefaceB_eq (input : ByteArray) :
    hasH2PrefaceB input = Reactor.Ingress.hasH2Preface input.toList := by
  show prefixAtB (full input) Reactor.Ingress.h2Preface 0
      = List.isPrefixOf Reactor.Ingress.h2Preface input.toList
  rw [prefixAtB_eq, List.drop_zero, read_eq_denote _ (full_wf _), denote_full,
    ← ba_toList_eq]

/-! ## 2. The dispatch bridge — a parsed head IS the dispatched request

Every existing deployed-arm proof takes `deploySubs input = .dispatch req :: rest`
as a HYPOTHESIS. This discharges it from the parse: on a non-oversize, non-empty
accumulation whose head parses to `.request n req ka`, the deployed reactor step
(`Proto.step` on the plain-H1 lane, through `finish`/`gate` and the reactor's
`ofOutput`+recycle wrap) emits `.dispatch req` FIRST. -/

/-- The pipelining loop's head output on a successful parse. -/
theorem h1Loop_dispatch (input : Bytes) (n : Nat) (req : Proto.Request) (ka : Bool)
    (hne : input.isEmpty = false)
    (hp : deployConfig.h1Parse input = .request n req ka) :
    ∃ tail, (Proto.h1Loop deployConfig (input.length + 1) input).outs
        = Proto.Output.dispatch req :: tail := by
  rw [Proto.h1Loop, if_neg (by rw [hne]; exact Bool.false_ne_true), hp]
  cases ka with
  | true => exact ⟨_, rfl⟩
  | false => exact ⟨[], rfl⟩

/-- The send-block gate is open on a fresh plain connection: `finish` passes the
effect's outputs through (with the close realized when the effect closes). Stated
over the effect's FIELDS so the caller's rewrites match syntactically. -/
theorem finish_mkPlain_outs (p : Proto.ProtoState) (outs : List Proto.Output)
    (cl : Bool) (tm : Option (List Proto.TimerSlot)) :
    (Proto.finish Proto.Conn.mkPlain
        { proto := p, outs := outs, closeNow := cl, timers := tm }).2
      = if cl then outs ++ [Proto.Output.close] else outs := by
  unfold Proto.finish
  cases cl with
  | true => rfl
  | false => rfl

/-- **The dispatch bridge.** An in-budget, non-empty accumulation whose head parses
to `.request n req ka` is dispatched: the deployed submissions open with
`.dispatch req`. -/
theorem deploySubs_dispatch (input : Bytes) (n : Nat) (req : Proto.Request) (ka : Bool)
    (hlen : ¬ input.length > deployConfig.maxHeaderBytes)
    (hne : input.isEmpty = false)
    (hparse : Reactor.Config.h1ParseFn input = .request n req ka) :
    ∃ rest, deploySubs input = .dispatch req :: rest := by
  have hp : deployConfig.h1Parse input = .request n req ka := by
    rw [deploy_h1_arena]; exact hparse
  -- the reactor step is `finish mkPlain (runH1 …)` on the plain-H1 lane
  have hstep : Proto.step deployConfig (.active .mkPlain) (.bytesReceived input)
      = Proto.finish .mkPlain (Proto.runH1 deployConfig .plainH1 input []) := rfl
  -- runH1 under budget is the pipelining loop's effect
  have hrun : Proto.runH1 deployConfig .plainH1 input []
      = { proto := .plainH1 (Proto.h1Loop deployConfig (input.length + 1) input).residual,
          outs := (Proto.h1Loop deployConfig (input.length + 1) input).outs,
          closeNow := (Proto.h1Loop deployConfig (input.length + 1) input).closing } := by
    unfold Proto.runH1
    rw [if_neg hlen]
    exact rfl
  obtain ⟨tail, hloop⟩ := h1Loop_dispatch input n req ka hne hp
  show ∃ rest,
      ((Proto.step deployConfig (.active .mkPlain) (.bytesReceived input)).2.map
          Reactor.ofOutput ++ [.recycleBuffer 0])
        = .dispatch req :: rest
  rw [hstep, hrun, finish_mkPlain_outs]
  cases hcl : (Proto.h1Loop deployConfig (input.length + 1) input).closing with
  | true =>
    rw [hloop]
    exact ⟨_, rfl⟩
  | false =>
    rw [hloop]
    exact ⟨_, rfl⟩

/-! ## 3. The request-level arm, and the guard decided off the index parse -/

/-- The context a bare request denotes (no raw input, no attrs) — `BulkArm` reads
ONLY the request and the (empty) attrs, so this carries the whole decision. -/
def reqCtx (req : Proto.Request) : Ctx :=
  { input := [], req := req, attrs := [] }

/-- **The request-level `/bulk` arm** — `BulkArm` keyed on the request alone. -/
def ReqArm (req : Proto.Request) : Prop := BulkArm (reqCtx req)

instance (req : Proto.Request) : Decidable (ReqArm req) := by
  unfold ReqArm; infer_instance

/-- `BulkArm` transports along the request: it never reads `Ctx.input`, and both
contexts carry empty attrs. -/
theorem bulkArm_of_reqArm (l : Bytes) (req : Proto.Request)
    (hreq : (ctxOf l).req = req) (h : ReqArm req) : BulkArm (ctxOf l) := by
  have hctx : ctxOf l = { input := l, req := req, attrs := [] } := by
    rw [← hreq]; exact rfl
  rw [hctx]
  exact h

/-- **The index-decided dense-arm guard.** Size gates by `input.size` (O(1) field
reads), the head parse by `parseIndexNative` (index probes off the borrowed
window), the arm conjuncts decided on the parsed request. NO `input.toList`, NO
`deploySubs` on the deciding path. -/
def denseArmB (input : ByteArray) : Bool :=
  decide (0 < input.size)
    && decide (¬ input.size > deployConfig.maxHeaderBytes)
    && (match parseIndexNative (full input) with
        | .request _ req _ => decide (ReqArm req)
        | _ => false)

/-- **Guard soundness.** When the index-decided guard fires, the deployed `/bulk`
arm (`BulkArm` over the deployed `List` ctx) genuinely holds — through the parse
refinement (`parseIndexNative_refines`) and the dispatch bridge
(`deploySubs_dispatch` + `ctxOf_req`). Soundness is the direction byte-identity
needs; the off-guard side falls back to the deployed serve verbatim. -/
theorem denseArmB_sound (input : ByteArray) (h : denseArmB input = true) :
    BulkArm (ctxOf input.toList) := by
  unfold denseArmB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsz, hlen⟩, harm⟩ := h
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  cases hpo : parseIndexNative (full input) with
  | request n req ka =>
    rw [hpo] at harm
    have harm' : ReqArm req := of_decide_eq_true harm
    have hparse : Reactor.Config.h1ParseFn input.toList = .request n req ka := by
      rw [← hread, ← parseIndexNative_refines _ (full_wf _), hpo]
    have hlen' : ¬ input.toList.length > deployConfig.maxHeaderBytes := by
      rw [ba_toList_length]; exact of_decide_eq_true hlen
    have hne : input.toList.isEmpty = false := by
      have hpos : 0 < input.toList.length := by
        rw [ba_toList_length]; exact of_decide_eq_true hsz
      cases hl : input.toList with
      | nil => rw [hl] at hpos; exact absurd hpos (by simp)
      | cons a t => rfl
    obtain ⟨rest, hsub⟩ := deploySubs_dispatch input.toList n req ka hlen' hne hparse
    exact bulkArm_of_reqArm input.toList req (ctxOf_req input.toList req rest hsub) harm'
  | reject n resp => rw [hpo] at harm; exact absurd harm (by simp)
  | incomplete => rw [hpo] at harm; exact absurd harm (by simp)
  | error => rw [hpo] at harm; exact absurd harm (by simp)

/-! ## 3b. The dense HEAD SCALARS — `x-upstream` a constant, `x-corr` index-native

`denseHeadBytes input.toList` computes the two request-derived response scalars over
the `List` machinery: `x-upstream = upstreamVal (deployPlan (deploySubs input))`
(re-running the WHOLE `Proto.step` `List` parse a second time just to plan the
proxy/DNS upstream) and `x-corr = corrVal input` (the request bytes dotted-decimal,
read off `input.toList`). This section removes both `List` views from the dense arm:

* the deployed proxy sits on the reactor's FIRST `dispatch` only
  (`serveProxyOn_dispatch`), the LB ignores the request (`proxyHandle _req`), and the
  router keys only on `targetSegments req.target` — which the arm PINS to `["bulk"]`.
  So on the arm the whole `deploySubs`/`deployPlan` chain collapses to the TOP-LEVEL
  CONSTANT `uvBulk` (`uv_arm`), computed once at initialization, never per request;
* the deployed correlation id is DEFINITIONALLY the request bytes as `Nat`s
  (`demoGen = id`, `demoTrust = false`, nothing carried), so `corrValB` re-reads them
  by INDEX PROBES off the borrowed window (`natsB`) and renders the SAME
  dotted-decimal value (`corrValB_eq`). The O(|request|) value it builds is the
  response header's own CONTENT (inherent output bytes — the deployed response
  genuinely carries the whole request dotted-decimal in `x-corr`); `input.toList`
  itself is never materialized.
-/

/-- A dummy request — the LB ignores its request argument entirely, so any value
serves as the placeholder `routeProxySegs` feeds it. -/
def dummyReq : Proto.Request :=
  { method := [], target := [], version := [], headers := [] }

/-- `routeProxy` keyed directly on the target SEGMENTS: the same route match and
handler dispatch, the (ignored) request argument fixed to the dummy. -/
def routeProxySegs (ac : Reactor.App.AppConfig) (ctx : Proxy.Ctx)
    (segs : List String) : List Reactor.RingSubmission :=
  match Route.Match.bestMatch ac.table segs with
  | some r =>
    match r.handler with
    | Reactor.App.Handler.proxy pool => Reactor.Proxy.proxyHandle pool ctx dummyReq
    | _ => []
  | none => []

/-- The router keys only on the target segments, and the LB ignores the request. -/
theorem routeProxy_eq_segs (ac : Reactor.App.AppConfig) (ctx : Proxy.Ctx)
    (req : Proto.Request) :
    Reactor.ProxyServe.routeProxy ac ctx req
      = routeProxySegs ac ctx (Reactor.App.targetSegments req.target) := by
  cases hbm : Route.Match.bestMatch ac.table (Reactor.App.targetSegments req.target) with
  | none => simp only [Reactor.ProxyServe.routeProxy, routeProxySegs, hbm]
  | some r =>
    cases hh : r.handler <;>
      simp only [Reactor.ProxyServe.routeProxy, routeProxySegs, hbm, hh] <;>
      rfl

/-- **The `/bulk`-arm `x-upstream` value — a top-level constant.** The deployed
plan value of the `["bulk"]` route, computed ONCE at module initialization. -/
def uvBulk : Header.Value :=
  upstreamVal (Reactor.DnsWire.resolveSubs Reactor.DnsWire.demoResolver
    (routeProxySegs Reactor.ProxyServe.demoProxyApp Reactor.Proxy.demoCtx ["bulk"]))

/-- **`x-upstream` collapses to `uvBulk` on the arm.** For a dispatched request whose
target segments are `["bulk"]`, the deployed plan value is the constant: the proxy
reads only the FIRST dispatch, the router only the segments, the LB neither. -/
theorem uv_arm (l : Bytes) (req : Proto.Request) (rest : List Reactor.RingSubmission)
    (hsub : deploySubs l = .dispatch req :: rest)
    (hseg : Reactor.App.targetSegments req.target = ["bulk"]) :
    upstreamVal (deployPlan (deploySubs l)) = uvBulk := by
  rw [hsub]
  unfold Reactor.Deploy.deployPlan
  rw [Reactor.ProxyServe.serveProxyOn_dispatch, routeProxy_eq_segs, hseg]
  rfl

/-- The window bytes from index `i`, as `Nat`s — INDEX PROBES (`getByteOr0`), no
`toList`. -/
def natsB (s : Datapath.SpanBytes) (i : Nat) : List Nat :=
  if h : i < s.len then (getByteOr0 s i).toNat :: natsB s (i + 1) else []
termination_by s.len - i

/-- The index probes read back exactly the window suffix (spec side only). -/
theorem natsB_eq (s : Datapath.SpanBytes) : ∀ i,
    natsB s i = (s.read.drop i).map UInt8.toNat := by
  have key : ∀ k i, s.len ≤ i + k → natsB s i = (s.read.drop i).map UInt8.toNat := by
    intro k
    induction k with
    | zero =>
      intro i hk
      rw [natsB.eq_def, dif_neg (by omega),
        List.drop_eq_nil_of_le (by rw [length_read]; omega)]
      rfl
    | succ k ih =>
      intro i _hk
      rw [natsB.eq_def]
      by_cases h : i < s.len
      · have hi : i < s.read.length := by rw [length_read]; exact h
        rw [dif_pos h, ih (i + 1) (by omega), List.drop_eq_getElem_cons hi,
          List.map_cons, getByteOr0_eq_readGetD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi, Option.getD_some]
      · rw [dif_neg h,
          List.drop_eq_nil_of_le (by rw [length_read]; omega)]
        rfl
  intro i
  exact key s.len i (by omega)

/-- **The index-native `x-corr` value**: the request bytes dotted-decimal, read by
index probes off the borrowed window. The value LIST it builds is the response
header's own content; the input is never `toList`ed. -/
def corrValB (input : ByteArray) : Header.Value :=
  Reactor.Deploy.corrBytes (natsB (full input) 0)

/-- The index-native `x-corr` is the deployed `corrVal` — for EVERY input. (The
deployed trace generator is `id` over the byte seed, nothing carried, untrusted.) -/
theorem corrValB_eq (input : ByteArray) : corrValB input = corrVal input.toList := by
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  unfold corrValB
  rw [natsB_eq, List.drop_zero, hread]
  rfl

/-- A firing guard yields the dispatched request together with its arm conjuncts —
the same bridge `denseArmB_sound` crosses, surfaced for the head-scalar collapse. -/
theorem denseArmB_dispatch (input : ByteArray) (h : denseArmB input = true) :
    ∃ req rest, deploySubs input.toList = .dispatch req :: rest ∧ ReqArm req := by
  unfold denseArmB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsz, hlen⟩, harm⟩ := h
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  cases hpo : parseIndexNative (full input) with
  | request n req ka =>
    rw [hpo] at harm
    have harm' : ReqArm req := of_decide_eq_true harm
    have hparse : Reactor.Config.h1ParseFn input.toList = .request n req ka := by
      rw [← hread, ← parseIndexNative_refines _ (full_wf _), hpo]
    have hlen' : ¬ input.toList.length > deployConfig.maxHeaderBytes := by
      rw [ba_toList_length]; exact of_decide_eq_true hlen
    have hne : input.toList.isEmpty = false := by
      have hpos : 0 < input.toList.length := by
        rw [ba_toList_length]; exact of_decide_eq_true hsz
      cases hl : input.toList with
      | nil => rw [hl] at hpos; exact absurd hpos (by simp)
      | cons a t => rfl
    obtain ⟨rest, hsub⟩ := deploySubs_dispatch input.toList n req ka hlen' hne hparse
    exact ⟨req, rest, hsub, harm'⟩
  | reject n resp => rw [hpo] at harm; exact absurd harm (by simp)
  | incomplete => rw [hpo] at harm; exact absurd harm (by simp)
  | error => rw [hpo] at harm; exact absurd harm (by simp)

/-- **The dense `/bulk` head bytes with NO `input.toList`**: constant `x-upstream`
(`uvBulk`), index-native `x-corr` (`corrValB`), the proven flat header fold. -/
def denseHeadBytesIdx (input : ByteArray) : Bytes :=
  Datapath.DenseHead.renderHead 200 (Reactor.App.reasonFor 200)
    (Datapath.DenseHead.denseHeadersBlock [] uvBulk (corrValB input)).denote
    Reactor.App.bulkSize

/-- On a firing guard the index-native head IS the deployed dense head — the
scalar collapse (`uv_arm` + `corrValB_eq`) under the dispatch bridge. -/
theorem denseHeadBytesIdx_eq (input : ByteArray) (h : denseArmB input = true) :
    denseHeadBytesIdx input = denseHeadBytes input.toList := by
  obtain ⟨req, rest, hsub, harm⟩ := denseArmB_dispatch input h
  obtain ⟨_, _, _, _, _, _, _, _, hseg, _, _⟩ := harm
  unfold denseHeadBytesIdx Datapath.ServeDenseReal.denseHeadBytes
  rw [corrValB_eq, uv_arm input.toList req rest hsub hseg]

/-! ## 3c. The `/health` arm — a SECOND dense route (constant body)

The off-arm residual: every non-`/bulk` route still fell back to the deployed
`List` serve. `/health` has a CONSTANT 2-byte body (`"ok"`), so the same dense kit
closes it: an index-decided guard (`healthArmB`, same shape as `denseArmB`), the
constant `x-upstream` scalar of the `["health"]` route (`uvHealth`), the
index-native `x-corr` (`corrValB`, already ∀-proven), the same flat header fold,
and the CONSTANT dense body (`healthBodyDense`, a top-level `ByteArray`). The arm
equality is proven from scratch (there is no SPAN=18 `/health` analog): a
GENERALIZED `builtScalarsGen` — `ServeDenseReal.builtScalars` freed from `/bulk`,
usable by ANY constant-body route whose body the html-rewrite fixes — plus the
route-generic head linchpin `ServeDenseReal.denseHeadersUnknown`. -/

open Reactor (Response)
open Reactor.Pipeline (ResponseBuilder runPipeline)
open Datapath.DenseHead (renderHead denseHeadersBlock serialize_eq_head_body
  renderHead_eq_headBytes)
open Datapath.ServeDenseReal (denseHeadersUnknown)

/-- **The `/health`-arm guard** — the same eight gate/transform conjuncts as
`BulkArm`, the route shape pinned to the exact author route `["health"]` (which
matches FIRST from ANY host, so no vhost conjuncts are needed). -/
def HealthArm (c : Ctx) : Prop :=
  isAdminPath c.req = false
  ∧ Reactor.Stage.BasicAuth.isProtectedPath c.req = false
  ∧ Reactor.Stage.Rate.admits c = true
  ∧ ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)
  ∧ targetEscapes c.req = false
  ∧ policyReserved c.req = false
  ∧ Reactor.Stage.Gzip.acceptsGzip c.req = false
  ∧ _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none
  ∧ Reactor.App.targetSegments c.req.target = ["health"]

instance (c : Ctx) : Decidable (HealthArm c) := by
  unfold HealthArm; infer_instance

/-- The request-level `/health` arm — `HealthArm` keyed on the request alone. -/
def ReqArmHealth (req : Proto.Request) : Prop := HealthArm (reqCtx req)

instance (req : Proto.Request) : Decidable (ReqArmHealth req) := by
  unfold ReqArmHealth; infer_instance

/-- `HealthArm` transports along the request: it never reads `Ctx.input`, and both
contexts carry empty attrs. -/
theorem healthArm_of_reqArm (l : Bytes) (req : Proto.Request)
    (hreq : (ctxOf l).req = req) (h : ReqArmHealth req) : HealthArm (ctxOf l) := by
  have hctx : ctxOf l = { input := l, req := req, attrs := [] } := by
    rw [← hreq]; exact rfl
  rw [hctx]
  exact h

/-- **The index-decided `/health` guard** — same shape as `denseArmB`: O(1) size
gates, the head parse by `parseIndexNative` (index probes off the borrowed window),
the arm conjuncts decided on the parsed request. NO `input.toList`, NO `deploySubs`
on the deciding path. -/
def healthArmB (input : ByteArray) : Bool :=
  decide (0 < input.size)
    && decide (¬ input.size > deployConfig.maxHeaderBytes)
    && (match parseIndexNative (full input) with
        | .request _ req _ => decide (ReqArmHealth req)
        | _ => false)

/-- A firing `/health` guard yields the dispatched request together with its arm
conjuncts — the same parse-refinement + dispatch bridge as `denseArmB_dispatch`. -/
theorem healthArmB_dispatch (input : ByteArray) (h : healthArmB input = true) :
    ∃ req rest, deploySubs input.toList = .dispatch req :: rest ∧ ReqArmHealth req := by
  unfold healthArmB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsz, hlen⟩, harm⟩ := h
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  cases hpo : parseIndexNative (full input) with
  | request n req ka =>
    rw [hpo] at harm
    have harm' : ReqArmHealth req := of_decide_eq_true harm
    have hparse : Reactor.Config.h1ParseFn input.toList = .request n req ka := by
      rw [← hread, ← parseIndexNative_refines _ (full_wf _), hpo]
    have hlen' : ¬ input.toList.length > deployConfig.maxHeaderBytes := by
      rw [ba_toList_length]; exact of_decide_eq_true hlen
    have hne : input.toList.isEmpty = false := by
      have hpos : 0 < input.toList.length := by
        rw [ba_toList_length]; exact of_decide_eq_true hsz
      cases hl : input.toList with
      | nil => rw [hl] at hpos; exact absurd hpos (by simp)
      | cons a t => rfl
    obtain ⟨rest, hsub⟩ := deploySubs_dispatch input.toList n req ka hlen' hne hparse
    exact ⟨req, rest, hsub, harm'⟩
  | reject n resp => rw [hpo] at harm; exact absurd harm (by simp)
  | incomplete => rw [hpo] at harm; exact absurd harm (by simp)
  | error => rw [hpo] at harm; exact absurd harm (by simp)

/-- **Guard soundness**: when the index-decided `/health` guard fires, the deployed
`HealthArm` (over the deployed `List` ctx) genuinely holds. -/
theorem healthArmB_sound (input : ByteArray) (h : healthArmB input = true) :
    HealthArm (ctxOf input.toList) := by
  obtain ⟨req, rest, hsub, harm⟩ := healthArmB_dispatch input h
  exact healthArm_of_reqArm input.toList req (ctxOf_req input.toList req rest hsub) harm

/-! ### The `/health` response pieces — constant body, generalized built scalars -/

/-- The constant `/health` body (`"ok"`), `List` side — what the deployed app
route answers (`Reactor.App.health_unchanged`). -/
def healthBody : Bytes := "ok".toUTF8.toList

/-- The constant `/health` body as a `ByteArray` — a TOP-LEVEL CONSTANT, computed
once at initialization, never consed per request. -/
def healthBodyDense : ByteArray := "ok".toUTF8

/-- The dense constant body denotes to the deployed `/health` body. -/
theorem healthBodyDense_toList : healthBodyDense.data.toList = healthBody :=
  (ba_toList_eq _).symm

/-- The `/health` body bytes, pinned (`ByteArray.toList` does not kernel-reduce;
`ba_toList_eq` bridges to the `.data` view, which does). -/
theorem healthBody_bytes : healthBody = [0x6F, 0x6B] := by
  unfold healthBody
  rw [ba_toList_eq]
  decide

/-- The deployed html-rewrite fixes the tiny tagless `/health` body — no `<`
(0x3C) to strip in `"ok"` (same spec route as `rewriteBytes_bulkBody`). -/
theorem rewriteBytes_healthBody :
    Reactor.Stage.HtmlRewrite.rewriteBytes healthBody = healthBody := by
  rw [healthBody_bytes, HtmlRewriteCorrect.rewriteBytes_eq_spec]
  show HtmlRewriteCorrect.strip false [0x6F, 0x6B] = [0x6F, 0x6B]
  exact Datapath.ServeDenseFullReal.strip_false_no_lt _ (by decide)

/-- On the `/health` arm the app handler answers the constant `200 "ok"`:
`App.handle` selects the exact author route `["health"]` first, from any host. -/
theorem appHandler_health (c : Ctx)
    (hseg : Reactor.App.targetSegments c.req.target = ["health"]) :
    appHandler c = { status := 200, reason := Reactor.App.reasonFor 200,
                     headers := [], body := healthBody } := by
  unfold appHandler
  exact Reactor.App.health_unchanged c.req hseg

/-- **The deployed built response scalars, GENERALIZED to any constant-body
admitted route** — `Datapath.ServeDenseReal.builtScalars` freed from `/bulk`: with
every gate admitting and the app response `{st, rs, [], bd}` where the html-rewrite
fixes `bd`, the BUILT fold over `deployStagesFull2` carries exactly those scalars.
Same proof skeleton (the header transforms leave status/reason/body; the two
body-touching transforms are gated off or fix the body). -/
theorem builtScalarsGen (c : Ctx) (st : Nat) (rs bd : Bytes)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hpol : policyReserved c.req = false)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none)
    (happ : appHandler c = { status := st, reason := rs, headers := [], body := bd })
    (hbd : Reactor.Stage.HtmlRewrite.rewriteBytes bd = bd) :
    ((runPipeline deployStagesFull2 appHandler c).build).status = st
    ∧ ((runPipeline deployStagesFull2 appHandler c).build).reason = rs
    ∧ ((runPipeline deployStagesFull2 appHandler c).build).body = bd := by
  have hcorsResp : ∀ b : ResponseBuilder, deployCorsStage.onResponse c b = b := by
    intro b
    show (match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
          | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
          | none   => b) = b
    rw [hcors]
  have hgzResp : ∀ b : ResponseBuilder, Reactor.Stage.Gzip.gzipStage.onResponse c b = b := by
    intro b
    show (match Reactor.Stage.Gzip.acceptsGzip c.req with
          | true  => (b.mapResp Reactor.Stage.Gzip.gzipBody).addHeader
                        (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
          | false => b) = b
    rw [hgz]
  have hlcS : ∀ (prog : List Header.Op) (r : Response),
      (Reactor.Lifecycle.rewriteResp prog r).status = r.status := fun _ _ => rfl
  have hlcR : ∀ (prog : List Header.Op) (r : Response),
      (Reactor.Lifecycle.rewriteResp prog r).reason = r.reason := fun _ _ => rfl
  have hlcB : ∀ (prog : List Header.Op) (r : Response),
      (Reactor.Lifecycle.rewriteResp prog r).body = r.body := fun _ _ => rfl
  have hhrB : ∀ r : Response, (Reactor.Stage.Header.rewriteResp r).body = r.body := fun _ => rfl
  have hhrS : ∀ r : Response, (Reactor.Stage.Header.rewriteResp r).status = r.status := fun _ => rfl
  have hhrR : ∀ r : Response, (Reactor.Stage.Header.rewriteResp r).reason = r.reason := fun _ => rfl
  rw [full2_reduces_unknown c hadmin hpriv hip hrate hredir htrav hpol, Reactor.Pipeline.build_mapResp]
  have hinner : (runPipeline full2InnerStages appHandler c).build
      = Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp
          ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                         Reactor.Stage.Header.headerStage] appHandler c).build) := by
    show (runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
        :: Reactor.Stage.HtmlRewrite.htmlrewriteStage
        :: Reactor.Stage.SecurityHeaders.securityheadersStage
        :: [Reactor.Stage.Header.headerStage]) appHandler c).build = _
    rw [Reactor.Deploy.prepend_pass deployCorsStage _ appHandler c rfl hcorsResp,
        Reactor.Deploy.prepend_pass Reactor.Stage.Gzip.gzipStage _ appHandler c rfl hgzResp,
        Reactor.Stage.HtmlRewrite.htmlrewriteStage_effect, Reactor.Pipeline.build_mapResp]
  have hmidReduce : (runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                            Reactor.Stage.Header.headerStage] appHandler c).build
      = { (runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build with
          headers := ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).headers
            ++ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy } := by
    rw [Reactor.Stage.SecurityHeaders.securityheadersStage_effect [Reactor.Stage.Header.headerStage]
        appHandler c, Reactor.Pipeline.build_addHeaders]
  have hmidStatus : ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage] appHandler c).build).status = (appHandler c).status := by
    rw [hmidReduce]
    show ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).status
      = (appHandler c).status
    rw [Reactor.Stage.Header.headerStage_effect, hhrS,
        show (runPipeline [] appHandler c).build = appHandler c from rfl]
  have hmidReason : ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage] appHandler c).build).reason = (appHandler c).reason := by
    rw [hmidReduce]
    show ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).reason
      = (appHandler c).reason
    rw [Reactor.Stage.Header.headerStage_effect, hhrR,
        show (runPipeline [] appHandler c).build = appHandler c from rfl]
  have hmidBody : ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage] appHandler c).build).body = (appHandler c).body := by
    rw [hmidReduce]
    show ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).body
      = (appHandler c).body
    rw [Reactor.Stage.Header.headerStage_effect, hhrB,
        show (runPipeline [] appHandler c).build = appHandler c from rfl]
  have hreason : ∀ r : Response,
      (Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp r).reason = r.reason := by
    intro r
    unfold Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp Reactor.Stage.HtmlRewrite.htmlTransformResp
    cases Reactor.Stage.HtmlRewrite.isHtmlCT r.headers <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hlcS, hinner, Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp_status, hmidStatus, happ]
  · rw [hlcR, hinner, hreason, hmidReason, happ]
  · rw [hlcB, hinner, Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp_body, hmidBody, happ]
    split
    · exact hbd
    · rfl

/-! ### The `/health` head — constant `x-upstream`, index-native `x-corr` -/

/-- **The `/health`-arm `x-upstream` value — a top-level constant.** The deployed
plan value of the `["health"]` route, computed ONCE at module initialization. -/
def uvHealth : Header.Value :=
  upstreamVal (Reactor.DnsWire.resolveSubs Reactor.DnsWire.demoResolver
    (routeProxySegs Reactor.ProxyServe.demoProxyApp Reactor.Proxy.demoCtx ["health"]))

/-- **`x-upstream` collapses to `uvHealth` on the `/health` arm** — same collapse
as `uv_arm`: the proxy reads only the FIRST dispatch, the router only the
segments, the LB neither. -/
theorem uv_health (l : Bytes) (req : Proto.Request) (rest : List Reactor.RingSubmission)
    (hsub : deploySubs l = .dispatch req :: rest)
    (hseg : Reactor.App.targetSegments req.target = ["health"]) :
    upstreamVal (deployPlan (deploySubs l)) = uvHealth := by
  rw [hsub]
  unfold Reactor.Deploy.deployPlan
  rw [Reactor.ProxyServe.serveProxyOn_dispatch, routeProxy_eq_segs, hseg]
  rfl

/-- The `/health` head bytes, `List` side — the deployed request-derived scalars
(`x-upstream` via the full `deploySubs` plan, `x-corr` via `corrVal`), the proven
flat header fold, body-length `healthBody.length`. -/
def healthHeadBytes (input : Bytes) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs input))) (corrVal input)).denote
    healthBody.length

/-- **The dense `/health` head with NO `input.toList`**: constant `x-upstream`
(`uvHealth`), index-native `x-corr` (`corrValB`), the proven flat header fold. -/
def healthHeadBytesIdx (input : ByteArray) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (denseHeadersBlock [] uvHealth (corrValB input)).denote
    healthBody.length

/-- On a firing `/health` guard the index-native head IS the deployed one — the
scalar collapse (`uv_health` + `corrValB_eq`) under the dispatch bridge. -/
theorem healthHeadBytesIdx_eq (input : ByteArray) (h : healthArmB input = true) :
    healthHeadBytesIdx input = healthHeadBytes input.toList := by
  obtain ⟨req, rest, hsub, harm⟩ := healthArmB_dispatch input h
  obtain ⟨_, _, _, _, _, _, _, _, hseg⟩ := harm
  unfold healthHeadBytesIdx healthHeadBytes
  rw [corrValB_eq, uv_health input.toList req rest hsub hseg]

/-! ### The `/health` arm equality — dense (head ++ constant body) = deployed -/

/-- Bulk-append a constant dense body onto the head `Array` = the flat `ByteArray`
of the head list appended with the body list — `ServeDenseReal.denseOut_eq`
generalized to ANY dense body that denotes its `List` body. -/
theorem denseOutGen (head : Bytes) (bA : ByteArray) (l : Bytes)
    (hl : bA.data.toList = l) :
    ByteArray.mk head.toArray ++ bA = ByteArray.mk (head ++ l).toArray := by
  have hda_gen : ∀ a b : ByteArray, (a ++ b).data = a.data ++ b.data := fun a b => by
    show (ByteArray.append a b).data = a.data ++ b.data
    simp [ByteArray.append, ByteArray.copySlice, ByteArray.size,
      Array.extract_empty_of_size_le_start a.data (Nat.le_add_right _ _)]
  have hda : (ByteArray.mk head.toArray ++ bA).data
      = head.toArray ++ bA.data := hda_gen (ByteArray.mk head.toArray) bA
  have harr : head.toArray ++ bA.data = (head ++ l).toArray := by
    apply Array.toList_inj.mp
    rw [Array.toList_append, Array.toList_toArray, Array.toList_toArray]
    show head.toArray.toList ++ bA.data.toList = head ++ l
    rw [Array.toList_toArray, hl]
  have heta : ByteArray.mk head.toArray ++ bA
      = ByteArray.mk ((ByteArray.mk head.toArray ++ bA).data) := by
    cases (ByteArray.mk head.toArray ++ bA); rfl
  rw [heta, hda, harr]

/-- **The `/health` dense arm equals the deployed serve.** On the `HealthArm` the
dense (head ++ constant-body) output is byte-identical to the deployed
`servePipelineFull2` — via the route-generic head linchpin
(`denseHeadersUnknown`), the GENERALIZED built scalars (`builtScalarsGen`), and
the generic dense-body bridge (`denseOutGen`). -/
theorem healthArm_eq (input : ByteArray) (harm : HealthArm (ctxOf input.toList)) :
    ByteArray.mk (healthHeadBytes input.toList).toArray ++ healthBodyDense
      = ByteArray.mk (servePipelineFull2 input.toList).toArray := by
  obtain ⟨hadmin, hpriv, hrate, hredir, htrav, hpol, hgz, hcors, hseg⟩ := harm
  have hip : (ctxOf input.toList).attrs.find?
      (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none := rfl
  have happ : appHandler (ctxOf input.toList)
      = { status := 200, reason := Reactor.App.reasonFor 200,
          headers := [], body := healthBody } :=
    appHandler_health (ctxOf input.toList) hseg
  obtain ⟨hst, hrs, hbd⟩ :=
    builtScalarsGen (ctxOf input.toList) 200 (Reactor.App.reasonFor 200) healthBody
      hadmin hpriv hip hrate hredir htrav hpol hgz hcors happ rewriteBytes_healthBody
  have hserve : servePipelineFull2 input.toList
      = Reactor.serialize
          ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build) := rfl
  have hhdr := denseHeadersUnknown (ctxOf input.toList) hadmin hpriv hip hrate hredir
    htrav hpol hgz hcors
  rw [hserve, serialize_eq_head_body
        ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build)]
  rw [← renderHead_eq_headBytes
        ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build)]
  rw [hst, hrs, hbd]
  have hAheaders : (appHandler (ctxOf input.toList)).headers = [] := by rw [happ]
  rw [show ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build).headers
        = (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs (ctxOf input.toList).input)))
            (corrVal (ctxOf input.toList).input)).denote from by rw [← hhdr, hAheaders]]
  show ByteArray.mk (healthHeadBytes input.toList).toArray ++ healthBodyDense
    = ByteArray.mk ((healthHeadBytes input.toList) ++ healthBody).toArray
  exact denseOutGen (healthHeadBytes input.toList) healthBodyDense healthBody
    healthBodyDense_toList

/-! ## 4. THE SERVE — both forks index-decided, the dense arm SPAN=18's -/

/-- **The index-decided runtime-dense serve.** The h2c fork and BOTH dense-arm
guards are decided by INDEX PROBES off the borrowed window (`hasH2PrefaceB`,
`denseArmB`, `healthArmB` — no `input.toList`, no reactor `List` step on the
deciding path); the `/bulk` arm emits the proven SPAN=18 dense head + dense 1 MiB
body, the `/health` arm the dense head + CONSTANT 2-byte body; the h2c and
remaining off-arm branches are the deployed serve verbatim. -/
@[export drorb_serve_dense_idx]
def serveDenseIdx (input : ByteArray) : ByteArray :=
  if hasH2PrefaceB input then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else if denseArmB input then
    ByteArray.mk (denseHeadBytesIdx input).toArray ++ bulkBodyDense
  else if healthArmB input then
    ByteArray.mk (healthHeadBytesIdx input).toArray ++ healthBodyDense
  else
    ByteArray.mk (servePipelineFull2 input.toList).toArray

/-- **Byte-identity to the deployed serve.** For EVERY input, `serveDenseIdx`
produces the identical bytes to `Datapath.ServeFlatFull.deployedServeRef`
(= `Dataplane.drorbServe`): the preface fork agrees by `hasH2PrefaceB_eq`; a firing
`/bulk` guard implies the deployed `/bulk` arm (`denseArmB_sound`), where the dense
output is the proven SPAN=18 byte-identity (`denseArm_eq`); a firing `/health`
guard implies the deployed `HealthArm` (`healthArmB_sound`), where the dense output
is the NEW from-scratch byte-identity (`healthArm_eq`); off both guards it is the
deployed serve verbatim. -/
theorem serveDenseIdx_refines (input : ByteArray) :
    serveDenseIdx input = Datapath.ServeFlatFull.deployedServeRef input := by
  unfold serveDenseIdx Datapath.ServeFlatFull.deployedServeRef
  rw [hasH2PrefaceB_eq]
  by_cases h2 : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h2, if_true]
  · simp only [h2, Bool.false_eq_true, if_false]
    by_cases hb : denseArmB input
    · rw [if_pos hb, denseHeadBytesIdx_eq input hb]
      exact denseArm_eq input (denseArmB_sound input hb)
    · rw [if_neg hb]
      by_cases hh : healthArmB input
      · rw [if_pos hh, healthHeadBytesIdx_eq input hh]
        exact healthArm_eq input (healthArmB_sound input hh)
      · rw [if_neg hh]

/-! ## 5. Non-vacuity — the index-decided guard genuinely fires (and refuses)

Kernel-evaluated: the guard FIRES on real `/bulk` requests (localhost AND
non-localhost hosts), REFUSES the non-arm requests (`/health` route,
gzip-accepting `/bulk`, CORS-origin `/bulk`), agrees with the deployed `BulkArm`
decision on all of them, and the assembled serve is byte-identical to the deployed
serve on every one. -/

/-- A gzip-accepting `/bulk` request — the arm must NOT fire (deployed gzip arm). -/
def bulkGzipReq : ByteArray :=
  "GET /bulk HTTP/1.1\r\nHost: localhost\r\nAccept-Encoding: gzip\r\n\r\n".toUTF8

/-- A CORS `/bulk` request with the deployed policy's PERMITTED origin
(`corsPolicy.allowedOrigins = ["https://app.example.com"]`) — the deployed CORS
transform stamps `Access-Control-Allow-Origin`, so the arm must NOT fire. -/
def bulkCorsReq : ByteArray :=
  "GET /bulk HTTP/1.1\r\nHost: localhost\r\nOrigin: https://app.example.com\r\n\r\n".toUTF8

/-- A `/health` request — parses fine, wrong route: the arm must NOT fire. -/
def healthReq : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The guard FIRES on the real `/bulk` requests (both hosts) — index-decided.
#guard denseArmB bulkDemoReq
#guard denseArmB bulkDemoReqAnyHost
-- The guard REFUSES off-arm requests (gzip / CORS / wrong route / h2 preface).
#guard !(denseArmB bulkGzipReq)
#guard !(denseArmB bulkCorsReq)
#guard !(denseArmB healthReq)
-- The index-decided guard AGREES with the deployed `List`-decided arm on all five
-- (soundness is proven ∀; these five pin completeness on the demo surface).
#guard denseArmB bulkDemoReq == decide (BulkArm (ctxOf bulkDemoReq.toList))
#guard denseArmB bulkDemoReqAnyHost == decide (BulkArm (ctxOf bulkDemoReqAnyHost.toList))
#guard denseArmB bulkGzipReq == decide (BulkArm (ctxOf bulkGzipReq.toList))
#guard denseArmB bulkCorsReq == decide (BulkArm (ctxOf bulkCorsReq.toList))
#guard denseArmB healthReq == decide (BulkArm (ctxOf healthReq.toList))
-- The index-decided preface fork agrees with the deployed one.
#guard hasH2PrefaceB (ByteArray.mk (Reactor.Ingress.h2Preface ++ [0]).toArray)
#guard !(hasH2PrefaceB bulkDemoReq)
-- The assembled serve is byte-identical to the deployed serve, on-arm and off.
#guard (serveDenseIdx bulkDemoReqAnyHost).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReqAnyHost).data.toList
#guard (serveDenseIdx healthReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef healthReq).data.toList
#guard (serveDenseIdx bulkGzipReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkGzipReq).data.toList
-- The dense arm genuinely serves the 1 MiB body.
#guard (serveDenseIdx bulkDemoReqAnyHost).size > 1048576

/-! ### `/health` dense-arm non-vacuity -/

/-- A gzip-accepting `/health` request — the deployed gzip arm fires instead, so
the dense `/health` arm must NOT. -/
def healthGzipReq : ByteArray :=
  "GET /health HTTP/1.1\r\nHost: x\r\nAccept-Encoding: gzip\r\n\r\n".toUTF8

-- The `/health` guard FIRES on the real request — index-decided.
#guard healthArmB healthReq
-- The guard REFUSES off-arm shapes (gzip-accepting `/health`, `/bulk` requests).
#guard !(healthArmB healthGzipReq)
#guard !(healthArmB bulkDemoReq)
#guard !(healthArmB bulkDemoReqAnyHost)
-- The index-decided guard AGREES with the deployed `List`-decided arm.
#guard healthArmB healthReq == decide (HealthArm (ctxOf healthReq.toList))
#guard healthArmB healthGzipReq == decide (HealthArm (ctxOf healthGzipReq.toList))
#guard healthArmB bulkDemoReq == decide (HealthArm (ctxOf bulkDemoReq.toList))
-- The index-native `/health` head equals the deployed one on the arm request.
#guard healthHeadBytesIdx healthReq == healthHeadBytes healthReq.toList
-- The constant upstream scalar is the deployed plan value on the arm.
#guard uvHealth == Reactor.Deploy.upstreamVal (Reactor.Deploy.deployPlan
        (Reactor.Deploy.deploySubs healthReq.toList))
-- The assembled serve is byte-identical to the deployed serve on the NEW dense
-- `/health` arm (the healthReq guard above now exercises the dense arm) and on
-- the gzip fallback.
#guard (serveDenseIdx healthGzipReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef healthGzipReq).data.toList
-- The dense `/health` response genuinely carries the 2-byte constant body.
#guard (serveDenseIdx healthReq).size > healthBody.length

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

-- The index-native head equals the deployed dense head on the demo arm requests.
#guard denseHeadBytesIdx bulkDemoReq == denseHeadBytes bulkDemoReq.toList
#guard denseHeadBytesIdx bulkDemoReqAnyHost == denseHeadBytes bulkDemoReqAnyHost.toList
-- The constant upstream scalar is the deployed plan value on the arm.
#guard uvBulk == Reactor.Deploy.upstreamVal (Reactor.Deploy.deployPlan
        (Reactor.Deploy.deploySubs bulkDemoReq.toList))
-- The index-native corr value is the deployed one.
#guard corrValB bulkDemoReq == Reactor.Deploy.corrVal bulkDemoReq.toList

#print axioms deploySubs_dispatch
#print axioms uv_arm
#print axioms corrValB_eq
#print axioms denseHeadBytesIdx_eq
#print axioms denseArmB_sound
#print axioms builtScalarsGen
#print axioms uv_health
#print axioms healthArmB_sound
#print axioms healthHeadBytesIdx_eq
#print axioms healthArm_eq
#print axioms serveDenseIdx_refines

end Datapath.ServeDenseIdx
