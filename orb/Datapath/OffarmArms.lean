import Datapath.OffarmApp
import Datapath.HeadIdx

/-!
# Datapath.OffarmArms — the four off-arm route decisions, INDEX-NATIVE

The arm predicates for the four constant-body off-arm routes (the catch-all
`404`, the two exact virtual hosts, the assets glob route), each in two forms:

* the **deployed-side `Prop`** (`NotFoundArm` / `VhostAArm` / `VhostBArm` /
  `GlobArm`), keyed on the pipeline `Ctx` exactly as `BulkArm`/`HealthArm` are —
  the eight gate conjuncts plus the route shape, with request-level variants and
  the `ctxOf` transport;
* the **index-native decision** (`notFoundIdxB` / `vhostAIdxB` / `vhostBIdxB` /
  `globIdxB`) on the arena head: header NAMES compared by index probes
  (`gzipAnyIdx`/`corsNoneIdx`/`hostNeIdx` and the NEW `hostEqIdx` — the index
  host-compare), header VALUES resolved only on a name hit, the target resolved
  once. `protoReqOf` (the whole-head `List` materialization) is never called on
  the deciding path.

Each decision is proven **Boolean-equivalent** (`…IdxB_iff`) to its deployed arm
on the materialized head — the SAME decision on every request, not a
sound-but-narrower guard.
-/

namespace Datapath.OffarmArms

open Proto (Bytes)
open Reactor.Pipeline (Ctx)
open Reactor.Deploy
open Reactor.Config (protoReqOf resolveBytes)
open Datapath.ServeDenseIdx (reqCtx)
open Datapath.HeadIdx (tqOf gzipAnyIdx corsNoneIdx gzipAnyIdx_eq corsNoneIdx_eq
  hostNeIdx hostNeIdx_iff hostKey findValIdx rate_admits_reqCtx hostLabelsOf_idx)
open Datapath.OffarmApp (globPathPat bulkPathPat)

/-! ## 1. The index-native EXACT host compare (the vhost-arm decision) -/

/-- **The vhost-equality conjunct, index-native.** The `host` lookup scans names
by index probes; a present host resolves the (small) value on demand and splits
it exactly as the deployed `hostLabelsOf` does; an absent host never equals a
non-empty label list. -/
def hostEqIdx (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader)
    (labels : List String) : Bool :=
  match findValIdx s hostKey hs with
  | some ve => decide ((Reactor.App.bytesToString (resolveBytes s ve)).splitOn "." = labels)
  | none => false

/-- The index-native host equality decides exactly the deployed label equality
(for any non-empty label list). -/
theorem hostEqIdx_iff (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader)
    (req : Proto.Request) (labels : List String) (hne : labels ≠ [])
    (hh : req.headers = hs.map fun (h : Arena.Parse.ParsedHeader) =>
      (resolveBytes s h.name, resolveBytes s h.value)) :
    hostEqIdx s hs labels = true ↔ Reactor.App.hostLabelsOf req = labels := by
  rw [hostLabelsOf_idx s hs req hh]
  unfold hostEqIdx
  cases findValIdx s hostKey hs with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => hne h.symm
  | some ve => simp only [decide_eq_true_eq]

/-! ## 2. The catch-all `404` arm -/

/-- **The catch-all `404` arm** — the eight gate conjuncts (as `BulkArm`), the
author-table miss (not `/health`, not under `/static` or `/cgi-bin`), the block
miss (neither the glob nor the `/bulk` path), and a non-vhost authority. -/
def NotFoundArm (c : Ctx) : Prop :=
  isAdminPath c.req = false
  ∧ Reactor.Stage.BasicAuth.isProtectedPath c.req = false
  ∧ Reactor.Stage.Rate.admits c = true
  ∧ ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)
  ∧ targetEscapes c.req = false
  ∧ policyReserved c.req = false
  ∧ Reactor.Stage.Gzip.acceptsGzip c.req = false
  ∧ _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none
  ∧ Reactor.App.targetSegments c.req.target ≠ ["health"]
  ∧ List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false
  ∧ List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false
  ∧ RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments c.req.target) = false
  ∧ RouteAdvanced.pathMatch bulkPathPat (Reactor.App.targetSegments c.req.target) = false
  ∧ Reactor.App.hostLabelsOf c.req ≠ ["a", "example"]
  ∧ Reactor.App.hostLabelsOf c.req ≠ ["b", "example"]

/-- The request-level `404` arm. -/
def ReqArmNotFound (req : Proto.Request) : Prop := NotFoundArm (reqCtx req)

/-- `NotFoundArm` transports along the request: it never reads `Ctx.input`, and
both contexts carry empty attrs. -/
theorem notFoundArm_of_req (l : Bytes) (req : Proto.Request)
    (hreq : (ctxOf l).req = req) (h : ReqArmNotFound req) : NotFoundArm (ctxOf l) := by
  have hctx : ctxOf l = { input := l, req := req, attrs := [] } := by
    rw [← hreq]; exact rfl
  rw [hctx]
  exact h

/-- **The index-native `404` decision** on the arena head. -/
def notFoundIdxB (areq : Arena.Parse.Request) : Bool :=
  let tq := tqOf areq
  let segs := Reactor.App.targetSegments tq.target
  !isAdminPath tq
  && !Reactor.Stage.BasicAuth.isProtectedPath tq
  && !decide (tq.target = Reactor.Stage.Redirect.ruleTarget)
  && !targetEscapes tq
  && !policyReserved tq
  && !gzipAnyIdx areq.store areq.headers
  && corsNoneIdx areq.store areq.headers
  && !decide (segs = ["health"])
  && !List.isPrefixOf ["static"] segs
  && !List.isPrefixOf ["cgi-bin"] segs
  && !RouteAdvanced.pathMatch globPathPat segs
  && !RouteAdvanced.pathMatch bulkPathPat segs
  && hostNeIdx areq.store areq.headers

/-- **The `404` decision equivalence** — both directions. -/
theorem notFoundIdxB_iff (areq : Arena.Parse.Request) :
    notFoundIdxB areq = true ↔ ReqArmNotFound (protoReqOf areq) := by
  have hgz : gzipAnyIdx areq.store areq.headers
      = Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) :=
    gzipAnyIdx_eq areq.store areq.headers
  have hcors : corsNoneIdx areq.store areq.headers
      = (_root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (corsOriginOf (reqCtx (protoReqOf areq)))).isNone :=
    corsNoneIdx_eq areq.store areq.headers
  have hhost := hostNeIdx_iff areq.store areq.headers (protoReqOf areq) rfl
  unfold notFoundIdxB ReqArmNotFound NotFoundArm
  show (!isAdminPath (tqOf areq)
      && !Reactor.Stage.BasicAuth.isProtectedPath (tqOf areq)
      && !decide ((tqOf areq).target = Reactor.Stage.Redirect.ruleTarget)
      && !targetEscapes (tqOf areq)
      && !policyReserved (tqOf areq)
      && !gzipAnyIdx areq.store areq.headers
      && corsNoneIdx areq.store areq.headers
      && !decide (Reactor.App.targetSegments (tqOf areq).target = ["health"])
      && !List.isPrefixOf ["static"] (Reactor.App.targetSegments (tqOf areq).target)
      && !List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments (tqOf areq).target)
      && !RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments (tqOf areq).target)
      && !RouteAdvanced.pathMatch bulkPathPat (Reactor.App.targetSegments (tqOf areq).target)
      && hostNeIdx areq.store areq.headers) = true
    ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩
    rw [hgz] at h6
    rw [hcors] at h7
    obtain ⟨h13a, h13b⟩ := hhost.mp h13
    exact ⟨h1, h2, rate_admits_reqCtx _, h3, h4, h5, h6,
      Option.isNone_iff_eq_none.mp h7, h8, h9, h10, h11, h12, h13a, h13b⟩
  · rintro ⟨k1, k2, _, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩
    have k7' : Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) = false := k7
    rw [← hgz] at k7'
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k4⟩, k5⟩, k6⟩, k7'⟩, ?_⟩, k9⟩, k10⟩, k11⟩, k12⟩, k13⟩,
      hhost.mpr ⟨k14, k15⟩⟩
    rw [hcors]
    exact Option.isNone_iff_eq_none.mpr k8

/-! ## 3. The `a.example` virtual-host arm -/

/-- **The `a.example` arm** — the gates, the author-table miss, and the EXACT
`a.example` authority (which selects the first vhost block, whose only route is
its catch-all — no path conjuncts needed). -/
def VhostAArm (c : Ctx) : Prop :=
  isAdminPath c.req = false
  ∧ Reactor.Stage.BasicAuth.isProtectedPath c.req = false
  ∧ Reactor.Stage.Rate.admits c = true
  ∧ ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)
  ∧ targetEscapes c.req = false
  ∧ policyReserved c.req = false
  ∧ Reactor.Stage.Gzip.acceptsGzip c.req = false
  ∧ _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none
  ∧ Reactor.App.targetSegments c.req.target ≠ ["health"]
  ∧ List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false
  ∧ List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false
  ∧ Reactor.App.hostLabelsOf c.req = ["a", "example"]

/-- The request-level `a.example` arm. -/
def ReqArmVhostA (req : Proto.Request) : Prop := VhostAArm (reqCtx req)

theorem vhostAArm_of_req (l : Bytes) (req : Proto.Request)
    (hreq : (ctxOf l).req = req) (h : ReqArmVhostA req) : VhostAArm (ctxOf l) := by
  have hctx : ctxOf l = { input := l, req := req, attrs := [] } := by
    rw [← hreq]; exact rfl
  rw [hctx]
  exact h

/-- **The index-native `a.example` decision** on the arena head. -/
def vhostAIdxB (areq : Arena.Parse.Request) : Bool :=
  let tq := tqOf areq
  let segs := Reactor.App.targetSegments tq.target
  !isAdminPath tq
  && !Reactor.Stage.BasicAuth.isProtectedPath tq
  && !decide (tq.target = Reactor.Stage.Redirect.ruleTarget)
  && !targetEscapes tq
  && !policyReserved tq
  && !gzipAnyIdx areq.store areq.headers
  && corsNoneIdx areq.store areq.headers
  && !decide (segs = ["health"])
  && !List.isPrefixOf ["static"] segs
  && !List.isPrefixOf ["cgi-bin"] segs
  && hostEqIdx areq.store areq.headers ["a", "example"]

/-- **The `a.example` decision equivalence** — both directions. -/
theorem vhostAIdxB_iff (areq : Arena.Parse.Request) :
    vhostAIdxB areq = true ↔ ReqArmVhostA (protoReqOf areq) := by
  have hgz : gzipAnyIdx areq.store areq.headers
      = Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) :=
    gzipAnyIdx_eq areq.store areq.headers
  have hcors : corsNoneIdx areq.store areq.headers
      = (_root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (corsOriginOf (reqCtx (protoReqOf areq)))).isNone :=
    corsNoneIdx_eq areq.store areq.headers
  have hhost := hostEqIdx_iff areq.store areq.headers (protoReqOf areq) ["a", "example"]
    (List.cons_ne_nil _ _) rfl
  unfold vhostAIdxB ReqArmVhostA VhostAArm
  show (!isAdminPath (tqOf areq)
      && !Reactor.Stage.BasicAuth.isProtectedPath (tqOf areq)
      && !decide ((tqOf areq).target = Reactor.Stage.Redirect.ruleTarget)
      && !targetEscapes (tqOf areq)
      && !policyReserved (tqOf areq)
      && !gzipAnyIdx areq.store areq.headers
      && corsNoneIdx areq.store areq.headers
      && !decide (Reactor.App.targetSegments (tqOf areq).target = ["health"])
      && !List.isPrefixOf ["static"] (Reactor.App.targetSegments (tqOf areq).target)
      && !List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments (tqOf areq).target)
      && hostEqIdx areq.store areq.headers ["a", "example"]) = true
    ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    rw [hgz] at h6
    rw [hcors] at h7
    exact ⟨h1, h2, rate_admits_reqCtx _, h3, h4, h5, h6,
      Option.isNone_iff_eq_none.mp h7, h8, h9, h10, hhost.mp h11⟩
  · rintro ⟨k1, k2, _, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩
    have k7' : Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) = false := k7
    rw [← hgz] at k7'
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k4⟩, k5⟩, k6⟩, k7'⟩, ?_⟩, k9⟩, k10⟩, k11⟩, hhost.mpr k12⟩
    rw [hcors]
    exact Option.isNone_iff_eq_none.mpr k8

/-! ## 4. The `b.example` virtual-host arm -/

/-- **The `b.example` arm** — as `VhostAArm`, the authority pinned to
`b.example`. -/
def VhostBArm (c : Ctx) : Prop :=
  isAdminPath c.req = false
  ∧ Reactor.Stage.BasicAuth.isProtectedPath c.req = false
  ∧ Reactor.Stage.Rate.admits c = true
  ∧ ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)
  ∧ targetEscapes c.req = false
  ∧ policyReserved c.req = false
  ∧ Reactor.Stage.Gzip.acceptsGzip c.req = false
  ∧ _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none
  ∧ Reactor.App.targetSegments c.req.target ≠ ["health"]
  ∧ List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false
  ∧ List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false
  ∧ Reactor.App.hostLabelsOf c.req = ["b", "example"]

/-- The request-level `b.example` arm. -/
def ReqArmVhostB (req : Proto.Request) : Prop := VhostBArm (reqCtx req)

theorem vhostBArm_of_req (l : Bytes) (req : Proto.Request)
    (hreq : (ctxOf l).req = req) (h : ReqArmVhostB req) : VhostBArm (ctxOf l) := by
  have hctx : ctxOf l = { input := l, req := req, attrs := [] } := by
    rw [← hreq]; exact rfl
  rw [hctx]
  exact h

/-- **The index-native `b.example` decision** on the arena head. -/
def vhostBIdxB (areq : Arena.Parse.Request) : Bool :=
  let tq := tqOf areq
  let segs := Reactor.App.targetSegments tq.target
  !isAdminPath tq
  && !Reactor.Stage.BasicAuth.isProtectedPath tq
  && !decide (tq.target = Reactor.Stage.Redirect.ruleTarget)
  && !targetEscapes tq
  && !policyReserved tq
  && !gzipAnyIdx areq.store areq.headers
  && corsNoneIdx areq.store areq.headers
  && !decide (segs = ["health"])
  && !List.isPrefixOf ["static"] segs
  && !List.isPrefixOf ["cgi-bin"] segs
  && hostEqIdx areq.store areq.headers ["b", "example"]

/-- **The `b.example` decision equivalence** — both directions. -/
theorem vhostBIdxB_iff (areq : Arena.Parse.Request) :
    vhostBIdxB areq = true ↔ ReqArmVhostB (protoReqOf areq) := by
  have hgz : gzipAnyIdx areq.store areq.headers
      = Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) :=
    gzipAnyIdx_eq areq.store areq.headers
  have hcors : corsNoneIdx areq.store areq.headers
      = (_root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (corsOriginOf (reqCtx (protoReqOf areq)))).isNone :=
    corsNoneIdx_eq areq.store areq.headers
  have hhost := hostEqIdx_iff areq.store areq.headers (protoReqOf areq) ["b", "example"]
    (List.cons_ne_nil _ _) rfl
  unfold vhostBIdxB ReqArmVhostB VhostBArm
  show (!isAdminPath (tqOf areq)
      && !Reactor.Stage.BasicAuth.isProtectedPath (tqOf areq)
      && !decide ((tqOf areq).target = Reactor.Stage.Redirect.ruleTarget)
      && !targetEscapes (tqOf areq)
      && !policyReserved (tqOf areq)
      && !gzipAnyIdx areq.store areq.headers
      && corsNoneIdx areq.store areq.headers
      && !decide (Reactor.App.targetSegments (tqOf areq).target = ["health"])
      && !List.isPrefixOf ["static"] (Reactor.App.targetSegments (tqOf areq).target)
      && !List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments (tqOf areq).target)
      && hostEqIdx areq.store areq.headers ["b", "example"]) = true
    ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    rw [hgz] at h6
    rw [hcors] at h7
    exact ⟨h1, h2, rate_admits_reqCtx _, h3, h4, h5, h6,
      Option.isNone_iff_eq_none.mp h7, h8, h9, h10, hhost.mp h11⟩
  · rintro ⟨k1, k2, _, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩
    have k7' : Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) = false := k7
    rw [← hgz] at k7'
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k4⟩, k5⟩, k6⟩, k7'⟩, ?_⟩, k9⟩, k10⟩, k11⟩, hhost.mpr k12⟩
    rw [hcors]
    exact Option.isNone_iff_eq_none.mpr k8

/-! ## 5. The assets glob arm -/

/-- **The glob arm** — the gates, the author-table miss, a MATCHING glob path,
and a non-vhost authority (which selects the `anyHost` block, whose FIRST
matching route is the glob route). -/
def GlobArm (c : Ctx) : Prop :=
  isAdminPath c.req = false
  ∧ Reactor.Stage.BasicAuth.isProtectedPath c.req = false
  ∧ Reactor.Stage.Rate.admits c = true
  ∧ ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)
  ∧ targetEscapes c.req = false
  ∧ policyReserved c.req = false
  ∧ Reactor.Stage.Gzip.acceptsGzip c.req = false
  ∧ _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none
  ∧ Reactor.App.targetSegments c.req.target ≠ ["health"]
  ∧ List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false
  ∧ List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false
  ∧ RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments c.req.target) = true
  ∧ Reactor.App.hostLabelsOf c.req ≠ ["a", "example"]
  ∧ Reactor.App.hostLabelsOf c.req ≠ ["b", "example"]

/-- The request-level glob arm. -/
def ReqArmGlob (req : Proto.Request) : Prop := GlobArm (reqCtx req)

theorem globArm_of_req (l : Bytes) (req : Proto.Request)
    (hreq : (ctxOf l).req = req) (h : ReqArmGlob req) : GlobArm (ctxOf l) := by
  have hctx : ctxOf l = { input := l, req := req, attrs := [] } := by
    rw [← hreq]; exact rfl
  rw [hctx]
  exact h

/-- **The index-native glob decision** on the arena head. -/
def globIdxB (areq : Arena.Parse.Request) : Bool :=
  let tq := tqOf areq
  let segs := Reactor.App.targetSegments tq.target
  !isAdminPath tq
  && !Reactor.Stage.BasicAuth.isProtectedPath tq
  && !decide (tq.target = Reactor.Stage.Redirect.ruleTarget)
  && !targetEscapes tq
  && !policyReserved tq
  && !gzipAnyIdx areq.store areq.headers
  && corsNoneIdx areq.store areq.headers
  && !decide (segs = ["health"])
  && !List.isPrefixOf ["static"] segs
  && !List.isPrefixOf ["cgi-bin"] segs
  && RouteAdvanced.pathMatch globPathPat segs
  && hostNeIdx areq.store areq.headers

/-- **The glob decision equivalence** — both directions. -/
theorem globIdxB_iff (areq : Arena.Parse.Request) :
    globIdxB areq = true ↔ ReqArmGlob (protoReqOf areq) := by
  have hgz : gzipAnyIdx areq.store areq.headers
      = Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) :=
    gzipAnyIdx_eq areq.store areq.headers
  have hcors : corsNoneIdx areq.store areq.headers
      = (_root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (corsOriginOf (reqCtx (protoReqOf areq)))).isNone :=
    corsNoneIdx_eq areq.store areq.headers
  have hhost := hostNeIdx_iff areq.store areq.headers (protoReqOf areq) rfl
  unfold globIdxB ReqArmGlob GlobArm
  show (!isAdminPath (tqOf areq)
      && !Reactor.Stage.BasicAuth.isProtectedPath (tqOf areq)
      && !decide ((tqOf areq).target = Reactor.Stage.Redirect.ruleTarget)
      && !targetEscapes (tqOf areq)
      && !policyReserved (tqOf areq)
      && !gzipAnyIdx areq.store areq.headers
      && corsNoneIdx areq.store areq.headers
      && !decide (Reactor.App.targetSegments (tqOf areq).target = ["health"])
      && !List.isPrefixOf ["static"] (Reactor.App.targetSegments (tqOf areq).target)
      && !List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments (tqOf areq).target)
      && RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments (tqOf areq).target)
      && hostNeIdx areq.store areq.headers) = true
    ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
    rw [hgz] at h6
    rw [hcors] at h7
    obtain ⟨h12a, h12b⟩ := hhost.mp h12
    exact ⟨h1, h2, rate_admits_reqCtx _, h3, h4, h5, h6,
      Option.isNone_iff_eq_none.mp h7, h8, h9, h10, h11, h12a, h12b⟩
  · rintro ⟨k1, k2, _, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩
    have k7' : Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) = false := k7
    rw [← hgz] at k7'
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k4⟩, k5⟩, k6⟩, k7'⟩, ?_⟩, k9⟩, k10⟩, k11⟩, k12⟩,
      hhost.mpr ⟨k13, k14⟩⟩
    rw [hcors]
    exact Option.isNone_iff_eq_none.mpr k8

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms hostEqIdx_iff
#print axioms notFoundIdxB_iff
#print axioms vhostAIdxB_iff
#print axioms vhostBIdxB_iff
#print axioms globIdxB_iff

end Datapath.OffarmArms
