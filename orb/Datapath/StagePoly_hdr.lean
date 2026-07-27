import Datapath.HdrSeq
import Datapath.FlatStage_hdr

/-!
# Datapath.StagePoly_hdr — the DEPLOYED header-stamp stage (`deployStagesFull2`
stage 8, `Reactor.Deploy.headerRewriteStage`) written ONCE over `[HdrSeq H]`.

This is the header-grain sibling of `Datapath.HdrSeqProto`'s `hrwStagePoly`, but
grounded in the ACTUAL deployed stage rather than `stdRewrite` alone. The deployed
header stage runs `Reactor.Lifecycle.rewriteResp (deployProg …)` through the affine
builder's `mapResp` (read off `headerRewriteStage.onResponse`), where

```
deployProg plan input
  = stdRewrite ++ [ set upstreamName (upstreamVal plan), set corrName (corrVal input) ]
  = [ hopDyn, set Server drorb, set x-upstream <lb-addr>, set x-corr <corr-id> ]
```

so the net response-header effect is: **strip the RFC 9110 §7.6.1 hop-by-hop set,
then install `Server`, `x-upstream`, `x-corr`** (each `set` = `remove`-then-append).

`deployHdrPoly` writes that exact effect ONCE over `[HdrSeq H]` as three `setPoly`
layers (each `push` after a name-`filter`) on top of the hop `filter` — the same
`push`/`filter` op vocabulary `hrwStagePoly` uses. Its whole refinement
(`deployHdrPoly_refines`) is a 2-line `rw`+`simp` over `push_denote`/`filter_denote`
— NO per-stage induction — and instantiates at `List (Bytes × Bytes)` (spec) and
`HdrBlock` (fast, genuinely flat: `Array.filter`/`Array.push`, no cons-spine).

## Grounding (equality-transfer, not a re-spec)

`deployHdrPoly_eq_deployed` proves the spec instance computes EXACTLY the deployed
`headerRewriteStage.onResponse`'s built-header block, read off the real stage by
reusing `Datapath.FlatStage_hdr.deployHdrStage_headers_effect`
(`ofHeaders (Header.run (deployProg …) (toHeaders b.build.headers))`) and unfolding
the real `Header.run` over the real `deployProg`. The hop set is `dynHopSet` of the
message's own headers (RFC 9110 §7.6.1) and the `x-upstream`/`x-corr` VALUES are the
deployed `upstreamVal`/`corrVal` — passed as parameters (denotation-derived), the
one data-dependence the byte-grain never had (same wrinkle as `hrwStagePoly`).

The **refinement** (poly form = poly form across instances) is the ~2-line `simp`;
the **grounding** (poly form = the deployed `Header.run`) is NOT a `simp` — it is the
strip+set `Header.run` bridge (`toH_setlayer`/`toH_strip` + a `run_cons` unfold),
exactly the re-scope `Datapath.FlatStage_hdr` documents for this stage: a strip+set
stage is a whole `Header.run`, not a monotone push-fold. See `residual` in the return.
-/

namespace Datapath.StagePoly_hdr

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder)
open Reactor.Deploy (headerRewriteStage deployProg deployPlan deploySubs
  upstreamName corrName upstreamVal corrVal)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatStage_hdr (deployHdrStage_headers_effect)

/-! ## 1. The polymorphic stage — three `set` layers over a hop `filter` -/

/-- **One `set` layer, written over `[HdrSeq H]`.** `set n v` = drop every prior
field named `n` (a name-`filter`), then `push` the `(n, v)` pair — exactly
`Header.set n v = remove n · ++ [⟨n, v⟩]`. The `push`/`filter` op vocabulary only. -/
def setPoly {H : Type} [HdrSeq H] (n v : Bytes) (h : H) : H :=
  HdrSeq.push (HdrSeq.filter h (fun nv => !Header.nameEqb nv.1 n)) (n, v)

/-- **The deployed header-stamp stage, written ONCE over `[HdrSeq H]`.** Strip the
hop set `hop` (`filter` keeping the non-hop pairs), then install `Server`,
`x-upstream`, `x-corr` in order via `setPoly` — precisely
`Header.run [hopDyn, set Server, set x-upstream, set x-corr]` on the flat block.
`hop`, the `x-upstream` value `uV` and the `x-corr` value `cV` are PARAMETERS: the
deployed stage passes `dynHopSet` of the message's own headers and the real
`upstreamVal`/`corrVal` (the data-dependence; see `deployHdrPoly_eq_deployed`). -/
def deployHdrPoly {H : Type} [HdrSeq H] (hop : List Header.Name) (uV cV : Bytes) (h : H) : H :=
  setPoly corrName cV
    (setPoly upstreamName uV
      (setPoly Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
        (HdrSeq.filter h (fun nv => !Header.isHop hop nv.1))))

/-- The stage at the spec instance is exactly the nested `List.filter`s + appends —
the `List` normal form (`push@List = · ++ [·]`, `filter@List = List.filter`). No
separate spec expression is written; this is `deployHdrPoly` at `H := List _`. -/
theorem deployHdrPoly_list (hop : List Header.Name) (uV cV : Bytes)
    (l : List (Bytes × Bytes)) :
    deployHdrPoly (H := List (Bytes × Bytes)) hop uV cV l
      = (((((l.filter (fun nv => !Header.isHop hop nv.1)).filter
              (fun nv => !Header.nameEqb nv.1 Reactor.Lifecycle.serverName)
            ++ [(Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal)]).filter
              (fun nv => !Header.nameEqb nv.1 upstreamName)
          ++ [(upstreamName, uV)]).filter
            (fun nv => !Header.nameEqb nv.1 corrName))
        ++ [(corrName, cV)]) := rfl

/-! ## 2. The whole-stage refinement — FOLLOWS from the op laws (~2 lines) -/

/-- **The whole-stage refinement.** The dense stage's denotation equals the stage
run at the spec instance on the denoted input. Proven polymorphically in `H`;
discharged by `rw` to the `List` normal form + one `simp` over `push_denote` +
`filter_denote` (each `@[simp]`). No per-stage induction, no strip/set reasoning. -/
theorem deployHdrPoly_refines {H : Type} [HdrSeq H] (hop : List Header.Name)
    (uV cV : Bytes) (h : H) :
    HdrSeq.toHdrs (deployHdrPoly hop uV cV h)
      = deployHdrPoly (H := List (Bytes × Bytes)) hop uV cV (HdrSeq.toHdrs h) := by
  rw [deployHdrPoly_list, deployHdrPoly, setPoly, setPoly, setPoly]
  simp only [HdrSeq.push_denote, HdrSeq.filter_denote]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance of the
once-proven polymorphic theorem, no `HdrBlock`-specific reasoning. -/
theorem deployHdrBlock_refines (hop : List Header.Name) (uV cV : Bytes) (h : HdrBlock) :
    HdrBlock.denote (deployHdrPoly hop uV cV h)
      = deployHdrPoly (H := List (Bytes × Bytes)) hop uV cV h.denote :=
  deployHdrPoly_refines hop uV cV h

/-! ## 3. Grounding in the REAL deployed stage (the strip+set `Header.run` bridge) -/

/-- `toHeaders` transports a name-`filter` across the `⟨p.1, p.2⟩` view: the
predicate on the pair's first component equals the predicate on the field's name. -/
private theorem toH_filter (q : Bytes → Bool) (l : List (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (l.filter (fun p => q p.1))
      = (Reactor.Lifecycle.toHeaders l).filter (fun f => q f.name) := by
  unfold Reactor.Lifecycle.toHeaders
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : q a.1 <;> simp [h, ih]

/-- `toHeaders` distributes over `++`. -/
private theorem toH_append (l m : List (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (l ++ m)
      = Reactor.Lifecycle.toHeaders l ++ Reactor.Lifecycle.toHeaders m := by
  unfold Reactor.Lifecycle.toHeaders; rw [List.map_append]

/-- `ofHeaders ∘ toHeaders = id` — the field view round-trips (Prod eta). -/
private theorem ofH_toH (l : List (Bytes × Bytes)) :
    Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders l) = l := by
  unfold Reactor.Lifecycle.ofHeaders Reactor.Lifecycle.toHeaders
  induction l with
  | nil => rfl
  | cons a t ih =>
    have e : Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders (a :: t))
        = a :: Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders t) := rfl
    unfold Reactor.Lifecycle.ofHeaders Reactor.Lifecycle.toHeaders at e
    rw [e, ih]

/-- The hop-strip layer bridges to `Header.strip` on the denotation. -/
private theorem toH_strip (hop : List Header.Name) (l : List (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (l.filter (fun nv => !Header.isHop hop nv.1))
      = Header.strip hop (Reactor.Lifecycle.toHeaders l) := by
  rw [Header.strip]; exact toH_filter (fun nm => !Header.isHop hop nm) l

/-- One `set` layer bridges to `Header.set` on the denotation. -/
private theorem toH_setlayer (n v : Bytes) (l : List (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (l.filter (fun nv => !Header.nameEqb nv.1 n) ++ [(n, v)])
      = Header.set n v (Reactor.Lifecycle.toHeaders l) := by
  rw [toH_append]
  have : Reactor.Lifecycle.toHeaders (l.filter (fun nv => !Header.nameEqb nv.1 n))
      = Header.remove n (Reactor.Lifecycle.toHeaders l) := by
    rw [Header.remove]; exact toH_filter (fun nm => !Header.nameEqb nm n) l
  rw [this]; rfl

/-- **Grounded in the REAL deployed stage (non-vacuous).** With the hop set taken to
be the message's `dynHopSet` and the `x-upstream`/`x-corr` values taken to be the
deployed `upstreamVal`/`corrVal` (exactly what the deployed stage supplies), the
poly stage at the spec instance computes PRECISELY the header block the deployed
`headerRewriteStage` builds — the effect read off the real
`headerRewriteStage.onResponse` by `deployHdrStage_headers_effect`
(`ofHeaders (Header.run (deployProg …) (toHeaders b.build.headers))`), unfolded
against the real `deployProg`. Grounded on `Header.run`/`set`/`strip`, not re-specified. -/
theorem deployHdrPoly_eq_deployed (c : Ctx) (b : ResponseBuilder) :
    deployHdrPoly (H := List (Bytes × Bytes))
        (Header.dynHopSet (Reactor.Lifecycle.toHeaders b.build.headers))
        (upstreamVal (deployPlan (deploySubs c.input)))
        (corrVal c.input)
        b.build.headers
      = ((headerRewriteStage.onResponse c b).build).headers := by
  rw [deployHdrStage_headers_effect]
  rw [← ofH_toH (deployHdrPoly (H := List (Bytes × Bytes))
        (Header.dynHopSet (Reactor.Lifecycle.toHeaders b.build.headers))
        (upstreamVal (deployPlan (deploySubs c.input)))
        (corrVal c.input) b.build.headers)]
  congr 1
  rw [deployHdrPoly_list, toH_setlayer, toH_setlayer, toH_setlayer, toH_strip]
  -- Now LHS = set x-corr (set x-upstream (set Server (strip dynHop H0))); reduce the
  -- deployed `Header.run (deployProg …)` to the same nested strip/set form.
  have hrun : Header.run (deployProg (deployPlan (deploySubs c.input)) c.input)
        (Reactor.Lifecycle.toHeaders b.build.headers)
      = Header.set corrName (corrVal c.input)
          (Header.set upstreamName (upstreamVal (deployPlan (deploySubs c.input)))
            (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
              (Header.strip (Header.dynHopSet (Reactor.Lifecycle.toHeaders b.build.headers))
                (Reactor.Lifecycle.toHeaders b.build.headers)))) := by
    show Header.run
        [ Header.Op.hopDyn,
          Header.Op.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal,
          Header.Op.set upstreamName (upstreamVal (deployPlan (deploySubs c.input))),
          Header.Op.set corrName (corrVal c.input) ]
        (Reactor.Lifecycle.toHeaders b.build.headers) = _
    simp only [Header.run_cons, Header.run_nil, Header.applyOp]
  rw [hrun]

/-! ## Non-vacuity — the poly form genuinely computes the REAL deployed effect at
BOTH instances (kernel-evaluated). Concrete `x-upstream`/`x-corr` values stand in
for the deployed `upstreamVal`/`corrVal`; the general theorem above is over them. -/

open Datapath.FlatStage_hdr (connF xtF)

/-- Concrete `x-upstream` value used by the `#guard`s. -/
private def uVg : Bytes := [49]      -- "1"
/-- Concrete `x-corr` value used by the `#guard`s. -/
private def cVg : Bytes := [55]      -- "7"

/-- The full deploy program at the concrete guard values — the REAL `deployProg`
shape (`stdRewrite ++ [set x-upstream, set x-corr]`). -/
private def progG : List Header.Op :=
  Reactor.Lifecycle.stdRewrite ++
    [Header.Op.set upstreamName uVg, Header.Op.set corrName cVg]

-- The flat `HdrBlock` poly stage computes exactly the deployed `Header.run` header
-- block on a concrete `Connection: close` response — hop stripped, Server /
-- x-upstream / x-corr installed — evaluated by the kernel.
#guard (deployHdrPoly (H := HdrBlock)
          (Header.dynHopSet (Reactor.Lifecycle.toHeaders [connF, xtF])) uVg cVg
          (HdrBlock.ofList [connF, xtF])).denote
        == Reactor.Lifecycle.ofHeaders
            (Header.run progG (Reactor.Lifecycle.toHeaders [connF, xtF]))

-- The poly stage genuinely rewrites: the flat output differs from the input.
#guard (deployHdrPoly (H := HdrBlock)
          (Header.dynHopSet (Reactor.Lifecycle.toHeaders [connF, xtF])) uVg cVg
          (HdrBlock.ofList [connF, xtF])).denote
        != [connF, xtF]

-- The installed headers are all present (Server / x-upstream / x-corr), hop gone.
#guard (deployHdrPoly (H := HdrBlock)
          (Header.dynHopSet (Reactor.Lifecycle.toHeaders [connF, xtF])) uVg cVg
          (HdrBlock.ofList [connF, xtF])).denote
        == [xtF,
            (Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal),
            (upstreamName, uVg), (corrName, cVg)]

-- Spec instance and flat instance agree on a concrete input (the refinement, run).
#guard (deployHdrPoly (H := HdrBlock)
          (Header.dynHopSet (Reactor.Lifecycle.toHeaders [connF, xtF])) uVg cVg
          (HdrBlock.ofList [connF, xtF])).denote
        == deployHdrPoly (H := List (Bytes × Bytes))
             (Header.dynHopSet (Reactor.Lifecycle.toHeaders [connF, xtF])) uVg cVg
             [connF, xtF]

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms Datapath.StagePoly_hdr.deployHdrPoly_refines
#print axioms Datapath.StagePoly_hdr.deployHdrBlock_refines
#print axioms Datapath.StagePoly_hdr.deployHdrPoly_eq_deployed

end Datapath.StagePoly_hdr
