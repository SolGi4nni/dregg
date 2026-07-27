import Datapath.HdrSeq
import Datapath.FlatStage
import Datapath.FlatStage_cors
import Reactor.Stage.Header

/-!
# Datapath.HdrSeqProto — REAL header stages written polymorphically over `[HdrSeq H]`,
and the load-bearing test: does each stage's refinement FOLLOW from the op laws?

This is the header-grain sibling of `Datapath.ByteSeqProto`. Where `ByteSeqProto`
wrote ONE body stage (`servePoly`) over `[ByteSeq T]` and showed its whole
refinement is a `simp` chain over the op laws, this file writes THREE real
deployed header-transform stages over `[HdrSeq H]` and asks the same question at
the header-PAIR grain:

* `securityStagePoly` — the `securityheaders` stage (a FIXED header set folded on;
  the deployed `Reactor.Stage.SecurityHeaders.securityheadersStage`).
* `corsStagePoly` — the `cors` stage (a CONTEXT-conditional allow/deny header;
  the deployed `Reactor.Stage.Cors.corsStage`).
* `hrwStagePoly` — the `header` rewrite stage (STRIP the hop-by-hop set, then SET
  the `Server` header; the deployed `Reactor.Stage.Header.headerStage`, running the
  real `Header.run rewriteProg`). This one exercises the `filter` op.

Each stage is ONE polymorphic expression, and each `<stage>Poly_refines` is a
1–2-line `simp`/`rw` over the op laws (`push_denote`, `filter_denote`) plus the one
generic fold lemma `foldPush_denote` — NO per-stage induction, NO re-expression of
the stage. Each is then GROUNDED in the REAL deployed stage effect (read off the
actual `onResponse` / `Header.run`, not re-specified) and instantiated at both
`List (Bytes × Bytes)` (spec) and `HdrBlock` (fast, genuinely flat).

## The header-grain verdict (see the report at the bottom)

`securityheaders` and `cors` are byte-grain-tractable: a pure `push`-fold, ~4 LOC,
refinement free from `foldPush_denote`. `hrw` adds the `filter` op — which ALSO
goes poly in ~4 LOC (refinement from `filter_denote` + `push_denote`, still no
induction). The one header-grain WRINKLE the byte grain never had: `hrw`'s hop set
is **`dynHopSet`, computed from the header block's OWN `Connection` header** (RFC
9110 §7.6.1), so the polymorphic stage takes that strip-set as a parameter
(denotation-derived). The op *machinery* is unchanged; only the *strip-set
argument* is data-dependent — a bounded, named residual, not a wall.
-/

namespace Datapath.HdrSeqProto

open Proto (Bytes)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Reactor.Pipeline (Ctx ResponseBuilder)
open Reactor (Response)

/-! ## 1. `securityheaders` — a fixed header set (the simplest header stage) -/

open Reactor.Stage.SecurityHeaders (securityheadersStage wireHeaders policy)
open Datapath.FlatStage (securityStage_headers_effect)

/-- **The `securityheaders` stage, written ONCE over `[HdrSeq H]`.** Fold the fixed
security-header set (`wireHeaders policy` — the REAL rendered HSTS / X-Frame-Options
/ … set) onto the header block with `push`. -/
def securityStagePoly {H : Type} [HdrSeq H] (h : H) : H :=
  foldPush (wireHeaders policy) h

/-- **The whole-stage refinement — FOLLOWS from the op laws.** The dense stage's
denotation equals the stage run at the spec instance on the denoted input. Proven
polymorphically in `H`; discharged by `simp` over `foldPush_denote` (⇐ `push_denote`)
— one line, no per-stage induction. -/
theorem securityStagePoly_refines {H : Type} [HdrSeq H] (h : H) :
    HdrSeq.toHdrs (securityStagePoly h)
      = securityStagePoly (H := List (Bytes × Bytes)) (HdrSeq.toHdrs h) := by
  simp only [securityStagePoly, foldPush_denote, foldPush_list]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance of the
once-proven polymorphic theorem, no `HdrBlock`-specific reasoning. -/
theorem securityStageBlock_refines (h : HdrBlock) :
    HdrBlock.denote (securityStagePoly h)
      = securityStagePoly (H := List (Bytes × Bytes)) h.denote :=
  securityStagePoly_refines h

/-- **Grounded in the REAL deployed stage (non-vacuous).** The poly stage at the
spec instance computes exactly the deployed `securityheadersStage.onResponse`'s net
header effect — `securityStage_headers_effect` reads that effect off the actual
stage (`b.build.headers ++ wireHeaders policy`); the poly stage equals it. -/
theorem securityStagePoly_eq_deployed (c : Ctx) (b : ResponseBuilder) :
    securityStagePoly (H := List (Bytes × Bytes)) b.build.headers
      = ((securityheadersStage.onResponse c b).build).headers := by
  rw [securityStage_headers_effect, securityStagePoly, foldPush_list]

/-! ## 2. `cors` — a context-conditional allow/deny header -/

open Reactor.Stage.Cors (corsStage allowedCtx)
open Datapath.FlatStage_cors (corsHeaders corsStage_headers_effect)

/-- **The `cors` stage, written ONCE over `[HdrSeq H]`.** Fold the
context-conditional header list `corsHeaders c` (the singleton
`Access-Control-Allow-Origin` pair when the deployed policy admits the origin, `[]`
when it denies — read off the REAL `corsStage.onResponse` allow/deny branch) onto
the header block with `push`. -/
def corsStagePoly {H : Type} [HdrSeq H] (c : Ctx) (h : H) : H :=
  foldPush (corsHeaders c) h

/-- **The whole-stage refinement — FOLLOWS from the op laws.** Same one-line
`simp` over `foldPush_denote`; the context `c` is an external parameter, so the
allow/deny logic needs NO special handling. -/
theorem corsStagePoly_refines {H : Type} [HdrSeq H] (c : Ctx) (h : H) :
    HdrSeq.toHdrs (corsStagePoly c h)
      = corsStagePoly (H := List (Bytes × Bytes)) c (HdrSeq.toHdrs h) := by
  simp only [corsStagePoly, foldPush_denote, foldPush_list]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance. -/
theorem corsStageBlock_refines (c : Ctx) (h : HdrBlock) :
    HdrBlock.denote (corsStagePoly c h)
      = corsStagePoly (H := List (Bytes × Bytes)) c h.denote :=
  corsStagePoly_refines c h

/-- **Grounded in the REAL deployed stage (non-vacuous).** The poly stage at the
spec instance computes exactly the deployed `corsStage.onResponse`'s net header
effect (`corsStage_headers_effect`: `b.build.headers ++ corsHeaders c`, its
allow/deny branch). -/
theorem corsStagePoly_eq_deployed (c : Ctx) (b : ResponseBuilder) :
    corsStagePoly (H := List (Bytes × Bytes)) c b.build.headers
      = ((corsStage.onResponse c b).build).headers := by
  rw [corsStage_headers_effect, corsStagePoly, foldPush_list]

/-! ## 3. `header` rewrite — STRIP the hop set, then SET `Server` (the `filter` op) -/

open Reactor.Stage.Header (serverName serverVal rewriteProg rewriteResp toFields fromFields baseResp)
open Header (isHop nameEqb dynHopSet)

/-- **The `header` rewrite stage, written ONCE over `[HdrSeq H]`.** Strip the
hop-by-hop set `hop` (`filter` keeping the non-hop pairs), then remove any prior
`Server` header (`filter` keeping `name ≠ Server`), then `push` the `Server` pair —
exactly `Header.run [.hopDyn, .set serverName serverVal]` (`set n v = remove n · ++
[⟨n,v⟩]`, `remove`/`strip` = `filter`). The hop set `hop` is a PARAMETER: the
deployed stage passes `dynHopSet` of the message's own headers (the wrinkle; see
`hrwStagePoly_eq_deployed`). -/
def hrwStagePoly {H : Type} [HdrSeq H] (hop : List Bytes) (h : H) : H :=
  HdrSeq.push
    (HdrSeq.filter
      (HdrSeq.filter h (fun nv => !isHop hop nv.1))
      (fun nv => !nameEqb nv.1 serverName))
    (serverName, serverVal)

/-- The stage at the spec instance is exactly the nested `List.filter`s + append —
the `List` normal form (`push@List = · ++ [·]`, `filter@List = List.filter`). No
separate spec expression is written; this is `hrwStagePoly` at `H := List _`. -/
theorem hrwStagePoly_list (hop : List Bytes) (l : List (Bytes × Bytes)) :
    hrwStagePoly (H := List (Bytes × Bytes)) hop l
      = ((l.filter (fun nv => !isHop hop nv.1)).filter (fun nv => !nameEqb nv.1 serverName))
        ++ [(serverName, serverVal)] := rfl

/-- **The whole-stage refinement — FOLLOWS from the op laws.** Discharged by `simp`
over `push_denote` + `filter_denote` (each `@[simp]`) — the `filter`/strip op needs
NO more than a `simp`, exactly like `push`. No per-stage induction. -/
theorem hrwStagePoly_refines {H : Type} [HdrSeq H] (hop : List Bytes) (h : H) :
    HdrSeq.toHdrs (hrwStagePoly hop h)
      = hrwStagePoly (H := List (Bytes × Bytes)) hop (HdrSeq.toHdrs h) := by
  rw [hrwStagePoly, hrwStagePoly_list]
  simp only [HdrSeq.push_denote, HdrSeq.filter_denote]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance. -/
theorem hrwStageBlock_refines (hop : List Bytes) (h : HdrBlock) :
    HdrBlock.denote (hrwStagePoly hop h)
      = hrwStagePoly (H := List (Bytes × Bytes)) hop h.denote :=
  hrwStagePoly_refines hop h

/-! ### Grounding `hrw` in the REAL `Header.run` (the strip/set bridge) -/

/-- Generic map/filter fusion across a name-preserving field embedding: filtering
the embedded list on a name-predicate is embedding the list filtered on the pair's
first component. Proven once; both `strip` and `remove` bridges instantiate it. -/
private theorem map_filter_name {g : (Bytes × Bytes) → Header.Field}
    (hn : ∀ nv, (g nv).name = nv.1) (q : Bytes → Bool) (l : List (Bytes × Bytes)) :
    (l.map g).filter (fun f => q f.name) = (l.filter (fun nv => q nv.1)).map g := by
  induction l with
  | nil => rfl
  | cons nv rest ih =>
    simp only [List.map_cons, List.filter_cons, hn]
    by_cases h : q nv.1 <;> simp [h, ih]

/-- `strip` commutes with `toFields`: stripping the hop set on the field view of a
pair list is the field view of `filter`-ing the pair list on the same
name-predicate. -/
theorem strip_toFields (hop : List Bytes) (hs : List (Bytes × Bytes)) :
    Header.strip hop (toFields hs) = toFields (hs.filter (fun nv => !isHop hop nv.1)) :=
  map_filter_name (g := fun nv => ⟨nv.1, nv.2⟩) (fun _ => rfl) (fun nm => !isHop hop nm) hs

/-- `remove` commutes with `toFields`. -/
theorem remove_toFields (n : Bytes) (hs : List (Bytes × Bytes)) :
    Header.remove n (toFields hs) = toFields (hs.filter (fun nv => !nameEqb nv.1 n)) :=
  map_filter_name (g := fun nv => ⟨nv.1, nv.2⟩) (fun _ => rfl) (fun nm => !nameEqb nm n) hs

/-- `fromFields` distributes over append. -/
theorem fromFields_append (a b : Header.Headers) :
    fromFields (a ++ b) = fromFields a ++ fromFields b := by
  simp [fromFields]

/-- `fromFields ∘ toFields = id` — the field view round-trips (Prod eta). -/
theorem fromFields_toFields (hs : List (Bytes × Bytes)) :
    fromFields (toFields hs) = hs := by
  induction hs with
  | nil => rfl
  | cons nv rest ih =>
    have e : fromFields (toFields (nv :: rest)) = nv :: fromFields (toFields rest) := rfl
    rw [e, ih]

/-- **Grounded in the REAL deployed stage (non-vacuous).** With the hop set taken
to be the message's `dynHopSet` (exactly what the deployed `.hopDyn` uses), the
poly stage at the spec instance computes precisely `(rewriteResp r).headers` — the
header block the deployed `header` stage yields, running the real
`Header.run rewriteProg`. Grounded on `Header.run` / `set` / `strip`, not
re-specified. -/
theorem hrwStagePoly_eq_deployed (r : Response) :
    hrwStagePoly (H := List (Bytes × Bytes)) (dynHopSet (toFields r.headers)) r.headers
      = (rewriteResp r).headers := by
  have hrun : Header.run rewriteProg (toFields r.headers)
      = Header.set serverName serverVal
          (Header.strip (dynHopSet (toFields r.headers)) (toFields r.headers)) := by
    show Header.run [Header.Op.hopDyn, Header.Op.set serverName serverVal] (toFields r.headers) = _
    rw [Header.run_hopDyn_cons, Header.run_cons, Header.run_nil]
    rfl
  show hrwStagePoly (H := List (Bytes × Bytes)) _ r.headers
      = fromFields (Header.run rewriteProg (toFields r.headers))
  rw [hrwStagePoly_list, hrun, Header.set, strip_toFields, remove_toFields,
    fromFields_append, fromFields_toFields]
  rfl

/-! ## Non-vacuity — the flat ops genuinely compute the REAL deployed effects -/

open Datapath.FlatHeaders (HdrBlock)

-- securityheaders: the flat `HdrBlock` stage produces the deployed header block.
#guard (securityStagePoly (HdrBlock.ofList [("X-A".toUTF8.toList, "1".toUTF8.toList)])).denote
        == [("X-A".toUTF8.toList, "1".toUTF8.toList)] ++ wireHeaders policy

-- cors: the flat stage at the ALLOWED context lands the real ACAO header.
#guard (corsStagePoly allowedCtx (HdrBlock.ofList [("X-A".toUTF8.toList, "1".toUTF8.toList)])).denote
        == [("X-A".toUTF8.toList, "1".toUTF8.toList)] ++ corsHeaders allowedCtx

-- cors depends on the decision: allowed ≠ denied (ACAO present vs absent).
#guard (corsStagePoly allowedCtx (HdrBlock.ofList [])).denote
        != (corsStagePoly { input := [], req := { headers := [] } } (HdrBlock.ofList [])).denote

-- hrw: the flat `HdrBlock` rewrite stage, with the real `dynHopSet`, computes the
-- deployed `rewriteResp` header block on a concrete `Connection: close` response —
-- the hop header stripped, `Server` set — evaluated by the kernel.
#guard (hrwStagePoly (dynHopSet (toFields baseResp.headers)) (HdrBlock.ofList baseResp.headers)).denote
        == (rewriteResp baseResp).headers

-- hrw genuinely rewrites: the flat output differs from the input (hop stripped).
#guard (hrwStagePoly (dynHopSet (toFields baseResp.headers)) (HdrBlock.ofList baseResp.headers)).denote
        != baseResp.headers

-- Spec instance and flat instance agree on a concrete input (the refinement, run).
#guard (securityStagePoly (HdrBlock.ofList [("H".toUTF8.toList, "v".toUTF8.toList)])).denote
        == securityStagePoly (H := List (Bytes × Bytes)) [("H".toUTF8.toList, "v".toUTF8.toList)]

-- Every HdrSeq op is non-vacuous at the flat HdrBlock instance.
#guard (HdrSeq.toHdrs (HdrSeq.push (HdrBlock.ofList []) ("a".toUTF8.toList, "b".toUTF8.toList)))
        == [("a".toUTF8.toList, "b".toUTF8.toList)]
#guard (HdrSeq.toHdrs (HdrSeq.filter (HdrBlock.ofList [("a".toUTF8.toList, "1".toUTF8.toList), ("b".toUTF8.toList, "2".toUTF8.toList)])
          (fun nv => nv.1 == "a".toUTF8.toList)))
        == [("a".toUTF8.toList, "1".toUTF8.toList)]
#guard (HdrSeq.toHdrs (HdrSeq.empty : HdrBlock)) == ([] : List (Bytes × Bytes))

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms foldPush_denote
#print axioms securityStagePoly_refines
#print axioms securityStagePoly_eq_deployed
#print axioms corsStagePoly_refines
#print axioms corsStagePoly_eq_deployed
#print axioms hrwStagePoly_refines
#print axioms hrwStagePoly_eq_deployed

end Datapath.HdrSeqProto
