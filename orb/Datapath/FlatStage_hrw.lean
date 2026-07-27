import Datapath.FlatHeaders
import Reactor.Deploy

/-!
# Datapath.FlatStage_hrw — the deployed `headerRewrite` stage proven flat,
byte-identical to its deployed `List` form.

The `headerRewrite` stage (`Reactor.Deploy.headerRewriteStage`, position 8 of the
14 in `Reactor.Deploy.deployStagesFull2`) is a RESPONSE transform: on the response
phase it applies the REAL `Header.run` rewrite under the deployed program
`deployProg (deployPlan (deploySubs c.input)) c.input`
(`Lifecycle.stdRewrite` — strip the RFC 9110 §7.6.1 hop-by-hop set, install
`Server` — then stamp the proxy/DNS-chosen `x-upstream` and the `Trace` `x-corr`
correlation id) through the affine builder's `mapResp`.

Unlike `securityheaders` (`Datapath.FlatStage`) and `cors` (`FlatStage_cors`),
which are pure header APPENDS (`· ++ xs`), `headerRewrite` genuinely SETs and
REMOVEs headers: `Header.run` folds `Header.applyOp`, whose steps are
`set`/`remove`/`add`/`hop`/`hopDyn` — a `List.filter` (remove/strip) and a
`List.++ [nv]` (add/set-append) on the header block. So this stage does not fit
the pure-append `refinesHdr_foldAddHeader` recipe; instead it needs the flat
sibling of the whole `Header.run` interpreter — the "push/remove fold on
`HdrBlock`" the scope named. That is what is built here:

* `flatApplyOp` / `flatRun` — the flat sibling of `Header.applyOp` / `Header.run`,
  interpreting a rewrite program directly on the flat `HdrBlock`: `remove`/`strip`
  are `Array.filter` (no per-op cons-spine copy), `add`/`set` an `Array.push`
  (amortized `O(1)`), `hopDyn` reads its strip set from the current headers and
  `Array.filter`s. The big per-stage work — walking and rebuilding the header
  block — is flat; only the small `Connection`-nominated hop-name set is read as a
  `List`.

## What is proven here (equality-transfer, NOT a re-spec)

* `hrwStage_headers_effect` — the DEPLOYED stage's net effect on the built
  response header block is exactly `hrwFn (progOf c) hs`, read off the real
  `headerRewriteStage.onResponse` (its `mapResp (Lifecycle.rewriteResp …)`) via
  `Reactor.Pipeline.build_mapResp`. This grounds the flat form in the ACTUAL
  deployed function; the effect is not re-specified — `progOf c` is the real
  `deployProg (deployPlan (deploySubs c.input)) c.input`.
* `flatHrwStage` + `flatHrwStage_refines` — the flat interpreter runs on the flat
  `HdrBlock` and is proven to compute the SAME header effect
  (`RefinesHdrFn (hrwFn prog)`), via the per-op naturality `flatRun_denote`.
  Non-vacuous: the flat ops genuinely filter and push (`hopDyn` strips
  `Connection`, `set serverName` installs `Server`); the content is proven equal,
  not assumed.
* `flatHrwStage_matches_deployed` — the money theorem: the flat interpreter over
  the DEPLOYED program, run on the deployed stage's incoming header block, denotes
  to EXACTLY the deployed stage's built header block. Flat = deployed, byte-for-byte.
* `flatHrwStage_render_byte_identical` — the header-grain refinement composed with
  the byte-grain flat renderer (`RefinesHdrFn.compRender`): the flat stage's
  rendered header bytes are byte-identical to `Reactor.renderHeaders` of the
  deployed stage's header block.
* `flatHrw_serialize_refines` — the full serialized response of the flat stage is
  byte-identical to `Reactor.serialize` of the deployed stage's response, chaining
  the header-block refinement into the derived flat serializer
  `Datapath.ByteRefine.flatSerialize`.

Mirrors `Datapath.FlatStage` end-to-end; the difference is that the flat header
transform is the `Header.run` interpreter (filter + push), not a fixed append.
-/

namespace Datapath.FlatStage_hrw

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_mapResp)
open Reactor.Deploy (headerRewriteStage deployProg deployPlan deploySubs)
open Reactor.Lifecycle (rewriteResp toHeaders ofHeaders)
open Datapath.FlatHeaders
open Datapath.Refinement

/-! ## 0. `toHeaders` / `ofHeaders` are inverse coercions, and distribute -/

/-- The header ↔ field coercions are inverse: `ofHeaders ∘ toHeaders = id`. -/
theorem ofHeaders_toHeaders (hs : List (Bytes × Bytes)) :
    ofHeaders (toHeaders hs) = hs := by
  have hid : (fun f : Header.Field => (f.name, f.value))
      ∘ (fun p : Bytes × Bytes => (⟨p.1, p.2⟩ : Header.Field)) = id := by
    funext x; rfl
  unfold ofHeaders toHeaders
  rw [List.map_map, hid, List.map_id]

/-- `toHeaders` distributes over append. -/
theorem toHeaders_append (a b : List (Bytes × Bytes)) :
    toHeaders (a ++ b) = toHeaders a ++ toHeaders b := by
  unfold toHeaders; rw [List.map_append]

/-- `toHeaders` of a single pair is the single field. -/
theorem toHeaders_singleton (nv : Bytes × Bytes) :
    toHeaders [nv] = [⟨nv.1, nv.2⟩] := rfl

/-- A name-keyed flat `filter` matches `Header.remove` under the coercion: filtering
the flat pairs by name equals `Header.remove` on the coerced field list. This is
the `filter`/`map` interchange (`List.filter_map`) at the header grain. -/
theorem toHeaders_filter_name (n : Header.Name) (hs : List (Bytes × Bytes)) :
    toHeaders (hs.filter (fun nv => !Header.nameEqb nv.1 n))
      = Header.remove n (toHeaders hs) := by
  unfold Header.remove toHeaders
  rw [List.filter_map]
  rfl

/-- A hop-set-keyed flat `filter` matches `Header.strip` under the coercion. -/
theorem toHeaders_filter_hop (names : List Header.Name) (hs : List (Bytes × Bytes)) :
    toHeaders (hs.filter (fun nv => !Header.isHop names nv.1))
      = Header.strip names (toHeaders hs) := by
  unfold Header.strip toHeaders
  rw [List.filter_map]
  rfl

/-! ## 1. The flat rewrite interpreter — the flat sibling of `Header.run` -/

/-- **The flat sibling of `Header.applyOp`.** Interpret one rewrite operation
directly on the flat `HdrBlock`: `remove`/`hop` are `Array.filter` (drop the
matching pairs, no per-op cons-spine copy); `add` is `Array.push`; `set` is
`Array.filter` then `Array.push` (drop the prior field, append the new one);
`hopDyn` reads its dynamic strip set (`Header.dynHopSet`, the fixed table plus the
`Connection`-nominated names) from the CURRENT headers, then `Array.filter`s. The
big work — rebuilding the header block — is flat; only the small hop-name set is a
`List` read. -/
def flatApplyOp (o : Header.Op) (h : HdrBlock) : HdrBlock :=
  match o with
  | .set n v   => ⟨(h.headers.filter (fun nv => !Header.nameEqb nv.1 n)).push (n, v)⟩
  | .remove n  => ⟨h.headers.filter (fun nv => !Header.nameEqb nv.1 n)⟩
  | .add n v   => ⟨h.headers.push (n, v)⟩
  | .hop names => ⟨h.headers.filter (fun nv => !Header.isHop names nv.1)⟩
  | .hopDyn    =>
      ⟨h.headers.filter (fun nv => !Header.isHop (Header.dynHopSet (toHeaders h.denote)) nv.1)⟩

/-- **The flat sibling of `Header.run`.** Fold the rewrite program over the flat
block. The flat interpreter of the WHOLE `Header.run` program — the "push/remove
fold on `HdrBlock`" the cons-list-removal scope named. -/
def flatRun (prog : List Header.Op) (h : HdrBlock) : HdrBlock :=
  prog.foldl (fun acc o => flatApplyOp o acc) h

/-! ### Per-op and whole-program naturality -/

/-- Denote of a flat `filter` — the flat `Array.filter` denotes to the `List.filter`. -/
theorem denote_filter (h : HdrBlock) (q : (Bytes × Bytes) → Bool) :
    (⟨h.headers.filter q⟩ : HdrBlock).denote = h.denote.filter q := by
  show (h.headers.filter q).toList = h.headers.toList.filter q
  rw [Array.toList_filter]

/-- Denote of a flat `push` — the flat `Array.push` denotes to `List.++ [x]`. -/
theorem denote_push (h : HdrBlock) (x : Bytes × Bytes) :
    (⟨h.headers.push x⟩ : HdrBlock).denote = h.denote ++ [x] := by
  show (h.headers.push x).toList = h.headers.toList ++ [x]
  rw [Array.toList_push]

/-- Denote of a flat `filter` then `push`. -/
theorem denote_filter_push (h : HdrBlock) (q : (Bytes × Bytes) → Bool) (x : Bytes × Bytes) :
    (⟨(h.headers.filter q).push x⟩ : HdrBlock).denote = h.denote.filter q ++ [x] := by
  show ((h.headers.filter q).push x).toList = h.headers.toList.filter q ++ [x]
  rw [Array.toList_push, Array.toList_filter]

/-- **Per-op naturality.** Running the flat op then coercing equals coercing then
running the abstract `Header.applyOp` — the naturality square for one rewrite
operation. Proven case-by-case; each case is a `filter`/`push` denotation plus the
`filter`/`map` interchange. -/
theorem toHeaders_denote_flatApplyOp (o : Header.Op) (h : HdrBlock) :
    toHeaders (flatApplyOp o h).denote = Header.applyOp o (toHeaders h.denote) := by
  cases o with
  | set n v =>
    show toHeaders (⟨(h.headers.filter (fun nv => !Header.nameEqb nv.1 n)).push (n, v)⟩ : HdrBlock).denote
        = Header.set n v (toHeaders h.denote)
    rw [denote_filter_push, toHeaders_append, toHeaders_filter_name, toHeaders_singleton]
    rfl
  | remove n =>
    show toHeaders (⟨h.headers.filter (fun nv => !Header.nameEqb nv.1 n)⟩ : HdrBlock).denote
        = Header.applyOp (.remove n) (toHeaders h.denote)
    rw [denote_filter, toHeaders_filter_name]
    rfl
  | add n v =>
    show toHeaders (⟨h.headers.push (n, v)⟩ : HdrBlock).denote
        = Header.applyOp (.add n v) (toHeaders h.denote)
    rw [denote_push, toHeaders_append, toHeaders_singleton]
    rfl
  | hop names =>
    show toHeaders (⟨h.headers.filter (fun nv => !Header.isHop names nv.1)⟩ : HdrBlock).denote
        = Header.applyOp (.hop names) (toHeaders h.denote)
    rw [denote_filter, toHeaders_filter_hop]
    rfl
  | hopDyn =>
    show toHeaders (⟨h.headers.filter
          (fun nv => !Header.isHop (Header.dynHopSet (toHeaders h.denote)) nv.1)⟩ : HdrBlock).denote
        = Header.applyOp .hopDyn (toHeaders h.denote)
    rw [denote_filter, toHeaders_filter_hop]
    rfl

/-- **Whole-program naturality.** Coercing the flat run equals the abstract
`Header.run` on the coerced input — for ANY program. Induction on the program,
each step the per-op naturality. -/
theorem toHeaders_denote_flatRun (prog : List Header.Op) :
    ∀ h : HdrBlock, toHeaders (flatRun prog h).denote = Header.run prog (toHeaders h.denote) := by
  induction prog with
  | nil => intro h; rfl
  | cons o rest ih =>
    intro h
    show toHeaders (flatRun rest (flatApplyOp o h)).denote = Header.run (o :: rest) (toHeaders h.denote)
    rw [ih (flatApplyOp o h), toHeaders_denote_flatApplyOp, Header.run_cons]

/-- **The flat run denotes to the deployed rewrite effect.** `flatRun prog h`
denotes to exactly `ofHeaders (Header.run prog (toHeaders (denote h)))` — the
function the deployed stage applies to its header block. Equality-transfer through
the inverse coercions; no byte re-reasoning. -/
theorem flatRun_denote (prog : List Header.Op) (h : HdrBlock) :
    (flatRun prog h).denote = ofHeaders (Header.run prog (toHeaders h.denote)) := by
  rw [← toHeaders_denote_flatRun prog h, ofHeaders_toHeaders]

/-! ## 2. The deployed stage's header effect, read off the REAL stage -/

/-- The deployed rewrite program at context `c` — the REAL
`deployProg (deployPlan (deploySubs c.input)) c.input` (`stdRewrite` + the
proxy/DNS `x-upstream` + the `Trace` `x-corr`). -/
def progOf (c : Ctx) : List Header.Op :=
  deployProg (deployPlan (deploySubs c.input)) c.input

/-- The abstract header effect of a rewrite program: run `Header.run` on the
coerced header block and coerce back. This is `(rewriteResp prog r).headers` as a
function of the incoming headers. -/
def hrwFn (prog : List Header.Op) (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  ofHeaders (Header.run prog (toHeaders hs))

/-- **The deployed `headerRewrite` stage's net header effect — grounded, not
re-specified.** For any context and any incoming builder, the BUILT response of
the real `headerRewriteStage.onResponse` has header block `hrwFn (progOf c)
b.build.headers`. Proven directly from the stage's definition (its `onResponse`
is `mapResp (Lifecycle.rewriteResp (deployProg …))`) via the deployed faithfulness
lemma `Reactor.Pipeline.build_mapResp`. This is the function the flat form must
compute. -/
theorem hrwStage_headers_effect (c : Ctx) (b : ResponseBuilder) :
    ((headerRewriteStage.onResponse c b).build).headers
      = hrwFn (progOf c) b.build.headers := by
  show ((b.mapResp (rewriteResp (progOf c))).build).headers = hrwFn (progOf c) b.build.headers
  rw [build_mapResp]
  rfl

/-! ## 3. The flat stage and its refinement (header grain) -/

/-- **The flat `headerRewrite` stage.** Runs the flat `Header.run` interpreter on
the flat `HdrBlock` — the flat sibling of the deployed stage's
`Lifecycle.rewriteResp (deployProg …)`. -/
def flatHrwStage (prog : List Header.Op) : HdrBlock → HdrBlock := flatRun prog

/-- **The flat stage refines the deployed stage's header effect.** `flatHrwStage
prog` computes `hrwFn prog` on the denotation — the exact function
`hrwStage_headers_effect` reads off the deployed stage (at `prog := progOf c`).
Non-vacuous: the flat interpreter genuinely filters and pushes; the content is
proven equal, not assumed. -/
theorem flatHrwStage_refines (prog : List Header.Op) :
    RefinesHdrFn (hrwFn prog) (flatHrwStage prog) :=
  fun h => flatRun_denote prog h

/-- **The money theorem: flat = deployed, byte-for-byte.** The flat interpreter
over the DEPLOYED program `progOf c`, run on the flat form of the deployed stage's
incoming header block, denotes to EXACTLY the deployed stage's built header block. -/
theorem flatHrwStage_matches_deployed (c : Ctx) (b : ResponseBuilder) :
    (flatHrwStage (progOf c) (HdrBlock.ofList b.build.headers)).denote
      = ((headerRewriteStage.onResponse c b).build).headers := by
  rw [flatHrwStage_refines (progOf c) (HdrBlock.ofList b.build.headers),
      HdrBlock.denote_ofList, hrwStage_headers_effect]

/-! ## 4. Byte-identical: the flat stage rendered = the deployed stage rendered -/

/-- **The flat stage's rendered header bytes are byte-identical to the deployed
stage's.** Given any flat block refining the abstract header list `a`, the flat
stage's output rendered through the flat renderer equals
`Reactor.renderHeaders (hrwFn prog a)` — `renderHeaders` of exactly the header
block `hrwStage_headers_effect` produces. This is `RefinesHdrFn.compRender`: the
header-grain stage refinement composed with the byte-grain flat renderer, across
the grain boundary, in one step. -/
theorem flatHrwStage_render_byte_identical (prog : List Header.Op)
    {a : List (Bytes × Bytes)} {h : HdrBlock} (r : RefinesHdr a h) :
    Datapath.Refinement.Refines (Reactor.renderHeaders (hrwFn prog a))
      (flatRenderBlock (flatHrwStage prog h)) :=
  (flatHrwStage_refines prog).compRender r

/-! ## 5. Full serialize: the flat stage's whole response is byte-identical -/

/-- The flat computation of the header-rewrite stage response: accumulate the
header block flat with `flatRun` (filter/push interpreter), then present it for
serialization. The single `denote` (Array → List) at the `Response.headers`
boundary is the named residual seam; the header transform and the serialization
are both flat. -/
def flatHrwResp (prog : List Header.Op) (r : Response) : Response :=
  { r with headers := (flatRun prog (HdrBlock.ofList r.headers)).denote }

/-- The flat header-rewrite response equals the DEPLOYED one (`rewriteResp prog`,
the exact whole-`Response` transform the deployed stage's `mapResp` applies) —
PROVEN via the flat-interpreter naturality, not by definition. -/
theorem flatHrwResp_eq (prog : List Header.Op) (r : Response) :
    flatHrwResp prog r = rewriteResp prog r := by
  have hh : (flatRun prog (HdrBlock.ofList r.headers)).denote
      = ofHeaders (Header.run prog (toHeaders r.headers)) := by
    rw [flatRun_denote, HdrBlock.denote_ofList]
  show { r with headers := (flatRun prog (HdrBlock.ofList r.headers)).denote }
      = { r with headers := ofHeaders (Header.run prog (toHeaders r.headers)) }
  rw [hh]

/-- **THE FULL BYTE-IDENTITY.** The flat header-rewrite stage's whole serialized
response (flat header interpreter ⟶ `Datapath.ByteRefine.flatSerialize`, the
derived flat serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED
stage's response (`rewriteResp prog r`). Chains the header-block refinement
(`flatHrwResp_eq`) into the byte-grain serialize equality (`flatSerialize_refines`). -/
theorem flatHrw_serialize_refines (prog : List Header.Op) (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (rewriteResp prog r))
      (flatSerialize (flatHrwResp prog r)) := by
  rw [flatHrwResp_eq]
  exact flatSerialize_refines (rewriteResp prog r)

/-! ## Non-vacuity — the flat interpreter genuinely computes, witnessed on real
inputs. We use `Lifecycle.stdRewrite` (`[hopDyn, set serverName serverVal]`), the
head of the deployed `deployProg`, over a concrete response carrying a
`Connection: close` hop header and an end-to-end `X-Trace` header, no `Server`. -/

/-- `Connection: close` — a hop-by-hop header the dynamic strip removes. -/
private def connHdr : Bytes × Bytes :=
  ([67, 111, 110, 110, 101, 99, 116, 105, 111, 110], [99, 108, 111, 115, 101])

/-- `X-Trace: 1` — an end-to-end header that must survive. -/
private def xtHdr : Bytes × Bytes := ([88, 45, 84, 114, 97, 99, 101], [49])

/-- A concrete base header block: one hop header, one end-to-end header, no `Server`. -/
private def baseHeaders : List (Bytes × Bytes) := [connHdr, xtHdr]

-- The flat interpreter over the real `stdRewrite` computes EXACTLY the deployed
-- rewrite effect (`hrwFn stdRewrite`) — evaluated by the kernel, not just proven.
#guard (flatRun Reactor.Lifecycle.stdRewrite (HdrBlock.ofList baseHeaders)).denote
        == hrwFn Reactor.Lifecycle.stdRewrite baseHeaders

-- And that effect is the REAL `Header.run` rewrite: the `Connection` hop header is
-- stripped and the `Server` header is installed — the genuine set/remove, evaluated.
#guard (flatRun Reactor.Lifecycle.stdRewrite (HdrBlock.ofList baseHeaders)).denote
        == [xtHdr, (Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal)]

-- The flat interpreter genuinely CHANGES the header bytes (a real transform, not a
-- pass-through / proof-attachment).
#guard (flatRun Reactor.Lifecycle.stdRewrite (HdrBlock.ofList baseHeaders)).denote
        != baseHeaders

-- The flat rendered header bytes of the flat stage equal `renderHeaders` of the
-- deployed rewrite's header block — evaluated across the header→byte grain.
#guard (flatRenderBlock (flatHrwStage Reactor.Lifecycle.stdRewrite (HdrBlock.ofList baseHeaders))).toList
        == Reactor.renderHeaders (hrwFn Reactor.Lifecycle.stdRewrite baseHeaders)

-- The flat op genuinely depends on its input: two different base blocks give
-- different flat rendered bytes (not a constant).
#guard (flatRenderBlock (flatHrwStage Reactor.Lifecycle.stdRewrite (HdrBlock.ofList [connHdr]))).toList
        != (flatRenderBlock (flatHrwStage Reactor.Lifecycle.stdRewrite (HdrBlock.ofList [xtHdr]))).toList

-- The full flat serialized response is byte-identical to the deployed serialize —
-- evaluated on a real `200 OK` carrying the hop header.
#guard (flatSerialize (flatHrwResp Reactor.Lifecycle.stdRewrite
          { Reactor.ok200 "hi".toUTF8.toList with headers := baseHeaders })).data.toList
        == Reactor.serialize (rewriteResp Reactor.Lifecycle.stdRewrite
          { Reactor.ok200 "hi".toUTF8.toList with headers := baseHeaders })

/-! ## REMAINING (the honest residual for this stage)

* **(a) The `Response.headers` `List` seam.** `flatHrwResp` still `denote`s the
  flat `HdrBlock` back to a `List` at the `Reactor.Response.headers` field boundary
  (the deployed `Response` is `List`-typed), exactly as `Datapath.FlatStage`'s
  `flatSecuredResp`. `flatHrwStage_render_byte_identical` shows the header block
  renders flat with NO such materialization; closing it fully is a flat serialize
  variant taking `HdrBlock` directly (additive, shared with every header stage).

* **(b) The `dynHopSet` read.** `flatApplyOp .hopDyn` computes its strip set from
  `toHeaders h.denote` — a `List` read of the (small) `Connection`-nominated hop
  names. The BIG per-stage work — rebuilding the header block — is flat
  (`Array.filter`/`Array.push`); only the tiny hop-name set is a `List` read, which
  a flat `Array`-scan of the `Connection` field would also remove (additive).

* **(c) The deployed program's own inputs.** `progOf c` runs the real proxy/DNS/
  trace passes to build the rewrite program (`deployProg`); those are the request/
  observe seams, unchanged by this slice — this is the RESPONSE header-block half.
-/

end Datapath.FlatStage_hrw
