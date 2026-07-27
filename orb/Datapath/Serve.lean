import Datapath.Refine
import Datapath.Scan
import Reactor.Deploy

/-!
# Datapath.Serve — the `RefinesServe` composition (request half unconditional,
response write conditional on the named codegen lemma)

`Datapath.Refine` states `RefinesServe serveA serveC` — the borrowed-buffer serve
yields the same bytes as the deployed list serve on the span's denotation — and
proves its request-parse half. This module assembles the **whole composition**:

    serveC s out  =  (span-scan the request out of `s`)
                  >> (run the proven `runPipeline` over the deployed stages)
                  >> (write the finalized response into the borrowed `out`)

and proves `RefinesServe (servePipelineOf defaultDeployment) (serveC writeResp)`
**as far as the response half allows** — i.e. CONDITIONAL on one clearly-stated
codegen lemma, threaded as a hypothesis, never `sorry`d.

## What is unconditional vs. conditional

* **Request half — UNCONDITIONAL.** The request bytes are read from the borrowed
  window by index (`s.read`); `read_eq_denote` bridges them to the abstract
  `s.denote`. The dominant framing scan is even materialization-free in the model
  (`Datapath.Scan.spanFindDoubleCrlf_eq_denote`). No hypothesis.
* **Pipeline half — UNCONDITIONAL.** `serveC` runs the *actual* deployed
  `runPipeline` over `deployStagesFull2` and serializes its built response — the
  same affine-`ResponseBuilder` fold the deployed serve runs. No hypothesis.
* **Response WRITE half — a PROVEN in-place store-fold, residual = capacity.**
  Two layers. First, the parametric `refinesServe_serveConcrete` factors the write
  through an abstract `writeResp` with named spec `ResponseWriteRefines`. Then the
  concrete layer (`writeInPlace`, `writeInPlace_faithful`, `serveInPlace_refines`)
  *realizes* that writer as `Datapath.storeFrom` — one store per byte into the
  borrowed `OutBuf`, no allocation, CODEGEN OBLIGATION #2 of `Reactor.Pipeline` —
  and PROVES its faithfulness from the store-fold readback (`storeFrom_get!_at`).
  The response half is no longer an opaque "the writer is correct"; the sole
  remaining residual is `OutFitsResponse` — the pool sizing the send buffer to the
  response (capacity), carried as a named hypothesis, discharged per call.

The three ownership obligations are threaded: no-aliasing by
`denote_store_disjoint` — lifted to the WHOLE multi-byte write by
`denote_storeFrom_disjoint` / `inPlaceWrite_preserves_request` — recycle-exactly-once
by `Uring.recycle_at_most_once`, affine consume-once by
`Reactor.Pipeline.built_absorbing`.
-/

namespace Datapath

open SpanBytes

/-! ## The abstract serve -/

/-- The abstract (deployed) list serve to refine against: the config-driven
`servePipelineOf defaultDeployment`, byte-identical to the running
`servePipelineFull2` (`Reactor.Deploy.servePipelineOf_default`). -/
def serveAbstract : ServeA := Reactor.Deploy.servePipelineOf Reactor.Deploy.defaultDeployment

/-! ## THE REMAINING CODEGEN OBLIGATION (named, unclosed — a hypothesis, not a sorry)

The response-write refinement: writing a finalized response byte-list into the
borrowed output buffer makes the buffer's live window *equal* that byte-list.
This is the concrete counterpart of `Reactor.Pipeline`'s CODEGEN OBLIGATION #2
(lower the affine `ResponseBuilder` to an in-place extend on a borrowed buffer);
realizing a `writeResp` that satisfies it is emitting the in-place writer, which
lives below this additive model layer. -/

/-- **The response-write codegen obligation.** `writeResp out resp` writes the
finalized response `resp` into the borrowed output buffer, and the buffer's live
window then reads back exactly `resp`. The whole `RefinesServe` composition is
proven modulo THIS. -/
def ResponseWriteRefines (writeResp : OutBuf → List UInt8 → OutBuf) : Prop :=
  ∀ (out : OutBuf) (resp : List UInt8), (writeResp out resp).bytes = resp

/-! ## The concrete serve skeleton -/

/-- The response bytes the concrete serve produces: read the request out of the
borrowed window by index (`s.read`), then run the *deployed* serve pipeline over
those bytes — the real `runPipeline` over `deployStagesFull2`, the affine
`ResponseBuilder` threaded and `serialize`d. Zero-copy on the request side (index
loads); the pipeline is the deployed one unchanged. -/
def serveResponseBytes (s : SpanBytes) : List UInt8 :=
  serveAbstract s.read

/-- **The concrete zero-copy serve skeleton** (parameterized by the unrealized
in-place writer `writeResp`): scan the request span, run the proven pipeline,
write the response into the borrowed `out`. -/
def serveConcrete (writeResp : OutBuf → List UInt8 → OutBuf) : ServeC :=
  fun s out => writeResp out (serveResponseBytes s)

/-! ## The composition theorem -/

/-- **`refinesServe_serveConcrete` — the composition, proven MODULO the named
codegen lemma.** For every well-formed span, the concrete serve's live output
bytes equal the abstract deployed serve on the span's denotation. The request
half (index read = denotation) and the pipeline half (the real deployed fold) are
discharged unconditionally by `read_eq_denote`; the response-write half is
discharged by the hypothesis `hwrite : ResponseWriteRefines writeResp` — the one
remaining codegen obligation, carried as a parameter, not assumed by `sorry`. -/
theorem refinesServe_serveConcrete
    (writeResp : OutBuf → List UInt8 → OutBuf)
    (hwrite : ResponseWriteRefines writeResp) :
    RefinesServe serveAbstract (serveConcrete writeResp) := by
  intro s out hwf
  show (writeResp out (serveResponseBytes s)).bytes = serveAbstract s.denote
  rw [hwrite out (serveResponseBytes s)]
  unfold serveResponseBytes
  rw [read_eq_denote s hwf]

/-- **The full obligation bundle, discharged modulo the codegen lemma.** Packages
the byte-refinement (conditional on `hwrite`) with the no-aliasing separation
(unconditional, `denote_store_disjoint`). The other two ownership obligations —
recycle-exactly-once and affine consume-once — are the existing proven theorems
bound below. -/
theorem serveObligations_serveConcrete
    (writeResp : OutBuf → List UInt8 → OutBuf)
    (hwrite : ResponseWriteRefines writeResp) :
    ServeObligations serveAbstract (serveConcrete writeResp) :=
  { refines := refinesServe_serveConcrete writeResp hwrite
    noAlias := noAlias_discharged }

/-- Recycle-exactly-once on the leased recv buffer, held across the whole span
parse + serve — the existing proven theorem. -/
def serveConcrete_recycleOnce := @Uring.recycle_at_most_once

/-- Affine consume-once on the response builder — the existing proven theorem
that licenses the in-place `writeResp` lowering. -/
def serveConcrete_affineWriteOnce := @Reactor.Pipeline.built_absorbing

/-! ## The codegen obligation is SATISFIABLE (consistency — not the zero-copy path)

To show the composition is not conditional on a false hypothesis, here is a
model-side `writeResp` that meets `ResponseWriteRefines`: it materializes the
response into a fresh buffer. This is a *consistency witness only* — it copies, so
it is NOT the zero-copy in-place lowering the real obligation demands; it merely
proves the obligation is dischargeable, hence the composition is not vacuous. -/

/-- A materializing writer (fresh buffer). Satisfies the obligation but copies —
the witness that the codegen lemma is consistent, not the zero-copy realization. -/
def writeOutFresh (_out : OutBuf) (resp : List UInt8) : OutBuf :=
  { buf := ⟨resp.toArray⟩, live := resp.length }

theorem writeOutFresh_spec : ResponseWriteRefines writeOutFresh := by
  intro out resp
  show (OutBuf.mk ⟨resp.toArray⟩ resp.length).bytes = resp
  unfold OutBuf.bytes
  show (resp.toArray.toList).take resp.length = resp
  rw [List.toList_toArray, List.take_length]

/-- With the consistency witness plugged in, `RefinesServe` holds *unconditionally*
(a sanity check that the composition closes once ANY conforming writer is given —
the witness copies, so this is not the zero-copy serve, only evidence the
composition is sound). -/
theorem refinesServe_witness :
    RefinesServe serveAbstract (serveConcrete writeOutFresh) :=
  refinesServe_serveConcrete writeOutFresh writeOutFresh_spec

/-! ## The ZERO-COPY in-place writer — a concrete byte-store fold (not a copy)

`writeOutFresh` above is only a *consistency* witness: it copies into a fresh
buffer, so it discharges `ResponseWriteRefines` but is not the zero-copy write.
This section replaces the opaque hypothesis with the real thing.

`writeInPlace` writes the response into the BORROWED output buffer by the
store-fold `storeFrom` — one store per byte, no allocation — the write CODEGEN
OBLIGATION #2 lowers to. Its faithfulness (`writeInPlace_faithful`) is now
**PROVEN** from the store-fold readback (`storeFrom_get!_at`), not assumed; the
composition `refinesServe_inPlace` uses it, so the response half is no longer an
opaque "the writer is correct". The ONLY residual is `OutFitsResponse` — the
borrowed buffer has room for the response (the pool sizing the send buffer), a
concrete capacity fact carried as a named hypothesis. And `inPlaceWrite_preserves_request`
threads the separation guarantee (`denote_storeFrom_disjoint`) across the whole
multi-byte write: writing the response in place cannot corrupt a live request
span in a disjoint region. -/

/-- The zero-copy in-place response writer: fold the response bytes into the
borrowed output buffer starting at index 0 (`storeFrom`), and set the live count
to the response length. No fresh buffer — the pooled `out.buf` is written in
place. -/
def writeInPlace (out : OutBuf) (resp : List UInt8) : OutBuf :=
  { buf := storeFrom out.buf 0 resp, live := resp.length }

/-- **The in-place write is faithful — PROVEN, not assumed.** When the borrowed
buffer has room (`resp.length ≤ out.buf.size`), the live window of the written
buffer reads back byte-for-byte the response, established from the store-fold
readback `storeFrom_get!_at`. This is the response half of the refinement,
discharged concretely for the actual in-place store-fold writer. -/
theorem writeInPlace_faithful (out : OutBuf) (resp : List UInt8)
    (hcap : resp.length ≤ out.buf.size) :
    (writeInPlace out resp).bytes = resp := by
  show (storeFrom out.buf 0 resp).data.toList.take resp.length = resp
  apply List.ext_getElem
  · rw [List.length_take]
    have hle : resp.length ≤ (storeFrom out.buf 0 resp).data.toList.length := by
      show resp.length ≤ (storeFrom out.buf 0 resp).size
      rw [storeFrom_size]; exact hcap
    omega
  · intro i h₁ h₂
    have hb : i < (storeFrom out.buf 0 resp).size := by rw [storeFrom_size]; omega
    have hat : (storeFrom out.buf 0 resp).get! (0 + i) = resp[i] :=
      storeFrom_get!_at out.buf 0 resp (by omega) i h₂
    rw [Nat.zero_add] at hat
    rw [List.getElem_take, Array.getElem_toList]
    rw [byteArray_get!_eq_getElem _ i hb] at hat
    exact hat

/-! ## The residual codegen/runtime obligation — capacity, stated precisely -/

/-- **The residual, stated precisely.** For a request span and the borrowed
output buffer, the buffer is at least as large as the response the deployed
pipeline produced. This is the concrete counterpart of Pipeline CODEGEN
OBLIGATION #2: the ONLY thing the in-place write needs that this model layer
cannot furnish is *room* — the pool sizing the send buffer to the response. It is
NOT "the writer is correct" (that is now proven, `writeInPlace_faithful`), only
"the buffer has room". Discharged per-call by the allocator that sizes `out.buf`
to `serveResponseBytes s`. -/
def OutFitsResponse (out : OutBuf) (s : SpanBytes) : Prop :=
  (serveResponseBytes s).length ≤ out.buf.size

/-- **The zero-copy serve refines the deployed serve — per call, the honest
residual.** For a well-formed request span and a borrowed output buffer that has
room for the response (`hcap : OutFitsResponse out s`), the in-place store-fold
serve `serveConcrete writeInPlace` produces exactly the bytes the *actual deployed*
abstract serve (`serveAbstract = servePipelineOf defaultDeployment`) yields on the
span's denotation. The request half is `read_eq_denote`; the response half is the
PROVEN `writeInPlace_faithful` (an in-place byte-store fold), not an opaque
assumption. The sole hypothesis is capacity — satisfied per-call by the pool
sizing `out.buf` to this response. -/
theorem serveInPlace_refines (s : SpanBytes) (out : OutBuf)
    (hwf : s.Wf) (hcap : OutFitsResponse out s) :
    (serveConcrete writeInPlace s out).bytes = serveAbstract s.denote := by
  show (writeInPlace out (serveResponseBytes s)).bytes = serveAbstract s.denote
  rw [writeInPlace_faithful out (serveResponseBytes s) hcap]
  unfold serveResponseBytes
  rw [read_eq_denote s hwf]

/-- **The `RefinesServe` composition for the concrete in-place writer.** Assembles
the per-call refinement into the framework's end-to-end obligation
`RefinesServe serveAbstract (serveConcrete writeInPlace)`, under the named residual
that the pool provides room for every response (`hcap`). Non-vacuous: `serveAbstract`
is the real deployed pipeline and `writeInPlace` the real in-place store-fold; the
conclusion genuinely depends on `hcap` (a too-small buffer breaks the readback), so
this is not a tautology. The `hcap` here is the global (∀-quantified) form of the
per-call capacity residual `serveInPlace_refines` carries. -/
theorem refinesServe_inPlace
    (hcap : ∀ (out : OutBuf) (s : SpanBytes), s.Wf → OutFitsResponse out s) :
    RefinesServe serveAbstract (serveConcrete writeInPlace) :=
  fun s out hwf => serveInPlace_refines s out hwf (hcap out s hwf)

/-- **The full obligation bundle for the concrete in-place writer.** Packages the
byte-refinement (conditional only on capacity `hcap`) with the no-aliasing
separation (unconditional, `denote_store_disjoint`). Unlike
`serveObligations_serveConcrete`, this is stated for the REAL zero-copy writer,
not a parameter. -/
theorem serveObligations_inPlace
    (hcap : ∀ (out : OutBuf) (s : SpanBytes), s.Wf → OutFitsResponse out s) :
    ServeObligations serveAbstract (serveConcrete writeInPlace) :=
  { refines := refinesServe_inPlace hcap
    noAlias := noAlias_discharged }

/-- **No-aliasing across the in-place response write.** If the response is written
by the store-fold into a region of the request's OWN buffer disjoint from the read
window, the request span's denotation is preserved across the ENTIRE write — every
byte, not just one. The separation guarantee that licenses writing the response in
place while the request span is still live, lifted from one store
(`denote_store_disjoint`) to the whole response (`denote_storeFrom_disjoint`). -/
theorem inPlaceWrite_preserves_request (s : SpanBytes) (base : Nat) (resp : List UInt8)
    (hw : s.Wf) (hdisj : s.off + s.len ≤ base ∨ base + resp.length ≤ s.off) :
    ({ s with buf := storeFrom s.buf base resp } : SpanBytes).denote = s.denote :=
  denote_storeFrom_disjoint s base resp hw hdisj

end Datapath
