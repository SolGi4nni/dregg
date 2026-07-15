# TRANSLATOR-ARC — from the data-lowering keystone to one-run-compiles-the-real-serve

Status of grounding: every claim below is checked against the built tree on the
build host. The translator chain
`Sem → Lower → EmitCorrectRegion → EmitCorrectCompose → EmitCorrectLoop →
EmitCorrectClock` and the proof-producing chain `ProofProducing → ServeFragment`
both build GREEN under the canonical Lean 4.30 toolchain
(`~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`), and every keystone
theorem's `#print axioms` is `⊆ {propext, Quot.sound, Classical.choice}` with
**0 `sorry`, no `native_decide`, no `ofReduceBool`**. The clock-accounting wave
in particular certifies `RefinesClk`, `refinesClk_seq/_dec/_conseq`,
`while_inv_cond_clk`, `refinesClk_scanWhile`, `refinesClk_scan_publish`, and
`region_via_clock` all axiom-clean.

This document is the honest sequence from where the proven translator is TODAY
(word-decision stages + one hand-instantiated byte-reading loop, composing under
a uniform clock-accounting grammar) to the destination: **one run of one proven
translator that swallows the REAL response path** — `serialize : Response →
Bytes` and the deployed stage pipeline (`~/dev/drorb/Reactor/Serialize.lean`,
`~/dev/drorb/Reactor/Pipeline.lean`, `~/dev/drorb/Reactor/Stage/*.lean`) — and
returns emitted flat-byte-memory code paired with its machine-checked refinement
certificate, replacing per-stage hand authoring.

---

## 0. Why this is a PIVOT, not more of the same

Everything proven so far certifies **word decisions**. `redirectStatusStage`
picks a status *number* (301/302/307/308). `connLimitDecision` computes a 0/1
*admit word*. `ipfilterDecision`, `bodyLimitDecision`, `methodFilterDecision`,
`securityHeadersDecision` all end in `result := <word>`. These are real stages of
the deployed serve, and their certificates are auto-produced by `wf_auto` with
zero per-stage hand proof — a genuine result. But NONE of them produces a byte of
the actual HTTP response.

The real serve produces **bytes**. `serialize` renders
`HTTP/1.1 SP status SP reason CRLF (name ": " value CRLF)* CRLF body` off a
`Response` struct (`status : Nat`, `reason : Bytes`, `headers : List (Bytes ×
Bytes)`, `body : Bytes`) through a `Wire` struct, a header-render loop
(`renderHeaders` / `renderHeadersClPush`), and a decimal render (`natToDec`).
Its value domain is `Bytes = List UInt8`, structs, and lists.

The translator's value domain is **one word** (`Value := BitVec 64`) and **flat
byte-memory** (`memory : Word → Word`). `Pancake/Sem.lean`'s header states the
restriction explicitly: the modelled subset emits **no structs**, so
`Value := BitVec 64` is exact and every `shape_of` is `One`.

The gap between "word decisions over locals" and "the real byte-producing serve
over structs/lists" is exactly the **data model**. Closing it is not more
per-stage authoring — it is building the one lowering that lets the translator we
already have chew the real serve's data. That is the pivot this arc executes.

The good news, and the reason the arc is finite: the serve is
**bounded-first-order, sans-IO**. `serialize` is a total structural function over
inductive lists; its loops are structural folds/maps with a length measure; it
has no closures, no effects except a well-defined FFI boundary. Data of exactly
this shape **lowers to flat byte-memory the standard way**, and we already own
the loop machinery (`while_inv_cond`, `RefinesClk`, `while_inv_cond_clk`) that
budgets and certifies bounded loops. The missing piece is the DATA lowering, not
the control lowering.

---

## 1. The ARC DEFINITION

**One proven translator that swallows the real serve.**

Today `translateCert o st (by wf_auto)` (`Pancake/ProofProducing.lean`) returns,
for a concrete loop-free stage `st`, a pair
`⟨PancakeProg, Refines o code (denote st)⟩` — emitted code plus a machine-checked
certificate that it computes the stage's denotation, with zero hand lines. The
arc's endpoint generalises this along TWO axes at once:

1. **From word denotations to byte denotations under a lowering relation.** The
   certificate's contract becomes: for a serve function `f : A → Bytes` (the real
   `serialize`, `renderHeaders`, `natToDec`, a real `Stage.onResponse`), the
   emitted flat-memory program `p` satisfies
   `RefinesClk o p (Lowered inputs) (fun s s' → LowerBytes (f inputs) (out-region s'))`
   — where `LowerBytes` is the proven relation between a serve-level `Bytes`/struct
   value and its flat byte-memory image. The refinement is over the REAL serve
   value, not a word-decision proxy.

2. **From per-stage hand authoring to one run over the real definition.** The
   input to the translator is the serve's OWN structural definition
   (`serialize`/`renderHeaders`/`natToDec`/`Response` as they stand), lowered by a
   generic pass, not a hand re-encoded `Stage` term rebuilt per feature. "Swallows
   the real serve" is the operative test: the arc is done when running the
   translator over the deployed response path emits code + certificate with no new
   per-stage `.lean` and no hand-authored `.pnk`.

Concretely, the endpoint theorem has the shape:

```
theorem serve_translated (o : Oracle σ) (resp : Response) :
    { p : PancakeProg //
        RefinesClk o p (Lowered resp)
          (fun s s' => LowerBytes (Reactor.serialize resp) (outRegion s' s)) }
```

produced by a translator run, its `RefinesClk` obligation discharged by the
loop-aware generalisation of `wf_auto`. The named non-negotiables that keep it
honest: **non-vacuous** (`serialize` genuinely emits distinct bytes for distinct
responses — `Serialize.lean`'s own `#guard`s witness this), **real lowering**
(`LowerBytes` relates the actual `List UInt8` to the actual byte-memory
effect, not `P → P`), **axiom-clean** (`⊆ {propext, Quot.sound,
Classical.choice}`), and **first-order** (no fabricated semantics for constructs
outside the modelled subset — `Lower.lean` already returns `none` rather than
inventing images for `storeb`/`call`/`==`/`<=`/`-`).

The arc REPLACES per-stage hand authoring. It does NOT hand-author another
per-stage `.pnk`. Every wave EXTENDS the general translator (a new lowering
layer, a new proven op, a new loop schema) so the next batch of real serve
functions falls out of the existing machinery.

---

## 2. The LAYER stack

The arc is a bottom-up stack. Each layer is a proven capability the layer above
consumes. Reality is checked at every rung: when a layer's obligation cannot be
discharged over the REAL serve value, you move DOWN and fix the lowering, never
sideways into a word-decision proxy.

```
  L7  run over the real serve      translateCert over serialize / the pipeline
      ────────────────────────────────────────────────────────────────────────
  L6  wf_auto generalization       loop-aware WF automation over RefinesClk
  L5  loop-invariant automation    schema-driven invariant + step discharge
      ────────────────────────────────────────────────────────────────────────
  L4  response-construction loop    byte-WRITE loop (renderHeaders / natToDec)
  L3  ops                           byte-append / copy / decimal-digit leaves
  L2  struct / list                 Response/Wire field layout, list layout
  L1  bytes-lowering  (KEYSTONE)    LowerBytes : Bytes ↔ (buf,len,memory)
```

**L1 — bytes-lowering (the keystone).** A first-class relation
`LowerBytes (bs : Bytes) (buf len : Word) (m : Word → Word) : Prop` stating that
the flat byte-memory `m` holds exactly the bytes `bs` in the region
`[buf, buf+len)`, plus the two proven directions: a READ direction (pull `bs`
back out of memory, already latent as `readByteArray`) and a WRITE direction
(a byte pushed into the region extends the represented `Bytes` by exactly that
byte). This is the keystone because every struct field that is a `Bytes`, every
render loop, and the final body append is stated in terms of it. The seam already
exists in embryo: `EmitCorrectLoop.ViewBytes s a buf off len` is precisely
`LowerBytes` specialised to the scan's READ side. L1 promotes it to a bidirectional,
stage-independent layer.

**L2 — struct / list.** A `Response`/`Wire` struct lowers to a fixed field
layout: scalar fields (`status : Nat`) as words, `Bytes` fields as `(ptr, len)`
pairs into byte-memory (L1), the header list `List (Bytes × Bytes)` as an indexed
/ linked layout of `(ptr,len)` pairs. The lowering carries the proof that reading
a field back through the layout recovers the struct's field value. This is the
layer the Sem model's header currently excludes by construction (`Value := BitVec
64`, no structs), so L2 is where the modelled value domain is genuinely widened —
the largest single conceptual step in the stack. It is still first-order: a struct
is a fixed record of words and `(ptr,len)`s, not a closure.

**L3 — ops.** The byte-producing primitive leaves, each a proven `RefinesClk`
leaf the way `assignPrim`/`storePrim` are proven leaves today:
- byte-append (`acc.push b` / `st8` → `writeByteArray`/`memStoreByte` refining
  `bs ++ [b]`),
- byte-region copy (append a whole `Bytes`),
- decimal-digit emit (one `natToDec` digit).
The word-op leaves (`add/and/mul/lt`, word `Store`/`Load`, byte `LoadByte`) are
already proven; L3 adds their byte-WRITE duals. Note the concrete debt this
surfaces: `Lower.lean` currently maps `storeb` (byte store) to `none` — the byte
store op is not yet even in the lowered subset, so L3 begins by admitting it.

**L4 — response-construction write-loop.** The render is a LOOP that writes bytes:
`renderHeaders` folds the header list into the output region;
`renderHeadersClPush` is its byte-direct twin (the deployed one); `natToDec` folds
digits. These are `while_inv_cond_clk` instances whose body is an L3 byte-write
leaf and whose invariant relates the accumulator region to `renderHeaders`/`natToDec`
of the processed prefix. Structurally identical to the scan loop we already
certified — the scan READS bytes and folds a word; the render READS a list and
WRITES bytes. Same `while_inv_cond_clk`, dual step lemma.

**L5 — loop-invariant automation.** Today the scan loop is certified by
hand-supplying `scanInv`, `scan_guard`, `scan_step` and instantiating
`while_inv_cond_clk`. L5 makes that mechanical for the serve's structural loops
(§4). This is the hard automation piece.

**L6 — wf_auto generalization.** `wf_auto` today discharges the loop-free
`{prim, seq, cond}` `WF`. L6 lifts it to the clock-accounting grammar: it must
recognise loop nodes, fire L5 to discharge them, and thread the `RefinesClk`
compose rules (`refinesClk_seq`/`_dec`) that `region_via_clock` currently applies
by hand. After L6 the whole assembly `Dec…; Dec…; (While…; publish)` closes with
no hand composition — `region_via_clock`'s hand assembly becomes what the tactic
emits.

**L7 — run over the real serve.** With L1–L6, `translateCert` runs over the real
`serialize` / the real `Stage.onResponse` and returns code + a byte-level
`RefinesClk` certificate. The destination.

---

## 3. What THIS wave landed vs what remains, per layer

The wave under review is the **clock-accounting** landing: `EmitCorrectClock.lean`
(`RefinesClk` + the compose rules + `region_via_clock`), sitting on the loop wave
(`EmitCorrectLoop.lean`, `while_inv_cond`) and the proof-producing/fragment waves
(`ProofProducing.lean`, `ServeFragment.lean`).

| Layer | Landed | Remains |
|---|---|---|
| **L1 bytes-lowering** | `ViewBytes` (READ side of `LowerBytes`, used by the scan); full faithful byte substrate — `getByte`/`setByte`/`memLoadByte`/`memStoreByte`/`readByteArray`/`writeByteArray` all transcribed and used in proofs. | Promote `ViewBytes` to a stage-independent bidirectional `LowerBytes`; prove the WRITE direction (byte-push extends the represented `Bytes`). **The keystone itself is the next-wave target.** |
| **L2 struct/list** | Nothing. Value domain is one word by construction. | Entire layer: `Response`/`Wire` field layout, `List (Bytes×Bytes)` layout, field-read-back proofs. Widens the modelled value domain. |
| **L3 ops** | All WORD leaves proven (`assignPrim`/`storePrim`, `add/and/mul/lt`, word `Store`/`Load`, byte `LoadByte`). | Byte-WRITE dual leaves: byte-append, region-copy, decimal-digit. `Lower.lean` must first admit `storeb` (currently `none`). |
| **L4 response-construction loop** | The WORD-fold loop shape: `scanWhile` reads bytes, folds a digest word, certified as ONE `RefinesClk` stage (`refinesClk_scanWhile`) and composed with a publish frame (`refinesClk_scan_publish`). | The byte-WRITE loop: a `renderHeaders`/`natToDec` instance of `while_inv_cond_clk` whose invariant relates the accumulator region to the fold of the processed prefix. |
| **L5 loop-invariant automation** | Nothing automated — `scanInv`/`scan_guard`/`scan_step` are hand-authored. | The schema generator + loop-step discharge (§4). |
| **L6 wf_auto generalization** | `wf_auto` scales across 6 real loop-free decision stages (`ServeFragment.lean`), each 0 hand lines. The compose rules exist (`refinesClk_seq/_dec/_conseq`) and `region_via_clock` assembles the whole loop-bearing region THROUGH them — but by hand. | Lift `wf_auto` to fire the compose rules and L5 automatically; retire the hand assembly. |
| **L7 real serve** | Word-decision stages only (status pick, admit/deny). Structurally real (real `deployStagesFull2` decisions) but byte-free. | The byte-producing `serialize` / `renderHeaders` / `natToDec` / real `onResponse`. |

**The one-sentence read:** this wave unified straight-line AND loop stages under a
single clock-accounting refinement grammar and proved the whole loop-bearing
region composes inside it — i.e. it finished the **control** story for one loop.
The **data** story (L1/L2) is still at the water's edge: we have the READ side of
one bytes relation and no struct layer at all. The arc's weight is now in the data
lowering, and the loop machinery it will run on is done.

---

## 4. The loop-invariant AUTOMATION challenge (L5 — the hard piece)

This is the crux, and it deserves a precise, honest characterisation rather than
a hand-wave at "automate the loops".

**Is it invariant SYNTHESIS or invariant CHECKING-WITH-ANNOTATIONS? — Neither
extreme. It is invariant checking against a SCHEMA instantiated from the fold
structure.** The honest position:

Free-form invariant *synthesis* (discover an arbitrary inductive invariant for an
arbitrary loop) is undecidable and is NOT what the serve needs — and pretending we
will solve it would be dishonest. Pure *annotation* (the human writes the full
invariant, the tactic only checks) is what we do TODAY by hand and is the fallback
that always works but does not scale.

The serve sits in the sweet spot between them because **every loop in the serve is
a structural fold or map over an inductive list with a length measure** —
`renderHeaders` folds the header list, `renderHeadersClPush` folds it byte-direct,
`natToDec` folds digits, the body append copies a `Bytes`. For a structural fold
`fold f z xs`, the loop invariant is not free — it is **schematic**, mechanically
derivable from the recursion:

```
I n s  ≜  ∃ prefix suffix,  prefix ++ suffix = xs  ∧  suffix.length = n
              ∧  accumulator-region(s) = LowerBytes-image (fold f z prefix)
              ∧  index(s) = prefix.length
              ∧  LowerBytes suffix (remaining input region of s)
```

`EmitCorrectLoop.scanInv` is **exactly this schema** already, hand-instantiated at
`f = rolling-digest`, `xs = the view bytes`, carrier = the `acc` word. L5's job is
to GENERATE this term from the stage's fold witness rather than have a human write
it out. So the automation decomposes cleanly:

1. **Recognise the fold.** The annotation the author supplies is small and is
   DATA, not a hand proof: which list the loop walks and which fold function it
   accumulates (`renderHeaders`, `natToDec`). This is the same *class* of input as
   today's named input-scoping fact `hcode`/`hactive` — a stated fact about the
   stage, not a proof term.
2. **Instantiate the schema** to get `I`, and `hguard` falls out of the schema for
   free (the guard is `index < length`, whose evaluation the schema pins — cf.
   `scan_guard`, which is fully mechanical given the invariant).
3. **Discharge the step** (`hstep`/`hbody`): the loop body is itself a **loop-free
   sub-stage** over the extended scope (one L3 byte-write leaf + an index bump).
   So the step obligation is discharged by the SAME leaf tactics `wf_auto` already
   fires — `scan_step` is, under the hand-work, just `sem_assign`/`sem_seq_none`
   over the body leaves plus the schema's prefix-extension algebra
   (`fold f z (prefix ++ [x]) = f (fold f z prefix) x`, the fold's own cons law).

So **L5 = schema instantiation + fold-cons rewriting + loop-free `wf_auto` on the
body.** It is checking-with-a-schema: the human input is the fold witness (DATA),
the schema supplies the invariant, and the discharge reuses the loop-free
automation we have. Genuinely non-structural loops (unbounded search, data-dependent
iteration counts that are not a list length) fall OUTSIDE this schema and outside
the bounded-first-order serve fragment — and are named honestly as out of scope
rather than pretended into it. Every loop we have inventoried in the real serve
(`renderHeaders`, `natToDec`, body copy, and the parser/HMAC loops flagged as the
P3 residual in `ServeFragment.lean`) is either a structural fold — in scope — or an
explicitly named parser/crypto loop deferred with its own boundary.

**Why this is tractable and not a research bet:** the schema is proven ONCE
(`while_inv_cond_clk` is the reusable rule; the schema is a fixed instantiation of
its `I`), the fold-cons law is the list's own recursion equation, and the body is
loop-free. Nothing in L5 requires inferring an invariant no human stated; it
requires wiring the fold witness into a fixed template — which is engineering, not
open research.

---

## 5. The honest velocity framing

**Bounded, first-order, sans-IO — and we already own the control machinery.** The
serve is a total structural program: finite records of words and `(ptr,len)`s, no
closures (first-order), loops that are structural folds with a length measure
(bounded, budgeted by the clock the model already threads), and no effects beyond
the named FFI boundary (sans-IO). Data of this shape lowers to flat byte-memory the
standard way. This is why the arc is a finite stack of engineering layers, not a
sequence of research problems — and why it is honest to sequence it per-wave rather
than gate it on a breakthrough.

What "we have the loop machinery" concretely buys: the control story that usually
dominates a compiler-correctness effort — clocked termination, the `fix_clock`
clamp discipline, composing a loop-bearing stage with straight-line frames — is
DONE and axiom-clean. `RefinesClk` hosts loops and straight-line stages under one
predicate; `refinesClk_seq/_dec/_conseq` compose them; `while_inv_cond_clk` budgets
the bounded loop; `region_via_clock` demonstrates a full `Dec;Dec;(While;publish)`
assembly closing purely by those rules. The remaining weight is DATA lowering
(L1/L2) and the automation that rides on the finished control layer (L5/L6).

**Per-wave milestones (each a green, axiom-clean, non-vacuous landing):**

- **Wave A — the L1 keystone.** Promote `ViewBytes` to a bidirectional
  `LowerBytes`; prove the byte-WRITE direction; admit `storeb` in `Lower.lean` and
  prove the byte-append leaf (L3 begins). *Milestone:* a straight-line stage that
  writes ONE real response byte-fragment refines its serve denotation over
  byte-memory — the first stage that produces a REAL response byte, not a word
  decision. Ground it on `Serialize.statusLine` / `natToDec` of a fixed status.
- **Wave B — L2 struct/list + L4 render loop.** Lower `Response`/`Wire` fields and
  the header list; instantiate `while_inv_cond_clk` at `renderHeaders`/`natToDec`
  (the byte-write loop, dual of the scan). *Milestone:* the header block of a real
  fixed-header response is emitted and certified against `renderHeaders`.
- **Wave C — L5 loop automation.** The fold-schema generator + step discharge, so
  the Wave-B render loop is certified without a hand-written invariant.
- **Wave D — L6 + L7.** Lift `wf_auto` to the clock grammar (retire the hand
  compose), then run `translateCert` over the real `serialize` and one real
  `Stage.onResponse`. *Milestone:* one run of the translator emits code + a
  byte-level certificate for the real response path — the arc's endpoint.

**The honest next-wave target is Wave A: the L1 data-lowering keystone.** It is the
narrowest step that crosses the pivot — from "certifies a word decision" to
"produces a real response byte with a byte-level refinement certificate" — and it
is precisely the keystone the whole stack above rests on. Everything after it is
layering onto a foundation whose control machinery is already proven.

---

## Residuals named

- **L1 WRITE direction unproven.** `ViewBytes` is READ-only today; the byte-push-
  extends-the-region lemma is the keystone's missing half.
- **L2 does not exist.** No struct or list layout; the modelled value domain is one
  word by construction and must be widened. Largest conceptual step.
- **`Lower.lean` rejects the byte store.** `storeb` → `none`; the byte-write op is
  not yet in the lowered subset. Admitting it is the first concrete L3 task.
- **Loop automation is manual.** `scanInv`/`scan_guard`/`scan_step` are hand-authored;
  L5 (§4) is the schema generator that removes the hand work; until then every loop
  costs a hand invariant.
- **Compose is manual.** `region_via_clock` assembles by hand through the compose
  rules; `wf_auto` does not yet fire them (L6).
- **Parser / crypto loops out of the structural-fold fragment.** base64 decode,
  byte-equality compares, HMAC, body rewrites (the `ServeFragment.lean` P3 list) are
  NOT structural folds over a list length in scope for L5's schema; they carry their
  own bounded-loop + invariant/measure obligations and are named, not swept in.
- **FFI boundary is an explicit assumption.** The oracle (`A0`) is a stated trusted
  contract, not a `sorry`; the arc does not discharge it and does not pretend to.
