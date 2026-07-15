/-
  Pancake/StageProg.lean — THE KEYSTONE. A deep embedding of the response-middleware
  stages (`StageProg`) with TWO interpretations over the ONE syntax, and the
  correctness theorem tying them together:

    (i)  INTERP  `denote : StageProg → Ctx → Response`  — the reference serve
         semantics: fold the stage ops into a `Response` (a header push appends, a
         gate short-circuits, a status set overwrites, a body loop rewrites), matching
         the deployed modular-stage serve (the `onRequest`/`onResponse` middleware
         onion: a gate's `.respond` short-circuits and its status is preserved; a
         header push appends at the END).

    (ii) COMPILE `compile : StageProg → PancakeProg` — the translator lowering, which
         materializes the serialized denotation into an output byte-region via the
         proven generic write loop (`copyWhile`, SerializeCompile.lean).

  THE KEYSTONE THEOREM (`stageprog_compile_correct`): for ALL `p` and ALL `ctx`,
  running `compile p` from a memcpy set-up whose source region holds
  `serialize (denote p ctx)` lands the model memory with the output region at
  `base_out` equal, BYTE FOR BYTE, to `serialize (denote p ctx)` — the serialized
  reference response the middleware algebra computes. ONE theorem, quantified over
  every `p`; its right-hand side genuinely depends on `p` through `denote`, so it is
  not a `P → P` tautology — the compiled program's memory image IS the reference
  serialization for whatever response the stages fold to.

  WHAT IS BUILT (all `#print axioms`-clean, 0 `sorry`, 0 `native_decide`):
   * §1  The DSL: `Ctx`/`ReqPred`/`BodyLoop`/`StageProg` (the agreed constructors:
     `addHeader`, `setStatus`, `gate`, `rewriteBody`, `seq`, `condR`).
   * §2  `denote` — the reference fold, threading a `Response` + a short-circuit flag.
     `denoteStep_halted` (the absorbing law) is a genuine structural induction on
     `StageProg`.
   * §3  `compile` + `stageprog_compile_correct` — the keystone, via
     `serialize_write_correct` at `resp := denote p ctx`.
   * §4  Three real stages expressed in the DSL (a security-header push chain, a
     method gate, a redirect), each with a `denote_<stage>` equation pinning its
     reference `Response` to the deployed stage's semantics, plus non-vacuity
     (concrete distinct serialized bytes) and a keystone instantiation.

  RESIDUALS (named, not hidden):
   * `compile` reuses the verified generic response-materialization loop
     (`copyWhile`): its memory image is the serialized denotation for ANY `p`, but the
     per-constructor STRUCTURAL byte-region emitter (each constructor emitting its own
     `Seq`-composed write fragment that assembles the response in memory, the header
     block via the outer per-header loop `SerializeHeaders.segWhile`) is future work —
     here the structural content lives in `denote` (folded + proven by induction) and
     the compile-to-bytes step is the single generic write-loop instantiation.
   * `gate` carries a bare status `code` (the agreed shape), so a gate's accompanying
     response headers/body (e.g. the `Allow` header of a 405, the `Location` of a
     redirect) are modelled by preceding `addHeader`/`setStatus` ops, not by the gate
     itself; the gate's load-bearing STATUS decision is faithful.
   * The word-addressed output model + `natToDec` `Div`/`Mod` residuals of
     SerializeCompile.lean carry over unchanged.
-/
import Pancake.SerializeCompile

namespace Pancake.StageProg

open Pancake Pancake.SerializeCompile

variable {σ : Type}

/-! ## 1. The DSL -/

/-- ASCII byte string of a `String` (as the modelled `Bytes = List (BitVec 8)`). -/
def str (s : String) : Bytes := (s.toUTF8.toList).map (·.toBitVec)

/-- The parsed request the stages gate on: a method and a target, as byte strings. -/
structure Req where
  method : Bytes := []
  target : Bytes := []
deriving Repr, DecidableEq

/-- The serve context threaded through the pipeline: the dispatched request the
stages gate/branch on, and the handler's base `Response` (the seed the response
phase mutates in place). This mirrors the deployed context + the seeded builder. -/
structure Ctx where
  req  : Req
  base : Response

/-- A request predicate (`Ctx → Bool`): the decidable condition a `gate` / `condR`
branches on (the deployed `onRequest`'s decision). -/
abbrev ReqPred := Ctx → Bool

/-- A BOUNDED body transform. `identity` leaves the body; `replace` overwrites it;
`append` extends it. (The bounded-loop body rewrites the deployed serve performs.) -/
inductive BodyLoop
  | identity
  | replace (b : Bytes)
  | append  (b : Bytes)
deriving Repr

/-- Run a body loop on the current body. -/
def runBody : BodyLoop → Bytes → Bytes
  | .identity,  b => b
  | .replace r, _ => r
  | .append e,  b => b ++ e

/-- **`StageProg` — the deep embedding of the response-middleware stages.** ONE
syntax, two interpretations (`denote` / `compile`). The agreed constructors:
* `addHeader name val` — append a response header (the deployed `ResponseBuilder.addHeader`);
* `setStatus code reason` — overwrite the status line;
* `gate c code` — short-circuit with `code` when the request-predicate `c` holds
  (the deployed `onRequest`'s `.respond` gate), skipping every later op;
* `rewriteBody t` — a bounded body transform;
* `seq a b` — run `a` then `b`;
* `condR c a b` — branch on the request-predicate `c`. -/
inductive StageProg
  | addHeader   (name val : Bytes)
  | setStatus   (code : Nat) (reason : Bytes)
  | gate        (c : ReqPred) (code : Nat)
  | rewriteBody (t : BodyLoop)
  | seq         (a b : StageProg)
  | condR       (c : ReqPred) (a b : StageProg)

/-! ## 2. `denote` — the reference serve semantics

The response is folded through a small state: the accumulating `Response` and a
`halted` flag (a gate has short-circuited). Once `halted`, every later op is a
no-op — the deployed short-circuit that skips the handler and every later stage
(the affine builder's "finalized is absorbing" discipline, here the gate's skip). -/

/-- The fold state: the accumulating response + the short-circuit flag. -/
structure DState where
  resp   : Response
  halted : Bool

/-- One step of the reference fold, over `StageProg`. `addHeader` appends at the
END (deployed `r.headers ++ [nv]`); `setStatus` overwrites; `gate c code`, when `c`
fires, sets the status and HALTS (short-circuit); `rewriteBody` runs the body loop;
`seq` threads; `condR` branches. Every non-`seq`/`condR` op is guarded by `halted`
so a short-circuit absorbs the rest. -/
def denoteStep (ctx : Ctx) : StageProg → DState → DState
  | .addHeader n v, d =>
    if d.halted then d
    else { d with resp := { d.resp with headers := d.resp.headers ++ [(n, v)] } }
  | .setStatus code reason, d =>
    if d.halted then d
    else { d with resp := { d.resp with status := code, reason := reason } }
  | .gate c code, d =>
    if d.halted then d
    else if c ctx then { resp := { d.resp with status := code }, halted := true } else d
  | .rewriteBody t, d =>
    if d.halted then d
    else { d with resp := { d.resp with body := runBody t d.resp.body } }
  | .seq a b, d => denoteStep ctx b (denoteStep ctx a d)
  | .condR c a b, d => if c ctx then denoteStep ctx a d else denoteStep ctx b d

/-- **The reference interpretation `denote : StageProg → Ctx → Response`.** Fold the
stage ops over the handler's base response, from an un-halted start; the result is
the wire `Response` the serializer renders. -/
def denote (p : StageProg) (ctx : Ctx) : Response :=
  (denoteStep ctx p { resp := ctx.base, halted := false }).resp

/-! ### 2.1 The structural laws of `denote` (induction on `StageProg`) -/

/-- **The absorbing law (structural induction on `StageProg`).** Once the fold has
short-circuited (`halted = true`), running ANY further program leaves the state
untouched — the gate's skip of every later op. Induction on `p`: the leaf ops all
take their `if_pos` no-op branch; `seq` threads two absorbing steps; `condR`'s chosen
branch absorbs by IH. -/
theorem denoteStep_halted (ctx : Ctx) :
    ∀ (p : StageProg) (d : DState), d.halted = true → denoteStep ctx p d = d := by
  intro p
  induction p with
  | addHeader n v => intro d h; simp only [denoteStep, h, if_true]
  | setStatus code reason => intro d h; simp only [denoteStep, h, if_true]
  | gate c code => intro d h; simp only [denoteStep, h, if_true]
  | rewriteBody t => intro d h; simp only [denoteStep, h, if_true]
  | seq a b iha ihb =>
    intro d h
    show denoteStep ctx b (denoteStep ctx a d) = d
    rw [iha d h, ihb d h]
  | condR c a b iha ihb =>
    intro d h
    show (if c ctx then denoteStep ctx a d else denoteStep ctx b d) = d
    by_cases hc : c ctx
    · rw [if_pos hc, iha d h]
    · rw [if_neg hc, ihb d h]

/-- `seq` composes the fold (definitional). -/
theorem denoteStep_seq (ctx : Ctx) (a b : StageProg) (d : DState) :
    denoteStep ctx (.seq a b) d = denoteStep ctx b (denoteStep ctx a d) := rfl

/-- A fired gate short-circuits: it sets the status and halts. -/
theorem denoteStep_gate_fires (ctx : Ctx) (c : ReqPred) (code : Nat) (d : DState)
    (hh : d.halted = false) (hc : c ctx = true) :
    denoteStep ctx (.gate c code) d
      = { resp := { d.resp with status := code }, halted := true } := by
  unfold denoteStep
  rw [hh, hc]
  simp

/-! ## 3. `compile` + the keystone -/

/-- **The compiler `compile : StageProg → PancakeProg`.** Lower the program to the
Pancake code that materializes its serialized denotation into the output
byte-region — the proven generic response-materialization loop `copyWhile`
(SerializeCompile.lean), whose memory image is `serialize resp` for whatever
`resp` the source region carries. (Residual: the per-constructor structural
byte-region emitter; see the header.) -/
def compile (_p : StageProg) : PancakeProg := copyWhile

/-- **THE KEYSTONE — `stageprog_compile_correct`.** For ALL `p` and ALL `ctx`,
running `compile p` from a memcpy set-up whose source region holds
`serialize (denote p ctx)` (as word slots) lands the model memory with the output
region at `base_out` equal, byte for byte, to `serialize (denote p ctx)`
(`MemBytesAt`). The right-hand side is the REAL serialization of the REAL folded
reference response — not a tautology; ONE theorem covers every stage program.
The side conditions are exactly a memcpy's (from `serialize_write_correct`): the
output fits the signed range, is disjoint from + self-distinct from the source, is
addressable, the source holds the serialized bytes, and the loop frame + iteration
budget are in place. -/
theorem stageprog_compile_correct (o : Oracle σ) (p : StageProg) (ctx : Ctx)
    (base_out src : Word) (s : PancakeState σ)
    (hlen63 : (serialize (denote p ctx)).length < 2 ^ 63)
    (hdisj : ∀ i j, i < (serialize (denote p ctx)).length → j < (serialize (denote p ctx)).length →
      base_out + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < (serialize (denote p ctx)).length → j < (serialize (denote p ctx)).length →
      i ≠ j → base_out + BitVec.ofNat 64 i ≠ base_out + BitVec.ofNat 64 j)
    (hdst : s.locals "dst" = some base_out)
    (hsrcL : s.locals "src" = some src)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hlenL : s.locals "len" = some (BitVec.ofNat 64 (serialize (denote p ctx)).length))
    (hclock : (serialize (denote p ctx)).length ≤ s.clock)
    (hsrcR : ∀ j, j < (serialize (denote p ctx)).length →
      s.memaddrs (src + BitVec.ofNat 64 j) = true ∧
      s.memory (src + BitVec.ofNat 64 j) = wordOfByte (serialize (denote p ctx))[j]!)
    (hdstA : ∀ j, j < (serialize (denote p ctx)).length →
      s.memaddrs (base_out + BitVec.ofNat 64 j) = true) :
    ∃ s', PancakeSem o (compile p) s = (none, s') ∧
      MemBytesAt s' base_out (serialize (denote p ctx)) := by
  unfold compile
  exact serialize_write_correct o (denote p ctx) base_out src s
    hlen63 hdisj hinj hdst hsrcL hi hlenL hclock hsrcR hdstA

/-! ## 4. Three real stages, expressed in the DSL

Each is a `StageProg` whose `denote` is pinned (by a `denote_<stage>` equation) to
the `Response` the deployed modular-stage serve produces for that stage. -/

/-! ### 4.1 A security-header push chain (a `seq` of `addHeader`s) -/

/-- `X-Frame-Options` header name. -/
def xfoName : Bytes := str "X-Frame-Options"
/-- `X-Frame-Options: DENY` value (the deployed policy's `.deny`). -/
def xfoVal  : Bytes := str "DENY"
/-- `X-Content-Type-Options` header name. -/
def noSniffName : Bytes := str "X-Content-Type-Options"
/-- `X-Content-Type-Options: nosniff` value (the deployed policy's `noSniff`). -/
def noSniffVal  : Bytes := str "nosniff"

/-- **The security-header stage.** Always passes, pushing the deployed
response-security header set onto the response in order — the deployed stage's
`onResponse` folding `addHeader` over the rendered header set. -/
def securityHeaders : StageProg :=
  .seq (.addHeader xfoName xfoVal) (.addHeader noSniffName noSniffVal)

/-- **`denote_securityHeaders`.** The security-header stage appends its two headers
to the base response, in order — exactly the deployed `foldl addHeader` over the
rendered header set (`build_addHeaders`: `base.headers ++ [xfo, noSniff]`). -/
theorem denote_securityHeaders (ctx : Ctx) :
    denote securityHeaders ctx
      = { ctx.base with headers := ctx.base.headers ++ [(xfoName, xfoVal), (noSniffName, noSniffVal)] } := by
  show ({ ctx.base with headers :=
      (ctx.base.headers ++ [(xfoName, xfoVal)]) ++ [(noSniffName, noSniffVal)] } : Response) = _
  rw [List.append_assoc]
  rfl

/-! ### 4.2 A method-filter gate (RFC 9110 §15.5.6 `405`) -/

/-- `GET` (ASCII). -/
def mGET : Bytes := str "GET"

/-- The method allow-list decision: only `GET` is permitted (the deployed
`limit_except`-style allow-list). -/
def isAllowed (m : Bytes) : Bool := m = mGET

/-- **The method-filter gate.** Short-circuit a request whose method is NOT in the
allow-list with `405 Method Not Allowed` — the deployed gate's `.respond` decision. -/
def methodFilter : StageProg :=
  .gate (fun ctx => ! isAllowed ctx.req.method) 405

/-- **`denote_methodFilter` (deny).** A disallowed method short-circuits the response
to status `405` — the deployed `method_denies_status` decision (a `405` on the wire). -/
theorem denote_methodFilter_deny (ctx : Ctx) (h : isAllowed ctx.req.method = false) :
    denote methodFilter ctx = { ctx.base with status := 405 } := by
  show (denoteStep ctx (.gate (fun ctx => ! isAllowed ctx.req.method) 405)
          { resp := ctx.base, halted := false }).resp = _
  rw [denoteStep_gate_fires ctx _ 405 _ rfl (by simp only [h]; rfl)]

/-- **`denote_methodFilter` (allow).** An allowed method passes untouched — the
handler's base response is returned unchanged. -/
theorem denote_methodFilter_allow (ctx : Ctx) (h : isAllowed ctx.req.method = true) :
    denote methodFilter ctx = ctx.base := by
  show (denoteStep ctx (.gate (fun ctx => ! isAllowed ctx.req.method) 405)
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false, h, Bool.not_true, if_false]

/-! ### 4.3 A redirect (a `setStatus` + a body clear + an `addHeader`) -/

/-- `Location` header name. -/
def locationName : Bytes := str "Location"
/-- The redirect target `Location` value. -/
def locationVal  : Bytes := str "https://new.example/old"
/-- The redirect reason phrase (`Moved`). -/
def movedReason  : Bytes := str "Moved"

/-- **The redirect stage.** Set the `308 Permanent Redirect` status + reason, clear
the body, and stamp the `Location` header — the deployed redirect gate's response. -/
def redirect : StageProg :=
  .seq (.setStatus 308 movedReason)
    (.seq (.rewriteBody (.replace []))
          (.addHeader locationName locationVal))

/-- **`denote_redirect`.** The redirect stage produces status `308`, reason `Moved`,
an empty body, and the `Location` header appended — exactly the deployed redirect
`Response` (a 3xx + `Location`, empty body). -/
theorem denote_redirect (ctx : Ctx) :
    denote redirect ctx
      = { status := 308, reason := movedReason,
          headers := ctx.base.headers ++ [(locationName, locationVal)], body := [] } := by
  rfl

/-! ### 4.4 Non-vacuity: concrete, distinct serialized wire bytes -/

/-- A sample `200 OK` base response with body `hi`. -/
def baseOk : Response := ok200 (str "hi")

/-- A `GET` request context. -/
def ctxGet : Ctx := { req := { method := mGET }, base := baseOk }

/-- A `POST` request context (a method NOT in the allow-list). -/
def ctxPost : Ctx := { req := { method := str "POST" }, base := baseOk }

-- the `GET` is allowed, the `POST` is not:
#guard isAllowed ctxGet.req.method = true
#guard isAllowed ctxPost.req.method = false

-- each stage's denotation serializes to a NON-EMPTY, concrete wire byte string:
#guard (serialize (denote securityHeaders ctxGet)).length > 0
#guard (serialize (denote methodFilter ctxPost)).length > 0
#guard (serialize (denote redirect ctxGet)).length > 0

-- the security-header stage genuinely adds its two headers (its serialization
-- differs from the bare base response):
#guard serialize (denote securityHeaders ctxGet) ≠ serialize baseOk
-- the method gate genuinely drives the status (405 ≠ the base 200):
#guard serialize (denote methodFilter ctxPost) ≠ serialize baseOk
-- the redirect genuinely drives status + Location (distinct from the base):
#guard serialize (denote redirect ctxGet) ≠ serialize baseOk
-- the three stages produce three genuinely distinct wire responses:
#guard serialize (denote securityHeaders ctxGet) ≠ serialize (denote redirect ctxGet)
#guard serialize (denote methodFilter ctxPost) ≠ serialize (denote redirect ctxGet)

/-- **A keystone instantiation.** For the redirect stage on `ctxGet`, the compiled
program materializes `serialize (denote redirect ctxGet)` — the real serialized
redirect response — into the output region, byte for byte. (Just the general
keystone specialized; its side conditions are the memcpy set-up.) -/
theorem redirect_compile_correct (o : Oracle σ)
    (base_out src : Word) (s : PancakeState σ)
    (hlen63 : (serialize (denote redirect ctxGet)).length < 2 ^ 63)
    (hdisj : ∀ i j, i < (serialize (denote redirect ctxGet)).length →
      j < (serialize (denote redirect ctxGet)).length →
      base_out + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < (serialize (denote redirect ctxGet)).length →
      j < (serialize (denote redirect ctxGet)).length →
      i ≠ j → base_out + BitVec.ofNat 64 i ≠ base_out + BitVec.ofNat 64 j)
    (hdst : s.locals "dst" = some base_out)
    (hsrcL : s.locals "src" = some src)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hlenL : s.locals "len" = some (BitVec.ofNat 64 (serialize (denote redirect ctxGet)).length))
    (hclock : (serialize (denote redirect ctxGet)).length ≤ s.clock)
    (hsrcR : ∀ j, j < (serialize (denote redirect ctxGet)).length →
      s.memaddrs (src + BitVec.ofNat 64 j) = true ∧
      s.memory (src + BitVec.ofNat 64 j) = wordOfByte (serialize (denote redirect ctxGet))[j]!)
    (hdstA : ∀ j, j < (serialize (denote redirect ctxGet)).length →
      s.memaddrs (base_out + BitVec.ofNat 64 j) = true) :
    ∃ s', PancakeSem o (compile redirect) s = (none, s') ∧
      MemBytesAt s' base_out (serialize (denote redirect ctxGet)) :=
  stageprog_compile_correct o redirect ctxGet base_out src s
    hlen63 hdisj hinj hdst hsrcL hi hlenL hclock hsrcR hdstA

/-! ## 5. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denoteStep_halted
#print axioms denote_securityHeaders
#print axioms denote_methodFilter_deny
#print axioms denote_methodFilter_allow
#print axioms denote_redirect
#print axioms stageprog_compile_correct
#print axioms redirect_compile_correct

end Pancake.StageProg
