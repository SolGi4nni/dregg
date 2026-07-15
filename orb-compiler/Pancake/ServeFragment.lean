/-
  Pancake/ServeFragment.lean — SCALE proof-producing translation across the
  LOOP-FREE decision-stage fragment of drorb's deployed serve. ADDITIVE over
  Pancake/ProofProducing.lean (P1+P2) and Pancake/EmitCorrectCompose.lean
  (emit_correct_generic + the {prim, seq, cond} grammar) — nothing there is
  modified or re-proven.

  CLAIM. The redirect status stage (`ProofProducing.redirectStatusStage`) showed
  P1+P2 auto-producing ONE real stage's `Refines` certificate with zero per-stage
  hand proof. This file shows the SAME `wf_auto` mechanism auto-produces the
  certificate for a REAL FRACTION of `deployStagesFull2` — five more loop-free
  decision stages — each with `hand-proof lines per stage = 0` (just the grammar
  expression + the `by wf_auto` one-liner). That is proof-producing translation
  SCALING across the serve's loop-free fragment, not a single point.

  THE FIVE STAGES (each is a real `deployStagesFull2` / drorb decision, lowered
  into the loop-free `{skip, assign, seq, cond}` grammar over the modelled
  `Cmp Less` (`signedLt`) subset — the only comparison the Lean `PancakeSem` has):

    1. connLimitDecision  (ConnLimit  `admits`)        — EXACT: `active < 4`
    2. bodyLimitDecision  (BodyLimit  `oversized`)     — EXACT: `7 < cldigits`
    3. ipfilterDecision   (IpFilter   `deployAdmits`, HOL4 C29) — EXACT on the
                             CIDR-relevant first octet: admit iff `octet ≠ 10`
    4. methodFilterDecision (MethodFilter `isAllowed`) — TAG form: `tag < 4`
    5. securityHeadersDecision (SecurityHeaders `wireHeaders`, C26) — EXACT,
                             CLOSED: an unconditional set of header-present flags,
                             `wf_auto` closes it with ZERO hypotheses.

  FAITHFULNESS (no vacuous / wrong lowerings):

   * ConnLimit `admits cap active = (cap == 0 || active < cap)` with the deployed
     `connCap = 4` reduces (by `decide` on `4 == 0 = false`) to EXACTLY
     `active < 4`. The lowering is the deployed decision on the nose.
   * BodyLimit `oversized = decide (maxCLDigits < len)` with `maxCLDigits = 7` is
     EXACTLY `7 < len` on the content-length digit count. On the nose.
   * IpFilter's deployed ruleset is a SINGLE `deny 10.0.0.0/8` block with
     `defaultDeny := false`, so `deployAdmits a = (firstOctet a ≠ 10)`. A `/8`
     CIDR match tests exactly the first octet, so on that projection the lowering
     `octet < 10 ∨ 10 < octet` is exact (this is the C29 IP-filter decision).
   * MethodFilter's real `isAllowed = allowedMethods.contains m` is a LIST-membership
     LOOP over byte-strings; `tag < 4` is faithful only under the "method
     pre-decoded to an ordered tag with the four allowed methods as `{0,1,2,3}`"
     contract — the SAME enum→tag re-encoding the redirect reference uses
     (`Code` → `{0,1,2,3}`). Honest caveat: the byte-string decode is the loop; on
     the tag domain the decision is `tag < 4`.
   * SecurityHeaders `onResponse` unconditionally folds a fixed header list — no
     branch, no loop. Modelled as a `seq` of three distinct closed `assign`s
     (header-present flags): a genuine non-identity transformer (three locals),
     closed by `wf_auto` with NO hypotheses (the `closedDemo` class).

  DATA-DEPENDENT stages (1–4) each carry ONE named input-scoping hypothesis (the
  local the guard reads is bound — the A0 input contract, exactly as
  `redirectStatusStage` carries `hcode`). That is DATA, not a hand proof; `wf_auto`
  discharges everything else. Stage 5 needs nothing.

  LOOP/PARSER RESIDUAL (P3, NOT forced here — genuine loops/parsers, named):
   * BasicAuth  — base64 decode (`b64Decode`) + `user==…&&pass==…` byte-equality:
                   a PARSER + string compare (loop).  [C27]
   * Gzip / HtmlRewrite / headerRewrite — body rewrites: parse/emit LOOPS.
   * Rate / StickTable / Slowloris — windowed counters: stateful loops.
   * JWT-HMAC front-end — HMAC over the token bytes: a loop.  [C31]
   These need the bounded-`While` rule (`EmitCorrectCompose.while_inv`) + a
   per-loop invariant/measure — the Gate-A loop distance, out of the loop-free
   fragment. NOT lowered here; naming them is the honest boundary.

  This is Stack L (the Lean model of Pancake) — NO byte claims.

  ASSURANCE. `#print axioms` on every `<stage>_cert` / `<stage>_wf` is
  ⊆ {propext, Quot.sound, Classical.choice}, 0 `sorry`. Build:
  `Pancake/build_servefragment.sh`.
-/
import Pancake.ProofProducing

namespace Pancake.ServeFragment

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.ProofProducing

variable {σ : Type}

/-! ## Stage 1 — ConnLimit: `admits connCap active` (EXACT `active < 4`)

drorb `Reactor/Stage/ConnLimit.lean`: `admits cap active := (cap == 0 || active <
cap)`, deployed `connCap = 4`. Since `4 == 0` is `false`, the deployed decision is
EXACTLY `active < 4`. `activeVal s` is the current active-connection count word.
Writes `result := 1` (admit) / `0` (deny → 503 downstream). Data-dependent guard
reads local `"active"` — needs the input-scoping fact `hactive`. -/
def connLimitDecision (activeVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "active") (.const 4)) (fun s => signedLt (activeVal s) 4)
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.prim (assignPrim "result" (.const 0) (fun _ => 0)))

theorem connLimitDecision_wf (o : Oracle σ) (activeVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s)) :
    WF o (connLimitDecision activeVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the ConnLimit decision. -/
theorem connLimitDecision_cert (o : Oracle σ) (activeVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s)) :
    Refines o (emit (connLimitDecision activeVal)) (denote (connLimitDecision activeVal)) :=
  emit_correct_generic o _ (connLimitDecision_wf o activeVal hactive)

def connLimitDecision_translated (o : Oracle σ) (activeVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s)) :
    { p : PancakeProg // Refines o p (denote (connLimitDecision activeVal)) } :=
  translateCert o (connLimitDecision activeVal) (connLimitDecision_wf o activeVal hactive)

/-! ## Stage 2 — BodyLimit: `oversized req` (EXACT `7 < cldigits`)

drorb `Reactor/Stage/BodyLimit.lean`: `oversized := decide (maxCLDigits < len)`,
deployed `maxCLDigits = 7`. EXACTLY `7 < len` on the `Content-Length` digit count.
`clVal s` is that count word. Writes `result := 1` (oversized → 413) / `0`
(within). The guard reads local `"cldigits"` on the RIGHT of `<`. -/
def bodyLimitDecision (clVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.const 7) (.var "cldigits")) (fun s => signedLt 7 (clVal s))
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.prim (assignPrim "result" (.const 0) (fun _ => 0)))

theorem bodyLimitDecision_wf (o : Oracle σ) (clVal : PancakeState σ → Word)
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    WF o (bodyLimitDecision clVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the BodyLimit decision. -/
theorem bodyLimitDecision_cert (o : Oracle σ) (clVal : PancakeState σ → Word)
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    Refines o (emit (bodyLimitDecision clVal)) (denote (bodyLimitDecision clVal)) :=
  emit_correct_generic o _ (bodyLimitDecision_wf o clVal hcl)

def bodyLimitDecision_translated (o : Oracle σ) (clVal : PancakeState σ → Word)
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    { p : PancakeProg // Refines o p (denote (bodyLimitDecision clVal)) } :=
  translateCert o (bodyLimitDecision clVal) (bodyLimitDecision_wf o clVal hcl)

/-! ## Stage 3 — IpFilter: `deployAdmits a` (EXACT on the CIDR first octet)

drorb `Reactor/Stage/IpFilter.lean` (HOL4 C29): the deployed ruleset is the SINGLE
block `deny 10.0.0.0/8` with `defaultDeny := false`. A `/8` CIDR match tests only
the first octet, so `deployAdmits a = (firstOctet a ≠ 10)`, i.e. admit iff
`octet < 10 ∨ 10 < octet`. `octetVal s` is the first octet word. Writes
`result := 1` (admit) / `0` (deny → 403). The nested `cond` cascade reads local
`"octet"` in both guards. -/
def ipfilterDecision (octetVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "octet") (.const 10)) (fun s => signedLt (octetVal s) 10)
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.cond (.cmp .less (.const 10) (.var "octet")) (fun s => signedLt 10 (octetVal s))
      (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
      (.prim (assignPrim "result" (.const 0) (fun _ => 0))))

theorem ipfilterDecision_wf (o : Oracle σ) (octetVal : PancakeState σ → Word)
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s)) :
    WF o (ipfilterDecision octetVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the IpFilter decision. -/
theorem ipfilterDecision_cert (o : Oracle σ) (octetVal : PancakeState σ → Word)
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s)) :
    Refines o (emit (ipfilterDecision octetVal)) (denote (ipfilterDecision octetVal)) :=
  emit_correct_generic o _ (ipfilterDecision_wf o octetVal hoctet)

def ipfilterDecision_translated (o : Oracle σ) (octetVal : PancakeState σ → Word)
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s)) :
    { p : PancakeProg // Refines o p (denote (ipfilterDecision octetVal)) } :=
  translateCert o (ipfilterDecision octetVal) (ipfilterDecision_wf o octetVal hoctet)

/-! ## Stage 4 — MethodFilter: `isAllowed m` (TAG form `tag < 4`)

drorb `Reactor/Stage/MethodFilter.lean`: `isAllowed m := allowedMethods.contains m`
over `[GET, POST, HEAD, OPTIONS]`. The real `contains` is a LIST-membership LOOP
over byte-strings; on the enum→tag encoding the redirect reference also uses
(allowed methods as `{0,1,2,3}`, others `≥ 4`) the decision is EXACTLY `tag < 4`.
`tagVal s` is the method tag word. Writes `result := 1` (allowed) / `0` (405). The
byte-string decode is the P3 loop; this is the tag-domain decision. -/
def methodFilterDecision (tagVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "method") (.const 4)) (fun s => signedLt (tagVal s) 4)
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.prim (assignPrim "result" (.const 0) (fun _ => 0)))

theorem methodFilterDecision_wf (o : Oracle σ) (tagVal : PancakeState σ → Word)
    (hmethod : ∀ s : PancakeState σ, s.locals "method" = some (tagVal s)) :
    WF o (methodFilterDecision tagVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the MethodFilter (tag-domain) decision. -/
theorem methodFilterDecision_cert (o : Oracle σ) (tagVal : PancakeState σ → Word)
    (hmethod : ∀ s : PancakeState σ, s.locals "method" = some (tagVal s)) :
    Refines o (emit (methodFilterDecision tagVal)) (denote (methodFilterDecision tagVal)) :=
  emit_correct_generic o _ (methodFilterDecision_wf o tagVal hmethod)

def methodFilterDecision_translated (o : Oracle σ) (tagVal : PancakeState σ → Word)
    (hmethod : ∀ s : PancakeState σ, s.locals "method" = some (tagVal s)) :
    { p : PancakeProg // Refines o p (denote (methodFilterDecision tagVal)) } :=
  translateCert o (methodFilterDecision tagVal) (methodFilterDecision_wf o tagVal hmethod)

/-! ## Stage 5 — SecurityHeaders: `wireHeaders policy` (EXACT, CLOSED, ZERO hyps)

drorb `Reactor/Stage/SecurityHeaders.lean` (C26): `onResponse` UNCONDITIONALLY
folds a fixed header list onto the response — no branch, no loop, no input read.
Modelled as a `seq` of three distinct CLOSED `assign`s setting header-present flags
(`hsts`, `xfo`, `nosniff` — the deployed HSTS + X-Frame-Options + X-Content-Type).
All expressions are closed, so `wf_auto` closes `WF` with NO hypotheses (the
`closedDemo` class). Non-vacuous: three distinct locals are written. -/
def securityHeadersDecision : Stage σ :=
  .seq (.prim (assignPrim "hsts" (.const 1) (fun _ => 1)))
    (.seq (.prim (assignPrim "xfo" (.const 1) (fun _ => 1)))
      (.prim (assignPrim "nosniff" (.const 1) (fun _ => 1))))

/-- `wf_auto` closes the SecurityHeaders decision with ZERO hypotheses. -/
theorem securityHeadersDecision_wf (o : Oracle σ) :
    WF o (securityHeadersDecision (σ := σ)) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the SecurityHeaders decision (zero hyps). -/
theorem securityHeadersDecision_cert (o : Oracle σ) :
    Refines o (emit (securityHeadersDecision (σ := σ)))
      (denote (securityHeadersDecision (σ := σ))) :=
  emit_correct_generic o _ (securityHeadersDecision_wf o)

def securityHeadersDecision_translated (o : Oracle σ) :
    { p : PancakeProg // Refines o p (denote (securityHeadersDecision (σ := σ))) } :=
  translateCert o securityHeadersDecision (securityHeadersDecision_wf o)

/-! ## Emitted-Pancake witnesses (Stack L target = `Sem.PancakeProg`)

Each `emit <stage>` is a concrete nested `If (Cmp Less …) (Assign "result" …) …`
(or, for SecurityHeaders, a `Seq` of `Assign`s) over the model AST — the same
shape the HOL4 C-series probes lowered. Instantiate the data projections at `Unit`
and read the emitted program to confirm it genuinely computes the decision. -/
section EmitWitness

/-- Read a named local (default 0) so each emitted program is a closed term. -/
def localVal (name : String) : PancakeState σ → Word := fun s => (s.locals name).getD 0

#eval reprStr (emit (connLimitDecision   (σ := Unit) (localVal "active")))
#eval reprStr (emit (bodyLimitDecision   (σ := Unit) (localVal "cldigits")))
#eval reprStr (emit (ipfilterDecision    (σ := Unit) (localVal "octet")))
#eval reprStr (emit (methodFilterDecision (σ := Unit) (localVal "method")))
#eval reprStr (emit (securityHeadersDecision (σ := Unit)))

end EmitWitness

end Pancake.ServeFragment
