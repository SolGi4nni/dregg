/-
  Pancake/PredEval.lean — THE PROVED REQUEST DECISION (discharging `compile2`'s
  `hDec` assumption).

  `compile2` (StageCompile.lean) lowers each `StageProg` guard `c : ReqPred` by
  reading a PRE-DECIDED boolean local `nm c` — and `compile2_correct` ASSUMES that
  local already holds `c ctx` (`hDec : ∀ c, st.locals (nm c) = some (if c ctx then
  1 else 0)`). That is an ASSUMPTION, not a proof: nothing there computes the bit.

  This file closes that gap for the DATA-DENOTABLE subset of guards. It:

   * gives a DATA algebra of request predicates, `PredSpec`, and its denotation
     `denotePred : PredSpec → Ctx → Bool` over the REAL serve `Ctx` (so a
     `PredSpec` IS an ordinary `ReqPred` value, `denotePred spec`);
   * COMPILES a `PredSpec` to a REAL Pancake fragment `predEval` that READS the
     request region (the pre-decoded method-tag word) and LANDS the decision bit
     in the boolean local — a `.cmp .less` against the method-tag slot, or a
     constant for the unconditional predicates;
   * PROVES `predEval_correct`: for ALL `cfg`/`req`/`base` (i.e. all `Ctx`) and
     all covered `spec`, running `predEval` lands EXACTLY `denotePred spec ctx` in
     the named local — the decision is now COMPUTED and PROVEN, not assumed;
   * DISCHARGES the `hDec` clause: `predEval_hDec_clause` shows the post-state
     satisfies `st'.locals (nm (denotePred spec)) = some (if denotePred spec ctx
     then 1 else 0)` — an `hDec` clause is now a THEOREM;
   * COMPOSES the two into a concrete end-to-end: `methodFilter_discharged` runs
     `predEval` (the proved decision) THEN `compile2` of the real method-filter
     gate, and lands the `CoreEnc` skeleton of `denoteStep` — with the gate's bit
     supplied by `predEval_correct`, NOT by an `hDec` hypothesis. The assumed
     decision is gone from this composition.

  COVERED (word-comparison / constant): `methodLt bound` (the method filter,
  `tag < bound`; the allow-set `{GET,HEAD,POST,OPTIONS}` is `tag < 4`), `always`,
  `never`. CHARACTERIZED-ONLY (byte-list, residual): `methodIn` denotes fine as
  DATA but compiles to a byte-compare `While` (the `SerializeHeaders.segWhile`
  shape) — named, not smuggled. Header-list-reading guards (general `condResp`)
  stay EXCLUDED, as `Compilable` (StageProg2.lean) demands.

  HONEST BOUNDARY. `predEval` reads the method as a PRE-DECODED tag WORD, exactly
  the deployed dispatcher's output (`DslServe`'s "GET/POST/HEAD/OPTIONS pre-decoded
  to {0,1,2,3}"). `ReqEnc` names that interface: the tag slot holds `ofNat
  (methodTag req.method)`. The tag DECODE itself (bytes→tag) is the dispatcher's
  separate, named obligation, not re-proven here.

  This is Stack L (the Lean model of Pancake) + a locals/memory post-state claim.
-/
import Pancake.StageCompile

namespace Pancake.PredEval

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile
open Pancake.StructModel (wordAt eval_loadWord_of_wordAt eval_var)
open Pancake.EmitCorrect (sem_assign signedLt_ofNat sem_seq_none)
open Pancake.EmitCorrectCompose (sem_cond)

variable {σ : Type}

/-! ## 0. The method-tag decode (the dispatcher's pre-decode, as a pure function) -/

/-- Pre-decode a request method to its tag: the allow-set `{GET,HEAD,POST,OPTIONS}`
maps to `{0,1,2,3}`, everything else to `4` (the method-filter's "disallowed"
region). This is the pure spec of the deployed dispatcher's method decode; the
machine holds its output word (`ReqEnc`). -/
def methodTag (m : Bytes) : Nat :=
  if m = str "GET" then 0
  else if m = str "HEAD" then 1
  else if m = str "POST" then 2
  else if m = str "OPTIONS" then 3
  else 4

/-- The tag is one of `{0,1,2,3,4}` — in particular it fits the non-negative signed
range the signed compare needs. -/
theorem methodTag_le (m : Bytes) : methodTag m ≤ 4 := by
  unfold methodTag
  repeat' split
  all_goals omega

theorem methodTag_small (m : Bytes) : methodTag m < 2 ^ 63 := by
  have := methodTag_le m; omega

/-! ## 1. `PredSpec` — the DATA algebra of request predicates -/

/-- **`PredSpec`** — the config-denotable request predicates, as DATA (not a
`Ctx → Bool` function value). `methodLt` is the method filter (the pre-decoded tag
below `bound`); `always`/`never` are the unconditional guards. `methodIn` carries
a method allow-LIST as data — it denotes fine but compiles to a byte-compare loop
(residual, §5), so it is not in the `predEval`-covered set. -/
inductive PredSpec where
  | methodLt (bound : Nat)
  | methodGe (bound : Nat)
  | methodIn (methods : List Bytes)
  | always
  | never
  deriving Repr, DecidableEq

/-- **`denotePred`** — a `PredSpec` IS a `ReqPred`: its denotation over the REAL
serve `Ctx`. `methodLt b` fires iff the pre-decoded method tag is `< b`; `methodIn
ms` iff the raw method is in the list; `always`/`never` are constant. -/
def denotePred : PredSpec → Ctx → Bool
  | .methodLt b,  ctx => decide (methodTag ctx.req.method < b)
  | .methodGe b,  ctx => decide (b ≤ methodTag ctx.req.method)
  | .methodIn ms, ctx => decide (ctx.req.method ∈ ms)
  | .always,      _   => true
  | .never,       _   => false

/-- The vocabulary is a genuine subset of `ReqPred = Ctx → Bool`: `denotePred spec`
is an ordinary request predicate, so it slots straight into `StageProg`'s guards. -/
example (spec : PredSpec) : ReqPred := denotePred spec

/-! ### Non-vacuity: the denotation genuinely decides -/

/-- A `PUT` request (tag `4`), NOT in the allow-set. -/
def ctxPut : Ctx := { req := { method := str "PUT" }, base := baseOk }

-- `methodGe 4` is the real method-filter REFUSAL predicate (tag ≥ 4 = disallowed):
-- it fires on PUT (refuse) and not on GET (allow). `methodLt` is its allow-side dual.
#guard denotePred (.methodGe 4) ctxPut = true
#guard denotePred (.methodGe 4) ctxGet = false
#guard denotePred (.methodLt 4) ctxGet = true
#guard denotePred (.methodLt 4) ctxPut = false
#guard denotePred .always ctxGet = true
#guard denotePred .never  ctxGet = false

/-! ## 2. The request-region encoding + the compiler `predEval` -/

/-- **`ReqEnc`** — the machine holds the request facts `predEval` reads: the word
slot `aMethod` carries the pre-decoded method tag `methodTag req.method`. (This is
the dispatcher-output interface; the bytes→tag decode is its separate obligation.) -/
def ReqEnc (aMethod : Word) (st : PancakeState σ) (ctx : Ctx) : Prop :=
  wordAt st aMethod (BitVec.ofNat 64 (methodTag ctx.req.method))

/-- **`predEval aMethod name spec`** — lower a covered `PredSpec` to the Pancake
fragment that COMPUTES its bit into local `name`. `methodLt b` is a REAL signed
compare of the method-tag slot against `b`; `always`/`never` are the constants
`1`/`0`. (`methodIn` has no word-level fragment — it is the byte-loop residual, so
it emits the always-false constant here and is excluded from `predEval_correct`.) -/
def predEval (aMethod : Word) (name : String) : PredSpec → PancakeProg
  | .methodLt b => .assign name (.cmp .less    (.loadWord (.const aMethod)) (.const (BitVec.ofNat 64 b)))
  | .methodGe b => .assign name (.cmp .notLess (.loadWord (.const aMethod)) (.const (BitVec.ofNat 64 b)))
  | .always     => .assign name (.const 1)
  | .never      => .assign name (.const 0)
  | .methodIn _ => .assign name (.const 0)   -- residual: real byte-compare loop, §5

/-- The covered subset `predEval_correct` proves. `methodLt b` carries the SIGNED-
range side condition `b < 2^63` (satisfied by the deployed method-filter bound
`4`); `methodIn` is excluded (`False`), being the byte-loop residual. -/
def Covered : PredSpec → Prop
  | .methodLt b => b < 2 ^ 63
  | .methodGe b => b < 2 ^ 63
  | .always     => True
  | .never      => True
  | .methodIn _ => False

/-! ## 3. `eval` of the compare (the `.less` reduction has no library lemma yet) -/

/-- `eval (Cmp Less e1 e2) = SOME (if signedLt a b then 1 else 0)` (`word_cmp Less`,
SIGNED) — the `.less` analogue of `Sem`'s `eval_equal`/`eval_notLess`. -/
theorem eval_less {s : PancakeState σ} {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.cmp .less l r) = some (if signedLt a b then 1 else 0) := by
  simp only [eval, hl, hr]

/-! ## 4. `predEval_correct` — THE PROVED DECISION -/

/-- **`predEval_correct`.** For ALL `Ctx` (hence all `cfg`/`req`/`base`) and every
COVERED `spec`, running `predEval` from a state encoding the request (`ReqEnc`)
lands EXACTLY the decision `denotePred spec ctx` in local `name`, framing every
other local, all memory, and the clock. The decision is COMPUTED by the emitted
compare/constant and PROVEN equal to `denotePred` — no assumed bit. -/
theorem predEval_correct (o : Oracle σ) (aMethod : Word) (name : String) (ctx : Ctx)
    (st : PancakeState σ) (spec : PredSpec) (hcov : Covered spec)
    (hEnc : ReqEnc aMethod st ctx) :
    ∃ st', PancakeSem o (predEval aMethod name spec) st = (none, st') ∧
      st'.locals name = some (if denotePred spec ctx then (1 : Word) else 0) ∧
      (∀ k, k ≠ name → st'.locals k = st.locals k) ∧
      st'.memory = st.memory ∧
      (∀ x, st'.memaddrs x = st.memaddrs x) ∧
      st'.clock = st.clock := by
  cases spec with
  | methodLt b =>
    have hb : b < 2 ^ 63 := hcov
    have hload : eval st (.loadWord (.const aMethod))
        = some (BitVec.ofNat 64 (methodTag ctx.req.method)) :=
      eval_loadWord_of_wordAt (eval_const aMethod) hEnc
    have hval : eval st (.cmp .less (.loadWord (.const aMethod)) (.const (BitVec.ofNat 64 b)))
        = some (if denotePred (.methodLt b) ctx then (1 : Word) else 0) := by
      rw [eval_less hload (eval_const (BitVec.ofNat 64 b)),
          signedLt_ofNat _ _ (methodTag_small ctx.req.method) hb]
      rfl
    refine ⟨_, sem_assign (oracle := o) hval, ?_, ?_, rfl, fun _ => rfl, rfl⟩
    · show setLocal st.locals name _ name = _; simp [setLocal]
    · intro k hk; show setLocal st.locals name _ k = _; simp [setLocal, hk]
  | methodGe b =>
    have hb : b < 2 ^ 63 := hcov
    have hload : eval st (.loadWord (.const aMethod))
        = some (BitVec.ofNat 64 (methodTag ctx.req.method)) :=
      eval_loadWord_of_wordAt (eval_const aMethod) hEnc
    have hval : eval st (.cmp .notLess (.loadWord (.const aMethod)) (.const (BitVec.ofNat 64 b)))
        = some (if denotePred (.methodGe b) ctx then (1 : Word) else 0) := by
      rw [eval_notLess _ hload (eval_const (BitVec.ofNat 64 b)),
          signedLt_ofNat _ _ (methodTag_small ctx.req.method) hb]
      simp only [denotePred]
      by_cases h : methodTag ctx.req.method < b
      · have h2 : ¬ b ≤ methodTag ctx.req.method := by omega
        simp [h, h2]
      · have h2 : b ≤ methodTag ctx.req.method := by omega
        simp [h, h2]
    refine ⟨_, sem_assign (oracle := o) hval, ?_, ?_, rfl, fun _ => rfl, rfl⟩
    · show setLocal st.locals name _ name = _; simp [setLocal]
    · intro k hk; show setLocal st.locals name _ k = _; simp [setLocal, hk]
  | always =>
    refine ⟨_, sem_assign (oracle := o) (eval_const (1 : Word)), ?_, ?_, rfl, fun _ => rfl, rfl⟩
    · show setLocal st.locals name _ name = _; simp [setLocal, denotePred]
    · intro k hk; show setLocal st.locals name _ k = _; simp [setLocal, hk]
  | never =>
    refine ⟨_, sem_assign (oracle := o) (eval_const (0 : Word)), ?_, ?_, rfl, fun _ => rfl, rfl⟩
    · show setLocal st.locals name _ name = _; simp [setLocal, denotePred]
    · intro k hk; show setLocal st.locals name _ k = _; simp [setLocal, hk]
  | methodIn ms => exact hcov.elim

/-! ## 5. Discharging the `hDec` clause — the assumed bit becomes a THEOREM -/

/-- **`predEval_hDec_clause`.** For a covered `spec`, running `predEval` establishes
EXACTLY the `hDec` clause `compile2_correct` assumes, for the guard `c := denotePred
spec` and its local name `nm c`: `st'.locals (nm c) = some (if c ctx then 1 else 0)`.
So the assumed decision is a PROVED consequence of `predEval_correct`, not a
hypothesis. -/
theorem predEval_hDec_clause (o : Oracle σ) (aMethod : Word) (nm : ReqPred → String)
    (ctx : Ctx) (st : PancakeState σ) (spec : PredSpec) (hcov : Covered spec)
    (hEnc : ReqEnc aMethod st ctx) :
    ∃ st', PancakeSem o (predEval aMethod (nm (denotePred spec)) spec) st = (none, st') ∧
      st'.locals (nm (denotePred spec))
        = some (if denotePred spec ctx then (1 : Word) else 0) :=
  let ⟨st', h1, h2, _⟩ :=
    predEval_correct o aMethod (nm (denotePred spec)) ctx st spec hcov hEnc
  ⟨st', h1, h2⟩

/-! ## 6. The concrete end-to-end — `predEval` ⨾ `compile2`, the assumed bit GONE

`gate_run` is `compile2_correct` specialized to a single `gate`, but with the
per-guard `hDec` clause taken as ONE proved fact (`hclause`) rather than the
whole `∀ c` assumption — so it accepts EXACTLY what `predEval_hDec_clause`
produces. `methodFilter_discharged` then threads the two: run `predEval` (the
PROVED decision), then `compile2` of the real method-filter gate, landing the
`CoreEnc` skeleton of `denoteStep`. The gate's decision bit is supplied by
`predEval_correct` — there is no `hDec` hypothesis anywhere in the statement. -/

/-- **`gate_run`** — the gate compiled and run from ONE proved decision clause. The
same state transition as `compile2_correct`'s `gate` case, but its only predicate
input is the single fact `hclause : st.locals (nm c) = some (if c ctx then 1 else
0)` — precisely what `predEval` proves. -/
theorem gate_run (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx) (c : ReqPred) (code : Nat)
    (hd : Distinct aStat aCnt aBody aHalt)
    (d : DState) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st d)
    (hclause : st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (.gate c code)) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st' (denoteStep ctx (.gate c code) d) := by
  obtain ⟨d_sc, d_sb, d_sh, d_cb, d_ch, d_bh⟩ := hd
  obtain ⟨hS, hC, hB, hH⟩ := hEnc
  have hin1 : st.memaddrs aStat = true := hS.1
  obtain ⟨st1, hst1⟩ : ∃ s : PancakeState σ,
      s = { st with memory := fun k => if k = aStat then BitVec.ofNat 64 code else st.memory k } :=
    ⟨_, rfl⟩
  have hstore1 : PancakeSem o (stC aStat (BitVec.ofNat 64 code)) st = (none, st1) := by
    rw [hst1]; exact sem_stC o hin1
  obtain ⟨st2, hst2⟩ : ∃ s : PancakeState σ,
      s = { st1 with memory := fun k => if k = aHalt then (1 : Word) else st1.memory k } :=
    ⟨_, rfl⟩
  have hin2 : st1.memaddrs aHalt = true := by rw [hst1]; exact hH.1
  have hstore2 : PancakeSem o (stC aHalt 1) st1 = (none, st2) := by
    rw [hst2]; exact sem_stC o hin2
  have hseq : PancakeSem o (.seq (stC aStat (BitVec.ofNat 64 code)) (stC aHalt 1)) st
      = (none, st2) := by
    rw [sem_seq_none hstore1]
    have hc1 : st1.clock = st.clock := by rw [hst1]
    have hcl : ({ st1 with clock := min st.clock st1.clock } : PancakeState σ) = st1 := by
      rw [hc1, Nat.min_self, ← hc1]
    rw [hcl]; exact hstore2
  have hinner : PancakeSem o
      (.cond (.var (nm c)) (.seq (stC aStat (BitVec.ofNat 64 code)) (stC aHalt 1)) .skip) st
      = (none, if c ctx then st2 else st) := by
    rw [sem_cond o (eval_var hclause)]
    cases hc : c ctx with
    | true =>
      rw [if_pos (show (if (true : Bool) then (1 : Word) else 0) ≠ 0 from word_one_ne_zero),
          hseq, if_pos (rfl : (true : Bool) = true)]
    | false =>
      rw [if_neg (show ¬ ((if (false : Bool) then (1 : Word) else 0) ≠ 0) from fun h => h rfl),
          sem_skip o st, if_neg (show ¬ ((false : Bool) = true) by decide)]
  have hrun := run_guarded (d := d) o hH hinner
  refine ⟨_, hrun, ?_⟩
  show CoreEnc _ _ _ _ _ (denoteStep ctx (.gate c code) d)
  cases hh : d.halted with
  | true =>
    rw [show denoteStep ctx (.gate c code) d = d from by
      show (if d.halted then d else _) = d; rw [hh]; rfl]
    exact ⟨hS, hC, hB, hH⟩
  | false =>
    cases hc : c ctx with
    | false =>
      rw [show denoteStep ctx (.gate c code) d = d from by
        show (if d.halted then d else if c ctx then _ else d) = d; rw [hh, hc]; rfl]
      exact ⟨hS, hC, hB, hH⟩
    | true =>
      rw [show denoteStep ctx (.gate c code) d
          = { resp := { d.resp with status := code }, halted := true } from by
        show (if d.halted then d else if c ctx then
                { resp := { d.resp with status := code }, halted := true } else d) = _
        rw [hh, hc]; rfl]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show wordAt st2 aStat (BitVec.ofNat 64 code)
        rw [hst2]; refine wordAt_frame ?_ d_sh
        rw [hst1]; exact wordAt_hit hin1
      · show wordAt st2 aCnt (BitVec.ofNat 64 d.resp.headers.length)
        rw [hst2]; refine wordAt_frame ?_ d_ch
        rw [hst1]; exact wordAt_frame hC (Ne.symm d_sc)
      · show wordAt st2 aBody (BitVec.ofNat 64 d.resp.body.length)
        rw [hst2]; refine wordAt_frame ?_ d_bh
        rw [hst1]; exact wordAt_frame hB (Ne.symm d_sb)
      · show wordAt st2 aHalt (1 : Word)
        rw [hst2]; refine wordAt_hit ?_
        rw [hst1]; exact hH.1

/-- The REAL method filter as a `StageProg` gate: refuse `405` when the pre-decoded
method tag is `< b` fails to hold... i.e. the guard `denotePred (.methodLt b)` fires
(the deployed `onRequest` method-filter refusal). `methodLt 4` is the allow-set
`{GET,HEAD,POST,OPTIONS}` filter. -/
def methodFilterGate (b : Nat) : StageProg := .gate (denotePred (.methodGe b)) 405

/-- **`methodFilter_discharged` — the assumed decision is GONE.** Running `predEval`
(the proved decision) THEN `compile2` of the method-filter gate lands the `CoreEnc`
skeleton of `denoteStep ctx (methodFilterGate b) d`. The gate's boolean bit is
supplied by `predEval_correct` — the statement has NO `hDec` hypothesis. This is
the `hDec` discharge, end-to-end and operational: the `405` refusal genuinely fires
exactly when `methodTag req.method < b`, computed and proven from the request. -/
theorem methodFilter_discharged (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt aMethod : Word) (ctx : Ctx) (b : Nat)
    (hcov : b < 2 ^ 63) (hd : Distinct aStat aCnt aBody aHalt)
    (d : DState) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st d)
    (hReq : ReqEnc aMethod st ctx) :
    ∃ st', PancakeSem o
        (.seq (predEval aMethod (nm (denotePred (.methodGe b))) (.methodGe b))
              (compile2 nm aStat aCnt aBody aHalt (methodFilterGate b))) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st' (denoteStep ctx (methodFilterGate b) d) := by
  obtain ⟨st1, hpe, hloc1, _, hmem1, hma1, hclk1⟩ :=
    predEval_correct o aMethod (nm (denotePred (.methodGe b))) ctx st (.methodGe b) hcov hReq
  -- CoreEnc survives `predEval` (it touched only a local, not memory)
  have wa : ∀ a v, wordAt st a v → wordAt st1 a v := fun a v hw =>
    ⟨by rw [hma1]; exact hw.1, by rw [hmem1]; exact hw.2⟩
  obtain ⟨hS, hC, hB, hH⟩ := hEnc
  have hEnc1 : CoreEnc aStat aCnt aBody aHalt st1 d :=
    ⟨wa _ _ hS, wa _ _ hC, wa _ _ hB, wa _ _ hH⟩
  obtain ⟨st2, hgr, hEnc2⟩ :=
    gate_run o nm aStat aCnt aBody aHalt ctx (denotePred (.methodGe b)) 405 hd d st1 hEnc1 hloc1
  refine ⟨st2, ?_, hEnc2⟩
  rw [sem_seq_none hpe]
  have hcl : ({ st1 with clock := min st.clock st1.clock } : PancakeState σ) = st1 := by
    rw [hclk1, Nat.min_self, ← hclk1]
  rw [hcl]; exact hgr

/-! ## 7. Non-vacuity + axiom audit -/

-- The discharged filter genuinely REFUSES `PUT` (tag 4, `¬ 4 < 4`) and PASSES `GET`:
#guard (denoteStep ctxPut (methodFilterGate 4) { resp := baseOk, halted := false }).resp.status = 405
#guard (denoteStep ctxGet (methodFilterGate 4) { resp := baseOk, halted := false }).resp.status = baseOk.status

#print axioms predEval_correct
#print axioms predEval_hDec_clause
#print axioms gate_run
#print axioms methodFilter_discharged

end Pancake.PredEval
