/-
  Pancake/StageCompile.lean — THE REAL PER-CONSTRUCTOR STAGE COMPILER.

  StageProg.lean's `compile` is a COPY-STUB: `compile _p := copyWhile`, i.e. it
  IGNORES `p` entirely and leans on the source region ALREADY holding
  `serialize (denote p ctx)`. Its "generality" is the polymorphism of one generic
  memory-copy loop (`copyWhile`), NOT a lowering that dispatches on the program
  structure. This file replaces that with a GENUINE per-constructor compiler
  `compile2` whose correctness is proven BY STRUCTURAL INDUCTION on `StageProg`.

  WHAT `compile2` LOWERS. Each `StageProg` constructor emits its OWN, DISTINCT
  Pancake fragment that COMPUTES its effect on the response SKELETON — the scalar
  projection `(status, |headers|, |body|, halted)` of the reference denotation —
  directly from the machine state, guarded by the short-circuit flag exactly as
  `denoteStep` guards each op:

    * `addHeader`   → a guarded increment of the HEADER-COUNT word slot
                      (`store aCnt (load aCnt + 1)`), realizing `headers ++ [nv]`
                      lengthening the header block by one;
    * `setStatus`   → a guarded write of the STATUS word slot (`store aStat code`);
    * `gate c code` → a REAL nested `If`: `if ¬halted then (if c then { status:=code;
                      halt } )` — a `Cond` on the request decision that, when it
                      fires, writes the status and SETS THE HALT FLAG (the wire
                      short-circuit);
    * `rewriteBody` → a guarded write/adjust of the BODY-LENGTH word slot
                      (`.replace r` stores `|r|`; `.append e` adds `|e|`; `.identity`
                      is `Skip`);
    * `seq a b`     → `Seq (compile2 a) (compile2 b)` — the two fragments THREADED;
    * `condR c a b` → `Cond c (compile2 a) (compile2 b)` — a REAL branch.

  The request predicates are realized as pre-decided BOOLEAN LOCALS (`nm c` holds
  `1`/`0` for `c ctx`), the deployed `onRequest`'s decision computed to a bit; the
  compiler's guards read those locals and the halt/status/count/body word slots.

  THE KEYSTONE THEOREM (`compile2_correct`, §4): for ALL `p`, ALL input fold-states
  `d`, and ALL machine states `st` whose four word slots ENCODE `d`'s response
  skeleton (`CoreEnc`), running `compile2 p` lands a machine state whose slots
  encode `denoteStep ctx p d` — status, header-count, body-length AND halt tracked
  byte-exactly through the fold. Proven BY INDUCTION on `p`: the generality is the
  induction over `compile2`'s STRUCTURE (`seq`→IH∘IH, `condR`/`gate`→branch+IH),
  NOT one polymorphic copy loop. Non-vacuous: the right-hand side is the REAL
  `denoteStep`, so a `405` gate genuinely lands `405`+halt, a redirect genuinely
  lands `308`, and the header push genuinely bumps the count.

  HOW THIS DIFFERS FROM THE COPY-STUB. `compile` is a constant function of `p`;
  `compile2` PATTERN-MATCHES every constructor into a different fragment, and the
  proof recurses on that match. The stub proves ONE memcpy under the assumption the
  answer is pre-serialized in memory; `compile2` proves the SKELETON is COMPUTED
  from the request by the emitted control flow, per constructor, composed.

  RESIDUALS (named, not hidden — the "datacake constructs" the full byte-image needs):
   * `compile2` tracks the SCALAR skeleton `(status, |headers|, |body|, halted)`.
     The variable-length BYTE CONTENT — the header name/value bytes, the body bytes,
     the status reason phrase — is NOT written by these fragments; materializing it
     is the OUTER per-header write loop of SerializeHeaders.lean (`segLoop`) + the
     body copy (`copyWhile`) reading the skeleton this file builds. Wiring the
     skeleton-build (here) to that byte-serializer to reach `MemBytesAt base_out
     (serialize (denote p ctx))` is the remaining assembly step.
   * Rendering the status / Content-Length as ASCII DECIMAL in a real Pancake
     `While` needs `Div`/`Mod` in the expression subset (`natToDec`); PACKING the
     bytes eight-per-word needs `StoreByte`. Both are the standing SerializeCompile
     residuals, unchanged.
   * `setStatus`'s reason phrase and `addHeader`'s name/value bytes are carried as
     the skeleton's COUNT/STATUS only; their byte payloads are the residual above.

  This is Stack L (the Lean model of Pancake) + a memory post-state claim.
-/
import Pancake.StageProg
import Pancake.StructModel

namespace Pancake.StageCompile

open Pancake Pancake.SerializeCompile Pancake.StageProg
open Pancake.EmitCorrect (sem_assign sem_seq_none ofNat_add_small)
open Pancake.EmitCorrectCompose (sem_cond)
open Pancake.StructModel (wordAt eval_loadWord_of_wordAt eval_op_add eval_var)

variable {σ : Type}

/-! ## 0. An UNCONDITIONAL word-add readback

`ofNat_add_small` (EmitCorrect) needs the sum to fit; but `BitVec.ofNat 64` is the
`mod 2^64` ring map, so `ofNat a + ofNat b = ofNat (a+b)` holds UNCONDITIONALLY.
This is what lets the count / body-length increments be proven with NO smallness
side condition. -/
theorem ofNat_add_unc (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## 1. The machine encoding of the response SKELETON

Four distinct word slots hold the scalar projection of the fold state `DState`:
the status, the header count, the body length, and the halt flag. -/

/-- `CoreEnc aStat aCnt aBody aHalt st d`: the four word slots at the given
addresses hold, respectively, the status, header count, and body length of `d`'s
response (as `ofNat 64` words), and the halt flag (`1` halted / `0` live). This is
the skeleton image the compiled fragments read and advance. -/
def CoreEnc (aStat aCnt aBody aHalt : Word) (st : PancakeState σ) (d : DState) : Prop :=
  wordAt st aStat (BitVec.ofNat 64 d.resp.status) ∧
  wordAt st aCnt  (BitVec.ofNat 64 d.resp.headers.length) ∧
  wordAt st aBody (BitVec.ofNat 64 d.resp.body.length) ∧
  wordAt st aHalt (if d.halted then (1 : Word) else 0)

/-- The four slot addresses are pairwise distinct (so a write to one frames the
other three). -/
def Distinct (aStat aCnt aBody aHalt : Word) : Prop :=
  aStat ≠ aCnt ∧ aStat ≠ aBody ∧ aStat ≠ aHalt ∧
  aCnt ≠ aBody ∧ aCnt ≠ aHalt ∧ aBody ≠ aHalt

/-! ## 2. The compiler `compile2` — per-constructor lowering -/

/-- The "not halted" guard expression: `load aHalt == 0` (nonzero iff live). -/
def gNH (aHalt : Word) : PancakeExp :=
  .cmp .equal (.loadWord (.const aHalt)) (.const 0)

/-- Wrap a fragment in the short-circuit guard: run it only when live. -/
def guarded (aHalt : Word) (frag : PancakeProg) : PancakeProg :=
  .cond (gNH aHalt) frag .skip

/-- A constant store `store aAddr v`. -/
def stC (aAddr v : Word) : PancakeProg := .store (.const aAddr) (.const v)

/-- **`compile2` — the genuine per-constructor lowering.** Each constructor emits
its OWN Pancake fragment (see the file header). `nm` maps each request predicate to
the boolean local holding its pre-decided bit. -/
def compile2 (nm : ReqPred → String) (aStat aCnt aBody aHalt : Word) :
    StageProg → PancakeProg
  | .addHeader _ _ =>
      guarded aHalt (.store (.const aCnt)
        (.op .add (.loadWord (.const aCnt)) (.const (BitVec.ofNat 64 1))))
  | .setStatus code _ =>
      guarded aHalt (stC aStat (BitVec.ofNat 64 code))
  | .gate c code =>
      guarded aHalt
        (.cond (.var (nm c))
          (.seq (stC aStat (BitVec.ofNat 64 code)) (stC aHalt 1))
          .skip)
  | .rewriteBody .identity => .skip
  | .rewriteBody (.replace r) =>
      guarded aHalt (stC aBody (BitVec.ofNat 64 r.length))
  | .rewriteBody (.append e) =>
      guarded aHalt (.store (.const aBody)
        (.op .add (.loadWord (.const aBody)) (.const (BitVec.ofNat 64 e.length))))
  | .seq a b =>
      .seq (compile2 nm aStat aCnt aBody aHalt a) (compile2 nm aStat aCnt aBody aHalt b)
  | .condR c a b =>
      .cond (.var (nm c))
        (compile2 nm aStat aCnt aBody aHalt a) (compile2 nm aStat aCnt aBody aHalt b)

/-! ### The per-constructor fragments are DISTINCT (not one polymorphic loop) -/

-- A stage that WRITES compiles to a real `Cond` guard, NOT the empty `Skip` an
-- `identity` body-rewrite emits — so distinct constructors get distinct fragments
-- (unlike the stub, where every constructor is `copyWhile`):
example (nm : ReqPred → String) (aStat aCnt aBody aHalt : Word) :
    compile2 nm aStat aCnt aBody aHalt (.setStatus 200 [])
      ≠ compile2 nm aStat aCnt aBody aHalt (.rewriteBody .identity) := by
  intro h
  rw [show compile2 nm aStat aCnt aBody aHalt (.setStatus 200 [])
        = guarded aHalt (stC aStat (BitVec.ofNat 64 200)) from rfl, guarded] at h
  exact PancakeProg.noConfusion h

/-! ## 3. Semantic building blocks -/

/-- `eval` of a constant. -/
theorem eval_const {st : PancakeState σ} (w : Word) : eval st (.const w) = some w := rfl

/-- `Skip` terminates with no result, state unchanged (`PancakeSem` is WF-recursive,
so this needs its equation lemma, not `rfl`). -/
theorem sem_skip (o : Oracle σ) (s : PancakeState σ) : PancakeSem o .skip s = (none, s) := by
  rw [PancakeSem]

/-- `1 ≠ 0` at `Word` (`decide` can't reduce `BitVec 64`; go through `toNat`). -/
theorem word_one_ne_zero : (1 : Word) ≠ 0 := by
  intro h; have := congrArg BitVec.toNat h; simp at this

/-- Evaluating the "not halted" guard: `1` when live, `0` when halted. -/
theorem eval_gNH {st : PancakeState σ} {aHalt : Word} {d : DState}
    (h : wordAt st aHalt (if d.halted then (1 : Word) else 0)) :
    eval st (gNH aHalt) = some (if d.halted then (0 : Word) else 1) := by
  obtain ⟨hm, hv⟩ := h
  have hl : eval st (.loadWord (.const aHalt)) = some (if d.halted then (1 : Word) else 0) := by
    show (match eval st (.const aHalt) with
          | some w => if st.memaddrs w then some (st.memory w) else none
          | none => none) = _
    simp only [eval, hm, hv, if_true]
  show (match eval st (.loadWord (.const aHalt)), eval st (.const 0) with
        | some a, some b => some (if a = b then (1 : Word) else 0)
        | _, _ => none) = _
  rw [hl, eval_const]
  cases d.halted
  · -- live: halt slot 0, guard yields 1
    show some (if (0 : Word) = 0 then (1 : Word) else 0) = some 1
    rw [if_pos rfl]
  · -- halted: halt slot 1, guard yields 0
    show some (if (1 : Word) = 0 then (1 : Word) else 0) = some 0
    rw [if_neg word_one_ne_zero]

/-- A single constant store updates memory at `a`, framing every distinct slot. -/
theorem sem_stC (o : Oracle σ) {aAddr v : Word} {st : PancakeState σ}
    (hin : st.memaddrs aAddr = true) :
    PancakeSem o (stC aAddr v) st
      = (none, { st with memory := fun k => if k = aAddr then v else st.memory k }) := by
  unfold stC
  exact Pancake.SerializeCompile.sem_store o (by rfl) (by rfl) hin

/-- `wordAt` survives a store at a DISTINCT address. -/
theorem wordAt_frame {st : PancakeState σ} {a v k vk : Word}
    (h : wordAt st k vk) (hne : k ≠ a) :
    wordAt { st with memory := fun x => if x = a then v else st.memory x } k vk := by
  obtain ⟨hm, hv⟩ := h
  refine ⟨hm, ?_⟩
  show (if k = a then v else st.memory k) = vk
  rw [if_neg hne, hv]

/-- `wordAt` at the just-written address holds the stored value. -/
theorem wordAt_hit {st : PancakeState σ} {a v : Word} (hm : st.memaddrs a = true) :
    wordAt { st with memory := fun x => if x = a then v else st.memory x } a v := by
  refine ⟨hm, ?_⟩
  show (if a = a then v else st.memory a) = v
  rw [if_pos rfl]

/-- Running a guarded fragment: the halt guard selects the fragment (live) or a
no-op (halted). -/
theorem run_guarded (o : Oracle σ) {aHalt : Word} {frag : PancakeProg}
    {st st1 : PancakeState σ} {d : DState}
    (hH : wordAt st aHalt (if d.halted then (1 : Word) else 0))
    (hfrag : PancakeSem o frag st = (none, st1)) :
    PancakeSem o (guarded aHalt frag) st = (none, if d.halted then st else st1) := by
  rw [guarded, sem_cond o (eval_gNH hH)]
  cases hh : d.halted with
  | true =>
    rw [if_neg (show ¬ ((if (true : Bool) then (0 : Word) else 1) ≠ 0) from fun h => h rfl),
        sem_skip o st, if_pos (rfl : (true : Bool) = true)]
  | false =>
    rw [if_pos (show (if (false : Bool) then (0 : Word) else 1) ≠ 0 from word_one_ne_zero),
        hfrag, if_neg (show ¬ ((false : Bool) = true) by decide)]

/-! ## 4. THE KEYSTONE — `compile2_correct`, by structural induction -/

/-- **`compile2_correct`.** For ALL `p`, running `compile2 p` from a machine state
`st` whose slots ENCODE the fold state `d` (`CoreEnc`) lands a state whose slots
encode `denoteStep ctx p d` — the reference fold's status, header count, body
length AND halt flag, tracked byte-exactly. Proven BY STRUCTURAL INDUCTION on `p`:
`seq` composes two IHs, `condR`/`gate` branch into an IH / a leaf write; the halt
guard realizes the short-circuit absorb. The frame conclusions (`locals` /
`memaddrs` / `clock` unchanged) carry the predicate decisions and the slot
addressing across the composition.

`nm`-decisions (`hDec`) supply each request predicate's pre-decided bit; since NO
fragment writes locals, they survive the whole program. -/
theorem compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) :
    ∀ (p : StageProg) (d : DState) (st : PancakeState σ),
      CoreEnc aStat aCnt aBody aHalt st d →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt p) st = (none, st') ∧
        CoreEnc aStat aCnt aBody aHalt st' (denoteStep ctx p d) ∧
        st'.locals = st.locals ∧
        (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock := by
  obtain ⟨d_sc, d_sb, d_sh, d_cb, d_ch, d_bh⟩ := hd
  intro p
  induction p with
  | addHeader n v =>
    intro d st hEnc hDec
    obtain ⟨hS, hC, hB, hH⟩ := hEnc
    -- the stored value is `count + 1`
    have hval : eval st (.op .add (.loadWord (.const aCnt)) (.const (BitVec.ofNat 64 1)))
        = some (BitVec.ofNat 64 (d.resp.headers.length + 1)) := by
      rw [eval_op_add (eval_loadWord_of_wordAt (eval_const aCnt) hC)
            (eval_const (BitVec.ofNat 64 1)), ofNat_add_unc]
    have hin : st.memaddrs aCnt = true := hC.1
    have hrun := run_guarded (d := d) o hH
      (Pancake.SerializeCompile.sem_store o (eval_const aCnt) hval hin)
    refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
    · -- CoreEnc of denoteStep (addHeader)
      show CoreEnc _ _ _ _ _ (if d.halted then d
        else { d with resp := { d.resp with headers := d.resp.headers ++ [(n, v)] } })
      cases hh : d.halted with
      | true => simp only [hh, if_true]; exact ⟨hS, hC, hB, hH⟩
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by decide)]
        rw [hh] at hH
        refine ⟨wordAt_frame hS d_sc, ?_, wordAt_frame hB (Ne.symm d_cb),
                wordAt_frame hH (Ne.symm d_ch)⟩
        show wordAt _ aCnt (BitVec.ofNat 64 (d.resp.headers ++ [(n, v)]).length)
        rw [List.length_append]; simpa using wordAt_hit hin
    · cases d.halted <;> rfl
    · intro x; cases d.halted <;> rfl
    · cases d.halted <;> rfl
  | setStatus code reason =>
    intro d st hEnc hDec
    obtain ⟨hS, hC, hB, hH⟩ := hEnc
    have hin : st.memaddrs aStat = true := hS.1
    have hrun := run_guarded (d := d) o hH (sem_stC (v := BitVec.ofNat 64 code) o hin)
    refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
    · show CoreEnc _ _ _ _ _ (if d.halted then d
        else { d with resp := { d.resp with status := code, reason := reason } })
      cases hh : d.halted with
      | true => simp only [hh, if_true]; exact ⟨hS, hC, hB, hH⟩
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by decide)]
        rw [hh] at hH
        exact ⟨wordAt_hit hin, wordAt_frame hC (Ne.symm d_sc),
               wordAt_frame hB (Ne.symm d_sb), wordAt_frame hH (Ne.symm d_sh)⟩
    · cases d.halted <;> rfl
    · intro x; cases d.halted <;> rfl
    · cases d.halted <;> rfl
  | gate c code =>
    intro d st hEnc hDec
    obtain ⟨hS, hC, hB, hH⟩ := hEnc
    -- the gate's outer form is a `guarded` short-circuit around an inner decision cond
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
    -- the inner decision cond: fire → st2, else → st (unchanged)
    have hinner : PancakeSem o
        (.cond (.var (nm c)) (.seq (stC aStat (BitVec.ofNat 64 code)) (stC aHalt 1)) .skip) st
        = (none, if c ctx then st2 else st) := by
      rw [sem_cond o (eval_var (hDec c))]
      cases hc : c ctx with
      | true =>
        rw [if_pos (show (if (true : Bool) then (1 : Word) else 0) ≠ 0 from word_one_ne_zero),
            hseq, if_pos (rfl : (true : Bool) = true)]
      | false =>
        rw [if_neg (show ¬ ((if (false : Bool) then (1 : Word) else 0) ≠ 0) from fun h => h rfl),
            sem_skip o st, if_neg (show ¬ ((false : Bool) = true) by decide)]
    have hrun := run_guarded (d := d) o hH hinner
    refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
    · show CoreEnc _ _ _ _ _ (denoteStep ctx (.gate c code) d)
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
    · cases hh : d.halted <;> cases hc : c ctx <;> first | rfl | simp [hst1, hst2]
    · intro x; cases hh : d.halted <;> cases hc : c ctx <;> first | rfl | simp [hst1, hst2]
    · cases hh : d.halted <;> cases hc : c ctx <;> first | rfl | simp [hst1, hst2]
  | rewriteBody t =>
    intro d st hEnc hDec
    obtain ⟨hS, hC, hB, hH⟩ := hEnc
    cases t with
    | identity =>
      refine ⟨st, sem_skip o st, ?_, rfl, fun _ => rfl, rfl⟩
      show CoreEnc _ _ _ _ _ (if d.halted then d
        else { d with resp := { d.resp with body := runBody .identity d.resp.body } })
      cases hh : d.halted with
      | true => rw [if_pos (show (true : Bool) = true by decide)]; exact ⟨hS, hC, hB, hH⟩
      | false =>
        rw [if_neg (show ¬ ((false : Bool) = true) by decide)]
        rw [hh] at hH; exact ⟨hS, hC, hB, hH⟩
    | replace r =>
      have hin : st.memaddrs aBody = true := hB.1
      have hrun := run_guarded (d := d) o hH (sem_stC (v := BitVec.ofNat 64 r.length) o hin)
      refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
      · show CoreEnc _ _ _ _ _ (if d.halted then d
          else { d with resp := { d.resp with body := runBody (.replace r) d.resp.body } })
        cases hh : d.halted with
        | true => simp only [hh, if_true]; exact ⟨hS, hC, hB, hH⟩
        | false =>
          rw [if_neg (show ¬ ((false : Bool) = true) by decide)]
          rw [hh] at hH
          refine ⟨wordAt_frame hS d_sb, wordAt_frame hC d_cb, ?_,
                  wordAt_frame hH (Ne.symm d_bh)⟩
          show wordAt _ aBody (BitVec.ofNat 64 (runBody (.replace r) d.resp.body).length)
          show wordAt _ aBody (BitVec.ofNat 64 r.length)
          exact wordAt_hit hin
      · cases d.halted <;> rfl
      · intro x; cases d.halted <;> rfl
      · cases d.halted <;> rfl
    | append e =>
      have hval : eval st (.op .add (.loadWord (.const aBody)) (.const (BitVec.ofNat 64 e.length)))
          = some (BitVec.ofNat 64 (d.resp.body.length + e.length)) := by
        rw [eval_op_add (eval_loadWord_of_wordAt (eval_const aBody) hB)
              (eval_const (BitVec.ofNat 64 e.length)), ofNat_add_unc]
      have hin : st.memaddrs aBody = true := hB.1
      have hrun := run_guarded (d := d) o hH
        (Pancake.SerializeCompile.sem_store o (eval_const aBody) hval hin)
      refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
      · show CoreEnc _ _ _ _ _ (if d.halted then d
          else { d with resp := { d.resp with body := runBody (.append e) d.resp.body } })
        cases hh : d.halted with
        | true => simp only [hh, if_true]; exact ⟨hS, hC, hB, hH⟩
        | false =>
          rw [if_neg (show ¬ ((false : Bool) = true) by decide)]
          rw [hh] at hH
          refine ⟨wordAt_frame hS d_sb, wordAt_frame hC d_cb, ?_,
                  wordAt_frame hH (Ne.symm d_bh)⟩
          show wordAt _ aBody (BitVec.ofNat 64 (runBody (.append e) d.resp.body).length)
          show wordAt _ aBody (BitVec.ofNat 64 (d.resp.body ++ e).length)
          rw [List.length_append]; simpa using wordAt_hit hin
      · cases d.halted <;> rfl
      · intro x; cases d.halted <;> rfl
      · cases d.halted <;> rfl
  | seq a b iha ihb =>
    intro d st hEnc hDec
    obtain ⟨st1, ha_eq, ha_enc, ha_loc, ha_ma, ha_clk⟩ := iha d st hEnc hDec
    have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
      intro c; rw [ha_loc]; exact hDec c
    obtain ⟨st2, hb_eq, hb_enc, hb_loc, hb_ma, hb_clk⟩ :=
      ihb (denoteStep ctx a d) st1 ha_enc hDec1
    refine ⟨st2, ?_, ?_, ?_, ?_, ?_⟩
    · show PancakeSem o (.seq _ _) st = (none, st2)
      rw [sem_seq_none ha_eq]
      have hclamp : ({ st1 with clock := min st.clock st1.clock } : PancakeState σ) = st1 := by
        rw [ha_clk, Nat.min_self, ← ha_clk]
      rw [hclamp]; exact hb_eq
    · show CoreEnc _ _ _ _ _ (denoteStep ctx (.seq a b) d)
      rw [denoteStep_seq]; exact hb_enc
    · rw [hb_loc, ha_loc]
    · intro x; rw [hb_ma, ha_ma]
    · rw [hb_clk, ha_clk]
  | condR c a b iha ihb =>
    intro d st hEnc hDec
    cases hc : c ctx with
    | true =>
      obtain ⟨st', h1, h2, h3, h4, h5⟩ := iha d st hEnc hDec
      have hrun : PancakeSem o (compile2 nm aStat aCnt aBody aHalt (.condR c a b)) st
          = (none, st') := by
        show PancakeSem o (.cond (.var (nm c)) (compile2 nm aStat aCnt aBody aHalt a)
              (compile2 nm aStat aCnt aBody aHalt b)) st = (none, st')
        rw [sem_cond o (eval_var (hDec c)), hc,
            if_pos (show (if (true : Bool) then (1 : Word) else 0) ≠ 0 from word_one_ne_zero)]
        exact h1
      refine ⟨st', hrun, ?_, h3, h4, h5⟩
      show CoreEnc _ _ _ _ _ (denoteStep ctx (.condR c a b) d)
      rw [show denoteStep ctx (.condR c a b) d = denoteStep ctx a d from by
        show (if c ctx then denoteStep ctx a d else denoteStep ctx b d) = _; rw [hc]; rfl]
      exact h2
    | false =>
      obtain ⟨st', h1, h2, h3, h4, h5⟩ := ihb d st hEnc hDec
      have hrun : PancakeSem o (compile2 nm aStat aCnt aBody aHalt (.condR c a b)) st
          = (none, st') := by
        show PancakeSem o (.cond (.var (nm c)) (compile2 nm aStat aCnt aBody aHalt a)
              (compile2 nm aStat aCnt aBody aHalt b)) st = (none, st')
        rw [sem_cond o (eval_var (hDec c)), hc,
            if_neg (show ¬ ((if (false : Bool) then (1 : Word) else 0) ≠ 0) from fun h => h rfl)]
        exact h1
      refine ⟨st', hrun, ?_, h3, h4, h5⟩
      show CoreEnc _ _ _ _ _ (denoteStep ctx (.condR c a b) d)
      rw [show denoteStep ctx (.condR c a b) d = denoteStep ctx b d from by
        show (if c ctx then denoteStep ctx a d else denoteStep ctx b d) = _; rw [hc]; rfl]
      exact h2

/-! ## 5. Non-vacuity: the tracked skeleton genuinely varies with the program

The right-hand side of `compile2_correct` is the REAL `denoteStep`, so its scalar
image differs stage to stage — the theorem is not a `P → P` tautology. -/

-- The redirect stage genuinely drives status `308`, one header, empty body, live:
#guard (denote redirect ctxGet).status = 308
#guard (denote redirect ctxGet).headers.length = 1
#guard (denote redirect ctxGet).body.length = 0

-- The method gate on a POST genuinely SHORT-CIRCUITS to `405` (and halts):
#guard (denoteStep ctxPost methodFilter { resp := ctxPost.base, halted := false }).resp.status = 405
#guard (denoteStep ctxPost methodFilter { resp := ctxPost.base, halted := false }).halted = true
-- the base was 200 with a 2-byte body; the gate keeps the body, flips status:
#guard (denote methodFilter ctxPost).status = 405
#guard (denote methodFilter ctxPost).body.length = 2

-- the security-header chain genuinely adds two headers to the base (0 → 2):
#guard (denote securityHeaders ctxGet).headers.length = 2

-- the reference redirect DState the keystone lands (status/count/body/halt):
#guard (denoteStep ctxGet redirect { resp := ctxGet.base, halted := false }).resp.status = 308
#guard (denoteStep ctxGet redirect { resp := ctxGet.base, halted := false }).resp.headers.length = 1
#guard (denoteStep ctxGet redirect { resp := ctxGet.base, halted := false }).resp.body.length = 0
#guard (denoteStep ctxGet redirect { resp := ctxGet.base, halted := false }).halted = false

/-! ## 6. A general specialization at a named stage (the keystone, instantiated) -/

/-- **`redirect_compile2_correct`.** The general keystone specialized to the redirect
stage: from any `CoreEnc`-encoding of the base state, `compile2 redirect` lands the
redirect skeleton (`denote redirect ctx` = status 308, +1 header, empty body). -/
theorem redirect_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt redirect) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx redirect { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd redirect
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-! ## 7. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms compile2_correct
#print axioms redirect_compile2_correct
#print axioms ofNat_add_unc
#print axioms ofNat_add_unc

end Pancake.StageCompile
