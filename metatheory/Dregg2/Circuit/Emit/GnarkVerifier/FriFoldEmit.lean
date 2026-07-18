/-
# Dregg2.Circuit.Emit.GnarkVerifier.FriFoldEmit — the FRI arity-2 fold-consistency check,
Lean-authored, emitted as genuine R1CS, leaf-REFINED by a ∀-theorem.

THE CHECK (deployed: `chain/gnark/fri_query.go:136` `friFoldRowArity2`, consumed by the
fold loop of `chain/gnark/fri_verify_native.go:228` and checked against the claimed value
by `bb.ExtAssertIsEqual`, babybear_ext.go:96): one FRI commit-phase round's
fold-consistency — the claimed folded value equals the deployed linear combination of the
two siblings at the fold challenge β,

    folded = (e0 + e1)/2 + β·(e0 − e1)·inv(2s),

over the degree-4 BabyBear extension (X⁴ = 11), where `inv(s)` is the bit-selected
product of inverse two-adic-generator constants over the parent index bits
(`invS = Π_j Select(bit_j, ginv_{2+j}, 1)`, fri_query.go:138-142) and `inv(2s) =
(1/2)·inv(s)` via `MulConst(bbInv2, invS)`. Value mirror ground truth:
`friFoldCoreRef`/`invSFromParentRef` (chain/gnark/fri_query_ref.go:196-230).

This module (the `CanonicityToy` pattern, scaled to a composed gadget program):
  * §1 a ℕ value mirror of the deployed fold (`foldCoreV`, `invSV`) with the generator
    table + Fermat inverses `#guard`-KAT'd against Go-executed output, and gold fold
    vectors PRODUCED BY RUNNING the deployed `friFoldCoreRef` (2026-07-17);
  * §2 the circuit, BUILT FROM the committed `BabyBearFr` gadgets (`inputExt`, `gExtAdd`,
    `gExtSub`, `gExtMul`, `gMul`, `Wire.select` for the gnark `api.Select`) — node-for-node
    the `friFoldRowArity2` op-DAG, packaged as `GnarkCircuitData` (`friFoldData`);
  * §3–§5 a Hoare-style honest-run framework over the `BabyBearFr` builder monad
    (`StepTo`: state extension with all NEW asserts var-bounded and SATISFIED under the
    extended honest witness; `BBv`/`GEv`: a tracked element's wire evaluates to its
    canonical tracked value) with one spec lemma per committed gadget;
  * §6 **the leaf refinement theorem** `friFold_leaf_refines` — a genuine ∀-theorem over
    ALL canonical inputs and ALL parent-bit vectors, both polarities:

      gHolds (friFoldData s0 s1 β claimed bits) (friFoldAsg s0 s1 β claimed bits)
        ↔ foldCheckV s0 s1 β claimed bits = true

    plus the emitted-wire-form corollary (via the foundation's proven `emit_faithful`)
    and the reject corollary (`claimed ≠ fold ⇒ ¬ gHolds`).

Classified seams (named, not silent — the `BabyBearFr`/`CanonicityToy` ledger):
  * The ∀-theorem quantifies over the HONEST hint fill (the builder's generated witness —
    the Lean twin of gnark's hint solver / `test.IsSolved`), exactly the posture
    `BabyBearFr` names for all its gadgets; the adversarial-witness face of the reduce
    gadget stays the follow-up lane named in `BabyBearFr`'s header (the emitted circuit
    inherits `R1csFr.lower_sound` for the frontend→R1CS leg regardless).
  * Range checks realized as bit decomposition (deployed gnark: lookup argument) — the
    same semantic contract, the seam already named in `BabyBearFr`.
  * Parent-index bits are ingested with an explicit booleanity assert (`b·b = b`); in the
    deployed verifier their booleanity is established at challenger sampling.
-/
import Mathlib.Tactic.LinearCombination
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.BabyBearFr
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful

namespace Dregg2.Circuit.Emit.GnarkVerifier.FriFold

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.BabyBearFr

/-! ## §1 Value layer — the deployed fold, mirrored over ℕ.

Ground truth: `chain/gnark/fri_query_ref.go` (`twoAdicGeneratorsRef`, `twoAdicGenInvRef`,
`bbInv2`, `invSFromParentRef`, `friFoldCoreRef`, `bbExtScaleRef`). All `#guard` literals
below are output of RUNNING the deployed Go (2026-07-17). -/

/-- `twoAdicGeneratorsRef` (fri_query_ref.go:73; plonky3 `TWO_ADIC_GENERATORS`,
baby-bear/src/baby_bear.rs:46): the canonical order-`2^bits` generators. -/
def genT : List ℕ :=
  [ 0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090,
    0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715,
    0x11c33e2a, 0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f,
    0x3e9430e8, 0xba067a3, 0x18adc27d, 0x21fd55bc, 0x4b859b3d, 0x3bd57996,
    0x4483d85a, 0x3a26eef8, 0x1a427a41 ]

/-- `bbInv2 = 1/2 mod p = (p+1)/2` (fri_query_ref.go:85). -/
def inv2V : ℕ := 1006632961

/-- Square-and-multiply modular exponentiation mod `pBB`, fuel-structural so the kernel
computes it (`#guard`s below). The accumulator stays `< pBB` (`modPowAux_lt`). -/
def modPowAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, b, e, acc =>
      modPowAux f (b * b % pBB) (e / 2) (if e % 2 == 1 then acc * b % pBB else acc)

/-- Fermat inverse `a^(p−2) mod p` (the Go `bbInvRef`, fri_query_ref.go:97; 31 fuel steps
cover the 31-bit exponent `p − 2`). -/
def bbInvV (a : ℕ) : ℕ := modPowAux 31 a (pBB - 2) 1

/-- `twoAdicGenInvRef[j]` — the inverse-generator table entry (fri_query_ref.go:82). -/
def ginvT (j : ℕ) : ℕ := bbInvV (genT.getD j 0)

theorem modPowAux_lt (f : ℕ) : ∀ b e acc : ℕ, acc < pBB → modPowAux f b e acc < pBB := by
  induction f with
  | zero => intro _ _ _ h; exact h
  | succ f ih =>
      intro b e acc hacc
      unfold modPowAux
      exact ih _ _ _ (by split <;> [exact Nat.mod_lt _ (by decide); exact hacc])

theorem ginvT_lt (j : ℕ) : ginvT j < pBB := modPowAux_lt 31 _ _ 1 (by decide)

-- Generator table pins (decimal literals: deployed Go output, indices 2–7 — the ones the
-- fold's `twoAdicGenInvGadget[2+j]` selection reaches first).
#guard genT.getD 2 0 == 1728404513 && genT.getD 3 0 == 1592366214
  && genT.getD 4 0 == 196396260 && genT.getD 5 0 == 760005850
  && genT.getD 6 0 == 1721589904 && genT.getD 7 0 == 397765732
-- Inverse table KAT vs deployed Go `twoAdicGenInvRef` (Go-executed output).
#guard ginvT 2 == 284861408 && ginvT 3 == 1801542727 && ginvT 4 == 567209306
  && ginvT 5 == 1273220281 && ginvT 6 == 662200255 && ginvT 7 == 1856545343
-- The inverse property itself (mirror of fri_query_test.go:135's table check).
#guard (List.range 28).all fun j => j == 0 || bbMul (genT.getD j 0) (ginvT j) == 1

/-- One selection factor of the invS chain: `Select(bit_j, ginv_{2+j}, 1)`
(fri_query.go:140). -/
def invSFactorV (j : ℕ) (b : Bool) : ℕ := if b then ginvT (2 + j) else 1

/-- The bit-selected inverse-coset-point product `inv(s) = Π_j ginv_{2+j}^{bit_j}`
(`invSFromParentRef`, fri_query_ref.go:203; the gadget's running `bb.Mul` chain,
fri_query.go:138-142 — including the chain's leading `Mul(1, ·)`). -/
def invSVAux : ℕ → ℕ → List Bool → ℕ
  | _, acc, [] => acc
  | j, acc, b :: rest => invSVAux (j + 1) (bbMul acc (invSFactorV j b)) rest

def invSV (bits : List Bool) : ℕ := invSVAux 0 1 bits

theorem invSVAux_lt : ∀ (bits : List Bool) (j acc : ℕ), acc < pBB →
    invSVAux j acc bits < pBB := by
  intro bits
  induction bits with
  | nil => intro _ _ h; exact h
  | cons b rest ih => intro j acc _; exact ih _ _ (bbMul_lt _ _)

/-- `bbExtScaleRef` (fri_query_ref.go:233): base-scalar times extension element. -/
def extScaleV (s : ℕ) (a : ExtV) : ExtV :=
  ⟨bbMul s a.c0, bbMul s a.c1, bbMul s a.c2, bbMul s a.c3⟩

/-- **The deployed fold core** — `friFoldCoreRef` (fri_query_ref.go:221):
`(e0 + e1)/2 + β·(e0 − e1)·((1/2)·invS)`. -/
def foldCoreV (e0 e1 beta : ExtV) (invS : ℕ) : ExtV :=
  extAddV (extScaleV inv2V (extAddV e0 e1))
    (extScaleV (bbMul inv2V invS) (extMulV beta (extSubV e0 e1)))

/-- **The deployed fold-consistency check** (the spec of this leaf): the claimed folded
value equals the fold of the two siblings at β — `verifyAlgoO` fold-consistency, one
round. -/
def foldCheckV (s0 s1 beta claimed : ExtV) (bits : List Bool) : Bool :=
  decide (claimed = foldCoreV s0 s1 beta (invSV bits))

/-- All four coordinates canonical (the posture in which the deployed verifier's values
arrive at the fold — every producer is a `ReduceBounded` output or canonical ingestion). -/
def ExtCanon (v : ExtV) : Prop :=
  v.c0 < pBB ∧ v.c1 < pBB ∧ v.c2 < pBB ∧ v.c3 < pBB

-- GOLD fold vectors: output of RUNNING deployed `friFoldCoreRef`/`invSFromParentRef`
-- (chain/gnark, go test scratch harness, 2026-07-17).
-- parent = 5 (bits 1,0,1 → ginv₂·ginv₄):
#guard invSV [true, false, true] == 1934320121
#guard foldCoreV ⟨123, 456, 789, 1011⟩ ⟨2021, 2223, 2425, 2627⟩
    ⟨1234567890, 11111111, 222222222, 1999999999⟩ 1934320121
  == ⟨1739982707, 869530502, 1173455424, 1109545812⟩
-- all-zero bits (invS = 1):
#guard invSV [false, false, false] == 1
#guard foldCoreV ⟨123, 456, 789, 1011⟩ ⟨2021, 2223, 2425, 2627⟩
    ⟨1234567890, 11111111, 222222222, 1999999999⟩ 1
  == ⟨1716930976, 1464754115, 1668114350, 1489709974⟩
-- boundary coords (p−1 siblings), parent = 3 at lfh = 2 (ginv₂·ginv₃):
#guard invSV [true, true] == 420899707
#guard foldCoreV ⟨2013265920, 2013265920, 2013265920, 2013265920⟩
    ⟨987654321, 1888888888, 333333333, 44444444⟩ ⟨5, 6, 7, 8⟩ 420899707
  == ⟨721244950, 1391288293, 1968714273, 2009315255⟩

/-! ## §2 The circuit — `friFoldRowArity2` + `ExtAssertIsEqual`, from the committed
gadgets, in the deployed op order (fri_query.go:136-151). -/

/-- A constant as a tracked circuit element. -/
def constBB (c : ℕ) : BB := ⟨.const (c : Fr), c⟩

/-- Ingest one parent-index bit with the booleanity assert (`api.AssertIsBoolean`
posture; deployed booleanity comes from challenger sampling — classified seam). -/
def bitVarM (b : Bool) : M BB :=
  freshVar (if b then 1 else 0) >>= fun bw =>
  assertEq (.mul bw bw) bw >>= fun _ =>
  pure ⟨bw, if b then 1 else 0⟩

/-- `api.Select(bit, ginv_{2+j}, 1)` (fri_query.go:140) — the raw field mux over the two
constants, tracked at the honest bit value. -/
def selectFactor (j : ℕ) (b : Bool) (bv : BB) : BB :=
  ⟨.select bv.wire (.const ((ginvT (2 + j) : ℕ) : Fr)) (.const 1), invSFactorV j b⟩

/-- The invS chain: `invS := 1; for j: invS = bb.Mul(invS, Select(bit_j, ginv_{2+j}, 1))`
(fri_query.go:137-142), bits ingested as they are consumed. -/
def invSChainAux : ℕ → BB → List Bool → M BB
  | _, acc, [] => pure acc
  | j, acc, b :: rest =>
      bitVarM b >>= fun bv =>
      gMul acc (selectFactor j b bv) >>= fun acc' =>
      invSChainAux (j + 1) acc' rest

def invSChainM (bits : List Bool) : M BB := invSChainAux 0 (constBB 1) bits

/-- `ExtMulBase(s, a)` (babybear_ext.go:49): coefficient-wise `bb.Mul(s, aᵢ)`. -/
def gExtMulBase (sc : BB) (a : GExt) : M GExt :=
  gMul sc a.e0 >>= fun r0 =>
  gMul sc a.e1 >>= fun r1 =>
  gMul sc a.e2 >>= fun r2 =>
  gMul sc a.e3 >>= fun r3 =>
  pure ⟨r0, r1, r2, r3⟩

/-- `ExtAssertIsEqual` (babybear_ext.go:96): four per-lane `AssertIsEqual`s. -/
def extAssertEqM (a b : GExt) : M Unit :=
  assertEq a.e0.wire b.e0.wire >>= fun _ =>
  assertEq a.e1.wire b.e1.wire >>= fun _ =>
  assertEq a.e2.wire b.e2.wire >>= fun _ =>
  assertEq a.e3.wire b.e3.wire

/-- **The one-round fold-consistency program** — ingest the two siblings, β and the
claimed folded value (canonical ingestion), form `invS` from the parent bits, fold
exactly as `friFoldRowArity2` (halfInvS → sum → diff → betaTerm → the two `ExtMulBase`
legs → `ExtAdd`), and assert the claimed value equal to the fold. Returns the four
ingested inputs (for the emission metadata). -/
def foldRoundM (s0 s1 beta claimed : ExtV) (bits : List Bool) :
    M (GExt × GExt × GExt × GExt) :=
  inputExt s0 >>= fun g0 =>
  inputExt s1 >>= fun g1 =>
  inputExt beta >>= fun gb =>
  inputExt claimed >>= fun gc =>
  invSChainM bits >>= fun invS =>
  gMul (constBB inv2V) invS >>= fun halfInvS =>
  gExtAdd g0 g1 >>= fun sum =>
  gExtSub g0 g1 >>= fun diff =>
  gExtMul gb diff >>= fun betaTerm =>
  gExtMulBase (constBB inv2V) sum >>= fun sumHalf =>
  gExtMulBase halfInvS betaTerm >>= fun btScaled =>
  gExtAdd sumHalf btScaled >>= fun folded =>
  extAssertEqM folded gc >>= fun _ =>
  pure (g0, g1, gb, gc)

/-- The built package run: circuit + generated honest witness + the input records. -/
def friFoldRun (s0 s1 beta claimed : ExtV) (bits : List Bool) :
    RunOut (GExt × GExt × GExt × GExt) :=
  runM (foldRoundM s0 s1 beta claimed bits)

def friFoldCircuit (s0 s1 beta claimed : ExtV) (bits : List Bool) : Circuit :=
  (friFoldRun s0 s1 beta claimed bits).circ

/-- The generated honest witness (the Lean twin of gnark's hint solver fill). -/
def friFoldAsg (s0 s1 beta claimed : ExtV) (bits : List Bool) : Assignment :=
  (friFoldRun s0 s1 beta claimed bits).asg

def idxOf (b : BB) : ℕ := match b.wire with | .var k => k | _ => 0

def extIdx (g : GExt) : List ℕ := [idxOf g.e0, idxOf g.e1, idxOf g.e2, idxOf g.e3]

/-- **The emission package** for the one-round fold-consistency check. -/
def friFoldData (s0 s1 beta claimed : ExtV) (bits : List Bool) : GnarkCircuitData :=
  let ro := friFoldRun s0 s1 beta claimed bits
  let (g0, g1, gb, gc) := ro.out
  { name         := "fri_fold_arity2_round_v1"
    publicInputs :=
      (extIdx g0).zipIdx.map (fun p => (s!"sibling0_{p.2}", p.1))
        ++ (extIdx g1).zipIdx.map (fun p => (s!"sibling1_{p.2}", p.1))
        ++ (extIdx gb).zipIdx.map (fun p => (s!"beta_{p.2}", p.1))
        ++ (extIdx gc).zipIdx.map (fun p => (s!"folded_claim_{p.2}", p.1))
    gadgets      :=
      [ ⟨"FriFoldRowArity2", extIdx g0 ++ extIdx g1 ++ extIdx gb⟩,
        ⟨"ExtAssertIsEqual", extIdx gc⟩ ]
    circuit      := ro.circ }

/-! ## §3 Honest-run framework — states, var-bounded wires, the `StepTo` extension order. -/

/-- The honest witness a builder state denotes (index = mint order). -/
def asgOf (s : St) : Assignment := fun v => s.assigns.getD v 0

/-- Every variable mentioned by the wire is below `n`. -/
def wLt : Wire → ℕ → Prop
  | .var v, n => v < n
  | .const _, _ => True
  | .add x y, n => wLt x n ∧ wLt y n
  | .mul x y, n => wLt x n ∧ wLt y n
  | .select b x y, n => wLt b n ∧ wLt x n ∧ wLt y n

theorem wLt_mono : ∀ (w : Wire) {n m : ℕ}, wLt w n → n ≤ m → wLt w m
  | .var _, _, _, h, hnm => Nat.lt_of_lt_of_le h hnm
  | .const _, _, _, _, _ => trivial
  | .add x y, _, _, h, hnm => ⟨wLt_mono x h.1 hnm, wLt_mono y h.2 hnm⟩
  | .mul x y, _, _, h, hnm => ⟨wLt_mono x h.1 hnm, wLt_mono y h.2 hnm⟩
  | .select b x y, _, _, h, hnm =>
      ⟨wLt_mono b h.1 hnm, wLt_mono x h.2.1 hnm, wLt_mono y h.2.2 hnm⟩

/-- Var-bounded wires evaluate identically under assignments agreeing below the bound. -/
theorem eval_congr : ∀ (w : Wire) {n : ℕ}, wLt w n → ∀ {a b : Assignment},
    (∀ v, v < n → a v = b v) → w.eval a = w.eval b
  | .var v, _, h, _, _, hab => hab v h
  | .const _, _, _, _, _, _ => rfl
  | .add x y, _, h, _, _, hab => by
      simp only [Wire.eval, eval_congr x h.1 hab, eval_congr y h.2 hab]
  | .mul x y, _, h, _, _, hab => by
      simp only [Wire.eval, eval_congr x h.1 hab, eval_congr y h.2 hab]
  | .select b x y, _, h, _, _, hab => by
      simp only [Wire.eval, eval_congr b h.1 hab, eval_congr x h.2.1 hab,
        eval_congr y h.2.2 hab]

private theorem getD_append_lt (xs ys : List Fr) (i : ℕ) (h : i < xs.length) :
    (xs ++ ys).getD i 0 = xs.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_concat (l : List Fr) (x : Fr) : (l ++ [x]).getD l.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

/-- Assignments agree below the shorter length along a prefix extension. -/
theorem asg_prefix {s t : St} (h : s.assigns <+: t.assigns) :
    ∀ v, v < s.assigns.length → asgOf t v = asgOf s v := by
  obtain ⟨u, hu⟩ := h
  intro v hv
  simp only [asgOf, ← hu, getD_append_lt _ _ _ hv]

/-- **The honest-run extension order**: `t` extends `s` with new mints and new asserts,
every NEW assert var-bounded by the extended mint count and SATISFIED under the extended
honest witness. Chaining `StepTo ⟨[],[]⟩ t` says the whole accumulated circuit is
satisfied by the generated witness. -/
structure StepTo (s t : St) : Prop where
  apfx  : s.assigns <+: t.assigns
  newOk : ∃ Δ, t.asserts = s.asserts ++ Δ ∧
      ∀ p ∈ Δ, (wLt p.1 t.assigns.length ∧ wLt p.2 t.assigns.length) ∧
        p.1.eval (asgOf t) = p.2.eval (asgOf t)

theorem StepTo.refl (s : St) : StepTo s s :=
  ⟨List.prefix_rfl, [], by simp, by simp⟩

theorem StepTo.len_le {s t : St} (h : StepTo s t) :
    s.assigns.length ≤ t.assigns.length := h.apfx.length_le

theorem StepTo.trans {s t u : St} (h1 : StepTo s t) (h2 : StepTo t u) : StepTo s u := by
  refine ⟨h1.apfx.trans h2.apfx, ?_⟩
  obtain ⟨Δ1, he1, hp1⟩ := h1.newOk
  obtain ⟨Δ2, he2, hp2⟩ := h2.newOk
  refine ⟨Δ1 ++ Δ2, by rw [he2, he1, List.append_assoc], ?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨⟨hl, hr⟩, hev⟩ := hp1 p hp
    refine ⟨⟨wLt_mono _ hl h2.len_le, wLt_mono _ hr h2.len_le⟩, ?_⟩
    rw [eval_congr _ hl (asg_prefix h2.apfx), eval_congr _ hr (asg_prefix h2.apfx)]
    exact hev
  · exact hp2 p hp

/-- From the empty state, `StepTo` IS satisfaction of the accumulated circuit. -/
theorem StepTo.sat_of_nil {t : St} (h : StepTo ⟨[], []⟩ t) :
    ∀ p ∈ t.asserts, p.1.eval (asgOf t) = p.2.eval (asgOf t) := by
  obtain ⟨Δ, he, hp⟩ := h.newOk
  intro p hpm
  exact (hp p (by simpa [he] using hpm)).2

/-- A tracked element is GOOD at a state: wire var-bounded, wire evaluates to the tracked
value under the honest witness, value canonical. -/
structure BBv (s : St) (x : BB) : Prop where
  wlt : wLt x.wire s.assigns.length
  ev  : x.wire.eval (asgOf s) = (x.val : Fr)
  lt  : x.val < pBB

theorem BBv.mono {s t : St} {x : BB} (h : BBv s x) (st : StepTo s t) : BBv t x :=
  ⟨wLt_mono _ h.wlt st.len_le,
   (eval_congr _ h.wlt (asg_prefix st.apfx)).trans h.ev, h.lt⟩

/-- All four coordinates good. -/
structure GEv (s : St) (g : GExt) : Prop where
  b0 : BBv s g.e0
  b1 : BBv s g.e1
  b2 : BBv s g.e2
  b3 : BBv s g.e3

theorem GEv.mono {s t : St} {g : GExt} (h : GEv s g) (st : StepTo s t) : GEv t g :=
  ⟨h.b0.mono st, h.b1.mono st, h.b2.mono st, h.b3.mono st⟩

theorem GEv.canon {s : St} {g : GExt} (h : GEv s g) : ExtCanon g.vals :=
  ⟨h.b0.lt, h.b1.lt, h.b2.lt, h.b3.lt⟩

/-! ## §4 Run equations + primitive specs. -/

private theorem runBind {α β : Type} (m : M α) (f : α → M β) (s : St) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl

private theorem runPure {α : Type} (a : α) (s : St) :
    (pure a : M α).run s = (a, s) := rfl

private theorem runFreshVar (v : Fr) (s : St) :
    (freshVar v).run s = (Wire.var s.assigns.length, ⟨s.assigns ++ [v], s.asserts⟩) := rfl

private theorem runAssertEq (l r : Wire) (s : St) :
    (assertEq l r).run s = ((), ⟨s.assigns, s.asserts ++ [(l, r)]⟩) := rfl

/-- `freshVar` extends honestly: the minted wire is the next index, evaluates to the
minted value, and no assert is added. -/
theorem freshVar_spec (v : Fr) (s : St) :
    StepTo s ((freshVar v).run s).2 ∧
    ((freshVar v).run s).1 = Wire.var s.assigns.length ∧
    wLt ((freshVar v).run s).1 ((freshVar v).run s).2.assigns.length ∧
    ((freshVar v).run s).1.eval (asgOf ((freshVar v).run s).2) = v := by
  rw [runFreshVar]
  refine ⟨⟨⟨[v], rfl⟩, [], by simp, by simp⟩, rfl, ?_, ?_⟩
  · simp [wLt]
  · simpa [Wire.eval, asgOf] using getD_concat s.assigns v

/-- `assertEq` on a pair that HOLDS under the current honest witness is a `StepTo`. -/
theorem assertEq_spec (l r : Wire) (s : St)
    (hl : wLt l s.assigns.length) (hr : wLt r s.assigns.length)
    (h : l.eval (asgOf s) = r.eval (asgOf s)) :
    StepTo s ((assertEq l r).run s).2 := by
  rw [runAssertEq]
  exact ⟨List.prefix_rfl, [(l, r)], rfl, by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨⟨hl, hr⟩, h⟩⟩

/-! ## §4b The `rangeCheck` loop — the bit-decomposition engine every gadget rides. -/

/-- The loop body of `BabyBearFr.rangeCheck` (mint the honest `i`-th bit, assert it
boolean, extend the recomposition wire). -/
private def rcBody (v : ℕ) : ℕ → Wire → M (ForInStep Wire) := fun i r =>
  freshVar (((v >>> i) &&& 1 : ℕ) : Fr) >>= fun bw =>
  assertEq (.mul bw bw) bw >>= fun _ =>
  pure (.yield (.add r (.mul (.const ((2 ^ i : ℕ) : Fr)) bw)))

private theorem rangeCheck_eq (w : Wire) (v bits : ℕ) :
    rangeCheck w v bits
      = (forIn (List.range bits) (Wire.const 0) (rcBody v) >>= fun r => assertEq w r) :=
  rfl

/-- The ℕ recomposition value the loop accumulates over an index list. -/
private def bitsum (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: L => 2 ^ i * ((v >>> i) &&& 1) + bitsum v L

private theorem bitsum_append (v : ℕ) (L1 L2 : List ℕ) :
    bitsum v (L1 ++ L2) = bitsum v L1 + bitsum v L2 := by
  induction L1 with
  | nil => simp [bitsum]
  | cons i L ih => simp only [List.cons_append, bitsum, ih]; omega

private theorem bitsum_range (v : ℕ) : ∀ n : ℕ, bitsum v (List.range n) = v % 2 ^ n
  | 0 => by simp [bitsum, Nat.mod_one]
  | n + 1 => by
      rw [List.range_succ, bitsum_append, bitsum_range v n]
      simp only [bitsum, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
      have : v % 2 ^ (n + 1) = v % 2 ^ n + 2 ^ n * (v / 2 ^ n % 2) := by
        rw [pow_succ, Nat.mod_mul]
      omega

/-- The loop's honest-run spec, generalized over the index list and the running
recomposition wire: the state extends honestly (booleanity asserts satisfied by the
honest bits) and the final recomposition wire evaluates to the initial one plus the
bit-weighted sum. -/
private theorem rcLoop_spec (v : ℕ) : ∀ (L : List ℕ) (s : St) (r₀ : Wire),
    wLt r₀ s.assigns.length →
    StepTo s ((forIn L r₀ (rcBody v) : M Wire).run s).2 ∧
    wLt ((forIn L r₀ (rcBody v) : M Wire).run s).1
      ((forIn L r₀ (rcBody v) : M Wire).run s).2.assigns.length ∧
    ((forIn L r₀ (rcBody v) : M Wire).run s).1.eval
        (asgOf ((forIn L r₀ (rcBody v) : M Wire).run s).2)
      = r₀.eval (asgOf s) + ((bitsum v L : ℕ) : Fr) := by
  intro L
  induction L with
  | nil =>
      intro s r₀ hr
      refine ⟨StepTo.refl s, hr, ?_⟩
      show r₀.eval (asgOf s) = r₀.eval (asgOf s) + ((bitsum v [] : ℕ) : Fr)
      simp [bitsum]
  | cons i L ih =>
      intro s r₀ hr
      have hbody : (rcBody v i r₀).run s
          = (ForInStep.yield
               (.add r₀ (.mul (.const ((2 ^ i : ℕ) : Fr)) (.var s.assigns.length))),
             ⟨s.assigns ++ [(((v >>> i) &&& 1 : ℕ) : Fr)],
              s.asserts ++ [(.mul (.var s.assigns.length) (.var s.assigns.length),
                             .var s.assigns.length)]⟩) := rfl
      rw [List.forIn_cons, runBind, hbody]
      set s₁ : St :=
        ⟨s.assigns ++ [(((v >>> i) &&& 1 : ℕ) : Fr)],
         s.asserts ++ [(.mul (.var s.assigns.length) (.var s.assigns.length),
                        .var s.assigns.length)]⟩ with hs₁
      set r₁ : Wire := .add r₀ (.mul (.const ((2 ^ i : ℕ) : Fr)) (.var s.assigns.length))
        with hr₁
      have hbit : asgOf s₁ s.assigns.length = (((v >>> i) &&& 1 : ℕ) : Fr) := by
        simpa [asgOf, hs₁] using
          getD_concat s.assigns (((v >>> i) &&& 1 : ℕ) : Fr)
      have hstep1 : StepTo s s₁ := by
        refine ⟨⟨_, rfl⟩, [(.mul (.var s.assigns.length) (.var s.assigns.length),
                            .var s.assigns.length)], rfl, ?_⟩
        intro p hp
        rcases List.mem_singleton.mp hp with rfl
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · simp [wLt, hs₁]
        · simp [wLt, hs₁]
        · simp [wLt, hs₁]
        · simp only [Wire.eval, hbit]
          rcases Nat.and_one_is_mod (v >>> i) ▸ Nat.mod_two_eq_zero_or_one (v >>> i)
            with h | h <;> rw [h] <;> norm_num
      have hlen1 : s₁.assigns.length = s.assigns.length + 1 := by simp [hs₁]
      have hr₁lt : wLt r₁ s₁.assigns.length := by
        refine ⟨wLt_mono _ hr (by omega), trivial, ?_⟩
        show s.assigns.length < s₁.assigns.length
        omega
      obtain ⟨hstepL, hwltL, hevalL⟩ := ih s₁ r₁ hr₁lt
      refine ⟨hstep1.trans hstepL, hwltL, ?_⟩
      rw [hevalL]
      have hr₀ : r₀.eval (asgOf s₁) = r₀.eval (asgOf s) :=
        eval_congr _ hr (asg_prefix hstep1.apfx)
      simp only [hr₁, Wire.eval, hr₀, hbit, bitsum]
      push_cast
      ring

/-- `rangeCheck w v bits` with an in-range honest value is an honest `StepTo`. -/
theorem rangeCheck_spec (w : Wire) (v bits : ℕ) (s : St)
    (hw : wLt w s.assigns.length) (hev : w.eval (asgOf s) = (v : Fr))
    (hv : v < 2 ^ bits) :
    StepTo s ((rangeCheck w v bits).run s).2 := by
  rw [rangeCheck_eq, runBind]
  obtain ⟨hstep, hwlt, heval⟩ := rcLoop_spec v (List.range bits) s (Wire.const 0) trivial
  refine hstep.trans (assertEq_spec _ _ _ (wLt_mono _ hw hstep.len_le) hwlt ?_)
  rw [eval_congr _ hw (asg_prefix hstep.apfx), hev, heval, bitsum_range,
    Nat.mod_eq_of_lt hv]
  simp [Wire.eval]

/-! ## §5 Gadget specs — one honest-run lemma per committed `BabyBearFr` gadget. -/

private theorem pBB_eq : pBB = 2013265921 := rfl

private theorem h2p31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num

instance : NeZero rBN254 := ⟨by norm_num [rBN254]⟩

private theorem pBB_lt_r : pBB < rBN254 := by
  rw [pBB_eq, rBN254]; norm_num

/-- ℕ-cast injectivity below the BN254 scalar modulus. -/
private theorem cast_inj_lt {x y : ℕ} (hx : x < rBN254) (hy : y < rBN254)
    (h : (x : Fr) = (y : Fr)) : x = y := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hx, ZMod.val_cast_of_lt hy] at h'

private theorem mul_lt_2p62 {a b : ℕ} (ha : a < pBB) (hb : b < pBB) :
    a * b < 2 ^ 62 := by
  rw [pBB_eq] at ha hb
  calc a * b ≤ 2013265920 * 2013265920 := Nat.mul_le_mul (by omega) (by omega)
    _ < 2 ^ 62 := by norm_num

private theorem mod_congr {x y : ℕ} (h : (x : ZMod pBB) = (y : ZMod pBB)) :
    x % pBB = y % pBB :=
  (ZMod.natCast_eq_natCast_iff x y pBB).mp h

/-- `assertIsCanonical` on a canonical honest value is an honest `StepTo`
(babybear.go:69: both 31-bit range checks pass). -/
theorem assertIsCanonical_spec (w : Wire) (v : ℕ) (s : St)
    (hw : wLt w s.assigns.length) (hev : w.eval (asgOf s) = (v : Fr)) (hv : v < pBB) :
    StepTo s ((assertIsCanonical w v).run s).2 := by
  have heq : assertIsCanonical w v
      = (rangeCheck w v 31 >>= fun _ =>
         rangeCheck (.add (.const ((pBB - 1 : ℕ) : Fr)) (.mul (.const (-1)) w))
           (pBB - 1 - v) 31) := rfl
  rw [heq, runBind]
  have hv31 : v < 2 ^ 31 := by rw [h2p31]; rw [pBB_eq] at hv; omega
  have h1 := rangeCheck_spec w v 31 s hw hev hv31
  have hle : v ≤ pBB - 1 := by rw [pBB_eq] at hv ⊢; omega
  refine h1.trans (rangeCheck_spec _ (pBB - 1 - v) 31 _ ⟨trivial, trivial, ?_⟩ ?_ ?_)
  · exact wLt_mono _ hw h1.len_le
  · show ((pBB - 1 : ℕ) : Fr) + (-1) * w.eval (asgOf ((rangeCheck w v 31).run s).2)
      = ((pBB - 1 - v : ℕ) : Fr)
    rw [eval_congr _ hw (asg_prefix h1.apfx), hev, Nat.cast_sub hle]
    ring
  · rw [h2p31]; rw [pBB_eq] at hv ⊢; omega

/-- `reduceBounded x xv bB` (31 < bB, the shape every caller uses) under an honest
in-range value: honest `StepTo`, canonical tracked output `xv % p`. Stated as a run
EQUATION with an opaque final state so consumers never carry the expanded run term. -/
theorem reduceBounded_spec (x : Wire) (xv bB : ℕ) (s : St) (hbB : 31 < bB)
    (hx : wLt x s.assigns.length) (hev : x.eval (asgOf s) = (xv : Fr))
    (hxv : xv < 2 ^ bB) :
    ∃ out t, (reduceBounded x xv bB).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = xv % pBB := by
  -- arithmetic facts first (before any run terms enter the context)
  have hrlt : xv % pBB < pBB := Nat.mod_lt _ (by decide)
  have hq : xv / pBB < 2 ^ (bB - 30) := by
    by_contra hge
    push_neg at hge
    have h1 : 2 ^ (bB - 30) * pBB ≤ xv / pBB * pBB := Nat.mul_le_mul hge (Nat.le_refl _)
    have h2 : xv / pBB * pBB ≤ xv := Nat.div_mul_le_self xv pBB
    have h3 : 2 ^ (bB - 30) * 2 ^ 30 ≤ 2 ^ (bB - 30) * pBB :=
      Nat.mul_le_mul (Nat.le_refl _) (by decide)
    have h4 : 2 ^ (bB - 30) * 2 ^ 30 = 2 ^ bB := by
      rw [← pow_add]; congr 1; omega
    omega
  have heq : reduceBounded x xv bB
      = (freshVar ((xv / pBB : ℕ) : Fr) >>= fun wq =>
         freshVar ((xv % pBB : ℕ) : Fr) >>= fun wr =>
         assertEq x (.add (.mul wq (.const ((pBB : ℕ) : Fr))) wr) >>= fun _ =>
         assertIsCanonical wr (xv % pBB) >>= fun _ =>
         rangeCheck wq (xv / pBB) (bB - 30) >>= fun _ =>
         pure ⟨wr, xv % pBB⟩) := by
    simp only [reduceBounded]
    rw [if_neg (by omega : ¬ bB < 31)]
    simp only [if_neg (show ¬ bB ≤ 31 by omega)]
  rw [heq]
  simp only [runBind, runFreshVar, runAssertEq, runPure, List.length_append,
    List.length_cons, List.length_nil, Nat.zero_add]
  set n := s.assigns.length with hn
  set s₂ : St := ⟨s.assigns ++ [((xv / pBB : ℕ) : Fr)] ++ [((xv % pBB : ℕ) : Fr)],
                  s.asserts⟩ with hs₂
  have hlen2 : s₂.assigns.length = n + 2 := by simp [hs₂, hn]
  have hs02 : StepTo s s₂ :=
    ⟨⟨[((xv / pBB : ℕ) : Fr)] ++ [((xv % pBB : ℕ) : Fr)], by simp [hs₂]⟩,
     [], by simp [hs₂], by simp⟩
  -- the two minted hint wires and their honest values
  have hwq : asgOf s₂ n = ((xv / pBB : ℕ) : Fr) := by
    show (s.assigns ++ [((xv / pBB : ℕ) : Fr)] ++ [((xv % pBB : ℕ) : Fr)]).getD n 0 = _
    rw [getD_append_lt (s.assigns ++ [((xv / pBB : ℕ) : Fr)]) _ n (by simp [hn]), hn]
    exact getD_concat s.assigns _
  have hwr : asgOf s₂ (n + 1) = ((xv % pBB : ℕ) : Fr) := by
    show (s.assigns ++ [((xv / pBB : ℕ) : Fr)] ++ [((xv % pBB : ℕ) : Fr)]).getD (n + 1) 0
      = _
    have hl : (s.assigns ++ [((xv / pBB : ℕ) : Fr)]).length = n + 1 := by simp [hn]
    rw [← hl]
    exact getD_concat _ _
  -- the reduce equation assert is honest: q·p + r = xv
  have hqpr : (Wire.add (.mul (.var n) (.const ((pBB : ℕ) : Fr))) (.var (n + 1))).eval
      (asgOf s₂) = (xv : Fr) := by
    simp only [Wire.eval, hwq, hwr]
    have : ((xv / pBB * pBB + xv % pBB : ℕ) : Fr) = (xv : Fr) := by
      rw [Nat.div_add_mod']
    push_cast at this ⊢
    linear_combination this
  have hxev2 : x.eval (asgOf s₂) = (xv : Fr) := by
    rw [eval_congr _ hx (asg_prefix hs02.apfx), hev]
  set s₃ : St := ⟨s.assigns ++ [((xv / pBB : ℕ) : Fr)] ++ [((xv % pBB : ℕ) : Fr)],
      s.asserts
        ++ [(x, .add (.mul (.var n) (.const ((pBB : ℕ) : Fr))) (.var (n + 1)))]⟩ with hs₃
  have hstA : StepTo s₂ s₃ := by
    refine assertEq_spec _ _ _ (wLt_mono _ hx (by omega)) ⟨⟨?_, trivial⟩, ?_⟩
      (hxev2.trans hqpr.symm)
    · show n < s₂.assigns.length; omega
    · show n + 1 < s₂.assigns.length; omega
  have hlen3 : s₃.assigns.length = n + 2 := by
    simp [hs₃, hn]
  have hwr3 : (Wire.var (n + 1)).eval (asgOf s₃) = ((xv % pBB : ℕ) : Fr) := by
    have h := asg_prefix hstA.apfx (n + 1) (by omega)
    simpa [Wire.eval, h] using hwr
  have hstC := assertIsCanonical_spec (.var (n + 1)) (xv % pBB) s₃
    (by show n + 1 < s₃.assigns.length; omega) hwr3 hrlt
  -- opacify the canonicity-check run state (its expansion is a 62-step loop)
  obtain ⟨s₄, hrun₄⟩ :
      ∃ t, ((assertIsCanonical (.var (n + 1)) (xv % pBB)).run s₃).2 = t := ⟨_, rfl⟩
  rw [hrun₄] at hstC ⊢
  have hn4 : n + 2 ≤ s₄.assigns.length := by
    have h1 := hstC.len_le
    omega
  have hwq4 : (Wire.var n).eval (asgOf s₄) = ((xv / pBB : ℕ) : Fr) := by
    have h3 := asg_prefix hstA.apfx n (by omega)
    have h4 := asg_prefix hstC.apfx n (by omega)
    simp only [Wire.eval, h4, h3]
    exact hwq
  have hstR := rangeCheck_spec (.var n) (xv / pBB) (bB - 30) s₄
    (by show n < s₄.assigns.length; omega) hwq4 hq
  obtain ⟨s₅, hrun₅⟩ :
      ∃ t, ((rangeCheck (.var n) (xv / pBB) (bB - 30)).run s₄).2 = t := ⟨_, rfl⟩
  rw [hrun₅] at hstR ⊢
  have hAll : StepTo s s₅ := ((hs02.trans hstA).trans hstC).trans hstR
  have hCR : StepTo s₂ s₅ := (hstA.trans hstC).trans hstR
  refine ⟨⟨.var (n + 1), xv % pBB⟩, s₅, rfl, hAll, ⟨?_, ?_, hrlt⟩, rfl⟩
  · show n + 1 < s₅.assigns.length
    have := hCR.len_le; omega
  · show (Wire.var (n + 1)).eval (asgOf s₅) = ((xv % pBB : ℕ) : Fr)
    have h := asg_prefix hCR.apfx (n + 1) (by omega)
    simpa [Wire.eval, h] using hwr

private theorem h2p32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num

/-- `FromCanonicalU32` (babybear.go:76): mint + canonicity — honest for canonical `v`. -/
theorem inputU32_spec (v : ℕ) (s : St) (hv : v < pBB) :
    ∃ out t, (inputU32 v).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧ out.val = v := by
  have heq : inputU32 v
      = (freshVar ((v : ℕ) : Fr) >>= fun w =>
         assertIsCanonical w v >>= fun _ => pure ⟨w, v⟩) := rfl
  rw [heq]
  simp only [runBind, runFreshVar, runPure]
  set s₁ : St := ⟨s.assigns ++ [((v : ℕ) : Fr)], s.asserts⟩ with hs₁
  have hs01 : StepTo s s₁ := ⟨⟨[((v : ℕ) : Fr)], rfl⟩, [], by simp [hs₁], by simp⟩
  have hbit : asgOf s₁ s.assigns.length = ((v : ℕ) : Fr) := by
    show (s.assigns ++ [((v : ℕ) : Fr)]).getD s.assigns.length 0 = _
    exact getD_concat s.assigns _
  have hwlt : wLt (Wire.var s.assigns.length) s₁.assigns.length := by
    show s.assigns.length < s₁.assigns.length
    simp [hs₁]
  have hstC := assertIsCanonical_spec (.var s.assigns.length) v s₁ hwlt hbit hv
  obtain ⟨t, hrun⟩ :
      ∃ t, ((assertIsCanonical (.var s.assigns.length) v).run s₁).2 = t := ⟨_, rfl⟩
  rw [hrun] at hstC ⊢
  refine ⟨⟨.var s.assigns.length, v⟩, t, rfl, hs01.trans hstC, ⟨?_, ?_, hv⟩, rfl⟩
  · exact wLt_mono _ hwlt hstC.len_le
  · exact (eval_congr _ hwlt (asg_prefix hstC.apfx)).trans hbit

private theorem extV_eta (v : ExtV) : ExtV.mk v.c0 v.c1 v.c2 v.c3 = v := rfl

/-- Canonical extension ingestion (the Go test circuits' posture). -/
theorem inputExt_spec (v : ExtV) (s : St) (hv : ExtCanon v) :
    ∃ out t, (inputExt v).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧ out.vals = v := by
  have heq : inputExt v
      = (inputU32 v.c0 >>= fun b0 => inputU32 v.c1 >>= fun b1 =>
         inputU32 v.c2 >>= fun b2 => inputU32 v.c3 >>= fun b3 =>
         pure ⟨b0, b1, b2, b3⟩) := rfl
  rw [heq]
  obtain ⟨o0, t0, hr0, hst0, hb0, hv0⟩ := inputU32_spec v.c0 s hv.1
  obtain ⟨o1, t1, hr1, hst1, hb1, hv1⟩ := inputU32_spec v.c1 t0 hv.2.1
  obtain ⟨o2, t2, hr2, hst2, hb2, hv2⟩ := inputU32_spec v.c2 t1 hv.2.2.1
  obtain ⟨o3, t3, hr3, hst3, hb3, hv3⟩ := inputU32_spec v.c3 t2 hv.2.2.2
  simp only [runBind, hr0, hr1, hr2, hr3, runPure]
  refine ⟨⟨o0, o1, o2, o3⟩, t3, rfl, ((hst0.trans hst1).trans hst2).trans hst3,
    ⟨hb0.mono ((hst1.trans hst2).trans hst3), hb1.mono (hst2.trans hst3),
     hb2.mono hst3, hb3⟩, ?_⟩
  show ExtV.mk o0.val o1.val o2.val o3.val = v
  rw [hv0, hv1, hv2, hv3, extV_eta]

/-- `BBApi.Mul` (babybear.go:123). -/
theorem gMul_spec (a b : BB) (s : St) (ha : BBv s a) (hb : BBv s b) :
    ∃ out t, (gMul a b).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = bbMul a.val b.val := by
  have hev : (Wire.mul a.wire b.wire).eval (asgOf s) = ((a.val * b.val : ℕ) : Fr) := by
    simp only [Wire.eval, ha.ev, hb.ev]
    push_cast
    ring
  exact reduceBounded_spec (.mul a.wire b.wire) (a.val * b.val) 62 s (by omega)
    ⟨ha.wlt, hb.wlt⟩ hev (mul_lt_2p62 ha.lt hb.lt)

/-- `BBApi.Add` (babybear.go:113). -/
theorem gAdd_spec (a b : BB) (s : St) (ha : BBv s a) (hb : BBv s b) :
    ∃ out t, (gAdd a b).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = bbAdd a.val b.val := by
  have hev : (Wire.add a.wire b.wire).eval (asgOf s) = ((a.val + b.val : ℕ) : Fr) := by
    simp only [Wire.eval, ha.ev, hb.ev]
    push_cast
    ring
  have hlt : a.val + b.val < 2 ^ 32 := by
    have h1 := ha.lt
    have h2 := hb.lt
    rw [pBB_eq] at h1 h2
    rw [h2p32]
    omega
  obtain ⟨out, t, hrun, hst, hbv, hval⟩ :=
    reduceBounded_spec (.add a.wire b.wire) (a.val + b.val) 32 s (by omega)
      ⟨ha.wlt, hb.wlt⟩ hev hlt
  exact ⟨out, t, hrun, hst, hbv, hval.trans (bbAdd_eq_mod ha.lt hb.lt).symm⟩

/-- `BBApi.Sub` (babybear.go:118). -/
theorem gSub_spec (a b : BB) (s : St) (ha : BBv s a) (hb : BBv s b) :
    ∃ out t, (gSub a b).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = bbSub a.val b.val := by
  have hble : b.val ≤ pBB := Nat.le_of_lt hb.lt
  have hev : (Wire.add a.wire
        (.add (.const ((pBB : ℕ) : Fr)) (.mul (.const (-1)) b.wire))).eval (asgOf s)
      = ((a.val + (pBB - b.val) : ℕ) : Fr) := by
    simp only [Wire.eval, ha.ev, hb.ev]
    rw [Nat.cast_add, Nat.cast_sub hble]
    ring
  have hlt : a.val + (pBB - b.val) < 2 ^ 32 := by
    have h1 := ha.lt
    rw [pBB_eq] at h1 hble ⊢
    rw [h2p32]
    omega
  obtain ⟨out, t, hrun, hst, hbv, hval⟩ :=
    reduceBounded_spec
      (.add a.wire (.add (.const ((pBB : ℕ) : Fr)) (.mul (.const (-1)) b.wire)))
      (a.val + (pBB - b.val)) 32 s (by omega)
      ⟨ha.wlt, trivial, trivial, hb.wlt⟩ hev hlt
  refine ⟨out, t, hrun, hst, hbv, ?_⟩
  rw [hval, show a.val + (pBB - b.val) = pBB + a.val - b.val by omega,
    ← bbSub_eq_mod ha.lt hb.lt]

/-- Four independent binary lanes then repackage — the shared shape of
`ExtAdd`/`ExtSub`/`ExtMulBase`. -/
private theorem quad_spec {op : BB → BB → M BB} {vop : ℕ → ℕ → ℕ}
    (hop : ∀ (x y : BB) (s : St), BBv s x → BBv s y →
      ∃ out t, (op x y).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
        out.val = vop x.val y.val)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BB) (s : St)
    (ha0 : BBv s a0) (ha1 : BBv s a1) (ha2 : BBv s a2) (ha3 : BBv s a3)
    (hb0 : BBv s b0) (hb1 : BBv s b1) (hb2 : BBv s b2) (hb3 : BBv s b3) :
    ∃ out t, (op a0 b0 >>= fun r0 => op a1 b1 >>= fun r1 => op a2 b2 >>= fun r2 =>
        op a3 b3 >>= fun r3 => (pure ⟨r0, r1, r2, r3⟩ : M GExt)).run s = (out, t) ∧
      StepTo s t ∧ GEv t out ∧
      out.vals = ⟨vop a0.val b0.val, vop a1.val b1.val, vop a2.val b2.val,
                  vop a3.val b3.val⟩ := by
  obtain ⟨o0, t0, hr0, hst0, hbv0, hval0⟩ := hop a0 b0 s ha0 hb0
  obtain ⟨o1, t1, hr1, hst1, hbv1, hval1⟩ := hop a1 b1 t0 (ha1.mono hst0) (hb1.mono hst0)
  obtain ⟨o2, t2, hr2, hst2, hbv2, hval2⟩ := hop a2 b2 t1
    (ha2.mono (hst0.trans hst1)) (hb2.mono (hst0.trans hst1))
  obtain ⟨o3, t3, hr3, hst3, hbv3, hval3⟩ := hop a3 b3 t2
    (ha3.mono ((hst0.trans hst1).trans hst2)) (hb3.mono ((hst0.trans hst1).trans hst2))
  simp only [runBind, hr0, hr1, hr2, hr3, runPure]
  refine ⟨⟨o0, o1, o2, o3⟩, t3, rfl, ((hst0.trans hst1).trans hst2).trans hst3,
    ⟨hbv0.mono ((hst1.trans hst2).trans hst3), hbv1.mono (hst2.trans hst3),
     hbv2.mono hst3, hbv3⟩, ?_⟩
  show ExtV.mk o0.val o1.val o2.val o3.val = _
  rw [hval0, hval1, hval2, hval3]

/-- `ExtAdd` (babybear_ext.go:31). -/
theorem gExtAdd_spec (a b : GExt) (s : St) (ha : GEv s a) (hb : GEv s b) :
    ∃ out t, (gExtAdd a b).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extAddV a.vals b.vals :=
  quad_spec gAdd_spec a.e0 a.e1 a.e2 a.e3 b.e0 b.e1 b.e2 b.e3 s
    ha.b0 ha.b1 ha.b2 ha.b3 hb.b0 hb.b1 hb.b2 hb.b3

/-- `ExtSub` (babybear_ext.go:40). -/
theorem gExtSub_spec (a b : GExt) (s : St) (ha : GEv s a) (hb : GEv s b) :
    ∃ out t, (gExtSub a b).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extSubV a.vals b.vals :=
  quad_spec gSub_spec a.e0 a.e1 a.e2 a.e3 b.e0 b.e1 b.e2 b.e3 s
    ha.b0 ha.b1 ha.b2 ha.b3 hb.b0 hb.b1 hb.b2 hb.b3

/-- `ExtMulBase` (babybear_ext.go:49). -/
theorem gExtMulBase_spec (sc : BB) (a : GExt) (s : St) (hsc : BBv s sc) (ha : GEv s a) :
    ∃ out t, (gExtMulBase sc a).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extScaleV sc.val a.vals :=
  quad_spec gMul_spec sc sc sc sc a.e0 a.e1 a.e2 a.e3 s hsc hsc hsc hsc
    ha.b0 ha.b1 ha.b2 ha.b3

private theorem h2p62 : (2 : ℕ) ^ 62 = 4611686018427387904 := by norm_num

private theorem h2p68 : (2 : ℕ) ^ 68 = 295147905179352825856 := by norm_num

/-- `ExtMul` (babybear_ext.go:67): 16 raw products, four accumulations with `W = 11`,
one `ReduceBounded(·, 68)` per output coefficient — outputs are exactly `extMulV`. -/
theorem gExtMul_spec (a b : GExt) (s : St) (ha : GEv s a) (hb : GEv s b) :
    ∃ out t, (gExtMul a b).run s = (out, t) ∧ StepTo s t ∧ GEv t out ∧
      out.vals = extMulV a.vals b.vals := by
  have heq : gExtMul a b
      = (reduceBounded
          (.add (.mul a.e0.wire b.e0.wire)
            (.mul (.const ((wExt : ℕ) : Fr))
              (.add (.mul a.e1.wire b.e3.wire)
                (.add (.mul a.e2.wire b.e2.wire) (.mul a.e3.wire b.e1.wire)))))
          (a.e0.val * b.e0.val
            + wExt * (a.e1.val * b.e3.val
              + (a.e2.val * b.e2.val + a.e3.val * b.e1.val))) 68 >>= fun c0 =>
         reduceBounded
          (.add (.mul a.e0.wire b.e1.wire)
            (.add (.mul a.e1.wire b.e0.wire)
              (.mul (.const ((wExt : ℕ) : Fr))
                (.add (.mul a.e2.wire b.e3.wire) (.mul a.e3.wire b.e2.wire)))))
          (a.e0.val * b.e1.val
            + (a.e1.val * b.e0.val
              + wExt * (a.e2.val * b.e3.val + a.e3.val * b.e2.val))) 68 >>= fun c1 =>
         reduceBounded
          (.add (.mul a.e0.wire b.e2.wire)
            (.add (.mul a.e1.wire b.e1.wire)
              (.add (.mul a.e2.wire b.e0.wire)
                (.mul (.const ((wExt : ℕ) : Fr)) (.mul a.e3.wire b.e3.wire)))))
          (a.e0.val * b.e2.val
            + (a.e1.val * b.e1.val
              + (a.e2.val * b.e0.val + wExt * (a.e3.val * b.e3.val)))) 68 >>= fun c2 =>
         reduceBounded
          (.add (.mul a.e0.wire b.e3.wire)
            (.add (.mul a.e1.wire b.e2.wire)
              (.add (.mul a.e2.wire b.e1.wire) (.mul a.e3.wire b.e0.wire))))
          (a.e0.val * b.e3.val
            + (a.e1.val * b.e2.val
              + (a.e2.val * b.e1.val + a.e3.val * b.e0.val))) 68 >>= fun c3 =>
         pure ⟨c0, c1, c2, c3⟩) := rfl
  rw [heq]
  have hW : wExt = 11 := rfl
  -- product bounds
  have hP : ∀ (x y : BB), BBv s x → BBv s y → x.val * y.val < 4611686018427387904 :=
    fun x y hx hy => by
      have h := mul_lt_2p62 hx.lt hy.lt
      rwa [h2p62] at h
  have hp00 := hP _ _ ha.b0 hb.b0
  have hp01 := hP _ _ ha.b0 hb.b1
  have hp02 := hP _ _ ha.b0 hb.b2
  have hp03 := hP _ _ ha.b0 hb.b3
  have hp10 := hP _ _ ha.b1 hb.b0
  have hp11 := hP _ _ ha.b1 hb.b1
  have hp12 := hP _ _ ha.b1 hb.b2
  have hp13 := hP _ _ ha.b1 hb.b3
  have hp20 := hP _ _ ha.b2 hb.b0
  have hp21 := hP _ _ ha.b2 hb.b1
  have hp22 := hP _ _ ha.b2 hb.b2
  have hp23 := hP _ _ ha.b2 hb.b3
  have hp30 := hP _ _ ha.b3 hb.b0
  have hp31 := hP _ _ ha.b3 hb.b1
  have hp32 := hP _ _ ha.b3 hb.b2
  have hp33 := hP _ _ ha.b3 hb.b3
  -- the four accumulation evals under any state where the inputs are good
  have hevAt : ∀ t : St, GEv t a → GEv t b →
      ((Wire.add (.mul a.e0.wire b.e0.wire)
          (.mul (.const ((wExt : ℕ) : Fr))
            (.add (.mul a.e1.wire b.e3.wire)
              (.add (.mul a.e2.wire b.e2.wire) (.mul a.e3.wire b.e1.wire))))).eval
          (asgOf t)
        = ((a.e0.val * b.e0.val
            + wExt * (a.e1.val * b.e3.val
              + (a.e2.val * b.e2.val + a.e3.val * b.e1.val)) : ℕ) : Fr)) ∧
      ((Wire.add (.mul a.e0.wire b.e1.wire)
          (.add (.mul a.e1.wire b.e0.wire)
            (.mul (.const ((wExt : ℕ) : Fr))
              (.add (.mul a.e2.wire b.e3.wire) (.mul a.e3.wire b.e2.wire))))).eval
          (asgOf t)
        = ((a.e0.val * b.e1.val
            + (a.e1.val * b.e0.val
              + wExt * (a.e2.val * b.e3.val + a.e3.val * b.e2.val)) : ℕ) : Fr)) ∧
      ((Wire.add (.mul a.e0.wire b.e2.wire)
          (.add (.mul a.e1.wire b.e1.wire)
            (.add (.mul a.e2.wire b.e0.wire)
              (.mul (.const ((wExt : ℕ) : Fr)) (.mul a.e3.wire b.e3.wire))))).eval
          (asgOf t)
        = ((a.e0.val * b.e2.val
            + (a.e1.val * b.e1.val
              + (a.e2.val * b.e0.val + wExt * (a.e3.val * b.e3.val))) : ℕ) : Fr)) ∧
      ((Wire.add (.mul a.e0.wire b.e3.wire)
          (.add (.mul a.e1.wire b.e2.wire)
            (.add (.mul a.e2.wire b.e1.wire) (.mul a.e3.wire b.e0.wire)))).eval
          (asgOf t)
        = ((a.e0.val * b.e3.val
            + (a.e1.val * b.e2.val
              + (a.e2.val * b.e1.val + a.e3.val * b.e0.val)) : ℕ) : Fr)) := by
    intro t hat hbt
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · simp only [Wire.eval, hat.b0.ev, hat.b1.ev, hat.b2.ev, hat.b3.ev,
          hbt.b0.ev, hbt.b1.ev, hbt.b2.ev, hbt.b3.ev]
        push_cast
        ring
  have hwlt : ∀ (t : St), GEv t a → GEv t b → ∀ (x y : BB),
      BBv t x → BBv t y → wLt (Wire.mul x.wire y.wire) t.assigns.length :=
    fun _ _ _ x y hx hy => ⟨hx.wlt, hy.wlt⟩
  obtain ⟨hev0, hev1, hev2, hev3⟩ := hevAt s ha hb
  obtain ⟨o0, t0, hr0, hst0, hbv0, hval0⟩ :=
    reduceBounded_spec
      (.add (.mul a.e0.wire b.e0.wire)
        (.mul (.const ((wExt : ℕ) : Fr))
          (.add (.mul a.e1.wire b.e3.wire)
            (.add (.mul a.e2.wire b.e2.wire) (.mul a.e3.wire b.e1.wire)))))
      _ 68 s (by omega)
      ⟨⟨ha.b0.wlt, hb.b0.wlt⟩, trivial,
        ⟨ha.b1.wlt, hb.b3.wlt⟩, ⟨ha.b2.wlt, hb.b2.wlt⟩, ⟨ha.b3.wlt, hb.b1.wlt⟩⟩
      hev0 (by rw [hW, h2p68]; omega)
  have ha0 := ha.mono hst0
  have hb0' := hb.mono hst0
  obtain ⟨-, hev1', -, -⟩ := hevAt t0 ha0 hb0'
  obtain ⟨o1, t1, hr1, hst1, hbv1, hval1⟩ :=
    reduceBounded_spec
      (.add (.mul a.e0.wire b.e1.wire)
        (.add (.mul a.e1.wire b.e0.wire)
          (.mul (.const ((wExt : ℕ) : Fr))
            (.add (.mul a.e2.wire b.e3.wire) (.mul a.e3.wire b.e2.wire)))))
      _ 68 t0 (by omega)
      ⟨⟨ha0.b0.wlt, hb0'.b1.wlt⟩, ⟨ha0.b1.wlt, hb0'.b0.wlt⟩, trivial,
        ⟨ha0.b2.wlt, hb0'.b3.wlt⟩, ⟨ha0.b3.wlt, hb0'.b2.wlt⟩⟩
      hev1' (by rw [hW, h2p68]; omega)
  have ha1 := ha0.mono hst1
  have hb1' := hb0'.mono hst1
  obtain ⟨-, -, hev2', -⟩ := hevAt t1 ha1 hb1'
  obtain ⟨o2, t2, hr2, hst2, hbv2, hval2⟩ :=
    reduceBounded_spec
      (.add (.mul a.e0.wire b.e2.wire)
        (.add (.mul a.e1.wire b.e1.wire)
          (.add (.mul a.e2.wire b.e0.wire)
            (.mul (.const ((wExt : ℕ) : Fr)) (.mul a.e3.wire b.e3.wire)))))
      _ 68 t1 (by omega)
      ⟨⟨ha1.b0.wlt, hb1'.b2.wlt⟩, ⟨ha1.b1.wlt, hb1'.b1.wlt⟩,
        ⟨ha1.b2.wlt, hb1'.b0.wlt⟩, trivial, ⟨ha1.b3.wlt, hb1'.b3.wlt⟩⟩
      hev2' (by rw [hW, h2p68]; omega)
  have ha2 := ha1.mono hst2
  have hb2' := hb1'.mono hst2
  obtain ⟨-, -, -, hev3'⟩ := hevAt t2 ha2 hb2'
  obtain ⟨o3, t3, hr3, hst3, hbv3, hval3⟩ :=
    reduceBounded_spec
      (.add (.mul a.e0.wire b.e3.wire)
        (.add (.mul a.e1.wire b.e2.wire)
          (.add (.mul a.e2.wire b.e1.wire) (.mul a.e3.wire b.e0.wire))))
      _ 68 t2 (by omega)
      ⟨⟨ha2.b0.wlt, hb2'.b3.wlt⟩, ⟨ha2.b1.wlt, hb2'.b2.wlt⟩,
        ⟨ha2.b2.wlt, hb2'.b1.wlt⟩, ⟨ha2.b3.wlt, hb2'.b0.wlt⟩⟩
      hev3' (by rw [h2p68]; omega)
  simp only [runBind, hr0, hr1, hr2, hr3, runPure]
  refine ⟨⟨o0, o1, o2, o3⟩, t3, rfl, ((hst0.trans hst1).trans hst2).trans hst3,
    ⟨hbv0.mono ((hst1.trans hst2).trans hst3), hbv1.mono (hst2.trans hst3),
     hbv2.mono hst3, hbv3⟩, ?_⟩
  -- values: raw accumulation mod p = pre-reduced accumulation mod p (the Go ref order)
  have hc0 : (a.e0.val * b.e0.val
        + wExt * (a.e1.val * b.e3.val
          + (a.e2.val * b.e2.val + a.e3.val * b.e1.val))) % pBB
      = (bbMul a.e0.val b.e0.val + wExt * bbMul a.e1.val b.e3.val
          + wExt * bbMul a.e2.val b.e2.val + wExt * bbMul a.e3.val b.e1.val) % pBB := by
    apply mod_congr
    simp only [bbMul]
    push_cast [ZMod.natCast_mod]
    ring
  have hc1 : (a.e0.val * b.e1.val
        + (a.e1.val * b.e0.val
          + wExt * (a.e2.val * b.e3.val + a.e3.val * b.e2.val))) % pBB
      = (bbMul a.e0.val b.e1.val + bbMul a.e1.val b.e0.val
          + wExt * bbMul a.e2.val b.e3.val + wExt * bbMul a.e3.val b.e2.val) % pBB := by
    apply mod_congr
    simp only [bbMul]
    push_cast [ZMod.natCast_mod]
    ring
  have hc2 : (a.e0.val * b.e2.val
        + (a.e1.val * b.e1.val
          + (a.e2.val * b.e0.val + wExt * (a.e3.val * b.e3.val)))) % pBB
      = (bbMul a.e0.val b.e2.val + bbMul a.e1.val b.e1.val + bbMul a.e2.val b.e0.val
          + wExt * bbMul a.e3.val b.e3.val) % pBB := by
    apply mod_congr
    simp only [bbMul]
    push_cast [ZMod.natCast_mod]
    ring
  have hc3 : (a.e0.val * b.e3.val
        + (a.e1.val * b.e2.val
          + (a.e2.val * b.e1.val + a.e3.val * b.e0.val))) % pBB
      = (bbMul a.e0.val b.e3.val + bbMul a.e1.val b.e2.val + bbMul a.e2.val b.e1.val
          + bbMul a.e3.val b.e0.val) % pBB := by
    apply mod_congr
    simp only [bbMul]
    push_cast [ZMod.natCast_mod]
    ring
  show ExtV.mk o0.val o1.val o2.val o3.val = extMulV a.vals b.vals
  rw [hval0, hval1, hval2, hval3, hc0, hc1, hc2, hc3]
  rfl

/-! ### The invS chain pieces (bit ingestion, the constant select, the running product). -/

theorem bitVarM_spec (b : Bool) (s : St) :
    ∃ out t, (bitVarM b).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = (if b then 1 else 0) := by
  unfold bitVarM
  simp only [runBind, runFreshVar, runAssertEq, runPure]
  set s₂ : St := ⟨s.assigns ++ [if b then 1 else 0],
    s.asserts ++ [(.mul (.var s.assigns.length) (.var s.assigns.length),
                   .var s.assigns.length)]⟩ with hs₂
  have hbit : asgOf s₂ s.assigns.length = (if b then (1 : Fr) else 0) := by
    show (s.assigns ++ [if b then (1 : Fr) else 0]).getD s.assigns.length 0 = _
    exact getD_concat s.assigns _
  have hlen : s₂.assigns.length = s.assigns.length + 1 := by simp [hs₂]
  have hstep : StepTo s s₂ := by
    refine ⟨⟨[if b then (1 : Fr) else 0], rfl⟩, [_], rfl, ?_⟩
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show s.assigns.length < s₂.assigns.length; omega
    · show s.assigns.length < s₂.assigns.length; omega
    · show s.assigns.length < s₂.assigns.length; omega
    · simp only [Wire.eval, hbit]
      cases b <;> norm_num
  refine ⟨⟨.var s.assigns.length, if b then 1 else 0⟩, s₂, rfl, hstep,
    ⟨?_, ?_, ?_⟩, rfl⟩
  · show s.assigns.length < s₂.assigns.length; omega
  · show asgOf s₂ s.assigns.length = ((if b then 1 else 0 : ℕ) : Fr)
    rw [hbit]
    cases b <;> norm_num
  · cases b <;> simp <;> decide

/-- The `api.Select(bit, ginv, 1)` factor is good whenever the bit wire is an honest
boolean (raw mux over constants — no state change). -/
theorem selectFactor_ok {s : St} {bv : BB} (j : ℕ) (b : Bool)
    (h : BBv s bv) (hval : bv.val = if b then 1 else 0) :
    BBv s (selectFactor j b bv) := by
  refine ⟨⟨h.wlt, trivial, trivial⟩, ?_, ?_⟩
  · show bv.wire.eval (asgOf s) * (((ginvT (2 + j) : ℕ) : Fr) - (1 : Fr)) + (1 : Fr)
      = ((invSFactorV j b : ℕ) : Fr)
    -- The opaque Fermat inverse `ginvT (2+j)` must never meet `simp`/`norm_num`: they
    -- whnf-evaluate `modPowAux 31 …` and blow the heartbeat. Reduce the literal `if`s by
    -- `rfl` only, then `ring` treats the cast as an opaque atom (no evaluation).
    rw [h.ev, hval]
    unfold invSFactorV                 -- syntactic unfold — does NOT whnf `ginvT`
    generalize ginvT (2 + j) = g       -- the Fermat inverse is now a plain variable
    cases b
    · show ((0 : ℕ) : Fr) * _ + _ = ((1 : ℕ) : Fr)
      push_cast; ring
    · show ((1 : ℕ) : Fr) * _ + _ = ((g : ℕ) : Fr)
      push_cast; ring
  · show invSFactorV j b < pBB
    unfold invSFactorV
    generalize hg : ginvT (2 + j) = g
    cases b
    · show (1 : ℕ) < pBB; decide
    · show g < pBB; rw [← hg]; exact ginvT_lt (2 + j)

/-- The whole invS chain (fri_query.go:137-142). -/
theorem invSChainAux_spec : ∀ (bits : List Bool) (j : ℕ) (acc : BB) (s : St),
    BBv s acc →
    ∃ out t, (invSChainAux j acc bits).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = invSVAux j acc.val bits := by
  intro bits
  induction bits with
  | nil =>
      intro j acc s hacc
      exact ⟨acc, s, rfl, StepTo.refl s, hacc, rfl⟩
  | cons b rest ih =>
      intro j acc s hacc
      simp only [invSChainAux, runBind]
      obtain ⟨bv, t1, hr1, hst1, hbv, hbval⟩ := bitVarM_spec b s
      obtain ⟨acc', t2, hr2, hst2, hacc', hval2⟩ :=
        gMul_spec acc (selectFactor j b bv) t1 (hacc.mono hst1)
          (selectFactor_ok j b hbv hbval)
      obtain ⟨out, t3, hr3, hst3, hout, hval3⟩ := ih (j + 1) acc' t2 hacc'
      simp only [hr1, hr2, hr3]
      refine ⟨out, t3, rfl, (hst1.trans hst2).trans hst3, hout, ?_⟩
      rw [hval3, hval2]
      rfl

theorem invSChainM_spec (bits : List Bool) (s : St) :
    ∃ out t, (invSChainM bits).run s = (out, t) ∧ StepTo s t ∧ BBv t out ∧
      out.val = invSV bits :=
  invSChainAux_spec bits 0 (constBB 1) s ⟨trivial, rfl, by decide⟩


/-! ## §6 THE LEAF REFINEMENT — the deployed fold-consistency check, both polarities. -/

/-- `runM`'s generated witness reads the mint list as an `Array`; the honest-run framework
reads it as a `List`. They agree at every index (in-bounds by `getElem?`, out-of-bounds by
the shared default `0`), so the emitted witness IS the `asgOf` of the run's final state. -/
private theorem list_toArray_getD (l : List Fr) (v : ℕ) :
    l.toArray.getD v 0 = l.getD v 0 := by
  simp

/-- `extAssertEqM` adds NO mints and exactly the four per-lane equality asserts. -/
private theorem extAssertEqM_run (a b : GExt) (s : St) :
    (extAssertEqM a b).run s
      = ((), ⟨s.assigns, s.asserts ++
          [(a.e0.wire, b.e0.wire), (a.e1.wire, b.e1.wire),
           (a.e2.wire, b.e2.wire), (a.e3.wire, b.e3.wire)]⟩) := by
  simp only [extAssertEqM, runBind, runAssertEq, List.append_assoc, List.nil_append,
    List.cons_append]

/-- **The honest run of the one-round fold program.** Composing the committed-gadget specs:
the whole builder run threads honestly (a `StepTo` from the empty state), the ingested
claimed value `gc` and the computed `folded` are both good at the pre-assert state, `folded`
tracks EXACTLY the deployed fold `foldCoreV`, and the emitted circuit's asserts are the
gadget prefix (always honest) followed by the four fold-vs-claim lane equalities. -/
theorem foldRound_spec (s0 s1 beta claimed : ExtV) (bits : List Bool)
    (h0 : ExtCanon s0) (h1 : ExtCanon s1) (hbeta : ExtCanon beta) (hc : ExtCanon claimed) :
    ∃ (g0 g1 gb gc folded : GExt) (tpre : St),
      StepTo ⟨[], []⟩ tpre ∧
      GEv tpre folded ∧ GEv tpre gc ∧
      folded.vals = foldCoreV s0 s1 beta (invSV bits) ∧
      gc.vals = claimed ∧
      (foldRoundM s0 s1 beta claimed bits).run ⟨[], []⟩
        = ((g0, g1, gb, gc),
           ⟨tpre.assigns, tpre.asserts ++
             [(folded.e0.wire, gc.e0.wire), (folded.e1.wire, gc.e1.wire),
              (folded.e2.wire, gc.e2.wire), (folded.e3.wire, gc.e3.wire)]⟩) := by
  obtain ⟨g0, t0, hr0, hst0, hge0, hv0⟩ := inputExt_spec s0 ⟨[], []⟩ h0
  obtain ⟨g1, t1, hr1, hst1, hge1, hv1⟩ := inputExt_spec s1 t0 h1
  obtain ⟨gb, t2, hr2, hst2, hgeb, hvb⟩ := inputExt_spec beta t1 hbeta
  obtain ⟨gc, t3, hr3, hst3, hgec0, hvc⟩ := inputExt_spec claimed t2 hc
  obtain ⟨invS, t4, hr4, hst4, hbi, hvi⟩ := invSChainM_spec bits t3
  obtain ⟨half, t5, hr5, hst5, hbh, hvh⟩ :=
    gMul_spec (constBB inv2V) invS t4 ⟨trivial, rfl, by decide⟩ hbi
  have g0_5 : GEv t5 g0 := hge0.mono (hst1.trans (hst2.trans (hst3.trans (hst4.trans hst5))))
  have g1_5 : GEv t5 g1 := hge1.mono (hst2.trans (hst3.trans (hst4.trans hst5)))
  obtain ⟨sum, t6, hr6, hst6, hgesum, hvsum⟩ := gExtAdd_spec g0 g1 t5 g0_5 g1_5
  obtain ⟨diff, t7, hr7, hst7, hgediff, hvdiff⟩ :=
    gExtSub_spec g0 g1 t6 (g0_5.mono hst6) (g1_5.mono hst6)
  have gb_7 : GEv t7 gb := hgeb.mono (hst3.trans (hst4.trans (hst5.trans (hst6.trans hst7))))
  obtain ⟨betaTerm, t8, hr8, hst8, hgebt, hvbt⟩ := gExtMul_spec gb diff t7 gb_7 hgediff
  obtain ⟨sumHalf, t9, hr9, hst9, hgesh, hvsh⟩ :=
    gExtMulBase_spec (constBB inv2V) sum t8 ⟨trivial, rfl, by decide⟩ ((hgesum.mono hst7).mono hst8)
  obtain ⟨btScaled, t10, hr10, hst10, hgebs, hvbs⟩ :=
    gExtMulBase_spec half betaTerm t9 (hbh.mono (hst6.trans (hst7.trans (hst8.trans hst9))))
      (hgebt.mono hst9)
  obtain ⟨folded, t11, hr11, hst11, hgef, hvf⟩ :=
    gExtAdd_spec sumHalf btScaled t10 (hgesh.mono hst10) hgebs
  have gc_11 : GEv t11 gc :=
    hgec0.mono (hst4.trans (hst5.trans (hst6.trans (hst7.trans (hst8.trans
      (hst9.trans (hst10.trans hst11)))))))
  have hstAll : StepTo ⟨[], []⟩ t11 :=
    hst0.trans (hst1.trans (hst2.trans (hst3.trans (hst4.trans (hst5.trans
      (hst6.trans (hst7.trans (hst8.trans (hst9.trans (hst10.trans hst11))))))))))
  have hfval : folded.vals = foldCoreV s0 s1 beta (invSV bits) := by
    rw [hvf, hvsh, hvbs, hvsum, hvbt, hvdiff, hv0, hv1, hvb, hvh, hvi]
    rfl
  refine ⟨g0, g1, gb, gc, folded, t11, hstAll, hgef, gc_11, hfval, hvc, ?_⟩
  -- Reduce the run by EXPLICIT `rw` steps (small, kernel-cheap proof terms) rather than a
  -- monolithic `simp` over `foldRoundM` — the latter builds a term the kernel re-evaluates.
  show (foldRoundM s0 s1 beta claimed bits).run ⟨[], []⟩ = _
  unfold foldRoundM
  rw [runBind, hr0]; dsimp only
  rw [runBind, hr1]; dsimp only
  rw [runBind, hr2]; dsimp only
  rw [runBind, hr3]; dsimp only
  rw [runBind, hr4]; dsimp only
  rw [runBind, hr5]; dsimp only
  rw [runBind, hr6]; dsimp only
  rw [runBind, hr7]; dsimp only
  rw [runBind, hr8]; dsimp only
  rw [runBind, hr9]; dsimp only
  rw [runBind, hr10]; dsimp only
  rw [runBind, hr11]; dsimp only
  rw [runBind, extAssertEqM_run]; dsimp only; rw [runPure]

/-- **`friFold_leaf_refines`** — the leaf refinement of the deployed FRI arity-2
fold-consistency check. For ALL canonical siblings/challenge/claimed value and ALL
parent-bit vectors, the LOWERED genuine R1CS of the emitted `friFoldRowArity2 +
ExtAssertIsEqual` package, under the builder-generated honest witness, is satisfied IFF the
claimed folded value equals the deployed fold `(e0+e1)/2 + β·(e0−e1)·inv(2s)`. A genuine
∀-theorem, riding `R1csFr.gHolds` (frontend ↔ R1CS) over the committed `BabyBearFr`
gadgets — no field arithmetic is re-authored here. -/
theorem friFold_leaf_refines (s0 s1 beta claimed : ExtV) (bits : List Bool)
    (h0 : ExtCanon s0) (h1 : ExtCanon s1) (hbeta : ExtCanon beta) (hc : ExtCanon claimed) :
    gHolds (friFoldData s0 s1 beta claimed bits) (friFoldAsg s0 s1 beta claimed bits)
      ↔ foldCheckV s0 s1 beta claimed bits = true := by
  obtain ⟨g0, g1, gb, gc, folded, tpre, hstep, hgef, hgec, hfval, hgcval, hrun⟩ :=
    foldRound_spec s0 s1 beta claimed bits h0 h1 hbeta hc
  have hcirc : (friFoldData s0 s1 beta claimed bits).circuit
      = ⟨tpre.asserts ++ [(folded.e0.wire, gc.e0.wire), (folded.e1.wire, gc.e1.wire),
          (folded.e2.wire, gc.e2.wire), (folded.e3.wire, gc.e3.wire)]⟩ := by
    simp only [friFoldData, friFoldRun, runM, hrun]
  have hasg : friFoldAsg s0 s1 beta claimed bits = asgOf tpre := by
    funext v
    simp only [friFoldAsg, friFoldRun, runM, hrun]
    exact list_toArray_getD tpre.assigns v
  -- per-coordinate identifications of the tracked values
  have hf0 : folded.e0.val = (foldCoreV s0 s1 beta (invSV bits)).c0 := congrArg ExtV.c0 hfval
  have hf1 : folded.e1.val = (foldCoreV s0 s1 beta (invSV bits)).c1 := congrArg ExtV.c1 hfval
  have hf2 : folded.e2.val = (foldCoreV s0 s1 beta (invSV bits)).c2 := congrArg ExtV.c2 hfval
  have hf3 : folded.e3.val = (foldCoreV s0 s1 beta (invSV bits)).c3 := congrArg ExtV.c3 hfval
  have hg0 : gc.e0.val = claimed.c0 := congrArg ExtV.c0 hgcval
  have hg1 : gc.e1.val = claimed.c1 := congrArg ExtV.c1 hgcval
  have hg2 : gc.e2.val = claimed.c2 := congrArg ExtV.c2 hgcval
  have hg3 : gc.e3.val = claimed.c3 := congrArg ExtV.c3 hgcval
  have hfcC : ExtCanon (foldCoreV s0 s1 beta (invSV bits)) := hfval ▸ GEv.canon hgef
  -- unfold gHolds to frontend acceptance over the honest witness, split the assert list
  unfold gHolds
  rw [← R1csFr.gHolds, hcirc, hasg]
  show (∀ p ∈ tpre.asserts ++ [(folded.e0.wire, gc.e0.wire), (folded.e1.wire, gc.e1.wire),
      (folded.e2.wire, gc.e2.wire), (folded.e3.wire, gc.e3.wire)],
      p.1.eval (asgOf tpre) = p.2.eval (asgOf tpre)) ↔ _
  rw [List.forall_mem_append, and_iff_right (StepTo.sat_of_nil hstep),
    show (∀ p ∈ [(folded.e0.wire, gc.e0.wire), (folded.e1.wire, gc.e1.wire),
          (folded.e2.wire, gc.e2.wire), (folded.e3.wire, gc.e3.wire)],
          p.1.eval (asgOf tpre) = p.2.eval (asgOf tpre))
        ↔ (folded.e0.wire.eval (asgOf tpre) = gc.e0.wire.eval (asgOf tpre)
            ∧ folded.e1.wire.eval (asgOf tpre) = gc.e1.wire.eval (asgOf tpre)
            ∧ folded.e2.wire.eval (asgOf tpre) = gc.e2.wire.eval (asgOf tpre)
            ∧ folded.e3.wire.eval (asgOf tpre) = gc.e3.wire.eval (asgOf tpre)) from by simp]
  simp only [hgef.b0.ev, hgef.b1.ev, hgef.b2.ev, hgef.b3.ev,
    hgec.b0.ev, hgec.b1.ev, hgec.b2.ev, hgec.b3.ev,
    hf0, hf1, hf2, hf3, hg0, hg1, hg2, hg3, foldCheckV, decide_eq_true_eq]
  constructor
  · rintro ⟨e0, e1, e2, e3⟩
    have n0 : claimed.c0 = (foldCoreV s0 s1 beta (invSV bits)).c0 :=
      cast_inj_lt (lt_trans hc.1 pBB_lt_r) (lt_trans hfcC.1 pBB_lt_r) e0.symm
    have n1 : claimed.c1 = (foldCoreV s0 s1 beta (invSV bits)).c1 :=
      cast_inj_lt (lt_trans hc.2.1 pBB_lt_r) (lt_trans hfcC.2.1 pBB_lt_r) e1.symm
    have n2 : claimed.c2 = (foldCoreV s0 s1 beta (invSV bits)).c2 :=
      cast_inj_lt (lt_trans hc.2.2.1 pBB_lt_r) (lt_trans hfcC.2.2.1 pBB_lt_r) e2.symm
    have n3 : claimed.c3 = (foldCoreV s0 s1 beta (invSV bits)).c3 :=
      cast_inj_lt (lt_trans hc.2.2.2 pBB_lt_r) (lt_trans hfcC.2.2.2 pBB_lt_r) e3.symm
    calc claimed
        = ExtV.mk claimed.c0 claimed.c1 claimed.c2 claimed.c3 := rfl
      _ = ExtV.mk (foldCoreV s0 s1 beta (invSV bits)).c0 (foldCoreV s0 s1 beta (invSV bits)).c1
            (foldCoreV s0 s1 beta (invSV bits)).c2 (foldCoreV s0 s1 beta (invSV bits)).c3 := by
            rw [n0, n1, n2, n3]
      _ = foldCoreV s0 s1 beta (invSV bits) := rfl
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The same leaf refinement at the EMITTED wire form (composing the foundation's proven
`emit_faithful`): the bytes the JSON grammar renders denote exactly the fold-consistency
spec. -/
theorem friFold_leaf_refines_emitted (s0 s1 beta claimed : ExtV) (bits : List Bool)
    (h0 : ExtCanon s0) (h1 : ExtCanon s1) (hbeta : ExtCanon beta) (hc : ExtCanon claimed) :
    satisfiedEmitted (emit (friFoldData s0 s1 beta claimed bits))
        (friFoldAsg s0 s1 beta claimed bits)
      ↔ foldCheckV s0 s1 beta claimed bits = true :=
  (emit_faithful (friFoldData s0 s1 beta claimed bits) (friFoldAsg s0 s1 beta claimed bits)).symm.trans
    (friFold_leaf_refines s0 s1 beta claimed bits h0 h1 hbeta hc)

/-- **The reject polarity** (non-vacuity witness): a claimed folded value that DISAGREES
with the deployed fold makes the emitted circuit UNSATISFIABLE under the honest witness —
a tampered sibling or a wrong fold value cannot pass. -/
theorem friFold_leaf_reject (s0 s1 beta claimed : ExtV) (bits : List Bool)
    (h0 : ExtCanon s0) (h1 : ExtCanon s1) (hbeta : ExtCanon beta) (hc : ExtCanon claimed)
    (hne : claimed ≠ foldCoreV s0 s1 beta (invSV bits)) :
    ¬ gHolds (friFoldData s0 s1 beta claimed bits) (friFoldAsg s0 s1 beta claimed bits) := by
  rw [friFold_leaf_refines s0 s1 beta claimed bits h0 h1 hbeta hc]
  simp only [foldCheckV, decide_eq_true_eq]
  exact hne

#assert_axioms foldRound_spec
#assert_axioms friFold_leaf_refines
#assert_axioms friFold_leaf_refines_emitted
#assert_axioms friFold_leaf_reject

/-! ### Teeth — decidable samples at both polarities (the ∀-theorem above subsumes these;
the guards pin that the whole gadget program COMPUTES on the gold vectors). -/

-- accept: claimed = fold, parent bits (1,0,1) → invS = ginv₂·ginv₄
#guard foldCheckV ⟨123, 456, 789, 1011⟩ ⟨2021, 2223, 2425, 2627⟩
    ⟨1234567890, 11111111, 222222222, 1999999999⟩ ⟨1739982707, 869530502, 1173455424, 1109545812⟩
    [true, false, true]
-- reject: one tampered coordinate of the claimed value
#guard ¬ foldCheckV ⟨123, 456, 789, 1011⟩ ⟨2021, 2223, 2425, 2627⟩
    ⟨1234567890, 11111111, 222222222, 1999999999⟩ ⟨1739982708, 869530502, 1173455424, 1109545812⟩
    [true, false, true]

end Dregg2.Circuit.Emit.GnarkVerifier.FriFold
