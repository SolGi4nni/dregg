/-
# Dregg2.Circuit.Emit.KimchiGadgets — `Boolean`, `select`, `assertEq`, one-hot ON THE KIMCHI RAIL

## ⚑ WHAT WAS MISSING, MEASURED AT SOURCE (2026-08-05)

`Field.if_` occurs 25 times in `metatheory/` and **every one is a comment**. There is no `Boolean`
type on the kimchi rail at all. The mux is open-coded — `KimchiStepMainCore.lean:2999`
(`scale_fast2`'s `G.if_`, two coordinates), `:4176` (the sponge-state mask, three lanes),
`KimchiWrapMainCore.lean` (the wrap cone's copy). `choose_key` has no declaration.

**This file is the rail.** A gadget here is a list of `Half`s — the double-`Generic` sub-gate that
`packHalves` already consumes in both cores — so a gadget composes into an existing row schedule
without moving a byte, which §5 proves.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The coefficient vectors, the gadget shapes and the soundness
lemmas are authored here; `proof-systems` is the Rust prover that RUNS them and authors no
constraint. House Law #1.

## ⚑ THE CIRCUIT STAYS A VALUE

Every gadget is a function returning a `List Half` — an ordinary value. Nothing here is a builder
monad, so `KimchiPreimageCircuit`'s discipline survives: a circuit built from these gadgets is a
closed `def`, its emitted wires are readable by `decide`, and a control that drops one gadget is
*another value* rather than a failed test run.

## ⚑ CHECKED AGAINST o1js's OWN EMISSION (o1js 2.15.0, measured 2026-08-05)

`bridge/mina-zkapp/scripts/kimchi-gadget-oracle.mjs` diffs these coefficient vectors against
`Provable.constraintSystem`. What it found:

| gadget | o1js emits | here |
|---|---|---|
| `Bool` witness check | 1 half, coeffs `[-1,0,0,1,0]` | `cBool`, byte-identical |
| `Provable.if(b,x,y)` | 3 halves: `[1,-1,-1,0,0]`, mul, `[1,1,-1,0,0]` | `selectHalves`, same three |
| `x.assertEquals(y)`, both bare vars | **0 rows** | ⚠ see §4 — this is the MERGE, not a gate |
| `x.assertEquals(Field 7)` | 1 half, `[1,0,0,0,-7]` | `constHalf` |
| `x.add(y).assertEquals(z)` | 1 half, `[1,1,-1,0,0]` | `addHalf` |

⚑ **AND ONE PLACE WE ARE DELIBERATELY STRICTER.** o1js's `Provable.switch` over a 3-way mask emits
3 booleanity + 3 mul + 2 add halves and **no `Σ mask = 1` gate**: its exclusivity check is
`Provable.asProver(checkMask)` (`provable.js:353-370`), i.e. it runs OUTSIDE the circuit. A prover
choosing mask `[1,1,0]` satisfies every gate o1js emits. `oneHotHalves` (§6) emits the sum gate.
Per house rule we do not weaken a refusal to match an upstream convenience.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiArena

namespace Dregg2.Circuit.Emit.KimchiGadgets

open Dregg2.Circuit.Emit.KimchiPlacement

set_option autoImplicit false

/-! ## §1 — the double-`Generic` HALF, and what it means.

`generic.rs:283-314`: a `Generic` row carries TWO sub-gates. Half 1 is
`c₀·w₀ + c₁·w₁ + c₂·w₂ + c₃·w₀·w₁ + c₄ = 0` over columns 0,1,2 with coefficients `0..4`; half 2 is
the same over columns 3,4,5 with coefficients `5..9`. `packHalves` (both cores) fills a row from
two of these. -/

/-- One `Generic` sub-gate: its three permutation-column variables and its five coefficients. This
is exactly the pair `packHalves` consumes. -/
abbrev Half : Type := List (Option PVar) × List Int

/-- Slot `i`'s value; an unwired slot contributes `0`. -/
def slotVal {F : Type} [Field F] (w : PVar → F) (h : Half) (i : Nat) : F :=
  match h.1.getD i none with
  | some p => w p
  | none   => 0

/-- Coefficient `i`; a short vector reads as `0`. -/
def coef (h : Half) (i : Nat) : Int := h.2.getD i 0

/-- **The half's constraint polynomial**, over any field. A half HOLDS when this is `0`. -/
def halfEval {F : Type} [Field F] (w : PVar → F) (h : Half) : F :=
  (coef h 0 : F) * slotVal w h 0 + (coef h 1 : F) * slotVal w h 1 + (coef h 2 : F) * slotVal w h 2
    + (coef h 3 : F) * (slotVal w h 0 * slotVal w h 1) + (coef h 4 : F)

/-! ## §2 — the coefficient vectors, ONE copy each.

⚠ `KimchiStepMainCore` and `KimchiWrapMainCore` each carried their own `cAdd`/`cSub`/`cMul`/`cEq`/
`cConst`/`cNil`. Step's now delegate here (`KimchiStepMainCore` §3); the wrap cone's are a live
sibling's file and are named in the report, not edited. -/

/-- `w₀ + w₁ − w₂` — o1js `x.add(y).assertEquals(z)`. -/
def cAdd : List Int := [1, 1, -1, 0, 0]
/-- `w₀·w₁ − w₂`. -/
def cMul : List Int := [0, 0, -1, 1, 0]
/-- `w₀ − w₁ − w₂`. -/
def cSub : List Int := [1, -1, -1, 0, 0]
/-- `w₀ − w₁` — the ROW-COSTING equality (§4). -/
def cEq : List Int := [1, -1, 0, 0, 0]
/-- `w₀ − k`. -/
def cConst (k : Int) : List Int := [1, 0, 0, 0, -k]
/-- ⚑ `w₀·w₁ − w₀` — **booleanity, as ONE named gate.** Applied at `w₀ = w₁ = b` this is
`b² − b = b(b−1)`. Byte-identical to o1js's own `Bool` check (§0's table). -/
def cBool : List Int := [-1, 0, 0, 1, 0]
/-- An unused half. -/
def cNil : List Int := [0, 0, 0, 0, 0]

/-! ## §3 — the gadgets. -/

/-- `w₂ = w₀ + w₁`. -/
def addHalf (a b o : PVar) : Half := ([some a, some b, some o], cAdd)
/-- `w₂ = w₀ − w₁`. -/
def subHalf (a b o : PVar) : Half := ([some a, some b, some o], cSub)
/-- `w₂ = w₀ · w₁`. -/
def mulHalf (a b o : PVar) : Half := ([some a, some b, some o], cMul)
/-- `w₀ = k`. -/
def constHalf (v : PVar) (k : Int) : Half := ([some v, none, none], cConst k)
/-- `w₀ = w₁`, ONE half. See §4 for when you want this and when you want the merge. -/
def assertEqHalf (a b : PVar) : Half := ([some a, some b, none], cEq)

/-- ⚑ **`Boolean`** — the booleanity pin, as one named gate rather than a fifteenth `x(x−1)`. The
variable occupies BOTH multiplied slots, which is what makes `c₃·w₀·w₁` the square. -/
def boolHalf (b : PVar) : Half := ([some b, some b, none], cBool)

/-! ### §3a — soundness of the primitives. -/

variable {F : Type} [Field F]

theorem addHalf_eval (w : PVar → F) (a b o : PVar) :
    halfEval w (addHalf a b o) = w a + w b - w o := by
  simp [halfEval, slotVal, coef, addHalf, cAdd]; ring

theorem subHalf_eval (w : PVar → F) (a b o : PVar) :
    halfEval w (subHalf a b o) = w a - w b - w o := by
  simp [halfEval, slotVal, coef, subHalf, cSub]; ring

theorem mulHalf_eval (w : PVar → F) (a b o : PVar) :
    halfEval w (mulHalf a b o) = w a * w b - w o := by
  simp [halfEval, slotVal, coef, mulHalf, cMul]; ring

theorem constHalf_eval (w : PVar → F) (v : PVar) (k : Int) :
    halfEval w (constHalf v k) = w v - (k : F) := by
  simp [halfEval, slotVal, coef, constHalf, cConst]; ring

/-- **`assertEq` bites**: the half vanishes exactly when the two variables agree. -/
theorem assertEqHalf_zero_iff (w : PVar → F) (a b : PVar) :
    halfEval w (assertEqHalf a b) = 0 ↔ w a = w b := by
  have : halfEval w (assertEqHalf a b) = w a - w b := by
    simp [halfEval, slotVal, coef, assertEqHalf, cEq]; ring
  rw [this, sub_eq_zero]

/-- The booleanity half IS `b(b−1)`. -/
theorem boolHalf_eval (w : PVar → F) (b : PVar) :
    halfEval w (boolHalf b) = w b * (w b - 1) := by
  simp [halfEval, slotVal, coef, boolHalf, cBool]; ring

/-- ⚑ **`Boolean`'s soundness lemma**: the pin vanishes exactly on `{0,1}`. It genuinely BITES —
this is an `iff`, so it is also the statement that the pin admits both values and nothing else. -/
theorem boolHalf_zero_iff (w : PVar → F) (b : PVar) :
    halfEval w (boolHalf b) = 0 ↔ (w b = 0 ∨ w b = 1) := by
  rw [boolHalf_eval, mul_eq_zero, sub_eq_zero]

/-! ### §3b — `select` / `Field.if_`. -/

/-- The five variables one mux needs: the two branches, the two AUXILIARIES (`d = t − e`, the
sealed difference; `m = b·d`) and the output. ⚑ The two auxiliaries are exactly what a hand-picked
layout has to invent an id for, and exactly what `KimchiArena` allocates. -/
structure MuxWires where
  /-- the `then_` branch -/
  t : PVar
  /-- the `else_` branch -/
  e : PVar
  /-- `d = t − e`, sealed because a `Generic` half carries only three variables -/
  d : PVar
  /-- `m = b · d` -/
  m : PVar
  /-- the selected value -/
  out : PVar
  deriving Repr, DecidableEq, Inhabited

/-- ⚑ **`Field.if_ b ~then_:t ~else_:e`** — Snarky's mux `e + b·(t − e)`, three halves. The
difference is sealed into `d` because `res − e − b·(t − e)` needs four variables and a half carries
three (`KimchiStepMainCore.lean:2996`'s own note). Byte-identical to what o1js's `Provable.if`
emits (§0). -/
def selectHalves (b : PVar) (x : MuxWires) : List Half :=
  [ subHalf x.t x.e x.d, mulHalf b x.d x.m, addHalf x.e x.m x.out ]

/-- ⚑ **THE MUX'S FULL SEMANTICS** — no hypothesis on `b` at all. -/
theorem selectHalves_sound (w : PVar → F) (b : PVar) (x : MuxWires)
    (hs : ∀ h ∈ selectHalves b x, halfEval w h = 0) :
    w x.out = w x.e + w b * (w x.t - w x.e) := by
  have h1 := hs (subHalf x.t x.e x.d) (by simp [selectHalves])
  have h2 := hs (mulHalf b x.d x.m) (by simp [selectHalves])
  have h3 := hs (addHalf x.e x.m x.out) (by simp [selectHalves])
  rw [subHalf_eval] at h1
  rw [mulHalf_eval] at h2
  rw [addHalf_eval] at h3
  have hd : w x.d = w x.t - w x.e := by linear_combination -h1
  have hm : w x.m = w b * w x.d := by linear_combination -h2
  have ho : w x.out = w x.e + w x.m := by linear_combination -h3
  rw [ho, hm, hd]

/-- ⚑ **AND THE MUX ALONE DOES NOT CONSTRAIN ITS SELECTOR.** Snarky's `Field.if_` and gnark's
`api.Select` both leave booleanity to the caller (`R1csFr.Wire.eval_select_of_bool` says the same on
the R1CS rail). At `b = 2` this "conditional" outputs `2t − e`, which is NEITHER branch. This is
why `boolHalf` is a separate gate and why `selectChecked` exists — and it is a fact about the
emitted object, not a warning in a comment. -/
theorem selectHalves_escapes_at_two (w : PVar → F) (b : PVar) (x : MuxWires)
    (hs : ∀ h ∈ selectHalves b x, halfEval w h = 0) (h2 : w b = 2) :
    w x.out = 2 * w x.t - w x.e := by
  rw [selectHalves_sound w b x hs, h2]; ring

/-- **`Field.if_` WITH its selector pinned** — the four halves you actually want. -/
def selectChecked (b : PVar) (x : MuxWires) : List Half := boolHalf b :: selectHalves b x

/-- ⚑ **THE CONDITIONAL'S SOUNDNESS LEMMA.** With booleanity emitted, the mux is the genuine
if-then-else on the emitted object. -/
theorem selectChecked_sound (w : PVar → F) (b : PVar) (x : MuxWires)
    (hs : ∀ h ∈ selectChecked b x, halfEval w h = 0) :
    (w b = 0 → w x.out = w x.e) ∧ (w b = 1 → w x.out = w x.t) := by
  have hsel : ∀ h ∈ selectHalves b x, halfEval w h = 0 :=
    fun h hh => hs h (List.mem_cons_of_mem _ hh)
  have hgen := selectHalves_sound w b x hsel
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [hgen, h0]; ring
  · rw [hgen, h1]; ring

/-- A mux over SEVERAL coordinates sharing one selector, packed the way both existing open-coded
sites already pack it: every `(sub, mul)` pair first, then the adds. That order is what makes the
`packHalves` rows come out `cSub ++ cMul` ×n then `cAdd ++ cAdd` — see §5. -/
def selectHalvesN (b : PVar) (xs : List MuxWires) : List Half :=
  xs.flatMap (fun x => [subHalf x.t x.e x.d, mulHalf b x.d x.m])
    ++ xs.map (fun x => addHalf x.e x.m x.out)

/-- At one coordinate the vectorised packing IS the scalar one. -/
theorem selectHalvesN_singleton (b : PVar) (x : MuxWires) :
    selectHalvesN b [x] = selectHalves b x := rfl

/-! ## §4 — ⚠ `assertEq`, and the ZERO-ROW fact that belongs to the merge seam.

Measured against o1js 2.15.0: `x.assertEquals(y)` on two BARE VARIABLES emits **zero rows** — it is
a union in Snarky's union-find, and the two variables become one copy-permutation class. That
zero-row path is `KimchiPlacement`'s `mergeRoots` seam, which is a sibling's work and is not
touched here.

`assertEqHalf` is the OTHER case, and o1js emits a row for it too: `x.assertEquals(Field 7)` is one
half (`cConst`), `x.add(y).assertEquals(z)` is one half (`cAdd`). Use `assertEqHalf` when a side is
not a bare variable — when the merge cannot express it. ⚑ The two are not redundant and neither
should be deleted for the other; they are the two halves of Snarky's own `assert_equal`.

`assertEqHalf_zero_iff` (§3a) is its soundness lemma. -/

/-- Two variables that a merge WOULD union, pinned with a row instead. The relation this asserts is
the same one the zero-row merge asserts — `assertEqHalf_zero_iff` — which is exactly why the merge
is allowed to replace it. -/
def assertEqRowCost : Nat := 1

/-! ## §5 — one-hot.

⚑ Read §0's last paragraph first: o1js's `Provable.switch` emits NO exclusivity gate. -/

/-- A running-sum chain. `steps` is `(addend, next-accumulator)`; each step is one `Generic` half.
The accumulator variables are what `KimchiArena` allocates. -/
def sumFromHalves (acc : PVar) : List (PVar × PVar) → List Half
  | [] => []
  | (x, n) :: rest => addHalf acc x n :: sumFromHalves n rest

/-- The variable holding the chain's total. -/
def lastOut (acc : PVar) : List (PVar × PVar) → PVar
  | [] => acc
  | (_, n) :: rest => lastOut n rest

/-- **The chain's soundness lemma**: the last accumulator holds the sum. -/
theorem sumFromHalves_sound (w : PVar → F) :
    ∀ (acc : PVar) (steps : List (PVar × PVar)),
      (∀ h ∈ sumFromHalves acc steps, halfEval w h = 0) →
      w (lastOut acc steps) = w acc + (steps.map (fun s => w s.1)).sum := by
  intro acc steps
  induction steps generalizing acc with
  | nil => intro _; simp [lastOut]
  | cons st rest ih =>
    obtain ⟨x, n⟩ := st
    intro hs
    have h0 : halfEval w (addHalf acc x n) = 0 :=
      hs (addHalf acc x n) (by simp [sumFromHalves])
    rw [addHalf_eval] at h0
    have hrest : ∀ h ∈ sumFromHalves n rest, halfEval w h = 0 :=
      fun h hh => hs h (by simp only [sumFromHalves]; exact List.mem_cons_of_mem _ hh)
    have hih := ih n hrest
    simp only [lastOut, List.map_cons, List.sum_cons]
    rw [hih]
    linear_combination -h0

/-- ⚑ **A ONE-HOT SELECTOR BANK.** Every selector booleanity-pinned, their sum chained, and the
total pinned to `1`. The `Σ = 1` half is the one o1js's `Provable.switch` does not emit. -/
def oneHotHalves (s0 : PVar) (steps : List (PVar × PVar)) : List Half :=
  (boolHalf s0 :: steps.map (fun st => boolHalf st.1))
    ++ sumFromHalves s0 steps
    ++ [ constHalf (lastOut s0 steps) 1 ]

/-! The three membership facts, named so the soundness proofs do not depend on `simp`'s
normalisation of `++`. -/

theorem head_bool_mem (s0 : PVar) (steps : List (PVar × PVar)) :
    boolHalf s0 ∈ oneHotHalves s0 steps :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))

theorem step_bool_mem {s0 : PVar} {steps : List (PVar × PVar)} {st : PVar × PVar} (hst : st ∈ steps) :
    boolHalf st.1 ∈ oneHotHalves s0 steps :=
  List.mem_append_left _
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨st, hst, rfl⟩)))

theorem chain_mem {s0 : PVar} {steps : List (PVar × PVar)} {h : Half}
    (hh : h ∈ sumFromHalves s0 steps) : h ∈ oneHotHalves s0 steps :=
  List.mem_append_left _ (List.mem_append_right _ hh)

theorem sum_pin_mem (s0 : PVar) (steps : List (PVar × PVar)) :
    constHalf (lastOut s0 steps) 1 ∈ oneHotHalves s0 steps :=
  List.mem_append_right _ (List.mem_cons_self ..)

/-- Every selector is boolean. -/
theorem oneHotHalves_selectors_boolean (w : PVar → F) (s0 : PVar) (steps : List (PVar × PVar))
    (hs : ∀ h ∈ oneHotHalves s0 steps, halfEval w h = 0) :
    (w s0 = 0 ∨ w s0 = 1) ∧ ∀ st ∈ steps, (w st.1 = 0 ∨ w st.1 = 1) :=
  ⟨(boolHalf_zero_iff w s0).1 (hs _ (head_bool_mem s0 steps)),
   fun st hst => (boolHalf_zero_iff w st.1).1 (hs _ (step_bool_mem hst))⟩

/-- ⚑ **AND THEIR SUM IS `1`** — the gate o1js leaves to `Provable.asProver`. -/
theorem oneHotHalves_sums_to_one (w : PVar → F) (s0 : PVar) (steps : List (PVar × PVar))
    (hs : ∀ h ∈ oneHotHalves s0 steps, halfEval w h = 0) :
    w s0 + (steps.map (fun st => w st.1)).sum = 1 := by
  have hchain : ∀ h ∈ sumFromHalves s0 steps, halfEval w h = 0 := fun h hh => hs h (chain_mem hh)
  have hlast : halfEval w (constHalf (lastOut s0 steps) 1) = 0 := hs _ (sum_pin_mem s0 steps)
  rw [constHalf_eval] at hlast
  rw [sumFromHalves_sound w s0 steps hchain] at hlast
  push_cast at hlast
  linear_combination hlast

/-! ## §6 — ⚑ THE COLLAPSE: the open-coded muxes, expressed as gadget calls.

These are the shapes at `KimchiStepMainCore.lean:2999` (`sfTermRows`' `G.if_`, two coordinates) and
`:4176` (the sponge-state mask, three lanes). Stated here as `rfl` identities so that rewriting
those sites CANNOT move a byte: the row schedules are the SAME lists of halves.

⚠ `KimchiWrapMainCore`'s copy is a live sibling's file (the wrap cone) and is reported, not
edited. -/

/-- `sfTermRows`' two coordinate muxes, as gadget calls. -/
def sfMuxHalves (odd accX hmX dX mX resX accY hmY dY mY resY : PVar) : List Half :=
  selectHalves odd ⟨accX, hmX, dX, mX, resX⟩ ++ selectHalves odd ⟨accY, hmY, dY, mY, resY⟩

/-- **UNMOVED.** The gadget call produces the six-half block `sfTermRows` writes by hand (entries
2..7 of its `packHalves` list) — pinned against the COEFFICIENT BYTES, not against `cSub`/`cMul`/
`cAdd`, so the pin survives any later edit to those names. -/
theorem sfMuxHalves_is_the_open_coded_shape
    (odd accX hmX dX mX resX accY hmY dY mY resY : PVar) :
    sfMuxHalves odd accX hmX dX mX resX accY hmY dY mY resY =
      [ ([some accX, some hmX, some dX],   ([1, -1, -1, 0, 0] : List Int))
      , ([some odd,  some dX,  some mX],   ([0,  0, -1, 1, 0] : List Int))
      , ([some hmX,  some mX,  some resX], ([1,  1, -1, 0, 0] : List Int))
      , ([some accY, some hmY, some dY],   ([1, -1, -1, 0, 0] : List Int))
      , ([some odd,  some dY,  some mY],   ([0,  0, -1, 1, 0] : List Int))
      , ([some hmY,  some mY,  some resY], ([1,  1, -1, 0, 0] : List Int)) ] := rfl

/-- The sponge-state mask's three lanes, as ONE vectorised gadget call. -/
def spongeMaskHalves (keep : PVar) (lanes : List MuxWires) : List Half :=
  selectHalvesN keep lanes

/-- **UNMOVED.** At three lanes the vectorised packing is exactly the `(cSub ++ cMul) ×3` then
`(cAdd ++ cAdd)`, `(cAdd ++ cNil)` row schedule `:4176` writes by hand — pinned against the
coefficient bytes. -/
theorem spongeMaskHalves_three_lanes (keep : PVar) (x y z : MuxWires) :
    spongeMaskHalves keep [x, y, z] =
      [ ([some x.t, some x.e, some x.d],     ([1, -1, -1, 0, 0] : List Int))
      , ([some keep, some x.d, some x.m],    ([0,  0, -1, 1, 0] : List Int))
      , ([some y.t, some y.e, some y.d],     ([1, -1, -1, 0, 0] : List Int))
      , ([some keep, some y.d, some y.m],    ([0,  0, -1, 1, 0] : List Int))
      , ([some z.t, some z.e, some z.d],     ([1, -1, -1, 0, 0] : List Int))
      , ([some keep, some z.d, some z.m],    ([0,  0, -1, 1, 0] : List Int))
      , ([some x.e, some x.m, some x.out],   ([1,  1, -1, 0, 0] : List Int))
      , ([some y.e, some y.m, some y.out],   ([1,  1, -1, 0, 0] : List Int))
      , ([some z.e, some z.m, some z.out],   ([1,  1, -1, 0, 0] : List Int)) ] := rfl

/-! ## §7 — the gadgets' ROW COST, as arithmetic on the emitted object.

Two halves per `Generic` row. These are the numbers the o1js oracle checks against
`Provable.constraintSystem(...).rows`. -/

/-- Halves → rows, `packHalves`' own count. -/
def rowsOfHalves (hs : List Half) : Nat := (hs.length + 1) / 2

/-- An unused half. -/
def nilHalf : Half := ([none, none, none], cNil)

/-- **Pack halves two to a `Generic` row**, straight to `PGate` — Snarky's own double-generic
filling, the `place`-facing twin of `KimchiStepMainCore.packHalves` (which builds `SRow`) and
`KimchiWrapMainCore.packHalves` (which builds `WRow`). A gadget list becomes a circuit here. -/
def packHalvesPG (hs : List Half) : List PGate :=
  (List.range (rowsOfHalves hs)).map (fun r =>
    let h1 := hs.getD (2 * r) nilHalf
    let h2 := if 2 * r + 1 < hs.length then hs.getD (2 * r + 1) nilHalf else nilHalf
    { kind := .generic, permVars := h1.1 ++ h2.1 ++ [none], coeffs := h1.2 ++ h2.2 })

theorem packHalvesPG_length (hs : List Half) :
    (packHalvesPG hs).length = rowsOfHalves hs := by simp [packHalvesPG]

/-! ### §7a — an INTEGER witness, so a satisfying assignment is `decide`-able.

`halfEval` is stated over a field because that is where soundness lives. A concrete witness is
easier to check over `ℤ`, and `halfEval_ofInt` says the two agree: **an integer assignment that
makes a half vanish over `ℤ` makes it vanish in EVERY field**, so a `decide`d integer witness is
evidence about the real circuit and not about a toy. -/

/-- `halfEval` over `ℤ`. -/
def slotValInt (w : PVar → Int) (h : Half) (i : Nat) : Int :=
  match h.1.getD i none with
  | some p => w p
  | none   => 0

/-- The half's constraint polynomial at an integer assignment. -/
def halfEvalInt (w : PVar → Int) (h : Half) : Int :=
  coef h 0 * slotValInt w h 0 + coef h 1 * slotValInt w h 1 + coef h 2 * slotValInt w h 2
    + coef h 3 * (slotValInt w h 0 * slotValInt w h 1) + coef h 4

/-- ⚑ The bridge: the integer evaluation CASTS to the field evaluation. -/
theorem halfEval_ofInt (w : PVar → Int) (h : Half) :
    halfEval (fun p => ((w p : Int) : F)) h = ((halfEvalInt w h : Int) : F) := by
  have hs : ∀ i, slotVal (fun p => ((w p : Int) : F)) h i = ((slotValInt w h i : Int) : F) := by
    intro i; simp only [slotVal, slotValInt]
    cases h.1.getD i none <;> simp
  simp only [halfEval, halfEvalInt, hs]
  push_cast
  ring

/-- …so a witness that vanishes over `ℤ` vanishes over the field. -/
theorem halfEval_zero_of_int (w : PVar → Int) (h : Half) (hz : halfEvalInt w h = 0) :
    halfEval (fun p => ((w p : Int) : F)) h = 0 := by
  rw [halfEval_ofInt, hz]; simp

theorem selectChecked_halves (b : PVar) (x : MuxWires) : (selectChecked b x).length = 4 := rfl
theorem selectChecked_rows (b : PVar) (x : MuxWires) : rowsOfHalves (selectChecked b x) = 2 := by
  simp [rowsOfHalves, selectChecked_halves]

/-- ⚑ **o1js's `Provable.if` costs three halves and leaves booleanity to the caller**; ours costs
four because it emits the pin. The extra half is the difference between a mux and a conditional. -/
theorem selectHalves_halves (b : PVar) (x : MuxWires) : (selectHalves b x).length = 3 := rfl

#assert_axioms boolHalf_zero_iff
#assert_axioms assertEqHalf_zero_iff
#assert_axioms selectHalves_sound
#assert_axioms selectChecked_sound
#assert_axioms selectHalves_escapes_at_two
#assert_axioms sumFromHalves_sound
#assert_axioms oneHotHalves_selectors_boolean
#assert_axioms oneHotHalves_sums_to_one
#assert_axioms sfMuxHalves_is_the_open_coded_shape
#assert_axioms spongeMaskHalves_three_lanes

end Dregg2.Circuit.Emit.KimchiGadgets
