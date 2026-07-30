/-
# Dregg2.Circuit.Emit.KimchiEffectIncNonce — ONE Lean source, TWO emissions: the BabyBear
EffectVM row of `incrementNonceA`, and a Kimchi circuit for the SAME transition.

## ⚑ SAY THE SUBSTRATE OUT LOUD

This is **Lean-authored AIR on BOTH targets.** `incNonceHeads` is a `def`-generator producing a
`List AirBuilder.Head`; the BabyBear side lowers it through `headToExpr` (the deployed
`EmittedExpr` gate vocabulary) and the Kimchi side lowers it through `KimchiLower.lowerHeadGens`
(the deployed `GateType::Generic` sub-gate vocabulary). Neither Rust nor TypeScript authors a
constraint anywhere on this path: the o1js consumer is a TRANSCRIBER of the `Gen1` list this file
emits, driven entirely by the emitted coefficients.

## ⚑ WHAT THIS IS, AND HOW IT DIFFERS FROM THE VERIFIER ROUTE

`KimchiLower`'s header scopes the whole compiler to **route A** — a Kimchi circuit that VERIFIES a
dregg STARK proof, in which `lowerHead` is the verifier's `AIR.evalAtZeta` rung, invoked at the
opened points only. That framing is correct for that route and this file does not weaken it.

This file is **route B**: dregg's own semantics re-emitted into Kimchi, so Mina can check a dregg
state transition NATIVELY, with no FRI proof consumed. The two routes prove different things and
the difference is not cosmetic:

  * **A** establishes *dregg's chain says this*. It consumes a proof, so it inherits dregg's whole
    accumulator/commitment structure — and it inherits the undischarged FRI/STARK soundness floor.
  * **B** establishes *this transition is VALID under dregg's semantics*. It consumes no proof, so
    there is nothing to be unsound about beyond Kimchi itself — and it says **nothing whatever
    about whether dregg's chain contains the transition.** B is a semantics checker, not a
    membership checker. Anyone can present a well-formed transition that never happened.

Route B's honest question is "are these still the same semantics?", and §2/§5 are the answer:
BOTH emissions descend from `incNonceHeads`, and each has a forcing lemma landing on the SAME
Lean `def` (`EffectVmEmitIncrementNonce.CellIncNonceSpec`). Not two implementations agreeing on
tests — two lowerings of one source, with refinement proved on each side.

## The four rungs

  1. **§1 `incNonceHeads`** — the one source. Thirteen polynomial heads: eleven economic
     passthroughs, the reserved passthrough, and the nonce tick. Plus `selectorBindHead`, the
     fourteenth, which is what makes the circuit about `incrementNonceA` and not merely about the
     SHAPE "economic block frozen, nonce ticked"; `incNonceHeadsBound` is what is emitted.
  2. **§2 the WELD** — `heads_denote_deployed_gates`: head-for-head, `evalH` of the source equals
     `EmittedExpr.eval` of the gate body the DEPLOYED descriptor
     (`EffectVmEmitIncrementNonce.incNonceRowGates`) already carries. The source is not a third
     copy; it denotes the deployed list. **§2a** does the same for the selector head against the
     deployed `selectorGate 53`, which `selectorGate_in_descriptor` shows really is in the
     descriptor.
  3. **§4 the KIMCHI emission** — `incNonceKimchiRows`, `packGen`-packed, with
     `kimchi_rows_force_heads` at arbitrary `CommRing` over the ACTUAL emitted list.
  4. **§5 the apex** — `two_emissions_one_def`: both arrows land on `CellIncNonceSpec`; plus
     `kimchi_forces_selector`, which refuses a row carrying any other effect's selector.

⚑ **This covers 14 of the deployed descriptor's 35 constraints.** The 21 not emitted are
`transitionAll` (14, cross-row continuity — this emission is single-row), the 7 boundary PI pins,
and — the one that matters — **the 4 GROUP-4 hash sites binding the after-state into
`state_commit`.** Without those, the circuit relates two bare 13-tuples and does NOT prove they
are the pre-image of any commitment, i.e. that they are a dregg cell at all. See
`docs/MINA-DREGG-SEMANTICS-NATIVE.md` §4.2; it is where all the cost lives too.

## ⚑ WHERE THE TWO SIDES ARE NOT SYMMETRIC, stated rather than smoothed

`incNonceVm_faithful` (BabyBear) reads its gates through `holdsVm`, which is `≡ 0 [ZMOD 2013265921]`,
so it needs the full `IncNonceRowCanon` envelope INCLUDING `nonce_before + 1 < p`. The Kimchi side
over ℤ needs no envelope at all, and over the Pallas base field needs `KimchiRowCanon`, which is
`IncNonceRowCanon` MINUS the overflow hypothesis — because the residual a BabyBear-canonical row
produces is bounded by `2^31 + 2`, and the Kimchi field is `> 2^254`. `kimchiRowCanon_of_incNonceRowCanon`
proves the implication and `kimchi_envelope_strictly_weaker` exhibits a row satisfying the Kimchi
envelope and not the BabyBear one. **The weaker forcing lemma is the BabyBear one**, which is the
opposite of the direction one would fear.

## Anti-vacuity, at birth

`incNonceKimchiRows_satisfiable` exhibits a concrete assignment satisfying every emitted row (the
honest row `goodIncNonceRow`, bal 100→100, nonce 5→6). `tamper_moved_balance_refused` /
`tamper_frozen_nonce_refused` prove the emitted circuit has NO satisfying assignment over a row
that moves value or freezes the nonce — the general statement, not a sampled one. Every emitted row
is a MODELLED gate (`incNonceRows_all_modelled`), so `KimchiTarget`'s fail-closed `False` is not
what discharges anything here.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file. Imports read-only.
-/
import Dregg2.Circuit.Emit.KimchiLower
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce

namespace Dregg2.Circuit.Emit.KimchiEffectIncNonce

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.AirBuilder (Head evalH evalTerm headToExpr headToExpr_eval)
open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSA eSB eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false

/-! ## §1 — THE ONE SOURCE.

Thirteen polynomial heads. Both emissions descend from this list and nothing else. -/

/-- A state-block FREEZE head: `state_after[off] − state_before[off]`. -/
def freezeHead (off : Nat) : Head := ⟨[(1, [saCol off]), (-1, [sbCol off])], 0⟩

/-- The nonce TICK head: `state_after[NONCE] − state_before[NONCE] − (1 − s_noop)`, written out as
`+1·sa − 1·sb + 1·s_noop − 1`. This is the runtime convention (`air.rs`'s global nonce gate): the
counter advances on every non-NoOp row. -/
def nonceTickHead : Head :=
  ⟨[(1, [saCol state.NONCE]), (-1, [sbCol state.NONCE]), (1, [sel.NOOP])], -1⟩

/-- **THE SOURCE.** The `incrementNonceA` EffectVM row: the whole economic state block frozen,
the nonce ticked. Ordered exactly as `EffectVmEmitIncrementNonce.incNonceRowGates`. -/
def incNonceHeads : List Head :=
  [ freezeHead state.BALANCE_LO, freezeHead state.BALANCE_HI, nonceTickHead
  , freezeHead state.CAP_ROOT, freezeHead state.RESERVED ]
  ++ (List.range 8).map (fun i => freezeHead (state.FIELD_BASE + i))

/-- Thirteen heads: five named plus the eight generic fields. -/
theorem incNonceHeads_length : incNonceHeads.length = 13 := by
  simp [incNonceHeads]

/-- **The SELECTOR-BINDING head** — `(1 − s_noop)·(1 − s_incrementNonce)`, expanded.

This is the gate that makes the circuit about `incrementNonceA` RATHER THAN about the shape
"economic block frozen, nonce ticked". Without it, any effect with the same shape satisfies the
same rows and a proof would say less than its name. `EffectVmEmit.selectorGateBody` is the
deployed body; §2a welds this head to it.

Degree 2, so the lowering pays one multiplication sub-gate — the first non-linear head here. -/
def selectorBindHead : Head :=
  ⟨[(-1, [sel.NOOP]), (-1, [SEL_INCREMENT_NONCE]), (1, [sel.NOOP, SEL_INCREMENT_NONCE])], 1⟩

/-- **What the Kimchi side actually emits**: the thirteen row heads PLUS the selector binding.
Kept distinct from `incNonceHeads` so §2's denotational weld stays a statement about the
thirteen gates `incNonceRowGates` carries, and §2a is a separate weld to `selectorGate 53`. -/
def incNonceHeadsBound : List Head := incNonceHeads ++ [selectorBindHead]

theorem incNonceHeadsBound_length : incNonceHeadsBound.length = 14 := by
  simp [incNonceHeadsBound, incNonceHeads]

theorem mem_bound {h : Head} (hm : h ∈ incNonceHeads) : h ∈ incNonceHeadsBound := by
  simp [incNonceHeadsBound, hm]

/-! ### §1a — what a head MEANS, over ℤ. -/

@[simp] theorem evalH_freezeHead (a : Assignment) (off : Nat) :
    evalH (freezeHead off) a = a (saCol off) - a (sbCol off) := by
  simp only [freezeHead, evalH, evalTerm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.prod_cons, List.prod_nil]
  ring

@[simp] theorem evalH_selectorBindHead (a : Assignment) :
    evalH selectorBindHead a = (1 - a sel.NOOP) * (1 - a SEL_INCREMENT_NONCE) := by
  simp only [selectorBindHead, evalH, evalTerm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.prod_cons, List.prod_nil]
  ring

@[simp] theorem evalH_nonceTickHead (a : Assignment) :
    evalH nonceTickHead a
      = a (saCol state.NONCE) - a (sbCol state.NONCE) - (1 - a sel.NOOP) := by
  simp only [nonceTickHead, evalH, evalTerm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.prod_cons, List.prod_nil]
  ring

/-! ## §2 — THE WELD: the source DENOTES the deployed BabyBear gate list.

`EffectVmEmitIncrementNonce.incNonceRowGates` is the gate list the running descriptor carries and
that `incNonceVm_faithful` reasons about. If `incNonceHeads` were a re-authoring of it, this whole
file would be a differential test wearing a proof's clothes. It is not: the two lists are proved
head-for-head EQUAL AS DENOTATIONS, at every assignment. -/

/-- The deployed gate BODIES, in the deployed order. -/
def incNonceGateBodies : List EmittedExpr :=
  [gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass] ++ (List.range 8).map gFieldPass

/-- The deployed constraint list IS those bodies, wrapped. -/
theorem incNonceRowGates_eq :
    incNonceRowGates = incNonceGateBodies.map VmConstraint.gate := by
  simp only [incNonceRowGates, incNonceGateBodies, gFieldPassAll, List.map_append,
    List.map_cons, List.map_nil, List.map_map, Function.comp_def]

theorem freezeHead_denotes (a : Assignment) (off : Nat) :
    evalH (freezeHead off) a = (eSub (eSA off) (eSB off)).eval a := by
  simp only [evalH_freezeHead, eSub, eSA, eSB, EmittedExpr.eval]
  ring

theorem nonceTickHead_denotes (a : Assignment) :
    evalH nonceTickHead a = gNonce.eval a := by
  simp only [evalH_nonceTickHead, gNonce, eSub, eSA, eSB, eSelNoop, EmittedExpr.eval]
  ring

/-- **THE WELD.** Head-for-head, the source's value is the deployed gate body's value — at EVERY
assignment, so this is a denotational identity and not a sampled agreement. -/
theorem heads_denote_deployed_gates (a : Assignment) :
    incNonceHeads.map (fun h => evalH h a)
      = incNonceGateBodies.map (fun e => e.eval a) := by
  simp only [incNonceHeads, incNonceGateBodies, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, freezeHead_denotes, nonceTickHead_denotes,
    gBalLoFreeze, gBalHi, gCapPass, gResPass, gFieldPass]

/-! ### §2a — the SELECTOR weld, to the deployed `selectorGate 53`.

`selectorGates 53` is a segment of `incrementNonceVmDescriptor.constraints`, so this is a second
head welded to a second piece of the DEPLOYED descriptor — not a gate invented for the Kimchi
side. With it, §5's `kimchi_forces_selector` makes the emitted circuit refuse a row that is not
an `incrementNonce` row. -/

theorem selectorBindHead_denotes (a : Assignment) :
    evalH selectorBindHead a = (selectorGateBody SEL_INCREMENT_NONCE).eval a := by
  simp only [evalH_selectorBindHead, selectorGateBody, EmittedExpr.eval]
  ring

/-- The deployed descriptor really does carry this gate. -/
theorem selectorGate_in_descriptor :
    selectorGate SEL_INCREMENT_NONCE ∈ incrementNonceVmDescriptor.constraints := by
  simp only [incrementNonceVmDescriptor, List.mem_append, selectorGates, List.mem_singleton]
  exact Or.inr rfl

/-! ## §3 — THE SHARED MEANING: the heads vanish IFF the row realises the intent.

Over ℤ, with no canonicality envelope. `IncNonceRowIntent` is the deployed intent predicate that
`incNonceVm_faithful` names on the BabyBear side and `intent_to_cellSpec` consumes. -/

theorem heads_zero_iff_intent (env : VmRowEnv) :
    (∀ h ∈ incNonceHeads, evalH h env.loc = 0) ↔ IncNonceRowIntent env := by
  constructor
  · intro h
    have hLo := h (freezeHead state.BALANCE_LO) (by simp [incNonceHeads])
    have hHi := h (freezeHead state.BALANCE_HI) (by simp [incNonceHeads])
    have hN := h nonceTickHead (by simp [incNonceHeads])
    have hCap := h (freezeHead state.CAP_ROOT) (by simp [incNonceHeads])
    have hRes := h (freezeHead state.RESERVED) (by simp [incNonceHeads])
    simp only [evalH_freezeHead, evalH_nonceTickHead] at hLo hHi hN hCap hRes
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    intro i hi
    have hF := h (freezeHead (state.FIELD_BASE + i)) (by
      simp only [incNonceHeads, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩)
    simp only [evalH_freezeHead] at hF
    omega
  · rintro ⟨hLo, hHi, hN, hCap, hRes, hF⟩ h hm
    simp only [incNonceHeads, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [evalH_freezeHead]; omega
    · simp only [evalH_freezeHead]; omega
    · simp only [evalH_nonceTickHead]; omega
    · simp only [evalH_freezeHead]; omega
    · simp only [evalH_freezeHead]; omega
    · simp only [evalH_freezeHead]; have := hF i hi; omega

/-! ## §4 — THE KIMCHI EMISSION.

`lowerHeadGens` is `KimchiLower`'s straight-line lowering; `lowerHeadsGens` chains it across a list
of heads, threading the freshness watermark so no head's intermediates collide with another's.
`packGen` is the two-sub-gates-per-row backend whose meaning-preservation is
`packGen_holds_iff`. -/

/-- The first fresh variable index — past the whole EffectVM row (`EFFECT_VM_WIDTH = 188`), so no
intermediate can alias a real column. -/
def NV0 : Nat := EFFECT_VM_WIDTH

/-- Lower a LIST of heads, threading the watermark. -/
def lowerHeadsGens : List Head → Nat → List Gen1
  | [], _ => []
  | h :: rest, nv => lowerHeadGens h nv ++ lowerHeadsGens rest (lowerHeadWm h nv)

/-- **The emitted sub-gate program** for the `incrementNonceA` row. -/
def incNonceGens : List Gen1 := lowerHeadsGens incNonceHeadsBound NV0

/-- **The emitted Kimchi circuit** — `GateType::Generic` rows, two sub-gates each. -/
def incNonceKimchiRows : List KRow := packGen incNonceGens

/-- Twelve freeze heads at four sub-gates each, the nonce tick at five, the selector binding at
six (it is the only head with a product term, hence the only multiplication). -/
theorem incNonceGens_length : incNonceGens.length = 59 := by
  simp only [incNonceGens, incNonceHeadsBound, incNonceHeads, NV0]
  rfl

/-- **The row count is a theorem, not a measurement.** `⌈59/2⌉ = 30`. -/
theorem incNonceKimchiRows_length : incNonceKimchiRows.length = 30 := by
  rw [incNonceKimchiRows, packGen_length, incNonceGens_length]

/-- Every emitted row carries a MODELLED gate, so nothing below is discharged by
`KimchiTarget`'s fail-closed `False`. -/
theorem incNonceRows_all_modelled :
    ∀ r ∈ incNonceKimchiRows, r.gate.modelled = true :=
  packGen_all_modelled _

/-! ### §4a — soundness of the chained lowering. -/

/-- `lowerHead_sound` restated at the SUB-GATE level, which is what chains. -/
theorem lowerHeadGens_sound {R : Type} [CommRing R] (a : Nat → R) (h : Head) (nv : Nat)
    (hg : gensHold a (lowerHeadGens h nv)) : headEvalR a h = 0 :=
  lowerHead_sound a h nv ((packGen_holds_iff a _).mpr hg)

theorem lowerHeadsGens_sound {R : Type} [CommRing R] (a : Nat → R) :
    ∀ (hs : List Head) (nv : Nat), gensHold a (lowerHeadsGens hs nv) →
      ∀ h ∈ hs, headEvalR a h = 0 := by
  intro hs
  induction hs with
  | nil => intro _ _ h hm; cases hm
  | cons x xs ih =>
    intro nv hg h hm
    simp only [lowerHeadsGens] at hg
    obtain ⟨hg1, hg2⟩ := gensHold_append hg
    rcases List.mem_cons.1 hm with rfl | hm2
    · exact lowerHeadGens_sound a _ _ hg1
    · exact ih _ hg2 h hm2

/-- **SEMANTICS PRESERVATION, over the ACTUAL emitted rows, at arbitrary `CommRing`.** Any
assignment satisfying every emitted Kimchi row makes every source head vanish. -/
theorem kimchi_rows_force_bound {R : Type} [CommRing R] (a : Nat → R)
    (hr : rowsHold a incNonceKimchiRows) : ∀ h ∈ incNonceHeadsBound, headEvalR a h = 0 :=
  lowerHeadsGens_sound a incNonceHeadsBound NV0 ((packGen_holds_iff a _).mp hr)

/-- The same, restricted to the thirteen ROW heads — the form every downstream rung uses. -/
theorem kimchi_rows_force_heads {R : Type} [CommRing R] (a : Nat → R)
    (hr : rowsHold a incNonceKimchiRows) : ∀ h ∈ incNonceHeads, headEvalR a h = 0 :=
  fun h hm => kimchi_rows_force_bound a hr h (mem_bound hm)

/-! ## §5 — THE APEX: both emissions force the SAME Lean `def`. -/

/-- The Kimchi rows force the deployed intent predicate. Over ℤ this needs NO canonicality
envelope — contrast the BabyBear side, which reads its gates mod `2013265921`. -/
theorem kimchi_forces_intent (env : VmRowEnv)
    (hr : rowsHold env.loc incNonceKimchiRows) : IncNonceRowIntent env := by
  refine (heads_zero_iff_intent env).mp ?_
  intro h hm
  have hz := kimchi_rows_force_heads (R := ℤ) env.loc hr h hm
  rwa [headEvalR_int] at hz

/-- **THE EMITTED CIRCUIT REFUSES A ROW THAT IS NOT AN `incrementNonce` ROW.**

Over ℤ this needs no primality argument at all — `(1 − 0)·(1 − s) = 0` is `s = 1` outright, where
the BabyBear reading of the same gate (`selectorGate_holds_iff`) has to invoke that `2013265921`
is prime to split the product. Another place the Kimchi side's obligation is the lighter one. -/
theorem kimchi_forces_selector (a : Assignment)
    (hr : rowsHold a incNonceKimchiRows) (hnoop : a sel.NOOP = 0) :
    a SEL_INCREMENT_NONCE = 1 := by
  have hz := kimchi_rows_force_bound (R := ℤ) a hr selectorBindHead
    (by simp [incNonceHeadsBound])
  rw [headEvalR_int] at hz
  simp only [evalH_selectorBindHead, hnoop] at hz
  omega

/-- **ARROW ONE — the Kimchi emission forces `CellIncNonceSpec`.** -/
theorem kimchi_forces_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesIncNonce env pre post)
    (hr : rowsHold env.loc incNonceKimchiRows) : CellIncNonceSpec pre post :=
  intent_to_cellSpec env pre post hnoop henc (kimchi_forces_intent env hr)

/-- **ARROW TWO — the deployed BabyBear descriptor forces `CellIncNonceSpec`.** This is
`incNonceVm_faithful` (which is about the DEPLOYED `incNonceRowGates`) composed with
`intent_to_cellSpec`; nothing new is proved here, it is restated so the two arrows sit side by
side and the shared target is visible. -/
theorem babybear_forces_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : IncNonceRowCanon env)
    (henc : RowEncodesIncNonce env pre post)
    (hg : ∀ c ∈ incNonceRowGates, c.holdsVm env false false) : CellIncNonceSpec pre post :=
  intent_to_cellSpec env pre post hnoop henc ((incNonceVm_faithful env hcanon).mp hg)

/-- **THE DELIVERABLE — TWO EMISSIONS, ONE `def`.**

The Kimchi circuit `incNonceKimchiRows` and the deployed BabyBear gate list `incNonceRowGates`
both FORCE `EffectVmEmitIncrementNonce.CellIncNonceSpec pre post` — the same Lean `def`, at the
same encoded `(pre, post)`. Together with §2's `heads_denote_deployed_gates` (the two lowerings
descend from ONE source list of heads, and that source denotes the deployed gate bodies), this is
the "are these still the same semantics?" question answered with a theorem rather than a test. -/
theorem two_emissions_one_def (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesIncNonce env pre post) :
    (rowsHold env.loc incNonceKimchiRows → CellIncNonceSpec pre post)
    ∧ (IncNonceRowCanon env →
        (∀ c ∈ incNonceRowGates, c.holdsVm env false false) → CellIncNonceSpec pre post) :=
  ⟨fun hr => kimchi_forces_cellSpec env pre post hnoop henc hr,
   fun hcanon hg => babybear_forces_cellSpec env pre post hnoop hcanon henc hg⟩

/-! ## §6 — THE FIELD-ACCURATE KIMCHI STATEMENT.

§5 reads the emitted rows over ℤ. The deployed Kimchi circuit runs over the **Pallas base field**
(o1js's `Field`), so the honest statement quantifies an arbitrary `ZMod p`-valued assignment and
recovers the ℤ intent from a canonicality envelope — exactly the shape `IncNonceRowCanon` has on
the BabyBear side, and STRICTLY WEAKER, because the residual is `< 2^31 + 2` and `p > 2^254`. -/

/-- The Pallas base field modulus — o1js's `Field` (`2^254 + 45560315531419706090280762371685220353`). -/
def PALLAS_BASE_MODULUS : Nat :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337

theorem pallas_gt_two_pow_254 : 2 ^ 254 < PALLAS_BASE_MODULUS := by
  norm_num [PALLAS_BASE_MODULUS]

/-- **The whole reason the Kimchi envelope can be weaker.** A residual built from BabyBear-canonical
cells is bounded by `2013265921`, and the Kimchi field is larger than that by ~2^223. -/
theorem babybear_lt_pallas : 2013265921 < PALLAS_BASE_MODULUS := by
  norm_num [PALLAS_BASE_MODULUS]

/-- The bound the DEPLOYED o1js circuit actually enforces on every state cell:
`Gadgets.rangeCheck32`, i.e. `< 2^32`. It is a whole binade LOOSER than BabyBear canonicality and
still ~2^222 below the Kimchi modulus, which is the point. -/
theorem two_pow_32_lt_pallas : 4294967296 < PALLAS_BASE_MODULUS := by
  norm_num [PALLAS_BASE_MODULUS]

/-- **The Kimchi-side canonicality envelope** — weaker than `IncNonceRowCanon` in TWO ways: the
`nonce_before + 1 < p` overflow hypothesis is gone, and the per-cell box is `2^32` rather than the
BabyBear modulus. The BabyBear side needs both because its residual is read mod `2013265921`; the
Kimchi side needs neither, because the same residual is read mod a `> 2^254` prime.

`2^32` is not a slack chosen for comfort: it is EXACTLY what the deployed o1js circuit enforces
(`Gadgets.rangeCheck32` on every state-block column), so this envelope is discharged by the
circuit rather than assumed about it. -/
def KimchiRowCanon (env : VmRowEnv) : Prop :=
  (∀ off, off < STATE_SIZE →
      (0 ≤ env.loc (sbCol off) ∧ env.loc (sbCol off) < 4294967296)
      ∧ (0 ≤ env.loc (saCol off) ∧ env.loc (saCol off) < 4294967296))
  ∧ (env.loc sel.NOOP = 0 ∨ env.loc sel.NOOP = 1)

theorem kimchiRowCanon_of_incNonceRowCanon (env : VmRowEnv) (h : IncNonceRowCanon env) :
    KimchiRowCanon env := by
  refine ⟨fun off hoff => ?_, h.2.1⟩
  have := h.1 off hoff
  omega

/-- The columns any source head reads all live below `NV0`, so a Kimchi assignment that agrees with
the row on `[0, NV0)` pins every head's value. -/
theorem head_cols_below_NV0 (off : Nat) (hoff : off < STATE_SIZE) :
    saCol off < NV0 ∧ sbCol off < NV0 ∧ sel.NOOP < NV0 := by
  simp only [saCol, sbCol, NV0, EFFECT_VM_WIDTH, STATE_AFTER_BASE, STATE_BEFORE_BASE,
    PARAM_BASE, NUM_EFFECTS, NUM_PARAMS, STATE_SIZE, sel.NOOP] at *
  omega

/-- A ℤ-residual strictly inside `(−p, p)` that vanishes in `ZMod p` is zero. -/
theorem int_eq_zero_of_zmod_zero {p : Nat} (x : ℤ)
    (hbound : x.natAbs < p) (hz : ((x : ℤ) : ZMod p) = 0) : x = 0 := by
  have hdvd : (p : ℤ) ∣ x := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  have hnat : p ∣ x.natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at h2
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hnat hbound)

/-- **THE FIELD-ACCURATE FORCING.** An arbitrary Pallas-field assignment satisfying the emitted
rows, agreeing with the row window on `[0, NV0)`, forces the deployed ℤ intent — under
`KimchiRowCanon` only. -/
theorem kimchi_pallas_forces_intent (env : VmRowEnv)
    (A : Nat → ZMod PALLAS_BASE_MODULUS)
    (hcol : ∀ v, v < NV0 → A v = ((env.loc v : ℤ) : ZMod PALLAS_BASE_MODULUS))
    (hcanon : KimchiRowCanon env)
    (hr : rowsHold A incNonceKimchiRows) : IncNonceRowIntent env := by
  obtain ⟨hcells, hnoopB⟩ := hcanon
  have hbb : 4294967296 < PALLAS_BASE_MODULUS := two_pow_32_lt_pallas
  -- a head's value over the Pallas assignment is the cast of its ℤ value
  have hforce := kimchi_rows_force_heads A hr
  -- the freeze heads
  have hfreeze : ∀ off, off < STATE_SIZE → freezeHead off ∈ incNonceHeads →
      env.loc (saCol off) = env.loc (sbCol off) := by
    intro off hoff hmem
    have hz := hforce _ hmem
    have hcast : headEvalR A (freezeHead off)
        = ((env.loc (saCol off) - env.loc (sbCol off) : ℤ) : ZMod PALLAS_BASE_MODULUS) := by
      obtain ⟨hsa, hsb, _⟩ := head_cols_below_NV0 off hoff
      simp only [headEvalR, freezeHead, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.prod_cons, List.prod_nil, hcol _ hsa, hcol _ hsb]
      push_cast
      ring
    rw [hcast] at hz
    have hb := hcells off hoff
    have := int_eq_zero_of_zmod_zero _ (by omega) hz
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfreeze _ (by norm_num [state.BALANCE_LO, STATE_SIZE]) (by simp [incNonceHeads])
  · exact hfreeze _ (by norm_num [state.BALANCE_HI, STATE_SIZE]) (by simp [incNonceHeads])
  · -- the nonce tick
    have hz := hforce nonceTickHead (by simp [incNonceHeads])
    have hoffN : state.NONCE < STATE_SIZE := by norm_num [state.NONCE, STATE_SIZE]
    obtain ⟨hsa, hsb, hnoopLt⟩ := head_cols_below_NV0 state.NONCE hoffN
    have hcast : headEvalR A nonceTickHead
        = ((env.loc (saCol state.NONCE) - env.loc (sbCol state.NONCE)
              - (1 - env.loc sel.NOOP) : ℤ) : ZMod PALLAS_BASE_MODULUS) := by
      simp only [headEvalR, nonceTickHead, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.prod_cons, List.prod_nil, hcol _ hsa, hcol _ hsb, hcol _ hnoopLt]
      push_cast
      ring
    rw [hcast] at hz
    have hb := hcells state.NONCE hoffN
    have hn01 : 0 ≤ env.loc sel.NOOP ∧ env.loc sel.NOOP ≤ 1 := by
      rcases hnoopB with h | h <;> rw [h] <;> norm_num
    have := int_eq_zero_of_zmod_zero _ (by omega) hz
    omega
  · exact hfreeze _ (by norm_num [state.CAP_ROOT, STATE_SIZE]) (by simp [incNonceHeads])
  · exact hfreeze _ (by norm_num [state.RESERVED, STATE_SIZE]) (by simp [incNonceHeads])
  · intro i hi
    refine hfreeze _ (by simp only [state.FIELD_BASE, STATE_SIZE]; omega) ?_
    simp only [incNonceHeads, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨i, hi, rfl⟩

/-- **ARROW ONE, at the deployed field.** -/
theorem kimchi_pallas_forces_cellSpec (env : VmRowEnv) (pre post : CellState)
    (A : Nat → ZMod PALLAS_BASE_MODULUS)
    (hcol : ∀ v, v < NV0 → A v = ((env.loc v : ℤ) : ZMod PALLAS_BASE_MODULUS))
    (hnoop : env.loc sel.NOOP = 0) (hcanon : KimchiRowCanon env)
    (henc : RowEncodesIncNonce env pre post)
    (hr : rowsHold A incNonceKimchiRows) : CellIncNonceSpec pre post :=
  intent_to_cellSpec env pre post hnoop henc
    (kimchi_pallas_forces_intent env A hcol hcanon hr)

/-! ## §7 — ANTI-VACUITY: satisfiable at birth, and refutable. -/

/-- The honest witness: `goodIncNonceRow` on the real columns, and the lowering's intermediates
above `NV0`. `freezeHead`'s three intermediates are `(0, v, 0)`; the nonce tick's four are
`(−1, nonce_after, 0, 0)`; the selector binding's five are `(1, 1, 0, 0, 0)` at a row where the
NoOp selector is `0` and `sel[53]` is `1`. Every other fresh slot is zero because every other
frozen cell is. -/
def satAssign : Assignment := fun v =>
  if v < NV0 then goodIncNonceRow.loc v
  else if v = 189 then 100
  else if v = 194 then -1
  else if v = 195 then 5
  else if v = 228 then 1
  else if v = 229 then 1
  else 0

/-- **SATISFIABLE AT BIRTH (sub-gates).** -/
theorem incNonceGens_satisfied : gensHold satAssign incNonceGens := by
  have h : ∀ g ∈ incNonceGens, Gen1.body satAssign g = 0 := by decide
  intro g hg
  exact h g hg

/-- **SATISFIABLE AT BIRTH (rows).** The emitted Kimchi circuit ACCEPTS the honest
increment-nonce row — so nothing above is true because nothing satisfies it. -/
theorem incNonceKimchiRows_satisfiable : rowsHold satAssign incNonceKimchiRows :=
  (packGen_holds_iff satAssign incNonceGens).mpr incNonceGens_satisfied

/-- **REFUTABLE — moved value.** No assignment whatever satisfies the emitted circuit over a row
whose post-balance differs from its pre-balance. This is the GENERAL statement: not "this forged
row is rejected", but "the emitted circuit has no satisfying assignment over ANY such row". -/
theorem tamper_moved_balance_refused (a : Assignment)
    (hwrong : a (saCol state.BALANCE_LO) ≠ a (sbCol state.BALANCE_LO)) :
    ¬ rowsHold a incNonceKimchiRows := by
  intro hr
  have hz := kimchi_rows_force_heads (R := ℤ) a hr (freezeHead state.BALANCE_LO)
    (by simp [incNonceHeads])
  rw [headEvalR_int] at hz
  simp only [evalH_freezeHead] at hz
  exact hwrong (by omega)

/-- **REFUTABLE — frozen nonce.** A row that does not tick the nonce is UNSAT. -/
theorem tamper_frozen_nonce_refused (a : Assignment)
    (hwrong : a (saCol state.NONCE) ≠ a (sbCol state.NONCE) + (1 - a sel.NOOP)) :
    ¬ rowsHold a incNonceKimchiRows := by
  intro hr
  have hz := kimchi_rows_force_heads (R := ℤ) a hr nonceTickHead (by simp [incNonceHeads])
  rw [headEvalR_int] at hz
  simp only [evalH_nonceTickHead] at hz
  exact hwrong (by omega)

/-- The deployed forged row (`badIncNonceRow`, post-`bal_lo` minted to 999) is UNSAT under the
Kimchi emission — the same instance `badIncNonceRow_rejected` refutes on the BabyBear side. -/
theorem badIncNonceRow_kimchi_unsat : ¬ rowsHold badIncNonceRow.loc incNonceKimchiRows := by
  apply tamper_moved_balance_refused
  simp only [badIncNonceRow, goodIncNonceRow, sbCol, saCol, SEL_INCREMENT_NONCE,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-- The deployed frozen-nonce row is UNSAT under the Kimchi emission. -/
theorem staleNonceIncNonceRow_kimchi_unsat :
    ¬ rowsHold staleNonceIncNonceRow.loc incNonceKimchiRows := by
  apply tamper_frozen_nonce_refused
  simp only [staleNonceIncNonceRow, goodIncNonceRow, sel.NOOP, sbCol, saCol, SEL_INCREMENT_NONCE,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-- **The Kimchi envelope is STRICTLY weaker.** A row whose pre-nonce sits at `p − 1` satisfies
`KimchiRowCanon` and NOT `IncNonceRowCanon`: the BabyBear reading needs the tick to stay in-field,
the Pallas reading does not. -/
def highNonceRow : VmRowEnv where
  loc := fun v => if v = sbCol state.NONCE then 2013265920 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem kimchi_envelope_strictly_weaker :
    KimchiRowCanon highNonceRow ∧ ¬ IncNonceRowCanon highNonceRow := by
  constructor
  · refine ⟨?_, Or.inl ?_⟩
    · intro off hoff
      have hall : ∀ v, 0 ≤ highNonceRow.loc v ∧ highNonceRow.loc v < 4294967296 := by
        intro v; simp only [highNonceRow]; split_ifs <;> norm_num
      exact ⟨hall _, hall _⟩
    · show highNonceRow.loc 0 = 0
      simp only [highNonceRow, sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.NONCE]
      norm_num
  · rintro ⟨-, -, hovf⟩
    revert hovf
    show ¬ (highNonceRow.loc (sbCol state.NONCE) + 1 < 2013265921)
    simp only [highNonceRow]
    norm_num

/-! ## §8 — THE EMITTED ARTIFACT.

The o1js consumer must not re-author anything, so it reads THIS: the sub-gate list, verbatim, with
the coefficients the lowering produced. `Gates.generic` in o1js takes exactly
`c_l·l + c_r·r + c_o·o + c_m·l·r + c_c = 0`, which is `Gen1.body`, so the TypeScript side is a
transcription loop over this array and contains no dregg semantics at all. -/

private def i2s (z : ℤ) : String := toString z

/-- One sub-gate as JSON. -/
def genJson (g : Gen1) : String :=
  "{\"l\":" ++ toString g.l ++ ",\"r\":" ++ toString g.r ++ ",\"o\":" ++ toString g.o
    ++ ",\"cl\":" ++ i2s g.cl ++ ",\"cr\":" ++ i2s g.cr ++ ",\"co\":" ++ i2s g.co
    ++ ",\"cm\":" ++ i2s g.cm ++ ",\"cc\":" ++ i2s g.cc ++ "}"

private def joinWith (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinWith sep xs

/-- The honest row's NONZERO columns, straight off `goodIncNonceRow` — so the o1js driver builds
its base assignment from the row LEAN proved satisfying, not from one a reader retyped. -/
def honestBaseNonzero : List (Nat × ℤ) :=
  ((List.range NV0).filter (fun v => goodIncNonceRow.loc v ≠ 0)).map
    (fun v => (v, goodIncNonceRow.loc v))

/-- The lowering's intermediates at the honest row, i.e. `satAssign` above `NV0`. The o1js witness
solver is an INDEPENDENT implementation (it reads only the emitted coefficients); comparing its
output against this list is what keeps it from being a third opinion. -/
def honestFresh : List (Nat × ℤ) :=
  (List.range 45).map (fun k => (NV0 + k, satAssign (NV0 + k)))

/-- A named column of the EffectVM row the emitted program reads. -/
def namedCols : List (String × Nat) :=
  [ ("selNoop", sel.NOOP)
  , ("selIncrementNonce", SEL_INCREMENT_NONCE)
  , ("sbBalanceLo", sbCol state.BALANCE_LO), ("saBalanceLo", saCol state.BALANCE_LO)
  , ("sbBalanceHi", sbCol state.BALANCE_HI), ("saBalanceHi", saCol state.BALANCE_HI)
  , ("sbNonce", sbCol state.NONCE), ("saNonce", saCol state.NONCE)
  , ("sbCapRoot", sbCol state.CAP_ROOT), ("saCapRoot", saCol state.CAP_ROOT)
  , ("sbReserved", sbCol state.RESERVED), ("saReserved", saCol state.RESERVED)
  , ("sbFieldBase", sbCol state.FIELD_BASE), ("saFieldBase", saCol state.FIELD_BASE) ]

/-- **THE ARTIFACT.** Everything the o1js side needs, and nothing it could reinterpret. -/
def emitJson : String :=
  "{\"air\":\"" ++ incNonceVmAirName ++ "-kimchi-b\""
    ++ ",\"source\":\"Dregg2.Circuit.Emit.KimchiEffectIncNonce.incNonceHeads\""
    ++ ",\"rowWidth\":" ++ toString EFFECT_VM_WIDTH
    ++ ",\"firstFreshVar\":" ++ toString NV0
    ++ ",\"subGates\":" ++ toString incNonceGens.length
    ++ ",\"kimchiRows\":" ++ toString incNonceKimchiRows.length
    ++ ",\"cols\":{"
    ++ joinWith "," (namedCols.map (fun p => "\"" ++ p.1 ++ "\":" ++ toString p.2))
    ++ "},\"honestBase\":["
    ++ joinWith "," (honestBaseNonzero.map (fun p => "[" ++ toString p.1 ++ "," ++ i2s p.2 ++ "]"))
    ++ "],\"honestFresh\":["
    ++ joinWith "," (honestFresh.map (fun p => "[" ++ toString p.1 ++ "," ++ i2s p.2 ++ "]"))
    ++ "],\"gens\":["
    ++ joinWith "," (incNonceGens.map genJson)
    ++ "]}"

/-! ## §9 — tripwires. -/

#guard incNonceHeads.length == 13
#guard incNonceGens.length == 59
#guard incNonceKimchiRows.length == 30
#guard incNonceGateBodies.length == 13
#guard NV0 == 188
-- Every variable the emitted program mentions lies inside `[0, NV0 + 45)`, which is what makes
-- `honestFresh`'s 45 entries the WHOLE intermediate vector and not a prefix of one.
#guard incNonceGens.all (fun g => g.l < 233 && g.r < 233 && g.o < 233)
#guard honestFresh.length == 45
#guard incNonceHeadsBound.length == 14

#assert_axioms heads_denote_deployed_gates
#assert_axioms incNonceRowGates_eq
#assert_axioms heads_zero_iff_intent
#assert_axioms kimchi_rows_force_heads
#assert_axioms kimchi_rows_force_bound
#assert_axioms kimchi_forces_selector
#assert_axioms selectorBindHead_denotes
#assert_axioms selectorGate_in_descriptor
#assert_axioms kimchi_forces_cellSpec
#assert_axioms babybear_forces_cellSpec
#assert_axioms two_emissions_one_def
#assert_axioms kimchi_pallas_forces_intent
#assert_axioms kimchi_pallas_forces_cellSpec
#assert_axioms incNonceKimchiRows_satisfiable
#assert_axioms tamper_moved_balance_refused
#assert_axioms tamper_frozen_nonce_refused
#assert_axioms badIncNonceRow_kimchi_unsat
#assert_axioms staleNonceIncNonceRow_kimchi_unsat
#assert_axioms kimchi_envelope_strictly_weaker
#assert_axioms incNonceKimchiRows_length
#assert_axioms incNonceRows_all_modelled

end Dregg2.Circuit.Emit.KimchiEffectIncNonce
