/-
# Dregg2.Circuit.PeepholeBaseGateScan — the peephole recogniser WIDENED to `.base (.gate : EmittedExpr)`,
the base-gate forcing algebra, and THE FIRST CERTIFIED PEEPHOLE ON A REAL DEPLOYED GATE BLOCK.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint. Every
definition below is a RECOGNISER over, or a REWRITE of, the constraint list an `EffectVmDescriptor2`
already carries; every soundness step is a machine-checked field-algebra / list-membership argument
over the emitted gate bodies. The deployed gate blocks it fires on (`BareCohortFloorRefuseDeployed`'s
`deployedRefuseGates`, `DfaRoutingEmit.dfaRoutingDesc`) are read-only imports.

## What this closes — the recogniser-vocabulary limit `PeepholeDeployedShape` named

`PeepholeDeployedShape` proved, ∀-d, that every peephole recogniser in the family (`acceptRoots`,
`andEdges`, `hasBitGate`, `hasProdGate`, `collapseSites`, `frontierKeep`, `confirmedOuts`) reads ONLY
`.windowGate w` over `WindowExpr.loc`, hence is BLIND on a `NoPlainWindowGate` list — while deployed
emits author the SAME ALGEBRA as `.base (.gate …)` over `EmittedExpr.var`. Two concrete, named,
reachable targets:

* `DfaRoutingEmit.dfaRoutingDesc` carries THREE booleanity gates of exactly `v·(v−1) = 0`
  (`isFirstBoolGate` / `stateGridGate` / `symbolGridGate`) plus a raw gate `zero_lane = 0`;
* ALL 36 deployed cohort members carry `deployedRefuseGates` — twelve genuine zeroTest clusters whose
  `isZeroDefGateT tag tagCol boolCol invC` IS the `invGate` algebra `b + (tag−T)·inv − 1 = 0` and whose
  `isZeroForceGateT` IS the `prodGate` algebra `(tag−T)·b = 0`, plus three raw gates `floorCol = 0`.

§1 gives the SECOND matcher — the same six shapes over `EmittedExpr` (`.var` where `WindowExpr` uses
`.loc`; there is no `onTransition`, and no `nxt`, so a base gate is genuinely row-local). §1b PROVES,
by `rfl`, that the deployed constructors ARE the recognised constructors: the identification is
definitional, not a resemblance claim. §2 is the base-gate forcing algebra (`ForcedB`,
`forcedB_field_one`, `forcedB_prod_zero`) — the exact mirror of `forced_field_one` / `forcedS_field_one`
with one REAL semantic difference carried explicitly (below). §3 FIRES the widened recogniser on the two
real deployed descriptors, with the counts as `#guard` and the memberships as PROVEN theorems. §4–§5
land the certified pass.

## THE ONE REAL SEMANTIC DIFFERENCE (not cosmetic — it is why the mirror is not verbatim)

`.windowGate { onTransition := false }` holds on EVERY row. `.base (.gate body)` is guarded by the
deployed `builder.when_transition()`: `VmConstraint.holdsVm` makes it `True` on the LAST row. So the
base-gate forcing algebra is conditioned on `isLast = false`, and a base-gate rewrite is sound on the
wrap row for the trivial reason that BOTH sides are vacuous there. Consequently:

* `substZeroGate` (§4) substitutes ONLY inside `.base (.gate …)` bodies. It does NOT touch
  `.boundary` / `.piBinding` bodies (they fire on the first/last row, where the forcing gate is
  vacuous) nor `.lookup` tuples nor `.windowGate` bodies (they hold on the wrap row, where the forcing
  gate does not). Substituting there WOULD be unsound and the guard is the reason.

## §4–§5 — THE DELIVERABLE: a certified pass that FIRES on the deployed cohort weld

`zeroSubstCollapse c d` is the base-gate CONSTANT-PROPAGATION peephole the widened recogniser drives:
given a raw gate `c = 0` in the list (`bZeroCols` finds them), replace `.var c` by `.const 0` in every
`.base (.gate …)` body and re-append the raw gate. `zeroSubst_preservation` proves it a genuine ∀-d
`SatisfiabilityPreservation` with the IDENTITY trace map both ways, conditioned ONLY on
`bRawGate (.var c) ∈ d.constraints` — no accept-reachability certificate, no canonicality hypothesis,
no crypto floor.

The legs split ASYMMETRICALLY, in the good direction: `zeroSubst_security` needs NO hypothesis at all
(the pin it reads is the one the fold appends, present in the target unconditionally), so the leg
soundness rests on is ∀-c ∀-d. Only `zeroSubst_completeness` consumes the source pin — i.e. a misapplied
fold can only cost an honest witness, never admit a forged one.

`deployedRefuse_zeroSubst_escrow` instantiates it at the LIVE welded cohort shape: for EVERY bare
cohort member `d`, the escrow / discharge / vault block's own `floorZeroRefuseGate` supplies the
hypothesis (`refuse_mem_block` + `block_mem_deployed`, already in the tree), so the pass is CERTIFIED on
`gentianDeployedBareRefuse d`. That is a certified peephole on a real deployed descriptor — the first
one — and it is ∀-member, not one instance.

⚠ HONEST SCOPE, stated at the resolution it holds at:

* This is a REWRITE, not a size reduction. `zeroSubstCollapse` emits `|cs| + 1` constraints: it
  constant-folds real deployed gate bodies (`substChanged` counts them) and the size win would come
  from a downstream trivial-gate drop / degree pass, which is NOT done here. Do not read it as "the
  deployed circuit got smaller".
* The base-gate FRONTIER collapse (drop {bit, product, inverse}, append the raw affine gate) is built
  in §6 over `ForcedB` — and it does NOT fire on either deployed descriptor examined, because neither
  carries a `.base (.gate (out − 1))` ACCEPT gate: the refuse block's floor column is forced to ZERO
  (`floorZeroRefuseGate`), not to one, and its bits are pinned by the is-zero gadget's canonicality
  argument rather than by field-only booleanity. §6 is therefore machinery + a synthetic certified
  instance, NOT a deployed firing; §4–§5 is the deployed firing. Both are labelled as such.
* THE INVERSION LEG, NAMED PRECISELY. §5 needs no emitter inversion because `refuse_mem_block` /
  `block_mem_deployed` already ARE the membership inversion for `blockGates`. A base-gate frontier
  collapse on the refuse block would additionally need: (i) `orFoldGate`-shape forcing, i.e. that
  `fc = 0` plus `fc − (o + b − o·b) = 0` forces `o = 0 ∧ b = 0` — FALSE over the bare field (o = b = 2
  satisfies it) and TRUE only under the canonicality hypothesis `hcanon` the existing keystones carry;
  and (ii) an accept-side anchor, which the block does not have. That is the wall, and it is a
  SEMANTIC wall in the deployed block's own arithmetic, not a missing inversion lemma.
* Everything inherits the undischarged FRI/STARK floor: this is refinement between two constraint
  systems, not a claim about the deployed prover.

Standalone and additive: imports `PeepholeDeployedShape` and `BareCohortFloorRefuseDeployed` plus the
DFA-routing emit read-only; changes none of them. No existing `WindowExpr` recogniser is touched — the
base-gate path is a SECOND matcher alongside.
-/
import Dregg2.Circuit.PeepholeDeployedShape
import Dregg2.Deos.BareCohortFloorRefuseDeployed

namespace Dregg2.Circuit.PeepholeBaseGateScan

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (BabyBear fieldAssignment)

set_option autoImplicit false

/-! ## §0. The base-gate carrier: `EmittedExpr` in the field, and the gate reading.

`fieldBase` is the `EmittedExpr` twin of `DirectLogicBoolGraphDescriptorIR2.fieldWindow` (which reads
`WindowExpr`). Both are the honest field denotation: the integer `eval` cast into `BabyBear`, so a gate
congruence `body.eval ≡ 0 [ZMOD p]` becomes a field equation and the algebra is available. -/

/-- A base gate: the deployed `.base (.gate body)` — a row-local `assert_zero` over the CURRENT row,
guarded by `when_transition()` (vacuous on the wrap row). -/
def bGate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)

/-- The field value of an emitted expression on a row. -/
noncomputable def fieldBase (a : Assignment) : EmittedExpr → BabyBear
  | .var c   => fieldAssignment a c
  | .const k => (k : BabyBear)
  | .add x y => fieldBase a x + fieldBase a y
  | .mul x y => fieldBase a x * fieldBase a y

theorem fieldBase_eq_cast (a : Assignment) (e : EmittedExpr) :
    fieldBase a e = (e.eval a : BabyBear) := by
  induction e <;> simp [fieldBase, EmittedExpr.eval, fieldAssignment, *]

/-- A base gate on a TRANSITION row (`isLast = false`) forces its body to vanish in the field. -/
theorem field_of_base_gate {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    {body : EmittedExpr} (h : (bGate body).holdsAt hash tf env f false) :
    fieldBase env.loc body = 0 := by
  simp only [bGate, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  rw [fieldBase_eq_cast]
  exact (ZMod.intCast_eq_intCast_iff (body.eval env.loc) 0 2013265921).2 h

/-- Conversely a field-vanishing body makes the gate hold on ANY row (on the wrap row it is vacuous). -/
theorem bGate_holds_of_field_zero {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f l : Bool}
    {body : EmittedExpr} (h : fieldBase env.loc body = 0) :
    (bGate body).holdsAt hash tf env f l := by
  cases l with
  | true => exact trivial
  | false =>
      show body.eval env.loc ≡ 0 [ZMOD 2013265921]
      rw [fieldBase_eq_cast] at h
      exact (ZMod.intCast_eq_intCast_iff (body.eval env.loc) 0 2013265921).1 (by simpa using h)

/-! ### The six recognised base-gate SHAPES, as named constructors.

The exact mirrors of `PeepholeFrontierScan`'s `acceptGate` / `andGate` / `bitGate` / `prodGate` /
`invGate` / `rawGate`, with two deliberate generalisations forced by the deployed shapes:

* the ZERO-TESTED object is an arbitrary `EmittedExpr e`, not a bare column — the deployed is-zero
  gadget tests the residual `tagCol − T`, not a column;
* the inverse gate's summand ORDER is the deployed one (`out + e·inv − 1`, not `e·inv + out − 1`). -/

/-- `out − 1 = 0` — the accept gate, forcing `out = 1`. -/
def bAcceptGate (c : Nat) : VmConstraint2 := bGate (.add (.var c) (.const (-1)))

/-- `out − l·r = 0` — an and-node gate with column children. -/
def bAndGate (out l r : Nat) : VmConstraint2 :=
  bGate (.add (.var out) (.mul (.const (-1)) (.mul (.var l) (.var r))))

/-- `c·(c−1) = 0` — the booleanity gate. THE deployed shape of `dfaRoutingDesc`'s three grid gates. -/
def bBitGate (c : Nat) : VmConstraint2 := bGate (.mul (.var c) (.add (.var c) (.const (-1))))

/-- `e·out = 0` — a zero-test's product (force) gate on the residual `e`. THE deployed
`isZeroForceGateT`. -/
def bProdGate (e : EmittedExpr) (out : Nat) : VmConstraint2 := bGate (.mul e (.var out))

/-- `out + e·inv − 1 = 0` — a zero-test's inverse (def) gate on the residual `e`. THE deployed
`isZeroDefGateT`. -/
def bInvGate (e : EmittedExpr) (out inv : Nat) : VmConstraint2 :=
  bGate (.add (.add (.var out) (.mul e (.var inv))) (.const (-1)))

/-- `e = 0` — a raw gate. THE deployed `floorZeroRefuseGate` (at `e = .var floorCol`) and
`dfaRoutingDesc`'s `zeroLaneGate`. -/
def bRawGate (e : EmittedExpr) : VmConstraint2 := bGate e

/-! ### The field readings of the six bodies (the algebra the forcing core runs on). -/

theorem fb_accept (env : VmRowEnv) (c : Nat) :
    fieldBase env.loc (.add (.var c) (.const (-1))) = fieldAssignment env.loc c - 1 := by
  simp only [fieldBase]; push_cast; ring

theorem fb_and (env : VmRowEnv) (out l r : Nat) :
    fieldBase env.loc (.add (.var out) (.mul (.const (-1)) (.mul (.var l) (.var r))))
      = fieldAssignment env.loc out - fieldAssignment env.loc l * fieldAssignment env.loc r := by
  simp only [fieldBase]; push_cast; ring

theorem fb_bit (env : VmRowEnv) (c : Nat) :
    fieldBase env.loc (.mul (.var c) (.add (.var c) (.const (-1))))
      = fieldAssignment env.loc c * (fieldAssignment env.loc c - 1) := by
  simp only [fieldBase]; push_cast; ring

theorem fb_prod (env : VmRowEnv) (e : EmittedExpr) (out : Nat) :
    fieldBase env.loc (.mul e (.var out)) = fieldBase env.loc e * fieldAssignment env.loc out := by
  simp only [fieldBase]

theorem fb_inv (env : VmRowEnv) (e : EmittedExpr) (out inv : Nat) :
    fieldBase env.loc (.add (.add (.var out) (.mul e (.var inv))) (.const (-1)))
      = fieldAssignment env.loc out + fieldBase env.loc e * fieldAssignment env.loc inv - 1 := by
  simp only [fieldBase]; push_cast; ring

/-! ## §1. THE SECOND MATCHER — the same shapes read off `.base (.gate : EmittedExpr)`.

Every recogniser here is the `EmittedExpr` twin of a committed `WindowExpr` recogniser, and returns
`none`/`false` on EVERY other constraint constructor (including `.windowGate`), so the two matchers are
strictly complementary: neither can see the other's gates, and adding this one changes no existing
result. -/

/-- Columns carrying an accept gate `c − 1 = 0`, read by shape. -/
def bAcceptRoots (cs : List VmConstraint2) : List Nat :=
  cs.filterMap fun c => match c with
    | .base (.gate (.add (.var c') (.const k))) => if k == (-1 : Int) then some c' else none
    | _ => none

/-- And-node edges `(out, l, r)` for `out − l·r = 0`, read by shape. -/
def bAndEdges (cs : List VmConstraint2) : List (Nat × Nat × Nat) :=
  cs.filterMap fun c => match c with
    | .base (.gate (.add (.var out) (.mul (.const k) (.mul (.var l) (.var r))))) =>
        if k == (-1 : Int) then some (out, l, r) else none
    | _ => none

/-- The list carries a booleanity gate for column `c`. -/
def bHasBitGate (cs : List VmConstraint2) (c : Nat) : Bool :=
  cs.any fun d => match d with
    | .base (.gate (.mul (.var a) (.add (.var b) (.const k)))) =>
        a == c && b == c && k == (-1 : Int)
    | _ => false

/-- The columns a booleanity gate is carried for, in order. -/
def bBitGateCols (cs : List VmConstraint2) : List Nat :=
  cs.filterMap fun c => match c with
    | .base (.gate (.mul (.var a) (.add (.var b) (.const k)))) =>
        if a == b && k == (-1 : Int) then some a else none
    | _ => none

/-- Is this constraint exactly the product gate `e·out = 0`? -/
def isBProdGate (e : EmittedExpr) (out : Nat) : VmConstraint2 → Bool
  | .base (.gate (.mul e' (.var o))) => e' == e && o == out
  | _ => false

/-- The list carries the product gate `e·out = 0`. -/
def bHasProdGate (cs : List VmConstraint2) (e : EmittedExpr) (out : Nat) : Bool :=
  cs.any (isBProdGate e out)

/-- CONFIRMED base-gate zero-test clusters `(e, out, inv)`: an inverse gate whose matching product gate
is present in the same list. The residual `e` is read off the shape, exactly as the window recogniser
reads the tested column. -/
def bZeroTestSites (cs : List VmConstraint2) : List (EmittedExpr × Nat × Nat) :=
  cs.filterMap fun c => match c with
    | .base (.gate (.add (.add (.var out) (.mul e (.var inv))) (.const k))) =>
        if k == (-1 : Int) && bHasProdGate cs e out then some (e, out, inv) else none
    | _ => none

/-- Columns pinned to zero by a raw gate `c = 0` — the recogniser that drives §4. -/
def bZeroCols (cs : List VmConstraint2) : List Nat :=
  cs.filterMap fun c => match c with
    | .base (.gate (.var c')) => some c'
    | _ => none

/-! ### Recogniser INVERSIONS — a recognised shape really IS in the list. No `decide` on a descriptor. -/

theorem isBProdGate_eq {e : EmittedExpr} {out : Nat} {c : VmConstraint2}
    (h : isBProdGate e out c = true) : c = bProdGate e out := by
  cases c with
  | base bc =>
    cases bc with
    | gate body =>
        cases body with
        | mul l r =>
            cases r with
            | var o =>
                simp only [isBProdGate, Bool.and_eq_true, beq_iff_eq] at h
                obtain ⟨he, ho⟩ := h
                subst he; subst ho; rfl
            | _ => exact absurd h (by simp [isBProdGate])
        | _ => exact absurd h (by simp [isBProdGate])
    | _ => exact absurd h (by simp [isBProdGate])
  | _ => exact absurd h (by simp [isBProdGate])

theorem bProdGate_mem_of_hasProdGate {cs : List VmConstraint2} {e : EmittedExpr} {out : Nat}
    (h : bHasProdGate cs e out = true) : bProdGate e out ∈ cs := by
  obtain ⟨c, hc, hp⟩ := List.any_eq_true.1 h
  rw [isBProdGate_eq hp] at hc
  exact hc

theorem bAcceptGate_of_mem_bAcceptRoots {cs : List VmConstraint2} {c : Nat}
    (h : c ∈ bAcceptRoots cs) : bAcceptGate c ∈ cs := by
  obtain ⟨d, hd, hmatch⟩ := List.mem_filterMap.1 h
  cases d with
  | base bc =>
    cases bc with
    | gate body =>
        cases body with
        | add x y =>
            cases x with
            | var c' =>
                cases y with
                | const k =>
                    simp only at hmatch
                    split at hmatch
                    · rename_i hk
                      rw [Option.some.injEq] at hmatch
                      subst hmatch
                      simp only [beq_iff_eq] at hk
                      subst hk
                      exact hd
                    · exact absurd hmatch (by simp)
                | _ => exact absurd hmatch (by simp)
            | _ => exact absurd hmatch (by simp)
        | _ => exact absurd hmatch (by simp)
    | _ => exact absurd hmatch (by simp)
  | _ => exact absurd hmatch (by simp)

theorem bAndGate_of_mem_bAndEdges {cs : List VmConstraint2} {out l r : Nat}
    (h : (out, l, r) ∈ bAndEdges cs) : bAndGate out l r ∈ cs := by
  obtain ⟨d, hd, hmatch⟩ := List.mem_filterMap.1 h
  cases d with
  | base bc =>
    cases bc with
    | gate body =>
        cases body with
        | add x y =>
            cases x with
            | var o =>
                cases y with
                | mul kk p =>
                    cases kk with
                    | const k =>
                        cases p with
                        | mul pl pr =>
                            cases pl with
                            | var l' =>
                                cases pr with
                                | var r' =>
                                    simp only at hmatch
                                    split at hmatch
                                    · rename_i hk
                                      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hmatch
                                      obtain ⟨ho, hl, hr⟩ := hmatch
                                      subst ho; subst hl; subst hr
                                      simp only [beq_iff_eq] at hk
                                      subst hk
                                      exact hd
                                    · exact absurd hmatch (by simp)
                                | _ => exact absurd hmatch (by simp)
                            | _ => exact absurd hmatch (by simp)
                        | _ => exact absurd hmatch (by simp)
                    | _ => exact absurd hmatch (by simp)
                | _ => exact absurd hmatch (by simp)
            | _ => exact absurd hmatch (by simp)
        | _ => exact absurd hmatch (by simp)
    | _ => exact absurd hmatch (by simp)
  | _ => exact absurd hmatch (by simp)

theorem bBitGate_of_hasBitGate {cs : List VmConstraint2} {c : Nat}
    (h : bHasBitGate cs c = true) : bBitGate c ∈ cs := by
  obtain ⟨d, hd, hp⟩ := List.any_eq_true.1 h
  cases d with
  | base bc =>
    cases bc with
    | gate body =>
        cases body with
        | mul x y =>
            cases x with
            | var a =>
                cases y with
                | add yl yr =>
                    cases yl with
                    | var b =>
                        cases yr with
                        | const k =>
                            simp only [Bool.and_eq_true, beq_iff_eq] at hp
                            obtain ⟨⟨ha, hb⟩, hk⟩ := hp
                            subst ha; subst hb; subst hk
                            exact hd
                        | _ => exact absurd hp (by simp)
                    | _ => exact absurd hp (by simp)
                | _ => exact absurd hp (by simp)
            | _ => exact absurd hp (by simp)
        | _ => exact absurd hp (by simp)
    | _ => exact absurd hp (by simp)
  | _ => exact absurd hp (by simp)

theorem bZeroCol_rawGate_mem {cs : List VmConstraint2} {c : Nat} (h : c ∈ bZeroCols cs) :
    bRawGate (.var c) ∈ cs := by
  obtain ⟨d, hd, hmatch⟩ := List.mem_filterMap.1 h
  cases d with
  | base bc =>
    cases bc with
    | gate body =>
        cases body with
        | var c' =>
            simp only [Option.some.injEq] at hmatch
            subst hmatch
            exact hd
        | _ => exact absurd hmatch (by simp)
    | _ => exact absurd hmatch (by simp)
  | _ => exact absurd hmatch (by simp)

/-! ## §1b. THE IDENTIFICATION — the deployed constructors ARE the recognised constructors.

Every one of these is `rfl`. This is what makes §3's firing a fact about DEPLOYED gates rather than a
resemblance argument: the widened recogniser's vocabulary is definitionally the deployed vocabulary. -/

section Identification

open Dregg2.Deos.BareCohortFloorRefuse (isZeroDefGateT isZeroForceGateT floorZeroRefuseGate)
open Dregg2.Circuit.Emit.DfaRoutingEmit
  (isFirstBoolGate stateGridGate symbolGridGate zeroLaneGate IS_FIRST CURRENT SYMBOL ZERO_LANE)

/-- ⚑ The deployed is-zero FORCING gate IS the recognised product gate on the residual `tagCol − T`. -/
theorem isZeroForceGateT_is_bProdGate (tag : ℤ) (tagCol boolCol : Nat) :
    isZeroForceGateT tag tagCol boolCol
      = bProdGate (.add (.var tagCol) (.const (-tag))) boolCol := rfl

/-- ⚑ The deployed is-zero DEFINING gate IS the recognised inverse gate on the same residual. -/
theorem isZeroDefGateT_is_bInvGate (tag : ℤ) (tagCol boolCol invC : Nat) :
    isZeroDefGateT tag tagCol boolCol invC
      = bInvGate (.add (.var tagCol) (.const (-tag))) boolCol invC := rfl

/-- ⚑ The deployed floor-refuse gate IS the recognised raw gate. -/
theorem floorZeroRefuseGate_is_bRawGate (fc : Nat) :
    floorZeroRefuseGate fc = bRawGate (.var fc) := rfl

/-- ⚑ `dfaRoutingDesc`'s three booleanity gates ARE recognised bit gates. -/
theorem isFirstBoolGate_is_bBitGate : isFirstBoolGate = bBitGate IS_FIRST := rfl
theorem stateGridGate_is_bBitGate : stateGridGate = bBitGate CURRENT := rfl
theorem symbolGridGate_is_bBitGate : symbolGridGate = bBitGate SYMBOL := rfl

/-- ⚑ …and its zero-lane pin IS a recognised raw gate. -/
theorem zeroLaneGate_is_bRawGate : zeroLaneGate = bRawGate (.var ZERO_LANE) := rfl

end Identification

/-! ## §2. THE BASE-GATE FORCING ALGEBRA — the mirror of `Forced` / `ForcedS`.

`ForcedB cs c` : column `c` is forced to the field value 1 by an accept gate, transitively through
and-nodes, using EITHER a sibling's OR the child's OWN booleanity gate (the `ForcedS` strengthening,
adopted directly — the sibling-only `Forced` was already known too weak). Every premise is a gate
MEMBERSHIP: this is a syntactic certificate, no source program.

The field algebra is IDENTICAL to the window version. What changes is the hypothesis: the gates hold on
a TRANSITION row (`isLast = false`), because that is where a deployed `.base (.gate …)` binds. -/

inductive ForcedB (cs : List VmConstraint2) : Nat → Prop where
  | accept (c : Nat) (h : bAcceptGate c ∈ cs) : ForcedB cs c
  /-- force the LEFT child via the RIGHT sibling's bit gate. -/
  | andLsib (out l r : Nat) (hpar : ForcedB cs out)
      (hg : bAndGate out l r ∈ cs) (hrb : bBitGate r ∈ cs) : ForcedB cs l
  /-- force the RIGHT child via the LEFT sibling's bit gate. -/
  | andRsib (out l r : Nat) (hpar : ForcedB cs out)
      (hg : bAndGate out l r ∈ cs) (hlb : bBitGate l ∈ cs) : ForcedB cs r
  /-- force the LEFT child via its OWN bit gate. -/
  | andLself (out l r : Nat) (hpar : ForcedB cs out)
      (hg : bAndGate out l r ∈ cs) (hlb : bBitGate l ∈ cs) : ForcedB cs l
  /-- force the RIGHT child via its OWN bit gate. -/
  | andRself (out l r : Nat) (hpar : ForcedB cs out)
      (hg : bAndGate out l r ∈ cs) (hrb : bBitGate r ∈ cs) : ForcedB cs r

/-- THE BASE-GATE SOUNDNESS CORE. On a TRANSITION row on which every gate in `cs` holds, a `ForcedB`
column carries field value 1. Pure field algebra over the emitted base-gate bodies. -/
theorem forcedB_field_one {cs : List VmConstraint2} {c : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f false)
    (cert : ForcedB cs c) :
    fieldAssignment env.loc c = 1 := by
  induction cert with
  | accept c h =>
      have hz := field_of_base_gate (hall _ h)
      rw [fb_accept] at hz
      simpa using sub_eq_zero.mp hz
  | andLsib out l r hpar hg hrb ihpar =>
      have hgz := field_of_base_gate (hall _ hg)
      have hbz := field_of_base_gate (hall _ hrb)
      rw [fb_and] at hgz
      rw [fb_bit] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hr0 | hr1
      · rw [hr0, mul_zero] at hlr; exact absurd hlr (by norm_num)
      · have hr : fieldAssignment env.loc r = 1 := sub_eq_zero.mp hr1
        rw [hr, mul_one] at hlr; exact hlr
  | andRsib out l r hpar hg hlb ihpar =>
      have hgz := field_of_base_gate (hall _ hg)
      have hbz := field_of_base_gate (hall _ hlb)
      rw [fb_and] at hgz
      rw [fb_bit] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hl0 | hl1
      · rw [hl0, zero_mul] at hlr; exact absurd hlr (by norm_num)
      · have hl : fieldAssignment env.loc l = 1 := sub_eq_zero.mp hl1
        rw [hl, one_mul] at hlr; exact hlr
  | andLself out l r hpar hg hlb ihpar =>
      have hgz := field_of_base_gate (hall _ hg)
      have hbz := field_of_base_gate (hall _ hlb)
      rw [fb_and] at hgz
      rw [fb_bit] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hl0 | hl1
      · rw [hl0, zero_mul] at hlr; exact absurd hlr (by norm_num)
      · exact sub_eq_zero.mp hl1
  | andRself out l r hpar hg hrb ihpar =>
      have hgz := field_of_base_gate (hall _ hg)
      have hbz := field_of_base_gate (hall _ hrb)
      rw [fb_and] at hgz
      rw [fb_bit] at hbz
      rw [ihpar] at hgz
      have hlr : fieldAssignment env.loc l * fieldAssignment env.loc r = 1 :=
        (sub_eq_zero.mp hgz).symm
      rcases mul_eq_zero.mp hbz with hr0 | hr1
      · rw [hr0, mul_zero] at hlr; exact absurd hlr (by norm_num)
      · exact sub_eq_zero.mp hr1

/-- `ForcedB` is monotone in its constraint list. -/
theorem ForcedB.mono {cs cs' : List VmConstraint2} (hsub : cs ⊆ cs') {c : Nat}
    (cert : ForcedB cs c) : ForcedB cs' c := by
  induction cert with
  | accept c h => exact .accept c (hsub h)
  | andLsib out l r hpar hg hrb ih => exact .andLsib out l r ih (hsub hg) (hsub hrb)
  | andRsib out l r hpar hg hlb ih => exact .andRsib out l r ih (hsub hg) (hsub hlb)
  | andLself out l r hpar hg hlb ih => exact .andLself out l r ih (hsub hg) (hsub hlb)
  | andRself out l r hpar hg hrb ih => exact .andRself out l r ih (hsub hg) (hsub hrb)

/-- ⚑ THE ZERO-TEST FORCING STEP: a product gate `e·out = 0` whose bit `out` is forced to 1 forces the
tested RESIDUAL `e` to vanish. This is the base-gate twin of the window collapse's central step, and it
holds for an arbitrary residual expression `e` — which is what the deployed is-zero gadget needs. -/
theorem forcedB_prod_zero {cs : List VmConstraint2} {e : EmittedExpr} {out : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f false)
    (hprod : bProdGate e out ∈ cs) (cert : ForcedB cs out) :
    fieldBase env.loc e = 0 := by
  have hone : fieldAssignment env.loc out = 1 := forcedB_field_one hall cert
  have hz := field_of_base_gate (hall _ hprod)
  rw [fb_prod, hone, mul_one] at hz
  exact hz

/-- ⚑ THE BOOLEANITY REDUNDANCY, base-gate form: a zero-test cluster's `{product, inverse}` pair ALREADY
forces its bit to be boolean, so a co-located bit gate on that bit is redundant. Pure field algebra, no
forcing certificate and no canonicality hypothesis — `e·out = 0` and `out + e·inv = 1` give
`out² − out = out·(out + e·inv) − out = out·e·inv = inv·(e·out) = 0`. -/
theorem bBit_of_prod_inv {e : EmittedExpr} {out inv : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    (hprod : (bProdGate e out).holdsAt hash tf env f false)
    (hinv : (bInvGate e out inv).holdsAt hash tf env f false) :
    fieldAssignment env.loc out * (fieldAssignment env.loc out - 1) = 0 := by
  have hp := field_of_base_gate hprod
  have hi := field_of_base_gate hinv
  rw [fb_prod] at hp
  rw [fb_inv] at hi
  have hi' : fieldAssignment env.loc out
      = 1 - fieldBase env.loc e * fieldAssignment env.loc inv := by linear_combination hi
  rw [hi']
  have : fieldBase env.loc e * fieldAssignment env.loc out = 0 := hp
  rw [hi'] at this
  linear_combination (-(fieldAssignment env.loc inv)) * this

/-! ## §3. ⚑ FIRING THE WIDENED RECOGNISER ON REAL DEPLOYED DESCRIPTORS.

Two deployed objects, both read-only imports. The counts are `#guard` (compiled evaluation — these
prove NO Prop); the MEMBERSHIPS are proven theorems, which is what carries content. The contrast with
the committed `WindowExpr` recognisers is exhibited on the same lists: they see NOTHING there, which is
exactly `PeepholeDeployedShape`'s finding, now with the other side supplied. -/

section Firing

open Dregg2.Circuit.Emit.DfaRoutingEmit
  (dfaRoutingDesc isFirstBoolGate stateGridGate symbolGridGate zeroLaneGate
   IS_FIRST CURRENT SYMBOL ZERO_LANE)
open Dregg2.Deos.BareCohortFloorRefuse (isZeroDefGateT isZeroForceGateT floorZeroRefuseGate)
open Dregg2.Deos.BareCohortFloorRefuseDeployed
  (deployedRefuseGates blockGates decodeGatesAt refuseGatesAt gentianDeployedBareRefuse
   ebDep bcDep icDep ocDep fcDep GRAD_ROT_WIDTH decode_mem_block refuse_mem_block block_mem_deployed)
open Dregg2.Deos.ConstraintBinding (tagSettleEscrow tagDischargeObligation tagVaultDeposit)
open Dregg2.Circuit.PeepholeFrontierScan (collapseSites hasBitGate)

/-! ### DFA ROUTING — the three booleanity gates and the zero-lane pin, SEEN. -/

-- The widened recogniser finds all three deployed booleanity gates, at their real columns.
#guard bBitGateCols dfaRoutingDesc.constraints == [IS_FIRST, CURRENT, SYMBOL]
#guard (bBitGateCols dfaRoutingDesc.constraints).length == 3
#guard bHasBitGate dfaRoutingDesc.constraints CURRENT
#guard bHasBitGate dfaRoutingDesc.constraints SYMBOL
#guard bHasBitGate dfaRoutingDesc.constraints IS_FIRST
-- …and the raw gate `zero_lane = 0`.
#guard bZeroCols dfaRoutingDesc.constraints == [ZERO_LANE]

-- THE CONTRAST: the committed `WindowExpr` recogniser is blind on exactly the same list.
#guard hasBitGate dfaRoutingDesc.constraints CURRENT == false
#guard (collapseSites dfaRoutingDesc.constraints).length == 0

/-- PROVEN (not a `#guard`): the DFA-routing state-grid gate is a recognised bit gate IN the deployed
descriptor's constraint list. -/
theorem dfa_state_bBitGate_mem : bBitGate CURRENT ∈ dfaRoutingDesc.constraints := by
  show stateGridGate ∈ _
  simp [dfaRoutingDesc]

theorem dfa_symbol_bBitGate_mem : bBitGate SYMBOL ∈ dfaRoutingDesc.constraints := by
  show symbolGridGate ∈ _
  simp [dfaRoutingDesc]

theorem dfa_isFirst_bBitGate_mem : bBitGate IS_FIRST ∈ dfaRoutingDesc.constraints := by
  show isFirstBoolGate ∈ _
  simp [dfaRoutingDesc]

theorem dfa_zeroLane_bRawGate_mem : bRawGate (.var ZERO_LANE) ∈ dfaRoutingDesc.constraints := by
  show zeroLaneGate ∈ _
  simp [dfaRoutingDesc]

/-! ### THE DEPLOYED COHORT WELD — twelve zero-test clusters and three raw gates, SEEN. -/

-- The three-block deployed refuse weld: 12 confirmed zero-test clusters (4 slots × 3 capacity tags),
-- each recognised BY ITS CLUSTER (the inverse gate confirmed by its matching product gate).
#guard (bZeroTestSites (deployedRefuseGates GRAD_ROT_WIDTH)).length == 12
-- The three floor-refuse raw gates, at the real deployed floor columns.
#guard bZeroCols (deployedRefuseGates GRAD_ROT_WIDTH)
  == [fcDep GRAD_ROT_WIDTH 0, fcDep GRAD_ROT_WIDTH 1, fcDep GRAD_ROT_WIDTH 2]
#guard bZeroCols (deployedRefuseGates GRAD_ROT_WIDTH) == [1703, 1719, 1735]
-- The whole weld is 39 gates; the recogniser accounts for 12 + 12 + 3 of them by shape.
#guard (deployedRefuseGates GRAD_ROT_WIDTH).length == 39

-- THE CONTRAST: the committed recognisers see nothing in the deployed weld.
#guard (collapseSites (deployedRefuseGates GRAD_ROT_WIDTH)).length == 0
#guard (bZeroTestSites (deployedRefuseGates GRAD_ROT_WIDTH)).length != 0

/-- PROVEN: the deployed escrow block's slot-0 cluster is a recognised `{product, inverse}` zero-test
pair, at the real deployed caveat tag column and aux columns, inside `blockGates`. -/
theorem deployed_prod_mem (auxBase : Nat) (tag : ℤ) (b : Nat) :
    bProdGate (.add (.var (ebDep 0)) (.const (-tag))) (bcDep auxBase b 0)
      ∈ blockGates auxBase tag b :=
  decode_mem_block auxBase tag b (isZeroForceGateT tag (ebDep 0) (bcDep auxBase b 0))
    (by simp [decodeGatesAt])

theorem deployed_inv_mem (auxBase : Nat) (tag : ℤ) (b : Nat) :
    bInvGate (.add (.var (ebDep 0)) (.const (-tag))) (bcDep auxBase b 0) (icDep auxBase b 0)
      ∈ blockGates auxBase tag b :=
  decode_mem_block auxBase tag b
    (isZeroDefGateT tag (ebDep 0) (bcDep auxBase b 0) (icDep auxBase b 0))
    (by simp [decodeGatesAt])

/-- PROVEN: the deployed block's floor-refuse gate is a recognised RAW gate. -/
theorem deployed_raw_mem (auxBase : Nat) (tag : ℤ) (b : Nat) :
    bRawGate (.var (fcDep auxBase b)) ∈ blockGates auxBase tag b :=
  refuse_mem_block auxBase tag b

/-- ⚑ PROVEN AT THE LIVE WELDED MEMBER: for EVERY bare cohort member `d`, the escrow block's raw gate is
a recognised raw gate in `(gentianDeployedBareRefuse d).constraints`. This is the hypothesis §5's
certified pass consumes — supplied by the deployed weld itself. -/
theorem deployedRefuse_raw_mem_escrow (d : EffectVmDescriptor2) :
    bRawGate (.var (fcDep d.traceWidth 0)) ∈ (gentianDeployedBareRefuse d).constraints :=
  block_mem_deployed d _ (Or.inl (deployed_raw_mem d.traceWidth (tagSettleEscrow : ℤ) 0))

theorem deployedRefuse_raw_mem_discharge (d : EffectVmDescriptor2) :
    bRawGate (.var (fcDep d.traceWidth 1)) ∈ (gentianDeployedBareRefuse d).constraints :=
  block_mem_deployed d _
    (Or.inr (Or.inl (deployed_raw_mem d.traceWidth (tagDischargeObligation : ℤ) 1)))

theorem deployedRefuse_raw_mem_vault (d : EffectVmDescriptor2) :
    bRawGate (.var (fcDep d.traceWidth 2)) ∈ (gentianDeployedBareRefuse d).constraints :=
  block_mem_deployed d _
    (Or.inr (Or.inr (deployed_raw_mem d.traceWidth (tagVaultDeposit : ℤ) 2)))

end Firing

/-! ## §4. THE CERTIFIED BASE-GATE PASS — constant propagation off a recognised raw gate.

The rewrite the `bZeroCols` recogniser drives: with `c = 0` pinned by a raw gate, `.var c` may be
folded to `.const 0` inside every OTHER base-gate body. The raw gate is re-appended so the pin survives
in the target (it is the only thing the reverse leg has to work with).

⚠ The substitution is scoped to `.base (.gate …)` bodies and NOTHING else, for a semantic reason stated
in the header: `.boundary`/`.piBinding` fire on the first/last row and `.lookup`/`.windowGate` fire on
the wrap row, where the forcing base gate is VACUOUS. `substZeroGate` is the identity there. -/

/-- Fold `.var c` to `.const 0` in an emitted expression. -/
def substZero (c : Nat) : EmittedExpr → EmittedExpr
  | .var v   => if v == c then .const 0 else .var v
  | .const k => .const k
  | .add x y => .add (substZero c x) (substZero c y)
  | .mul x y => .mul (substZero c x) (substZero c y)

/-- Fold inside `.base (.gate …)` bodies ONLY; every other constraint kind is returned verbatim. -/
def substZeroGate (c : Nat) : VmConstraint2 → VmConstraint2
  | .base (.gate body)         => .base (.gate (substZero c body))
  | .base (.transition hi lo)  => .base (.transition hi lo)
  | .base (.boundary r b)      => .base (.boundary r b)
  | .base (.piBinding r cl k)  => .base (.piBinding r cl k)
  | .lookup l                  => .lookup l
  | .memOp m                   => .memOp m
  | .mapOp m                   => .mapOp m
  | .umemOp m                  => .umemOp m
  | .proofBind m               => .proofBind m
  | .windowGate w              => .windowGate w

/-- THE PASS's target descriptor: a record update of the constraint list alone. -/
def zeroSubstCollapse (c : Nat) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints.map (substZeroGate c) ++ [bRawGate (.var c)] }

/-- Under a zero pin, folding does not change the field value. -/
theorem substZero_field (c : Nat) (a : Assignment) (h : fieldAssignment a c = 0) :
    ∀ e : EmittedExpr, fieldBase a (substZero c e) = fieldBase a e
  | .var v => by
      simp only [substZero]
      split
      · rename_i hv
        simp only [beq_iff_eq] at hv
        subst hv
        simp only [fieldBase, h]
        push_cast
        ring
      · rfl
  | .const _ => rfl
  | .add x y => by simp only [substZero, fieldBase, substZero_field c a h x, substZero_field c a h y]
  | .mul x y => by simp only [substZero, fieldBase, substZero_field c a h x, substZero_field c a h y]

/-! ### Carrier bookkeeping — the fold touches only base-GATE bodies. -/

/-- Any `filterMap` recogniser that is `none` on every base GATE is invariant under the fold. -/
theorem filterMap_map_substZeroGate {β : Type} (f : VmConstraint2 → Option β)
    (hb : ∀ b, f (.base (.gate b)) = none) (c : Nat) (cs : List VmConstraint2) :
    (cs.map (substZeroGate c)).filterMap f = cs.filterMap f := by
  induction cs with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.filterMap_cons, List.filterMap_cons]
      cases a with
      | base bc =>
          cases bc with
          | gate b => simp only [substZeroGate, hb, ih]
          | transition hi lo => simp only [substZeroGate, ih]
          | boundary r bb => simp only [substZeroGate, ih]
          | piBinding r cl k => simp only [substZeroGate, ih]
      | lookup l => simp only [substZeroGate, ih]
      | memOp m => simp only [substZeroGate, ih]
      | mapOp m => simp only [substZeroGate, ih]
      | umemOp m => simp only [substZeroGate, ih]
      | proofBind m => simp only [substZeroGate, ih]
      | windowGate w => simp only [substZeroGate, ih]

theorem filterMap_zeroSubst {β : Type} (f : VmConstraint2 → Option β)
    (hb : ∀ b, f (.base (.gate b)) = none) (c : Nat) (d : EffectVmDescriptor2) :
    (zeroSubstCollapse c d).constraints.filterMap f = d.constraints.filterMap f := by
  show ((d.constraints.map (substZeroGate c)) ++ [bRawGate (.var c)]).filterMap f = _
  rw [List.filterMap_append, filterMap_map_substZeroGate f hb c d.constraints]
  simp only [bRawGate, bGate, List.filterMap_cons, hb, List.filterMap_nil, List.append_nil]

theorem memOps_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    memOpsOf (zeroSubstCollapse c d) = memOpsOf d :=
  filterMap_zeroSubst _ (fun _ => rfl) c d

theorem mapOps_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    mapOpsOf (zeroSubstCollapse c d) = mapOpsOf d :=
  filterMap_zeroSubst _ (fun _ => rfl) c d

theorem bindingSlots_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    publicBindingSlots (zeroSubstCollapse c d) = publicBindingSlots d :=
  filterMap_zeroSubst bindingSlot? (fun _ => rfl) c d

theorem hashSites_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    (zeroSubstCollapse c d).hashSites = d.hashSites := rfl

theorem ranges_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    (zeroSubstCollapse c d).ranges = d.ranges := rfl

theorem piCount_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    (zeroSubstCollapse c d).piCount = d.piCount := rfl

/-! ### The two refinement rows. -/

/-- The appended raw gate is in the target list. -/
theorem rawGate_mem_zeroSubst (c : Nat) (d : EffectVmDescriptor2) :
    bRawGate (.var c) ∈ (zeroSubstCollapse c d).constraints :=
  List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- The folded image of a source constraint is in the target list. -/
theorem substGate_mem_zeroSubst {c : Nat} {d : EffectVmDescriptor2} {x : VmConstraint2}
    (hx : x ∈ d.constraints) : substZeroGate c x ∈ (zeroSubstCollapse c d).constraints :=
  List.mem_append_left _ (List.mem_map_of_mem hx)

/-- The zero pin, read off a satisfying TRANSITION row of either side. -/
theorem pin_of_rawGate {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    {c : Nat} {cs : List VmConstraint2} (hraw : bRawGate (.var c) ∈ cs)
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f false) : fieldAssignment env.loc c = 0 := by
  have := field_of_base_gate (hall _ hraw)
  simpa [bRawGate, fieldBase] using this

/-- SECURITY row: every SOURCE constraint holds on an accepting TARGET row. Non-gate constraints are in
the target verbatim (the fold is the identity on them); a base gate is vacuous on the wrap row and, on a
transition row, recovered from its folded image plus the appended pin.

⚑ NOTE THE ASYMMETRY, and it is the good direction: this row takes NO hypothesis. The pin it needs is
the one the fold APPENDS, which is present in the target unconditionally. So the SECURITY leg — the leg
soundness rests on — holds for every `c` and every `d`, even where the source carries no raw gate at all
(there the fold is simply wrong-headed, and it is COMPLETENESS that fails, i.e. an honest witness may
stop verifying). Only `zeroSubst_completeness_row` consumes `bRawGate (.var c) ∈ d.constraints`. -/
theorem zeroSubst_security_row (c : Nat) (d : EffectVmDescriptor2)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (htgt : ∀ x ∈ (zeroSubstCollapse c d).constraints, x.holdsAt hash tf env f l)
    (x : VmConstraint2) (hx : x ∈ d.constraints) :
    x.holdsAt hash tf env f l := by
  cases x with
  | base bc =>
      cases bc with
      | gate body =>
          cases l with
          | true => exact trivial
          | false =>
              have hpin : fieldAssignment env.loc c = 0 :=
                pin_of_rawGate (rawGate_mem_zeroSubst c d) htgt
              have hfold : fieldBase env.loc (substZero c body) = 0 :=
                field_of_base_gate (htgt _ (substGate_mem_zeroSubst hx))
              rw [substZero_field c env.loc hpin body] at hfold
              exact bGate_holds_of_field_zero hfold
      | transition hi lo => exact htgt _ (substGate_mem_zeroSubst hx)
      | boundary r bb => exact htgt _ (substGate_mem_zeroSubst hx)
      | piBinding r cl k => exact htgt _ (substGate_mem_zeroSubst hx)
  | lookup l' => exact htgt _ (substGate_mem_zeroSubst hx)
  | memOp m => exact htgt _ (substGate_mem_zeroSubst hx)
  | mapOp m => exact htgt _ (substGate_mem_zeroSubst hx)
  | umemOp m => exact htgt _ (substGate_mem_zeroSubst hx)
  | proofBind m => exact htgt _ (substGate_mem_zeroSubst hx)
  | windowGate w => exact htgt _ (substGate_mem_zeroSubst hx)

/-- COMPLETENESS row: every TARGET constraint holds on an accepting SOURCE row. The appended pin IS a
source constraint; a folded base gate follows from the unfolded one plus the same pin. -/
theorem zeroSubst_completeness_row (c : Nat) (d : EffectVmDescriptor2)
    (hraw : bRawGate (.var c) ∈ d.constraints)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (f l : Bool)
    (hsrc : ∀ x ∈ d.constraints, x.holdsAt hash tf env f l)
    (x : VmConstraint2) (hx : x ∈ (zeroSubstCollapse c d).constraints) :
    x.holdsAt hash tf env f l := by
  rcases List.mem_append.1 hx with hmap | happ
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hmap
    cases y with
    | base bc =>
        cases bc with
        | gate body =>
            cases l with
            | true => exact trivial
            | false =>
                have hpin : fieldAssignment env.loc c = 0 := pin_of_rawGate hraw hsrc
                have hbody : fieldBase env.loc body = 0 := field_of_base_gate (hsrc _ hy)
                show (bGate (substZero c body)).holdsAt hash tf env f false
                exact bGate_holds_of_field_zero
                  (by rw [substZero_field c env.loc hpin body]; exact hbody)
        | transition hi lo => exact hsrc _ hy
        | boundary r bb => exact hsrc _ hy
        | piBinding r cl k => exact hsrc _ hy
    | lookup l' => exact hsrc _ hy
    | memOp m => exact hsrc _ hy
    | mapOp m => exact hsrc _ hy
    | umemOp m => exact hsrc _ hy
    | proofBind m => exact hsrc _ hy
    | windowGate w => exact hsrc _ hy
  · rw [List.mem_singleton] at happ
    subst happ
    exact hsrc _ hraw

/-! ### The pass and its ∀-d preservation. -/

/-- THE PASS. Both trace maps are the identity: the rewrite is constraint-only. -/
def zeroSubstPass (c : Nat) (d : EffectVmDescriptor2) :
    PassiveOptimization d (zeroSubstCollapse c d) where
  toTarget := id
  toSource := id
  publicABI := { piCount_eq := (piCount_zeroSubst c d).symm
                 bindingSlots_eq := (bindingSlots_zeroSubst c d).symm }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

open Dregg2.Circuit.PeepholeGeneralBatch (satisfied2_congr_constraints)

/-- ⚑ THE SECURITY LEG IS UNCONDITIONAL: ∀ `c`, ∀ `d`, no pin hypothesis. -/
theorem zeroSubst_security (c : Nat) (d : EffectVmDescriptor2) :
    SecurityRefinement (zeroSubstPass c d) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints (zeroSubstCollapse c d) d rfl rfl
    (memOps_zeroSubst c d).symm (mapOps_zeroSubst c d).symm ?_ hsat
  intro i hi x hx
  exact zeroSubst_security_row c d hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
    (hsat.rowConstraints i hi) x hx

theorem zeroSubst_completeness (c : Nat) (d : EffectVmDescriptor2)
    (hraw : bRawGate (.var c) ∈ d.constraints) :
    CompletenessPreservation (zeroSubstPass c d) := by
  intro hash minit mfin maddrs t hsat
  refine satisfied2_congr_constraints d (zeroSubstCollapse c d) rfl rfl
    (memOps_zeroSubst c d) (mapOps_zeroSubst c d) ?_ hsat
  intro i hi x hx
  exact zeroSubst_completeness_row c d hraw hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
    (hsat.rowConstraints i hi) x hx

/-- ⚑ BOTH LEGS, ∀-d: base-gate constant propagation off a recognised raw gate is a genuine
equisatisfiability-preserving passive pass on EVERY descriptor that carries the pin. No accept
reachability, no canonicality, no crypto floor — only `bRawGate (.var c) ∈ d.constraints`. -/
theorem zeroSubst_preservation (c : Nat) (d : EffectVmDescriptor2)
    (hraw : bRawGate (.var c) ∈ d.constraints) :
    SatisfiabilityPreservation (zeroSubstPass c d) :=
  ⟨zeroSubst_security c d, zeroSubst_completeness c d hraw⟩

theorem zeroSubst_satisfiable_iff (c : Nat) (d : EffectVmDescriptor2)
    (hraw : bRawGate (.var c) ∈ d.constraints)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash d minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (zeroSubstCollapse c d) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (zeroSubst_preservation c d hraw) hash minit mfin maddrs

/-- The recogniser DRIVES it: a column the scan reports is a legal instantiation. -/
theorem zeroSubst_preservation_of_scan (d : EffectVmDescriptor2) {c : Nat}
    (hc : c ∈ bZeroCols d.constraints) :
    SatisfiabilityPreservation (zeroSubstPass c d) :=
  zeroSubst_preservation c d (bZeroCol_rawGate_mem hc)

/-! ## §5. ⚑⚑ THE DELIVERABLE — CERTIFIED ON THE LIVE DEPLOYED COHORT WELD, ∀ MEMBER.

`gentianDeployedBareRefuse d` is the flag-day shape the whole 36-member `v3RegistryBare` cohort is
mapped to. Its escrow / discharge / vault blocks each carry a `floorZeroRefuseGate` — which §1b proves
IS a recognised raw gate and §3 proves IS a member — so the ∀-d pass above certifies on it with NO
further hypothesis. Three certified passes, one per deployed capacity block, for EVERY member. -/

section Deployed

open Dregg2.Deos.BareCohortFloorRefuseDeployed
  (gentianDeployedBareRefuse deployedRefuseGates blockGates refuseGatesAt decodeGatesAt
   ebDep bcDep icDep ocDep fcDep GRAD_ROT_WIDTH)
open Dregg2.Deos.CarrierBoundFloorGadget (orFoldGate orSeedGate)

/-- ⚑⚑ A CERTIFIED PEEPHOLE ON A REAL DEPLOYED DESCRIPTOR: for EVERY bare cohort member `d`, base-gate
constant propagation at the ESCROW block's floor column is a genuine `SatisfiabilityPreservation` on the
welded member. Not a `#guard`, no `decide`, no `native_decide`; the hypothesis is discharged by the
deployed weld's own gate. -/
theorem deployedRefuse_zeroSubst_escrow (d : EffectVmDescriptor2) :
    SatisfiabilityPreservation
      (zeroSubstPass (fcDep d.traceWidth 0) (gentianDeployedBareRefuse d)) :=
  zeroSubst_preservation _ _ (deployedRefuse_raw_mem_escrow d)

theorem deployedRefuse_zeroSubst_discharge (d : EffectVmDescriptor2) :
    SatisfiabilityPreservation
      (zeroSubstPass (fcDep d.traceWidth 1) (gentianDeployedBareRefuse d)) :=
  zeroSubst_preservation _ _ (deployedRefuse_raw_mem_discharge d)

theorem deployedRefuse_zeroSubst_vault (d : EffectVmDescriptor2) :
    SatisfiabilityPreservation
      (zeroSubstPass (fcDep d.traceWidth 2) (gentianDeployedBareRefuse d)) :=
  zeroSubst_preservation _ _ (deployedRefuse_raw_mem_vault d)

/-- …and the satisfiability equivalence it yields on the welded deployed member. -/
theorem deployedRefuse_satisfiable_iff (d : EffectVmDescriptor2)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (gentianDeployedBareRefuse d) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash
        (zeroSubstCollapse (fcDep d.traceWidth 0) (gentianDeployedBareRefuse d))
        minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (deployedRefuse_zeroSubst_escrow d) hash minit mfin maddrs

/-- ⚑ THE SAME, ON `dfaRoutingDesc` — a second real deployed descriptor, certified at its `zero_lane`
pin. `PeepholeDeployedShape.dfaRouting_frontier_noop` proved the window passes are the IDENTITY here;
this one is not. -/
theorem dfaRouting_zeroSubst_preservation :
    SatisfiabilityPreservation
      (zeroSubstPass Dregg2.Circuit.Emit.DfaRoutingEmit.ZERO_LANE
        Dregg2.Circuit.Emit.DfaRoutingEmit.dfaRoutingDesc) :=
  zeroSubst_preservation _ _ dfa_zeroLane_bRawGate_mem

/-! ### NON-VACUITY: the fold actually CHANGES real deployed gate bodies (compiled `==`, proves no Prop).

`substChanged` counts the base gates whose body the fold rewrites. On the deployed escrow block the
`orFoldGate` into the floor column reads `.var floorCol`, so it is genuinely constant-folded — together
with the refuse gate itself, which folds to `.const 0`. -/

/-- The body of a base gate, for comparison (`EmittedExpr` has `DecidableEq`; `VmConstraint2` does
not — `MapOp` carries functions). -/
def gateBody? : VmConstraint2 → Option EmittedExpr
  | .base (.gate b) => some b
  | _ => none

/-- How many base gates the fold rewrites. -/
def substChanged (c : Nat) (cs : List VmConstraint2) : Nat :=
  (cs.filter fun x =>
    match gateBody? x, gateBody? (substZeroGate c x) with
    | some a, some b => a != b
    | _, _ => false).length

-- The three deployed floor columns each have exactly TWO gates reading them: the OR-fold into the floor
-- and the refuse gate itself. Both are folded; the other 37 gates of the weld are untouched.
#guard substChanged (fcDep GRAD_ROT_WIDTH 0) (deployedRefuseGates GRAD_ROT_WIDTH) == 2
#guard substChanged (fcDep GRAD_ROT_WIDTH 1) (deployedRefuseGates GRAD_ROT_WIDTH) == 2
#guard substChanged (fcDep GRAD_ROT_WIDTH 2) (deployedRefuseGates GRAD_ROT_WIDTH) == 2

-- The folded OR-fold gate: the floor column really becomes `.const 0` in the deployed body.
#guard gateBody? (substZeroGate (fcDep GRAD_ROT_WIDTH 0)
    (orFoldGate (fcDep GRAD_ROT_WIDTH 0) (ocDep GRAD_ROT_WIDTH 0 2) (bcDep GRAD_ROT_WIDTH 0 3)))
  == some (.add (.const 0)
      (.mul (.const (-1))
        (.add (.add (.var (ocDep GRAD_ROT_WIDTH 0 2)) (.var (bcDep GRAD_ROT_WIDTH 0 3)))
          (.mul (.const (-1))
            (.mul (.var (ocDep GRAD_ROT_WIDTH 0 2)) (.var (bcDep GRAD_ROT_WIDTH 0 3)))))))

-- The fold is a REWRITE, not a size reduction: the target carries one more constraint (the re-appended
-- pin). Stated so it cannot be read as a shrink.
#guard (deployedRefuseGates GRAD_ROT_WIDTH).length == 39
#guard ((deployedRefuseGates GRAD_ROT_WIDTH).map (substZeroGate (fcDep GRAD_ROT_WIDTH 0))
  ++ [bRawGate (.var (fcDep GRAD_ROT_WIDTH 0))]).length == 40

end Deployed

/-! ## §6. The base-gate FRONTIER collapse over `ForcedB` — machinery, and why it does NOT fire deployed.

The direct mirror of `PeepholeFrontierScan.frontierCollapse`, but the honest report first: NEITHER
deployed descriptor examined carries a `.base (.gate (out − 1))` accept gate, so `bAcceptRoots` is EMPTY
on both and no `ForcedB` certificate is inhabited there. The refuse block's floor column is pinned to
ZERO, and its bits are boolean only via the is-zero gadget's CANONICALITY argument, not field-only
booleanity. So this section is machinery plus the forcing lemma it turns into a gate rewrite — the
deployed firing is §4–§5, and these `#guard`s record the absence rather than hiding it. -/

section FrontierB

open Dregg2.Circuit.Emit.DfaRoutingEmit (dfaRoutingDesc)
open Dregg2.Deos.BareCohortFloorRefuseDeployed (deployedRefuseGates GRAD_ROT_WIDTH)

-- ⚠ THE ABSENCE, RECORDED: no base-gate accept root, hence no inhabited `ForcedB`, on either deployed
-- descriptor. The base-gate frontier collapse has nothing to anchor to there.
#guard (bAcceptRoots dfaRoutingDesc.constraints).length == 0
#guard (bAcceptRoots (deployedRefuseGates GRAD_ROT_WIDTH)).length == 0
#guard (bAndEdges dfaRoutingDesc.constraints).length == 0
#guard (bAndEdges (deployedRefuseGates GRAD_ROT_WIDTH)).length == 0

/-- The forcing algebra DOES turn into a gate rewrite: on a list whose gates hold on a transition row,
a `ForcedB` bit plus its product gate makes the RAW gate `e = 0` hold — the appended replacement of a
frontier zero-test, base-gate form. This is the leg a full base-gate frontier collapse would consume,
and it is proven here even though no deployed descriptor currently anchors it. -/
theorem bRawGate_holds_of_forcedB {cs : List VmConstraint2} {e : EmittedExpr} {out : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f false)
    (hprod : bProdGate e out ∈ cs) (cert : ForcedB cs out) :
    (bRawGate e).holdsAt hash tf env f false :=
  bGate_holds_of_field_zero (forcedB_prod_zero hall hprod cert)

/-- …and symmetrically the elided INVERSE gate is recoverable from the raw replacement plus the forced
bit — the security-row leg of that collapse, base-gate form. -/
theorem bInvGate_holds_of_forced_and_raw {cs : List VmConstraint2} {e : EmittedExpr} {out inv : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f false)
    (hraw : bRawGate e ∈ cs) (cert : ForcedB cs out) :
    (bInvGate e out inv).holdsAt hash tf env f false := by
  have hone : fieldAssignment env.loc out = 1 := forcedB_field_one hall cert
  have hzero : fieldBase env.loc e = 0 := field_of_base_gate (hall _ hraw)
  refine bGate_holds_of_field_zero ?_
  rw [fb_inv, hzero, hone]
  ring

/-- …and the elided BIT gate likewise. -/
theorem bBitGate_holds_of_forcedB {cs : List VmConstraint2} {out : Nat}
    {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f : Bool}
    (hall : ∀ g ∈ cs, g.holdsAt hash tf env f false) (cert : ForcedB cs out) :
    (bBitGate out).holdsAt hash tf env f false := by
  have hone : fieldAssignment env.loc out = 1 := forcedB_field_one hall cert
  refine bGate_holds_of_field_zero ?_
  rw [fb_bit, hone]
  ring

end FrontierB

/-! ## §7. Axiom hygiene — every theorem above is kernel-clean (no `sorryAx`). -/

#assert_all_clean [
  fieldBase_eq_cast,
  field_of_base_gate,
  bGate_holds_of_field_zero,
  fb_accept,
  fb_and,
  fb_bit,
  fb_prod,
  fb_inv,
  isBProdGate_eq,
  bProdGate_mem_of_hasProdGate,
  bAcceptGate_of_mem_bAcceptRoots,
  bAndGate_of_mem_bAndEdges,
  bBitGate_of_hasBitGate,
  bZeroCol_rawGate_mem,
  isZeroForceGateT_is_bProdGate,
  isZeroDefGateT_is_bInvGate,
  floorZeroRefuseGate_is_bRawGate,
  isFirstBoolGate_is_bBitGate,
  stateGridGate_is_bBitGate,
  symbolGridGate_is_bBitGate,
  zeroLaneGate_is_bRawGate,
  forcedB_field_one,
  ForcedB.mono,
  forcedB_prod_zero,
  bBit_of_prod_inv,
  dfa_state_bBitGate_mem,
  dfa_symbol_bBitGate_mem,
  dfa_isFirst_bBitGate_mem,
  dfa_zeroLane_bRawGate_mem,
  deployed_prod_mem,
  deployed_inv_mem,
  deployed_raw_mem,
  deployedRefuse_raw_mem_escrow,
  deployedRefuse_raw_mem_discharge,
  deployedRefuse_raw_mem_vault,
  substZero_field,
  filterMap_map_substZeroGate,
  filterMap_zeroSubst,
  memOps_zeroSubst,
  mapOps_zeroSubst,
  bindingSlots_zeroSubst,
  rawGate_mem_zeroSubst,
  substGate_mem_zeroSubst,
  pin_of_rawGate,
  zeroSubst_security_row,
  zeroSubst_completeness_row,
  zeroSubst_security,
  zeroSubst_completeness,
  zeroSubst_preservation,
  zeroSubst_satisfiable_iff,
  zeroSubst_preservation_of_scan,
  deployedRefuse_zeroSubst_escrow,
  deployedRefuse_zeroSubst_discharge,
  deployedRefuse_zeroSubst_vault,
  deployedRefuse_satisfiable_iff,
  dfaRouting_zeroSubst_preservation,
  bRawGate_holds_of_forcedB,
  bInvGate_holds_of_forced_and_raw,
  bBitGate_holds_of_forcedB
]

end Dregg2.Circuit.PeepholeBaseGateScan
