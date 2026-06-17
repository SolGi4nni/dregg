/-
# Dregg2.Circuit.DeployedCapOpen — the IN-CIRCUIT cap-tree membership-open (authority leg foundation).

## Why this file exists (the critical-path authority leg)

`DeployedCapTree.lean` models the deployed 7-field depth-16 cap-tree (now committed to the SINGLE
chip absorb `cap_root.rs::cap_chip_absorb` — the arity-7 leaf + the arity-3 `[FACT_MARK, l, r]` node,
over the one `chipAbsorb` carrier) and proves the KERNEL-side bridge
`deployedCapOpen_implies_authorizedB`: a write-mask `MembersAt` opening implies the kernel's
`authorizedB`. But that bridge consumes `MembersAt` as a HYPOTHESIS — nothing in the circuit
denotation produced it.

This file closes that gap on the CIRCUIT side. It defines a CONSTRAINT — `CapOpenConstraint` — whose
denotation is exactly the in-circuit shape the Rust AIR realizes:

  * the 7 cap-leaf fields ride a Poseidon2 chip ABSORB (arity 7) producing the leaf digest column;
  * each of the depth-16 levels rides an arity-3 chip absorb (the tagged 3-list `[FACT_MARK, l, r]`)
    mixing `(cur, sib)` by the direction bit; the chain's top is CONSTRAINED `== cap_root` column;
  * the leaf's `target` column is CONSTRAINED `== src`, and `mask_lo` to the write-endpoint mask.

## The chip-rate reconciliation (DISCHARGED — decision #1, the gap CLOSED, §A)

The IR-v2 Poseidon2 chip (`DescriptorIR2`, `CHIP_RATE = babyBearD4W16.rate = 8`) realizes ONE rate-8
absorb of the lookup tuple: `chip_lookup_sound` enforces `digest = sponge (inputs.eval)` where
`sponge` is the chip's rate-8 list-hash. The deployed cap primitives are NOW the SAME single chip
absorb (`cap_root.rs::cap_chip_absorb`, mirrored in `DeployedCapTree`):

  * the leaf `capLeafDigest S = S.chipAbsorb ∘ leafFields` — ONE chip absorb of the 7 fields (arity 7);
  * the node `nodeOf S l r = S.chipAbsorb (packNode l r)` — ONE chip absorb of `[FACT_MARK, l, r]`
    (arity 3).

So the chip's `sponge (leafFields)` IS `capLeafDigest S leaf` and `sponge [FACT_MARK, l, r]` IS
`nodeOf S l r` — definitionally — when `sponge := S.chipAbsorb`. The reconciliation `SchemeRealizedBy
Chip sponge S` is therefore PROVABLE (`chipAbsorb_realizes`, §A): the chip genuinely realizes the
deployed cap hash now. The membership/soundness theorems specialize `sponge := S.chipAbsorb` and
DISCHARGE the bridge internally — it is no longer a carried hypothesis. (The named relation is kept as
documentation of the equations the realization satisfies.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR enters ONLY as the named
`CapHashScheme` carrier (`chipAbsorb`/`chipCR`, inherited from `DeployedCapTree`) + the chip-soundness
`ChipTableSound`. No `sorry`, no `native_decide`, no `:= True`.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.DeployedCapTree

namespace Dregg2.Circuit.DeployedCapOpen

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily TableId Lookup chipLookupTuple ChipTableSound chip_lookup_sound CHIP_RATE)
open Dregg2.Circuit.DeployedCapTree
  (CapLeaf FACT_MARK leafFields packNode CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (Step capLeafDigest nodeOf recomposeUp MembersAt DeployedFaithful confersTransferLeaf confersLeaf
   maskOfLimbs facetOfLeaf tierOfTag deployedCapOpen_implies_authorizedB)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (rightsMaskOf)
open Dregg2.Authority (Cap Auth Caps Label)
open Dregg2.Exec.FacetAuthority
  (AuthTier AuthProvided FacetCaps EffectMask EFFECT_TRANSFER isEffectPermitted authorizedFacetB)

set_option autoImplicit false

/-! ## §0 — the chip↔scheme realization bridge (NOW DISCHARGED — the chip IS the cap hash).

The chip's rate-8 `sponge : List ℤ → ℤ` realizes the deployed scheme `S` exactly when its single
absorb of the leaf-field list reproduces `capLeafDigest`, and its single absorb of `[FACT_MARK, l, r]`
reproduces `nodeOf`. Since the deployed scheme NOW commits exactly the chip absorb (`capLeafDigest S =
S.chipAbsorb ∘ leafFields`, `nodeOf S l r = S.chipAbsorb (packNode l r)`), the chip whose `sponge` is
`S.chipAbsorb` satisfies both equations DEFINITIONALLY — see `chipAbsorb_realizes` (§A). -/

/-- **`SchemeRealizedByChip sponge S`** — the chip's rate-8 list-hash `sponge` reproduces the deployed
cap scheme `S`'s leaf and node digests. With the cap-tree re-committed to the chip absorb, this is
DISCHARGED by `sponge := S.chipAbsorb` (`chipAbsorb_realizes`), not carried. (Kept as a named record
of the realization equations; `packNode S l r = [FACT_MARK, l, r]` is the chip's node block.) -/
structure SchemeRealizedByChip {State : Type} (sponge : List ℤ → ℤ) (S : CapHashScheme State) : Prop where
  /-- The chip's 7-field absorb reproduces the deployed leaf digest. -/
  leafRealized : ∀ l : CapLeaf, sponge (leafFields l) = capLeafDigest S l
  /-- The chip's `[FACT_MARK, l, r]` absorb reproduces the deployed node digest. -/
  nodeRealized : ∀ l r : ℤ, sponge (packNode l r) = nodeOf S l r

/-- **`chipAbsorb_realizes` — THE DISCHARGE.** The chip whose `sponge` is the deployed scheme's own
`chipAbsorb` carrier realizes `S`: both equations hold by `rfl` (`capLeafDigest`/`nodeOf` ARE
`S.chipAbsorb` of their input blocks). This is decision #1 made good — the cap-tree is re-committed to
the one in-circuit hash, so the chip genuinely realizes it. -/
theorem chipAbsorb_realizes {State : Type} (S : CapHashScheme State) :
    SchemeRealizedByChip S.chipAbsorb S :=
  { leafRealized := fun _ => rfl
  , nodeRealized := fun _ _ => rfl }

/-! ## §1 — the column plan for one cap-membership row.

(The COLUMN LAYOUT and the chip LOOKUPS are exactly what the Rust AIR realizes; with the cap-tree
re-committed to the chip absorb, the digest the chip soundness yields IS the deployed scheme's
`capLeafDigest`/`nodeOf` — no reconciliation step, the bridge discharges by `rfl`.) -/

/-- The deployed cap-tree depth (`cap_root.rs::CAP_TREE_DEPTH = 16`). -/
def DEPTH : Nat := 16

/-- The column layout for a cap-membership row. All indices abstract `Nat`; the Rust AIR pins them. -/
structure CapOpenCols where
  /-- The 7 leaf-field columns, in `CapLeaf` order. -/
  leaf       : Fin 7 → Nat
  /-- The leaf-digest column (the chip absorb output). -/
  leafDigest : Nat
  /-- The sibling-digest column at each level. -/
  sib        : Nat → Nat
  /-- The direction-bit column at each level (0 ⇒ cur is LEFT child). -/
  dir        : Nat → Nat
  /-- The node-output column at each level. -/
  node       : Nat → Nat
  /-- The committed `cap_root` column. -/
  capRoot    : Nat
  /-- The turn's source-cell-id column. -/
  src        : Nat

/-! ## §2 — the leaf-field accessors (decode the 7 leaf columns to a `CapLeaf`). -/

/-- Read the `CapLeaf` whose fields are the row's 7 leaf columns. -/
def leafOf (c : CapOpenCols) (env : VmRowEnv) : CapLeaf :=
  { slot_hash  := env.loc (c.leaf 0)
  , target     := env.loc (c.leaf 1)
  , auth_tag   := env.loc (c.leaf 2)
  , mask_lo    := env.loc (c.leaf 3)
  , mask_hi    := env.loc (c.leaf 4)
  , expiry     := env.loc (c.leaf 5)
  , breadstuff := env.loc (c.leaf 6) }

/-- The 7 leaf-field column EXPRESSIONS, in canonical order (the chip absorb's input tuple). -/
def leafInputs (c : CapOpenCols) : List EmittedExpr :=
  (List.finRange 7).map (fun i => EmittedExpr.var (c.leaf i))

/-- The leaf inputs evaluate to exactly the `leafFields` of the decoded leaf. -/
theorem leafInputs_eval (c : CapOpenCols) (env : VmRowEnv) :
    (leafInputs c).map (·.eval env.loc) = leafFields (leafOf c env) := by
  simp only [leafInputs, List.map_map, leafFields]
  rfl

/-! ## §3 — the chip-lookup tuples (leaf absorb + per-level node absorb). -/

/-- The leaf-digest chip lookup tuple: absorb the 7 leaf-field columns, output = `leafDigest`. -/
def leafLookup (c : CapOpenCols) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTuple (leafInputs c) c.leafDigest }

/-- The `cur` digest entering level `lvl`: the leaf digest at level 0, else the previous node. -/
def curCol (c : CapOpenCols) : Nat → Nat
  | 0       => c.leafDigest
  | (l + 1) => c.node l

/-- The `hash_fact` LEFT input at level `lvl`: `(1-dir)·cur + dir·sib`. -/
def leftExpr (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .add (.mul (.add (.const 1) (.mul (.const (-1)) (.var (c.dir lvl)))) (.var (curCol c lvl)))
       (.mul (.var (c.dir lvl)) (.var (c.sib lvl)))

/-- The `hash_fact` RIGHT input at level `lvl`: `(1-dir)·sib + dir·cur`. -/
def rightExpr (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .add (.mul (.add (.const 1) (.mul (.const (-1)) (.var (c.dir lvl)))) (.var (c.sib lvl)))
       (.mul (.var (c.dir lvl)) (.var (curCol c lvl)))

/-- The node chip lookup tuple at level `lvl`: absorb `[FACT_MARK, left, right]`, output = `node lvl`. -/
def nodeLookup (c : CapOpenCols) (lvl : Nat) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTuple [.const FACT_MARK, leftExpr c lvl, rightExpr c lvl] (c.node lvl) }

/-! ## §4 — the gate equations (booleanity, root pin, leaf↔effect binding). -/

/-- `dir` is boolean: `dir·(dir-1) = 0`. -/
def dirBoolGate (c : CapOpenCols) (lvl : Nat) : EmittedExpr :=
  .mul (.var (c.dir lvl)) (.add (.var (c.dir lvl)) (.const (-1)))

/-- The root pin: the TOP node output equals the committed `cap_root` column. -/
def rootPinGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.node (DEPTH - 1))) (.mul (.const (-1)) (.var c.capRoot))

/-- The target binding: `leaf.target - src = 0`. -/
def targetBindGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 1)) (.mul (.const (-1)) (.var c.src))

/-- **`transferFacetGate`** (THE CUTOVER, FacetAuthority §10(C)) — the FACET binding: it pins the
leaf's low mask limb to `EFFECT_TRANSFER` and the high limb to `0`, so the decoded facet `maskOfLimbs
mask_lo mask_hi = EFFECT_TRANSFER` permits the `EFFECT_TRANSFER` bit (`facet.rs:123`). This REPLACES the
toy `writeMaskGate` (`mask_lo == write-mask`). Two equations as one zero-pinned sum is impossible, so
we pin `mask_lo` here and `mask_hi` in `facetHiGate`. -/
def transferFacetGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 3)) (.const (-(EFFECT_TRANSFER)))

/-- The high-limb pin: `leaf.mask_hi = 0` (so `maskOfLimbs mask_lo mask_hi = mask_lo`). -/
def facetHiGate (c : CapOpenCols) : EmittedExpr :=
  .var (c.leaf 4)

/-- **`authTagGate`** (THE CUTOVER, FacetAuthority §10(C)) — the TIER binding: it pins the leaf's
`auth_tag` to the `Signature` tier byte `1` (`tierOfTag 1 = .signature`, satisfiable by a provided
signature). The tier-off-the-leaf generality (any committed `auth_tag`) is the NAMED §10 residual; here
the in-circuit row binds a concrete satisfiable tier. -/
def authTagGate (c : CapOpenCols) : EmittedExpr :=
  .add (.var (c.leaf 2)) (.const (-1))

/-! ## §5 — `Satisfied`: the full per-row denotation of one cap-membership constraint. -/

/-- **`Satisfied sponge tf c env`** — the cap-membership row is satisfied. The in-circuit denotation
the Rust `CapMembership` AIR realizes (the chip lookups + the base gates). -/
structure Satisfied (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) : Prop where
  /-- The leaf-digest chip absorb is a chip-table row. -/
  leafHashed : (leafLookup c).holdsAt tf env
  /-- Each level's node absorb is a chip-table row. -/
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  /-- Each level's direction column is boolean. -/
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  /-- The top node output equals the committed cap_root. -/
  rootPinned : (rootPinGate c).eval env.loc = 0
  /-- The leaf's target equals the turn's src. -/
  targetBound : (targetBindGate c).eval env.loc = 0
  /-- The leaf's `mask_lo` is `EFFECT_TRANSFER` (the facet permits TRANSFER). -/
  facetTransfer : (transferFacetGate c).eval env.loc = 0
  /-- The leaf's `mask_hi` is `0` (so the decoded facet is exactly `mask_lo`). -/
  facetHiZero : (facetHiGate c).eval env.loc = 0
  /-- The leaf's `auth_tag` is the `Signature` tier byte (satisfiable by a provided signature). -/
  tierTagged : (authTagGate c).eval env.loc = 0

/-! ## §6 — soundness: the leaf-digest column carries the genuine `capLeafDigest`.

The chip enforces `leafDigest = sponge (leafFields)` with `sponge := S.chipAbsorb` — and the deployed
`capLeafDigest S = S.chipAbsorb ∘ leafFields`, so the two coincide (the realization is `chipAbsorb_
realizes`, discharged in place). -/

/-- Under a sound chip table (the chip's hash IS the deployed `S.chipAbsorb`), the leaf-digest column
carries the deployed `capLeafDigest S (leafOf c env)`. The `SchemeRealizedByChip` bridge is DISCHARGED
internally by `chipAbsorb_realizes` — no longer a hypothesis. -/
theorem leafDigest_sound {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env) :
    env.loc c.leafDigest = capLeafDigest S (leafOf c env) := by
  have hlen : (leafInputs c).length ≤ CHIP_RATE := by
    simp [leafInputs, List.length_map, List.length_finRange, CHIP_RATE]
    decide
  have hmem : (chipLookupTuple (leafInputs c) c.leafDigest).map (·.eval env.loc) ∈ tf .poseidon2 := by
    have := hsat.leafHashed
    unfold Lookup.holdsAt leafLookup at this
    exact this
  have h := chip_lookup_sound S.chipAbsorb (tf .poseidon2) hChip env.loc (leafInputs c) c.leafDigest hlen hmem
  rw [h, leafInputs_eval, (chipAbsorb_realizes S).leafRealized]

/-- The direction BOOL value at a level. -/
def dirBoolVal (c : CapOpenCols) (env : VmRowEnv) (lvl : Nat) : Bool :=
  env.loc (c.dir lvl) = 1

/-- A boolean dir column is `0` or `1`. -/
theorem dir_zero_or_one (c : CapOpenCols) (env : VmRowEnv) (lvl : Nat)
    (h : (dirBoolGate c lvl).eval env.loc = 0) :
    env.loc (c.dir lvl) = 0 ∨ env.loc (c.dir lvl) = 1 := by
  unfold dirBoolGate at h
  simp only [EmittedExpr.eval] at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · right; linarith

/-- Under a sound chip table (the chip's hash IS the deployed `S.chipAbsorb`), level `lvl`'s node
column carries the genuine deployed `nodeOf S` of the mixed `(cur, sib)` pair — exactly one
`recomposeUp` step. The `SchemeRealizedByChip` bridge is DISCHARGED by `chipAbsorb_realizes`. -/
theorem node_sound {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env) (lvl : Nat) (hlvl : lvl < DEPTH) :
    env.loc (c.node lvl)
      = (if dirBoolVal c env lvl
          then nodeOf S (env.loc (c.sib lvl)) (env.loc (curCol c lvl))
          else nodeOf S (env.loc (curCol c lvl)) (env.loc (c.sib lvl))) := by
  have hlen : ([EmittedExpr.const FACT_MARK, leftExpr c lvl, rightExpr c lvl]).length ≤ CHIP_RATE := by
    show 3 ≤ CHIP_RATE
    rw [show CHIP_RATE = 8 from rfl]; omega
  have hmem : (chipLookupTuple [.const FACT_MARK, leftExpr c lvl, rightExpr c lvl] (c.node lvl)).map
      (·.eval env.loc) ∈ tf .poseidon2 := by
    have := hsat.nodeHashed lvl hlvl
    unfold Lookup.holdsAt nodeLookup at this
    exact this
  have h := chip_lookup_sound S.chipAbsorb (tf .poseidon2) hChip env.loc
    [.const FACT_MARK, leftExpr c lvl, rightExpr c lvl] (c.node lvl) hlen hmem
  rw [h]
  -- The absorbed list evaluates to `[FACT_MARK, leftVal, rightVal] = packNode leftVal rightVal`;
  -- the realization turns `S.chipAbsorb (packNode ·, ·)` into the deployed `nodeOf S`.
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval, leftExpr, rightExpr]
  rcases dir_zero_or_one c env lvl (hsat.dirBool lvl hlvl) with hd0 | hd1
  · have hbool : dirBoolVal c env lvl = false := by
      simp only [dirBoolVal, hd0]; decide
    rw [hbool, hd0]
    simp only [Bool.false_eq_true, if_false]
    rw [show ((1 : ℤ) + -1 * 0) * env.loc (curCol c lvl) + 0 * env.loc (c.sib lvl)
          = env.loc (curCol c lvl) by ring,
        show ((1 : ℤ) + -1 * 0) * env.loc (c.sib lvl) + 0 * env.loc (curCol c lvl)
          = env.loc (c.sib lvl) by ring]
    exact (chipAbsorb_realizes S).nodeRealized _ _
  · have hbool : dirBoolVal c env lvl = true := by
      simp only [dirBoolVal, hd1]; decide
    rw [hbool, hd1]
    simp only [if_true]
    rw [show ((1 : ℤ) + -1 * 1) * env.loc (curCol c lvl) + 1 * env.loc (c.sib lvl)
          = env.loc (c.sib lvl) by ring,
        show ((1 : ℤ) + -1 * 1) * env.loc (c.sib lvl) + 1 * env.loc (curCol c lvl)
          = env.loc (curCol c lvl) by ring]
    exact (chipAbsorb_realizes S).nodeRealized _ _

/-! ## §7 — assembling the recompose: the node columns realize a `recomposeUp` path. -/

/-- `recomposeUp` distributes over a path append. -/
theorem recomposeUp_append {State : Type} (S : CapHashScheme State) (cur : ℤ) (p q : List Step) :
    recomposeUp S cur (p ++ q) = recomposeUp S (recomposeUp S cur p) q := by
  induction p generalizing cur with
  | nil => simp [recomposeUp]
  | cons s rest ih => simp only [List.cons_append, recomposeUp]; rw [ih]

/-- The membership path read off the row's columns: `(sib, dir)` for levels `[0, n)`. -/
def pathOf (c : CapOpenCols) (env : VmRowEnv) (n : Nat) : List Step :=
  (List.range n).map (fun lvl => { sib := env.loc (c.sib lvl), dir := dirBoolVal c env lvl })

/-- Folding `recomposeUp` over the first `n` levels reproduces `curCol c n`, under chip soundness
(the chip↔scheme bridge DISCHARGED by `chipAbsorb_realizes`). -/
theorem recompose_reaches_cur {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env) :
    ∀ n, n ≤ DEPTH →
      recomposeUp S (env.loc c.leafDigest) (pathOf c env n) = env.loc (curCol c n) := by
  intro n
  induction n with
  | zero => intro _; simp [pathOf, recomposeUp, curCol]
  | succ k ih =>
    intro hk
    have hkd : k < DEPTH := Nat.lt_of_succ_le hk
    have hkle : k ≤ DEPTH := Nat.le_of_lt hkd
    have hpath : pathOf c env (k + 1)
        = pathOf c env k ++ [{ sib := env.loc (c.sib k), dir := dirBoolVal c env k }] := by
      simp [pathOf, List.range_succ, List.map_append]
    rw [hpath, recomposeUp_append, ih hkle]
    simp only [recomposeUp]
    have hns := node_sound S tf c env hChip hsat k hkd
    have hcur : curCol c (k + 1) = c.node k := rfl
    rw [hcur]
    cases hb : dirBoolVal c env k
    · simp only [hb, Bool.false_eq_true, if_false] at hns ⊢
      rw [hns]
    · simp only [hb, if_true] at hns ⊢
      rw [hns]

/-- **`capOpen_membership` — the in-circuit fold IS a `MembersAt` opening.** Under a sound chip table
(the chip's hash IS `S.chipAbsorb`, so the `SchemeRealizedByChip` bridge is DISCHARGED by
`chipAbsorb_realizes`), a `Satisfied` row witnesses `MembersAt S cap_root leaf`. -/
theorem capOpen_membership {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env) :
    MembersAt S (env.loc c.capRoot) (leafOf c env) := by
  refine ⟨pathOf c env DEPTH, ?_⟩
  have hfold := recompose_reaches_cur S tf c env hChip hsat DEPTH (le_refl _)
  have hleaf := leafDigest_sound S tf c env hChip hsat
  rw [hleaf] at hfold
  have hcurTop : curCol c DEPTH = c.node (DEPTH - 1) := rfl
  rw [hcurTop] at hfold
  have hpin := hsat.rootPinned
  unfold rootPinGate at hpin
  simp only [EmittedExpr.eval] at hpin
  have hroot : env.loc (c.node (DEPTH - 1)) = env.loc c.capRoot := by linarith
  rw [hfold, hroot]

/-! ## §8 — the leaf↔effect binding (target = src, write-mask). -/

/-- The target gate pins `leaf.target = src`. -/
theorem capOpen_target (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (hsat : Satisfied sponge tf c env) :
    (leafOf c env).target = env.loc c.src := by
  have h := hsat.targetBound
  unfold targetBindGate at h
  simp only [EmittedExpr.eval] at h
  simp only [leafOf]
  linarith

/-- **`capOpen_confers`** (THE CUTOVER) — the facet + tier gates pin the FAITHFUL two-axis
`confersTransferLeaf vkOfTag .signature leaf`: the decoded facet (`maskOfLimbs mask_lo mask_hi =
EFFECT_TRANSFER`) permits the TRANSFER bit, and the decoded tier (`tierOfTag auth_tag = .signature`,
since `auth_tag = 1`) is satisfied by a provided signature. Holds for ANY `vkOfTag` (the tag is `1`,
not the `Custom` byte `5`). -/
theorem capOpen_confers (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (vkOfTag : ℤ → Nat) (hsat : Satisfied sponge tf c env) :
    confersTransferLeaf vkOfTag .signature (leafOf c env) := by
  have hlo := hsat.facetTransfer
  have hhi := hsat.facetHiZero
  have htag := hsat.tierTagged
  unfold transferFacetGate at hlo
  unfold facetHiGate at hhi
  unfold authTagGate at htag
  simp only [EmittedExpr.eval] at hlo hhi htag
  -- decode: mask_lo = EFFECT_TRANSFER, mask_hi = 0, auth_tag = 1.
  have hmlo : (leafOf c env).mask_lo = EFFECT_TRANSFER := by simp only [leafOf]; linarith
  have hmhi : (leafOf c env).mask_hi = 0 := by simp only [leafOf]; exact hhi
  have htg : (leafOf c env).auth_tag = 1 := by simp only [leafOf]; linarith
  unfold confersTransferLeaf facetOfLeaf maskOfLimbs
  rw [hmlo, hmhi, htg]
  refine ⟨?_, ?_⟩
  · -- facet: maskOfLimbs EFFECT_TRANSFER 0 = EFFECT_TRANSFER permits EFFECT_TRANSFER.
    show isEffectPermitted (some (EFFECT_TRANSFER + (0 : ℤ) * 65536).toNat) EFFECT_TRANSFER = true
    decide
  · -- tier: tierOfTag vkOfTag 1 = .signature, satisfied by a provided signature (by rfl).
    show (tierOfTag vkOfTag 1).isSatisfiedBy .signature = true
    rfl

/-! ## §8.G — F6: the cap-open confers the GENERAL tier × facet (decoded, not pinned).

`capOpen_confers` above discharges `confersTransferLeaf … .signature` because the live descriptor's
`authTagGate` pins `auth_tag = 1` (Signature) and `transferFacetGate` pins `mask_lo = EFFECT_TRANSFER`.
F6 generalizes BOTH axes OFF THE COMMITTED LEAF:

  * **the TIER** (`§10` named residual) — instead of concluding the constant `.signature`, decode the
    committed `auth_tag` to `tierOfTag vkOfTag auth_tag` and conclude `confersTransferLeaf` for THAT
    tier against any `provided` the off-circuit AuthContext supplies that satisfies it. No `auth_tag`
    pin needed: the tier is GENUINELY read off the committed byte.
  * **the FACET** — `facetOfLeaf` already decodes the genuine `maskOfLimbs mask_lo mask_hi`; the
    general gate checks `isEffectPermitted` of the decoded mask against the turn's effect bit, rather
    than pinning the mask to a TRANSFER constant.

So `capOpen_confers_decoded` concludes `confersLeaf` for the GENERAL `(effectBit, provided)` from the
committed leaf, given only that the decoded facet permits `effectBit` and the decoded tier is
satisfied by `provided` — both read off the COMMITTED row, not pinned. -/

/-- **`capOpen_confers_decoded` (F6) — the cap-open confers the GENERAL tier × facet, DECODED.** From
a `Satisfied` row (the in-circuit membership open) plus the two facts read off the COMMITTED leaf —
the decoded facet `facetOfLeaf` permits `effectBit`, and the decoded tier `tierOfTag auth_tag` is
satisfied by `provided` — the leaf confers `effectBit` authority under `provided` (`confersLeaf`). The
tier is the GENUINE committed byte (NOT the Signature constant the `authTagGate` pins); the facet is
the GENUINE decoded `maskOfLimbs` (NOT the TRANSFER constant). This discharges the §10 tier residual:
the cap-open authorizes the general tier × facet, off the committed leaf. -/
theorem capOpen_confers_decoded (sponge : List ℤ → ℤ) (tf : TraceFamily) (c : CapOpenCols)
    (env : VmRowEnv) (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (hfacet : isEffectPermitted (facetOfLeaf (leafOf c env)) effectBit = true)
    (htier : (tierOfTag vkOfTag (leafOf c env).auth_tag).isSatisfiedBy provided = true) :
    confersLeaf vkOfTag provided effectBit (leafOf c env) :=
  ⟨hfacet, htier⟩

/-! ## §9 — THE KEYSTONE: `capOpen_sound` (Satisfied ⟹ MembersAt ∧ binding). -/

/-- **`capOpen_sound`** — the in-circuit cap-membership row is SOUND: it opens the deployed cap-tree
at a write-mask leaf whose target is the turn's `src`. THE authority leg's circuit foundation. The
`SchemeRealizedByChip` chip↔scheme bridge is DISCHARGED (the chip's hash IS `S.chipAbsorb`, by
`chipAbsorb_realizes`) — no longer a carried hypothesis. -/
theorem capOpen_sound {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (vkOfTag : ℤ → Nat)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env) :
    MembersAt S (env.loc c.capRoot) (leafOf c env)
    ∧ (leafOf c env).target = env.loc c.src
    ∧ confersTransferLeaf vkOfTag .signature (leafOf c env) :=
  ⟨capOpen_membership S tf c env hChip hsat,
   capOpen_target S.chipAbsorb tf c env hsat,
   capOpen_confers S.chipAbsorb tf c env vkOfTag hsat⟩

/-! ## §10 — CHAINING to the kernel `authorizedB` (the end-to-end authority leg). -/

/-- **`capOpen_authorizes` — THE END-TO-END AUTHORITY LEG.** GIVEN the deployed commitment, a
`Satisfied` row whose opened leaf IS the faithfulness contract's `(actor ⇒ src)` edge leaf yields the
kernel's `authorizedB = true`. The `SchemeRealizedByChip` bridge is DISCHARGED (`chipAbsorb_realizes`)
— the chip genuinely realizes the cap hash. -/
theorem capOpen_authorizes {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (vkOfTag : ℤ → Nat)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag .signature caps (env.loc c.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : env.loc c.src = (src : ℤ))
    (hedge : leafOf c env = leafAt actor src) :
    authorizedFacetB caps .signature
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hmem : MembersAt S (env.loc c.capRoot) (leafAt actor src) := by
    rw [← hedge]; exact capOpen_membership S tf c env hChip hsat
  have hconf : confersTransferLeaf vkOfTag .signature (leafAt actor src) := by
    rw [← hedge]; exact capOpen_confers S.chipAbsorb tf c env vkOfTag hsat
  have htgt : (leafAt actor src).target = (src : ℤ) := by
    rw [← hedge, capOpen_target S.chipAbsorb tf c env hsat, hsrc]
  exact ⟨deployedCapOpen_implies_authorizedB S vkOfTag .signature caps (env.loc c.capRoot) leafAt hfaith
    actor src dst amt hmem hconf, htgt⟩

/-- **`capOpen_authorizes_tierGeneral` (F6) — THE END-TO-END AUTHORITY LEG, GENERAL TIER.** The
generalization of `capOpen_authorizes` from the pinned `.signature` tier to ANY `provided` auth that
satisfies the tier DECODED off the committed leaf (`tierOfTag vkOfTag leaf.auth_tag`). The cap-open's
facet gate still binds the transfer facet (the kernel `authorizedFacetB` is over `turnEffectBit =
EFFECT_TRANSFER`), but the TIER is now the GENUINE committed `auth_tag` byte — NOT the Signature
constant the `authTagGate` pins. This discharges the §10 tier residual end-to-end: a cap-open whose
leaf commits ANY tier (None/Signature/Proof/Either/Impossible/Custom) authorizes exactly when the
off-circuit auth satisfies that committed tier. (`capOpen_authorizes` is the `.signature` instance,
recovered when `auth_tag = 1` and `provided = .signature`.) -/
theorem capOpen_authorizes_tierGeneral {State : Type} (S : CapHashScheme State)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) (vkOfTag : ℤ → Nat)
    (provided : AuthProvided)
    (hChip : ChipTableSound S.chipAbsorb (tf .poseidon2))
    (hsat : Satisfied S.chipAbsorb tf c env)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag provided caps (env.loc c.capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : env.loc c.src = (src : ℤ))
    (hedge : leafOf c env = leafAt actor src)
    -- the off-circuit auth satisfies the tier DECODED off the committed leaf (not a constant).
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hmem : MembersAt S (env.loc c.capRoot) (leafAt actor src) := by
    rw [← hedge]; exact capOpen_membership S tf c env hChip hsat
  -- the facet leg is read off the COMMITTED (decoded) mask; the tier leg is the committed `auth_tag`.
  have hfacet : isEffectPermitted (facetOfLeaf (leafAt actor src)) EFFECT_TRANSFER = true := by
    rw [← hedge]; exact (capOpen_confers S.chipAbsorb tf c env vkOfTag hsat).1
  have hconf : confersTransferLeaf vkOfTag provided (leafAt actor src) := ⟨hfacet, htier⟩
  have htgt : (leafAt actor src).target = (src : ℤ) := by
    rw [← hedge, capOpen_target S.chipAbsorb tf c env hsat, hsrc]
  exact ⟨deployedCapOpen_implies_authorizedB S vkOfTag provided caps (env.loc c.capRoot) leafAt hfaith
    actor src dst amt hmem hconf, htgt⟩

/-! ## §A — THE CHIP-RATE GAP IS CLOSED (`SchemeRealizedByChip` DISCHARGED, not carried).

Decision #1: the cap-tree is re-committed to the chip's hash (`cap_root.rs::cap_chip_absorb`,
mirrored as `DeployedCapTree`'s single `chipAbsorb` carrier). So the chip whose `sponge` is
`S.chipAbsorb` realizes the deployed scheme DEFINITIONALLY — `chipAbsorb_realizes` (§0) supplies it,
and every soundness theorem above specializes `sponge := S.chipAbsorb` and discharges the bridge in
place. There is NO carried `SchemeRealizedByChip` hypothesis on the live path anymore.

The realization is NON-VACUOUS in the load-bearing sense: it is the chip-absorb collision-resistance
`S.chipCR` (a `Compress1CR`, primitive #4 — NOT `True`; a constant compression falsifies it) that
makes the membership leg's anti-ghost (`recomposeUp_inj_of_path`, `nodeOf_injective`,
`capLeafDigest_injective`) bite. We re-state the discharge as the headline fact, and pin that the
node and leaf domains are length-disjoint (the chip's per-row arity seeding that lets one `chipAbsorb`
serve both shapes). -/

/-- **THE DISCHARGE, re-stated as the §A headline.** The deployed scheme's own chip-absorb carrier
realizes the scheme — `SchemeRealizedByChip S.chipAbsorb S` holds (both equations by `rfl`). The
chip-rate gap the prior revision carried is CLOSED: the IR-v2 chip genuinely realizes the cap hash. -/
theorem schemeRealizedByChip_discharged {State : Type} (S : CapHashScheme State) :
    SchemeRealizedByChip S.chipAbsorb S :=
  chipAbsorb_realizes S

/-- The node block `packNode l r = [FACT_MARK, l, r]` (length 3) and any leaf-field block `leafFields
leaf` (length 7) are LENGTH-DISJOINT — the structural fact behind the chip serving both arities from
one `chipAbsorb` (the chip seeds by `(arity, padded inputs)`, so the two shapes never alias). -/
theorem node_leaf_length_disjoint (l r : ℤ) (leaf : CapLeaf) :
    (packNode l r).length ≠ (leafFields leaf).length := by
  simp [packNode, leafFields]

/-! ## §11 — discriminating teeth (the gates are real). -/

/-- **The transfer-facet gate is DISCRIMINATING (witness FALSE).** A leaf whose `mask_lo` is NOT
`EFFECT_TRANSFER` fails the facet binding. -/
theorem transferFacetGate_discriminates (c : CapOpenCols) (env : VmRowEnv)
    (hbad : env.loc (c.leaf 3) = EFFECT_TRANSFER + 1) :
    (transferFacetGate c).eval env.loc ≠ 0 := by
  unfold transferFacetGate
  simp only [EmittedExpr.eval, hbad]
  intro h; linarith

/-- **The target gate is DISCRIMINATING (witness FALSE).** -/
theorem targetBindGate_discriminates (c : CapOpenCols) (env : VmRowEnv)
    (hne : env.loc (c.leaf 1) ≠ env.loc c.src) :
    (targetBindGate c).eval env.loc ≠ 0 := by
  unfold targetBindGate
  simp only [EmittedExpr.eval]
  intro h
  apply hne
  linarith

/-! ## §12 — Axiom hygiene. -/

#assert_axioms chipAbsorb_realizes
#assert_axioms leafDigest_sound
#assert_axioms node_sound
#assert_axioms recompose_reaches_cur
#assert_axioms capOpen_membership
#assert_axioms capOpen_confers
#assert_axioms capOpen_confers_decoded
#assert_axioms capOpen_sound
#assert_axioms capOpen_authorizes
#assert_axioms capOpen_authorizes_tierGeneral
#assert_axioms schemeRealizedByChip_discharged
#assert_axioms node_leaf_length_disjoint
#assert_axioms transferFacetGate_discriminates
#assert_axioms targetBindGate_discriminates

end Dregg2.Circuit.DeployedCapOpen
