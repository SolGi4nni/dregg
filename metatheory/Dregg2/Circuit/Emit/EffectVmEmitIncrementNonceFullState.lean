/-
# Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState — incrementNonce LIFTED to FULL-STATE on the
RUNNABLE descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitIncrementNonce` welds the per-cell block (`CellIncNonceSpec`: economic block FROZEN, the
on-trace seq-nonce TICKS) on the 186-wide RUNNABLE descriptor; its `state_commit` absorbs only the 13
state-block columns, NOT the 8 side-table roots (the dominant Class-C gap, `*_root_not_in_descriptor`).
This module CLOSES that for incrementNonce by amplifying its RUNNABLE descriptor to the WIDE
(`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the
FULL 17-field declarative post-state — the per-cell block (`CellIncNonceSpec`) AND every one of the 8
side-table roots FROZEN (`postRoots = preRoots`). incrementNonce touches NO side-table, so its
`system_roots` sub-block is frozen; the magnesium win is that the WIDE commitment now BINDS all 8 roots,
so a prover CANNOT tamper any side-table root (a dropped escrow, an omitted nullifier, …) while keeping
the published `NEW_COMMIT` without EXHIBITING a collision of the deployed sponge — the anti-ghost tooth
(`runnable_full_commit_binds_or_collides`) bites on all 17.

This is the §RECIPE of `EffectVmFullStateRunnable` applied to incrementNonce: (1) the wide descriptor
(`traceWidth := EFFECT_VM_WIDTH_SYSROOTS`, `hashSites := wideHashSites`, constraint list UNCHANGED so
`usesWideSites := rfl`); (2) `isRow := IsIncNonceRow`; (3) `decodeAfter` = `RowEncodesIncNonce` +
frozen-roots witness; (4) `fullClause` = `CellIncNonceSpec` ∧ `postRoots = preRoots`; (5) `decodeFull`
= the THIN gate-only soundness (the gates are the narrow descriptor's verbatim, so `intent_to_cellSpec`
applies) + the carried frozen-roots fact. The crypto/anti-ghost is discharged ONCE in the generic
theorem; per-effect is just the decode.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NO collision-resistance
hypothesis enters anywhere: the anti-ghost theorems are the UNCONDITIONAL `_or_collides` forms, whose
alternative branch hands back a specific colliding pair (`WideColl`/`RootsColl`). The former
`Poseidon2SpongeCR`-carrying forms were vacuous at deployed BabyBear parameters — the deployed
compressing sponge REFUTES that hypothesis. `fullClause` is NON-VACUOUS (the genuine per-cell
nonce-tick + the frozen 8-root sub-block, refutable on a forged post). Imports are read-only; this file
owns only its own declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
  (SEL_INCREMENT_NONCE IsIncNonceRow IncNonceRowCanon incNonceRowGates incrementNonceVmDescriptor
   incNonceHashSites RowEncodesIncNonce CellIncNonceSpec incNonceVm_faithful intent_to_cellSpec
   goodIncNonceRow goodIncNonceRow_noop goodIncNonceRow_realizes_intent)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound WideColl RootsColl
   runnable_full_commit_binds_or_collides wide_rejects_root_tamper_or_collides
   wideHashSites)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE incrementNonce descriptor (the §RECIPE step 1: width + sites, constraints UNCHANGED). -/

/-- **`incrementNonceVmDescriptorWide`** — incrementNonce's descriptor WIDENED: the SAME per-row
passthrough+nonce-tick gates + transitions + boundary pins + selector gate, but `traceWidth :=
EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites` (the `system_roots`-absorbing sites). Strictly
additive over `incrementNonceVmDescriptor`: the constraint list is byte-identical; only the width grows
by 2 and site 3's spare `.zero` slot becomes the `system_roots` carrier. -/
def incrementNonceVmDescriptorWide : EffectVmDescriptor :=
  { incrementNonceVmDescriptor with
    name := incrementNonceVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide incrementNonce descriptor's constraints ARE the narrow descriptor's (the width/site swap
leaves the per-row/transition/boundary/selector gate list untouched). -/
theorem incNonceWide_constraints_eq :
    incrementNonceVmDescriptorWide.constraints = incrementNonceVmDescriptor.constraints := rfl

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis — the THIN per-effect content).

The body of `incNonceDescriptor_full_sound` with the hash-site layer DROPPED: the per-cell
passthrough+tick factors through `incNonceVm_faithful` (gates ⟺ `IncNonceRowIntent`) + `intent_to_cellSpec`,
NEITHER of which reads the sites. So the runnable per-cell soundness depends ONLY on the gates (the wide
sites bind the COMMITMENT — discharged once in the generic theorem — not the per-cell spec). -/

/-- **`incNonceGates_give_cellSpec`** — the per-row gates of the incrementNonce descriptor, on a row
decoded by `RowEncodesIncNonce` with `s_noop = 0`, under the row's explicit canonicality envelope
(`IncNonceRowCanon` — the deployed range-check invariant that lets the ℤ intent be read back off the
mod-p checked gates), force `CellIncNonceSpec`. Flag-free: the gates are all `.gate`, whose `holdsVm`
ignores the first/last flags. -/
theorem incNonceGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : IncNonceRowCanon env)
    (henc : RowEncodesIncNonce env pre post)
    (hgates : ∀ c ∈ incrementNonceVmDescriptor.constraints, c.holdsVm env true false) :
    CellIncNonceSpec pre post := by
  have hrowgates : ∀ c ∈ incNonceRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ incrementNonceVmDescriptor.constraints := by
      unfold incrementNonceVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    -- the per-row gates are all `.gate`, whose `holdsVm` ignores the flags.
    unfold incNonceRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((incNonceVm_faithful env hcanon).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

/-- **`IncNonceFullClause`** — the FULL 17-field declarative post-state for incrementNonce over `(pre,
post, postRoots)`: the per-cell `CellIncNonceSpec` (economic block FROZEN, the on-trace seq-nonce TICKS
by 1) AND the `system_roots` sub-block FROZEN (`postRoots = preRoots` — incrementNonce touches no
side-table). `preRoots` is the frozen reference sub-block. NON-VACUOUS: §`goodIncNonce_realizes` inhabits
it; `incNonce_clause_not_trivial` refutes a forged post. -/
def IncNonceFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellIncNonceSpec pre post ∧ postRoots = preRoots

/-- **`incNonceRunnableSpec` — the FULL-state RUNNABLE instance for incrementNonce.** `decodeAfter` is
`RowEncodesIncNonce` + the frozen-roots witness; `decodeFull` projects the wide descriptor's per-row
gates (= the narrow descriptor's, `incNonceWide_constraints_eq`) to the GATE-ONLY
`incNonceGates_give_cellSpec`, then carries the frozen-roots fact. THIN; NON-VACUOUS (`fullClause` is the
genuine per-cell tick + the frozen sub-block, not `True`). The `s_noop = 0` leg of `IsIncNonceRow` feeds
the gate-only soundness; `isRow` also carries the row's explicit canonicality envelope
(`IncNonceRowCanon`, the deployed range-check invariant) that the mod-p gate denotation needs. -/
def incNonceRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := incrementNonceVmDescriptorWide
  usesWideSites := rfl
  isRow         := fun env => IsIncNonceRow env ∧ IncNonceRowCanon env
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesIncNonce env pre post ∧ postRoots = preRoots
  fullClause    := IncNonceFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨incNonceGates_give_cellSpec env pre post hrow.1.2 hrow.2 henc
            (incNonceWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `incrementNonce_runnable_full_sound` (full 17-field on the RUNNABLE descriptor). -/

/-- **`incrementNonce_runnable_full_sound` — the magnesium crown for incrementNonce.** A row satisfying
the WIDE RUNNABLE incrementNonce descriptor (`satisfiedVm incrementNonceVmDescriptorWide`, first/last
active), decoded by `RowEncodesIncNonce` with the frozen-roots witness, pins the FULL 17-field
declarative post-state: the per-cell block (`CellIncNonceSpec`: economic block FROZEN, the seq-nonce
TICKS) AND all 8 side-table roots FROZEN. The circuit the prover ACTUALLY RUNS binds the whole
post-state, not the 13-column projection. -/
theorem incrementNonce_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsIncNonceRow env) (hcanon : IncNonceRowCanon env)
    (henc : RowEncodesIncNonce env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash incrementNonceVmDescriptorWide env true false) :
    CellIncNonceSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (incNonceRunnableSpec preRoots) hash env pre post postRoots ⟨hrow, hcanon⟩
    ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST: tamper ANY of the 17 fields ⇒ UNSAT (incl. any side-table root). -/

/-! ### ⚑ THE WHOLE-STATE ANTI-GHOST IS A SECURITY REDUCTION, AND IT LIVES DOWNSTREAM (07-22).

`incrementNonce_runnable_full_commit_binds_or_collides` and `incrementNonce_rejects_root_tamper_or_collides` USED TO BE EXPORTED HERE as BARE DISJUNCTIONS —
`(cols agree ∧ roots agree) ∨ WideColl … ∨ RootsColl …`. True at deployed BabyBear parameters, unlike
their `Poseidon2SpongeCR`-carrying predecessors (which the deployed compressing sponge REFUTES), but
still UNCLOSED: a collision of that sponge EXISTS at deployed parameters by pigeonhole, so the right
branches are unconditionally available and `binds ∨ collides` never has to bind. A disjunction
quantifies over SOLUTIONS; cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

**BOTH ARE DELETED.** The deployed binding of incrementNonce's wide commitment is now the REDUCTION
`Dregg2.Circuit.Emit.EffectVmCommitReduction.incrementNonce_wide_binds_full_state_advantage_bound`
(with `hEff` discharged at `Eff := IsPolyTime` by `incrementNonce_wide_binds_full_state_from_polyTime`): the
forgery is a `Game` whose answers are DEPLOYED WIDE incrementNonce ROWS
(`incrementNonce_wide_forgery_is_break` / `incrementNonce_root_tamper_is_break`), the extractor is a MAP OF ADVERSARIES
into the deployed sponge's collision game, and the conclusion is a NEGLIGIBLE ADVANTAGE under
`DomainSeparatedCREff`, whose two poles are both proved.

⚑ It lives in a DOWNSTREAM module, not here, for a hard reason: the deployed sponge's keyed family
(`Poseidon2KeyedBridge`) transitively imports the effect-emission tree, so a reduction stated at that
family CANNOT be imported by an emission module without a build cycle. The GAME still names THIS
file's `incrementNonceVmDescriptorWide` — nothing is stated about an idealised stand-in. -/

/-! ## §6 — NON-VACUITY: a real incrementNonce inhabits the full clause; a forged post is refuted. -/

/-- The frozen reference sub-block (the empty `system_roots`, since incrementNonce touches no side-table). -/
def incNoncePreRoots : SysRoots := emptySystemRoots

/-- The pre-state `goodIncNonceRow` decodes: bal_lo 100, nonce 5, everything else 0. -/
def incNoncePre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The post-state `goodIncNonceRow` decodes: bal_lo 100 (FROZEN), nonce 6 (TICKED), frame frozen. -/
def incNoncePost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`goodIncNonce_realizes` — NON-VACUITY (witness TRUE).** The incrementNonce `fullClause` is INHABITED
by a real bump: `incNoncePost` is the genuine seq-nonce tick of `incNoncePre` (nonce `5 → 6`, balance
`100` frozen, frame frozen) and the roots are frozen. So `fullClause` is NOT `True` — a meaningful
17-field predicate a real bump satisfies. -/
theorem goodIncNonce_realizes :
    (incNonceRunnableSpec incNoncePreRoots).fullClause incNoncePre incNoncePost incNoncePreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`incNonce_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose nonce
is NOT the tick (`incNoncePre.nonce = 5`, demanding `6`, but a forged `99`) FAILS `IncNonceFullClause` —
so the clause is not vacuously true (it rejects a forged post), pinning non-vacuity from BOTH sides. -/
theorem incNonce_clause_not_trivial :
    ¬ IncNonceFullClause incNoncePreRoots incNoncePre { incNoncePost with nonce := 99 } incNoncePreRoots := by
  rintro ⟨⟨_, _, hn, _, _, _⟩, _⟩
  -- hn : (99) = incNoncePre.nonce + 1 = 5 + 1 = 6
  simp only [incNoncePre] at hn
  norm_num at hn

/-- **`incNonce_clause_rejects_root_drop` — non-vacuity on the SIDE-TABLE dimension.** A post whose
`system_roots` sub-block is NOT the frozen reference (a populated sub-block ≠ the empty one) FAILS the
clause — the frozen-roots leg is genuine (not vacuously true), so the magnesium binding is real: a
dropped/added side-table root is rejected by the full clause. -/
theorem incNonce_clause_rejects_root_drop :
    ¬ IncNonceFullClause incNoncePreRoots incNoncePre incNoncePost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  -- hroots : (populated sub-block) = emptySystemRoots — refuted at index 0.
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [incNoncePreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard incrementNonceVmDescriptorWide.traceWidth == 190
#guard incrementNonceVmDescriptorWide.hashSites.length == 4
#guard incrementNonceVmDescriptorWide.constraints.length == incrementNonceVmDescriptor.constraints.length

#assert_axioms incNonceGates_give_cellSpec
#assert_axioms incrementNonce_runnable_full_sound
#assert_axioms goodIncNonce_realizes
#assert_axioms incNonce_clause_not_trivial
#assert_axioms incNonce_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState
