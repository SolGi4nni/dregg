/-
# Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState — makeSovereign LIFTED to FULL-STATE on the
RUNNABLE descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitMakeSovereign`'s RUNNABLE row DROPS the readable economic block to ZERO (the rebind hides
the record behind the sovereign commitment): `makeSovereignRowGates` force `state_after[off] = 0` for
every economic-data column, and the 4 GROUP-4 sites bind that zero block into `state_commit`. But that
commitment absorbs only the 13 state-block columns, NOT the 8 side-table roots. This module CLOSES that
by amplifying the RUNNABLE descriptor to the WIDE (`system_roots`-absorbing) shape and lifting through
the generic `EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness
pins the FULL 17-field declarative post-state — the per-cell DROPPED block (`ZeroBlockSpec`: every
economic column zero) AND every one of the 8 side-table roots FROZEN (makeSovereign touches no side-table
in the RUNNABLE row). The anti-ghost tooth bites on all 17 (incl. any root): a tamper either moves
`state_commit` or exhibits a named collision of the deployed sponge (`WideColl`/`RootsColl`).

The `cap_root` column is among the dropped (absorbed) columns, so a `cap_root` tamper is anti-ghosted;
the cap-graph MEMBERSHIP stays the named opaque digest (a refinement, not a soundness gap). The §RECIPE
applied to makeSovereign.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; NO hash hypothesis — the anti-ghost keystones
are unconditional disjunctions naming the sponge collision they would need.
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
  (SEL_MAKESOVEREIGN makeSovereignRowGates makeSovereignVmDescriptor DroppedBlockIntent
   makeSovereignVm_faithful)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds_or_collides
   wide_rejects_root_tamper_or_collides WideColl RootsColl wideHashSites)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE makeSovereign descriptor (width + sites; constraints UNCHANGED). -/

def makeSovereignVmDescriptorWide : EffectVmDescriptor :=
  { makeSovereignVmDescriptor with
    name := makeSovereignVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem makeSovWide_constraints_eq :
    makeSovereignVmDescriptorWide.constraints = makeSovereignVmDescriptor.constraints := rfl

/-- The row hypothesis: a makeSovereign row (`s_makeSovereign = 1`). -/
def IsMakeSovereignRow (env : VmRowEnv) : Prop :=
  env.loc SEL_MAKESOVEREIGN = 1

/-! ## §2 — the structured post decode + the DROPPED-block spec. -/

/-- `RowEncodesMakeSov env post` ties the row's `state_after` block to a concrete post-`CellState`. The
PRE block is unconstrained (the rebind's post does not depend on the readable pre). -/
def RowEncodesMakeSov (env : VmRowEnv) (post : CellState) : Prop :=
  env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- **`ZeroBlockSpec post`** — the per-cell FULL-state dropped-block spec: every economic-data column of
`post` is ZERO as a field value (mod-`p` congruent to `0`; canonical `[0, p)` cells make this exact) —
the readable record dropped behind the sovereign commitment. -/
def ZeroBlockSpec (post : CellState) : Prop :=
  post.balLo ≡ 0 [ZMOD 2013265921]
  ∧ post.balHi ≡ 0 [ZMOD 2013265921]
  ∧ post.nonce ≡ 0 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ 0 [ZMOD 2013265921])
  ∧ post.capRoot ≡ 0 [ZMOD 2013265921]
  ∧ post.reserved ≡ 0 [ZMOD 2013265921]

theorem intent_to_zeroSpec (env : VmRowEnv) (post : CellState)
    (henc : RowEncodesMakeSov env post) (hint : DroppedBlockIntent env) :
    ZeroBlockSpec post := by
  obtain ⟨hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo]; exact hbal
  · rw [← hsaHi]; exact hbhi
  · rw [← hsaN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i]; exact this
  · rw [← hsaCap]; exact hcap
  · rw [← hsaRes]; exact hres

/-! ## §3 — the GATE-ONLY soundness (no hash-site hypothesis). -/

theorem makeSovGates_give_zeroSpec (env : VmRowEnv) (post : CellState)
    (henc : RowEncodesMakeSov env post)
    (hgates : ∀ c ∈ makeSovereignVmDescriptor.constraints, c.holdsVm env true false) :
    ZeroBlockSpec post := by
  have hrowgates : ∀ c ∈ makeSovereignRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ makeSovereignVmDescriptor.constraints := by
      unfold makeSovereignVmDescriptor; exact hc
    have hh := hgates c hmem
    -- every constraint is a `gZero _` = `.gate (eSA _)`; `holdsVm` of a gate ignores the flags.
    unfold makeSovereignRowGates Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign.gZero at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_zeroSpec env post henc ((makeSovereignVm_faithful env).mp hrowgates)

/-! ## §4 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

/-- **`MakeSovFullClause`** — the FULL 17-field declarative post for makeSovereign: the per-cell DROPPED
block (`ZeroBlockSpec`: every economic column zero) AND the `system_roots` sub-block FROZEN. The `pre`
argument is unconstrained (the dropped block does not depend on the readable pre). NON-VACUOUS. -/
def MakeSovFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  ZeroBlockSpec post ∧ postRoots = preRoots

def makeSovRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := makeSovereignVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsMakeSovereignRow
  decodeAfter   := fun env _pre post postRoots =>
    RowEncodesMakeSov env post ∧ postRoots = preRoots
  fullClause    := MakeSovFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨makeSovGates_give_zeroSpec env post henc
            (makeSovWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §5 — THE DELIVERABLE: `makeSovereign_runnable_full_sound`. -/

/-- **`makeSovereign_runnable_full_sound` — the magnesium crown for makeSovereign.** A row satisfying the
WIDE RUNNABLE descriptor, decoded by `RowEncodesMakeSov` with the frozen-roots witness, pins the FULL
17-field post-state: the per-cell DROPPED block (`ZeroBlockSpec`) AND all 8 side-table roots FROZEN. -/
theorem makeSovereign_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsMakeSovereignRow env)
    (henc : RowEncodesMakeSov env post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash makeSovereignVmDescriptorWide env true false) :
    ZeroBlockSpec post ∧ postRoots = preRoots :=
  runnable_full_sound (makeSovRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §6 — THE ANTI-GHOST. -/

/-- **`makeSovereign_runnable_full_commit_binds_or_collides` — the anti-ghost, UNCONDITIONALLY.** Two
satisfying WIDE makeSovereign rows publishing the SAME `NEW_COMMIT`, whose `sysRootsDigestCol` carriers
ARE the `systemRootsDigest` of `sr₁`/`sr₂`, EITHER agree on all 12 absorbed state-block columns AND on
every side-table root, OR exhibit a genuine collision of the deployed sponge — on the state block
(`WideColl`) or on the ordered root list (`RootsColl`).

The old form concluded the bare conjunction from `Poseidon2SpongeCR hash`, which the deployed BabyBear
sponge REFUTES, so at deployed parameters it was vacuous. This disjunction is formally weaker and holds
of the deployed sponge. -/
theorem makeSovereign_runnable_full_commit_binds_or_collides (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash makeSovereignVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash makeSovereignVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  runnable_full_commit_binds_or_collides (makeSovRunnableSpec preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`makeSovereign_rejects_root_tamper_or_collides`.** Two satisfying WIDE makeSovereign rows publishing
the same `NEW_COMMIT` that DISAGREE on some side-table root exhibit a genuine collision of the deployed
sponge — so a root tamper is UNSAT unless the prover holds a sponge collision.

The old form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed BabyBear sponge REFUTES,
so at deployed parameters it was vacuous. This form names what the tamper costs and holds of the deployed
sponge. -/
theorem makeSovereign_rejects_root_tamper_or_collides (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash makeSovereignVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash makeSovereignVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_root_tamper_or_collides (makeSovRunnableSpec preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §7 — NON-VACUITY. -/

def makeSovPreRoots : SysRoots := emptySystemRoots

/-- An arbitrary pre (unconstrained). -/
def makeSovPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The dropped post-block: every economic column ZERO. -/
def makeSovPost : CellState :=
  { balLo := 0, balHi := 0, nonce := 0, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodMakeSov_realizes :
    (makeSovRunnableSpec makeSovPreRoots).fullClause makeSovPre makeSovPost makeSovPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **NON-VACUITY (witness FALSE).** A post whose `bal_lo` is NOT dropped to zero (`999`) FAILS the
clause — the drop-to-zero is genuine. -/
theorem makeSov_clause_not_trivial :
    ¬ MakeSovFullClause makeSovPreRoots makeSovPre { makeSovPost with balLo := 999 } makeSovPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [makeSovPost] at hbal
  unfold Int.ModEq at hbal
  omega

theorem makeSov_clause_rejects_root_drop :
    ¬ MakeSovFullClause makeSovPreRoots makeSovPre makeSovPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [makeSovPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §8 — layout + axiom-hygiene tripwires. -/

#guard makeSovereignVmDescriptorWide.traceWidth == 190
#guard makeSovereignVmDescriptorWide.hashSites.length == 4
#guard makeSovereignVmDescriptorWide.constraints.length == makeSovereignVmDescriptor.constraints.length

#assert_axioms intent_to_zeroSpec
#assert_axioms makeSovGates_give_zeroSpec
#assert_axioms makeSovereign_runnable_full_sound
#assert_axioms makeSovereign_runnable_full_commit_binds_or_collides
#assert_axioms makeSovereign_rejects_root_tamper_or_collides
#assert_axioms goodMakeSov_realizes
#assert_axioms makeSov_clause_not_trivial
#assert_axioms makeSov_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState
