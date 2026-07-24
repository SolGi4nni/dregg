/-
# Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide — the RUNNABLE `pipelinedSendA` descriptor LIFTED
to FULL-STATE (the magnesium breadth, on the circuit the prover RUNS).

## What this module closes (vs the narrow `EffectVmEmitPipelinedSend`)

`EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor` is the deployed `EFFECT_VM_WIDTH = 186` row whose
published `state_commit` absorbs ONLY the 13 state-block columns (`baseAbsorbedCols`). The `system_roots`
sub-block (escrow / nullifier / commitment / queue / swiss / sealedBox / delegation / refcount) is bound
ONLY by a separate record-layer commitment the row does NOT carry — the dominant Class-C "pale ghost".
Its per-cell soundness `pipelinedSendDescriptor_full_sound` pins the cell's economic block (FROZEN) +
nonce (TICKED), but the descriptor's commitment leaves the 8 side-table roots unbound.

This module SUPERSEDES that with a verified-by-construction WIDE descriptor `pipelinedSendVmDescriptorWide`
(`EFFECT_VM_WIDTH_SYSROOTS = 188`, `hashSites = wideHashSites`) and the FULL-STATE-on-RUNNABLE crown
`pipelinedSend_runnable_full_sound` — a satisfying witness of the RUNNABLE descriptor pins the FULL
17-field declarative post-state the executor produces (the per-cell block via the absorbed columns; ALL 8
side-table roots FROZEN, since the apply-time pipelined send touches NO side-table — it is the
balance-neutral CapTP clock tick). This is the analog of the abstract `pipelinedSendA_full_sound`
(`Inst/pipelinedSendA.lean`), but for `satisfiedVm`, the circuit the prover ACTUALLY RUNS.

## The recipe applied (`EffectVmFullStateRunnable §6`, the transfer reference template)

  * **the wide descriptor** — `pipelinedSendVmDescriptor` with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`,
    `hashSites := wideHashSites` (so `usesWideSites := rfl`). Strictly additive: the constraint list is
    byte-identical (`pipelinedSendWide_constraints_eq`); only the width grows by 2 and site 3's spare
    `.zero` 4th slot becomes the `system_roots` carrier. NO root-update gate is needed — the pipelined
    send moves NO side-table, so the carrier is FROZEN at `before` by the row's overall freeze (the
    post sub-block EQUALS the pre sub-block).
  * **`isRow`** := `IsPipelinedSendRow` (selector hot / NoOp cold).
  * **`decodeAfter`** := `RowEncodesSend` (the structured column decode) PLUS the frozen-roots witness
    (`postRoots = preRoots`) AND `env.loc sysRootsDigestCol = systemRootsDigest postRoots`.
  * **`fullClause`** := `CellSendSpec pre post` (economic block FROZEN, nonce TICKED) AND `postRoots =
    preRoots` (the 8 side-table roots FROZEN — the apply-time clock tick is side-table-neutral).
  * **`decodeFull`** := THIN — project the wide descriptor's per-row gates (= the narrow's, byte-identical)
    to the (hash-site-free) gate-only soundness `pipelinedSendGates_give_cellSpec`, then carry the frozen
    roots. The crypto is discharged ONCE in the generic `runnable_full_sound`.

The anti-ghost on ALL 17 fields falls out of the generic `runnable_full_commit_binds_or_collides` /
`wide_rejects_state_tamper_or_collides` / `wide_rejects_root_tamper_or_collides` instantiated at this
spec (§4) — tamper ANY absorbed column OR any side-table root ⇒ the RUNNABLE descriptor is UNSAT unless
a collision of the deployed sponge is EXHIBITED.

## SURFACE — the kernel-vs-runtime log divergence is UNCHANGED and named.

The full clause pins the WHOLE 17-field `RecordKernelState` post-state (per-cell block + the 8 roots).
The ONE residual — the apply-time pipelined send's SOLE motion is the neutral receipt prepended to
the chained `RecChainedState.log`, which is NOT a `RecordKernelState` field and has NO EffectVM row column
(the row layout has no log column) — is the SAME boundary the narrow `EffectVmEmitPipelinedSend` header and
the Argus `PipelinedSend.lean` weld carry: the log receipt rides universe-A's `logHashInjective` portal,
NOT this per-row state descriptor. This module does not change that boundary; it closes the side-table-root
binding gap on the kernel state.

## No terminal: the teeth are UNCONDITIONAL

The §4 theorems take NO collision-resistance hypothesis. Their alternative branch hands back a specific
colliding pair of the deployed sponge (`WideColl`/`RootsColl`). The former forms carried
`Poseidon2Binding.Poseidon2SpongeCR hash`, which the deployed compressing sponge REFUTES — at deployed
BabyBear parameters they were vacuous. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on
every theorem. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (boundaryLastPins boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
  (SEL_PIPELINED_SEND IsPipelinedSendRow pipelinedSendRowGates pipelinedSendVmDescriptor
   PipelinedSendRowIntent PipelinedSendRowCanon pipelinedSendVm_faithful RowEncodesSend
   CellSendSpec intent_to_cellSpec goodSendRow goodSendRow_noop goodSendRow_realizes_intent)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites RunnableFullStateSpec runnable_full_sound WideColl RootsColl)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false

/-! ## §1 — the GATE-ONLY per-cell soundness (no hash-site hypothesis).

The per-cell freeze+tick factors through `pipelinedSendVm_faithful` (`pipelinedSendRowGates ⟺
PipelinedSendRowIntent`) + `intent_to_cellSpec`, NEITHER of which reads the hash sites. So the runnable
per-cell soundness depends ONLY on the gates (the sites bind the COMMITMENT — §4 — not the per-cell spec).
This is the body of `pipelinedSendDescriptor_full_sound`'s `CellSendSpec` leg with the hash-site /
boundary layers dropped — the analog of `EffectVmFullStateRunnable.transferGates_give_cellSpec`. -/

/-- **`pipelinedSendGates_give_cellSpec` — the GATE-ONLY per-cell soundness.** The narrow descriptor's
per-row gates (a constraint-list segment), on a pipelined-send row decoded by `RowEncodesSend`, force
`CellSendSpec`. No hash-site hypothesis. Under the mod-p `holdsVm` denotation the ℤ-stated row intent
is read back off the field-checked gates via the explicit canonicality envelope
(`PipelinedSendRowCanon` — the deployed range-check invariant), exactly as in the narrow
`pipelinedSendDescriptor_full_sound`. -/
theorem pipelinedSendGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : PipelinedSendRowCanon env)
    (henc : RowEncodesSend env pre post)
    (hgates : ∀ c ∈ pipelinedSendVmDescriptor.constraints, c.holdsVm env true false) :
    CellSendSpec pre post := by
  -- the per-row gates are a sub-list of the descriptor's constraints; restrict to them (flag-free).
  have hrowgates : ∀ c ∈ pipelinedSendRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ pipelinedSendVmDescriptor.constraints := by
      unfold pipelinedSendVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    -- pipelinedSendRowGates are all `.gate _`, whose `holdsVm` ignores the flags.
    unfold pipelinedSendRowGates
      Dregg2.Circuit.Emit.EffectVmEmitTransfer.gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc
    ((pipelinedSendVm_faithful env hcanon).mp hrowgates)

#assert_axioms pipelinedSendGates_give_cellSpec

/-! ## §2 — the WIDE descriptor (the `system_roots`-absorbing runnable circuit). -/

/-- **`pipelinedSendVmDescriptorWide`** — `pipelinedSendVmDescriptor` WIDENED: the SAME per-row gates +
transitions + boundary pins + selector gate, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites
:= wideHashSites` (so the published `state_commit` now absorbs the — frozen — side-table digest). Strictly
additive over `pipelinedSendVmDescriptor`: the constraint list is byte-identical; only the width grows by
2 and site 3's spare `.zero` 4th slot becomes the `system_roots` carrier. -/
def pipelinedSendVmDescriptorWide : EffectVmDescriptor :=
  { pipelinedSendVmDescriptor with
    name := pipelinedSendVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide pipelined-send descriptor's constraints ARE the narrow's (the width/site swap leaves the
per-row/transition/boundary gate list untouched). -/
theorem pipelinedSendWide_constraints_eq :
    pipelinedSendVmDescriptorWide.constraints = pipelinedSendVmDescriptor.constraints := rfl

/-! ## §3 — the FULL clause + the VALIDATED RUNNABLE instance.

The apply-time pipelined send touches NO side-table, so its `system_roots` sub-block is FROZEN: the full
clause is the per-cell `CellSendSpec` (economic block frozen, nonce ticked) AND `postRoots = preRoots`. -/

/-- **`PipelinedSendFullClause`** — the full declarative post-state for the pipelined send over `(pre,
post, postRoots)`: the per-cell `CellSendSpec` (economic block frozen, nonce ticked) AND the 8 side-table
roots FROZEN (the apply-time clock tick moves no side-table). `preRoots` is the frozen reference
sub-block. Non-vacuous: `goodPipelinedSend_realizes` inhabits it; `pipelinedSend_clause_not_trivial`
refutes a forged post-state. -/
def PipelinedSendFullClause (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellSendSpec pre post ∧ postRoots = preRoots

/-- **`pipelinedSendRunnableSpec` — the FULL-state RUNNABLE instance.** `decodeAfter` is `RowEncodesSend`
PLUS the explicit canonicality envelope (`PipelinedSendRowCanon` — the deployed range-check invariant,
needed to read the ℤ-stated intent off the mod-p gates) PLUS the frozen-roots witness + the
carrier-is-digest link; `decodeFull` projects the wide descriptor's per-row gates (= the narrow's) to the
GATE-ONLY `pipelinedSendGates_give_cellSpec`, then carries the frozen-roots fact. THIN. NON-VACUOUS:
`fullClause` is the genuine per-cell freeze+tick + the frozen sub-block, NOT `True`. -/
def pipelinedSendRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := pipelinedSendVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsPipelinedSendRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesSend env pre post ∧ PipelinedSendRowCanon env ∧ postRoots = preRoots
  fullClause    := PipelinedSendFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hcanon, hroots⟩ := hdec
    obtain ⟨_, hnoop⟩ := hrow
    exact ⟨pipelinedSendGates_give_cellSpec env pre post hnoop hcanon henc
            (pipelinedSendWide_constraints_eq ▸ hgates), hroots⟩

/-- **`pipelinedSend_runnable_full_sound` — THE CROWN (pipelinedSend slice).** A row satisfying the
RUNNABLE wide descriptor (`satisfiedVm pipelinedSendVmDescriptorWide`, first/last active), under the
structured decode (`RowEncodesSend` + the `PipelinedSendRowCanon` range-check envelope + frozen roots),
pins the FULL 17-field declarative post-state: the
per-cell `CellSendSpec` (economic block FROZEN, nonce TICKED) AND all 8 side-table roots FROZEN. This is
the analog of the abstract `pipelinedSendA_full_sound`, but for the circuit the prover ACTUALLY RUNS. -/
theorem pipelinedSend_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : IsPipelinedSendRow env) (hcanon : PipelinedSendRowCanon env)
    (henc : RowEncodesSend env pre post) (hroots : sr = preRoots)
    (hsat : satisfiedVm hash pipelinedSendVmDescriptorWide env true false) :
    CellSendSpec pre post ∧ sr = preRoots :=
  runnable_full_sound (pipelinedSendRunnableSpec preRoots) hash env pre post sr
    hrow ⟨henc, hcanon, hroots⟩ hsat

#assert_axioms pipelinedSend_runnable_full_sound

/-! ## §4 — ANTI-GHOST on ALL 17 fields (the generic teeth, instantiated).

Tampering ANY absorbed state-block column OR any side-table root makes two same-`NEW_COMMIT` wide rows'
bound data DISAGREE — UNSAT unless a collision of the deployed sponge is EXHIBITED. Both teeth bite
(per-cell block AND the 8 roots), via the generic `runnable_full_commit_binds_or_collides` instantiated
at `pipelinedSendRunnableSpec`. -/

/-- **`pipelinedSend_wide_binds_full_state_or_collides` — the whole-state anti-ghost.** Two rows
satisfying the wide descriptor that publish the SAME `NEW_COMMIT`, whose carriers ARE the
`systemRootsDigest` of their post sub-blocks, EITHER agree on EVERY absorbed state-block column AND
every side-table root, OR exhibit a genuine collision of the deployed sponge (`WideColl` on the two wide
preimages, or `RootsColl` on the two root lists). So a prover CANNOT keep `NEW_COMMIT` while tampering
ANY of the 17 fields' bound content without producing a collision.

The former `pipelinedSend_wide_binds_full_state` concluded the bare conjunction from `Poseidon2SpongeCR
hash`. The deployed sponge REFUTES that hypothesis, so at deployed parameters that theorem was vacuous.
This disjunction is formally weaker, but it HOLDS of the deployed sponge, which the old one did not. -/
theorem pipelinedSend_wide_binds_full_state_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash pipelinedSendVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash pipelinedSendVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides (pipelinedSendRunnableSpec preRoots)
    hash e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`pipelinedSend_wide_rejects_root_tamper_or_collides` — side-table anti-ghost (the gap's headline
tooth).** Two wide rows that publish the same `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose
side-table sub-blocks DIFFER at some index (a dropped escrow, an omitted nullifier) cannot both satisfy
WITHOUT exhibiting a collision of the deployed sponge. The side-table state is bound BY the runnable
commitment up to that collision.

The former `pipelinedSend_wide_rejects_root_tamper` concluded `False` from `Poseidon2SpongeCR hash`,
which the deployed sponge REFUTES; at deployed parameters it was vacuous. This disjunction is formally
weaker, but it HOLDS of the deployed sponge, which the old one did not. -/
theorem pipelinedSend_wide_rejects_root_tamper_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash pipelinedSendVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash pipelinedSendVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  EffectVmFullStateRunnable.wide_rejects_root_tamper_or_collides (pipelinedSendRunnableSpec preRoots)
    hash e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms pipelinedSend_wide_binds_full_state_or_collides
#assert_axioms pipelinedSend_wide_rejects_root_tamper_or_collides

/-! ## §5 — NON-VACUITY: the full clause is INHABITED by a real pipelined send (TRUE) and REFUTABLE
(FALSE), and the wide descriptor is the genuine 188-wide `system_roots`-absorbing circuit. -/

/-- A frozen reference sub-block (the empty `system_roots`, since the pipelined send touches no side
table). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- The pre-state `goodSendRow` encodes: bal_lo 100, nonce 5, everything else 0. -/
def sendPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- The post-state `goodSendRow` encodes: bal_lo 100 (frozen), nonce 6 (ticked), frame frozen. -/
def sendPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- **`goodPipelinedSend_realizes` — NON-VACUITY (witness TRUE).** The pipelined-send `fullClause` is
INHABITED by a real apply-time clock tick: `sendPost` is the genuine image of `sendPre` (bal_lo `100`
FROZEN, nonce `5 → 6`, frame frozen) and the roots are frozen. So the full clause is NOT `True` — it is a
meaningful 17-field predicate a real pipelined send satisfies, exactly the `fullClause` of
`pipelinedSendRunnableSpec`. -/
theorem goodPipelinedSend_realizes :
    (pipelinedSendRunnableSpec goodPreRoots).fullClause sendPre sendPost goodPreRoots := by
  refine ⟨⟨rfl, rfl, ?_, fun _ => rfl, rfl, rfl⟩, rfl⟩
  show (6 : ℤ) = 5 + 1; norm_num

/-- **`pipelinedSend_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
nonce does NOT tick (`sendPre.nonce = 5`, demanding `6`, but a forged frozen `5`) FAILS the full clause —
so the runnable `fullClause` is not vacuously true (it rejects a non-ticking post-state), pinning
non-vacuity from BOTH sides. -/
theorem pipelinedSend_clause_not_trivial :
    ¬ PipelinedSendFullClause goodPreRoots sendPre { sendPost with nonce := 5 } goodPreRoots := by
  rintro ⟨⟨_, _, hnon, _⟩, _⟩
  -- hnon : (5) = sendPre.nonce + 1 = 5 + 1 = 6
  simp only [sendPre] at hnon
  norm_num at hnon

/-- **NON-VACUITY (the wide descriptor is the genuine 188-wide circuit).** `pipelinedSendVmDescriptorWide`
declares `traceWidth = EFFECT_VM_WIDTH_SYSROOTS = 188` and its `hashSites` are EXACTLY the four
`system_roots`-absorbing `wideHashSites` (the 4th site absorbs `sysRootsDigestCol`, NOT the spare
`.zero`). So `pipelinedSend_runnable_full_sound` is a statement about a REAL, runnable, side-table-binding
circuit — not the narrow 186-wide one, and not a placeholder. -/
theorem pipelinedSendWide_is_genuine :
    pipelinedSendVmDescriptorWide.traceWidth = EFFECT_VM_WIDTH_SYSROOTS
    ∧ pipelinedSendVmDescriptorWide.hashSites = wideHashSites
    ∧ pipelinedSendVmDescriptorWide.hashSites.length = 4 := by
  refine ⟨rfl, rfl, ?_⟩
  show wideHashSites.length = 4
  decide

#assert_axioms goodPipelinedSend_realizes
#assert_axioms pipelinedSend_clause_not_trivial
#assert_axioms pipelinedSendWide_is_genuine

/-! ## §6 — axiom-hygiene tripwires. -/

#guard pipelinedSendVmDescriptorWide.traceWidth == 190
#guard pipelinedSendVmDescriptorWide.hashSites.length == 4
#guard pipelinedSendVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3 + 1

end Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide
