/-
# Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign — the `makeSovereign` effect's EffectVM-row circuit,
  EMITTED.

`makeSovereign` is SPECIAL (the mandate work flagged it): a FULL record-REBIND of the target cell. It
DROPS the target's entire readable record and installs a COMMITMENT-ONLY record
`[(commitmentField, .dig (stateCommitment (base target)))]` — the cell's prior state collapses behind a
single sovereign commitment. Its FULL universe-A soundness is
`Inst.MakeSovereignA.makeSovereignA_full_sound ⇒ MakeSovereignSpec` (the EffectSpec layer; all 17
kernel fields + log, `cell` the ONE touched component rebound via `sovereignRebind`, every other field
frozen).

## What the EffectVM row CAN pin (the genuine economic consequence of the rebind)

Because the readable record is DROPPED behind a commitment, the target cell's READABLE `balance` field
is GONE — so `balOf (sovereignRebind base target target) = 0` (the commitment-only record carries no
`balance` field). The EffectVM economic block of the TARGET cell therefore becomes the ZERO block
post-rebind. The row pins:

  * the post economic block is the all-zero block (the readable balance/frame are dropped);
  * that zero block is bound into the published `state_commit` under Poseidon2 CR (the anti-ghost
    tooth — but see the boundary: this is the EffectVM Poseidon2 digest, NOT the universe-A
    `stateCommitment` the rebind actually installs).

## What the EffectVM row CANNOT enforce (the boundary — the WHOLE point of the rebind)

`makeSovereign` REPLACES the dropped state with `stateCommitment (base target)` — the universe-A
state-commitment of the WHOLE pre-record. The EffectVM `state_commit` column is a DIFFERENT commitment
function (the Poseidon2 H4-of-H4 of the after-block), so the row's commitment does NOT witness that the
PRE-record was committed under `stateCommitment`. Concretely:

  * the INSTALL of the `commitmentField := stateCommitment(pre)` record — the universe-A commitment of
    the dropped pre-state — is OFF-ROW (the EffectVM block has no column carrying `stateCommitment`);
  * the self-targeted receipt; the self-authority guard.

So the row witnesses that the readable balance was ZEROED by the rebind, but NOT that the dropped state
was sovereign-committed. The rebind SOUNDNESS lives ONLY in `makeSovereignA_full_sound`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the commitment tooth is UNCONDITIONAL
(an extraction-as-data disjunction), never conditioned on the (refuted) injective sponge floor.
Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Emit.EffectVmKeyedStateCommit
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA site0 site1 site2 eqToModEq gate_modEq_iff
  not_modEq_zero_of_canon)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (sovereignRebind commitmentField stateCommitment)
open Dregg2.Circuit.Spec.SovereignCommitment

set_option linter.unusedVariables false

/-! ## §0 — the `makeSovereign` selector column (local). -/

/-- The `makeSovereign` selector column index. -/
def SEL_MAKESOVEREIGN : Nat := 6

/-! ## §1 — the DROPPED-TO-ZERO per-row gates (the target's readable economic block is zeroed). -/

/-- The drop-to-zero gate for state-block column `off`: `state_after[off] = 0`. -/
def gZero (off : Nat) : VmConstraint := .gate (eSA off)

/-- The 13 drop-to-zero gates (every economic-data column of the rebound block). -/
def makeSovereignRowGates : List VmConstraint :=
  [ gZero state.BALANCE_LO, gZero state.BALANCE_HI, gZero state.NONCE
  , gZero state.CAP_ROOT, gZero state.RESERVED ]
  ++ (List.range 8).map (fun i => gZero (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def makeSovereignHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted descriptor. -/

def makeSovereignVmAirName : String := "dregg-effectvm-makesovereign-v1"

/-- **`makeSovereignVmDescriptor`** — the `makeSovereign` EffectVM-row circuit: the 13 drop-to-zero
gates (the rebind drops the readable economic block) + the 4 ordered GROUP-4 hash sites binding the
zero block into `state_commit`. -/
def makeSovereignVmDescriptor : EffectVmDescriptor :=
  { name := makeSovereignVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := makeSovereignRowGates
  , hashSites := makeSovereignHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the DROPPED-BLOCK row intent. -/

/-- **`DroppedBlockIntent env`** — the row's post-block is the all-zero economic block (the readable
record is dropped behind the sovereign commitment). The EffectVM-row projection of the rebind's
balance-drop. -/
def DroppedBlockIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) ≡ 0 [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ 0 [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE) ≡ 0 [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ 0 [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ 0 [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) ≡ 0 [ZMOD 2013265921])

/-! ## §5 — FAITHFULNESS. -/

theorem makeSovereignVm_faithful (env : VmRowEnv) :
    (∀ c ∈ makeSovereignRowGates, c.holdsVm env false false) ↔ DroppedBlockIntent env := by
  unfold makeSovereignRowGates DroppedBlockIntent
  constructor
  · intro h
    have hLo := h (gZero state.BALANCE_LO) (by simp [gZero])
    have hHi := h (gZero state.BALANCE_HI) (by simp [gZero])
    have hN  := h (gZero state.NONCE) (by simp [gZero])
    have hCap := h (gZero state.CAP_ROOT) (by simp [gZero])
    have hRes := h (gZero state.RESERVED) (by simp [gZero])
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (gZero (state.FIELD_BASE + i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at hLo hHi hN hCap hRes
    refine ⟨hLo, hHi, hN, hCap, hRes, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at this
    exact this
  · rintro ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
    · exact hLo
    · exact hHi
    · exact hN
    · exact hCap
    · exact hRes
    · exact hFld i hi

/-! ## §6 — ANTI-GHOST. -/

theorem makeSovereignVm_rejects_nonzero (env : VmRowEnv) (hwrong : ¬ DroppedBlockIntent env) :
    ¬ (∀ c ∈ makeSovereignRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((makeSovereignVm_faithful env).mp h)

/-- **Anti-ghost (readable balance survived).** A row whose post-`bal_lo` is non-zero fails the
drop-to-zero gate — a sovereign rebind cannot leave the readable balance behind the commitment. -/
theorem makeSovereignVm_rejects_surviving_balance (env : VmRowEnv)
    (hcanon : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ 0) :
    ¬ (gZero state.BALANCE_LO).holdsVm env false false := by
  simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (b := 0) (by ring) hcanon (by norm_num) hwrong

/-! ## §7 — the commitment binding, REBUILT AS SECURITY REDUCTIONS.

⚑ **WHAT CHANGED AND WHY.** This section used to export
`makeSovereignVm_commit_binds_block_or_collides`, concluding
`absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂`. That form is TRUE of the deployed
sponge, but UNCLOSED: a collision of the deployed sponge EXISTS at BabyBear parameters by pigeonhole
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `binds ∨ collides` is satisfiable through
its RIGHT branch WITHOUT the binding ever holding. It quantified over SOLUTIONS; cryptographic
hardness quantifies over EFFICIENT ADVERSARIES. It is DELETED; the keyed-ROM closure below and the
`Eff`-parametric deployed-hash reduction after it are its successors. The extraction spine
(`absorbed_determined_by_commit_or_collides`) REMAINS in the transfer keystone as the
reduction-internal witness, its correct role. -/

open Dregg2.Circuit.Emit.EffectVmKeyedStateCommit Dregg2.Crypto.FloorGames
  Dregg2.Crypto.ConcreteSecurity in
/-- **⚑ THE KEYED-FLOOR CLOSURE at makeSovereign's own sites** (the honest successor of the
fraud-deleted `EffectVmCommitReduction` claim, whose `IsPolyTime` floor is REFUTED at deployed
parameters): in the LABELLED random-oracle idealization of the GROUP-4 surface
(`EffectVmKeyedStateCommit` — a MODELLING step, see that module's header), every QUERY-BOUNDED forger
producing two rows that satisfy THIS effect's hash sites with a shared commit column but different
absorbed 13-column state wins with NEGLIGIBLE probability — closed from the PROVED birthday floor
(`keyedRom_hard`); no `IsPolyTime`, no `Poseidon2SpongeCR`, no named-carrier hypothesis. The
deployed-hash leg is the `Eff`-parametric `_advantage_bound` reduction below (its
`boundaryLastPins` mod-`p` step is deployed-side content and deliberately does NOT transport to the
λ-wide model). -/
theorem makeSovereignVm_commit_binds_keyed (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (narrowBreakGame makeSovereignHashSites))
    (hA : NarrowBreakEff makeSovereignHashSites Q A) :
    Negl (gameAdv (narrowBreakGame makeSovereignHashSites) A) :=
  narrowStateCommit_binds makeSovereignHashSites rfl Q hQ A hA

/-- **`makeSovNarrowRowSpec`** — makeSovereign's narrow descriptor as the reduction's per-effect
datum: its hash sites ARE the deployed GROUP-4 sites (`rfl`). -/
def makeSovNarrowRowSpec : Dregg2.Circuit.Emit.EffectVmRowCommitReduction.NarrowRowSpec where
  descriptor := makeSovereignVmDescriptor
  usesTransferSites := rfl

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily carrierBreakToFinder) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant) in
open Dregg2.Crypto.ConcreteSecurity (Negl) in
/-- **⚑ `makeSovereignVm_binds_block_advantage_bound` — the DEPLOYED-hash reduction at
makeSovereign's own descriptor.** Under the deployed sponge's collision floor at the class `Eff`,
an adversary producing two rows BOTH ACCEPTED by `makeSovereignVmDescriptor` that publish one
`state_commit` while disagreeing on the absorbed state block has NEGLIGIBLE advantage. Replaces the
deleted bare disjunction. -/
theorem makeSovereignVm_binds_block_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (narrowRowBreakGame D makeSovNarrowRowSpec))
    (hEff : Eff (carrierBreakToFinder D group4Carrier
      (narrowRowToCarrier D makeSovNarrowRowSpec A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (narrowRowBreakGame D makeSovNarrowRowSpec) A) :=
  narrowRow_binds_advantage_bound D makeSovNarrowRowSpec Eff A hEff hCR

/-! ## §8 — the dropped record carries NO readable balance (the overlap with the executor).

The rebound cell IS the commitment-only record `[(commitmentField, .dig (stateCommitment(base)))]`,
which has NO `balance` field — so `balOf = 0`. We prove this from `sovereignRebindMap_correct`. -/

/-- **`sovereignRebind_balOf_zero` — the rebound cell carries `balance == 0`.** The target's rebound
record is commitment-only (`commitmentField ≠ balanceField`), so its `balOf` read fails closed to `0`:
the readable balance is dropped behind the commitment. -/
theorem sovereignRebind_balOf_zero (base : CellId → Value) (target : CellId) :
    balOf (sovereignRebind base target target) = 0 := by
  rw [(sovereignRebindMap_correct base target).1]
  -- balOf (.record [(commitmentField, .dig _)]) : the `balance` field is absent ⇒ 0
  rfl

/-! ## §9 — CONNECTOR to universe-A `MakeSovereignSpec` via `cellProj`. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`makeSovereign_target_dropped` — the OVERLAP, from the executor.** A committed `makeSovereign`
drops the target cell's readable economic block: the projected after-block of `cell` is the all-zero
economic block (the readable balance is dropped behind the sovereign commitment). So
`DroppedBlockIntent` is the executor's effect on the target's economic block. -/
theorem makeSovereign_target_dropped (s s' : RecChainedState) (actor cell : CellId)
    (hspec : MakeSovereignSpec s actor cell s') :
    (cellProj s'.kernel cell).balLo = 0
    ∧ (cellProj s'.kernel cell).balHi = 0
    ∧ (cellProj s'.kernel cell).nonce = 0
    ∧ (cellProj s'.kernel cell).capRoot = 0
    ∧ (cellProj s'.kernel cell).reserved = 0
    ∧ (∀ i, (cellProj s'.kernel cell).fields i = 0) := by
  -- MakeSovereignSpec: guard, cell (= sovereignRebind), log, frame...
  obtain ⟨_, hcellmap, _⟩ := hspec
  refine ⟨?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  show balOf (s'.kernel.cell cell) = 0
  rw [hcellmap]
  exact sovereignRebind_balOf_zero s.kernel.cell cell

/-- **`makeSovereign_row_matches_executor` — the CONNECTOR.** If the row's after-block decodes, the
gates hold, and the executor commits `MakeSovereignSpec`, the row's pinned post-block equals the
executor's dropped target block (all zero). -/
theorem makeSovereign_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ makeSovereignRowGates, c.holdsVm env false false)
    (s s' : RecChainedState) (actor cell : CellId)
    (hspec : MakeSovereignSpec s actor cell s') :
    post.balLo ≡ (cellProj s'.kernel cell).balLo [ZMOD 2013265921]
    ∧ post.balHi ≡ (cellProj s'.kernel cell).balHi [ZMOD 2013265921]
    ∧ post.capRoot ≡ (cellProj s'.kernel cell).capRoot [ZMOD 2013265921]
    ∧ post.reserved ≡ (cellProj s'.kernel cell).reserved [ZMOD 2013265921]
    ∧ (∀ i, post.fields i ≡ (cellProj s'.kernel cell).fields i [ZMOD 2013265921]) := by
  obtain ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ := (makeSovereignVm_faithful env).mp hgates
  obtain ⟨eLo, eHi, eN, eCap, eRes, eFld⟩ := makeSovereign_target_dropped s s' actor cell hspec
  obtain ⟨_, _, _, _, _, _, _, _, _, hsaLo, hsaHi, _, hsaF, hsaCap, hsaRes, _, _, _⟩ := henc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [eLo, ← hsaLo]; exact hLo
  · rw [eHi, ← hsaHi]; exact hHi
  · rw [eCap, ← hsaCap]; exact hCap
  · rw [eRes, ← hsaRes]; exact hRes
  · intro i; rw [eFld i, ← hsaF i]; exact hFld i.val i.isLt

/-! ## §10 — THE BOUNDARY: the sovereign-commitment INSTALL is OFF-ROW.

The rebind's defining act — installing `commitmentField := stateCommitment(pre)`, the universe-A
state-commitment of the WHOLE dropped pre-record — has NO EffectVM column. The EffectVM `state_commit`
column is a DIFFERENT commitment (the Poseidon2 H4-of-H4 of the AFTER-block), so the row's commitment
does NOT witness that the pre-record was committed under `stateCommitment`. The row's
`DroppedBlockIntent` only says the readable economic block was ZEROED — NOT that its content was
sovereign-committed. The install soundness lives ONLY in `makeSovereignA_full_sound`. -/

/-- **`makeSovereign_offrow_unenforced` — the loud finding.** `DroppedBlockIntent` is invariant under
any change OUTSIDE the `state_after` economic block — including the (unrepresented) sovereign
commitment install, the receipt, and the guard. Two rows agreeing on the economic after-columns satisfy
the intent equally regardless of what `stateCommitment` value was installed. The row witnesses the
balance-DROP but NOT the commitment INSTALL; that lives ONLY in `makeSovereignA_full_sound`. -/
theorem makeSovereign_offrow_unenforced :
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off)) →
      (DroppedBlockIntent env₁ ↔ DroppedBlockIntent env₂)) := by
  intro env₁ env₂ hagree
  unfold DroppedBlockIntent
  rw [hagree state.BALANCE_LO, hagree state.BALANCE_HI, hagree state.NONCE,
      hagree state.CAP_ROOT, hagree state.RESERVED]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [← hagree (state.FIELD_BASE + i)]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [hagree (state.FIELD_BASE + i)]; exact f i hi⟩

/-! ## §11 — NON-VACUITY. -/

/-- A concrete dropped row: every economic after-column is `0`. -/
def zeroRow : VmRowEnv where
  loc := fun v => if v = SEL_MAKESOVEREIGN then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `zeroRow` realizes the dropped-block intent. -/
theorem zeroRow_realizes_intent : DroppedBlockIntent zeroRow := by
  unfold DroppedBlockIntent zeroRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eqToModEq ?_
    show (if saCol state.BALANCE_LO = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · refine eqToModEq ?_
    show (if saCol state.BALANCE_HI = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · refine eqToModEq ?_
    show (if saCol state.NONCE = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · refine eqToModEq ?_
    show (if saCol state.CAP_ROOT = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · refine eqToModEq ?_
    show (if saCol state.RESERVED = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · intro i hi
    refine eqToModEq ?_
    show (if saCol (state.FIELD_BASE + i) = SEL_MAKESOVEREIGN then (1:ℤ) else 0) = 0
    rw [if_neg]
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE, SEL_MAKESOVEREIGN]
    omega

/-- A FORGED row: `zeroRow` with post-`bal_lo` left at `5` (the readable balance survived the rebind). -/
def forgedRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 5 else zeroRow.loc v
  nxt := zeroRow.nxt
  pub := zeroRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `forgedRow`'s post-`bal_lo` is non-zero
(the readable balance survived), so the drop-to-zero gate REJECTS it. -/
theorem forgedRow_rejected : ¬ (gZero state.BALANCE_LO).holdsVm forgedRow false false := by
  apply makeSovereignVm_rejects_surviving_balance
  · show (0:ℤ) ≤ (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (5:ℤ)
        else zeroRow.loc (saCol state.BALANCE_LO))
      ∧ (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (5:ℤ)
        else zeroRow.loc (saCol state.BALANCE_LO)) < 2013265921
    rw [if_pos rfl]; norm_num
  · show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (5:ℤ)
      else zeroRow.loc (saCol state.BALANCE_LO)) ≠ 0
    rw [if_pos rfl]; norm_num

/-! ## §12 — axiom-hygiene tripwires. -/

#guard makeSovereignVmDescriptor.constraints.length == 13
#guard makeSovereignVmDescriptor.hashSites.length == 4
#guard makeSovereignVmDescriptor.traceWidth == 188

#assert_axioms makeSovereignVm_faithful
#assert_axioms makeSovereignVm_rejects_nonzero
#assert_axioms makeSovereignVm_rejects_surviving_balance
#assert_axioms makeSovereignVm_binds_block_advantage_bound
#assert_axioms makeSovereignVm_commit_binds_keyed
#assert_axioms sovereignRebind_balOf_zero
#assert_axioms makeSovereign_target_dropped
#assert_axioms makeSovereign_row_matches_executor
#assert_axioms makeSovereign_offrow_unenforced
#assert_axioms zeroRow_realizes_intent
#assert_axioms forgedRow_rejected

/-! ## §RT — the RUNTIME-RECONCILED cutover descriptor (v2): frame-freeze + MODE-BIT SET + nonce-TICK
(GRADUATED into the descriptor cutover).

THE RUNTIME GROUND TRUTH. The running prover's `make_sovereign` (selector 12) trace arm
(`effect_vm/trace.rs`) sets `new_state.mode_flag = 1` and ticks the nonce; the `reserved` column packs
`low_bits + mode_flag·256`, so the hand-AIR enforces `new_reserved − old_reserved − 256 = 0` (+ the
aux mode-bit booleanity), freezes balances / `cap_root` / all 8 fields, and the global nonce gate TICKS
the nonce. The §1–§10 descriptor above (`makeSovereignVmDescriptor`, the verified-executor REBIND face:
the readable record dropped to the zero block behind `stateCommitment`) is a DIFFERENT semantics for
sovereignty than the runtime's mode-bit convention — the documented sovereign-ZERO divergence. WHICH
layer's sovereignty semantics is canonical (record-rebind-to-commitment vs mode-bit-with-retained
balance) is an open protocol decision; the CUTOVER convention (model the row the runtime hand-AIR
actually proves, keep the executor face as the named off-row/other-layer story) graduates the wire
descriptor NOW without changing any shipped semantics. This v2 emits the runtime row: frame-freeze +
`reserved` +256 MODE-BIT SET + nonce-tick + the makeSovereign selector binding. Both faces stay
verified; the WIRE descriptor is the runtime row. -/

open Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
  (RowEncodesRevoke)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSub eSelNoop gBalHi gNonce gCapPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)

/-- The `make_sovereign` selector column index (runtime `sel::MAKE_SOVEREIGN = 12`). -/
def SEL_MAKE_SOVEREIGN_RT : Nat := 12

/-- Balance-lo FREEZE body (the runtime row retains the balance; the rebind face zeroes it). -/
def gSovBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The MODE-BIT SET body: `(after.RESERVED − before.RESERVED) − 256·(1 − sel.NOOP)`. On the active
row (`s_noop = 0`) the reserved word advances by EXACTLY `256` (the packed `mode_flag` bit set, low
bits untouched); on NoOp pad rows it freezes. Mirrors the hand-AIR's
`s_makesov · (new_reserved − old_reserved − 256)`. -/
def gSovReserved : EmittedExpr :=
  eSub (eSub (eSA state.RESERVED) (eSB state.RESERVED))
       (.mul (.const 256) (.add (.const 1) (.mul (.const (-1)) eSelNoop)))

/-- The v2 per-row gates: balances + `cap_root` + 8 fields FROZEN, nonce TICK, reserved +256. -/
def sovereignRuntimeRowGates : List VmConstraint :=
  [ .gate gSovBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gSovReserved ] ++ gFieldPassAll

/-- The v2 (runtime-reconciled) `makeSovereign` AIR identity. -/
def makeSovereignRuntimeVmAirName : String := "dregg-effectvm-makesovereign-v2"

/-- **`makeSovereignRuntimeVmDescriptor`** — the `make_sovereign` runtime-row circuit, RECONCILED onto
the runtime hand-AIR: frame-freeze + mode-bit-SET + nonce-TICK gates ++ transition continuity ++ the 7
boundary PI pins ++ the selector-binding gate, with the 4 ordered GROUP-4 hash sites and the 2
balance-limb range checks. The executor REBIND face stays `makeSovereignVmDescriptor` (§3). -/
def makeSovereignRuntimeVmDescriptor : EffectVmDescriptor :=
  { name := makeSovereignRuntimeVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := sovereignRuntimeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates SEL_MAKE_SOVEREIGN_RT
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- **`SovRuntimeRowIntent env`** — balances / `cap_root` / fields UNCHANGED; the nonce TICKS by 1; the
reserved word advances by 256 (the mode bit), both gated off on NoOp pad rows. -/
def SovRuntimeRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE)
      ≡ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP) [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED)
      ≡ env.loc (sbCol state.RESERVED) + 256 * (1 - env.loc sel.NOOP) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-- **FAITHFULNESS.** The v2 per-row gates hold IFF `SovRuntimeRowIntent` holds. -/
theorem sovereignRuntimeVm_faithful (env : VmRowEnv) :
    (∀ c ∈ sovereignRuntimeRowGates, c.holdsVm env false false) ↔ SovRuntimeRowIntent env := by
  unfold sovereignRuntimeRowGates gFieldPassAll SovRuntimeRowIntent
  constructor
  · intro h
    have hLo := h (.gate gSovBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gSovReserved) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gSovBalLoFreeze, gBalHi, gNonce, gCapPass, gSovReserved,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨(gate_modEq_iff (by ring)).mp hLo, (gate_modEq_iff (by ring)).mp hHi,
      (gate_modEq_iff (by ring)).mp hNon, (gate_modEq_iff (by ring)).mp hCap,
      (gate_modEq_iff (by ring)).mp hRes, ?_⟩
    intro i hi
    have hfi := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hfi
    exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gSovBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gSovReserved, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-- **Anti-ghost (mode bit NOT set).** A row whose reserved word does NOT advance by 256 on the active
row fails the mode-bit gate — a sovereignty claim without the mode bit is UNSAT. -/
theorem sovereignRuntimeVm_rejects_unset_mode (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.RESERVED)
      ∧ env.loc (saCol state.RESERVED) < 2013265921)
    (hcanonMode : 0 ≤ env.loc (sbCol state.RESERVED) + 256 * (1 - env.loc sel.NOOP)
      ∧ env.loc (sbCol state.RESERVED) + 256 * (1 - env.loc sel.NOOP) < 2013265921)
    (hwrong : env.loc (saCol state.RESERVED)
        ≠ env.loc (sbCol state.RESERVED) + 256 * (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gSovReserved).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gSovReserved, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonMode hwrong

/-- **`SovRuntimeCellSpec pre post`** — the per-cell runtime makeSovereign spec: balances / capRoot /
fields FROZEN, nonce +1, reserved +256 (the packed mode bit). -/
def SovRuntimeCellSpec (pre post : CellState) : Prop :=
  post.balLo ≡ pre.balLo [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved + 256 [ZMOD 2013265921]

theorem sovIntent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRevoke env pre post) (hint : SovRuntimeRowIntent env) :
    SovRuntimeCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]
    have h := hnon; rw [hnoop] at h; simpa using h
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]
    have h := hres; rw [hnoop] at h; simpa using h

/-- **`sovereignRuntime_full_sound`** — the v2 descriptor's row soundness: a satisfying row, decoded,
pins the full per-cell frame-freeze + mode-bit + nonce-tick post-state AND publishes its commit as
`NEW_COMMIT`. -/
theorem sovereignRuntime_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesRevoke env pre post)
    (hgatesat : satisfiedVm hash makeSovereignRuntimeVmDescriptor env true false)
    (hsat : satisfiedVm hash makeSovereignRuntimeVmDescriptor env true true) :
    SovRuntimeCellSpec pre post ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ sovereignRuntimeRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ makeSovereignRuntimeVmDescriptor.constraints := by
      unfold makeSovereignRuntimeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold sovereignRuntimeRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (sovereignRuntimeVm_faithful env).mp hgates'
  refine ⟨sovIntent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ makeSovereignRuntimeVmDescriptor.constraints := by
      unfold makeSovereignRuntimeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-- A concrete runtime makeSovereign row: frame frozen at zero, nonce `0 → 1`, reserved `0 → 256`. -/
def goodSovRow : VmRowEnv where
  loc := fun v =>
    if v = saCol state.NONCE then 1
    else if v = saCol state.RESERVED then 256
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodSovRow` realizes the runtime makeSovereign intent. -/
theorem goodSovRow_realizes_intent : SovRuntimeRowIntent goodSovRow := by
  unfold SovRuntimeRowIntent goodSovRow
  refine ⟨eqToModEq (by decide), eqToModEq (by decide), eqToModEq (by decide),
    eqToModEq (by decide), eqToModEq (by decide), ?_⟩
  intro i hi
  refine eqToModEq ?_
  show (if saCol (state.FIELD_BASE + i) = saCol state.NONCE then (1:ℤ)
        else if saCol (state.FIELD_BASE + i) = saCol state.RESERVED then 256 else 0)
      = (if sbCol (state.FIELD_BASE + i) = saCol state.NONCE then (1:ℤ)
        else if sbCol (state.FIELD_BASE + i) = saCol state.RESERVED then 256 else 0)
  have h1 : (saCol (state.FIELD_BASE + i) = saCol state.NONCE) = False := by
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE, state.NONCE]
    exact eq_false (by omega)
  have h2 : (saCol (state.FIELD_BASE + i) = saCol state.RESERVED) = False := by
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE, state.RESERVED]
    exact eq_false (by omega)
  have h3 : (sbCol (state.FIELD_BASE + i) = saCol state.NONCE) = False := by
    simp only [saCol, sbCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, state.NONCE]
    exact eq_false (by omega)
  have h4 : (sbCol (state.FIELD_BASE + i) = saCol state.RESERVED) = False := by
    simp only [saCol, sbCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, state.RESERVED]
    exact eq_false (by omega)
  simp only [h1, h2, h3, h4, if_false]

/-- A FORGED row: `goodSovRow` with the reserved advance dropped (mode bit NOT set). -/
def badSovRow : VmRowEnv where
  loc := fun v => if v = saCol state.RESERVED then 0 else goodSovRow.loc v
  nxt := goodSovRow.nxt
  pub := goodSovRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSovRow` claims sovereignty without
setting the mode bit; the `gSovReserved` gate REJECTS it. -/
theorem badSovRow_rejected : ¬ (VmConstraint.gate gSovReserved).holdsVm badSovRow false false := by
  apply sovereignRuntimeVm_rejects_unset_mode <;>
    simp only [badSovRow, goodSovRow, sel.NOOP, sbCol, saCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.RESERVED, state.NONCE] <;> norm_num

#guard makeSovereignRuntimeVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard makeSovereignRuntimeVmDescriptor.hashSites.length == 4
#guard makeSovereignRuntimeVmDescriptor.traceWidth == 188

#assert_axioms sovereignRuntimeVm_faithful
#assert_axioms sovereignRuntimeVm_rejects_unset_mode
#assert_axioms sovIntent_to_cellSpec
#assert_axioms sovereignRuntime_full_sound
#assert_axioms goodSovRow_realizes_intent
#assert_axioms badSovRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
