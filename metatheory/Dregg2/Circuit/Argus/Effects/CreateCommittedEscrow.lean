/-
# Dregg2.Circuit.Argus.Effects.CreateCommittedEscrow — the createCommittedEscrow effect welded into
the Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the side-table cornerstone for PLAIN escrow:
`interp (createEscrowStmt …) = createEscrowKAsset` (the executor IS the meaning of the IR term, now
over a TWO-component move — a per-asset `bal` debit AND an `escrows` list prepend). `Argus/Compile.lean`
welded plain createEscrow's circuit (`createEscrowGenuine_sound`) to that term. This module does the
SAME for the COMMITTED (privacy) variant, which is the §8-hiding-portal-gated committed-escrow CREATE.

## The committed variant is the plain create UNDER a hiding portal — faithfully, not by fiat

The running executor is `createCommittedEscrowChainA` (`Exec/TurnExecutorFull.lean:3164`):

    createCommittedEscrowChainA s … hidingProof
      = if hidingProof = true then createEscrowChainA s … else none

i.e. the §8 hiding portal `hidingProof` (the executable boolean shadow of the Pedersen range/opening
proof, dregg1 `apply.rs:2125`) gates an OTHERWISE-IDENTICAL per-asset escrow lock. At the KERNEL level
`createEscrowChainA` is `createEscrowKAsset s.kernel …` (it stamps the log, `:1995`), so the committed
create's KERNEL step is exactly `if hidingProof then createEscrowKAsset k … else none`. We prove that
bridge (`createCommittedEscrowChainA_kernelStep`, NOT asserted) so the kernel target this module refines
to is the genuine kernel projection of the AUDITED chained executor — the privacy gate the plain escrow
LACKS, modelled fail-closed (`createCommittedEscrowChainA_fails_without_hiding`, `:3170`), not papered.

The IR term is therefore `seq (guard hidingGate) (createEscrowStmt …)`: the §8 portal as an Argus
`guard`, then the EXACT plain-escrow body the §E cornerstone already refined. Composing the proven
plain-escrow body under one more domain-restrictor guard is the honest encoding of "committed escrow =
hiding portal ∘ plain escrow", and the cornerstone here is that `interp` of THIS term IS the committed
kernel step.

## The circuit side — the audited CLASS-A genuine descriptor (the COMMITTED module's)

The circuit is `EffectVmEmitCreateCommittedEscrow.escrowCreateVmDescriptorGenuine` + its class-A
`escrowCreateGenuine_sound` (`Circuit/Emit/EffectVmEmitCreateCommittedEscrow.lean:854`), which on a
satisfying row forces (a) the per-cell `CellEscrowSpec` (the `balLo` DEBIT by `amount`, every other
limb FROZEN) and (b) the GENUINE in-row escrow-root RECOMPUTE
(`SYS_DIG_AFTER = advanceOf hash (leafOf hash id creator recipient amount asset resolved) SYS_DIG_BEFORE`,
the side-table digest FORCED — not a free step) and (c) the published commit. So the side-table prepend
is BOUND, not papered (`escrowCreateGenuine_binds_record`, `:898`: a forged/dropped park MOVES the
commitment ⇒ UNSAT).

## HONEST SURFACE — exactly createEscrow's weld surface (do NOT over-read)

The weld concludes the SAME two legs the plain-createEscrow weld concludes:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's debited
    `bal creator asset` (= pre − amount), with the frozen frame (balHi/fields/capRoot/reserved/nonce)
    agreeing. `cellProjEscrow` projects ONLY the `(creator, asset)` ledger entry into `balLo` (the other
    limbs are `0`, FROZEN) — so this binds the DEBITED CELL, exactly as transfer binds the SRC cell. The
    cross-cell combined per-asset conservation (debit ⊕ off-ledger park) is the executor's keystone
    (`createCommittedEscrowChainA_combined_neutral`, `:3179`), cited there — NOT re-claimed here.
  * **side-table leg (the escrow record):** the circuit FORCES the new escrow-list root to be the genuine
    recompute of the bound parked-record content + the old root, absorbed into `state_commit`, so the
    parked record (id/creator/recipient/amount/asset/resolved) is bound. The weld EXPOSES this
    genuine-recompute clause as a conjunct so the side-table binding is part of the welded statement.

What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the
executor's `parkedRecord :: k.escrows` as a LIST (the EffectVM row carries a DIGEST, not the list — they
agree only up to the side-table root). The executor produces the real list; the circuit produces the
genuine root of it. That digest-not-list boundary is faithful, stated, not hidden. SEPARATELY, the §8
hiding portal is part of the EXECUTOR gate (modelled fail-closed) but is NOT a per-row arithmetic
column on this descriptor (IR-EXTENSION flag #2, `EffectVmEmitCreateCommittedEscrow §11/§E`): the weld's
circuit side does not re-derive it; it is enforced on the executor side, where the IR term's `guard`
carries it.

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY
via the named `Poseidon2SpongeCR` hypothesis (inside the cited anti-ghost, not these theorems). No
`sorry`, no `:= True`, no `native_decide`. This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow
import Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrowWide

namespace Dregg2.Circuit.Argus.Effects.CreateCommittedEscrow

open Dregg2.Exec
-- The CHAINED committed-escrow executor + its plain delegate + the receipt stamp live in
-- `Dregg2.Exec.TurnExecutorFull`; opened so the §0 kernel-bridge lemma can name them.
open Dregg2.Exec.TurnExecutorFull (createCommittedEscrowChainA createEscrowChainA escrowReceiptA)
-- `VmRowEnv` / `satisfiedVm` / `prmCol` are the unqualified EffectVM IR names (exactly as
-- `Argus/Compile.lean` opens them) — without this they resolve to the fully-qualified path only.
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Argus
  (RecStmt interp createEscrowStmt interp_createEscrowStmt_eq_createEscrowKAsset kC)
open Dregg2.Exec (createEscrowKAsset recBalCreditCell)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow
  (escrowCreateVmDescriptorGenuine escrowCreateGenuine_sound EscrowParams CellEscrowSpec
   RowEncodesEscrow cellProjEscrow)

/-! ## §0 — THE KERNEL TARGET: the committed-escrow CREATE kernel step, and its bridge to the audited
chained executor.

The plain escrow §E cornerstone (`Stmt.lean`) refines its IR term to the KERNEL step
`createEscrowKAsset : RecordKernelState → Option RecordKernelState`. The committed variant adds the §8
hiding portal in front, so its kernel step is `if hidingProof then createEscrowKAsset k … else none`.
We DEFINE that here as the refinement target AND prove (not assert) it is the genuine kernel projection
of the audited chained executor `createCommittedEscrowChainA` (`TurnExecutorFull.lean:3164`), so the
target is faithful to the running system, not a fresh invention. -/

/-- **`createCommittedEscrowKAssetK`** — the committed-escrow CREATE kernel step: the §8 hiding portal
`hidingProof` gates the OTHERWISE-IDENTICAL plain per-asset escrow lock `createEscrowKAsset` (the
single-cell single-asset debit + the unresolved-record park). Fail-closed when the portal does not
hold (`hidingProof = false` ⇒ `none`) — the privacy gate plain escrow LACKS. -/
def createCommittedEscrowKAssetK (k : RecordKernelState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool) :
    Option RecordKernelState :=
  if hidingProof = true then
    createEscrowKAsset k id actor creator recipient asset amount
  else none

/-- **`createCommittedEscrowChainA_kernelStep` — the bridge (PROVED, not asserted).** The audited
chained committed executor `createCommittedEscrowChainA`, projected to the kernel, IS
`createCommittedEscrowKAssetK` (and it stamps the chained `log` by `escrowReceiptA actor ::`). So the
kernel target this module refines the IR term to is the genuine kernel image of the running system's
committed-escrow create — the §8 portal gating the plain `createEscrowKAsset`. -/
theorem createCommittedEscrowChainA_kernelStep (s : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool) :
    createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof
      = (createCommittedEscrowKAssetK s.kernel id actor creator recipient asset amount hidingProof).map
          (fun k' => { kernel := k', log := escrowReceiptA actor :: s.log }) := by
  unfold createCommittedEscrowChainA createCommittedEscrowKAssetK createEscrowChainA
  by_cases hp : hidingProof = true
  · rw [if_pos hp, if_pos hp]
    cases createEscrowKAsset s.kernel id actor creator recipient asset amount with
    | none => rfl
    | some k' => rfl
  · rw [if_neg hp, if_neg hp]; rfl

#assert_axioms createCommittedEscrowChainA_kernelStep

/-! ## §1 — THE IR TERM: gate on the §8 hiding portal, then the EXACT plain-escrow body.

`createCommittedEscrowStmt = seq (guard hidingGate) (createEscrowStmt …)` — the §8 hiding portal as an
Argus `guard` domain-restrictor, then the PLAIN-escrow IR term the §E cornerstone already refined to
`createEscrowKAsset`. Reusing `createEscrowStmt` (rather than re-inlining the two component writes) is
the honest encoding of "committed escrow = hiding portal ∘ plain escrow" — exactly the executor's own
`if hidingProof then createEscrowChainA else none` shape. -/

/-- The §8 hiding-portal gate as an Argus `RecordKernelState → Bool` guard (state-independent: it reads
only the carried `hidingProof` witness — the boolean shadow of the Pedersen range/opening proof). -/
def hidingGate (hidingProof : Bool) : RecordKernelState → Bool := fun _ => hidingProof

/-- **The createCommittedEscrow effect as an Argus IR term.** Gate on the §8 hiding portal, then run the
plain createEscrow body (the per-asset `bal` debit ++ the `escrows` prepend). The body is the proven
`createEscrowStmt`; the extra `guard (hidingGate …)` is the privacy domain-restrictor the committed
variant adds. -/
def createCommittedEscrowStmt (id : Nat) (actor creator recipient : CellId) (asset : AssetId)
    (amount : ℤ) (hidingProof : Bool) : RecStmt :=
  RecStmt.seq (RecStmt.guard (hidingGate hidingProof))
    (createEscrowStmt id actor creator recipient asset amount)

/-! ## §2 — THE CORNERSTONE: `interp` of the committed term IS the committed kernel step.

The SAME shape as the plain §E cornerstone, with one extra leading guard. On `hidingProof = true` the
guard fires (`some k`) and the `bind` runs the plain body, whose `interp` IS `createEscrowKAsset` by the
§E cornerstone; on `hidingProof = false` the guard rejects (`none`) and the `bind` short-circuits — which
is exactly `createCommittedEscrowKAssetK`. -/

/-- **The cornerstone (committed side-table).** `interp` of the createCommittedEscrow term IS the
committed kernel step `createCommittedEscrowKAssetK` — the §8 hiding portal gating the verified plain
`createEscrowKAsset`, the same partial function by construction, exactly as the plain §E cornerstone now
under one more domain-restrictor guard. -/
theorem interp_createCommittedEscrowStmt_eq_createCommittedEscrowKAssetK (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (k : RecordKernelState) :
    interp (createCommittedEscrowStmt id actor creator recipient asset amount hidingProof) k
      = createCommittedEscrowKAssetK k id actor creator recipient asset amount hidingProof := by
  simp only [createCommittedEscrowStmt, interp, hidingGate, createCommittedEscrowKAssetK]
  by_cases hp : hidingProof = true
  · -- §8 portal discharges: the guard fires (`some k`), `bind` runs the plain body = `createEscrowKAsset`.
    rw [if_pos hp, if_pos hp]
    simp only [Option.bind]
    exact interp_createEscrowStmt_eq_createEscrowKAsset id actor creator recipient asset amount k
  · -- §8 portal FAILS — fail-closed: the guard returns `none`, `bind` short-circuits to `none`.
    rw [if_neg hp, if_neg hp]
    rfl

#assert_axioms interp_createCommittedEscrowStmt_eq_createCommittedEscrowKAssetK

/-! ## §3 — THE EXECUTOR-side per-cell projection of the committed kernel step `createCommittedEscrowKAssetK`.

The §E.1 analog (`Compile.lean createEscrowKAsset_proj_balLo`), now over the committed step: a COMMITTED
create (under the discharged portal) DEBITS the creator cell's projected `(creator, asset)` ledger entry
by exactly `amount`. The frozen frame (balHi/nonce/fields/capRoot/reserved) is `0 = 0` on both
projections of `cellProjEscrow` (definitional). On the failed portal the step is `none`, so a commit
HYPOTHESIS already forces `hidingProof = true` — the gate is genuinely load-bearing in the projection. -/

/-- **`createCommittedEscrowKAssetK_proj_balLo`.** A committed kernel create (discharged §8 portal) debits
the creator cell's projected `(creator, asset)` ledger entry by exactly `amount` (the value parked
off-ledger). The per-cell conserved leg the weld pins. -/
theorem createCommittedEscrowKAssetK_proj_balLo {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ} {hidingProof : Bool}
    (h : createCommittedEscrowKAssetK k id actor creator recipient asset amount hidingProof = some k') :
    (cellProjEscrow k'.bal creator asset).balLo
      = (cellProjEscrow k.bal creator asset).balLo - amount := by
  unfold createCommittedEscrowKAssetK at h
  by_cases hp : hidingProof = true
  · -- portal discharges: reduce to the plain `createEscrowKAsset` per-asset debit.
    rw [if_pos hp] at h
    unfold createEscrowKAsset at h
    by_cases hg : authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
        ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
        ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      show recBalCreditCell k.bal creator asset (-amount) creator asset = k.bal creator asset - amount
      unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · -- portal FAILS ⇒ the step is `none`, contradicting the commit hypothesis.
    rw [if_neg hp] at h; exact absurd h (by simp)

#assert_axioms createCommittedEscrowKAssetK_proj_balLo

/-! ## §4 — THE WELD: a satisfying witness of `escrowCreateVmDescriptorGenuine` agrees, per cell, with the
post-state the IR term's executor interpretation produces — AND forces the genuine side-table root.

Unlike `Compile.lean` (which routes through the central `compileE .createEscrow`), this module proves the
weld DIRECTLY against the audited class-A descriptor `escrowCreateVmDescriptorGenuine` (no central
`compileE` needed). The circuit side is `escrowCreateGenuine_sound` (the committed module's class-A
soundness); the executor side is the §2 cornerstone + the §3 projection. -/

/-- **`createCommittedEscrow_compile_sound` — the welded soundness (committed createEscrow slice).**

Suppose, for the Argus committed-escrow term
`createCommittedEscrowStmt id actor creator recipient asset amount hidingProof`:
  * the audited class-A circuit `escrowCreateVmDescriptorGenuine` is SATISFIED by `(env, true, true)`
    under the abstract Poseidon carrier `hash`, and its `RowEncodesEscrow` decoding NAMES the post-state
    record `post` over the creator cell's projection `cellProjEscrow k.bal creator asset` with the
    `⟨amount⟩` param block (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (createCommittedEscrowStmt …) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    debited creator-cell projection `cellProjEscrow k'.bal creator asset` — the conserved `balLo`
    (debited by `amount`) AND the whole frozen frame (balHi/fields/capRoot/reserved/nonce). The committed
    create has NO nonce-tick divergence (the descriptor FREEZES the cell nonce, matching the executor;
    `cellProjEscrow` sends `nonce` to `0` on both sides).
  * **side-table leg:** the circuit FORCES the new escrow-list-root carrier to be the genuine in-row
    recompute `advanceOf hash (leafOf hash id creator recipient amount asset resolved) old_root` of the
    bound parked record + old root — the digest the executor's `parkedRecord :: k.escrows` prepend
    commits to (absorbed into `state_commit`; a forged/dropped park MOVES the commitment, see
    `escrowCreateGenuine_binds_record`).

So the class-A circuit the prover runs for the COMMITTED escrow create pins the per-cell debited state the
IR term's executor produces AND genuinely recomputes the bound `escrows` side-table root — the template
generalizes to the §8-hiding-portal-gated two-component side-table effect. (The §8 portal itself is the
out-of-row IR-EXTENSION flag #2: it is carried on the executor side by the IR term's `guard`, NOT
re-derived by the circuit side here.) -/
theorem createCommittedEscrow_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (henc : RowEncodesEscrow env (cellProjEscrow k.bal creator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash escrowCreateVmDescriptorGenuine env true true)
    (hexec : interp (createCommittedEscrowStmt id actor creator recipient asset amount hidingProof) k
              = some k') :
    -- conserved leg: the debited cell's projection agrees on balLo + the whole frozen frame …
    ( post.balLo = (cellProjEscrow k'.bal creator asset).balLo
      ∧ post.balHi = (cellProjEscrow k'.bal creator asset).balHi
      ∧ (∀ i, post.fields i = (cellProjEscrow k'.bal creator asset).fields i)
      ∧ post.capRoot = (cellProjEscrow k'.bal creator asset).capRoot
      ∧ post.reserved = (cellProjEscrow k'.bal creator asset).reserved
      ∧ post.nonce = (cellProjEscrow k'.bal creator asset).nonce )
    -- … and the SIDE-TABLE leg: the circuit FORCES the genuine escrow-list-root recompute (the bound
    -- parked record + old root), absorbed into `state_commit`.
    ∧ ( env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_AFTER
          = Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.advanceOf hash
              (Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.leafOf hash
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ID))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.CREATOR))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RECIPIENT))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.AMOUNT))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ASSET))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RESOLVED)))
              (env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_BEFORE) ) := by
  -- circuit side: the audited class-A soundness forces the per-cell `CellEscrowSpec` + the genuine root.
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    escrowCreateGenuine_sound hash env (cellProjEscrow k.bal creator asset) post ⟨amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the committed kernel step
  -- `createCommittedEscrowKAssetK`; its per-cell projection gives the debited balLo (frozen limbs `0=0`).
  rw [interp_createCommittedEscrowStmt_eq_createCommittedEscrowKAssetK] at hexec
  have heLo := createCommittedEscrowKAssetK_proj_balLo hexec
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
           hcN.trans rfl⟩, hroot⟩
  -- balLo: circuit pins post = pre − amount; executor debits the projected entry by amount.
  rw [hcLo, heLo]

#assert_axioms createCommittedEscrow_compile_sound

/-! ## §5 — NON-VACUITY: the committed term genuinely parks (and the §8 portal genuinely gates).

The cornerstone would be hollow if the committed term never committed, or if the §8 portal were inert.
Neither: with the discharged portal a fresh `0`-amount lock grows the `escrows` store from `[]` to
length `1` (the two-component move is real); with the portal FAILED the identical create REJECTS
(fail-closed) — the privacy gate is load-bearing, two-valued, exactly the executor's
`createCommittedEscrowChainA_fails_without_hiding` teeth lifted onto the IR term. -/

/-- **NON-VACUITY (witness TRUE — the park is real).** Under the discharged §8 portal
(`hidingProof = true`), running the committed term on the §C two-cell kernel `kC` (cell `0` Live, empty
`escrows`) with a fresh `0`-amount lock grows `escrows` from `[]` to length `1` — the two-component move
genuinely touches the side-table (the prepend is real). -/
theorem createCommittedEscrowStmt_parks :
    (interp (createCommittedEscrowStmt 7 0 0 1 0 0 true) kC).map (fun k => k.escrows.length) = some 1 := by
  rw [interp_createCommittedEscrowStmt_eq_createCommittedEscrowKAssetK]
  decide

/-- **NON-VACUITY (witness FALSE / the §8 portal teeth).** Without the hiding portal
(`hidingProof = false`), the IDENTICAL committed create REJECTS (`interp = none`) — the privacy gate the
plain escrow LACKS, modelled fail-closed. So `hidingGate` is genuinely load-bearing: the term is
two-valued in the portal, not a no-op that always commits. -/
theorem createCommittedEscrowStmt_fails_without_hiding (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (k : RecordKernelState) :
    interp (createCommittedEscrowStmt id actor creator recipient asset amount false) k = none := by
  rw [interp_createCommittedEscrowStmt_eq_createCommittedEscrowKAssetK]
  simp only [createCommittedEscrowKAssetK, if_neg (by decide : ¬ (false = true))]

#assert_axioms createCommittedEscrowStmt_parks
#assert_axioms createCommittedEscrowStmt_fails_without_hiding

/-! ## §6 — FULL-STATE on the RUNNABLE descriptor (the magnesium breadth — bind ALL 17 fields).

§4's weld concludes the per-cell agreement + the genuine escrow-root recompute over the AUDITED class-A
descriptor (`escrowCreateVmDescriptorGenuine`), whose root carrier is the raw `aux_off_sys.SYSTEM_ROOTS_DIGEST`
(= 96). That binds the `escrows` root into `state_commit`, but not in the shape the generic full-state crown
consumes (the DEDICATED `sysRootsDigestCol`, the `wideHashSites` GROUP-4, the widened width).

`EffectVmEmitCreateCommittedEscrowWide.committedEscrow_runnable_full_sound` lifts the SAME per-row gates
through the generic `runnable_full_sound` over the WIDE descriptor `committedEscrowVmDescriptorWide`
(`traceWidth = EFFECT_VM_WIDTH_SYSROOTS`, `hashSites = wideHashSites`, the dedicated-carrier root-update
gate). A satisfying row of THAT descriptor binds the FULL 17-field post-state: the per-cell DEBIT (here
the recipient cell's projected ledger entry) AND the `escrows` side-table digest advance — with the
generic anti-ghost (`committedEscrow_wide_rejects_root_tamper` / `…state_tamper`) giving: tamper ANY of
the 13 absorbed state-block columns OR ANY of the 8 side-table roots ⇒ the running descriptor is UNSAT.

This section welds THAT full-state crown to the SAME executor cornerstone (§2/§3), so the welded
statement now pins the executor's per-cell post-state through the FULL-STATE RUNNABLE descriptor — and,
since createObligation is the dispatch-alias of this descriptor (`Argus/Effects/CreateObligation.lean`),
createObligation inherits the full-state binding through the SAME wide circuit. -/

open Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrowWide
  (committedEscrowVmDescriptorWide committedEscrow_runnable_full_sound)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide (ESCROW_STEP_PARAM)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest)

/-- **`createCommittedEscrow_runnable_full_state` — THE FULL-STATE WELD (committed createEscrow / createObligation).**

Suppose, for the Argus committed-escrow term:
  * the WIDE RUNNABLE descriptor `committedEscrowVmDescriptorWide` is SATISFIED by `(env, true, true)`,
    its `RowEncodesEscrow` decoding NAMES `post` over the creator cell's projection
    `cellProjEscrow k.bal creator asset` with `⟨amount⟩`, and the dedicated digest carriers are pinned to
    the `systemRootsDigest` of the pre/post `system_roots` sub-blocks (`hAfter`/`hBefore`) with the
    accumulator `step` (`hStep`);
  * the IR term's EXECUTOR interpretation COMMITS (`hexec`).

Then the circuit's pinned `post` AGREES with the executor's debited creator-cell projection
`cellProjEscrow k'.bal creator asset` on EVERY limb (`balLo` debited, the whole frame frozen, nonce
frozen) AND the WIDE descriptor binds the `escrows` side-table digest advance
(`systemRootsDigest postRoots = systemRootsDigest preRoots + step`). So the circuit the prover RUNS pins
the per-cell state the executor produces AND the full side-table digest — all 17 fields bound (the other
7 roots through the generic crown's pointwise digest binding). -/
theorem createCommittedEscrow_runnable_full_state
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (preRoots postRoots : SysRoots) (step : ℤ)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow.IsEscrowCreateRow env)
    (henc : RowEncodesEscrow env (cellProjEscrow k.bal creator asset) ⟨amount⟩ post)
    (hAfter : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestCol
                = systemRootsDigest hash postRoots)
    (hBefore : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestColBefore
                = systemRootsDigest hash preRoots)
    (hStep : env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash committedEscrowVmDescriptorWide env true true)
    (hexec : interp (createCommittedEscrowStmt id actor creator recipient asset amount hidingProof) k
              = some k') :
    -- per-cell agreement with the executor (the conserved leg) …
    ( post.balLo = (cellProjEscrow k'.bal creator asset).balLo
      ∧ post.balHi = (cellProjEscrow k'.bal creator asset).balHi
      ∧ (∀ i, post.fields i = (cellProjEscrow k'.bal creator asset).fields i)
      ∧ post.capRoot = (cellProjEscrow k'.bal creator asset).capRoot
      ∧ post.reserved = (cellProjEscrow k'.bal creator asset).reserved
      ∧ post.nonce = (cellProjEscrow k'.bal creator asset).nonce )
    -- … and the FULL side-table digest advance bound by the WIDE RUNNABLE descriptor.
    ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step := by
  -- circuit side: the WIDE full-state crown forces the per-cell `CellEscrowSpec` + the digest advance.
  obtain ⟨hcs, hdig⟩ :=
    committedEscrow_runnable_full_sound ⟨amount⟩ hash preRoots step env
      (cellProjEscrow k.bal creator asset) post postRoots
      hrow henc hAfter hBefore hStep hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone + §3 projection give the debited balLo (frozen limbs `0 = 0`).
  rw [interp_createCommittedEscrowStmt_eq_createCommittedEscrowKAssetK] at hexec
  have heLo := createCommittedEscrowKAssetK_proj_balLo hexec
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
           hcN.trans rfl⟩, hdig⟩
  rw [hcLo, heLo]

#assert_axioms createCommittedEscrow_runnable_full_state

end Dregg2.Circuit.Argus.Effects.CreateCommittedEscrow
