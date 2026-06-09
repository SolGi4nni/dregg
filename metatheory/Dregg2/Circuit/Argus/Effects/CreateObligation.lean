/-
# Dregg2.Circuit.Argus.Effects.CreateObligation — the createObligation effect welded into the Argus IR,
in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the side-table cornerstone for PLAIN escrow:
`interp (createEscrowStmt …) = createEscrowKAsset` (the executor IS the meaning of the IR term, now over a
TWO-component move — a per-asset `bal` debit AND an `escrows` list prepend). `Argus/Compile.lean` welded
plain createEscrow's circuit (`createEscrowGenuine_sound`) to that term. This module does the SAME for the
OBLIGATION CREATE, which is dregg2's stake-posting effect: an obligor parks `stake` of an asset that the
beneficiary collects on a slash (deadline pass) or the obligor reclaims on a fulfil.

## The obligation create is a DEFINITIONAL DISPATCH-ALIAS of plain escrow create — faithfully, not by fiat

The running executor dispatches `createObligationA` to the EXACT plain-escrow chained step
(`Exec/TurnExecutorFull.lean:3835`):

    execFullA s (.createObligationA id actor obligor beneficiary asset stake)
      = createEscrowChainA s id actor obligor beneficiary asset stake          -- obligor↦creator,
                                                                               -- beneficiary↦recipient,
                                                                               -- stake↦amount

i.e. an obligation create IS a per-asset escrow lock under the obligation field-renaming (the obligor posts
the stake = the escrow `creator` debit; the beneficiary = the escrow `recipient` who collects on a slash;
the stake = the escrow `amount`). dregg1 confirms the aliasing at the apply layer: fulfil credits
`record.obligor` (= escrow refund, `apply.rs:1574`), slash credits `record.beneficiary` (= escrow release,
`apply.rs:1656`). At the KERNEL level `createEscrowChainA` is `createEscrowKAsset s.kernel …` (it stamps the
log, `:1995`), so the obligation create's KERNEL step is exactly `createEscrowKAsset k id actor obligor
beneficiary asset stake`. We prove that bridge (`execFullA_createObligationA_kernelStep`, NOT asserted) so
the kernel target this module refines to is the genuine kernel projection of the AUDITED chained executor —
the running system's obligation create, not a fresh invention. This is the SAME aliasing the spec layer
already records (`Spec/escrowholdingcreate.lean execFullA_createObligationA_iff_spec`) and the circuit-fold
layer treats as CLOSED (`TurnEffectRefinement.lean:345`, "createObligationA is a DEFINITIONAL ALIAS of
createEscrowA on the chained step").

Because the obligation create runs the IDENTICAL body, the IR term IS the proven plain-escrow term
`createEscrowStmt id actor obligor beneficiary asset stake` — reusing it (rather than re-inlining the two
component writes) is the honest encoding of "obligation create = escrow create under field-renaming", exactly
the executor's own `createObligationA ↦ createEscrowChainA` dispatch. The cornerstone here is that `interp` of
THIS term IS the obligation kernel step.

## The descriptor — SHARED with plain escrow (createObligation has NO dedicated descriptor) — REPORTED

createObligation carries NO standalone EffectVM descriptor: it is dispatch-aliased to plain createEscrow in
EVERY circuit layer (`CircuitOpenFronts.lean:54` — "createObligationA … CLOSED — dispatch-aliased to";
`EffectEmitRegistry.lean:115` routes it to a HOLE that resolves through the escrow create fold;
`TurnEmit.lean:744` discharges its circuit obligation through the create circuit step). So the circuit it
welds against is the AUDITED CLASS-A `createEscrowVmDescriptorGenuine` + `createEscrowGenuine_sound`
(`Circuit/Emit/EffectVmEmitCreateEscrow.lean`) — the SAME genuine-root-recompute descriptor plain escrow uses
(and `compileE .createEscrow` returns). On a satisfying row it forces (a) the per-cell `CellCreateSpec` (the
`balLo` DEBIT by `amount`, every other limb FROZEN), (b) the GENUINE in-row escrow-root RECOMPUTE
(`SYS_DIG_AFTER = advanceOf hash (leafOf hash id creator recipient amount asset resolved) SYS_DIG_BEFORE`, the
side-table digest FORCED — not a free step), and (c) the published commit. The side-table prepend is BOUND,
not papered.

## HONEST SURFACE — exactly createEscrow's weld surface (do NOT over-read)

The weld concludes the SAME two legs the plain-createEscrow weld concludes:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's debited
    `bal obligor asset` (= pre − stake), with the frozen frame (balHi/fields/capRoot/reserved/nonce) agreeing.
    `cellProjCreate` projects ONLY the `(obligor, asset)` ledger entry into `balLo` (the other limbs are `0`,
    FROZEN) — so this binds the DEBITED (obligor) CELL, exactly as transfer binds the SRC cell. The cross-cell
    combined per-asset conservation (debit ⊕ off-ledger park) is the executor's keystone
    (`createEscrowChainA_combined_neutral`, inherited via the alias at `TurnExecutorFull.lean:4151`), cited
    there — NOT re-claimed here.
  * **side-table leg (the obligation record):** the circuit FORCES the new escrow-list root to be the genuine
    recompute of the bound parked-record content + the old root, absorbed into `state_commit`, so the parked
    obligation record (id/obligor/beneficiary/stake/asset/resolved) is bound. The weld EXPOSES this
    genuine-recompute clause as a conjunct so the side-table binding is part of the welded statement.

What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the executor's
`parkedRecord :: k.escrows` as a LIST (the EffectVM row carries a DIGEST, not the list — they agree only up to
the side-table root). The executor produces the real list (the `Stmt.lean` cornerstone + `escrowParked`); the
circuit produces the genuine root of it. That digest-not-list boundary is faithful, stated, not hidden. There
is NO nonce-tick divergence (the descriptor FREEZES the cell nonce, matching the executor — `cellProjCreate`
sends `nonce` to `0` on both sides), so this module carries no nonce reconciliation.

## Honesty

`#assert_axioms` on both keystones (`interp_createObligationStmt_eq_createEscrowKAsset` and
`createObligation_compile_sound`) ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via the
named `Poseidon2SpongeCR` hypothesis (inside the cited anti-ghost `createEscrowGenuine_binds_record`, not these
theorems). No `sorry`, no `:= True`, no `native_decide`. This module OWNS only itself; every import is
read-only.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow

namespace Dregg2.Circuit.Argus.Effects.CreateObligation

open Dregg2.Exec
-- The CHAINED obligation/escrow executor (`createObligationA` dispatches to `createEscrowChainA`) + the
-- kernel step + the receipt stamp live in `Dregg2.Exec.TurnExecutorFull`; opened so the §0 kernel-bridge
-- lemma can name them. `createEscrowKAsset`/`recBalCreditCell`/`createEscrowRawAsset` are the RecordKernel
-- step + its per-asset debit + commit-post-state.
open Dregg2.Exec.TurnExecutorFull (execFullA createEscrowChainA escrowReceiptA)
open Dregg2.Exec (createEscrowKAsset createEscrowRawAsset recBalCreditCell)
-- `VmRowEnv` / `satisfiedVm` / `prmCol` are the unqualified EffectVM IR names (exactly as `Argus/Compile.lean`
-- opens them) — without this they resolve to the fully-qualified path only.
open Dregg2.Circuit.Emit.EffectVmEmit
-- The proven plain-escrow Argus term + its cornerstone (the body the obligation create dispatch-aliases) +
-- the parked-record literal + the §C non-vacuity kernel.
open Dregg2.Circuit.Argus
  (RecStmt interp createEscrowStmt interp_createEscrowStmt_eq_createEscrowKAsset escrowParked kC)
-- The SHARED class-A escrow-create descriptor + its soundness + the per-cell projection (createObligation has
-- NO dedicated descriptor — see header).
open Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow
  (createEscrowVmDescriptorGenuine createEscrowGenuine_sound cellProjCreate CreateParams CellCreateSpec
   RowEncodesCreate)

/-! ## §0 — THE KERNEL TARGET: the obligation CREATE kernel step IS the audited plain-escrow chained step.

The plain escrow §E cornerstone (`Stmt.lean`) refines its IR term to the KERNEL step `createEscrowKAsset`. The
obligation create dispatch-aliases the WHOLE chained step `createEscrowChainA` (under the obligation
field-renaming obligor↦creator, beneficiary↦recipient, stake↦amount), so we prove (NOT assert) that
`execFullA (.createObligationA …)` IS that chained step — anchoring the kernel target this module refines to in
the running system, not a fresh invention. -/

/-- **`execFullA_createObligationA_kernelStep` — the bridge (PROVED, not asserted).** The unified action
executor on the obligation-create action IS the audited plain-escrow chained step `createEscrowChainA` under
the obligation field-renaming (obligor↦creator, beneficiary↦recipient, stake↦amount). So the obligation create
is, on the nose, a per-asset escrow lock — the dispatch aliasing the executor, spec, and circuit-fold layers
already record, here pinned at the `execFullA` entry. -/
theorem execFullA_createObligationA_kernelStep (s : RecChainedState) (id : Nat)
    (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ) :
    execFullA s (.createObligationA id actor obligor beneficiary asset stake)
      = createEscrowChainA s id actor obligor beneficiary asset stake := rfl

#assert_axioms execFullA_createObligationA_kernelStep

/-! ## §1 — THE IR TERM: the proven plain-escrow body under the obligation field-renaming.

`createObligationStmt = createEscrowStmt id actor obligor beneficiary asset stake` — the PLAIN-escrow IR term
the §E cornerstone already refined to `createEscrowKAsset`, instantiated at the obligation parameters. Reusing
`createEscrowStmt` (rather than re-inlining the `setBal` debit ++ `setEscrows` prepend) is the honest encoding
of "obligation create = escrow create under field-renaming" — exactly the executor's own `createObligationA ↦
createEscrowChainA` dispatch. -/

/-- **The createObligation effect as an Argus IR term.** The obligor posts `stake` of `asset`: a per-asset
`bal` debit at `(obligor, asset)` ++ an `escrows` prepend of the unresolved record (the off-ledger stake lock).
This IS the proven `createEscrowStmt` under obligor↦creator, beneficiary↦recipient, stake↦amount — the body the
running executor dispatch-aliases the obligation create to. -/
def createObligationStmt (id : Nat) (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ) :
    RecStmt :=
  createEscrowStmt id actor obligor beneficiary asset stake

/-! ## §2 — THE CORNERSTONE: `interp` of the obligation term IS the obligation kernel step `createEscrowKAsset`.

Definitionally `createObligationStmt = createEscrowStmt …`, so the plain §E cornerstone
`interp_createEscrowStmt_eq_createEscrowKAsset` applies verbatim under the field-renaming: the obligation
create's `interp` IS `createEscrowKAsset k id actor obligor beneficiary asset stake`. -/

/-- **The cornerstone (obligation side-table).** `interp` of the createObligation term IS the verified kernel
step `createEscrowKAsset` under the obligation field-renaming (obligor↦creator, beneficiary↦recipient,
stake↦amount) — the same partial function by construction, exactly as the plain §E cornerstone (the obligation
create dispatch-aliases the escrow create body). -/
theorem interp_createObligationStmt_eq_createEscrowKAsset (id : Nat)
    (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ) (k : RecordKernelState) :
    interp (createObligationStmt id actor obligor beneficiary asset stake) k
      = createEscrowKAsset k id actor obligor beneficiary asset stake := by
  simp only [createObligationStmt]
  exact interp_createEscrowStmt_eq_createEscrowKAsset id actor obligor beneficiary asset stake k

#assert_axioms interp_createObligationStmt_eq_createEscrowKAsset

/-- **`interp_createObligationStmt_chained` — the IR term's executor, lifted to the running `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (createObligationStmt …) k = some k'`), the unified
action executor on the obligation-create action commits to the chained state `⟨k', escrowReceiptA actor ::
s.log⟩` (for any chained `s` over the kernel `k = s.kernel`). So the Argus term's kernel meaning lifts to the
genuine running obligation-create step `execFullA (.createObligationA …)` — the dispatch alias of
`createEscrowChainA`, anchored at the unified executor. -/
theorem interp_createObligationStmt_chained
    (s : RecChainedState) (id : Nat) (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
    (k' : RecordKernelState)
    (hexec : interp (createObligationStmt id actor obligor beneficiary asset stake) s.kernel = some k') :
    execFullA s (.createObligationA id actor obligor beneficiary asset stake)
      = some { kernel := k', log := escrowReceiptA actor :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `createEscrowKAsset`.
  rw [interp_createObligationStmt_eq_createEscrowKAsset] at hexec
  -- `execFullA (.createObligationA …)` IS `createEscrowChainA s …` (§0), which on a committing kernel step
  -- opens to `some ⟨k', escrowReceiptA actor :: s.log⟩`.
  rw [execFullA_createObligationA_kernelStep]
  unfold createEscrowChainA
  rw [hexec]

#assert_axioms interp_createObligationStmt_chained

/-! ## §3 — THE EXECUTOR-side per-cell projection of the obligation kernel step `createEscrowKAsset`.

The §E.1 analog (`Compile.lean createEscrowKAsset_proj_balLo`), proved locally to keep this module's import
surface to `Stmt` + `EffectVmEmitCreateEscrow`: a committed obligation create DEBITS the obligor cell's
projected `(obligor, asset)` ledger entry by exactly `stake` (the value parked off-ledger). The frozen frame
(balHi/nonce/fields/capRoot/reserved) is `0 = 0` on both projections of `cellProjCreate` (definitional). -/

/-- **`createObligationKAsset_proj_balLo`.** A committed obligation kernel create debits the obligor cell's
projected `(obligor, asset)` ledger entry by exactly `stake` (the value parked off-ledger). The per-cell
conserved leg the weld pins. -/
theorem createObligationKAsset_proj_balLo {k k' : RecordKernelState} {id : Nat}
    {actor obligor beneficiary : CellId} {asset : AssetId} {stake : ℤ}
    (h : createEscrowKAsset k id actor obligor beneficiary asset stake = some k') :
    (cellProjCreate k'.bal obligor asset).balLo
      = (cellProjCreate k.bal obligor asset).balLo - stake := by
  unfold createEscrowKAsset at h
  by_cases hg : authorizedB k.caps { actor := actor, src := obligor, dst := beneficiary, amt := stake } = true
      ∧ 0 ≤ stake ∧ stake ≤ k.bal obligor asset ∧ obligor ∈ k.accounts
      ∧ ¬ (∃ r ∈ k.escrows, r.id = id)
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    -- `(cellProjCreate (createEscrowRawAsset …).bal obligor asset).balLo = recBalCreditCell … obligor asset`
    show recBalCreditCell k.bal obligor asset (-stake) obligor asset = k.bal obligor asset - stake
    unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms createObligationKAsset_proj_balLo

/-! ## §4 — THE WELD: a satisfying witness of the SHARED escrow descriptor agrees, per cell, with the
post-state the IR term's executor interpretation produces — AND forces the genuine side-table root.

The circuit side is `createEscrowGenuine_sound` (the SHARED class-A soundness — createObligation has no
dedicated descriptor); the executor side is the §2 cornerstone + the §3 projection. The conclusion is the SAME
two legs the plain-createEscrow weld concludes, now over the obligation field-renaming. -/

/-- **`createObligation_compile_sound` — the welded soundness (createObligation slice, the side-table effect).**

Suppose, for the Argus obligation-create term
`createObligationStmt id actor obligor beneficiary asset stake`:
  * the SHARED audited class-A circuit `createEscrowVmDescriptorGenuine` is SATISFIED by `(env, true, true)`
    under the abstract Poseidon carrier `hash`, and its `RowEncodesCreate` decoding NAMES the post-state record
    `post` over the obligor cell's projection `cellProjCreate k.bal obligor asset` with the `⟨stake⟩` param
    block (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (createObligationStmt …) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's debited
    obligor-cell projection `cellProjCreate k'.bal obligor asset` — the conserved `balLo` (debited by `stake`)
    AND the whole frozen frame (balHi/fields/capRoot/reserved/nonce). The obligation create has NO nonce-tick
    divergence (the descriptor FREEZES the cell nonce, matching the executor — `cellProjCreate` sends `nonce`
    to `0` on both sides).
  * **side-table leg:** the circuit FORCES the new escrow-list-root carrier to be the genuine in-row recompute
    `advanceOf hash (leafOf hash id obligor beneficiary stake asset resolved) old_root` of the bound parked
    obligation record + old root — the digest the executor's `parkedRecord :: k.escrows` prepend commits to
    (absorbed into `state_commit`; a forged/dropped park MOVES the commitment).

So the SHARED class-A circuit the prover runs for the obligation create pins the per-cell debited state the IR
term's executor produces AND genuinely recomputes the bound `escrows` side-table root — the template
generalizes to the obligation create (a per-asset escrow lock under field-renaming). -/
theorem createObligation_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (actor obligor beneficiary : CellId)
    (asset : AssetId) (stake : ℤ)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (henc : RowEncodesCreate env (cellProjCreate k.bal obligor asset) ⟨stake⟩ post)
    (hsat : satisfiedVm hash createEscrowVmDescriptorGenuine env true true)
    (hexec : interp (createObligationStmt id actor obligor beneficiary asset stake) k = some k') :
    -- conserved leg: the debited (obligor) cell's projection agrees on balLo + the whole frozen frame …
    ( post.balLo = (cellProjCreate k'.bal obligor asset).balLo
      ∧ post.balHi = (cellProjCreate k'.bal obligor asset).balHi
      ∧ (∀ i, post.fields i = (cellProjCreate k'.bal obligor asset).fields i)
      ∧ post.capRoot = (cellProjCreate k'.bal obligor asset).capRoot
      ∧ post.reserved = (cellProjCreate k'.bal obligor asset).reserved
      ∧ post.nonce = (cellProjCreate k'.bal obligor asset).nonce )
    -- … and the SIDE-TABLE leg: the circuit FORCES the genuine escrow-list-root recompute (the bound parked
    -- obligation record + old root), absorbed into `state_commit`.
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
  -- circuit side: the SHARED audited class-A soundness forces the per-cell `CellCreateSpec` + the genuine root.
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    createEscrowGenuine_sound hash env (cellProjCreate k.bal obligor asset) post ⟨stake⟩ henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `createEscrowKAsset`; its per-cell projection gives the debited balLo (the frozen limbs are `0=0`).
  rw [interp_createObligationStmt_eq_createEscrowKAsset] at hexec
  have heLo := createObligationKAsset_proj_balLo hexec
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
           hcN.trans rfl⟩, hroot⟩
  -- balLo: circuit pins post = pre − stake; executor debits the projected entry by stake.
  rw [hcLo, heLo]

#assert_axioms createObligation_compile_sound

/-! ## §5 — NON-VACUITY: the obligation term genuinely posts the stake, and the gate REJECTS forged inputs.

The cornerstone/weld would be hollow if the obligation term never committed, if the post were a no-op, or if
the gate admitted everything. A fresh `0`-stake lock on the §C two-cell kernel `kC` (cell `0` Live, empty
`escrows`) grows the holding-store from `[]` to length `1` (the two-component move is real); the rejection
lemmas show each guard leg fails closed (overdraft, dead obligor, id-reuse), inherited from the shared escrow
gate. -/

/-- **NON-VACUITY (witness TRUE — the stake post is real).** Running the obligation term on the §C two-cell
kernel `kC` (cell `0` Live, empty `escrows`) with a fresh `0`-stake lock grows `escrows` from `[]` to length
`1` — the two-component move genuinely touches the side-table (the prepend is real, not a no-op). The `0` stake
keeps the gate's availability/non-negativity legs trivially satisfied so the commit fires. -/
theorem createObligationStmt_posts :
    (interp (createObligationStmt 7 0 0 1 0 0) kC).map (fun k => k.escrows.length) = some 1 := by
  rw [interp_createObligationStmt_eq_createEscrowKAsset]
  decide

/-- **NON-VACUITY (fail-closed: overdraft).** Posting MORE stake than the obligor holds in `asset` does NOT
commit — the term returns `none` (the AVAILABILITY leg of the shared escrow gate fails). No value is conjured.
Here cell `0` holds `0` of asset `0`, so a `1`-stake post overdrafts. -/
theorem createObligationStmt_rejects_overdraft :
    interp (createObligationStmt 7 0 0 1 0 1) kC = none := by
  rw [interp_createObligationStmt_eq_createEscrowKAsset]
  decide

/-- **NON-VACUITY (fail-closed: dead obligor).** Posting a stake out of a NON-account obligor (cell `5`, not in
`kC.accounts = {0,1}`) does NOT commit — the OBLIGOR-LIVENESS leg fails. So the gate is genuinely load-bearing,
not a no-op that always commits. -/
theorem createObligationStmt_rejects_dead_obligor :
    interp (createObligationStmt 7 5 5 1 0 0) kC = none := by
  rw [interp_createObligationStmt_eq_createEscrowKAsset]
  decide

#assert_axioms createObligationStmt_posts
#assert_axioms createObligationStmt_rejects_overdraft
#assert_axioms createObligationStmt_rejects_dead_obligor

end Dregg2.Circuit.Argus.Effects.CreateObligation
