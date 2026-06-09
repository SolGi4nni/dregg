/-
# Dregg2.Circuit.Argus.Effects.SlashObligation — the slashObligation effect welded into the Argus IR,
in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the side-table cornerstone for PLAIN escrow create; the sibling
`Argus/Effects/ReleaseEscrow.lean` welded the SETTLE-leg **release** (a `find?`-keyed, record-reading,
replace-in-place credit to the record's RECIPIENT), proving `interp (releaseEscrowStmt …) =
releaseEscrowKAsset` (the executor IS the meaning of the IR term) and welding it to the AUDITED class-A
genuine descriptor `releaseEscrowVmDescriptorGenuine`. This module does the SAME for the OBLIGATION
SLASH, dregg2's stake-FORFEIT effect: when an obligation's deadline passes without fulfilment, the
posted stake is TRANSFERRED from the holding-store to the BENEFICIARY (the dual of `fulfillObligation`,
which RETURNS the stake to the obligor on a met condition).

## The obligation slash is a DEFINITIONAL DISPATCH-ALIAS of plain escrow RELEASE — faithfully, not by fiat

The running executor dispatches `slashObligationA` to the EXACT plain-escrow RELEASE chained step
(`Exec/TurnExecutorFull.lean:3844`):

    execFullA s (.slashObligationA id actor) = releaseEscrowChainA s id actor

i.e. an obligation slash IS a per-asset escrow release under the obligation field-renaming (the
beneficiary = the escrow `recipient` who collects on a slash; the stake = the escrow `amount`). dregg1
confirms the aliasing at the apply layer: slash credits `record.beneficiary` (= escrow release,
`apply.rs:1656`), exactly as fulfil credits `record.obligor` (= escrow refund, `apply.rs:1574`). At the
KERNEL level `releaseEscrowChainA` is `releaseEscrowKAsset s.kernel id` under the settle-actor auth
gate (it stamps the receipt, `:2022`), so the obligation slash's KERNEL step is exactly
`releaseEscrowKAsset k id` — credit the FOUND unresolved record's `recipient`/beneficiary by `amount`
at the record's asset + `markResolved`. We prove that bridge (`execFullA_slashObligationA_kernelStep`,
NOT asserted) so the kernel target this module refines to is the genuine kernel projection of the
AUDITED chained executor — the running system's obligation slash, not a fresh invention. This is the
SAME aliasing the executor's own comment records ("Routes to `releaseEscrowChainA`", `:3381`) and the
circuit-fold layer treats as CLOSED (`slashObligation` dispatch-aliased to `releaseEscrow`).

Because the obligation slash runs the IDENTICAL body, the IR term IS the proven plain-escrow RELEASE
term `ReleaseEscrow.releaseEscrowStmt id` — reusing it (rather than re-inlining the gate + the two
component writes) is the honest encoding of "obligation slash = escrow release under field-renaming",
exactly the executor's own `slashObligationA ↦ releaseEscrowChainA` dispatch. The cornerstone here is
that `interp` of THIS term IS the obligation-slash kernel step.

## The descriptor — SHARED with plain escrow release (slashObligation has NO dedicated descriptor) — REPORTED

slashObligation carries NO standalone EffectVM descriptor: it is dispatch-aliased to plain escrow
release in EVERY circuit layer (it routes to `releaseEscrowChainA`, and `compileE .releaseEscrow`
returns `releaseEscrowVmDescriptorGenuine`). So the circuit it welds against is the AUDITED CLASS-A
`releaseEscrowVmDescriptorGenuine` + `releaseEscrowGenuine_sound`
(`Circuit/Emit/EffectVmEmitReleaseEscrow.lean`) — the SAME genuine-root-recompute descriptor plain
escrow release uses. On a satisfying row it forces (a) the per-cell `CellReleaseSpec` (the `balLo`
CREDIT by `amount`, every other limb FROZEN, the cell nonce FROZEN — release does NOT tick), (b) the
GENUINE in-row escrow-root RECOMPUTE (`SYS_DIG_AFTER = advanceOf hash (leafOf hash id creator recipient
amount asset resolved) SYS_DIG_BEFORE`, the side-table digest FORCED — not a free step), and (c) the
published commit. The side-table resolve is BOUND, not papered.

## HONEST SURFACE — exactly releaseEscrow's weld surface (do NOT over-read)

The weld concludes the SAME two legs the plain-escrow RELEASE weld concludes:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's settle-credited
    `bal r.recipient r.asset` at the FOUND record `r` (= pre + `r.amount`, the stake forfeited TO the
    beneficiary), with the frozen frame (balHi/fields/capRoot/reserved) AND the FROZEN nonce agreeing.
    `cellProjRelease` projects ONLY the `(recipient, asset)` ledger entry into `balLo` (the other limbs
    are `0`, FROZEN) — so this binds the CREDITED (beneficiary) CELL, exactly as transfer binds the SRC
    cell. The cross-cell combined per-asset conservation (off-ledger drop ⊕ ledger credit) is the
    executor's keystone (`releaseEscrow_conserves_combined` family), cited there — NOT re-claimed here.
  * **side-table leg (the resolved record):** the circuit FORCES the new escrow-list root to be the
    genuine recompute of the bound record content + the old root, absorbed into `state_commit`, so the
    resolved obligation record (id/obligor/beneficiary/stake/asset/resolved) is bound. The weld EXPOSES
    this genuine-recompute clause as a conjunct so the side-table binding is part of the welded statement.

What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the
executor's `markResolved k.escrows id` as a LIST (the EffectVM row carries a DIGEST, not the list — they
agree only up to the side-table root, the `SystemRoots` digest connector). The executor produces the
real resolved list (the `ReleaseEscrow` cornerstone + `markResolved`); the circuit produces the genuine
root of it. That digest-not-list boundary is faithful, stated, not hidden. There is NO nonce-tick
divergence (the descriptor FREEZES the cell nonce, matching the executor — `cellProjRelease` sends
`nonce` to `0` on both sides), so this module carries no nonce reconciliation.

## REPORTED DIVERGENCE — the post-deadline SLASH gate is a §8/theorem-layer carrier, NOT in this weld

slashObligation is DISTINCT from a plain escrow release by ONE gate the running system enforces but the
KERNEL step (and hence this weld) does NOT: dregg1's `apply_slash_obligation` rejects when the deadline
has NOT yet passed (`apply.rs:1637`, `block_height <= deadline_height`). The kernel step
`releaseEscrowKAsset` carries the settle-LIVENESS gate (the beneficiary must be a live account) but NOT
the post-deadline temporal gate, which dregg1/dregg2 carry at the §8/theorem layer (block-height) — the
SAME way the obligor-only/before-deadline gates of `fulfillObligation` are §8-carried, and the auth gate
of release is carried at `releaseEscrowChainA` (`releaseSettleAuthB`, above the kernel step). So this
weld pins the per-asset settle SEMANTICS (credit the beneficiary + resolve + genuine root) that the
slash and a plain release SHARE, and EXPLICITLY does not claim the post-deadline admissibility, which is
out of the EffectVM row's scope. This is carried as an honest note, not hidden — the same boundary the
executor's own `slashObligationA` doc-comment draws ("DISTINCT from `releaseEscrowA` by the post-deadline
slash gate").

## Honesty

`#assert_axioms` on the keystones (`execFullA_slashObligationA_kernelStep`,
`interp_slashObligationStmt_eq_releaseEscrowKAsset`, `slashObligation_compile_sound`) ⊆ {propext,
Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via the named `Poseidon2SpongeCR` hypothesis
(inside the cited anti-ghost `releaseEscrowGenuine_binds_record`, not these theorems). No `sorry`, no
`:= True`, no `native_decide`. This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Argus.Effects.ReleaseEscrow

namespace Dregg2.Circuit.Argus.Effects.SlashObligation

open Dregg2.Exec
-- The CHAINED obligation/escrow executor (`slashObligationA` dispatches to `releaseEscrowChainA`) + the
-- kernel step + the receipt stamp live in `Dregg2.Exec.TurnExecutorFull`; opened so the §0 kernel-bridge
-- lemma can name them. `releaseEscrowKAsset` is the RecordKernel SETTLE step (credit the found record's
-- recipient at its asset + `markResolved`).
open Dregg2.Exec.TurnExecutorFull (execFullA releaseEscrowChainA escrowReceiptA)
open Dregg2.Exec (releaseEscrowKAsset settleEscrowRawAsset markResolved recBalCreditCell cellLifecycleLive)
-- `VmRowEnv` / `satisfiedVm` / `prmCol` are the unqualified EffectVM IR names (exactly as the sibling
-- `ReleaseEscrow.lean` opens them) — without this they resolve to the fully-qualified path only.
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
-- The proven plain-escrow RELEASE Argus term + its cornerstone + the per-cell projection + the find-pred
-- (the body the obligation slash dispatch-aliases). This is the SIBLING module's public surface — reused,
-- never re-proved (the honest encoding of "slash = release under field-renaming").
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Argus.Effects.ReleaseEscrow
  (releaseEscrowStmt interp_releaseEscrowStmt_eq_releaseEscrowKAsset releaseEscrowKAsset_proj_balLo
   findUnresolved kR0)
-- The SHARED class-A escrow-RELEASE descriptor + its soundness + the per-cell projection (slashObligation
-- has NO dedicated descriptor — see header). Same names `ReleaseEscrow.lean` opens.
open Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow
  (releaseEscrowVmDescriptorGenuine releaseEscrowGenuine_sound ReleaseParams CellReleaseSpec
   RowEncodesRelease cellProjRelease)

/-! ## §0 — THE KERNEL TARGET: the obligation SLASH kernel step IS the audited plain-escrow RELEASE step.

The sibling release cornerstone (`ReleaseEscrow.lean`) refines its IR term to the KERNEL step
`releaseEscrowKAsset`. The obligation slash dispatch-aliases the WHOLE chained step `releaseEscrowChainA`
(under the obligation field-renaming beneficiary↦recipient, stake↦amount), so we prove (NOT assert) that
`execFullA (.slashObligationA …)` IS that chained step — anchoring the kernel target this module refines
to in the running system, not a fresh invention. -/

/-- **`execFullA_slashObligationA_kernelStep` — the bridge (PROVED, not asserted).** The unified action
executor on the obligation-slash action IS the audited plain-escrow RELEASE chained step
`releaseEscrowChainA` under the obligation field-renaming (beneficiary↦recipient, stake↦amount). So the
obligation slash is, on the nose, a per-asset escrow release — the dispatch aliasing the executor and
circuit-fold layers already record, here pinned at the `execFullA` entry. -/
theorem execFullA_slashObligationA_kernelStep (s : RecChainedState) (id : Nat) (actor : CellId) :
    execFullA s (.slashObligationA id actor) = releaseEscrowChainA s id actor := rfl

#assert_axioms execFullA_slashObligationA_kernelStep

/-! ## §1 — THE IR TERM: the proven plain-escrow RELEASE body, under the obligation field-renaming.

`slashObligationStmt id = ReleaseEscrow.releaseEscrowStmt id` — the PLAIN-escrow RELEASE IR term the
sibling cornerstone already refined to `releaseEscrowKAsset`. Reusing `releaseEscrowStmt` (rather than
re-inlining the `find?`-keyed gate ++ the `setBal` credit ++ the `setEscrows` `markResolved`) is the
honest encoding of "obligation slash = escrow release under field-renaming" — exactly the executor's own
`slashObligationA ↦ releaseEscrowChainA` dispatch. (The slash takes only `id` + `actor`: the
beneficiary/stake/asset are READ from the FOUND parked record, never free arguments — the settle shape.) -/

/-- **The slashObligation effect as an Argus IR term.** The deadline passed: the stake parked under the
obligation record `id` is FORFEITED to the beneficiary — a per-asset `bal` CREDIT at `(recipient, asset)`
of the FOUND record by `amount` ++ a `markResolved` on the `escrows` side-table. This IS the proven
`releaseEscrowStmt id` under beneficiary↦recipient, stake↦amount — the body the running executor
dispatch-aliases the obligation slash to. -/
def slashObligationStmt (id : Nat) : RecStmt :=
  releaseEscrowStmt id

/-! ## §2 — THE CORNERSTONE: `interp` of the slash term IS the obligation-slash kernel step
`releaseEscrowKAsset`.

Definitionally `slashObligationStmt = releaseEscrowStmt …`, so the sibling release cornerstone
`interp_releaseEscrowStmt_eq_releaseEscrowKAsset` applies verbatim under the field-renaming: the
obligation slash's `interp` IS `releaseEscrowKAsset k id`. -/

/-- **The cornerstone (obligation settle side-table).** `interp` of the slashObligation term IS the
verified kernel step `releaseEscrowKAsset` under the obligation field-renaming (beneficiary↦recipient,
stake↦amount) — the same partial function by construction, exactly as the sibling release cornerstone
(the obligation slash dispatch-aliases the escrow release body). -/
theorem interp_slashObligationStmt_eq_releaseEscrowKAsset (id : Nat) (k : RecordKernelState) :
    interp (slashObligationStmt id) k = releaseEscrowKAsset k id := by
  simp only [slashObligationStmt]
  exact interp_releaseEscrowStmt_eq_releaseEscrowKAsset id k

#assert_axioms interp_slashObligationStmt_eq_releaseEscrowKAsset

/-- **`interp_slashObligationStmt_chained` — the IR term's executor, lifted to the running `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (slashObligationStmt …) k = some k'`), the
unified action executor on the obligation-slash action commits to the chained state
`⟨k', escrowReceiptA actor :: s.log⟩` (for any chained `s` over the kernel `k = s.kernel`), PROVIDED the
running step's settle-actor auth gate `releaseSettleAuthB` holds (`hauth`). So the Argus term's kernel
meaning lifts to the genuine running obligation-slash step `execFullA (.slashObligationA …)` — the
dispatch alias of `releaseEscrowChainA`, anchored at the unified executor.

(The `hauth` hypothesis is the HONEST seam: the KERNEL step `releaseEscrowKAsset` — the thing the IR term
refines to — does NOT itself carry the settle-actor auth gate; that gate lives one layer up in the
chained `releaseEscrowChainA`. We expose it as a hypothesis rather than hide it.) -/
theorem interp_slashObligationStmt_chained
    (s : RecChainedState) (id : Nat) (actor : CellId) (k' : RecordKernelState)
    (hauth : Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB s.kernel id actor = true)
    (hexec : interp (slashObligationStmt id) s.kernel = some k') :
    execFullA s (.slashObligationA id actor)
      = some { kernel := k', log := escrowReceiptA actor :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `releaseEscrowKAsset`.
  rw [interp_slashObligationStmt_eq_releaseEscrowKAsset] at hexec
  -- `execFullA (.slashObligationA …)` IS `releaseEscrowChainA s …` (§0), which under the settle-actor
  -- auth gate, on a committing kernel step, opens to `some ⟨k', escrowReceiptA actor :: s.log⟩`.
  rw [execFullA_slashObligationA_kernelStep]
  unfold releaseEscrowChainA
  rw [if_pos hauth, hexec]

#assert_axioms interp_slashObligationStmt_chained

/-! ## §3 — THE WELD: a satisfying witness of the SHARED escrow-RELEASE descriptor agrees, per cell, with
the post-state the IR term's executor interpretation produces — AND forces the genuine side-table root.

The circuit side is `releaseEscrowGenuine_sound` (the SHARED class-A soundness — slashObligation has no
dedicated descriptor); the executor side is the §2 cornerstone + the sibling per-cell projection
`releaseEscrowKAsset_proj_balLo`. The conclusion is the SAME two legs the plain-escrow RELEASE weld
concludes (`ReleaseEscrow.releaseEscrow_compile_sound`), now under the obligation field-renaming. -/

/-- **`slashObligation_compile_sound` — the welded soundness (slashObligation slice, the SETTLE side-table
effect).**

Suppose, for the Argus obligation-slash term `slashObligationStmt id`:
  * the SHARED audited class-A circuit `releaseEscrowVmDescriptorGenuine` is SATISFIED by `(env, true,
    true)` under the abstract Poseidon carrier `hash`, and its `RowEncodesRelease` decoding NAMES the
    post-state record `post` over the beneficiary cell's pre-projection
    `cellProjRelease k.bal r.recipient r.asset` (for the FOUND record `r`) crediting `r.amount` with the
    `⟨amount⟩` param block (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (slashObligationStmt id) k = some k'` (`hexec`).

Then there is a FOUND record `r` (`findUnresolved k id = some r`, the holding-store entry the slash
forfeits) such that:
  * **conserved leg (per-cell):** the circuit's pinned `post` AGREES with the executor's settle-credited
    beneficiary-cell projection `cellProjRelease k'.bal r.recipient r.asset` — the conserved `balLo`
    (credited by `r.amount`, the stake forfeited) AND the whole frozen frame (balHi/fields/capRoot/
    reserved) AND the FROZEN nonce. The obligation slash has NO nonce-tick divergence (the descriptor
    FREEZES the cell nonce, matching the executor — `cellProjRelease` sends `nonce` to `0` on both sides).
  * **side-table leg:** the circuit FORCES the new escrow-list-root carrier to be the genuine in-row
    recompute `advanceOf hash (leafOf hash id creator recipient amount asset resolved) old_root` of the
    bound resolved obligation record + old root — the digest the executor's `escrows := markResolved
    k.escrows id` resolve commits to (absorbed into `state_commit`; a forged/un-resolved record MOVES the
    commitment — `releaseEscrowGenuine_binds_record`, cited).

So the SHARED class-A circuit the prover runs for the obligation slash pins the per-cell forfeited state
the IR term's executor produces AND genuinely recomputes the bound `escrows` side-table root — the
template generalizes to the obligation slash (a per-asset escrow release under field-renaming). This is
the per-asset settle SEMANTICS the slash and a plain release SHARE; the post-deadline temporal gate is a
§8/theorem-layer carrier, explicitly OUT of this weld (header REPORTED DIVERGENCE). -/
theorem slashObligation_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (amount : ℤ)
    (post : CellState)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptorGenuine env true true)
    (hexec : interp (slashObligationStmt id) k = some k')
    (henc : ∃ r, findUnresolved k id = some r ∧ r.amount = amount ∧
      RowEncodesRelease env (cellProjRelease k.bal r.recipient r.asset) ⟨amount⟩ post) :
    ∃ r, findUnresolved k id = some r ∧
      -- conserved leg: the credited (beneficiary) cell's projection agrees on balLo + the whole frozen frame …
      ( post.balLo = (cellProjRelease k'.bal r.recipient r.asset).balLo
        ∧ post.balHi = (cellProjRelease k'.bal r.recipient r.asset).balHi
        ∧ (∀ i, post.fields i = (cellProjRelease k'.bal r.recipient r.asset).fields i)
        ∧ post.capRoot = (cellProjRelease k'.bal r.recipient r.asset).capRoot
        ∧ post.reserved = (cellProjRelease k'.bal r.recipient r.asset).reserved
        ∧ post.nonce = (cellProjRelease k'.bal r.recipient r.asset).nonce )
      -- … and the SIDE-TABLE leg: the circuit FORCES the genuine escrow-list-root recompute (the bound
      -- resolved obligation record + old root), absorbed into `state_commit`.
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
  obtain ⟨r, hfind, hamt, hrenc⟩ := henc
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `releaseEscrowKAsset`; its sibling per-cell projection gives the credited balLo (frozen limbs `0=0`).
  rw [interp_slashObligationStmt_eq_releaseEscrowKAsset] at hexec
  obtain ⟨r', hfind', heLo⟩ := releaseEscrowKAsset_proj_balLo hexec
  -- the found record is unique (`find?` is a function), so `r' = r`.
  rw [hfind] at hfind'; cases hfind'
  -- circuit side: the SHARED audited class-A soundness forces the per-cell `CellReleaseSpec` + the root.
  subst hamt
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    releaseEscrowGenuine_sound hash env (cellProjRelease k.bal r.recipient r.asset) post ⟨r.amount⟩ hrenc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  refine ⟨r, hfind, ⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
    hcN.trans rfl⟩, hroot⟩
  -- balLo: circuit pins post = pre + r.amount; executor credits the projected entry by r.amount.
  rw [hcLo, heLo]

#assert_axioms slashObligation_compile_sound

/-! ## §4 — NON-VACUITY: the slash term genuinely FORFEITS the stake to the beneficiary, RESOLVES the
record, and the gate REJECTS a missing id. AND the SHARED descriptor is the genuine class-A one.

The cornerstone/weld would be hollow if the slash term never committed, if the `markResolved` resolve
were a no-op, or if the credit vanished. We reuse the sibling's concrete kernel `kR0` (it parks ONE
unresolved escrow: id 7, recipient/beneficiary cell 1, amount/stake 30, asset 0 — read as the obligation
record obligor↦creator 0, beneficiary↦recipient 1, stake↦amount 30): running the slash term FORFEITS the
30-stake to the beneficiary (cell 1's `(1,0)` ledger entry rises `0 → 30`), RESOLVES the record (its
`resolved` flag flips `false → true`, the FILTER write is real, not a no-op), and a slash of a missing id
fails closed. And the SHARED descriptor carries the 34 per-row gates + 6 hash-sites (2 genuine
escrow-recompute + 4 commitment), distinct from the inert placeholder. -/

/-- **NON-VACUITY (witness TRUE — the stake FORFEIT is real).** Running the slash term for `id = 7` on the
sibling kernel `kR0` (the parked obligation record, beneficiary cell 1, stake 30, asset 0) commits and
raises the beneficiary cell `1`'s per-asset `(1, 0)` ledger entry from `0` to `30` — the staked value
genuinely forfeits TO the beneficiary on the slash. -/
theorem slashObligationStmt_forfeits :
    (interp (slashObligationStmt 7) kR0).map (fun k => k.bal 1 0) = some 30 := by
  rw [interp_slashObligationStmt_eq_releaseEscrowKAsset]
  decide

/-- **NON-VACUITY (the settle write is OBSERVABLE — the record RESOLVES).** The committed slash flips the
parked obligation record's `resolved` flag `false → true`: the `markResolved` FILTER write is a real,
observable holding-store mutation (the record LEAVES the unresolved set), not a no-op. -/
theorem slashObligationStmt_resolves :
    (interp (slashObligationStmt 7) kR0).map
        (fun k => (k.escrows.head?.map (fun r => r.resolved)).getD false) = some true := by
  rw [interp_slashObligationStmt_eq_releaseEscrowKAsset]
  decide

/-- **NON-VACUITY (fail-closed).** A slash of a NON-existent obligation id (`99`) does NOT commit — the
term returns `none` (the gate's `find?` is `none`), so the forfeit/resolve never fires on a missing
record. The cornerstone's two-valued, non-vacuous reject side. -/
theorem slashObligationStmt_rejects_missing :
    interp (slashObligationStmt 99) kR0 = none := by
  rw [interp_slashObligationStmt_eq_releaseEscrowKAsset]
  decide

/-- The welded slashObligation circuit is the genuine class-A SHARED escrow-release descriptor, NOT the
empty placeholder: it carries the 34 per-row constraints (credit + frame freeze + transition/boundary)
and the 6 hash-sites (2 genuine escrow-root-recompute + 4 commitment). So `slashObligation_compile_sound`
is about a REAL side-table-binding circuit. -/
theorem slashObligationDescriptorGenuine_nontrivial :
    releaseEscrowVmDescriptorGenuine.constraints.length = 34
    ∧ releaseEscrowVmDescriptorGenuine.hashSites.length = 6
    ∧ releaseEscrowVmDescriptorGenuine.ranges.length = 2 := by
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms slashObligationStmt_forfeits
#assert_axioms slashObligationStmt_resolves
#assert_axioms slashObligationStmt_rejects_missing
#assert_axioms slashObligationDescriptorGenuine_nontrivial

/-! ## §6 — FULL-STATE on the RUNNABLE descriptor (the magnesium breadth — bind ALL 17 fields).

`slashObligationStmt = releaseEscrowStmt` definitionally, so the FULL-STATE release weld
(`ReleaseEscrow.releaseEscrow_runnable_full_state` over the WIDE descriptor `releaseEscrowVmDescriptorWide`)
applies VERBATIM on the slash term: a satisfying row of the WIDE RUNNABLE descriptor binds the FULL
17-field post-state (the beneficiary/recipient-cell CREDIT AND the `escrows` digest advance), all 17
bound by the circuit the prover RUNS (the generic anti-ghost gives the no-malleability tooth). -/

open Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrowWide (releaseEscrowVmDescriptorWide)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide (ESCROW_STEP_PARAM)
open Dregg2.Circuit.Argus.Effects.ReleaseEscrow (releaseEscrow_runnable_full_state)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest)

/-- **`slashObligation_runnable_full_state` — THE FULL-STATE WELD (slashObligation).** The full-state
release weld lifted verbatim onto the slash term (the dispatch-alias): for the FOUND record `r`, a
satisfying row of the WIDE RUNNABLE descriptor agrees per-cell with the executor's settle-credited
recipient-cell projection on EVERY limb AND binds the `escrows` side-table digest advance — all 17 fields. -/
theorem slashObligation_runnable_full_state
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (amount : ℤ)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (preRoots postRoots : SysRoots) (step : ℤ)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow.IsReleaseEscrowRow env)
    (hAfter : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestCol
                = systemRootsDigest hash postRoots)
    (hBefore : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestColBefore
                = systemRootsDigest hash preRoots)
    (hStep : env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptorWide env true true)
    (hexec : interp (slashObligationStmt id) k = some k')
    (henc : ∃ r, findUnresolved k id = some r ∧ r.amount = amount ∧
      RowEncodesRelease env (cellProjRelease k.bal r.recipient r.asset) ⟨amount⟩ post) :
    ∃ r, findUnresolved k id = some r ∧
      ( post.balLo = (cellProjRelease k'.bal r.recipient r.asset).balLo
        ∧ post.balHi = (cellProjRelease k'.bal r.recipient r.asset).balHi
        ∧ (∀ i, post.fields i = (cellProjRelease k'.bal r.recipient r.asset).fields i)
        ∧ post.capRoot = (cellProjRelease k'.bal r.recipient r.asset).capRoot
        ∧ post.reserved = (cellProjRelease k'.bal r.recipient r.asset).reserved
        ∧ post.nonce = (cellProjRelease k'.bal r.recipient r.asset).nonce )
      ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step := by
  have hexec' : interp (releaseEscrowStmt id) k = some k' := by
    rw [slashObligationStmt] at hexec; exact hexec
  exact releaseEscrow_runnable_full_state hash env k k' id amount post preRoots postRoots step
    hrow hAfter hBefore hStep hsat hexec' henc

#assert_axioms slashObligation_runnable_full_state

end Dregg2.Circuit.Argus.Effects.SlashObligation
