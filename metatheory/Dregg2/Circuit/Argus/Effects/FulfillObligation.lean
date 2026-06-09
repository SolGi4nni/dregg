/-
# Dregg2.Circuit.Argus.Effects.FulfillObligation — the fulfillObligation effect welded into the Argus IR,
in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and `Effects/
RefundEscrow.lean` welded the SETTLE-leg sibling refundEscrow: `interp (refundEscrowStmt id) =
refundEscrowKAsset` (read the found record, CREDIT its `creator` `+amount`, `markResolved` the holding
store), then welded that term to the AUDITED class-A genuine descriptor `refundEscrowVmDescriptorGenuine`
(`Circuit/Emit/EffectVmEmitRefundEscrow`). This module does the SAME for the OBLIGATION FULFIL, dregg2's
stake-DISCHARGE effect: on fulfilment the obligor met the condition and RECLAIMS the staked collateral.

## The obligation fulfil is a DEFINITIONAL DISPATCH-ALIAS of escrow REFUND — faithfully, not by fiat

The running executor dispatches `fulfillObligationA` to the EXACT plain-escrow REFUND chained step
(`Exec/TurnExecutorFull.lean:3840`):

    execFullA s (.fulfillObligationA id actor) = refundEscrowChainA s id actor

i.e. an obligation fulfil IS a per-asset escrow refund — the staked value RETURNS to the record's
`creator` (the obligor who posted it). dregg1 confirms the aliasing at the apply layer: fulfil credits
`record.obligor` (`apply.rs:1574`), which is exactly the escrow refund target (`createObligation` posts the
stake as the escrow `creator` debit — see `Effects/CreateObligation.lean`'s obligor↦creator renaming, so
the obligor IS the record's `creator`). At the KERNEL level `refundEscrowChainA` is `refundEscrowKAsset
s.kernel id` (it stamps the receipt log; the settle-actor gate `refundSettleAuthB` is the §8/theorem-layer
carrier), so the obligation fulfil's KERNEL step is exactly `refundEscrowKAsset k id`. We prove that bridge
(`execFullA_fulfillObligationA_kernelStep`, NOT asserted) so the kernel target this module refines to is the
genuine kernel projection of the AUDITED chained executor — the running system's obligation fulfil, not a
fresh invention. This is the SAME aliasing the executor records (`fulfillObligationA ↦ refundEscrowChainA`,
verbatim the line `refundEscrowA ↦ refundEscrowChainA` runs) and `Exec/Handlers/Escrow.lean:294`
(`fulfillObligationA = refundEscrowA`) already states.

Because the obligation fulfil runs the IDENTICAL body, the IR term IS the proven refund term
`refundEscrowStmt id` — reusing it (rather than re-inlining the `setBal` credit ++ `setEscrows` resolve)
is the honest encoding of "obligation fulfil = escrow refund", exactly the executor's own
`fulfillObligationA ↦ refundEscrowChainA` dispatch. The cornerstone here is that `interp` of THIS term IS
the obligation-fulfil kernel step.

## The descriptor — SHARED with refundEscrow (fulfillObligation has NO dedicated descriptor) — REPORTED

fulfillObligation carries NO standalone EffectVM descriptor: it is dispatch-aliased to escrow refund in
EVERY layer (the executor dispatch above; `Exec/Handlers/Escrow.lean:294` `fulfillObligationA =
refundEscrowA`; the obligations all "reuse the SAME" automaton, `Exec/EffectsPaired.lean:541`). So the
circuit it welds against is the AUDITED CLASS-A `refundEscrowVmDescriptorGenuine` +
`refundEscrowGenuine_sound` (`Circuit/Emit/EffectVmEmitRefundEscrow.lean`) — the SAME genuine-root-recompute
descriptor escrow refund uses. On a satisfying row it forces (a) the per-cell `CellRefundSpec` (the moved
cell's `balLo` CREDIT by the parked `amount`, every other limb FROZEN), (b) the GENUINE in-row escrow-root
RECOMPUTE (`SYS_DIG_AFTER = advanceOf hash (leafOf hash id creator recipient amount asset resolved)
SYS_DIG_BEFORE`, the side-table digest FORCED — not a free step; `resolved = 1` on a refund), and (c) the
published commit. The side-table RESOLVE is BOUND, not papered.

## HONEST SURFACE — exactly refundEscrow's weld surface (do NOT over-read)

The weld concludes the SAME two legs the refundEscrow weld concludes, on the FOUND record `r`:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's CREDITED
    creator-cell projection `cellProjRefund k'.bal r.creator r.asset` (= pre **+** `r.amount`), with the
    frozen frame (balHi/fields/capRoot/reserved/nonce) agreeing. `cellProjRefund` projects ONLY the
    `(creator, asset)` ledger entry into `balLo` (every other limb is `0`, FROZEN) — so this binds the
    REFUNDED (obligor) CELL, exactly as transfer binds the SRC cell. fulfillObligation has NO nonce-tick
    divergence (the descriptor FREEZES the cell nonce, matching the executor — `cellProjRefund` sends
    `nonce` to `0` on both sides). The cross-cell combined-per-asset conservation (ledger credit ⊕
    holding-store drop) is the executor's keystone (`refundEscrowKAsset_conserves_combined_per_asset`,
    `RecordKernel.lean:1677`), cited there — NOT re-claimed here.
  * **side-table leg (the resolved record):** the circuit FORCES the new escrow-list root to be the genuine
    in-row recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the bound
    resolved record + old root (`refundEscrowGenuine_sound`'s clause (b), with `resolved = 1` on a fulfil),
    absorbed into `state_commit`. So under `Poseidon2SpongeCR` the resolved record is bound — a
    dropped/forged resolve MOVES the commitment (`refundEscrowGenuine_binds_record`, cited).

  What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the executor's
  `markResolved k.escrows id` as a LIST (the EffectVM row carries a DIGEST, not the list — the
  `SystemRoots` digest connector). The executor produces the real list (the cornerstone + `markResolved`);
  the circuit produces the genuine root of it. That is the faithful digest-not-list boundary, stated, not
  hidden.

## DIVERGENCE the weld carries explicitly (the obligor-only fulfil gate is NOT in the kernel step)

dregg1's `apply_fulfill_obligation` additionally enforces an OBLIGOR-ONLY, BEFORE-DEADLINE admission gate
(`TurnExecutorFull.lean:3364`, "DISTINCT from `refundEscrowA` by the obligor-only fulfil gate"). The KERNEL
step `refundEscrowKAsset` this module welds does NOT carry that gate — it is a §8/theorem-layer carrier
(exactly as the dispatch comment at `:3837` records: "the obligor-only + before-deadline gates are
§8/theorem-layer carriers"). So `fulfillObligation_compile_sound` welds the STAKE-RETURN transition
(credit-the-obligor + resolve + genuine root) faithfully, but does NOT bind the obligor-identity /
deadline admission of the fulfil — that is the chained executor's `refundSettleAuthB` settle-actor gate
(carried in `refundEscrowChainA`, which the §2.1 `execFullA` lift goes through) PLUS the dregg1 obligor
predicate, not the per-row circuit. This divergence is reported, not hidden, and is IDENTICAL in kind to
the createObligation weld's "obligor-only is a §8 carrier" note.

## Honesty

`#assert_axioms` on both keystones (`interp_fulfillObligationStmt_eq_refundEscrowKAsset` and
`fulfillObligation_compile_sound`) ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via
the named `Poseidon2SpongeCR` hypothesis (inside the cited anti-ghost `refundEscrowGenuine_binds_record`,
not these theorems). No `sorry`, no `:= True`, no `native_decide`. This module OWNS only itself; every
import is read-only and it edits no other Argus file.
-/
import Dregg2.Circuit.Argus.Effects.RefundEscrow

namespace Dregg2.Circuit.Argus.Effects.FulfillObligation

open Dregg2.Exec
-- The CHAINED obligation-fulfil/escrow-refund executor (`fulfillObligationA` dispatches to
-- `refundEscrowChainA`) + the kernel step + the receipt stamp live in `Dregg2.Exec.TurnExecutorFull`;
-- opened so the §0 kernel-bridge lemma can name them.
open Dregg2.Exec.TurnExecutorFull (execFullA refundEscrowChainA escrowReceiptA)
open Dregg2.Exec (RecordKernelState EscrowRecord CellId AssetId
  refundEscrowKAsset settleEscrowRawAsset markResolved recBalCreditCell cellLifecycleLive)
-- `VmRowEnv` / `satisfiedVm` / `prmCol` are the unqualified EffectVM IR names (exactly as the
-- RefundEscrow weld opens them).
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
-- The proven refundEscrow Argus term + its cornerstone + the per-cell projection + the WELD + the find
-- predicate + the §3 non-vacuity kernel + `compileRefund` (the body/descriptor the obligation fulfil
-- dispatch-aliases). This module reuses these wholesale under the obligation reading.
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Argus.Effects.RefundEscrow
  (refundEscrowStmt matchPred interp_refundEscrowStmt_eq_refundEscrowKAsset
   refundEscrowKAsset_proj_balLo refundEscrow_compile_sound compileRefund compileRefund_eq
   refundEscrowStmt_resolves refundEscrowStmt_rejects_missing kR)
-- The SHARED class-A escrow-refund descriptor + its soundness + the per-cell projection + the row-encode/
-- params (fulfillObligation has NO dedicated descriptor — see header).
open Dregg2.Circuit.Emit.EffectVmEmitRefundEscrow
  (refundEscrowVmDescriptorGenuine refundEscrowGenuine_sound cellProjRefund RefundParams
   RowEncodesRefund CellRefundSpec)

/-! ## §0 — THE KERNEL TARGET: the obligation FULFIL kernel step IS the audited escrow-REFUND chained step.

The refundEscrow §2 cornerstone (`Effects/RefundEscrow.lean`) refines its IR term to the KERNEL step
`refundEscrowKAsset`. The obligation fulfil dispatch-aliases the WHOLE chained step `refundEscrowChainA`
(the staked value returns to the record's `creator` = the obligor), so we prove (NOT assert) that
`execFullA (.fulfillObligationA …)` IS that chained step — anchoring the kernel target this module refines
to in the running system, not a fresh invention. -/

/-- **`execFullA_fulfillObligationA_kernelStep` — the bridge (PROVED, not asserted).** The unified action
executor on the obligation-fulfil action IS the audited escrow-REFUND chained step `refundEscrowChainA` —
verbatim the line the escrow `refundEscrowA` action runs (`TurnExecutorFull.lean:3840` vs `:3834`). So the
obligation fulfil is, on the nose, a per-asset escrow refund: the staked collateral returns to the
record's `creator` (the obligor). This is the dispatch aliasing the executor and handler layers already
record, here pinned at the `execFullA` entry. -/
theorem execFullA_fulfillObligationA_kernelStep (s : RecChainedState) (id : Nat) (actor : CellId) :
    execFullA s (.fulfillObligationA id actor) = refundEscrowChainA s id actor := rfl

#assert_axioms execFullA_fulfillObligationA_kernelStep

/-! ## §1 — THE IR TERM: the proven refundEscrow body (the obligation fulfil dispatch-aliases it).

`fulfillObligationStmt id = refundEscrowStmt id` — the refundEscrow IR term the §2 cornerstone of
`Effects/RefundEscrow.lean` already refined to `refundEscrowKAsset`. Reusing `refundEscrowStmt` (rather
than re-inlining the `setBal` credit ++ `setEscrows` resolve) is the honest encoding of "obligation fulfil
= escrow refund" — exactly the executor's own `fulfillObligationA ↦ refundEscrowChainA` dispatch. -/

/-- **The fulfillObligation effect as an Argus IR term.** On fulfilment the obligor reclaims the staked
collateral: a per-asset `bal` credit at the found record's `(creator, asset)` ++ a `markResolved` of the
record on the `escrows` side-table (the off-ledger stake DISCHARGE). This IS the proven `refundEscrowStmt`
— the body the running executor dispatch-aliases the obligation fulfil to. -/
def fulfillObligationStmt (id : Nat) : RecStmt :=
  refundEscrowStmt id

/-! ## §2 — THE CORNERSTONE: `interp` of the fulfil term IS the obligation kernel step `refundEscrowKAsset`.

Definitionally `fulfillObligationStmt = refundEscrowStmt`, so the refundEscrow §2 cornerstone
`interp_refundEscrowStmt_eq_refundEscrowKAsset` applies verbatim: the obligation fulfil's `interp` IS
`refundEscrowKAsset k id`. -/

/-- **The cornerstone (obligation fulfil — settle side-table).** `interp` of the fulfillObligation term IS
the verified kernel step `refundEscrowKAsset` — the same partial function by construction, exactly as the
refundEscrow §2 cornerstone (the obligation fulfil dispatch-aliases the escrow refund body: read the found
record, CREDIT its `creator` `+amount`, `markResolved` the holding store). -/
theorem interp_fulfillObligationStmt_eq_refundEscrowKAsset (id : Nat) (k : RecordKernelState) :
    interp (fulfillObligationStmt id) k = refundEscrowKAsset k id := by
  simp only [fulfillObligationStmt]
  exact interp_refundEscrowStmt_eq_refundEscrowKAsset id k

#assert_axioms interp_fulfillObligationStmt_eq_refundEscrowKAsset

/-- **`interp_fulfillObligationStmt_chained` — the IR term's executor, lifted to the running `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (fulfillObligationStmt id) s.kernel = some k'`) AND
the chained settle-actor gate `refundSettleAuthB` admits (`hauth` — the gate `refundEscrowChainA` checks,
which the kernel step alone does NOT, see the DIVERGENCE note), the unified action executor on the
obligation-fulfil action commits to `⟨k', escrowReceiptA actor :: s.log⟩`. So the Argus term's kernel
meaning lifts to the genuine running obligation-fulfil step `execFullA (.fulfillObligationA …)` — the
dispatch alias of `refundEscrowChainA`, anchored at the unified executor. The `hauth` hypothesis makes the
settle-actor gate EXPLICIT (it is part of the running step but NOT of the welded kernel transition). -/
theorem interp_fulfillObligationStmt_chained
    (s : RecChainedState) (id : Nat) (actor : CellId) (k' : RecordKernelState)
    (hexec : interp (fulfillObligationStmt id) s.kernel = some k')
    (hauth : Dregg2.Exec.TurnExecutorFull.refundSettleAuthB s.kernel id actor = true) :
    execFullA s (.fulfillObligationA id actor)
      = some { kernel := k', log := escrowReceiptA actor :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `refundEscrowKAsset`.
  rw [interp_fulfillObligationStmt_eq_refundEscrowKAsset] at hexec
  -- `execFullA (.fulfillObligationA …)` IS `refundEscrowChainA s …` (§0); under the admitting settle-actor
  -- gate and the committing kernel step it opens to `some ⟨k', escrowReceiptA actor :: s.log⟩`.
  rw [execFullA_fulfillObligationA_kernelStep]
  unfold refundEscrowChainA
  rw [if_pos hauth, hexec]

#assert_axioms interp_fulfillObligationStmt_chained

/-! ## §3 — THE WELD: a satisfying witness of the SHARED escrow-REFUND descriptor agrees, per cell, with
the post-state the IR term's executor interpretation produces — AND forces the genuine side-table root.

The circuit side is `refundEscrowGenuine_sound` (the SHARED class-A soundness — fulfillObligation has no
dedicated descriptor); the executor side is the §2 cornerstone + the refundEscrow per-cell projection. The
conclusion is the SAME two legs the refundEscrow weld concludes. We obtain it directly from
`refundEscrow_compile_sound` (the proven settle weld), instantiated on the fulfil term (= the refund term
by §1). -/

/-- **`fulfillObligation_compile_sound` — the welded soundness (fulfillObligation slice, the settle
side-table effect).**

Suppose, for the Argus obligation-fulfil term `fulfillObligationStmt id` and the FOUND unresolved record
`r` (`hr` — the parked obligation stake this fulfil discharges):
  * the SHARED audited class-A circuit `compileRefund` (= `refundEscrowVmDescriptorGenuine`) is SATISFIED
    by `(env, true, true)` under the abstract Poseidon carrier `hash`, and its `RowEncodesRefund` decoding
    NAMES the post-state record `post` over the record's `creator` (the obligor) cell projection
    `cellProjRefund k.bal r.creator r.asset` with the `⟨r.amount⟩` param block (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (fulfillObligationStmt id) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    CREDITED obligor-cell projection `cellProjRefund k'.bal r.creator r.asset` — the conserved `balLo`
    (credited by `r.amount`, the reclaimed stake) AND the whole frozen frame
    (balHi/fields/capRoot/reserved/nonce). fulfillObligation has NO nonce-tick divergence (the descriptor
    FREEZES the cell nonce, matching the executor — `cellProjRefund` sends `nonce` to `0` on both sides).
  * **side-table leg:** the circuit FORCES the new escrow-list root carrier to be the genuine in-row
    recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the bound resolved
    record + old root — the digest the executor's `escrows := markResolved k.escrows id` resolve commits to
    (absorbed into `state_commit`, so the resolved record is bound; see `refundEscrowGenuine_binds_record`).

So the SHARED class-A circuit the prover runs for the obligation fulfil pins the per-cell stake-return
state the IR term's executor produces AND genuinely recomputes the bound `escrows` side-table root — the
template generalizes to the obligation fulfil (a per-asset escrow refund). NOT bound by this per-row weld:
the dregg1 obligor-only/before-deadline admission gate (the §8/theorem-layer carrier — see the DIVERGENCE
note in this file's header). -/
theorem fulfillObligation_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (r : EscrowRecord)
    (post : CellState)
    (hr : k.escrows.find? (matchPred id) = some r)
    (henc : RowEncodesRefund env (cellProjRefund k.bal r.creator r.asset) ⟨r.amount⟩ post)
    (hsat : satisfiedVm hash compileRefund env true true)
    (hexec : interp (fulfillObligationStmt id) k = some k') :
    -- conserved leg: the credited (obligor) cell's projection agrees on balLo + the whole frozen frame …
    ( post.balLo = (cellProjRefund k'.bal r.creator r.asset).balLo
      ∧ post.balHi = (cellProjRefund k'.bal r.creator r.asset).balHi
      ∧ (∀ i, post.fields i = (cellProjRefund k'.bal r.creator r.asset).fields i)
      ∧ post.capRoot = (cellProjRefund k'.bal r.creator r.asset).capRoot
      ∧ post.reserved = (cellProjRefund k'.bal r.creator r.asset).reserved
      ∧ post.nonce = (cellProjRefund k'.bal r.creator r.asset).nonce )
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
  -- `fulfillObligationStmt = refundEscrowStmt` (§1), so the proven refundEscrow settle weld applies
  -- verbatim on the SAME shared descriptor + the SAME found record.
  have hexec' : interp (refundEscrowStmt id) k = some k' := hexec
  exact refundEscrow_compile_sound hash env k k' id r post hr henc hsat hexec'

#assert_axioms fulfillObligation_compile_sound

/-! ## §4 — NON-VACUITY: the obligation-fulfil term genuinely RESOLVES + CREDITS, REJECTS a missing id,
and the welded descriptor is the genuine class-A one (not the placeholder).

The cornerstone/weld would be hollow if the fulfil term never committed, if the resolve were a no-op, or if
the descriptor were inert. The witnesses ride the refundEscrow §3 non-vacuity kernel `kR` (account `0`
Live, ONE unresolved record `id 7`, creator `0`) under the §1 definitional equality. -/

/-- **NON-VACUITY (witness TRUE — the discharge RESOLVES).** Running the obligation-fulfil term for `id = 7`
on `kR` commits and flips the parked record's `resolved` flag `false → true` (via `markResolved`): the
side-table discharge is a real, observable state edit, not a no-op. Rides the refundEscrow witness
`refundEscrowStmt_resolves` under `fulfillObligationStmt = refundEscrowStmt`. -/
theorem fulfillObligationStmt_resolves :
    (interp (fulfillObligationStmt 7) kR).map
        (fun k => (k.escrows.find? (fun r => decide (r.id = 7))).map (·.resolved))
      = some (some true) := by
  show (interp (refundEscrowStmt 7) kR).map _ = _
  exact refundEscrowStmt_resolves

/-- **NON-VACUITY (witness TRUE — the stake-return CREDIT is OBSERVABLE).** The committed fulfil raises the
obligor (record `creator` = cell `0`) per-asset `(0, 0)` ledger entry by the parked amount — here the
record carries amount `0`, so we exhibit the COMMIT itself is genuine (the term is `some`, not `none`): the
stake-discharge transition fires. Combined with `fulfillObligationStmt_resolves`, the two-component move is
real on `kR`. -/
theorem fulfillObligationStmt_commits :
    (interp (fulfillObligationStmt 7) kR).isSome = true := by
  rw [fulfillObligationStmt, interp_refundEscrowStmt_eq_refundEscrowKAsset]
  decide

/-- **NON-VACUITY (fail-closed: missing id).** A fulfil query for an id with NO parked record (`9`) does NOT
commit — the term returns `none` (the `find?`-gate fails closed). So the cornerstone's reject side is
genuine (two-valued, non-vacuous). Rides `refundEscrowStmt_rejects_missing`. -/
theorem fulfillObligationStmt_rejects_missing :
    interp (fulfillObligationStmt 9) kR = none := by
  show interp (refundEscrowStmt 9) kR = none
  exact refundEscrowStmt_rejects_missing

/-- The compiled fulfillObligation circuit is the genuine class-A descriptor `refundEscrowVmDescriptorGenuine`
(= `compileRefund`, NOT an empty placeholder): it carries the 13+14+4+3 = 34 constraints / 2+4 = 6
hash-sites (2 genuine escrow-root-recompute + 4 commitment) / 2 range checks. So
`fulfillObligation_compile_sound` is a statement about a REAL class-A circuit with a genuinely-recomputed
side-table root. -/
theorem fulfillObligationDescriptor_nontrivial :
    compileRefund.constraints.length = 34
    ∧ compileRefund.hashSites.length = 6
    ∧ compileRefund.ranges.length = 2 := by
  rw [compileRefund_eq]
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms fulfillObligationStmt_resolves
#assert_axioms fulfillObligationStmt_commits
#assert_axioms fulfillObligationStmt_rejects_missing
#assert_axioms fulfillObligationDescriptor_nontrivial

/-! ## §6 — FULL-STATE on the RUNNABLE descriptor (the magnesium breadth — bind ALL 17 fields).

`fulfillObligationStmt = refundEscrowStmt` definitionally, so the FULL-STATE refund weld
(`RefundEscrow.refundEscrow_runnable_full_state` over the WIDE descriptor `refundEscrowVmDescriptorWide`)
applies VERBATIM on the fulfil term: a satisfying row of the WIDE RUNNABLE descriptor binds the FULL
17-field post-state (the obligor/creator-cell CREDIT AND the `escrows` digest advance), all 17 bound by
the circuit the prover RUNS (the generic anti-ghost gives the no-malleability tooth). -/

open Dregg2.Circuit.Emit.EffectVmEmitRefundEscrowWide (refundEscrowVmDescriptorWide)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide (ESCROW_STEP_PARAM)
open Dregg2.Circuit.Argus.Effects.RefundEscrow (refundEscrow_runnable_full_state)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest)

/-- **`fulfillObligation_runnable_full_state` — THE FULL-STATE WELD (fulfillObligation).** The full-state
refund weld lifted verbatim onto the fulfil term (the dispatch-alias): a satisfying row of the WIDE
RUNNABLE descriptor agrees per-cell with the executor's CREDITED creator-cell projection on EVERY limb
AND binds the `escrows` side-table digest advance — all 17 fields. -/
theorem fulfillObligation_runnable_full_state
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (r : EscrowRecord)
    (post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (preRoots postRoots : SysRoots) (step : ℤ)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitRefundEscrow.IsRefundEscrowRow env)
    (hr : k.escrows.find? (matchPred id) = some r)
    (henc : RowEncodesRefund env (cellProjRefund k.bal r.creator r.asset) ⟨r.amount⟩ post)
    (hAfter : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestCol
                = systemRootsDigest hash postRoots)
    (hBefore : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestColBefore
                = systemRootsDigest hash preRoots)
    (hStep : env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash refundEscrowVmDescriptorWide env true true)
    (hexec : interp (fulfillObligationStmt id) k = some k') :
    ( post.balLo = (cellProjRefund k'.bal r.creator r.asset).balLo
      ∧ post.balHi = (cellProjRefund k'.bal r.creator r.asset).balHi
      ∧ (∀ i, post.fields i = (cellProjRefund k'.bal r.creator r.asset).fields i)
      ∧ post.capRoot = (cellProjRefund k'.bal r.creator r.asset).capRoot
      ∧ post.reserved = (cellProjRefund k'.bal r.creator r.asset).reserved
      ∧ post.nonce = (cellProjRefund k'.bal r.creator r.asset).nonce )
    ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step := by
  -- the fulfil term IS the refund term (`fulfillObligationStmt = refundEscrowStmt` definitionally);
  -- route through the proven full-state refund weld.
  have hexec' : interp (refundEscrowStmt id) k = some k' := by
    rw [fulfillObligationStmt] at hexec; exact hexec
  exact refundEscrow_runnable_full_state hash env k k' id r post preRoots postRoots step
    hrow hr henc hAfter hBefore hStep hsat hexec'

#assert_axioms fulfillObligation_runnable_full_state

end Dregg2.Circuit.Argus.Effects.FulfillObligation
