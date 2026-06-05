/-
# Dregg2.Exec.Handlers.Seal — the SEAL + SWISS-REF handler batch.

The THIRD batch of `EffectHandler` instances (after the `transfer`/`escrow`/`state` slice in
`Dregg2.Exec.Handler` and the `mint`/`burn`/`createCell`/`state-write` batch in
`Dregg2.Exec.Handlers.StateSupply`). This file EXTENDS the algebra over dregg1's CAPABILITY-ROUTING
op-set: the seal/unseal/seal-pair box machinery (`apply_seal`/`apply_unseal`/`apply_create_seal_pair`)
and the CapTP swiss-table export/enliven/handoff/GC effects. EVERY handler here is balance-NEUTRAL
(`delta = 0`): these ops move CAPABILITIES (edit `caps`/`sealedBoxes`/`swiss`), never the `bal` ledger
NOR the `escrows` holding-store — so the COMBINED per-asset measure `recTotalAssetWithEscrow` is left
LITERALLY fixed and `conserves` is the `rfl`-grade frame (a `{ k with caps/sealedBoxes/swiss := … }`
update keeps `bal`/`accounts`/`escrows` definitionally equal).

Each handler reuses the effect's EXISTING kernel logic — re-founded HERE at the bare `RecordKernelState`
layer (dropping the receipt `.log` the chained `…ChainA` wrappers carry, exactly as the escrow batch
re-founds `createEscrowKAsset` at the kernel layer): the seal-cap helpers `sealerCap`/`unsealerCap`/
`holdsSealCapFor` + `findSealedBox`, the swiss kernel ops `swissExportK`/`swissEnlivenK`/`swissHandoffK`/
`swissDropK` (which ALREADY carry the non-amplification gate `rightsNarrowerOrEqual` read off the
adversary-uncontrollable committed `heldAuths`, the refcount-GC, and membership-fail-closed), and the
authority gate `stateAuthB`. We do NOT touch `execFullA`/`FullActionA` (the cutover is a later step); we
only IMPORT and REUSE.

What this batch CLOSES — **the R3 hole (seal-pair pid freshness)**:

  `createSealPairChainA` has NO pid-freshness gate, and `findSealedBox` returns the FIRST match. So if a
  pid is REUSED — a new seal-pair created under a pid that already has a sealed box — a HOLDER of the OLD
  unsealer cap can open a box that was sealed under the NEW pair (the first-match lookup resolves to the
  stale box). The `createSealPairA` handler's `step` WRAPS the create with a pid-FRESHNESS conjunct
  (`findSealedBox k.sealedBoxes pid = none` — the pid must not already bind a box) in its admission gate;
  `admission_gated` makes it a TYPING obligation: a handler whose step ignored freshness would not
  type-check. The export amplification gate (the exported `rights` must be `⊆` the exporter's REAL
  committed `heldAuths` — `swissExportK`'s `rightsNarrowerOrEqual`) is ALREADY carried by the kernel op
  and surfaces here verbatim (we carry it; the `#eval` teeth re-exhibit it).

Handlers registered: `sealA`, `unsealA`, `createSealPairA`, `exportSturdyRefA` (= `swissExportK`),
`enlivenRefA` (= `swissEnlivenK`), `swissHandoffA` (= `swissHandoffK`), `swissDropA` (= `swissDropK`).

EVAL-VERIFIED (`§TEETH`):
  * R3: creating a seal-pair with an ALREADY-USED pid (a box already bound under it) ⇒ `none`; a FRESH
    pid ⇒ `some` (not everything-rejected).
  * unseal moves the REAL cap (the unsealed payload lands in the recipient's c-list); seal needs a
    genuinely-held sealer cap; unseal of an absent box ⇒ `none`.
  * export AMPLIFICATION (rights ⊄ committed-held) ⇒ `none`; a subset export ⇒ `some`; enliven/handoff/
    drop fail-closed on an absent swiss number; drop GCs at refcount 0.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/eval-only. Every keystone `#assert_axioms`-pinned
(a `sorryAx` fails the pin and the build). Pure, computable, `#eval`-able. Verified standalone:
`lake build Dregg2.Exec.Handlers.Seal`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Seal

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle
   sealerCap unsealerCap holdsSealCapFor)

/-! ## §1 — SEAL: the sealed-box capability-move machinery (`apply_seal`/`apply_unseal`/`pair`).

`createSealPairChainA`/`sealChainA`/`unsealChainA` (in `TurnExecutorFull`) operate on the CHAINED state
`RecChainedState` (kernel + receipt log). The `EffectHandler` algebra operates on the bare
`RecordKernelState`, so we RE-FOUND the kernel-touching content here (dropping the `.log` row — exactly
as the escrow batch re-founds `createEscrowKAsset` at the kernel layer). The seal-cap helpers
(`sealerCap`/`unsealerCap`/`holdsSealCapFor`) and the box store (`findSealedBox`, `sealedBoxes`) are
imported verbatim — the gate LOGIC is identical, only the carrier state differs. All `delta = 0`: these
edit `caps`/`sealedBoxes`, never `bal`/`escrows`. -/

/-! ### §1.1 — `createSealPairA`: grant the sealer+unsealer caps, R3-gated on pid FRESHNESS.

The bare `createSealPairChainA` gates only on `stateAuthB actor sealerHolder` — it does NOT check that
`pid` is fresh, and `findSealedBox` returns the FIRST match. Reusing a pid (a box already bound under it)
lets the OLD unsealer-cap holder open the NEW pair's box. The R3 fix WRAPS a freshness conjunct
(`findSealedBox k.sealedBoxes pid = none`) into the admission gate: a pid that already binds a box is
REJECTED. -/

/-- createSealPair arguments: the pair id, the actor (authority subject), and the two cap holders. -/
structure CreateSealPairArgs where
  /-- The seal-pair id (dregg1's `[u8;32]`, modelled `Nat`). -/
  pid : Nat
  /-- The actor performing the create (must hold authority over `sealerHolder`). -/
  actor : CellId
  /-- The cell granted the SEALER cap. -/
  sealerHolder : CellId
  /-- The cell granted the UNSEALER cap. -/
  unsealerHolder : CellId

/-- **The R3 pid-freshness gate.** A seal-pair may be created only if `pid` does not ALREADY bind a box
in the holding-store (`findSealedBox … = none`). This is the conjunct the bare `createSealPairChainA`
lacks; reusing a pid that already binds a box is the R3 attack (a stale unsealer opens the new box). -/
def pidFresh (k : RecordKernelState) (pid : Nat) : Bool :=
  (findSealedBox k.sealedBoxes pid).isNone

/-- **The R3-closing create-seal-pair step.** Commit ONLY if the actor is authorized over `sealerHolder`
AND `pid` is FRESH (no box already bound under it); then GRANT the sealer cap to `sealerHolder` and the
unsealer cap to `unsealerHolder` — two real c-list grants (the bare `createSealPairChainA` content,
de-chained). bal-NEUTRAL (edits only `caps`). -/
def createSealPairStep (k : RecordKernelState) (a : CreateSealPairArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.sealerHolder = true ∧ pidFresh k a.pid = true then
    some { k with caps := grant (grant k.caps a.sealerHolder (sealerCap a.pid))
                                a.unsealerHolder (unsealerCap a.pid) }
  else none

/-- **`createSealPairA` — the registered (R3-closing) seal-pair handler.** `delta = 0` (caps-only edit).
`conserves` is the `rfl`-grade frame (`bal`/`accounts`/`escrows` untouched by the caps update).
`auth_gated` from the `stateAuthB` conjunct. The headline is `admission_gated`: the wrapper's
`pidFresh` conjunct FORCES the freshness check the bare op skipped — a re-used pid does not type-check
past it. -/
def createSealPairA : EffectHandler CreateSealPairArgs where
  step := createSealPairStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.sealerHolder
  admission := fun k a => pidFresh k a.pid
  trace := fun a => { actor := a.actor, src := a.sealerHolder, dst := a.sealerHolder, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold createSealPairStep at h
    by_cases hg : stateAuthB s.caps a.actor a.sealerHolder = true ∧ pidFresh s a.pid = true
    · exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold createSealPairStep at h
    by_cases hg : stateAuthB s.caps a.actor a.sealerHolder = true ∧ pidFresh s a.pid = true
    · exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold createSealPairStep at h
    by_cases hg : stateAuthB s.caps a.actor a.sealerHolder = true ∧ pidFresh s a.pid = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      unfold recTotalAssetWithEscrow recTotalAsset escrowHeldAsset; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §1.2 — `sealA`: insert a box binding a HELD payload cap (fail-closed on cap-not-held). -/

/-- seal arguments: the pair id, the actor sealing, and the payload cap being sealed. -/
structure SealArgs where
  /-- The seal-pair id the box is keyed under. -/
  pid : Nat
  /-- The actor sealing (must HOLD the sealer cap for `pid` AND HOLD the `payload`). -/
  actor : CellId
  /-- The payload cap sealed into the box (the cap genuinely moves through the box). -/
  payload : Cap

/-- The seal-cap-held-AND-payload-held gate (the bare `sealChainA` gate, de-chained). -/
def sealGate (k : RecordKernelState) (a : SealArgs) : Bool :=
  (k.caps a.actor).any (fun c => holdsSealCapFor a.pid c) && decide (a.payload ∈ k.caps a.actor)

/-- **The seal step.** Commit ONLY if the actor genuinely HOLDS the sealer cap for `pid` AND HOLDS the
`payload` cap; then INSERT a box binding that held `payload` keyed by `pid`. bal-NEUTRAL (edits only
`sealedBoxes`). -/
def sealStep (k : RecordKernelState) (a : SealArgs) : Option RecordKernelState :=
  if sealGate k a then
    some { k with sealedBoxes := { pairId := a.pid, sealer := a.actor, payload := a.payload }
                                 :: k.sealedBoxes }
  else none

/-- **`sealA` — the registered seal handler.** `delta = 0` (sealedBoxes-only edit). `conserves` `rfl`-grade.
`auth_gated`/`admission_gated` both from the seal-cap-held-AND-payload-held gate (the actor cannot seal a
cap it does not hold — the box payload stays a confined held cap, so `unseal` cannot leak authority). -/
def sealA : EffectHandler SealArgs where
  step := sealStep
  delta := fun _ _ => 0
  auth := fun k a => sealGate k a
  admission := fun k a => sealGate k a
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold sealStep at h
    by_cases hg : sealGate s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold sealStep at h
    by_cases hg : sealGate s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold sealStep at h
    by_cases hg : sealGate s a
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      unfold recTotalAssetWithEscrow recTotalAsset escrowHeldAsset; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §1.3 — `unsealA`: open a box, GRANT the recovered cap to the recipient (fail-closed on no-box). -/

/-- unseal arguments: the pair id, the actor unsealing, and the recipient of the recovered cap. -/
structure UnsealArgs where
  /-- The seal-pair id whose box is opened. -/
  pid : Nat
  /-- The actor unsealing (must HOLD the unsealer cap for `pid`). -/
  actor : CellId
  /-- The cell the recovered payload cap is granted to. -/
  recipient : CellId

/-- The unsealer-cap-held gate (the bare `unsealChainA` authority gate, de-chained). -/
def unsealGate (k : RecordKernelState) (a : UnsealArgs) : Bool :=
  (k.caps a.actor).any (fun c => holdsSealCapFor a.pid c)

/-- **The unseal step.** Commit ONLY if the actor holds the unsealer cap for `pid` AND a box is bound
under `pid` (fail-closed via `findSealedBox`); then GRANT the recovered `payload` cap to the recipient's
c-list (the cap genuinely MOVES out of the box). bal-NEUTRAL (edits only `caps`). -/
def unsealStep (k : RecordKernelState) (a : UnsealArgs) : Option RecordKernelState :=
  if unsealGate k a then
    match findSealedBox k.sealedBoxes a.pid with
    | some box => some { k with caps := grant k.caps a.recipient box.payload }
    | none     => none
  else none

/-- The held-box admission witness (unseal): a committed unseal required a box bound under `pid`. -/
def unsealAdmitB (k : RecordKernelState) (a : UnsealArgs) : Bool :=
  (findSealedBox k.sealedBoxes a.pid).isSome

/-- **`unsealA` — the registered unseal handler.** `delta = 0` (caps-only edit). `conserves` `rfl`-grade
on the box-found branch. `auth_gated` from the unsealer-cap-held gate; `admission_gated` recovers the
box-found requirement (an unseal of an absent box is fail-closed, `unsealAdmitB`). -/
def unsealA : EffectHandler UnsealArgs where
  step := unsealStep
  delta := fun _ _ => 0
  auth := fun k a => unsealGate k a
  admission := unsealAdmitB
  trace := fun a => { actor := a.actor, src := a.recipient, dst := a.recipient, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold unsealStep at h
    by_cases hg : unsealGate s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold unsealStep at h
    by_cases hg : unsealGate s a
    · rw [if_pos hg] at h
      show unsealAdmitB s a = true
      unfold unsealAdmitB
      cases hfind : findSealedBox s.sealedBoxes a.pid with
      | none     => rw [hfind] at h; exact absurd h (by simp)
      | some box => rfl
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold unsealStep at h
    by_cases hg : unsealGate s a
    · rw [if_pos hg] at h
      cases hfind : findSealedBox s.sealedBoxes a.pid with
      | none     => rw [hfind] at h; exact absurd h (by simp)
      | some box =>
          rw [hfind] at h; simp only [Option.some.injEq] at h; subst h
          unfold recTotalAssetWithEscrow recTotalAsset escrowHeldAsset; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §2 — SWISS: the CapTP export/enliven/handoff/GC swiss-table effects (Wave-8 de-THIN).

These RE-FOUND the chained swiss wrappers (`swissExportChainA`/…/`swissDropChainA`) at the bare kernel
layer: each is the kernel op (`swissExportK`/`swissEnlivenK`/`swissHandoffK`/`swissDropK`, which ALREADY
carry the non-amplification gate `rightsNarrowerOrEqual` over the committed `heldAuths`, the membership
fail-close, and the refcount-GC) wrapped in the `stateAuthB actor exporter` authority gate the chained
wrapper adds (the holder-of-the-cap may export/enliven/drop). The §amplification gate is CARRIED — it is
the kernel op's own gate, read off adversary-uncontrollable committed state, and the `#eval` teeth below
re-exhibit it. ALL `delta = 0`: the swiss-table moves REFERENCES (capability routing), never `bal`. -/

/-! ### §2.1 — `exportSturdyRefA` (= `swissExportK`): mint a sturdy ref, non-amplification carried. -/

/-- export arguments: the swiss number, the actor (authority subject), the exporter cell, the target
cell, and the exported rights (which MUST be `⊆` the exporter's REAL committed rights). -/
structure ExportArgs where
  /-- The swiss number key (dregg1's `[u8;32]`, modelled `Nat`). -/
  sw : Nat
  /-- The actor performing the export (must hold authority over `exporter`). -/
  actor : CellId
  /-- The exporter cell minting the sturdy ref. -/
  exporter : CellId
  /-- The target cell the sturdy ref points to. -/
  target : CellId
  /-- The exported permission tier (MUST be `⊆` `heldAuths k exporter` — non-amplification). -/
  rights : List Auth

/-- **The export step.** Gate on `stateAuthB actor exporter` (the holder may export) AND run the kernel
`swissExportK` (INSERT a swiss→cap entry, refcount 1; fail-closed on a duplicate swiss number OR
amplification — the exported `rights` ⊄ `heldAuths k exporter`). bal-NEUTRAL (edits only `swiss`). -/
def exportStep (k : RecordKernelState) (a : ExportArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.exporter = true then
    swissExportK k a.sw a.exporter a.target a.rights
  else none

/-- `swissExportK` touches only `swiss`, so the combined measure is fixed whenever it commits. -/
theorem exportStep_measure_fixed (k k' : RecordKernelState) (a : ExportArgs)
    (h : exportStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold exportStep at h
  by_cases hg : stateAuthB k.caps a.actor a.exporter = true
  · rw [if_pos hg] at h; exact swissExportK_balNeutral h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`exportSturdyRefA` — the registered export handler (non-amplification CARRIED).** `delta = 0`
(swiss-only edit); `conserves` composes the kernel `swissExportK_balNeutral`. `auth_gated`/`admission_gated`
from the `stateAuthB` exporter gate. The amplification gate (`rights` ⊆ committed-held) lives in the
kernel op and is `#eval`-teeth-verified. -/
def exportSturdyRefA : EffectHandler ExportArgs where
  step := exportStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.exporter
  admission := fun k a => stateAuthB k.caps a.actor a.exporter
  trace := fun a => { actor := a.actor, src := a.exporter, dst := a.exporter, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold exportStep at h
    by_cases hg : stateAuthB s.caps a.actor a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold exportStep at h
    by_cases hg : stateAuthB s.caps a.actor a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    obtain ⟨hbal, hheld⟩ := exportStep_measure_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbal, hheld]; ring

/-! ### §2.2 — `enlivenRefA` (= `swissEnlivenK`): grant a live ref, non-amplification carried. -/

/-- enliven arguments: the swiss number, the actor, the holding cell, and the bearer's claimed rights
(which MUST be `⊆` the entry's exported rights). -/
structure EnlivenArgs where
  /-- The swiss number presented. -/
  sw : Nat
  /-- The actor enlivening (must hold authority over `exporter`). -/
  actor : CellId
  /-- The cell whose c-list authorizes the enliven. -/
  exporter : CellId
  /-- The bearer's CLAIMED rights (MUST be `⊆` the entry's exported rights — non-amplification). -/
  claimed : List Auth

/-- **The enliven step.** Gate on `stateAuthB actor exporter` AND run `swissEnlivenK` (LOOKUP-fail-closed
+ non-amplification: `claimed` ⊆ the entry's rights + refcount bump). bal-NEUTRAL. -/
def enlivenStep (k : RecordKernelState) (a : EnlivenArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.exporter = true then
    swissEnlivenK k a.sw a.claimed
  else none

/-- `swissEnlivenK` touches only `swiss`, so the combined measure is fixed whenever it commits. -/
theorem enlivenStep_measure_fixed (k k' : RecordKernelState) (a : EnlivenArgs)
    (h : enlivenStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold enlivenStep at h
  by_cases hg : stateAuthB k.caps a.actor a.exporter = true
  · rw [if_pos hg] at h; exact swissEnlivenK_balNeutral h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`enlivenRefA` — the registered enliven handler (non-amplification CARRIED).** `delta = 0`;
`conserves` composes `swissEnlivenK_balNeutral`. `auth_gated`/`admission_gated` from the `stateAuthB`
gate. The claimed-rights non-amplification gate lives in the kernel op and is `#eval`-teeth-verified. -/
def enlivenRefA : EffectHandler EnlivenArgs where
  step := enlivenStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.exporter
  admission := fun k a => stateAuthB k.caps a.actor a.exporter
  trace := fun a => { actor := a.actor, src := a.exporter, dst := a.exporter, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold enlivenStep at h
    by_cases hg : stateAuthB s.caps a.actor a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold enlivenStep at h
    by_cases hg : stateAuthB s.caps a.actor a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    obtain ⟨hbal, hheld⟩ := enlivenStep_measure_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbal, hheld]; ring

/-! ### §2.3 — `swissHandoffA` (= `swissHandoffK`): bind a 3-vat introduce cert, refcount bump. -/

/-- handoff arguments: the swiss number, the introduce cert hash, the introducer, and the holding cell. -/
structure HandoffArgs where
  /-- The swiss number presented. -/
  sw : Nat
  /-- The 3-vat introduce cert hash bound to the entry. -/
  certHash : Nat
  /-- The introducer (must hold authority over `exporter`). -/
  introducer : CellId
  /-- The cell whose c-list authorizes the handoff. -/
  exporter : CellId

/-- **The handoff step.** Gate on `stateAuthB introducer exporter` AND run `swissHandoffK` (bind the cert
+ refcount bump; fail-closed on an absent swiss number). bal-NEUTRAL. -/
def handoffStep (k : RecordKernelState) (a : HandoffArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.introducer a.exporter = true then
    swissHandoffK k a.sw a.certHash
  else none

/-- `swissHandoffK` touches only `swiss`, so the combined measure is fixed whenever it commits. -/
theorem handoffStep_measure_fixed (k k' : RecordKernelState) (a : HandoffArgs)
    (h : handoffStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold handoffStep at h
  by_cases hg : stateAuthB k.caps a.introducer a.exporter = true
  · rw [if_pos hg] at h; exact swissHandoffK_balNeutral h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`swissHandoffA` — the registered handoff handler.** `delta = 0`; `conserves` composes
`swissHandoffK_balNeutral`. `auth_gated`/`admission_gated` from the `stateAuthB introducer exporter`
gate. -/
def swissHandoffA : EffectHandler HandoffArgs where
  step := handoffStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.introducer a.exporter
  admission := fun k a => stateAuthB k.caps a.introducer a.exporter
  trace := fun a => { actor := a.introducer, src := a.exporter, dst := a.exporter, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold handoffStep at h
    by_cases hg : stateAuthB s.caps a.introducer a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold handoffStep at h
    by_cases hg : stateAuthB s.caps a.introducer a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    obtain ⟨hbal, hheld⟩ := handoffStep_measure_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbal, hheld]; ring

/-! ### §2.4 — `swissDropA` (= `swissDropK`): GC a reference (refcount decrement, remove at 0). -/

/-- drop arguments: the swiss number, the actor, and the holding cell. -/
structure DropArgs where
  /-- The swiss number whose refcount is decremented. -/
  sw : Nat
  /-- The actor dropping the ref (must hold authority over `exporter`). -/
  actor : CellId
  /-- The cell whose c-list authorizes the drop. -/
  exporter : CellId

/-- **The drop step.** Gate on `stateAuthB actor exporter` AND run `swissDropK` (decrement refcount, GC
the entry at 0; fail-closed on an absent swiss number OR an already-zero refcount). bal-NEUTRAL. -/
def dropStep (k : RecordKernelState) (a : DropArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.exporter = true then
    swissDropK k a.sw
  else none

/-- `swissDropK` touches only `swiss`, so the combined measure is fixed whenever it commits. -/
theorem dropStep_measure_fixed (k k' : RecordKernelState) (a : DropArgs)
    (h : dropStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold dropStep at h
  by_cases hg : stateAuthB k.caps a.actor a.exporter = true
  · rw [if_pos hg] at h; exact swissDropK_balNeutral h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`swissDropA` — the registered drop/GC handler.** `delta = 0`; `conserves` composes
`swissDropK_balNeutral`. `auth_gated`/`admission_gated` from the `stateAuthB actor exporter` gate. -/
def swissDropA : EffectHandler DropArgs where
  step := dropStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.exporter
  admission := fun k a => stateAuthB k.caps a.actor a.exporter
  trace := fun a => { actor := a.actor, src := a.exporter, dst := a.exporter, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold dropStep at h
    by_cases hg : stateAuthB s.caps a.actor a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold dropStep at h
    by_cases hg : stateAuthB s.caps a.actor a.exporter = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    obtain ⟨hbal, hheld⟩ := dropStep_measure_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbal, hheld]; ring

/-! ## §3 — The SEAL+SWISS registry coproduct and the `ClosedEffect` builders.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler`. -/

/-- The seal/swiss batch registry (the coproduct menu for this cluster). -/
def sealBatchRegistry : Registry :=
  [ ⟨CreateSealPairArgs, createSealPairA⟩,
    ⟨SealArgs, sealA⟩,
    ⟨UnsealArgs, unsealA⟩,
    ⟨ExportArgs, exportSturdyRefA⟩,
    ⟨EnlivenArgs, enlivenRefA⟩,
    ⟨HandoffArgs, swissHandoffA⟩,
    ⟨DropArgs, swissDropA⟩ ]

/-- Build a closed create-seal-pair effect (tag `0`). -/
def createSealPairEffect (pid : Nat) (actor sealerHolder unsealerHolder : CellId) : ClosedEffect :=
  { tag := 0, Args := CreateSealPairArgs,
    args := { pid := pid, actor := actor, sealerHolder := sealerHolder,
              unsealerHolder := unsealerHolder }, handler := createSealPairA }

/-- Build a closed seal effect (tag `1`). -/
def sealEffect (pid : Nat) (actor : CellId) (payload : Cap) : ClosedEffect :=
  { tag := 1, Args := SealArgs, args := { pid := pid, actor := actor, payload := payload },
    handler := sealA }

/-- Build a closed unseal effect (tag `2`). -/
def unsealEffect (pid : Nat) (actor recipient : CellId) : ClosedEffect :=
  { tag := 2, Args := UnsealArgs, args := { pid := pid, actor := actor, recipient := recipient },
    handler := unsealA }

/-- Build a closed export-sturdy-ref effect (tag `3`). -/
def exportSturdyRefEffect (sw : Nat) (actor exporter target : CellId) (rights : List Auth) :
    ClosedEffect :=
  { tag := 3, Args := ExportArgs,
    args := { sw := sw, actor := actor, exporter := exporter, target := target, rights := rights },
    handler := exportSturdyRefA }

/-- Build a closed enliven-ref effect (tag `4`). -/
def enlivenRefEffect (sw : Nat) (actor exporter : CellId) (claimed : List Auth) : ClosedEffect :=
  { tag := 4, Args := EnlivenArgs,
    args := { sw := sw, actor := actor, exporter := exporter, claimed := claimed },
    handler := enlivenRefA }

/-- Build a closed swiss-handoff effect (tag `5`). -/
def swissHandoffEffect (sw certHash : Nat) (introducer exporter : CellId) : ClosedEffect :=
  { tag := 5, Args := HandoffArgs,
    args := { sw := sw, certHash := certHash, introducer := introducer, exporter := exporter },
    handler := swissHandoffA }

/-- Build a closed swiss-drop effect (tag `6`). -/
def swissDropEffect (sw : Nat) (actor exporter : CellId) : ClosedEffect :=
  { tag := 6, Args := DropArgs, args := { sw := sw, actor := actor, exporter := exporter },
    handler := swissDropA }

/-! ## §4 — TEETH: the R3 attack + the amplification gate + cap-movement, evaluated.

Creating a seal-pair with an already-used pid is REJECTED (R3); a fresh pid SUCCEEDS. unseal moves the
REAL cap into the recipient's c-list. export amplification (rights ⊄ committed-held) is REJECTED; a
subset export SUCCEEDS. The gates are load-bearing: a handler whose step ignored `admission` would have
FAILED `admission_gated`. -/

/-- A fixture: cells 0,1,2 are accounts; cell 0 holds 100 of asset 0 + the privileged `node`/`endpoint`
caps. Cell 0 holds `node 0`/`node 1`/`node 2` (self+target authority via `stateAuthB`), the
`endpoint 7 [read, call]` cap (its REAL exportable rights — the export non-amplification bound), AND a
`node 99` cap (the payload it will SEAL — you can only seal a cap you genuinely hold). All cells Live. -/
def sk0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1, Cap.node 2,
                                    Cap.endpoint 7 [Auth.read, Auth.call], Cap.node 99] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- The fixture AFTER cell 0 creates seal-pair 5 (granting itself the sealer cap + cell 1 the unsealer
cap) and seals the `node 99` payload into a box under pid 5. The box now binds pid 5. -/
def skSealed : Option RecordKernelState :=
  (createSealPairStep sk0 { pid := 5, actor := 0, sealerHolder := 0, unsealerHolder := 1 }).bind
    (fun k => sealStep k { pid := 5, actor := 0, payload := Cap.node 99 })

-- §TEETH-1 (R3 ATTACK): creating a NEW seal-pair under pid 5 — which ALREADY binds a box — is REJECTED
-- (the freshness gate bites: a stale unsealer must not be able to open the new pair's box).
#guard ((skSealed.bind (fun k =>
        execEffect (createSealPairEffect 5 0 0 1) k)).isSome) == false  --  false  (R3 attack rejected)
-- §TEETH-2 (R3 honest): creating a seal-pair under a FRESH pid 6 SUCCEEDS (not everything-rejected).
#guard ((skSealed.bind (fun k =>
        execEffect (createSealPairEffect 6 0 0 1) k)).isSome)  --  true   (fresh pid admitted)
-- §TEETH-3 (cap MOVES): the recipient (cell 1) unseals box 5 ⇒ the `node 99` payload lands in cell 1.
#guard ((skSealed.bind (fun k => execEffect (unsealEffect 5 1 1) k)).map
        (fun k => (k.caps 1).contains (Cap.node 99))) == some true  --  some true
-- §TEETH-4 (unseal needs a seal cap for the pid): cell 2 holds NO endpoint cap keyed to pid 5
-- (`holdsSealCapFor 5` fails), so its unseal attempt is REJECTED (fail-closed on cap-not-held).
#guard ((skSealed.bind (fun k => execEffect (unsealEffect 5 2 2) k)).isSome) == false  --  false
-- §TEETH-5 (unseal of an absent box fail-closed): no box under pid 99 ⇒ none even with a held cap.
#guard ((execEffect (unsealEffect 99 1 1) sk0).isSome) == false  --  false
-- §TEETH-6 (seal needs a HELD payload): sealing a cap the actor does NOT hold ⇒ none.
#guard ((skSealed.bind (fun k =>
        execEffect (sealEffect 5 0 (Cap.node 12345)) k)).isSome) == false  --  false
-- §TEETH-7 (export AMPLIFICATION denied): exporting [read, write] when cell 0 holds only [read, call]
-- (write ∉ committed-held) ⇒ none (the non-amplification gate, carried from the kernel op).
#guard ((execEffect (exportSturdyRefEffect 42 0 0 1 [Auth.read, Auth.write]) sk0).isSome) == false  --  false
-- §TEETH-8 (export subset OK): exporting [read] (⊆ [read, call]) by the authorized holder SUCCEEDS.
#guard ((execEffect (exportSturdyRefEffect 42 0 0 1 [Auth.read]) sk0).isSome)  --  true
-- §TEETH-9 (export conserves): a committed export leaves the combined per-asset measure UNCHANGED.
#guard ((execEffect (exportSturdyRefEffect 42 0 0 1 [Auth.read]) sk0).map
        (fun k => (recTotalAssetWithEscrow sk0 0, recTotalAssetWithEscrow k 0))) == some (100, 100)  --  some (100, 100)
-- §TEETH-10 (export UNAUTHORIZED): cell 1 holds no authority over exporter 0 ⇒ none.
#guard ((execEffect (exportSturdyRefEffect 42 1 0 1 [Auth.read]) sk0).isSome) == false  --  false
-- §TEETH-11 (enliven/handoff/drop fail-closed on an absent swiss number).
#guard ((execEffect (enlivenRefEffect 999 0 0 [Auth.read]) sk0).isSome) == false  --  false
#guard ((execEffect (swissHandoffEffect 999 1234 0 0) sk0).isSome) == false  --  false
#guard ((execEffect (swissDropEffect 999 0 0) sk0).isSome) == false  --  false
-- §TEETH-12 (drop GCs the ref): export sw 42, then a single drop removes it (refcount 1 → 0 ⇒ GC).
#guard (((execEffect (exportSturdyRefEffect 42 0 0 1 [Auth.read]) sk0).bind
        (fun k => execEffect (swissDropEffect 42 0 0) k)).map
        (fun k => (findSwiss k.swiss 42).isNone)) == some true  --  some true
-- §TEETH-13 (turn conserves): a turn [export; enliven] runs the foldlM and conserves the measure.
#guard ((execTurn [exportSturdyRefEffect 42 0 0 1 [Auth.read], enlivenRefEffect 42 0 0 [Auth.read]] sk0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100

/-! ## §5 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler `def` pins its obligation FIELDS transitively (the structure literal CARRIES the
proofs), and each measure-fixed helper is pinned directly. A `sorryAx` anywhere in the composed lemmas
fails the pin AND the build. -/

#assert_axioms createSealPairA
#assert_axioms sealA
#assert_axioms unsealA
#assert_axioms exportSturdyRefA
#assert_axioms enlivenRefA
#assert_axioms swissHandoffA
#assert_axioms swissDropA
#assert_axioms exportStep_measure_fixed
#assert_axioms enlivenStep_measure_fixed
#assert_axioms handoffStep_measure_fixed
#assert_axioms dropStep_measure_fixed

/-! ## §DEFER — honest scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **R3 freshness scope.** The freshness gate here is `findSealedBox … = none` (no box already bound
    under `pid`), which closes the documented attack (a stale unsealer opening a NEW pair's box, because
    `findSealedBox` returns the FIRST match). A stricter gate would ALSO reject re-granting the
    sealer/unsealer caps when those caps already exist somewhere; that is a separate (cap-table) freshness
    invariant and is the next refinement — the box-freshness conjunct is the one that closes the
    first-match box-confusion R3 attack.

  * **AEAD / STARK crypto portals.** The seal box's AEAD ciphertext (`apply_seal`/`apply_unseal`) and the
    sturdy-ref AIR `EXPORT_PERMISSIONS` proof are §8 `CryptoPortal` faces. What is REAL here is the
    WHICH-cap box binding, the c-list grant on unseal, and the non-amplification rights gate (read off
    committed `heldAuths`) — the crypto is the portal hypothesis, not modelled.

  * **3-vat handoff cert VALIDATION.** `swissHandoffK` BINDS the cert hash + bumps the refcount; the
    cryptographic validation of the introduce cert against the entry (the 3-vat introduce protocol) is the
    §8 portal face. The executable content is the cert-binding + refcount bookkeeping.
-/

end Dregg2.Exec.Handlers.Seal
