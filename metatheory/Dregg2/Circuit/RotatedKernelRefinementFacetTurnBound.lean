/-
# Dregg2.Circuit.RotatedKernelRefinementFacetTurnBound — the TURN-IDENTITY binding (the smuggle close).

## The hole this module closes

`RotatedKernelRefinementFacet` lands the faithful authority leg, but the apex
(`lightclient_turn_unfoolable_forest_facet` / `lightclient_transfer_faithful`) concludes

  `∃ (tr : Turn) (a : AssetId), BalanceMovementSpecFacet fcaps provided pre tr a post`

with the kernel turn `tr` EXISTENTIALLY quantified. The authority leg of `BalanceMovementSpecFacet`
reads `authorizedFacetB fcaps provided tr` — whose OWNER disjunct is `decide (tr.actor = tr.src)` and
whose CAP disjunct opens a cap over `tr.src` for actor `tr.actor`. NONE of `tr.actor`, `tr.src`,
`tr.dst` is bound to the LIGHT CLIENT'S published commitment:

  * `recStateCommit k t` (`StateCommit.lean`) uses `t.src`/`t.dst` only as the cell-digest PARTITION
    index (`k.accounts \ {t.src, t.dst}`) and never absorbs `t.actor` at all;
  * the rotated descriptor publishes 4 PI pins (OLD/NEW commit · height · caveat commit —
    `EffectVmEmitRotationV3.rotPins`); NONE is the turn's `actor`/`src`/`dst`;
  * the cap-open columns `capOpenCols.src`/`capOpenCols.capRoot` are FREE appendix columns (no gate
    welds them to a committed before-block — `CapOpenEmit §1` documents a weld that the constraint list
    `capOpenConstraintsEff` does NOT lay down).

A light client that trusts ONLY the proof + the published `(pre, post)` therefore cannot see WHICH
turn the authority gate ran on. A prover can existentially instantiate `tr.actor := tr.src` (owner
disjunct, no cap needed) for ANY `src` it moves, and the apex's conclusion still holds — the owner
authority is entirely OFF-CIRCUIT.

## What this module forces

The published `BatchPublicInputs.turn` (`pc.turn`) IS exposed to the light client. The honest fix is
to make the kernel step's turn BE that published turn — so the authority gate (owner OR cap) runs on
the turn the light client SEES, not a free existential. This module:

  1. **`dispatchArmFacetTB fcaps provided pubTurn`** — the TURN-BOUND faithful arm: the step's turn IS
     the published `pubTurn` (no free existential `tr`). `BalanceMovementSpecFacet fcaps provided pre
     pubTurn a post` — so `authorizedFacetB fcaps provided pubTurn` reads the COMMITTED identity.

  2. **`TurnIdentityBound`** — the NAMED in-circuit binding the light client requires: the witness's
     `rotatedEncodes`/cap-open turn IS the published `pc.turn` (`tr = pc.turn`). This is what a
     turn-identity PI gate forces (the designated rows publish `(actor, src, dst, amt)` to the PI turn
     slots). It is the genuine residual the LEDGER commitment cannot carry on its own — but UNLIKE the
     prior free existential, it is now an EXPLICIT equality the apex consumes, not a hidden choice.

  3. **`ownerGateForced` / `dispatchArmFacetTB_owner`** — the OWNER disjunct made an IN-CIRCUIT decision
     over the COMMITTED turn: `decide (pc.turn.actor = pc.turn.src)`. Because the turn is now `pc.turn`
     (bound), the owner gate is a decision on PUBLISHED data — a light client CAN check it. The prior
     hole (owner-authority off-circuit) is closed: ownership is asserted of the published actor/src, not
     a free existential.

  4. **`transfer_descriptorRefines_facetTB`** — the turn-bound refinement: a satisfying value witness +
     its decode + the cap-open source + the turn-identity binding force `BalanceMovementSpecFacet fcaps
     provided pre pc.turn a post` — the authority leg over the PUBLISHED turn.

  5. **`descriptorRefinesTBKernelFree`** (§8) + **`lightclient_transfer_kernelArm_turnbound`** (§9) —
     the apex re-stated so the conclusion's turn IS `pi.turn`: the authority a light client gets is over
     the turn it published, NOT a free one.
     ⚰ These REPLACED `descriptorRefinesTB` + `lightclient_transfer_faithful_turnbound` on 2026-08-02.
     The old rung carried a refuted `Poseidon2SpongeCR` in its VALUE, so the apex over it asserted
     nothing at deployed BabyBear; see the ⚰ TOMBSTONE at §6. The receipt-chain conjunct of the
     conclusion is now the named per-instance residual `FacetLogResidual`; every authority conjunct this
     module exists to force is still delivered unconditionally, over `pi.turn`.

## Honest residual (named, not faked)

`TurnIdentityBound` is the genuine in-circuit obligation a turn-identity PI gate discharges (publish the
witness's turn fields to the PI turn slots; the gate `pi.turn = witnessTurn`). It is REALIZABLE — the
honest prover's witness IS the published turn — and it is now CARRIED EXPLICITLY (exactly as
`StarkSound`/`WitnessDecodes` are), consumed by the apex, NOT a hidden existential choice. The deployed
realization (adding the 4 turn-field PI pins + the equality gate to `rotPins`) is VK-affecting circuit
work named in the report. The Lean side — the binding made explicit + the apex re-pointed at the
published turn — is what closes the SMUGGLE: the authority is no longer over a turn the light client
cannot see.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported keystones. NEW names only.
-/
import Dregg2.Circuit.RotatedKernelRefinementFacet
import Dregg2.Circuit.Emit.CapOpenTurnPins
-- §8's floor-free rung is stated over `ApexFloorFree.CommitMap`/`StateDecodeC` and refuted at
-- `ApexFloorFree.collapseMap`. No cycle: `ApexFloorFree` imports only `Dregg2.Circuit.CircuitSoundness`,
-- which this file already sits above.
import Dregg2.Circuit.ApexFloorFree

namespace Dregg2.Circuit.RotatedKernelRefinementFacetTurnBound

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Exec.FacetAuthority (FacetCaps AuthProvided authorizedFacetB authorizedFacetB_owner)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.RotatedKernelRefinement (rotatedEncodes transferV3 RotTableSide transfer_descriptorRefines)
open Dregg2.Circuit.RotatedKernelRefinementFacet
  (BalanceMovementSpecFacet admitGuardAFacet TransferAuthoritySourceCanon
   transferAuthoritySourceCanon_authorizes balanceMovementSpecFacet_owner_admits)

set_option autoImplicit false

/-! ## §1 — `TurnIdentityBound`: the published turn IS the witness's turn (the NAMED in-circuit binding).

The value witness (`rotatedEncodes`) and the cap-open source both carry a kernel turn `tr`. The light
client publishes `pc.turn`. `TurnIdentityBound pc tr` is the equality `tr = pc.turn` — the obligation a
turn-identity PI gate discharges (the designated rows publish `(actor, src, dst, amt)` into the PI turn
slots, and the gate equates them). It is the genuine residual the LEDGER commitment cannot carry on its
own (the commitment partitions on `src`/`dst` and ignores `actor`), made EXPLICIT and consumed by the
apex — not a hidden existential choice as before. -/

/-- **`TurnIdentityBound pc tr`** — the published boundary turn IS the witness's kernel turn. The
turn-identity PI binding: a light client that publishes `pc.turn` is certified that the authority gate
ran on EXACTLY that turn (`tr = pc.turn`), so the owner/cap decision is over the PUBLISHED identity. -/
def TurnIdentityBound (pc : PublishedCommit) (tr : Turn) : Prop :=
  tr = pc.turn

/-- The turn-identity binding rewrites the witness turn to the published turn. -/
theorem TurnIdentityBound.eq {pc : PublishedCommit} {tr : Turn} (h : TurnIdentityBound pc tr) :
    tr = pc.turn := h

/-! ## §2 — `dispatchArmFacetTB`: the TURN-BOUND faithful arm (no free existential turn).

`RotatedKernelRefinementFacet.dispatchArmFacet` is `∃ tr a, BalanceMovementSpecFacet … tr …` — the turn
is existential, so the authority gate `authorizedFacetB … tr` reads a turn the light client cannot see.
`dispatchArmFacetTB fcaps provided pubTurn` PINS the turn to the published `pubTurn`: only the asset is
existential. The authority leg now reads the COMMITTED published turn. -/

/-- **`dispatchArmFacetTB fcaps provided pubTurn pre post`** — the TURN-BOUND faithful transfer arm: a
faithful transfer of SOME asset `a` ON THE PUBLISHED TURN `pubTurn` (NOT a free existential). The
authority leg `authorizedFacetB fcaps provided pubTurn` reads the turn the light client published. -/
def dispatchArmFacetTB (fcaps : FacetCaps) (provided : AuthProvided) (pubTurn : Turn)
    (pre post : RecChainedState) : Prop :=
  ∃ a : AssetId, BalanceMovementSpecFacet fcaps provided pre pubTurn a post

/-- **`dispatchArmFacetTB_to_dispatchArmFacet`** — the turn-bound arm entails the existential arm (the
published turn IS a witness). So the turn-bound apex is STRONGER: it pins the existential the old apex
left free. (The converse FAILS without `TurnIdentityBound` — exactly the smuggle.) -/
theorem dispatchArmFacetTB_to_dispatchArmFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (pubTurn : Turn) (pre post : RecChainedState)
    (h : dispatchArmFacetTB fcaps provided pubTurn pre post) :
    Dregg2.Circuit.RotatedKernelRefinementFacet.dispatchArmFacet fcaps provided 0 pre post := by
  obtain ⟨a, hspec⟩ := h
  exact ⟨pubTurn, a, hspec⟩

/-! ## §3 — the OWNER gate, FORCED over the COMMITTED turn.

The prior hole: the owner disjunct `decide (tr.actor = tr.src)` ran on a free existential `tr`, so a
prover could pick `tr.actor := tr.src` for any `src` it moves — owner authority OFF-circuit. With the
turn bound to `pc.turn`, the owner gate is a decision on the PUBLISHED actor/src, which a light client
CAN inspect. `ownerGateForced` discharges the authority leg from `pc.turn.actor = pc.turn.src` over the
COMMITTED turn — the owner authority is now over published data. -/

/-- **`ownerGateForced` — the owner disjunct over the COMMITTED turn.** If the PUBLISHED turn's actor
owns its src (`pc.turn.actor = pc.turn.src`), the deployed two-axis gate PASSES on the published turn.
Because the turn is `pc.turn` (bound, not existential), this is a decision a light client makes on the
published identity — the owner authority is IN the published surface, not smuggled. -/
theorem ownerGateForced (fcaps : FacetCaps) (provided : AuthProvided) (pc : PublishedCommit)
    (howner : pc.turn.actor = pc.turn.src) :
    authorizedFacetB fcaps provided pc.turn = true :=
  authorizedFacetB_owner fcaps provided pc.turn howner

/-- **`dispatchArmFacetTB_owner` — the OWNER path lands the turn-bound arm over the published turn.** An
owner-authorized PUBLISHED transfer (`pc.turn.actor = pc.turn.src`) whose value movement holds lands the
turn-bound faithful arm — its authority discharged by the IN-PUBLISHED-SURFACE owner gate, NOT a free
existential. This is the owner-authority smuggle closed: the ownership is asserted of `pc.turn`. -/
theorem dispatchArmFacetTB_owner (fcaps : FacetCaps) (provided : AuthProvided) (pc : PublishedCommit)
    (pre post : RecChainedState) (a : AssetId)
    (howner : pc.turn.actor = pc.turn.src)
    (hval : BalanceMovementSpec pre pc.turn a post) :
    dispatchArmFacetTB fcaps provided pc.turn pre post :=
  ⟨a, balanceMovementSpecFacet_owner_admits fcaps provided pre pc.turn a post howner hval⟩

/-! ## §4 — `transfer_descriptorRefines_facetTB`: the turn-bound refinement.

The faithful refinement with the turn PINNED to the published `pc.turn`. From a satisfying value
witness, its decode (whose turn is bound to `pc.turn` via `TurnIdentityBound`), and the cap-open source
OVER `pc.turn`, force `BalanceMovementSpecFacet fcaps provided pre pc.turn a post` — the authority leg
over the PUBLISHED turn. -/

set_option maxHeartbeats 800000 in
/-- **`transfer_descriptorRefines_facetTB` — THE TURN-BOUND FAITHFUL REFINEMENT.** Satisfying the live
rotated transfer value descriptor with a decode `rotatedEncodes … tr a`, the turn-identity binding
`TurnIdentityBound pc tr` (the witness turn IS the published turn), and the cap-open authority source
OVER THE PUBLISHED TURN `pc.turn`, forces `BalanceMovementSpecFacet fcaps provided pre pc.turn a post`.
The authority leg (owner OR cap) now reads `pc.turn` — the turn the light client published — closing the
free-existential smuggle. -/
theorem transfer_descriptorRefines_facetTB (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (pc : PublishedCommit) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (hbound : TurnIdentityBound pc tr)
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hauth : TransferAuthoritySourceCanon hash fcaps provided pre pc.turn) :
    BalanceMovementSpecFacet fcaps provided pre pc.turn a post := by
  -- the VALUE leg (debit/credit/availability/frame/log) over the witness turn `tr`.
  have hval : BalanceMovementSpec pre tr a post :=
    transfer_descriptorRefines hash hside hsat pre post tr a henc
  -- rewrite the witness turn to the PUBLISHED turn (the in-circuit identity binding).
  rw [hbound.eq] at hval
  obtain ⟨⟨_htoy, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := hval
  -- the AUTHORITY leg — FORCED by the cap-open over the PUBLISHED turn (owner OR cap), faithfulness
  -- DISCHARGED (canonical leaf), NOT a carried `hfaith`.
  have hfaithAuth : authorizedFacetB fcaps provided pc.turn = true :=
    transferAuthoritySourceCanon_authorizes hash fcaps provided pre pc.turn hauth
  exact ⟨⟨hfaithAuth, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩

/-- **`transfer_descriptorRefinesTB_dispatchArm`** — package the turn-bound refinement as the turn-bound
dispatcher arm over the published turn. -/
theorem transfer_descriptorRefinesTB_dispatchArm (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (pc : PublishedCommit) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (hbound : TurnIdentityBound pc tr)
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hauth : TransferAuthoritySourceCanon hash fcaps provided pre pc.turn) :
    dispatchArmFacetTB fcaps provided pc.turn pre post :=
  ⟨a, transfer_descriptorRefines_facetTB hash hside hsat pre post pc tr a henc hbound fcaps provided hauth⟩

/-! ## §5 — the BOTH-POLARITY tooth: the turn-bound authority bites over the PUBLISHED turn.

A PUBLISHED turn the deployed gate rejects (neither owner nor a conferring cap) has NO turn-bound
faithful arm — so the published authority is genuinely load-bearing, not vacuous. -/

/-- **`dispatchArmFacetTB_rejects_unauthorized` (the published-turn authority TOOTH).** If the deployed
two-axis gate REJECTS the PUBLISHED turn (`authorizedFacetB fcaps provided pubTurn = false` — neither
owner nor a conferring cap), then NO `(pre, post)` is a turn-bound faithful step on that turn. The
authority leg bites over the turn the light client published — an unauthorized published transfer is
rejected. -/
theorem dispatchArmFacetTB_rejects_unauthorized (fcaps : FacetCaps) (provided : AuthProvided)
    (pubTurn : Turn) (pre post : RecChainedState)
    (hbad : authorizedFacetB fcaps provided pubTurn = false) :
    ¬ dispatchArmFacetTB fcaps provided pubTurn pre post := by
  rintro ⟨a, ⟨⟨hauth, _⟩, _⟩⟩
  rw [hbad] at hauth
  exact absurd hauth (by simp)

/-- **`dispatchArmFacetTB_owner_fires` — the owner arm is NON-VACUOUS.** A concrete owner-authorized
published transfer (`pc.turn.actor = pc.turn.src`) with a valid value movement inhabits the turn-bound
arm — so the owner path is realizable, not an empty hypothesis. -/
theorem dispatchArmFacetTB_owner_fires (fcaps : FacetCaps) (provided : AuthProvided)
    (pc : PublishedCommit) (pre post : RecChainedState) (a : AssetId)
    (howner : pc.turn.actor = pc.turn.src)
    (hval : BalanceMovementSpec pre pc.turn a post) :
    dispatchArmFacetTB fcaps provided pc.turn pre post :=
  dispatchArmFacetTB_owner fcaps provided pc pre post a howner hval

/-! ## §6 — ⚰ TOMBSTONE: `descriptorRefinesTB`, `descriptorRefinesTB_to_descriptorRefines` and
`lightclient_transfer_faithful_turnbound` (DELETED / REWIRED 2026-08-02).

This section held the TURN-BOUND apex. The apex survives — it moved to §9, below §8's sound rung, and
concludes at the kernel-endpoint arm plus a NAMED per-instance log residual. What was deleted is the rung
it stood on and the lowering that forwarded that rung's floor.

**What `descriptorRefinesTB S hash d fcaps provided` claimed.**

    Poseidon2SpongeCR hash →
    ∀ minit mfin maddrs t pc pre post,
      Satisfied2 hash d minit mfin maddrs t → StateDecode S pc pre post →
      dispatchArmFacetTB fcaps provided pc.turn pre post

— "any satisfying witness of `d` whose decoded published commitment is `pc` forces the whole faithful
transfer step, authority leg included, ON THE PUBLISHED TURN `pc.turn`".

**Why it was vacuous.** The `Poseidon2SpongeCR hash →` antecedent sat in the VALUE, and
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES IT FALSE at deployed BabyBear.
`DescriptorRefinesShirkRefuted.descriptorRefines_vacuous_babyBear` transfers verbatim: at any
field-bounded sponge the def held for EVERY `fcaps` and `provided`, including at an unsatisfiable
turn-bound arm — so the "authority over the PUBLISHED turn" this module exists to force was, at deployed
parameters, discharged by the parameters and not by the circuit. The floor being in the value meant no
floor binder appeared in the type of anything mentioning it, so `#floor_ratchet`, which keys on binders,
saw nothing at the consumers. Nothing in the tree ever discharged it.

**Why deleting the antecedent was not the repair, twice over.** First,
`Market.ProtocolAssurance.shieldedRingDescriptorRefinesFree_forces_no_decode` transfers: `StateDecode` is
LOG-BLIND, `dispatchArmFacetTB` is LOG-FORCING (`not_dispatchArmFacetTB_log_collapse`), so the forged pair
`(pre, ⟨post.kernel, pre.log⟩)` decodes the same `pc` and demands `pre.log = pc.turn :: pre.log`. Second —
and this is where this def was WORSE placed than the shielded twin — it carried NO
`tracePublishedCommit t = pc` link, so its `pc` was free; `descriptorRefinesTBKernelUnlinked_forces_no_decode`
(§8) proves that even the LOG-FREE kernel-endpoint half then entails that nothing decodes, at EVERY commit
map, because a decode is two equations in `pc.turn` and survives moving `pc` to a degenerate self-transfer
the `admitGuardAFacet` refuses.

**What replaced it.** `descriptorRefinesTBKernelFree` (§8) — no floor, `CommitSurface` replaced by a bare
`ApexFloorFree.CommitMap`, conclusion weakened to `dispatchArmFacetTBKernel`, and the publication link
RESTORED (which the apex already holds from `StarkSound.extract` and used to discard). Both poles live:
`dispatchArmFacetTBKernel_owner_fires` and `descriptorRefinesTBKernelFree_refutable`.

**What the caller now discharges.** `FacetLogResidual pc.turn pre post` — `post.log = pc.turn :: pre.log`,
one equation, zero quantifiers, naming the decoded pair AND the published turn — carried as an implication
on the instance the apex's existential binds. `facetLogResidual_unconditional_false` proves dropping it
makes the rung false, so it is work and not decoration.

**`descriptorRefinesTB_to_descriptorRefines` is DELETED, not rewired onto its old target.** It said the
turn-bound rung entails `CircuitSoundness.descriptorRefines S hash d (dispatchArmFacet fcaps provided 0)`
— i.e. "the turn-bound rung pins what the old existential rung leaves free". Its TARGET is itself a live
prop-body floor carrier (`CircuitSoundness.descriptorRefines`, `FloorCensus.sentinelPropBody`), so keeping
the lowering would mean forwarding into a dead antecedent from a rung that no longer has one — the exact
floor-to-floor plumbing with no reader at either end that this def's own §6 annotation named. The CONTENT
survives floor-free as `descriptorRefinesTBKernelFree_to_free_turn` (§9): the turn-bound kernel rung
entails `ApexFloorFree.descriptorRefinesFree` at the same arm with the turn released back to an
existential. ⚠ That is a STRICTLY WEAKER conclusion than the deleted lowering's, because the target arm is
the kernel half; the receipt-chain clause of the old target is the residual, and this is stated at the
weaker place deliberately rather than reconstructed with a floor.

⚠ The `hCR : Poseidon2SpongeCR hash` binder of the apex went with the rung: it was consumed ONLY to feed
the deleted antecedent. The `Dregg2/Verify/FloorRatchetBaseline.lean` rows naming `descriptorRefinesTB`,
`descriptorRefinesTB_to_descriptorRefines` and `lightclient_transfer_faithful_turnbound` are now SLACK —
that file is emitted as `baseline ∩ current`, so a baseline name that is no longer a carrier is absent
from `current` and never errors. They are left in place.

Do NOT resurrect this shape. Do NOT re-ground on `¬ SpongeColl` at a named pair (no proof here feeds the
sponge a pair, so a per-instance side condition would be decoration and a fresh carrier), and do NOT
re-ground on `OrBreak (SpongeCollision hash) _` — refuted wholesale by
`SpongeCollisionShirk.bareDisjunction_is_not_a_regrounding`. -/

/-! ## §6.R — THE REALIZATION: `hsrc` (and the src leg of `TurnIdentityBound`) DERIVED from the live
turn-identity PI weld, no longer carried.

`transfer_descriptorRefines_facetTB` carries `hbound : TurnIdentityBound pc tr` and `hauth :
TransferAuthoritySourceCanon … pc.turn` — whose `hsrc` field (`capOpenCols.src = tr.src`) is an ASSUMED
equality. `CapOpenTurnPins` REALIZES that binding in the live descriptor: `effCapOpenV3TB` publishes the
turn's `src` to a PI slot and welds the cap-open `src` column to it; the deployed verifier ANCHORS that PI
to `turn.src` (`TurnIdentityAnchored`). So a `Satisfied2` witness of the turn-pinned descriptor whose
verifier anchored `PI = turn.src` FORCES `capOpenCols.src = turn.src` — `hsrc` is now a CIRCUIT
consequence, no longer a structure field a prover supplies for a free column.

This section feeds that forced `hsrc` into the slim canonical authority source, so the transfer
refinement's authority leg rests on the OPENED LEAF's target welded to the PUBLISHED source — closing the
prover-chosen-src smuggle for the cap disjunct. -/

open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols EFF_TRANSFER)
open Dregg2.Circuit.Emit.CapOpenTurnPins
  (effCapOpenV3TB TurnIdentityAnchored effCapOpenV3TB_to_base effCapOpenV3TB_hsrc)
open Dregg2.Circuit.DeployedCapOpen (leafOf)
open Dregg2.Circuit.DeployedCapTree (CapHashScheme CapLeaf Cap8Scheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (canonicalLeafAt tierOfTag)
open Dregg2.Circuit.RotatedKernelRefinementFacet
  (EffAuthoritySourceCanon TransferAuthoritySourceCanon transferAuthoritySourceCanon_authorizes
   transfer_descriptorRefines_facet)

/-- The LIVE transfer cap-open descriptor with the turn-identity PI weld (`effCapOpenV3TB` at the
transfer base / `EFF_TRANSFER` bit). The descriptor the deployed prover routes through PLUS the three
turn-identity pins (`capOpenCols.src` welded to the published `src`). -/
def transferCapOpenEffV3TB : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2 :=
  effCapOpenV3TB Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER

/-- **`transferAuthoritySourceCanon_ofTB` — the slim canonical transfer authority source with `hsrc`
DERIVED from the turn-identity PI weld, on the FIRST (active) row.** Build the
`TransferAuthoritySourceCanon` over the LIVE `effCapOpenV3TB` cap-open. The turn-identity weld rides the
FIRST row (`.piBinding .first`), the SAME active row the membership binding gates bite on (`isFirst =
true` AND `isLast = false`, in any real ≥2-row trace), so the published-src binding and the depth-16
open constrain ONE `src` column — the source's row is `0`. The carried `hsrc` field is REPLACED by the
forced first-row binding `effCapOpenV3TB_hsrc` (`.piBinding .first` + the verifier anchor force
`capOpenCols.src(0) = tr.src`); `hiNotLast` comes from the genuine ≥2-row shape `hlen`. No cross-row
residual — the weld is co-located with the membership. The base `hsat` lifts via `effCapOpenV3TB_to_base`;
every other field (`hChip`/`hedge`/`htier`/`hipc`/the bit bounds) is the same cap-tree residual. -/
def transferAuthoritySourceCanon_ofTB (hash : List ℤ → ℤ) (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (S8 : Cap8Scheme) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut S8) (t.tf .poseidon2))
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash transferCapOpenEffV3TB
      minit mfin maddrs t)
    -- the FIRST row carries BOTH the membership gates (non-last) AND the turn-identity pin (first);
    -- `hlen` is the genuine ≥2-row shape of a real cap-open trace (depth-16 open + its wrap row).
    (hlen : 2 ≤ t.rows.length)
    (hanchor : TurnIdentityAnchored Dregg2.Circuit.RotatedKernelRefinement.transferV3
      "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER t 0 tr.src)
    -- the FIRST-row canonicality envelope (cells range-checked `0 ≤ · < p`): supplies the `hcanon` field
    -- AND the `hcellSrc` the `src` pin needs to lift the mod-`p` weld to the ℤ equality.
    (hcanon : Dregg2.Circuit.Emit.CapOpenEmit.CapOpenRowCanon
      (capOpenCols Dregg2.Circuit.RotatedKernelRefinement.transferV3.traceWidth)
      (Dregg2.Circuit.DescriptorIR2.envAt t 0) EFF_TRANSFER)
    -- the turn's `src` label is a canonical field element (`0 ≤ src < p`, the deployed Label range check).
    (hsrcLt : (tr.src : ℤ) < 2013265921)
    (hedge : leafOf (capOpenCols Dregg2.Circuit.RotatedKernelRefinement.transferV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt t 0)
      = canonicalLeafAt fcaps tr.actor tr.src)
    (hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
      c ∈ fcaps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk)
    (htier : (tierOfTag vkOfTag (canonicalLeafAt fcaps tr.actor tr.src).auth_tag).isSatisfiedBy
      provided = true) :
    TransferAuthoritySourceCanon hash fcaps provided pre tr where
  hn := by decide
  hn32 := by decide
  S8 := S8
  vkOfTag := vkOfTag
  minit := minit
  mfin := mfin
  maddrs := maddrs
  t := t
  hChip := hChip
  -- THE LIFT: the TB descriptor's witness restricts to the cap-open base descriptor.
  hsat := effCapOpenV3TB_to_base Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER hash minit mfin maddrs t hsat
  -- the source's cap-open row is the FIRST (active) row, where membership AND the pin co-fire.
  i := 0
  hi := by omega
  hiNotLast := by omega
  hcanon := hcanon
  -- THE DISCHARGE: `hsrc` on the first row is the `.piBinding .first` weld + the verifier anchor
  -- (`= tr.src`), lifted from the mod-`p` pin to the ℤ equality by the first-row cell canonicality
  -- (`hcanon.cells`) and the turn-src Label range (`hsrcLt`) — the SAME row the membership opens.
  hsrc := effCapOpenV3TB_hsrc Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER hash minit mfin maddrs t hsat
    0 (by omega) rfl tr.src hanchor (hcanon.cells _) hsrcLt
  hedge := hedge
  hipc := hipc
  htier := htier

set_option maxHeartbeats 800000 in
/-- **`transfer_descriptorRefines_facetTB_realized` — THE TURN-BOUND REFINEMENT WITH `hsrc` REALIZED
IN-CIRCUIT.** From a satisfying transfer VALUE witness + its decode, the turn-identity binding `hbound`,
AND the LIVE turn-identity-pinned cap-open `Satisfied2` (whose verifier-anchored PI weld FORCES
`capOpenCols.src = tr.src`), force `BalanceMovementSpecFacet fcaps provided pre pc.turn a post`. Unlike
`transfer_descriptorRefines_facetTB`, the authority source's `hsrc` is NOT a carried hypothesis — it is
DISCHARGED from the in-circuit PI weld (`transferAuthoritySourceCanon_ofTB`). The carried floor for the
authority leg SHRINKS: the cap-open `src` column is forced to the PUBLISHED source, so a cap proof
authorizes the committed src, not a free column. -/
theorem transfer_descriptorRefines_facetTB_realized (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (pc : PublishedCommit) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (hbound : TurnIdentityBound pc tr)
    (fcaps : FacetCaps) (provided : AuthProvided)
    -- the LIVE turn-identity-pinned cap-open witness + the verifier's anchor + the cap-tree residual:
    (Sc8 : Cap8Scheme) (vkOfTag : ℤ → Nat)
    (cminit : ℤ → ℤ) (cmfin : ℤ → ℤ × Nat) (cmaddrs : List ℤ)
    (ct : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Sc8) (ct.tf .poseidon2))
    (hcsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash transferCapOpenEffV3TB
      cminit cmfin cmaddrs ct)
    -- the cap-open membership + the turn-identity weld co-fire on the FIRST (active) row of the
    -- ≥2-row cap-open trace; `hclen` is its genuine shape (depth-16 open + its wrap row).
    (hclen : 2 ≤ ct.rows.length)
    (hanchor : TurnIdentityAnchored Dregg2.Circuit.RotatedKernelRefinement.transferV3
      "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER ct 0 pc.turn.src)
    -- the cap-open FIRST-row canonicality envelope (cells range-checked) + the turn-src Label range —
    -- what lifts the mod-`p` src pin to the ℤ equality (fed into `transferAuthoritySourceCanon_ofTB`).
    (hccanon : Dregg2.Circuit.Emit.CapOpenEmit.CapOpenRowCanon
      (capOpenCols Dregg2.Circuit.RotatedKernelRefinement.transferV3.traceWidth)
      (Dregg2.Circuit.DescriptorIR2.envAt ct 0) EFF_TRANSFER)
    (hsrcLt : (pc.turn.src : ℤ) < 2013265921)
    (hedge : leafOf (capOpenCols Dregg2.Circuit.RotatedKernelRefinement.transferV3.traceWidth) (Dregg2.Circuit.DescriptorIR2.envAt ct 0)
      = canonicalLeafAt fcaps pc.turn.actor pc.turn.src)
    (hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
      c ∈ fcaps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk)
    (htier : (tierOfTag vkOfTag (canonicalLeafAt fcaps pc.turn.actor pc.turn.src).auth_tag).isSatisfiedBy
      provided = true) :
    BalanceMovementSpecFacet fcaps provided pre pc.turn a post := by
  -- build the slim canonical authority source with `hsrc` DERIVED from the in-circuit PI weld.
  have hauth : TransferAuthoritySourceCanon hash fcaps provided pre pc.turn :=
    transferAuthoritySourceCanon_ofTB hash fcaps provided pre pc.turn Sc8 vkOfTag cminit cmfin cmaddrs ct
      hChip hcsat hclen hanchor hccanon hsrcLt hedge hipc htier
  -- the VALUE leg over the witness turn `tr`, rewritten to `pc.turn` via the turn-identity binding.
  have hval : BalanceMovementSpec pre tr a post :=
    transfer_descriptorRefines hash hside hsat pre post tr a henc
  rw [hbound.eq] at hval
  obtain ⟨⟨_htoy, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := hval
  -- the AUTHORITY leg — FORCED by the canonical cap-open whose `src` is the PUBLISHED source.
  have hfaithAuth : authorizedFacetB fcaps provided pc.turn = true :=
    transferAuthoritySourceCanon_authorizes hash fcaps provided pre pc.turn hauth
  exact ⟨⟨hfaithAuth, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩

/-! ## §8 — ⚑ THE SOUND HALF, AND THE PRECISE REASON THIS DEF IS WORSE PLACED THAN THE SHIELDED TWIN.

`descriptorRefinesTB`'s annotation (now the ⚰ TOMBSTONE at §6) recorded two findings and took neither:
the `Poseidon2SpongeCR` antecedent in its VALUE is dead and refuted, and DELETING it is not the repair,
because the conclusion `dispatchArmFacetTB` is LOG-FORCING while `StateDecode` is LOG-BLIND
(`Market.ProtocolAssurance.shieldedRingDescriptorRefinesFree_forces_no_decode`, proved for the shielded
twin, transfers verbatim). This section lands the same repair the shielded twin got — the
kernel-endpoint half plus a named per-instance log residual — and then measures the ONE
place where that def was genuinely worse. It landed ADDITIVELY on 2026-08-02 and was WIRED IN the same
day (§9); the def it replaces is deleted.

⚑⚑ **THE KERNEL-ENDPOINT HALF IS STATABLE HERE, BUT ONLY WITH THE PUBLICATION LINK RESTORED.** The §6
annotation was right that `descriptorRefinesTB` carried no `tracePublishedCommit t = pc`, and that is not
a cosmetic gap: `descriptorRefinesTBKernelUnlinked_forces_no_decode` proves that WITHOUT the link even
the log-free kernel-endpoint rung holds only where its own premise is empty — for a reason that has
nothing to do with the log. `StateDecodeC C pc pre post` is two equations in `pc.turn`, so from ANY
decode one manufactures a decode at ANY OTHER turn `τ` (take `pc' := ⟨C pre.kernel τ, C post.kernel τ,
τ⟩`), and the unlinked rung then demands the faithful arm on EVERY published turn — including a
degenerate self-transfer `⟨0,0,0,0⟩`, which `admitGuardAFacet`'s `src ≠ dst` conjunct refuses.
`descriptorRefinesTBKernelUnlinked_false` therefore refutes it at EVERY commit map, no exhibited
boundary needed.

So the honest kernel-endpoint rung here is `descriptorRefinesTBKernelFree`, which RESTORES the link (a
strictly weaker obligation — the apex already holds `tracePublishedCommit t = pi.toPublished` from
`StarkSound.extract` and throws it away, exactly as `ApexFloorFree.descriptorRefinesFree` observed of
`CircuitSoundness.descriptorRefines`). With the link restored the free-turn attack is closed and the
rung has both poles: `descriptorRefinesTBKernelFree_refutable` and
`dispatchArmFacetTBKernel_owner_fires`.

⚑ **THIS IS NOW WIRED IN (2026-08-02).** `descriptorRefinesTB` and `descriptorRefinesTB_to_
descriptorRefines` are DELETED (⚰ §6) and the apex — `lightclient_transfer_kernelArm_turnbound`, §9 —
takes `descriptorRefinesTBKernelFree` and binds no floor. What the turn-bound apex advertises DID change:
it exports the kernel-endpoint arm on the PUBLISHED turn plus `FacetLogResidual` as an implication on the
decoded pair, rather than the whole faithful arm. Nothing real was lost — the old conclusion was VACUOUS
at deployed BabyBear because the rung it rested on was — and the smuggle §1 closes is untouched: the
authority leg `authorizedFacetB fcaps provided pi.turn` still reads the PUBLISHED turn, since
`dispatchArmFacetTBKernel` retains every conjunct of `BalanceMovementSpecFacet` except the receipt-chain
one. -/

section KernelEndpointRungTB

open Dregg2.Circuit.ApexFloorFree
  (CommitMap StateDecodeC emptyTrace satisfied2_emptyTrace state0 state1 kernel0 kernel1 kernel0_wf
   kernel1_wf kernel1_ne_kernel0 collapseMap)

/-- **`dispatchArmFacetTBKernel fcaps provided pubTurn pre post` — the KERNEL-ENDPOINT half of
`dispatchArmFacetTB`.** The turn-bound faithful arm with its receipt-chain clause discharged by
construction: the spec is asked at the post state's KERNEL paired with the log the spec itself forces,
so its `st'.log = tr :: st.log` conjunct is `rfl` and every remaining conjunct — the deployed two-axis
authority over the PUBLISHED turn, non-negativity, availability, distinctness, liveness, accepts, the
`recTransferBal` ledger movement and the 16-field frame — reads kernels alone.

Stated this way rather than by restating twenty conjuncts, so it is by CONSTRUCTION the same spec, not a
second one that could drift from it. -/
def dispatchArmFacetTBKernel (fcaps : FacetCaps) (provided : AuthProvided) (pubTurn : Turn)
    (pre post : RecChainedState) : Prop :=
  ∃ a : AssetId,
    BalanceMovementSpecFacet fcaps provided pre pubTurn a ⟨post.kernel, pubTurn :: pre.log⟩

/-- **`FacetLogResidual pubTurn pre post` — THE LOG CLAUSE, NAMED, PER INSTANCE.** The receipt-chain
advance of `BalanceMovementSpecFacet`, as a proposition about ONE named pair and ONE named published
turn. It quantifies over nothing: not `∀ pre post, …` (a universal side condition over decoded pairs is
`ClosureLog.StateDecodeLog`'s `logHashInjective` rewritten — the refuted floor this port exists to
avoid), and not `_ ∨ ∃ collision` (free — `SpongeCollisionShirk.orBreak_spongeCollision_iff_True`). -/
def FacetLogResidual (pubTurn : Turn) (pre post : RecChainedState) : Prop :=
  post.log = pubTurn :: pre.log

/-- ⚑ **POST-LOG BLINDNESS, DEFINITIONALLY.** The kernel-endpoint arm does not read the post state's
receipt chain: replacing it by anything at all is the SAME proposition, by `Iff.rfl`.

This is the exact move the log-forcing rung dies to. `StateDecodeC` reads `pre.kernel`, `post.kernel`
and their well-formedness and NEVER `.log`, so from any decode of `(pre, post)` the forged pair
`(pre, ⟨post.kernel, pre.log⟩)` decodes the same commitment; against `dispatchArmFacetTB` that yields
`pre.log = pubTurn :: pre.log` (`not_dispatchArmFacetTB_log_collapse`), and against this conclusion it
yields nothing. -/
theorem dispatchArmFacetTBKernel_post_log_blind (fcaps : FacetCaps) (provided : AuthProvided)
    (pubTurn : Turn) (pre post : RecChainedState) (l : List Turn) :
    dispatchArmFacetTBKernel fcaps provided pubTurn pre ⟨post.kernel, l⟩
      ↔ dispatchArmFacetTBKernel fcaps provided pubTurn pre post := Iff.rfl

/-- ⚑ **THE ENGINE OF THE REFUTATION, ISOLATED.** At the log-collapsed pair the FULL turn-bound arm is
false — for EVERY `pre`, `post` and published turn, at no hypothesis: the spec demands
`post.log = pubTurn :: pre.log` and the collapsed pair's post log IS `pre.log`. -/
theorem not_dispatchArmFacetTB_log_collapse (fcaps : FacetCaps) (provided : AuthProvided)
    (pubTurn : Turn) (pre post : RecChainedState) :
    ¬ dispatchArmFacetTB fcaps provided pubTurn pre ⟨post.kernel, pre.log⟩ := by
  rintro ⟨_a, hspec⟩
  have hlog : pre.log = pubTurn :: pre.log := hspec.2.2.1
  have hlen := congrArg List.length hlog
  simp at hlen

/-- The full turn-bound arm entails its kernel-endpoint half — this rung claims strictly less. -/
theorem dispatchArmFacetTB.kernelArm (fcaps : FacetCaps) (provided : AuthProvided) (pubTurn : Turn)
    (pre post : RecChainedState) (h : dispatchArmFacetTB fcaps provided pubTurn pre post) :
    dispatchArmFacetTBKernel fcaps provided pubTurn pre post := by
  obtain ⟨a, hspec⟩ := h
  refine ⟨a, ?_⟩
  have heq : (⟨post.kernel, pubTurn :: pre.log⟩ : RecChainedState) = post := by
    rw [← (hspec.2.2.1 : post.log = pubTurn :: pre.log)]
  rwa [heq]

/-- **THE DECOMPOSITION.** Kernel endpoints plus the named log residual reassemble the full turn-bound
faithful arm, with no floor and no side condition anywhere. -/
theorem dispatchArmFacetTB_of_kernelArm_and_residual (fcaps : FacetCaps) (provided : AuthProvided)
    (pubTurn : Turn) (pre post : RecChainedState)
    (hk : dispatchArmFacetTBKernel fcaps provided pubTurn pre post)
    (hres : FacetLogResidual pubTurn pre post) :
    dispatchArmFacetTB fcaps provided pubTurn pre post := by
  obtain ⟨a, hspec⟩ := hk
  refine ⟨a, ?_⟩
  have heq : (⟨post.kernel, pubTurn :: pre.log⟩ : RecChainedState) = post := by
    rw [← (hres : post.log = pubTurn :: pre.log)]
  rwa [heq] at hspec

/-- **SATISFIABLE — the kernel-endpoint arm FIRES on the owner path.** The same pole the full arm has
(`dispatchArmFacetTB_owner_fires`), one rung down: an owner-authorized PUBLISHED transfer with a valid
value movement inhabits it. So neither the rung's conclusion nor
`facetLogResidual_unconditional_false`'s hypothesis is an empty proposition. -/
theorem dispatchArmFacetTBKernel_owner_fires (fcaps : FacetCaps) (provided : AuthProvided)
    (pc : PublishedCommit) (pre post : RecChainedState) (a : AssetId)
    (howner : pc.turn.actor = pc.turn.src)
    (hval : BalanceMovementSpec pre pc.turn a post) :
    dispatchArmFacetTBKernel fcaps provided pc.turn pre post :=
  dispatchArmFacetTB.kernelArm fcaps provided pc.turn pre post
    (dispatchArmFacetTB_owner fcaps provided pc pre post a howner hval)

/-- ⚑⚑ **DROPPING THE RESIDUAL MAKES THE RUNG FALSE.** Wherever the kernel-endpoint arm holds at all,
the implication "kernel-endpoint arm ⟹ full turn-bound arm" is FALSE: the log-collapse of that very pair
satisfies the kernel arm (`dispatchArmFacetTBKernel_post_log_blind`, definitionally) and refutes the full
one (`not_dispatchArmFacetTB_log_collapse`). So `FacetLogResidual` is honest work and not decoration.

Stated from an inhabitant rather than unconditionally, because a `¬ ∀` whose antecedent is never
satisfied is exactly the emptiness this section exists to rule out. -/
theorem facetLogResidual_unconditional_false (fcaps : FacetCaps) (provided : AuthProvided)
    (pubTurn : Turn) (pre post : RecChainedState)
    (hk : dispatchArmFacetTBKernel fcaps provided pubTurn pre post) :
    ¬ ∀ (pre' post' : RecChainedState),
        dispatchArmFacetTBKernel fcaps provided pubTurn pre' post' →
        dispatchArmFacetTB fcaps provided pubTurn pre' post' := by
  intro hall
  exact not_dispatchArmFacetTB_log_collapse fcaps provided pubTurn pre post
    (hall pre ⟨post.kernel, pre.log⟩ hk)

/-- **`descriptorRefinesTBKernelFree C hash d fcaps provided` — THE SOUND RUNG, and since 2026-08-02 the
ONLY per-effect rung the turn-bound apex takes.** The retired `descriptorRefinesTB` (⚰ §6)
with the refuted `Poseidon2SpongeCR` antecedent gone, the `CommitSurface` bundle replaced by a bare
commit map, the conclusion weakened to its kernel-endpoint half, AND the publication link
`tracePublishedCommit t = pc` RESTORED. The link is not decoration here: without it the rung is refuted
at every commit map (`descriptorRefinesTBKernelUnlinked_false`), log or no log. -/
def descriptorRefinesTBKernelFree (C : CommitMap) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (fcaps : FacetCaps) (provided : AuthProvided) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    tracePublishedCommit t = pc →
    StateDecodeC C pc pre post →
    dispatchArmFacetTBKernel fcaps provided pc.turn pre post

/-- **`descriptorRefinesTBKernelUnlinked` — the same rung with `descriptorRefinesTB`'s OWN quantifier
prefix**, i.e. with the publication link still absent. Minted only to be refuted; it is the shape the
deployed def has, one rung down. -/
def descriptorRefinesTBKernelUnlinked (C : CommitMap) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (fcaps : FacetCaps) (provided : AuthProvided) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    StateDecodeC C pc pre post →
    dispatchArmFacetTBKernel fcaps provided pc.turn pre post

/-- ⚑⚑ **THE MEASUREMENT: WITHOUT THE PUBLICATION LINK, EVEN THE KERNEL-ENDPOINT HALF ENTAILS THAT
NOTHING DECODES.** If the unlinked rung holds then no pair of chained states decodes any published
commitment at any commit map. The proof uses nothing about the hash and nothing about the log: a decode
is two equations in `pc.turn`, so it survives replacing `pc` by `⟨C pre.kernel τ, C post.kernel τ, τ⟩`
for ANY turn `τ`; at the degenerate self-transfer `τ = ⟨0,0,0,0⟩` the arm's `admitGuardAFacet` demands
`τ.src ≠ τ.dst`.

⚠ This is the precise sense in which `descriptorRefinesTB` is WORSE placed than the shielded twin. There,
weakening the conclusion to its kernel-endpoint half is the whole repair; here it is not enough, and the
publication link has to be restored first. -/
theorem descriptorRefinesTBKernelUnlinked_forces_no_decode
    (C : CommitMap) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (fcaps : FacetCaps) (provided : AuthProvided)
    (h : descriptorRefinesTBKernelUnlinked C hash d fcaps provided)
    (pc : PublishedCommit) (pre post : RecChainedState)
    (hdec : StateDecodeC C pc pre post) : False := by
  obtain ⟨_a, hspec⟩ :=
    h (fun _ => 0) (fun _ => (0, 0)) [] emptyTrace
      ⟨C pre.kernel ⟨0, 0, 0, 0⟩, C post.kernel ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩ pre post
      (satisfied2_emptyTrace hash d _ _) ⟨rfl, rfl, hdec.preWF, hdec.postWF⟩
  exact hspec.1.2.2.2.1 rfl

/-- ⚑ **REFUTED AT EVERY COMMIT MAP** — the premise of the measurement above is inhabited everywhere,
since `ApexFloorFree.state0` is well-formed and `⟨C kernel0 τ, C kernel0 τ, τ⟩` decodes it by `rfl`. No
exhibited boundary and no opaque published value is needed: the unlinked shape is empty at every
parameter. -/
theorem descriptorRefinesTBKernelUnlinked_false (C : CommitMap) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (fcaps : FacetCaps) (provided : AuthProvided) :
    ¬ descriptorRefinesTBKernelUnlinked C hash d fcaps provided := fun h =>
  descriptorRefinesTBKernelUnlinked_forces_no_decode C hash d fcaps provided h
    ⟨C kernel0 ⟨0, 0, 0, 0⟩, C kernel0 ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩ state0 state0
    ⟨rfl, rfl, kernel0_wf, kernel0_wf⟩

/-- ⚑ **REFUTABLE — the LINKED sound rung passes the standing acceptance test.** At the exhibited commit
map `ApexFloorFree.collapseMap emptyTrace`, for EVERY hash and EVERY descriptor (the deployed `Rfix e`
included), every `fcaps` and every `provided`, the kernel-endpoint rung is FALSE. `state0`'s kernel has
NO live accounts, and `admitGuardAFacet` demands the published source be one — a KERNEL refutation, which
is what a kernel-endpoint rung ought to be refutable on, and it says nothing about the log.

Contrast, at the same descriptor and a deployed-shaped sponge: the retired `descriptorRefinesTB` (⚰ §6)
HELD, because `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` refutes its antecedent. That
obligation was discharged by the PARAMETERS; this one is a claim about the circuit. -/
theorem descriptorRefinesTBKernelFree_refutable (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (fcaps : FacetCaps) (provided : AuthProvided) :
    ¬ descriptorRefinesTBKernelFree (collapseMap emptyTrace) hash d fcaps provided := by
  intro h
  have hdec : StateDecodeC (collapseMap emptyTrace) (tracePublishedCommit emptyTrace) state0 state1 := by
    refine ⟨?_, ?_, kernel0_wf, kernel1_wf⟩
    · show (tracePublishedCommit emptyTrace).pubPre
          = collapseMap emptyTrace kernel0 (tracePublishedCommit emptyTrace).turn
      unfold collapseMap
      rw [if_pos rfl]
    · show (tracePublishedCommit emptyTrace).pubPost
          = collapseMap emptyTrace kernel1 (tracePublishedCommit emptyTrace).turn
      unfold collapseMap
      rw [if_neg kernel1_ne_kernel0]
  obtain ⟨_a, hspec⟩ :=
    h (fun _ => 0) (fun _ => (0, 0)) [] emptyTrace (tracePublishedCommit emptyTrace) state0 state1
      (satisfied2_emptyTrace hash d _ _) rfl hdec
  have hmem : (tracePublishedCommit emptyTrace).turn.src ∈ (∅ : Finset CellId) :=
    hspec.1.2.2.2.2.1
  simp at hmem

#assert_axioms dispatchArmFacetTBKernel
#assert_axioms FacetLogResidual
#assert_axioms dispatchArmFacetTBKernel_post_log_blind
#assert_axioms not_dispatchArmFacetTB_log_collapse
#assert_axioms dispatchArmFacetTB.kernelArm
#assert_axioms dispatchArmFacetTB_of_kernelArm_and_residual
#assert_axioms dispatchArmFacetTBKernel_owner_fires
#assert_axioms facetLogResidual_unconditional_false
#assert_axioms descriptorRefinesTBKernelFree
#assert_axioms descriptorRefinesTBKernelUnlinked
#assert_axioms descriptorRefinesTBKernelUnlinked_forces_no_decode
#assert_axioms descriptorRefinesTBKernelUnlinked_false
#assert_axioms descriptorRefinesTBKernelFree_refutable

end KernelEndpointRungTB

/-! ## §9 — ⚑ THE TURN-BOUND APEX, REWIRED ONTO THE SOUND RUNG (2026-08-02).

`lightclient_transfer_faithful_turnbound` stood in §6 on `descriptorRefinesTB`, whose
`Poseidon2SpongeCR` antecedent `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` refutes at deployed
BabyBear — so the apex asserted nothing at the parameters we deploy at. It now stands on
`descriptorRefinesTBKernelFree` (§8) and binds no floor at all: `hCR` is gone, because its only use was to
feed the deleted antecedent.

**WHAT IT ADVERTISES NOW, EXACTLY.** UNCONDITIONALLY: the decode, the two commitment equations, and
`dispatchArmFacetTBKernel fcaps provided pi.turn pre post` — the faithful arm on the PUBLISHED turn with
its receipt-chain conjunct discharged by construction, i.e. the deployed two-axis authority gate over
`pi.turn`, non-negativity, availability, `src ≠ dst`, liveness, accepts, the `recTransferBal` movement and
the 16-field frame. BEHIND `FacetLogResidual pi.turn pre post`: the full `dispatchArmFacetTB`. So the
smuggle §1 closes is untouched — the authority a light client is certified is still over the turn it
PUBLISHED — and what moved behind the residual is only the receipt-chain advance.

**THE PUBLICATION LINK IS NOW CONSUMED.** The old apex held `tracePublishedCommit t = pi.toPublished` from
`StarkSound.extract` and threw it away. §8's rung takes it, and `descriptorRefinesTBKernelUnlinked_false`
shows that is not bookkeeping: without it the rung is refuted at every commit map. The apex therefore asks
STRICTLY LESS of the circuit than the deleted one did while carrying no floor. -/

section TurnBoundApexRewired

open Dregg2.Circuit.ApexFloorFree (CommitMap StateDecodeC descriptorRefinesFree)

/-- ★ **`lightclient_transfer_kernelArm_turnbound` — THE TURN-BOUND APEX, FLOOR-FREE.** From a verifying
batch, `[StarkSound hash R]`, the carried witness→state existence rung, and the turn-bound KERNEL rung
`descriptorRefinesTBKernelFree` at `S.commit`, there EXIST decoded endpoints between which the faithful
transfer arm holds ON THE PUBLISHED TURN `pi.turn` at its kernel endpoints, with the receipt-chain advance
carried as a NAMED per-instance residual on that pair.

⚰ Renamed from `lightclient_transfer_faithful_turnbound` (⚰ §6): the old name promised the whole faithful
arm from an accept, and what an accept plus a sound rung delivers is the kernel arm, plus the faithful arm
under `FacetLogResidual`.

⚠ **NOTHING REAL IS LOST, at the right resolution.** The old theorem was UNAPPLICABLE at deployed
BabyBear — its `hCR : Poseidon2SpongeCR hash` binder is refuted there
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`) — and its one circuit-specific premise, `hrefines`
at `descriptorRefinesTB`, was FREE there for the same reason, so it constrained the transfer circuit in
no way either. Unusable premise plus empty premise; what replaces it is a real guarantee over `pi.turn`
plus a residual the caller can see and discharge.

The `CommitSurface` here is read only through its `commit` projection (`ApexFloorFree` §1), which is why
the rung is asked at `S.commit` and the decode converts field for field. -/
theorem lightclient_transfer_kernelArm_turnbound
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry) [StarkSound hash R]
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hrefines : ∀ e, descriptorRefinesTBKernelFree S.commit hash (R e) fcaps provided)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      dispatchArmFacetTBKernel fcaps provided pi.turn pre post ∧
      (FacetLogResidual pi.turn pre post → dispatchArmFacetTB fcaps provided pi.turn pre post) ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- `StateDecode S` IS `StateDecodeC S.commit`, field for field.
  have hdecC : StateDecodeC S.commit pi.toPublished pre post :=
    ⟨hdecode.preBinds, hdecode.postBinds, hdecode.preWF, hdecode.postWF⟩
  -- the sound rung, fed the SAME publication link the extraction supplied.
  have hstep : dispatchArmFacetTBKernel fcaps provided pi.toPublished.turn pre post :=
    hrefines pi.effect minit mfin maddrs t pi.toPublished pre post hsat hpub hdecC
  rw [BatchPublicInputs.toPublished_turn] at hstep
  exact ⟨pre, post, hdecode, hstep,
    fun hres =>
      dispatchArmFacetTB_of_kernelArm_and_residual fcaps provided pi.turn pre post hstep hres,
    by simpa using hdecode.preBinds, by simpa using hdecode.postBinds⟩

/-- **`descriptorRefinesTBKernelFree_to_free_turn` — what survives of the deleted lowering.**
`descriptorRefinesTB_to_descriptorRefines` (⚰ §6) said the turn-bound rung entails the existential-turn
rung, i.e. it PINS what the old one leaves free. That comparison is restated here at the sound rungs: the
turn-bound kernel rung entails `ApexFloorFree.descriptorRefinesFree` at the same arm with the turn
released back to an existential, and the witness is the PUBLISHED `pc.turn`.

⚠ Say what this is NOT. The deleted lowering's target was `CircuitSoundness.descriptorRefines`, which
carries its own refuted `Poseidon2SpongeCR` antecedent in its VALUE; forwarding into it from a rung that
no longer has one is floor-to-floor plumbing with no reader at either end. This is stated at
`descriptorRefinesFree` instead, and at the KERNEL arm — a strictly weaker conclusion than the deleted
one's, the difference being exactly `FacetLogResidual`. The converse fails, which is the whole point of
this module: a free turn is the smuggle §1 names. -/
theorem descriptorRefinesTBKernelFree_to_free_turn (C : CommitMap) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (fcaps : FacetCaps) (provided : AuthProvided)
    (h : descriptorRefinesTBKernelFree C hash d fcaps provided) :
    descriptorRefinesFree C hash d
      (fun pre post => ∃ tr : Turn, dispatchArmFacetTBKernel fcaps provided tr pre post) :=
  fun minit mfin maddrs t pc pre post hsat hlink hdec =>
    ⟨pc.turn, h minit mfin maddrs t pc pre post hsat hlink hdec⟩

#assert_axioms lightclient_transfer_kernelArm_turnbound
#assert_axioms descriptorRefinesTBKernelFree_to_free_turn

end TurnBoundApexRewired

/-! ## §7 — Axiom hygiene. -/

#assert_axioms transferAuthoritySourceCanon_ofTB
#assert_axioms transfer_descriptorRefines_facetTB_realized
#assert_axioms TurnIdentityBound.eq
#assert_axioms dispatchArmFacetTB_to_dispatchArmFacet
#assert_axioms ownerGateForced
#assert_axioms dispatchArmFacetTB_owner
#assert_axioms transfer_descriptorRefines_facetTB
#assert_axioms transfer_descriptorRefinesTB_dispatchArm
#assert_axioms dispatchArmFacetTB_rejects_unauthorized
#assert_axioms dispatchArmFacetTB_owner_fires

end Dregg2.Circuit.RotatedKernelRefinementFacetTurnBound
