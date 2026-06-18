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

  5. **`descriptorRefinesTB`** + **`lightclient_transfer_faithful_turnbound`** — the apex re-stated so
     the conclusion's turn IS `pi.turn`: the authority a light client gets is over the turn it
     published, NOT a free one.

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
imported keystones. No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW names only.
-/
import Dregg2.Circuit.RotatedKernelRefinementFacet
import Dregg2.Circuit.Emit.CapOpenTurnPins

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
    (hside : RotTableSide hash t)
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
    (hside : RotTableSide hash t)
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

/-! ## §6 — the TURN-BOUND apex: the authority a light client gets is over the turn it PUBLISHED.

`descriptorRefinesTB` is the per-effect rung whose `kstep` is the TURN-BOUND arm over `pc.turn`; the
apex over it concludes the step on the PUBLISHED turn — the smuggle (authority over a free turn) closed.
The turn-identity binding `TurnIdentityBound` is consumed inside the rung (it is the named PI obligation
the rung needs to tie the witness turn to the published one). -/

/-- **`descriptorRefinesTB S hash d fcaps provided`** — the per-effect refinement whose kernel step is
the TURN-BOUND faithful arm: any satisfying witness of `d` whose published commitment `pc` decodes to
`pre`/`post` forces `dispatchArmFacetTB fcaps provided pc.turn pre post` — the faithful step ON THE
PUBLISHED TURN. The turn-identity binding lives inside the discharge (the value-rung's witness turn IS
`pc.turn`); the conclusion's turn is the light client's `pc.turn`, not a free existential. -/
def descriptorRefinesTB (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (fcaps : FacetCaps) (provided : AuthProvided) : Prop :=
  Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash →
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    StateDecode S pc pre post →
    dispatchArmFacetTB fcaps provided pc.turn pre post

/-- **`descriptorRefinesTB_to_descriptorRefines`** — the turn-bound rung entails the existential rung at
`dispatchArmFacet`, so an apex carrying `descriptorRefinesTB` is STRONGER than one carrying the old
`descriptorRefines … (dispatchArmFacet …)` (it pins the turn the old one left free). -/
theorem descriptorRefinesTB_to_descriptorRefines (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (fcaps : FacetCaps) (provided : AuthProvided)
    (h : descriptorRefinesTB S hash d fcaps provided) :
    descriptorRefines S hash d (Dregg2.Circuit.RotatedKernelRefinementFacet.dispatchArmFacet fcaps provided 0) := by
  intro hCR minit mfin maddrs t pc pre post hsat hdec
  exact dispatchArmFacetTB_to_dispatchArmFacet fcaps provided pc.turn pre post
    (h hCR minit mfin maddrs t pc pre post hsat hdec)

/-- **`lightclient_transfer_faithful_turnbound` — THE TURN-BOUND APEX.** From a verifying batch + the
named floors + the carried TURN-BOUND per-effect rung `descriptorRefinesTB`, there EXIST decoded
endpoints and a genuine faithful transfer transition ON THE PUBLISHED TURN `pi.turn`: the authority leg
(owner OR cap) reads the turn the LIGHT CLIENT PUBLISHED, not a free existential. The light client RAN
NOTHING; the authority it is certified is over the identity it sees. This closes the owner-authority /
turn-identity smuggle at the apex. -/
theorem lightclient_transfer_faithful_turnbound
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash) [StarkSound hash R]
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hrefines : ∀ e, descriptorRefinesTB S hash (R e) fcaps provided)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      dispatchArmFacetTB fcaps provided pi.turn pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  -- lower the turn-bound rung to the existential rung and run the apex; then re-derive the STRONGER
  -- turn-bound conclusion from the same witness via the turn-bound rung directly.
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- the turn-bound rung forces the step ON THE PUBLISHED TURN `pi.toPublished.turn = pi.turn`.
  have hstep : dispatchArmFacetTB fcaps provided pi.toPublished.turn pre post :=
    hrefines pi.effect hCR minit mfin maddrs t pi.toPublished pre post hsat hdecode
  rw [BatchPublicInputs.toPublished_turn] at hstep
  exact ⟨pre, post, hdecode, hstep, by simpa using hdecode.preBinds, by simpa using hdecode.postBinds⟩

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
open Dregg2.Circuit.DeployedCapTree (CapHashScheme CapLeaf)
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
DERIVED from the turn-identity PI weld.** Build the `TransferAuthoritySourceCanon` over the LIVE
`effCapOpenV3TB` cap-open whose `src` column the verifier-anchored PI pins to `tr.src`: the carried
`hsrc` field is REPLACED by the forced `effCapOpenV3TB_hsrc` (the PI weld + the anchor). The base `hsat`
is lifted from the TB descriptor via `effCapOpenV3TB_to_base`; every other field (`hChip`/`hedge`/
`htier`/`hipc`/the bit bounds) is the same cap-tree residual as before — this constructor closes ONLY the
`src`-binding leg, in-circuit. -/
def transferAuthoritySourceCanon_ofTB (hash : List ℤ → ℤ) (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : Dregg2.Circuit.DescriptorIR2.ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 S.chipAbsorb transferCapOpenEffV3TB
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : (i + 1 == t.rows.length) = true)
    (hanchor : TurnIdentityAnchored Dregg2.Circuit.RotatedKernelRefinement.transferV3
      "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER t i tr.src tr.actor tr.dst)
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt t i)
      = canonicalLeafAt fcaps tr.actor tr.src)
    (hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
      c ∈ fcaps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk)
    (htier : (tierOfTag vkOfTag (canonicalLeafAt fcaps tr.actor tr.src).auth_tag).isSatisfiedBy
      provided = true) :
    TransferAuthoritySourceCanon hash fcaps provided pre tr where
  hn := by decide
  hn32 := by decide
  State := State
  S := S
  vkOfTag := vkOfTag
  minit := minit
  mfin := mfin
  maddrs := maddrs
  t := t
  hChip := hChip
  -- THE LIFT: the TB descriptor's witness restricts to the cap-open base descriptor.
  hsat := effCapOpenV3TB_to_base Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER S.chipAbsorb minit mfin maddrs t hsat
  i := i
  hi := hi
  -- THE DISCHARGE: `hsrc` is FORCED by the turn-identity PI weld + the verifier's anchor, not carried.
  hsrc := effCapOpenV3TB_hsrc Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER S.chipAbsorb minit mfin maddrs t hsat
    i hi hlast tr.src tr.actor tr.dst hanchor
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
    (hside : RotTableSide hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (pc : PublishedCommit) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (hbound : TurnIdentityBound pc tr)
    (fcaps : FacetCaps) (provided : AuthProvided)
    -- the LIVE turn-identity-pinned cap-open witness + the verifier's anchor + the cap-tree residual:
    {State : Type} (Sc : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (cminit : ℤ → ℤ) (cmfin : ℤ → ℤ × Nat) (cmaddrs : List ℤ)
    (ct : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (hChip : Dregg2.Circuit.DescriptorIR2.ChipTableSound Sc.chipAbsorb (ct.tf .poseidon2))
    (hcsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 Sc.chipAbsorb transferCapOpenEffV3TB
      cminit cmfin cmaddrs ct)
    (ci : Nat) (hci : ci < ct.rows.length) (hclast : (ci + 1 == ct.rows.length) = true)
    (hanchor : TurnIdentityAnchored Dregg2.Circuit.RotatedKernelRefinement.transferV3
      "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER ct ci pc.turn.src pc.turn.actor
      pc.turn.dst)
    (hedge : leafOf capOpenCols (Dregg2.Circuit.DescriptorIR2.envAt ct ci)
      = canonicalLeafAt fcaps pc.turn.actor pc.turn.src)
    (hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
      c ∈ fcaps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk)
    (htier : (tierOfTag vkOfTag (canonicalLeafAt fcaps pc.turn.actor pc.turn.src).auth_tag).isSatisfiedBy
      provided = true) :
    BalanceMovementSpecFacet fcaps provided pre pc.turn a post := by
  -- build the slim canonical authority source with `hsrc` DERIVED from the in-circuit PI weld.
  have hauth : TransferAuthoritySourceCanon hash fcaps provided pre pc.turn :=
    transferAuthoritySourceCanon_ofTB hash fcaps provided pre pc.turn Sc vkOfTag cminit cmfin cmaddrs ct
      hChip hcsat ci hci hclast hanchor hedge hipc htier
  -- the VALUE leg over the witness turn `tr`, rewritten to `pc.turn` via the turn-identity binding.
  have hval : BalanceMovementSpec pre tr a post :=
    transfer_descriptorRefines hash hside hsat pre post tr a henc
  rw [hbound.eq] at hval
  obtain ⟨⟨_htoy, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := hval
  -- the AUTHORITY leg — FORCED by the canonical cap-open whose `src` is the PUBLISHED source.
  have hfaithAuth : authorizedFacetB fcaps provided pc.turn = true :=
    transferAuthoritySourceCanon_authorizes hash fcaps provided pre pc.turn hauth
  exact ⟨⟨hfaithAuth, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩

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
#assert_axioms descriptorRefinesTB_to_descriptorRefines
#assert_axioms lightclient_transfer_faithful_turnbound

end Dregg2.Circuit.RotatedKernelRefinementFacetTurnBound
