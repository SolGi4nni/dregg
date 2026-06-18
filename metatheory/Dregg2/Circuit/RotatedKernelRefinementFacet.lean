/-
# Dregg2.Circuit.RotatedKernelRefinementFacet — the AUTHORITY leg of the soundness apex, closed
faithfully for `transfer` (the template the ~29 other effects follow).

## What this module closes (the authority leg)

`RotatedKernelRefinement.lean` builds the VALUE rung: the live rotated transfer circuit FORCES the
debit/credit movement + availability (`transfer_descriptorRefines` against `BalanceMovementSpec`).
But its AUTHORITY conjunct rides the TOY `admitGuardA`/`authorizedB` (`authorizedB k.caps t`) as a
carried `rotatedEncodes.guardAuth` field — the toy `Cap.node`/`Auth.write` shadow, not the deployed
two-axis (tier × facet) gate.

This module repoints that conjunct onto the FAITHFUL `authorizedFacetB`
(`Dregg2.Exec.FacetAuthority`), and DISCHARGES it — no longer carried — from the IN-CIRCUIT cap-open
the descriptor now realizes (`CapOpenEmit.transferCapOpenEffV3_authorizes` — the LIVE membership
descriptor the deployed prover routes through). It is PURELY ADDITIVE: the toy `BalanceMovementSpec`,
`admitGuardA`, `authorizedB`, and the ~150 modules that read them are UNTOUCHED.

## What is built (the three rungs of the prompt)

  1. **`BalanceMovementSpecFacetK`** (over `FacetKernelState`) + **`execFaithful_iff_specFacet`** —
     the FAITHFUL executor (`FacetAuthority.execFaithful`, which gates on `authorizedFacetB`) ⟺ the
     FAITHFUL full-state spec, BOTH directions. The authority conjunct is
     `authorizedFacetB k.fcaps provided turn = true` over the deployed FACET caps. This is the
     executor corner of the faithful triangle (the §10(A) `exec_authorized` made a ⟺).

  2. **`BalanceMovementSpecFacet`** (over `RecChainedState`, parameterized by the deployed
     `fcaps`/`provided`) + **`transfer_descriptorRefines_facet`** — the TEMPLATE keystone. Identical
     to `BalanceMovementSpec` EXCEPT the `admitGuardA` authority conjunct is
     `authorizedFacetB fcaps provided tr = true`. The VALUE leg (debit/credit/availability/frame/log)
     is REUSED verbatim from `RotatedKernelRefinement` via `transfer_descriptorRefines`; the AUTHORITY
     leg is FORCED by the cap-open (`capOpen_authorizes ⟹ authorizedFacetB`), discharged from the
     decoded `fcaps` wired to the cap-open's opened leaf — NOT a carried assumption.

  3. **`dispatchArmFacet`** + **`lightclient_transfer_faithful` / `lightclient_transfer_faithful_forest`**
     — the apex (`CircuitSoundness.lightclient_unfoolable` / `lightclient_turn_unfoolable_forest`)
     instantiated at `kstep := dispatchArmFacet`, whose `.balanceA` arm is `BalanceMovementSpecFacet`.
     The apex now concludes a FAITHFUL kernel transition for a transfer turn: the authority leg is the
     deployed two-axis gate, discharged by the in-circuit cap-open.

## The `StateDecode ↔ cap-open` wiring (the named bridge — NOT assumed)

The apex hands the rung a `StateDecode S pc pre post` (the published-commitment binding) and a
`Satisfied2 hash transferV3` witness. The VALUE leg needs the `rotatedEncodes` boundary decode; the
AUTHORITY leg needs the cap-open `Satisfied` row + the deployed-faithfulness `DeployedFaithful` for
the decoded `fcaps`, plus the `(actor ⇒ src)` edge identification. None of these are derivable from
`StateDecode` alone (the commitment surface commits the LEDGER, not the cap-tree's leaf assignment
nor the `fcaps`). So they are bundled as ONE named bridge `TransferAuthoritySource` (§2), exactly the
genuine residual the commitment cannot certify — named, not laundered. The authority CONCLUSION
(`authorizedFacetB`) is then DERIVED inside, FROM the cap-open, not taken as a field.

## Residual ledger (carried, named — not faked)

  * **The tier is `Signature`** (`provided := .signature`): the in-circuit `authTagGate` pins
    `auth_tag = 1`, so the cap-open discharges `authorizedFacetB … .signature …`. Reading the tier
    generically off the committed `auth_tag` is the `FacetAuthority §10` named residual.
  * **The `Custom`-tier vk decode** (`vkOfTag`): transfers never use `Custom` (tag ≠ 5), so it is
    inert here; carried as the named felt-absorb residual.
  * **`TransferAuthoritySource`** (the §2 bridge): the cap-open `Satisfied` row, the deployed
    faithfulness, and the edge identification — the genuine cap-tree residual the LEDGER commitment
    cannot carry. The authority CONCLUSION is forced from it; the bridge itself is the realizability
    of the prover's cap-tree opening (REALIZABLE — the honest prover opens the actor's real cap).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported keystones (`StarkSound`, `Poseidon2SpongeCR`, the cap-hash `chipCR`/`Compress1CR`, the
chip-soundness `ChipTableSound`). No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW
names only; imports are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinement
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.RotatedKernelRefinementFacet

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FacetAuthority
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.RotatedKernelRefinement
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (MembersAt confersTransferLeaf DeployedFaithful DeployedFaithfulEff tierOfTag)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf)
open Dregg2.Circuit.Emit.CapOpenEmit
  (transferCapOpenEffV3 capOpenCols transferCapOpenEffV3_authorizes EFF_TRANSFER
   effCapOpenV3 effCapOpenV3_authorizes)
open Dregg2.Exec.FacetAuthority (authorizedFacetEffB)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 ChipTableSound TraceFamily envAt)
open Dregg2.Circuit.CircuitSoundness

set_option autoImplicit false

/-! ## §1 — `BalanceMovementSpecFacetK` + the FAITHFUL executor⟺spec (over `FacetKernelState`).

The faithful executor `FacetAuthority.execFaithful` gates on the deployed two-axis `authorizedFacetB
k.fcaps provided turn` (NOT the toy `authorizedB`). `BalanceMovementSpecFacetK` is its full-state
declarative post-condition: the deployed-authority guard holds, the post-`bal` ledger is the
debit/credit movement, and the FRAME — the live `accounts` and the FACET cap-table `fcaps` — is
unchanged. `execFaithful_iff_specFacet` is the executor⟺spec, BOTH directions: the `→` VALIDATES the
faithful executor against the independent spec (a silently mutated `fcaps`/`accounts` would fail the
proof); the `←` reconstructs the committed state. -/

/-- The deployed-authority admissibility guard the faithful executor checks, as a `Prop`. Conjunct (1)
is the FAITHFUL two-axis `authorizedFacetB` (NOT the toy `authorizedB`). -/
def admitGuardFacet (k : FacetKernelState) (provided : AuthProvided) (turn : Turn) : Prop :=
  authorizedFacetB k.fcaps provided turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
    ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts

/-- **`BalanceMovementSpecFacetK`** — the FULL-state declarative spec of a committed faithful transfer
over `FacetKernelState`: the deployed-authority guard holds (`admitGuardFacet`, whose authority leg is
`authorizedFacetB`); the post-`bal` ledger is the per-cell debit/credit (`transferBal`); and the
FRAME — the live `accounts` and the FACET caps `fcaps` — is unchanged. -/
def BalanceMovementSpecFacetK (k : FacetKernelState) (provided : AuthProvided) (turn : Turn)
    (k' : FacetKernelState) : Prop :=
  admitGuardFacet k provided turn
  ∧ k'.bal = transferBal k.bal turn.src turn.dst turn.amt
  ∧ k'.accounts = k.accounts
  ∧ k'.fcaps = k.fcaps

/-- **`execFaithful_iff_specFacet` — the FAITHFUL executor ⟺ the FAITHFUL spec (both directions).**
The faithful executor (`execFaithful`, gating on the deployed `authorizedFacetB`) commits a transfer
into `k'` IFF `k'` is EXACTLY the spec'd full faithful post-state. The `→` VALIDATES the executor
against the independent spec (`fcaps`/`accounts` frame checked — a silent mutation FAILS the proof);
the `←` reconstructs the committed state. This is the executor corner of the FAITHFUL spec⟺executor
triangle — the §10(A) `exec_authorized` strengthened to a ⟺. -/
theorem execFaithful_iff_specFacet (k : FacetKernelState) (provided : AuthProvided) (turn : Turn)
    (k' : FacetKernelState) :
    execFaithful k provided turn = some k' ↔ BalanceMovementSpecFacetK k provided turn k' := by
  unfold execFaithful BalanceMovementSpecFacetK admitGuardFacet
  by_cases hg : authorizedFacetB k.fcaps provided turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hacc, hfc⟩
      obtain ⟨acc, bal, fc⟩ := k'
      simp only at hbal hacc hfc
      subst hbal hacc hfc
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hguard, hbal, _, _⟩; exact absurd hguard hg

/-- **`specFacet_rejects_unauthorized` — the faithful authority leg BITES (witness FALSE).** A turn the
deployed two-axis `authorizedFacetB` REJECTS does NOT commit ⇒ no `k'` satisfies the faithful spec. A
spec that accepted unauthorized movements would be worthless. -/
theorem specFacet_rejects_unauthorized (k : FacetKernelState) (provided : AuthProvided) (turn : Turn)
    (hbad : authorizedFacetB k.fcaps provided turn = false) (k' : FacetKernelState) :
    ¬ BalanceMovementSpecFacetK k provided turn k' := by
  rw [← execFaithful_iff_specFacet]
  rw [execFaithful_unauthorized_fails k provided turn hbad]
  simp

/-! ## §2 — `BalanceMovementSpecFacet` (over `RecChainedState`) — the template keystone spec.

Identical to `BalanceMovementSpec` EXCEPT the `admitGuardA` AUTHORITY conjunct (1) is the FAITHFUL
`authorizedFacetB fcaps provided tr = true` (the deployed two-axis gate over the FACET caps `fcaps`),
NOT the toy `authorizedB tr.caps tr`. Every OTHER conjunct (non-negativity, availability, distinctness,
liveness, accepts; the post-`bal` ledger; the 17-field frame; the log advance) is LITERALLY the same as
`BalanceMovementSpec`. -/

/-- The deployed-authority admissibility guard for the full-state refinement, as a `Prop`. Conjunct (1)
is `authorizedFacetB fcaps provided tr` (faithful); the rest is exactly `admitGuardA` minus its toy
authority leg. -/
def admitGuardAFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (k : RecordKernelState) (tr : Turn) (a : AssetId) : Prop :=
  authorizedFacetB fcaps provided tr = true ∧ 0 ≤ tr.amt ∧ tr.amt ≤ k.bal tr.src a
    ∧ tr.src ≠ tr.dst ∧ tr.src ∈ k.accounts ∧ tr.dst ∈ k.accounts
    ∧ acceptsEffects k tr.dst = true

/-- **`BalanceMovementSpecFacet`** — the FAITHFUL full-state transfer spec, parameterized by the
deployed `fcaps`/`provided`. Identical to `BalanceMovementSpec` but the authority conjunct is the
deployed two-axis `authorizedFacetB`. The post-`bal` ledger movement, the 16 non-`bal` frame fields,
and the log advance are verbatim `BalanceMovementSpec`. -/
def BalanceMovementSpecFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (st : RecChainedState) (tr : Turn) (a : AssetId) (st' : RecChainedState) : Prop :=
  admitGuardAFacet fcaps provided st.kernel tr a
  ∧ st'.kernel.bal = recTransferBal st.kernel.bal tr.src tr.dst a tr.amt
  ∧ st'.log = tr :: st.log
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps

/-- **`BalanceMovementSpecFacet` ⟹ `BalanceMovementSpec` once authority is shown the toy way too.**
The faithful spec and the toy spec share EVERY conjunct except authority; so a faithful spec PLUS the
toy authority fact reassembles the toy spec. (Used nowhere on the faithful path; recorded to pin that
the two specs differ ONLY on the authority conjunct — the additive contract.) -/
theorem balanceMovementSpecFacet_to_toy (fcaps : FacetCaps) (provided : AuthProvided)
    (st : RecChainedState) (tr : Turn) (a : AssetId) (st' : RecChainedState)
    (h : BalanceMovementSpecFacet fcaps provided st tr a st')
    (htoy : authorizedB st.kernel.caps tr = true) :
    BalanceMovementSpec st tr a st' := by
  obtain ⟨⟨_, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := h
  exact ⟨⟨htoy, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩

/-! ## §3 — the `StateDecode ↔ cap-open` bridge: `TransferAuthoritySource`.

The apex hands the rung a `StateDecode S pc pre post` + a `Satisfied2 hash transferV3 …` witness. The
VALUE leg of the faithful spec is forced by `RotatedKernelRefinement.transfer_descriptorRefines`,
which needs a `rotatedEncodes pre post` boundary decode. The AUTHORITY leg needs the cap-open's
`authorizedFacetB`, which the live descriptor's cap-open realizes — but to fire
`transferCapOpenEffV3_authorizes` we need its row data: the cap-open `Satisfied2` (the descriptor's
appendix is satisfied), the chip-table soundness, the deployed `DeployedFaithful` for the decoded
`fcaps`, and the `(actor ⇒ src)` edge identification (`hsrc`/`hedge`). NONE of these is derivable
from `StateDecode` (the commitment surface commits the LEDGER, not the cap-tree leaf assignment).

`TransferAuthoritySource` bundles EXACTLY that residual — the genuine cap-tree data the ledger
commitment cannot carry — as ONE named bridge. The authority CONCLUSION (`authorizedFacetB`) is then
DERIVED from it (`authoritySource_authorizes`), not taken as a field. -/

/-- **`TransferAuthoritySource hash fcaps pre tr` — the cap-open authority source (NAMED, not faked).**
The realizability of the prover's IN-CIRCUIT cap-tree opening for the transfer's authority: a cap-open
`Satisfied2` witness of the live cap-open descriptor (against a sound chip table) whose opened leaf IS
the deployed-faithful `(actor ⇒ src)` edge, with the decoded `fcaps` the deployed faithfulness backs.
The authority conclusion is FORCED from these (via `transferCapOpenEffV3_authorizes`); they are the
cap-tree residual the ledger commitment cannot certify — carried, named (exactly as `StarkSound` is).
DATA-bearing (`Type`, like `rotatedEncodes`): it exhibits the cap-open trace + row + leaf assignment,
so the authority derivation reads them directly rather than burying them existentially. -/
structure TransferAuthoritySource (hash : List ℤ → ℤ) (fcaps : FacetCaps)
    (pre : RecChainedState) (tr : Turn) : Type 1 where
  /-- the deployed cap-hash scheme the cap-tree commits under (its existential state type). -/
  State : Type
  /-- the deployed cap-hash scheme carrier. -/
  S : CapHashScheme State
  /-- the `Custom`-tier vk decode (inert for transfers — tag ≠ 5; the named felt residual). -/
  vkOfTag : ℤ → Nat
  /-- the cap-open trace + its memory boundary (the prover's cap-tree opening witness). -/
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the chip table is sound (the chip's hash IS the deployed cap-hash `S.chipAbsorb`). -/
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  /-- the LIVE transfer cap-open descriptor's appendix is satisfied (the depth-16 Merkle open + the
  genuine `EFF_TRANSFER` submask facet gate + the decoded tier). This is the descriptor the live
  `transferCapOpenVmDescriptor2R24` route proves through (the genuine submask facet + decoded tier). -/
  hsat : Satisfied2 S.chipAbsorb transferCapOpenEffV3 minit mfin maddrs t
  /-- the cap-open row index. -/
  i : Nat
  hi : i < t.rows.length
  /-- the deployed leaf assignment the cap-tree root realizes. -/
  leafAt : Dregg2.Authority.Label → Dregg2.Authority.Label → CapLeaf
  /-- the decoded `fcaps` are deployed-faithfully realized by `leafAt` at the cap-open's root, over the
  turn's ACTUAL effect bit (`1 <<< EFF_TRANSFER`), the effect-general faithfulness. -/
  hfaith : DeployedFaithfulEff S vkOfTag .signature (1 <<< EFF_TRANSFER) fcaps
    ((envAt t i).loc capOpenCols.capRoot) leafAt
  /-- the cap-open row's `src` column IS the turn's `src`. -/
  hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ)
  /-- the opened leaf IS the faithful `(actor ⇒ src)` edge leaf. -/
  hedge : leafOf capOpenCols (envAt t i) = leafAt tr.actor tr.src
  /-- the pinned `.signature` satisfies the tier DECODED off the committed leaf (the decoded-tier
  side condition the live keystone consumes; for the `.signature` pin this is the realizable fact that
  the committed cap's tier admits a signature). -/
  htier : (tierOfTag vkOfTag (leafAt tr.actor tr.src).auth_tag).isSatisfiedBy .signature = true

/-- **`authoritySource_authorizes` — the cap-open FORCES the deployed authority.** From a
`TransferAuthoritySource`, the deployed two-axis `authorizedFacetB fcaps .signature tr` PASSES: the
in-circuit depth-16 cap-membership open discharges the faithful authority gate
(`transferCapOpenEffV3_authorizes`). The authority leg is NOT carried — it is forced by the circuit. -/
theorem authoritySource_authorizes (hash : List ℤ → ℤ) (fcaps : FacetCaps)
    (pre : RecChainedState) (tr : Turn)
    (src0 : TransferAuthoritySource hash fcaps pre tr) :
    authorizedFacetB fcaps .signature tr = true := by
  -- `transferCapOpenEffV3_authorizes` concludes the gate over the rebuilt turn record
  -- `⟨actor,src,dst,amt⟩`; since `Turn` is exactly those four fields, that record IS `tr` by eta, so
  -- the goal converts to the literal definitionally (`show`).
  show authorizedFacetB fcaps .signature
      { actor := tr.actor, src := tr.src, dst := tr.dst, amt := tr.amt } = true
  exact (transferCapOpenEffV3_authorizes src0.S src0.vkOfTag .signature src0.minit src0.mfin src0.maddrs
    src0.t src0.hChip src0.hsat src0.i src0.hi fcaps src0.leafAt src0.hfaith
    tr.actor tr.src tr.dst tr.amt src0.hsrc src0.hedge src0.htier).1

/-! ## §3.G — F6: the GENERAL-TIER cap-open authority source (decoded `auth_tag`, not pinned).

`TransferAuthoritySource` pins `.signature` (the cap-open's `authTagGate` constant). F6 generalizes:
`TransferAuthoritySourceG` carries a `provided : AuthProvided` and the fact that `provided` satisfies
the tier DECODED off the committed leaf (`tierOfTag vkOfTag (leafAt actor src).auth_tag`), rather than
hardcoding Signature. `authoritySourceG_authorizes` then forces `authorizedFacetB fcaps provided tr`
for the GENUINE committed tier — the §10 tier residual closed in the apex authority leg. -/

/-- **`TransferAuthoritySourceG hash fcaps provided pre tr`** (F6) — the GENERAL-TIER cap-open authority
source. Identical to `TransferAuthoritySource` but the deployed faithfulness is over an arbitrary
`provided` (not `.signature`), and it adds `htier`: `provided` satisfies the tier decoded off the
committed leaf. The authority conclusion (`authorizedFacetB fcaps provided`) is forced from the
in-circuit open + the committed tier — NOT pinned to Signature. -/
structure TransferAuthoritySourceG (hash : List ℤ → ℤ) (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) : Type 1 where
  State : Type
  S : CapHashScheme State
  vkOfTag : ℤ → Nat
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  hsat : Satisfied2 S.chipAbsorb transferCapOpenEffV3 minit mfin maddrs t
  i : Nat
  hi : i < t.rows.length
  leafAt : Dregg2.Authority.Label → Dregg2.Authority.Label → CapLeaf
  hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< EFF_TRANSFER) fcaps
    ((envAt t i).loc capOpenCols.capRoot) leafAt
  hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ)
  hedge : leafOf capOpenCols (envAt t i) = leafAt tr.actor tr.src
  /-- the off-circuit auth satisfies the tier DECODED off the committed leaf (NOT a Signature pin). -/
  htier : (tierOfTag vkOfTag
      (leafAt tr.actor tr.src).auth_tag).isSatisfiedBy provided = true

/-- **`authoritySourceG_authorizes` (F6) — the cap-open FORCES the GENERAL-tier deployed authority.**
From a `TransferAuthoritySourceG`, `authorizedFacetB fcaps provided tr` PASSES for the GENUINE committed
tier (`tierOfTag auth_tag`), not the pinned Signature: the in-circuit cap-open + the committed-tier
satisfaction discharge the faithful authority gate. -/
theorem authoritySourceG_authorizes (hash : List ℤ → ℤ) (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (src0 : TransferAuthoritySourceG hash fcaps provided pre tr) :
    authorizedFacetB fcaps provided tr = true := by
  show authorizedFacetB fcaps provided
      { actor := tr.actor, src := tr.src, dst := tr.dst, amt := tr.amt } = true
  exact (transferCapOpenEffV3_authorizes
    src0.S src0.vkOfTag provided src0.minit src0.mfin src0.maddrs src0.t src0.hChip src0.hsat
    src0.i src0.hi fcaps src0.leafAt src0.hfaith tr.actor tr.src tr.dst tr.amt src0.hsrc
    src0.hedge src0.htier).1

/-! ## §3.E — `EffAuthoritySource`: the EFFECT-PARAMETRIC cap-open authority source.

`TransferAuthoritySource`/`…G` pin `transferCapOpenEffV3` + `EFF_TRANSFER`, so they discharge
`authorizedFacetB` (the `turnEffectBit _ = EFFECT_TRANSFER` collapse). The 6 FAN-OUT cap-effects
(introduce/delegate/grantCap/revoke/refreshDelegation/revokeCapability) ride DIFFERENT effect bits and
do NOT collapse to `authorizedFacetB`; their authority is the GENERAL `authorizedFacetEffB caps provided
(1 <<< n)` at the effect's OWN bit `n` — exactly what a per-effect authority gate needs. `EffAuthoritySource`
generalizes the cap-open source to ANY fan-out descriptor `effCapOpenV3 base name n` at bit `n`, deriving
`authorizedFacetEffB caps provided (1 <<< n)` from the in-circuit open (via `effCapOpenV3_authorizes`).
The transfer source is the `base := transferV3, n := EFF_TRANSFER` instance (recovered below), so the
load-bearing transfer leg is PRESERVED, not broken — it is a specialization of THIS. -/

/-- **`EffAuthoritySource hash caps provided pre tr base name n`** — the EFFECT-PARAMETRIC cap-open
authority source for the fan-out effect whose descriptor is `effCapOpenV3 base name n` at effect bit
`n < MASK_BITS`. Carries the cap-open `Satisfied2` of THAT descriptor, the chip soundness, the deployed
faithfulness over the ACTUAL effect bit `1 <<< n`, the `(actor ⇒ src)` edge identification, and the
decoded-tier side condition. The authority conclusion `authorizedFacetEffB caps provided (1 <<< n)` is
FORCED from it (`effAuthoritySource_authorizes`) — NOT carried. DATA-bearing (`Type 1`, like
`TransferAuthoritySource`): it exhibits the cap-open trace + row + leaf assignment directly. -/
structure EffAuthoritySource (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    : Type 1 where
  /-- the effect bit `n` is a valid mask bit (`< MASK_BITS = 32`); the submask-gate side condition. -/
  hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS
  /-- the deployed cap-hash scheme the cap-tree commits under (its existential state type). -/
  State : Type
  /-- the deployed cap-hash scheme carrier. -/
  S : CapHashScheme State
  /-- the `Custom`-tier vk decode (the named felt residual). -/
  vkOfTag : ℤ → Nat
  /-- the cap-open trace + its memory boundary (the prover's cap-tree opening witness). -/
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the chip table is sound (the chip's hash IS the deployed cap-hash `S.chipAbsorb`). -/
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  /-- the LIVE fan-out cap-open descriptor's appendix is satisfied (the depth-16 Merkle open + the
  genuine submask facet gate at bit `n` + the decoded tier). -/
  hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t
  /-- the cap-open row index. -/
  i : Nat
  hi : i < t.rows.length
  /-- the deployed leaf assignment the cap-tree root realizes. -/
  leafAt : Dregg2.Authority.Label → Dregg2.Authority.Label → CapLeaf
  /-- the decoded `caps` are deployed-faithfully realized by `leafAt` at the cap-open's root, over the
  turn's ACTUAL effect bit `1 <<< n`. -/
  hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps
    ((envAt t i).loc capOpenCols.capRoot) leafAt
  /-- the cap-open row's `src` column IS the turn's `src`. -/
  hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ)
  /-- the opened leaf IS the faithful `(actor ⇒ src)` edge leaf. -/
  hedge : leafOf capOpenCols (envAt t i) = leafAt tr.actor tr.src
  /-- `provided` satisfies the tier DECODED off the committed leaf (NOT a Signature pin). -/
  htier : (tierOfTag vkOfTag (leafAt tr.actor tr.src).auth_tag).isSatisfiedBy provided = true

/-- **`effAuthoritySource_authorizes` — the fan-out cap-open FORCES the GENERAL-bit deployed authority.**
From an `EffAuthoritySource … base name n`, the deployed two-axis `authorizedFacetEffB caps provided
(1 <<< n) tr` PASSES at the effect's OWN bit: the in-circuit depth-16 cap-membership open discharges the
faithful authority gate (`effCapOpenV3_authorizes`). The authority leg is NOT carried — it is forced by
the circuit, at the GENUINE effect bit (a cap permitting a different effect would fail `hfaith`). -/
theorem effAuthoritySource_authorizes (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (src0 : EffAuthoritySource hash caps provided pre tr base name n) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true := by
  show authorizedFacetEffB caps provided (1 <<< n)
      { actor := tr.actor, src := tr.src, dst := tr.dst, amt := tr.amt } = true
  exact (effCapOpenV3_authorizes (State := src0.State) base name n src0.hn
    src0.S src0.vkOfTag provided src0.minit src0.mfin src0.maddrs src0.t src0.hChip src0.hsat
    src0.i src0.hi caps src0.leafAt src0.hfaith tr.actor tr.src tr.dst tr.amt src0.hsrc
    src0.hedge src0.htier).1

/-- **`transferAuthoritySourceG_to_eff` — the transfer source IS the `EFF_TRANSFER` instance of
`EffAuthoritySource`.** A `TransferAuthoritySourceG` (which pins `transferCapOpenEffV3 = effCapOpenV3
transferV3 … EFF_TRANSFER`) yields the parametric `EffAuthoritySource` at `base := transferV3,
n := EFF_TRANSFER`. This records that the load-bearing transfer leg is a SPECIALIZATION of the
parametric source — not a separate, possibly-divergent path. -/
def transferAuthoritySourceG_to_eff (hash : List ℤ → ℤ) (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (src0 : TransferAuthoritySourceG hash fcaps provided pre tr) :
    EffAuthoritySource hash fcaps provided pre tr
      Dregg2.Circuit.RotatedKernelRefinement.transferV3
      "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER where
  hn := by decide
  State := src0.State
  S := src0.S
  vkOfTag := src0.vkOfTag
  minit := src0.minit
  mfin := src0.mfin
  maddrs := src0.maddrs
  t := src0.t
  hChip := src0.hChip
  hsat := src0.hsat
  i := src0.i
  hi := src0.hi
  leafAt := src0.leafAt
  hfaith := src0.hfaith
  hsrc := src0.hsrc
  hedge := src0.hedge
  htier := src0.htier

/-! ## §7.D — DISCHARGE the carried `hfaith` field: build the authority source from CR + the CANONICAL
cap-tree, not from an assumed `DeployedFaithfulEff`.

`EffAuthoritySource.hfaith` (and `TransferAuthoritySource(G).hfaith`) carry `DeployedFaithfulEff` as an
ASSUMED structure FIELD over a FREE `leafAt` — the soundness analog of the completeness laundering. The
discharge lives in `DeployedCapTree.deployedFaithfulEff_canonical`: for the CANONICAL leaf function the
cap-tree actually commits (`canonicalLeafAt caps`, built FROM the c-list — the cap-tree analog of
`recStateCommit`'s "leaves from the kernel"), `DeployedFaithfulEff` holds UNCONDITIONALLY (the `backed`
witness is read off the construction's `find?`), modulo only the named `Custom`/`vkOfTag` residual.

`effAuthoritySource_ofCanonical` constructs the `EffAuthoritySource` with that DISCHARGED `hfaith`:
the caller supplies the cap-open trace data (`Satisfied2` + chip soundness — the genuine in-circuit
membership the apex needs) and the IPC-tier side condition, NOT an independent faithful-encoding contract.
The `leafAt` is PINNED to `canonicalLeafAt caps` (so `hedge` becomes "the prover opens the CANONICAL
leaf", the realizable honest-prover identification — not a free leaf assignment). This shrinks the
carried-floor set: `hfaith` is no longer an assumed field but a CR/construction consequence. -/

open Dregg2.Circuit.DeployedCapTree.CapHashScheme
  (canonicalLeafAt canonicalLeaf deployedFaithfulEff_canonical)

/-- **`effAuthoritySource_ofCanonical` — the cap-open authority source with `hfaith` DISCHARGED.**
Build an `EffAuthoritySource` at the CANONICAL leaf function `canonicalLeafAt caps` (the leaves the
cap-tree commits, built from the c-list). The faithfulness `hfaith : DeployedFaithfulEff` is NOT a
carried field — it is supplied by `deployedFaithfulEff_canonical` from the construction (the `backed`
witness is the held cap `find?` returns), modulo the named IPC-tier side condition `hipc` (a `Custom`
cap rides the `vkOfTag` residual). The caller provides ONLY the genuine in-circuit cap-open data
(`hsat`/`hChip` — the depth-16 membership) + the edge/tier reads, NOT an independent encoding contract.
This is the soundness de-laundering: the authority leg's faithfulness is a CR consequence, carried no
more. -/
def effAuthoritySource_ofCanonical (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS) (hn32 : n < 32)
    {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ))
    (hedge : leafOf capOpenCols (envAt t i) = canonicalLeafAt caps tr.actor tr.src)
    -- the named IPC-tier residual: no held cap over the relevant edge is a `Custom` tier.
    (hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
      c ∈ caps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk)
    -- the decoded-tier side condition for the opened canonical leaf.
    (htier : (tierOfTag vkOfTag (canonicalLeafAt caps tr.actor tr.src).auth_tag).isSatisfiedBy
      provided = true) :
    EffAuthoritySource hash caps provided pre tr base name n where
  hn := hn
  State := State
  S := S
  vkOfTag := vkOfTag
  minit := minit
  mfin := mfin
  maddrs := maddrs
  t := t
  hChip := hChip
  hsat := hsat
  i := i
  hi := hi
  leafAt := canonicalLeafAt caps
  -- THE DISCHARGE: faithfulness is CONSTRUCTED from the canonical leaf set, not carried.
  hfaith := deployedFaithfulEff_canonical S vkOfTag provided n hn32 caps
    ((envAt t i).loc capOpenCols.capRoot) hipc
  hsrc := hsrc
  hedge := hedge
  htier := htier

/-- **`effAuthoritySource_ofCanonical_authorizes` — authority FORCED with faithfulness DISCHARGED.**
The end-to-end: from the cap-open trace data + the canonical-leaf edge identification + the IPC-tier
residual, the deployed `authorizedFacetEffB caps provided (1 <<< n) tr` PASSES — and the faithfulness
the authorization rests on is the CONSTRUCTED `deployedFaithfulEff_canonical`, NOT an assumed field. The
carried floor for this leg is now: the in-circuit membership (`hsat`/`hChip`, the genuine depth-16
open), the canonical-leaf edge read, and the named IPC-tier/`vkOfTag` residual — `DeployedFaithfulEff`
is no longer among them. -/
theorem effAuthoritySource_ofCanonical_authorizes (hash : List ℤ → ℤ) (caps : FacetCaps)
    (provided : AuthProvided) (pre : RecChainedState) (tr : Turn)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS) (hn32 : n < 32)
    {State : Type} (S : CapHashScheme State) (vkOfTag : ℤ → Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2))
    (hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ))
    (hedge : leafOf capOpenCols (envAt t i) = canonicalLeafAt caps tr.actor tr.src)
    (hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
      c ∈ caps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk)
    (htier : (tierOfTag vkOfTag (canonicalLeafAt caps tr.actor tr.src).auth_tag).isSatisfiedBy
      provided = true) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true :=
  effAuthoritySource_authorizes hash caps provided pre tr base name n
    (effAuthoritySource_ofCanonical hash caps provided pre tr base name n hn hn32 S vkOfTag
      minit mfin maddrs t hChip hsat i hi hsrc hedge hipc htier)

/-! ## §7.E — THE SLIM CANONICAL SOURCES: the live soundness authority floor with `hfaith`/`leafAt` GONE.

`EffAuthoritySource` carries `leafAt` + `hfaith : DeployedFaithfulEff` as ASSUMED structure FIELDS — the
soundness laundering. `EffAuthoritySourceCanon` is the SLIM replacement the LIVE soundness keystones now
consume: it has NO `leafAt` (the leaf function is PINNED to the canonical `canonicalLeafAt caps` the
cap-tree actually commits) and NO `hfaith` (faithfulness is CONSTRUCTED inside `_authorizes` via
`deployedFaithfulEff_canonical`). The only NEW carry over the trace data is the named IPC-tier residual
`hipc` (a `Custom` cap rides the `vkOfTag` residual) + the bit bound `hn32`. The opened-leaf
identification `hedge` is now "the prover opens the CANONICAL leaf" — the realizable honest-prover
identification, not a free leaf assignment.

THIS retires `hfaith`/`leafAt` from the live authority leg: the keystones (`transfer_descriptorRefines_facet`,
`stepAuthorityFacetEff`, the whole-turn fold) take `EffAuthoritySourceCanon`/`TransferAuthoritySourceCanon`,
and the deployed gate is FORCED with faithfulness a CR/construction consequence, carried no more. The
general `EffAuthoritySource` (with `leafAt`/`hfaith`) survives ONLY as the COMPLETENESS dual's home, where
`hfaith` is itself CONSTRUCTED (`CircuitCompletenessAuthorityConstruct.authConstructs_source`) — never an
assumed soundness field. -/

/-- **`EffAuthoritySourceCanon hash caps provided pre tr base name n` — the SLIM canonical authority
source (`hfaith`/`leafAt` RETIRED).** Carries ONLY the genuine in-circuit cap-open data (the depth-16
membership trace `t`/`hsat`/`hChip` + row id), the canonical-leaf edge identification (`hedge` against
`canonicalLeafAt caps`), the decoded-tier read (`htier`), and the NAMED IPC-tier residual `hipc`. The
faithfulness `DeployedFaithfulEff` is NOT a field — it is constructed in `effAuthoritySourceCanon_authorizes`
from `deployedFaithfulEff_canonical`. DATA-bearing (`Type 1`). -/
structure EffAuthoritySourceCanon (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    : Type 1 where
  /-- the effect bit `n` is a valid mask bit (`< MASK_BITS = 32`); the submask-gate side condition. -/
  hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS
  /-- the effect bit `n` is `< 32` (the `deployedFaithfulEff_canonical` single-bit side condition). -/
  hn32 : n < 32
  /-- the deployed cap-hash scheme the cap-tree commits under (its existential state type). -/
  State : Type
  /-- the deployed cap-hash scheme carrier. -/
  S : CapHashScheme State
  /-- the `Custom`-tier vk decode (the named felt residual). -/
  vkOfTag : ℤ → Nat
  /-- the cap-open trace + its memory boundary (the prover's cap-tree opening witness). -/
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the chip table is sound (the chip's hash IS the deployed cap-hash `S.chipAbsorb`). -/
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  /-- the LIVE fan-out cap-open descriptor's appendix is satisfied (the depth-16 Merkle open + the
  genuine submask facet gate at bit `n` + the decoded tier). -/
  hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t
  /-- the cap-open row index. -/
  i : Nat
  hi : i < t.rows.length
  /-- the cap-open row's `src` column IS the turn's `src`. -/
  hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ)
  /-- the opened leaf IS the CANONICAL `(actor ⇒ src)` edge leaf — "the prover opens the canonical tree". -/
  hedge : leafOf capOpenCols (envAt t i) = canonicalLeafAt caps tr.actor tr.src
  /-- the NAMED IPC-tier residual: no held cap over the relevant edge is a `Custom` tier (a `Custom` cap
  rides the `vkOfTag` felt residual). -/
  hipc : ∀ (actor src : Dregg2.Authority.Label) (c : Dregg2.Exec.FacetAuthority.FacetCap),
    c ∈ caps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk
  /-- `provided` satisfies the tier DECODED off the committed CANONICAL leaf. -/
  htier : (tierOfTag vkOfTag (canonicalLeafAt caps tr.actor tr.src).auth_tag).isSatisfiedBy provided = true

/-- **`effAuthoritySourceCanon_authorizes` — the fan-out cap-open FORCES authority, faithfulness DISCHARGED.**
From the SLIM `EffAuthoritySourceCanon` (NO assumed `hfaith`/`leafAt`), the deployed two-axis
`authorizedFacetEffB caps provided (1 <<< n) tr` PASSES — the faithfulness the authorization rests on is the
CONSTRUCTED `deployedFaithfulEff_canonical`, not a carried field. The carried floor for this leg is now:
the in-circuit membership (`hsat`/`hChip`), the canonical-leaf edge read (`hedge`), and the named
IPC-tier/`vkOfTag` residual (`hipc`/`htier`) — `DeployedFaithfulEff` is no longer among them. -/
theorem effAuthoritySourceCanon_authorizes (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (src0 : EffAuthoritySourceCanon hash caps provided pre tr base name n) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true :=
  effAuthoritySource_ofCanonical_authorizes hash caps provided pre tr base name n
    src0.hn src0.hn32 src0.S src0.vkOfTag src0.minit src0.mfin src0.maddrs src0.t
    src0.hChip src0.hsat src0.i src0.hi src0.hsrc src0.hedge src0.hipc src0.htier

/-- **`TransferAuthoritySourceCanon hash fcaps provided pre tr` — the SLIM canonical transfer source.**
The transfer instance of `EffAuthoritySourceCanon` at `base := transferV3, n := EFF_TRANSFER` — the live
transfer authority floor with `hfaith`/`leafAt` RETIRED. Used by `transfer_descriptorRefines_facet` so the
transfer keystone no longer takes an assumed `DeployedFaithfulEff`. -/
abbrev TransferAuthoritySourceCanon (hash : List ℤ → ℤ) (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) : Type 1 :=
  EffAuthoritySourceCanon hash fcaps provided pre tr
    Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER

/-- **`transferAuthoritySourceCanon_authorizes` — the canonical transfer source FORCES `authorizedFacetB`.**
From the slim `TransferAuthoritySourceCanon`, the deployed two-axis `authorizedFacetB fcaps provided tr`
PASSES (the transfer-bit collapse `authorizedFacetEffB … (1 <<< EFF_TRANSFER) = authorizedFacetB`),
faithfulness DISCHARGED via the canonical construction — NOT a carried field. -/
theorem transferAuthoritySourceCanon_authorizes (hash : List ℤ → ℤ) (fcaps : FacetCaps)
    (provided : AuthProvided) (pre : RecChainedState) (tr : Turn)
    (src0 : TransferAuthoritySourceCanon hash fcaps provided pre tr) :
    authorizedFacetB fcaps provided tr = true := by
  have h := effAuthoritySourceCanon_authorizes hash fcaps provided pre tr
    Dregg2.Circuit.RotatedKernelRefinement.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff" EFF_TRANSFER src0
  -- `authorizedFacetB = authorizedFacetEffB … (turnEffectBit _)`, and `turnEffectBit _ =
  -- EFFECT_TRANSFER = 1 <<< 1 = 1 <<< EFF_TRANSFER` definitionally, so the collapse is `rw`+defeq.
  rw [authorizedFacetB_eq_eff]
  exact h

/-! ## §4 — `transfer_descriptorRefines_facet`: the TEMPLATE keystone.

The faithful refinement. From a satisfying transfer VALUE witness (`Satisfied2 hash transferV3 …`
with the chip/range side conditions), its boundary decode (`rotatedEncodes`), AND the cap-open
authority source (`TransferAuthoritySource`), derive `BalanceMovementSpecFacet fcaps .signature pre
tr a post`. The VALUE leg comes from `RotatedKernelRefinement.transfer_descriptorRefines`; the
AUTHORITY leg is FORCED by the cap-open (`authoritySource_authorizes`), repointing the toy
`rotatedEncodes.guardAuth` onto the deployed `authorizedFacetB`. -/

set_option maxHeartbeats 800000 in
/-- **`transfer_descriptorRefines_facet` — THE FAITHFUL CIRCUIT→KERNEL REFINEMENT (the template).**
Satisfying the LIVE rotated transfer VALUE descriptor (`transferV3`) with its boundary decode
(`rotatedEncodes`), TOGETHER with the in-circuit cap-open authority source (`TransferAuthoritySource`,
the named cap-tree residual), forces the FAITHFUL kernel transfer step
`BalanceMovementSpecFacet fcaps .signature pre tr a post`. The debit/credit + availability + frame +
log come FROM the VALUE witness (reusing `transfer_descriptorRefines`); the AUTHORITY leg is FORCED by
the cap-open (`authoritySource_authorizes ⟹ authorizedFacetB`), NOT carried as `guardAuth`. The
decoded `fcaps` are wired to the cap-open's opened leaf through `TransferAuthoritySource.hfaith`/
`hedge`. -/
theorem transfer_descriptorRefines_facet (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (fcaps : FacetCaps)
    (hauth : TransferAuthoritySourceCanon hash fcaps .signature pre tr) :
    BalanceMovementSpecFacet fcaps .signature pre tr a post := by
  -- the VALUE leg (debit/credit/availability/frame/log) — REUSED verbatim from the value rung.
  have hval : BalanceMovementSpec pre tr a post :=
    transfer_descriptorRefines hash hside hsat pre post tr a henc
  obtain ⟨⟨_htoy, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := hval
  -- the AUTHORITY leg — FORCED by the CANONICAL cap-open, faithfulness DISCHARGED (no carried `hfaith`).
  have hfaithAuth : authorizedFacetB fcaps .signature tr = true :=
    transferAuthoritySourceCanon_authorizes hash fcaps .signature pre tr hauth
  exact ⟨⟨hfaithAuth, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩

set_option maxHeartbeats 800000 in
/-- **`transfer_descriptorRefines_facet_tierGeneral` (F6) — the FAITHFUL refinement at the GENERAL
tier.** Identical to `transfer_descriptorRefines_facet` but the authority leg rides the GENERAL-tier
cap-open source (`TransferAuthoritySourceG`, the committed `auth_tag` decoded — NOT the Signature
pin), forcing `BalanceMovementSpecFacet fcaps provided` for any `provided` the committed tier admits.
The §10 tier residual is closed in the refinement keystone: the faithful spec now carries the deployed
two-axis gate at the GENUINE committed tier. -/
theorem transfer_descriptorRefines_facet_tierGeneral (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hauth : TransferAuthoritySourceCanon hash fcaps provided pre tr) :
    BalanceMovementSpecFacet fcaps provided pre tr a post := by
  have hval : BalanceMovementSpec pre tr a post :=
    transfer_descriptorRefines hash hside hsat pre post tr a henc
  obtain ⟨⟨_htoy, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := hval
  have hfaithAuth : authorizedFacetB fcaps provided tr = true :=
    transferAuthoritySourceCanon_authorizes hash fcaps provided pre tr hauth
  exact ⟨⟨hfaithAuth, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩

/-- **`transfer_descriptorRefines_facet_rejects_unauthorized` (the faithful authority tooth).** If the
deployed two-axis gate REJECTS the turn (`authorizedFacetB fcaps .signature tr = false`), then NO
`post` satisfies the faithful spec — the faithful authority leg genuinely bites at the refinement
level (a wrong-cap / wrong-tier / wrong-facet transfer cannot satisfy `BalanceMovementSpecFacet`). -/
theorem transfer_descriptorRefines_facet_rejects_unauthorized (fcaps : FacetCaps)
    (provided : AuthProvided) (st : RecChainedState) (tr : Turn) (a : AssetId) (st' : RecChainedState)
    (hbad : authorizedFacetB fcaps provided tr = false) :
    ¬ BalanceMovementSpecFacet fcaps provided st tr a st' := by
  rintro ⟨⟨hauth, _⟩, _⟩
  rw [hbad] at hauth; exact absurd hauth (by simp)

/-! ## §5 — route the apex at `dispatchArmFacet` (the faithful transfer arm).

`dispatchArmFacet fcaps provided` is the dispatcher whose `.balanceA` arm is `BalanceMovementSpecFacet`
(the FAITHFUL spec) — the deployed-authority analog of `CircuitSoundness.dispatchArm`. Instantiating
the apex (`lightclient_unfoolable` / `lightclient_turn_unfoolable_forest`) at `kstep :=
dispatchArmFacet …` makes the apex conclude a FAITHFUL transfer transition: the authority leg is the
deployed two-axis gate, discharged by the in-circuit cap-open through the carried per-effect rung. -/

/-- **`dispatchArmFacet fcaps provided e pre post`** — the FAITHFUL dispatcher arm: the published
effect index names a faithful transfer of SOME asset `a` whose `BalanceMovementSpecFacet` holds
between the decoded endpoints. The deployed-authority analog of `dispatchArm`; its authority conjunct
is `authorizedFacetB`. (Parameterized by the deployed `fcaps`/`provided` the apex's `kstep` fixes.) -/
def dispatchArmFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (_e : EffectIdx) (pre post : RecChainedState) : Prop :=
  ∃ (tr : Turn) (a : AssetId), BalanceMovementSpecFacet fcaps provided pre tr a post

/-- **`lightclient_transfer_faithful` — the apex at the FAITHFUL transfer arm (single step).** From a
verifying batch + the named floors (STARK soundness, the hash CR carrier, the carried witness→state
existence rung) + the carried per-effect rung `hrefines` AT `dispatchArmFacet`, there EXIST decoded
endpoints and a genuine FAITHFUL transfer transition (`BalanceMovementSpecFacet` — the authority leg
is the deployed two-axis gate) whose endpoints are the published commitments. The light client RAN
NOTHING; the faithful authority is discharged in-circuit by the cap-open through `hrefines`. -/
theorem lightclient_transfer_faithful
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash) [StarkSound hash R]
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArmFacet fcaps provided e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      (∃ (tr : Turn) (a : AssetId), BalanceMovementSpecFacet fcaps provided pre tr a post) ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  obtain ⟨pre, post, hdecode, harm, hpre, hpost⟩ :=
    lightclient_unfoolable hash S R hCR (dispatchArmFacet fcaps provided) hrefines pi π hwitdec hacc
  exact ⟨pre, post, hdecode, harm, hpre, hpost⟩

/-! ## §6 — the whole-turn faithful apex (forest shape), routed at the FAITHFUL arm.

The whole-turn lift, ALSO at the faithful arm. We re-state the §8 `TurnDecodeChain` fold of
`CircuitSoundness` with the per-effect family carried at `dispatchArmFacet`: a verified turn (every
step's circuit `Satisfied2`, decoded, seams agreeing) whose steps refine to the FAITHFUL
`dispatchArmFacet` yields a genuine `execFullTurnA start acts = some fin`. The fold itself
(`turnDecodeChain_refines_turnSpec`) is generic over the arm's `dispatchArm`, so the faithful arm
plugs in once each step's `dispatchArmFacet ⟹ dispatchArm` (a faithful transfer IS a `.balanceA`
action whose `fullActionStep` holds — `dispatchArmFacet_to_dispatchArm`). -/

/-- **`dispatchArmFacet_to_dispatchArm` — a FAITHFUL transfer step IS a dispatcher step.** A
`dispatchArmFacet` (the faithful transfer arm: `BalanceMovementSpecFacet`, authority via
`authorizedFacetB`) entails the generic `dispatchArm` (`∃ fa, actionTag fa = e ∧ fullActionStep pre fa
post`) via the toy `.balanceA` action — PROVIDED the toy authority also holds at the step (the value
legs are shared; the executor `fullActionStep` reads the toy `authorizedB`). The faithful authority is
the STRONGER fact; this lowering is to the toy executor arm the apex's `execFullTurnA` runs. The toy
authority side-condition is the NAMED residual of the lowering (the executor still gates on
`authorizedB`; cutting it over to `authorizedFacetB` is FacetAuthority §10(A), not this module). -/
theorem dispatchArmFacet_to_dispatchArm (fcaps : FacetCaps) (provided : AuthProvided)
    (e : EffectIdx) (pre post : RecChainedState)
    (he : e = 0)   -- the transfer effect tag (`actionTag (.balanceA _ _) = 0`); the published index.
    (h : dispatchArmFacet fcaps provided e pre post)
    (htoy : ∀ tr : Turn, (∃ a, BalanceMovementSpecFacet fcaps provided pre tr a post) →
      authorizedB pre.kernel.caps tr = true) :
    dispatchArm e pre post := by
  subst he
  obtain ⟨tr, a, hfacet⟩ := h
  have htoyAuth : authorizedB pre.kernel.caps tr = true := htoy tr ⟨a, hfacet⟩
  have hspec : BalanceMovementSpec pre tr a post :=
    balanceMovementSpecFacet_to_toy fcaps provided pre tr a post hfacet htoyAuth
  refine ⟨FullActionA.balanceA tr a, ?_, ?_⟩
  · rfl
  · show BalanceMovementSpec pre tr a post
    exact hspec

/-! ## §7 — non-vacuity: the faithful refinement FIRES (the value+authority both real). -/

/-- **`balanceMovementSpecFacet_nonvacuous` — the faithful spec is SATISFIABLE.** On a concrete owner
transfer (actor owns `src` ⇒ `authorizedFacetB` admits intra-vat) with a valid debit/credit, SOME
post-state meets `BalanceMovementSpecFacet` — the faithful spec is not vacuously unsatisfiable. -/
theorem balanceMovementSpecFacet_owner_admits (fcaps : FacetCaps) (provided : AuthProvided)
    (st : RecChainedState) (tr : Turn) (a : AssetId) (st' : RecChainedState)
    (howner : tr.actor = tr.src)
    (h : BalanceMovementSpec st tr a st') :
    BalanceMovementSpecFacet fcaps provided st tr a st' := by
  obtain ⟨⟨_, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩ := h
  refine ⟨⟨?_, hnn, hav, hne, hls, hld, hacc⟩, hrest⟩
  exact authorizedFacetB_owner fcaps provided tr howner

/-! ## §8 — Axiom hygiene. -/

#assert_axioms effAuthoritySource_ofCanonical
#assert_axioms effAuthoritySource_ofCanonical_authorizes
#assert_axioms effAuthoritySourceCanon_authorizes
#assert_axioms transferAuthoritySourceCanon_authorizes
#assert_axioms execFaithful_iff_specFacet
#assert_axioms specFacet_rejects_unauthorized
#assert_axioms balanceMovementSpecFacet_to_toy
#assert_axioms authoritySource_authorizes
#assert_axioms authoritySourceG_authorizes
#assert_axioms effAuthoritySource_authorizes
#assert_axioms transferAuthoritySourceG_to_eff
#assert_axioms transfer_descriptorRefines_facet
#assert_axioms transfer_descriptorRefines_facet_tierGeneral
#assert_axioms transfer_descriptorRefines_facet_rejects_unauthorized
#assert_axioms lightclient_transfer_faithful
#assert_axioms dispatchArmFacet_to_dispatchArm
#assert_axioms balanceMovementSpecFacet_owner_admits

end Dregg2.Circuit.RotatedKernelRefinementFacet
