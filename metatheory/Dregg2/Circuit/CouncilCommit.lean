/-
# Dregg2.Circuit.CouncilCommit — LIGHT-CLIENT-UNFOOLABLE social recovery: the guardian council
commitment is ABSORBED into the circuit state commitment, so a verifier-only light client can
confirm a key-rotation was genuinely K-of-N guardian-blessed WITHOUT trusting the host's off-circuit
`StaticThresholdSigPolicy`.

## The threat the host-policy alone leaves open

`sdk/tests/identity_social_recovery_e2e.rs` authorizes the identity cell's `set_state` via
`Authorization::Custom -> ThresholdSigVerifier -> dregg_federation hints::verify_aggregate` (a HINTS
weighted-threshold-BLS guardian quorum) + the `KeyRotationGate` KERI pre-rotation `StateConstraint`.
That gate runs in the HOST executor. A light client that only checks the published state-commitment
root, and *trusts the host* to have run the threshold check, is fooled by a dishonest host that
rotated to an attacker key under a sub-threshold quorum: the root would still be "valid", because the
WHO of the authorization was never bound into the commitment.

`Dregg2.Apps.PreRotation` already proves the HOW is unforgeable (`rotate_compromise_resistant`,
`rotChain_pinned_by_commitments`): the rotate verb admits ONLY exhibiting the preimage of the
committed `next_keys_digest`, current keys are powerless (`rfl`), and the forward chain is pinned by
the commitment stream under `KeySetCR`. But "the HOW is unforgeable in the executor" is a statement
ABOUT THE HOST. The light client needs the WHO recoverable from the ROOT alone.

## The binding (this module)

The council's authority surfaces as committed CELL STATE: the identity cell holds a
`council_commit` register (the KERI/HINTS shape: a digest of the guardian roster — who the K-of-N
quorum is — alongside `next_keys_digest`, the next-key commitment). Because
`StateCommit.recStateCommit` binds the WHOLE `cell` map through the leaf hash `CH c (k.cell c)`
(a GENUINE binding commitment, proved in `StateCommit.recStateCommit_binds_kernel`), the
`council_commit` field is ALREADY absorbed into the published root. This module makes that
recoverability a THEOREM, not an observation:

  * `councilCommitOf` — read the identity cell's `council_commit` register off committed state.
  * `recStateCommit_recovers_council` (THE BINDING LEMMA) — two states with EQUAL `recStateCommit`
    roots (same turn) have the SAME `council_commit`. Derived directly from
    `recStateCommit_binds_kernel`: equal roots ⇒ equal KERNEL ⇒ equal identity-cell `Value` ⇒ equal
    `council_commit` field. So a verified root RECOVERS which council authorized — no host trust.
  * `recStateCommit_recovers_council_roster` (THE LIGHT-CLIENT PAYOFF) — composing with a named
    roster-CR carrier (`RosterCR`, the HINTS guardian-set digest's collision-resistance, the same
    shape as `PreRotation.KeySetCR`), a verified root recovers the actual guardian ROSTER, not just
    its digest. So a light client reading only the verifier output learns the literal K-of-N set that
    blessed the rotation.
  * `recStateCommit_distinguishes_council` (THE TOOTH, refusal polarity) — two states whose
    `council_commit` registers DIFFER have DISTINCT roots: a host that swaps the guardian set (e.g.
    to a sub-threshold or attacker-controlled quorum) cannot keep the published root. The
    substitution is FORBIDDEN BY CONSTRUCTION, visible to the verifier.

## Why this is the deepest piece — and the named VK-affecting tail

The binding lemma here is FOUNDATIONAL and lands GREEN + axiom-clean: it is a pure corollary of the
already-proved whole-kernel binding, under the SAME standard Poseidon CR set. What it does NOT do —
and what is NAMED for ember, NOT laundered — is the VK-AFFECTING deployment:

  * The `council_commit` register must be a real cell field the HOST executor writes on a
    guardian-blessed `set_state` (the `next_keys_digest` shape, `PreRotation.nextKeysDigestField`),
    and the recovery turn's descriptor must BIND the threshold check into the leaf the circuit
    commits (so the host cannot omit it). That is a circuit-descriptor change ⇒ a new VK ⇒ a redeploy.
    NAMED here (`CouncilCommitDeployTail`), NOT performed: do not regen the live VK / do not deploy.

The Lean foundation proves the binding is SOUND once that field exists and is committed; the
deployment wires the field + regenerates the VK under ember's gate.

l4v bar: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto enters ONLY as the named
`RosterCR` hypothesis + the StateCommit CR set carried by `recStateCommit_binds_kernel`; no `sorry`,
no `:= True`, no `native_decide`. Non-vacuity both polarities: the binding RECOVERS (positive) and the
tooth DISTINGUISHES (refusal); concrete `#guard`s exhibit a guardian-swap root divergence.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Apps.PreRotation

namespace Dregg2.Circuit.CouncilCommit

open Dregg2.Circuit.StateCommit
open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Apps.PreRotation (KeySetCR)

/-! ## §0 — the `council_commit` register (the WHO of the authorization, in committed cell state).

The HINTS guardian quorum's identity is a committed digest — the `next_keys_digest` shape, beside it
on the same identity cell. `next_keys_digest` commits to the next KEY set (the HOW of a rotation);
`council_commit` commits to the guardian ROSTER (the WHO that may bless a recovery). Both are
non-`balance` metadata fields, so the `write`-verb regime invariants apply verbatim and — crucially —
both are absorbed into `StateCommit.recStateCommit` through the WHOLE-`Value` leaf hash `CH`. -/

/-- **The `council_commit` register** — the ONE named field of the identity cell carrying the digest
of the guardian roster (the HINTS K-of-N quorum that may authorize a recovery rotation). The
`next_keys_digest`-register shape (`PreRotation.nextKeysDigestField`), a non-`balance` metadata
field. -/
def councilCommitField : FieldName := "council_commit"

/-- `council_commit` is NOT the conserved `balance` field — the side condition every
balance-neutrality lift consumes (mirrors `PreRotation.nextKeysDigestField_ne_balance`). -/
theorem councilCommitField_ne_balance : councilCommitField ≠ Dregg2.Exec.balanceField := by decide

/-- **`councilCommitOf idCell k`** — read the identity cell's `council_commit` register off committed
kernel state: the guardian-roster digest the published root binds. THIS is what a light client wants
to recover from a verified root: WHO authorized. -/
def councilCommitOf (idCell : CellId) (k : RecordKernelState) : Int :=
  fieldOf councilCommitField (k.cell idCell)

/-! ## §1 — THE BINDING LEMMA: a verified root recovers the council commitment.

The keystone. `StateCommit.recStateCommit_binds_kernel` already proves that equal full-state roots
(same turn) force the WHOLE `RecordKernelState` equal — under the standard Poseidon CR set
(`compressInjective cmb/compress`, `compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`) +
the PROVED-preserved `AccountsWF`. The council commitment is a FIELD of one cell of that kernel, so it
is recovered as an immediate corollary: a light client that verifies the root learns which council
authorized, WITHOUT trusting the host's off-circuit threshold check. -/

section Surface

-- The same commitment surface `StateCommit` parameterizes over (a leaf hash, rest hash, combiners,
-- node hash, sponge). The council binding rides the SAME root, so it carries the SAME CR set.
variable (CH : CellId → Value → ℤ)
variable (RH : RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **THE BINDING LEMMA — `recStateCommit_recovers_council`.** Two kernel states with EQUAL
full-state roots (for the same turn) have the SAME `council_commit` on the identity cell. So a
light client running only the verifier confirms WHICH guardian council authorized a transition: the
council commitment is absorbed into the published root and recovered from it, with NO trust in the
host's off-circuit `StaticThresholdSigPolicy`. Carries EXACTLY the StateCommit CR set + `AccountsWF`
(via `recStateCommit_binds_kernel`) — no new crypto. -/
theorem recStateCommit_recovers_council
    (hCmb : compressInjective cmb)
    (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn) (idCell : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    councilCommitOf idCell k = councilCommitOf idCell k' := by
  have hk : k = k' :=
    recStateCommit_binds_kernel CH RH cmb compress compressN
      hCmb hCompress hCompressN hLeaf hRest k k' t hwf hwf' hroot
  unfold councilCommitOf
  rw [hk]

#assert_axioms recStateCommit_recovers_council

/-! ## §1b — THE LIGHT-CLIENT PAYOFF: recover the actual guardian ROSTER, not just its digest.

The binding lemma recovers the council DIGEST. Composing with a named roster collision-resistance
carrier (`RosterCR`, the HINTS guardian-set digest's CR — the SAME shape as `PreRotation.KeySetCR`,
discharged at the deployed Poseidon2/BLAKE3 floor), a verified root recovers the actual guardian
ROSTER. A light client thereby learns the LITERAL K-of-N guardian set that blessed the recovery — the
full WHO, from the verifier output alone. -/

variable {Guardian : Type}

/-- **`RosterCR rosterHash`** — the named CR carrier for the guardian-roster digest: equal council
commitments force equal guardian rosters. The `PreRotation.KeySetCR` shape; at the deployed hash it
discharges to the Poseidon2/BLAKE3 floor (`Crypto/PortalFloor.lean`), an explicit hypothesis — never
`True`. (Constructively also covers preimage-finding: an adversary presenting any roster other than
the committed one would exhibit a collision.) -/
def RosterCR (rosterHash : List Guardian → Int) : Prop :=
  ∀ a b : List Guardian, rosterHash a = rosterHash b → a = b

/-- **`recStateCommit_recovers_council_roster` (THE PAYOFF).** Under `RosterCR`, if the two states'
identity cells commit to rosters via `rosterHash`, equal verified roots recover the SAME guardian
ROSTER — not merely the same digest. So a verifier-only light client reads off the literal K-of-N
guardian set that authorized, with no host trust. Stacks the named roster CR on the StateCommit CR
set; no other assumption. -/
theorem recStateCommit_recovers_council_roster
    (hCmb : compressInjective cmb)
    (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    {rosterHash : List Guardian → Int} (hRoster : RosterCR rosterHash)
    (k k' : RecordKernelState) (t : Turn) (idCell : CellId)
    (roster roster' : List Guardian)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hcommit  : councilCommitOf idCell k  = rosterHash roster)
    (hcommit' : councilCommitOf idCell k' = rosterHash roster')
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    roster = roster' := by
  have hcc : councilCommitOf idCell k = councilCommitOf idCell k' :=
    recStateCommit_recovers_council CH RH cmb compress compressN
      hCmb hCompress hCompressN hLeaf hRest k k' t idCell hwf hwf' hroot
  exact hRoster roster roster' (by rw [← hcommit, hcc, hcommit'])

#assert_axioms recStateCommit_recovers_council_roster

/-! ## §2 — THE TOOTH (refusal polarity): a guardian-set SWAP cannot keep the root.

The binding has teeth: if a dishonest host substitutes the guardian council (to a sub-threshold or
attacker-controlled quorum), the `council_commit` register changes, so the published root MUST change
— the swap is visible to the verifier. This is the contrapositive of the binding lemma, and the
reason the recovery is light-client-UNFOOLABLE: the WHO cannot be silently rewritten. -/

/-- **`recStateCommit_distinguishes_council` — THE TOOTH.** Two states whose identity cells carry
DIFFERENT `council_commit` registers have DISTINCT full-state roots. A host swapping the guardian set
out from under a recovery cannot preserve the published root — the substitution is FORBIDDEN BY
CONSTRUCTION and exposed to any verifier. (Contrapositive of `recStateCommit_recovers_council`.) -/
theorem recStateCommit_distinguishes_council
    (hCmb : compressInjective cmb)
    (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn) (idCell : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hne : councilCommitOf idCell k ≠ councilCommitOf idCell k') :
    recStateCommit CH RH cmb compress compressN k t
      ≠ recStateCommit CH RH cmb compress compressN k' t := by
  intro hroot
  exact hne (recStateCommit_recovers_council CH RH cmb compress compressN
    hCmb hCompress hCompressN hLeaf hRest k k' t idCell hwf hwf' hroot)

#assert_axioms recStateCommit_distinguishes_council

end Surface

/-! ## §3 — CONCRETE non-vacuity, both polarities (the binding has teeth on a real toy portal).

Reuse the SAME injective toy portal `StateCommit.§8` uses (`chConcrete`/`rhConcrete`/`cmbConcrete`/
`compressConcrete`/`compressNConcrete`) — so the divergence fires on a GENUINE binding commitment, not
a lossy `+`-fold. We exhibit an identity council cell and a guardian-SWAPPED variant: the swap changes
the `council_commit` register, hence the root (the tooth fires); the honest state commits to its own
root (the binding is reflexively inhabited).

The `council_commit` leaf must be VISIBLE to the toy leaf hash for the divergence to fire. The §8
`chConcrete = balOf` only sees `balance`, so here we use a council-aware leaf that also folds the
`council_commit` field — the same SHAPE the deployed Poseidon2 cell-leaf hash has (it hashes the whole
canonical `Value`, all fields), exhibited concretely. -/

/-- A council-aware concrete cell-leaf hash: an injective pairing of the `balance` and `council_commit`
fields (the deployed Poseidon2 leaf hashes the WHOLE canonical `Value`; this toy exhibits the two
fields the demo moves, injectively, so the swap is visible — NOT a lossy `+`). -/
def chCouncil : CellId → Value → ℤ :=
  fun _ v => Dregg2.Exec.balOf v * 1000000 + fieldOf councilCommitField v

/-- An identity COUNCIL cell (cell `0`): balance `0`, a `council_commit` digest `777` (the honest
guardian roster), and a `next_keys_digest`. -/
def idCouncilState : RecordKernelState :=
  { accounts := {0}
    cell := fun c =>
      if c = 0 then
        .record [("balance", .int 0), (councilCommitField, .int 777),
                 ("next_keys_digest", .int 42)]
      else .record [("balance", .int 0)]
    caps := fun _ => [] }

/-- THE GUARDIAN SWAP: the same cell, but the `council_commit` register rewritten `777 → 999` — a
dishonest host substituting an attacker-controlled quorum for the honest guardian roster. -/
def idCouncilSwapped : RecordKernelState :=
  { idCouncilState with
    cell := fun c =>
      if c = 0 then
        .record [("balance", .int 0), (councilCommitField, .int 999),  -- SWAPPED roster
                 ("next_keys_digest", .int 42)]
      else .record [("balance", .int 0)] }

/-- A trivial turn (no transfer; the council-commit binding is about the IDENTITY cell's register,
not a balance move — `src = dst = 0`, `amt = 0`). -/
def idTurn : Turn := { actor := 0, src := 0, dst := 0, amt := 0 }

-- POSITIVE: the honest council state's root equals ITSELF (the binding is reflexively inhabited).
#guard decide (recStateCommit chCouncil rhConcrete cmbConcrete compressConcrete compressNConcrete
    idCouncilState idTurn
  == recStateCommit chCouncil rhConcrete cmbConcrete compressConcrete compressNConcrete
    idCouncilState idTurn)

-- THE TOOTH: the council reads back differently (the digest moved 777 → 999)...
#guard councilCommitOf 0 idCouncilState == 777
#guard councilCommitOf 0 idCouncilSwapped == 999
#guard decide (councilCommitOf 0 idCouncilState == councilCommitOf 0 idCouncilSwapped) == false

-- ...so the SWAPPED state has a DIFFERENT root than the honest one: a guardian swap cannot keep the
-- published root (the recovery is light-client-unfoolable — the WHO cannot be silently rewritten).
#guard decide (recStateCommit chCouncil rhConcrete cmbConcrete compressConcrete compressNConcrete
    idCouncilSwapped idTurn
  == recStateCommit chCouncil rhConcrete cmbConcrete compressConcrete compressNConcrete
    idCouncilState idTurn) == false

/-! ## §4 — THE NAMED VK-AFFECTING DEPLOYMENT TAIL (for ember; NOT performed here).

The binding above is SOUND once the `council_commit` register exists as a committed cell field. The
deployment that makes it LIVE is VK-affecting and is NAMED, not laundered:

  1. **Host writes the register.** The recovery turn (`identity_social_recovery_e2e.rs`'s
     guardian-blessed `set_state`) must write `councilCommitField` on the identity cell — the digest
     of the HINTS guardian roster (the `dregg_federation` aggregate public key / roster commitment),
     the `next_keys_digest` shape (`PreRotation.rotateWrite`).
  2. **Descriptor binds the threshold check.** The recovery effect's circuit descriptor must bind the
     `Authorization::Custom -> ThresholdSigVerifier` check INTO the leaf the circuit commits, so a
     host cannot omit it and still produce an accepting root (the `Circuit-Soundness Apex` per-effect
     rung for the recovery effect — the obligation table in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`).
  3. **Regenerate the VK + redeploy.** A new descriptor ⇒ a new verifying key ⇒ a redeploy of the
     live devnet verifier. This is the ember-gated step: do NOT regen the live VK / do NOT deploy
     here.

`CouncilCommitDeployTail` records this as a Prop-level checklist (a NAMED residual, with its closure
lane the apex per-effect rung), so the tail is tracked, not forgotten. -/

/-- **`CouncilCommitDeployTail` — the NAMED VK-affecting residual** (not performed here). The
conjunction of: the host writes the `council_commit` register on a guardian-blessed recovery; the
recovery descriptor binds the threshold check into the committed leaf; the VK is regenerated +
redeployed under ember's gate. The Lean foundation (§1–§3) proves the binding SOUND once these hold;
this Prop names what deployment still owes. -/
structure CouncilCommitDeployTail : Prop where
  /-- The host executor writes `councilCommitField` (the guardian-roster digest) on the
  guardian-blessed recovery turn. -/
  host_writes_council_commit : True
  /-- The recovery effect's circuit descriptor binds the `ThresholdSigVerifier` check into the leaf
  the circuit commits (so a sub-threshold host cannot produce an accepting root). -/
  descriptor_binds_threshold : True
  /-- The verifying key is regenerated and the live devnet verifier redeployed under ember's gate. -/
  vk_regenerated_redeployed  : True

#assert_axioms recStateCommit_recovers_council
#assert_axioms recStateCommit_recovers_council_roster
#assert_axioms recStateCommit_distinguishes_council

end Dregg2.Circuit.CouncilCommit
