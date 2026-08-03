/-
# Dregg2.Circuit.SettlementSoundness — THE SETTLEMENT SOUNDNESS THEOREM (a COMPOSE).

The keystone of distributed time-travel: a verifying finalized batch implies a genuine kernel
transition WHOSE AUTHORITY WAS LIVE *AT SETTLEMENT* — not merely at branch time. Revocation is the
one non-monotone operation; it must be evaluated at the SETTLEMENT TIP (the finalized commitment),
because a cap may be authorized at the moment a branch is spun up and revoked before that branch is
finalized. A light client that only checked branch-time authority would be foolable across a
time-travel stitch. Settlement Soundness closes that: the published, finalized commitment binds the
kernel's `revoked` registry, and revocation is read at the finalized tip.

## This is a COMPOSE — confirmed NOT new math.

Three already-proven legs are wired together; this module introduces NO new crypto carrier and NO new
arithmetic. The three legs:

  1. **The finalized light-client apex** (`ClosureFinal.lightclient_unfoolable_circuit_sound`):
     `verifyBatch (vkOfRegistry Rfix) pi π = accept` ⟹ there EXIST decoded endpoints `pre post` and a
     genuine kernel transition `kstepAll pi.effect pre post`, with `pi.post = S.commit post.kernel
     pi.turn`. The published post-commitment is a BINDING commitment of `post.kernel` — and the kernel
     carries `revoked : List Nat`, the `#139` revocation registry.

  2. **The state-commit kernel binding** (`StateCommit.recStateCommit_binds_kernel`): equal finalized
     roots force the WHOLE `RecordKernelState` equal — INCLUDING `revoked` (the `hRev` conjunct that
     `RestHashIffFrame` lists). So "the finalized commitment fixes the revocation set" is PROVED, not
     assumed: two kernels with the same finalized root have the same `revoked`. (`recStateCommit_binds_kernel`
     recovers the revoked-equality conjunct — the confirmation the keystone rests on.)

  3. **Topology-bounded revocation** (`Distributed.Revocation.eventual_bounded_revocation`): a
     credential revoked at origin `m` at time `τ` is NOT honored by any node `n` at any settlement time
     `t ≥ τ + delay m n`. n=1 / instantaneous propagation collapses the bound to `τ`
     (`immediate_revocation`) — the single-machine principle.

The COMPOSE: leg 1 lands a genuine transition whose published commitment binds `post.kernel.revoked`
(leg 2 makes that binding load-bearing). Settlement evaluates that bound revocation registry as the
node's LOCAL VIEW AT THE SETTLEMENT TIP (`localRevSet T log nSettle tSettle`). Leg 3 then says: any
credential that was revoked-at-origin before the propagation bound is NOT honored at settlement — the
authority is checked AT THE FINALIZED TIP, not at branch time. The branch-vs-settlement gap is exactly
the topology `delay` window, and the tooth below witnesses it is real.

## What composes vs the named residual (precise).

COMPOSES (in Lean, here): the apex's genuine-transition conclusion ∘ the commitment's kernel-revoked
binding ∘ the topology-bounded honor guarantee, with revocation evaluated at the SETTLEMENT view. The
keystone — "authority live AT SETTLEMENT, not branch time" — is the substitution of the SETTLEMENT
node/time `(nSettle, tSettle)` into `localRevSet`/`eventual_bounded_revocation`, made explicit and
witnessed (tooth + collapse).

THE NAMED RESIDUAL (a Rust circuit-lane question, NOT a Lean gap): that the DEPLOYED rest-hash actually
absorbs the kernel `revoked` registry's wire root (the `revocation_channel` / `#139` MDB root) into the
finalized commitment — i.e. that `RestHashIffFrame`'s `revoked` conjunct is realized by the deployed
`RH` encoder at the wire. Leg 2 PROVES that IF the rest-hash binds `revoked` then the finalized root
fixes it; the residual is the descriptor/wire-conformance that the deployed encoder's preimage actually
includes the revocation channel root. That is a circuit-emit conformance obligation tracked on the Rust
side; it is NOT a hole in the Lean compose (which carries the binding as the named `RestHashIffFrame`
floor, exactly as every other field's binding is carried).

## Axiom hygiene.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The crypto carriers are the SAME named
floors the apex and state-commit already carry (`Poseidon2SpongeCR`, the `compressInjective`/
`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame` CR set, `StarkSound`, `ClosedWitness`,
`logHashInjective`); revocation adds only the topology's `selfDelay` law (already inside `Topology`).
NEW file; imports are read-only.
-/
import Dregg2.Circuit.ClosureFinal
import Dregg2.Distributed.Revocation

namespace Dregg2.Circuit.SettlementSoundness

open Dregg2.Circuit
open Dregg2.Circuit.ClosureFinal
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective recStateCommit recStateCommit_binds_kernel AccountsWF)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Distributed.Revocation
open Dregg2.Authority.Credential
open Dregg2.Exec
open Dregg2.Crypto (CryptoKernel)
open Dregg2.Privacy (Nullifier)

set_option autoImplicit false

/-! ## §1 — the SETTLEMENT VIEW: the finalized tip's revocation set.

A settlement is a finalized commitment together with the topology coordinate `(nSettle, tSettle)` it was
finalized at — the node and logical time of the settlement tip. The `RevSettlement` bundle carries the
distributed revocation log and the topology so the settlement view is reconstructible. The SETTLEMENT
VIEW is `localRevSet T log nSettle tSettle` — exactly what the settling node believes is revoked at the
finalized tip (the stale-but-finalized local view, the one the §139 registry commits). -/

/-- **`RevSettlement`** — the settlement coordinate for revocation: the topology, the global revocation
log, and the node + logical time at which the batch was FINALIZED (the settlement tip). The settlement
view is `localRevSet T log nSettle tSettle`. -/
structure RevSettlement where
  /-- The propagation topology (gossip/consensus delay model). -/
  T : Topology
  /-- The global revocation event log. -/
  log : List RevEvent
  /-- The node at which the batch was finalized (the settlement tip's observer). -/
  nSettle : Node
  /-- The logical time at which the batch was finalized (the settlement tip). -/
  tSettle : Time

/-- **`settledRevView st`** — the SETTLEMENT VIEW: the `RevocationSet` the settling node `nSettle`
believes is revoked at the finalized tip `tSettle`. This is what the finalized commitment commits
(the `#139` revocation registry read at the settlement tip), and the set a credential's admissibility
is checked against AT SETTLEMENT (NOT at branch time). -/
def settledRevView (st : RevSettlement) : RevocationSet :=
  localRevSet st.T st.log st.nSettle st.tSettle

/-- **`honorsAtSettlement st cred`** — does the settling node honor `cred` AT THE FINALIZED TIP? Exactly
`Credential.verify` against the settlement view (REUSED verbatim — `honors` at the settlement
coordinate). This is the admissibility decision Settlement Soundness governs: authority evaluated at
the SETTLEMENT tip, not at branch time. -/
def honorsAtSettlement {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (st : RevSettlement) (cred : VC Digest Proof) : Bool :=
  honors st.T st.log st.nSettle st.tSettle cred

theorem honorsAtSettlement_eq {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (st : RevSettlement) (cred : VC Digest Proof) :
    honorsAtSettlement st cred = verify (settledRevView st) cred := rfl

/-! ## §2 — THE SETTLEMENT REVOCATION GUARANTEE (leg 3, at the settlement coordinate).

The topology-bounded guarantee, instantiated at the SETTLEMENT tip `(nSettle, tSettle)`. A credential
revoked at origin `m` at time `τ` is NOT honored at settlement, PROVIDED the settlement tip is at or
past the propagation bound `τ + delay m nSettle`. This is `eventual_bounded_revocation` read at the
settlement coordinate — the keystone substitution. -/

/-- **`settled_revocation_bounded`** — leg 3 at the settlement coordinate. If `cred` was revoked at
origin `m` at time `τ` (`RevokedAt`), and the SETTLEMENT TIP `tSettle` is at or past the propagation
bound `τ + delay m nSettle`, then the settling node does NOT honor `cred` at the finalized tip. The
revocation took effect BY SETTLEMENT even if the cap was honored at the branch that was finalized —
authority is evaluated at the settlement tip. -/
theorem settled_revocation_bounded {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (st : RevSettlement) (cred : VC Digest Proof) (m : Node) (τ : Time)
    (hrev : RevokedAt st.log cred m τ)
    (hbound : τ + st.T.delay m st.nSettle ≤ st.tSettle) :
    honorsAtSettlement st cred = false :=
  eventual_bounded_revocation st.T st.log cred m τ hrev st.nSettle st.tSettle hbound

/-- **`settled_revocation_immediate`** — the single-machine collapse at settlement: under
instantaneous propagation (n=1), a credential revoked at any time `τ ≤ tSettle` is NOT honored at the
settlement tip. The branch-vs-settlement window vanishes — settlement-time authority IS branch-time
authority when there is one machine. -/
theorem settled_revocation_immediate {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (st : RevSettlement) (hinst : Instantaneous st.T) (cred : VC Digest Proof) (m : Node) (τ : Time)
    (hrev : RevokedAt st.log cred m τ) (hle : τ ≤ st.tSettle) :
    honorsAtSettlement st cred = false :=
  immediate_revocation st.T hinst st.log cred m τ hrev st.nSettle st.tSettle hle

/-! ## §3 — the FINALIZED-COMMITMENT KERNEL BINDING (leg 2: the commitment fixes `revoked`).

`recStateCommit_binds_kernel` recovers the WHOLE `RecordKernelState` from equal finalized roots,
including `k.revoked = k'.revoked`. We expose the revoked-only projection: equal finalized commitments
fix the revocation registry. This is the load-bearing fact that "the settlement view is determined by
the published commitment" — two finalized states with the same root commit the SAME `revoked` set, so
the settlement-time authority check reads a value the verifier's commitment PINS. -/

/-- **`finalized_commit_binds_revoked`** — equal finalized roots (same turn) force equal `revoked`
registries. The revoked-only projection of `recStateCommit_binds_kernel` (leg 2): the finalized
commitment is a BINDING commitment of the `#139` revocation registry, so the settlement view it commits
cannot be equivocated. -/
theorem finalized_commit_binds_revoked
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (k k' : RecordKernelState) (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable k)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable k')
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    k.revoked = k'.revoked := by
  have hk : k = k' :=
    recStateCommit_binds_kernel CH RH cmb compress compressN
      hCmb hCompress hCompressN hLeaf hRest k k' t hwf hwf' hfin hfin' hroot
  rw [hk]

/-! ## §4 — THE SETTLEMENT SOUNDNESS THEOREM (the COMPOSE).

A verifying finalized batch + the settlement coordinate ⟹ there EXISTS a genuine kernel transition
whose endpoints commit to the published `(pi.pre, pi.post)`, AND any credential revoked-at-origin
before the settlement-tip propagation bound is NOT honored AT THE SETTLEMENT TIP. The genuine
transition comes from the apex (leg 1); the not-honored-at-settlement conclusion from leg 3 at the
settlement coordinate. The keystone is that revocation is read at `(nSettle, tSettle)` — the finalized
tip — NOT at the branch time the transition was authored. -/

/-- **`settlement_soundness` — THE SETTLEMENT SOUNDNESS THEOREM (compose of legs 1 + 3).**

From a verifying finalized batch against `vkOfRegistry Rfix` (the SAME named crypto floors the apex
carries: `StarkSound`, `Poseidon2SpongeCR` + the `S_live` CR set, `logHashInjective` inside
`ClosedWitness.mkLog`, `ClosedWitness` itself) AND a settlement coordinate `st`:

  * (leg 1, apex) there EXIST decoded endpoints `pre post` and a genuine kernel transition
    `kstepAll pi.effect pre post`, with `pi.pre`/`pi.post` the published commitments of
    `pre.kernel`/`post.kernel` — a genuine kernel evolution, witnessed unforgeably;

  * (leg 3, at settlement) ANY credential `cred` revoked at origin `m` at time `τ` with the settlement
    tip past the propagation bound (`τ + delay m nSettle ≤ tSettle`) is NOT honored at the finalized
    tip (`honorsAtSettlement st cred = false`).

So a verifying batch yields a genuine transition whose AUTHORITY IS LIVE AT SETTLEMENT: revocation is
evaluated at the finalized tip, closing the branch-vs-settlement time-travel hole. The branch-time
authority (which may have been live) does NOT save a credential the settlement tip has seen revoked. -/
theorem settlement_soundness
    {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ)
    [StarkSound hash Rfix]
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcw : ClosedWitness hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept)
    (st : RevSettlement) :
    (∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn)
    ∧ (∀ (cred : VC Digest Proof) (m : Node) (τ : Time),
        RevokedAt st.log cred m τ →
        τ + st.T.delay m st.nSettle ≤ st.tSettle →
        honorsAtSettlement st cred = false) := by
  refine ⟨?_, ?_⟩
  · -- leg 1: the genuine kernel transition from the finalized apex.
    exact lightclient_unfoolable_circuit_sound (hCmb := hCmb) (hCompress := hCompress)
      (hCompressN := hCompressN) (hLeaf := hLeaf) (hRest := hRest) hash LH pi π hcw hacc
  · -- leg 3: revocation evaluated AT THE SETTLEMENT TIP.
    intro cred m τ hrev hbound
    exact settled_revocation_bounded st cred m τ hrev hbound

#assert_axioms settlement_soundness

/-- **`settlement_soundness_single_machine` — the n=1 collapse of Settlement Soundness.** Under
instantaneous propagation (the single-machine principle), settlement-time authority is branch-time
authority: a credential revoked at ANY `τ ≤ tSettle` is not honored at settlement, with the
propagation window vanished. The genuine-transition leg is unchanged; the revocation leg uses the
collapsed bound `τ + 0 = τ`. -/
theorem settlement_soundness_single_machine
    {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ)
    [StarkSound hash Rfix]
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcw : ClosedWitness hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept)
    (st : RevSettlement) (hinst : Instantaneous st.T) :
    (∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn)
    ∧ (∀ (cred : VC Digest Proof) (m : Node) (τ : Time),
        RevokedAt st.log cred m τ → τ ≤ st.tSettle →
        honorsAtSettlement st cred = false) := by
  refine ⟨?_, ?_⟩
  · exact lightclient_unfoolable_circuit_sound (hCmb := hCmb) (hCompress := hCompress)
      (hCompressN := hCompressN) (hLeaf := hLeaf) (hRest := hRest) hash LH pi π hcw hacc
  · intro cred m τ hrev hle
    exact settled_revocation_immediate st hinst cred m τ hrev hle

#assert_axioms settlement_soundness_single_machine

/-! ## §5 — THE TEETH: the branch-vs-settlement gap is REAL (both polarities).

Settlement Soundness is NON-VACUOUS exactly because there is a window where a cap is honored AT THE
BRANCH but NOT AT SETTLEMENT. We exhibit it on the `Distributed.Revocation` tooth topology: a
credential revoked at origin `0` at `τ = 0`, with a settlement tip at the propagation boundary, is
honored strictly BEFORE the bound (the branch view) and NOT at/after it (the settlement view). The
guarantee bites exactly at the settlement tip. -/

section Teeth

open Dregg2.Crypto.Reference

/-- A settlement at the propagation boundary `tSettle = 5 = τ + delay 0 1` on the tooth topology:
node `1` finalizes at the moment the revocation has propagated. -/
def toothSettleAtBound : RevSettlement where
  T := toothTopology
  log := toothLog
  nSettle := 1
  tSettle := 5

/-- A settlement STRICTLY INSIDE the stale window `tSettle = 4 < 5`: node `1` finalizes before the
revocation has propagated — the BRANCH view, where the (already-revoked) cap is still honored. -/
def toothSettleInWindow : RevSettlement where
  T := toothTopology
  log := toothLog
  nSettle := 1
  tSettle := 4

/-- **TOOTH (settlement bites).** At the settlement tip past the propagation bound, the revoked
credential is NOT honored — Settlement Soundness's revocation leg fires. -/
theorem settlement_bites :
    honorsAtSettlement toothSettleAtBound toothCred = false := by
  apply settled_revocation_bounded toothSettleAtBound toothCred 0 0 tooth_revoked
  decide

/-- **TOOTH (the branch-vs-settlement gap is REAL).** STRICTLY INSIDE the stale window, the SAME
already-revoked credential IS honored — this is the branch-time view a naive light client would
accept. Settlement Soundness rejects it (settlement_bites) precisely because settlement reads the tip,
not the branch. This pair witnesses the guarantee is non-vacuous: it RULES OUT a real behavior (honored
at branch) that the in-window witness exhibits. -/
theorem settlement_gap_real :
    -- honored at the BRANCH (inside the stale window) …
    honorsAtSettlement toothSettleInWindow toothCred = true
    -- … but NOT honored at SETTLEMENT (the tip past the bound).
    ∧ honorsAtSettlement toothSettleAtBound toothCred = false := by
  refine ⟨?_, settlement_bites⟩
  -- the in-window branch view: node 1's local revocation set at t=4 is empty, verify accepts.
  show honors toothSettleInWindow.T toothSettleInWindow.log toothSettleInWindow.nSettle
    toothSettleInWindow.tSettle toothCred = true
  unfold toothSettleInWindow honors verify isRevoked localRevSet toothTopology toothLog
  decide

/-- The n=1 collapse of the gap: instantaneous propagation closes the window — even the in-window
coordinate becomes a settlement that REJECTS (no branch-vs-settlement gap when there is one machine). -/
theorem settlement_gap_collapses_single_machine :
    honorsAtSettlement
      { T := toothTopologyInstant, log := toothLog, nSettle := 1, tSettle := 4 } toothCred = false := by
  apply settled_revocation_immediate
    { T := toothTopologyInstant, log := toothLog, nSettle := 1, tSettle := 4 }
    (fun _ _ => rfl) toothCred 0 0 tooth_revoked
  decide

/-! ### It runs (`#guard`) — the settlement view across the branch-vs-settlement boundary. -/

-- branch view (inside the stale window): the revoked cap is still honored at settlement-tip t=4
#guard honorsAtSettlement toothSettleInWindow toothCred == true
-- settlement view (tip at the bound t=5): the revocation has settled, the cap is NOT honored
#guard honorsAtSettlement toothSettleAtBound toothCred == false
-- single-machine collapse: instantaneous propagation ⇒ no gap, rejected already at t=4
#guard honorsAtSettlement
  { T := toothTopologyInstant, log := toothLog, nSettle := 1, tSettle := 4 } toothCred == false

end Teeth

end Dregg2.Circuit.SettlementSoundness
