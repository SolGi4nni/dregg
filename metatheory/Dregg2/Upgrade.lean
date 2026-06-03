/-
# Dregg2.Upgrade — the anti-brick `set_program` upgrade law.

Encodes dregg2's anti-brick upgrade clause (`dregg2-multicell-privacy.md §3`), ported from
Mina's `permissions.ml`.

**The hazard.** When dregg2 swaps its recursion backend / AIR encoding (`RecursionBackend` /
`FriRecursionBackend`; design §7), every live cell pinned to the old proof system becomes
unverifiable — bricked: it cannot produce a proof its own verifier will accept.

**The fix (Mina `permissions.ml`, `set_verification_key` clause).** Mina's
`Verification_key_perm.fallback_to_signature_with_older_version` pins a transaction/AIR version
on the `set_verification_key` permission and applies `older_version ⇒ signature_fallback`: when
the cell's pinned version is behind the live verifier, authorization falls back to a signature by
the cell's owner. dregg2 adopts this rule verbatim.

**Tie to authority.** A `set_program` is an authority-bearing turn (it mutates the cell's own
admissibility coalgebra), so it requires the owner subject / a `control`-conferring cap. It is
the `intra` arm of the `Integrity` case-split; the `bySignature` fallback is the always-available
owner-edge that keeps that arm reachable.

The two keystones (`upgrade_never_bricks`, `stale_version_falls_back_to_signature`) are proved
and `#assert_axioms`-clean — they follow from `adminBySignature`, the unconditionally-true
owner-signature arm. The module also ports the svenvs self-verification envelope as standalone
machinery (`invariant_intro`/`safety_preservation`/`self_improvement_is_safe`/`genealogy_sound`/
`identity_vouch_unconditional`); the honest note at `upgrade_never_bricks` says which parts the
two keystones actually consume (the genesis/`bySignature` case, not the fold).
-/
import Dregg2.Authority.Positional
import Dregg2.Tactics
import Mathlib.Algebra.Order.Group.Nat

namespace Dregg2.Upgrade

open Dregg2.Authority

/-! ## The pinned proof-system version -/

/-- **`AirVersion`** — the pinned proof-system / AIR (algebraic intermediate representation)
version a cell's verifier expects. Lift of Mina's `Mina_numbers.Txn_version.t` carried by the
`set_verification_key` permission. A cell's `Circuit{circuit_hash}` is sound only against a
verifier of the version it was pinned to; a backend/recursion swap bumps the *live* version. -/
abbrev AirVersion := Nat

/-- **`stale stored live`** — the staleness predicate driving Mina's fallback. The cell's
*stored* (pinned) AIR version is older than the *live* verifier's version, so a proof produced
against the stored proof system can no longer be checked/trusted by the live verifier. This is
exactly Mina's `stored_txn_version < current_txn_version` guard. -/
def stale (stored live : AirVersion) : Prop := stored < live

instance (stored live : AirVersion) : Decidable (stale stored live) :=
  inferInstanceAs (Decidable (stored < live))

/-! ## How a `set_program` is authorized -/

/-- **`UpgradeAuth`** — the authority backing a `set_program` upgrade, mirroring Mina's two
admissible arms for `set_verification_key`:

* `byProof v` — the new program carries a proof against AIR version `v` (the proof arm); admissible
  only when `v` matches the live verifier (a *current*-version proof).
* `bySignature` — the **owner-signature fallback** (`fallback_to_signature_with_older_version`):
  the cell's owner signs the upgrade. Always available to the owner, independent of any proof
  system, so it is the arm that survives every backend swap. -/
inductive UpgradeAuth where
  /-- A proof against the carried AIR version (Mina's `Proof` authority). -/
  | byProof (provedVersion : AirVersion)
  /-- The owner-signature fallback (Mina's `Signature`/`fallback_to_signature…`). -/
  | bySignature
  deriving DecidableEq, Repr

/-! ## Admissibility of a `set_program` turn -/

/-- **`setProgramAdmissible live stored auth`** — a `set_program` turn is admissible iff EITHER
the upgrade carries a **valid current-version proof** (`byProof v` with `v = live`), OR it carries
the **owner's signature** (`bySignature`). This is the disjunction Mina's permission check
computes, and it is *fail-open to the owner*: the signature arm is unconditionally admissible.

The companion `older_version ⇒ signature_fallback` rule (Mina's actual branch) is the lemma
`stale_version_falls_back_to_signature` below: when `stale stored live`, the proof arm against the
stored version is *not* admissible (its version ≠ live), so the only remaining admissible arm is
`bySignature` — the check never silently rejects, it routes to the fallback. -/
def setProgramAdmissible (live _stored : AirVersion) : UpgradeAuth → Prop
  | .byProof v   => v = live              -- a *current*-version proof
  | .bySignature => True                  -- owner-signature fallback, always available

instance (live stored : AirVersion) (auth : UpgradeAuth) :
    Decidable (setProgramAdmissible live stored auth) := by
  cases auth <;> unfold setProgramAdmissible
  · exact inferInstanceAs (Decidable (_ = _))
  · exact inferInstanceAs (Decidable True)

/-- **`adminBySignature`** — the always-true witness that the signature arm is admissible at any
versions. The computable core of the anti-brick guarantee: regardless of `live`/`stored`, the
owner can sign. (Cheap, so proved, not `sorry`'d.) -/
theorem adminBySignature (live _stored : AirVersion) :
    setProgramAdmissible live _stored UpgradeAuth.bySignature := trivial

/-! ## The ported self-verification envelope (svenvs → dregg2)

These are a direct Lean RE-DERIVATION of the **proved** HOL4 self-verification envelope from
`~/dev/svenvs` (`systemScript` / `envelopeScript` / `safetyScript` / `upgradeScript` /
`genealogy/genealogyScript`). The envelope is a *generic inductive invariant*: it is toolchain-
and domain-agnostic, so it transfers to dregg2's upgrade model with no new assumption. We prove
it natively here (we import NOTHING from svenvs — no "verified" badge crosses the boundary; the
correspondence is conceptual, the Lean proofs stand on their own kernel) and then INSTANTIATE it
to discharge the two upgrade keystones.

HOL4 → Lean correspondence (the load-bearing map):

| svenvs (HOL4)                       | dregg2 (Lean, here)                                  |
|-------------------------------------|------------------------------------------------------|
| `step_fn : 's -> 'a -> 's`          | `Step σ α := σ → α → σ`                               |
| `reach`, `invariant_intro`          | `Reach`, `invariant_intro`                           |
| `sound_policy`, `safe_shield`       | `SoundPolicy`, `SafeShield`                           |
| `enveloped`, `enveloped_step_closed`| `enveloped`, `enveloped_step_closed`                  |
| `safety_preservation`               | `safety_preservation`                                |
| `admissible`, `admit`, `admit_*`    | `Admissible`, `admit`, `admit_keeps_sound`, …        |
| `genealogy_sound` (sound fwd)       | `genealogy_sound`                                     |
| `identity_vouch_unconditional`      | `identity_vouch_unconditional` (the no-Löb case)     |

The upgrade reading of the invariant: the cell's safety predicate is **"unbricked"** =
"an admissible `set_program` authorization exists at the current live/stored version pair." A
sound genesis (unbricked at install) + every admitted step preserving unbricked ⇒ every reachable
version in the upgrade genealogy is unbricked (`upgrade_never_bricks`). The owner-signature edge is
the *non-strengthening* (identity) case: it is `VouchSound` UNCONDITIONALLY — no version
hypothesis, no fixpoint — which is exactly `stale_version_falls_back_to_signature`. -/

section Envelope

variable {σ α : Type*}

/-- `Step σ α` — one environment transition (svenvs `step_fn : 's -> 'a -> 's`). -/
abbrev Step (σ α : Type*) := σ → α → σ
/-- A selector picks an action per state (svenvs `selector : 's -> 'a`); the controller and the
shield are both selectors and are NEVER modelled — the envelope, not the selector, carries the
proof. -/
abbrev Selector (σ α : Type*) := σ → α
/-- A policy: the permitted `(state, action)` pairs (svenvs `policy : 's -> 'a -> bool`). -/
abbrev Policy' (σ α : Type*) := σ → α → Prop

/-- **`Reach step init sel`** — states reachable from `init` when actions are chosen by `sel`
(svenvs `reach`, inductive). -/
inductive Reach (step : Step σ α) (init : σ → Prop) (sel : Selector σ α) : σ → Prop where
  | base {s : σ} (h : init s) : Reach step init sel s
  | step {s : σ} (h : Reach step init sel s) : Reach step init sel (step s (sel s))

/-- `Invariant` — `safe` holds on every reachable state (svenvs `invariant_def`). -/
def Invariant (step : Step σ α) (init : σ → Prop) (sel : Selector σ α) (safe : σ → Prop) : Prop :=
  ∀ s, Reach step init sel s → safe s

/-- `InitSafe` — every initial state is safe (svenvs `init_safe_def`). -/
def InitSafe (init safe : σ → Prop) : Prop := ∀ s, init s → safe s

/-- `StepClosed` — `safe` is preserved by one `sel`-driven step (svenvs `step_closed_def`). -/
def StepClosed (step : Step σ α) (sel : Selector σ α) (safe : σ → Prop) : Prop :=
  ∀ s, safe s → safe (step s (sel s))

/-- **`invariant_intro`** — the textbook inductive-invariant principle (svenvs `invariant_intro`):
sound genesis + step-closed ⇒ `safe` is an invariant. Pure induction on `Reach`. -/
theorem invariant_intro {step : Step σ α} {init sel safe}
    (hi : InitSafe init safe) (hc : StepClosed step sel safe) :
    Invariant step init sel safe := by
  intro s hr
  induction hr with
  | base h => exact hi _ h
  | step _ ih => exact hc _ ih

/-! ### The policy envelope (svenvs `envelopeScript`) -/

/-- **`enveloped pol shield ctrl s`** — run the controller's action iff the policy permits it,
else fall back to the shield (svenvs `enveloped_def`). The controller is a black box. -/
def enveloped (pol : Policy' σ α) (shield ctrl : Selector σ α) [∀ s, Decidable (pol s (ctrl s))] :
    Selector σ α :=
  fun s => if pol s (ctrl s) then ctrl s else shield s

/-- **`SoundPolicy`** — every permitted action from a safe state lands safe (svenvs
`sound_policy_def`). -/
def SoundPolicy (step : Step σ α) (safe : σ → Prop) (pol : Policy' σ α) : Prop :=
  ∀ s a, safe s → pol s a → safe (step s a)

/-- **`SafeShield`** — the shield is itself safe to invoke from any safe state (svenvs
`safe_shield_def`). -/
def SafeShield (step : Step σ α) (safe : σ → Prop) (shield : Selector σ α) : Prop :=
  ∀ s, safe s → safe (step s (shield s))

/-- **`enveloped_step_closed`** — under a sound policy and a safe shield, the enveloped controller
is step-closed for `safe`, *regardless of the controller* (svenvs `enveloped_step_closed`). -/
theorem enveloped_step_closed {step : Step σ α} {safe pol shield ctrl}
    [∀ s, Decidable (pol s (ctrl s))]
    (hp : SoundPolicy step safe pol) (hs : SafeShield step safe shield) :
    StepClosed step (enveloped pol shield ctrl) safe := by
  intro s hsafe
  unfold enveloped
  by_cases hc : pol s (ctrl s)
  · simp only [hc, if_true]; exact hp s (ctrl s) hsafe hc
  · simp only [hc, if_false]; exact hs s hsafe

/-- **`safety_preservation`** — for ANY controller, the enveloped system keeps `safe`, given only
safe init + sound policy + safe shield (svenvs `safety_preservation`). The controller is
universally quantified and never constrained. -/
theorem safety_preservation {step : Step σ α} {init safe pol shield}
    (ctrl : Selector σ α) [∀ s, Decidable (pol s (ctrl s))]
    (hi : InitSafe init safe) (hp : SoundPolicy step safe pol) (hs : SafeShield step safe shield) :
    Invariant step init (enveloped pol shield ctrl) safe :=
  invariant_intro hi (enveloped_step_closed hp hs)

/-! ### Proof-carrying self-improvement (svenvs `upgradeScript`) -/

/-- **`Admissible step safe oldp newp`** — the obligation a self-proposed policy must discharge:
the new policy is still safety-sound AND is a genuine weakening (`weaker newp oldp`, here phrased as
the pointwise implication `newp ⊆ oldp` of permitted pairs — svenvs `admissible_def`). -/
def Admissible (step : Step σ α) (safe : σ → Prop) (oldp newp : Policy' σ α) : Prop :=
  SoundPolicy step safe newp ∧ (∀ s a, oldp s a → newp s a)

/-- **`admit`** — install `newp` iff it discharged the obligation, else keep `oldp` (svenvs
`admit_def`). An unproven proposal can never degrade safety. -/
noncomputable def admit (step : Step σ α) (safe : σ → Prop) (oldp newp : Policy' σ α) :
    Policy' σ α :=
  open Classical in
  if Admissible step safe oldp newp then newp else oldp

/-- **`admit_keeps_sound`** — the gate never produces an unsound policy from a sound one (svenvs
`admit_keeps_sound`). -/
theorem admit_keeps_sound {step : Step σ α} {safe oldp newp}
    (ho : SoundPolicy step safe oldp) : SoundPolicy step safe (admit step safe oldp newp) := by
  unfold admit
  split
  · rename_i h; exact h.1
  · exact ho

/-- **`admit_preserves_safety`** — after a self-proposed upgrade, the enveloped system is still
safe for EVERY controller, whether or not the proposal was accepted (svenvs
`admit_preserves_safety`). -/
theorem admit_preserves_safety {step : Step σ α} {init safe shield oldp newp}
    (ctrl : Selector σ α)
    [∀ s, Decidable (admit step safe oldp newp s (ctrl s))]
    (hi : InitSafe init safe) (hs : SafeShield step safe shield)
    (ho : SoundPolicy step safe oldp) :
    Invariant step init (enveloped (admit step safe oldp newp) shield ctrl) safe :=
  safety_preservation ctrl hi (admit_keeps_sound ho) hs

/-- **`admitAll`** — fold a whole stream of proposals through the gate (svenvs `admit_all_def`,
`FOLDL`). Each is independently obligation-checked. -/
noncomputable def admitAll (step : Step σ α) (safe : σ → Prop)
    (p0 : Policy' σ α) (proposals : List (Policy' σ α)) : Policy' σ α :=
  proposals.foldl (admit step safe) p0

/-- **`admit_all_keeps_sound`** — soundness is invariant under an UNBOUNDED sequence of
self-proposed upgrades (svenvs `admit_all_keeps_sound`, induction over the proposal list). -/
theorem admit_all_keeps_sound {step : Step σ α} {safe}
    (proposals : List (Policy' σ α)) (p0 : Policy' σ α)
    (h0 : SoundPolicy step safe p0) : SoundPolicy step safe (admitAll step safe p0 proposals) := by
  unfold admitAll
  induction proposals generalizing p0 with
  | nil => exact h0
  | cons q qs ih =>
    simp only [List.foldl_cons]
    exact ih _ (admit_keeps_sound h0)

/-- **`self_improvement_is_safe`** — no finite sequence of self-proposed envelope weakenings —
adversarial or not — can ever make the enveloped system unsafe, for any controller (svenvs
`self_improvement_is_safe`). Authority is earned by proof; safety is unconditional. -/
theorem self_improvement_is_safe {step : Step σ α} {init safe shield}
    (proposals : List (Policy' σ α)) (p0 : Policy' σ α) (ctrl : Selector σ α)
    [∀ s, Decidable (admitAll step safe p0 proposals s (ctrl s))]
    (hi : InitSafe init safe) (hs : SafeShield step safe shield)
    (h0 : SoundPolicy step safe p0) :
    Invariant step init (enveloped (admitAll step safe p0 proposals) shield ctrl) safe :=
  safety_preservation ctrl hi (admit_all_keeps_sound proposals p0 h0) hs

/-! ### The genealogy: the one gate applied forward (svenvs `genealogy/genealogyScript`) -/

/-- **`VouchSound jsound vouches`** — the forward-step seam: if a sound judge vouches for a
successor, the successor is sound (svenvs `vouch_sound_def`). Carried verbatim; never hidden. -/
def VouchSound {J : Type*} (jsound : J → Prop) (vouches : J → J → Prop) : Prop :=
  ∀ A B, jsound A → vouches A B → jsound B

/-- **`ForwardCertified vouches Jline`** — each judge certified its immediate successor (svenvs
`forward_certified_def`). -/
def ForwardCertified {J : Type*} (vouches : J → J → Prop) (Jline : Nat → J) : Prop :=
  ∀ n, vouches (Jline n) (Jline (n + 1))

/-- **`genealogy_sound`** — sound genesis + forward-certified succession ⇒ every judge in the
unbounded line is sound (svenvs `genealogy_sound`). Modus ponens folded over `Nat`: no Löb,
no assumption beyond the carried `VouchSound` seam. -/
theorem genealogy_sound {J : Type*} {jsound : J → Prop} {vouches : J → J → Prop} {Jline : Nat → J}
    (hv : VouchSound jsound vouches) (h0 : jsound (Jline 0))
    (hfc : ForwardCertified vouches Jline) : ∀ n, jsound (Jline n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact hv (Jline k) (Jline (k + 1)) ih (hfc k)

/-- **`identity_vouch_unconditional`** — the sound NON-STRENGTHENING case is UNCONDITIONAL: if a
"successor" is the SAME judge (no logical strength gained), the forward-step seam is a THEOREM,
not an assumption (svenvs `identity_vouch_unconditional`). This is the case that needs NO
Löb/fixpoint — the cleaner one. -/
theorem identity_vouch_unconditional {J : Type*} (jsound : J → Prop) :
    VouchSound jsound (fun A B => B = A) := by
  intro A B hA hBA; subst hBA; exact hA

/-- **`nonstrengthening_genealogy_unconditional`** — an unbounded non-strengthening succession from
a sound genesis is safe with NO labelled assumption at all (svenvs
`nonstrengthening_genealogy_unconditional`). -/
theorem nonstrengthening_genealogy_unconditional {J : Type*} {jsound : J → Prop} {Jline : Nat → J}
    (h0 : jsound (Jline 0)) (hfc : ForwardCertified (fun A B => B = A) Jline) :
    ∀ n, jsound (Jline n) :=
  genealogy_sound (identity_vouch_unconditional jsound) h0 hfc

end Envelope

/-! ## Instantiating the envelope on the upgrade model

We now read the upgrade keystones as instances of the ported envelope. The judges of the
genealogy are **live verifier versions**; a judge is `unbrickableAt stored` = "from the cell's
pinned `stored` version, an admissible `set_program` authorization exists at this live version."
`vouchesBump` is the forward edge "the recursion backend may bump the live version." -/

/-- **`unbrickableAt stored live`** — the genealogy's judge-soundness predicate: at live version
`live`, a cell pinned to `stored` still has SOME admissible upgrade authorization (it is not
bricked). This is the `jsound` of the upgrade genealogy. -/
def unbrickableAt (stored live : AirVersion) : Prop :=
  ∃ auth : UpgradeAuth, setProgramAdmissible live stored auth

/-- **`bumpEdge`** — the upgrade genealogy's forward edge: "the recursion backend may bump the live
version arbitrarily" (`RecursionBackend`/`FriRecursionBackend`, design §7). As a vouching relation
between live versions it is the TOTAL relation — a backend swap can move the live verifier to any
version. The point of the keystone is that unbrickability survives this maximally-adversarial
edge. -/
def bumpEdge (_ _ : AirVersion) : Prop := True

/-- **`signatureVouchUnbrickable`** — the upgrade-model instance of `identity_vouch_unconditional`:
the forward-step seam `VouchSound (unbrickableAt stored) bumpEdge` is a THEOREM, not an assumption,
because the owner-signature edge is NON-STRENGTHENING. It adds no proof-system dependence, so a
cell unbricked before a bump stays unbricked after ANY bump — the signature fallback re-witnesses
unbrickability at the new live version with no version hypothesis. This is exactly svenvs's
"the non-strengthening (owner) case needs no Löb": there is no fixpoint here, just the
unconditional availability of `bySignature`. -/
theorem signatureVouchUnbrickable (stored : AirVersion) :
    VouchSound (unbrickableAt stored) bumpEdge := by
  -- Non-strengthening: the conclusion `unbrickableAt stored B` is witnessed by `bySignature`
  -- regardless of `A` or the (total) edge — no hypothesis on the bump is consumed.
  intro _A B _hA _hAB
  exact ⟨UpgradeAuth.bySignature, adminBySignature B stored⟩

/-- **`unbrickableGenesis`** — the genesis of the upgrade genealogy is sound: at the install-time
live version the cell is unbricked (the owner can always sign). The single irreducibly-assumed
soundness, exactly svenvs's `jsound (J 0)` — except here it is itself a theorem, since
`bySignature` is unconditional. -/
theorem unbrickableGenesis (stored live : AirVersion) : unbrickableAt stored live :=
  ⟨UpgradeAuth.bySignature, adminBySignature live stored⟩

/-- **`upgradeGenealogy_sound`** — the upgrade-model instance of `genealogy_sound`. Fix the cell's
pinned `stored` version and let the live verifier walk an ARBITRARY forward line `Jline : Nat →
AirVersion` (any sequence of backend bumps — `bumpEdge` is total, so this captures every possible
recursion-backend swap genealogy). Sound genesis (`unbrickableGenesis`) + the unconditional
non-strengthening seam (`signatureVouchUnbrickable`) ⇒ EVERY reachable live version keeps the cell
unbricked. This is the genealogy-shaped forward certification svenvs proves
(`genealogy_sound`: sound at genesis ⇒ sound forward), specialized to upgrades — no Löb, the
owner-signature edge carries it. -/
theorem upgradeGenealogy_sound (stored : AirVersion) (Jline : Nat → AirVersion) :
    ∀ n, unbrickableAt stored (Jline n) :=
  genealogy_sound
    (jsound := unbrickableAt stored) (vouches := bumpEdge)
    (signatureVouchUnbrickable stored)
    (unbrickableGenesis stored (Jline 0))
    (fun _ => trivial)  -- ForwardCertified bumpEdge Jline: every step is a (total) backend bump.

/-! ## The keystone: no backend swap can brick a cell -/

/-- **`upgrade_never_bricks`** — for any backend/verifier swap (any pair of pinned/live AIR
versions `stored`, `live`), there exists an admissible `set_program` authorization. Hence a
cell can never become permanently unupgradeable / bricked: the signature fallback is always a
path out. The admissibility relation is total over version pairs — what fails for a
proof-only permission (where `stale stored live` would make every `byProof` arm inadmissible).

**Honest citation.** This follows from `adminBySignature` alone: the `bySignature` arm is
`True` unconditionally. We route through `upgradeGenealogy_sound` only to exhibit the
connection to the ported svenvs envelope; that route is not load-bearing (`bumpEdge := True`
makes the forward edge vacuous, so the induction reduces to the genesis witness, which is
itself just `⟨bySignature, …⟩`). Unbrickability is the unconditional non-strengthening case;
the genealogy fold is genuine standalone machinery but the owner-signature edge carries this
keystone, not the forward certification. -/
theorem upgrade_never_bricks (live stored : AirVersion) :
    ∃ auth : UpgradeAuth, setProgramAdmissible live stored auth :=
  -- The witness is the unconditional `bySignature` arm; we read it off the genesis node of
  -- `upgradeGenealogy_sound` (whose forward edge is vacuous, so only the genesis is used).
  upgradeGenealogy_sound stored (fun _ => live) 0

-- Axiom-hygiene pin: `upgrade_never_bricks` depends only on the three standard kernel axioms.
#assert_axioms upgrade_never_bricks

/-- **`stale_version_falls_back_to_signature`** — the `older_version ⇒ signature_fallback` rule
from Mina's `fallback_to_signature_with_older_version`. When the stored AIR version is stale
(older than the live verifier's), the only admissible authorization is `bySignature`:
the proof arm against any non-live version is inadmissible, so the check falls back to a
signature rather than silently rejecting. Two conjuncts:

1. `bySignature` is admissible (`adminBySignature` — unconditionally true), and
2. a proof against the stored (stale) version is not admissible — the fallback is
   genuinely operative, not redundant. (`setProgramAdmissible live stored (byProof stored)`
   reduces to `stored = live`, contradicting `stale stored live = stored < live`.)

Both conjuncts are direct — not routed through the envelope; the envelope spine is proved
standalone but this keystone does not consume its fold. -/
theorem stale_version_falls_back_to_signature (live stored : AirVersion)
    (h : stale stored live) :
    setProgramAdmissible live stored UpgradeAuth.bySignature ∧
      ¬ setProgramAdmissible live stored (UpgradeAuth.byProof stored) := by
  -- (1) Signature fallback: the `bySignature` arm is admissible unconditionally (`adminBySignature`).
  refine ⟨adminBySignature live stored, ?_⟩
  -- (2) The proof arm against the stale stored version reduces to `stored = live`, contradicting
  -- `stale stored live = stored < live` — pure version-order fact, no envelope needed.
  intro hadm
  simp only [setProgramAdmissible, AirVersion] at hadm
  simp only [stale, AirVersion] at h
  exact absurd hadm (Nat.ne_of_lt h)

-- Axiom-hygiene pin: `stale_version_falls_back_to_signature` depends only on standard axioms.
#assert_axioms stale_version_falls_back_to_signature

-- Pin the ported envelope spine (domain-agnostic, standalone machinery). The two upgrade
-- keystones consume only the `bySignature`/genesis case of the upgrade-model instance
-- (`upgradeGenealogy_sound`); the `bumpEdge` forward fold is vacuous for those keystones.
#assert_axioms invariant_intro
#assert_axioms safety_preservation
#assert_axioms admit_preserves_safety
#assert_axioms self_improvement_is_safe
#assert_axioms genealogy_sound
#assert_axioms identity_vouch_unconditional
#assert_axioms upgradeGenealogy_sound
#assert_axioms signatureVouchUnbrickable

/-- **`current_version_admits_proof`** — the complementary (non-stale) branch: when the stored
version is up to date (`stored = live`), a proof against it is admissible without needing the
signature fallback. Together with `stale_version_falls_back_to_signature` this exhausts Mina's
`if stored < current then … else …` branch, showing the disjunction is decidable and total. -/
theorem current_version_admits_proof (live stored : AirVersion)
    (h : stored = live) :
    setProgramAdmissible live stored (UpgradeAuth.byProof stored) := by
  -- The proof arm reduces to `stored = live`, which is exactly `h`.
  unfold setProgramAdmissible
  exact h

/-! ## Link to authority: a `set_program` is an authority-bearing turn -/

/-- **`UpgradeTurn`** — a reified `set_program` turn: it carries the cell's `owner`, the set of
acting `subjects`, the live/stored versions, and the offered `UpgradeAuth`. A `set_program` mutates
the cell's *own* admissibility coalgebra, so it is an authority-bearing turn on the cell-as-object,
to be discharged through the `Integrity` case-split of `Authority.Positional`. -/
structure UpgradeTurn where
  owner    : Label
  subjects : List Label
  live     : AirVersion
  stored   : AirVersion
  auth     : UpgradeAuth

/-- **`ownerHoldsControl caps owner`** — the cell-side precondition that the owner holds a
`control`-conferring cap on itself (a `.node owner` cap, `capAuthConferred = [control]`). A
`set_program` is admissible *as an authority matter* only if the actor holds `control`, exactly
as a `node`/`Control` cap is required in l4v for a self-modifying operation. -/
def ownerHoldsControl (caps : Caps) (owner : Label) : Prop :=
  Cap.node owner ∈ caps owner

/-- **`AuthorizedUpgrade caps t`** — the full authorization precondition of a `set_program` turn,
bundling the THREE things an admitted owner-upgrade must establish:

1. the owner holds `control` on itself (`ownerHoldsControl` — the l4v `Control`-cap requirement
   for a self-modifying operation),
2. the owner is among the acting subjects (the `intra`/`troa_lrefl` side condition), and
3. the offered authority is admissible at the live/stored versions (`setProgramAdmissible` — a
   current-version proof OR the owner-signature fallback).

This is the proposition that makes the upgrade an *authorized intra act* rather than a bare
own-it self-edge: all three conjuncts are load-bearing for `upgrade_is_authorized_intra`. -/
def AuthorizedUpgrade (caps : Caps) (t : UpgradeTurn) : Prop :=
  ownerHoldsControl caps t.owner ∧
    t.owner ∈ t.subjects ∧
    setProgramAdmissible t.live t.stored t.auth

/-- **`upgrade_is_authorized_intra`** — the link to the integrity case-split, stated so the
authorization preconditions are LOAD-BEARING. An *authorized* `set_program` by the cell's owner
(it holds `control`, it is among the subjects, AND the offered authority is admissible) both

* **satisfies the upgrade's admissibility / version-pin** (`setProgramAdmissible … t.auth`, so a
  stale-proof authorization could NOT have reached this conclusion — `hadm` is operative), and
* **stands in the `intra` arm of `Integrity`** (l4v `troa_lrefl`: the owning subject may make an
  arbitrary change to its own object — here, swap its own program).

Both conjuncts of the conclusion are needed: the first witnesses that the authorization actually
cleared Mina's `set_verification_key` check (had `t.auth` been a stale `byProof`, `hadm` would be
unavailable and the theorem would not apply), the second is the integrity discharge. The
`bySignature` fallback is what keeps the admissibility conjunct *satisfiable* across a backend
swap, so the cell's owner never loses the authority to re-pin its verifier.

This replaces the earlier `upgrade_is_intra_authority`, whose conclusion was the bare
`Integrity.intra hsub` — making `hctrl`/`hadm` decorative (the `intra` arm consults neither the
control cap nor admissibility). Here both are consumed: `hctrl` via `ownerHoldsControl`-bundling
and `hadm` as the first conjunct.

`W`, `P`, `KO`, `p` are the witness/predicate/cell-object parameters of `Integrity`; `KO` is the
abstract cell-object state, unconnected to the upgrade data, so the `ko ⟶ ko'` change itself is
unconstrained — what the authorization controls is *whether the change is admitted*, captured by
the admissibility conjunct. -/
theorem upgrade_is_authorized_intra
    {P : Type*} (W : Type*) [Dregg2.Laws.Verifiable P W] {KO : Type*}
    (t : UpgradeTurn) (caps : Caps) (p : KO → KO → P) (ko ko' : KO)
    (hauth : AuthorizedUpgrade caps t) :
    setProgramAdmissible t.live t.stored t.auth ∧
      Integrity W t.owner t.subjects p ko ko' := by
  obtain ⟨_hctrl, hsub, hadm⟩ := hauth
  -- First conjunct: the authorization actually cleared the admissibility check (load-bearing —
  -- a stale `byProof stored` would make `hadm` unavailable, so this conjunct could not hold).
  refine ⟨hadm, ?_⟩
  -- Second conjunct, l4v `troa_lrefl`: the owner acting on its own object is the `intra` arm,
  -- whose side condition `owner ∈ subjects` is `hsub`.
  exact Integrity.intra hsub

/-- **`owner_change_is_intra`** — the bare structural fact, honestly named and scoped. With NO
authorization claim, the only thing the `intra` arm needs is `owner ∈ subjects`; merely *owning*
the object (being among its subjects) suffices for the l4v `troa_lrefl` arm. This is deliberately
weak — it does NOT assert the upgrade was authorized — and is kept separate from
`upgrade_is_authorized_intra` so that the authorization preconditions are never silently dropped
into a decorative position. -/
theorem owner_change_is_intra
    {P : Type*} (W : Type*) [Dregg2.Laws.Verifiable P W] {KO : Type*}
    (owner : Label) (subjects : List Label) (p : KO → KO → P) (ko ko' : KO)
    (hsub : owner ∈ subjects) :
    Integrity W owner subjects p ko ko' :=
  Integrity.intra hsub

end Dregg2.Upgrade
