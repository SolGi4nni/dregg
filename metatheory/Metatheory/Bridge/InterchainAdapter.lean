/-
# Metatheory.Bridge.InterchainAdapter — foreign-chain finality as a HYPOTHESIS, not a
re-implemented consensus.

The one thing a cross-chain bridge must NOT do is re-derive the foreign chain's consensus
inside dregg's proofs. `Dregg2.Circuit.Spec.bridgeinboundmint`'s §8 already names the
right shape: the "CryptoPortal" other-chain confirmation is a **`Prop`-carrier** that
governs WHEN the bridge cell may move — conservation and issuer-authority hold *regardless*
of the confirmation (they are the in-VM gates `bridgeMint_authorized` / `bridgeMint_supply_delta`).

This file GENERALIZES that single §8 carrier into the `InterchainAdapter`: an interface that
lets dregg treat ANY foreign chain's finality as an assumed oracle (`foreignFinal`), pinned to
a `TrustRung` dial (proof / optimistic-watchtower / committee / rpc). For the `proof` rung the
oracle is *dischargeable to a theorem*; for the weaker rungs it is an assumption supplied AS
DATA (a structure field), never a global `axiom` and never a `def FooHard` used as a hidden
hypothesis. The adapter's acceptance predicate then GATES the deployed settlement
(`Metatheory.SettlementSoundness.deployedSettle`) with the foreign-finality witness, and the
top theorem COMPOSES — it re-proves nothing:

  * settlement authority live-at-tip  ← `settlement_soundness` (the deployed binding discipline),
  * bridge-issuer authority held      ← `execBridgeMintA_iff_spec` (the executor⟺spec ⟺),
  * every asset's supply UNCHANGED    ← `bridgeMint_supply_delta` (the W1 conservation content).

NON-VACUITY (load-bearing, the branchSettle_NOT_binds analog): the gate DISCRIMINATES. The
SAME live cap at the SAME tip credits under a FINALIZED confirmation and is REFUSED under an
UNFINALIZED / zero-height (uninitialized) confirmation — the foreign-finality leg is the only
difference. And an EMPTY adapter (`foreignFinal ≡ False`, the fail-closed default) credits
NOTHING: the Nomad-law rejection — an unproven/zero confirmation is never "accepted".

Kernel-clean: composes only the already-axiom-clean keystones; `#assert_axioms` hard-gates.
-/
import Metatheory.SettlementSoundness
import Dregg2.Circuit.Spec.bridgeinboundmint
import Dregg2.Tactics

namespace Metatheory.Bridge

open Metatheory.SettlementSoundness Metatheory.KeyLeak
open Dregg2.Exec Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.BridgeInboundMint

/-! ## §1 — The trust dial and the adapter interface.

`TrustRung` mirrors the Rust dials conceptually: how the foreign chain's finality is believed.
It carries NO proof power by itself — it names the epistemic posture; the actual finality
witness lives in the adapter's `foreignFinal` field. -/

/-- **`TrustRung`** — how a foreign chain's finality is trusted, weakest-last. `proof`: a
validity proof of the foreign consensus (`foreignFinal` is DISCHARGEABLE to a theorem).
`optimisticWatchtower`: a fraud-proof window elapsed with no challenge (assumed). `committee`:
a multisig/committee attestation (assumed honest threshold). `rpc`: a trusted RPC (fully
assumed — the weakest rung). -/
inductive TrustRung
  | proof
  | optimisticWatchtower
  | committee
  | rpc
deriving DecidableEq, Repr

/-- **`InterchainAdapter Header Event`** — the interface that lets dregg treat a foreign
chain's finality as a HYPOTHESIS without re-implementing its consensus.

  * `foreignFinal : Header → Prop` — the §8 `CryptoPortal` `Prop`-carrier, GENERALIZED: an
    assumed oracle "this foreign header is final". Supplied as DATA (a field), so for the
    `proof` rung it is a proven predicate and for the weaker rungs an explicit assumption —
    never an `axiom`, never a laundered `def FooHard`.
  * `inclusion : Event → Header → Prop` — "this cross-chain event (a lock confirmation) is
    included in that foreign header".
  * `trust : TrustRung` — the epistemic dial the finality witness rests on. -/
structure InterchainAdapter (Header Event : Type) where
  foreignFinal : Header → Prop
  inclusion    : Event → Header → Prop
  trust        : TrustRung

/-- **`InterchainAdapter.accepts A ev`** — the adapter accepts a cross-chain event `ev` iff
there is a FINALIZED foreign header that INCLUDES it. This is the generalized §8 portal gate:
`∃ hdr, foreignFinal hdr ∧ inclusion ev hdr`. A zero/uninitialized event with no finalized
including header is NOT accepted — the fail-closed Nomad-law default. -/
def InterchainAdapter.accepts {Header Event : Type}
    (A : InterchainAdapter Header Event) (ev : Event) : Prop :=
  ∃ hdr, A.foreignFinal hdr ∧ A.inclusion ev hdr

/-! ## §2 — The adapter-GATED settlement predicate, and that it still BINDS live authority.

`adapterSettle A ev` restricts the deployed settlement with the foreign-finality gate: a turn
settles only if (a) the adapter accepts the confirmation AND (b) the deployed
attenuation-∧-tip-revocation gate admits it. Because it is a RESTRICTION of `deployedSettle`,
it inherits `BindsLiveAuthority` verbatim — the keystone applies unchanged. -/

/-- **`adapterSettle A ev`** — the deployed settlement, additionally gated by the adapter's
foreign-finality acceptance of `ev`. A `SettlePred`. -/
def adapterSettle {Header Event : Type}
    (A : InterchainAdapter Header Event) (ev : Event) : SettlePred :=
  fun T log held tip ac => A.accepts ev ∧ deployedSettle T log held tip ac

/-- **`adapterSettle_binds`** — the adapter-gated settlement STILL binds live authority (the
foreign gate only restricts; the honored-∧-attenuation legs come straight from the deployed
closure `deployedSettle_binds_live_authority`). No new obligation is invented — it reduces to
the existing `BindsLiveAuthority deployedSettle`. -/
theorem adapterSettle_binds {Header Event : Type}
    (A : InterchainAdapter Header Event) (ev : Event) :
    BindsLiveAuthority (adapterSettle A ev) := by
  intro T log held tip ac hset
  exact deployedSettle_binds_live_authority T log held tip ac hset.2

/-! ## §3 — THE TOP THEOREM — foreign finality + a committed bridge mint ⟹ sound + conservative.

The composition, re-proving nothing: from an adapter-gated settlement AND a committed inbound
mint, conclude (1) the foreign confirmation was witnessed final, (2) the settlement authority
was LIVE at the tip (`settlement_soundness`), (3) the bridge-ISSUER authority held and the
amount was non-negative (`execBridgeMintA_iff_spec`), (4) EVERY asset's supply is UNCHANGED
(`bridgeMint_supply_delta`). The foreign chain's consensus is never re-derived — its finality
is the assumed `A.accepts ev` leg. -/

theorem interchain_credit_sound_and_conservative
    {Header Event : Type} (A : InterchainAdapter Header Event) (ev : Event)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hset : adapterSettle A ev T log held tip ac)
    (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState)
    (hmint : execFullA st (.bridgeMintA actor cell a value) = some st') :
    A.accepts ev
    ∧ LiveAtTip T log held tip ac
    ∧ mintAuthorizedB st.kernel.caps actor a = true
    ∧ 0 ≤ value
    ∧ (∀ b, recTotalAsset st'.kernel b = recTotalAsset st.kernel b) := by
  -- (3) via the executor⟺spec ⟺: a committed mint ENTAILS the full admissibility guard.
  have hspec := (execBridgeMintA_iff_spec st actor cell a value st').mp hmint
  refine ⟨hset.1, ?_, hspec.1.1, hspec.1.2.1, ?_⟩
  · -- (2) via the keystone on the adapter-gated (still-binding) settlement.
    exact settlement_soundness (adapterSettle_binds A ev) T log held tip ac hset
  · -- (4) via the W1 conservation content, lifted from the same committed mint.
    exact fun b => bridgeMint_supply_delta st actor cell a value st' hmint b

/-- The soundness projection alone (authority live at settlement), for callers who only need
the settlement leg. -/
theorem interchain_authority_live_at_tip
    {Header Event : Type} (A : InterchainAdapter Header Event) (ev : Event)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hset : adapterSettle A ev T log held tip ac) :
    LiveAtTip T log held tip ac :=
  settlement_soundness (adapterSettle_binds A ev) T log held tip ac hset

/-! ## §4 — The demo instances: a finalized adapter, the zero/uninitialized confirmation, and
the fail-closed empty adapter.

`ForeignHeader.height 0` is the UNINITIALIZED / genesis-zero header: `goodAdapter` treats it
as NOT final (`1 ≤ height`) — the Nomad-law default (the zero slot is never "accepted"). -/

/-- A foreign block header, keyed by height. Height `0` is the uninitialized/zero header. -/
structure ForeignHeader where
  height : Nat
deriving DecidableEq, Repr

/-- A cross-chain lock confirmation: the foreign height it claims inclusion at. -/
structure LockConfirm where
  atHeight : Nat
deriving DecidableEq, Repr

/-- **`goodAdapter`** — a `committee`-rung adapter. `foreignFinal h := 1 ≤ h.height` (the
zero/uninitialized header is NOT final — the fail-closed default); `inclusion ev h :=
ev.atHeight = h.height`. -/
def goodAdapter : InterchainAdapter ForeignHeader LockConfirm where
  foreignFinal := fun h => 1 ≤ h.height
  inclusion    := fun ev h => ev.atHeight = h.height
  trust        := .committee

/-- **`proofAdapter`** — the SAME predicate on the `proof` rung, where finality is DISCHARGED
to a theorem (`proofAdapter_final_discharged`) rather than assumed. Same interface; stronger
dial. -/
def proofAdapter : InterchainAdapter ForeignHeader LockConfirm where
  foreignFinal := fun h => 1 ≤ h.height
  inclusion    := fun ev h => ev.atHeight = h.height
  trust        := .proof

/-- **`emptyAdapter`** — the FAIL-CLOSED default: `foreignFinal ≡ False`. An uninitialized
adapter treats NOTHING as final (the correct inverse of the Nomad bug, where the default was
"accepted"). Credits nothing (`emptyAdapter_never_credits`). -/
def emptyAdapter : InterchainAdapter ForeignHeader LockConfirm where
  foreignFinal := fun _ => False
  inclusion    := fun _ _ => True
  trust        := .rpc

/-- A finalized confirmation at height `5`. -/
def goodConfirm : LockConfirm := ⟨5⟩
/-- The zero/uninitialized confirmation — claims inclusion at the height-`0` (never-final) header. -/
def zeroConfirm : LockConfirm := ⟨0⟩

/-- For the `proof` rung, finality is a THEOREM, not an assumption (discharged, not assumed).
`proofAdapter.foreignFinal ⟨7⟩` is defeq `1 ≤ 7`. -/
theorem proofAdapter_final_discharged : proofAdapter.foreignFinal ⟨7⟩ :=
  (by decide : (1 : Nat) ≤ 7)

/-! ## §5 — NON-VACUITY — the foreign-finality gate DISCRIMINATES (the branchSettle_NOT_binds analog). -/

/-- **NON-VACUITY (TRUE side).** `goodAdapter` accepts the finalized confirmation `goodConfirm`
(there IS a final header at height `5` including it), and — with the SAME live cap at `liveTip`
that `deployedSettle` admits (`deployedSettle_nonvacuous.1`) — the adapter-gated settlement
holds. So the credit gate is genuinely inhabited. -/
theorem interchain_demo_accepts_and_settles :
    goodAdapter.accepts goodConfirm
    ∧ adapterSettle goodAdapter goodConfirm demoTopo demoLog' demoHeld liveTip demoAc := by
  have hacc : goodAdapter.accepts goodConfirm :=
    ⟨(⟨5⟩ : ForeignHeader), (by decide : (1 : Nat) ≤ 5), rfl⟩
  exact ⟨hacc, hacc, deployedSettle_nonvacuous.1⟩

/-- **NON-VACUITY (FALSE side / the NOMAD-LAW rejection).** `goodAdapter` does NOT accept the
zero/uninitialized confirmation: inclusion forces the including header to height `0`, but the
zero header is not final (`1 ≤ height` fails). An unproven/zero confirmation is never accepted. -/
theorem interchain_rejects_unfinalized_zero : ¬ goodAdapter.accepts zeroConfirm := by
  rintro ⟨hdr, hfin, hinc⟩
  have hf : 1 ≤ hdr.height := hfin
  have hi : hdr.height = 0 := hinc.symm
  omega

/-- **THE DISCRIMINATOR BITES (the load-bearing tooth).** With the SAME live cap at the SAME
`liveTip` — where `deployedSettle` DOES admit the turn — the adapter-gated settlement is
REFUSED for the zero/uninitialized confirmation. The ONLY difference from the TRUE side is the
foreign-finality leg: the gate is not a `True`-carrier, it genuinely turns on finality. -/
theorem interchain_zero_confirm_unsettleable :
    ¬ adapterSettle goodAdapter zeroConfirm demoTopo demoLog' demoHeld liveTip demoAc := by
  intro hset
  exact interchain_rejects_unfinalized_zero hset.1

/-- **THE FAIL-CLOSED DEFAULT.** The empty adapter (`foreignFinal ≡ False`) accepts NO event —
the correct inverse of the Nomad default. -/
theorem emptyAdapter_never_accepts (ev : LockConfirm) : ¬ emptyAdapter.accepts ev := by
  rintro ⟨_, hfin, _⟩; exact hfin

/-- The empty adapter credits NOTHING: no settlement ever passes its (always-`False`) gate,
for ANY topology / log / held-list / tip / cap. -/
theorem emptyAdapter_never_credits (ev : LockConfirm)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap) :
    ¬ adapterSettle emptyAdapter ev T log held tip ac := by
  intro hset
  exact emptyAdapter_never_accepts ev hset.1

/-- **The discriminator, assembled** (the laundering guard, `deployed_closure_discriminates`
analog): SAME adapter, SAME held authority, SAME tip — a FINALIZED confirmation credits, the
zero/uninitialized one does NOT. The foreign-finality gate separates them. -/
theorem interchain_gate_discriminates :
    adapterSettle goodAdapter goodConfirm demoTopo demoLog' demoHeld liveTip demoAc
    ∧ ¬ adapterSettle goodAdapter zeroConfirm demoTopo demoLog' demoHeld liveTip demoAc :=
  ⟨interchain_demo_accepts_and_settles.2, interchain_zero_confirm_unsettleable⟩

/-! ## §6 — THE FULL COMPOSITION ON CONCRETE DATA — a real committed mint under a real adapter.

Reuse `BridgeInboundMint.stB0` (cell 1 = the bridge, actor 9 = its issuer). The privileged
inbound mint of 40 of asset 1 COMMITS, and under `goodAdapter`'s finalized confirmation the top
theorem yields live-at-tip authority, held issuer authority, and every-asset supply unchanged. -/

/-- The concrete mint commits (reuses the `bridgeinboundmint` admissibility ⟺). -/
theorem stB0_mint_commits : ∃ st', execFullA stB0 (.bridgeMintA 9 0 1 40) = some st' := by
  apply (bridgeMint_admits_iff stB0 9 0 1 40).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE END-TO-END WITNESS.** For the actual committed mint under `goodAdapter`'s finalized
confirmation at `liveTip`: authority is live at the tip, the bridge-issuer cap held, and EVERY
asset's supply is unchanged (the −40 well debit is exactly the +40 recipient credit). This
exercises `interchain_credit_sound_and_conservative` on real data — not a shape. -/
theorem interchain_demo_credit_sound :
    ∀ st', execFullA stB0 (.bridgeMintA 9 0 1 40) = some st' →
      LiveAtTip demoTopo demoLog' demoHeld liveTip demoAc
      ∧ mintAuthorizedB stB0.kernel.caps 9 1 = true
      ∧ (∀ b, recTotalAsset st'.kernel b = recTotalAsset stB0.kernel b) := by
  intro st' hmint
  have h := interchain_credit_sound_and_conservative goodAdapter goodConfirm
    demoTopo demoLog' demoHeld liveTip demoAc interchain_demo_accepts_and_settles.2
    stB0 9 0 1 40 st' hmint
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩

/-! ### It runs (`#guard`): the credited mint really commits (the bridge well goes −40, sum 0). -/

#guard (execFullA stB0 (.bridgeMintA 9 0 1 40)).isSome
#guard ((execFullA stB0 (.bridgeMintA 9 0 1 40)).map
        (fun s => (s.kernel.bal 1 1, s.kernel.bal 0 1, recTotalAsset s.kernel 1)))
        == some (-40, 40, 0)

/-! ## §7 — Axiom hygiene — every keystone is kernel-clean (CI hard-gate). -/

#assert_axioms adapterSettle_binds
#assert_axioms interchain_credit_sound_and_conservative
#assert_axioms interchain_authority_live_at_tip
#assert_axioms proofAdapter_final_discharged
#assert_axioms interchain_demo_accepts_and_settles
#assert_axioms interchain_rejects_unfinalized_zero
#assert_axioms interchain_zero_confirm_unsettleable
#assert_axioms emptyAdapter_never_accepts
#assert_axioms emptyAdapter_never_credits
#assert_axioms interchain_gate_discriminates
#assert_axioms stB0_mint_commits
#assert_axioms interchain_demo_credit_sound

#print axioms interchain_credit_sound_and_conservative
#print axioms interchain_zero_confirm_unsettleable

end Metatheory.Bridge
