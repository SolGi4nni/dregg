/-
# Dregg2.Circuit.WitnessExtractPerEffect — per-effect ADVERSARIAL-witness extraction for the v2 effects.

`WitnessExtract.effect2_extract` is the generic adversarial-witness extractor: an ARBITRARY assignment
`a` that (1) satisfies the v2 effect circuit and (2) is `PIBindsDigests`-pinned (the verifier's
public-input check binds its six digest wires + guard region to the committed values for the claimed
`(pre, args, post)`) forces the effect's `apex`. The adversary keeps every non-gate wire (the un-gated
roots `64/65` and every `w ≥ 72`); the verifier pins only the gate-relevant wires, exactly the genuine
ZK soundness obligation. This was instantiated per-effect ONLY for `mintA` (`TurnEmit.mintA_extract`,
the validated reference).

THIS module lifts that instantiation to every OTHER v2 (`EffectCommit2`) effect that has the three
per-effect obligations `mintA` has — its `EffectSpec2` instance `*E`, its `RestFrameDecodes2`/
`GuardDecodes2` discharges, and its `apex ↔ *Spec` bridge. For each effect we get:

  * `*_extract`               — arbitrary satisfying + PI-bound trace ⇒ the COMPLETE declarative spec
    (NO whole-trace `hEnc`; the adversary keeps every non-gate wire). This is the hostile-witness
    closure: a satisfying witness FORCES the genuine kernel step, not merely "an honest witness exists".
  * `*_extract_emitted`       — the same against the EMITTED (Rust-prover) wire form.
  * `*_extract_rejects_*`     — ANTI-GHOST teeth: a claimed post that VIOLATES the apex (wrong touched
    component / tampered frame / forged log) has NO satisfying PI-bound witness. Forgery is refuted.

Every theorem is a thin composition of the framework crown jewels — the soundness lives ONCE in
`WitnessExtract` / `EffectCommit2`; here we only retarget the spec bridge per effect (the exact shape of
`TurnEmit.mintA_extract` / `mintA_extract_emitted` / `mintA_extract_rejects_wrong_supply`).

ADDITIVE: imports the per-effect `Inst/*` modules (which it does NOT edit) and the generic
`WitnessExtract`. Touches NO executor / `Claims.lean` / `TurnEmit.lean`.
-/
import Dregg2.Circuit.WitnessExtract
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Inst.bridgeMintA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Circuit.Inst.receiptArchiveLifecycleA

namespace Dregg2.Circuit.WitnessExtractPerEffect

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective cellLeafInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 emittedEffect2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.WitnessExtract (PIBindsDigests effect2_extract effect2_extract_emitted
  effect2_extract_rejects_wrong_component effect2_extract_rejects_frame_tamper
  effect2_extract_rejects_log_forge)
open Dregg2.Authority (Caps Cap)
open Dregg2.Exec (RecChainedState CellId AssetId)
open Dregg2.Exec.CircuitEmit (satisfiedEmitted)

set_option autoImplicit false

/-! ## §1 — BALANCE MOVEMENT: `transfer` (the cross-cell `bal` write) and `balanceA`.

Both touch the per-asset ledger `bal` (a `funcComponent`, the realizable injective whole-function digest
of `Function.Injective D`); the rest-frame is the 16 non-`bal` fields (`RestIffNoBal`); the log grows by
the movement receipt. A satisfying PI-bound trace forces `BalanceMovementSpec` — i.e. the claimed write
IS the genuine conservation-respecting transfer, no forged supply. -/

/-- **`transfer_extract`** — adversarial extraction for the cross-cell transfer (`balanceE`). -/
theorem transfer_extract
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.Transfer.BalanceArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.Transfer.balanceE D hD) a)
    (hPI : PIBindsDigests S (Inst.Transfer.balanceE D hD) s args s' a) :
    Spec.BalanceMovement.BalanceMovementSpec s args.t args.a s' :=
  (Inst.Transfer.apex_iff_balanceMovementSpec D hD s args s').mp
    (effect2_extract S (Inst.Transfer.balanceE D hD) (Inst.Transfer.balanceRestFrameDecodes S D hD hRest)
      hLog (Inst.Transfer.balanceGuardDecodes D hD) s args s' a hsat hPI)

/-- **`transfer_extract_emitted`** — the same against the EMITTED (Rust-prover) wire form. -/
theorem transfer_extract_emitted
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.Transfer.BalanceArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.Transfer.balanceE D hD)) a)
    (hPI : PIBindsDigests S (Inst.Transfer.balanceE D hD) s args s' a) :
    Spec.BalanceMovement.BalanceMovementSpec s args.t args.a s' :=
  (Inst.Transfer.apex_iff_balanceMovementSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.Transfer.balanceE D hD)
      (Inst.Transfer.balanceRestFrameDecodes S D hD hRest) hLog (Inst.Transfer.balanceGuardDecodes D hD)
      name s args s' a hsat hPI)

/-- **`transfer_extract_rejects_wrong_ledger`** — ANTI-GHOST: a claimed post whose `bal` violates the
movement's `postClause` (a forged ledger) has NO satisfying PI-bound witness. -/
theorem transfer_extract_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.Transfer.BalanceArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.Transfer.balanceE D hD) s args s' a)
    (htamper : ¬ (Inst.Transfer.balanceE D hD).active.postClause s args
      ((Inst.Transfer.balanceE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.Transfer.balanceE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.Transfer.balanceE D hD) s args s' a hPI htamper

/-- **`balanceA_extract`** — adversarial extraction for `balanceA` (`balanceAE`). -/
theorem balanceA_extract
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.BalanceA.BalanceArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.BalanceA.balanceAE D hD) a)
    (hPI : PIBindsDigests S (Inst.BalanceA.balanceAE D hD) s args s' a) :
    Spec.BalanceMovement.BalanceMovementSpec s args.t args.a s' :=
  (Inst.BalanceA.apex_iff_balanceASpec D hD s args s').mp
    (effect2_extract S (Inst.BalanceA.balanceAE D hD) (Inst.BalanceA.balanceRestFrameDecodes S D hD hRest)
      hLog (Inst.BalanceA.balanceGuardDecodes D hD) s args s' a hsat hPI)

theorem balanceA_extract_emitted
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.BalanceA.BalanceArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.BalanceA.balanceAE D hD)) a)
    (hPI : PIBindsDigests S (Inst.BalanceA.balanceAE D hD) s args s' a) :
    Spec.BalanceMovement.BalanceMovementSpec s args.t args.a s' :=
  (Inst.BalanceA.apex_iff_balanceASpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.BalanceA.balanceAE D hD)
      (Inst.BalanceA.balanceRestFrameDecodes S D hD hRest) hLog (Inst.BalanceA.balanceGuardDecodes D hD)
      name s args s' a hsat hPI)

theorem balanceA_extract_rejects_wrong_ledger
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.BalanceA.BalanceArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.BalanceA.balanceAE D hD) s args s' a)
    (htamper : ¬ (Inst.BalanceA.balanceAE D hD).active.postClause s args
      ((Inst.BalanceA.balanceAE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.BalanceA.balanceAE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.BalanceA.balanceAE D hD) s args s' a hPI htamper

/-! ## §2 — SUPPLY DESTRUCTION: `burnA` (the `bal` DEBIT, dual of mint). -/

/-- **`burnA_extract`** — adversarial extraction for burn (`burnE`). A satisfying PI-bound trace forces
the COMPLETE declarative `BurnSpec` — a forged supply-destruction is refuted. -/
theorem burnA_extract
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.BurnA.BurnArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.BurnA.burnE D hD) a)
    (hPI : PIBindsDigests S (Inst.BurnA.burnE D hD) s args s' a) :
    Spec.SupplyDestruction.BurnSpec s args.actor args.cell args.a args.amt s' :=
  (Inst.BurnA.apex_iff_burnSpec D hD s args s').mp
    (effect2_extract S (Inst.BurnA.burnE D hD) (Inst.BurnA.burnRestFrameDecodes S D hD hRest)
      hLog (Inst.BurnA.burnGuardDecodes D hD) s args s' a hsat hPI)

theorem burnA_extract_emitted
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.BurnA.BurnArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.BurnA.burnE D hD)) a)
    (hPI : PIBindsDigests S (Inst.BurnA.burnE D hD) s args s' a) :
    Spec.SupplyDestruction.BurnSpec s args.actor args.cell args.a args.amt s' :=
  (Inst.BurnA.apex_iff_burnSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.BurnA.burnE D hD) (Inst.BurnA.burnRestFrameDecodes S D hD hRest)
      hLog (Inst.BurnA.burnGuardDecodes D hD) name s args s' a hsat hPI)

theorem burnA_extract_rejects_wrong_supply
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.BurnA.BurnArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.BurnA.burnE D hD) s args s' a)
    (htamper : ¬ (Inst.BurnA.burnE D hD).active.postClause s args
      ((Inst.BurnA.burnE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.BurnA.burnE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.BurnA.burnE D hD) s args s' a hPI htamper

/-! ## §3 — AUTHORITY: the cap-write family (`caps` component, injective `D : Caps → ℤ`).

`attenuate`, `delegate`, `delegateAtten`, `introduce`, `revoke`, `revokeDelegation` all touch the `caps`
component over `RestIffNoCaps`. A satisfying PI-bound trace forces the genuine authority spec — a forged
capability (an un-attenuated descent, a phantom delegation, a skipped revocation) is refuted. -/

/-- **`attenuateA_extract`** — adversarial extraction for `attenuate`. -/
theorem attenuateA_extract
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.AttenuateA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.AttenuateA.AttenuateArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.AttenuateA.attenuateE D hD) a)
    (hPI : PIBindsDigests S (Inst.AttenuateA.attenuateE D hD) s args s' a) :
    Spec.AuthorityAttenuation.AttenuateSpec s args.actor args.idx args.keep s' :=
  (Inst.AttenuateA.apex_iff_attenuateSpec D hD s args s').mp
    (effect2_extract S (Inst.AttenuateA.attenuateE D hD)
      (Inst.AttenuateA.attenuateRestFrameDecodes S D hD hRest) hLog
      (Inst.AttenuateA.attenuateGuardDecodes D hD) s args s' a hsat hPI)

theorem attenuateA_extract_emitted
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.AttenuateA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.AttenuateA.AttenuateArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.AttenuateA.attenuateE D hD)) a)
    (hPI : PIBindsDigests S (Inst.AttenuateA.attenuateE D hD) s args s' a) :
    Spec.AuthorityAttenuation.AttenuateSpec s args.actor args.idx args.keep s' :=
  (Inst.AttenuateA.apex_iff_attenuateSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.AttenuateA.attenuateE D hD)
      (Inst.AttenuateA.attenuateRestFrameDecodes S D hD hRest) hLog
      (Inst.AttenuateA.attenuateGuardDecodes D hD) name s args s' a hsat hPI)

theorem attenuateA_extract_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.AttenuateA.AttenuateArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.AttenuateA.attenuateE D hD) s args s' a)
    (htamper : ¬ (Inst.AttenuateA.attenuateE D hD).active.postClause s args
      ((Inst.AttenuateA.attenuateE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.AttenuateA.attenuateE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.AttenuateA.attenuateE D hD) s args s' a hPI htamper

/-- **`delegate_extract`** — adversarial extraction for `delegate`. -/
theorem delegate_extract
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.Delegate.DelegateArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.Delegate.delegateE D hD) a)
    (hPI : PIBindsDigests S (Inst.Delegate.delegateE D hD) s args s' a) :
    Spec.AuthorityUnattenuated.DelegateSpec s args.del args.recipient args.target s' :=
  (Inst.Delegate.apex_iff_delegateSpec D hD s args s').mp
    (effect2_extract S (Inst.Delegate.delegateE D hD)
      (Inst.Delegate.delegateRestFrameDecodes S D hD hRest) hLog
      (Inst.Delegate.delegateGuardDecodes D hD) s args s' a hsat hPI)

theorem delegate_extract_emitted
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.Delegate.DelegateArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.Delegate.delegateE D hD)) a)
    (hPI : PIBindsDigests S (Inst.Delegate.delegateE D hD) s args s' a) :
    Spec.AuthorityUnattenuated.DelegateSpec s args.del args.recipient args.target s' :=
  (Inst.Delegate.apex_iff_delegateSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.Delegate.delegateE D hD)
      (Inst.Delegate.delegateRestFrameDecodes S D hD hRest) hLog
      (Inst.Delegate.delegateGuardDecodes D hD) name s args s' a hsat hPI)

theorem delegate_extract_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.Delegate.DelegateArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.Delegate.delegateE D hD) s args s' a)
    (htamper : ¬ (Inst.Delegate.delegateE D hD).active.postClause s args
      ((Inst.Delegate.delegateE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.Delegate.delegateE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.Delegate.delegateE D hD) s args s' a hPI htamper

/-- **`delegateAttenA_extract`** — adversarial extraction for `delegateAtten` (the attenuating delegation). -/
theorem delegateAttenA_extract
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.DelegateAttenA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.DelegateAttenA.DelegateAttenArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2 S (Inst.DelegateAttenA.delegateAttenE D hD) a)
    (hPI : PIBindsDigests S (Inst.DelegateAttenA.delegateAttenE D hD) s args s' a) :
    Spec.AuthorityAttenuation.DelegateAttenSpec s args.del args.recv args.t args.keep s' :=
  (Inst.DelegateAttenA.apex_iff_delegateAttenSpec D hD s args s').mp
    (effect2_extract S (Inst.DelegateAttenA.delegateAttenE D hD)
      (Inst.DelegateAttenA.delAttenRestFrameDecodes S D hD hRest) hLog
      (Inst.DelegateAttenA.delAttenGuardDecodes D hD) s args s' a hsat hPI)

theorem delegateAttenA_extract_emitted
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.DelegateAttenA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.DelegateAttenA.DelegateAttenArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.DelegateAttenA.delegateAttenE D hD)) a)
    (hPI : PIBindsDigests S (Inst.DelegateAttenA.delegateAttenE D hD) s args s' a) :
    Spec.AuthorityAttenuation.DelegateAttenSpec s args.del args.recv args.t args.keep s' :=
  (Inst.DelegateAttenA.apex_iff_delegateAttenSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.DelegateAttenA.delegateAttenE D hD)
      (Inst.DelegateAttenA.delAttenRestFrameDecodes S D hD hRest) hLog
      (Inst.DelegateAttenA.delAttenGuardDecodes D hD) name s args s' a hsat hPI)

theorem delegateAttenA_extract_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.DelegateAttenA.DelegateAttenArgs) (s' : RecChainedState)
    (a : Assignment)
    (hPI : PIBindsDigests S (Inst.DelegateAttenA.delegateAttenE D hD) s args s' a)
    (htamper : ¬ (Inst.DelegateAttenA.delegateAttenE D hD).active.postClause s args
      ((Inst.DelegateAttenA.delegateAttenE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.DelegateAttenA.delegateAttenE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.DelegateAttenA.delegateAttenE D hD) s args s' a hPI htamper

/-- **`introduceA_extract`** — adversarial extraction for `introduce` (a `caps` write to `DelegateSpec`). -/
theorem introduceA_extract
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.IntroduceA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.IntroduceA.IntroduceArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.IntroduceA.introduceE D hD) a)
    (hPI : PIBindsDigests S (Inst.IntroduceA.introduceE D hD) s args s' a) :
    Spec.AuthorityUnattenuated.DelegateSpec s args.intro args.recip args.t s' :=
  (Inst.IntroduceA.apex_iff_delegateSpec D hD s args s').mp
    (effect2_extract S (Inst.IntroduceA.introduceE D hD)
      (Inst.IntroduceA.introduceRestFrameDecodes S D hD hRest) hLog
      (Inst.IntroduceA.introduceGuardDecodes D hD) s args s' a hsat hPI)

theorem introduceA_extract_emitted
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.IntroduceA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.IntroduceA.IntroduceArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.IntroduceA.introduceE D hD)) a)
    (hPI : PIBindsDigests S (Inst.IntroduceA.introduceE D hD) s args s' a) :
    Spec.AuthorityUnattenuated.DelegateSpec s args.intro args.recip args.t s' :=
  (Inst.IntroduceA.apex_iff_delegateSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.IntroduceA.introduceE D hD)
      (Inst.IntroduceA.introduceRestFrameDecodes S D hD hRest) hLog
      (Inst.IntroduceA.introduceGuardDecodes D hD) name s args s' a hsat hPI)

theorem introduceA_extract_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.IntroduceA.IntroduceArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.IntroduceA.introduceE D hD) s args s' a)
    (htamper : ¬ (Inst.IntroduceA.introduceE D hD).active.postClause s args
      ((Inst.IntroduceA.introduceE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.IntroduceA.introduceE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.IntroduceA.introduceE D hD) s args s' a hPI htamper

/-- **`revoke_extract`** — adversarial extraction for `revoke`. -/
theorem revoke_extract
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.Revoke.RevokeArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.Revoke.revokeE D hD) a)
    (hPI : PIBindsDigests S (Inst.Revoke.revokeE D hD) s args s' a) :
    Spec.AuthorityRevocation.RevokeSpec s args.holder args.t s' :=
  (Inst.Revoke.apex_iff_revokeSpec D hD s args s').mp
    (effect2_extract S (Inst.Revoke.revokeE D hD)
      (Inst.Revoke.revokeRestFrameDecodes S D hD hRest) hLog
      (Inst.Revoke.revokeGuardDecodes D hD) s args s' a hsat hPI)

theorem revoke_extract_emitted
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.Revoke.RevokeArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.Revoke.revokeE D hD)) a)
    (hPI : PIBindsDigests S (Inst.Revoke.revokeE D hD) s args s' a) :
    Spec.AuthorityRevocation.RevokeSpec s args.holder args.t s' :=
  (Inst.Revoke.apex_iff_revokeSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.Revoke.revokeE D hD)
      (Inst.Revoke.revokeRestFrameDecodes S D hD hRest) hLog
      (Inst.Revoke.revokeGuardDecodes D hD) name s args s' a hsat hPI)

theorem revoke_extract_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.Revoke.RevokeArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.Revoke.revokeE D hD) s args s' a)
    (htamper : ¬ (Inst.Revoke.revokeE D hD).active.postClause s args
      ((Inst.Revoke.revokeE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.Revoke.revokeE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.Revoke.revokeE D hD) s args s' a hPI htamper

/-- **`revokeDelegationA_extract`** — adversarial extraction for `revokeDelegation`. -/
theorem revokeDelegationA_extract
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.RevokeDelegationA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2 S (Inst.RevokeDelegationA.revokeDelegationE D hD) a)
    (hPI : PIBindsDigests S (Inst.RevokeDelegationA.revokeDelegationE D hD) s args s' a) :
    Spec.AuthorityRevocation.RevokeSpec s args.holder args.t s' :=
  (Inst.RevokeDelegationA.apex_iff_revokeSpec D hD s args s').mp
    (effect2_extract S (Inst.RevokeDelegationA.revokeDelegationE D hD)
      (Inst.RevokeDelegationA.revokeRestFrameDecodes S D hD hRest) hLog
      (Inst.RevokeDelegationA.revokeGuardDecodes D hD) s args s' a hsat hPI)

theorem revokeDelegationA_extract_emitted
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Inst.RevokeDelegationA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.RevokeDelegationA.revokeDelegationE D hD)) a)
    (hPI : PIBindsDigests S (Inst.RevokeDelegationA.revokeDelegationE D hD) s args s' a) :
    Spec.AuthorityRevocation.RevokeSpec s args.holder args.t s' :=
  (Inst.RevokeDelegationA.apex_iff_revokeSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.RevokeDelegationA.revokeDelegationE D hD)
      (Inst.RevokeDelegationA.revokeRestFrameDecodes S D hD hRest) hLog
      (Inst.RevokeDelegationA.revokeGuardDecodes D hD) name s args s' a hsat hPI)

theorem revokeDelegationA_extract_rejects_wrong_caps
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState)
    (a : Assignment)
    (hPI : PIBindsDigests S (Inst.RevokeDelegationA.revokeDelegationE D hD) s args s' a)
    (htamper : ¬ (Inst.RevokeDelegationA.revokeDelegationE D hD).active.postClause s args
      ((Inst.RevokeDelegationA.revokeDelegationE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.RevokeDelegationA.revokeDelegationE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.RevokeDelegationA.revokeDelegationE D hD) s args s' a
    hPI htamper

/-! ## §4 — NOTE COMMITMENTS: `noteCreate` (the `commitments` write) and `noteSpend` (the `nullifiers`
write). The digest is the realizable list-Merkle injective pair (`compressNInjective` + `listLeafInjective`),
NOT a `Function.Injective D` — the extractor consumes whatever obligation shape the effect carries. -/

/-- **`noteCreateA_extract`** — adversarial extraction for `noteCreate`. -/
theorem noteCreateA_extract
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Inst.NoteCreateA.RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.NoteCreateA.NoteCreateArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.NoteCreateA.noteCreateE LE cN hN hLE) a)
    (hPI : PIBindsDigests S (Inst.NoteCreateA.noteCreateE LE cN hN hLE) s args s' a) :
    Spec.NoteCommitment.NoteCreateASpec s args.cm args.actor s' :=
  (Inst.NoteCreateA.apex_iff_noteCreateASpec LE cN hN hLE s args s').mp
    (effect2_extract S (Inst.NoteCreateA.noteCreateE LE cN hN hLE)
      (Inst.NoteCreateA.noteCreateRestFrameDecodes S LE cN hN hLE hRest) hLog
      (Inst.NoteCreateA.noteCreateGuardDecodes LE cN hN hLE) s args s' a hsat hPI)

theorem noteCreateA_extract_emitted
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Inst.NoteCreateA.RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.NoteCreateA.NoteCreateArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.NoteCreateA.noteCreateE LE cN hN hLE)) a)
    (hPI : PIBindsDigests S (Inst.NoteCreateA.noteCreateE LE cN hN hLE) s args s' a) :
    Spec.NoteCommitment.NoteCreateASpec s args.cm args.actor s' :=
  (Inst.NoteCreateA.apex_iff_noteCreateASpec LE cN hN hLE s args s').mp
    (effect2_extract_emitted S (Inst.NoteCreateA.noteCreateE LE cN hN hLE)
      (Inst.NoteCreateA.noteCreateRestFrameDecodes S LE cN hN hLE hRest) hLog
      (Inst.NoteCreateA.noteCreateGuardDecodes LE cN hN hLE) name s args s' a hsat hPI)

theorem noteCreateA_extract_rejects_wrong_commitment
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : Inst.NoteCreateA.NoteCreateArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.NoteCreateA.noteCreateE LE cN hN hLE) s args s' a)
    (htamper : ¬ (Inst.NoteCreateA.noteCreateE LE cN hN hLE).active.postClause s args
      ((Inst.NoteCreateA.noteCreateE LE cN hN hLE).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.NoteCreateA.noteCreateE LE cN hN hLE) a :=
  effect2_extract_rejects_wrong_component S (Inst.NoteCreateA.noteCreateE LE cN hN hLE) s args s' a
    hPI htamper

/-- **`noteSpendA_extract`** — adversarial extraction for `noteSpend` (the nullifier grow-gate;
double-spend non-membership). -/
theorem noteSpendA_extract
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.NoteSpendA.NoteSpendArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.NoteSpendA.noteSpendE LE cN hN hLE) a)
    (hPI : PIBindsDigests S (Inst.NoteSpendA.noteSpendE LE cN hN hLE) s args s' a) :
    Spec.NoteNullifier.NoteSpendSpec s args.nf args.actor args.spendProof s' :=
  (Inst.NoteSpendA.apex_iff_noteSpendSpec LE cN hN hLE s args s').mp
    (effect2_extract S (Inst.NoteSpendA.noteSpendE LE cN hN hLE)
      (Inst.NoteSpendA.noteSpendRestFrameDecodes S LE cN hN hLE hRest) hLog
      (Inst.NoteSpendA.noteSpendGuardDecodes LE cN hN hLE) s args s' a hsat hPI)

theorem noteSpendA_extract_emitted
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.NoteSpendA.NoteSpendArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.NoteSpendA.noteSpendE LE cN hN hLE)) a)
    (hPI : PIBindsDigests S (Inst.NoteSpendA.noteSpendE LE cN hN hLE) s args s' a) :
    Spec.NoteNullifier.NoteSpendSpec s args.nf args.actor args.spendProof s' :=
  (Inst.NoteSpendA.apex_iff_noteSpendSpec LE cN hN hLE s args s').mp
    (effect2_extract_emitted S (Inst.NoteSpendA.noteSpendE LE cN hN hLE)
      (Inst.NoteSpendA.noteSpendRestFrameDecodes S LE cN hN hLE hRest) hLog
      (Inst.NoteSpendA.noteSpendGuardDecodes LE cN hN hLE) name s args s' a hsat hPI)

theorem noteSpendA_extract_rejects_wrong_nullifier
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : Inst.NoteSpendA.NoteSpendArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.NoteSpendA.noteSpendE LE cN hN hLE) s args s' a)
    (htamper : ¬ (Inst.NoteSpendA.noteSpendE LE cN hN hLE).active.postClause s args
      ((Inst.NoteSpendA.noteSpendE LE cN hN hLE).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.NoteSpendA.noteSpendE LE cN hN hLE) a :=
  effect2_extract_rejects_wrong_component S (Inst.NoteSpendA.noteSpendE LE cN hN hLE) s args s' a
    hPI htamper

/-! ## §5 — BRIDGE INBOUND MINT: `bridgeMintA` (the cross-chain `bal` credit). -/

/-- **`bridgeMintA_extract`** — adversarial extraction for `bridgeMintA`. -/
theorem bridgeMintA_extract
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.BridgeMintA.BridgeMintArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.BridgeMintA.bridgeMintE D hD) a)
    (hPI : PIBindsDigests S (Inst.BridgeMintA.bridgeMintE D hD) s args s' a) :
    Spec.BridgeInboundMint.InboundMintSpec s args.actor args.cell args.a args.value s' :=
  (Inst.BridgeMintA.apex_iff_inboundMintSpec D hD s args s').mp
    (effect2_extract S (Inst.BridgeMintA.bridgeMintE D hD)
      (Inst.BridgeMintA.bridgeMintRestFrameDecodes S D hD hRest) hLog
      (Inst.BridgeMintA.bridgeMintGuardDecodes D hD) s args s' a hsat hPI)

theorem bridgeMintA_extract_emitted
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (name : String)
    (s : RecChainedState) (args : Inst.BridgeMintA.BridgeMintArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 name (Inst.BridgeMintA.bridgeMintE D hD)) a)
    (hPI : PIBindsDigests S (Inst.BridgeMintA.bridgeMintE D hD) s args s' a) :
    Spec.BridgeInboundMint.InboundMintSpec s args.actor args.cell args.a args.value s' :=
  (Inst.BridgeMintA.apex_iff_inboundMintSpec D hD s args s').mp
    (effect2_extract_emitted S (Inst.BridgeMintA.bridgeMintE D hD)
      (Inst.BridgeMintA.bridgeMintRestFrameDecodes S D hD hRest) hLog
      (Inst.BridgeMintA.bridgeMintGuardDecodes D hD) name s args s' a hsat hPI)

theorem bridgeMintA_extract_rejects_wrong_supply
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.BridgeMintA.BridgeMintArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.BridgeMintA.bridgeMintE D hD) s args s' a)
    (htamper : ¬ (Inst.BridgeMintA.bridgeMintE D hD).active.postClause s args
      ((Inst.BridgeMintA.bridgeMintE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.BridgeMintA.bridgeMintE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.BridgeMintA.bridgeMintE D hD) s args s' a hPI htamper

/-! ## §6 — LIFECYCLE family: `cellSeal`, `cellUnseal` (the `lifecycle` component), `refreshDelegation`
(the `delegations` component), `receiptArchiveLifecycle` (the `lifecycle` archive). Each touches its
component over the matching `RestIffNo*` portal; a satisfying PI-bound trace forces the genuine lifecycle
transition (no forged seal/unseal/refresh/archive). -/

/-- **`cellSealA_extract`** — adversarial extraction for `cellSeal`. -/
theorem cellSealA_extract
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Inst.CellSealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CellSealA.CellSealArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.CellSealA.cellSealE D hD) a)
    (hPI : PIBindsDigests S (Inst.CellSealA.cellSealE D hD) s args s' a) :
    Spec.CellLifecycle.CellSealSpec s args.actor args.cell s' :=
  (Inst.CellSealA.apex_iff_cellSealSpec D hD s args s').mp
    (effect2_extract S (Inst.CellSealA.cellSealE D hD)
      (Inst.CellSealA.cellSealRestFrameDecodes S D hD hRest) hLog
      (Inst.CellSealA.cellSealGuardDecodes D hD) s args s' a hsat hPI)

theorem cellSealA_extract_rejects_wrong_lifecycle
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.CellSealA.CellSealArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.CellSealA.cellSealE D hD) s args s' a)
    (htamper : ¬ (Inst.CellSealA.cellSealE D hD).active.postClause s args
      ((Inst.CellSealA.cellSealE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.CellSealA.cellSealE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.CellSealA.cellSealE D hD) s args s' a hPI htamper

/-- **`cellUnsealA_extract`** — adversarial extraction for `cellUnseal`. -/
theorem cellUnsealA_extract
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Inst.CellUnsealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CellUnsealA.CellUnsealArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (Inst.CellUnsealA.cellUnsealE D hD) a)
    (hPI : PIBindsDigests S (Inst.CellUnsealA.cellUnsealE D hD) s args s' a) :
    Spec.CellLifecycle.CellUnsealSpec s args.actor args.cell s' :=
  (Inst.CellUnsealA.apex_iff_cellUnsealSpec D hD s args s').mp
    (effect2_extract S (Inst.CellUnsealA.cellUnsealE D hD)
      (Inst.CellUnsealA.cellUnsealRestFrameDecodes S D hD hRest) hLog
      (Inst.CellUnsealA.cellUnsealGuardDecodes D hD) s args s' a hsat hPI)

theorem cellUnsealA_extract_rejects_wrong_lifecycle
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.CellUnsealA.CellUnsealArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (Inst.CellUnsealA.cellUnsealE D hD) s args s' a)
    (htamper : ¬ (Inst.CellUnsealA.cellUnsealE D hD).active.postClause s args
      ((Inst.CellUnsealA.cellUnsealE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.CellUnsealA.cellUnsealE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.CellUnsealA.cellUnsealE D hD) s args s' a hPI htamper

/-- **`refreshDelegationA_extract`** — adversarial extraction for `refreshDelegation`. -/
theorem refreshDelegationA_extract
    (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (hRest : Inst.RefreshDelegationA.RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.RefreshDelegationA.RefreshDelegationArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2 S (Inst.RefreshDelegationA.refreshDelegationE D hD) a)
    (hPI : PIBindsDigests S (Inst.RefreshDelegationA.refreshDelegationE D hD) s args s' a) :
    Spec.RefreshDelegation.RefreshDelegationSpec s args.actor args.child s' :=
  (Inst.RefreshDelegationA.apex_iff_refreshDelegationSpec D hD s args s').mp
    (effect2_extract S (Inst.RefreshDelegationA.refreshDelegationE D hD)
      (Inst.RefreshDelegationA.refreshDelegationRestFrameDecodes S D hD hRest) hLog
      (Inst.RefreshDelegationA.refreshDelegationGuardDecodes D hD) s args s' a hsat hPI)

theorem refreshDelegationA_extract_rejects_wrong_delegations
    (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.RefreshDelegationA.RefreshDelegationArgs) (s' : RecChainedState)
    (a : Assignment)
    (hPI : PIBindsDigests S (Inst.RefreshDelegationA.refreshDelegationE D hD) s args s' a)
    (htamper : ¬ (Inst.RefreshDelegationA.refreshDelegationE D hD).active.postClause s args
      ((Inst.RefreshDelegationA.refreshDelegationE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.RefreshDelegationA.refreshDelegationE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.RefreshDelegationA.refreshDelegationE D hD) s args s' a
    hPI htamper

/-- **`receiptArchiveLifecycleA_extract`** — adversarial extraction for `receiptArchiveLifecycle`. -/
theorem receiptArchiveLifecycleA_extract
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : Inst.ReceiptArchiveLifecycleA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.ReceiptArchiveLifecycleA.ReceiptArchiveArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2 S (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD) a)
    (hPI : PIBindsDigests S (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD) s args s' a) :
    Spec.CellStateAudit.ReceiptArchiveLifecycleSpec s args.actor args.cell s' :=
  (Inst.ReceiptArchiveLifecycleA.apex_iff_ReceiptArchiveLifecycleSpec D hD s args s').mp
    (effect2_extract S (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD)
      (Inst.ReceiptArchiveLifecycleA.archiveRestFrameDecodes S D hD hRest) hLog
      (Inst.ReceiptArchiveLifecycleA.archiveGuardDecodes D hD) s args s' a hsat hPI)

theorem receiptArchiveLifecycleA_extract_rejects_wrong_lifecycle
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Inst.ReceiptArchiveLifecycleA.ReceiptArchiveArgs) (s' : RecChainedState)
    (a : Assignment)
    (hPI : PIBindsDigests S (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD) s args s' a)
    (htamper : ¬ (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD).active.postClause s args
      ((Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD).view.toKernel s')) :
    ¬ satisfiedE2 S (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD) a :=
  effect2_extract_rejects_wrong_component S (Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE D hD)
    s args s' a hPI htamper

/-! ## §7 — axiom-hygiene tripwires. Whitelist `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms transfer_extract
#assert_axioms transfer_extract_emitted
#assert_axioms transfer_extract_rejects_wrong_ledger
#assert_axioms balanceA_extract
#assert_axioms balanceA_extract_rejects_wrong_ledger
#assert_axioms burnA_extract
#assert_axioms burnA_extract_emitted
#assert_axioms burnA_extract_rejects_wrong_supply
#assert_axioms attenuateA_extract
#assert_axioms attenuateA_extract_rejects_wrong_caps
#assert_axioms delegate_extract
#assert_axioms delegate_extract_rejects_wrong_caps
#assert_axioms delegateAttenA_extract
#assert_axioms delegateAttenA_extract_rejects_wrong_caps
#assert_axioms introduceA_extract
#assert_axioms introduceA_extract_rejects_wrong_caps
#assert_axioms revoke_extract
#assert_axioms revoke_extract_rejects_wrong_caps
#assert_axioms revokeDelegationA_extract
#assert_axioms revokeDelegationA_extract_rejects_wrong_caps
#assert_axioms noteCreateA_extract
#assert_axioms noteCreateA_extract_rejects_wrong_commitment
#assert_axioms noteSpendA_extract
#assert_axioms noteSpendA_extract_rejects_wrong_nullifier
#assert_axioms bridgeMintA_extract
#assert_axioms bridgeMintA_extract_rejects_wrong_supply
#assert_axioms cellSealA_extract
#assert_axioms cellSealA_extract_rejects_wrong_lifecycle
#assert_axioms cellUnsealA_extract
#assert_axioms cellUnsealA_extract_rejects_wrong_lifecycle
#assert_axioms refreshDelegationA_extract
#assert_axioms refreshDelegationA_extract_rejects_wrong_delegations
#assert_axioms receiptArchiveLifecycleA_extract
#assert_axioms receiptArchiveLifecycleA_extract_rejects_wrong_lifecycle

end Dregg2.Circuit.WitnessExtractPerEffect
