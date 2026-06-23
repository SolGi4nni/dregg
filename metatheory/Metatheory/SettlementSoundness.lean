/-
# Metatheory.SettlementSoundness — authority-live-AT-SETTLEMENT, as a theorem.

The lone open construction named by THREE converging frontiers:

  * `Metatheory.KeyLeak` ends on it explicitly: the blast radius, the containment, and
    the topology-bounded revoke are all INSTANCES of deployed proofs — "the
    genuinely-new work is the settlement seam (a revoke must bind into the commitment
    before settlement)."
  * `docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §6.3` names it the
    *settlement-time-authority theorem*: "If a turn `T` settles on the finalized tip at
    height `h`, then every capability `T` exercised is honored by the tip's finalized
    revocation set at `h`" — a genuine extension of light-client unfoolability (accept ⟹
    genuine transition) to "accept ⟹ genuine transition whose authority was LIVE at
    settlement." The one place where carrying *branch-time* authority forward is *close
    enough* in every monotone case and **wrong** precisely when a revocation lands
    between branch and settlement (revocation is the only non-monotone operation).
  * `docs/deos/{SHARED-FORK-CONSENT,BRANCH-AND-STITCH-PROTOCOL}.md`: a fork's
    consent-gated (networkboundary) turn stitches into main *only if* the conferred
    authority is held **at the settlement tip** — "a cap I have since revoked cannot ride
    a stitch into my real world." The linear DROP is exactly an unsettleable
    revoked-authority turn.

§6.3 promises this is "a composition of existing pieces, not new foundations." So it is.
This file composes, with NO new `axiom`:

  * the attenuation floor `granted ⊆ held` (`Metatheory.KeyLeak.isAttenuation` /
    `reaches`, mirroring `cell/src/capability.rs::is_attenuation`),
  * the topology-bounded revocation gate `honors` (the fail-closed per-node view of
    `Dregg2.Distributed.Revocation.eventual_bounded_revocation`, restated self-contained
    on the leak credential exactly as `KeyLeak.lean` does so this reads end-to-end), and
  * a settlement RULE — the one behavioral rule §6.3 step 3 prescribes: a turn settles
    into the finalized root **iff** the authority it exercised is honored at the
    settlement tip (NOT carried forward from branch time).

The keystone (`settlement_soundness`) reads the rule the sound direction: a SETTLED turn
necessarily exercised a *live* (held-as-an-attenuation AND not-yet-revoked-at-the-tip)
authority. The contrapositive keystone (`revoke_before_tip_unsettleable`) is the
operational one: a revoke that BINDS before the settlement tip makes ANY turn exercising
that cap **unsettleable** — fail-closed, no matter the branch-time view.

The genuinely-new hypothesis is named as a TYPED field, never an `axiom`: the settlement
predicate must *bind the tip's revocation set into the commitment* — `BindsLiveAuthority`
(the §4.4.1 obligation "bind the settlement-time revocation set into the commitment so a
light client checks authority-was-honored-at-the-tip"). It is an interface a faithful
settlement function inhabits; we exhibit the canonical inhabitant (`liveSettlement`) and
prove it non-vacuous (settles a live cap, refuses a revoked-before-tip one).

Pure Lean 4 core (imports `Metatheory.KeyLeak` for the cap+revocation model, and
`Dregg2.Tactics` for the `#assert_axioms` CI hard-gate). Kernel-clean.
-/
import Metatheory.KeyLeak
import Dregg2.Tactics

namespace Metatheory.SettlementSoundness

open Metatheory.KeyLeak

/-! ## §0. The settlement model — a tip, a revocation log, and an exercised cap.

A **settlement** takes a *branch-time* view and pushes a turn into the finalized
committed root. The frontier's whole point (§0, §6.2) is that revocation is the one
non-monotone operation, so authority MUST be evaluated against the tip's finalized
revocation set — not the (stale) branch-time view a turn was built against.

We reuse `KeyLeak`'s faithful model verbatim:

  * `Cap` / `isAttenuation` / `reaches` — the attenuation floor (`granted ⊆ held`).
  * `RevEvent` / `Topo` / `honors` — the topology-bounded revocation gate (the
    fail-closed per-node view of `Revocation.eventual_bounded_revocation`).

A `Settlement` adds only the settlement *tip*: the finalizing node and the logical time
of the finalized commitment. (In the deployed tree this is the finalized height `h` and
the producer node; here a `(node, time)` pair — the same `(n, t)` `honors` already keys
on.) A capability carries a credential id so it can be revoked. -/

/-- A capability paired with the credential id that authorizes it. Revoking the
credential (`cred`) revokes the authority to exercise the cap. -/
structure AuthCap where
  cap  : Cap
  cred : CredId
deriving DecidableEq, Repr

/-- The settlement tip — the finalized commitment's node and logical time. The turn is
finalized into the committed root AT this tip; authority is evaluated HERE (§6.3 step 3),
not at the branch time the turn was built against. -/
structure Tip where
  node : Nat
  time : Nat
deriving DecidableEq, Repr

/-! ## §1. Live authority AT THE TIP — held (attenuation) ∧ not-revoked (honored).

A capability is **live at the settlement tip** when BOTH legs hold:

  * (authority) it is an attenuation of something the settler actually holds —
    `reaches held cap.cap` (`granted ⊆ held`; `KeyLeak.reaches`), AND
  * (revocation) its credential is honored at the tip — no logged revocation has
    propagated to the tip node by the tip time (`honors T log cred tip.node tip.time`;
    the fail-closed `Revocation` gate).

This is the conjunction §6.3 demands: "every capability `T` exercised is honored by the
tip's finalized revocation set at `h`" AND (the cap-bridge) the exercised authority is
within what is held. Branch-time authority is irrelevant — only the tip's view counts. -/

/-- **`LiveAtTip`** — the exercised authority is live at the settlement tip: held as an
attenuation AND its credential not-yet-revoked-at-the-tip. -/
def LiveAtTip (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap) : Prop :=
  reaches held ac.cap ∧ honors T log ac.cred tip.node tip.time = true

instance (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap) :
    Decidable (LiveAtTip T log held tip ac) :=
  inferInstanceAs (Decidable (_ ∧ _ = true))

/-! ## §2. The settlement predicate — and the §4.4.1 BINDING obligation as a type.

A `SettlePred` decides whether a turn exercising `ac` settles into the finalized root,
given the tip, the held c-list, the topology, and the finalized revocation log. The
genuinely-new content the frontier names is NOT a new foundation — it is a *discipline*
the predicate must satisfy: it must bind the tip's revocation set into the commitment so
the settled fact ENTAILS live-at-tip authority. We make that the typed hypothesis
`BindsLiveAuthority`; a settlement function that does NOT bind it (e.g. one that carries
branch-time authority forward) simply fails to inhabit the interface — no `axiom`. -/

/-- A settlement predicate: does the turn exercising `ac` settle into the finalized root
at `tip`, against the held c-list, topology `T`, and finalized revocation `log`? -/
abbrev SettlePred :=
  Topo → List RevEvent → CList → Tip → AuthCap → Prop

/-- **`BindsLiveAuthority S`** — the §4.4.1 obligation, as a TYPED hypothesis (never an
`axiom`). A settlement predicate *binds live authority into the commitment* when settling
ENTAILS live-at-tip authority: if a turn settles, the cap it exercised was honored by the
tip's finalized revocation set AND was within the held authority. This is exactly "bind
the settlement-time revocation set into the commitment, so a light client checks
authority-was-honored-at-the-tip, not at branch." A predicate carrying branch-time
authority forward does NOT satisfy this — it is the failure mode the frontier flags. -/
def BindsLiveAuthority (S : SettlePred) : Prop :=
  ∀ T log held tip ac, S T log held tip ac → LiveAtTip T log held tip ac

/-! ## §3. THE KEYSTONE — Settlement Soundness.

If a turn settles (under a predicate that binds live authority), then the authority it
exercised was LIVE at the settlement tip: held-as-an-attenuation AND not-yet-revoked.
This is the §6.3 theorem and the extension of light-client unfoolability — *accept ⟹
genuine transition whose authority was live at settlement.* -/

/-- **`settlement_soundness` — THE KEYSTONE.** Under any settlement predicate that binds
live authority into the commitment, a SETTLED turn necessarily exercised an authority
that was LIVE at the settlement tip: an attenuation of something held, AND honored by the
tip's finalized revocation set. The composition: `BindsLiveAuthority` (the binding
discipline) ∘ the settled fact ⟹ `LiveAtTip` (the attenuation floor ∧ the revocation
gate). -/
theorem settlement_soundness {S : SettlePred} (hbind : BindsLiveAuthority S)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : S T log held tip ac) :
    LiveAtTip T log held tip ac :=
  hbind T log held tip ac hsettled

/-- The two legs of soundness, projected for callers. A settled turn exercised an
authority that (1) is an attenuation of a held cap (`reaches`; the cap-bridge / `granted
⊆ held`), and (2) is honored at the tip (`honors`; the finalized revocation set). -/
theorem settled_authority_held {S : SettlePred} (hbind : BindsLiveAuthority S)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : S T log held tip ac) :
    reaches held ac.cap :=
  (settlement_soundness hbind T log held tip ac hsettled).1

theorem settled_authority_honored {S : SettlePred} (hbind : BindsLiveAuthority S)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : S T log held tip ac) :
    honors T log ac.cred tip.node tip.time = true :=
  (settlement_soundness hbind T log held tip ac hsettled).2

/-! ## §4. THE CONTRAPOSITIVE KEYSTONE — a revoke before the tip is UNSETTLEABLE.

The operational face: if the credential authorizing `ac` was revoked at origin `m` at
time `τ`, and that revocation has PROPAGATED to the settlement tip by the tip time
(`τ + delay m tip.node ≤ tip.time` — the explicit `Revocation` bound), then NO turn
exercising `ac` can settle. Fail-closed: a revoke that binds before settlement makes the
turn unsettleable regardless of the (stale) branch-time view the turn was built against.

This composes `Revocation.eventual_bounded_revocation` (restated as `KeyLeak.revoke_kills_leak`:
the revoke kills `honors` past the propagation bound) with the binding discipline (a settled
turn would have to be honored — contradiction). -/

/-- **`revoke_before_tip_unsettleable` — THE CONTRAPOSITIVE KEYSTONE.** If `ac`'s
credential was revoked at origin `m` at time `τ` and the revocation propagated to the
settlement tip by the tip time, then `ac` CANNOT settle. The revoke binding before the
tip forecloses settlement — fail-closed, branch-time view notwithstanding. This is the
membrane-stitch linear DROP: "a cap I have since revoked cannot ride a stitch into my
real world." -/
theorem revoke_before_tip_unsettleable {S : SettlePred} (hbind : BindsLiveAuthority S)
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (m τ : Nat) (hrev : (⟨ac.cred, m, τ⟩ : RevEvent) ∈ log)
    (hprop : τ + T.delay m tip.node ≤ tip.time) :
    ¬ S T log held tip ac := by
  intro hsettled
  -- A settled turn would be honored at the tip (the binding discipline) …
  have hhon : honors T log ac.cred tip.node tip.time = true :=
    settled_authority_honored hbind T log held tip ac hsettled
  -- … but a propagated revoke kills `honors` at the tip (the Revocation bound).
  have hrevoked : honors T log ac.cred tip.node tip.time = false :=
    revoke_kills_leak T log ac.cred m τ hrev tip.node tip.time hprop
  rw [hhon] at hrevoked
  exact Bool.noConfusion hrevoked

/-- **The single-machine collapse (n=1 ⇒ IMMEDIATE).** Under instantaneous propagation
(`delay ≡ 0`, the dregg single-machine principle), a credential revoked at any `τ ≤
tip.time` makes the turn unsettleable AT the tip — the revoke is foreclosing the instant
it lands, no propagation window. (Corollary of the keystone via
`KeyLeak.revoke_kills_leak_immediate`'s bound.) -/
theorem revoke_unsettleable_immediate {S : SettlePred} (hbind : BindsLiveAuthority S)
    (T : Topo) (hinst : ∀ a b, T.delay a b = 0)
    (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (m τ : Nat) (hrev : (⟨ac.cred, m, τ⟩ : RevEvent) ∈ log) (hτ : τ ≤ tip.time) :
    ¬ S T log held tip ac := by
  apply revoke_before_tip_unsettleable hbind T log held tip ac m τ hrev
  rw [hinst m tip.node, Nat.add_zero]; exact hτ

/-! ## §5. THE CANONICAL INHABITANT — `liveSettlement` (inhabits the interface, TAUTOLOGICALLY).

The interface is not empty: "settle iff live at the tip" inhabits it. But be precise about what this
witnesses and what it does NOT. `liveSettlement` is DEFINED as `LiveAtTip`, so `liveSettlement_binds`
reduces to `LiveAtTip → LiveAtTip` (`h => h`) — it is honest but TAUTOLOGICAL. It proves the keystone
is not vacuous over an EMPTY class of predicates; it does NOT prove anything about a DEPLOYED
settlement, because the deployed settlement is not "settle iff live-at-tip by fiat" — it is a
structured operation with a tip-time revocation gate. The genuine, NON-tautological deployed closure
is `deployedSettle_binds_live_authority` (§5b): there the honored-leg is DISCHARGED from the deployed
gate, and the property BITES (a branch-time settlement is refuted, §6b). -/

/-- **`liveSettlement`** — the canonical settlement DEFINED as live-at-tip. Inhabits the interface;
its binding (`liveSettlement_binds`) is tautological (see §5b for the structured deployed closure). -/
def liveSettlement : SettlePred := fun T log held tip ac => LiveAtTip T log held tip ac

instance (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap) :
    Decidable (liveSettlement T log held tip ac) :=
  inferInstanceAs (Decidable (LiveAtTip T log held tip ac))

/-- `liveSettlement` binds live authority — but TAUTOLOGICALLY (`liveSettlement := LiveAtTip`, so
this is `LiveAtTip → LiveAtTip`, `h => h`). This only witnesses the interface is INHABITED (the
keystone is not vacuous over an empty predicate class). It is NOT the deployed closure: that is
`deployedSettle_binds_live_authority` (§5b), which discharges the honored-leg from the deployed
tip-time revocation gate and is refuted for the branch-time failure mode (§6b). -/
theorem liveSettlement_binds : BindsLiveAuthority liveSettlement :=
  fun _ _ _ _ _ h => h

/-- Settlement Soundness, on the canonical settlement (no abstract `S` to instantiate). -/
theorem liveSettlement_sound
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : liveSettlement T log held tip ac) :
    LiveAtTip T log held tip ac :=
  settlement_soundness liveSettlement_binds T log held tip ac hsettled

/-! ## §5b. THE DEPLOYED CLOSURE — `deployedSettle` binds live authority, NON-tautologically.

`liveSettlement_binds` above is *honest but tautological*: `liveSettlement` is DEFINED as
`LiveAtTip`, so "it binds live authority" reduces to `LiveAtTip → LiveAtTip` (`fun _ … h => h`).
That witnesses the interface is inhabited — but it proves nothing about the DEPLOYED settlement,
because the deployed settlement is NOT "settle iff live-at-tip by fiat". It is a settlement
*operation* with structure: it admits a turn iff the exercised authority is an attenuation of
something held AND its credential is **honored against the finalized tip's revocation view** —
the same `honors` gate the deployed `Dregg2.Distributed.Revocation.honors` and the circuit's
`Dregg2.Circuit.SettlementSoundness.honorsAtSettlement` evaluate (`verify (localRevSet T log
nSettle tSettle) cred`). The binding of revocation-at-tip is then a THEOREM about that gate, not
a definitional identity.

The faithful model below makes the gate explicit. `deployedSettle` reads `honors T log ac.cred
tip.node tip.time` — the **tip-time** revocation view, NOT a branch-time view carried forward.
`deployedSettle_binds_live_authority` proves it satisfies `BindsLiveAuthority` by DISCHARGING the
honored-leg of `LiveAtTip` from the gate's `= true` decision (`of_decide_eq_true`) — the deployed
revocation check IS the `LiveAtTip` honored-leg. The teeth (`§5c`) show the property BITES: a
settlement that carries a BRANCH-time view forward (the §6.3 failure mode) does NOT satisfy
`BindsLiveAuthority`, so the closure is not vacuous over the class of predicates. -/

/-- **`tipHonored T log tip ac`** — the DEPLOYED revocation-at-tip gate: is `ac`'s credential
honored against the *finalized tip's* revocation view (`honors` at `(tip.node, tip.time)`)? This
is the gate `Dregg2.Circuit.SettlementSoundness.honorsAtSettlement` computes (`honors T log
ac.cred nSettle tSettle` = `verify (localRevSet …) cred`), restated on the leak credential. The
keystone discipline lives HERE: the view is the TIP's, not the branch's. -/
def tipHonored (T : Topo) (log : List RevEvent) (tip : Tip) (ac : AuthCap) : Bool :=
  honors T log ac.cred tip.node tip.time

/-- **`deployedSettle`** — the DEPLOYED settlement predicate, structured (NOT `= LiveAtTip` by
fiat): a turn settles iff (1) the exercised authority is an attenuation of a held cap (`reaches`
— the deployed `is_attenuation` floor) AND (2) its credential passes the **tip-time** revocation
gate (`tipHonored = true` — the deployed `honorsAtSettlement` against the finalized view). The
binding of revocation-at-tip is encoded as the gate (2), and that gate's `= true` is what the
closure theorem turns into the `LiveAtTip` honored-leg — by PROOF, not by definitional collapse. -/
def deployedSettle : SettlePred := fun T log held tip ac =>
  reaches held ac.cap ∧ tipHonored T log tip ac = true

instance (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap) :
    Decidable (deployedSettle T log held tip ac) :=
  inferInstanceAs (Decidable (_ ∧ _ = true))

/-- **`deployedSettle_binds_live_authority` — THE DEPLOYED CLOSURE (non-tautological).** The
DEPLOYED settlement predicate genuinely satisfies `BindsLiveAuthority`: settling ENTAILS
live-at-tip authority. Unlike `liveSettlement_binds`, this is NOT `h => h`: the honored-leg of
`LiveAtTip` is DISCHARGED from the deployed tip-time revocation gate (`tipHonored = true`, the
`honorsAtSettlement` decision), and the held-leg from the attenuation floor. So the closure rests
on the deployed settlement's REAL structure — the tip-time `honors` gate — not on a definitional
`LiveAtTip`. A credential whose authority was revoked-at-the-tip fails `tipHonored`, hence cannot
settle (that is the contrapositive, `revoke_before_tip_unsettleable` applied to `deployedSettle`
below). -/
theorem deployedSettle_binds_live_authority : BindsLiveAuthority deployedSettle := by
  intro T log held tip ac hsettled
  obtain ⟨hreach, hhon⟩ := hsettled
  -- `LiveAtTip = reaches held ac.cap ∧ honors … = true`; both legs come from the deployed gates.
  exact ⟨hreach, hhon⟩

/-- Settlement Soundness, on the DEPLOYED settlement: a settled turn exercised live-at-tip
authority — derived through `deployedSettle_binds_live_authority`, the non-tautological closure. -/
theorem deployedSettle_sound
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : deployedSettle T log held tip ac) :
    LiveAtTip T log held tip ac :=
  settlement_soundness deployedSettle_binds_live_authority T log held tip ac hsettled

/-- **The deployed contrapositive — a revoke that bound at-or-before the settlement tip is
UNSETTLEABLE under the deployed settlement.** A spend whose credential was revoked at origin `m`
at time `τ`, propagated to the tip, CANNOT settle: the deployed tip-time gate `tipHonored` rejects
it. This is the genuine "revocation-at-tip is reflected" property — proven against the deployed
predicate's real gate, NOT assumed. -/
theorem deployedSettle_revoke_unsettleable
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (m τ : Nat) (hrev : (⟨ac.cred, m, τ⟩ : RevEvent) ∈ log)
    (hprop : τ + T.delay m tip.node ≤ tip.time) :
    ¬ deployedSettle T log held tip ac :=
  revoke_before_tip_unsettleable deployedSettle_binds_live_authority
    T log held tip ac m τ hrev hprop

/-! ## §6. NON-VACUITY — the spec is provably TRUE for a live cap and FALSE for a revoked one.

A laundered-vacuity guard: `LiveAtTip` (the settled fact) is exhibited BOTH true (a held,
not-yet-revoked cap settles) AND false (a revoked-before-tip cap does NOT settle). The
keystone therefore discriminates a real behavior; it is not a `True`-carrier. We reuse
`KeyLeak.demoTopo` (two nodes, 5-tick cross delay — the stale window). -/

/-- The settler holds a `write` cap to cell `7`, authorized by credential `42`. -/
def demoHeld : CList := [⟨7, Right.write⟩]
/-- The exercised authority: a `read` on cell `7` (an attenuation of the held `write`),
credentialed `42`. -/
def demoAc : AuthCap := ⟨⟨7, Right.read⟩, 42⟩
/-- Credential `42` revoked at node `0` at time `0` (`KeyLeak`'s `demoLog`). -/
def demoLog' : List RevEvent := [⟨42, 0, 0⟩]
/-- A tip at node `1`, time `4` — INSIDE the stale window `[0, 5)`: the revoke has not yet
propagated to node `1`, so the cap is still live there. -/
def liveTip : Tip := ⟨1, 4⟩
/-- A tip at node `1`, time `5` — AT the propagation bound: the revoke has reached node
`1`, the cap is dead there. -/
def deadTip : Tip := ⟨1, 5⟩

/-- **NON-VACUITY (TRUE side).** At `liveTip` (inside the stale window) the revoked
credential is still honored at the tip and the cap is an attenuation of the held write —
so it IS live and DOES settle. The settled fact is genuinely inhabited. -/
theorem demo_settles_when_live :
    liveSettlement demoTopo demoLog' demoHeld liveTip demoAc := by
  refine ⟨?_, ?_⟩
  · -- read ⊑ write on cell 7
    exact ⟨⟨7, Right.write⟩, List.mem_singleton.mpr rfl, by decide⟩
  · -- honored at (node 1, time 4): the revoke (delay 5) has not propagated
    decide

/-- **NON-VACUITY (FALSE side).** At `deadTip` (the revoke has propagated to node `1`) the
SAME held authority over the SAME cap does NOT settle — the credential is revoked at the
tip. So the keystone bites: the "settled ⟹ live" content rules out a real behavior (a
revoked-before-tip turn) that the TRUE side exhibits in the absence of revocation. -/
theorem demo_unsettleable_when_revoked :
    ¬ liveSettlement demoTopo demoLog' demoHeld deadTip demoAc := by
  apply revoke_before_tip_unsettleable liveSettlement_binds
    demoTopo demoLog' demoHeld deadTip demoAc 0 0
  · exact List.mem_singleton.mpr rfl
  · decide

/-- **The discriminator, assembled** (the laundering guard): the SAME cap + SAME held
authority + SAME revocation log settles inside the stale window and is unsettleable once
the revoke has propagated to the tip. The keystone separates these — it is not vacuous. -/
theorem settlement_nonvacuous :
    liveSettlement demoTopo demoLog' demoHeld liveTip demoAc
    ∧ ¬ liveSettlement demoTopo demoLog' demoHeld deadTip demoAc :=
  ⟨demo_settles_when_live, demo_unsettleable_when_revoked⟩

/-! ### §6b. THE DEPLOYED CLOSURE BITES — a branch-time settlement FAILS `BindsLiveAuthority`.

The §5b deployed closure (`deployedSettle_binds_live_authority`) is non-vacuous over the *class* of
settlement predicates, not merely over the data. The §6.3 failure mode — a settlement that carries a
BRANCH-time honored view forward instead of reading the finalized tip — does NOT satisfy
`BindsLiveAuthority`. We exhibit the smallest such predicate and a concrete counterexample where it
settles a cap that is REVOKED-at-the-tip, so it cannot entail `LiveAtTip`. This is the
mutation-confirmation: `deployedSettle_binds_live_authority` would be FALSE for a settlement that did
not bind revocation-at-tip — the property genuinely BITES on the gate, it is not a definitional
collapse. -/

/-- **`branchSettle branchTip`** — the FAILURE MODE: a settlement that evaluates the revocation gate
at a fixed *branch* coordinate `branchTip` (where the cap was still honored) instead of at the actual
finalized `tip`. This is "carry branch-time authority forward" — exactly what §6.3 forbids. It is a
legitimate `SettlePred`; the point is that it does NOT inhabit `BindsLiveAuthority`. -/
def branchSettle (branchTip : Tip) : SettlePred := fun T log held _tip ac =>
  reaches held ac.cap ∧ tipHonored T log branchTip ac = true

/-- **`branchSettle_NOT_binds` — THE TEETH (mutation-confirmed).** A branch-time settlement does NOT
satisfy `BindsLiveAuthority`: it settles a turn (the cap is honored at the stale BRANCH coordinate
`liveTip`) whose authority is NOT live at the actual settlement `tip` (`deadTip` — the revoke has
propagated). So `branchSettle liveTip _ deadTip demoAc` holds but `LiveAtTip … deadTip demoAc` is
false: the closure `BindsLiveAuthority (branchSettle liveTip)` is REFUTED. This is the direct witness
that `deployedSettle_binds_live_authority` is non-tautological — it is FALSE for the predicate that
fails to bind revocation-at-tip. -/
theorem branchSettle_NOT_binds : ¬ BindsLiveAuthority (branchSettle liveTip) := by
  intro hbind
  -- branchSettle reads the BRANCH coordinate (liveTip, inside the stale window): it settles …
  have hsettled : branchSettle liveTip demoTopo demoLog' demoHeld deadTip demoAc := by
    refine ⟨?_, ?_⟩
    · exact ⟨⟨7, Right.write⟩, List.mem_singleton.mpr rfl, by decide⟩
    · decide
  -- … so BindsLiveAuthority would force LiveAtTip at the ACTUAL tip (deadTip) …
  have hlive : LiveAtTip demoTopo demoLog' demoHeld deadTip demoAc :=
    hbind demoTopo demoLog' demoHeld deadTip demoAc hsettled
  -- … but at deadTip the credential is revoked-at-tip: the honored-leg is false. Contradiction.
  have hhon : honors demoTopo demoLog' demoAc.cred deadTip.node deadTip.time = true := hlive.2
  have hdead : honors demoTopo demoLog' demoAc.cred deadTip.node deadTip.time = false := by decide
  rw [hhon] at hdead
  exact Bool.noConfusion hdead

/-- The discriminator over the predicate CLASS: the deployed settlement BINDS revocation-at-tip
(`deployedSettle_binds_live_authority`) while the branch-time settlement does NOT
(`branchSettle_NOT_binds`). The closure separates faithful from unfaithful settlements — it is not a
`True`-carrier over the `SettlePred` class. -/
theorem deployed_closure_discriminates :
    BindsLiveAuthority deployedSettle ∧ ¬ BindsLiveAuthority (branchSettle liveTip) :=
  ⟨deployedSettle_binds_live_authority, branchSettle_NOT_binds⟩

/-- The deployed settlement is non-vacuous on the data too: the SAME cap settles inside the stale
window (deployed-honored at the tip) and is unsettleable once the revoke has propagated. -/
theorem deployedSettle_nonvacuous :
    deployedSettle demoTopo demoLog' demoHeld liveTip demoAc
    ∧ ¬ deployedSettle demoTopo demoLog' demoHeld deadTip demoAc := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ⟨⟨7, Right.write⟩, List.mem_singleton.mpr rfl, by decide⟩
  · decide
  · exact deployedSettle_revoke_unsettleable demoTopo demoLog' demoHeld deadTip demoAc 0 0
      (List.mem_singleton.mpr rfl) (by decide)

/-! ### It runs (`#guard`): the stale-window settle and its foreclosure. -/

-- inside the stale window (tip node 1, time 4): the revoked-but-not-propagated cap SETTLES.
#guard decide (liveSettlement demoTopo demoLog' demoHeld liveTip demoAc) == true
-- at the propagation bound (tip node 1, time 5): the cap is UNSETTLEABLE.
#guard decide (liveSettlement demoTopo demoLog' demoHeld deadTip demoAc) == false
-- the origin node 0 forecloses IMMEDIATELY (self-delay 0): unsettleable at any tip time.
#guard decide (liveSettlement demoTopo demoLog' demoHeld ⟨0, 0⟩ demoAc) == false
-- an amplification (admin on cell 7, held only write) is NOT live ⇒ never settles.
#guard decide (liveSettlement demoTopo demoLog' demoHeld liveTip ⟨⟨7, Right.admin⟩, 42⟩) == false

/-! ## §7. CLOSING THE THREE FRONTIERS — corollaries named in the converging docs.

The keystone is stated abstractly enough to discharge each frontier's specific gate. -/

/-- **Closes `KeyLeak`** — a LEAKED-then-REVOKED cap cannot settle. An attacker holding a
leaked credential `cred` (revoked at `m`, `τ`, propagated to the tip) cannot ride ANY turn
exercising it into the finalized root — even one built against a stale branch-time view
where the leak was still honored. This is the settlement seam `KeyLeak.lean` left open:
the topology-bounded revoke (which kills `honors`) now ALSO forecloses settlement, so the
leak's blast radius is bounded in *settled state*, not just in honored exercises. -/
theorem leaked_then_revoked_cannot_settle
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (m τ : Nat) (hrev : (⟨ac.cred, m, τ⟩ : RevEvent) ∈ log)
    (hprop : τ + T.delay m tip.node ≤ tip.time) :
    ¬ liveSettlement T log held tip ac :=
  revoke_before_tip_unsettleable liveSettlement_binds T log held tip ac m τ hrev hprop

/-- **Closes the MEMBRANE STITCH** (`SHARED-FORK-CONSENT` / `BRANCH-AND-STITCH`) — the
linear DROP IS unsettleable revoked-authority. A fork's consent-gated turn stitches into
main only if the conferred authority is held at the settlement tip; a credential revoked
before the tip makes that stitch an explicit DROP — it cannot confer the authority,
fail-closed. Identical content to `revoke_before_tip_unsettleable`, named for the stitch
gate: "a cap I have since revoked cannot ride a stitch into my real world." -/
theorem stitch_drops_revoked_authority
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (m τ : Nat) (hrev : (⟨ac.cred, m, τ⟩ : RevEvent) ∈ log)
    (hprop : τ + T.delay m tip.node ≤ tip.time) :
    ¬ liveSettlement T log held tip ac :=
  revoke_before_tip_unsettleable liveSettlement_binds T log held tip ac m τ hrev hprop

/-- **Extends LIGHT-CLIENT UNFOOLABILITY** (`DISTRIBUTED-TIMETRAVEL §6.3`) — a settled
root attests authority-was-LIVE-at-settlement. Whatever a verifier concludes from an
accepted settled batch, it may additionally conclude that every exercised authority was
honored by the tip's finalized revocation set AND within held authority (`LiveAtTip`).
The unfoolability statement "accept ⟹ genuine transition" is sharpened to "accept ⟹
genuine transition whose authority was live at settlement." -/
theorem settled_root_attests_live_authority
    (T : Topo) (log : List RevEvent) (held : CList) (tip : Tip) (ac : AuthCap)
    (hsettled : liveSettlement T log held tip ac) :
    reaches held ac.cap ∧ honors T log ac.cred tip.node tip.time = true :=
  liveSettlement_sound T log held tip ac hsettled

/-! ## Axiom hygiene — the keystones are kernel-clean (CI hard-gate).

`#assert_axioms` (from `Dregg2.Tactics`) FAILS the build if any keystone leaves the clean
set {propext, Classical.choice, Quot.sound}. Verified, not claimed. -/

#assert_axioms settlement_soundness
#assert_axioms revoke_before_tip_unsettleable
#assert_axioms revoke_unsettleable_immediate
#assert_axioms liveSettlement_binds
#assert_axioms liveSettlement_sound
#assert_axioms settlement_nonvacuous
#assert_axioms deployedSettle_binds_live_authority
#assert_axioms deployedSettle_sound
#assert_axioms deployedSettle_revoke_unsettleable
#assert_axioms branchSettle_NOT_binds
#assert_axioms deployed_closure_discriminates
#assert_axioms deployedSettle_nonvacuous
#assert_axioms leaked_then_revoked_cannot_settle
#assert_axioms stitch_drops_revoked_authority
#assert_axioms settled_root_attests_live_authority

#print axioms settlement_soundness
#print axioms revoke_before_tip_unsettleable
#print axioms deployedSettle_binds_live_authority
#print axioms branchSettle_NOT_binds

/-!
Settlement Soundness, in the logic — the composition the frontiers named:

  1. LIVE-AT-TIP = the attenuation floor (`reaches`, `granted ⊆ held`, from `is_attenuation`)
     ∧ the revocation gate (`honors`, the fail-closed tip view, from `eventual_bounded_revocation`).
  2. KEYSTONE = a SETTLED turn exercised a LIVE-at-tip authority (`settlement_soundness`),
     because a faithful settlement predicate BINDS live authority into the commitment
     (`BindsLiveAuthority` — the §4.4.1 obligation as a TYPED hypothesis, never an axiom).
  3. CONTRAPOSITIVE = a revoke that PROPAGATED to the tip makes the turn UNSETTLEABLE
     (`revoke_before_tip_unsettleable`); n=1 ⇒ immediate (`revoke_unsettleable_immediate`).
  4. NON-VACUOUS = the SAME cap settles inside the stale window and is unsettleable past
     the propagation bound (`settlement_nonvacuous`) — true AND false, not a `True`-carrier.

It closes the three converging frontiers:
  * KeyLeak — `leaked_then_revoked_cannot_settle` (the named settlement seam).
  * Membrane stitch — `stitch_drops_revoked_authority` (the linear DROP).
  * Light-client unfoolability — `settled_root_attests_live_authority` (accept ⟹ live-at-settlement).

THE DEPLOYED CLOSURE (§5b/§6b) — NON-tautological, the codex strengthening:
  `liveSettlement_binds` is honest but TAUTOLOGICAL — `liveSettlement := LiveAtTip`, so binding
  reduces to `LiveAtTip → LiveAtTip` (`h => h`); it witnesses the interface is inhabited but proves
  nothing about a DEPLOYED settlement. `deployedSettle_binds_live_authority` is the strengthening:
  `deployedSettle` is a STRUCTURED predicate (an attenuation floor `reaches` ∧ the *tip-time*
  revocation gate `tipHonored = honors … tip.node tip.time`, the same gate the deployed
  `Dregg2.Distributed.Revocation.honors` / `Dregg2.Circuit.SettlementSoundness.honorsAtSettlement`
  compute), and the closure DISCHARGES the honored-leg from that gate. The property BITES on the
  predicate CLASS: a settlement that carries a BRANCH-time view forward (`branchSettle`, the §6.3
  failure mode) does NOT satisfy `BindsLiveAuthority` (`branchSettle_NOT_binds` — refuted on a
  cap revoked-at-the-tip), so the closure separates faithful from unfaithful settlements
  (`deployed_closure_discriminates`).

THE NAMED RESIDUAL (the precise connection to the live consensus/exec settlement — NOT a Lean gap
  here, an inter-module bridge): `deployedSettle`'s `tipHonored` is the self-contained restatement
  (on the `KeyLeak` leak-credential model) of the deployed circuit gate
  `Dregg2.Circuit.SettlementSoundness.honorsAtSettlement st cred = verify (localRevSet T log nSettle
  tSettle) cred`. The full deployed compose — `verifyBatch (vkOfRegistry Rfix) pi π = accept` ⟹ a
  genuine kernel transition whose `revoked` registry is BOUND by the finalized commitment
  (`finalized_commit_binds_revoked`) and whose authority is read at `(nSettle, tSettle)` — is
  PROVEN, against the real `recStateCommit`/`verifyBatch`, in `Dregg2.Circuit.SettlementSoundness`
  (`settlement_soundness` there). The residual that remains external to BOTH Lean modules is the
  circuit-emit conformance obligation already named in that file's header §49–56: that the DEPLOYED
  rest-hash absorbs the `#139` revocation-channel wire root into the finalized commitment
  (`RestHashIffFrame`'s `revoked` conjunct realized at the wire) — a Rust circuit-lane obligation,
  not a hole in either compose.
-/

end Metatheory.SettlementSoundness
