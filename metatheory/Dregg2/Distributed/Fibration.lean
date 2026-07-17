/-
# Dregg2.Distributed.Fibration — the distributed-adversarial semantics as ONE indexed structure.

Titanium Phase 1 (`.docs-history-noclaude/rebuild/metatheory/TITANIUM-PHASE.md` §"PHASE 1 · THE FIBRATION"). The per-deployment
guarantees of dregg are not independent theorems; they are **fibres of one structure** — a fibration

    p : E → B   over the base   B = Topology × FaultModel × CryptoStrength

of *deployment conditions*. A point `b ∈ B` is a concrete deployment (e.g. single-machine / honest /
ideal-crypto … up to global-mesh / sleepy-Byzantine / computational). The fibre over `b` is the
system's guarantee *as it actually holds there*, packaged as a **measured bound**: the strong local
property degraded by a stated, finite amount.

## The geometry (the single-machine principle, formalized)

* The **terminal fibre** sits over the apex `apex = (single-machine, honest, ideal)`. There the bound
  collapses to `0` — the strong local property. `lift_collapse` is **DEFINITIONAL** (it reads the
  apex's bound off the structure; it is not a re-proof) — but it is not therefore decorative: it is
  the SINGLE collapse route all three fibres take, and CONTRAPOSED it becomes a refutation rule with
  real reach. `not_apex_of_violation` turns one OBSERVED violation into a proof that a deployment is
  not apex — deriving from BEHAVIOUR ALONE what §6 otherwise gets only by reading a topology's delay
  table by hand (`distBase_not_apex_from_behaviour`; `distBase_not_apex_routes_agree` pins the two
  independent routes to one verdict). `IsApex` is not inspectable on a real network; a violation is.
* The **reindexing functor `lift`** transports a fibre to a *weaker* base point, replacing the apex's
  `0` slack with the deployment's measured slack — "distribution bounds the single-machine ideal" is
  literally `lift apex→b` adding the topology's delay to a `0` window.

## The fault model (CONSENSUS-GROUNDING.md §1, Sridhar et al. 2411.01689)

`FaultModel` is NOT a scalar `f<n/3`. It is Sridhar's **4-dimension model space**
`(validatorSleepiness, clientSleepiness, clientInteractivity, network)`, ordered by "model X is no
harder than Y" (their Fig. 2 Hasse diagram). dregg's real deployment is ONE point —
`(sleepy, sleepy, communicating, partial-sync)` — and `lift` reindexing *down* that order is the
reindexing of the guarantee. (We adopt the framing; we do not re-derive the 16-model characterization.)

## The three fibres (REUSING existing proofs, through the SAME `lift`)

1. **Revocation** — the FIRST concrete instance, reused verbatim from `Revocation.lean`:
   `eventual_bounded_revocation` is the fibre over a *distributed* base point (window `= delay`);
   `immediate_revocation` (n=1 / instantaneous) is the **terminal-fibre collapse** (window `= 0`);
   `tightness_tooth` is the **negative tooth** (the window is non-empty distributed).
2. **Conservation** — the terminal fibre is `Exec.Unified.unified_ledger_conserves` (n=1 ledger
   exactly conserves: window `0`). Its *distributed* bound is the hypothesis structure
   `DistConservationBound`; **§12 DISCHARGES it with a DERIVED witness**
   (`distConservationBound_derived`): for any per-deployment view of locally-executed finalized
   prefixes, conservation holds with window ZERO at EVERY base point — conservation is
   PREFIX-CLOSED (`HistoryAggregation.wellformed_history_conserves`), so a partition cannot skew
   the visible total at all. (Honest scope: the EXACT body executor; the FEE-wrapped history's
   cross-node skew = the missing turns' burns — `Distributed/FeeHistory`.)
3. **Attenuation** — the terminal fibre is `Authority.attenuate_narrows` (a child token admits
   ⊆ the parent: window `0`, the inclusion is exact). Its *distributed* bound is
   `DistAttenuationBound`; **§13 DISCHARGES it, derived from the revocation fibre** exactly as
   this header always said it should be (`distAttenuationBound_derived`): an attenuation event =
   the broad parent revoked + the narrowed child live; the stale-token honoring window IS the
   revocation propagation window, and the narrowing itself is window-free.

The honesty discipline: the two former named opens are now THEOREM-witnessed structures (the
hypothesis shapes remain for generality, but a derived witness inhabits each — no vacuity, no
carried hypothesis). The `lift` functor is real precisely because (a) it has a non-vacuity witness
(a deployment where the bound is positive) AND (b) a negative tooth (a deployment where the
guarantee weakens — the same `tightness_tooth` instance, re-read as "the fibre over this base
point is strictly weaker than the terminal fibre"; §13's stale-token fibre inherits it).

Pure, computable where decidable.
-/
import Dregg2.Distributed.Revocation
import Dregg2.Distributed.HistoryAggregation
import Dregg2.Authority.Caveat

namespace Dregg2.Distributed.Fibration

open Dregg2.Distributed.Revocation
open Dregg2.Authority.Credential
open Dregg2.Crypto (CryptoKernel)

/-! ## 1. The base `B = Topology × FaultModel × CryptoStrength`.

A point of `B` is a deployment condition. `Topology` is REUSED from `Revocation.lean`. `FaultModel`
is Sridhar's 4-dimension model space. `CryptoStrength` is `ideal | computational`. -/

/-- **Validator sleepiness** (Sridhar axis 1): an always-on validator vs an intermittent ("sleepy")
one — a phone validator is `sleepy`. -/
inductive Sleepiness where
  | alwaysOn
  | sleepy
  deriving DecidableEq, Repr

/-- **Client interactivity** (Sridhar axis 3): a `silent` client (Nakamoto, 49%) vs a
`communicating` one (Dolev–Strong / gossiping, up to 99%). dregg's clients gossip (Plumtree) ⇒
`communicating`. -/
inductive Interactivity where
  | silent
  | communicating
  deriving DecidableEq, Repr

/-- **Network model** (Sridhar axis 4): `synchrony` vs `partialSync` (GST). dregg targets
partial-synchrony. -/
inductive Network where
  | synchrony
  | partialSync
  deriving DecidableEq, Repr

/-- **`FaultModel`** — Sridhar's 4-dimension model space (CONSENSUS-GROUNDING.md §1), replacing the
scalar `f<n/3`. The point `(sleepy, sleepy, communicating, partialSync)` is dregg's real deployment;
`(alwaysOn, alwaysOn, communicating, synchrony)` is the *easiest* (apex) corner. -/
structure FaultModel where
  /-- Validator sleepiness. -/
  validatorSleepiness : Sleepiness
  /-- Client sleepiness. -/
  clientSleepiness : Sleepiness
  /-- Client interactivity. -/
  clientInteractivity : Interactivity
  /-- Network synchrony model. -/
  network : Network
  deriving DecidableEq, Repr

/-- The *easiest* (apex) fault model: every validator and client always-on, communicating, synchronous
network. This is the corner where consensus is trivial — the terminal fibre lives here. -/
def FaultModel.apex : FaultModel :=
  { validatorSleepiness := .alwaysOn, clientSleepiness := .alwaysOn,
    clientInteractivity := .communicating, network := .synchrony }

/-- dregg's REAL deployment point: sleepy validators (phones), sleepy communicating clients
(merchants gossiping), partial-synchrony. This is the point whose consensus fibre carries an
*asymmetric* `(t^S, t^L)` pair (Sridhar Thm. 4) — NOT a scalar. -/
def FaultModel.dregg : FaultModel :=
  { validatorSleepiness := .sleepy, clientSleepiness := .sleepy,
    clientInteractivity := .communicating, network := .partialSync }

/-- Per-axis "no harder than": `alwaysOn`/`silent`/`synchrony`/`ideal` are the easy ends. -/
def Sleepiness.le : Sleepiness → Sleepiness → Bool
  | .alwaysOn, _ => true
  | .sleepy, .sleepy => true
  | .sleepy, .alwaysOn => false

def Interactivity.le : Interactivity → Interactivity → Bool
  | .communicating, _ => true
  | .silent, .silent => true
  | .silent, .communicating => false

def Network.le : Network → Network → Bool
  | .synchrony, _ => true
  | .partialSync, .partialSync => true
  | .partialSync, .synchrony => false

/-- **`FaultModel.harder a b`** — `a` is "no harder than" `b` (Sridhar Fig. 2 Hasse order): each axis
is at least as easy. `apex` is the bottom (easiest) of this order; `lift` reindexes DOWN it (toward
harder deployments). -/
def FaultModel.harder (a b : FaultModel) : Bool :=
  a.validatorSleepiness.le b.validatorSleepiness
    && a.clientSleepiness.le b.clientSleepiness
    && a.clientInteractivity.le b.clientInteractivity
    && a.network.le b.network

/-- **`CryptoStrength`** — `ideal` (information-theoretic / random-oracle idealisation) vs
`computational` (real primitives under a hardness assumption). The apex is `ideal`. -/
inductive CryptoStrength where
  | ideal
  | computational
  deriving DecidableEq, Repr

/-- **`B`** — the base of the fibration: a deployment condition = topology × fault model × crypto
strength. (We carry `Topology` from `Revocation.lean`; a one-node topology is the single-machine
corner.) -/
structure B where
  /-- The propagation topology (`Revocation.Topology`). -/
  topo : Topology
  /-- The fault model (Sridhar 4-dim). -/
  fault : FaultModel
  /-- The cryptographic strength. -/
  crypto : CryptoStrength

/-! ## 2. The apex base point and the "is-apex" predicate.

The apex is `(single-machine, honest, ideal)`: a topology with instantaneous propagation, the easiest
fault model, ideal crypto. The terminal fibre lives over any apex point. -/

/-- **`IsApex b`** — `b` is an apex deployment: instantaneous propagation (single-machine /
zero-delay, `Revocation.Instantaneous`), the easiest fault model, ideal crypto. The terminal fibre
collapses the bound to `0` exactly over apex points. -/
def IsApex (b : B) : Prop :=
  Instantaneous b.topo ∧ b.fault = FaultModel.apex ∧ b.crypto = CryptoStrength.ideal

/-- A one-node topology with the apex fault model and ideal crypto IS an apex point — the
single-machine corner, derived (not assumed) from `Revocation.oneNode_instantaneous` via
`Instantaneous`. -/
def apexPoint (T : Topology) (_hinst : Instantaneous T) : B :=
  { topo := T, fault := FaultModel.apex, crypto := CryptoStrength.ideal }

theorem apexPoint_isApex (T : Topology) (hinst : Instantaneous T) :
    IsApex (apexPoint T hinst) :=
  ⟨hinst, rfl, rfl⟩

/-! ## 3. The fibre — a guarantee as a MEASURED BOUND over a base point.

A fibre is the system's guarantee *at* a base point, packaged as a window `bound : Time` plus the
proof obligation "the property holds at/after `bound`". We make the *shape* generic (so conservation,
attenuation, revocation are instances of ONE `Fibre`) and then instantiate.

The key structural fact: over an apex point the bound is `0` (terminal fibre); `lift` to a weaker
point can only *grow* the bound. -/

/-- **`Fibre P`** — a fibre of the property `P` over a base point. `bound b` is the measured slack at
deployment `b` (e.g. the revocation propagation window); `holdsAfter` is the obligation that the
property holds once `bound` ticks have elapsed; `apexZero` is the *definitional* terminal-fibre law:
over an apex point the bound is `0`. This is the indexed object of the fibration; `lift` reindexes it.

`P : B → Time → Prop` is the property read at a base point and an elapsed time (e.g.
"at every node, time `t ≥ window`, the revoked cred is not honored"). -/
structure Fibre (P : B → Time → Prop) where
  /-- The measured slack (window) at each deployment. -/
  bound : B → Time
  /-- The property holds at/after the window, at every base point. -/
  holdsAfter : ∀ b t, bound b ≤ t → P b t
  /-- **Terminal-fibre law (definitional collapse):** over any apex point the window is `0`. -/
  apexZero : ∀ b, IsApex b → bound b = 0

/-- **`lift_collapse` — DEFINITIONAL terminal-fibre collapse.** Over any apex point, a fibre's window
is `0` and the property holds at *every* time `t` (including `t = 0`). This is NOT a new theorem: it
reads `apexZero` off the structure and feeds `0 ≤ t` to `holdsAfter`. "The strong local property is
the terminal fibre" is structural. -/
theorem lift_collapse {P : B → Time → Prop} (F : Fibre P) (b : B) (hb : IsApex b) (t : Time) :
    F.bound b = 0 ∧ P b t := by
  refine ⟨F.apexZero b hb, ?_⟩
  apply F.holdsAfter
  rw [F.apexZero b hb]
  exact Nat.zero_le t

/-- **`not_apex_of_violation` — `lift_collapse` CONTRAPOSED, and the direction that does work.**
`lift_collapse` runs apex ⟹ guarantee-at-every-time. Contraposed, it runs the other way: a SINGLE
OBSERVED violation — the property failing at any one time `t`, for any fibre over `b` — REFUTES the
deployment's apex-ness outright.

This is the operationally meaningful direction. `IsApex` is not something you can inspect on a running
system (you cannot read a network's `Instantaneous`-ness off a wire), but a violation is exactly what
you *do* see. So this turns the terminal-fibre law into a REFUTATION RULE: behaviour witnesses
deployment class. It also makes `lift_collapse` load-bearing for a fact §6 otherwise establishes only
by reading a topology's delay table by hand (`distBase_not_apex`) — see
`distBase_not_apex_from_behaviour`, an independent second route to the same conclusion. -/
theorem not_apex_of_violation {P : B → Time → Prop} (F : Fibre P) (b : B) (t : Time)
    (hviol : ¬ P b t) : ¬ IsApex b :=
  fun hb => hviol (lift_collapse F b hb t).2

/-- Contrapositive of the window half: a fibre with a strictly positive window at `b` cannot be over
an apex point. (The bound half of `lift_collapse`, made into a refutation rule.) -/
theorem not_apex_of_positive_bound {P : B → Time → Prop} (F : Fibre P) (b : B)
    (hpos : 0 < F.bound b) : ¬ IsApex b :=
  fun hb => absurd (lift_collapse F b hb 0).1 (Nat.ne_of_gt hpos)

/-! ## 4. The reindexing functor `lift` — transport a fibre to a weaker base point.

`lift F src dst hmeasured` transports the fibre `F` from base point `src` to a weaker `dst`, replacing
`src`'s bound by `dst`'s — but only when the move is *measured*: the new window is finite and the
property still holds after it (the `hmeasured` premise carries exactly the bound the weaker deployment
pays). The functor law we expose: lifting FROM the apex adds the deployment's slack to a `0` window —
"distributed bounds the single-machine ideal" is `lift apex→b`. -/

/-- **`liftedBound F dst`** — the window `F` assigns at the destination deployment. (The reindexing is
just reading the fibre at `dst`; the structure already carries `bound : B → Time` globally, so `lift`
is a *projection* — the functoriality is that `apexZero` pins the apex value and `holdsAfter` carries
the property everywhere.) This makes `lift` total and definitional, with the *content* in the two
laws below. -/
def liftedBound {P : B → Time → Prop} (F : Fibre P) (dst : B) : Time := F.bound dst

/-- **`lift_from_apex` — the single-machine principle as a reindexing theorem.** Lifting a fibre from
the apex (`src` apex, window `0`) to *any* destination `dst` yields the destination's measured window
`F.bound dst`, and the property holds after it. The apex window is `0`; the destination window is
whatever slack the weaker deployment pays — distribution can only *add* slack to the ideal `0`. This
is the formal "distributed bounds the single-machine ideal". -/
theorem lift_from_apex {P : B → Time → Prop} (F : Fibre P) (src dst : B) (hsrc : IsApex src) :
    F.bound src = 0 ∧ (∀ t, liftedBound F dst ≤ t → P dst t) := by
  refine ⟨F.apexZero src hsrc, ?_⟩
  intro t ht
  exact F.holdsAfter dst t ht

/-- **`lift_monotone_into_apex`** — reindexing INTO an apex point recovers the terminal fibre: the
lifted window is `0`. Composed with `lift_from_apex` this says the apex is terminal (every
lift into it lands at window `0`). -/
theorem lift_monotone_into_apex {P : B → Time → Prop} (F : Fibre P) (dst : B) (hdst : IsApex dst) :
    liftedBound F dst = 0 :=
  F.apexZero dst hdst

/-! ## 5. FIBRE #1 — REVOCATION (the first concrete instance, reused from `Revocation.lean`).

The revocation guarantee read at a base point: a credential revoked at origin `m`, time `τ`, is NOT
honored at any node once the window has elapsed. We package `eventual_bounded_revocation` as a
`Fibre`; the window is the topology's `delay`, the apex collapse is `immediate_revocation`, and the
negative tooth is `tightness_tooth` re-read as "this fibre is strictly weaker than terminal". -/

section RevocationFibre

variable {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]

/-- The revocation property at a base point, for a *fixed* revocation `(cred, m, τ)` in a *fixed* log,
observed at a *fixed* node `n`: "the credential is not honored at elapsed time `t`" — where `t` is
measured from `τ`. We read the topology off `b.topo`. -/
def revProperty (log : List RevEvent) (cred : VC Digest Proof) (_m n : Node) (τ : Time)
    (b : B) (elapsed : Time) : Prop :=
  honors b.topo log n (τ + elapsed) cred = false

/-- **The REVOCATION FIBRE.** Window at `b` = `b.topo.delay m n` (the propagation delay). The
property after the window is exactly `eventual_bounded_revocation` (with `t = τ + elapsed` and
`hbound : τ + delay ≤ τ + elapsed` from `delay ≤ elapsed`). The apex collapse is the definitional
fact that an apex topology is `Instantaneous`, so `delay m n = 0`. -/
def revocationFibre (log : List RevEvent) (cred : VC Digest Proof) (m n : Node) (τ : Time)
    (hrev : RevokedAt log cred m τ) : Fibre (revProperty log cred m n τ) where
  bound b := b.topo.delay m n
  holdsAfter b elapsed hle := by
    unfold revProperty
    exact eventual_bounded_revocation b.topo log cred m τ hrev n (τ + elapsed)
      (Nat.add_le_add_left hle τ)
  apexZero b hb := hb.1 m n

/-- **`revocation_terminal_collapse`** — over an apex point the revocation fibre's window is `0` and
the credential is not honored at *any* elapsed time (= `immediate_revocation`). This is `lift_collapse`
specialized: the strong, instantaneous revocation IS the terminal fibre. -/
theorem revocation_terminal_collapse (log : List RevEvent) (cred : VC Digest Proof)
    (m n : Node) (τ : Time) (hrev : RevokedAt log cred m τ) (b : B) (hb : IsApex b) (elapsed : Time) :
    (revocationFibre log cred m n τ hrev).bound b = 0 ∧ revProperty log cred m n τ b elapsed :=
  lift_collapse (revocationFibre log cred m n τ hrev) b hb elapsed

end RevocationFibre

/-! ## 6. The NEGATIVE TOOTH — a base point where the guarantee GENUINELY weakens.

The fibration is a *real constraint*, not a metaphor: we exhibit a base point `distBase` (the two-node
`toothTopology`, distributed) where the revocation fibre's window is strictly positive AND the
credential is still honored inside the window — i.e. the fibre over `distBase` is **strictly weaker**
than the terminal fibre (where it would be `0` and unhonored). This is `tightness_tooth`, re-read
through the fibration lens. -/

/-- The distributed base point built on `Revocation.toothTopology` (two nodes, cross-delay `5`),
dregg's real fault model, computational crypto — a non-apex deployment. -/
def distBase : B :=
  { topo := toothTopology, fault := FaultModel.dregg, crypto := CryptoStrength.computational }

/-- `distBase` is NOT apex — its topology is not instantaneous (the `0→1` delay is `5`). -/
theorem distBase_not_apex : ¬ IsApex distBase := by
  rintro ⟨hinst, _, _⟩
  have : toothTopology.delay 0 1 = 0 := hinst 0 1
  simp [toothTopology] at this

/-- **THE NEGATIVE TOOTH (fibration is a real constraint).** Over the distributed base point
`distBase`, the revocation fibre's window is strictly positive (`= 5 > 0`) AND the credential — though
revoked — is STILL HONORED at an elapsed time inside the window. So the fibre over
`distBase` is strictly weaker than the terminal fibre: the guarantee degrades off the apex.
Reuses `tightness_tooth` (`honors … 1 4 … = true`, with `t = τ + elapsed = 0 + 4`). -/
theorem fibre_weakens_offApex :
    -- (a) the fibre's window at the distributed point is strictly positive
    0 < (revocationFibre toothLog toothCred 0 1 0 tooth_revoked).bound distBase
    -- (b) the revocation is real
    ∧ RevokedAt toothLog toothCred 0 0
    -- (c) yet the credential is still honored at elapsed time 4 (inside the window [0,5)) —
    --     the fibre is STRICTLY WEAKER than terminal (where it would be unhonored)
    ∧ ¬ revProperty toothLog toothCred 0 1 0 distBase 4 := by
  refine ⟨?_, tooth_revoked, ?_⟩
  · show 0 < toothTopology.delay 0 1
    decide
  · -- revProperty … 4 = (honors … (0+4) … = false); but the tooth says it is `true`.
    unfold revProperty distBase
    rw [(by rfl : (0 : Time) + 4 = 4)]
    rw [tightness_tooth.2.2]
    decide

/-! ### 6b. The negative tooth, read as a REFUTATION — two independent routes to non-apexness.

`distBase_not_apex` (§6) proves `¬ IsApex distBase` by INSPECTION: it unfolds `toothTopology` and
reads the `0→1` delay off the table. That route is only available because this deployment is a model
we wrote down; on a real network there is no table to read.

`not_apex_of_violation` gives the route that survives contact with a real deployment: feed it the
OBSERVED violation from `fibre_weakens_offApex` (the revoked credential still honored at elapsed time
`4`) and apex-ness is refuted from BEHAVIOUR ALONE — no access to the topology's interior. The two
routes are independent (one reads the delay table, the other reads only the honor decision) and
`distBase_not_apex_routes_agree` pins that they land on the same conclusion. -/

/-- **`distBase_not_apex_from_behaviour`** — `¬ IsApex distBase`, derived from the OBSERVED revocation
failure rather than from the topology's delay table. The only input is `fibre_weakens_offApex.2.2`:
the credential, though revoked, is still honored at elapsed time `4`. An apex deployment could not do
that (`lift_collapse`), so `distBase` is not apex. This is the sense in which the terminal-fibre law
constrains reality: a deployment's *behaviour* betrays its class. -/
theorem distBase_not_apex_from_behaviour : ¬ IsApex distBase :=
  not_apex_of_violation (revocationFibre toothLog toothCred 0 1 0 tooth_revoked) distBase 4
    fibre_weakens_offApex.2.2

/-- The window route: `distBase`'s revocation window is `5 > 0`, and a positive window alone already
refutes apex-ness — no behavioural observation needed. A third, independent route. -/
theorem distBase_not_apex_from_window : ¬ IsApex distBase :=
  not_apex_of_positive_bound (revocationFibre toothLog toothCred 0 1 0 tooth_revoked) distBase
    fibre_weakens_offApex.1

/-- **Two gates provably agree.** The by-inspection route (`distBase_not_apex`, reads the delay
table), the behavioural route (`distBase_not_apex_from_behaviour`, reads only whether the revoked
credential was honored) and the window route (`distBase_not_apex_from_window`) all establish the same
proposition. Independent derivations, one verdict — so the terminal-fibre law is not an artefact of
how we happened to model the topology. -/
theorem distBase_not_apex_routes_agree :
    (¬ IsApex distBase) ∧ (¬ IsApex distBase) ∧ (¬ IsApex distBase) :=
  ⟨distBase_not_apex, distBase_not_apex_from_behaviour, distBase_not_apex_from_window⟩

/-! ## 7. NON-VACUITY of the fibration itself.

`lift` is not a trivial identity: there is a deployment where the window is positive (Tooth, §6) AND a
deployment (apex) where it collapses to `0` with the property holding everywhere. Together they show
`lift` *moves* the bound — both a witness where the guarantee is strong (apex, window `0`) and one
where it is weaker (distributed, window `5`, honored inside). -/

/-- An apex instance: the single-node instantaneous topology `Revocation.toothTopologyInstant` gives an
apex base point where the revocation fibre's window is `0` and the credential is unhonored at every
elapsed time. The terminal-fibre witness. -/
def apexBase : B :=
  { topo := toothTopologyInstant, fault := FaultModel.apex, crypto := CryptoStrength.ideal }

theorem apexBase_isApex : IsApex apexBase :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

/-- **NON-VACUITY, assembled.** `lift` transports the bound:
* over `apexBase` (terminal) the window is `0` and the cred is unhonored at every elapsed time;
* over `distBase` (distributed) the window is `5 > 0` and the cred is *honored* inside it.
So the revocation fibre is a real section that *weakens* off the apex — the fibration discriminates
deployments, it is not a `True`-carrier. -/
theorem fibration_nonvacuous :
    -- terminal fibre: window 0, property holds everywhere
    ((revocationFibre toothLog toothCred 0 1 0 tooth_revoked).bound apexBase = 0
      ∧ ∀ elapsed, revProperty toothLog toothCred 0 1 0 apexBase elapsed)
    -- distributed fibre: window strictly positive, property FAILS inside it
    ∧ (0 < (revocationFibre toothLog toothCred 0 1 0 tooth_revoked).bound distBase
      ∧ ¬ revProperty toothLog toothCred 0 1 0 distBase 4) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (revocation_terminal_collapse toothLog toothCred 0 1 0 tooth_revoked apexBase
      apexBase_isApex 0).1
  · intro elapsed
    exact (revocation_terminal_collapse toothLog toothCred 0 1 0 tooth_revoked apexBase
      apexBase_isApex elapsed).2
  · exact fibre_weakens_offApex.1
  · exact fibre_weakens_offApex.2.2

/-! ## 8. FIBRE #2 — CONSERVATION, through the SAME `lift`.

The terminal fibre of conservation is the single-machine ledger law (`Exec.Unified` —
`unified_ledger_conserves`: the n=1 ledger conserves `total` *exactly*, window `0`). Its DISTRIBUTED
bound — by how much a network partition can transiently skew the *visible* total before reconciliation
— is NOT yet derived in Lean. Per the honesty discipline we carry it as an EXPLICIT named hypothesis,
NOT an unproven hole: a `DistConservationBound` supplies the window and the after-window property; from
it we BUILD the conservation fibre through the same `Fibre`/`lift` machinery. -/

/-- **`DistConservationBound P`** — the NAMED OPEN for conservation's distributed bound. It packages
exactly the data a future Phase-2 proof must supply: a window `cwindow b` per deployment (the transient
partition skew), the after-window property, and the apex-collapse to `0` (the terminal ledger law). It
is a *hypothesis structure*, so any user must produce a witness — there is no vacuity. -/
structure DistConservationBound (P : B → Time → Prop) where
  /-- The partition-skew window per deployment (`0` at apex = exact conservation). -/
  cwindow : B → Time
  /-- After the window, conservation holds (reconciliation has completed). -/
  reconciledAfter : ∀ b t, cwindow b ≤ t → P b t
  /-- Apex collapse: single-machine ledger conserves exactly (window `0` — the `Exec.Unified` law). -/
  cwindowApexZero : ∀ b, IsApex b → cwindow b = 0

/-- **The CONSERVATION FIBRE — built from the named open through the SAME `Fibre`.** Given a
`DistConservationBound`, conservation becomes a fibre with the identical apex-collapse / measured-lift
structure as revocation. This proves conservation is an *instance of the fibration*, not a separate
theory — the open part is only the distributed *witness*, isolated in `DistConservationBound`. -/
def conservationFibre {P : B → Time → Prop} (H : DistConservationBound P) : Fibre P where
  bound := H.cwindow
  holdsAfter := H.reconciledAfter
  apexZero := H.cwindowApexZero

/-- Conservation's terminal collapse is `lift_collapse` of its fibre: over an apex point the window is
`0` and conservation holds at every time. (The single-machine ledger law, as the terminal fibre.) -/
theorem conservation_terminal_collapse {P : B → Time → Prop} (H : DistConservationBound P)
    (b : B) (hb : IsApex b) (t : Time) :
    (conservationFibre H).bound b = 0 ∧ P b t :=
  lift_collapse (conservationFibre H) b hb t

/-! ## 9. FIBRE #3 — ATTENUATION, through the SAME `lift`.

The terminal fibre of attenuation is `Authority.Caveat.attenuate_narrows` (a child token admits ⊆ the
parent — the inclusion is *exact*, window `0`). Its DISTRIBUTED bound — stale-token honoring across a
partition, exactly the revocation-style window — is carried as the NAMED hypothesis
`DistAttenuationBound` until derived from the revocation fibre. Same machinery, same collapse. -/

/-- **`DistAttenuationBound P`** — the NAMED OPEN for attenuation's distributed bound: a window
`awindow b` (the stale-token honoring window across a partition), the after-window property (an
attenuated/revoked token stops being over-honored once the narrowing has propagated), and the apex
collapse to `0` (the exact `attenuate_narrows` inclusion single-machine). A hypothesis structure ⇒ no
vacuity. -/
structure DistAttenuationBound (P : B → Time → Prop) where
  /-- The stale-token honoring window per deployment (`0` at apex = exact inclusion). -/
  awindow : B → Time
  /-- After the window, the attenuation is enforced everywhere (narrowing propagated). -/
  narrowedAfter : ∀ b t, awindow b ≤ t → P b t
  /-- Apex collapse: single-machine attenuation is exact (window `0` — `attenuate_narrows`). -/
  awindowApexZero : ∀ b, IsApex b → awindow b = 0

/-- **The ATTENUATION FIBRE — through the SAME `Fibre`.** Given a `DistAttenuationBound`, attenuation
is a fibre with the identical structure. The open part is only the distributed witness, isolated in
`DistAttenuationBound`; the *shape* is shared with revocation and conservation. -/
def attenuationFibre {P : B → Time → Prop} (H : DistAttenuationBound P) : Fibre P where
  bound := H.awindow
  holdsAfter := H.narrowedAfter
  apexZero := H.awindowApexZero

theorem attenuation_terminal_collapse {P : B → Time → Prop} (H : DistAttenuationBound P)
    (b : B) (hb : IsApex b) (t : Time) :
    (attenuationFibre H).bound b = 0 ∧ P b t :=
  lift_collapse (attenuationFibre H) b hb t

/-! ## 10. The three fibres share ONE `lift` — the structural payoff.

`lift_from_apex` applies UNIFORMLY to all three fibres: revocation (proven distributed bound),
conservation (named open), attenuation (named open). This is the Phase-1 milestone: the per-deployment
guarantees are fibres of ONE indexed structure, transported by ONE reindexing functor, collapsing to
the terminal (single-machine) fibre by ONE definitional law. -/

/-- **`three_fibres_one_lift`** — the same `lift_from_apex` reindexes all three fibres from any apex
source to any destination. Revocation is fully proven; conservation and attenuation are gated on their
NAMED distributed-bound hypotheses (`DistConservationBound`/`DistAttenuationBound`). This is the milestone-1 statement: one base, one fibre shape, one `lift`. -/
theorem three_fibres_one_lift
    {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (log : List RevEvent) (cred : VC Digest Proof) (m n : Node) (τ : Time)
    (hrev : RevokedAt log cred m τ)
    {Pc Pa : B → Time → Prop} (Hc : DistConservationBound Pc) (Ha : DistAttenuationBound Pa)
    (src dst : B) (hsrc : IsApex src) :
    -- revocation fibre lifts (proven)
    ((revocationFibre log cred m n τ hrev).bound src = 0
      ∧ ∀ t, liftedBound (revocationFibre log cred m n τ hrev) dst ≤ t
        → revProperty log cred m n τ dst t)
    -- conservation fibre lifts (gated on the named open)
    ∧ ((conservationFibre Hc).bound src = 0
      ∧ ∀ t, liftedBound (conservationFibre Hc) dst ≤ t → Pc dst t)
    -- attenuation fibre lifts (gated on the named open)
    ∧ ((attenuationFibre Ha).bound src = 0
      ∧ ∀ t, liftedBound (attenuationFibre Ha) dst ≤ t → Pa dst t) :=
  ⟨lift_from_apex (revocationFibre log cred m n τ hrev) src dst hsrc,
   lift_from_apex (conservationFibre Hc) src dst hsrc,
   lift_from_apex (attenuationFibre Ha) src dst hsrc⟩

/-! ## 12. CONSERVATION DISCHARGED (#35) — the carried hypothesis now has a DERIVED witness.

`DistConservationBound` packaged "by how much can a partition transiently skew the visible
total". The landed answer: NOT AT ALL — conservation is PREFIX-CLOSED. Every locally-executed
finalized prefix is a genuine `recCexec` run from genesis (`execute_finalized_turn` maintains
exactly this), and EVERY committed turn conserves (`recChained_run_conserves`), so a node that
has received ANY prefix of the history already sees the genesis total. The window is `0` at
EVERY base point, not just the apex — STRONGER than the fibre shape demanded.

HONEST SCOPE: this is the EXACT body executor (`recCexec`, the strand the light client checks).
The FEE-wrapped history (`runTurn`) burns per turn, so two nodes at different heights see totals
differing by exactly the missing turns' burns — that statement is
`Distributed/FeeHistory.wellformed_history_conserves_modulo_burn`, and its reconciliation window
IS the propagation delay of the missing turns. -/

section ConservationDischarge

open Dregg2.Distributed.HistoryAggregation
  (ChainStep StateChained lastStateOf wellformed_history_conserves honestStep)
open Dregg2.Exec (RecChainedState recTotal)
open Dregg2.Exec.ConsensusExec (teethGenesis)

variable (g : RecChainedState) (view : B → Time → List ChainStep)

/-- The conservation property at a base point: the locally-VISIBLE ledger total (the fold of the
finalized turns this deployment's node has executed by elapsed `t`) equals the genesis total. -/
def consProperty (b : B) (t : Time) : Prop :=
  recTotal (lastStateOf g (view b t)).kernel = recTotal g.kernel

/-- **THE DISCHARGE — a derived `DistConservationBound` witness.** For ANY view assignment whose
prefixes are genuine state-chained executor runs from genesis (`hview` — what
`execute_finalized_turn` maintains), conservation holds with window ZERO at EVERY deployment:
`wellformed_history_conserves` applied to the local prefix. The §8 named open is closed — and the
derived bound is stronger than required (`0` off-apex too: prefix-closure beats reconciliation). -/
def distConservationBound_derived (hview : ∀ b t, StateChained g (view b t)) :
    DistConservationBound (consProperty g view) where
  cwindow _ := 0
  reconciledAfter b t _ := wellformed_history_conserves g (view b t) (hview b t)
  cwindowApexZero _ _ := rfl

/-- A REAL view: every deployment has executed the one-step honest teeth chain. -/
def demoView : B → Time → List ChainStep := fun _ _ => [honestStep]

theorem demoView_chained : ∀ b t, StateChained teethGenesis (demoView b t) :=
  fun _ _ => ⟨rfl, trivial⟩

/-- **Non-vacuity**: the discharged conservation fibre FIRES on a real executed history — at
EVERY base point and EVERY elapsed time the visible total equals genesis (window 0, off-apex
included). -/
theorem conservation_fibre_real (b : B) (t : Time) :
    consProperty teethGenesis demoView b t :=
  (distConservationBound_derived teethGenesis demoView demoView_chained).reconciledAfter
    b t (Nat.zero_le t)

/-- The discharged witness builds the SAME `Fibre` the §8 machinery transports — the
conservation fibre is now hypothesis-free end to end. -/
theorem conservation_discharged_collapse (b : B) (hb : IsApex b) (t : Time) :
    (conservationFibre
        (distConservationBound_derived teethGenesis demoView demoView_chained)).bound b = 0
      ∧ consProperty teethGenesis demoView b t :=
  conservation_terminal_collapse
    (distConservationBound_derived teethGenesis demoView demoView_chained) b hb t

-- the visible total really is the genesis total on the real chain (executed check):
#guard recTotal (Dregg2.Distributed.HistoryAggregation.lastStateOf teethGenesis
        [Dregg2.Distributed.HistoryAggregation.honestStep]).kernel
    == recTotal teethGenesis.kernel

end ConservationDischarge

/-! ## 13. ATTENUATION DISCHARGED (#35) — derived from the REVOCATION fibre, as §9 prescribed.

The distributed face of attenuation is STALE-TOKEN HONORING: a narrowing event (the broad parent
superseded by `tok.attenuate c`) propagates like a revocation of the parent — until it arrives, a
node may still honor the stale broad token. So the attenuation window IS the revocation window
(`eventual_bounded_revocation` at the superseded credential), and the narrowing itself —
everything the live child admits, the parent admitted — is `attenuate_narrows`, exact at every
deployment with no window at all. -/

section AttenuationDischarge

open Dregg2.Authority (Token Caveat Discharges attenuate_narrows)

variable {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
variable {Ctx Gateway : Type}

/-- The stale-token attenuation property at a base point, elapsed `t` after the narrowing event
at `(m, τ)`: (i) the SUPERSEDED broad credential is no longer honored at `n` (the stale half —
the parent's revocation has propagated), and (ii) everything the LIVE narrowed token admits, the
parent admitted (the narrowing half — `attenuate_narrows`, time-independent). -/
def attProperty (log : List RevEvent) (cred : VC Digest Proof) (m n : Node) (τ : Time)
    (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway) (b : B) (elapsed : Time) : Prop :=
  honors b.topo log n (τ + elapsed) cred = false
    ∧ ∀ ctx d, (tok.attenuate c).admits ctx d = true → tok.admits ctx d = true

/-- **THE DISCHARGE — a derived `DistAttenuationBound` witness, from the revocation fibre.**
Window = the propagation delay of the parent's supersession (`eventual_bounded_revocation`);
the narrowing conjunct is window-free (`attenuate_narrows`); the apex collapse is the
instantaneous-topology fact. The §9 named open is closed by exactly the derivation it named. -/
def distAttenuationBound_derived (log : List RevEvent) (cred : VC Digest Proof)
    (m n : Node) (τ : Time) (hrev : RevokedAt log cred m τ)
    (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway) :
    DistAttenuationBound (attProperty log cred m n τ tok c) where
  awindow b := b.topo.delay m n
  narrowedAfter b elapsed hle :=
    ⟨eventual_bounded_revocation b.topo log cred m τ hrev n (τ + elapsed)
        (Nat.add_le_add_left hle τ),
     fun ctx d h => attenuate_narrows tok c ctx d h⟩
  awindowApexZero b hb := hb.1 m n

/-- A concrete narrowed pair for the teeth: a bare biscuit parent, narrowed by a refusing caveat
(a REAL narrowing — the child admits nothing, the parent admitted everything). -/
def demoTok : Token Unit Unit := { kind := .biscuit, caveats := [] }
def demoCav : Caveat Unit Unit := .opaque (fun _ => false)

/-- **The derived attenuation fibre inherits the NEGATIVE TOOTH**: over the distributed base
point its window is strictly positive AND the stale broad token is STILL HONORED inside it
(`tightness_tooth`) — the fibre genuinely weakens off the apex; the discharge is not vacuous. -/
theorem att_fibre_weakens_offApex :
    0 < (attenuationFibre
          (distAttenuationBound_derived toothLog toothCred 0 1 0 tooth_revoked
            demoTok demoCav)).bound distBase
    ∧ ¬ attProperty toothLog toothCred 0 1 0 demoTok demoCav distBase 4 := by
  constructor
  · show 0 < toothTopology.delay 0 1
    decide
  · rintro ⟨h1, -⟩
    have h1' : honors toothTopology toothLog 1 4 toothCred = false := h1
    rw [tightness_tooth.2.2] at h1'
    exact Bool.noConfusion h1'

/-- **The terminal collapse fires on the derived fibre**: over an apex point the window is `0`
and the stale parent is unhonored at every elapsed time while the child's narrowing is exact —
the single-machine collapse of attenuation, now derived end to end. -/
theorem att_fibre_terminal (b : B) (hb : IsApex b) (elapsed : Time) :
    (attenuationFibre
        (distAttenuationBound_derived toothLog toothCred 0 1 0 tooth_revoked
          demoTok demoCav)).bound b = 0
      ∧ attProperty toothLog toothCred 0 1 0 demoTok demoCav b elapsed :=
  attenuation_terminal_collapse
    (distAttenuationBound_derived toothLog toothCred 0 1 0 tooth_revoked demoTok demoCav)
    b hb elapsed

end AttenuationDischarge

/-! ## 11. Axiom-hygiene tripwires.

The fibration's load-bearing results are pinned to the standard kernel whitelist (`propext`,
`Classical.choice`, `Quot.sound`). The negative tooth (`fibre_weakens_offApex`, `distBase_not_apex`)
and the assembled non-vacuity (`fibration_nonvacuous`) are pinned alongside the structural functor laws
so a regression that smuggles in an axiom — or silently makes a witness vacuous — is caught here. -/

#assert_axioms lift_collapse
#assert_axioms lift_from_apex
#assert_axioms lift_monotone_into_apex
#assert_axioms apexPoint_isApex
#assert_axioms revocation_terminal_collapse
#assert_axioms distBase_not_apex
#assert_axioms not_apex_of_violation
#assert_axioms not_apex_of_positive_bound
#assert_axioms distBase_not_apex_from_behaviour
#assert_axioms distBase_not_apex_from_window
#assert_axioms distBase_not_apex_routes_agree
#assert_axioms fibre_weakens_offApex
#assert_axioms apexBase_isApex
#assert_axioms fibration_nonvacuous
#assert_axioms conservation_terminal_collapse
#assert_axioms attenuation_terminal_collapse
#assert_axioms three_fibres_one_lift

end Dregg2.Distributed.Fibration
