/-
# Dregg2.Distributed.Fibration — the distributed-adversarial semantics as ONE indexed structure.

Titanium Phase 1 (`docs/rebuild/TITANIUM-PHASE.md` §"PHASE 1 · THE FIBRATION"). The per-deployment
guarantees of dregg are not independent theorems; they are **fibres of one structure** — a fibration

    p : E → B   over the base   B = Topology × FaultModel × CryptoStrength

of *deployment conditions*. A point `b ∈ B` is a concrete deployment (e.g. single-machine / honest /
ideal-crypto … up to global-mesh / sleepy-Byzantine / computational). The fibre over `b` is the
system's guarantee *as it actually holds there*, packaged as a **measured bound**: the strong local
property degraded by a stated, finite amount.

## The geometry (the single-machine principle, formalized)

* The **terminal fibre** sits over the apex `apex = (single-machine, honest, ideal)`. There the bound
  collapses to `0` — the strong local property. `lift_collapse` is **DEFINITIONAL** (it reads the
  apex's bound off the structure; it is not a re-proof).
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
   exactly conserves: window `0`). Its *distributed* bound — by how much a partition can transiently
   skew the visible total before reconciliation — is **not yet derived in Lean**, so it is carried as
   an EXPLICIT named hypothesis `DistConservationBound` (never `sorry`, never `True`).
3. **Attenuation** — the terminal fibre is `Authority.Caveat.attenuate_narrows` (a child token admits
   ⊆ the parent: window `0`, the inclusion is exact). Its *distributed* bound — stale-token honoring
   across a partition, exactly the revocation-style window — is carried as the named hypothesis
   `DistAttenuationBound` until it is derived from the revocation fibre.

The honesty discipline: a fibre whose distributed bound is not yet a theorem is a **named open**, not
a vacuity. The `lift` functor is real precisely because (a) it has a non-vacuity witness (a deployment
where the bound is positive) AND (b) a negative tooth (a deployment where the guarantee
weakens — the same `tightness_tooth` instance, re-read as "the fibre over this base point is strictly
weaker than the terminal fibre").

Pure, computable where decidable.
-/
import Dregg2.Distributed.Revocation

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
NOT `sorry`/`True`: a `DistConservationBound` supplies the window and the after-window property; from
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
NAMED distributed-bound hypotheses (`DistConservationBound`/`DistAttenuationBound`) — never `sorry`,
never `True`. This is the milestone-1 statement: one base, one fibre shape, one `lift`. -/
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
#assert_axioms fibre_weakens_offApex
#assert_axioms apexBase_isApex
#assert_axioms fibration_nonvacuous
#assert_axioms conservation_terminal_collapse
#assert_axioms attenuation_terminal_collapse
#assert_axioms three_fibres_one_lift

end Dregg2.Distributed.Fibration
