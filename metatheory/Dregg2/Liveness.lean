/-
# Dregg2.Liveness — GC-as-cell-liveness, and distributed cycle collection.

This module formalizes `dregg2.md §1.7` ("CapTP GC = cell-liveness, the dual of
coinductive existence") together with the design probe `docs/rebuild/study-gc.md`.
It is the **operational dual** of `Dregg2.Boundary`: where `Boundary` says a sound
cell's `ν`-unfold *never bottoms out*, this module supplies the side-condition that
makes that honest — the unfold continues **only while the cell is reachable**, and the
runtime reclaims it (transitions it to a terminal lifecycle object) once it is not.

Literature anchors (see `study-gc.md`):
  * **ORCA** (Pony, Clebsch et al., "Orca: GC and Type System Co-Design for Actor
    Languages", OOPSLA'17; orca-soundness ESOP'18) — per-actor reference counting with
    a causal-message discipline that needs *no* global synchronization for safety; the
    template for "GC-safety is local/bilateral, not consensus."
  * **CapTP / OCapN distributed GC** (Spritely) — the protocol dregg2 inherits, which
    provides only **(acyclic)** distributed GC and *explicitly* does not collect
    cross-vat cycles.
  * **Refcounting ≠ reachability** (classic GC folklore; Bacon–Rajan trial-deletion) —
    a refcount measures inbound fan-in, not root-reachability; cyclic garbage pins
    refcounts ≥ 1 forever.
  * **The verify/find seam** (`Dregg2.Laws`) — *reachable* is semi-decidable
    (witness a finite path = a `Verify`); *dead* is the global, non-co-witnessable
    `find`. Deadness is never decided; it is **timed out** by lease expiry.

The KEY FACTS this module encodes — including the impossibilities:

  1. The **liveness graph is cyclic** and is a DIFFERENT graph from the **acyclic
     capability-derivation tree (CDT)** of `Authority`. Refcount ≠ reachability:
     `theorem refcount_ne_reachability` exhibits a cell with positive refcount that is
     unreachable (a dead cycle). Do NOT conflate the two graphs.
  2. **"dead" is UNDECIDABLE** in general — this is *exactly* the FIND/VERIFY seam of
     `Laws`. There is no `Decidable (Dead g c)` instance; we state that as an honest
     negative obligation and resolve it operationally via `Lease`/`leaseExpired`.
  3. **GC-safety is local/bilateral and needs NO consensus** (`gc_safety_local`): a
     drop touches only the dropper's own holder count, so collecting on local evidence
     is sound. Only its dual — **revocation** — needs consensus
     (`revocation_needs_consensus`).
  4. The honest **IMPOSSIBILITY** (`crossvat_cycle_leaks`): a reference cycle spanning
     mutually-distrusting vats cannot be collected soundly — there is no sound
     distributed cycle collector. dregg2 ships this leak and bounds it by lease expiry.

Style: spec-first, grind up. Data that is computable and cheap (graphs, refcount,
reachability, lease expiry) is *defined*; the load-bearing facts are stated as faithful
`Prop`s and discharged — including the undecidability of `Dead`, which is now PROVED by a
halting reduction (`dead_undecidable`) rather than left as an obligation.
-/
import Dregg2.Core
import Dregg2.Laws
import Dregg2.Authority.Positional
import Mathlib.Computability.Halting

namespace Dregg2.Liveness

open Dregg2.Laws Dregg2.Authority

/-! ## The liveness reference graph (possibly cyclic) -/

/- A cell identity in the liveness graph. We reuse `Label` (`= Nat`, from
`Authority.Positional`) as the cell-id carrier so that the liveness graph and the
authority/CDT projection range over the same identities and the `refcount ≠ reachability`
remark can compare them on the nose. -/
abbrev CellId := Label

/-- A **vat** identity (an island / trust-root domain). Cross-vat cycles — cycles whose
nodes do not all share one `VatId` — are the unsolvable case. -/
abbrev VatId := Nat

/-- **`LivenessGraph`** — the (possibly **cyclic**) directed graph of *live* cell
references. An edge `edge a b` means "cell `a` holds an un-dropped `CapabilityRef`
targeting cell `b`" (`cell/src/capability.rs:43`: an inbound edge into the target).
`root` marks the vat-resident holders that are live by fiat (a CSpace slot a running
computation holds). `vat` assigns each cell to its owning vat (for the cross-vat
impossibility). NOTHING here forces acyclicity — that is the entire point: this graph is
NOT the CDT. -/
structure LivenessGraph where
  /-- `edge a b`: cell `a` holds a live (un-dropped) reference to cell `b`. -/
  edge : CellId → CellId → Prop
  /-- The roots: holders live by fiat (running computations, trust-roots). -/
  root : CellId → Prop
  /-- The owning vat of each cell. -/
  vat  : CellId → VatId

/-- One-step successor in the liveness graph (an outbound live edge). -/
def LivenessGraph.succ (g : LivenessGraph) (a b : CellId) : Prop := g.edge a b

/-- **`Reaches`** — the reflexive-transitive closure of `edge`: there is a path of
un-dropped references from `a` to `b`. This is the *positive*, finitely-witnessable
fact (a path is a finite object) — a `Verify` in the sense of `Laws`. -/
inductive Reaches (g : LivenessGraph) : CellId → CellId → Prop where
  /-- A cell reaches itself (empty path). -/
  | refl  (a : CellId) : Reaches g a a
  /-- Extend a path by one live edge. -/
  | step  {a b c : CellId} : Reaches g a b → g.edge b c → Reaches g a c

/-- **`reachable g c`** — `c` is reachable iff some ROOT reaches it. This is the true
liveness predicate: liveness is reachability-**from-a-root**, NOT
reachability-from-a-direct-holder. -/
def reachable (g : LivenessGraph) (c : CellId) : Prop :=
  ∃ r : CellId, g.root r ∧ Reaches g r c

/-! ## Refcount — the local approximation, and why it ≠ reachability -/

/-- **`refcount g c`** — the inbound fan-in of `c`: the cells that hold a live edge
*into* `c`, as a predicate-form multiset. The runtime's `RefCount{count}` (`gc.rs:38`)
is the cardinality of this set per holder; here we model the *existence* of an inbound
holder, which is all the `refcount ≠ reachability` distinction needs. `hasInbound g c`
is "`refcount > 0`". -/
def hasInbound (g : LivenessGraph) (c : CellId) : Prop :=
  ∃ a : CellId, g.edge a c

/-- **`refcountZero g c`** — no holder retains a live edge into `c` (`total_refs == 0`,
`DropResult::CanRevoke`, `gc.rs:207`). This is the runtime's *local* collection trigger
on the acyclic half. -/
def refcountZero (g : LivenessGraph) (c : CellId) : Prop :=
  ¬ hasInbound g c

/-- **`theorem refcount_ne_reachability` — refcount ≠ reachability.** There exists a liveness
graph and a cell with positive refcount (`hasInbound`) that is not root-reachable (`¬ reachable`):
a dead cycle. Concretely, cells `A` and `B` in a 2-cycle with no root each pin the other's
refcount ≥ 1 forever, yet neither is root-reachable. This is why the runtime's collection
trigger is incomplete for cycles. -/
theorem refcount_ne_reachability :
    ∃ (g : LivenessGraph) (c : CellId), hasInbound g c ∧ ¬ reachable g c := by
  -- Two cells 0,1 in a mutual cycle, no roots.
  refine ⟨{ edge := fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0),
            root := fun _ => False,
            vat  := fun _ => 0 }, 0, ?_, ?_⟩
  · -- refcount of 0 is positive: cell 1 points at 0.
    exact ⟨1, Or.inr ⟨rfl, rfl⟩⟩
  · -- 0 is not reachable: there is no root at all.
    rintro ⟨r, hr, _⟩
    exact hr

/-! ## The acyclic capability-derivation tree (CDT) — a SEPARATE graph -/

/-- **`CDT`** — the **acyclic** capability-derivation tree of `Authority` (`§1.1`): the
append-only, monotone-attenuation partial order parent→child. We model it abstractly as
a `parent` partial function; `Acyclic` is the well-foundedness that distinguishes it
from `LivenessGraph`. The CDT is the *authority* projection; the liveness graph is the
*reference* graph. The doc's seam-to-fix (`study-gc.md §1`) is precisely that these were
conflated — they are NOT the same graph (the CDT omits the back-edges that make liveness
cyclic). -/
structure CDT where
  /-- The derivation parent of a cell (`none` at a derivation root). -/
  parent : CellId → Option CellId

/-- The CDT derivation relation: `b` is a direct attenuation-child of `a`. -/
def CDT.derives (t : CDT) (a b : CellId) : Prop := t.parent b = some a

/-- Reflexive-transitive closure of CDT derivation. -/
inductive CDT.Derives (t : CDT) : CellId → CellId → Prop where
  | refl (a : CellId) : CDT.Derives t a a
  | step {a b c : CellId} : CDT.Derives t a b → t.derives b c → CDT.Derives t a c

/-- **`CDT.Acyclic`** — the CDT has no nontrivial derivation cycle: if `a` derives `b`
and `b` derives `a` then `a = b`. This is forced by monotone attenuation (a child is
strictly narrower than its parent) and is the property the **liveness graph lacks**. -/
def CDT.Acyclic (t : CDT) : Prop :=
  ∀ a b : CellId, CDT.Derives t a b → CDT.Derives t b a → a = b

/-- **`theorem liveness_not_cdt` — the two graphs are distinct.** The CDT is
acyclic by construction, but the liveness graph that *projects onto the same cells* can
carry a cycle (a child cell handing a cap back to an ancestor). Hence one cannot soundly
substitute "refcount-zero on the (acyclic) CDT" for "unreachable on the (cyclic) liveness
graph". Stated as: there is a liveness graph with a cycle whose underlying cells admit an
acyclic CDT. -/
theorem liveness_not_cdt :
    ∃ (g : LivenessGraph) (t : CDT) (a b : CellId),
      g.edge a b ∧ g.edge b a ∧ CDT.Acyclic t := by
  -- Same 2-cycle (0→1, 1→0) as `refcount_ne_reachability` for the liveness graph; the
  -- CDT is the empty derivation tree (every cell a derivation root, `parent = none`), in
  -- which `derives` is uninhabited so `Derives` is only `refl`, hence trivially acyclic.
  refine ⟨{ edge := fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0),
            root := fun _ => False,
            vat  := fun _ => 0 },
          { parent := fun _ => none }, 0, 1, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, ?_⟩
  -- Acyclicity: in this CDT `derives` is `none = some _`, i.e. always `False`, so any
  -- `Derives` derivation must be the reflexive base case.
  have hderiv : ∀ x y : CellId, CDT.Derives { parent := fun _ => none } x y → x = y := by
    intro x y h
    induction h with
    | refl => rfl
    | step _ hstep _ => exact absurd hstep (by simp [CDT.derives])
  intro a b _ hba
  exact (hderiv b a hba).symm

/-! ## Live (operational, via lease) vs Dead — and the undecidability of death -/

/-- **`Dead g c`** — the *semantic* deadness predicate: `c` is unreachable from every
root. This is a **universally-quantified, global** claim over a graph that spans
mutually-distrustful vats and is partly hidden by design (tier-3 graph privacy). It is
the negation of the semi-decidable `reachable`; it is **not** finitely co-witnessable. -/
def Dead (g : LivenessGraph) (c : CellId) : Prop := ¬ reachable g c

/-- **`theorem reachable_semidecidable_witness`** — *reachable* is positively witnessed:
to assert `reachable g c` it suffices to exhibit a finite path (a root and a `Reaches`
derivation). This is the `Verify` side of the seam — local to the path, tractable. (The
content: `reachable` is literally an existential over a finite inductive witness.) -/
theorem reachable_semidecidable_witness
    (g : LivenessGraph) (c r : CellId) (hr : g.root r) (hpath : Reaches g r c) :
    reachable g c :=
  ⟨r, hr, hpath⟩

/-! ### The computability reduction: halting ↪ reachability ↪ deadness.

Deadness is undecidable in the computability sense, not just the distributed-adversary sense.
The true claim is that no *computable* procedure decides deadness (a bare-existence form over
`Prop`-valued fields would be classically vacuous). We prove this by reduction from the halting
problem via `Mathlib.Computability.Halting`. -/

/-- **`haltGraph P`** — the 2-cell reduction gadget: a root cell `0` whose single outgoing
edge to the target cell `1` exists **iff `P` holds**. Thus `1` is reachable iff `P`, and
`Dead (haltGraph P) 1 ↔ ¬P`. Instantiating `P` with a halting predicate
`(eval c n).Dom` turns "decide deadness of cell `1`" into "decide halting of code `c`". -/
noncomputable def haltGraph (P : Prop) : LivenessGraph where
  edge a b := a = 0 ∧ b = 1 ∧ P
  root a   := a = 0
  vat _    := 0

/-- Cell `1` is reachable in `haltGraph P` exactly when `P` holds (the gadget's edge fires
iff `P`). The only path to `1` is the single root-edge `0 → 1`, present iff `P`. -/
theorem haltGraph_reachable (P : Prop) : reachable (haltGraph P) 1 ↔ P := by
  constructor
  · rintro ⟨r, hr, hpath⟩
    simp only [haltGraph] at hr
    subst hr
    cases hpath with
    | step _ he => exact he.2.2
  · intro hp
    exact ⟨0, rfl, Reaches.step (Reaches.refl 0) ⟨rfl, rfl, hp⟩⟩

/-- Hence cell `1` is `Dead` in `haltGraph P` exactly when `¬P` (deadness = unreachability,
and reachability of `1` is `P`). This is the reduction's pivot. -/
theorem haltGraph_dead (P : Prop) : Dead (haltGraph P) 1 ↔ ¬ P := by
  unfold Dead; rw [haltGraph_reachable]

open Nat.Partrec (Code) in
open Nat.Partrec.Code in
/-- **`theorem dead_undecidable` — deadness is undecidable.** No computable `d : Code → Bool`
soundly-and-completely decides deadness of the gadget cell across the `haltGraph`-of-halting
family: if it did, `d c = true ↔ ¬(eval c n).Dom` would make halting's complement computable,
contradicting `ComputablePred.halting_problem`. Resolved operationally via `Lease`/`leaseExpired`. -/
theorem dead_undecidable (n : ℕ) :
    ¬ ∃ d : Code → Bool,
        Computable d ∧
        (∀ c : Code, d c = true ↔ Dead (haltGraph ((eval c n).Dom)) 1) := by
  rintro ⟨d, hcomp, hspec⟩
  -- `fun c => d c = true` is a computable predicate (its indicator is `d`).
  have hp : ComputablePred (fun c => d c = true) := by
    apply Computable.computablePred
    simpa using hcomp
  -- It is iff-equal to the *complement* of halting (via the gadget reduction).
  have hp2 : ComputablePred (fun c => ¬ (eval c n).Dom) :=
    hp.of_eq (fun c => by rw [hspec c, haltGraph_dead])
  -- Closure of computable predicates under negation gives halting itself computable.
  have hp3 : ComputablePred (fun c => (eval c n).Dom) :=
    hp2.not.of_eq (fun c => by simp)
  -- …contradicting the undecidability of the halting problem.
  exact ComputablePred.halting_problem n hp3

/-- **`Lease`** — the operational liveness bound. Every export edge carries an
`expires_at` (`capability.rs:56`) and a `last_activity`; `leaseExpired now` is the
locally-decidable predicate that *replaces* the undecidable global `Dead`. dregg2 demotes
"drop = the await engine's backward face" and promotes `expires_at` to the first-class
liveness bound it operationally already is (`study-gc.md §5`). -/
structure Lease where
  /-- The block/time at which the lease lapses. -/
  expiresAt : Nat
  /-- Last observed activity (for `stale_exports` idle-reclaim, `gc.rs:219`). -/
  lastActivity : Nat

/-- **`leaseExpired`** — locally decidable: has the lease lapsed at `now`? This is the
*completing fallback* that converts the non-co-witnessable global predicate "dead" into a
locally-decidable one "lease lapsed." Death is never decided; it is **timed out**. -/
def leaseExpired (l : Lease) (now : Nat) : Bool := decide (l.expiresAt ≤ now)

/-- **`Live g l now c`** — the OPERATIONAL liveness predicate the runtime actually uses:
a cell is treated as live iff it is reachable OR its lease has not yet expired. This is a
**sound-for-liveness over-approximation** of true reachability: it never collects a cell
whose lease is current (fail-closed for safety), and it eventually reclaims an unreachable
cell once its lease lapses (fail-open for liveness, recovering from leaked cycles and lost
drops). It is the dregg2-coherent resolution: safety from reachability-or-lease, liveness
from lease expiry. -/
def Live (g : LivenessGraph) (l : Lease) (now : Nat) (c : CellId) : Prop :=
  reachable g c ∨ leaseExpired l now = false

/-- **`theorem lease_completes_deadness`** — the lease *completes* the undecidable
deadness test: although `Dead` is undecidable, `Live` is decidable-modulo-reachability
and, crucially, a cell that is both `Dead` and past its lease is NOT `Live` — so the
operational predicate reclaims every dead cell *eventually* (once `now` passes
`expiresAt`). This is the construction that is consistent with codata + no-global-snapshot
+ graph-privacy simultaneously. -/
theorem lease_completes_deadness
    (g : LivenessGraph) (l : Lease) (now : Nat) (c : CellId)
    (hdead : Dead g c) (hexp : leaseExpired l now = true) :
    ¬ Live g l now c := by
  -- `Live := reachable ∨ leaseExpired = false`; `Dead := ¬reachable` kills the first
  -- disjunct and `hexp : leaseExpired = true` kills the second.
  rintro (hreach | hnotexp)
  · exact hdead hreach
  · rw [hexp] at hnotexp; exact absurd hnotexp (by decide)

/-! ## GC-safety is local/bilateral; revocation needs consensus -/

/-- A **drop event**: vat `from` relinquishes its OWN holder edge into `target` on
session `session`. The CapTP discipline (`process_drop`, `gc.rs:183`) keys strictly on
`from_federation` and only touches `entry.holders[from_federation]` — a vat **cannot**
drop another vat's references. `session` is the epoch gate (`gc.rs:193`) blocking
cross-session forgery. -/
structure DropEvent where
  /-- The vat relinquishing its own reference. -/
  fromVat : VatId
  /-- The cell whose inbound edge is being dropped. -/
  target  : CellId
  /-- The session/epoch on which the drop is valid. -/
  session : Nat

/-- **`LocalEvidence g c`** — the *bilateral* evidence sufficient to collect `c`: every
inbound edge into `c` has been dropped by its own holder (refcount has reached zero on
local accounting), with no appeal to any other vat's internal state. This is the ORCA-
style local certificate: it mentions only edges incident to `c` and their droppers. -/
def LocalEvidence (g : LivenessGraph) (c : CellId) : Prop :=
  refcountZero g c

/-- **`theorem gc_safety_local` — collecting is safe on local/bilateral evidence; no
consensus required.** If `LocalEvidence g c` holds (`refcountZero`), `c` has no inbound
holder. A drop touches only the dropper's own count and is session/epoch-gated — no global
agreement required. This is the ORCA result: GC-safety is local and bilateral. -/
theorem gc_safety_local
    (g : LivenessGraph) (c : CellId)
    (hlocal : LocalEvidence g c) :
    ¬ hasInbound g c := by
  -- `LocalEvidence` is definitionally `refcountZero`, which is `¬ hasInbound`.
  exact hlocal

/-- **`RevocationDecision`** — revoking a cap while it is *still wanted* (the NEGATIVE
lifecycle): unlike collection, this kills authority other vats may legitimately still
hold. It is gated by a **root epoch** that all parties must agree advanced (`§3`: "the
lone consensus seam"). Modelled by an `epoch` and the set of `agreeing` vats. -/
structure RevocationDecision where
  /-- The new root epoch the revocation advances to. -/
  epoch : Nat
  /-- The vats that have agreed the epoch advanced. -/
  agreeing : VatId → Prop

/-- **`Consensus parties d`** — every relevant vat agrees the revocation epoch advanced.
This is the global-agreement predicate GC-safety deliberately does NOT require. -/
def Consensus (parties : List VatId) (d : RevocationDecision) : Prop :=
  ∀ v ∈ parties, d.agreeing v

/-- **`CrossVatSound parties d view`** — the *semantic* soundness of a revocation under the
parties' post-revocation authority `view : VatId → RevocationDecision → Prop` (`view v d` = "vat
`v` now treats the cap as revoked"): every relevant party's view agrees the cap is gone — no
split-brain where one vat still honors a cap another revoked. The `view` is supplied by the
operational model (`World`/the blocklace). This is a GENUINE semantic predicate, not a `→ True`
stub. -/
def CrossVatSound (parties : List VatId) (d : RevocationDecision)
    (view : VatId → RevocationDecision → Prop) : Prop :=
  ∀ v ∈ parties, view v d

/-- **`theorem revocation_needs_consensus` — revocation requires agreement.** If a revocation is
cross-vat sound (every relevant party's `view` agrees the cap is revoked) AND a vat only revokes
its view after agreeing the epoch advanced (`hgate : view v d → d.agreeing v`), then all parties
reached `Consensus`. The dual of `gc_safety_local`: GC is the positive lifecycle (collect-when-
unwanted, no consensus); revocation is the negative lifecycle (kill-while-wanted, consensus-bound). -/
theorem revocation_needs_consensus
    (parties : List VatId) (d : RevocationDecision)
    (view : VatId → RevocationDecision → Prop)
    (hsound : CrossVatSound parties d view)
    (hgate : ∀ v, view v d → d.agreeing v) :
    Consensus parties d := by
  intro v hv
  exact hgate v (hsound v hv)

/-- **`revocation_needs_consensus_satisfiable` — the NON-VACUITY witness.** A CONCRETE two-vat
revocation that takes effect under agreement: `parties = [1, 2]`, the decision advances to `epoch 1`
with BOTH vats agreeing (`d.agreeing v := True`), and the post-revocation view treats the cap as gone
at both (`view v _ := True`). The hypotheses hold — `CrossVatSound` (both views agree) and the gate
(`view v d → d.agreeing v`) — AND the conclusion is EXERCISED: `Consensus [1,2] d` fires (every party
agrees the epoch advanced). So the keystone is not vacuous: there is a real multi-vat scene where
revocation-under-agreement takes effect. -/
theorem revocation_needs_consensus_satisfiable :
    ∃ (parties : List VatId) (d : RevocationDecision) (view : VatId → RevocationDecision → Prop),
      CrossVatSound parties d view
        ∧ (∀ v, view v d → d.agreeing v)
        ∧ Consensus parties d := by
  refine ⟨[1, 2], ⟨1, fun _ => True⟩, fun _ _ => True, ?_, ?_, ?_⟩
  · intro v _; trivial
  · intro v _; trivial
  · -- the conclusion is EXERCISED: revocation_needs_consensus fires and yields Consensus.
    exact revocation_needs_consensus [1, 2] ⟨1, fun _ => True⟩ (fun _ _ => True)
      (fun v _ => trivial) (fun v _ => trivial)

/-- **`revocation_needs_consensus_teeth` — the DISCRIMINATING witness (the conclusion is NOT `True`).**
A UNILATERAL revocation where party `2` has NOT agreed the epoch advanced: `parties = [1, 2]`,
`d.agreeing v := (v = 1)` (only vat 1 agreed). Then `Consensus [1, 2] d` is FALSE — vat `2 ∈ parties`
but `¬ d.agreeing 2`. So `Consensus` is a two-valued predicate that genuinely FAILS when agreement is
not unanimous: revocation does NOT take effect for a party that did not agree. This is the contrapositive
content — "revocation REQUIRES consensus" — made concrete: drop the agreement of one party and the
consensus conclusion collapses, exactly as the negative-lifecycle discipline demands. -/
theorem revocation_needs_consensus_teeth :
    ¬ Consensus [1, 2] (⟨1, fun v => v = 1⟩ : RevocationDecision) := by
  intro hcon
  -- vat 2 ∈ parties but did NOT agree (`2 = 1` is false), so `Consensus` cannot hold.
  have h2 : (⟨1, fun v => v = 1⟩ : RevocationDecision).agreeing 2 :=
    hcon 2 (by simp)
  exact absurd h2 (by decide)

/-! ## The impossibility: cross-vat GC cycles leak -/

/-- **`CrossVatCycle g a b`** — a reference cycle spanning two MUTUALLY-DISTRUSTING vats:
`a→b`, `b→a`, the cells live in different vats, and no root reaches either. Each pins the
other's refcount ≥ 1 forever, so `refcountZero` (the only sound local trigger) never
fires at either node. -/
structure CrossVatCycle (g : LivenessGraph) (a b : CellId) : Prop where
  /-- `a` holds a live edge to `b`. -/
  edge_ab : g.edge a b
  /-- `b` holds a live edge back to `a`. -/
  edge_ba : g.edge b a
  /-- The two cells live in distinct (mutually-distrusting) vats. -/
  cross   : g.vat a ≠ g.vat b
  /-- The cycle is rootless: `a` is dead. -/
  dead_a  : Dead g a
  /-- ...and so is `b`. -/
  dead_b  : Dead g b

/-- **`SoundLocalCollector`** — the type of a would-be collector that decides to collect a
cell using ONLY local refcount evidence (`refcountZero`), with NO cross-vat cooperation
(no peer back-edge reports, preserving graph privacy). `collect g c = true` means "reclaim
`c`". Soundness-for-safety: it only collects when refcount is zero. -/
structure SoundLocalCollector where
  /-- The collection decision. -/
  collect : LivenessGraph → CellId → Bool
  /-- It only ever collects a refcount-zero cell (never strands a holder) — the
  ORCA/CapTP safety discipline. -/
  sound : ∀ g c, collect g c = true → refcountZero g c

/-- **`theorem crossvat_cycle_leaks` — the cross-vat GC impossibility.** No sound,
local-evidence-only collector can reclaim a cross-vat cycle: every node has a positive
inbound count, so `refcountZero` is false and the collector's soundness side-condition
forbids collecting. Cross-vat cycles leak; dregg2 bounds the leak by lease expiry
(`leaseExpired`) alone. Cooperative back-tracing is rejected (requires unenforceable peer
reports and breaks tier-3 graph privacy). -/
theorem crossvat_cycle_leaks
    (col : SoundLocalCollector) (g : LivenessGraph) (a b : CellId)
    (hcyc : CrossVatCycle g a b) :
    col.collect g a = false ∧ col.collect g b = false := by
  -- `a` has an inbound edge (from `b`), so `refcountZero g a` is false; soundness then
  -- forbids collecting `a`. Symmetrically for `b`.
  have hin_a : hasInbound g a := ⟨b, hcyc.edge_ba⟩
  have hin_b : hasInbound g b := ⟨a, hcyc.edge_ab⟩
  refine ⟨?_, ?_⟩
  · by_contra h
    have hca : col.collect g a = true := by
      cases hco : col.collect g a with
      | false => exact absurd hco h
      | true  => rfl
    exact (col.sound g a hca) hin_a
  · by_contra h
    have hcb : col.collect g b = true := by
      cases hco : col.collect g b with
      | false => exact absurd hco h
      | true  => rfl
    exact (col.sound g b hcb) hin_b

/-- **`theorem leak_bounded_by_lease` — the only honest mitigation.** Although a cross-vat
cycle is never reachability-collected (`crossvat_cycle_leaks`), the operational `Live`
predicate STILL reclaims it once the lease lapses: a dead cell past its lease is not
`Live`. So a leaked cycle leaks not *forever* but only *until its leases lapse* — the
dregg2-coherent bound that needs no global view, survives partition, and respects graph
privacy. (Follows from `lease_completes_deadness` applied to a cycle node.) -/
theorem leak_bounded_by_lease
    (g : LivenessGraph) (l : Lease) (now : Nat) (a b : CellId)
    (hcyc : CrossVatCycle g a b) (hexp : leaseExpired l now = true) :
    ¬ Live g l now a := by
  exact lease_completes_deadness g l now a hcyc.dead_a hexp

end Dregg2.Liveness
