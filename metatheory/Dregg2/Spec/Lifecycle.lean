/-
# Dregg2.Spec.Lifecycle — the cell lifecycle as the ATTESTED DUAL of creation.

Part of the **factored middle layer** (between ultra-abstract `Core`/`Laws`/`Boundary`
and the executable `Exec.*`), this module makes the cell lifecycle a first-class
structural shape and pins the one fact that the whole "no terminal object" gap was
hiding: **termination is not deletion, it is *witnessed* ending** — the categorical
dual of *witnessed* creation.

## Grounding

This is the faithful Lean image of `cell/src/lifecycle.rs` (`CellLifecycle`,
`DeathCertificate`, `ArchivalAttestation`, `DeathReason`), itself the realization of
`PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4/§1.5/§4.2` — the cell-lifecycle terminal-object
gap. It sits ALONGSIDE `Dregg2.Liveness` (GC-as-cell-liveness): `Liveness` answers
"*when* is a cell collectable?" (reachability vs lease); THIS module answers "*what
are the states*, and what does it MEAN to end?" The two meet at the epistemic limit
(`§5` below), where this module reuses `Liveness`'s honest impossibility wholesale.

## The thesis: creation ⊣ termination, both ATTESTED

A cell's life is a state machine with a **generative** end (it was *made* — by some
factory constructor, recorded in a `Provenance`) and a **terminal** end (it *ended* —
witnessed by a `DeathCertificate` or a migration tombstone). These are dual:

  * **creation is PROVABLE** — provenance is a finite, first-party artifact (which
    constructor ran); you can always exhibit it. This is the *generative* object.
  * **termination is ATTESTED, not inferred** — a cell is `Destroyed` only with a
    witnessed certificate bound into its final state (you prove "retired", you do not
    infer it from absence); `Migrated` carries a destination tombstone. This is the
    *terminal* object: one-way, no inverse (`terminal_rejects_transition`).
  * **archival is the IVC/recursive-fold reused as history-compression** — an
    `Archived` cell stays live, but its receipt-chain *prefix* is folded into ONE
    `checkpointHash` (`archival_is_fold`): the same fold that powers IVC, here
    compressing history rather than verifying it.

## The epistemic limit (the sharpest part, §5)

Creation is provable; **distributed death is not**. You cannot constructively
co-witness that a cross-vat reference cycle is garbage — that is exactly
`Dregg2.Liveness.crossvat_cycle_leaks` / `dead_undecidable`, the undecidable corner.
So reclamation degrades to a *temporal* bound: a cell past its **lease-expiry height**
may be reclaimed regardless of the (un-provable) distributed-liveness fact. The lease
is the provable alternative to the impossible proof. `reclaim_by_lease` is PROVED;
`distributed_death_not_co_witnessable` is PROVED too (see its theorem below — a one-line
delegation to `Dregg2.Liveness.dead_undecidable`'s halting reduction; pinned in
`Dregg2/Claims.lean` §19).

Style: spec-first, grind up. Computable classifiers are *defined* and their
classifications *proved*; the duality and fold are faithful `Prop`s; the one genuine
impossibility is itself a proved negative theorem (the halting-reduction above).
-/
import Dregg2.Liveness
import Dregg2.Tactics

namespace Dregg2.Spec

open Dregg2.Liveness

universe u

/-! ## §0 — Abstract carriers.

Per the shared discipline: NO `Nat`-for-semantics. A cryptographic `Digest` (the
checkpoint / certificate / attestation hashes that in `lifecycle.rs` are `[u8; 32]`),
a `CellId` (the migration destination / cell identity), and a `FactoryId` (which
constructor made the cell) are **abstract type parameters**. They carry only the
structure the obligations need — decidable equality on `Digest` for the fold, nothing
more. -/

variable {Digest : Type u} {CellId : Type u} {FactoryId : Type u}

/-! ## §1 — The lifecycle state machine.

The five canonical states of `CellLifecycle` (`lifecycle.rs:37`). `Sealed` is
reversible quiescence; `Archived` keeps the cell live (history pruned only);
`Migrated` and `Destroyed` are the two *terminal* shapes. The attesting payloads
(`§2`) ride inside the constructors — this is what makes ending *witnessed*. -/

/-- A reason for retirement (`DeathReason`, `lifecycle.rs:206`): substrate-opaque.
`Custom` carries an app-specific reason `Digest`. -/
inductive DeathReason (Digest : Type u) : Type u where
  /-- Voluntary retirement by the owner (graceful shutdown). -/
  | voluntary
  /-- Forced retirement by the federation (policy). -/
  | forced
  /-- Retired because a migration destination accepted custody. -/
  | migrated
  /-- App-specific reason; the `Digest` is opaque to the substrate. -/
  | custom (reasonHash : Digest)

/-- **`Provenance`** — the GENERATIVE witness (creation side of the duality). Every
freshly-constructed cell records *which factory constructor made it* (`Exec.Factory`)
and a `birthCommitment` — the state commitment at birth. This is a finite, first-party
artifact: creation is always provable by exhibiting it. -/
structure Provenance (FactoryId Digest : Type u) where
  /-- The factory constructor that produced this cell. -/
  factory : FactoryId
  /-- The state commitment the cell carried at birth. -/
  birthCommitment : Digest
  /-- Federation height at which the cell entered `Live`. -/
  bornAtHeight : Nat

/-- **`DeathCertificate`** — the TERMINAL witness (termination side of the duality;
`DeathCertificate`, `lifecycle.rs:148`). A *witnessed* death: it binds the cell's
final receipt head, its final state commitment, the height, and a `reason`. A holder
of the cell's final commitment can PROVE "this cell was retired" rather than inferring
it from absence. -/
structure DeathCertificate (CellId Digest : Type u) where
  /-- The cell being retired. -/
  cellId : CellId
  /-- Receipt hash of the cell's last live turn (the chain terminator). -/
  lastReceiptHash : Digest
  /-- The state commitment at the moment of death. -/
  finalStateCommitment : Digest
  /-- Federation height at which destruction took effect. -/
  destroyedAtHeight : Nat
  /-- Why the cell was retired. -/
  reason : DeathReason Digest

/-- **`ArchivalAttestation`** — the HISTORY-COMPRESSION witness (`ArchivalAttestation`,
`lifecycle.rs:248`). An archived cell stays live, but its receipt-chain prefix over
`[archiveStart, archiveEnd]` is summarized by ONE `checkpointHash`; the live chain's
`previous_receipt_hash` at `archiveEnd + 1` points into it. `checkpointHash` is the
IVC-style *fold* of the prefix (`§3`). -/
structure ArchivalAttestation (CellId Digest : Type u) where
  /-- The cell whose chain prefix is archived. -/
  cellId : CellId
  /-- First chain height included (inclusive). -/
  archiveStart : Nat
  /-- Last chain height included (inclusive). -/
  archiveEnd : Nat
  /-- BLAKE3-style fold of the off-chain archival blob — the checkpoint into which the
  prefix is compressed. -/
  checkpointHash : Digest

/-- **`Lifecycle`** — the canonical lifecycle state machine (`CellLifecycle`,
`lifecycle.rs:37`). The default for a freshly-constructed cell is `live`. -/
inductive Lifecycle (CellId FactoryId Digest : Type u) : Type u where
  /-- Effects flow normally. -/
  | live
  /-- Reversible quiescence: rejects new effects, state/history preserved, `unseal`
  returns to `live`. Carries a `reasonHash` and the seal height. -/
  | sealed (reasonHash : Digest) (sealedAt : Nat)
  /-- Still live, but the receipt-chain prefix was folded into a checkpoint. -/
  | archived (att : ArchivalAttestation CellId Digest)
  /-- TOMBSTONE: relocated to another federation; the local copy retains a pointer at
  the destination cell id. Terminal. -/
  | migrated (dest : CellId)
  /-- Permanently retired, with a witnessed death certificate bound in. Terminal. -/
  | destroyed (cert : DeathCertificate CellId Digest)

namespace Lifecycle

variable {CellId FactoryId Digest : Type u}

/-! ## §2 — The two computable classifiers, and their proven classifications. -/

/-- **`acceptsEffects`** — does this state accept new effects? `true` for `live` and
`archived` ONLY (archival prunes history but the cell stays live); `false` for
`sealed`, `migrated`, `destroyed` (`accepts_effects`, `lifecycle.rs:109`). -/
def acceptsEffects : Lifecycle CellId FactoryId Digest → Bool
  | live          => true
  | archived _    => true
  | sealed _ _    => false
  | migrated _    => false
  | destroyed _   => false

/-- **`isTerminal`** — is this state *permanent* (no further transition)? `true` for
`destroyed` and `migrated` ONLY (`is_terminal`, `lifecycle.rs:116`). These are the two
**terminal objects** of the lifecycle category: one-way, no inverse. -/
def isTerminal : Lifecycle CellId FactoryId Digest → Bool
  | destroyed _   => true
  | migrated _    => true
  | live          => false
  | sealed _ _    => false
  | archived _    => false

/-- **PROVED classification of `acceptsEffects`**: a state accepts effects iff it is
`live` or `archived`. This is the exhaustive characterization (the dual of the Rust
`matches!`), turned into an `Iff` with real content (case split, not `rfl`). -/
theorem acceptsEffects_iff (s : Lifecycle CellId FactoryId Digest) :
    acceptsEffects s = true ↔ (s = live ∨ ∃ att, s = archived att) := by
  cases s with
  | live        => simp [acceptsEffects]
  | archived a  => simp [acceptsEffects]
  | sealed r h  => simp [acceptsEffects]
  | migrated d  => simp [acceptsEffects]
  | destroyed c => simp [acceptsEffects]

/-- **PROVED classification of `isTerminal`**: a state is terminal iff it is `destroyed`
or `migrated`. -/
theorem isTerminal_iff (s : Lifecycle CellId FactoryId Digest) :
    isTerminal s = true ↔ ((∃ c, s = destroyed c) ∨ ∃ d, s = migrated d) := by
  cases s with
  | live        => simp [isTerminal]
  | archived a  => simp [isTerminal]
  | sealed r h  => simp [isTerminal]
  | migrated d  => simp [isTerminal]
  | destroyed c => simp [isTerminal]

/-- A terminal state never accepts effects: the two classifiers are coherent
(`is_terminal → ¬accepts_effects`, as `lifecycle.rs` tests assert for both
`Destroyed` and `Migrated`). PROVED by case split. -/
theorem terminal_rejects_effects (s : Lifecycle CellId FactoryId Digest)
    (h : isTerminal s = true) : acceptsEffects s = false := by
  cases s with
  | live        => simp [isTerminal] at h
  | archived a  => simp [isTerminal] at h
  | sealed r h' => simp [isTerminal] at h
  | migrated d  => simp [acceptsEffects]
  | destroyed c => simp [acceptsEffects]

/-! ## §3 — Transitions, and the terminal object's one-wayness. -/

/-- **`Transition s s'`** — the legal one-step lifecycle transitions (the state-machine
edges of `lifecycle.rs`'s doc-comment §24–35; `LifecycleTransitionError::Terminal`,
`lifecycle.rs:168`, is precisely the *absence* of any edge out of a terminal state).

Note: EVERY edge originates at a non-terminal source. There is deliberately NO
constructor whose source is `migrated` or `destroyed` — that is the categorical
terminal-object property (`is_terminal` = one-way, no inverse), enforced *structurally*
by which constructors exist. -/
inductive Transition : Lifecycle CellId FactoryId Digest → Lifecycle CellId FactoryId Digest → Prop where
  /-- `live → sealed`. -/
  | seal (r : Digest) (at_ : Nat) : Transition live (sealed r at_)
  /-- `sealed → live` (reversible: the `Unseal` effect). -/
  | unseal (r : Digest) (at_ : Nat) : Transition (sealed r at_) live
  /-- `live → archived` (history fold; cell stays live). -/
  | archive (att : ArchivalAttestation CellId Digest) : Transition live (archived att)
  /-- `archived → archived` (re-archive a longer prefix; still live). -/
  | rearchive (a a' : ArchivalAttestation CellId Digest) : Transition (archived a) (archived a')
  /-- `live → migrated` (relocate; produces a terminal tombstone). -/
  | migrate (dest : CellId) : Transition live (migrated dest)
  /-- `live → destroyed` (witnessed permanent retirement; terminal). -/
  | destroy (cert : DeathCertificate CellId Digest) : Transition live (destroyed cert)
  /-- `archived → destroyed` (an archived-but-live cell may still be retired). -/
  | destroyArchived (att : ArchivalAttestation CellId Digest) (cert : DeathCertificate CellId Digest) :
      Transition (archived att) (destroyed cert)

/-- **`terminal_rejects_transition` — the categorical terminal-object law.**
No transition leaves a terminal state: if `isTerminal s` then there is NO `s'` with
`Transition s s'`. This is `LinearityClass.Terminal` made structural — the terminal
object has no outgoing morphism, so ending is irreversible (`migrated`/`destroyed`
admit no inverse, no `unseal`-style return). Proved by exhausting the (impossible)
transition constructors out of a terminal source. -/
theorem terminal_rejects_transition (s s' : Lifecycle CellId FactoryId Digest)
    (hterm : isTerminal s = true) : ¬ Transition s s' := by
  intro htr
  -- Every `Transition` constructor has a non-terminal source; case on the transition
  -- and discharge each via the incompatible `isTerminal` value of its source.
  cases htr <;> simp [isTerminal] at hterm

/-- Corollary: a `migrated` tombstone is a dead end — no transition out. -/
theorem migrated_terminal (dest : CellId) (s' : Lifecycle CellId FactoryId Digest) :
    ¬ Transition (migrated dest) s' :=
  terminal_rejects_transition _ s' (by simp [isTerminal])

/-- Corollary: a `destroyed` cell is a dead end — no transition out. -/
theorem destroyed_terminal (cert : DeathCertificate CellId Digest)
    (s' : Lifecycle CellId FactoryId Digest) :
    ¬ Transition (destroyed cert) s' :=
  terminal_rejects_transition _ s' (by simp [isTerminal])

/-! ## §4 — The creation ⊣ termination duality, and archival-as-IVC-fold.

A *birth* is a (non-terminal) `live` state paired with the `Provenance` that produced
it; an *ending* is a transition into a terminal state carrying its witness. The thesis:
these are symmetric *witnessed* acts — generative and terminal poles of one linear
object. -/

/-- **`Birth`** — a cell that has entered `live` carrying its generative witness. The
state is `live` (default-constructed, `lifecycle.rs:85`) and the provenance records the
constructor. Creation is exhibited by this pair: provable, first-party. -/
structure Birth (CellId FactoryId Digest : Type u) where
  /-- The lifecycle state at birth — always `live`. -/
  state : Lifecycle CellId FactoryId Digest
  /-- Proof that it is `live` (a fresh cell is not born terminal). -/
  isLive : state = live
  /-- The generative witness (which factory made it). -/
  prov : Provenance FactoryId Digest

/-- **`Ending s`** — a cell's terminal state together with its termination witness.
`destroyedBy` supplies the `DeathCertificate` for a `destroyed` state, or the
destination `CellId` tombstone for a `migrated` state — every ending is witnessed. -/
inductive Ending : Lifecycle CellId FactoryId Digest → Type u where
  /-- Retired with a witnessed death certificate. -/
  | byCertificate (cert : DeathCertificate CellId Digest) : Ending (destroyed cert)
  /-- Migrated, leaving a destination tombstone. -/
  | byMigration (dest : CellId) : Ending (migrated dest)

/-- **`creation_and_death_are_dual` — the duality theorem.** Symmetric
witnessed poles: from a `Birth` (a `live` state with a `Provenance`) and any `Ending`
(a terminal state with its witness), BOTH ends carry a finite witness AND the two
states are distinct poles — the birth state accepts effects while the ending
state is terminal (hence rejects them). Formally: birth accepts effects, ending is
terminal, and they are unequal lifecycle states. This is the generative/terminal
`LinearityClass` duality: creation and termination are symmetric *attested* acts, not
a constructor + a silent `free()`. -/
theorem creation_and_death_are_dual
    (b : Birth CellId FactoryId Digest)
    {s : Lifecycle CellId FactoryId Digest} (e : Ending s) :
    acceptsEffects b.state = true ∧ isTerminal s = true ∧ b.state ≠ s := by
  refine ⟨?_, ?_, ?_⟩
  · -- birth is `live`, which accepts effects (the generative pole)
    rw [b.isLive]; simp [acceptsEffects]
  · -- the ending state is terminal (the terminal pole)
    cases e with
    | byCertificate _ => simp [isTerminal]
    | byMigration _   => simp [isTerminal]
  · -- the poles are distinct: `live` ≠ any terminal state
    rw [b.isLive]
    cases e with
    | byCertificate _ => intro h; cases h
    | byMigration _   => intro h; cases h

/-- **`birthProvable` — creation is constructively provable.** Trivially, from any
`Birth` we can EXHIBIT the generative witness (the factory that ran). There is no dual
"death is exhibitable for free": for *distributed* death the witness cannot be
constructed (`§5`). This asymmetry is the whole point. -/
theorem birthProvable (b : Birth CellId FactoryId Digest) :
    ∃ f : FactoryId, b.prov.factory = f :=
  ⟨b.prov.factory, rfl⟩

/-- **`FoldsTo prefix h`** — the abstract IVC/recursive-fold relation: the
receipt-chain prefix `prefix` (a list of receipt `Digest`s) folds, under the kernel's
recursive accumulator `accum`, into the single checkpoint digest `h`. This is the SAME
fold that drives IVC (verify a chain by folding step proofs); here it is reused as
**history-compression**. Modelled as a `foldl` over an abstract step `accum` from an
abstract `seed` — a faithful `Prop`, agnostic to the concrete hash. -/
def FoldsTo (accum : Digest → Digest → Digest) (seed : Digest)
    (prefixChain : List Digest) (h : Digest) : Prop :=
  prefixChain.foldl accum seed = h

/-- **`archival_is_fold` — archival IS the fold (faithful).** An
`ArchivalAttestation` whose `checkpointHash` was produced by folding the receipt-chain
prefix is exactly a `FoldsTo` witness: the checkpoint summarizes the prefix via the
recursive accumulator. Given the prefix and that `checkpointHash = foldl accum seed
prefix`, we obtain `FoldsTo accum seed prefix att.checkpointHash`. This is the IVC fold
reused for history compression — `Archived` keeps the cell live (`acceptsEffects`) but
replaces its prior history with this one digest. -/
theorem archival_is_fold
    (accum : Digest → Digest → Digest) (seed : Digest)
    (att : ArchivalAttestation CellId Digest) (prefixChain : List Digest)
    (hfold : att.checkpointHash = prefixChain.foldl accum seed) :
    FoldsTo accum seed prefixChain att.checkpointHash := by
  -- `FoldsTo` unfolds to `foldl … = checkpointHash`; reverse the hypothesis.
  unfold FoldsTo
  exact hfold.symm

/-- An archived cell stays live: it still `acceptsEffects`. The fold compressed
*history*, not the cell's capacity to act (`lifecycle.rs:351` test). Reinforces that
archival is history-compression, NOT a step toward termination. -/
theorem archived_still_live (att : ArchivalAttestation CellId Digest) :
    acceptsEffects (archived att : Lifecycle CellId FactoryId Digest) = true := by
  simp [acceptsEffects]

/-! ## §5 — THE EPISTEMIC LIMIT: creation is provable, distributed death is not.

The sharp asymmetry. `§4` showed creation is always exhibitable (`birthProvable`). The
dual — exhibiting that a cell is *distributedly* dead — is NOT constructively possible:
a cross-vat reference cycle pins every refcount ≥ 1 yet is genuine garbage, and no
sound local-evidence collector can reclaim it (`Liveness.crossvat_cycle_leaks`); worse,
`Dead` admits no decision procedure (`Liveness.dead_undecidable`). So reclamation
degrades to a *temporal* substitute for the proof that cannot exist: **lease expiry**. -/

/-- A cell's reclamation-relevant bookkeeping: its operational `Lifecycle` and the
`Lease` (`Liveness.Lease`) whose `expiresAt` height bounds the leak. The lease is the
first-class liveness bound dregg2 promotes `expires_at` to (`study-gc.md §5`). -/
structure Reclaimable (CellId FactoryId Digest : Type u) where
  /-- The cell's current lifecycle state. -/
  state : Lifecycle CellId FactoryId Digest
  /-- Its export lease — the temporal bound that replaces the impossible deadness proof. -/
  lease : Lease

open Nat.Partrec (Code) in
open Nat.Partrec.Code in
/--
**`distributed_death_not_co_witnessable` — the honest negative obligation.**

Dual to `birthProvable`: there is NO uniform constructive co-witness of distributed
deadness. Stated in `Liveness`'s own shape — no **computable** decider soundly-and-
completely decides `Dead` of the gadget cell across the `haltGraph`-of-halting family —
and a one-line **DELEGATION** to `Liveness`'s standing impossibility,
`Dregg2.Liveness.dead_undecidable`, rather than re-deriving it.

The obstruction is computability, not a distributed adversary: `reachable` is semi-
decidable (a path is a finite `Verify`), so `Dead = ¬reachable` is co-semi-decidable at
best, and is in fact undecidable — `dead_undecidable` proves it by reducing the halting
problem to deadness. (As `Liveness` records, the *arbitrary*-`Bool`-decider form is
classically vacuous; the load-bearing claim is the absence of a *computable* decider.)
This is the precise sense in which *creation is provable but distributed death is not*. -/
theorem distributed_death_not_co_witnessable (n : ℕ) :
    ¬ ∃ d : Code → Bool,
        Computable d ∧
        (∀ c : Code, d c = true ↔ Dead (haltGraph ((eval c n).Dom)) 1) :=
  Dregg2.Liveness.dead_undecidable n

/-- **`reclaimableByLease r now`** — the locally-decidable reclamation trigger: a cell
is reclaimable at height `now` iff its lease has lapsed (`Liveness.leaseExpired`). This
is the *temporal* predicate that stands in for the impossible global deadness proof —
decidable, partition-tolerant, graph-privacy-respecting. -/
def reclaimableByLease (r : Reclaimable CellId FactoryId Digest) (now : Nat) : Bool :=
  leaseExpired r.lease now

/--
**`reclaim_by_lease` — the PROVED alternative to the impossible proof.**

A cell past its lease-expiry height may be reclaimed **regardless** of any (un-provable)
distributed-liveness fact. Concretely: take a cell that is `Dead` in the
liveness graph `g` (the case no collector can detect, `crossvat_cycle_leaks`) AND whose
lease has lapsed at `now`. Then it is *not* operationally `Live` (`Liveness.Live`) — so
the runtime reclaims it — **even though** `Dead` was never decided. The reclamation is
driven entirely by the locally-decidable `reclaimableByLease`, never by a deadness proof.

This is the dregg2-coherent resolution of `§5`'s asymmetry: where creation is witnessed
by `Provenance` (provable), distributed death is witnessed only by the *clock*
(`leaseExpired`) — a temporal bound substituting for the categorical-dual proof that
cannot exist. PROVED via `Liveness.lease_completes_deadness`.
-/
theorem reclaim_by_lease
    (r : Reclaimable CellId FactoryId Digest) (now : Nat)
    (g : LivenessGraph) (c : Liveness.CellId)
    (hdead : Dead g c)
    (hexp : reclaimableByLease r now = true) :
    ¬ Live g r.lease now c := by
  -- `reclaimableByLease` is definitionally `leaseExpired r.lease now`; feed it to
  -- `lease_completes_deadness`, which kills both disjuncts of `Live` (reachability by
  -- `hdead`, the lease-not-expired escape by `hexp`).
  have hexp' : leaseExpired r.lease now = true := hexp
  exact lease_completes_deadness g r.lease now c hdead hexp'

/-- **`creation_provable_death_temporal` — the asymmetry, stated as one theorem.**
For any `Birth` (creation side) and any `Reclaimable` whose lease has lapsed over a
`Dead` cell (the distributed-death side): the factory that created the cell
is EXHIBITABLE (a constructive witness), while the dead cell is reclaimed by lease and
is NOT operationally `Live` — its death was *timed out*, never proved. Creation:
provable. Distributed death: temporal. -/
theorem creation_provable_death_temporal
    (b : Birth CellId FactoryId Digest)
    (r : Reclaimable CellId FactoryId Digest) (now : Nat)
    (g : LivenessGraph) (c : Liveness.CellId)
    (hdead : Dead g c) (hexp : reclaimableByLease r now = true) :
    (∃ f : FactoryId, b.prov.factory = f) ∧ ¬ Live g r.lease now c :=
  ⟨birthProvable b, reclaim_by_lease r now g c hdead hexp⟩

end Lifecycle

/-! ## §6 — Axiom-hygiene tripwires.

Pin the clean keystones: each must depend ONLY on the three standard kernel axioms
(no `sorryAx`). These cover both classifier classifications, the terminal-object
one-wayness, the creation↔termination duality, archival-as-fold, the lease
fallback, AND — via the halting reduction in `Dregg2.Liveness` — the
distributed-death undecidability (`distributed_death_not_co_witnessable`). -/

#assert_axioms Lifecycle.acceptsEffects_iff
#assert_axioms Lifecycle.isTerminal_iff
#assert_axioms Lifecycle.terminal_rejects_effects
#assert_axioms Lifecycle.terminal_rejects_transition
#assert_axioms Lifecycle.migrated_terminal
#assert_axioms Lifecycle.destroyed_terminal
#assert_axioms Lifecycle.creation_and_death_are_dual
#assert_axioms Lifecycle.birthProvable
#assert_axioms Lifecycle.archival_is_fold
#assert_axioms Lifecycle.distributed_death_not_co_witnessable
#assert_axioms Lifecycle.archived_still_live
#assert_axioms Lifecycle.reclaim_by_lease
#assert_axioms Lifecycle.creation_provable_death_temporal

end Dregg2.Spec
