/-
# Dregg2.Substrate.VerbCompression — the VERB-COMPRESSION verdict: the kernel under the
universal map (the rotation question, investigated and PROVED both ways).

THE QUESTION. `Substrate/VerbRegistry.lean` proves the eight survivor verbs minimal — but its
minimality theorem quantifies over `verbBehavior : Verb → Substance × Polarity`, i.e. over
TODAY'S flat ontology (one structural rule per substance). The universal-map rotation
(REFINEMENT-DESIGN Decision 1 + task #165: caps / nullifiers / heap as collections of ONE
sorted-map family, `Substrate/Heap.lean`) re-houses every substance as a COLLECTION of that one
family. Under that ontology, is 8 still minimal — or do grant / revoke / lifecycle /
shield-unshield collapse into GUARDED WRITES to distinguished collections?

## THE VERDICT (every clause below is a theorem in this file)

The honest answer is BOTH, with the boundary exactly where the proof obligations live:

  * **lifecycle COMPRESSES into the landed caveat class.** The seal/unseal/destroy automaton is
    a guarded write whose guard reads only `(old value at the written key, new value)` —
    `lifecycle_compresses_local` puts `lifeGuard` in `LocalGuard`, the `SlotCaveat.eval actor
    old new` class `stateStepGuarded` already enforces. The one-way teeth survive verbatim:
    `life_reseal_refused`, `life_destroyed_terminal`.
  * **revoke COMPRESSES into the same class.** Narrowing (`new ⊆ old`) is a local guard
    (`revoke_compresses_local`); a committed narrow write provably narrows
    (`narrow_committed_narrows`), widening is refused (`demo_widen_refused`), and removal
    (`held \ drop`) always passes (`revoke_removal_admitted`). The delegation-epoch bump is the
    `new = old + 1` local guard — the existing MonotonicSequence caveat shape.
  * **unshield COMPRESSES — but ONLY past a PROVEN guard-algebra extension.** The double-spend
    gate is the freshness guard `(get m nf).isNone`, which is EXACTLY the absence atom
    (`fresh_is_absence_atom`) — and `freshness_not_positive` PROVES no conjunction of the landed
    POSITIVE atoms (`HeapKernel.HeapAtom` = `heapContains`/`heapGetEq`, the deployed `.all`
    shape) expresses it. The absence atom's semantic floor is already in-tree: the proven
    non-membership opening (`Heap.get_none_of_gap`). Anti-double-spend survives compression:
    `fresh_write_no_replay`. Shield is the same fresh write on the commitment collection, and
    evidence-monotonicity survives: `fresh_write_grows`.
  * **grant COMPRESSES — but ONLY past a SECOND, strictly stronger extension.** Non-amplification
    ("granted ⊆ some held authority of the delegator") is a guard that compares the WRITTEN value
    against the pre-state opening of ANOTHER key. `grant_guard_not_local` proves it is outside
    the local class; `grant_guard_not_literal` proves it is outside ALL conjunctions of literal
    atoms (contains / absent / getEq — even WITH the absence extension). It IS a guarded write
    under the order-relational guard `grantGuard` (`new ⊆ get(delegatorKey)`), and the guard IS
    the guarantee: `grant_non_amplifying`; an amplifying grant is refused
    (`demo_amplify_refused`); the real `Exec.attenuate` always passes (`attenuate_passes_guard`).
  * **move SEPARATES — conservation is NOT a guard, in ANY guard class.**
    `gwrite_conservation_trivializes` proves: for EVERY guard (arbitrary decidable predicate of
    the whole pre-state, actor, key, value — the maximal class), a committed single-key write
    that preserves the collection total writes the value already there. So a conservation-
    respecting guarded write can never debit or credit (`demo_debit_breaks_conservation`), and
    the genuine two-key move (`moveStep`, which conserves: `move_conserves`) is NOT any guarded
    write (`move_not_single_write` — it changes two openings, a guarded write changes at most
    one, `gwStep_changes_at_most_one`). Conservation lives in the ARITY (the paired cancelling
    deltas), not in the guard algebra.
  * **create SEPARATES by the same arity argument.** Its existence facet is the SAME absence-
    guarded fresh write as unshield (`fresh_write_no_replay` = no-rebirth), but bundle birth
    initializes several addresses atomically — not one guarded write
    (`create_birth_not_single_write`). (Its authority polarity — no prior holder — also inverts
    the write gate, per `verbBehavior .create = (.birth, .introduce)`.)
  * **exercise was NEVER a verb** — `exercise_already_structure` re-pins
    `VerbRegistry.classify .ExerciseViaCapability = .turnStructure .exercise`.

## What this means

The kernel under the universal map is **create · guarded-write · move** (3 verbs;
`compressed_kernel_three`), with exercise staying turn-structure. FIVE of the seven verb
constructors (write, grant, revoke, shieldUnshield, lifecycle) are ONE verb — so the 8-verb
minimality is an ARTIFACT of the flat ontology (`verb_minimality_is_ontology_relative`: distinct
verbs share a compressed fate). BUT the verb distinctions do NOT evaporate — they survive as a
PROVEN-STRICT stratification of the guard algebra:

      local (actor, old, new)  ──  the SlotCaveat class      : write, lifecycle, revoke
      + literal atoms          ──  the landed HeapAtom class : heap-write
      + the absence atom       ──  proven non-membership     : unshield, shield, create-legs
      + order-relational atoms ──  `new ⊆ get(k)`            : grant (non-amplification)

with each extension PROVEN proper (`freshness_not_positive`, `grant_guard_not_literal`) and
conservation PROVEN outside the whole tower (`gwrite_conservation_trivializes`). The honest
counter-argument was right about WHERE the obligations live, wrong about what they protect:
grant's authority algebra and unshield's freshness are GUARD-CLASS obligations (they ride the
rotation as guard-algebra extensions); move's conservation is a SHAPE obligation (it keeps its
own verb).

## Scope & provenance

NEW file; self-contained over `Substrate.Heap`'s proven sorted-map machinery (`get`/`set`/
frames), `Exec.Caps`'s REAL rights lattice (`ExecAuth = Finset Auth`, the genuine `⊆` order
`attenuate_subset` narrows along), and `Substrate.VerbRegistry`'s reified verb roster. The
separation theorems are stated against atom CONJUNCTIONS — the deployed guard shape
(`caveatsAdmit` / `heapAtomsAdmit` are both `.all`). The executor-state bridge (interpreting
`RecordKernelState` itself into the one map) rides THE ONE ROTATION; this module settles the
guard-class mathematics that rotation decision needs.

⛑ AND THAT BRIDGE LANDED — `Exec/UniversalBridge.lean` IS it, and cites these very lines as its
motivation (`Exec/UniversalBridge.lean:4-5`). It proves the commuting square for ALL THREE
compressed verbs against the LIVE executable steps (`stateStepGuarded` / `recCexec` /
`createCellStep`): `gwrite_is_memory_program` / `move_is_memory_program` /
`create_is_memory_program` state that the projection of the executor's post-state EQUALS the fold
of the verb's emitted Blum trace over the projection of the pre-state, where `uproj` is TOTAL over
all 17 `RecordKernelState` fields plus the receipt log (the `registers` domain deliberately empty —
per-proof VM transients, never persistent state). So "rides THE ONE ROTATION" reads as a completed
dependency, not a pending one. Every theorem `#assert_axioms`-pinned.
-/
import Dregg2.Substrate.Heap
import Dregg2.Substrate.VerbRegistry
import Dregg2.Exec.Caps
import Dregg2.Tactics

namespace Dregg2.Substrate.VerbCompression

open Dregg2.Authority (Auth Cap capAuthConferred)
open Dregg2.Exec (ExecAuth confRights attenuate attenuate_subset)

/-! ## §0 — the COMPRESSED VERB: one guarded write over the universal map.

The candidate compressed kernel's workhorse. State = collections of ONE sorted-map family
(`Substrate.Heap §1`, keys `ℤ` — the deployed key-hash address space); the verb = `gwStep`:
evaluate a guard against the pre-state, then perform ONE sorted insert-or-update. Everything the
conjecture says should collapse must become an instance of THIS step with an explicit guard. -/

/-- **A guard** — a decidable predicate of the WHOLE pre-collection, the actor, the written key,
and the written value. Deliberately the MAXIMAL class: the separation theorems below quantify
over all of it (so they are guard-class-independent), and the named sub-classes (§1) carve out
what the deployed guard algebra can actually express. -/
def UGuard (ν : Type) : Type := List (ℤ × ν) → ℤ → ℤ → ν → Bool

/-- **`gwStep` — the compressed guarded-write verb.** Guard against the pre-state, then ONE
`Heap.set` (sorted insert-or-update). Fail-closed: a refused guard commits nothing. Every
compression claim in this file is "verb X = `gwStep` with guard G". -/
def gwStep {ν : Type} (g : UGuard ν) (m : List (ℤ × ν)) (actor key : ℤ) (new : ν) :
    Option (List (ℤ × ν)) :=
  if g m actor key new = true then some (Heap.set m key new) else none

/-- A committed guarded write factors: the guard held, and the post-state is exactly the sorted
insert-or-update. -/
theorem gwStep_factors {ν : Type} {g : UGuard ν} {m m' : List (ℤ × ν)} {actor key : ℤ} {new : ν}
    (h : gwStep g m actor key new = some m') :
    g m actor key new = true ∧ m' = Heap.set m key new := by
  unfold gwStep at h
  by_cases hg : g m actor key new = true
  · rw [if_pos hg] at h
    exact ⟨hg, (Option.some.inj h).symm⟩
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- READ-AFTER-WRITE through the compressed verb (from `Heap.get_set_self`). -/
theorem gwStep_writes {ν : Type} {g : UGuard ν} {m m' : List (ℤ × ν)} {actor key : ℤ} {new : ν}
    (h : gwStep g m actor key new = some m') : Heap.get m' key = some new := by
  obtain ⟨-, rfl⟩ := gwStep_factors h
  exact Heap.get_set_self m key new

/-- FRAME through the compressed verb: every other key keeps its opening (the universal-map
frame discipline, from `Heap.get_set_frame` — unconditional, no crypto). -/
theorem gwStep_frame {ν : Type} {g : UGuard ν} {m m' : List (ℤ × ν)} {actor key : ℤ} {new : ν}
    (h : gwStep g m actor key new = some m') (k' : ℤ) (hk : k' ≠ key) :
    Heap.get m' k' = Heap.get m k' := by
  obtain ⟨-, rfl⟩ := gwStep_factors h
  exact Heap.get_set_frame m key k' new hk

/-- The sorted invariant is preserved by the compressed verb (`Heap.set_sorted`). -/
theorem gwStep_sorted {ν : Type} {g : UGuard ν} {m m' : List (ℤ × ν)} {actor key : ℤ} {new : ν}
    (h : gwStep g m actor key new = some m') (hs : Heap.SortedKeys m) : Heap.SortedKeys m' := by
  obtain ⟨-, rfl⟩ := gwStep_factors h
  exact Heap.set_sorted m key new hs

/-- **ARITY: a guarded write changes AT MOST ONE opening.** If two keys both changed, they are
the same key. The lemma both arity separations (move, create) ride. -/
theorem gwStep_changes_at_most_one {ν : Type} {g : UGuard ν} {m m' : List (ℤ × ν)}
    {actor key : ℤ} {new : ν} (h : gwStep g m actor key new = some m') (k₁ k₂ : ℤ)
    (h₁ : Heap.get m' k₁ ≠ Heap.get m k₁) (h₂ : Heap.get m' k₂ ≠ Heap.get m k₂) : k₁ = k₂ := by
  obtain ⟨-, rfl⟩ := gwStep_factors h
  by_cases e₁ : k₁ = key
  · by_cases e₂ : k₂ = key
    · rw [e₁, e₂]
    · exact absurd (Heap.get_set_frame m key k₂ new e₂) h₂
  · exact absurd (Heap.get_set_frame m key k₁ new e₁) h₁

#assert_axioms gwStep_factors
#assert_axioms gwStep_writes
#assert_axioms gwStep_frame
#assert_axioms gwStep_sorted
#assert_axioms gwStep_changes_at_most_one

/-! ## §1 — the GUARD CLASSES (the deployed guard algebra, reified).

The compression question is only non-vacuous relative to a guard CLASS — with arbitrary guards
every verb "compresses" trivially (the guard can encode the whole step). The deployed classes:

  * `LocalGuard` — guards reading only `(actor, old value at the written key, new value)`: the
    `SlotCaveat.eval actor old new` class `EffectsState.caveatsAdmit` enforces today.
  * `LitAtom` conjunctions — guards built from per-key LITERAL atoms, evaluated fail-closed as a
    conjunction (`.all`): `contains`/`getEq` are EXACTLY the landed `HeapKernel.HeapAtom`
    algebra; `absent` is the extension the unshield compression needs (its semantic floor = the
    proven non-membership opening `Heap.get_none_of_gap`).
  * order-relational guards — `new ⊆ get(k)` for a key `k` chosen by the instance (§4's
    `grantGuard`): the rights ORDER enters the guard language. Proven strictly beyond both
    classes above. -/

/-- **The local guard class** — the `SlotCaveat` shape: the guard factors through
`(actor, the written key's pre-opening, the written value)`. -/
def LocalGuard {ν : Type} (g : UGuard ν) : Prop :=
  ∃ p : ℤ → Option ν → ν → Bool, ∀ m actor key new, g m actor key new = p actor (Heap.get m key) new

/-- **The literal atoms** — per-key membership/value tests, the `HeapAtom` shape plus the
absence extension. `contains`/`getEq` mirror `HeapKernel.HeapAtom.heapContains`/`heapGetEq`
LITERALLY; `absent` is the non-membership atom (NOT yet in the landed algebra — that gap is the
point of `freshness_not_positive`). -/
inductive LitAtom (ν : Type) where
  /-- the key is present (the landed `heapContains`). -/
  | contains (k : ℤ)
  /-- the key is ABSENT (the non-membership atom — the proposed extension). -/
  | absent (k : ℤ)
  /-- the key holds exactly `v` (the landed `heapGetEq`). -/
  | getEq (k : ℤ) (v : ν)

/-- The key an atom reads (every literal atom reads exactly one opening). -/
def LitAtom.key {ν : Type} : LitAtom ν → ℤ
  | .contains k => k
  | .absent k => k
  | .getEq k _ => k

/-- Atom truth as a function of the read opening — the factorization that makes "an atom sees
only one key" a definitional fact. -/
def LitAtom.evalAt {ν : Type} [DecidableEq ν] : LitAtom ν → Option ν → Bool
  | .contains _, o => o.isSome
  | .absent _, o => o.isNone
  | .getEq _ v, o => decide (o = some v)

/-- Evaluate an atom against a collection (read the one opening, test it). -/
def LitAtom.eval {ν : Type} [DecidableEq ν] (a : LitAtom ν) (m : List (ℤ × ν)) : Bool :=
  a.evalAt (Heap.get m a.key)

/-- The conjunction shape the deployed guard algebra uses (`caveatsAdmit`/`heapAtomsAdmit` are
both `.all` — fail-closed conjunction). The separation theorems are stated against THIS shape. -/
def litConj {ν : Type} [DecidableEq ν] (atoms : List (LitAtom ν)) (m : List (ℤ × ν)) : Bool :=
  atoms.all (fun a => a.eval m)

/-- An atom is POSITIVE iff it is in the LANDED algebra (`contains`/`getEq` — `HeapAtom` has no
negative atom today). -/
def LitAtom.Positive {ν : Type} : LitAtom ν → Prop
  | .absent _ => False
  | .contains _ => True
  | .getEq _ _ => True

/-! ## §2 — LIFECYCLE COMPRESSES (into the landed local class, teeth intact).

The seal/unseal/destroy automaton (`RecordKernelState.lifecycle` discriminants: 0 = Live,
1 = Sealed, 3 = Destroyed; `EffectsState.sealStep`'s one-way gate) is a guarded write to the
lifecycle collection whose guard reads ONLY the written key's old discriminant and the new one —
the `SlotCaveat.eval actor old new` class, EXACTLY. Nothing beyond the landed guard algebra is
needed: lifecycle was a guarded write all along. -/

/-- The lifecycle automaton's edge relation, as a guard kernel: Live→Sealed (seal),
Sealed→Live (unseal), {Live,Sealed}→Destroyed (destroy). Everything else — including EVERY edge
out of Destroyed — is refused. Mirrors dregg1's `CellLifecycle` transitions
(`cell/src/lifecycle.rs`), discriminants as in `RecordKernel.lifecycle`. -/
def lifeAdmits (old new : ℤ) : Bool :=
  (old == 0 && new == 1) || (old == 1 && new == 0) || ((old == 0 || old == 1) && new == 3)

/-- **The lifecycle guard** — `lifeAdmits` against the written key's pre-opening (absent key =
discriminant 0 = Live, the kernel's `DEFAULTS Live`). -/
def lifeGuard : UGuard ℤ := fun m _actor key new => lifeAdmits ((Heap.get m key).getD 0) new

/-- **LIFECYCLE COMPRESSES.** `lifeGuard` is in the LOCAL class — the landed `SlotCaveat` shape.
The lifecycle verb is a guarded write under TODAY'S guard algebra. -/
theorem lifecycle_compresses_local : LocalGuard lifeGuard :=
  ⟨fun _ old new => lifeAdmits (old.getD 0) new, fun _ _ _ _ => rfl⟩

/-- Sealing a (default-)Live cell commits — the compressed seal is live (witness TRUE). -/
theorem life_seal_commits_default {m : List (ℤ × ℤ)} {actor key : ℤ}
    (h : Heap.get m key = none) : gwStep lifeGuard m actor key 1 = some (Heap.set m key 1) := by
  have hg : lifeGuard m actor key 1 = true := by
    unfold lifeGuard
    rw [h]
    decide
  unfold gwStep
  rw [if_pos hg]

/-- Unsealing a Sealed cell commits (the automaton's return edge survives compression). -/
theorem life_unseal_commits {m : List (ℤ × ℤ)} {actor key : ℤ}
    (h : Heap.get m key = some 1) : gwStep lifeGuard m actor key 0 = some (Heap.set m key 0) := by
  have hg : lifeGuard m actor key 0 = true := by
    unfold lifeGuard
    rw [h]
    decide
  unfold gwStep
  rw [if_pos hg]

/-- **The no-double-seal tooth survives compression** (`seal_irreversible`'s shape): re-sealing
an already-Sealed cell is refused by the GUARD — fail-closed, no special case. -/
theorem life_reseal_refused {m : List (ℤ × ℤ)} {actor key : ℤ}
    (h : Heap.get m key = some 1) : gwStep lifeGuard m actor key 1 = none := by
  have hg : lifeGuard m actor key 1 = false := by
    unfold lifeGuard
    rw [h]
    decide
  unfold gwStep
  rw [if_neg (by simp [hg])]

/-- **Destroyed is TERMINAL under compression**: from discriminant 3, EVERY lifecycle write is
refused — the death certificate's finality is a guard fact. -/
theorem life_destroyed_terminal {m : List (ℤ × ℤ)} {actor key : ℤ} (v : ℤ)
    (h : Heap.get m key = some 3) : gwStep lifeGuard m actor key v = none := by
  have hg : lifeGuard m actor key v = false := by
    unfold lifeGuard
    rw [h]
    show lifeAdmits 3 v = false
    unfold lifeAdmits
    simp [show ((3 : ℤ) == 0) = false from by decide, show ((3 : ℤ) == 1) = false from by decide]
  unfold gwStep
  rw [if_neg (by simp [hg])]

-- Non-vacuity: the compressed automaton, executable (TRUE and FALSE witnesses per edge).
#guard (gwStep lifeGuard ([] : List (ℤ × ℤ)) 0 5 1).isSome           -- seal a default-Live cell
#guard (gwStep lifeGuard [((5 : ℤ), (1 : ℤ))] 0 5 1).isNone           -- re-seal REFUSED
#guard (gwStep lifeGuard [((5 : ℤ), (1 : ℤ))] 0 5 0).isSome           -- unseal Sealed → Live
#guard (gwStep lifeGuard [((5 : ℤ), (1 : ℤ))] 0 5 3).isSome           -- destroy from Sealed
#guard (gwStep lifeGuard [((5 : ℤ), (3 : ℤ))] 0 5 0).isNone           -- Destroyed is terminal
#guard (gwStep lifeGuard ([] : List (ℤ × ℤ)) 0 5 2).isNone            -- no edge to Migrated (oos)

#assert_axioms lifecycle_compresses_local
#assert_axioms life_seal_commits_default
#assert_axioms life_unseal_commits
#assert_axioms life_reseal_refused
#assert_axioms life_destroyed_terminal

/-! ## §3 — REVOKE COMPRESSES (narrowing is a local guard over the REAL rights lattice).

The revocation family edits the capability collection by NARROWING: `recKRevokeTarget` filters a
slot (`new = old.filter …`), attenuation keeps a subset, the delegation-epoch bump is
`new = old + 1` (the MonotonicSequence caveat shape, already landed). Over the universal map the
cap collection holds `ExecAuth = Finset Auth` rights at edge addresses, and the whole family is
ONE guarded write with the narrowing guard `new ⊆ old` — local, hence in the landed class. -/

/-- **The narrowing guard** — admit a write iff the written rights are `⊆` the rights ALREADY at
the written key (fail-closed on an absent key: nothing held, nothing to narrow). The
revoke/attenuate guard over the genuine `ExecAuth` order (`Exec/Caps §0`). -/
def narrowGuard : UGuard ExecAuth := fun m _actor key new =>
  ((Heap.get m key).map (fun held => decide (new ⊆ held))).getD false

/-- **REVOKE COMPRESSES.** The narrowing guard is LOCAL — the landed `SlotCaveat` class. The
revoke/attenuate family is a guarded write under TODAY'S guard algebra. -/
theorem revoke_compresses_local : LocalGuard narrowGuard :=
  ⟨fun _ old new => (old.map (fun held => decide (new ⊆ held))).getD false, fun _ _ _ _ => rfl⟩

/-- A committed narrowing write provably NARROWS: the written rights are `⊆` the previously held
rights (the `attenuate_subset` discipline, enforced by the guard). -/
theorem narrow_committed_narrows {m m' : List (ℤ × ExecAuth)} {actor key : ℤ} {new : ExecAuth}
    (h : gwStep narrowGuard m actor key new = some m') :
    ∃ held, Heap.get m key = some held ∧ new ⊆ held := by
  obtain ⟨hg, -⟩ := gwStep_factors h
  unfold narrowGuard at hg
  cases hh : Heap.get m key with
  | none =>
      rw [hh] at hg
      exact absurd hg (by simp)
  | some held =>
      rw [hh] at hg
      refine ⟨held, rfl, ?_⟩
      have hd : decide (new ⊆ held) = true := hg
      exact of_decide_eq_true hd

/-- Removal always passes the narrowing guard: revoking rights `drop` from a held set commits
(`revoke_removes`'s shape — `held \ drop ⊆ held` is `Finset.sdiff_subset`). -/
theorem revoke_removal_admitted (m : List (ℤ × ExecAuth)) (actor key : ℤ)
    (held drop : ExecAuth) (hheld : Heap.get m key = some held) :
    gwStep narrowGuard m actor key (held \ drop)
      = some (Heap.set m key (held \ drop)) := by
  have hg : narrowGuard m actor key (held \ drop) = true := by
    unfold narrowGuard
    rw [hheld]
    exact decide_eq_true Finset.sdiff_subset
  unfold gwStep
  rw [if_pos hg]

-- Non-vacuity: narrowing commits, WIDENING is refused (the compressed revoke cannot amplify).
#guard (gwStep narrowGuard [((7 : ℤ), ({Auth.read, Auth.write} : ExecAuth))] 0 7
        ({Auth.read} : ExecAuth)).isSome
#guard (gwStep narrowGuard [((7 : ℤ), ({Auth.read} : ExecAuth))] 0 7
        ({Auth.read, Auth.write} : ExecAuth)).isNone
#guard (gwStep narrowGuard ([] : List (ℤ × ExecAuth)) 0 7 ({Auth.read} : ExecAuth)).isNone

/-- The widening refusal, as a theorem (witness FALSE for the narrowing guard): writing strictly
more rights than held is refused. -/
theorem demo_widen_refused :
    gwStep narrowGuard [((7 : ℤ), ({Auth.read} : ExecAuth))] 0 7
      ({Auth.read, Auth.write} : ExecAuth) = none := by decide

#assert_axioms revoke_compresses_local
#assert_axioms narrow_committed_narrows
#assert_axioms revoke_removal_admitted
#assert_axioms demo_widen_refused

/-! ## §4 — GRANT: the SEPARATION (literal atoms cannot say "non-amplifying") and the
COMPRESSION (the order-relational guard, which IS non-amplification).

Grant writes rights to the RECIPIENT's edge address, but its guard — the constructive-knowledge
non-amplification `granted ⊆ heldBy(delegator)` (`recKDelegateAtten`'s gate,
`cell/src/capability.rs:461` `is_attenuation`) — reads a DIFFERENT key than it writes, and
compares the WRITTEN VALUE against that opening under the rights ORDER. Both features are proven
essential: the guard is outside the local class (§4.2) and outside every literal-atom
conjunction even WITH the absence extension (§4.3). So grant compresses only by admitting the
order-comparison atom into the guard algebra — the verb's proof obligation survives as a
guard-CLASS obligation. -/

/-- **The grant guard** — the order-relational non-amplification gate: admit writing rights
`new` (to any key — the recipient's edge) iff `new ⊆ ` the rights at the DELEGATOR's address
`d`. Fail-closed when the delegator holds nothing. The guard IS the non-amplification theorem. -/
def grantGuard (d : ℤ) : UGuard ExecAuth := fun m _actor _key new =>
  ((Heap.get m d).map (fun held => decide (new ⊆ held))).getD false

/-- Evaluating the grant guard against a delegator slot (the consumable unfolding). -/
theorem grantGuard_cons_self (d actor key : ℤ) (new held : ExecAuth)
    (t : List (ℤ × ExecAuth)) :
    grantGuard d ((d, held) :: t) actor key new = decide (new ⊆ held) := by
  unfold grantGuard
  rw [Heap.get_cons_self]
  rfl

/-- **§4.1 GRANT COMPRESSES (the guarantee is the guard).** A committed grant-guarded write
means the delegator HELD the written rights (and more): `granted ⊆ held` — non-amplification,
in-step, by construction. -/
theorem grant_non_amplifying {d : ℤ} {m m' : List (ℤ × ExecAuth)} {actor key : ℤ}
    {granted : ExecAuth} (h : gwStep (grantGuard d) m actor key granted = some m') :
    ∃ held, Heap.get m d = some held ∧ granted ⊆ held := by
  obtain ⟨hg, -⟩ := gwStep_factors h
  unfold grantGuard at hg
  cases hh : Heap.get m d with
  | none =>
      rw [hh] at hg
      exact absurd hg (by simp)
  | some held =>
      rw [hh] at hg
      refine ⟨held, rfl, ?_⟩
      have hd : decide (granted ⊆ held) = true := hg
      exact of_decide_eq_true hd

/-- The committed grant INSTALLS exactly the granted rights at the recipient's address. -/
theorem grant_installs {d : ℤ} {m m' : List (ℤ × ExecAuth)} {actor key : ℤ}
    {granted : ExecAuth} (h : gwStep (grantGuard d) m actor key granted = some m') :
    Heap.get m' key = some granted :=
  gwStep_writes h

/-- The REAL `Exec.attenuate` always passes the grant guard: a delegator holding `confRights c`
may grant `confRights (attenuate keep c)` for ANY `keep` — the landed cap machinery slots into
the compressed verb with zero adaptation (`attenuate_subset` lifted to the `Finset` order). -/
theorem attenuate_passes_guard (keep : List Auth) (c : Cap) (d actor key : ℤ)
    (m : List (ℤ × ExecAuth)) (hheld : Heap.get m d = some (confRights c)) :
    grantGuard d m actor key (confRights (attenuate keep c)) = true := by
  unfold grantGuard
  rw [hheld]
  show decide (confRights (attenuate keep c) ⊆ confRights c) = true
  rw [decide_eq_true_iff]
  intro a ha
  simp only [confRights, List.mem_toFinset] at ha ⊢
  exact attenuate_subset keep c ha

-- §4 probe rights (the three delegator slots the separation argument distinguishes):
/-- A sufficient held set: exactly the granted rights. -/
private def probeLo : ExecAuth := {Auth.read}
/-- ANOTHER sufficient held set (strictly larger). -/
private def probeHi : ExecAuth := {Auth.read, Auth.call}
/-- An insufficient held set. -/
private def probeBad : ExecAuth := ∅

/-- **§4.2 SEPARATION (grant is not local).** The grant guard is OUTSIDE the `SlotCaveat` class:
it reads the delegator's key, not the written one. No function of
`(actor, the written key's opening, the written value)` agrees with it. -/
theorem grant_guard_not_local (d : ℤ) : ¬ LocalGuard (grantGuard d) := by
  rintro ⟨p, hp⟩
  have h₁ := hp [(d, probeLo)] 0 (d + 1) probeLo
  have h₂ := hp ([] : List (ℤ × ExecAuth)) 0 (d + 1) probeLo
  rw [grantGuard_cons_self] at h₁
  have hLo : decide (probeLo ⊆ probeLo) = true := by decide
  rw [hLo] at h₁
  -- both probes open the WRITTEN key (d+1) to `none`, so the local kernel cannot tell them apart:
  have hne : (d + 1 : ℤ) ≠ d := by omega
  rw [Heap.get_cons_ne probeLo [] hne] at h₁
  unfold grantGuard at h₂
  rw [Heap.get_nil] at h₁ h₂
  rw [Heap.get_nil] at h₂
  rw [← h₁] at h₂
  exact Bool.noConfusion h₂

/-- **§4.3 SEPARATION (grant is not literal-atomic).** NO conjunction of literal atoms —
`contains`, `getEq`, even WITH the `absent` extension — expresses the non-amplification guard.
The witness triple: two DIFFERENT sufficient delegator slots (`{read}`, `{read, call}`) must
both be admitted, an insufficient one (`∅`) refused; a conjunction true on both sufficient slots
can mention the delegator key only through `contains` (a `getEq` pins ONE exact value), and
`contains` cannot refuse the insufficient slot. The rights ORDER cannot be compiled away into
per-key literals: compressing grant REQUIRES the order-relational guard class. -/
theorem grant_guard_not_literal (d : ℤ) :
    ¬ ∃ atoms : List (LitAtom ExecAuth),
        ∀ m : List (ℤ × ExecAuth), litConj atoms m = grantGuard d m 0 0 probeLo := by
  rintro ⟨atoms, h⟩
  have h₁ : litConj atoms [(d, probeLo)] = true := by
    rw [h, grantGuard_cons_self]
    decide
  have h₂ : litConj atoms [(d, probeHi)] = true := by
    rw [h, grantGuard_cons_self]
    decide
  have h₃ : litConj atoms [(d, probeBad)] = false := by
    rw [h, grantGuard_cons_self]
    decide
  -- extract an atom the insufficient slot fails…
  obtain ⟨a, hmem, hfa⟩ : ∃ a, a ∈ atoms ∧ a.eval [(d, probeBad)] = false := by
    by_contra hno
    have hall : litConj atoms [(d, probeBad)] = true := by
      unfold litConj
      rw [List.all_eq_true]
      intro a ha
      cases hb : a.eval [(d, probeBad)] with
      | false => exact absurd ⟨a, ha, hb⟩ hno
      | true => rfl
    rw [hall] at h₃
    exact Bool.noConfusion h₃
  -- …which both sufficient slots satisfy:
  have ht₁ : a.eval [(d, probeLo)] = true := by
    unfold litConj at h₁
    exact List.all_eq_true.mp h₁ a hmem
  have ht₂ : a.eval [(d, probeHi)] = true := by
    unfold litConj at h₂
    exact List.all_eq_true.mp h₂ a hmem
  by_cases hk : a.key = d
  · cases a with
    | contains k =>
        have hkd : k = d := hk
        subst hkd
        simp [LitAtom.eval, LitAtom.evalAt, LitAtom.key, Heap.get_cons_self] at hfa
    | absent k =>
        have hkd : k = d := hk
        subst hkd
        simp [LitAtom.eval, LitAtom.evalAt, LitAtom.key, Heap.get_cons_self] at ht₁
    | getEq k v =>
        have hkd : k = d := hk
        subst hkd
        simp only [LitAtom.eval, LitAtom.evalAt, LitAtom.key, Heap.get_cons_self] at ht₁ ht₂
        have hv₁ : probeLo = v := Option.some.inj (of_decide_eq_true ht₁)
        have hv₂ : probeHi = v := Option.some.inj (of_decide_eq_true ht₂)
        exact absurd (hv₁.trans hv₂.symm) (by decide)
  · -- an atom off the delegator key sees `none` in BOTH probes — it cannot separate them:
    have e₁ : Heap.get [(d, probeLo)] a.key = none := by
      rw [Heap.get_cons_ne probeLo [] hk]
      exact Heap.get_nil _
    have e₃ : Heap.get [(d, probeBad)] a.key = none := by
      rw [Heap.get_cons_ne probeBad [] hk]
      exact Heap.get_nil _
    have heq : a.eval [(d, probeLo)] = a.eval [(d, probeBad)] := by
      unfold LitAtom.eval
      rw [e₁, e₃]
    rw [ht₁, hfa] at heq
    exact Bool.noConfusion heq

-- Non-vacuity: a compressed grant that would AMPLIFY is refused; an attenuated one commits.
#guard (gwStep (grantGuard 7) [((7 : ℤ), ({Auth.read, Auth.write} : ExecAuth))] 0 9
        ({Auth.read} : ExecAuth)).isSome
#guard (gwStep (grantGuard 7) [((7 : ℤ), ({Auth.read, Auth.write} : ExecAuth))] 0 9
        ({Auth.read, Auth.grant} : ExecAuth)).isNone
#guard (gwStep (grantGuard 7) ([] : List (ℤ × ExecAuth)) 0 9 ({Auth.read} : ExecAuth)).isNone

/-- The amplification refusal, as a theorem: granting `{read, grant}` against a delegator
holding only `{read, write}` is REFUSED by the compressed grant (witness FALSE — the
non-amplification tooth survives compression). -/
theorem demo_amplify_refused :
    gwStep (grantGuard 7) [((7 : ℤ), ({Auth.read, Auth.write} : ExecAuth))] 0 9
      ({Auth.read, Auth.grant} : ExecAuth) = none := by decide

#assert_axioms grantGuard_cons_self
#assert_axioms grant_non_amplifying
#assert_axioms grant_installs
#assert_axioms attenuate_passes_guard
#assert_axioms grant_guard_not_local
#assert_axioms grant_guard_not_literal
#assert_axioms demo_amplify_refused

/-! ## §5 — SHIELD/UNSHIELD: the SEPARATION (positive atoms cannot say "fresh") and the
COMPRESSION (the absence atom, whose floor is the proven non-membership opening).

The evidence verbs are fresh inserts into grow-only collections: shield/noteCreate into the
commitment collection, unshield/noteSpend into the nullifier collection (`noteSpendNullifier`'s
double-spend gate). Over the universal map both are ONE guarded write with the FRESHNESS guard —
which is EXACTLY the absence atom, and provably NOT expressible in the landed positive algebra. -/

/-- **The freshness guard** — admit a write iff the key is ABSENT (the double-spend /
re-commitment / re-birth gate). -/
def freshGuard {ν : Type} : UGuard ν := fun m _actor key _new => (Heap.get m key).isNone

/-- **The freshness guard IS the absence atom** — the compression target named exactly:
`freshGuard = litConj [absent key]`. Its circuit floor is already proven
(`Heap.get_none_of_gap`, the reused sorted-tree non-membership opening). -/
theorem fresh_is_absence_atom {ν : Type} [DecidableEq ν] (m : List (ℤ × ν)) (actor key : ℤ)
    (v : ν) : freshGuard m actor key v = litConj [LitAtom.absent key] m := by
  simp [freshGuard, litConj, LitAtom.eval, LitAtom.evalAt, LitAtom.key]

/-- A committed fresh write was at an ABSENT key (the gate, read back off the commit). -/
theorem fresh_committed_was_absent {ν : Type} {m m' : List (ℤ × ν)} {actor key : ℤ} {v : ν}
    (h : gwStep freshGuard m actor key v = some m') : Heap.get m key = none := by
  obtain ⟨hg, -⟩ := gwStep_factors h
  unfold freshGuard at hg
  exact Option.isNone_iff_eq_none.mp hg

/-- **EVIDENCE MONOTONICITY survives compression**: a committed fresh write GROWS the collection
by exactly one leaf (`Heap.length_set_fresh` through the step) — the shield verb's grow-only
law. -/
theorem fresh_write_grows {ν : Type} {m m' : List (ℤ × ν)} {actor key : ℤ} {v : ν}
    (h : gwStep freshGuard m actor key v = some m') : m'.length = m.length + 1 := by
  have habs := fresh_committed_was_absent h
  obtain ⟨-, rfl⟩ := gwStep_factors h
  exact Heap.length_set_fresh m key v ((Heap.get_eq_none_iff m key).mp habs)

/-- **ANTI-DOUBLE-SPEND survives compression**: after a committed fresh write of `key`, EVERY
further fresh write of the SAME key is refused — by any actor, with any value. The
`noteSpend`/no-rebirth tooth, now a guard fact. -/
theorem fresh_write_no_replay {ν : Type} {m m' : List (ℤ × ν)} {actor key : ℤ} {v : ν}
    (h : gwStep freshGuard m actor key v = some m') :
    ∀ (actor' : ℤ) (v' : ν), gwStep freshGuard m' actor' key v' = none := by
  intro actor' v'
  have hw : Heap.get m' key = some v := gwStep_writes h
  unfold gwStep
  rw [if_neg]
  unfold freshGuard
  rw [hw]
  simp

/-- **The compressed unshield** — the §8 spending-proof gate (the boolean shadow of the STARK
note-spend portal, exactly `noteSpendChainA`'s first gate) composed onto the fresh write of the
nullifier. Fail-closed on EITHER gate. -/
def unshieldStep (proof : Bool) (m : List (ℤ × ℤ)) (actor nf : ℤ) :
    Option (List (ℤ × ℤ)) :=
  if proof = true then gwStep freshGuard m actor nf 1 else none

/-- No unshield commits without the spending proof (`noteSpendChainA_fails_without_proof`,
compressed). -/
theorem unshield_fails_without_proof (m : List (ℤ × ℤ)) (actor nf : ℤ) :
    unshieldStep false m actor nf = none := rfl

/-- The compressed unshield cannot double-spend: a committed spend of `nf` refuses every later
spend of `nf`. -/
theorem unshield_no_double_spend {proof : Bool} {m m' : List (ℤ × ℤ)} {actor nf : ℤ}
    (h : unshieldStep proof m actor nf = some m') :
    ∀ (proof' : Bool) (actor' : ℤ), unshieldStep proof' m' actor' nf = none := by
  intro proof' actor'
  unfold unshieldStep at h ⊢
  cases proof with
  | false => exact absurd h (by simp)
  | true =>
      rw [if_pos rfl] at h
      cases proof' with
      | false => rfl
      | true =>
          rw [if_pos rfl]
          exact fresh_write_no_replay h actor' 1

/-- **§5 SEPARATION: freshness is NOT expressible in the LANDED positive atom algebra.** No
conjunction of `contains`/`getEq` atoms (= `HeapKernel.HeapAtom`, the deployed `.all` shape)
agrees with the freshness guard: every positive atom is FALSE on the empty collection, so the
only positive conjunction admitting the fresh-spend-on-empty case is the EMPTY one — which then
admits the double spend. Compressing unshield REQUIRES the absence atom (whose semantic floor,
the non-membership opening, is already proven). -/
theorem freshness_not_positive (nf : ℤ) :
    ¬ ∃ atoms : List (LitAtom ℤ), (∀ a ∈ atoms, a.Positive) ∧
        ∀ m : List (ℤ × ℤ), litConj atoms m = (Heap.get m nf).isNone := by
  rintro ⟨atoms, hpos, h⟩
  have hempty : litConj atoms ([] : List (ℤ × ℤ)) = true := by
    rw [h]
    rfl
  have hnil : atoms = [] := by
    cases hatoms : atoms with
    | nil => rfl
    | cons a t =>
        have hmem : a ∈ atoms := by
          rw [hatoms]
          exact List.mem_cons_self ..
        have hpa := hpos a hmem
        have hfalse : a.eval ([] : List (ℤ × ℤ)) = false := by
          cases a with
          | contains k => rfl
          | absent k => exact hpa.elim
          | getEq k v => simp [LitAtom.eval, LitAtom.evalAt, LitAtom.key]
        have : litConj atoms ([] : List (ℤ × ℤ)) = false := by
          rw [hatoms]
          unfold litConj
          rw [List.all_cons, hfalse]
          rfl
        rw [this] at hempty
        exact Bool.noConfusion hempty
  subst hnil
  have hbad := h [(nf, 1)]
  simp [litConj, Heap.get_cons_self] at hbad

-- Non-vacuity: the compressed evidence verbs, executable.
#guard (unshieldStep true ([] : List (ℤ × ℤ)) 0 42).isSome            -- a fresh spend commits
#guard (unshieldStep false ([] : List (ℤ × ℤ)) 0 42).isNone           -- no proof, no spend
#guard (unshieldStep true [((42 : ℤ), (1 : ℤ))] 0 42).isNone          -- double spend REFUSED
#guard (gwStep freshGuard ([] : List (ℤ × ℤ)) 0 9 1).isSome           -- shield: fresh commitment
#guard (gwStep freshGuard [((9 : ℤ), (1 : ℤ))] 0 9 1).isNone          -- re-commitment refused

#assert_axioms fresh_is_absence_atom
#assert_axioms fresh_committed_was_absent
#assert_axioms fresh_write_grows
#assert_axioms fresh_write_no_replay
#assert_axioms unshield_fails_without_proof
#assert_axioms unshield_no_double_spend
#assert_axioms freshness_not_positive

/-! ## §6 — MOVE SEPARATES: conservation is not a guard — in ANY guard class.

The deepest separation, and it is guard-class-INDEPENDENT: quantifying over EVERY guard (the
maximal `UGuard` class — arbitrary decidable predicates of the whole pre-state), a committed
single-key write that preserves the collection total writes the value that was already there.
Conservation does not restrict WHICH writes commit (a guard's only power); it constrains the
SHAPE of the state change — two openings moving by cancelling deltas. `move` keeps its verb. -/

/-- The conserved measure: the sum of a value collection (the per-asset `Σ bal` of the universal
map — `recTotalAsset`'s shape at one asset). -/
def valTotal (m : List (ℤ × ℤ)) : ℤ := (m.map Prod.snd).sum

/-- `valTotal` on a cons (the unfolding proofs rewrite by). -/
theorem valTotal_cons (k v : ℤ) (t : List (ℤ × ℤ)) :
    valTotal ((k, v) :: t) = v + valTotal t := by
  simp [valTotal]

/-- A FRESH write grows the total by exactly the written value. -/
theorem valTotal_set_fresh : ∀ (m : List (ℤ × ℤ)) (k v : ℤ), Heap.get m k = none →
    valTotal (Heap.set m k v) = valTotal m + v := by
  intro m
  induction m with
  | nil =>
      intro k v _
      simp [Heap.set, valTotal]
  | cons hd rest ih =>
      intro k v hk
      obtain ⟨k', v'⟩ := hd
      by_cases heq : k = k'
      · subst heq
        rw [Heap.get_cons_self] at hk
        exact absurd hk (by simp)
      · rw [Heap.get_cons_ne v' rest heq] at hk
        simp only [Heap.set]
        by_cases hlt : k < k'
        · rw [if_pos hlt]
          simp only [valTotal_cons]
          ring
        · rw [if_neg hlt, if_neg heq]
          simp only [valTotal_cons]
          rw [ih k v hk]
          ring

/-- A PRESENT-key write moves the total by exactly the delta `v - old` (sorted collection — the
invariant every committed state carries). -/
theorem valTotal_set_present : ∀ (m : List (ℤ × ℤ)) (k v old : ℤ), Heap.SortedKeys m →
    Heap.get m k = some old → valTotal (Heap.set m k v) = valTotal m - old + v := by
  intro m
  induction m with
  | nil =>
      intro k v old _ hk
      simp [Heap.get] at hk
  | cons hd rest ih =>
      intro k v old hs hk
      obtain ⟨k', v'⟩ := hd
      by_cases heq : k = k'
      · subst heq
        rw [Heap.get_cons_self] at hk
        have hov : v' = old := Option.some.inj hk
        subst hov
        have hset : Heap.set ((k, v') :: rest) k v = (k, v) :: rest := by
          simp [Heap.set]
        rw [hset, valTotal_cons, valTotal_cons]
        ring
      · rw [Heap.get_cons_ne v' rest heq] at hk
        have hmem : k ∈ Heap.keys rest := by
          by_contra hnot
          rw [(Heap.get_eq_none_iff rest k).mpr hnot] at hk
          exact absurd hk (by simp)
        have hgt : k' < k := Heap.sortedKeys_head_lt hs k hmem
        simp only [Heap.set, if_neg (not_lt.mpr hgt.le), if_neg heq]
        simp only [valTotal_cons]
        rw [ih k v old (Heap.sortedKeys_tail hs) hk]
        ring

/-- **THE SEPARATION (guard-class-independent).** For EVERY guard `g` — the maximal class —
a committed guarded write that preserves the total is value-TRIVIAL: it writes the value already
(effectively) at the key. No guard algebra, however expressive, makes a single-key write both
conservative and value-moving — conservation is a SHAPE property, not a guard property. -/
theorem gwrite_conservation_trivializes {g : UGuard ℤ} {m m' : List (ℤ × ℤ)}
    {actor key new : ℤ} (hs : Heap.SortedKeys m) (h : gwStep g m actor key new = some m')
    (hcons : valTotal m' = valTotal m) : new = (Heap.get m key).getD 0 := by
  obtain ⟨-, rfl⟩ := gwStep_factors h
  cases hk : Heap.get m key with
  | none =>
      rw [valTotal_set_fresh m key new hk] at hcons
      simp only [Option.getD_none]
      omega
  | some old =>
      rw [valTotal_set_present m key new old hs hk] at hcons
      simp only [Option.getD_some]
      omega

/-- **The genuine move** — the paired two-key write: debit `src`, credit `dst`, same `amt`,
gated on `0 ≤ amt ≤ balance(src)` and `src ≠ dst`. The Σδ = 0 exchange (`recKExecAsset`'s
shape over the universal map). -/
def moveStep (m : List (ℤ × ℤ)) (src dst amt : ℤ) : Option (List (ℤ × ℤ)) :=
  (Heap.get m src).bind fun bs =>
    (Heap.get m dst).bind fun bd =>
      if 0 ≤ amt ∧ amt ≤ bs ∧ src ≠ dst then
        some (Heap.set (Heap.set m src (bs - amt)) dst (bd + amt))
      else none

/-- A committed move factors: both parties present, the gate held, and the post-state is the
paired debit/credit. -/
theorem moveStep_factors {m m' : List (ℤ × ℤ)} {src dst amt : ℤ}
    (h : moveStep m src dst amt = some m') :
    ∃ bs bd, Heap.get m src = some bs ∧ Heap.get m dst = some bd ∧
      (0 ≤ amt ∧ amt ≤ bs ∧ src ≠ dst) ∧
      m' = Heap.set (Heap.set m src (bs - amt)) dst (bd + amt) := by
  unfold moveStep at h
  rcases hsrc : Heap.get m src with _ | bs
  · rw [hsrc] at h
    have h' : (none : Option (List (ℤ × ℤ))) = some m' := h
    exact absurd h' (by simp)
  · rw [hsrc] at h
    have h1 : (Heap.get m dst).bind (fun bd =>
        if 0 ≤ amt ∧ amt ≤ bs ∧ src ≠ dst then
          some (Heap.set (Heap.set m src (bs - amt)) dst (bd + amt))
        else none) = some m' := h
    rcases hdst : Heap.get m dst with _ | bd
    · rw [hdst] at h1
      have h2 : (none : Option (List (ℤ × ℤ))) = some m' := h1
      exact absurd h2 (by simp)
    · rw [hdst] at h1
      have h2 : (if 0 ≤ amt ∧ amt ≤ bs ∧ src ≠ dst then
          some (Heap.set (Heap.set m src (bs - amt)) dst (bd + amt))
        else none) = some m' := h1
      by_cases hg : 0 ≤ amt ∧ amt ≤ bs ∧ src ≠ dst
      · rw [if_pos hg] at h2
        exact ⟨bs, bd, rfl, rfl, hg, (Option.some.inj h2).symm⟩
      · rw [if_neg hg] at h2
        exact absurd h2 (by simp)

/-- **CONSERVATION — what move provides and no guarded write can**: a committed move preserves
the collection total EXACTLY (Σδ = 0), while genuinely changing two openings. -/
theorem move_conserves {m m' : List (ℤ × ℤ)} {src dst amt : ℤ} (hs : Heap.SortedKeys m)
    (h : moveStep m src dst amt = some m') : valTotal m' = valTotal m := by
  obtain ⟨bs, bd, hsrc, hdst, ⟨-, -, hne⟩, rfl⟩ := moveStep_factors h
  have hdst' : Heap.get (Heap.set m src (bs - amt)) dst = some bd := by
    rw [Heap.get_set_frame m src dst (bs - amt) (Ne.symm hne)]
    exact hdst
  have hs' : Heap.SortedKeys (Heap.set m src (bs - amt)) := Heap.set_sorted m src (bs - amt) hs
  rw [valTotal_set_present _ dst (bd + amt) bd hs' hdst',
      valTotal_set_present m src (bs - amt) bs hs hsrc]
  ring

/-- The §6 concrete ledger (cells 1, 2 holding 100, 5) and its committed move of 30. -/
def demoLedger : List (ℤ × ℤ) := [(1, 100), (2, 5)]
/-- The post-state of moving 30 from cell 1 to cell 2. -/
def demoMoved : List (ℤ × ℤ) := [(1, 70), (2, 35)]

/-- The demo ledger satisfies the sorted invariant. -/
theorem demoLedger_sorted : Heap.SortedKeys demoLedger := by
  norm_num [demoLedger, Heap.SortedKeys, Heap.keys, List.pairwise_cons]

/-- The demo move commits and lands exactly the paired debit/credit. -/
theorem demo_move_commits : moveStep demoLedger 1 2 30 = some demoMoved := by decide

/-- **The debit tooth (the leg-wise separation).** NO guard `g` — none — lets the bare debit leg
(writing 70 over cell 1's 100) preserve the total: every guard algebra in existence either
refuses all real debits or breaks conservation. The two legs of a move cannot be liberated into
independent guarded writes. -/
theorem demo_debit_breaks_conservation (g : UGuard ℤ) (actor : ℤ) (m' : List (ℤ × ℤ))
    (h : gwStep g demoLedger actor 1 70 = some m') : valTotal m' ≠ valTotal demoLedger := by
  intro hcons
  have htriv := gwrite_conservation_trivializes demoLedger_sorted h hcons
  have hget : Heap.get demoLedger 1 = some 100 := by decide
  rw [hget] at htriv
  simp only [Option.getD_some] at htriv
  exact absurd htriv (by decide)

/-- The committed move changes BOTH parties' openings (it is not secretly value-trivial). -/
theorem demo_move_changes_two :
    Heap.get demoMoved 1 ≠ Heap.get demoLedger 1 ∧
    Heap.get demoMoved 2 ≠ Heap.get demoLedger 2 := by decide

/-- **MOVE IS NOT A GUARDED WRITE (the arity separation).** No guard, no actor, no key, no
value: no single guarded write produces the move's post-state — a guarded write changes at most
one opening (`gwStep_changes_at_most_one`); the move changes two. Together with
`demo_debit_breaks_conservation` (the legs can't be split conservatively), move's conservation
pairing is irreducibly two-key: `move` SURVIVES as its own verb. -/
theorem move_not_single_write :
    ¬ ∃ (g : UGuard ℤ) (actor key new : ℤ),
        gwStep g demoLedger actor key new = some demoMoved := by
  rintro ⟨g, actor, key, new, h⟩
  have h12 := gwStep_changes_at_most_one h 1 2
    demo_move_changes_two.1 demo_move_changes_two.2
  exact absurd h12 (by decide)

-- Non-vacuity: the move's own gates, executable.
#guard moveStep demoLedger 1 2 30 == some demoMoved
#guard valTotal demoMoved == valTotal demoLedger        -- Σδ = 0
#guard moveStep demoLedger 1 2 200 == none              -- overdraft refused
#guard moveStep demoLedger 1 2 (-3) == none             -- negative amount refused
#guard moveStep demoLedger 1 1 10 == none               -- self-move refused
#guard moveStep demoLedger 1 9 10 == none               -- absent counterparty refused

#assert_axioms valTotal_set_fresh
#assert_axioms valTotal_set_present
#assert_axioms gwrite_conservation_trivializes
#assert_axioms moveStep_factors
#assert_axioms move_conserves
#assert_axioms demo_move_commits
#assert_axioms demo_debit_breaks_conservation
#assert_axioms move_not_single_write

/-! ## §7 — CREATE: the legs compress (the SAME absence guard as unshield), the bundle does not.

Birth's existence facet over the universal map is a FRESH insert — `gwStep freshGuard`, with
no-rebirth = `fresh_write_no_replay` and domain growth = `fresh_write_grows`, ALREADY proven in
§5 (the pleasing identity: birth and note-spend ride the same non-membership opening). What does
NOT compress is the BUNDLE: minting a cell initializes several addresses (existence + lifecycle
+ balance + …) in one atomic step, and a guarded write changes at most one opening — the same
arity argument as move (without move's stronger leg-wise impossibility: create's individual legs
are each fine). Plus the polarity residue: create is the one verb whose write gate must NOT
demand held authority over the target (nothing holds an unborn cell) —
`VerbRegistry.verbBehavior .create = (.birth, .introduce)`. -/

/-- **CREATE'S ATOMICITY SEPARATION.** Birth initializing two addresses (existence ↦ 1,
lifecycle ↦ Live) from the empty state is NOT any single guarded write — same arity tooth as
move. -/
theorem create_birth_not_single_write :
    ¬ ∃ (g : UGuard ℤ) (actor key new : ℤ),
        gwStep g ([] : List (ℤ × ℤ)) actor key new = some [(10, 1), (20, 0)] := by
  rintro ⟨g, actor, key, new, h⟩
  have h₁ : Heap.get [((10 : ℤ), (1 : ℤ)), (20, 0)] 10 ≠ Heap.get ([] : List (ℤ × ℤ)) 10 := by
    decide
  have h₂ : Heap.get [((10 : ℤ), (1 : ℤ)), (20, 0)] 20 ≠ Heap.get ([] : List (ℤ × ℤ)) 20 := by
    decide
  exact absurd (gwStep_changes_at_most_one h 10 20 h₁ h₂) (by decide)

-- Non-vacuity: the existence leg compresses (fresh insert; re-birth refused) — §5's machinery.
#guard (gwStep freshGuard ([] : List (ℤ × ℤ)) 0 10 1).isSome
#guard (gwStep freshGuard [((10 : ℤ), (1 : ℤ))] 0 10 1).isNone        -- no rebirth

#assert_axioms create_birth_not_single_write

/-! ## §8 — THE VERDICT, REIFIED: the kernel under the universal map.

Each `VerbRegistry.Verb` gets its proven FATE: stays primitive, or dissolves into the one
guarded-write verb at a named guard class. The compressed kernel is `create · gwrite · move`
(`compressed_kernel_three`); the 8-verb minimality is ontology-relative
(`verb_minimality_is_ontology_relative`); the guard classes keep the dissolved verbs' proof
obligations alive (`grant` ≠ `revoke` in fate — `guard_class_distinguishes_grant_revoke`). -/

/-- The guard class a dissolved verb's interpretation PROVABLY needs (weakest sufficient,
per this module's theorems). -/
inductive GuardClass where
  /-- `(actor, old, new)` predicates — the landed `SlotCaveat` class. -/
  | localOldNew
  /-- conjunctions of `contains`/`getEq` literal atoms — the landed `HeapAtom` class. -/
  | literalAtoms
  /-- literal atoms + the ABSENCE atom (floor: the proven non-membership opening). -/
  | withAbsence
  /-- order-relational guards comparing the written value to another key's opening
      (`new ⊆ get(k)` — the rights lattice enters the guard language). -/
  | withOrderGuard
  deriving DecidableEq, BEq, Repr

/-- The compressed kernel's verbs. -/
inductive CVerb where
  /-- atomic multi-address bundle birth (separated by arity, `create_birth_not_single_write`). -/
  | create
  /-- THE guarded write (`gwStep` — five of the seven constructors dissolve into it). -/
  | gwrite
  /-- the paired Σδ = 0 exchange (separated by `gwrite_conservation_trivializes` +
      `move_not_single_write`). -/
  | move
  deriving DecidableEq, BEq, Repr

/-- A survivor verb's fate under the universal map. -/
inductive Fate where
  /-- the verb survives compression as its own primitive. -/
  | primitive (v : CVerb)
  /-- the verb dissolves into `gwStep` at the named guard class. -/
  | guardedWrite (c : GuardClass)
  deriving DecidableEq, BEq, Repr

/-- The compressed verb a fate lands on. -/
def Fate.compressedVerb : Fate → CVerb
  | .primitive v => v
  | .guardedWrite _ => .gwrite

/-- **THE FATE TABLE** — each entry backed by this module's theorems:
`create` → primitive (`create_birth_not_single_write`); `write` → the guarded write at the
landed atom class (it IS the verb, `HeapKernel.heapStepGuarded`); `move` → primitive
(`move_not_single_write`, `gwrite_conservation_trivializes`); `grant` → guarded write at the
order class (`grant_non_amplifying`; necessity: `grant_guard_not_literal`,
`grant_guard_not_local`); `revoke` → guarded write, local (`revoke_compresses_local`,
`narrow_committed_narrows`); `shieldUnshield` → guarded write with absence
(`fresh_is_absence_atom`; necessity: `freshness_not_positive`); `lifecycle` → guarded write,
local (`lifecycle_compresses_local`, teeth `life_reseal_refused`/`life_destroyed_terminal`). -/
def cfate : Dregg2.Substrate.VerbRegistry.Verb → Fate
  | .create => .primitive .create
  | .write => .guardedWrite .literalAtoms
  | .move => .primitive .move
  | .grant => .guardedWrite .withOrderGuard
  | .revoke => .guardedWrite .localOldNew
  | .shieldUnshield => .guardedWrite .withAbsence
  | .lifecycle => .guardedWrite .localOldNew

/-- **THE COMPRESSED KERNEL HAS THREE VERBS.** Mapping the full survivor roster through its fate
and deduplicating leaves exactly `create · gwrite · move`. -/
theorem compressed_kernel_three :
    ((Dregg2.Substrate.VerbRegistry.survivors.map
        (fun v => (cfate v).compressedVerb)).eraseDups).length = 3 := by decide

/-- **THE 8-VERB MINIMALITY IS ONTOLOGY-RELATIVE.** `VerbRegistry.minimality` proves the eight
pairwise-irreplaceable via `verbBehavior` (substance × polarity) — TODAY'S ontology. Under the
universal-map fate, DISTINCT verbs share one behavior class: revoke and lifecycle have the SAME
fate (a local guarded write). The old injectivity does not survive the re-ontologization — what
survives is the guard-class stratification. -/
theorem verb_minimality_is_ontology_relative :
    cfate .revoke = cfate .lifecycle ∧
      Dregg2.Substrate.VerbRegistry.Verb.revoke ≠ .lifecycle :=
  ⟨rfl, by decide⟩

/-- The dissolved verbs are NOT flattened into one undifferentiated "write": grant's fate is
provably distinct from revoke's — the authority verbs' asymmetry (production needs the order
guard, narrowing is local) is carried by the guard classes. -/
theorem guard_class_distinguishes_grant_revoke : cfate .grant ≠ cfate .revoke := by decide

/-- **EXERCISE WAS NEVER A VERB** — the registry already classifies it as turn structure (the
eval map); under the universal map there is nothing to compress. Re-pinned here so the
compressed kernel's census is complete against the live wire enum. -/
theorem exercise_already_structure :
    Dregg2.Substrate.VerbRegistry.classify .ExerciseViaCapability
      = Dregg2.Substrate.VerbRegistry.Classification.turnStructure .exercise := rfl

-- The census counts: 7 constructors in, 3 compressed verbs out, 5 dissolved into gwrite.
#guard ((Dregg2.Substrate.VerbRegistry.survivors.map
          (fun v => (cfate v).compressedVerb)).eraseDups).length == 3
#guard (Dregg2.Substrate.VerbRegistry.survivors.filter
          (fun v => (cfate v).compressedVerb == .gwrite)).length == 5

#assert_axioms compressed_kernel_three
#assert_axioms verb_minimality_is_ontology_relative
#assert_axioms guard_class_distinguishes_grant_revoke
#assert_axioms exercise_already_structure

end Dregg2.Substrate.VerbCompression
