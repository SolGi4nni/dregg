/-
# `Dregg2.Storage.Retrievability` — proof-of-retrievability, IN LEAN, on the bucket commitment.

The existing Rust storage is CLIENT-side (`availability`/`retrieval`: a light client samples chunks
from untrusted operators and Merkle-verifies each against the manifest root). This is the
PROVIDER-side dual: an auditor challenges a set of positions, the provider answers with the objects
it serves there, and each answer is Merkle-checked against the committed content root. The soundness
is proved down to `BucketCommitment.read_sound_or_collides` — a provider that PASSES holds the GENUINE
committed objects at every challenged position, OR it exhibited a specific sponge collision, and a
substitution FORCES that collision (`por_substitution_forces_collision`).

⇑ **CUTOVER 2026-07-25.** These used to ride the one `Poseidon2SpongeCR` floor, which the deployed
hash REFUTES by `rfl` — the audit guarantee was vacuous exactly where it mattered. No floor is spent
on the live path now; `Storage.DeployedFloorRegrounded` prices the collision residual as a game
advantage.

The remaining sampling-EXTRACTABILITY step (passing a random challenge ⟹ enough shards held that
the blob RECONSTRUCTS) is the honest boundary: it composes the per-position soundness proved here
with the erasure k-of-n reconstruction theorem (`Dregg2/Storage/Erasure.lean`, forthcoming) plus the
availability sampling bound (`erasure::sample_availability`). It is NOT assumed away here — the real,
load-bearing part (each sampled point is trustworthy, and a forged point is refused) is proved.
-/
import Dregg2.Storage.BucketCommitment

namespace Dregg2.Storage

open Dregg2.Lightclient.MMR (Opens)
open Dregg2.Circuit.Poseidon2Binding
  (Poseidon2SpongeCR SpongeColl spongeColl_refutable_of_injective)

/-- A provider's response to one challenged position: the object it serves for position `pos`. -/
structure Response where
  pos : ℕ
  obj : Object
deriving Repr

/-- The response OPENS against the committed bucket: its object is the genuine `pos`-th leaf under
the published content root. (The verifier checks this via the Merkle opening; `Opens` is the
semantic content the opening witnesses — `read_sound_or_collides` reduces it to the root.) -/
def opensAt (hash : List ℤ → ℤ) (objs : List Object) (r : Response) : Prop :=
  Opens (objectLeaves hash objs) r.pos (objectLeaf hash r.obj)

/-- **A provider PASSES the audit** iff every response opens against the committed bucket. -/
def passes (hash : List ℤ → ℤ) (objs : List Object) (responses : List Response) : Prop :=
  ∀ r ∈ responses, opensAt hash objs r

/-! ## §2 — PoR soundness with NO refuted floor.

`por_sound`/`por_refuses_substitution`/`por_holds_committed` were gated on `Poseidon2SpongeCR hash`,
which the deployed hash REFUTES (`Storage.DeployedFloorRefuted.deployed_floor_false`) — the audit
guarantee was vacuous exactly where it mattered. Migrated onto
`BucketCommitment.read_sound_or_collides`: the audit now says a cheating provider must have FOUND a
specific Poseidon2 collision, which is a claim about the deployed system rather than about an
unsatisfiable hypothesis. -/

/-- **THE AUDIT EXTRACTOR (TOTAL).** At a challenged position, the two arity-3 preimages a
substituting provider would need to have collided: the object it SERVED and the object the bucket
COMMITTED there. `([], [])` on an out-of-range position, which no opening can reach. -/
def porFind (hash : List ℤ → ℤ) (objs : List Object) (r : Response) : List ℤ × List ℤ :=
  match objs[r.pos]? with
  | some o' => objectLeafFind r.obj o'
  | none => ([], [])

/-- **⚑ PoR SOUNDNESS (per challenged position), UNCONDITIONAL.** Every response a passing provider
gives IS the genuine committed object at that position, OR `porFind` hands back a genuine sponge
collision. No floor: this holds of the DEPLOYED Poseidon2. -/
theorem por_sound_or_collides (hash : List ℤ → ℤ)
    (objs : List Object) (responses : List Response) (hpass : passes hash objs responses) :
    ∀ r ∈ responses,
      objs[r.pos]? = some r.obj ∨ SpongeColl hash (porFind hash objs r) := by
  intro r hr
  rcases read_sound_or_collides hash objs r.pos r.obj (hpass r hr) with hgood | ⟨o', hm, hcoll⟩
  · exact Or.inl hgood
  · refine Or.inr ?_
    simp only [porFind, hm]
    exact hcoll

/-- **⚑ ANTI-FORGERY (the negative pole — the audit BITES), UNCONDITIONAL AND SHARPER.** A provider
serving an object DIFFERENT from the one committed at a position, whose response nevertheless opens,
has EXHIBITED a genuine sponge collision — not "cannot happen under an assumption the hash refutes",
but "costs a real Poseidon2 collision". This is the strongest form in the file: substitution does not
merely fail, it FORCES the break. -/
theorem por_substitution_forces_collision (hash : List ℤ → ℤ)
    (objs : List Object) (r : Response) (hne : objs[r.pos]? ≠ some r.obj)
    (hopen : opensAt hash objs r) : SpongeColl hash (porFind hash objs r) := by
  rcases read_sound_or_collides hash objs r.pos r.obj hopen with hgood | ⟨o', hm, hcoll⟩
  · exact absurd hgood hne
  · simp only [porFind, hm]
    exact hcoll

/-- The first challenged position at which the provider's answer is NOT the committed object — the
pair of preimages that must therefore have collided. Total; `([], [])` only on a response list the
caller has already shown genuine. -/
def porFirstColl (hash : List ℤ → ℤ) (objs : List Object) : List Response → List ℤ × List ℤ
  | [] => ([], [])
  | r :: rs => if objs[r.pos]? = some r.obj then porFirstColl hash objs rs else porFind hash objs r

/-- **⚑ THE PASSING SET IS GENUINE END-TO-END, UNCONDITIONALLY.** A provider that passes a challenge
holds EXACTLY the committed objects at every challenged position, OR `porFirstColl` exhibits a genuine
sponge collision at the first position where it does not. This is the load-bearing input to the
sampling-extractability step, and it is now a statement about the deployed hash. -/
theorem por_holds_committed_or_collides (hash : List ℤ → ℤ)
    (objs : List Object) (responses : List Response) (hpass : passes hash objs responses) :
    responses.map (fun r => objs[r.pos]?) = responses.map (fun r => some r.obj)
    ∨ SpongeColl hash (porFirstColl hash objs responses) := by
  induction responses with
  | nil => exact Or.inl rfl
  | cons r rs ih =>
    by_cases hgood : objs[r.pos]? = some r.obj
    · simp only [porFirstColl, if_pos hgood]
      rcases ih (fun q hq => hpass q (List.mem_cons_of_mem r hq)) with hmap | hcoll
      · exact Or.inl (by simp [hgood, hmap])
      · exact Or.inr hcoll
    · refine Or.inr ?_
      simp only [porFirstColl, if_neg hgood]
      exact por_substitution_forces_collision hash objs r hgood (hpass r (List.mem_cons_self ..))

/-! ### §2½ — the STRENGTH BRIDGES: the deleted keystones, at an injective sponge.

Nothing was surrendered: the `Poseidon2SpongeCR`-gated conclusions fall out of the unconditional
forms in one line each. They are not on the live path. -/

/-- The deleted `por_sound`, recovered at an injective sponge (contradiction-style: a passing
provider cannot hold a different object at a challenged position). -/
theorem por_sound_of_or_collides (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (responses : List Response) (hpass : passes hash objs responses)
    (r : Response) (hr : r ∈ responses) (hne : objs[r.pos]? ≠ some r.obj) : False :=
  hne ((por_sound_or_collides hash objs responses hpass r hr).resolve_right
    (spongeColl_refutable_of_injective hash hCR _))

/-- The deleted `por_refuses_substitution`, recovered at an injective sponge (contradiction-style: a
substituted object cannot produce a passing response). -/
theorem por_refuses_substitution_of_or_collides (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (r : Response) (hne : objs[r.pos]? ≠ some r.obj)
    (hopen : opensAt hash objs r) : False :=
  spongeColl_refutable_of_injective hash hCR _
    (por_substitution_forces_collision hash objs r hne hopen)

/-- The deleted `por_holds_committed`, recovered at an injective sponge (contradiction-style: a
passing response set cannot differ from the committed objects). -/
theorem por_holds_committed_of_or_collides (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (responses : List Response) (hpass : passes hash objs responses)
    (hne : responses.map (fun r => objs[r.pos]?) ≠ responses.map (fun r => some r.obj)) : False :=
  hne ((por_holds_committed_or_collides hash objs responses hpass).resolve_right
    (spongeColl_refutable_of_injective hash hCR _))

#assert_axioms por_sound_or_collides
#assert_axioms por_substitution_forces_collision
#assert_axioms por_holds_committed_or_collides
#assert_axioms por_sound_of_or_collides
#assert_axioms por_refuses_substitution_of_or_collides
#assert_axioms por_holds_committed_of_or_collides

end Dregg2.Storage
