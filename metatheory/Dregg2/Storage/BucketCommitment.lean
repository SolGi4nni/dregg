/-
# `Dregg2.Storage.BucketCommitment` — the bucket object-store's content commitment, IN LEAN.

The Rust `storage::bucket_commitment` (Poseidon2 content-root + trustless `verify_opening`) was
built Rust-first. THIS is its Lean source of truth: the content commitment as an executable
`MMR.mroot` fold over per-object leaves.

⇑ **CUTOVER 2026-07-25.** The binding used to be proved down to the ONE `Poseidon2SpongeCR` crypto
floor — literal INJECTIVITY of the sponge, which `Storage.DeployedFloorRefuted.deployed_floor_false`
REFUTES at the deployed hash by `rfl` and which is unsatisfiable at ANY range-bounded hash by
cardinality. So the floor was never a floor and the keystones were vacuous at deployment. They are now
EXTRACTION-AS-DATA and carry NO hypothesis: each says "binds, OR here is the specific sponge collision".
The residual is priced as a collision-GAME advantage in `Storage.DeployedFloorRegrounded`.

* `objectLeaf` — the wide leaf `H(key, contentType, bodyDigest)`; its arity-3 preimage separates it
  from the Merkle nodes (arity 2) and the MMR log leaves (arity 1) under CR, so no domain tag.
* `contentRoot` — the bucket commitment: `MMR.mroot` over the object leaves.
* `objectLeaf_binds_or_collides` / `contentRoot_binds_or_collides` — the root BINDS the committed
  object set (no ghost object hides under a genuine root) OR the total extractors `objectLeafFind` /
  `firstObjFind` / `contentRootFind` exhibit the collision. UNCONDITIONAL.
* `read_sound_or_collides` — the TRUSTLESS READ: a served object that opens at a position is genuinely
  the object the bucket committed there, no trust in the provider, OR the provider found a collision.
  Reduces to the MMR positional binding + `objectLeaf_binds_or_collides`.

NOTHING is assumed on the live path (checked by `#assert_axioms`); the three `*_of_binds_or_collides`
bridges retain the refuted floor ONLY to record, contradiction-style, that the cutover surrendered
nothing.
-/
import Dregg2.Lightclient.MMR

namespace Dregg2.Storage

open Dregg2.Lightclient.MMR
open Dregg2.Circuit.Poseidon2Binding
  (Poseidon2SpongeCR SpongeColl spongeColl_refutable_of_injective)

/-- A stored object: its key, a content-type tag, and the body's wide content-address digest. -/
structure Object where
  key : ℤ
  contentType : ℤ
  bodyDigest : ℤ
deriving Repr, DecidableEq

/-- The per-object leaf — the wide digest binding `(key, contentType, bodyDigest)`. The arity-3
preimage separates an object leaf from Merkle nodes (arity 2) and MMR log leaves (arity 1) under
the CR floor, so no domain tag is needed. -/
def objectLeaf (hash : List ℤ → ℤ) (o : Object) : ℤ :=
  hash [o.key, o.contentType, o.bodyDigest]

/-- The object leaves of a bucket, in commit order. -/
def objectLeaves (hash : List ℤ → ℤ) (objs : List Object) : List ℤ :=
  objs.map (objectLeaf hash)

/-- **The bucket content commitment.** The Poseidon2 content-root: the MMR fold over the object
leaves — one felt binding the whole ordered object set. -/
def contentRoot (hash : List ℤ → ℤ) (objs : List Object) : ℤ :=
  mroot hash (objectLeaves hash objs)

/-! ## §2 — THE BINDING, EXTRACTED AS DATA (no refuted floor anywhere on the live path).

The three keystones below used to be gated on `Poseidon2SpongeCR hash` — literal injectivity of the
sponge. That floor is REFUTED at the deployed hash by `rfl`
(`Storage.DeployedFloorRefuted.deployed_floor_false`) and false for ANY range-bounded sponge by
pigeonhole (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the gated forms said nothing
about the deployed bucket store. They are REPLACED, not kept beside a repair: each is now
UNCONDITIONAL and hands back the specific sponge collision an equivocating provider would have to
have found. `Storage.DeployedFloorRegrounded` prices that residual as a collision-game advantage. -/

/-- **THE LEAF-COLLISION EXTRACTOR (TOTAL).** Two objects claiming one leaf: their arity-3 preimages
ARE the candidate collision. No search. -/
def objectLeafFind (o o' : Object) : List ℤ × List ℤ :=
  ([o.key, o.contentType, o.bodyDigest], [o'.key, o'.contentType, o'.bodyDigest])

/-- **⚑ THE OBJECT LEAF BINDS ITS OBJECT, UNCONDITIONALLY.** Equal leaves force equal objects OR
`objectLeafFind` exhibits a genuine sponge collision — the arity-3 preimage is structurally
injective, so the ONLY way two distinct objects share a leaf is a collision of the hash itself. -/
theorem objectLeaf_binds_or_collides (hash : List ℤ → ℤ) (o o' : Object)
    (h : objectLeaf hash o = objectLeaf hash o') :
    o = o' ∨ SpongeColl hash (objectLeafFind o o') := by
  by_cases hoo : o = o'
  · exact Or.inl hoo
  · refine Or.inr ⟨?_, h⟩
    simp only [objectLeafFind, ne_eq, List.cons.injEq, and_true, not_and]
    intro hk hc hb
    exact absurd (by cases o; cases o'; simp_all) hoo

/-- The first position at which two object lists of pinned-equal leaves actually differ — the pair of
arity-3 preimages that must therefore collide. `([], [])` is returned only on lists the caller has
already shown equal, so it is never read. -/
def firstObjFind : List Object → List Object → List ℤ × List ℤ
  | [], _ => ([], [])
  | _, [] => ([], [])
  | o :: os, o' :: os' => if o ≠ o' then objectLeafFind o o' else firstObjFind os os'

/-- Equal LEAF LISTS force equal object lists OR expose a collision at the first differing object. -/
theorem objectLeaves_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ objs objs' : List Object, objectLeaves hash objs = objectLeaves hash objs' →
      objs = objs' ∨ SpongeColl hash (firstObjFind objs objs') := by
  intro objs
  induction objs with
  | nil =>
    intro objs' h
    cases objs' with
    | nil => exact Or.inl rfl
    | cons o' os' => simp [objectLeaves] at h
  | cons o os ih =>
    intro objs' h
    cases objs' with
    | nil => simp [objectLeaves] at h
    | cons o' os' =>
      simp only [objectLeaves, List.map_cons, List.cons.injEq] at h
      obtain ⟨hleaf, htail⟩ := h
      by_cases hoo : o = o'
      · subst hoo
        simp only [firstObjFind, if_neg (by simp : ¬ (o ≠ o))]
        rcases ih os' htail with hos | hcoll
        · exact Or.inl (by rw [hos])
        · exact Or.inr hcoll
      · refine Or.inr ?_
        simp only [firstObjFind, if_pos hoo]
        exact (objectLeaf_binds_or_collides hash o o' hleaf).resolve_left hoo

/-- **THE CONTENT-ROOT COLLISION EXTRACTOR (TOTAL).** Locate the break: if the two buckets' LEAF
LISTS differ, the MMR root walk (`MMR.mrootFind`) returns the collision; otherwise the leaf lists
agree and the first differing OBJECT's preimages do. -/
def contentRootFind (hash : List ℤ → ℤ) (objs objs' : List Object) : List ℤ × List ℤ :=
  if objectLeaves hash objs ≠ objectLeaves hash objs' then
    mrootFind hash (objectLeaves hash objs) (objectLeaves hash objs')
  else
    firstObjFind objs objs'

/-- **⚑ THE CONTENT ROOT BINDS THE COMMITTED OBJECT SET — UNCONDITIONALLY.** Two buckets with the
same content root hold the SAME ordered objects, OR the pair `contentRootFind` returns is a genuine
collision of the sponge. No ghost object hides under a genuine root unless the provider found a
Poseidon2 collision.

This is what `contentRoot_injective` was reaching for, minus the hypothesis the deployed hash
refutes: it holds OF the deployed Poseidon2 (`Storage.contentRootDeployed_binds_or_collides`). -/
theorem contentRoot_binds_or_collides (hash : List ℤ → ℤ) (objs objs' : List Object)
    (h : contentRoot hash objs = contentRoot hash objs') :
    objs = objs' ∨ SpongeColl hash (contentRootFind hash objs objs') := by
  by_cases hleaves : objectLeaves hash objs ≠ objectLeaves hash objs'
  · refine Or.inr ?_
    simp only [contentRootFind, if_pos hleaves]
    exact (mroot_binds_or_collides hash h).resolve_left hleaves
  · rw [not_not] at hleaves
    simp only [contentRootFind, if_neg (not_not_intro hleaves)]
    exact objectLeaves_binds_or_collides hash objs objs' hleaves

/-- **⚑ THE TRUSTLESS READ IS SOUND — UNCONDITIONALLY.** A served object `o` that opens at position
`i` of the committed bucket IS the object the bucket committed at `i`, OR the provider exhibited a
genuine sponge collision. No trust in the provider, and no refuted floor: a substituted object needs
a real collision, not merely the failure of an unsatisfiable injectivity assumption. -/
theorem read_sound_or_collides (hash : List ℤ → ℤ)
    (objs : List Object) (i : ℕ) (o : Object)
    (hopen : Opens (objectLeaves hash objs) i (objectLeaf hash o)) :
    objs[i]? = some o
    ∨ ∃ o' : Object, objs[i]? = some o' ∧ SpongeColl hash (objectLeafFind o o') := by
  rw [Opens, objectLeaves, List.getElem?_map] at hopen
  cases hm : objs[i]? with
  | none => rw [hm] at hopen; simp at hopen
  | some o' =>
    rw [hm] at hopen
    simp only [Option.map_some, Option.some.injEq] at hopen
    rcases objectLeaf_binds_or_collides hash o o' hopen.symm with heq | hcoll
    · exact Or.inl (by rw [heq])
    · exact Or.inr ⟨o', rfl, hcoll⟩

/-! ### §2½ — the STRENGTH BRIDGES: the deleted keystones are the injective special case.

Each bridge below re-derives, in one line, exactly what the `Poseidon2SpongeCR`-gated original
concluded. That is the proof the cutover surrendered nothing: at the (unsatisfiable) hypothesis the
old theorems assumed, the new unconditional forms give the old conclusions back. They are NOT the
live path — no consumer in this cone calls them — and the floor appears nowhere else in this file. -/

/-- The deleted `objectLeaf_injective`, recovered at an injective sponge (contradiction-style: two
DISTINCT objects cannot share a leaf). -/
theorem objectLeaf_injective_of_binds_or_collides (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (o o' : Object)
    (h : objectLeaf hash o = objectLeaf hash o') (hne : o ≠ o') : False :=
  hne ((objectLeaf_binds_or_collides hash o o' h).resolve_right
    (spongeColl_refutable_of_injective hash hCR _))

/-- The deleted `contentRoot_injective`, recovered at an injective sponge (contradiction-style: two
DISTINCT object sets cannot share a content root). -/
theorem contentRoot_injective_of_binds_or_collides (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (objs objs' : List Object)
    (h : contentRoot hash objs = contentRoot hash objs') (hne : objs ≠ objs') : False :=
  hne ((contentRoot_binds_or_collides hash objs objs' h).resolve_right
    (spongeColl_refutable_of_injective hash hCR _))

/-- The deleted `read_sound`, recovered at an injective sponge (contradiction-style: a served object
that opens cannot differ from the committed one). -/
theorem read_sound_of_binds_or_collides (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (i : ℕ) (o : Object)
    (hopen : Opens (objectLeaves hash objs) i (objectLeaf hash o))
    (hne : objs[i]? ≠ some o) : False := by
  rcases read_sound_or_collides hash objs i o hopen with h | ⟨_, _, hcoll⟩
  · exact hne h
  · exact spongeColl_refutable_of_injective hash hCR _ hcoll

#assert_axioms objectLeaf_binds_or_collides
#assert_axioms objectLeaves_binds_or_collides
#assert_axioms contentRoot_binds_or_collides
#assert_axioms read_sound_or_collides
#assert_axioms objectLeaf_injective_of_binds_or_collides
#assert_axioms contentRoot_injective_of_binds_or_collides
#assert_axioms read_sound_of_binds_or_collides

end Dregg2.Storage
