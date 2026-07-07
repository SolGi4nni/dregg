/-
# `Dregg2.Storage.BucketCommitment` — the bucket object-store's content commitment, IN LEAN.

The Rust `storage::bucket_commitment` (Poseidon2 content-root + trustless `verify_opening`) was
built Rust-first. THIS is its Lean source of truth: the content commitment as an executable
`MMR.mroot` fold over per-object leaves, with the binding proved down to the ONE
`Poseidon2SpongeCR` crypto floor — the SAME carrier the MMR / cap-root / heap-root rest on, and
nothing else assumed.

* `objectLeaf` — the wide leaf `H(key, contentType, bodyDigest)`; its arity-3 preimage separates it
  from the Merkle nodes (arity 2) and the MMR log leaves (arity 1) under CR, so no domain tag.
* `contentRoot` — the bucket commitment: `MMR.mroot` over the object leaves.
* `objectLeaf_injective` / `contentRoot_injective` — the root BINDS the committed object set (no
  ghost object hides under a genuine root).
* `read_sound` — the TRUSTLESS READ: a served object that opens at a position is genuinely the
  object the bucket committed there, no trust in the provider. Reduces to the MMR positional
  binding + `objectLeaf_injective`.

Only `Poseidon2SpongeCR` is assumed (checked by `#assert_axioms`); everything else is proved.
-/
import Dregg2.Lightclient.MMR

namespace Dregg2.Storage

open Dregg2.Lightclient.MMR
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

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

/-- **The object leaf binds its object.** Under the CR floor, equal leaves force equal objects —
the arity-3 preimage is componentwise-injective. -/
theorem objectLeaf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    Function.Injective (objectLeaf hash) := by
  intro o o' h
  have hl := hCR _ _ h
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨hk, hc, hb⟩ := hl
  cases o
  cases o'
  simp_all

/-- **The content root binds the committed object set.** Two buckets with the same content root
hold the SAME ordered objects — no ghost object can hide under a genuine root. Reduces to
`MMR.mroot_injective` (the leaf list is pinned) + `objectLeaf_injective` (each leaf pins its
object). -/
theorem contentRoot_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ objs objs' : List Object, contentRoot hash objs = contentRoot hash objs' → objs = objs' := by
  intro objs objs' h
  have hleaves : objectLeaves hash objs = objectLeaves hash objs' :=
    mroot_injective hash hCR h
  exact List.map_injective_iff.mpr (objectLeaf_injective hash hCR) hleaves

/-- **The trustless read is sound.** If a served object `o` opens at position `i` of the committed
bucket — its leaf is the genuine `i`-th leaf under the published root — then `o` is genuinely the
object the bucket committed at `i`. No trust in the serving provider (a substituted object would
have a different leaf, refused by CR). -/
theorem read_sound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (i : ℕ) (o : Object)
    (hopen : Opens (objectLeaves hash objs) i (objectLeaf hash o)) :
    objs[i]? = some o := by
  rw [Opens, objectLeaves, List.getElem?_map] at hopen
  cases hm : objs[i]? with
  | none => rw [hm] at hopen; simp at hopen
  | some o' =>
    rw [hm] at hopen
    simp only [Option.map_some, Option.some.injEq] at hopen
    rw [objectLeaf_injective hash hCR hopen]

#assert_axioms objectLeaf_injective
#assert_axioms contentRoot_injective
#assert_axioms read_sound

end Dregg2.Storage
