/-
# `Dregg2.Storage.Retrievability` — proof-of-retrievability, IN LEAN, on the bucket commitment.

The existing Rust storage is CLIENT-side (`availability`/`retrieval`: a light client samples chunks
from untrusted operators and Merkle-verifies each against the manifest root). This is the
PROVIDER-side dual: an auditor challenges a set of positions, the provider answers with the objects
it serves there, and each answer is Merkle-checked against the committed content root. The soundness
is proved down to `BucketCommitment.read_sound` (hence to the one `Poseidon2SpongeCR` floor) — a
provider that PASSES holds the GENUINE committed objects at every challenged position, and cannot
substitute or fabricate one.

The remaining sampling-EXTRACTABILITY step (passing a random challenge ⟹ enough shards held that
the blob RECONSTRUCTS) is the honest boundary: it composes the per-position soundness proved here
with the erasure k-of-n reconstruction theorem (`Dregg2/Storage/Erasure.lean`, forthcoming) plus the
availability sampling bound (`erasure::sample_availability`). It is NOT assumed away here — the real,
load-bearing part (each sampled point is trustworthy, and a forged point is refused) is proved.
-/
import Dregg2.Storage.BucketCommitment

namespace Dregg2.Storage

open Dregg2.Lightclient.MMR (Opens)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- A provider's response to one challenged position: the object it serves for position `pos`. -/
structure Response where
  pos : ℕ
  obj : Object
deriving Repr

/-- The response OPENS against the committed bucket: its object is the genuine `pos`-th leaf under
the published content root. (The verifier checks this via the Merkle opening; `Opens` is the
semantic content the opening witnesses — `read_sound` reduces it to the root.) -/
def opensAt (hash : List ℤ → ℤ) (objs : List Object) (r : Response) : Prop :=
  Opens (objectLeaves hash objs) r.pos (objectLeaf hash r.obj)

/-- **A provider PASSES the audit** iff every response opens against the committed bucket. -/
def passes (hash : List ℤ → ℤ) (objs : List Object) (responses : List Response) : Prop :=
  ∀ r ∈ responses, opensAt hash objs r

/-- **PoR soundness (per challenged position).** Every response a passing provider gives IS the
genuine object the bucket committed at that position — no substitution, no fabrication. Reduces to
`BucketCommitment.read_sound`. -/
theorem por_sound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (responses : List Response) (hpass : passes hash objs responses) :
    ∀ r ∈ responses, objs[r.pos]? = some r.obj := by
  intro r hr
  exact read_sound hash hCR objs r.pos r.obj (hpass r hr)

/-- **Anti-forgery (the negative pole — the audit BITES).** A provider serving an object DIFFERENT
from the one committed at a position cannot produce a passing response there: the substituted
object has a different leaf, refused by CR. -/
theorem por_refuses_substitution (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (r : Response) (hne : objs[r.pos]? ≠ some r.obj) :
    ¬ opensAt hash objs r := by
  intro hopen
  exact hne (read_sound hash hCR objs r.pos r.obj hopen)

/-- **The passing set is genuine end-to-end.** A provider that passes a challenge holds EXACTLY the
committed objects at every challenged position — the full per-position guarantee, mapped over the
whole response set. This is the load-bearing input to the sampling-extractability step: each of the
`q` sampled points is trustworthy, so a provider passing `q` distinct challenges genuinely holds `q`
distinct committed objects (which, once ≥ the erasure threshold `k`, reconstructs — via
`Erasure.lean`). -/
theorem por_holds_committed (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs : List Object) (responses : List Response) (hpass : passes hash objs responses) :
    responses.map (fun r => objs[r.pos]?) = responses.map (fun r => some r.obj) := by
  apply List.map_congr_left
  intro r hr
  exact por_sound hash hCR objs responses hpass r hr

#assert_axioms por_sound
#assert_axioms por_refuses_substitution
#assert_axioms por_holds_committed

end Dregg2.Storage
