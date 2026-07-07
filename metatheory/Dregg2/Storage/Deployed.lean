/-
# `Dregg2.Storage.Deployed` — the bucket content root over the DEPLOYED Poseidon2, via Lean↔Rust FFI.

The storage proofs (`BucketCommitment`) are over an ABSTRACT collision-resistant hash — the stronger
form (they hold for *any* CR hash). This module instantiates them at the **deployed** hash: the fast
Rust/plonky3 Poseidon2, called from Lean through `@[extern]` (the same shape as
`@[extern "dregg_ed25519_verify"]` in `Crypto/PortalFloor.lean`).

The runtime split: the verified content-root LOGIC is Lean (compiled to native via `leanc`); the hot
Poseidon2 PRIMITIVE is the fastest Rust, called back through a **native-scalar** `@[extern]`
(`u64 → u64 → u64` — trivial ABI, no `lean_object` marshaling); the FFI binds them both ways.
Lean-side the crypto is the opaque `p2compress` (the binding proofs assume `Poseidon2SpongeCR` about
the resulting hash — the §8 floor, never a Lean law); the Rust symbol `dregg_poseidon2_2to1` realizes
it at runtime, wrapping `circuit::binding` Poseidon2.
-/
import Dregg2.Storage.BucketCommitment

namespace Dregg2.Storage

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **The fast Rust Poseidon2 2-to-1 compress**, called from Lean via a native-scalar `@[extern]`
(`u64 → u64 → u64`) — trivial ABI, no `lean_object`. Realized at runtime by `dregg_poseidon2_2to1`
(wrapping `circuit::binding` Poseidon2 over BabyBear; field elements < 2^31 fit a `u64`). Opaque
here; soundness is the §8 collision-resistance carrier, never a Lean law. -/
@[extern "dregg_poseidon2_2to1"]
opaque p2compress : UInt64 → UInt64 → UInt64

/-- **The deployed hash**: a Poseidon2 sponge fold over the field elements, each step the fast Rust
compress. The verified LOGIC (the fold + the content-root structure) is Lean; the hot PRIMITIVE is
Rust. The binding proofs assume `Poseidon2SpongeCR` about this `def` (the crypto floor). -/
def poseidon2Hash (xs : List Int) : Int :=
  Int.ofNat (xs.foldl (fun acc x => p2compress acc x.toNat.toUInt64) xs.length.toUInt64).toNat

/-- **The bucket content root over the DEPLOYED Poseidon2** — executable (the `@[export]` wrapper
calls the fast Rust hash through the `@[extern]`), and — under the CR floor for the deployed hash —
binding. This is what the Rust `storage::bucket_commitment::content_root` becomes: Lean logic, Rust
primitive. -/
def contentRootDeployed (objs : List Object) : Int :=
  contentRoot poseidon2Hash objs

/-- **The deployed content root binds the committed object set** — the extracted, real-crypto form of
`contentRoot_injective`, discharged by the collision-resistance carrier for the deployed Poseidon2.
No ghost object hides under a genuine deployed root. -/
theorem contentRootDeployed_injective (hCR : Poseidon2SpongeCR poseidon2Hash) :
    ∀ objs objs' : List Object,
      contentRootDeployed objs = contentRootDeployed objs' → objs = objs' :=
  contentRoot_injective poseidon2Hash hCR

#assert_axioms contentRootDeployed_injective

/-- Build objects from a flat int list (triples: key, contentType, bodyDigest). -/
private partial def buildObjects : List Int → List Object
  | k :: c :: b :: rest => {key := k, contentType := c, bodyDigest := b} :: buildObjects rest
  | _ => []

/-- **FFI entry** (Rust→Lean): space-separated ints (triples = objects) → the deployed content root
as a decimal string. This runs the VERIFIED Lean content-root logic, calling the fast Rust Poseidon2
through the `@[extern]` — the real "Lean is the runtime" for storage. -/
@[export dregg_storage_content_root]
def contentRootFFI (input : String) : String :=
  let nums := (input.splitOn " ").filterMap String.toInt?
  toString (contentRootDeployed (buildObjects nums))

end Dregg2.Storage
