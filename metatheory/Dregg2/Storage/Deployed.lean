/-
# `Dregg2.Storage.Deployed` — the bucket content root over the DEPLOYED Poseidon2, via Lean↔Rust FFI.

The storage proofs (`BucketCommitment`) are over an ABSTRACT collision-resistant hash — the stronger
form (they hold for *any* CR hash). This module instantiates them at the **deployed** hash: the fast
Rust/plonky3 Poseidon2, called from Lean through `@[extern]` (the same shape as
`@[extern "dregg_ed25519_verify"]` in `Crypto/PortalFloor.lean`).

The runtime split: the verified content-root LOGIC is Lean (compiled to native via `leanc`); the hot
Poseidon2 PRIMITIVE is the fastest Rust, called back through a **native-scalar** `@[extern]`
(`u64 → u64 → u64` — trivial ABI, no `lean_object` marshaling); the FFI binds them both ways.
Lean-side the crypto is the opaque `p2compress`; the Rust symbol `dregg_poseidon2_2to1` realizes it at
runtime, wrapping `circuit::binding` Poseidon2.

⚑ **CUTOVER 2026-07-25.** The binding proof used to ASSUME `Poseidon2SpongeCR` about `poseidon2Hash`.
`DeployedFloorRefuted.deployed_floor_false` refutes that by `rfl` — `Int.toNat` clamps `-1` and `0`
onto one `UInt64` limb — so `contentRootDeployed_injective` was VACUOUS AT DEPLOYMENT and is DELETED.
Its replacement `contentRootDeployed_binds_or_collides` carries NO hypothesis: it binds, or the total
extractor hands back the colliding pair.

⛔ **AND THE ENCODER BUG IS REAL, NOT HYPOTHETICAL.**
`DeployedFloorRegrounded.deployed_ghost_object_exists` exhibits — with ZERO axioms — two DISTINCT
objects (`key = -1` and `key = 0`) sharing one deployed content root. The clamp on line 33 below is
the cause (`DeployedFloorRegrounded.deployedLimb_collides` vs `babyBearLimb_separates`, both by
`decide`). Not repaired here: `poseidon2Hash` is on the `@[export]` FFI path, so changing the limb
encoding changes emitted roots and is a wire change.
-/
import Dregg2.Storage.BucketCommitment

namespace Dregg2.Storage

open Dregg2.Circuit.Poseidon2Binding
  (Poseidon2SpongeCR SpongeColl spongeColl_refutable_of_injective)

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

/-- **⚑ THE DEPLOYED CONTENT ROOT BINDS THE COMMITTED OBJECT SET — UNCONDITIONALLY.**

Two buckets with the same DEPLOYED content root hold the SAME ordered objects, OR
`contentRootFind` hands back the specific pair of sponge inputs at which the DEPLOYED
`poseidon2Hash` collides. No ghost object hides under a genuine deployed root unless the provider
found a real Poseidon2 collision.

⚑ **THIS REPLACES `contentRootDeployed_injective` (2026-07-25), WHICH WAS VACUOUS AT DEPLOYMENT.**
That theorem was gated on `Poseidon2SpongeCR poseidon2Hash` — literal injectivity of THIS `def` —
and `DeployedFloorRefuted.deployed_floor_false` refutes it by `rfl`: `Int.toNat` clamps `-1` and `0`
to the same `UInt64` limb, so `poseidon2Hash [-1] = poseidon2Hash [0]`. The hypothesis could never be
supplied, so the theorem said nothing about the deployed bucket store. It is not repairable by a
better encoder either — `poseidon2Hash` factors through `UInt64`, a finite image over an infinite
domain, so exact injectivity is unsatisfiable at ANY encoding.

This statement has NO hypothesis at all, so it holds OF the deployed hash. What it costs is named,
not hidden: the guarantee is now "binds, unless a collision was found", and
`Storage.DeployedFloorRegrounded` prices that residual as an advantage in a real collision GAME —
satisfiable at the deployed hash, refutable, not provable — instead of assuming it away. -/
theorem contentRootDeployed_binds_or_collides (objs objs' : List Object)
    (h : contentRootDeployed objs = contentRootDeployed objs') :
    objs = objs' ∨ SpongeColl poseidon2Hash (contentRootFind poseidon2Hash objs objs') :=
  contentRoot_binds_or_collides poseidon2Hash objs objs' h

/-- **THE STRENGTH BRIDGE, and the record of what it is worth.** At the (refuted) injectivity the old
`contentRootDeployed_injective` assumed, the collision disjunct is impossible and its exact conclusion
returns — so the cutover surrendered nothing. Read it beside
`DeployedFloorRefuted.deployed_floor_false`: this hypothesis is FALSE at `poseidon2Hash`, which is
precisely why the unconditional form above is the one a light client can use. -/
theorem contentRootDeployed_injective_of_binds_or_collides
    (hCR : Poseidon2SpongeCR poseidon2Hash) (objs objs' : List Object)
    (h : contentRootDeployed objs = contentRootDeployed objs') (hne : objs ≠ objs') : False :=
  hne ((contentRootDeployed_binds_or_collides objs objs' h).resolve_right
    (spongeColl_refutable_of_injective poseidon2Hash hCR _))

#assert_axioms contentRootDeployed_binds_or_collides
#assert_axioms contentRootDeployed_injective_of_binds_or_collides

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
