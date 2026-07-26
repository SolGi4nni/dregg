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

⛑ **THE ENCODER BUG IS REPAIRED (2026-07-26) — and the repair is a no-op on every correctly
encoded input.** The limb map used to be `x.toNat.toUInt64`; `Int.toNat` CLAMPS every negative to
`0`, so `key = -1` and `key = 0` — two DIFFERENT BabyBear elements — produced the same limb, hence
the same object leaf, hence the same content root. `DeployedFloorRegrounded.deployed_ghost_object_exists`
exhibited that pair with ZERO axioms. The limb map is now `canonLimb`, the CANONICAL reduction
`(x % babyBearP).toNat.toUInt64` (`Int.emod` is non-negative for a positive modulus, so nothing
clamps) — the same shape the tree already uses at `Circuit.MapOpWideKeyCanonDischarge.canonFelt`
and `Crypto.Poseidon2RomHidingInstantiation`.

**MIGRATION: NONE.** `dregg_poseidon2_2to1` (`circuit/src/storage_ffi.rs:12-16`) already reduces its
arguments `% BABYBEAR_P` before hashing, so for every limb `0 ≤ x < 2^64` the OLD and NEW encoders
feed the Rust primitive the identical field element — `x % 2^64` then `% p` versus `x % p` then
`% p`. Every root over correctly encoded (canonical, non-negative) data is BYTE-IDENTICAL across
this change. Only limbs that were being MIS-encoded move: negatives (the bug) and `x ≥ 2^64`.

⚠ **WHAT THE REPAIR DOES NOT BUY, STATED UP FRONT.** It closes the NEGATIVE-INTEGER ghost channel.
It does NOT make `poseidon2Hash` injective — that is unreachable (finite `UInt64` image, infinite
`List ℤ` domain) and is why `DeployedFloorRegrounded` moved the storage binding onto the collision
GAME. And a residual ghost channel SURVIVES, narrower and by design: `canonLimb` is a reduction, so
integers congruent mod `p` share a limb (`canonLimb babyBearP = canonLimb 0`, below). Two integers
congruent mod `p` ARE the same field element, so that is correct field semantics — but
`contentRootFFI` parses arbitrary `String.toInt?` decimals, so a caller that treats keys as unbounded
ℤ rather than as felts still has an aliasing channel. Closing THAT is a wire-contract change (reject
non-canonical limbs at the FFI boundary) and is NOT made here; it is named in
`DeployedFloorRegrounded` §4.1 with the exact recipe.
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

/-- The BabyBear prime, `2^31 - 2^27 + 1`. It must equal the Rust `BABYBEAR_P`
(`circuit/src/field.rs:12`) that `dregg_poseidon2_2to1` reduces its arguments by. ⚠ That agreement is
a WIRE FACT across the `@[extern]`, NOT a theorem — `p2compress` is `opaque` here and nothing in Lean
can see the Rust body. It is checked by reading both sides, which is the honest resolution of an FFI
seam; the same seam every `@[extern]` in this tree carries. -/
def babyBearP : Int := 2013265921

/-- **⛑ THE LIMB ENCODER — the canonical reduction.** A limb is a BabyBear FIELD ELEMENT, so the
integer must be reduced into `[0, p)` before it is narrowed to `UInt64`. `Int.emod` is non-negative
for a positive modulus, so nothing clamps. Same shape as
`Circuit.MapOpWideKeyCanonDischarge.canonFelt` and the `(x % babyBearP).toNat` in
`Crypto.Poseidon2RomHidingInstantiation`; not invented here. -/
def canonLimb (x : Int) : UInt64 := (x % babyBearP).toNat.toUInt64

/-- **THE PRE-FIX LIMB ENCODER, RETAINED AS A SUBJECT.** This is what shipped until 2026-07-26 and
what `DeployedFloorRegrounded.deployed_ghost_object_exists` broke. It is kept — unused by
`poseidon2Hash` — so the defect has a NAME that a regression can be stated against, rather than
vanishing from the record along with the bug. -/
def clampLimb (x : Int) : UInt64 := x.toNat.toUInt64

/-- **THE DEFECT.** `Int.toNat` clamps, so the old encoder MERGED `-1` and `0` — two distinct
BabyBear elements onto one limb. This is the whole content of the ghost object. -/
theorem clampLimb_merges_negative : clampLimb (-1) = clampLimb 0 := by decide

/-- **THE REPAIR.** The canonical reduction SEPARATES them: `-1` encodes to `p - 1`, not to `0`. -/
theorem canonLimb_separates_negative : canonLimb (-1) ≠ canonLimb 0 := by decide

/-- `-1` lands on the canonical representative `p - 1`, exactly as a BabyBear element should. -/
theorem canonLimb_neg_one : canonLimb (-1) = 2013265920 := by decide

/-- **⚠ THE SURVIVING RESIDUAL, PROVED, NOT PROMISED.** `canonLimb` is a REDUCTION, so integers
congruent mod `p` still share a limb. As field semantics this is CORRECT — they denote one element —
but `contentRootFFI` accepts arbitrary decimal integers, so a caller treating keys as unbounded ℤ
retains an aliasing channel. The narrowing is the win (`every negative` → `only p-congruent`); the
closure is a range check at the wire, named in `DeployedFloorRegrounded` §4.1 and not made here. -/
theorem canonLimb_aliases_mod_p : canonLimb babyBearP = canonLimb 0 := by decide

/-- **The deployed hash**: a Poseidon2 sponge fold over the field elements, each step the fast Rust
compress. The verified LOGIC (the fold + the content-root structure) is Lean; the hot PRIMITIVE is
Rust. Limbs go through `canonLimb` — see the ⛑ block in the module header for why, and for why the
change moves no correctly-encoded root. -/
def poseidon2Hash (xs : List Int) : Int :=
  Int.ofNat (xs.foldl (fun acc x => p2compress acc (canonLimb x)) xs.length.toUInt64).toNat

/-- **⛑ THE REGRESSION TOOTH — the pre-fix collision CANNOT SILENTLY RETURN.**

`poseidon2Hash [-1] = poseidon2Hash [0]` used to be closed by `rfl`: the clamp made the two folds
the SAME TERM. It no longer is, and this `fail_if_success` is the machine-checked assertion of that.
Reinstate the clamp — anywhere in the limb path, by any spelling — and this line goes RED at
elaboration. A comment saying "fixed" would not. -/
example : True := by
  fail_if_success (have : poseidon2Hash [(-1 : Int)] = poseidon2Hash [(0 : Int)] := rfl)
  trivial

/-- **The bucket content root over the DEPLOYED Poseidon2** — executable (the `@[export]` wrapper
calls the fast Rust hash through the `@[extern]`). This is what the Rust
`storage::bucket_commitment::content_root` becomes: Lean logic, Rust primitive. Its binding guarantee
is `contentRootDeployed_binds_or_collides` below — UNCONDITIONAL, and deliberately not "binding under
the CR floor", which is the phrasing the 2026-07-25 cutover removed because that floor is refuted at
this very hash. -/
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

/-- **⛑ THE REPAIR, AT THE EXACT PAIR THAT BROKE.** The `key = -1` / `key = 0` ghost pair no longer
comes free: if their deployed content roots are still equal, the extractor hands back a GENUINE
sponge collision. Before the fix this hypothesis was discharged by `rfl` and the "collision" was an
encoder artifact; now supplying it means breaking Poseidon2.

⚠ **AND THE HONEST LIMIT.** This is NOT "the fixed root separates the pair". That statement is
UNPROVABLE in this tree and would be a lie to claim: `p2compress` is `opaque`, so Lean cannot
evaluate the two folds and cannot show their outputs differ. What is proved is the correct and
weaker thing — the pair is separated *unless the primitive itself collides* — which is exactly the
guarantee `contentRootDeployed_binds_or_collides` provides and exactly what the clamp was stealing. -/
theorem prefix_ghost_pair_costs_a_sponge_collision
    (h : contentRootDeployed [{key := -1, contentType := 0, bodyDigest := 0}]
        = contentRootDeployed [{key := 0, contentType := 0, bodyDigest := 0}]) :
    SpongeColl poseidon2Hash
      (contentRootFind poseidon2Hash [{key := -1, contentType := 0, bodyDigest := 0}]
        [{key := 0, contentType := 0, bodyDigest := 0}]) :=
  (contentRootDeployed_binds_or_collides _ _ h).resolve_left (by decide)

#assert_axioms contentRootDeployed_binds_or_collides
#assert_axioms contentRootDeployed_injective_of_binds_or_collides
#assert_axioms clampLimb_merges_negative
#assert_axioms canonLimb_separates_negative
#assert_axioms canonLimb_neg_one
#assert_axioms canonLimb_aliases_mod_p
#assert_axioms prefix_ghost_pair_costs_a_sponge_collision

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
