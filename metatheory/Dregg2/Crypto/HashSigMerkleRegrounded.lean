/-
# `Dregg2.Crypto.HashSigMerkleRegrounded` — the SLH-DSA / SPHINCS+ MANY-TIME hash signature binding
RE-GROUNDED off the VACUOUS injective `Poseidon2SpongeCR` floor onto the PROPER keyed `CollisionResistant`
floor.

## The gap this closes (the hash-signature sponge leg of the forward-scaffolding floor sweep)

`HashSigMerkle.merkle_ots_binds_index` is the BINDING floor of the many-time hash signature (a Merkle root
over `N` one-time keys — the SLH-DSA / SPHINCS+ shape): any verifying signature at index `i` carries EXACTLY
the OTS public key committed at `i` (no key swap), so a verifying forgery is a genuine Lamport forgery on the
committed key. It is conditioned on `Poseidon2Binding.Poseidon2SpongeCR hash` — the SAME injective sponge
floor `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE (a compressing sponge has collisions
by pigeonhole). The deployed p3 Poseidon2 sponge is compressing, so the deployed key-swap binding is
VACUOUSLY TRUE at real parameters.

This is the SPONGE leg — the SAME shape as `Circuit.FloorRegroundedConsumers` (the STARK/FRI Merkle binding),
which re-grounds the injective `Poseidon2SpongeCR`/`HashCR` consumers onto the keyed `CollisionResistant`
floor via an abstract node-hash family `F` and discharges the `Negl` obligation with `thread_advantage_bound`.
This file moves the hash-signature consumer the same way.

## The re-grounding

The OLD consumer says "verifying signature ⟹ committed key" (a key swap ⟹ equal), which NEEDS sponge
injectivity and so is empty. Its honest replacement is the ADVANTAGE-BOUNDED form: a leaf-swap equivocation
adversary — one that, per key, presents two DISTINCT OTS public keys hashing (through `pkEncode`/`pkLeaf`)
to ONE committed Merkle leaf — **IS a `CollisionFinder`** on the keyed sponge family `F` (exactly the
collision `HashSigMerkle.merkle_ots_binds_index` rules out via `hCR _ _ hleaf`). So under the proper
`CollisionResistant F` floor its equivocation advantage is `Negl` — "key swap ⟹ committed key" becomes
"⟹ committed key EXCEPT with negligible probability". Discharged by `thread_advantage_bound` (the single
`CollisionResistant` leaf).

## Non-fake

The floor is SATISFIABLE (`HashFloorHonesty.idFamily_CR`), so the sibling fires at a real floor witness with a
genuine advantage bound; and LOAD-BEARING (`HashFloorHonesty.brokenFamily_not_CR`): on the constant-`0`
sponge family CR fails, so the sibling cannot be discharged there. Old injective-floor consumer KEPT
untouched; sibling ADDED. `#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no
fresh `axiom`, no `native_decide`.

## Coordination

Hash-signature sponge leg. The STARK/FRI/apex sponge consumers are `Circuit.FloorRegroundedConsumers`
(sibling lane, same abstract-family shape); the commit-reveal `HashCR` consumers are
`HermineHashCRRegrounded` / `IdentityCommitmentRegrounded` / `WireAkeRegrounded` /
`RandomnessBeaconRegrounded` / `XmVrfRefinementRegrounded`. Stays in the hash-signature subtree.
-/
import Dregg2.Tactics.ThreadAdvantageBound

namespace Dregg2.Crypto.HashSigMerkleRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv idFamily idFamily_CR
   brokenFamily brokenFamily_not_CR)

set_option autoImplicit false

/-! ## §1 — the advantage-bounded key-swap binding (`merkle_ots_binds_index`, re-grounded).

`HashSigMerkle.merkle_ots_binds_index` (on the vacuous injective `Poseidon2SpongeCR`) says a verifying
signature at index `i` carries the committed OTS public key. Its own proof witnesses the reduction: a key
swap forces `pkLeaf hash s.pk = pkLeaf hash (publicKey …)`, and `hCR _ _ hleaf` (sponge collision-resistance)
peels the sponge — so a DISTINCT verifying key at a leaf IS a sponge collision. That equivocation, realized
as a `CollisionFinder` on the keyed sponge family `F`, has negligible advantage under the proper floor. -/

/-- **RE-GROUNDED `HashSigMerkle.merkle_ots_binds_index`.** The advantage-bounded form of the many-time
key-swap binding: under the proper keyed sponge floor, the leaf-swap-equivocation adversary `leafSwap` (per
key, two DISTINCT OTS public keys hashing through `pkEncode`/`pkLeaf` to one committed Merkle leaf — a sponge
collision) has negligible advantage. "verifying signature ⟹ committed key" becomes "⟹ committed key except
with negligible probability": a key swap at an index succeeds only with negligible advantage, and a verifying
forgery is a genuine Lamport forgery on the committed key except with that advantage. Proof:
`thread_advantage_bound` (the single `CollisionResistant` leaf). -/
theorem merkle_ots_binds_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (leafSwap : CollisionFinder F) :
    Negl (collisionAdv F leafSwap) := by
  thread_advantage_bound

/-! ## §2 — non-vacuity (the sibling is a genuine implication, the floor is load-bearing). -/

/-- **(TOOTH — the sibling is instantiable at a REAL floor witness.)** The injective identity family satisfies
the proper floor, so the key-swap binding sibling fires with a genuine advantage bound — the hypothesis is
inhabited, unlike the vacuous injective sponge floor. -/
theorem merkle_ots_binds_fires (leafSwap : CollisionFinder idFamily) :
    Negl (collisionAdv idFamily leafSwap) :=
  merkle_ots_binds_advantage_bound idFamily_CR leafSwap

/-- **(TOOTH — the floor is LOAD-BEARING.)** On the constant-`0` sponge family collision-resistance FAILS
(`brokenFamily_not_CR`), so the sibling cannot be discharged there — a broken sponge admits a leaf swap. The
proper floor is a genuine constraint, exactly as `merkle_ots_binds_index` needs the sponge collision-resistant
to forbid the key swap. -/
theorem merkle_ots_binds_floor_load_bearing : ¬ CollisionResistant brokenFamily :=
  brokenFamily_not_CR

#assert_all_clean [
  merkle_ots_binds_advantage_bound,
  merkle_ots_binds_fires
]

end Dregg2.Crypto.HashSigMerkleRegrounded
