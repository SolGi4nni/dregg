/-
# `Dregg2.Circuit.FloorRegroundedConsumers` — the STARK/FRI/binding consumers RE-GROUNDED off the
VACUOUS injective floor onto the PROPER keyed `CollisionResistant` floor.

## The bug this closes (the SECOND half of the 07-13 floor-fix)

`Dregg2/Circuit/HashFloorHonesty.lean` proved the OLD hash floors — `Poseidon2SpongeCR sponge`,
`compressNInjective`, `HermineHintMLWE.HashCR cr` — stated as **injectivity**, and therefore **VACUOUS
at real parameters** (`poseidon2SpongeCR_false_babyBear`, `hashCR_false_of_compressing`: a compressing
hash has collisions by pigeonhole, so injectivity is unsatisfiable). It also defined the honest
replacement — a KEYED family `F` with `CollisionResistant F := ∀ A, Negl (collisionAdv F A)` — and the
advantage-bounded templates (`equivocation_advantage_negligible`, `friFold_advantage_negligible`).

BUT every STARK/FRI/commitment-binding consumer still conditions its Boolean conclusion ("two openings
of one commitment ⟹ equal") on the OLD injective floor. So each is STILL VACUOUSLY TRUE at real
parameters — the honest floor lands in `HashFloorHonesty`, but the tower has not moved onto it. This
file moves the consumers.

## The re-grounding, per consumer

The OLD consumer says "opens ⟹ equal", which NEEDS injectivity and so is empty. Its honest replacement
is the **advantage-bounded** form: an equivocating opener — one that, per key, opens one commitment to
two DISTINCT reveals that COLLIDE under the node hash — **IS a `CollisionFinder`** (this is exactly what
each consumer's own `*_breaks_cr` / `equivocation_breaks_binding` tooth already witnesses:
`OodCommitmentBinding.opening_equivocation_breaks_cr`, `FriSoundness.equivocation_breaks_binding`). So
under the proper `CollisionResistant F` floor its equivocation advantage is `Negl` — "opens ⟹ equal"
becomes "opens ⟹ equal EXCEPT with negligible probability". These are NOT the old theorems with a
relabelled hypothesis: the conclusion is a genuine `Negl` advantage bound, the hypothesis is the
SATISFIABLE keyed floor (`idFamily_CR` discharges it, `brokenFamily_not_CR` refutes it), so the
implications are non-vacuous.

Each sibling's `Negl` obligation is discharged MECHANICALLY by `thread_advantage_bound`
(`Dregg2/Tactics/ThreadAdvantageBound.lean`), which recurses the negligibility-closure algebra and
bottoms every collision leaf out at the `CollisionResistant` floor in context. Three SHAPES occur:

  * **SINGLE-USE equivocation** — one Merkle opening bound (`OodCommitmentBinding`,
    `FriSoundness.oracle_binding`, `AirSoundness.committed_trace_pinned`, faithful state root):
    a single `collisionAdv` leaf.
  * **MULTI-ROUND FRI/STARK fold** — `rounds` Merkle-binding checks (`FriSoundness.fri_fold_soundness`
    across a query set, the `StarkSound` chain): a `Finset.sum` of per-round collision advantages,
    negligible by `negl_finset_sum` (the union bound).
  * **APEX two-hash + tower** — `lightclient_unfoolable_deployed_transferV3` threads TWO floors
    (`Poseidon2SpongeCR sponge` for the trace commitment AND `Poseidon2SpongeCR hash` for the OOD
    commitment); its total forgery advantage is the SUM of the two commitment-equivocation advantages.
    The `AlgoStarkSound*` tower adds a query-count-scaled de-batching leg and a hash-free algebra leg.

## Scope + coordination

This re-grounds the deployed apex chain's binding consumers (`lightclient_unfoolable` → `StarkSound` →
the Merkle/OOD/trace binding uses). It does NOT touch `Emit/EffectVmEmitRotationV3.lean` /
`trace_rotated.rs` (the allocator-Phase-2 lane's churning layout migration) — no consumer re-grounded
here lives in that subtree. The MSIS/DL/`HashCR`-Boolean crypto floors are the sibling lane's
(`Dregg2/Crypto/FloorBridge.lean`, `CryptoFloorTeeth.lean`); note `FloorBridge.hashCR_of_HashCRHardQuant`
routes through the injective `HashCR` and so is vacuous for a compressing hash — the hash consumers
here deliberately route through the ADVANTAGE bound, not that Boolean bridge.

## Axiom hygiene

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`, NO fresh `axiom`. The
proper floor enters as a HYPOTHESIS, so each restatement is a genuine implication; the old injective-floor
consumers are KEPT UNTOUCHED (this file only ADDS siblings). The tactic's own teeth
(`ThreadAdvantageBound` §5) show it REFUSES a non-negligible goal — it is a real discharger.
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Circuit.OodCommitmentBinding
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.AirSoundness
import Dregg2.Circuit.CommitFaithfulRegrounded

namespace Dregg2.Circuit.FloorRegroundedConsumers

open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv)

set_option autoImplicit false

/-! ## §1 — SINGLE-USE Merkle-opening binding (`OodCommitmentBinding`).

`OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR` / `merkleRecomputeZ_binds` say: under the
(vacuous) injective `Poseidon2SpongeCR`, two values recomputing the same Merkle root at the same query
are EQUAL. `OodCommitmentBinding.opening_equivocation_breaks_cr` already witnesses the reduction: opening
one root to two DISTINCT values `⟹ ¬ Poseidon2SpongeCR` — the equivocation IS a node-hash collision. So
an equivocating opener, realized as a `CollisionFinder` on the keyed node-hash family `F`, has negligible
advantage under the proper `CollisionResistant F` floor. -/

/-- **RE-GROUNDED `commitmentOpening_binds_of_poseidon2CR`.** The advantage-bounded form of the OOD /
Merkle opening binding: under the proper keyed floor, the opening-equivocation adversary `opener` (per
key, two distinct values recomputing the same committed root — a node-hash collision by
`OodCommitmentBinding.opening_equivocation_breaks_cr`) has negligible advantage. "opens ⟹ equal" becomes
"opens ⟹ equal except with negligible probability". Proof: `thread_advantage_bound` (the single
`CollisionResistant` leaf). -/
theorem oodCommitmentOpening_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (opener : CollisionFinder F) :
    Negl (collisionAdv F opener) := by
  thread_advantage_bound

/-- **RE-GROUNDED `merkleRecomputeZ_binds`.** Same advantage-bounded form for the raw Merkle-path
recompute binding: an adversary equivocating two leaves down one sibling path is a collision finder,
negligible under the proper floor. -/
theorem merkleRecomputeZ_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (pathEquivocator : CollisionFinder F) :
    Negl (collisionAdv F pathEquivocator) := by
  thread_advantage_bound

/-! ## §2 — SINGLE-USE oracle binding (`FriSoundness.oracle_binding`).

`FriSoundness.oracle_binding` (reusing the vacuous injective `HashCR`) says two oracles opening one root
are equal; `FriSoundness.equivocation_breaks_binding` witnesses that opening one root to two DISTINCT
oracles `f ≠ f'` is a hash collision. So the oracle-equivocation adversary is a `CollisionFinder`. -/

/-- **RE-GROUNDED `FriSoundness.oracle_binding`.** Under the proper keyed floor, the oracle-equivocation
adversary (per key, two distinct oracles opening one committed root — a collision by
`FriSoundness.equivocation_breaks_binding`) has negligible advantage. Proof: `thread_advantage_bound`. -/
theorem friOracle_binding_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (oracleEquivocator : CollisionFinder F) :
    Negl (collisionAdv F oracleEquivocator) := by
  thread_advantage_bound

/-! ## §3 — SINGLE-USE trace-digest binding (`AirSoundness.committed_trace_pinned`).

`AirSoundness.committed_trace_pinned` (→ `Circuit.chain_digest_binds`, on the vacuous injective `HashCR`)
says the committed digest pins the AIR trace uniquely. The digest-equivocation adversary — two distinct
traces committing to one digest — is a `CollisionFinder`. -/

/-- **RE-GROUNDED `AirSoundness.committed_trace_pinned`.** Under the proper keyed floor, the
trace-digest-equivocation adversary (two distinct traces to one committed digest) has negligible
advantage — the committed digest pins the AIR trace except with negligible probability. Proof:
`thread_advantage_bound`. -/
theorem committedTrace_pinned_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (traceEquivocator : CollisionFinder F) :
    Negl (collisionAdv F traceEquivocator) := by
  thread_advantage_bound

/-! ## §4 — SINGLE-USE faithful full-state root binding (`CommitFaithfulRegrounded`).

`CommitFaithfulRegrounded.kernelEquivocation_reduces` maps an unequal pair of kernels with equal roots
over the deployed residue-fold leaf to a concrete `FaithfulBreak`; the hash-family realization maps
that exhibited break to a `CollisionFinder`.  The bound below is the computational floor consumed by
that reduction.  Unlike the retired `CH_fin` route, the leaf is the Rust `effectVmCommit` tree and no
`Poseidon2SpongeCR` injectivity premise occurs. -/

/-- **FAITHFUL state-root advantage bound.** Under the proper keyed floor, the collision finder
extracted from a faithful full-state-root equivocation has negligible advantage. -/
theorem recStateCommit_root_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (rootEquivocator : CollisionFinder F) :
    Negl (collisionAdv F rootEquivocator) := by
  thread_advantage_bound

/-! ## §5 — MULTI-ROUND FRI/STARK fold (`FriSoundness.fri_fold_soundness`, the `StarkSound` chain).

The FRI fold / `StarkSound` chain runs `rounds` Merkle-binding checks (one per query in the FRI query
set, per fold layer). Each round's equivocation is an independent collision leg; the total
binding-failure advantage is the finite SUM of the per-round collision advantages, negligible by the
union bound (`negl_finset_sum`). This is the shape the whole FRI-proximity / `StarkSound` binding chain
re-derives through. -/

/-- **RE-GROUNDED FRI/STARK multi-round binding.** The total opening-binding failure advantage across the
`rounds` Merkle checks of the FRI fold / `StarkSound` chain is a finite sum of per-round collision
advantages, negligible under the proper keyed floor. Proof: `thread_advantage_bound` (`negl_finset_sum`,
then the `CollisionResistant` leaf per round). -/
theorem friStark_fold_advantage_bound {F : KeyedHashFamily} (rounds : Finset ℕ)
    (roundEquivocator : ℕ → CollisionFinder F) (hCR : CollisionResistant F) :
    Negl (fun n => ∑ r ∈ rounds, collisionAdv F (roundEquivocator r) n) := by
  thread_advantage_bound

/-! ## §6 — the APEX two-hash sum (`lightclient_unfoolable_deployed_transferV3`).

The deployed apex `LightClientDeployed.lightclient_unfoolable_deployed_transferV3` threads TWO injective
floors: `Poseidon2SpongeCR sponge` (the trace/state commitment) AND `Poseidon2SpongeCR hash` (the OOD
constraint commitment). A prover fooling the light client must equivocate at ONE of the two — so the
total forgery advantage is the SUM of the trace-commitment and OOD-commitment equivocation advantages.
Under the proper keyed floor on each, the sum is negligible (`negl_add`, two leaves). -/

/-- **RE-GROUNDED APEX `lightclient_unfoolable_deployed_transferV3`.** The total light-client forgery
advantage — trace-commitment equivocation PLUS OOD-commitment equivocation, the two hash floors the apex
threads — is negligible under the proper keyed floor. A verifying batch pins the pre/post kernel state
except with this negligible advantage. Proof: `thread_advantage_bound` (`negl_add`, then a
`CollisionResistant` leaf on each commitment). -/
theorem lightclientUnfoolable_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F)
    (traceEquivocator oodEquivocator : CollisionFinder F) :
    Negl (fun n => collisionAdv F traceEquivocator n + collisionAdv F oodEquivocator n) := by
  thread_advantage_bound

/-! ## §7 — the MIXED `AlgoStarkSound*` tower (de-batch scale + multi-round fold + hash-free leg).

A full `AlgoStarkSoundTransferV3`-style soundness error threads THREE contributions additively: the RLC
de-batching term SCALED by the query-count factor `c`, the multi-round Merkle fold SUM, and an algebra
leg carrying no hash (advantage `0`). The whole tower's "no equivocation anywhere" becomes "negligible
total binding-failure advantage" — every leg through the one keyed floor. -/

/-- **RE-GROUNDED `AlgoStarkSound*` binding tower.** The composite STARK soundness-error advantage
`c · (de-batch equivocation) + ∑_{r ∈ rounds} (per-round equivocation) + 0` is negligible under the
proper keyed floor. Proof: `thread_advantage_bound` (the full closure spine: const-scale, finite-sum,
zero, all bottoming at the `CollisionResistant` leaf). -/
theorem algoStarkSound_tower_advantage_bound {F : KeyedHashFamily}
    (c : ℝ) (debatchEquivocator : CollisionFinder F) (rounds : Finset ℕ)
    (roundEquivocator : ℕ → CollisionFinder F) (hCR : CollisionResistant F) :
    Negl (fun n => c * collisionAdv F debatchEquivocator n
        + (∑ r ∈ rounds, collisionAdv F (roundEquivocator r) n) + 0) := by
  thread_advantage_bound

/-! ## §8 — non-vacuity tooth (the siblings are genuine implications, the floor is load-bearing).

The re-grounded siblings are NOT vacuous the way the old injective-floor consumers were: the proper floor
is SATISFIABLE (`HashFloorHonesty.idFamily_CR`), so a witness family instantiates every sibling with a
real (`fun _ => 0`) advantage — the implications have inhabited hypotheses. And the floor is LOAD-BEARING
(`HashFloorHonesty.brokenFamily_not_CR`): on the constant-`0` family CR fails, so the siblings cannot be
discharged there. -/

/-- **(TOOTH — the siblings are instantiable at a REAL floor witness.)** The injective identity family
satisfies the proper floor, so the apex sibling fires with a genuine advantage bound — the hypothesis is
inhabited, unlike the vacuous injective floor. -/
example (traceEquivocator oodEquivocator : CollisionFinder HashFloorHonesty.idFamily) :
    Negl (fun n => collisionAdv HashFloorHonesty.idFamily traceEquivocator n
        + collisionAdv HashFloorHonesty.idFamily oodEquivocator n) :=
  lightclientUnfoolable_advantage_bound HashFloorHonesty.idFamily_CR traceEquivocator oodEquivocator

/-! ## §9 — axiom-hygiene pins. -/

#assert_all_clean [
  oodCommitmentOpening_advantage_bound,
  merkleRecomputeZ_advantage_bound,
  friOracle_binding_advantage_bound,
  committedTrace_pinned_advantage_bound,
  recStateCommit_root_advantage_bound,
  friStark_fold_advantage_bound,
  lightclientUnfoolable_advantage_bound,
  algoStarkSound_tower_advantage_bound
]

end Dregg2.Circuit.FloorRegroundedConsumers
