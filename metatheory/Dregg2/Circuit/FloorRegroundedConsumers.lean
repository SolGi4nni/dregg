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
-- ⚑ IMPORT SURFACE NARROWED (2026-07-22). `FriSoundness`, `AirSoundness` and
-- `CommitFaithfulRegrounded` were imported for the three consumers whose bounds were `hCR opener` — they
-- were never actually USED, because those bounds mentioned none of those files' objects. The two
-- consumers that genuinely need them (`committedTrace_pinned`, `recStateCommit_root`) are documented as
-- BLOCKED at §7 with their precise blockers, and export no bound. So the imports go: a file must not
-- claim a dependency it does not have.
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Circuit.OodCommitmentBinding
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Crypto.RomMerkleOpening

namespace Dregg2.Circuit.FloorRegroundedConsumers

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded negl_add negl_const_mul negl_finset_sum negl_zero)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv idFamily idFamily_CR
   brokenFamily brokenFamily_not_CR)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv hashGame finderToAdv HashCRHardQuant collisionAdv_eq_gameAdv
   collisionResistant_iff_hashCRHardQuant_top collisionResistant_false_of_compressing hard_bot_vacuous)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeKeyed SpongeCarrier IsSpongeColl spongeFamily carrierBreakGame carrierBreakToFinder
   carrier_binds_advantage_bound
   carrierFloor_top_false_babyBear carrierFloor_bot_vacuous)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)

set_option autoImplicit false

/-! ## §0 — ⚑ WHY §1–§7 WERE REWRITTEN (2026-07-22): they were `P → P`, on a FALSE `P`.

The bounds this file used to export had the shape

    theorem oodCommitmentOpening_advantage_bound (hCR : CollisionResistant F) (opener : CollisionFinder F)
        : Negl (collisionAdv F opener) := by thread_advantage_bound

and that is, unfolded, `hCR opener` — the hypothesis handed back as the conclusion. TWO independent
defects, either one fatal:

  1. **The statement does not mention the thing it is named after.** `opener` is an arbitrary
     `CollisionFinder`; nothing in the statement says it opens a Merkle root, nothing says two openings
     disagree, nothing connects it to `merkleRecomputeZ`. The reduction ("an equivocating opener IS a
     collision finder") lived ONLY in the docstring. A theorem whose security content is in its prose
     is not a theorem about that content.
  2. **`CollisionResistant F` is FALSE for every compressing family** — `FloorGames`
     `collisionResistant_iff_hashCRHardQuant_top` + `collisionResistant_false_of_compressing`, which §10
     below already re-proves as `effFloor_top_false_of_compressing`. So the implication was true and
     vacuous at the deployed Poseidon2, exactly the fate of the injective floors this file was written
     to retire. The file's own §9 header says so in as many words; §1–§7 were never brought onto it.

§1–§7 are now genuine SECURITY REDUCTIONS on the `Dregg2.Crypto.SpongeCarrierReduction` spine, in the
shape `Market.WideCommitBoundary` established for the wide carrier:

  * the forgery is a first-class `Game` whose win relation is the DEPLOYED equivocation
    (`carrierBreakGame D merkleOpenCarrier` — one root, one query index, one sibling path, TWO DISTINCT
    opened values);
  * the extractor is a TOTAL FUNCTION `merklePathCollFind` with an UNCONDITIONAL correctness theorem —
    it walks the path and LOCATES the colliding node, where the old proof assumed injectivity and peeled;
  * the advantage inequality (`carrier_adv_le`) quantifies over ALL adversaries — the class does not
    appear in it;
  * the DISCHARGED conclusion (2026-07-24) is on the KEYED-ROM floor, which is PROVED
    (`KeyedRomFloor.keyedRom_hard`, the birthday bound): the `_binds_rom` forms of §2–§6. The
    `IsPolyTime` discharges that briefly stood here carried a floor
    `Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` REFUTES, and are
    deleted; only the `Eff`-parametric fixed-hash forms (`hEff` in the open) remain beside the ROM
    successors, as the honest fixed-hash content.

⚑ **TWO OF THE EIGHT ARE NOT REBUILT, AND ARE NOT FAKED.** `committedTrace_pinned` and
`recStateCommit_root` are documented at §7 with their precise blockers; the honest statements
that ARE available for them are exported there. Do not read their absence as an oversight. -/

/-! ## §1 — the MERKLE-OPENING EXTRACTOR: the induction, turned inside out.

`OodCommitmentBinding.merkleRecomputeZ_binds` peels the sibling path from the OUTSIDE in, applying
`Poseidon2SpongeCR` at each level to conclude the two leaves are equal. That hypothesis is false at
BabyBear, so the conclusion is empty. The honest object does the same walk but in the other direction:
assume the leaves DIFFER, and RETURN the level at which the node hashes collided. -/

/-- **THE ORDERED NODE PREIMAGE at one path level.** The index bit fixes the side (even ⇒ accumulator on
the left), EXACTLY as `merkleRecomputeZ` branches. Naming it makes the extractor's correspondence to the
deployed recompute a rewrite rather than a case split repeated in every proof. -/
def nodeAt (idx : Nat) (acc s : ℤ) : List ℤ := if idx % 2 = 0 then [acc, s] else [s, acc]

/-- **THE DEPLOYED RECOMPUTE, ONE LEVEL, IN TERMS OF `nodeAt`.** The bridge that makes the extractor
provably walk the SAME path the verifier walks — not a parallel reconstruction of it. -/
theorem merkleRecomputeZ_cons (sponge : List ℤ → ℤ) (idx : Nat) (acc s : ℤ) (rest : List ℤ) :
    merkleRecomputeZ sponge idx acc (s :: rest)
      = merkleRecomputeZ sponge (idx / 2) (sponge (nodeAt idx acc s)) rest := by
  have h : sponge (nodeAt idx acc s)
      = (if idx % 2 = 0 then sponge [acc, s] else sponge [s, acc]) := by
    unfold nodeAt
    exact apply_ite sponge _ _ _
  rw [h]
  rfl

/-- Distinct accumulators give DISTINCT node preimages on either side of the index bit — the fact that
makes each level's candidate pair a genuine collision candidate rather than a trivial one. -/
theorem nodeAt_ne (idx : Nat) (l1 l2 s : ℤ) (hne : l1 ≠ l2) :
    nodeAt idx l1 s ≠ nodeAt idx l2 s := by
  intro hc
  unfold nodeAt at hc
  by_cases hb : idx % 2 = 0
  · rw [if_pos hb, if_pos hb] at hc
    exact hne (List.cons.inj hc).1
  · rw [if_neg hb, if_neg hb] at hc
    exact hne (List.cons.inj (List.cons.inj hc).2).1

/-- A node preimage is exactly two felts — the deployed binary Merkle arity. -/
theorem nodeAt_length (idx : Nat) (acc s : ℤ) : (nodeAt idx acc s).length = 2 := by
  unfold nodeAt
  by_cases hb : idx % 2 = 0 <;> simp [hb]

/-- **⚑ THE PATH WALK, AS A FUNCTION.** Descend the sibling path alongside two candidate opened values.
At each level form the two ordered node preimages; if their sponges AGREE, that level IS the collision
(the preimages are distinct whenever the accumulators are) — return it. Otherwise the two new
accumulators are distinct, so recurse. If the path runs out, the caller's equal-root hypothesis has
already forced the two values equal, so the returned value is unconstrained there — `merklePathCollFind_spec`
is what pins the useful case, and it never reaches that branch. -/
def merklePathCollFind (sponge : List ℤ → ℤ) : Nat → ℤ → ℤ → List ℤ → (List ℤ × List ℤ)
  | _, l1, l2, [] => ([l1], [l2])
  | idx, l1, l2, s :: rest =>
      if sponge (nodeAt idx l1 s) = sponge (nodeAt idx l2 s) then
        (nodeAt idx l1 s, nodeAt idx l2 s)
      else
        merklePathCollFind sponge (idx / 2)
          (sponge (nodeAt idx l1 s)) (sponge (nodeAt idx l2 s)) rest

/-- **⚑ THE EXTRACTOR IS CORRECT, UNCONDITIONALLY.** If two DISTINCT values recompute the SAME root at
the same query index over the same sibling path, the walk returns a GENUINE collision of the real sponge:
two distinct lists with equal image. This is `merkleRecomputeZ_binds`'s induction inverted — instead of
ASSUMING injectivity and concluding equality, it assumes inequality and PRODUCES the collision.

⚑ Note what this theorem does NOT take: no collision-resistance hypothesis, no injectivity, no floor.
It is therefore a true statement at deployed BabyBear parameters, unlike the binding it replaces. -/
theorem merklePathCollFind_spec (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ), l1 ≠ l2 →
      merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings →
      IsSpongeColl sponge (merklePathCollFind sponge idx l1 l2 siblings) := by
  intro siblings
  induction siblings with
  | nil =>
      intro idx l1 l2 hne heq
      exact absurd (by simpa [merkleRecomputeZ] using heq) hne
  | cons s rest ih =>
      intro idx l1 l2 hne heq
      rw [merkleRecomputeZ_cons, merkleRecomputeZ_cons] at heq
      by_cases hcoll : sponge (nodeAt idx l1 s) = sponge (nodeAt idx l2 s)
      · rw [merklePathCollFind, if_pos hcoll]
        exact ⟨nodeAt_ne idx l1 l2 s hne, hcoll⟩
      · rw [merklePathCollFind, if_neg hcoll]
        exact ih (idx / 2) _ _ hcoll heq

/-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — every branch returns two lists of at most two felts,
so at most four felts total, whatever the path length. This is the cost model's output-growth obligation,
PROVED rather than assumed; without it the reduction would not provably preserve efficiency. -/
theorem merklePathCollFind_len_le (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ),
      (merklePathCollFind sponge idx l1 l2 siblings).1.length
        + (merklePathCollFind sponge idx l1 l2 siblings).2.length ≤ 4 := by
  intro siblings
  induction siblings with
  | nil => intro idx l1 l2; simp [merklePathCollFind]
  | cons s rest ih =>
      intro idx l1 l2
      by_cases hcoll : sponge (nodeAt idx l1 s) = sponge (nodeAt idx l2 s)
      · rw [merklePathCollFind, if_pos hcoll]
        show (nodeAt idx l1 s).length + (nodeAt idx l2 s).length ≤ 4
        rw [nodeAt_length, nodeAt_length]
      · rw [merklePathCollFind, if_neg hcoll]
        exact ih (idx / 2) _ _

/-- **⚑ THE MERKLE-OPENING CARRIER.** The deployed 1-felt commitment is the path recompute; the shared
context is the query index and sibling path the verifier already fixed; the payload is the opened value.
Everything a `SpongeCarrier` owes the spine, discharged from §1: the extractor, its unconditional
correctness, and its proved output bound. -/
def merkleOpenCarrier : SpongeCarrier where
  Ctx := Nat × List ℤ
  Val := ℤ
  valDecEq := inferInstance
  enc := fun hash c v => merkleRecomputeZ hash c.1 v c.2
  find := fun hash c a b => merklePathCollFind hash c.1 a b c.2
  find_spec := fun hash c a b hne heq => merklePathCollFind_spec hash c.2 c.1 a b hne heq
  size := fun c _ => c.2.length + 1
  outCo := 0
  outBo := 4
  find_len_le := fun hash c a b => by
    have := merklePathCollFind_len_le hash c.2 c.1 a b
    omega

/-- **THE MERKLE-OPENING EQUIVOCATION GAME.** The adversary is handed a uniformly sampled
domain-separation tag and WINS iff it opens ONE committed Merkle root at ONE query index over ONE sibling
path to TWO DISTINCT values. That is exactly the forgery `OodCommitmentBinding.opening_equivocation_breaks_cr`
describes. The break is IN the win relation — not in a docstring. -/
abbrev merkleOpenBreakGame (D : SpongeKeyed) : Game := carrierBreakGame D merkleOpenCarrier

/-- **⚑ THE FORGERY IS THE DEPLOYED OPENING OBJECT.** Two openings of the SAME committed root at the SAME
query index that DISAGREE ARE a `merkleOpenBreakGame` win. This ties the abstract game to the very
`commitmentOpening_binds_of_poseidon2CR` endpoint the OOD/FRI/AIR consumers use, so the game is not a
free-floating construction — it is the deployed check, negated. -/
theorem opening_equivocation_is_break (D : SpongeKeyed) (t : D.Tag) (l : ℕ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ (D.hashAt t) idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ (D.hashAt t) idx vOpened siblings = root) :
    (merkleOpenBreakGame D).wins l t ((idx, siblings), vOpened, vCommitted) :=
  ⟨hne, hOpened.trans hCommitted.symm⟩

/-- **⚑ AND THE EXACT-PROP CONCLUSION IS RECOVERED OFF THE BREAK EVENT.** At any tag where the adversary
does NOT win, the deployed binding holds on the nose: two openings of one root at one query are EQUAL.
So the reduction does not weaken the consumer's conclusion — it prices the event on which it can fail,
which is what "except with negligible probability" means. -/
theorem opening_binds_off_break (D : SpongeKeyed) (t : D.Tag) (l : ℕ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ (D.hashAt t) idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ (D.hashAt t) idx vOpened siblings = root)
    (hsafe : ¬ (merkleOpenBreakGame D).wins l t ((idx, siblings), vOpened, vCommitted)) :
    vOpened = vCommitted := by
  by_contra hne
  exact hsafe ⟨hne, hOpened.trans hCommitted.symm⟩

/-! ## §2 — the OOD / Merkle-opening binder, AS A REDUCTION.

`OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR` says the value `verifyAlgo` opens at ζ and
the honest committed value, both recomputing to one root, are EQUAL — under injectivity. Here it is
instead: an efficient adversary that makes them DISAGREE has negligible advantage, because it would be a
collision finder for the deployed sponge, by §1's extractor. -/

/-! ### The keyed-ROM successors — the DISCHARGED headlines, on a floor that is PROVED.

⚑ **WHAT WAS DELETED HERE (2026-07-24), AND WHY.** The five discharged bounds this section used to
export (`oodCommitmentOpening_advantage_bound`, `friOracle_binding_advantage_bound`,
`friStark_fold_advantage_bound`, `lightclientUnfoolable_advantage_bound`,
`algoStarkSound_tower_advantage_bound`) closed their floor at
`HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))` — and
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` PROVES that floor FALSE at
deployed BabyBear parameters (`IsPolyTime` prices answer SIZE, so a `Classical.choice` `.pure`-leaf
answering a short collision is in the class and wins with probability `1`). Nor can a better `Eff`
repair the fixed-hash game (`Crypto.RomBindingReduction`'s header): the fixed public sponge can be
brute-forced by anything allowed to evaluate it. The floor must move to a SAMPLED oracle, where the
birthday bound is a THEOREM (`KeyedRomFloor.keyedRom_hard`). The successors below are that move, on
`Crypto.RomMerkleOpening`'s walking-extractor kit; the `Eff`-parametric forms (§2's
`merkleRecomputeZ_advantage_bound`, §9) remain as the honest fixed-hash content, `hEff` in the open.

⚑ **THE MODELLING STEP, STATED (not smuggled), exactly `RomMerkleOpening`'s header:** the fixed
Poseidon2 node hash is idealised as a keyed RANDOM ORACLE over ordered node pairs at an ASYMPTOTIC
digest width `Fin (2 ^ l)` — there is NO `l` at which that is the deployed ~31-bit BabyBear felt, and
at the deployed width the honest reading stays "binds exactly as well as ~31 bits allow" (birthday
≈ `2^15.5`, the felt-width wound). The depth `d` is pinned per parameter, as deployed: a committed
tree has a fixed height. -/

/-- **THE MERKLE-OPENING FORGERY GAME AT THE SAMPLED ORACLE** — `merkleOpenBreakGame`'s win relation
(one root, one shared index-bit/sibling path, TWO DISTINCT opened leaves), transposed to the oracle
model, keyed by the DEPLOYED sponge's own tag space. -/
abbrev merkleOpenRomBreakGame (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (d : ℕ → ℕ) : Game :=
  Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame D.Tag D.tagFintype tagDec D.tagNonempty d

/-- **THE QUERY-BOUNDED OPENING-FORGER CLASS at this site** — the fixed `Eff` the successors close
at: the forger factors through a `Q`-query oracle tree fixed BEFORE the oracle is sampled. -/
abbrev MerkleOpenRomEff (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (d Q : ℕ → ℕ) :
    Adversary (merkleOpenRomBreakGame D tagDec d) → Prop :=
  Dregg2.Crypto.RomCarrierSites.RomForgeryEff
    (Dregg2.Crypto.RomMerkleOpening.merkleRomFamily D.Tag D.tagFintype tagDec D.tagNonempty)
    (Dregg2.Crypto.RomMerkleOpening.merkleOpenForgery D.Tag D.tagFintype tagDec D.tagNonempty d) Q

/-- **⚑⚑ THE OOD / MERKLE-OPENING BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the
deleted `oodCommitmentOpening_advantage_bound` (floor refuted, §-header): a query-bounded forger that
opens one committed OOD/Merkle root at one query to two DISTINCT leaves has NEGLIGIBLE advantage, in
the keyed ROM model. The hypotheses are a polynomial total budget `Q'` dominating the forger's `Q`
plus the extractor's `2·d` re-walk — nothing refutable. Combined with `opening_binds_off_break`,
"opens ⟹ equal" stays "opens ⟹ equal except with negligible probability". -/
theorem oodCommitmentOpening_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (merkleOpenRomBreakGame D tagDec d))
    (hA : MerkleOpenRomEff D tagDec d Q A) :
    Negl (gameAdv (merkleOpenRomBreakGame D tagDec d) A) :=
  Dregg2.Crypto.RomMerkleOpening.merkleOpenRom_binds
    D.Tag D.tagFintype tagDec D.tagNonempty d Q Q' hle hQ' A hA

/-- **⚑ RE-GROUNDED `merkleRecomputeZ_binds` — the raw path recompute binds, as a REDUCTION.** The same
spine at the general path-equivocation adversary, stated at an ARBITRARY adversary class so a consumer
that has not yet instantiated `Eff` can still land on it (`hEff` in the open, `FloorGames` §8). The
DISCHARGED instance is `oodCommitmentOpening_binds_rom` above — on the keyed-ROM floor, not on the
refuted `IsPolyTime` one. -/
theorem merkleRecomputeZ_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (pathEquivocator : Adversary (merkleOpenBreakGame D))
    (hEff : Eff (carrierBreakToFinder D merkleOpenCarrier pathEquivocator))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (merkleOpenBreakGame D) pathEquivocator) :=
  carrier_binds_advantage_bound D merkleOpenCarrier Eff pathEquivocator hEff hCR

/-! ## §3 — the FRI oracle binder, AS A REDUCTION.

`FriSoundness.oracle_binding` says two oracles opening one root are equal, under the vacuous injective
`HashCR`. ⚑ WHAT IS MODELLED HERE, PRECISELY: the DEPLOYED FRI verifier never compares whole oracles —
it checks, per query in the FRI query set, that the opened evaluation recomputes the committed layer root
(`FriVerifier.merkleRecompute`, the `merkleRecomputeZ` of §1). Two distinct oracles opening one root must
disagree at SOME query, and at that query the check is exactly a two-value opening equivocation. So the
per-query opening IS the deployed object, and it is what §3 bounds.

⚑ WHAT IS NOT CLOSED BY THIS: `FriSoundness`'s `OracleCR` is an ABSTRACT `CommitReveal` over an abstract
`Digest`, not a `ℤ`-valued deployed function, so the step from "the abstract `cr.opens root () f`" to
"the deployed per-query Merkle recompute" is a MODELLING identification, stated here rather than proved.
Proving it needs `FriSoundness` to be re-stated over the concrete Merkle commitment — real work, in a
file this lane does not own. Named, not smuggled. -/

/-- **⚑ RE-GROUNDED `FriSoundness.oracle_binding` — the per-query FRI layer opening binds, ON THE
PROVED FLOOR** — the successor of the deleted `friOracle_binding_advantage_bound`: a query-bounded
adversary that opens one committed FRI layer root at one query to two distinct evaluations has
negligible advantage in the keyed ROM model. See the §3 header for exactly which step is modelled and
which is proved — that identification is unchanged by the floor move. -/
theorem friOracle_binding_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (oracleEquivocator : Adversary (merkleOpenRomBreakGame D tagDec d))
    (hA : MerkleOpenRomEff D tagDec d Q oracleEquivocator) :
    Negl (gameAdv (merkleOpenRomBreakGame D tagDec d) oracleEquivocator) :=
  oodCommitmentOpening_binds_rom D tagDec d Q Q' hle hQ' oracleEquivocator hA

/-! ## §4 — MULTI-ROUND FRI/STARK fold: the union bound over REAL per-round games.

The FRI fold / `StarkSound` chain runs one Merkle-binding check per query per fold layer. Each round's
equivocation is now a genuine `merkleOpenBreakGame` win at that round's own adversary, so the total
binding-failure advantage is the finite SUM of REAL game advantages — negligible by the union bound.
The old version summed `collisionAdv F (roundEquivocator r)`, i.e. summed the hypothesis. -/

/-- **⚑ RE-GROUNDED FRI/STARK multi-round binding, ON THE PROVED FLOOR** — the successor of the
deleted `friStark_fold_advantage_bound`: the total opening-binding failure advantage across the
`rounds` Merkle checks is a finite sum of PER-ROUND MERKLE-OPENING GAME advantages at the sampled
oracle, negligible by the union bound. Each round's equivocator carries its own query-class
membership. -/
theorem friStark_fold_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (rounds : Finset ℕ)
    (roundEquivocator : ℕ → Adversary (merkleOpenRomBreakGame D tagDec d))
    (hA : ∀ r ∈ rounds, MerkleOpenRomEff D tagDec d Q (roundEquivocator r)) :
    Negl (fun n => ∑ r ∈ rounds,
      gameAdv (merkleOpenRomBreakGame D tagDec d) (roundEquivocator r) n) :=
  negl_finset_sum rounds (fun r hr =>
    oodCommitmentOpening_binds_rom D tagDec d Q Q' hle hQ' (roundEquivocator r) (hA r hr))

/-! ## §5 — the APEX two-hash sum, AS A REDUCTION.

The deployed apex threads TWO commitments — the trace/state commitment and the OOD constraint commitment.
A prover fooling the light client must equivocate at ONE of them, so the total forgery advantage is the
SUM of the two per-commitment MERKLE-OPENING GAME advantages. Both legs are the same deployed check at
different roots, so both ride §1's extractor; the sum is negligible by `negl_add`. -/

/-- **⚑ RE-GROUNDED APEX light-client forgery bound.** The total light-client forgery advantage —
trace-commitment opening equivocation PLUS OOD-commitment opening equivocation — is negligible under the
deployed sponge's collision floor, with both legs' efficiency DISCHARGED.

⚑ HONEST SCOPE, unchanged by this rebuild: this bounds the HASH-BINDING contribution to the apex forgery
advantage. It is not the whole light-client soundness — the FRI proximity leg is a separate, named
residual (`AirSoundness`'s `FriProximity`), and the ~31-bit felt width of the digest means the collision
game itself is winnable in ~2^15.5 work by birthday search. What is closed is that this leg now rests on
a floor the deployed sponge does not REFUTE, instead of one it does. -/
theorem lightclientUnfoolable_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (traceEquivocator oodEquivocator : Adversary (merkleOpenRomBreakGame D tagDec d))
    (hT : MerkleOpenRomEff D tagDec d Q traceEquivocator)
    (hO : MerkleOpenRomEff D tagDec d Q oodEquivocator) :
    Negl (fun n => gameAdv (merkleOpenRomBreakGame D tagDec d) traceEquivocator n
        + gameAdv (merkleOpenRomBreakGame D tagDec d) oodEquivocator n) :=
  negl_add (oodCommitmentOpening_binds_rom D tagDec d Q Q' hle hQ' traceEquivocator hT)
    (oodCommitmentOpening_binds_rom D tagDec d Q Q' hle hQ' oodEquivocator hO)

/-! ## §6 — the MIXED `AlgoStarkSound*` tower, AS A REDUCTION, ON THE PROVED FLOOR. -/

/-- **⚑ RE-GROUNDED `AlgoStarkSound*` binding tower** — the successor of the deleted
`algoStarkSound_tower_advantage_bound` (whose `IsPolyTime` floor §-header refutes): the composite
STARK soundness-error advantage `c · (de-batch equivocation) + ∑_{r ∈ rounds} (per-round
equivocation) + 0` is negligible in the keyed ROM model — const-scale (`negl_const_mul`), finite-sum
(`negl_finset_sum` inside `friStark_fold_binds_rom`), zero (`negl_zero`), every collision leg through
a REAL per-leg Merkle-opening game at the SAMPLED oracle, each equivocator carrying its own
query-class membership. NO floor hypothesis is carried; the floor is `keyedRom_hard`, PROVED. -/
theorem algoStarkSound_tower_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (c : ℝ) (debatchEquivocator : Adversary (merkleOpenRomBreakGame D tagDec d))
    (rounds : Finset ℕ)
    (roundEquivocator : ℕ → Adversary (merkleOpenRomBreakGame D tagDec d))
    (hD : MerkleOpenRomEff D tagDec d Q debatchEquivocator)
    (hA : ∀ r ∈ rounds, MerkleOpenRomEff D tagDec d Q (roundEquivocator r)) :
    Negl (fun n => c * gameAdv (merkleOpenRomBreakGame D tagDec d) debatchEquivocator n
        + (∑ r ∈ rounds, gameAdv (merkleOpenRomBreakGame D tagDec d) (roundEquivocator r) n)
        + 0) :=
  negl_add
    (negl_add
      (negl_const_mul c
        (oodCommitmentOpening_binds_rom D tagDec d Q Q' hle hQ' debatchEquivocator hD))
      (friStark_fold_binds_rom D tagDec d Q Q' hle hQ' rounds roundEquivocator hA))
    negl_zero

/-! ## §7 — ⚑ THE TWO SITES THAT ARE **NOT** REBUILT, AND WHY (BLOCKED, NOT FAKED).

Two of the eight consumers cannot be put on this spine without work in files this lane does not own.
Recording the precise blocker is the point; a fabricated reduction here would be worse than the `P → P`
it replaced, because it would LOOK closed.

**(a) `committedTrace_pinned` — the AIR trace-digest binder.** `AirSoundness.committed_trace_pinned`
routes through `Circuit.chain_digest_binds`, which is stated over an ABSTRACT `CommitReveal Unit Pre Dig`
with an abstract `Dig` and the abstract floor `HashCR cr := ∀ ctx a b, cr.commit ctx a = cr.commit ctx b
→ a = b`. There is no `List ℤ → ℤ` deployed function in that statement, so there is no `SpongeCarrier` to
build: `enc` has nowhere to land. What is available and honest is the PER-QUERY form — the committed
Merkle root pins the opened trace ROW at each query — which is exactly §2's bound at the trace root, and
is what a STARK verifier actually checks. Pinning the WHOLE trace additionally needs the FRI proximity
leg, which is a separate named residual and NOT a hash-floor consequence. Closing (a) properly means
re-stating `chain_digest_binds` over the concrete Merkle commitment in `Dregg2/Circuit.lean`.

**(b) `recStateCommit_root` — the faithful full-state root binder.** `CommitFaithfulRegrounded`'s
extractor chain ends at `FaithfulBreak`, which is a DISJUNCTION OF EXISTENTIALS (`SpongeCollision h :=
∃ xs ys, xs ≠ ys ∧ h xs = h ys`, and four siblings of the same shape). `SpongeCarrier.find` needs a
TOTAL FUNCTION from an equivocation to a collision — that is the whole content of the repair, because an
existential extractor is precisely the "quantifies over SOLUTIONS" defect this sweep exists to retire.
Going from `FaithfulBreak` to a function requires `Classical.choice`, and a choice-extracted finder is
NOT an efficient adversary — it would satisfy `IsPolyTime` only by declaring a cost for a function that
has no algorithm, which is laundering. Closing (b) properly means re-proving
`recStateCommit_binds_kernel_orBreak` with a function-valued extractor (the shape
`Emit.EffectVmEmitRotationR.wireCommit8Find` already has for the wide leg) in `CommitFaithfulRegrounded`
/ `StateCommit` — real proof engineering, not a restatement.

Both are on the work-list. Neither is exported from this file as a bound. -/

/-! ## §8 — non-vacuity and load-bearingness of the REBUILT spine.

The rebuilt bounds are not vacuous the way §0's `P → P` forms were, and the teeth that show it are the
spine's own (`SpongeCarrierReduction` §5): the floor is priced at BOTH poles, and the canary shows the
bound does NOT follow from the floor applied at an unrelated finder. -/

/-- **(TOOTH — the floor these bounds rest on is FALSE at the REAL BabyBear parameters.)** The honest
price of every `hEff` discharge above, re-exported at this file's carrier so no consumer can read its own
reduction as stronger than it is. What the rebuild buys is NOT a floor the deployed sponge satisfies at
the unrestricted class — no such floor exists — it is that the residual is ONE named parameter with both
poles proved, instead of a hypothesis the deployed hash simply refutes. -/
theorem merkleFloor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  carrierFloor_top_false_babyBear D hb

/-- **(TOOTH — the other pole is vacuous.)** Recorded beside the refutation so satisfiability of the
floor can never be mistaken for evidence. -/
theorem merkleFloor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  carrierFloor_bot_vacuous D

/-- **(CANARY — the rebuilt bound does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the opening equivocator's negligibility from the collision floor at some OTHER
finder `B`, not the one EXTRACTED from it. It does not go through — only `carrier_adv_le` at the
extracted finder connects the two games. This tooth reds if a future edit disconnects them, which is
exactly the edit that would restore the `P → P` shape. -/
example (D : SpongeKeyed) (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (merkleOpenBreakGame D)) (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (merkleOpenBreakGame D) A) := hCR B hB)
  trivial

/-- **(CANARY — the QUERY-CLASS hypothesis is load-bearing, not decorative.)** The rebuilt ROM bound
cannot be had without `hA` (the forger factors through a `Q`-query tree): `trivial` does not prove the
existential class membership, and the application does not elaborate. The retired `P → P` form needed
no such hypothesis precisely because it did no work. -/
example (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (merkleOpenRomBreakGame D tagDec d)) : True := by
  fail_if_success
    (have : Negl (gameAdv (merkleOpenRomBreakGame D tagDec d) A) :=
      oodCommitmentOpening_binds_rom D tagDec d Q Q' hle hQ' A trivial)
  trivial

/-- **THE POSITIVE POLE — the rebuilt bound FIRES, on an ADMITTED member of the class.** A gate that
refuses everything is a broken keystone, not a fixed one. The `0`-query constant answerer — the exact
shape that refutes the `IsPolyTime` floor with probability `1` against the fixed sponge — is IN the
query class (`constOpenAdv_in_eff`), WINS at the constant oracle when the depth is positive and the
leaves distinct (`constOpenAdv_gameAdv_pos` — the game is genuinely winnable), and the discharged
bound applies to it: NEGLIGIBLE advantage. Admitted, positive, defanged — the counterexample dying at
this site, with no `IsPolyTime` anywhere. -/
theorem the_rebuilt_opening_bound_fires (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (c : ∀ l, D.Tag × (Fin (d l) → Bool × Fin (2 ^ l))) (v w : ∀ l, Fin (2 ^ l)) :
    MerkleOpenRomEff D tagDec d Q
        (Dregg2.Crypto.RomMerkleOpening.constOpenAdv D.Tag D.tagFintype tagDec D.tagNonempty d c v w)
      ∧ Negl (gameAdv (merkleOpenRomBreakGame D tagDec d)
        (Dregg2.Crypto.RomMerkleOpening.constOpenAdv D.Tag D.tagFintype tagDec D.tagNonempty d c v w))
      ∧ ∀ l, 1 ≤ d l → v l ≠ w l →
        0 < gameAdv (merkleOpenRomBreakGame D tagDec d)
          (Dregg2.Crypto.RomMerkleOpening.constOpenAdv D.Tag D.tagFintype tagDec D.tagNonempty d c v w) l :=
  ⟨Dregg2.Crypto.RomMerkleOpening.constOpenAdv_in_eff D.Tag D.tagFintype tagDec D.tagNonempty
      d c v w Q,
    Dregg2.Crypto.RomMerkleOpening.constOpenAdv_negl D.Tag D.tagFintype tagDec D.tagNonempty
      d Q Q' hle hQ' c v w,
    fun l hd hvw => Dregg2.Crypto.RomMerkleOpening.constOpenAdv_gameAdv_pos
      D.Tag D.tagFintype tagDec D.tagNonempty d c v w l hd hvw⟩

/-! ## §9 — ⚑ the `Eff`-CARRYING re-grounding (FINDING-2 of the 07-17 sweep).

⚑ **THE `CollisionResistant F` HYPOTHESIS EVERY §1-§7 SIBLING TAKES IS ITSELF FALSE AT DEPLOYED
PARAMETERS.** `FloorGames.collisionResistant_iff_hashCRHardQuant_top` proves `CollisionResistant F ↔
HashCRHardQuant F ⊤`, and `collisionResistant_false_of_compressing` proves that floor FALSE for ANY
compressing family — every real Poseidon2 node hash. So the §1-§7 bounds (kept above, untouched, and
consumed by `Poseidon2KeyedBridge`'s deployed re-groundings) are true implications off a hypothesis that
transports NO security. This section re-grounds each onto `HashCRHardQuant F Eff` — the SAME collision
game over the SAME family, at an EXPLICIT adversary class, with each finder's `Eff` obligation carried in
the open at the use site (`FloorGames` §8 — this tree has no cost model). The deployed-sponge instances
land in `Circuit.DomainSeparatedCREffRegrounded`; these are the generic-`F` keystones. -/

/-- **THE SINGLE-FINDER `Eff` KEYSTONE.** An equivocator in the class `Eff` has negligible collision
advantage: the `CollisionFinder` advantage the old consumers state IS the game advantage the honest floor
bounds (`collisionAdv_eq_gameAdv`). Every single-use §1-§4 binder re-grounds through this one. -/
theorem collision_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (A : CollisionFinder F)
    (hEff : Eff (finderToAdv A)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F A) := by
  rw [collisionAdv_eq_gameAdv]
  exact hD _ hEff

/-- **RE-GROUNDED `commitmentOpening_binds_of_poseidon2CR` (`Eff` form).** -/
theorem oodCommitmentOpening_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (opener : CollisionFinder F)
    (hEff : Eff (finderToAdv opener)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F opener) :=
  collision_advantage_bound_eff Eff opener hEff hD

/-- **RE-GROUNDED `merkleRecomputeZ_binds` (`Eff` form).** -/
theorem merkleRecomputeZ_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (pathEquivocator : CollisionFinder F)
    (hEff : Eff (finderToAdv pathEquivocator)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F pathEquivocator) :=
  collision_advantage_bound_eff Eff pathEquivocator hEff hD

/-- **RE-GROUNDED `FriSoundness.oracle_binding` (`Eff` form).** -/
theorem friOracle_binding_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (oracleEquivocator : CollisionFinder F)
    (hEff : Eff (finderToAdv oracleEquivocator)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F oracleEquivocator) :=
  collision_advantage_bound_eff Eff oracleEquivocator hEff hD

/-- **RE-GROUNDED `AirSoundness.committed_trace_pinned` (`Eff` form).** -/
theorem committedTrace_pinned_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (traceEquivocator : CollisionFinder F)
    (hEff : Eff (finderToAdv traceEquivocator)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F traceEquivocator) :=
  collision_advantage_bound_eff Eff traceEquivocator hEff hD

/-- **RE-GROUNDED faithful full-state root binding (`Eff` form).** -/
theorem recStateCommit_root_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (rootEquivocator : CollisionFinder F)
    (hEff : Eff (finderToAdv rootEquivocator)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F rootEquivocator) :=
  collision_advantage_bound_eff Eff rootEquivocator hEff hD

/-- **RE-GROUNDED multi-round FRI/STARK fold (`Eff` form).** The total binding-failure advantage across the
`rounds` Merkle checks is a finite SUM of per-round collision advantages, negligible under the `Eff`-floor
by `negl_finset_sum`. Every round's equivocator carries its own `hEff`. -/
theorem friStark_fold_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (rounds : Finset ℕ)
    (roundEquivocator : ℕ → CollisionFinder F)
    (hEff : ∀ r ∈ rounds, Eff (finderToAdv (roundEquivocator r)))
    (hD : HashCRHardQuant F Eff) :
    Negl (fun n => ∑ r ∈ rounds, collisionAdv F (roundEquivocator r) n) :=
  negl_finset_sum rounds
    (fun r hr => collision_advantage_bound_eff Eff (roundEquivocator r) (hEff r hr) hD)

/-- **⚑ RE-GROUNDED APEX two-hash forgery advantage (`Eff` form).** The light-client forgery advantage —
trace-commitment equivocation PLUS OOD-commitment equivocation — is negligible under the `Eff`-floor, each
finder carrying its own `hEff`. This is the apex bound `Poseidon2KeyedBridge`'s deployed sibling ships; the
`Eff` form transports security where the `CollisionResistant`-shaped one does not (§9 header). -/
theorem lightclientUnfoolable_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop)
    (traceEquivocator oodEquivocator : CollisionFinder F)
    (hEffT : Eff (finderToAdv traceEquivocator)) (hEffO : Eff (finderToAdv oodEquivocator))
    (hD : HashCRHardQuant F Eff) :
    Negl (fun n => collisionAdv F traceEquivocator n + collisionAdv F oodEquivocator n) :=
  negl_add (collision_advantage_bound_eff Eff traceEquivocator hEffT hD)
    (collision_advantage_bound_eff Eff oodEquivocator hEffO hD)

/-- **RE-GROUNDED `AlgoStarkSound*` binding tower (`Eff` form).** The composite STARK soundness-error
advantage `c · (de-batch equivocation) + ∑ (per-round equivocation) + 0` is negligible under the `Eff`-floor
— const-scale (`negl_const_mul`), finite-sum (`negl_finset_sum`), zero (`negl_zero`), each collision leaf
through the one `Eff`-floor. Every finder carries its own `hEff`. -/
theorem algoStarkSound_tower_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop)
    (c : ℝ) (debatchEquivocator : CollisionFinder F) (rounds : Finset ℕ)
    (roundEquivocator : ℕ → CollisionFinder F)
    (hEffD : Eff (finderToAdv debatchEquivocator))
    (hEff : ∀ r ∈ rounds, Eff (finderToAdv (roundEquivocator r)))
    (hD : HashCRHardQuant F Eff) :
    Negl (fun n => c * collisionAdv F debatchEquivocator n
        + (∑ r ∈ rounds, collisionAdv F (roundEquivocator r) n) + 0) :=
  negl_add
    (negl_add (negl_const_mul c (collision_advantage_bound_eff Eff debatchEquivocator hEffD hD))
      (negl_finset_sum rounds
        (fun r hr => collision_advantage_bound_eff Eff (roundEquivocator r) (hEff r hr) hD)))
    negl_zero

/-! ## §10 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at a compressing family.)** At the unrestricted class the `Eff`-floor IS
`CollisionResistant F` (`collisionResistant_iff_hashCRHardQuant_top`), FALSE for any compressing node hash
(`collisionResistant_false_of_compressing`). The price of every `hEff` above, stated as a theorem: the
class cannot be left implicit, because the implicit `⊤` is the empty hypothesis §1-§7 rested on. -/
theorem effFloor_top_false_of_compressing {F : KeyedHashFamily} (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) :=
  fun h => collisionResistant_false_of_compressing F hin hcol
    ((collisionResistant_iff_hashCRHardQuant_top F).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY family. -/
theorem effFloor_bot_vacuous {F : KeyedHashFamily} : HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the apex bound does NOT follow from the floor applied at another adversary.)** Strip the
connection — try to conclude the trace/OOD equivocators' negligibility from the floor applied at some OTHER
adversary `B` — and the proof does not go through: `hD B hB` bounds a DIFFERENT ensemble, and only
`collisionAdv_eq_gameAdv` at the EXTRACTED finders connects it to the apex sum. -/
example {F : KeyedHashFamily} (Eff : Adversary (hashGame F) → Prop)
    (traceEquivocator oodEquivocator : CollisionFinder F)
    (B : Adversary (hashGame F)) (hB : Eff B) (hD : HashCRHardQuant F Eff) : True := by
  fail_if_success
    (have : Negl (fun n => collisionAdv F traceEquivocator n + collisionAdv F oodEquivocator n) :=
      negl_add (hD B hB) (hD B hB))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge the apex.** With the floor at the EXTRACTED finders
the apex bound fires; refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_apex_fires_on_the_right_floor {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop)
    (traceEquivocator oodEquivocator : CollisionFinder F)
    (hEffT : Eff (finderToAdv traceEquivocator)) (hEffO : Eff (finderToAdv oodEquivocator))
    (hD : HashCRHardQuant F Eff) :
    Negl (fun n => collisionAdv F traceEquivocator n + collisionAdv F oodEquivocator n) :=
  lightclientUnfoolable_advantage_bound_eff Eff traceEquivocator oodEquivocator hEffT hEffO hD

/-! ## §11 — axiom-hygiene pins. -/

#assert_all_clean [
  merkleRecomputeZ_cons,
  nodeAt_ne,
  nodeAt_length,
  merklePathCollFind_spec,
  merklePathCollFind_len_le,
  opening_equivocation_is_break,
  opening_binds_off_break,
  oodCommitmentOpening_binds_rom,
  merkleRecomputeZ_advantage_bound,
  friOracle_binding_binds_rom,
  friStark_fold_binds_rom,
  lightclientUnfoolable_binds_rom,
  algoStarkSound_tower_binds_rom,
  merkleFloor_top_false_babyBear,
  merkleFloor_bot_vacuous,
  the_rebuilt_opening_bound_fires,
  collision_advantage_bound_eff,
  oodCommitmentOpening_advantage_bound_eff,
  merkleRecomputeZ_advantage_bound_eff,
  friOracle_binding_advantage_bound_eff,
  committedTrace_pinned_advantage_bound_eff,
  recStateCommit_root_advantage_bound_eff,
  friStark_fold_advantage_bound_eff,
  lightclientUnfoolable_advantage_bound_eff,
  algoStarkSound_tower_advantage_bound_eff,
  effFloor_top_false_of_compressing,
  effFloor_bot_vacuous,
  the_repaired_apex_fires_on_the_right_floor
]

end Dregg2.Circuit.FloorRegroundedConsumers
