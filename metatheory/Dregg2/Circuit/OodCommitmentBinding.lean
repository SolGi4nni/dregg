/-
# Dregg2.Circuit.OodCommitmentBinding — STARK-FLOOR REDUCTION 3: `hood.b` reduced to `Poseidon2SpongeCR`.

**What this closes.** `FieldIntegerLift.OodInterpF.hood` (the per-constraint OOD identity
`(constraintPoly d t c).eval ζ = Zp.eval ζ · (qp c).eval ζ`) bundles THREE sub-obligations
(`docs/SUPERSEDED/STARK-FLOOR-REDUCTION.md §1`):

  * (a) RLC de-batching — Schwartz–Zippel, no assumption [handled by the RLC lane];
  * (b) **commitment-opening binding** — the value `verifyAlgo` OPENS at ζ (`TableOpening.constraintEval`)
        genuinely equals the COMMITTED constraint polynomial evaluated at ζ, i.e. the Merkle/FRI opening
        BINDS — a prover cannot open the commitment to a different value [THIS FILE];
  * (c) FRI low-degreeness — the genuine hard floor [later].

Sub-obligation (b) is NOT algebra: it is a hash-binding fact. This module REDUCES it to the ONE named
hash floor `Poseidon2SpongeCR` (`Dregg2/Circuit/Poseidon2Binding.lean`, a `Prop` HYPOTHESIS, never an
`axiom`) — the SAME floor `AggAirSound.combine_digest_binds` (the CR tooth) and `FriVerifier`'s
`merkleRecompute_binds` rest on. After this, `hood.b` is a legitimately-named crypto assumption (same
status as the PQ apex's hash/lattice floors), NOT a bare `hood` premise.

## The reduction (a break ⟹ a Poseidon2 collision)

`TableOpening.constraintEval` is delivered to the verifier by a Poseidon2 Merkle opening: the opened
leaf (the field value) is recomputed up its sibling path (`FriVerifier.merkleRecompute`, the
`MerkleTreeMmcs` opening — each node hashes two child digests, order fixed by the index bit) and
compared to the committed root. We model the node hash as the ordered two-felt Poseidon2 sponge
`sponge [l, r]` — the EXACT binary specialization whose collision-resistance is `Poseidon2SpongeCR`,
identical to `AggAirSound.Hsponge`.

  * **`merkleRecomputeZ_binds`** (mirrors `FriVerifier.merkleRecompute_binds`) — under
    `Poseidon2SpongeCR`, two leaves that recompute the SAME root at the SAME query index over the SAME
    sibling path are EQUAL. Proven by induction on the path; the ONLY crypto reliance is that each node
    hash `sponge [·, ·]` is injective, which is `Poseidon2SpongeCR` (`injection` splits `[a,b]=[a',b']`).
  * **`commitmentOpening_binds_of_poseidon2CR`** (THE `hood.b` REDUCTION) — under `Poseidon2SpongeCR`,
    an opened value `vOpened` and the honest committed value `vCommitted := (constraintPoly d t c).eval ζ`
    that BOTH recompute to the same committed root ARE EQUAL: the opened `constraintEval` is BOUND to the
    committed polynomial's evaluation. An adversary opening a DIFFERENT value forces two distinct leaves
    to the same root — a Poseidon2 collision (`opening_equivocation_breaks_cr`: a break ⟹ `¬
    Poseidon2SpongeCR`). This is the honest floor, not a re-assumed `hood.b`.

Anti-ghost, witnessed BOTH ways: on the injective toy sponge (`Poseidon2Binding.Reference.refSponge`,
CR-discharged) an honest opening BINDS (`honest_opening_binds`); on a NON-injective sponge
(constant-zero) an adversary equivocates two distinct values to the same root, and that equivocation
IS a witnessed collision (`constant_sponge_equivocates` — the CR floor is load-bearing, not vacuous).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `Poseidon2SpongeCR` is a Prop
hypothesis where used, never an `axiom`. Imported into `Dregg2.lean` (transitively, via `StarkSoundFriLdt`/`AlgoStarkSoundTransferV3`, which CONSUME `commitmentOpening_binds_of_poseidon2CR` on the deployed soundness path).

## Remaining wire to `OodInterpF.hood`

The standalone binding is proven green. To land it INTO `OodInterpF.hood` for the deployed verifier one
supplies three deployment-plumbing facts (the same "unmodeled commitment/column layout" residual the doc
names, NOT new crypto): (i) the committed root of the constraint-poly commitment and that
`verifyAlgo`'s accepted opening (`OodQuotientConsistency.verifyAlgo_accept_forces_table_identity` ties
`topen.constraintEval` to `A.mul vanishingAtZeta quotientAtZeta`) recomputes to it via `merkleRecomputeZ`;
(ii) the honest committed leaf equals `(constraintPoly d t c).eval ζ` cast to the leaf felt; (iii) the
BabyBear→ℤ canonical-representative bridge (the same one `FieldIntegerLift` carries). Given those,
`commitmentOpening_binds_of_poseidon2CR` yields `topen.constraintEval = (constraintPoly d t c).eval ζ` —
`hood.b`, now DERIVED FROM `Poseidon2SpongeCR`.
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Crypto.RomMerkleOpening

namespace Dregg2.Circuit.OodCommitmentBinding

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeCarrier SpongeKeyed spongeFamily carrierBreakGame
   carrierFloor_top_false_babyBear carrierFloor_bot_vacuous)
open Dregg2.Crypto.FloorGames (Adversary gameAdv HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)

/-! ## §1 — the ordered two-felt Merkle node hash (the `Poseidon2SpongeCR` binary specialization).

A Poseidon2 `MerkleTreeMmcs` node hashes two child digests into the parent; the index bit fixes the
order (even ⇒ `acc` on the left). We model the multi-lane digest as a single felt over the list-sponge
`sponge`, so a node hash is `sponge [l, r]` — the EXACT binary specialization of the sponge whose
collision-resistance is `Poseidon2SpongeCR` (identical to `AggAirSound.Hsponge`). -/

/-- Scalar-digest Merkle-path recompute: fold the opened `leaf` (a single felt) up through the
`siblings`, hashing two child digests per level with the ordered node hash `sponge [·, ·]`, branching on
the index bit exactly as `FriVerifier.merkleRecompute` does. Structural recursion on `siblings`. -/
def merkleRecomputeZ (sponge : List ℤ → ℤ) : Nat → ℤ → List ℤ → ℤ
  | _, acc, [] => acc
  | idx, acc, s :: rest =>
      merkleRecomputeZ sponge (idx / 2)
        (if idx % 2 = 0 then sponge [acc, s] else sponge [s, acc]) rest

/-! ## §2 — the Merkle binding tooth (mirrors `FriVerifier.merkleRecompute_binds`). -/

/-- One Merkle level, as the deployment computes it: the index bit fixes which side the accumulator
goes on. Named so the extractor and the recompute can be reasoned about with the same object. -/
def nodeStep (sponge : List ℤ → ℤ) (idx : Nat) (acc s : ℤ) : List ℤ :=
  if idx % 2 = 0 then [acc, s] else [s, acc]

theorem merkleRecomputeZ_cons (sponge : List ℤ → ℤ) (idx : Nat) (acc s : ℤ) (rest : List ℤ) :
    merkleRecomputeZ sponge idx acc (s :: rest)
      = merkleRecomputeZ sponge (idx / 2) (sponge (nodeStep sponge idx acc s)) rest := by
  have hdef : merkleRecomputeZ sponge idx acc (s :: rest)
      = merkleRecomputeZ sponge (idx / 2)
          (if idx % 2 = 0 then sponge [acc, s] else sponge [s, acc]) rest := rfl
  rw [hdef, nodeStep]
  by_cases hb : idx % 2 = 0 <;> simp [hb]

/-- Two distinct accumulators land on two distinct node preimages at the same level and sibling. -/
theorem nodeStep_ne (sponge : List ℤ → ℤ) (idx : Nat) {a b : ℤ} (s : ℤ) (hne : a ≠ b) :
    nodeStep sponge idx a s ≠ nodeStep sponge idx b s := by
  unfold nodeStep
  by_cases hb : idx % 2 = 0 <;> simp [hb, hne]

/-! ### ⚑ THE `Poseidon2SpongeCR` FLOOR IS DELETED FROM THE MERKLE BINDING.

`merkleRecomputeZ_binds` used to take `hCR : Poseidon2SpongeCR sponge`. That floor is **FALSE at
deployed BabyBear parameters** (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` — a bounded field
range against an infinite `List ℤ` domain), so the theorem the whole FRI/STARK tower consumes for its
opening binding was **VACUOUSLY TRUE at the deployed hash**. It is a true implication whose hypothesis
nothing deployed satisfies, and `#assert_axioms` cannot see that: the proof was clean; the HYPOTHESIS
was the flaw. This is the single most load-bearing instance of the defect in the tree, because
`hood.b`, `FriSoundness.oracle_binding` and `AirSoundness.committed_trace_pinned` all bottom out here.

What replaces it assumes NOTHING: the path induction that used to peel a CR hypothesis becomes a walk
that LOCATES the colliding node. The deployed binding is then §3.1's reduction. -/

/-- **THE MERKLE-PATH EXTRACTOR.** Walk the sibling path carrying the two divergent accumulators; the
FIRST level at which they hash to the same node is a genuine sponge collision, and it is handed back.
A total function — the `([], [])` fallback is returned only at the end of the path, which the spec's
hypotheses exclude (at an empty path the two recomputes ARE the two accumulators). -/
def merkleFind (sponge : List ℤ → ℤ) : Nat → ℤ → ℤ → List ℤ → List ℤ × List ℤ
  | _, _, _, [] => ([], [])
  | idx, a, b, s :: rest =>
      if sponge (nodeStep sponge idx a s) = sponge (nodeStep sponge idx b s) then
        (nodeStep sponge idx a s, nodeStep sponge idx b s)
      else
        merkleFind sponge (idx / 2) (sponge (nodeStep sponge idx a s))
          (sponge (nodeStep sponge idx b s)) rest

/-- **⚑ THE MERKLE-PATH EXTRACTOR IS CORRECT — UNCONDITIONALLY.** Two DISTINCT leaves that recompute
the SAME root at the same index over the same sibling path yield a genuine collision of the deployed
sponge. No collision-resistance hypothesis, no injectivity: unlike the theorem it replaces, this is a
true and non-empty statement at deployed BabyBear parameters. -/
theorem merkleFind_spec (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ), l1 ≠ l2 →
      merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings →
      (merkleFind sponge idx l1 l2 siblings).1 ≠ (merkleFind sponge idx l1 l2 siblings).2
        ∧ sponge (merkleFind sponge idx l1 l2 siblings).1
            = sponge (merkleFind sponge idx l1 l2 siblings).2 := by
  intro siblings
  induction siblings with
  | nil =>
      intro idx l1 l2 hne h
      exact absurd (by simpa [merkleRecomputeZ] using h) hne
  | cons s rest ih =>
      intro idx l1 l2 hne h
      rw [merkleRecomputeZ_cons, merkleRecomputeZ_cons] at h
      by_cases hnode : sponge (nodeStep sponge idx l1 s) = sponge (nodeStep sponge idx l2 s)
      · rw [merkleFind, if_pos hnode]
        exact ⟨nodeStep_ne sponge idx s hne, hnode⟩
      · rw [merkleFind, if_neg hnode]
        exact ih (idx / 2) _ _ hnode h

/-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — it returns two two-felt node preimages, or nothing:
at most four felts, a CONSTANT, whichever branch it takes. The cost model's output-growth obligation,
PROVED rather than assumed; it is what makes the reduction efficiency-preserving. -/
theorem merkleFind_len_le (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ),
      (merkleFind sponge idx l1 l2 siblings).1.length
        + (merkleFind sponge idx l1 l2 siblings).2.length ≤ 4 := by
  intro siblings
  induction siblings with
  | nil => intro idx l1 l2; simp [merkleFind]
  | cons s rest ih =>
      intro idx l1 l2
      by_cases hnode : sponge (nodeStep sponge idx l1 s) = sponge (nodeStep sponge idx l2 s)
      · rw [merkleFind, if_pos hnode]
        show (nodeStep sponge idx l1 s).length + (nodeStep sponge idx l2 s).length ≤ 4
        unfold nodeStep
        by_cases hb : idx % 2 = 0 <;> simp [hb]
      · rw [merkleFind, if_neg hnode]
        exact ih (idx / 2) _ _

/-- **⚑ DEMOTED — `merkleRecomputeZ_binds` at plain INJECTIVITY, which BabyBear REFUTES.**

The named floor `Poseidon2SpongeCR` is DELETED from this statement; what remains is exactly the
injective special case, kept as the strength bridge (nothing was lost re-grounding) and doc-marked as
NOT a deployed guarantee. A deployed BabyBear sponge is not injective, so reading this as a statement
about the running verifier is precisely the vacuity being retired.

**The deployed opening binding is §3.1's `merkleOpening_binds_rom`.** -/
theorem merkleRecomputeZ_binds (sponge : List ℤ → ℤ) (hinj : Function.Injective sponge) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ),
      merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings →
      l1 = l2 := by
  intro siblings idx l1 l2 h
  by_contra hne
  exact (merkleFind_spec sponge siblings idx l1 l2 hne h).1
    (hinj (merkleFind_spec sponge siblings idx l1 l2 hne h).2)

/-! ## §3 — THE `hood.b` REDUCTION: the opened value is BOUND to the committed polynomial. -/

/-- **`commitmentOpening_binds_of_poseidon2CR` (THE `hood.b` REDUCTION).** Under `Poseidon2SpongeCR`,
the value `verifyAlgo` opens at ζ (`vOpened`, the `TableOpening.constraintEval`) and the honest
committed value `vCommitted` (intended `(constraintPoly d t c).eval ζ`) that BOTH recompute to the same
committed Merkle root `root` at the same query index over the same sibling path ARE EQUAL. So the opened
`constraintEval` is BOUND to the committed polynomial's evaluation at ζ — a prover cannot open the
commitment to a different value. The ONLY crypto reliance is the named `Poseidon2SpongeCR` floor; this
is `hood.b` DERIVED, not re-assumed. -/
theorem commitmentOpening_binds_of_poseidon2CR (sponge : List ℤ → ℤ)
    (hinj : Function.Injective sponge)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    vOpened = vCommitted :=
  merkleRecomputeZ_binds sponge hinj siblings idx vOpened vCommitted (hOpened.trans hCommitted.symm)

/-! ## §3.1 — ⚑ THE DEPLOYED OPENING BINDING, AS A SECURITY REDUCTION.

This is the HEADLINE of the module and it replaces `merkleRecomputeZ_binds` in that role. `hood.b`,
`FriSoundness.oracle_binding` and `AirSoundness.committed_trace_pinned` all consume this binding, so
this is where the tower's opening soundness actually rests.

What changed: the old statement assumed the deployed sponge is injective, which BabyBear refutes, so
it transported nothing. A `binds ∨ collides` disjunction would not have fixed it either — a collision
EXISTS by pigeonhole, so that disjunction is satisfiable through its right branch without binding ever
holding; it quantifies over SOLUTIONS. The reduction below quantifies over EFFICIENT ADVERSARIES: a
prover that opens one committed root at one query to two DIFFERENT values is turned, by `merkleFind`,
into a genuine collision finder for the deployed sponge.

⚑ **WHAT THIS DOES NOT CLOSE.** The digest is ONE felt. The floor bounds an adversary's advantage in
the deployed sponge's collision game; at ~31 bits that game is winnable by birthday search in ~2^15.5
work. The honest reading is "the opening binds exactly as well as the digest width allows", NOT "the
opening binds". Widening is a separate, still-open repair. Nor does this discharge the FRI
low-degreeness floor (sub-obligation (c)), which is untouched and remains the genuine hard residual. -/

/-- **THE MERKLE-OPENING CARRIER.** The context is the deployment's fixed opening data — the query
index and the sibling path — which both claims agree on; the payload is the opened leaf; the
commitment is the recomputed root. The extractor is `merkleFind` with its unconditional spec and its
proved constant output bound.

⚑ **COORDINATION — A DUPLICATE EXISTS UPSTAIRS AND ONE OF THE TWO MUST GO.**
`Circuit.FloorRegroundedConsumers` (which IMPORTS this module) independently grew
`merklePathCollFind` / `merkleOpenCarrier` / `oodCommitmentOpening_advantage_bound` on the same
`SpongeCarrierReduction` spine, for the same deployed object. They are the same extractor and the same
carrier under two names. THIS is the right home — the extractor belongs at the site that defines
`merkleRecomputeZ`, not in a consumers file — so the dedup should DELETE the `FloorRegroundedConsumers`
copies and re-point its `§2` bounds at `merkleOpeningCarrier` here. Recorded rather than done because
that file is another lane's live working copy. -/
def merkleOpeningCarrier : SpongeCarrier where
  Ctx := Nat × List ℤ
  Val := ℤ
  valDecEq := inferInstance
  enc := fun sponge c v => merkleRecomputeZ sponge c.1 v c.2
  find := fun sponge c a b => merkleFind sponge c.1 a b c.2
  find_spec := fun sponge c a b hne heq => merkleFind_spec sponge c.2 c.1 a b hne heq
  size := fun _ _ => 1
  outCo := 0
  outBo := 4
  find_len_le := fun sponge c a b => by
    have := merkleFind_len_le sponge c.2 c.1 a b
    omega

/-- **THE OPENING-EQUIVOCATION GAME.** The adversary is handed a sampled domain-separation tag and
WINS iff it opens one query — one index, one sibling path — to two DISTINCT leaves carrying the SAME
recomputed root. That is exactly the forgery `hood.b` needs excluded, stated as the event it is. -/
abbrev merkleOpeningBreakGame (D : SpongeKeyed) :=
  carrierBreakGame D merkleOpeningCarrier

/-- **⚑⚑ THE DEPLOYED OPENING BINDING — DISCHARGED ON THE PROVED FLOOR.** A query-bounded prover
that equivocates a Merkle opening — one committed root, one shared (index-bit, sibling) path of
pinned depth `d`, TWO DISTINCT opened leaves — has NEGLIGIBLE advantage, in the keyed ROM model of
`RomMerkleOpening`'s header, keyed by the deployed sponge's OWN tag space. NO floor hypothesis is
carried: the floor is `KeyedRomFloor.keyedRom_hard` (the birthday bound), PROVED, where the deleted
`merkleOpening_binds_from_polyTime` carried `HashCRHardQuant … (IsPolyTime …)` — a floor
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` REFUTES at the deployed
sponge. The budget is honest: the walking extractor re-descends both chains, paying `2·d` queries on
top of the forger's `Q`, all inside the polynomial total `Q'`.

⚑ The ROM idealisation is the labelled modelling step of `RomCarrierSites`' header — ideal
`Fin (2 ^ l)` digest vs the deployed ~31-bit felt (birthday ≈ `2^15.5`, the felt-width wound); the
fixed-hash content of this module stays §2/§4's unconditional extractor + the poles below. -/
theorem merkleOpening_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame
      D.Tag D.tagFintype tagDec D.tagNonempty d))
    (hA : Dregg2.Crypto.RomCarrierSites.RomForgeryEff
      (Dregg2.Crypto.RomMerkleOpening.merkleRomFamily D.Tag D.tagFintype tagDec D.tagNonempty)
      (Dregg2.Crypto.RomMerkleOpening.merkleOpenForgery D.Tag D.tagFintype tagDec D.tagNonempty d)
      Q A) :
    Negl (gameAdv (Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame
      D.Tag D.tagFintype tagDec D.tagNonempty d) A) :=
  Dregg2.Crypto.RomMerkleOpening.merkleOpenRom_binds D.Tag D.tagFintype tagDec D.tagNonempty
    d Q Q' hle hQ' A hA

/-- **(TOOTH — the floor is FALSE at the REAL BabyBear parameters.)** The honest price of the `hEff`
obligation, re-exported here so the tower's opening lane cannot read its own reduction as stronger
than it is. -/
theorem merkleOpening_floor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  carrierFloor_top_false_babyBear D hb

/-- **(TOOTH — the other pole is vacuous.)** Recorded beside the refutation. -/
theorem merkleOpening_floor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  carrierFloor_bot_vacuous D

/-- **`opening_equivocation_breaks_cr` (A BREAK ⟹ A POSEIDON2 COLLISION).** If a prover opens the SAME
committed root at the SAME query to TWO DISTINCT values (`vOpened ≠ vCommitted`), it witnesses that the
sponge is NOT collision-resistant — `¬ Poseidon2SpongeCR`. This is the load-bearing role of the Merkle
commitment: equivocating the opened `constraintEval` after ζ is fixed is EXACTLY a Poseidon2 collision.
So `hood.b` bottoms out at the hash floor and nothing weaker. -/
theorem opening_equivocation_breaks_cr (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    ¬ Poseidon2SpongeCR sponge := fun hCR =>
  hne (commitmentOpening_binds_of_poseidon2CR sponge hCR hCommitted hOpened)

/-! ## §4 — NON-VACUITY: honest openings BIND, and the CR floor is LOAD-BEARING.

The reduction would be hollow if no opening ever bound, or if it bound even without CR. We exhibit BOTH:
on the injective toy sponge (`Poseidon2Binding.Reference.refSponge`, CR-discharged) an honest opening
binds; on a NON-injective sponge (constant-zero) an adversary equivocates two DISTINCT values to the
same root — a witnessed collision showing the `Poseidon2SpongeCR` hypothesis is genuinely required. -/

section Vacuity

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- **`honest_opening_binds` (POSITIVE non-vacuity).** On the injective toy sponge whose CR is proved
(`refSponge_CR`), any two openings to a common root over the same path bind — the reduction FIRES on a
concrete CR-satisfying instance, so `commitmentOpening_binds_of_poseidon2CR` is not vacuous. -/
theorem honest_opening_binds
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ refSponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ refSponge idx vOpened    siblings = root) :
    vOpened = vCommitted :=
  commitmentOpening_binds_of_poseidon2CR refSponge refSponge_CR hCommitted hOpened

/-- The constant-zero sponge — NOT collision-resistant: it maps every input to `0`. -/
def zSponge : List ℤ → ℤ := fun _ => 0

/-- **`constant_sponge_equivocates` (the CR floor is LOAD-BEARING).** Over the constant-zero sponge, two
DISTINCT leaves (`1 ≠ 2`) recompute the SAME root (`0`) over a one-level path — an equivocation. By
`opening_equivocation_breaks_cr` this is a witnessed failure of collision-resistance: `¬
Poseidon2SpongeCR zSponge`. Without the CR hypothesis the binding is FALSE, so the floor is real, not
vacuous — exactly the `OodQuotientConsistency.ood_exceptional_escape` role for `hnonexc`. -/
theorem constant_sponge_equivocates : ¬ Poseidon2SpongeCR zSponge :=
  opening_equivocation_breaks_cr zSponge (root := 0) (idx := 0) (siblings := [5])
    (vCommitted := 2) (vOpened := 1)
    (by decide) (by simp [merkleRecomputeZ, zSponge]) (by simp [merkleRecomputeZ, zSponge])

end Vacuity

/-! ## §5 — axiom hygiene: each result pins exactly the whitelist. -/

#assert_axioms merkleFind_spec
#assert_axioms merkleFind_len_le
#assert_axioms merkleRecomputeZ_binds
#assert_axioms merkleOpening_binds_rom
#assert_axioms merkleOpening_floor_top_false_babyBear
#assert_axioms merkleOpening_floor_bot_vacuous
#assert_axioms commitmentOpening_binds_of_poseidon2CR
#assert_axioms opening_equivocation_breaks_cr
#assert_axioms honest_opening_binds
#assert_axioms constant_sponge_equivocates

end Dregg2.Circuit.OodCommitmentBinding
