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

Sub-obligation (b) is NOT algebra: it is a hash-binding fact.

⚑ **2026-07-28 — THE FLOOR IS GONE FROM THIS MODULE.** It used to reduce (b) to the named floor
`Poseidon2SpongeCR` (`= Function.Injective sponge` at `List ℤ → ℤ`), which
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` REFUTES at deployed parameters — so the theorem
the whole FRI/STARK tower consumes for its opening binding was a true implication whose hypothesis
nothing deployed satisfies. `merkleRecomputeZ_binds` and `commitmentOpening_binds_of_poseidon2CR` are
DELETED. What (b) actually needs is a PER-INSTANCE non-collision at the ONE pair the extractor
produces — `¬ OpeningColl` (§2) — and the deployed binding is `merkleOpening_binds_rom` (§3.1), which
carries NO floor hypothesis and rests on `KeyedRomFloor.keyedRom_hard`, the PROVED birthday bound.
`hood.b` is therefore a per-run side condition with both poles proved, plus a proved bound on how
often it fails — not a named assumption nothing satisfies.

## The reduction (a break ⟹ a Poseidon2 collision)

`TableOpening.constraintEval` is delivered to the verifier by a Poseidon2 Merkle opening: the opened
leaf (the field value) is recomputed up its sibling path (`FriVerifier.merkleRecompute`, the
`MerkleTreeMmcs` opening — each node hashes two child digests, order fixed by the index bit) and
compared to the committed root. We model the node hash as the ordered two-felt Poseidon2 sponge
`sponge [l, r]` — the EXACT binary specialization whose collision-resistance is `Poseidon2SpongeCR`,
identical to `AggAirSound.Hsponge`.

  * **`merkleFind` / `merkleFind_spec`** — the walking extractor and its UNCONDITIONAL correctness:
    two DISTINCT leaves recomputing the SAME root over the same path yield a genuine sponge collision,
    with no hypothesis. This is the whole content the deleted injectivity floor was hiding.
  * **`merkleRecomputeZ_binds_of_noColl` / `commitmentOpening_binds_of_noColl`** (THE `hood.b`
    REDUCTION) — an opened value `vOpened` and the honest committed value
    `vCommitted := (constraintPoly d t c).eval ζ` that BOTH recompute to the same committed root ARE
    EQUAL, given `¬ OpeningColl` at that ONE extracted pair. An adversary opening a DIFFERENT value
    hands over the collision itself (`opening_equivocation_exhibits_coll`, and hence
    `opening_equivocation_breaks_cr`: a break ⟹ `¬ Poseidon2SpongeCR`).

Anti-ghost, witnessed BOTH ways: on the injective toy sponge (`Poseidon2Binding.Reference.refSponge`,
CR-discharged) an honest opening BINDS (`honest_opening_binds`); on a NON-injective sponge
(constant-zero) an adversary equivocates two distinct values to the same root, and that equivocation
IS a witnessed collision (`constant_sponge_equivocates`). And `honest_run_needs_no_residual` proves
the side condition is FREE on every non-equivocating run, for every sponge — the port costs the
honest path nothing.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no refuted floor appears in any
statement here. Imported into `Dregg2.lean` (transitively, via
`StarkSoundFriLdt`/`AlgoStarkSoundTransferV3`, which CONSUME `commitmentOpening_binds_of_noColl` on
the deployed soundness path).

## Remaining wire to `OodInterpF.hood`

The standalone binding is proven green. To land it INTO `OodInterpF.hood` for the deployed verifier one
supplies three deployment-plumbing facts (the same "unmodeled commitment/column layout" residual the doc
names, NOT new crypto): (i) the committed root of the constraint-poly commitment and that
`verifyAlgo`'s accepted opening (`OodQuotientConsistency.verifyAlgo_accept_forces_table_identity` ties
`topen.constraintEval` to `A.mul vanishingAtZeta quotientAtZeta`) recomputes to it via `merkleRecomputeZ`;
(ii) the honest committed leaf equals `(constraintPoly d t c).eval ζ` cast to the leaf felt; (iii) the
BabyBear→ℤ canonical-representative bridge (the same one `FieldIntegerLift` carries). Given those,
`commitmentOpening_binds_of_noColl` yields `topen.constraintEval = (constraintPoly d t c).eval ζ` —
`hood.b`, now DERIVED from a per-run side condition whose failure probability `merkleOpening_binds_rom`
bounds on a PROVED floor.
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

/-! ### ⚑ THE PER-INSTANCE RESIDUAL — what the binding ACTUALLY needs.

`merkleRecomputeZ_binds` and `commitmentOpening_binds_of_poseidon2CR` are **DELETED** (2026-07-28).
Both took `Function.Injective sponge`, which at `List ℤ → ℤ` IS `Poseidon2SpongeCR` and is refuted by
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`. Neither ever inspected that hypothesis at more
than ONE argument: the proof applied it to `(merkleFind_spec …).2` — a single pair, produced by a
TOTAL CONSTRUCTIVE extractor, already known distinct with equal images. A global injectivity floor for
a one-pair obligation is the injectivity-floor disease in miniature.

What replaces it is that one pair, named: `OpeningColl` is the residual "the pair `merkleFind`
extracts from THIS opening really is a sponge collision", and the binding is stated on its negation.
Both poles are proved below — `openingColl_self_false` (dischargeable: a side condition that can never
be discharged is a broken keystone, not a repaired one) and `openingColl_of_constant_sponge`
(refutable: so `¬ OpeningColl` is not free) — and `openingColl_refutes_poseidon2CR` records that
holding the residual REFUTES the deleted floor, so the port is visibly a WEAKENING of the hypothesis
rather than a change of subject.

⚑ **The residual is PRICED, not merely named.** §3.1's `merkleOpening_binds_rom` bounds the
probability that a query-bounded prover produces exactly this event, on `KeyedRomFloor.keyedRom_hard`
— the birthday bound, PROVED, carrying no assumption. That is the honest shape of the deployed claim:
per run a side condition, and a proved bound on how often it fails. -/

/-- **`OpeningColl sponge idx l1 l2 siblings`** — the PER-INSTANCE residual. `merkleFind` walks the
shared sibling path carrying the two divergent accumulators and returns the first level at which they
agree; this says that returned pair is a genuine collision of the deployed sponge (two DISTINCT node
preimages with EQUAL images). It is the exact event `merkleFind_spec` produces from an equivocated
opening, and nothing wider. -/
def OpeningColl (sponge : List ℤ → ℤ) (idx : Nat) (l1 l2 : ℤ) (siblings : List ℤ) : Prop :=
  (merkleFind sponge idx l1 l2 siblings).1 ≠ (merkleFind sponge idx l1 l2 siblings).2
    ∧ sponge (merkleFind sponge idx l1 l2 siblings).1
        = sponge (merkleFind sponge idx l1 l2 siblings).2

/-- At a single leaf the extractor returns a pair of EQUAL preimages: either the empty fallback, or
the same node twice. -/
theorem merkleFind_self (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l : ℤ),
      (merkleFind sponge idx l l siblings).1 = (merkleFind sponge idx l l siblings).2 := by
  intro siblings idx l
  cases siblings with
  | nil => simp [merkleFind]
  | cons s rest => simp [merkleFind]

/-- **(POLE — the residual is DISCHARGEABLE.)** An opening that does not equivocate has nothing to
collide, so `¬ OpeningColl` holds outright, with no hypothesis about the sponge. A side condition that
can never be discharged would be a broken keystone rather than a repaired one; this is the proof it is
not one, and it is what makes an honest prover's run FREE of the residual. -/
theorem openingColl_self_false (sponge : List ℤ → ℤ) (idx : Nat) (l : ℤ) (siblings : List ℤ) :
    ¬ OpeningColl sponge idx l l siblings :=
  fun h => h.1 (merkleFind_self sponge siblings idx l)

/-- **(POLE — the residual is REFUTABLE.)** On a sponge that collapses everything to one value, two
DISTINCT leaves over a one-level path DO make the extractor return a genuine collision. So
`¬ OpeningColl` is not free: it is a real hypothesis about the deployed hash at this opening. -/
theorem openingColl_of_constant_sponge (c s : ℤ) {l1 l2 : ℤ} (hne : l1 ≠ l2) :
    OpeningColl (fun _ => c) 0 l1 l2 [s] := by
  have hfind : merkleFind (fun _ => c) 0 l1 l2 [s] = ([l1, s], [l2, s]) := by
    simp [merkleFind, nodeStep]
  unfold OpeningColl
  rw [hfind]
  exact ⟨by simp [hne], rfl⟩

/-- **THE PORT IS A WEAKENING, NOT A CHANGE OF SUBJECT.** The residual holding at ANY opening REFUTES
the deleted floor — equivalently, the deleted `Poseidon2SpongeCR sponge` implied `¬ OpeningColl` at
every instance. So every consumer that used to buy its binding with the global floor can still buy it,
and the new hypothesis is strictly weaker. (Stated in the ¬-direction deliberately: this is anti-floor
content, and assumes no floor.) -/
theorem openingColl_refutes_poseidon2CR (sponge : List ℤ → ℤ) (idx : Nat) (l1 l2 : ℤ)
    (siblings : List ℤ) (h : OpeningColl sponge idx l1 l2 siblings) :
    ¬ Poseidon2SpongeCR sponge := fun hCR => h.1 (hCR _ _ h.2)

/-- **THE MERKLE BINDING, FLOOR-FREE.** Two leaves that recompute the SAME root at the same index over
the same sibling path are EQUAL, provided the ONE pair `merkleFind` extracts from them is not a
collision. No injectivity, no named floor, and — unlike the theorem it replaces — a statement that is
not vacuous at deployed BabyBear parameters. -/
theorem merkleRecomputeZ_binds_of_noColl (sponge : List ℤ → ℤ)
    (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ)
    (hno : ¬ OpeningColl sponge idx l1 l2 siblings)
    (h : merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings) :
    l1 = l2 := by
  by_contra hne
  exact hno (merkleFind_spec sponge siblings idx l1 l2 hne h)

/-! ## §3 — THE `hood.b` REDUCTION: the opened value is BOUND to the committed polynomial. -/

/-- **`commitmentOpening_binds_of_noColl` (THE `hood.b` REDUCTION, FLOOR-FREE).** The value
`verifyAlgo` opens at ζ (`vOpened`, the `TableOpening.constraintEval`) and the honest committed value
`vCommitted` (intended `(constraintPoly d t c).eval ζ`) that BOTH recompute to the same committed
Merkle root `root` at the same query index over the same sibling path ARE EQUAL — provided the ONE
pair the extractor produces from them is not a sponge collision. So the opened `constraintEval` is
BOUND to the committed polynomial's evaluation at ζ, on a PER-RUN side condition with both poles
proved, and no refuted hypothesis anywhere. This is `hood.b` DERIVED, not re-assumed. -/
theorem commitmentOpening_binds_of_noColl (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hno : ¬ OpeningColl sponge idx vOpened vCommitted siblings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    vOpened = vCommitted :=
  merkleRecomputeZ_binds_of_noColl sponge siblings idx vOpened vCommitted hno
    (hOpened.trans hCommitted.symm)

/-- **A BREAK EXHIBITS THE COLLISION** — the converse direction, and floor-free. A prover that opens
one committed root at one query to two DIFFERENT values hands over the collision itself, at the exact
pair the extractor names. This is what makes `¬ OpeningColl` the right side condition: it is
equivalent to the binding at this opening, not merely sufficient for it. -/
theorem opening_equivocation_exhibits_coll (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    OpeningColl sponge idx vOpened vCommitted siblings := by
  by_contra hno
  exact hne (commitmentOpening_binds_of_noColl sponge hno hCommitted hOpened)

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
So `hood.b` bottoms out at the hash floor and nothing weaker. Anti-floor content: it CONCLUDES the
negation and assumes no floor, and its proof now routes through the floor-free extractor. -/
theorem opening_equivocation_breaks_cr (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    ¬ Poseidon2SpongeCR sponge :=
  openingColl_refutes_poseidon2CR sponge idx vOpened vCommitted siblings
    (opening_equivocation_exhibits_coll sponge hne hCommitted hOpened)

/-! ## §4 — NON-VACUITY: honest openings BIND, and the CR floor is LOAD-BEARING.

The reduction would be hollow if no opening ever bound, or if it bound even without CR. We exhibit BOTH:
on the injective toy sponge (`Poseidon2Binding.Reference.refSponge`, CR-discharged) an honest opening
binds; on a NON-injective sponge (constant-zero) an adversary equivocates two DISTINCT values to the
same root — a witnessed collision showing the `Poseidon2SpongeCR` hypothesis is genuinely required. -/

section Vacuity

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- **`honest_opening_binds` (POSITIVE non-vacuity).** On the injective toy sponge whose CR is proved
(`refSponge_CR`), any two openings to a common root over the same path bind — the reduction FIRES on a
concrete instance where the residual is discharged, so `commitmentOpening_binds_of_noColl` is not
vacuous. The discharge is by `refSponge_CR`, kept in the PROOF where it is a fact about a concrete toy
object, rather than in the STATEMENT where it would be a floor. -/
theorem honest_opening_binds
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ refSponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ refSponge idx vOpened    siblings = root) :
    vOpened = vCommitted :=
  commitmentOpening_binds_of_noColl refSponge (fun h => h.1 (refSponge_CR _ _ h.2))
    hCommitted hOpened

/-- **`honest_run_needs_no_residual` (TOTAL re-inhabitation).** An honest prover — one that opens the
value it committed — discharges the side condition for EVERY sponge, EVERY index and EVERY path, with
no hypothesis at all. So routing the tower off the refuted floor onto `¬ OpeningColl` costs the honest
path nothing: what was bought with a false global assumption is now free on every non-equivocating
run, and is a real assumption exactly on the runs that equivocate. -/
theorem honest_run_needs_no_residual (sponge : List ℤ → ℤ) (idx : Nat) (v : ℤ)
    (siblings : List ℤ) : ¬ OpeningColl sponge idx v v siblings :=
  openingColl_self_false sponge idx v siblings

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
#assert_axioms merkleFind_self
#assert_axioms openingColl_self_false
#assert_axioms openingColl_of_constant_sponge
#assert_axioms openingColl_refutes_poseidon2CR
#assert_axioms merkleRecomputeZ_binds_of_noColl
#assert_axioms merkleOpening_binds_rom
#assert_axioms merkleOpening_floor_top_false_babyBear
#assert_axioms merkleOpening_floor_bot_vacuous
#assert_axioms commitmentOpening_binds_of_noColl
#assert_axioms opening_equivocation_exhibits_coll
#assert_axioms opening_equivocation_breaks_cr
#assert_axioms honest_opening_binds
#assert_axioms honest_run_needs_no_residual
#assert_axioms constant_sponge_equivocates

end Dregg2.Circuit.OodCommitmentBinding
