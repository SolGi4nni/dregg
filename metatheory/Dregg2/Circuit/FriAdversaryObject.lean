/-
# `Dregg2.Circuit.FriAdversaryObject` — the FRI PROVER STRATEGY as a typed object, its
Fiat–Shamir transform as an `OracleComp`, and the fold-chain farness propagation (proven).

Design lane D1 (docs/DESIGN-fri-adversary-object.md). The FRI-soundness record's program step (1)
is "build a real protocol/adversary object — prover strategy, rounds, the Fiat–Shamir transform —
so there is something for an adversary to BE." This module is that object, at the resolution the
current tree supports:

  * **§1 `Strategy R C`** — a FRI prover strategy IS the next-round commitment as a function of
    the FS challenges so far (round index = prefix length). The honest prover inhabits the type
    (`honestStrategy`: fold a fixed initial word), and NOTHING constrains a cheating strategy —
    it may commit anything at any round. This is the object the deterministic
    `FriLdtExtractV3` never had: a thing whose success can be an event.
  * **§2 the FS TRANSFORM** — `fsRun enc S n cs` runs `n` rounds against a random oracle: each
    round QUERIES the oracle at the encoded transcript prefix (which pins the commitment the
    challenge must be good for — the point `enc (S cs) cs` carries `S cs`) and continues with the
    answer as the round's challenge. Three theorems, all proven:
      - `fsRun_queryBounded` — the transform is a `QueryBounded n` tree: FS challenges ARE ROM
        queries, one per round, and the budget is the round count. This is what plugs the strategy
        into the banked per-query machinery (`hit_cond`, `birthday_cond`, the query-log substrate).
      - `fsRun_eval` — FAITHFULNESS: running the oracle tree against a FIXED oracle recovers the
        deterministic chain `fsChain` — the strategy-level echo of `verifyAlgoO_run_eq`. The
        deployed derandomized FS is the `eval` image of this object; the re-basing is conservative.
      - `fsChain_length` — `n` rounds produce exactly `n` challenges (the transcript is real).
  * **§3 the FOLD-CHAIN, and farness propagation** — `ChainStep far goodSet fold` is the TYPED
    per-round obligation ("a far word folded at a challenge outside its good set stays far"); it
    is deliberately a `def`, NOT proven here — its instances at the deployed radius are ladder
    stage L2 (UD radius: engineering on `FriFoldArity`; Johnson radius: the named carrier, where
    `M = 1` is a REFUTED theorem — `FriJohnsonRadiusGap.deployed_M1_false_at_johnson`).
    `honest_chain_far` is the PROVEN easy half: under `ChainStep`, if the initial word is far and
    every round's challenge avoids its own point's bad set (`AvoidsBad`), the terminal word is
    far. `chainStep_is_load_bearing` is the mutation canary (drop `ChainStep` and the conclusion
    is FALSE at a witness); `honest_chain_far_fires` is the positive pole.

## ⚑ What this module does NOT do, stated so it cannot be read up

  * No probability bound is proven here. The failure probability of `AvoidsBad` is EXACTLY what
    `FriVerifierCompose.hit_cond` prices (`≤ n·b/|R|` for `b`-capped bad sets), via
    `fsRun_queryBounded`; the two-line corollary
    `winProb (¬ far terminal) ≤ n·b/|R|` is deliberately NOT landed here because
    `FriVerifierCompose`'s import closure is RED at HEAD (`SpongeForgeReduction.lean:324,329`
    references `effFloor_top_false_babyBear`/`effFloor_bot_vacuous` without importing
    `DomainSeparatedCREffRegrounded` — an unpropagated regrounding rename, independently found by
    the concurrent `DeployedProximitySoundnessSampler` lane). This module imports ONLY the green
    `RomOracle` substrate; the connection corollary is ladder stage L2's first item once the
    upstream repair lands.
  * `Strategy` does not model the query phase (the Merkle-opened leaves). That is the extraction
    substrate's job (`RomQueryLog` + `FriVerifierMerkle.findCollisionZ` — state-as-data, nothing
    to falsify), and the committed-word-from-query-log definition is ladder stage L4.
  * Nothing here discharges `FriLdtExtractV3` or moves any deployed statement. ADDITIVE only.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. Imports: `RomOracle` (green closure verified at HEAD) only.
-/
import Dregg2.Crypto.RomOracle
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false

namespace Dregg2.Circuit.FriAdversaryObject

open Dregg2.Crypto.RomOracle

/-! ## §1 — THE STRATEGY TYPE: something for an adversary to BE. -/

/-- **A FRI prover strategy.** The next-round commitment as a function of the FS challenges so
far; the round index is the length of the prefix (challenges newest-first). `C` is the per-round
commitment type (a Merkle cap over the round's committed word; the final round's value doubles as
the final-polynomial claim). A CHEATING strategy is any inhabitant — nothing ties `S cs` to a fold
of `S cs.tail`; that tie is exactly what the verifier's spot checks must enforce, and what the
discharge ladder prices. -/
def Strategy (R C : Type) : Type := List R → C

/-- **The honest prover inhabits the type**: commit the repeated fold of a fixed initial word
`w0` along the challenge prefix. `foldr` because prefixes are newest-first: the OLDEST challenge
is applied first. -/
def honestStrategy {R C : Type} (fold : C → R → C) (w0 : C) : Strategy R C :=
  fun cs => cs.foldr (fun r w => fold w r) w0

@[simp] theorem honestStrategy_nil {R C : Type} (fold : C → R → C) (w0 : C) :
    honestStrategy fold w0 [] = w0 := rfl

@[simp] theorem honestStrategy_cons {R C : Type} (fold : C → R → C) (w0 : C) (r : R)
    (cs : List R) :
    honestStrategy fold w0 (r :: cs) = fold (honestStrategy fold w0 cs) r := rfl

/-! ## §2 — THE FIAT–SHAMIR TRANSFORM: rounds as ROM queries. -/

/-- **The FS transform of a strategy** — an `OracleComp` that runs `n` rounds: each round queries
the random oracle at `enc (S cs) cs` (the encoded post-commitment transcript prefix — the point
CARRIES the commitment the challenge must be good for, which is what makes per-point bad sets
`E : D → Finset R` the right pricing shape) and continues with the oracle's answer as the round's
challenge. Returns the full challenge list, newest-first. -/
def fsRun {R C D : Type} (enc : C → List R → D) (S : Strategy R C) :
    ℕ → List R → OracleComp D R (List R)
  | 0, cs => .pure cs
  | n + 1, cs => .query (enc (S cs) cs) (fun c => fsRun enc S n (c :: cs))

/-- **FS challenges ARE ROM queries, one per round.** The transform is a syntactically
`QueryBounded n` tree — the budget the whole banked per-query machinery (`hit_cond`,
`birthday_cond`, `RomQueryLog`) consumes. -/
theorem fsRun_queryBounded {R C D : Type} (enc : C → List R → D) (S : Strategy R C) :
    ∀ (n : ℕ) (cs : List R), QueryBounded n (fsRun enc S n cs)
  | 0, cs => QueryBounded.pure 0 cs
  | n + 1, cs =>
      QueryBounded.query n _ _ (fun c => fsRun_queryBounded enc S n (c :: cs))

/-- **The deterministic FS chain** — the transcript the strategy produces against a FIXED oracle
`H`. This is the derandomized object the deployed `deriveTranscript` computes. -/
def fsChain {R C D : Type} (enc : C → List R → D) (S : Strategy R C) (H : D → R) :
    ℕ → List R → List R
  | 0, cs => cs
  | n + 1, cs => fsChain enc S H n (H (enc (S cs) cs) :: cs)

/-- **⚑ FAITHFULNESS** — running the FS transform against a fixed oracle recovers the
deterministic chain. The strategy-level echo of `FriVerifierO.verifyAlgoO_run_eq`: the ROM
re-basing of the prover is CONSERVATIVE — the deployed derandomized transcript is the `eval`
image of the oracle object, so nothing about the deployed FS is changed by giving the prover an
adversary type. -/
theorem fsRun_eval {R C D : Type} (enc : C → List R → D) (S : Strategy R C) (H : D → R) :
    ∀ (n : ℕ) (cs : List R), (fsRun enc S n cs).eval H = fsChain enc S H n cs := by
  intro n
  induction n with
  | zero => intro cs; rfl
  | succ n ih =>
      intro cs
      simpa [fsRun, fsChain, OracleComp.eval] using ih (H (enc (S cs) cs) :: cs)

/-- The chain is real: `n` rounds append exactly `n` challenges. -/
theorem fsChain_length {R C D : Type} (enc : C → List R → D) (S : Strategy R C) (H : D → R) :
    ∀ (n : ℕ) (cs : List R), (fsChain enc S H n cs).length = n + cs.length := by
  intro n
  induction n with
  | zero => intro cs; simp [fsChain]
  | succ n ih =>
      intro cs
      simp only [fsChain, ih, List.length_cons]
      omega

/-- **The query log of the FS run is the transcript.** Under any oracle, the points `fsRun`
queries are exactly the encoded prefixes `fsChain` passes through, in round order — so the
query-log substrate (`RomQueryLog`) sees the WHOLE transcript of every strategy, which is what a
straight-line (no-rewinding) extractor reads. -/
theorem fsRun_queried {R C D : Type} (enc : C → List R → D) (S : Strategy R C) (H : D → R) :
    ∀ (n : ℕ) (cs : List R),
      (fsRun enc S n cs).queried H
        = (List.range n).map
            (fun i => enc (S (fsChain enc S H i cs)) (fsChain enc S H i cs)) := by
  intro n
  induction n with
  | zero => intro cs; simp [fsRun, OracleComp.queried]
  | succ n ih =>
      intro cs
      rw [List.range_succ_eq_map]
      simp only [fsRun, OracleComp.queried, ih (H (enc (S cs) cs) :: cs), List.map_cons,
        List.map_map]
      rfl

/-! ## §3 — THE FOLD CHAIN: the typed per-round obligation, and farness propagation (proven). -/

/-- **`ChainStep` — the per-round distance-preservation obligation, TYPED.** "A far word folded
at a challenge outside its good set stays far." Deliberately a `def`, not a theorem: its
instances are ladder stage L2. At the unique-decoding radius the instance is engineering over
`FriFoldArity` (the `goodSet` cardinality is what `FriLedgerSound.ledger_perFold_soundness`'s
`goodCount`/`perFoldBits` bound); at the Johnson radius the `M = 1` route is REFUTED
(`FriJohnsonRadiusGap.deployed_M1_false_at_johnson`) and the honest instance is the `M ≤ 7`
count (`arity8_johnson_good_card_le`) under the named correlated-agreement carrier. Supplying a
`ChainStep` instance IS the per-fold column attaching to the adversary object. -/
def ChainStep {R C : Type} (far : C → Prop) (goodSet : C → Finset R) (fold : C → R → C) : Prop :=
  ∀ (w : C) (r : R), far w → r ∉ goodSet w → far (fold w r)

/-- **`AvoidsBad` — the transcript-avoidance event**: every round's drawn challenge avoids the
bad set of its own query point. This is the complement, specialized to `fsRun`, of
`FriVerifierCompose.hitWin` — and `hit_cond` prices its failure at `≤ n·b/|R|` for `b`-capped
`E`, via `fsRun_queryBounded`. (The corollary is deferred: that import closure is red at HEAD —
see the module header. Nothing here re-derives it.) -/
def AvoidsBad {R C D : Type} (enc : C → List R → D) (S : Strategy R C) (E : D → Finset R)
    (H : D → R) : ℕ → List R → Prop
  | 0, _ => True
  | n + 1, cs =>
      H (enc (S cs) cs) ∉ E (enc (S cs) cs)
        ∧ AvoidsBad enc S E H n (H (enc (S cs) cs) :: cs)

/-- **⚑ FAR SURVIVES THE WHOLE FOLD CHAIN** (the proven easy half of the round-chain argument).
For the honest-FOLD word evolution — which is the evolution the verifier's fold-consistency
checks force on pain of a caught inconsistency, the OTHER branch of the L2 dichotomy — under
`ChainStep`, if the current word is far and every remaining round's challenge avoids its point's
bad set (which COVERS the word's good set, `hcover`), then the terminal word is still far.

Combined with the (deferred) `hit_cond` corollary this is the round-chain shape of `εFri`'s query
leg: except with probability `≤ rounds·b/|R|`, a far word is STILL far at the terminal round,
where the spot-check bound (`FriQuerySoundness.accept_prob_le`) finishes the argument. -/
theorem honest_chain_far {R C D : Type} {far : C → Prop} {goodSet : C → Finset R}
    {fold : C → R → C} (hstep : ChainStep far goodSet fold)
    (enc : C → List R → D) (E : D → Finset R) (w0 : C)
    (hcover : ∀ (w : C) (cs : List R), goodSet w ⊆ E (enc w cs))
    (H : D → R) :
    ∀ (n : ℕ) (cs : List R),
      far (honestStrategy fold w0 cs) →
      AvoidsBad enc (honestStrategy fold w0) E H n cs →
      far (honestStrategy fold w0 (fsChain enc (honestStrategy fold w0) H n cs)) := by
  intro n
  induction n with
  | zero =>
      intro cs hfar _
      simpa [fsChain] using hfar
  | succ n ih =>
      intro cs hfar havoid
      simp only [AvoidsBad] at havoid
      obtain ⟨hnotE, htail⟩ := havoid
      have hnotGood :
          H (enc (honestStrategy fold w0 cs) cs) ∉ goodSet (honestStrategy fold w0 cs) :=
        fun hmem => hnotE (hcover _ _ hmem)
      have hfar' :
          far (honestStrategy fold w0 (H (enc (honestStrategy fold w0 cs) cs) :: cs)) := by
        simpa using hstep _ _ hfar hnotGood
      simpa [fsChain] using ih (H (enc (honestStrategy fold w0 cs) cs) :: cs) hfar' htail

/-! ### §3.1 — teeth: the hypothesis is load-bearing, and the theorem fires. -/

/-- **CANARY — `ChainStep` is LOAD-BEARING.** Drop it and `honest_chain_far`'s conclusion is
FALSE at a witness: a fold that ruins farness (`w ↦ w + 1` against `far = (· = 0)`) with empty
bad sets satisfies every other hypothesis (`AvoidsBad` trivially, `hcover` trivially, `far w0`)
and the terminal word is NOT far. So the theorem cannot be weakened to discard its per-round
obligation — the per-fold column is genuinely what the chain stands on. -/
theorem chainStep_is_load_bearing :
    ∃ (far : ℕ → Prop) (goodSet : ℕ → Finset Bool) (fold : ℕ → Bool → ℕ)
      (enc : ℕ → List Bool → Unit) (E : Unit → Finset Bool) (w0 : ℕ) (H : Unit → Bool),
      (∀ w cs, goodSet w ⊆ E (enc w cs)) ∧
      far w0 ∧
      AvoidsBad enc (honestStrategy fold w0) E H 1 [] ∧
      ¬ far (honestStrategy fold w0 (fsChain enc (honestStrategy fold w0) H 1 [])) := by
  refine ⟨(· = 0), fun _ => ∅, fun w _ => w + 1, fun _ _ => (), fun _ => ∅, 0,
    fun _ => true, ?_, rfl, ?_, ?_⟩
  · intro w cs
    simp
  · simp [AvoidsBad]
  · simp [fsChain, honestStrategy]

/-- **POSITIVE POLE — the theorem FIRES on a genuine `ChainStep` instance.** `far = (1 ≤ ·)`
with `fold = (· + 1)` satisfies `ChainStep` outright (adding never un-fars), and the chain
conclusion holds at 2 rounds from `w0 = 1`. Non-vacuity of the whole §3 shape. -/
theorem honest_chain_far_fires :
    (1 : ℕ) ≤ honestStrategy (fun w (_ : Bool) => w + 1) 1
      (fsChain (fun _ _ => ()) (honestStrategy (fun w (_ : Bool) => w + 1) 1)
        (fun _ => true) 2 []) := by
  refine honest_chain_far (far := (1 ≤ ·)) (goodSet := fun _ => ∅)
    (fold := fun w (_ : Bool) => w + 1)
    (fun w r hw _ => Nat.le_succ_of_le hw)
    (fun _ _ => ()) (fun _ => ∅) 1 (fun w cs => by simp) (fun _ => true) 2 [] ?_ ?_
  · exact le_refl 1
  · simp [AvoidsBad]

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  honestStrategy_nil,
  honestStrategy_cons,
  fsRun_queryBounded,
  fsRun_eval,
  fsChain_length,
  fsRun_queried,
  honest_chain_far,
  chainStep_is_load_bearing,
  honest_chain_far_fires
]

end Dregg2.Circuit.FriAdversaryObject
