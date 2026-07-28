/-
# Dregg2.Circuit.BindingAirSound — the `TurnChainBindingAir` soundness, PROVEN not assumed.

**What this is.** `RecursiveAggregation.EngineSound.binding_sound` (`RecursiveAggregation.lean:139`)
is a NAMED hypothesis: it asserts that a verifying `TurnChainBindingAir` leaf delivers the temporal
ordering tooth `ChainBound` over the whole chain AND pins the public genesis/final roots. That field
was carried as a *boundary* — the in-circuit soundness of the chain-binding AIR. The AIR census flagged
it as a SMALL, ISOLATED proof: the binding AIR's constraints are simple enough to model denotationally
and discharge in Lean, resting only on the standard Poseidon2 collision-resistance floor.

This file does that. It models the per-row constraints of the Rust `TurnChainBindingAir`
(`circuit-prove/src/ivc_turn_chain.rs::TurnChainBindingAir::eval`) as a denotational predicate
`Satisfies` over a list of rows + the four public inputs `[genesis, final, num_turns, chain_digest]`,
and proves:

  * **`binding_air_discharges_binding_sound` (THE KEYSTONE).** A satisfying binding-AIR trace whose
    rows expose the chain steps' commitment roots (`Represents`) FORCES the exact `binding_sound`
    conclusion — `ChainBound` (the ordered continuity `new_root[i] == old_root[i+1]`), the genesis pin
    (head old_root = the public genesis), and the final pin (public final = `foldedFinalRoot`). This is
    a pure reading of the AIR's continuity + boundary constraints — it needs NO crypto assumption at
    all, so the ordering guarantee a light client gets is PROVED, strictly stronger than assumed.

  * **`digest_binds_ordered_history` (THE CR FLOOR).** Under `Poseidon2SpongeCR` (the single named hash
    floor, never an axiom), two satisfying traces that publish the SAME `chain_digest` and the same
    `num_turns` have the SAME ordered `(old_root, new_root, idx)` sequence — the digest binds the whole
    ordered history, so a same-endpoint reorder is rejected by the digest. This is the only result that
    rests on the hash floor, and it rests on it ALONE.

Non-vacuity is witnessed BOTH ways: a concrete honest trace satisfies (`satisfies_two`) and the
keystone fires on a real chain step (`keystone_fires`); a reordered trace whose continuity is broken
does NOT satisfy (`reordered_not_satisfies`), so the constraints are genuinely falsifiable.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `Poseidon2SpongeCR` is a Prop
HYPOTHESIS where used, never an `axiom`. Imported into `Dregg2.lean` (in the trusted, axiom-audited closure).
-/
import Dregg2.Distributed.HistoryAggregation
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.BindingAirSound

open Dregg2.Distributed.HistoryAggregation
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecChainedState)

/-! ## 1. The denotational model of one `TurnChainBindingAir` row + the public inputs.

The Rust AIR carries per row `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]` plus the
Poseidon2 permutation aux block. The acc columns + the per-row hash gate are internal witnesses whose
NET effect is a running ordered digest; we model that effect directly as the fold `histDigest` below, so
a row's load-bearing exposed content is its `(old_root, new_root, idx)`. -/

/-- One binding-AIR row's load-bearing content: the pre/post state-commitment roots it binds and its
positional index `idx` (the AIR's `COL_OLD_ROOT`/`COL_NEW_ROOT`/`COL_IDX`). -/
structure BindingRow where
  oldRoot : ℤ
  newRoot : ℤ
  idx     : ℤ

/-- The four public inputs of the binding AIR: `[genesis_root, final_root, num_turns, chain_digest]`
(`TurnChainBindingAir::num_public_values = 4`). -/
structure BindingPublic where
  genesis     : ℤ
  final       : ℤ
  numTurns    : Nat
  chainDigest : ℤ

/-- The `(old_root, new_root, idx)` projection of a row — the ordered datum the digest commits to. -/
def proj (r : BindingRow) : ℤ × ℤ × ℤ := (r.oldRoot, r.newRoot, r.idx)

/-! ## 2. The constraint predicates (the Lean twins of `TurnChainBindingAir::eval`). -/

/-- **`RowBound`** — the temporal-tooth (continuity) constraint: each row's `new_root` is the next
row's `old_root` (Rust constraint 1, `builder.when_transition().assert_zero(new_root - next_old_root)`).
Defined with the SAME 2-lookahead recursion as `HistoryAggregation.ChainBound` so the two align. -/
def RowBound : List BindingRow → Prop
  | []            => True
  | [_]           => True
  | r :: r' :: rest => r.newRoot = r'.oldRoot ∧ RowBound (r' :: rest)

/-- **`histDigest hash acc rows`** — the genuine running ordered-history digest the AIR's digest gates
(Rust constraints 4 + 5) compute: a left fold that absorbs each row's `(old, new, idx)` into the
running `acc` via the Poseidon2 `hash_4_to_1` of `[acc, old, new, idx]`, starting from `acc_in = 0` on
the first row. `chain_digest` (the last row's `acc_out`) is exactly `histDigest hash 0 rows`. -/
def histDigest (hash : List ℤ → ℤ) (acc : ℤ) : List BindingRow → ℤ
  | []          => acc
  | r :: rest => histDigest hash (hash [acc, r.oldRoot, r.newRoot, r.idx]) rest

/-- **`Satisfies hash rows pub`** — a denotational satisfying binding-AIR trace: the rows + public
inputs meet the AIR's constraints. The fields are the Rust constraints:
  * `nonempty` — a folded chain has at least one row;
  * `continuity` (C1) — the temporal tooth `RowBound`;
  * `genesis` (C2) — first row `old_root == genesis_root`;
  * `final` (C3) — last row `new_root == final_root`;
  * `digestEq` (C4 + C5) — the public `chain_digest` is the genuine running digest `histDigest hash 0`
    of the ordered rows (the unrolled digest-chain + per-row Poseidon2 hash gates);
  * `count` (C7) — the public `num_turns` is the count of (all-real) rows. -/
structure Satisfies (hash : List ℤ → ℤ) (rows : List BindingRow) (pub : BindingPublic) : Prop where
  nonempty   : rows ≠ []
  continuity : RowBound rows
  genesis    : ∀ r, rows.head? = some r → r.oldRoot = pub.genesis
  final      : ∀ r, rows.getLast? = some r → r.newRoot = pub.final
  digestEq   : pub.chainDigest = histDigest hash 0 rows
  count      : pub.numTurns = rows.length

/-! ## 3. The modeling bridge — a trace's rows EXPOSE the chain steps' commitment roots.

A `TurnChainBindingAir` leaf over a sequence of finalized turns has, at row `i`, exactly the `i`-th
turn's rotated `(OLD_COMMIT, NEW_COMMIT)` — which are the `ChainStep`'s `oldRoot`/`newRoot` (the §8
state commitments). `Represents` is that positional correspondence, the honest reading of what the
binding leaf's rows ARE. -/

section Portal

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`Represents rows steps`** — positional: each row's `old_root`/`new_root` ARE the paired
`ChainStep`'s genuine commitment roots. (Same length, same order — the leaf is bound to its turns.) -/
def Represents : List BindingRow → List ChainStep → Prop
  | [], []                  => True
  | r :: rows, s :: steps =>
      (r.oldRoot = ChainStep.oldRoot CH RH cmb compress compressN s
        ∧ r.newRoot = ChainStep.newRoot CH RH cmb compress compressN s)
      ∧ Represents rows steps
  | _, _                    => False

/-- A represented trace is nonempty iff its step list is. -/
theorem represents_steps_ne_nil {rows : List BindingRow} {steps : List ChainStep}
    (hrep : Represents CH RH cmb compress compressN rows steps) (hne : rows ≠ []) : steps ≠ [] := by
  cases rows with
  | nil => exact absurd rfl hne
  | cons r rest =>
    cases steps with
    | nil => simp [Represents] at hrep
    | cons s ss => exact List.cons_ne_nil s ss

/-- The last row of a represented trace is paired with the last step. -/
theorem represents_getLast (rows : List BindingRow) (steps : List ChainStep)
    (hrep : Represents CH RH cmb compress compressN rows steps) :
    ∀ r, rows.getLast? = some r →
      ∃ s, steps.getLast? = some s
        ∧ r.oldRoot = ChainStep.oldRoot CH RH cmb compress compressN s
        ∧ r.newRoot = ChainStep.newRoot CH RH cmb compress compressN s := by
  induction rows generalizing steps with
  | nil => intro r hr; simp at hr
  | cons a rest ih =>
    cases steps with
    | nil => simp [Represents] at hrep
    | cons s ss =>
      obtain ⟨hpair, htail⟩ := hrep
      intro r hr
      cases rest with
      | nil =>
        cases ss with
        | nil =>
          rw [List.getLast?_singleton] at hr
          cases hr
          exact ⟨s, by simp, hpair.1, hpair.2⟩
        | cons s' ss' => simp [Represents] at htail
      | cons b rest' =>
        cases ss with
        | nil => simp [Represents] at htail
        | cons s' ss' =>
          rw [List.getLast?_cons_cons] at hr
          obtain ⟨t, ht, ho, hn⟩ := ih (s' :: ss') htail r hr
          exact ⟨t, by rw [List.getLast?_cons_cons]; exact ht, ho, hn⟩

/-- **`represents_length`** — a represented trace has EXACTLY as many rows as the chain has steps.
Purely structural (`Represents` is a positional zip that is `False` on a length mismatch), and it is
what carries the AIR's published `num_turns` onto the chain: `Satisfies.count` says the public count
is the ROW count, this says the row count is the STEP count. No cryptographic assumption. -/
theorem represents_length :
    ∀ (rows : List BindingRow) (steps : List ChainStep),
      Represents CH RH cmb compress compressN rows steps → rows.length = steps.length := by
  intro rows
  induction rows with
  | nil =>
    intro steps hrep
    cases steps with
    | nil => rfl
    | cons s ss => simp [Represents] at hrep
  | cons r rest ih =>
    intro steps hrep
    cases steps with
    | nil => simp [Represents] at hrep
    | cons s ss => simpa using ih ss hrep.2

/-- **`rowbound_represents_chainbound`** — the temporal tooth on the rows transfers to the steps: a
`RowBound` represented trace forces `HistoryAggregation.ChainBound` over the steps (the `binding_sound`
ordering conclusion). Induction matching `ChainBound`'s own 2-lookahead recursion. -/
theorem rowbound_represents_chainbound :
    ∀ (rows : List BindingRow) (steps : List ChainStep),
      Represents CH RH cmb compress compressN rows steps → RowBound rows →
      ChainBound CH RH cmb compress compressN steps := by
  intro rows
  induction rows with
  | nil =>
    intro steps hrep _
    cases steps with
    | nil => trivial
    | cons s ss => simp [Represents] at hrep
  | cons r rest ih =>
    intro steps hrep hbound
    cases steps with
    | nil => simp [Represents] at hrep
    | cons s ss =>
      obtain ⟨hp0, htail⟩ := hrep
      cases rest with
      | nil =>
        cases ss with
        | nil => trivial
        | cons s' ss' => simp [Represents] at htail
      | cons r' rest' =>
        cases ss with
        | nil => simp [Represents] at htail
        | cons s' ss' =>
          obtain ⟨hcont, hbtail⟩ := hbound
          have hp1 := htail.1
          refine ⟨?_, ?_⟩
          · show ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s'
            rw [← hp0.2, hcont, hp1.1]
          · exact ih (s' :: ss') htail hbtail

/-- The genuine final root of a nonempty chain is the last step's `new_root` (purely structural). -/
theorem foldedFinalRoot_eq_lastNew (g : RecChainedState) (steps : List ChainStep) (last : ChainStep)
    (h : steps.getLast? = some last) :
    foldedFinalRoot CH RH cmb compress compressN g steps
      = ChainStep.newRoot CH RH cmb compress compressN last := by
  have hls : lastStateOf g steps = last.post := by
    induction steps generalizing g with
    | nil => simp at h
    | cons a rest ih =>
      cases rest with
      | nil =>
        rw [List.getLast?_singleton] at h; cases h; rfl
      | cons b rest' =>
        have h' : (b :: rest').getLast? = some last := by rwa [List.getLast?_cons_cons] at h
        simpa [lastStateOf] using ih a.post h'
  unfold foldedFinalRoot
  rw [h]
  simp only [hls, ChainStep.newRoot]

/-! ## 4. THE KEYSTONE — `binding_sound` discharged as a theorem (no crypto). -/

/-- **`binding_air_discharges_binding_sound` (THE KEYSTONE).** A satisfying binding-AIR trace whose
rows expose the chain steps' commitment roots discharges EXACTLY the
`RecursiveAggregation.EngineSound.binding_sound` obligation: the temporal ordering tooth `ChainBound`
holds over the whole chain, the public `genesis` is the chain's first `old_root`, the public `final`
is the genuine `foldedFinalRoot`, and the public `num_turns` IS the chain's step count. This rests on
NO cryptographic assumption — the ordering tooth + boundary pins + the count are forced by the AIR's
continuity / first-row / last-row / real-count constraints alone, so the light client's ordering
guarantee is PROVED, not assumed.

**[2026-07-28 — the count leg was in hand and thrown away.]** `Satisfies.count` (the AIR's constraint
14, `real_count[last] = pi[num_turns]`, emitted at `Emit/EffectVmEmitTurnChainBinding.lean`'s
`lastRealCountBind`) has always been a field of the hypothesis, and this keystone used to conclude
only three of the four facts it could. That omission is precisely why `Aggregate.numTurns` was
UNPINNED downstream and why an inflated settled height was accepted
(`SelfSettlement.settle_accepts_inflated_height`, now superseded). The deployed AIR always pinned it;
the MODEL did not carry it across. It costs nothing: `count` + `represents_length`. -/
theorem binding_air_discharges_binding_sound
    (hash : List ℤ → ℤ) (rows : List BindingRow) (pub : BindingPublic)
    (steps : List ChainStep) (g : RecChainedState)
    (hsat : Satisfies hash rows pub)
    (hrep : Represents CH RH cmb compress compressN rows steps) :
    ChainBound CH RH cmb compress compressN steps
      ∧ pub.genesis = (match steps.head? with
          | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
          | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
      ∧ pub.final = foldedFinalRoot CH RH cmb compress compressN g steps
      ∧ pub.numTurns = steps.length := by
  -- (1) ChainBound from the row continuity tooth.
  have hbound := rowbound_represents_chainbound CH RH cmb compress compressN rows steps hrep hsat.continuity
  -- (0) the count leg: public num_turns = row count (AIR constraint 14) = step count (Represents).
  have hcount : pub.numTurns = steps.length := by
    rw [hsat.count]
    exact represents_length CH RH cmb compress compressN rows steps hrep
  -- decompose the (nonempty) rows / steps to read off the endpoints.
  obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hsat.nonempty
  cases steps with
  | nil => simp [Represents] at hrep
  | cons s ss =>
    have hp0 := hrep.1
    refine ⟨hbound, ?_, ?_, hcount⟩
    · -- genesis pin: head row old_root = pub.genesis, paired with step s.
      have hg : r.oldRoot = pub.genesis := hsat.genesis r (by simp)
      show pub.genesis = (match (s :: ss).head? with
          | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
          | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
      simp only [List.head?_cons]
      rw [← hg, hp0.1]
    · -- final pin: last row new_root = pub.final, paired with the last step = foldedFinalRoot.
      obtain ⟨lr, hlr⟩ : ∃ lr, (r :: rest).getLast? = some lr := by
        cases h : (r :: rest).getLast? with
        | none => rw [List.getLast?_eq_none_iff] at h; exact absurd h (List.cons_ne_nil r rest)
        | some lr => exact ⟨lr, rfl⟩
      have hf : lr.newRoot = pub.final := hsat.final lr hlr
      obtain ⟨t, ht, _, hn⟩ := represents_getLast CH RH cmb compress compressN (r :: rest) (s :: ss) hrep lr hlr
      rw [← hf, hn, foldedFinalRoot_eq_lastNew CH RH cmb compress compressN g (s :: ss) t ht]

end Portal

/-! ## 5. THE CR FLOOR — the digest binds the whole ordered history (rests on `Poseidon2SpongeCR`). -/

/-- **`histDigest_inj`** — injectivity of the running ordered digest under hash collision-resistance:
two equal-length row lists folded (from any starting accumulators) to the SAME digest have equal
starting accumulator AND equal ordered `(old, new, idx)` projections. The single use of
`Poseidon2SpongeCR`: each fold step peels one `hash [acc, old, new, idx]` collision. -/
theorem histDigest_inj (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (rows rows' : List BindingRow) (a b : ℤ),
      rows.length = rows'.length →
      histDigest hash a rows = histDigest hash b rows' →
      a = b ∧ rows.map proj = rows'.map proj := by
  intro rows
  induction rows with
  | nil =>
    intro rows' a b hlen heq
    cases rows' with
    | nil => exact ⟨heq, rfl⟩
    | cons r' rest' => simp at hlen
  | cons r rest ih =>
    intro rows' a b hlen heq
    cases rows' with
    | nil => simp at hlen
    | cons r' rest' =>
      have hlen' : rest.length = rest'.length := by simpa using hlen
      simp only [histDigest] at heq
      obtain ⟨hinner, htail⟩ :=
        ih rest' (hash [a, r.oldRoot, r.newRoot, r.idx]) (hash [b, r'.oldRoot, r'.newRoot, r'.idx]) hlen' heq
      have hlist := hCR _ _ hinner
      injection hlist with hab h1
      injection h1 with ho h2
      injection h2 with hn h3
      injection h3 with hi _
      refine ⟨hab, ?_⟩
      have hprojr : proj r = proj r' := by unfold proj; rw [ho, hn, hi]
      simp only [List.map_cons, hprojr, htail]

/-- **`digest_binds_ordered_history` (THE CR ANTI-REORDER TOOTH).** Two satisfying binding-AIR traces
that publish the same `chain_digest` and the same `num_turns` have the SAME ordered
`(old_root, new_root, idx)` sequence. So a same-endpoint, same-count reorder of the finalized history
yields a DIFFERENT `chain_digest` and is rejected — the only crypto reliance is the named
`Poseidon2SpongeCR` floor. -/
theorem digest_binds_ordered_history
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (rows rows' : List BindingRow) (pub pub' : BindingPublic)
    (h : Satisfies hash rows pub) (h' : Satisfies hash rows' pub')
    (hnum : pub.numTurns = pub'.numTurns)
    (hdig : pub.chainDigest = pub'.chainDigest) :
    rows.map proj = rows'.map proj := by
  have hlen : rows.length = rows'.length := by
    rw [← h.count, ← h'.count, hnum]
  have e : histDigest hash 0 rows = histDigest hash 0 rows' := by
    rw [← h.digestEq, ← h'.digestEq, hdig]
  exact (histDigest_inj hash hCR rows rows' 0 0 hlen e).2

/-! ## 6. NON-VACUITY — the constraints are satisfiable (witnessed) AND falsifiable (anti-ghost). -/

section Vacuity

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- The 1-row trace exposing a single chain step's roots. -/
def rowOf (s : ChainStep) : BindingRow :=
  { oldRoot := ChainStep.oldRoot CH RH cmb compress compressN s
  , newRoot := ChainStep.newRoot CH RH cmb compress compressN s
  , idx := 0 }

/-- The public inputs for the 1-row trace over step `s`. -/
def pubOf (hash : List ℤ → ℤ) (s : ChainStep) : BindingPublic :=
  { genesis := ChainStep.oldRoot CH RH cmb compress compressN s
  , final := ChainStep.newRoot CH RH cmb compress compressN s
  , numTurns := 1
  , chainDigest := histDigest hash 0 [rowOf CH RH cmb compress compressN s] }

/-- The 1-row trace satisfies the AIR (positive non-vacuity, for ANY step and hash). -/
theorem satisfies_one (hash : List ℤ → ℤ) (s : ChainStep) :
    Satisfies hash [rowOf CH RH cmb compress compressN s] (pubOf CH RH cmb compress compressN hash s) where
  nonempty := by simp
  continuity := trivial
  genesis := by intro r hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; rfl
  final := by intro r hr; rw [List.getLast?_singleton] at hr; cases hr; rfl
  digestEq := rfl
  count := rfl

/-- The 1-row trace represents the singleton chain `[s]`. -/
theorem represents_one (s : ChainStep) :
    Represents CH RH cmb compress compressN [rowOf CH RH cmb compress compressN s] [s] :=
  ⟨⟨rfl, rfl⟩, trivial⟩

/-- **`keystone_fires` (the discharge is non-vacuous).** On a real single-step chain the keystone
FIRES, delivering a genuine `binding_sound` conclusion: `ChainBound [s]`, the genesis pin to `s`'s
`old_root`, the final pin to `foldedFinalRoot`, and the count pin `num_turns = 1`. So the discharged
obligation is a true fact about a real chain, not an empty implication. -/
theorem keystone_fires (hash : List ℤ → ℤ) (s : ChainStep) (g : RecChainedState) :
    ChainBound CH RH cmb compress compressN [s]
      ∧ (pubOf CH RH cmb compress compressN hash s).genesis = (match ([s] : List ChainStep).head? with
          | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
          | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
      ∧ (pubOf CH RH cmb compress compressN hash s).final
          = foldedFinalRoot CH RH cmb compress compressN g [s]
      ∧ (pubOf CH RH cmb compress compressN hash s).numTurns = ([s] : List ChainStep).length :=
  binding_air_discharges_binding_sound CH RH cmb compress compressN hash _ _ [s] g
    (satisfies_one CH RH cmb compress compressN hash s) (represents_one CH RH cmb compress compressN s)

end Vacuity

/-- A concrete honest 2-row trace (roots `10 → 20 → 30`). -/
def goodRows : List BindingRow :=
  [{ oldRoot := 10, newRoot := 20, idx := 0 }, { oldRoot := 20, newRoot := 30, idx := 1 }]

/-- Public inputs for the honest 2-row trace. -/
def goodPub (hash : List ℤ → ℤ) : BindingPublic :=
  { genesis := 10, final := 30, numTurns := 2, chainDigest := histDigest hash 0 goodRows }

/-- **`satisfies_two` (positive non-vacuity with nontrivial continuity).** A genuinely 2-row honest
trace satisfies the AIR — the continuity tooth `20 == 20` holds. So `Satisfies` is inhabited with a
nontrivial ordered chain. -/
theorem satisfies_two (hash : List ℤ → ℤ) : Satisfies hash goodRows (goodPub hash) where
  nonempty := by simp [goodRows]
  continuity := ⟨rfl, trivial⟩
  genesis := by intro r hr; simp only [goodRows, List.head?_cons, Option.some.injEq] at hr; subst hr; rfl
  final := by
    intro r hr
    simp only [goodRows] at hr
    rw [List.getLast?_cons_cons, List.getLast?_singleton] at hr
    cases hr; rfl
  digestEq := rfl
  count := rfl

/-- A reordered/spliced 2-row trace whose continuity is broken (`new_root[0] = 0 ≠ 1 = old_root[1]`). -/
def badRows : List BindingRow :=
  [{ oldRoot := 0, newRoot := 0, idx := 0 }, { oldRoot := 1, newRoot := 1, idx := 1 }]

/-- **`reordered_not_satisfies` (THE ANTI-GHOST TOOTH).** A trace whose temporal tooth is broken does
NOT satisfy the AIR: the continuity constraint forces `0 = 1`, a contradiction. Together with
`satisfies_two`, the AIR constraints are both satisfiable and falsifiable — `Satisfies` is non-vacuous,
and a tampered (reordered/dropped/inserted) chain is genuinely rejected. -/
theorem reordered_not_satisfies (hash : List ℤ → ℤ) (pub : BindingPublic) :
    ¬ Satisfies hash badRows pub := by
  intro h
  have hb := h.continuity
  simp only [badRows, RowBound] at hb
  exact absurd hb.1 (by norm_num)

/-! ## 7. Axiom hygiene. -/

#assert_axioms binding_air_discharges_binding_sound
#assert_axioms represents_length
#assert_axioms rowbound_represents_chainbound
#assert_axioms foldedFinalRoot_eq_lastNew
#assert_axioms represents_getLast
#assert_axioms histDigest_inj
#assert_axioms digest_binds_ordered_history
#assert_axioms keystone_fires
#assert_axioms satisfies_one
#assert_axioms satisfies_two
#assert_axioms reordered_not_satisfies

end Dregg2.Circuit.BindingAirSound
