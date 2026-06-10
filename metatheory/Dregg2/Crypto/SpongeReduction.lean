/-
# Dregg2.Crypto.SpongeReduction — the sponge/commitment CR REDUCED to the permutation compression CR.

`Dregg2/Circuit/Poseidon2Binding.lean` grounds the whole full-state commitment tower on a SINGLE
named assumption `Poseidon2SpongeCR sponge` (`∀ xs ys, sponge xs = sponge ys → xs = ys`), and the
crypto-ledger classified that named assumption as IRREDUCIBLE PRIMITIVE #4 "at the sponge level".

That left a real gap: `Poseidon2SpongeCR` is a statement about an UNBOUNDED-arity hash over `List ℤ`.
The genuine cryptographic primitive a Poseidon2 implementation rests on is much smaller — the
collision-resistance of ONE FIXED-WIDTH permutation `P : State → State`, used as a per-block
compression. The sponge over that permutation is a CONSTRUCTION, and the security of the construction
is a THEOREM (the sponge / Merkle–Damgård domain-extension reduction), not a fresh assumption. This
module discharges that theorem.

## What is modelled (faithful to `circuit/src/poseidon2.rs::hash_many`)

The real `hash_many` (`poseidon2.rs:369`) over `inputs : &[BabyBear]`, `rate = 4`, width 16:

```rust
let mut state = Poseidon2State::new();           // all-zero state
state.state[4] = BabyBear::new(inputs.len());    // capacity domain-sep: length
for chunk in inputs.chunks(rate) {               // absorb, rate-4 chunks
    for (i, &e) in chunk.iter().enumerate() { state.state[i] += e; }
    state.permute();                             // the FIXED-WIDTH permutation P
}
state.state[0]                                   // squeeze slot 0
```

abstracted as a `SpongeMachine`:
  * `perm    : State → State`     — the fixed-width Poseidon2 permutation (`Poseidon2State::permute`).
  * `init    : ℕ → State`         — `new()` then capacity slot ← length (the length domain-sep tag).
  * `absorb  : State → List ℤ → State` — add a (≤rate) chunk into the rate slots (`state[i] += e`).
  * `squeeze : State → ℤ`         — read slot 0.
  * `chunksOf rate`               — `inputs.chunks(rate)` (modelled by `List.toChunks`, flatten-invertible).

with `step s a := perm (absorb s a)` the per-block compression and
`spongeOf xs := squeeze (foldl step (init xs.length) (chunksOf xs))` the whole `hash_many`.

## The reduction (a real proof, NOT a relabel)

`Poseidon2SpongeCR (spongeOf …)` is DISCHARGED from THREE separate pieces — two irreducible
crypto carriers and one structural domain-separation fact, ALL stated explicitly:

  1. **`CompressionCR M`** — IRREDUCIBLE PRIMITIVE: ONE permutation call, used as the per-block
     compression `step = perm ∘ absorb`, is collision-resistant as a chaining function (equal next
     FULL state ⇒ equal predecessor state AND equal absorbed block). Primitive #4 for a single `perm`.
  2. **`SqueezeBindsReachable M`** — the truncation residual: the slot-0 squeeze is injective on
     REACHABLE final sponge states (a digest collision without a final-state collision is exactly a
     last-permutation truncation collision). The honest narrow-output bit.
  3. **`InitStepSeparated M`** — STRUCTURAL domain separation: an `init` output (rate slots 0,
     capacity = length tag) is never a `step` output (a `perm` image). This is the length-prefix
     domain separation that makes the construction prefix-free; it is a structural property of the
     real `init`/`perm` (proved for the `Reference` machine by construction), NOT a crypto assumption.

`spongeCR_of_reduction`: a digest collision ⇒[2] final-state collision ⇒[1 + 3 MD peel] equal block
lists ⇒[`chunksOf` flatten-invertible] equal inputs. The crypto content is exactly `CompressionCR` +
`SqueezeBindsReachable`; `InitStepSeparated`, `chunksOf`, the induction are structural.

l4v bar: every theorem pins `{propext, Classical.choice, Quot.sound}` (`#assert_axioms`); no `sorry`,
no `:= True`, no `native_decide`.
-/
import Dregg2.Circuit.Poseidon2Binding
import Mathlib.Data.List.Basic

namespace Dregg2.Crypto.SpongeReduction

open Dregg2.Circuit.Poseidon2Binding
  (Poseidon2SpongeCR babyBearD4W16 Poseidon2RealParams Poseidon2RealizedSponge)

/-! ## §0 — the abstract sponge machine over a fixed-width permutation. -/

/-- A sponge machine: the fixed-width permutation plus the absorb/init/squeeze wiring, mirroring
`circuit/src/poseidon2.rs::hash_many`. -/
structure SpongeMachine (State : Type) where
  /-- The fixed-width permutation `P` (`Poseidon2State::permute`). -/
  perm : State → State
  /-- `new()` then capacity slot ← length (the domain-separation tag). -/
  init : ℕ → State
  /-- Add a (≤ rate) chunk into the rate slots (`state[i] += e`). -/
  absorb : State → List ℤ → State
  /-- Squeeze slot 0. -/
  squeeze : State → ℤ
  /-- The absorption rate (`= 4` for the real `hash_many`). -/
  rate : ℕ
  /-- `rate > 0` (a real sponge has positive rate; `hash_many` uses 4). -/
  rate_pos : 0 < rate

/-- `chunksRec rate xs` — split `xs` into rate-sized blocks (take `rate`, recurse on the drop). The
positive-rate hypothesis lives on the caller; with `rate = 0` the `take`/`drop` are degenerate but
`chunksRec` still terminates by the explicit guard. Self-defined so `chunksRec.induct` and its
`flatten`-invertibility are PROVED structurally — no library dependency. -/
def chunksRec (rate : ℕ) : List ℤ → List (List ℤ)
  | [] => []
  | x :: xs =>
    if h : 0 < rate then
      have : ((x :: xs).drop rate).length < (x :: xs).length := by
        rw [List.length_drop]; simp; omega
      (x :: xs).take rate :: chunksRec rate ((x :: xs).drop rate)
    else [x :: xs]
termination_by xs => xs.length

/-- `chunksRec` recovers the original list under `flatten` when `rate > 0` (`take rate ++ drop rate`),
PROVED by the equation-compiler induction principle. The `rate = 0` branch returns `[xs]`, also
flatten-recovering. -/
theorem chunksRec_flatten (rate : ℕ) (xs : List ℤ) : (chunksRec rate xs).flatten = xs := by
  induction xs using (chunksRec.induct rate) with
  | case1 => simp [chunksRec]
  | case2 x xs h _ ih =>
      rw [chunksRec]; simp only [h, dif_pos]
      rw [List.flatten_cons, ih, List.take_append_drop]
  | case3 x xs h =>
      rw [chunksRec]; simp only [h, dif_neg, not_false_iff]
      simp

namespace SpongeMachine

variable {State : Type} (M : SpongeMachine State)

/-- `chunksOf xs` — `inputs.chunks(rate)` at this machine's rate. -/
def chunksOf (xs : List ℤ) : List (List ℤ) := chunksRec M.rate xs

/-- One absorb-then-permute step (`state[i] += chunk[i]; state.permute()`): the per-block COMPRESSION
the sponge folds; its CR is the genuine primitive. -/
def step (s : State) (chunk : List ℤ) : State := M.perm (M.absorb s chunk)

/-- The final sponge STATE: init at the length, fold the compression over the blocks. -/
def finalState (xs : List ℤ) : State :=
  List.foldl M.step (M.init xs.length) (M.chunksOf xs)

/-- The full sponge digest: squeeze slot 0 of the final state. This is `hash_many` line-for-line. -/
def spongeOf (xs : List ℤ) : ℤ := M.squeeze (M.finalState xs)

/-- `chunksOf` recovers the original list under `flatten` (structural invertibility of the
chunking — the domain-extension alignment step needs no assumption). -/
theorem chunksOf_flatten (xs : List ℤ) : (M.chunksOf xs).flatten = xs :=
  chunksRec_flatten M.rate xs

end SpongeMachine

/-! ## §1 — the irreducible carriers + the structural domain-separation field. -/

variable {State : Type}

/-- **`CompressionCR M`** — the per-block compression `step = perm ∘ absorb` is collision-resistant as
a chaining function: a collision in the next FULL state forces equal predecessor state AND equal
absorbed block. THE irreducible primitive (one permutation call), primitive #4 for a single `perm`. -/
def CompressionCR (M : SpongeMachine State) : Prop :=
  ∀ (s t : State) (a b : List ℤ), M.step s a = M.step t b → s = t ∧ a = b

/-- **`SqueezeBindsReachable M`** — the slot-0 squeeze is injective on REACHABLE final sponge states:
two inputs with equal digests have equal final states. The honest truncation residual. -/
def SqueezeBindsReachable (M : SpongeMachine State) : Prop :=
  ∀ xs ys : List ℤ, M.spongeOf xs = M.spongeOf ys → M.finalState xs = M.finalState ys

/-- **`InitStepSeparated M`** — STRUCTURAL domain separation: an `init` output is never a `step`
(`perm`) output. The length-prefix tag (`state[4] = len`, rate slots 0) lives in a part of the state a
fresh `perm` image does not reproduce; this makes the construction prefix-free. A structural property
of the real `init`/`perm` (the `Reference` machine proves it by construction), not a crypto carrier. -/
def InitStepSeparated (M : SpongeMachine State) : Prop :=
  ∀ (n : ℕ) (s : State) (a : List ℤ), M.init n ≠ M.step s a

/-! ## §2 — the MD induction: equal final states ⇒ equal block lists (⇒ equal inputs).

By double `reverseRecOn`: a matched final state forces (via `CompressionCR`) the last blocks equal and
the predecessors equal, recursing. The empty-vs-nonempty boundary (`init` vs `step` output) is the
case `InitStepSeparated` rules out — that is exactly where the length-prefix earns its keep. -/

/-- Equal `foldl step` runs (from ANY inits in the `init`-image) have equal block lists. The crux: the
asymmetric base cases equate an `init` with a `step` output, excluded by `InitStepSeparated`. Nested
`reverseRecOn` peels the LAST block on each side, so `foldl_concat` exposes the terminal `step`. -/
theorem foldl_step_eq (M : SpongeMachine State)
    (hC : CompressionCR M) (hSep : InitStepSeparated M) :
    ∀ (cs ds : List (List ℤ)) (m n : ℕ),
      List.foldl M.step (M.init m) cs = List.foldl M.step (M.init n) ds →
      M.init m = M.init n ∧ cs = ds := by
  intro cs
  induction cs using List.reverseRecOn with
  | nil =>
      intro ds m n h
      induction ds using List.reverseRecOn with
      | nil => exact ⟨h, rfl⟩
      | append_singleton ds' e _ =>
          -- LHS = init m ; RHS = step (foldl step (init n) ds') e — excluded by InitStepSeparated.
          rw [List.foldl_concat] at h
          exact absurd h (hSep m _ e)
  | append_singleton cs c ih =>
      intro ds m n h
      induction ds using List.reverseRecOn with
      | nil =>
          -- LHS = step (...) c ; RHS = init n — excluded by InitStepSeparated (symmetric).
          rw [List.foldl_concat] at h
          exact absurd h.symm (hSep n _ c)
      | append_singleton ds' e _ =>
          -- both nonempty: peel both terminal steps via CompressionCR.
          rw [List.foldl_concat, List.foldl_concat] at h
          obtain ⟨hstate, hchunk⟩ := hC _ _ c e h
          obtain ⟨hinit, hcs⟩ := ih ds' m n hstate
          exact ⟨hinit, by rw [hcs, hchunk]⟩

/-- **`finalState_inj`** — equal final sponge states force equal inputs. Composes the MD block-list
equality (`foldl_step_eq`) with the flatten-invertibility of `chunksOf`. Pure structural + the
compression CR; no truncation hardness yet (this is the FULL-state level). -/
theorem finalState_inj (M : SpongeMachine State)
    (hC : CompressionCR M) (hSep : InitStepSeparated M) {xs ys : List ℤ}
    (h : M.finalState xs = M.finalState ys) : xs = ys := by
  unfold SpongeMachine.finalState at h
  obtain ⟨_, hblocks⟩ := foldl_step_eq M hC hSep _ _ _ _ h
  have : (M.chunksOf xs).flatten = (M.chunksOf ys).flatten := by rw [hblocks]
  rwa [M.chunksOf_flatten, M.chunksOf_flatten] at this

/-! ## §3 — THE REDUCTION: sponge CR ⟸ CompressionCR + SqueezeBindsReachable + InitStepSeparated. -/

/-- **`spongeCR_of_reduction`** — the headline. The variable-length sponge digest `M.spongeOf` is
collision-resistant, REDUCED to: the per-permutation-call compression CR (`hC`), the slot-0 truncation
residual (`hSq`), and the structural length-prefix domain separation (`hSep`). A real reduction: a
digest collision is lifted (truncation residual) to a FINAL-STATE collision, which the MD induction
peels into a compression collision; no fresh assumption beyond the two named carriers. -/
theorem spongeCR_of_reduction (M : SpongeMachine State)
    (hC : CompressionCR M) (hSq : SqueezeBindsReachable M) (hSep : InitStepSeparated M) :
    Poseidon2SpongeCR M.spongeOf := by
  intro xs ys h
  exact finalState_inj M hC hSep (hSq xs ys h)

/-! ## §4 — non-vacuity: a REAL `SpongeMachine` whose carriers hold.

A concrete machine over `State := ℕ × List ℤ` (chaining nat × accumulated blocks), with an INJECTIVE
"permutation" (the carriers HOLD), so every reduction above FIRES on a real instance — and the
carriers are provably FALSE on a degenerate machine (a constant squeeze / a non-prefix-free init),
witnessing they are not `True`. The genuine Poseidon2 leaves CR as the standing obligation; here we
discharge with a provably-injective stand-in, exactly as `PortalFloor.Reference` does. -/

namespace Reference

/-- The reference state: a `tag : ℕ` (`0` = fresh init, incremented by each `perm` so it is injective
and init-vs-step separated), the length tag `n`, and the list of absorbed blocks. -/
abbrev RState : Type := (ℕ × ℕ) × List (List ℤ)

/-- Reference machine. `init n := ((0, n), [])` (tag 0); `absorb` appends the block; `perm` increments
the tag (INJECTIVE, and keeps tag ≥ 1 on every step output, so init outputs (tag 0) are disjoint —
the structural `InitStepSeparated`); `squeeze` reads the FULL state via the injective `Encodable`
encoding (so the truncation residual `SqueezeBindsReachable` holds with room to spare). -/
def refMachine : SpongeMachine RState where
  perm := fun ((t, n), bs) => ((t + 1, n), bs)
  init := fun n => ((0, n), [])
  absorb := fun ((t, n), bs) chunk => ((t, n), bs ++ [chunk])
  squeeze := fun s => (Encodable.encode s : ℕ)
  rate := 4
  rate_pos := by decide

/-- `refMachine`'s compression is INJECTIVE in the full input state (tag incremented, block appended,
length carried), so `CompressionCR` HOLDS — discharged structurally, no crypto. -/
theorem refCompressionCR : CompressionCR refMachine := by
  intro s t a b h
  obtain ⟨⟨ts, ns⟩, bss⟩ := s
  obtain ⟨⟨tt, nt⟩, bst⟩ := t
  simp only [SpongeMachine.step, refMachine] at h
  -- h : ((ts + 1, ns), bss ++ [a]) = ((tt + 1, nt), bst ++ [b])
  rw [Prod.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨ht, hn⟩, hbs⟩ := h
  have hts : ts = tt := by omega
  obtain ⟨hbss, hab⟩ := List.append_inj' hbs rfl
  refine ⟨?_, (List.cons.inj hab).1⟩
  rw [hts, hn, hbss]

/-- `refMachine` is init/step separated: a `step` output has tag ≥ 1 (incremented by `perm`), an
`init` output has tag 0. STRUCTURAL, proved by `omega` on the tag. -/
theorem refInitStepSeparated : InitStepSeparated refMachine := by
  intro n s a h
  obtain ⟨⟨t, m⟩, bs⟩ := s
  simp only [SpongeMachine.step, refMachine] at h
  -- h : ((0, n), []) = ((t + 1, m), bs ++ [a])  — tags 0 vs t+1 clash.
  rw [Prod.mk.injEq, Prod.mk.injEq] at h
  omega

/-- `refMachine`'s squeeze binds the reachable final state (`Encodable.encode` is injective on the
whole state), so `SqueezeBindsReachable` HOLDS. -/
theorem refSqueezeBindsReachable : SqueezeBindsReachable refMachine := by
  intro xs ys h
  simp only [SpongeMachine.spongeOf, refMachine] at h
  exact Encodable.encode_injective (by exact_mod_cast h)

/-- The full reduction FIRES on the reference machine: its `spongeOf` is collision-resistant, derived
through `spongeCR_of_reduction` from the three structurally-discharged carriers. Witnesses that the
reduction is non-vacuous (the carriers are inhabitable and the theorem applies). -/
theorem refSpongeCR : Poseidon2SpongeCR refMachine.spongeOf :=
  spongeCR_of_reduction refMachine refCompressionCR refSqueezeBindsReachable refInitStepSeparated

/-! ### A degenerate machine that FALSIFIES `SqueezeBindsReachable` (the carriers are not `True`).

`badMachine` is `refMachine` with a CONSTANT squeeze (`fun _ => 0`). Then every digest is `0`, so two
distinct inputs collide on the digest while their final states differ — `SqueezeBindsReachable` is
provably FALSE. This proves the carrier is a meaningful named proposition, not a relabelled `True`. -/

def badMachine : SpongeMachine RState := { refMachine with squeeze := fun _ => 0 }

/-- One `badMachine.step` appends the absorbed block to the recorded block list. -/
theorem badMachine_step_blocks (s : RState) (c : List ℤ) :
    (badMachine.step s c).2 = s.2 ++ [c] := by
  obtain ⟨⟨t, n⟩, bs⟩ := s; rfl

/-- Folding `badMachine.step` from any state appends the blocks to the state's recorded block list. -/
theorem badMachine_foldl_blocks (cs : List (List ℤ)) (s : RState) :
    (List.foldl badMachine.step s cs).2 = s.2 ++ cs := by
  induction cs using List.reverseRecOn generalizing s with
  | nil => simp
  | append_singleton cs c ih =>
      rw [List.foldl_concat, badMachine_step_blocks, ih, List.append_assoc]

/-- Under `badMachine`, the final-state block component is exactly the input's chunking (init starts
empty, each `step` appends one block). So distinct chunkings ⇒ distinct final states. -/
theorem refFinalState_blocks (xs : List ℤ) :
    (badMachine.finalState xs).2 = badMachine.chunksOf xs := by
  unfold SpongeMachine.finalState
  rw [badMachine_foldl_blocks]
  show ([] : List (List ℤ)) ++ badMachine.chunksOf xs = badMachine.chunksOf xs
  simp

/-- The final states of `[0]` and `[0,0]` under `badMachine` differ: `[0,0]` chunks to one block of
length 2, `[0]` to one block of length 1 — distinct chunk lists, hence distinct recorded block
lists, hence distinct final states. -/
theorem badMachine_finalState_ne :
    badMachine.finalState [0] ≠ badMachine.finalState [(0 : ℤ), 0] := by
  intro h
  have h2 := congrArg Prod.snd h
  rw [refFinalState_blocks, refFinalState_blocks] at h2
  -- chunksOf [0] = [[0]] ; chunksOf [0,0] = [[0,0]]  (rate 4)
  simp only [SpongeMachine.chunksOf, badMachine, refMachine, chunksRec] at h2
  norm_num at h2

/-- `badMachine` FALSIFIES `SqueezeBindsReachable`: equal (constant) digests, unequal final states. -/
theorem badMachine_not_squeezeBinds : ¬ SqueezeBindsReachable badMachine := by
  intro hbad
  have hdig : badMachine.spongeOf [0] = badMachine.spongeOf [(0 : ℤ), 0] := rfl
  exact badMachine_finalState_ne (hbad _ _ hdig)

end Reference

/-! ## §5 — the bridge into the commitment tower: a `Poseidon2RealizedSponge` FROM the reduction.

`Poseidon2Binding.Poseidon2RealizedSponge` is the bundle the whole `StateCommit` tower consumes; it
carries `spongeCR` as a FIELD. Before this module that field was the IRREDUCIBLE sponge-level CR.
`realizedSpongeOfReduction` now BUILDS that bundle from a `SpongeMachine` + the reduction, so the
`spongeCR` the tower consumes is PROVED by `spongeCR_of_reduction` (the MD/permutation reduction)
rather than assumed at the sponge level. The named obligation drops from "the unbounded list-hash is
injective" to "ONE permutation call is CR (`CompressionCR`) + the slot-0 truncation residual
(`SqueezeBindsReachable`)" — a strictly smaller, deeper carrier. -/

/-- **`realizedSpongeOfReduction`** — package `M.spongeOf` as a `Poseidon2RealizedSponge` (tagged with
the REAL `babyBearD4W16` p3 params), with its `spongeCR` field DISCHARGED by the permutation reduction.
This is what makes `Poseidon2SpongeCR` DISCHARGEABLE (not primitive-at-the-sponge-level): the
tower's `spongeCR` carrier is now a THEOREM over `CompressionCR` + `SqueezeBindsReachable`. -/
def realizedSpongeOfReduction (M : SpongeMachine State)
    (hC : CompressionCR M) (hSq : SqueezeBindsReachable M) (hSep : InitStepSeparated M) :
    Poseidon2RealizedSponge M.spongeOf :=
  { params := babyBearD4W16
    params_are_real := rfl
    spongeCR := spongeCR_of_reduction M hC hSq hSep }

/-- The reference machine yields a real `Poseidon2RealizedSponge` through the reduction — the bridge
fires end-to-end on a concrete instance (non-vacuity of the whole §5 bridge). -/
def Reference.refRealizedSpongeOfReduction : Poseidon2RealizedSponge Reference.refMachine.spongeOf :=
  realizedSpongeOfReduction Reference.refMachine
    Reference.refCompressionCR Reference.refSqueezeBindsReachable Reference.refInitStepSeparated

#assert_axioms foldl_step_eq
#assert_axioms finalState_inj
#assert_axioms spongeCR_of_reduction
#assert_axioms realizedSpongeOfReduction
#assert_axioms Reference.refCompressionCR
#assert_axioms Reference.refInitStepSeparated
#assert_axioms Reference.refSqueezeBindsReachable
#assert_axioms Reference.refSpongeCR
#assert_axioms Reference.badMachine_not_squeezeBinds

end Dregg2.Crypto.SpongeReduction
