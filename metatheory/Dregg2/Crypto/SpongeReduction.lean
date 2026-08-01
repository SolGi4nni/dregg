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
module ONCE discharged that theorem — the discharge rode a premise the tree PROVES FALSE, so it is
deleted; see the tombstone below and consume `Crypto/SpongeCompressionRegrounded.lean`.

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

## ⚠ THE REDUCTION IS DELETED — it was VACUOUS at every deployed parameter

The construction is still modelled here, and the THREE carrier defs survive below:

  1. **`CompressionCR M`** — ONE permutation call, used as the per-block compression
     `step = perm ∘ absorb`, is collision-resistant as a chaining function (equal next FULL state ⇒
     equal predecessor state AND equal absorbed block). ⚠ **REFUTED — see below.**
  2. **`SqueezeBindsReachable M`** — the truncation residual: the slot-0 squeeze is injective on
     REACHABLE final sponge states. The honest narrow-output bit.
  3. **`InitStepSeparated M`** — STRUCTURAL domain separation: an `init` output (rate slots 0,
     capacity = length tag) is never a `step` output (a `perm` image); the length-prefix separation
     that makes the construction prefix-free. A structural property of the real `init`/`perm`.

What is GONE is everything that CONSUMED (1): `foldl_step_eq`, `finalState_inj`, the headline
`spongeCR_of_reduction`, `realizedSpongeOfReduction`, and the two `Reference` witnesses that existed
only to fire them. Tombstones at §2 / §3 / §4 / §5 say what each claimed.

⚠ `CompressionCR` is not merely unproven — it is PROVED FALSE, by
`Crypto.SpongeCompressionRegrounded.compressionCR_false_of_finite_state [Nonempty State]
[Finite State]`. Uncurried, `step : State × List ℤ → State` carries an INFINITE domain (`List ℤ`) into
a fixed-width permutation state, which is precisely and only what `SpongeMachine` says a real `perm`
acts on: no numeric bound, no field modulus, no parameter regime is needed to refute it. So every
consumer was VACUOUSLY TRUE at deployed parameters, and `#assert_axioms` could never see it — it
audits the PROOF (kernel-clean, and they all were) and never the HYPOTHESIS. The def is KEPT because
its own falsity theorem names it, and `Verify/FloorRatchet.lean` keys the accrual stop on that name.

**Consume `Crypto/SpongeCompressionRegrounded.lean` instead — the ROM-DISCHARGED forms first:**
`foldl_step_eq_binds_rom` (:847), `finalState_inj_binds_rom` (:859), and the headline
`spongeCR_of_reduction_binds_rom` (:874). Those carry NO floor hypothesis and NO cost model — only
query-boundedness and a `PolyBounded` query count, concluding `Negl`. The `_advantage_bound` siblings
(`foldl_step_eq_advantage_bound` :563, `finalState_inj_advantage_bound` :576,
`spongeCR_of_reduction_advantage_bound` :604) state the same reductions carrying an EXPLICIT
undischarged `Eff`, for the settings where the ROM is not available.

l4v bar: every surviving theorem pins `{propext, Classical.choice, Quot.sound}` (`#assert_axioms`).
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
absorbed block. THE irreducible primitive (one permutation call), primitive #4 for a single `perm`.

⚠ **BROKEN AS NAMED — FALSE for ANY REAL SPONGE. Its four consumers (`foldl_step_eq`,
`finalState_inj`, the headline `spongeCR_of_reduction`, `realizedSpongeOfReduction`) were VACUOUSLY
TRUE at deployed parameters and are DELETED** — tombstones at §2/§3/§5. The refutation is
`Crypto.SpongeCompressionRegrounded.compressionCR_false_of_finite_state` (`docs/deos/VACUITY-SWEEP.md`
FINDING 2): uncurried, `step : State × List ℤ → State` has an INFINITE domain (`List ℤ`) and a FINITE
codomain, and `[Finite State]` is the WHOLE hypothesis — no numeric bound needed, because a
fixed-width permutation state IS a finite type. So the reduction that demoted the tower's `spongeCR`
carrier from "an unbounded list-hash is injective" to "ONE permutation call is CR" transported nothing
at a real sponge.

**Consume `Crypto.SpongeCompressionRegrounded` instead**, ROM-discharged forms first
(`foldl_step_eq_binds_rom` :847, `finalState_inj_binds_rom` :859, `spongeCR_of_reduction_binds_rom`
:874 — query-boundedness + a `PolyBounded` query count ⇒ `Negl`, no floor and no cost model), with the
`_advantage_bound` siblings (:563/:576/:604) where the ROM is unavailable. Both routes run through
`peel`: a CONSTRUCTIVE extractor that walks the two `foldl step` chains from the last block inward and
RETURNS the first divergence as an explicit `(state, block)` collision — the deleted `foldl_step_eq`
induction run BACKWARDS, PRODUCING the collision that theorem merely CONSUMED, with
`InitStepSeparated` discharging the boundary exactly as it did here.

⚑ **This def is KEPT deliberately.** Deleting it would delete the falsity theorem that names it, and
`Verify/FloorRatchet.lean` keys the accrual stop on the sentinel name: a refuted floor with a visible
in-tree refutation is a tombstone WITH TEETH, and removing it is how new vacuous floors get in. -/
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

/-! ## §2 — TOMBSTONE: the MD induction `foldl_step_eq` and `finalState_inj`, DELETED as VACUOUS.

`foldl_step_eq (hC : CompressionCR M) (hSep : InitStepSeparated M)` claimed that two `foldl M.step`
runs from starts in the `init`-image with equal results have equal block lists (nested `reverseRecOn`
peeling one `CompressionCR` per block via `List.foldl_concat`; the asymmetric base cases, which equate
an `init` output with a `step` output, closed by `InitStepSeparated` — exactly where the length-prefix
earned its keep). `finalState_inj` composed that with `chunksOf_flatten` to get equal INPUTS from equal
final sponge states: the FULL-state level, no truncation hardness yet.

⚠ Both were VACUOUSLY TRUE at every deployed parameter. Their `hC : CompressionCR M` premise is
PROVED FALSE by `Crypto.SpongeCompressionRegrounded.compressionCR_false_of_finite_state
[Nonempty State] [Finite State]` — uncurried, `step : State × List ℤ → State` maps an INFINITE domain
into a fixed-width, hence `Finite`, permutation state, and that instance is the WHOLE hypothesis.
`#assert_axioms` pinned both proofs clean and never looked at the premise, so they read as the result
while transporting nothing. The `CompressionCR` def is KEPT above, as the tombstone the falsity
theorem names.

**CONSUME INSTEAD**, in `Crypto/SpongeCompressionRegrounded.lean` — the ROM-DISCHARGED forms:
  * **`foldl_step_eq_binds_rom` (:847)** succeeds `foldl_step_eq`;
  * **`finalState_inj_binds_rom` (:859)** succeeds `finalState_inj`.
Neither carries a floor hypothesis or a cost model: query-boundedness plus a `PolyBounded` query count
concluding `Negl`, over `mdPeelGame` / `finalStateCollisionGame` — the events these theorems claimed
to make outright IMPOSSIBLE. Where the ROM is unavailable, `foldl_step_eq_advantage_bound` (:563) and
`finalState_inj_advantage_bound` (:576) state the same reductions with an EXPLICIT undischarged `Eff`.
Both routes go through `peel`/`peel_spec` — this induction run BACKWARDS as a CONSTRUCTIVE extractor
that walks the two chains from the last block inward and RETURNS the first divergence as an explicit
`(state, block)` compression collision, PRODUCING what this theorem merely CONSUMED. -/

/-! ## §3 — TOMBSTONE: the headline `spongeCR_of_reduction`, DELETED as VACUOUS.

`spongeCR_of_reduction (hC : CompressionCR M) (hSq : SqueezeBindsReachable M)
(hSep : InitStepSeparated M) : Poseidon2SpongeCR M.spongeOf` was THIS FILE'S KEYSTONE and the tower's:
the theorem that demoted the whole `StateCommit` commitment tower's `spongeCR` carrier from "an
unbounded list-hash over `List ℤ` is injective" to "ONE permutation call is CR" — primitive #4 at the
permutation rather than at the sponge. It lifted a digest collision through `hSq` to a FINAL-STATE
collision and handed that to §2's MD induction.

⚠ It was VACUOUSLY TRUE at every deployed parameter, for the same reason as §2: `hC` is refuted at any
fixed-width permutation state by `Crypto.SpongeCompressionRegrounded.compressionCR_false_of_finite_state`.
A demotion that rides a FALSE premise demotes nothing — the tower never received the smaller carrier
this claimed to hand it, and the crypto-ledger's "primitive #4 is now at the permutation" followed from
a theorem with no content at the parameters anyone runs.

**CONSUME INSTEAD: `Crypto/SpongeCompressionRegrounded.spongeCR_of_reduction_binds_rom` (:874)** — the
ROM-DISCHARGED headline. No floor hypothesis and no cost model: a query-bounded adversary with a
`PolyBounded` query count wins `spongeCollisionGame` — precisely the event this theorem claimed to
make impossible — only with `Negl` probability. Where the ROM is unavailable,
`spongeCR_of_reduction_advantage_bound` (:604) states the same reduction carrying an EXPLICIT
undischarged `Eff` instead of a false floor. -/

/-! ## §4 — the carriers' POSITIVE POLE: a `SpongeMachine` on which each one HOLDS.

A concrete machine over `State := ℕ × List ℤ` (chaining nat × accumulated blocks), with an INJECTIVE
"permutation", so each carrier above is INHABITED — `CompressionCR` included, which is what keeps
`SpongeCompressionRegrounded.compressionCR_false_of_finite_state` a claim about FIXED-WIDTH state and
not about an empty predicate (that file's header cites `refCompressionCR` for exactly this). The
opposite pole is here too: the carriers are provably FALSE on a degenerate machine (a constant
squeeze), witnessing they are not relabelled `True`.

⚠ The reduction these once fired end-to-end is DELETED (§2/§3), and with it the two witnesses that
existed only to fire it — `refSpongeCR` (§4 tombstone) and `refRealizedSpongeOfReduction` (§5). What
survives here are the carrier poles, which stand on their own and are what the ratchet reads. -/

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

/-! ### TOMBSTONE: `refSpongeCR`, deleted with the reduction it witnessed.

`refSpongeCR : Poseidon2SpongeCR refMachine.spongeOf` applied §3's `spongeCR_of_reduction` to the three
structurally-discharged reference carriers. Its statement was TRUE (the toy state is infinite and
`Encodable.encode` is injective) but its whole content was "the §3 reduction is non-vacuous on a
concrete instance" — scaffolding of a deleted theorem, and re-proving it directly would mean
re-materialising the deleted MD induction specialised to `refMachine`. It is gone with §3.

The carrier poles it consumed — `refCompressionCR`, `refSqueezeBindsReachable`,
`refInitStepSeparated` — are KEPT above: they are the standing evidence that each named carrier is
inhabited, which is a fact about the DEFS and survives their consumers. -/

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

/-! ## §5 — TOMBSTONE: the bridge into the commitment tower, DELETED as VACUOUS.

`realizedSpongeOfReduction (M) (hC : CompressionCR M) (hSq : SqueezeBindsReachable M)
(hSep : InitStepSeparated M) : Poseidon2RealizedSponge M.spongeOf` packaged `M.spongeOf` as the bundle
the whole `StateCommit` tower consumes — tagged with the REAL `babyBearD4W16` p3 params, with the
`spongeCR` FIELD filled by §3's `spongeCR_of_reduction` instead of assumed at the sponge level. It was
the object that made the tower's named obligation READ as "ONE permutation call is CR
(`CompressionCR`) + the slot-0 truncation residual" rather than "the unbounded list-hash is
injective". `Reference.refRealizedSpongeOfReduction` was its end-to-end witness on the toy machine and
is deleted with it, for the same reason as `refSpongeCR` in §4.

⚠ Since `hC` is refuted at any fixed-width state
(`Crypto.SpongeCompressionRegrounded.compressionCR_false_of_finite_state`), this constructor was
UNINHABITABLE at deployed parameters: it built a `Poseidon2RealizedSponge` only from an argument no
real sponge can supply. That is the worst shape in the set — an OBJECT, not just a proposition,
advertising a carrier reduction the tower could never actually take delivery of.

**A tower consumer needing the digest-binding fact should take
`Crypto/SpongeCompressionRegrounded.spongeCR_of_reduction_binds_rom` (:874)** — the ROM-discharged
headline (query-boundedness + `PolyBounded` query count ⇒ `Negl`) — and carry the negligible-advantage
statement rather than an injectivity FIELD. A `Poseidon2RealizedSponge` bundle whose `spongeCR` field
is unconditional injectivity cannot be honestly filled at a real sponge by any route; that is a fact
about `Poseidon2Binding`'s bundle shape, and it is where the next repair goes. -/

#assert_axioms Reference.refCompressionCR
#assert_axioms Reference.refInitStepSeparated
#assert_axioms Reference.refSqueezeBindsReachable
#assert_axioms Reference.badMachine_not_squeezeBinds

end Dregg2.Crypto.SpongeReduction
