/-
# `Dregg2.Bridge.MinaPackInjective` — **`pack_to_fields` IS INJECTIVE, AND THE RANGE HYPOTHESIS IS
THE WHOLE OF WHY.**

## ⚑ SUBSTRATE

This file authors **NO AIR**. It is a theorem about the `List (Nat × Nat) → List Nat` function
`MinaStateHashDerive.packToFields` — itself a transcription of `random_oracle_input.ml:59-75` and
openmina's `poseidon/src/hash.rs:139-163`. The emitted gate that DISCHARGES the hypothesis proved
here is `Circuit.Emit.MinaBodyPreimageBitsAir`, and it is Lean-authored (House Law #1).

## ⚑⚑ THE HOLE THIS CLOSES, AND IT IS AN ALIASING

`MinaStateBodyHashChain` §8 residual 2 named it:

> *"nothing gates that they are the packing of 819 width-declared chunks, and in particular
> **nothing forces each chunk `< 2^n`**, without which the packing is not injective."*

Not injective is not a figure of speech. `packStep` computes `acc := acc · 2^n + x` and never looks
at `x`, so an over-wide `x` spills into the bits its predecessor occupies:

    packToFields ⟨[], [(1, 1), (0, 1)]⟩ = [2] = packToFields ⟨[], [(0, 1), (2, 1)]⟩

Two different bodies, the SAME 49 absorbed field elements, therefore the same `state_body_hash`,
therefore the same 25-link chain, therefore the same root — **and every link honest.** That is the
family this campaign has closed five times, and `the_range_hypothesis_is_load_bearing` below is it
exhibited rather than described.

## ⚑ WHAT IS PROVED, AND ABOUT WHICH OBJECT

`packing_is_injective` is about **`packToFields` on `Inp`** — a pair of streams, whole field
elements and `(value, width)` chunks. It says: fix the FIELD stream, fix the WIDTH SCHEDULE, put
every chunk below its declared width; then the packed output determines the chunk stream.

Three hypotheses, and each is refuted below when dropped, so none of them is decoration:

  * ⚑ **the range** — `the_range_hypothesis_is_load_bearing` (the alias above);
  * ⚑ **the width schedule** — `the_schedule_hypothesis_is_load_bearing`: `[(1,1)]` and `[(1,2)]`
    are both in range and both pack to `[1]`. A prover who may DECLARE the widths chooses the
    reading, which is why the emitted gate bakes the schedule in as shape rather than witnessing it;
  * ⚑ **positive widths** — `the_positive_width_hypothesis_is_load_bearing`: a zero-width chunk is
    a value the packing never emits. Mina's schedule has none (every width is 1, 32 or 64,
    `MinaStateHashPackPrice.the_chunk_widths_are_almost_all_boolean`), and this is the one
    hypothesis that is a SHAPE fact rather than a gate.

⚠ **AND WHAT IT IS NOT ABOUT.** It says nothing about the 38 whole field elements: those pass
through `packToFields` untouched, are not chunked, and have no width to declare. Injectivity of the
packing constrains the 2 381 bits of the CHUNK stream and not one bit of the field stream. Said in
the units the campaign uses: of a `Protocol_state.Body` preimage, this rung is about the 2 381 bits
and `MinaBodyPreimageBitsAir` gates all 2 381 of them; the 38 field elements are a separate
question and remain what `PICKLES_OPENING_WITNESSED` covers.

## Import line for the root: `import Dregg2.Bridge.MinaPackInjective`
-/
import Dregg2.Bridge.MinaStateHashPackPrice

namespace Dregg2.Bridge.MinaPackInjective

open Dregg2.Bridge.MinaStateHashDerive

set_option autoImplicit false

/-! ## §1 — the two predicates the gate discharges, and the arithmetic under one step. -/

/-- ⚑ **THE RANGE PREDICATE — the thing no circuit forced until `MinaBodyPreimageBitsAir`.** Every
chunk strictly below its DECLARED width. -/
def InRange (ps : List (Nat × Nat)) : Prop := ∀ p ∈ ps, p.1 < 2 ^ p.2

/-- Widths are positive. ⚠ A SHAPE fact about `Body.to_input`, not a gate: Mina declares 1, 32 and
64 and nothing else. -/
def PositiveWidths (ps : List (Nat × Nat)) : Prop := ∀ p ∈ ps, 0 < p.2

/-- The declared width schedule of a chunk stream. -/
def widths (ps : List (Nat × Nat)) : List Nat := ps.map Prod.snd

/-- `packStep` with its `let` and its pattern match opened, so every proof below rewrites rather
than unfolds. -/
theorem packStep_def (out : List Nat) (acc accN x n : Nat) :
    packStep (out, acc, accN) (x, n)
      = if n + accN < fieldSizeInBits then (out, acc * 2 ^ n + x, n + accN)
        else (out ++ [acc], x, n) := rfl

/-- ⚑ **THE INVARIANT.** An accumulator that fits its width, extended by a chunk that fits ITS
width, fits the sum. This is the whole reason the range hypothesis is what injectivity needs. -/
theorem acc_bound {acc accN x n : Nat} (ha : acc < 2 ^ accN) (hx : x < 2 ^ n) :
    acc * 2 ^ n + x < 2 ^ (n + accN) := by
  have h1 : acc + 1 ≤ 2 ^ accN := ha
  calc acc * 2 ^ n + x < acc * 2 ^ n + 2 ^ n := by omega
    _ = (acc + 1) * 2 ^ n := by ring
    _ ≤ 2 ^ accN * 2 ^ n := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (n + accN) := by rw [Nat.pow_add]; ring

/-- ⚑ **ONE STEP IS INJECTIVE — GIVEN THE RANGE.** `acc · 2^n + x` recovers both halves exactly
when `x` is below `2^n`; without that the two halves are not separable, which is the alias. -/
theorem step_injective {a b x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : a * 2 ^ n + x = b * 2 ^ n + y) : a = b ∧ x = y := by
  have hpos : 0 < 2 ^ n := by positivity
  have hmodx : (a * 2 ^ n + x) % 2 ^ n = x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have hmody : (b * 2 ^ n + y) % 2 ^ n = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have hxy : x = y := by rw [← hmodx, ← hmody, h]
  subst hxy
  have hmul : a * 2 ^ n = b * 2 ^ n := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hpos hmul, rfl⟩

/-! ## §2 — the fold's OUTPUT list is a suffix-independent function of its state.

⚑ The bridge the injectivity induction needs: `packStep` only ever APPENDS to `out`, so a fold from
`out` is `out ++` a fold from `[]`. Without this the induction's step case compares two `out ++ [a]`
prefixes it cannot take apart. -/

theorem fold_out_prefix : ∀ (ps : List (Nat × Nat)) (out : List Nat) (a n : Nat),
    ps.foldl packStep (out, a, n)
      = (out ++ (ps.foldl packStep ([], a, n)).1, (ps.foldl packStep ([], a, n)).2) := by
  intro ps
  induction ps with
  | nil => intro out a n; simp
  | cons p rest ih =>
    intro out a n
    obtain ⟨x, w⟩ := p
    rw [List.foldl_cons, List.foldl_cons, packStep_def, packStep_def]
    by_cases hb : w + n < fieldSizeInBits
    · simp only [hb, if_true]
      exact ih out (a * 2 ^ w + x) (w + n)
    · simp only [hb, if_false, List.nil_append]
      rw [ih (out ++ [a]) x w, ih [a] x w]
      simp [List.append_assoc]

/-! ## §3 — ⚑⚑⚑ THE FOLD IS INJECTIVE ON IN-RANGE STREAMS OF A FIXED SCHEDULE. -/

/-- ⚑ **THE SHAPE HALF, AND IT IS THE `the_packing_control_flow_reads_only_the_width` FACT PUSHED
THROUGH THE WHOLE FOLD.** Two streams with the same width schedule leave the fold with the same
accumulator WIDTH and the same number of emitted elements, whatever their values. -/
theorem fold_shape : ∀ (ps qs : List (Nat × Nat)) (a b n : Nat),
    widths ps = widths qs →
    (ps.foldl packStep ([], a, n)).1.length = (qs.foldl packStep ([], b, n)).1.length
      ∧ (ps.foldl packStep ([], a, n)).2.2 = (qs.foldl packStep ([], b, n)).2.2 := by
  intro ps
  induction ps with
  | nil =>
    intro qs a b n hw
    cases qs with
    | nil => simp
    | cons q rest => simp [widths] at hw
  | cons p rest ih =>
    intro qs a b n hw
    cases qs with
    | nil => simp [widths] at hw
    | cons q qrest =>
      obtain ⟨x, w⟩ := p
      obtain ⟨y, v⟩ := q
      have hwv : w = v := by simpa [widths] using congrArg (fun l => l.headD 0) hw
      have hrest : widths rest = widths qrest := by
        simpa [widths] using congrArg List.tail hw
      subst hwv
      rw [List.foldl_cons, List.foldl_cons, packStep_def, packStep_def]
      by_cases hb : w + n < fieldSizeInBits
      · simp only [hb, if_true]
        exact ih qrest (a * 2 ^ w + x) (b * 2 ^ w + y) (w + n) hrest
      · simp only [hb, if_false, List.nil_append]
        rw [fold_out_prefix rest [a] x w, fold_out_prefix qrest [b] y w]
        have := ih qrest x y w hrest
        simpa using this

/-- ⚑⚑⚑ **THE FOLD IS INJECTIVE.** Same schedule, same starting width, both accumulators in range,
both streams in range: equal fold results force equal accumulators AND equal streams — chunk value
by chunk value, not merely element by element. -/
theorem fold_injective : ∀ (ps qs : List (Nat × Nat)) (a b n : Nat),
    widths ps = widths qs → InRange ps → InRange qs → a < 2 ^ n → b < 2 ^ n →
    ps.foldl packStep ([], a, n) = qs.foldl packStep ([], b, n) →
    a = b ∧ ps = qs := by
  intro ps
  induction ps with
  | nil =>
    intro qs a b n hw _ _ _ _ h
    cases qs with
    | nil => exact ⟨by simpa using congrArg (fun t => t.2.1) h, rfl⟩
    | cons q rest => simp [widths] at hw
  | cons p rest ih =>
    intro qs a b n hw hp hq ha hb h
    cases qs with
    | nil => simp [widths] at hw
    | cons q qrest =>
      obtain ⟨x, w⟩ := p
      obtain ⟨y, v⟩ := q
      have hwv : w = v := by simpa [widths] using congrArg (fun l => l.headD 0) hw
      have hrest : widths rest = widths qrest := by
        simpa [widths] using congrArg List.tail hw
      subst hwv
      have hx : x < 2 ^ w := hp (x, w) (by simp)
      have hy : y < 2 ^ w := hq (y, w) (by simp)
      have hpr : InRange rest := fun r hr => hp r (by simp [hr])
      have hqr : InRange qrest := fun r hr => hq r (by simp [hr])
      rw [List.foldl_cons, List.foldl_cons, packStep_def, packStep_def] at h
      by_cases hbnd : w + n < fieldSizeInBits
      · simp only [hbnd, if_true] at h
        obtain ⟨hacc, hlists⟩ :=
          ih qrest (a * 2 ^ w + x) (b * 2 ^ w + y) (w + n) hrest hpr hqr
            (acc_bound ha hx) (acc_bound hb hy) h
        obtain ⟨hab, hxy⟩ := step_injective hx hy hacc
        exact ⟨hab, by rw [hxy, hlists]⟩
      · simp only [hbnd, if_false, List.nil_append] at h
        rw [fold_out_prefix rest [a] x w, fold_out_prefix qrest [b] y w] at h
        have h1 : a = b := by
          have := congrArg (fun t => t.1.headD 0) h
          simpa using this
        have h2 : rest.foldl packStep ([], x, w) = qrest.foldl packStep ([], y, w) := by
          have hfst := congrArg (fun t => t.1) h
          have hsnd := congrArg (fun t => t.2) h
          simp only [h1] at hfst
          refine Prod.ext ?_ ?_
          · simpa using hfst
          · simpa using hsnd
        obtain ⟨hxy, hlists⟩ := ih qrest x y w hrest hpr hqr hx hy h2
        exact ⟨h1, by rw [hxy, hlists]⟩

/-! ## §4 — ⚑⚑⚑ AND THEREFORE `pack_to_fields` IS INJECTIVE. -/

/-- The fold's accumulator width is positive as soon as the stream is non-empty and its widths are.
⚑ This is what stops the final `if accN > 0` from silently DISCARDING an accumulator — the one
place `packToFields` can lose information, and the reason `PositiveWidths` is a hypothesis rather
than an omission. -/
theorem fold_accN_pos : ∀ (ps : List (Nat × Nat)) (a n : Nat),
    PositiveWidths ps → ps ≠ [] → 0 < (ps.foldl packStep ([], a, n)).2.2 := by
  intro ps
  induction ps with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons p rest ih =>
    intro a n hpos _
    obtain ⟨x, w⟩ := p
    have hw : 0 < w := hpos (x, w) (by simp)
    have hrest : PositiveWidths rest := fun r hr => hpos r (by simp [hr])
    rw [List.foldl_cons, packStep_def]
    cases hne : rest with
    | nil =>
      subst hne
      by_cases hb : w + n < fieldSizeInBits
      · simp only [hb, if_true, List.foldl_nil]
        show 0 < w + n
        omega
      · simp only [hb, if_false, List.foldl_nil]
        show 0 < w
        omega
    | cons r rs =>
      have hne' : (r :: rs) ≠ [] := by simp
      by_cases hb : w + n < fieldSizeInBits
      · simp only [hb, if_true]
        exact hne ▸ ih (a * 2 ^ w + x) (w + n) (hne ▸ hrest) (hne ▸ hne')
      · simp only [hb, if_false]
        rw [fold_out_prefix]
        exact hne ▸ ih x w (hne ▸ hrest) (hne ▸ hne')

/-- ⚑⚑⚑ **`pack_to_fields` IS INJECTIVE ON IN-RANGE CHUNK STREAMS OF A FIXED SCHEDULE.**

Given the same field stream and the same declared widths, two chunk streams that both respect their
declared widths and pack to the same list of field elements ARE the same stream. This is the
statement that turns the eleven packed field elements the body-hash chain absorbs into a faithful
encoding of 2 381 bits — and it is FALSE without the range hypothesis, which is why
`MinaBodyPreimageBitsAir` exists. -/
theorem packing_is_injective (a b : Inp)
    (hf : a.fields = b.fields) (hw : widths a.packeds = widths b.packeds)
    (hpa : InRange a.packeds) (hpb : InRange b.packeds)
    (hwa : PositiveWidths a.packeds) (hwb : PositiveWidths b.packeds)
    (h : packToFields a = packToFields b) : a = b := by
  obtain ⟨fa, pa⟩ := a
  obtain ⟨fb, pb⟩ := b
  simp only at hf hw hpa hpb hwa hwb h
  subst hf
  -- the two folds
  set A := pa.foldl packStep ([], 0, 0) with hA
  set B := pb.foldl packStep ([], 0, 0) with hB
  obtain ⟨hlen, haccN⟩ := fold_shape pa pb 0 0 0 hw
  rw [← hA, ← hB] at hlen haccN
  -- strip the common field stream
  rw [packToFields, packToFields, ← hA, ← hB] at h
  have htail : (if A.2.2 > 0 then A.1 ++ [A.2.1] else A.1)
      = (if B.2.2 > 0 then B.1 ++ [B.2.1] else B.1) := by
    exact List.append_cancel_left h
  have hAB : A = B := by
    by_cases hz : A.2.2 > 0
    · have hz' : B.2.2 > 0 := by omega
      simp only [hz, hz', if_true] at htail
      obtain ⟨h1, h2⟩ := List.append_inj htail hlen
      refine Prod.ext h1 (Prod.ext ?_ haccN)
      simpa using congrArg (fun l => l.headD 0) h2
    · -- both accumulator widths are zero, so both streams are EMPTY (positive widths)
      have hz' : ¬ B.2.2 > 0 := by omega
      have hpaNil : pa = [] := by
        by_contra hne
        exact hz (hA ▸ fold_accN_pos pa 0 0 hwa hne)
      have hpbNil : pb = [] := by
        by_contra hne
        exact hz' (hB ▸ fold_accN_pos pb 0 0 hwb hne)
      rw [hA, hB, hpaNil, hpbNil]
  have hstreams : (0 : Nat) = 0 ∧ pa = pb :=
    fold_injective pa pb 0 0 0 hw hpa hpb (by norm_num) (by norm_num) (hA ▸ hB ▸ hAB)
  rw [hstreams.2]

/-! ## §5 — ⚑ AND EACH HYPOTHESIS IS REFUTABLE, SO NONE OF THEM IS DECORATION.

A floor must be SATISFIABLE and REFUTABLE. Each theorem below drops exactly one hypothesis of
`packing_is_injective` and exhibits the collision that follows. -/

/-- ⚑⚑ **THE RANGE HYPOTHESIS IS LOAD-BEARING — THIS IS THE ALIAS.** Two chunk streams, the SAME
one-bit width schedule, the SAME packed output, and the only difference is that the second declares
one bit and supplies two. A `state_body_hash` over either is the same felt.

⚠ **THIS IS THE THEOREM THAT SAYS THE CHAIN ALONE ATTESTED THE WRONG THING.** Every one of the 25
links stays honest under this substitution: the absorbed elements are identical. -/
theorem the_range_hypothesis_is_load_bearing :
    packToFields ⟨[], [(1, 1), (0, 1)]⟩ = packToFields ⟨[], [(0, 1), (2, 1)]⟩
      ∧ widths [(1, 1), (0, 1)] = widths [(0, 1), (2, 1)]
      ∧ (⟨[], [(1, 1), (0, 1)]⟩ : Inp) ≠ ⟨[], [(0, 1), (2, 1)]⟩
      ∧ InRange [(1, 1), (0, 1)]
      ∧ ¬ InRange [(0, 1), (2, 1)] := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro p hp
    fin_cases hp <;> decide
  · intro hc
    have := hc (2, 1) (by simp)
    simp at this

/-- ⚑ **THE SCHEDULE HYPOTHESIS IS LOAD-BEARING.** Both streams are in range, both have positive
widths, both pack to `[1]` — and they declare different widths. So a prover who may CHOOSE the
widths chooses the reading of the bits, which is why `MinaBodyPreimageBitsAir` bakes the schedule
in as descriptor SHAPE and witnesses only the bits. -/
theorem the_schedule_hypothesis_is_load_bearing :
    packToFields ⟨[], [(1, 1)]⟩ = packToFields ⟨[], [(1, 2)]⟩
      ∧ widths [(1, 1)] ≠ widths [(1, 2)]
      ∧ InRange [(1, 1)] ∧ InRange [(1, 2)] := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> (intro p hp; fin_cases hp; decide)

/-- ⚑ **AND THE POSITIVE-WIDTH HYPOTHESIS IS LOAD-BEARING** — a zero-width chunk is a value the
packing never emits, so it aliases with its own absence. ⚠ Unlike the other two this one is a SHAPE
fact and not a gate: `Body.to_input` declares 1, 32 and 64 and nothing else
(`MinaStateHashPackPrice.the_chunk_widths_are_almost_all_boolean`). -/
theorem the_positive_width_hypothesis_is_load_bearing :
    packToFields ⟨[], [(0, 0)]⟩ = packToFields ⟨[], []⟩
      ∧ (⟨[], [(0, 0)]⟩ : Inp) ≠ ⟨[], []⟩
      ∧ InRange [(0, 0)]
      ∧ ¬ PositiveWidths [(0, 0)] := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro p hp; fin_cases hp; decide
  · intro hc
    have := hc (0, 0) (by simp)
    simp at this

/-- ⚑ **AND THE THEOREM IS NOT VACUOUS ON THE REAL BLOCK.** The devnet block's own chunk stream
satisfies both hypotheses, so `packing_is_injective` applies to the object the body-hash chain
actually absorbs rather than to an empty premise. -/
theorem the_real_block_stream_satisfies_the_hypotheses :
    InRange Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds
      ∧ PositiveWidths Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds := by
  constructor
  · have h : (Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds.all
        (fun p => decide (p.1 < 2 ^ p.2))) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this
  · have h : (Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds.all
        (fun p => decide (0 < p.2))) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this

/-! ## §6 — ⚑⚑⚑ THE BRIDGE: A BOOLEANITY GATE **IS** THE RANGE HYPOTHESIS.

⚠ Without this section `packing_is_injective` is a theorem whose hypothesis nothing discharges —
the honest-label sin, one layer down. `Circuit.Emit.MinaBodyPreimageBitsAir` emits `x·(x−1) = 0` on
every one of the 2 381 bit columns of the packed preimage and NOTHING ELSE about their values; what
turns that into `InRange` is `the_boolean_gates_force_the_range`, and it is general over every
slicing of every bit vector. -/

/-- A bit list read **MSB-first** — the order `packStep`'s `acc · 2^n + x` places a chunk in. -/
def bitsToNat (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 2 + b) 0

theorem foldl_bits_from : ∀ (bs : List Nat) (a : Nat),
    bs.foldl (fun acc b => acc * 2 + b) a = a * 2 ^ bs.length + bitsToNat bs := by
  intro bs
  induction bs with
  | nil => intro a; simp [bitsToNat]
  | cons b rest ih =>
    intro a
    have hb : bitsToNat (b :: rest) = b * 2 ^ rest.length + bitsToNat rest := by
      rw [bitsToNat, List.foldl_cons, ih]; simp
    rw [List.foldl_cons, ih, hb]
    simp only [List.length_cons, pow_succ]
    ring

/-- ⚑⚑ **A BIT SLICE FITS ITS OWN LENGTH.** The whole arithmetic content of "a booleanity gate is a
declared-width gate": `n` boolean columns cannot denote a value `≥ 2^n`, whatever the prover writes,
because there is nowhere for the value to come from. -/
theorem bitsToNat_lt : ∀ (bs : List Nat), (∀ b ∈ bs, b ≤ 1) → bitsToNat bs < 2 ^ bs.length := by
  intro bs
  induction bs with
  | nil => intro _; simp [bitsToNat]
  | cons b rest ih =>
    intro h
    have hb : b ≤ 1 := h b (by simp)
    have hr : bitsToNat rest < 2 ^ rest.length := ih (fun x hx => h x (by simp [hx]))
    have hmul : b * 2 ^ rest.length ≤ 2 ^ rest.length := by
      simpa using Nat.mul_le_mul_right (2 ^ rest.length) hb
    have hcons : bitsToNat (b :: rest) = b * 2 ^ rest.length + bitsToNat rest := by
      rw [bitsToNat, List.foldl_cons, foldl_bits_from]; simp
    rw [hcons]
    simp only [List.length_cons, pow_succ]
    omega

/-- The chunk stream a SLICING of a bit vector denotes: each slice is one chunk, its LENGTH is that
chunk's declared width. ⚑ The declared width is the slice's length and therefore a SHAPE constant of
the emitted descriptor — not a witness, which is what
`the_schedule_hypothesis_is_load_bearing` says it must not be. -/
def chunksOfSlices (slices : List (List Nat)) : List (Nat × Nat) :=
  slices.map (fun s => (bitsToNat s, s.length))

/-- The declared schedule of a sliced bit vector is the slice lengths — so two bit vectors sliced the
SAME way carry the same schedule by construction, with nothing witnessed. -/
theorem widths_of_slices (slices : List (List Nat)) :
    widths (chunksOfSlices slices) = slices.map List.length := by
  simp [widths, chunksOfSlices, List.map_map, Function.comp_def]

/-- ⚑⚑⚑ **THE BOOLEANITY GATES FORCE THE RANGE.** This is the theorem that connects the emitted
`x·(x−1) = 0` on 2 381 columns to `packing_is_injective`'s hypothesis. General: every slicing, every
bit vector. -/
theorem the_boolean_gates_force_the_range (slices : List (List Nat))
    (h : ∀ s ∈ slices, ∀ b ∈ s, b ≤ 1) : InRange (chunksOfSlices slices) := by
  intro p hp
  simp only [chunksOfSlices, List.mem_map] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  exact bitsToNat_lt s (h s hs)

/-- ⚑⚑⚑ **AND THEREFORE THE GATED BITS ARE DETERMINED BY THE PACKED OUTPUT.** Two boolean bit
vectors, sliced by the SAME schedule of positive-length slices, whose packings agree, denote the
SAME chunk stream. Said in the units this campaign uses: the eleven packed field elements the
body-hash chain absorbs pin all 2 381 bits, and pin them exactly once.

⚠ **AND SAY WHICH OBJECT.** This is about the CHUNK stream. The `fields` argument rides through
untouched on both sides: the 38 whole field elements of a `Protocol_state.Body` are not chunked, have
no declared width, and are not constrained by anything here. -/
theorem the_gated_bits_are_determined_by_the_packing (fields : List Nat)
    (sa sb : List (List Nat))
    (hsched : sa.map List.length = sb.map List.length)
    (hba : ∀ s ∈ sa, ∀ b ∈ s, b ≤ 1) (hbb : ∀ s ∈ sb, ∀ b ∈ s, b ≤ 1)
    (hpa : ∀ s ∈ sa, 0 < s.length) (hpb : ∀ s ∈ sb, 0 < s.length)
    (h : packToFields ⟨fields, chunksOfSlices sa⟩ = packToFields ⟨fields, chunksOfSlices sb⟩) :
    chunksOfSlices sa = chunksOfSlices sb := by
  have hw : widths (chunksOfSlices sa) = widths (chunksOfSlices sb) := by
    rw [widths_of_slices, widths_of_slices, hsched]
  have hpos : ∀ (sl : List (List Nat)), (∀ s ∈ sl, 0 < s.length) →
      PositiveWidths (chunksOfSlices sl) := by
    intro sl hsl p hp
    simp only [chunksOfSlices, List.mem_map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    exact hsl s hs
  have := packing_is_injective ⟨fields, chunksOfSlices sa⟩ ⟨fields, chunksOfSlices sb⟩ rfl hw
    (the_boolean_gates_force_the_range sa hba) (the_boolean_gates_force_the_range sb hbb)
    (hpos sa hpa) (hpos sb hpb) h
  exact congrArg Inp.packeds this

#assert_axioms packStep_def
#assert_axioms acc_bound
#assert_axioms step_injective
#assert_axioms fold_out_prefix
#assert_axioms fold_shape
#assert_axioms fold_injective
#assert_axioms fold_accN_pos
#assert_axioms packing_is_injective
#assert_axioms the_range_hypothesis_is_load_bearing
#assert_axioms the_schedule_hypothesis_is_load_bearing
#assert_axioms the_positive_width_hypothesis_is_load_bearing
#assert_axioms foldl_bits_from
#assert_axioms bitsToNat_lt
#assert_axioms widths_of_slices
#assert_axioms the_boolean_gates_force_the_range
#assert_axioms the_gated_bits_are_determined_by_the_packing

-- ⚑ COMPILER-TRUSTED, and said out loud: this one reduces the 1 544-byte binprot parse, a two-block
-- SHA-256 and an 819-chunk tally — the same object `MinaStateHashPackPrice` measures compiled.
#assert_compiled the_real_block_stream_satisfies_the_hypotheses

end Dregg2.Bridge.MinaPackInjective
