/-
# Dregg2.Bridge.TickShifts — **the seven Tick coset `shifts` at `domain_log2 = 16`, DERIVED in Lean
by the Blake2b→field construction, not carried and not extracted.**

## The residual this closes, quoted from the file that named it

`MinaWrapFtEval0Weld` §6:

> the **seven Tick coset `shifts` at `domain_log2 = 16`** … do not exist in this tree in any form.
> They are Blake2b-derived per domain (`kimchi/src/circuits/polynomials/permutation.rs`
> `Shifts::new`), so they are an EXTRACTOR line, not a formalization — but until that line is run,
> the Step side has a wire and no answer.

and, at `MinaWrapDeferredWeld.FT_EVAL0`:

> ⚑⚑ **SOLVED FROM SLOT 0, NOT DERIVED.** `cipOf` is affine in this argument and it enters at
> exactly one index, so this value is whatever makes §4 hold. … Deriving it is
> `KimchiVerify.ftEval0R` over the same `EVALS`, whose own inputs beyond the wire are the seven Tick
> coset `shifts`.

This file is that derivation. It authors `tickShiftsFp`, the `Shifts::new` construction over the
Step field `ZMod pN` (the Pallas base / Vesta scalar prime — the field the Step evaluation domain is
over, pinned by `MinaWrapFtEval0Weld` §6's `rootOfUnity pN 16 == MinaWrapDeferred.rootOfUnity 16`),
and `MinaWrapFtEval0Weld` §6 consumes it: with these shifts `deriveSide S539508` reproduces the
block's own `FT_EVAL0`, which turns the slot-0 (`combined_inner_product`) leg from an arithmetic
identity SOLVED from its slot into a DISCRIMINATION.

## ⚑ SUBSTRATE / verb discipline

No AIR. This file authors no constraint. It is a deterministic value-returning `def` that reuses
`Blake2bGadget.Ref.compress` (dregg's Blake2b-512, KAT-anchored against `hashlib.blake2b`) and
`MinaWrapFtEval0.powFast` (the square-and-multiply ladder) — one body, no twin. The `#guard`s pin
the seven derived values to o1-labs' own `Shifts::new` output (the read-only ORACLE,
`metatheory/fixtures/pickles-extractors/src/bin/tick_shifts_export.rs`) byte-exact. This is
SYNTHESIS fidelity — a MEASURED match, NOT machine-checked soundness: the recursion's security is
still the IPA/FRI floor, unmoved.

## The `Shifts::new` construction (`permutation.rs:149-197`), transcribed

  * `shifts[0] = 1`.
  * a `u32` counter `i` starts at `7`; each sample increments it FIRST, then hashes.
  * `sample`: `Blake2b512(i.to_be_bytes())`, take `digest[..31]`, read it LITTLE-ENDIAN as a field
    element (`F::from_random_bytes`, which for 31 bytes < a 255-bit modulus is exactly `LE(bytes)`).
    Loop while the candidate is NOT a quadratic non-residue OR lies in the domain
    (`shift^n = 1`) — resampling with a fresh incremented `i`.
  * outer loop: reject a candidate that duplicates an already-accepted shift; the counter never
    resets.
  * collect six samples (positions 1..6); prepend `shifts[0] = 1`.

The counter is a single monotone stream `i = 8, 9, 10, …`; a candidate at `i` becomes the next shift
iff it is a QNR, not in the domain, and distinct from the prior shifts. The oracle trace confirms Fp
reaches `i = 22` (accepts at `i ∈ {8,14,19,20,21,22}`); the vanishing check never fires at
`n = 2^16` because a QNR's order is divisible by `2^32 > 2^16`.

NOT rooted in `Dregg2/FFI.lean`: the heavy one-block consumer (`MinaWrapFtEval0Weld`) is off the
archive hot path, and this file only adds `powFast`/`Blake2b` which are already in the closure.
-/
import Dregg2.Circuit.Emit.Blake2bGadget
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Bridge.MinaWrapFtEval0

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.TickShifts

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.Blake2bGadget.Ref (compress h0Default FF)
open Dregg2.Bridge.MinaWrapFtEval0 (powFast)

/-! ## §1 — little-endian byte plumbing, local so the file is self-contained. -/

/-- Little-endian integer of a byte list. Structural, kernel-reducing. -/
def leNat : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leNat bs

/-- The eight little-endian bytes of a 64-bit word. -/
def wordBytesLE (w : Nat) : List Nat := (List.range 8).map (fun i => (w / 256 ^ i) % 256)

/-- Pack message bytes into the sixteen little-endian 64-bit words of one Blake2b block (zero-padded
to 128 bytes). Same shape `MinaBinprot.blockOfBytes` uses, local here. -/
def blockOfBytes (bs : List Nat) : List Nat :=
  (List.range 16).map (fun i => leNat (((bs.drop (i * 8)) ++ List.replicate 8 0).take 8))

/-- The four big-endian bytes of a `u32` counter — `i.to_be_bytes()`. -/
def u32BE (i : Nat) : List Nat :=
  [ (i / 2 ^ 24) % 256, (i / 2 ^ 16) % 256, (i / 2 ^ 8) % 256, i % 256 ]

/-! ## §2 — Blake2b-512 of the four-byte counter, and the field candidate. -/

/-- The 64 digest bytes of `Blake2b512(i.to_be_bytes())`. Single block (4-byte message), counter
`t0 = 4`, final-block flag `f0 = FF`. `compress`/`h0Default` are the Blake2b-512 primitives already
KAT-anchored against `hashlib.blake2b(digest_size=64)` in `Blake2bGadget`. -/
def blake2b512BE4 (i : Nat) : List Nat :=
  (compress h0Default (blockOfBytes (u32BE i)) 4 0 FF 0).flatMap wordBytesLE

/-- The `sample` candidate at counter `i`: `LE(digest[..31])`, exactly `F::from_random_bytes` on a
31-byte slice under a 255-bit modulus (no flag masking, always canonical). -/
def candOf (i : Nat) : Nat := leNat ((blake2b512BE4 i).take 31)

/-! ## §3 — the acceptance predicate over `ZMod pN`. -/

/-- ⚑ `legendre(c).is_qnr()` — `c^{(p-1)/2} = −1`. (`c = 0` gives `0 ≠ −1`; a QR gives `1 ≠ −1`.) -/
def isQNR (c : ZMod pN) : Bool := decide (powFast c ((pN - 1) / 2) = (-1 : ZMod pN))

/-- `domain.evaluate_vanishing_polynomial(c).is_zero()` — `c^n = 1`, i.e. `c` lies in the domain. -/
def inDomain (n : Nat) (c : ZMod pN) : Bool := decide (powFast c n = (1 : ZMod pN))

/-- Duplicate of an already-accepted shift (the outer `while shifts.contains`). The full prior set is
`1 :: acc`; a QNR is never `1` or `0`, so this matches `shifts.contains` exactly. -/
def dup (prior : List (ZMod pN)) (c : ZMod pN) : Bool :=
  ((1 : ZMod pN) :: prior).any (fun s => decide (s = c))

/-- The combined `Shifts::sample` + outer-distinctness acceptance: a QNR, not in the domain, and
distinct from every prior shift. -/
def accept (n : Nat) (prior : List (ZMod pN)) (c : ZMod pN) : Bool :=
  isQNR c && !inDomain n c && !dup prior c

/-! ## §4 — the sampler. Fuel-structural; the counter is a monotone stream from `i = 8`. -/

/-- Collect the six non-identity shifts by scanning `i = start, start+1, …`. `fuel` bounds the scan;
`64` covers Fp's worst case (`i = 22`, fifteen attempts) with margin. -/
def sampleAux (n : Nat) : Nat → Nat → List (ZMod pN) → List (ZMod pN)
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
      if acc.length ≥ 6 then acc
      else
        let c : ZMod pN := ((candOf i : Nat) : ZMod pN)
        if accept n acc c then sampleAux n fuel (i + 1) (acc ++ [c])
        else sampleAux n fuel (i + 1) acc

/-- **`tickShiftsFp domainLog2`** — the seven Tick coset shifts over `ZMod pN`, `shifts[0] = 1`
prepended to the six sampled ones. This is the value `MinaWrapFtEval0Weld` §6's `sh` wants. -/
def tickShiftsFp (domainLog2 : Nat) : List (ZMod pN) :=
  (1 : ZMod pN) :: sampleAux (2 ^ domainLog2) 64 8 []

/-! ## §5 — ⚑ THE PIN: the derived shifts EQUAL o1-labs' `Shifts::new`, byte-exact.

`TICK_SHIFTS_16_ORACLE` is o1-labs' own `Shifts::new(Radix2EvaluationDomain::<Fp>::new(2^16))`
output — `tick_shifts_export`'s `Fp SHIFTS_CSV`, produced on a path that runs kimchi and touches no
Lean. A MEASURED match. -/

/-- The oracle values (READ-ONLY, from `tick_shifts_export`). -/
def TICK_SHIFTS_16_ORACLE : List Nat :=
  [ 1,
    328286983623303317637963920346571898945724874896624808297627776768640590563,
    91433028157768305433241271390810941046493237899366836746431422160024463706,
    240213425742950025341713987028051046476975246675775993287051503548513551377,
    417757293700961807788464308236931191792053554682199437460107260306038610067,
    430348682428487492383428014506756320686619984007091686553051322507181255952,
    326625242707153437805405281465150497418605074624614708160829052937679007395 ]

/-- ⚑⚑ **DERIVED == EXTRACTED.** Seven values, byte-exact against `Shifts::new`.

This is the file's load-bearing claim and it is now a NAMED THEOREM, not a `#guard`. The assertion
is unchanged — same expression, same object, same evaluator: `#guard` is implemented as
`unsafe evalExpr Bool`, exactly the engine `native_decide` runs on (`Dregg2.Tactics`,
`#assert_compiled` §). What the theorem adds is a name §6b can cite, a term in the environment, and
an axiom record — `#assert_compiled` below states out loud that this rests on compiled evaluation,
which the `#guard` rested on just as much while showing nothing. -/
theorem tickShiftsFp_16_matches_oracle :
    (tickShiftsFp 16).map (fun x => x.val) = TICK_SHIFTS_16_ORACLE := by native_decide

/-- …and the derivation really produces seven field elements at the emitted domain. -/
theorem tickShiftsFp_16_length : (tickShiftsFp 16).length = 7 := by native_decide

/-- ⚑ **∀-GAIN.** The identity shift leads the list AT EVERY DOMAIN — the cons is structural, so the
kernel closes this by `rfl` without evaluating one Blake2b block. The `#guard` this replaces asserted
it at `d = 16` only, and paid a full compiled run of the sampler to learn it. -/
theorem tickShiftsFp_getD_zero (d : Nat) : (tickShiftsFp d).getD 0 0 = (1 : ZMod pN) := rfl

/-- The instance the `#guard` asserted, over the same object, now a corollary of the ∀. -/
theorem tickShiftsFp_16_getD_zero : (tickShiftsFp 16).getD 0 0 = (1 : ZMod pN) :=
  tickShiftsFp_getD_zero 16

/-! ### §5b — the field is the STEP field, pinned by the domain generator.

The Fp and Fq `Shifts::new` sequences share only `shifts[1]` and then diverge (the oracle prints
both). This anchor states we took the Fp branch: `rootOfUnity pN 16` is exactly the Radix2 domain
generator `tick_shifts_export` printed as `Fp GROUP_GEN`, so the shifts sit over the same field the
Step domain does. -/
theorem rootOfUnity_pN_16_is_the_step_domain_generator :
    (MinaWrapFtEval0.rootOfUnity pN 16).val =
      15891333241237338948802440868534957611422987089162911289567511717843897011994 := by
  native_decide

/-! ### §5c — the counter mechanics are as transcribed. -/

/-- The first candidate is at `i = 8` and it IS the first non-identity shift (a QNR at the start of
the stream). -/
theorem candOf_8_is_first_shift : candOf 8 = TICK_SHIFTS_16_ORACLE.getD 1 0 := by native_decide

/-- `i = 9` is a quadratic RESIDUE over Fp, so it is rejected — the reason the second shift is not
the next counter. (Over Fq it is accepted; the branch really depends on the field.) -/
theorem candOf_9_is_rejected : isQNR ((candOf 9 : Nat) : ZMod pN) = false := by native_decide

/-- …and the second accepted shift is the `i = 14` candidate, the next QNR. -/
theorem candOf_14_is_second_shift : candOf 14 = TICK_SHIFTS_16_ORACLE.getD 2 0 := by native_decide

/-! ## §5d — ⚑ the STEP `endo_coefficient`, DERIVED (a bonus config the weld was conflating).

`Plonk_checks.Scalars.Tick.constant_term`'s `endomul` body reads `env.endo_coefficient`, which
Pickles sets to `mina_poseidon::sponge::endo_coefficient() = GENERATOR^((p-1)/3)`
(`proof-systems/poseidon/src/sponge.rs:110`; `mina-rust .../scalars.rs:325`) — a primitive cube root
of unity in `Fp`, `5^((p-1)/3)`. It is a DIFFERENT cube root from `er` (the Vesta scalar endo used
for the `ScalarChallenge` lift): the two nontrivial cube roots of `Fp` are exactly these two values.
`MinaWrapFtEval0Weld` §6's Step side set `endo := er := ENDO`, i.e. conflated them — the exact hazard
`MinaWrapFtEval0` §54 warns against ("`endo` … NOT `er`; conflating the two produces a complete,
self-consistent, entirely wrong `linConstTerm`"). This derives the correct one. -/

/-- **`stepEndoCoefficient`** — `GENERATOR^((p-1)/3)`, the endomul gate's `endo_coefficient` on the
Step (Fp) side. Derived, not carried. -/
def stepEndoCoefficient : ZMod pN := powFast ((5 : Nat) : ZMod pN) ((pN - 1) / 3)

/-- ⚑ MEASURED == o1-labs' `mina_poseidon::sponge::endo_coefficient::<Fp>()` (oracle
`tick_shifts_export`, `ENDO Pallas.endos().0`). -/
theorem stepEndoCoefficient_matches_oracle :
    stepEndoCoefficient.val =
      20444556541222657078399132219657928148671392403212669005631716460534733845831 := by
  native_decide

/-- It is a cube root of unity. -/
theorem stepEndoCoefficient_cube : stepEndoCoefficient ^ 3 = (1 : ZMod pN) := by native_decide

/-- ⚑ …and it is NOT `ENDO` — the conflation `MinaWrapFtEval0Weld` §6 committed. -/
theorem stepEndoCoefficient_ne_endo :
    stepEndoCoefficient ≠
      ((8503465768106391777493614032514048814691664078728891710322960303815233784505 : Nat) :
        ZMod pN) := by
  native_decide

/-! ## §6 — structural theorems, and the ∀ facts the single-instance pins were instances of.

⚑ This section used to be headed *"cheap structural theorems for axiom hygiene (the heavy pins stay
`#guard`)"* — a split that put every claim a reader cares about on the side that produces no term
and no axiom record. The heavy pins are now theorems too (§5); what follows is the part that gained
a **∀**. -/

/-- `tickShiftsFp` always leads with the identity shift, WITHOUT evaluating the sampler — the cons is
structural. -/
theorem tickShiftsFp_head (d : Nat) : (tickShiftsFp d).headD 0 = (1 : ZMod pN) := rfl

/-- `u32BE` is exactly four bytes — the `i.to_be_bytes()` width. -/
theorem u32BE_length (i : Nat) : (u32BE i).length = 4 := rfl

/-- A Blake2b block is sixteen 64-bit words. -/
theorem blockOfBytes_length (bs : List Nat) : (blockOfBytes bs).length = 16 := by
  simp [blockOfBytes]

/-- ⚑ **∀-GAIN.** The sampler NEVER overruns its six slots — at every domain size, every fuel, every
starting counter, every accumulator. `#guard (tickShiftsFp 16).length == 7` was one instance of this;
the instance cannot see that the `acc.length ≥ 6` early-out is what bounds the loop, so it could not
distinguish "the bound holds" from "64 fuel happened to run out at seven". -/
theorem sampleAux_length_le (n : Nat) :
    ∀ (fuel i : Nat) (acc : List (ZMod pN)),
      (sampleAux n fuel i acc).length ≤ max acc.length 6
  | 0, _, acc => by simp [sampleAux]
  | fuel + 1, i, acc => by
      rw [sampleAux]
      dsimp only
      split_ifs with h6 hacc
      · exact Nat.le_max_left _ _
      · have ih := sampleAux_length_le n fuel (i + 1) (acc ++ [((candOf i : Nat) : ZMod pN)])
        simp only [List.length_append, List.length_cons, List.length_nil] at ih
        omega
      · exact sampleAux_length_le n fuel (i + 1) acc

/-- ⚑ **∀-GAIN.** `tickShiftsFp` is at most seven shifts at EVERY domain — the `Shifts::new` arity,
proved rather than observed at `d = 16`. -/
theorem tickShiftsFp_length_le (d : Nat) : (tickShiftsFp d).length ≤ 7 := by
  have h := sampleAux_length_le (2 ^ d) 64 8 ([] : List (ZMod pN))
  simp only [List.length_nil] at h
  simp only [tickShiftsFp, List.length_cons]
  omega

/-- ⚑ **∀-GAIN.** The outer distinctness check really rejects a repeat — for every prior set and
every candidate, not just along the one accepted trace the pins walk. This is the `while
shifts.contains` line of `permutation.rs` as a statement about all inputs. -/
theorem dup_of_mem (prior : List (ZMod pN)) (c : ZMod pN) (h : c ∈ prior) :
    dup prior c = true := by
  simp only [dup, List.any_eq_true, List.mem_cons, decide_eq_true_eq]
  exact ⟨c, Or.inr h, rfl⟩

/-- ⚑ **∀-GAIN.** `accept` never admits a duplicate — for every domain, prior set and candidate. -/
theorem accept_not_dup (n : Nat) (prior : List (ZMod pN)) (c : ZMod pN)
    (h : accept n prior c = true) : dup prior c = false := by
  simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

/-- ⚑ **∀-GAIN.** `u32BE` really IS `i.to_be_bytes()` — big-endian, for every `i < 2^32`. NO `#guard`
in this file ever checked the encoder itself; they checked `candOf` at three counters and inherited
the encoding. This states it directly, over all inputs in range. -/
theorem u32BE_bigEndian (i : Nat) (h : i < 2 ^ 32) :
    (u32BE i).foldl (fun a b => a * 256 + b) 0 = i := by
  simp only [u32BE, List.foldl_cons, List.foldl_nil]
  omega

#assert_axioms tickShiftsFp_head
#assert_axioms tickShiftsFp_getD_zero
#assert_axioms tickShiftsFp_16_getD_zero
#assert_axioms u32BE_length
#assert_axioms u32BE_bigEndian
#assert_axioms blockOfBytes_length
#assert_axioms sampleAux_length_le
#assert_axioms tickShiftsFp_length_le
#assert_axioms dup_of_mem
#assert_axioms accept_not_dup

/-! ### §6b — the compiled pins, ACCOUNTED FOR.

⚑ Each name below was a `#guard` and is now a theorem resting on a `native_decide` oracle axiom.
`#assert_compiled` states that out loud: the fact is true by compiled evaluation — which is exactly
what the `#guard` was, with the axiom record deleted. Nothing here got weaker; the trust got
VISIBLE. If any of these ever becomes kernel-reachable, `#assert_compiled` REFUSES it and demands
the stronger `#assert_axioms` — the ratchet points the right way. -/
#assert_compiled tickShiftsFp_16_matches_oracle
#assert_compiled tickShiftsFp_16_length
#assert_compiled rootOfUnity_pN_16_is_the_step_domain_generator
#assert_compiled candOf_8_is_first_shift
#assert_compiled candOf_9_is_rejected
#assert_compiled candOf_14_is_second_shift
#assert_compiled stepEndoCoefficient_matches_oracle
#assert_compiled stepEndoCoefficient_cube
#assert_compiled stepEndoCoefficient_ne_endo

end Dregg2.Bridge.TickShifts
