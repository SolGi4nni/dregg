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

/- ⚑⚑ **DERIVED == EXTRACTED.** Seven values, byte-exact against `Shifts::new`. -/
#guard (tickShiftsFp 16).map (fun x => x.val) == TICK_SHIFTS_16_ORACLE

/- …and the derivation really produces seven distinct field elements. -/
#guard (tickShiftsFp 16).length == 7
#guard (tickShiftsFp 16).getD 0 0 == (1 : ZMod pN)

/-! ### §5b — the field is the STEP field, pinned by the domain generator.

The Fp and Fq `Shifts::new` sequences share only `shifts[1]` and then diverge (the oracle prints
both). This anchor states we took the Fp branch: `rootOfUnity pN 16` is exactly the Radix2 domain
generator `tick_shifts_export` printed as `Fp GROUP_GEN`, so the shifts sit over the same field the
Step domain does. -/
#guard (MinaWrapFtEval0.rootOfUnity pN 16).val ==
  15891333241237338948802440868534957611422987089162911289567511717843897011994

/-! ### §5c — the counter mechanics are as transcribed. -/

/- The first candidate is at `i = 8` and it IS the first non-identity shift (a QNR at the start of
the stream). -/
#guard candOf 8 == TICK_SHIFTS_16_ORACLE.getD 1 0
/- `i = 9` is a quadratic RESIDUE over Fp, so it is rejected — the reason the second shift is not the
next counter. (Over Fq it is accepted; the branch really depends on the field.) -/
#guard (isQNR ((candOf 9 : Nat) : ZMod pN)) == false
/- …and the second accepted shift is the `i = 14` candidate, the next QNR. -/
#guard candOf 14 == TICK_SHIFTS_16_ORACLE.getD 2 0

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

/- ⚑ MEASURED == o1-labs' `mina_poseidon::sponge::endo_coefficient::<Fp>()` (oracle
`tick_shifts_export`, `ENDO Pallas.endos().0`). It is a cube root of unity, and NOT `ENDO`. -/
#guard stepEndoCoefficient.val ==
  20444556541222657078399132219657928148671392403212669005631716460534733845831
#guard stepEndoCoefficient ^ 3 == (1 : ZMod pN)
#guard stepEndoCoefficient !=
  ((8503465768106391777493614032514048814691664078728891710322960303815233784505 : Nat) : ZMod pN)

/-! ## §6 — cheap structural theorems for axiom hygiene (the heavy pins stay `#guard`). -/

/-- `tickShiftsFp` always leads with the identity shift, WITHOUT evaluating the sampler — the cons is
structural. -/
theorem tickShiftsFp_head (d : Nat) : (tickShiftsFp d).headD 0 = (1 : ZMod pN) := rfl

/-- `u32BE` is exactly four bytes — the `i.to_be_bytes()` width. -/
theorem u32BE_length (i : Nat) : (u32BE i).length = 4 := rfl

/-- A Blake2b block is sixteen 64-bit words. -/
theorem blockOfBytes_length (bs : List Nat) : (blockOfBytes bs).length = 16 := by
  simp [blockOfBytes]

#assert_axioms tickShiftsFp_head
#assert_axioms u32BE_length
#assert_axioms blockOfBytes_length

end Dregg2.Bridge.TickShifts
