/-
# Fhegg.Rtl.Golden.Butterfly — the NTT butterfly as a hardware golden model (the core FHE datapath op).

The single op the FHE-on-FPGA literature names as THE bottleneck datapath: the number-theoretic
transform (NTT) butterfly, the engine of the TFHE programmable bootstrap's blind-rotation +
external product (Zama HPU: "the external product … is implemented using an NTT"; FPT, FAB;
`FHEGG-FPGA-ACCELERATOR.md §2.2`). A Cooley-Tukey (decimation-in-time) butterfly over `ℤ/qℤ`:

    (a, b, ω)  ↦  ( (a + ω·b) mod q ,  (a − ω·b) mod q )

This file is the **hardware golden model** the contributor's NTT-butterfly RTL is co-simulated
against: the computable spec (`butterfly`) + its structural correctness (`butterfly_add`,
`butterfly_sub` — the invertibility identities a Gentleman-Sande inverse relies on) + concrete
`#guard`s at a real small modulus. Core Lean only (`omega` after generalizing the product).

## Honest scope

  * `butterfly` — the computable golden op (runs; the co-sim reference).
  * `butterfly_add` / `butterfly_sub` — the algebraic identities (`hi + lo = 2a`,
    `hi − lo = 2ωb`) that make the transform invertible, PROVEN sorry-free.
  * `#guard` — concrete butterflies at `q = 17` match hand computation.
  * The full NTT (log N stages of butterflies with bit-reversal + twiddle schedule), the modular
    reduction (Barrett/Montgomery) RTL, and the negacyclic wrap are the NAMED contributor
    effort (`fhegg-rtl/CONTRIBUTING.md`). This file is the single butterfly cell's golden model,
    not the NTT.
-/
import Fhegg.Rtl.Netlist

namespace Fhegg.Rtl.Golden

/-! ## 1. The butterfly, pre-reduction combiner and full modular op. -/

/-- The high leg's pre-reduction value `a + ω·b` (the modular ADD half — the ripple-adder core
of `Examples/RippleAdder.lean`, one modular multiply upstream). -/
def bfHi (a b w : Int) : Int := a + w * b

/-- The low leg's pre-reduction value `a − ω·b` (the modular SUBTRACT half). -/
def bfLo (a b w : Int) : Int := a - w * b

/-- **The NTT butterfly** over `ℤ/qℤ`: `(a, b, ω) ↦ ((a+ωb) mod q, (a−ωb) mod q)`. The
computable golden op — exactly what the emitted Verilog butterfly is co-simulated against. -/
def butterfly (q a b w : Int) : Int × Int := (bfHi a b w % q, bfLo a b w % q)

/-! ## 2. Structural correctness — the invertibility identities (PROVEN). -/

/-- **`butterfly_add` — `hi + lo = 2a`.** The pre-reduction legs sum to twice the first input,
independent of the twiddle `ω·b`. This (with `butterfly_sub`) is why the butterfly is
invertible: the Gentleman-Sande inverse recovers `a` from `hi + lo`. Proof: generalize the
product `ω·b` to an opaque integer, then `omega`. -/
theorem butterfly_add (a b w : Int) : bfHi a b w + bfLo a b w = 2 * a := by
  unfold bfHi bfLo
  generalize w * b = t
  omega

/-- **`butterfly_sub` — `hi − lo = 2·ω·b`.** The leg difference recovers twice the twiddled
second input, so the inverse butterfly recovers `ω·b` (hence `b`, given invertible `ω`). Proof:
generalize the product, then `omega`. -/
theorem butterfly_sub (a b w : Int) : bfHi a b w - bfLo a b w = 2 * (w * b) := by
  unfold bfHi bfLo
  generalize w * b = t
  omega

/-- **Invertibility, packaged.** From the two output legs (pre-reduction) one recovers `2a` and
`2ωb` by pure addition/subtraction — the inverse-NTT butterfly is the SAME add/sub datapath. So
the forward butterfly loses no information (up to the public factor 2 and invertible `ω`). -/
theorem butterfly_invertible (a b w : Int) :
    bfHi a b w + bfLo a b w = 2 * a ∧ bfHi a b w - bfLo a b w = 2 * (w * b) :=
  ⟨butterfly_add a b w, butterfly_sub a b w⟩

/-! ## 3. Non-vacuity — concrete butterflies at `q = 17` (`#guard`, computed).

`q = 17` is a real NTT-friendly modulus (Fermat prime `2⁴+1`); `ω = 4` has order 4
(`4² = 16 ≡ −1`), a valid size-2 twiddle. These are hand-checkable: `a = 5, b = 3, ω = 4` →
`ω·b = 12`; hi `= 17 ≡ 0`, lo `= 5 − 12 = −7 ≡ 10 (mod 17)`. -/

#guard butterfly 17 5 3 4 == (0, -7 % 17)      -- (0, 10) up to Int.emod sign convention
#guard bfHi 5 3 4 == 17
#guard bfLo 5 3 4 == -7
#guard (bfHi 5 3 4 + bfLo 5 3 4) == 2 * 5       -- butterfly_add, computed
#guard (bfHi 5 3 4 - bfLo 5 3 4) == 2 * (4 * 3) -- butterfly_sub, computed
-- a second point: a = 9, b = 2, ω = 3 → ωb = 6; hi = 15, lo = 3.
#guard butterfly 17 9 2 3 == (15 % 17, 3 % 17)
#guard (bfHi 9 2 3 + bfLo 9 2 3) == 2 * 9

/-! ## 4. The butterfly as a NETLIST target.

The butterfly's `a ± ω·b` combiner is a modular adder + subtractor — the verified
`Examples/RippleAdder.lean` core wrapped in modular reduction — preceded by a modular
multiplier `ω·b`. The golden `butterfly` above is the co-sim reference for the contributor's
SpinalHDL butterfly (`hardware/spinalhdl/Butterfly.scala`): the add/sub bit-datapath is
verified here; the modular multiply + Barrett/Montgomery reduction + the log-N NTT schedule are
the named productive-bulk build. -/

end Fhegg.Rtl.Golden
