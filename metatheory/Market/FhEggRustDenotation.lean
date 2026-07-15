/-
# Market.FhEggRustDenotation — the fixed fhEgg Rust denotes the Lean argmax clearing.

This file is the aggregate-boundary correspondence audit for the post-fix implementations in
`fhegg-fhe/src/{lib.rs,mpc.rs,additive.rs}`.  All five stale negative residuals are CLOSED at their
honest observable scope:

* `FhEggCrossingDenotation`: the plaintext Rust strict-increase scan is the Lean
  `argmaxUpto`/`crossing` scan, including the lowest-price tie-break.  The worked book is `(1,8)` and
  the old counter-witness is now also `(1,9)` on both sides.
* `FhEggTfheWidthDenotation`: the encrypted aggregates are `FheUint32`; two 32768-lot bids and asks
  aggregate to 65536 and clear at `(0,65536)` rather than wrapping at `2^16`.
* `FhEggTfheNoCrossDenotation`: a genuinely non-clearing book (bids and no asks) produces
  `(None,0)` on both paths.  The old bucket-zero sentinel behavior is absent.
* `MpcCrossingRevealOnlyDenotation`: the input-dependent transcript of `mpc_crossing` factors through
  only `(p*,V*)`; its remaining opened Beaver values are represented explicitly as the independent
  mask stream supplied to both the real view and simulator.  No sign vector or curve height is in the
  modeled view.
* `MpcCrossingDenotation`: the MPC secure-min plus oblivious strict argmax reveals the same encoded
  Lean clearing.

Two scope boundaries remain explicit.  First, Lean quantities are unbounded integers while both Rust
aggregate paths use `u32`; correspondence to the unbounded Lean clearing therefore assumes
`AggregatesFitU32`.  Per-order `Qty = u16` alone does not imply that aggregate bound.  Second, this file
proves the decrypted/plaintext observable semantics, not correctness of tfhe-rs ciphertext evaluation.
`FhEggTfheCiphertextRefinementResidual` names the exact missing implementation relation.  No theorem
below claims that relation.

`fhe_clear` itself is the single-`ClientKey` benchmark harness.  A holder of that key is omniscient if
given intermediate ciphertexts; it is not the no-viewer deployment.  The no-viewer claim here is scoped
to `mpc.rs::mpc_crossing`, whose deployed transcript opens only `(p*,V*)` plus one-time-pad-masked Beaver
values and has the matching `simulate` construction.

Pure.  No axioms.
-/
import Market.MpcClearingSecurity
import Dregg2.Tactics

namespace Market.FhEggRustDenotation

open Market

set_option autoImplicit false

/-! ## 1. The fixed plaintext Rust reference is the Lean volume argmax. -/

/-- The public result shared by `reference_clear`, `fhe_clear`, and `mpc_crossing`.
`None` is the Rust encoding of a zero-volume (non-clearing) book. -/
structure ClearingOutput where
  pStar : Option Nat
  vStar : Int
  deriving DecidableEq, Repr

/-- The modulus of Rust/tfhe-rs `u32` aggregate arithmetic. -/
def u32Modulus : Int := 4294967296

/-- The deployed release-level value semantics of a `u32` aggregate. -/
def u32Residue (x : Int) : Int := x % u32Modulus

/-- Plaintext Rust demand after aggregation into `Vec<u32>`. -/
def rustDemand (bk : OrderBook) (p : Nat) : Int := u32Residue (demand bk p)

/-- Plaintext Rust supply after aggregation into `Vec<u32>`. -/
def rustSupply (bk : OrderBook) (p : Nat) : Int := u32Residue (supply bk p)

/-- The fixed Rust per-bucket executable volume. -/
def rustExecVol (bk : OrderBook) (p : Nat) : Int :=
  min (rustDemand bk p) (rustSupply bk p)

/-- The fixed Rust scan: replace the incumbent only on a strict volume increase. -/
def rustArgmaxUpto (bk : OrderBook) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if rustExecVol bk (rustArgmaxUpto bk n) < rustExecVol bk (n + 1)
      then n + 1
      else rustArgmaxUpto bk n

/-- The fixed Rust output, including its `best_v == 0` no-clear encoding. -/
def rustReferenceOutput (bk : OrderBook) (k : Nat) : ClearingOutput :=
  let p := rustArgmaxUpto bk (k - 1)
  let v := rustExecVol bk p
  if v = 0 then ⟨none, 0⟩ else ⟨some p, v⟩

/-- The Lean clearing with the same public no-clear encoding as Rust.  This removes the old
`some p, 0` versus `none, 0` representation mismatch without changing `crossing` itself. -/
def leanClearingOutput (bk : OrderBook) (k : Nat) : ClearingOutput :=
  let p := crossing bk k
  let v := clearedVolume bk k
  if v = 0 then ⟨none, 0⟩ else ⟨some p, v⟩

/-- The honest range premise relating unbounded Lean aggregates to Rust's `u32` values. -/
def AggregatesFitU32 (bk : OrderBook) : Prop :=
  ∀ p, 0 ≤ demand bk p ∧ demand bk p < u32Modulus ∧
       0 ≤ supply bk p ∧ supply bk p < u32Modulus

theorem rustDemand_eq (bk : OrderBook) (hfit : AggregatesFitU32 bk) (p : Nat) :
    rustDemand bk p = demand bk p := by
  exact Int.emod_eq_of_lt (hfit p).1 (hfit p).2.1

theorem rustSupply_eq (bk : OrderBook) (hfit : AggregatesFitU32 bk) (p : Nat) :
    rustSupply bk p = supply bk p := by
  exact Int.emod_eq_of_lt (hfit p).2.2.1 (hfit p).2.2.2

theorem rustExecVol_eq (bk : OrderBook) (hfit : AggregatesFitU32 bk) (p : Nat) :
    rustExecVol bk p = execVol bk p := by
  simp only [rustExecVol, execVol, rustDemand_eq bk hfit p, rustSupply_eq bk hfit p]

/-- The independently written Rust loop is extensionally the Lean `argmaxUpto` loop. -/
theorem rustArgmaxUpto_eq_argmaxUpto (bk : OrderBook) (hfit : AggregatesFitU32 bk) :
    ∀ n, rustArgmaxUpto bk n = argmaxUpto bk n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rustArgmaxUpto, argmaxUpto, ih,
        rustExecVol_eq bk hfit (argmaxUpto bk n), rustExecVol_eq bk hfit (n + 1)]

/-- **Positive crossing denotation.** On every nonempty bucket range whose aggregate curves fit the
deployed `u32` representation, the fixed Rust reference output equals the Lean argmax output. -/
theorem FhEggCrossingDenotation :
    ∀ (bk : OrderBook) (k : Nat), 0 < k → AggregatesFitU32 bk →
      leanClearingOutput bk k = rustReferenceOutput bk k := by
  intro bk k _ hfit
  simp only [leanClearingOutput, rustReferenceOutput, clearedVolume, crossing]
  rw [rustArgmaxUpto_eq_argmaxUpto bk hfit,
    rustExecVol_eq bk hfit (argmaxUpto bk (k - 1))]

/-! The two named books now agree on both implementations. -/

#guard leanClearingOutput workBook 3 == (⟨some 1, 8⟩ : ClearingOutput)
#guard rustReferenceOutput workBook 3 == (⟨some 1, 8⟩ : ClearingOutput)
#guard leanClearingOutput counterBook 2 == (⟨some 1, 9⟩ : ClearingOutput)
#guard rustReferenceOutput counterBook 2 == (⟨some 1, 9⟩ : ClearingOutput)

theorem workBook_conventions_agree :
    leanClearingOutput workBook 3 = rustReferenceOutput workBook 3 := by decide

theorem counterWitness_conventions_agree :
    leanClearingOutput counterBook 2 = rustReferenceOutput counterBook 2 := by decide

/-- A genuinely zero-volume book: there are bids but no asks. -/
def noClearTfheBook : OrderBook :=
  [⟨Side.bid, 10, 1⟩, ⟨Side.bid, 8, 0⟩]

#guard (demand noClearTfheBook 0, supply noClearTfheBook 0) == (18, 0)
#guard leanClearingOutput noClearTfheBook 2 == (⟨none, 0⟩ : ClearingOutput)
#guard rustReferenceOutput noClearTfheBook 2 == (⟨none, 0⟩ : ClearingOutput)

theorem noClearEncodingDenotation :
    leanClearingOutput noClearTfheBook 2 = rustReferenceOutput noClearTfheBook 2 := by decide

/-! ## 2. The widened `FheUint32` observable semantics. -/

/-- Every individual order is representable by Rust's public `Qty = u16`. -/
def OrdersFitU16 (bk : OrderBook) : Prop :=
  ∀ o ∈ bk, 0 ≤ o.qty ∧ o.qty < 65536

/-- The encrypted demand aggregate after the fixed `FheUint32::sum`. -/
def fheDemand (bk : OrderBook) (p : Nat) : Int := u32Residue (demand bk p)

/-- The encrypted supply aggregate after the fixed `FheUint32::sum`. -/
def fheSupply (bk : OrderBook) (p : Nat) : Int := u32Residue (supply bk p)

/-- Homomorphic `secure_min` at one bucket, at decrypted observable semantics. -/
def fheExecVol (bk : OrderBook) (p : Nat) : Int :=
  min (fheDemand bk p) (fheSupply bk p)

/-- The homomorphic strict argmax scan (lowest bucket wins ties). -/
def fheArgmaxUpto (bk : OrderBook) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if fheExecVol bk (fheArgmaxUpto bk n) < fheExecVol bk (n + 1)
      then n + 1
      else fheArgmaxUpto bk n

/-- The decrypted output of the fixed `fhe_clear`.  The zero-volume test happens on `best_v`, so the
sentinel and volume cannot disagree. -/
def fheOutput (bk : OrderBook) (k : Nat) : ClearingOutput :=
  let p := fheArgmaxUpto bk (k - 1)
  let v := fheExecVol bk p
  if v = 0 then ⟨none, 0⟩ else ⟨some p, v⟩

theorem fheArgmaxUpto_eq_rustArgmaxUpto (bk : OrderBook) :
    ∀ n, fheArgmaxUpto bk n = rustArgmaxUpto bk n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [fheArgmaxUpto, rustArgmaxUpto, ih, fheExecVol, rustExecVol,
        fheDemand, fheSupply, rustDemand, rustSupply]
      rfl

/-- The fixed FHE observable program computes the same `u32` reference function for every modeled
book.  The implementation-level ciphertext relation remains separately named below. -/
theorem fheOutput_eq_rustReferenceOutput (bk : OrderBook) (k : Nat) :
    fheOutput bk k = rustReferenceOutput bk k := by
  simp only [fheOutput, rustReferenceOutput]
  rw [fheArgmaxUpto_eq_rustArgmaxUpto bk]
  rfl

/-- The public, input-level scope of the deployed FHE call: nonempty bucket range, a `u32` bucket
index, and `u16` orders. -/
def FheComputesReference : Prop :=
  ∀ (bk : OrderBook) (k : Nat), 0 < k → k < 4294967296 → OrdersFitU16 bk →
    fheOutput bk k = rustReferenceOutput bk k

/-- The former aggregate no-cross/width counterexamples no longer refute the program-level observable
denotation. -/
theorem FhEggTfheProgramDenotation : FheComputesReference := by
  intro bk k _ _ _
  exact fheOutput_eq_rustReferenceOutput bk k

/-- Two 32768-lot bids and asks: the aggregate is 65536, above `2^16` but inside `u32`. -/
def wideTfheBook : OrderBook :=
  [⟨Side.bid, 32768, 0⟩, ⟨Side.bid, 32768, 0⟩,
   ⟨Side.ask, 32768, 0⟩, ⟨Side.ask, 32768, 0⟩]

#guard demand wideTfheBook 0 == 65536
#guard supply wideTfheBook 0 == 65536
#guard fheDemand wideTfheBook 0 == 65536
#guard fheSupply wideTfheBook 0 == 65536
#guard rustReferenceOutput wideTfheBook 1 == (⟨some 0, 65536⟩ : ClearingOutput)
#guard fheOutput wideTfheBook 1 == (⟨some 0, 65536⟩ : ClearingOutput)

/-- **Positive width denotation.** The exact old overflow witness now remains 65536 in both widened
aggregates and clears identically to the reference. -/
theorem FhEggTfheWidthDenotation :
    OrdersFitU16 wideTfheBook ∧
    fheDemand wideTfheBook 0 = 65536 ∧ fheSupply wideTfheBook 0 = 65536 ∧
    fheOutput wideTfheBook 1 = rustReferenceOutput wideTfheBook 1 ∧
    fheOutput wideTfheBook 1 = (⟨some 0, 65536⟩ : ClearingOutput) := by
  constructor
  · intro o ho
    simp [wideTfheBook] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> decide
  · decide

/-- **Positive no-cross denotation.** On a genuine no-clear book, the fixed FHE sentinel reports
exactly `(None,0)`, matching the plaintext reference. -/
theorem FhEggTfheNoCrossDenotation :
    OrdersFitU16 noClearTfheBook ∧
    fheOutput noClearTfheBook 2 = rustReferenceOutput noClearTfheBook 2 ∧
    fheOutput noClearTfheBook 2 = (⟨none, 0⟩ : ClearingOutput) := by
  constructor
  · intro o ho
    simp [noClearTfheBook] at ho
    rcases ho with rfl | rfl <;> decide
  · decide

/-! ### Honest TFHE boundary. -/

/-- An abstract hook for the real encrypted implementation.  Instantiating `Key`, `CipherOutput`,
`eval`, and `decrypt` with tfhe-rs and proving this predicate is the remaining ciphertext-level task;
the plaintext theorem `FhEggTfheProgramDenotation` is not that proof. -/
def FhEggTfheCiphertextRefinementResidual
    (Key CipherOutput : Type*)
    (eval : Key → OrderBook → Nat → CipherOutput)
    (decrypt : Key → CipherOutput → ClearingOutput) : Prop :=
  ∀ (key : Key) (bk : OrderBook) (k : Nat), 0 < k → k < 4294967296 → OrdersFitU16 bk →
    decrypt key (eval key bk k) = fheOutput bk k

/-! ## 3. The fixed `mpc_crossing`: argmax denotation and reveal-only view. -/

/-- MPC's secret-shared demand coefficient, at opened value semantics. -/
def mpcDemand (bk : OrderBook) (p : Nat) : Int := u32Residue (demand bk p)

/-- MPC's secret-shared supply coefficient, at opened value semantics. -/
def mpcSupply (bk : OrderBook) (p : Nat) : Int := u32Residue (supply bk p)

/-- MPC's secret-shared per-bucket `secure_min`. -/
def mpcExecVol (bk : OrderBook) (p : Nat) : Int :=
  min (mpcDemand bk p) (mpcSupply bk p)

/-- MPC's oblivious strict argmax scan.  No comparison bit is opened. -/
def mpcArgmaxUpto (bk : OrderBook) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if mpcExecVol bk (mpcArgmaxUpto bk n) < mpcExecVol bk (n + 1)
      then n + 1
      else mpcArgmaxUpto bk n

/-- The `(p*,V*)` opened by the fixed MPC crossing. -/
def mpcOutput (bk : OrderBook) (k : Nat) : ClearingOutput :=
  let p := mpcArgmaxUpto bk (k - 1)
  let v := mpcExecVol bk p
  if v = 0 then ⟨none, 0⟩ else ⟨some p, v⟩

theorem mpcArgmaxUpto_eq_rustArgmaxUpto (bk : OrderBook) :
    ∀ n, mpcArgmaxUpto bk n = rustArgmaxUpto bk n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [mpcArgmaxUpto, rustArgmaxUpto, ih, mpcExecVol, rustExecVol,
        mpcDemand, mpcSupply, rustDemand, rustSupply]
      rfl

theorem mpcOutput_eq_rustReferenceOutput (bk : OrderBook) (k : Nat) :
    mpcOutput bk k = rustReferenceOutput bk k := by
  simp only [mpcOutput, rustReferenceOutput]
  rw [mpcArgmaxUpto_eq_rustArgmaxUpto bk]
  rfl

/-- The real bit-sliced MPC call additionally requires each curve coefficient to fit the selected
public bit width `b`. -/
def MpcInputsFit (bk : OrderBook) (k b : Nat) : Prop :=
  ∀ p < k, 0 ≤ mpcDemand bk p ∧ mpcDemand bk p < (2 : Int) ^ b ∧
             0 ≤ mpcSupply bk p ∧ mpcSupply bk p < (2 : Int) ^ b

/-- **Positive MPC denotation.** Subject to the actual aggregate and bit-width admission premises, the
revealed fixed-MPC result is the encoded Lean argmax clearing. -/
theorem MpcCrossingDenotation :
    ∀ (bk : OrderBook) (k b : Nat), 0 < k → AggregatesFitU32 bk → MpcInputsFit bk k b →
      mpcOutput bk k = leanClearingOutput bk k := by
  intro bk k _ hk hfit _
  calc
    mpcOutput bk k = rustReferenceOutput bk k := mpcOutput_eq_rustReferenceOutput bk k
    _ = leanClearingOutput bk k := (FhEggCrossingDenotation bk k hk hfit).symm

#guard mpcOutput workBook 3 == (⟨some 1, 8⟩ : ClearingOutput)
#guard mpcOutput counterBook 2 == (⟨some 1, 9⟩ : ClearingOutput)
#guard mpcOutput noClearTfheBook 2 == (⟨none, 0⟩ : ClearingOutput)

/-- The input-dependent portion of the real transcript.  `masked` is the stream of Beaver openings;
its values are uniform one-time pads (proved algebraically in `MpcClearingSecurity.otpMasks`).  The
remaining fields are public shape plus the only unmasked reveal `(p*,V*)`. -/
structure MpcTranscriptView where
  masked : List Bool
  k : Nat
  bitWidth : Nat
  revealed : ClearingOutput
  deriving DecidableEq, Repr

/-- Observable view of `mpc_crossing`; notably absent are the old sign vector and curve heights. -/
def mpcCrossingView (bk : OrderBook) (k bitWidth : Nat) (masked : List Bool) : MpcTranscriptView :=
  ⟨masked, k, bitWidth, mpcOutput bk k⟩

/-- The Rust `simulate` view from only public shape, independent masks, and `(p*,V*)`. -/
def mpcSimulator (k bitWidth : Nat) (masked : List Bool)
    (out : ClearingOutput) : MpcTranscriptView :=
  ⟨masked, k, bitWidth, out⟩

/-- The exact deterministic factorization induced by coupling the real and simulated uniform Beaver
mask streams.  Together with `otpMasks`, this is the observable no-viewer statement at this model's
scope. -/
def MpcCrossingViewFactorsThroughOutput : Prop :=
  ∀ (bk : OrderBook) (k bitWidth : Nat) (masked : List Bool),
    mpcCrossingView bk k bitWidth masked = mpcSimulator k bitWidth masked (mpcOutput bk k)

/-- **Positive no-viewer denotation for `mpc_crossing`.** -/
theorem MpcCrossingRevealOnlyDenotation : MpcCrossingViewFactorsThroughOutput := by
  intro bk k bitWidth masked
  rfl

/-- Two different private books with the same public `(p*,V*)=(0,8)`. -/
def sameOutputBookA : OrderBook := [⟨Side.bid, 10, 0⟩, ⟨Side.ask, 8, 0⟩]
def sameOutputBookB : OrderBook := [⟨Side.bid, 8, 0⟩, ⟨Side.ask, 8, 0⟩]

#guard demand sameOutputBookA 0 != demand sameOutputBookB 0
#guard mpcOutput sameOutputBookA 1 == mpcOutput sameOutputBookB 1
#guard mpcCrossingView sameOutputBookA 1 32 [true, false, true] ==
  mpcCrossingView sameOutputBookB 1 32 [true, false, true]

/-- A concrete same-output/different-book tooth: under the same coupled pad stream, the MPC views are
identical even though the private demand coefficients differ. -/
theorem mpcSameOutputIndistinguishable :
    demand sameOutputBookA 0 ≠ demand sameOutputBookB 0 ∧
    mpcCrossingView sameOutputBookA 1 32 [true, false, true] =
      mpcCrossingView sameOutputBookB 1 32 [true, false, true] := by decide

/-- A curve-height leak would not factor through `(p*,V*)`; this is the negative tooth showing that
the reveal-only codomain is a real restriction rather than a vacuous type alias. -/
theorem mpcCurveHeightLeakage_refused :
    ¬ ∃ sim : ClearingOutput → Int,
        ∀ bk : OrderBook, sim (mpcOutput bk 1) = demand bk 0 := by
  rintro ⟨sim, hsim⟩
  have hA := hsim sameOutputBookA
  have hB := hsim sameOutputBookB
  have hout : mpcOutput sameOutputBookA 1 = mpcOutput sameOutputBookB 1 := by decide
  rw [hout] at hA
  exact (by decide : demand sameOutputBookA 0 ≠ demand sameOutputBookB 0) (hA.symm.trans hB)

/-! ### Axiom hygiene — every theorem in this audit is pinned kernel-clean. -/

#assert_axioms rustDemand_eq
#assert_axioms rustSupply_eq
#assert_axioms rustExecVol_eq
#assert_axioms rustArgmaxUpto_eq_argmaxUpto
#assert_axioms FhEggCrossingDenotation
#assert_axioms workBook_conventions_agree
#assert_axioms counterWitness_conventions_agree
#assert_axioms noClearEncodingDenotation
#assert_axioms fheArgmaxUpto_eq_rustArgmaxUpto
#assert_axioms fheOutput_eq_rustReferenceOutput
#assert_axioms FhEggTfheProgramDenotation
#assert_axioms FhEggTfheWidthDenotation
#assert_axioms FhEggTfheNoCrossDenotation
#assert_axioms mpcArgmaxUpto_eq_rustArgmaxUpto
#assert_axioms mpcOutput_eq_rustReferenceOutput
#assert_axioms MpcCrossingDenotation
#assert_axioms MpcCrossingRevealOnlyDenotation
#assert_axioms mpcSameOutputIndistinguishable
#assert_axioms mpcCurveHeightLeakage_refused

end Market.FhEggRustDenotation
