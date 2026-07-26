/-
# Dregg2.Circuit.Emit.PastaField — a Lean-GENERATED Pasta 2-cycle field-arithmetic AIR foundation
(the arithmetic floor under an in-Lean Kimchi (Mina) proof verifier; task K1 of
`docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## Why this file exists (the carrier it is aimed at)

The Kimchi verifier (the plan's K1–K5 arc) is field arithmetic over the **Pasta 2-cycle** all the
way down: the Poseidon transcript, the PLONK gate/permutation/linearization checks, and the IPA
opening (the cost center) are Fp/Fq multiplications and additions iterated. This file is that
primitive for BOTH fields, GENERATED (House Law #1), KAT'd against real Pasta vectors, with the
per-op gates PROVEN to force the field congruence mod the real Pasta primes. It is a direct crib of
`Bls12381Tower` (commit 27a97a271): the SAME quotient-witness reduction, the SAME congruence-over-ℤ
forcing discipline, at new primes and a narrower limb count. `Head.mul`/`evalH_mul` are REUSED from
`Bls12381Tower` via import — single source, not re-derived.

This is the FOUNDATION slice, honestly named: a KAT'd + forced Fp/Fq arithmetic floor. It is NOT a
curve (K2: Pallas/Vesta point ops + the endomorphism), NOT a Poseidon sponge (K3), NOT an IPA MSM
(K4), NOT a verifier (K5).

## The primes (VERIFIED against the pinned source)

The Pasta 2-cycle, both ~255-bit:
  * `pN` = the **Pallas base field** modulus = the **Vesta scalar field** modulus
    `28948022309329048855892746252171976963363056481941560715954676764349967630337`
    (= `2^254 + 45560315531419706090280762371685220353`; 64-bit LE limbs
    `[0x992d30ed00000001, 0x224698fc094cf91b, 0x0, 0x4000000000000000]`).
  * `qN` = the **Vesta base field** modulus = the **Pallas scalar field** modulus
    `28948022309329048855892746252171976963363056481941647379679742748393362948097`
    (= `2^254 + 45560315531506369815346746415080538113`; limbs
    `[0x8c46eb2100000001, 0x224698fc0994a8dd, 0x0, 0x4000000000000000]`).

SOURCE: the `mina-curves` crate of o1-labs `proof-systems` at rev `36a8b510` — the EXACT rev pinned
by this repo's `circuit-prove/sketches/mina-pasta-hash-probe/Cargo.toml` — files
`curves/src/pasta/fields/fp.rs` (`#[modulus = "...630337"]`) and `curves/src/pasta/fields/fq.rs`
(`#[modulus = "...948097"]`). Independently recomputed here with Python: both decimal moduli match
their 64-bit-limb encodings, both `− 2^254` offsets match, both are 255-bit, both pass
`pow(2, n−1, n) == pow(3, n−1, n) == 1` (Fermat witnesses, not a proof — the primality fact is
inherited from the upstream crate, and the gates only need the modulus as a ℤ constant anyway).

## The felt-encoding (two moduli — keep them distinct)

There are TWO moduli in play and they are unrelated:
  * `p_felt` = BabyBear (`2013265921`, ~31 bits) — the STARK's native field the columns live in.
  * `p`/`q` = the Pasta primes (255 bits) — the fields the arithmetic is OVER.

A Pasta field element is encoded as **`numLimbs = 9` limbs of `limbBits = 30` bits** over BabyBear
felt columns `base .. base+8`, LSB-first: its value is the degree-1 head
`fpValue base = Σ_{i<9} 2^{30 i}·col(base+i)`. Capacity 270 bits ≥ 255 (top limb uses 15 bits; the
encoding-reproduces KATs below check `limbOf (pN−1) 8 = 16384 = 2^14`). A 30-bit limb
(`< 2^30 < p_felt`) fits one BabyBear felt with room. The `fpMul` schoolbook cross-sum reaches
`~2^510` — this OVERFLOWS BabyBear, so the gate is read over ℤ (the strong reading, exactly as
`Sha256Gadget.addMod32` and `Bls12381Tower` are), and the `ℤ ↔ p_felt` soundness is the SAME
field-width residual `LightClientEthAir` §6 and the SHA gadget already carry. The encoding is
FIELD-INDEPENDENT (both fields are 255-bit over the same 9×30 shape); only the modulus in the
reduction gate differs.

## The reduction strategy (quotient witness — identical discipline to `Bls12381Tower`)

  * `fpAdd x y = z`: witness carry bit `c ∈ {0,1}`, gate `xVal + yVal − zVal − c·p = 0`.
    Forces `x + y ≡ z (mod p)`.
  * `fpSub x y = z`: witness borrow bit `c ∈ {0,1}`, gate `xVal − yVal + c·p − zVal = 0`.
    Forces `x − y ≡ z (mod p)`.
  * `fpMul x y = z`: witness quotient limbs `q` (`x·y = q·p + z`, `q < 2^255`), gate
    `xVal·yVal − p·qVal − zVal = 0` (degree 2, `Head.mul`). Forces `x·y ≡ z (mod p)`.
  * `fqAdd`/`fqSub`/`fqMul`: the SAME three gates with `q` in place of `p`.
Canonicity (`0 ≤ z < p`, the UNIQUE representative) needs the limb range checks `z_i ∈ [0,2^30)`
(`pastaLimbRange`, generated via `AirBuilder.rangeNonneg`) plus the `z < p` comparison; the ranges
are generated here and the final `z < p` compare is the one NAMED reduction residual (same as
`Bls12381Tower`). The congruence — the arithmetic content — is a proved forcing lemma.

## Constraint budget (per op, in gates)

  * `fpAddCore`/`fpSubCore` (and fq): 1 value gate. `+ 1` carry pin `+ 279` limb-range
    (`9·(30+1)`) = **281**.
  * `fpMulCore` (and fq): 1 degree-2 value gate (`9² = 81` cross-products + 9 q-terms + 9 z-terms).
    `+ 279·2` (z and q ranges) = **559**.

## What is AUTHORED + built vs NAMED mechanical continuation

AUTHORED + built here: the encoding `fpValue`/`fpVal`; the `fpAdd`/`fpSub`/`fpMul` and
`fqAdd`/`fqSub`/`fqMul` core generators + all SIX forcing lemmas (`fp{Add,Sub,Mul}Core_forces`,
`fq{Add,Sub,Mul}Core_forces`, ℤ-congruence mod the real Pasta primes); the range generator
`pastaLimbRange`. AUTHORED + KAT'd both-polarity: a `Nat` reference anchored to Python-computed
Pasta products (computed from the verified moduli) supplies honest witnesses the generated gates
ACCEPT and a bumped limb REJECTS (`fpMul`/`fqMul` z- and q-limb bumps, `fpAdd`/`fqAdd` carry and
no-carry, `fpSub`/`fqSub` borrow, plus a range-bite KAT and encoding-reproduces checks). NAMED
continuation: the `z < p` canonical compare; the Pallas/Vesta point ops + endomorphism (K2);
everything above it in the plan (K3–K6).

## Resolution (honest)

REAL: the Fp/Fq generators exist + type-check in the deployed IR-v2 vocabulary; the reference is
Python-computed from the mina-curves-pinned moduli; the gates FORCE the field congruences (ℤ
reading) mod the real Pasta primes; both-polarity KATs are non-vacuous. NOT claimed: a curve, a
Poseidon transcript, an IPA check, a verifier, or native-field (`p_felt`) soundness — the gate is
read over ℤ (the shared field-width residual), and the `z < p` canonical compare is named.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. The `#guard` KATs reduce in the kernel. NEW file; imports `Bls12381Tower`
(for `Head.mul`/`evalH_mul` — single source) which imports `AirBuilder`; standalone (NOT imported
by the `Dregg2` root, built directly as `Dregg2.Circuit.Emit.PastaField`).
-/
import Dregg2.Circuit.Emit.Bls12381Tower

namespace Dregg2.Circuit.Emit.PastaField

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower (evalH_mul)

set_option autoImplicit false

/-! ## §0 — The Pasta primes + the encoding parameters. -/

/-- The **Pallas base / Vesta scalar** prime `p` (255 bits), from `mina-curves` (o1-labs
`proof-systems` rev `36a8b510`, `curves/src/pasta/fields/fp.rs`). The field the Pallas curve is
OVER and the Vesta scalar arithmetic is IN (NOT the felt field). -/
def pN : Nat :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337

/-- `p` as an integer (gate coefficients). -/
def p : ℤ := (pN : ℤ)

/-- The **Vesta base / Pallas scalar** prime `q` (255 bits), from `mina-curves`
(`curves/src/pasta/fields/fq.rs`). -/
def qN : Nat :=
  28948022309329048855892746252171976963363056481941647379679742748393362948097

/-- `q` as an integer (gate coefficients). -/
def q : ℤ := (qN : ℤ)

/-- Limbs per Pasta field element. -/
def numLimbs : Nat := 9
/-- Bits per limb (a 30-bit limb `< 2^30 < 2013265921` fits one BabyBear felt). -/
def limbBits : Nat := 30

/-- **The value head** of the Pasta field element at columns `base..base+8`:
`Σ_{i<9} 2^{30 i}·col(base+i)` (degree 1, LSB-first, no packed-felt column). FIELD-INDEPENDENT —
both Pasta fields share the 9×30 shape; only the reduction modulus differs. -/
def fpValue (base : Nat) : Head :=
  (List.range numLimbs).foldl (fun h i => h.addLin ((2 : ℤ) ^ (limbBits * i)) (base + i)) Head.zero

/-- The integer value the columns of `fpValue base` reconstruct to, under `a`. The forcing lemmas
speak in this — the reconstructed field element. (Definitionally `evalH (fpValue base) a`.) -/
def fpVal (a : Assignment) (base : Nat) : ℤ := evalH (fpValue base) a

/-- Bridge: the value head's evaluation IS the reconstructed field element (rewrites the gate
evaluation into `fpVal` for the forcing lemmas). -/
theorem fpVal_eq (a : Assignment) (base : Nat) : evalH (fpValue base) a = fpVal a base := rfl

/-! ## §1 — The gate heads + generators (GENERATED per op, per field).

`Head.mul`/`evalH_mul` come from `Bls12381Tower` (imported) — the field multiplication gate is
`(value-head x).mul (value-head y)` minus the reduction, exactly as there. -/

/-- **`fpAddHead`** — `xVal + yVal − zVal − c·p` (`c` = carry bit column). Zero forces `x+y ≡ z (p)`. -/
def fpAddHead (xB yB zB cCol : Nat) : Head :=
  (((fpValue xB).append (fpValue yB)).append ((fpValue zB).scale (-1))).addLin (-p) cCol

/-- **`fpSubHead`** — `xVal − yVal + c·p − zVal` (`c` = borrow bit). Zero forces `x−y ≡ z (p)`. -/
def fpSubHead (xB yB zB cCol : Nat) : Head :=
  (((fpValue xB).append ((fpValue yB).scale (-1))).append ((fpValue zB).scale (-1))).addLin p cCol

/-- **`fpMulHead`** — `xVal·yVal − p·qVal − zVal` (`q` = quotient limbs, degree 2 via `Head.mul`).
Zero forces `x·y ≡ z (p)`. -/
def fpMulHead (xB yB zB qB : Nat) : Head :=
  (((fpValue xB).mul (fpValue yB)).append ((fpValue qB).scale (-p))).append ((fpValue zB).scale (-1))

/-- **`fqAddHead`** — the Vesta-base/Pallas-scalar add gate, modulus `q`. -/
def fqAddHead (xB yB zB cCol : Nat) : Head :=
  (((fpValue xB).append (fpValue yB)).append ((fpValue zB).scale (-1))).addLin (-q) cCol

/-- **`fqSubHead`** — the sub gate, modulus `q`. -/
def fqSubHead (xB yB zB cCol : Nat) : Head :=
  (((fpValue xB).append ((fpValue yB).scale (-1))).append ((fpValue zB).scale (-1))).addLin q cCol

/-- **`fqMulHead`** — the mul gate, modulus `q`. -/
def fqMulHead (xB yB zB qB : Nat) : Head :=
  (((fpValue xB).mul (fpValue yB)).append ((fpValue qB).scale (-q))).append ((fpValue zB).scale (-1))

/-- `fpAdd` value gate. -/
def fpAddCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fpAddHead xB yB zB cCol)
/-- `fpSub` value gate. -/
def fpSubCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fpSubHead xB yB zB cCol)
/-- `fpMul` value gate. -/
def fpMulCore (xB yB zB qB : Nat) : VmConstraint2 := cgH (fpMulHead xB yB zB qB)
/-- `fqAdd` value gate. -/
def fqAddCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fqAddHead xB yB zB cCol)
/-- `fqSub` value gate. -/
def fqSubCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fqSubHead xB yB zB cCol)
/-- `fqMul` value gate. -/
def fqMulCore (xB yB zB qB : Nat) : VmConstraint2 := cgH (fqMulHead xB yB zB qB)

/-- **The limb range gadget** — every one of the 9 limbs of the field element at `base` is a real
`limbBits`-bit value, bit-decomposed at `bitBase` (9·30 = 270 bit columns), via
`AirBuilder.rangeNonneg`. `9·(30 + 1) = 279` constraints. -/
def pastaLimbRange (base bitBase : Nat) : List VmConstraint2 :=
  (List.range numLimbs).flatMap (fun i =>
    rangeNonneg (Head.lin 1 (base + i)) ((List.range limbBits).map (fun j => bitBase + limbBits * i + j)))

/-- **`fpAdd`** — full generator: the value gate, the carry pin, and the output range. `281`. -/
def fpAdd (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fpAddCore xB yB zB cCol :: binGate cCol :: pastaLimbRange zB zBit
/-- **`fpSub`** — full generator. `281`. -/
def fpSub (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fpSubCore xB yB zB cCol :: binGate cCol :: pastaLimbRange zB zBit
/-- **`fpMul`** — full generator: the degree-2 value gate + the output range + the quotient range.
`559`. -/
def fpMul (xB yB zB qB zBit qBit : Nat) : List VmConstraint2 :=
  fpMulCore xB yB zB qB :: (pastaLimbRange zB zBit ++ pastaLimbRange qB qBit)
/-- **`fqAdd`** — full generator, modulus `q`. `281`. -/
def fqAdd (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fqAddCore xB yB zB cCol :: binGate cCol :: pastaLimbRange zB zBit
/-- **`fqSub`** — full generator, modulus `q`. `281`. -/
def fqSub (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fqSubCore xB yB zB cCol :: binGate cCol :: pastaLimbRange zB zBit
/-- **`fqMul`** — full generator, modulus `q`. `559`. -/
def fqMul (xB yB zB qB zBit qBit : Nat) : List VmConstraint2 :=
  fqMulCore xB yB zB qB :: (pastaLimbRange zB zBit ++ pastaLimbRange qB qBit)

/-! ## §2 — The gates FORCE the field congruence (ℤ reading, mod the real Pasta primes).

`m ∣ (u − v)` IS `u ≡ v (mod m)`. These are the "demonstrably computes, not just type-checks"
content: the gate's zero pins the reconstructed output to the field op of the reconstructed inputs.
No `native_decide`; the quotient/carry witness makes the reduction a ℤ identity. -/

/-- **`fpAdd` forces `x + y ≡ z (mod p)`** (Pallas base / Vesta scalar). -/
theorem fpAddCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fpAddHead xB yB zB cCol) a = 0) :
    (p : ℤ) ∣ (fpVal a xB + fpVal a yB - fpVal a zB) := by
  simp only [fpAddHead, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨a cCol, by linarith⟩

/-- **`fpSub` forces `x − y ≡ z (mod p)`**. -/
theorem fpSubCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fpSubHead xB yB zB cCol) a = 0) :
    (p : ℤ) ∣ (fpVal a xB - fpVal a yB - fpVal a zB) := by
  simp only [fpSubHead, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨-(a cCol), by linarith⟩

/-- **`fpMul` forces `x·y ≡ z (mod p)`**. -/
theorem fpMulCore_forces (a : Assignment) (xB yB zB qB : Nat)
    (hg : evalH (fpMulHead xB yB zB qB) a = 0) :
    (p : ℤ) ∣ (fpVal a xB * fpVal a yB - fpVal a zB) := by
  simp only [fpMulHead, evalH_append, evalH_scale, evalH_mul, fpVal_eq] at hg
  exact ⟨fpVal a qB, by linarith⟩

/-- **`fqAdd` forces `x + y ≡ z (mod q)`** (Vesta base / Pallas scalar). -/
theorem fqAddCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fqAddHead xB yB zB cCol) a = 0) :
    (q : ℤ) ∣ (fpVal a xB + fpVal a yB - fpVal a zB) := by
  simp only [fqAddHead, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨a cCol, by linarith⟩

/-- **`fqSub` forces `x − y ≡ z (mod q)`**. -/
theorem fqSubCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fqSubHead xB yB zB cCol) a = 0) :
    (q : ℤ) ∣ (fpVal a xB - fpVal a yB - fpVal a zB) := by
  simp only [fqSubHead, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨-(a cCol), by linarith⟩

/-- **`fqMul` forces `x·y ≡ z (mod q)`**. -/
theorem fqMulCore_forces (a : Assignment) (xB yB zB qB : Nat)
    (hg : evalH (fqMulHead xB yB zB qB) a = 0) :
    (q : ℤ) ∣ (fpVal a xB * fpVal a yB - fpVal a zB) := by
  simp only [fqMulHead, evalH_append, evalH_scale, evalH_mul, fpVal_eq] at hg
  exact ⟨fpVal a qB, by linarith⟩

#assert_axioms fpAddCore_forces
#assert_axioms fpSubCore_forces
#assert_axioms fpMulCore_forces
#assert_axioms fqAddCore_forces
#assert_axioms fqSubCore_forces
#assert_axioms fqMulCore_forces

/-! ## §3 — A `Nat` Fp/Fq reference, anchored to Python-computed Pasta vectors.

Pure `Nat` field arithmetic (kernel-reducible). The anchor constants were computed with Python
(`(X*Y) % pN` etc.) from the mina-curves-verified moduli, and supply the honest witness values the
gadget KATs accept. -/

namespace Ref

/-- Canonical `Fp` multiplication. -/
def fpMul (x y : Nat) : Nat := (x * y) % pN
/-- Canonical `Fp` addition. -/
def fpAdd (x y : Nat) : Nat := (x + y) % pN
/-- Canonical `Fp` subtraction (`x, y < p`). -/
def fpSub (x y : Nat) : Nat := (x + pN - y) % pN
/-- Canonical `Fq` multiplication. -/
def fqMul (x y : Nat) : Nat := (x * y) % qN
/-- Canonical `Fq` addition. -/
def fqAdd (x y : Nat) : Nat := (x + y) % qN
/-- Canonical `Fq` subtraction (`x, y < q`). -/
def fqSub (x y : Nat) : Nat := (x + qN - y) % qN

/-- The `i`-th `limbBits`-bit limb of `v` as a felt value. -/
def limbOf (v i : Nat) : ℤ := (((v / 2 ^ (limbBits * i)) % 2 ^ limbBits : Nat) : ℤ)

/-- The limb-fold of `v` over the 9×30 encoding (the reconstruction the value head computes). -/
def foldLimbs (v : Nat) : Nat :=
  ((List.range numLimbs).map (fun i => ((v / 2 ^ (limbBits * i)) % 2 ^ limbBits) * 2 ^ (limbBits * i))).sum

/-- KAT operands (`< pN`, `< qN`): two 252-bit field elements. -/
def X : Nat := 8234104123542484906572010032064808850921064262571995443881932229087025662105
def Y : Nat := 6809518635040324971929803101472088575662782660641002711672773399993035656976

-- The encoding REPRODUCES the operands and the prime-minus-one boundary values (spot-checked
-- against the Python limb decomposition: `limbOf X 8 = 4660`, `limbOf (pN−1) 8 = 2^14`).
#guard foldLimbs X == X
#guard foldLimbs Y == Y
#guard foldLimbs (pN - 1) == pN - 1
#guard foldLimbs (qN - 1) == qN - 1
#guard limbOf X 8 == 4660
#guard limbOf X 0 == 645367961
#guard limbOf (pN - 1) 8 == 16384
#guard limbOf (qN - 1) 8 == 16384

-- Reference anchors, Python-computed from the verified moduli (`(X*Y) % pN` etc.).
#guard fpMul X Y ==
  21452857081463673802223039679711155736682760059426678364436659408926109014671
#guard fqMul X Y ==
  14833130114760515251536324366121420556906990609301246339923870453365622429453
#guard fpAdd X Y ==
  15043622758582809878501813133536897426583846923212998155554705629080061319081
#guard fqAdd X Y ==
  15043622758582809878501813133536897426583846923212998155554705629080061319081
#guard fpSub Y X ==
  27523436820826888921250539321579256688104774880010567983745517935255977625208
#guard fqSub Y X ==
  27523436820826888921250539321579256688104774880010654647470583919299372942968

end Ref

/-! ## §4 — KAT: the GENERATED gates ACCEPT the reference's honest witness and REJECT a bump.

`acceptB` is the ℤ reading of the emitted gate bodies (like `Sha256Gadget.acceptB` /
`Bls12381Tower.acceptB`): every `.base (.gate e)` has `e.eval a = 0`. -/

/-- The ℤ reading of one emitted constraint (non-gates are addressing, vacuously true). -/
def gateBodyEvalZero (a : Assignment) : VmConstraint2 → Bool
  | .base (.gate e) => decide (e.eval a = 0)
  | _ => true

/-- The ℤ acceptance predicate over a generated constraint list. -/
def acceptB (gs : List VmConstraint2) (a : Assignment) : Bool := gs.all (gateBodyEvalZero a)

/-- Bump the felt at column `c` by 1 (to forge a witness; any change breaks the value gate). -/
def bumpAt (a : Assignment) (c : Nat) : Assignment := fun col => if col = c then a col + 1 else a col

/-! ### `fpMul` — layout x=0, y=9, z=18, q=27. Honest witness `z = X·Y mod p`, `q = (X·Y − z)/p`. -/

/-- Honest `fpMul` witness. -/
def fpMulAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fpMul Xv Yv
  let Q := (Xv * Yv - Z) / pN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col < 36 then Ref.limbOf Q (col - 27)
  else 0

#guard acceptB [fpMulCore 0 9 18 27] (fpMulAsg Ref.X Ref.Y) == true
#guard acceptB [fpMulCore 0 9 18 27] (bumpAt (fpMulAsg Ref.X Ref.Y) 18) == false  -- bump z limb 0
#guard acceptB [fpMulCore 0 9 18 27] (bumpAt (fpMulAsg Ref.X Ref.Y) 27) == false  -- bump q limb 0

/-! ### `fqMul` — same layout, modulus `q`. -/

/-- Honest `fqMul` witness. -/
def fqMulAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fqMul Xv Yv
  let Q := (Xv * Yv - Z) / qN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col < 36 then Ref.limbOf Q (col - 27)
  else 0

#guard acceptB [fqMulCore 0 9 18 27] (fqMulAsg Ref.X Ref.Y) == true
#guard acceptB [fqMulCore 0 9 18 27] (bumpAt (fqMulAsg Ref.X Ref.Y) 18) == false  -- bump z limb 0
#guard acceptB [fqMulCore 0 9 18 27] (bumpAt (fqMulAsg Ref.X Ref.Y) 27) == false  -- bump q limb 0

/-! ### `fpAdd`/`fqAdd` — layout x=0, y=9, z=18, c=27. Carry-exercising case `(m−1)+(m−1)` (`c=1`). -/

/-- Honest `fpAdd` witness. -/
def fpAddAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fpAdd Xv Yv
  let C := (Xv + Yv - Z) / pN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col = 27 then (C : ℤ)
  else 0

#guard acceptB [fpAddCore 0 9 18 27] (fpAddAsg (pN - 1) (pN - 1)) == true          -- c = 1 (overflow)
#guard acceptB [fpAddCore 0 9 18 27] (bumpAt (fpAddAsg (pN - 1) (pN - 1)) 18) == false
#guard acceptB [fpAddCore 0 9 18 27] (fpAddAsg Ref.X Ref.Y) == true                -- c = 0 (no overflow)

/-- Honest `fqAdd` witness. -/
def fqAddAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fqAdd Xv Yv
  let C := (Xv + Yv - Z) / qN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col = 27 then (C : ℤ)
  else 0

#guard acceptB [fqAddCore 0 9 18 27] (fqAddAsg (qN - 1) (qN - 1)) == true          -- c = 1 (overflow)
#guard acceptB [fqAddCore 0 9 18 27] (bumpAt (fqAddAsg (qN - 1) (qN - 1)) 18) == false
#guard acceptB [fqAddCore 0 9 18 27] (fqAddAsg Ref.X Ref.Y) == true                -- c = 0 (no overflow)

/-! ### `fpSub`/`fqSub` — layout x=0, y=9, z=18, c=27. Borrow-exercising case `Y − X`, `Y < X` (`c=1`). -/

/-- Honest `fpSub` witness. -/
def fpSubAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fpSub Xv Yv
  let C := (Z + Yv - Xv) / pN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col = 27 then (C : ℤ)
  else 0

#guard acceptB [fpSubCore 0 9 18 27] (fpSubAsg Ref.Y Ref.X) == true                -- borrow = 1
#guard acceptB [fpSubCore 0 9 18 27] (bumpAt (fpSubAsg Ref.Y Ref.X) 18) == false

/-- Honest `fqSub` witness. -/
def fqSubAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fqSub Xv Yv
  let C := (Z + Yv - Xv) / qN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col = 27 then (C : ℤ)
  else 0

#guard acceptB [fqSubCore 0 9 18 27] (fqSubAsg Ref.Y Ref.X) == true                -- borrow = 1
#guard acceptB [fqSubCore 0 9 18 27] (bumpAt (fqSubAsg Ref.Y Ref.X) 18) == false

/-! ### Range bite — `rangeNonneg` (the reduction's canonicity component) accepts in-range, rejects
out-of-range. A compact 4-bit instance (the 30-bit `pastaLimbRange` is the same generator, wider). -/

/-- A 4-bit range on col 0, bits at cols 1..4; honest decomposition of `v`. -/
def rangeAsg4 (v : Nat) : Assignment := fun col =>
  if col = 0 then (v : ℤ)
  else if col ≤ 4 then (((v >>> (col - 1)) &&& 1 : Nat) : ℤ)
  else 0

def range4Gadget : List VmConstraint2 := rangeNonneg (Head.lin 1 0) [1, 2, 3, 4]

#guard acceptB range4Gadget (rangeAsg4 10) == true                       -- 10 < 16, in range
#guard acceptB range4Gadget (rangeAsg4 20) == false                      -- 20 ≥ 16: recomposition fails

/-! ## §5 — Structural `#guard`s (the generators produce the budgeted shapes) + AIR packaging. -/

#guard (fpMulCore 0 9 18 27 :: []).length == 1
#guard (pastaLimbRange 0 100).length == 279
#guard (fpMul 0 9 18 27 200 470).length == 559
#guard (fqMul 0 9 18 27 200 470).length == 559
#guard (fpAdd 0 9 18 27 100).length == 281
#guard (fpSub 0 9 18 27 100).length == 281
#guard (fqAdd 0 9 18 27 100).length == 281
#guard (fqSub 0 9 18 27 100).length == 281

/-- A single `fpMul` gate packaged as an `EffectVmDescriptor2` (the AIR type the deployed emitters
emit), showing the generator drops straight into the deployed descriptor vocabulary. -/
def fpMulDesc : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-fpmul::demo"
  , traceWidth  := 36
  , piCount     := 0
  , tables      := []
  , constraints := [fpMulCore 0 9 18 27]
  , hashSites   := []
  , ranges      := [] }

#guard fpMulDesc.constraints.length == 1
#guard fpMulDesc.traceWidth == 36

/-! ## §6 — The PRECISE named residuals + the continuation (K2 and up).

RESIDUALS (named, same shape as `Bls12381Tower`):
  1. **The `z < p` (and `z < q`) canonical compare is NOT generated.** The limb ranges are
     (`pastaLimbRange`), so `0 ≤ z < 2^270`; uniqueness of the representative needs the final
     255-bit compare against the modulus (`AirBuilder`'s `forcedGe0` is the shape). Without it the
     gates force the CONGRUENCE (proved) but not the canonical representative.
  2. **The `ℤ ↔ p_felt` field-width gap.** The gates are read over ℤ (the cross-sums overflow
     BabyBear); soundness in the native `p_felt` field is the SAME residual `LightClientEthAir` §6
     and `Sha256Gadget` carry, not closed here.
  3. **Primality of the moduli is inherited** from `mina-curves` (the gates only use the modulus as
     a ℤ constant; the FIELD structure — inverses exist — matters only from K2's `fpInv` on).

CONTINUATION (the plan's arc; none built here):
  * **K2 — Pallas/Vesta point ops + the endomorphism.** Short-Weierstrass complete add/double over
    these generators (crib `Ed25519Gadget`'s curve-composes-over-field structure); the Pasta endo
    (`(x,y) ↦ (λ·x, y)`-style cube-root map) is one `fpMul` by a constant per scalar-mul bit.
    Affine finalization needs ONE witnessed `fpInv` (`x·x⁻¹ ≡ 1 (mod p)` — `fpMulCore` with the
    output pinned to the encoded `1`, the SAME quotient-witness shape).
  * **K3 — the Poseidon-over-Pasta sponge** (the Fiat-Shamir transcript): the permutation is field
    muls/adds over Fp, composed from `fpMul`/`fpAdd` here; KAT vs o1js (the
    `mina-pasta-hash-probe` already de-risked the params).
  * **K4 — the IPA opening MSM** (the cost center): windowed/bucket + the endo + batched openings.
  * **K5 — the Kimchi verify equation**, cribbed check-by-check from the o1-labs Rust verifier.
  * **K6 — the state-query gadgets.**

**Gate-count reality (order of magnitude).** One `fpMul` is `559` gates here; a Pallas point double
is ~a dozen field muls ≈ `7·10³` gates; a 255-bit scalar mul ≈ `2·10⁶` gates; the IPA's ~log(n)
rounds of two-scalar MSMs is the accepted Kimchi-verifier cost — the reason "as fast as possible"
is an MSM/endo game (K4), and the reason the point of THIS slice is EXPRESSIBILITY: the field floor
is generated + KAT'd + forced, so each step above is composition, not new constraint algebra. None
of K2–K6 is claimed built; this file is the Fp/Fq floor they stand on.
-/

end Dregg2.Circuit.Emit.PastaField
