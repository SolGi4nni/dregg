/-
# Dregg2.Circuit.Emit.Bls12381TowerExt — the BLS12-381 tower+curve layers ON TOP of Bls12381Tower
(Fp6, Fp12, G1, G2 — the next mechanical step of the pairing arc).

## What this file IS (the continuation of Bls12381Tower's §7, now BUILT one level up)

`Bls12381Tower` built the Fp/Fp2 field floor (encoding, `Head.mul`, `fp{Add,Sub,Mul}Core` +
forcing lemmas, `fp2MulGadget` + `fp2Mul_forces`, py_ecc-anchored KATs). This file iterates the SAME
generator pattern to the layers a Miller loop actually walks:

  * **Fp6 = Fp2[v]/(v³ − (u+1))** and **Fp12 = Fp6[w]/(w² − v)** — the tower folded deeper. Fp6 mul is
    9 Fp2 muls + the `v³ = u+1 = ξ` fold (`mulByXi`); Fp12 mul is Karatsuba over Fp6 (3 Fp6 muls +
    the `w² = v` fold, `mulByGamma`).
  * **G1 ⊂ E(Fp) : y² = x³ + 4** and **G2 ⊂ E'(Fp2) : y² = x³ + 4(u+1)** — Jacobian point DOUBLE and
    ADD, the curve arithmetic the loop's line evaluations are built from.

Everything GENERATED (House Law #1): the gadgets are `def`-generators COMPOSING `Bls12381Tower`'s
`fp{Mul,Add,Sub}Core` and `fp2MulGadget` (no gate hand-authored). The correctness ground truth is a
`Nat` reference — the full tower + the Jacobian curve laws — KAT'd against an INDEPENDENT computation:
py_ecc-style product/point vectors (external decimals), the on-curve invariant (`y² = x³ + b·Z⁶` on
the real BLS12-381 generators, doubled and added), and ring axioms (identity/commutativity/
distributivity). `mulByXi_forces` proves the ξ-multiply gadget forces its Fp2 congruence (composing
`Bls12381Tower`'s `nSub/fpAddCore_forces`); the composed `fp6Mul`/curve forcings are named-mechanical
(each sub-gadget is already forced by `fp2Mul_forces`/`fpMul_forces`).

## Both-polarity gadget KATs (generated gates ACCEPT the honest witness, REJECT tamper)

`mulByXiGadget` (Fp2 ξ-multiply), `fp6AddGadget` (Fp6 addition), and the WHOLE `g1DoubleGadget`
(21-gate Jacobian doubling) are `acceptB`-KAT'd both polarities against reference-derived witnesses —
the curve layer accepts a real trace and rejects a bumped output limb.

## What remains to a FOLDED BLS_OK (the last mile — NOT built, ~millions of gates)

The Miller loop (~64 doubling/line-eval iterations threading these G2 doublings + G1 point data into an
Fp12 accumulator), the final exponentiation ((p¹²−1)/r over Fp12), and the aggregate-verify wiring
(two pairings + an Fp12 equality gate) that would DERIVE `BLS_OK`. This file is the tower+curve layer
under that; it does NOT claim a pairing.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`.
`#guard` KATs reduce in the kernel. NEW file; imports read-only (`Bls12381Tower`); standalone (NOT
imported by the truncated `Dregg2.lean`; built directly as `Dregg2.Circuit.Emit.Bls12381TowerExt`).
-/
import Dregg2.Circuit.Emit.Bls12381Tower

namespace Dregg2.Circuit.Emit.Bls12381TowerExt

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower
-- The felt limb-reader from the base module (bare; no clash).
open Dregg2.Circuit.Emit.Bls12381Tower.Ref (limbOf)

set_option autoImplicit false

-- The canonical Nat Fp ops, aliased to non-clashing names (`Bls12381Tower` also exports GADGET
-- generators `fpMul`/`fpAdd`/`fpSub`, so the bare Nat ops would be ambiguous).
abbrev nMul : Nat → Nat → Nat := Dregg2.Circuit.Emit.Bls12381Tower.Ref.fpMul
abbrev nAdd : Nat → Nat → Nat := Dregg2.Circuit.Emit.Bls12381Tower.Ref.fpAdd
abbrev nSub : Nat → Nat → Nat := Dregg2.Circuit.Emit.Bls12381Tower.Ref.fpSub

/-! ## §0 — The `Nat` reference: the full Fp2/Fp6/Fp12 tower + G1/G2 Jacobian curve laws.

Built on `Bls12381Tower.Ref.fp{Mul,Add,Sub}` (the canonical Fp ops). Kernel-reducible; the anchors
below KAT it against an independent (py_ecc-style) computation, the on-curve invariant, and ring
axioms. -/

namespace R

/-- An `Fp2` value `a0 + a1·u`. -/
abbrev F2 := Nat × Nat
def f2add (a b : F2) : F2 := (nAdd a.1 b.1, nAdd a.2 b.2)
def f2sub (a b : F2) : F2 := (nSub a.1 b.1, nSub a.2 b.2)
def f2mul (a b : F2) : F2 :=
  (nSub (nMul a.1 b.1) (nMul a.2 b.2), nAdd (nMul a.1 b.2) (nMul a.2 b.1))
/-- Multiply by `ξ = u+1`: `(a0+a1 u)(1+u) = (a0−a1) + (a0+a1)u`. -/
def f2xi (a : F2) : F2 := (nSub a.1 a.2, nAdd a.1 a.2)
def f2z : F2 := (0, 0)
def f2one : F2 := (1, 0)

/-- An `Fp6` value `c0 + c1·v + c2·v²`, each `ci : Fp2`. -/
abbrev F6 := F2 × F2 × F2
def f6add (A B : F6) : F6 := (f2add A.1 B.1, f2add A.2.1 B.2.1, f2add A.2.2 B.2.2)
def f6sub (A B : F6) : F6 := (f2sub A.1 B.1, f2sub A.2.1 B.2.1, f2sub A.2.2 B.2.2)
/-- Fp6 multiplication (schoolbook with the `v³ = ξ` fold). -/
def f6mul (A B : F6) : F6 :=
  let a0 := A.1; let a1 := A.2.1; let a2 := A.2.2
  let b0 := B.1; let b1 := B.2.1; let b2 := B.2.2
  ( f2add (f2mul a0 b0) (f2xi (f2add (f2mul a1 b2) (f2mul a2 b1)))
  , f2add (f2add (f2mul a0 b1) (f2mul a1 b0)) (f2xi (f2mul a2 b2))
  , f2add (f2add (f2mul a0 b2) (f2mul a1 b1)) (f2mul a2 b0) )
def f6z : F6 := (f2z, f2z, f2z)
def f6one : F6 := (f2one, f2z, f2z)

/-- An `Fp12` value `d0 + d1·w`, each `di : Fp6`. -/
abbrev F12 := F6 × F6
/-- Multiply an `Fp6` by `γ = v`: `(c0+c1 v+c2 v²)·v = ξ·c2 + c0 v + c1 v²`. -/
def f6gamma (C : F6) : F6 := (f2xi C.2.2, C.1, C.2.1)
/-- Fp12 multiplication (Karatsuba over Fp6 with the `w² = v` fold). -/
def f12mul (A B : F12) : F12 :=
  let a0 := A.1; let a1 := A.2; let b0 := B.1; let b1 := B.2
  let v0 := f6mul a0 b0; let v1 := f6mul a1 b1
  ( f6add v0 (f6gamma v1)
  , f6sub (f6mul (f6add a0 a1) (f6add b0 b1)) (f6add v0 v1) )

/-! ### G1 — Jacobian point ops over Fp (curve `y² = x³ + 4`). -/

def m (x y : Nat) : Nat := nMul x y
def ad (x y : Nat) : Nat := nAdd x y
def sb (x y : Nat) : Nat := nSub x y
def sc (k x : Nat) : Nat := nMul (k % pN) x  -- scalar multiply

/-- Jacobian `[2]P` (a = 0 doubling, dbl-2009-l). -/
def g1dbl (P : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let X := P.1; let Y := P.2.1; let Z := P.2.2
  let A := m X X; let B := m Y Y; let C := m B B
  let D := sc 2 (sb (sb (m (ad X B) (ad X B)) A) C)
  let E := sc 3 A; let F := m E E
  let X3 := sb F (sc 2 D)
  let Y3 := sb (m E (sb D X3)) (sc 8 C)
  let Z3 := sc 2 (m Y Z)
  (X3, Y3, Z3)

/-- Jacobian `P + Q` (a = 0 addition, add-2007-bl; `P ≠ ±Q`). -/
def g1add (P Q : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let X1 := P.1; let Y1 := P.2.1; let Z1 := P.2.2
  let X2 := Q.1; let Y2 := Q.2.1; let Z2 := Q.2.2
  let Z1Z1 := m Z1 Z1; let Z2Z2 := m Z2 Z2
  let U1 := m X1 Z2Z2; let U2 := m X2 Z1Z1
  let S1 := m (m Y1 Z2) Z2Z2; let S2 := m (m Y2 Z1) Z1Z1
  let H := sb U2 U1; let I := m (sc 2 H) (sc 2 H); let J := m H I
  let r := sc 2 (sb S2 S1); let V := m U1 I
  let X3 := sb (sb (m r r) J) (sc 2 V)
  let Y3 := sb (m r (sb V X3)) (sc 2 (m S1 J))
  let Z3 := m (sb (sb (m (ad Z1 Z2) (ad Z1 Z2)) Z1Z1) Z2Z2) H
  (X3, Y3, Z3)

/-- On-curve (Jacobian) `Y² = X³ + 4·Z⁶`. -/
def oncurve1 (P : Nat × Nat × Nat) : Bool :=
  let X := P.1; let Y := P.2.1; let Z := P.2.2
  let Z3v := m (m Z Z) Z
  m Y Y == ad (m (m X X) X) (sc 4 (m Z3v Z3v))

/-! ### G2 — Jacobian point ops over Fp2 (curve `y² = x³ + 4(u+1)`). -/

abbrev P2 := F2 × F2 × F2
def sc2 (k : Nat) (x : F2) : F2 := f2mul (k % pN, 0) x
/-- `b'` = `4(u+1)` = `4 + 4u`. -/
def b2const : F2 := (4, 4)

def g2dbl (P : P2) : P2 :=
  let X := P.1; let Y := P.2.1; let Z := P.2.2
  let A := f2mul X X; let B := f2mul Y Y; let C := f2mul B B
  let D := sc2 2 (f2sub (f2sub (f2mul (f2add X B) (f2add X B)) A) C)
  let E := sc2 3 A; let F := f2mul E E
  let X3 := f2sub F (sc2 2 D)
  let Y3 := f2sub (f2mul E (f2sub D X3)) (sc2 8 C)
  let Z3 := sc2 2 (f2mul Y Z)
  (X3, Y3, Z3)

def g2add (P Q : P2) : P2 :=
  let X1 := P.1; let Y1 := P.2.1; let Z1 := P.2.2
  let X2 := Q.1; let Y2 := Q.2.1; let Z2 := Q.2.2
  let Z1Z1 := f2mul Z1 Z1; let Z2Z2 := f2mul Z2 Z2
  let U1 := f2mul X1 Z2Z2; let U2 := f2mul X2 Z1Z1
  let S1 := f2mul (f2mul Y1 Z2) Z2Z2; let S2 := f2mul (f2mul Y2 Z1) Z1Z1
  let H := f2sub U2 U1; let I := f2mul (sc2 2 H) (sc2 2 H); let J := f2mul H I
  let r := sc2 2 (f2sub S2 S1); let V := f2mul U1 I
  let X3 := f2sub (f2sub (f2mul r r) J) (sc2 2 V)
  let Y3 := f2sub (f2mul r (f2sub V X3)) (sc2 2 (f2mul S1 J))
  let Z3 := f2mul (f2sub (f2sub (f2mul (f2add Z1 Z2) (f2add Z1 Z2)) Z1Z1) Z2Z2) H
  (X3, Y3, Z3)

def oncurve2 (P : P2) : Bool :=
  let X := P.1; let Y := P.2.1; let Z := P.2.2
  let Z3v := f2mul (f2mul Z Z) Z
  f2mul Y Y == f2add (f2mul (f2mul X X) X) (f2mul b2const (f2mul Z3v Z3v))

/-! ### KAT anchors (external py_ecc-style vectors + on-curve invariant + ring axioms). -/

-- Test tower operands.
def A6 : F6 := ((1, 2), (3, 4), (5, 6))
def B6 : F6 := ((7, 8), (9, 10), (11, 12))
def D6 : F6 := ((2, 3), (5, 7), (11, 13))
def A12 : F12 := (((1, 2), (3, 4), (5, 6)), ((7, 8), (9, 10), (11, 12)))
def B12 : F12 := (((13, 14), (15, 16), (17, 18)), ((19, 20), (21, 22), (23, 24)))

-- External anchor: the Fp6 product `A6·B6`, independently computed.
#guard f6mul A6 B6 ==
  ( (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559564, 176)
  , (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559622, 189)
  , (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559748, 182) )
-- External anchor: the Fp12 product `A12·B12`, independently computed (both Fp6 halves).
#guard f12mul A12 B12 ==
  ( ( (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272558137, 1405)
    , (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272558505, 1475)
    , (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559097, 1505) )
  , ( (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272558549, 1240)
    , (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272558977, 1290)
    , (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559637, 1300) ) )

-- Ring axioms (non-vacuous robustness — a wrong ξ/reduction breaks these).
#guard f6mul A6 f6one == A6                                  -- identity
#guard f6mul A6 B6 == f6mul B6 A6                            -- commutativity
#guard f6mul A6 (f6add B6 D6) == f6add (f6mul A6 B6) (f6mul A6 D6)  -- distributivity
#guard f12mul A12 B12 == f12mul B12 A12                              -- Fp12 commutativity (non-vacuous)

-- BLS12-381 generators (affine).
def G1gen : Nat × Nat × Nat :=
  ( 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
  , 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569
  , 1 )
def G2gen : P2 :=
  ( (352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160,
     3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758)
  , (1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905,
     927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582)
  , (1, 0) )

-- On-curve invariants: the generators, DOUBLED, and 2P+P, stay on the curve (a wrong formula wouldn't).
#guard oncurve1 G1gen == true
#guard oncurve1 (g1dbl G1gen) == true
#guard oncurve1 (g1add (g1dbl G1gen) G1gen) == true
#guard oncurve2 G2gen == true
#guard oncurve2 (g2dbl G2gen) == true
#guard oncurve2 (g2add (g2dbl G2gen) G2gen) == true

-- External anchors: the exact doubled generators, independently computed.
#guard g1dbl G1gen ==
  ( 506495629725590588476438736938928437216878988401200917968428110806855219037361470594787775621162927277631758167243
  , 3215784584818841779393380451963501913485474208604528267666791755940205624806737197312591247682567521662969376111781
  , 2679013089888952946040942759883842443169867751876699240853087472833022847912667012945449310706733069984783512883138 )
#guard g2dbl G2gen ==
  ( (3615371968425162313504701611584580861091541671906640286537610648981546277559811355418121120405186865192603156540471,
     1996123912207319781232871775273589916094509852833549867151637455520658731483328327777718782754201260420931019497944)
  , (978142457653236052983988388396292566217089069272380812666116929298652861694202207333864830606577192738105844024927,
     2248711152455689790114026331322133133284196260289964969465268080325775757898907753181154992709229860715480504777099)
  , (3970301204574583871136109042354343276601737956431311461718757330132689452747647436847738208526667969282988680695810,
     1855107330984664911494403931552075761515480386907185940050055957587953754005351129961898579455915131150866688439164) )

end R

/-! ## §1 — The Fp2-level gadget helpers (GENERATED, composing `Bls12381Tower` cores). -/

/-- **`mulByXiGadget`** — Fp2 `×(u+1)`: `r0 = x0−x1` (an `fpSubCore`), `r1 = x0+x1` (an `fpAddCore`).
`x0/x1` = the input Fp2 coord bases; `r0/r1` outputs; `br/cr` the borrow/carry bits. 2 gates. -/
def mulByXiGadget (x0 x1 r0 r1 br cr : Nat) : List VmConstraint2 :=
  [fpSubCore x0 x1 r0 br, fpAddCore x0 x1 r1 cr]

/-- **`fp2AddGadget`** — `(a0+a1u)+(b0+b1u)`: two `fpAddCore`. 2 gates. -/
def fp2AddGadget (a0 a1 b0 b1 r0 r1 c0 c1 : Nat) : List VmConstraint2 :=
  [fpAddCore a0 b0 r0 c0, fpAddCore a1 b1 r1 c1]

/-- **`fp2SubGadget`** — `(a0+a1u)−(b0+b1u)`: two `fpSubCore`. 2 gates. -/
def fp2SubGadget (a0 a1 b0 b1 r0 r1 c0 c1 : Nat) : List VmConstraint2 :=
  [fpSubCore a0 b0 r0 c0, fpSubCore a1 b1 r1 c1]

/-- **`fp6AddGadget`** — Fp6 addition: three Fp2 adds over the 6 Fp coord bases (given as pairs).
6 gates. Outputs at `rBases` (6 bases), carries at `cBases` (6 bits). -/
def fp6AddGadget (a : List Nat) (b : List Nat) (r : List Nat) (c : List Nat) : List VmConstraint2 :=
  (List.range 6).map (fun i => fpAddCore (a.getD i 0) (b.getD i 0) (r.getD i 0) (c.getD i 0))

/-! ### An Fp2 gadget-value = a pair of Fp column bases; fresh-threaded wrappers for composition. -/

/-- An Fp2 value in a gadget = (real base, imag base). -/
abbrev C2 := Nat × Nat

/-- Fp2 mul, allocating `fp2MulGadget`'s 148-column scratch from `fresh`. Returns
`(constraints, output C2, next fresh)`. 8 gates. -/
def fp2mulG (x y : C2) (fresh : Nat) : List VmConstraint2 × C2 × Nat :=
  (fp2MulGadget x.1 x.2 y.1 y.2 fresh, (fp2MulR0 fresh, fp2MulR1 fresh), fresh + 148)

/-- Fp2 add (outputs at `fresh`, `fresh+13`; carries `fresh+26`, `fresh+27`). 2 gates. -/
def fp2addG (x y : C2) (fresh : Nat) : List VmConstraint2 × C2 × Nat :=
  ([fpAddCore x.1 y.1 fresh (fresh + 26), fpAddCore x.2 y.2 (fresh + 13) (fresh + 27)],
   (fresh, fresh + 13), fresh + 28)

/-- Fp2 sub. 2 gates. -/
def fp2subG (x y : C2) (fresh : Nat) : List VmConstraint2 × C2 × Nat :=
  ([fpSubCore x.1 y.1 fresh (fresh + 26), fpSubCore x.2 y.2 (fresh + 13) (fresh + 27)],
   (fresh, fresh + 13), fresh + 28)

/-- Fp2 `×(u+1)` (fresh-threaded). 2 gates. -/
def fp2xiG (x : C2) (fresh : Nat) : List VmConstraint2 × C2 × Nat :=
  ([fpSubCore x.1 x.2 fresh (fresh + 26), fpAddCore x.1 x.2 (fresh + 13) (fresh + 27)],
   (fresh, fresh + 13), fresh + 28)

/-! ## §2 — Fp6 / Fp12 multiplication gadgets (GENERATED, the tower folded deeper). -/

/-- **`fp6MulGadget`** — Fp6 multiplication (schoolbook + the `v³=ξ` fold), the 9 Fp2 muls, 6 Fp2
adds, and 2 `mulByXi`s COMPOSED from §1's fresh-threaded wrappers. `a0/a1/a2`, `b0/b1/b2` are the six
input Fp2 values; returns `(constraints, (c0,c1,c2), next fresh)`. 88 gates. -/
def fp6MulGadget (a0 a1 a2 b0 b1 b2 : C2) (fresh : Nat) : List VmConstraint2 × (C2 × C2 × C2) × Nat :=
  let (g1, p00, f1) := fp2mulG a0 b0 fresh
  let (g2, p11, f2) := fp2mulG a1 b1 f1
  let (g3, p22, f3) := fp2mulG a2 b2 f2
  let (g4, p12, f4) := fp2mulG a1 b2 f3
  let (g5, p21, f5) := fp2mulG a2 b1 f4
  let (g6, p01, f6) := fp2mulG a0 b1 f5
  let (g7, p10, f7) := fp2mulG a1 b0 f6
  let (g8, p02, f8) := fp2mulG a0 b2 f7
  let (g9, p20, f9) := fp2mulG a2 b0 f8
  -- c0 = p00 + ξ(p12 + p21)
  let (h1, s1, fa) := fp2addG p12 p21 f9
  let (h2, x1, fb) := fp2xiG s1 fa
  let (h3, c0, fc) := fp2addG p00 x1 fb
  -- c1 = (p01 + p10) + ξ(p22)
  let (h4, s2, fd) := fp2addG p01 p10 fc
  let (h5, x2, fe) := fp2xiG p22 fd
  let (h6, c1, ff) := fp2addG s2 x2 fe
  -- c2 = (p02 + p11) + p20
  let (h7, s3, fg) := fp2addG p02 p11 ff
  let (h8, c2, fh) := fp2addG s3 p20 fg
  ( g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9
      ++ h1 ++ h2 ++ h3 ++ h4 ++ h5 ++ h6 ++ h7 ++ h8
  , (c0, c1, c2), fh )

/-- Fp6 add (fresh-threaded), three Fp2 adds. Returns `(constraints, (c0,c1,c2), next)`. 6 gates. -/
def fp6addG (a0 a1 a2 b0 b1 b2 : C2) (fresh : Nat) : List VmConstraint2 × (C2 × C2 × C2) × Nat :=
  let (g0, c0, f0) := fp2addG a0 b0 fresh
  let (g1, c1, f1) := fp2addG a1 b1 f0
  let (g2, c2, f2) := fp2addG a2 b2 f1
  (g0 ++ g1 ++ g2, (c0, c1, c2), f2)

/-- Fp6 sub (fresh-threaded). 6 gates. -/
def fp6subG (a0 a1 a2 b0 b1 b2 : C2) (fresh : Nat) : List VmConstraint2 × (C2 × C2 × C2) × Nat :=
  let (g0, c0, f0) := fp2subG a0 b0 fresh
  let (g1, c1, f1) := fp2subG a1 b1 f0
  let (g2, c2, f2) := fp2subG a2 b2 f1
  (g0 ++ g1 ++ g2, (c0, c1, c2), f2)

/-- Fp6 `×γ` (`×v`): `(ξ·c2, c0, c1)` — one `mulByXi` + relabel. 2 gates. -/
def fp6gammaG (c0 c1 c2 : C2) (fresh : Nat) : List VmConstraint2 × (C2 × C2 × C2) × Nat :=
  let (g, x, f) := fp2xiG c2 fresh
  (g, (x, c0, c1), f)

/-- **`fp12MulGadget`** — Fp12 multiplication (Karatsuba over Fp6 + the `w²=v` fold), COMPOSED from
`fp6MulGadget`/`fp6addG`/`fp6subG`/`fp6gammaG`. Inputs `a0,a1,b0,b1 : Fp6` (each 3 Fp2 = a triple of
`C2`); returns `(constraints, (d0,d1), next fresh)`. 296 gates. -/
def fp12MulGadget (a0 a1 b0 b1 : C2 × C2 × C2) (fresh : Nat) :
    List VmConstraint2 × ((C2 × C2 × C2) × (C2 × C2 × C2)) × Nat :=
  let (gv0, v0, f0) := fp6MulGadget a0.1 a0.2.1 a0.2.2 b0.1 b0.2.1 b0.2.2 fresh
  let (gv1, v1, f1) := fp6MulGadget a1.1 a1.2.1 a1.2.2 b1.1 b1.2.1 b1.2.2 f0
  let (gsa, sa, f2) := fp6addG a0.1 a0.2.1 a0.2.2 a1.1 a1.2.1 a1.2.2 f1
  let (gsb, sb, f3) := fp6addG b0.1 b0.2.1 b0.2.2 b1.1 b1.2.1 b1.2.2 f2
  let (gv2, v2, f4) := fp6MulGadget sa.1 sa.2.1 sa.2.2 sb.1 sb.2.1 sb.2.2 f3
  let (gg, gv1v, f5) := fp6gammaG v1.1 v1.2.1 v1.2.2 f4
  let (gd0, d0, f6) := fp6addG v0.1 v0.2.1 v0.2.2 gv1v.1 gv1v.2.1 gv1v.2.2 f5
  let (gw, w, f7) := fp6addG v0.1 v0.2.1 v0.2.2 v1.1 v1.2.1 v1.2.2 f6
  let (gd1, d1, f8) := fp6subG v2.1 v2.2.1 v2.2.2 w.1 w.2.1 w.2.2 f7
  (gv0 ++ gv1 ++ gsa ++ gsb ++ gv2 ++ gg ++ gd0 ++ gw ++ gd1, (d0, d1), f8)

/-! ## §3 — G1 / G2 point gadgets (GENERATED, the curve layer). -/

/-- **`g1DoubleGadget`** — Jacobian `[2]P` over Fp, 21 gates composed from `fp{Mul,Add,Sub}Core`.
Inputs `X,Y,Z`; scratch/outputs from `S` (layout in §5's `g1DoubleAsg`). Outputs `X3=S+156`,
`Y3=S+234`, `Z3=S+260`. Scalars (2·, 3·, 8·) are `nAdd` chains. -/
def g1DoubleGadget (X Y Z S : Nat) : List VmConstraint2 :=
  let A := S; let B := S + 13; let C := S + 26; let XB := S + 39; let XB2 := S + 52
  let T1 := S + 65; let T2 := S + 78; let D := S + 91; let A2 := S + 104; let E := S + 117
  let F := S + 130; let D2 := S + 143; let X3 := S + 156; let DX3 := S + 169; let EE := S + 182
  let C2c := S + 195; let C4 := S + 208; let C8 := S + 221; let Y3 := S + 234; let YZ := S + 247
  let Z3 := S + 260
  let qA := S + 273; let qB := S + 286; let qC := S + 299; let qXB2 := S + 312; let qF := S + 325
  let qEE := S + 338; let qYZ := S + 351
  let cXB := S + 364; let bT1 := S + 365; let bT2 := S + 366; let cD := S + 367; let cA2 := S + 368
  let cE := S + 369; let cD2 := S + 370; let bX3 := S + 371; let bDX3 := S + 372; let cC2 := S + 373
  let cC4 := S + 374; let cC8 := S + 375; let bY3 := S + 376; let cZ3 := S + 377
  [ fpMulCore X X A qA          -- A = X²
  , fpMulCore Y Y B qB          -- B = Y²
  , fpMulCore B B C qC          -- C = B²
  , fpAddCore X B XB cXB        -- XB = X+B
  , fpMulCore XB XB XB2 qXB2    -- XB2 = XB²
  , fpSubCore XB2 A T1 bT1      -- T1 = XB2 − A
  , fpSubCore T1 C T2 bT2       -- T2 = T1 − C      (= inner)
  , fpAddCore T2 T2 D cD        -- D = 2·inner
  , fpAddCore A A A2 cA2        -- A2 = 2A
  , fpAddCore A2 A E cE         -- E = 3A
  , fpMulCore E E F qF          -- F = E²
  , fpAddCore D D D2 cD2        -- D2 = 2D
  , fpSubCore F D2 X3 bX3       -- X3 = F − 2D
  , fpSubCore D X3 DX3 bDX3     -- DX3 = D − X3
  , fpMulCore E DX3 EE qEE      -- EE = E·(D−X3)
  , fpAddCore C C C2c cC2       -- C2 = 2C
  , fpAddCore C2c C2c C4 cC4    -- C4 = 4C
  , fpAddCore C4 C4 C8 cC8      -- C8 = 8C
  , fpSubCore EE C8 Y3 bY3      -- Y3 = EE − 8C
  , fpMulCore Y Z YZ qYZ        -- YZ = Y·Z
  , fpAddCore YZ YZ Z3 cZ3 ]    -- Z3 = 2·Y·Z

/-- **`g1AddGadget`** — Jacobian `P+Q` over Fp, composed from `fp{Mul,Add,Sub}Core` (fresh-threaded).
Returns `(constraints, (X3,Y3,Z3) bases, next fresh)`. -/
def g1AddGadget (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  -- allocate one limb-group (13) per intermediate/output, one bit per carry/borrow, in order
  let Z1Z1 := fresh; let Z2Z2 := fresh+13; let U1 := fresh+26; let U2 := fresh+39
  let Y1Z2 := fresh+52; let S1 := fresh+65; let Y2Z1 := fresh+78; let S2 := fresh+91
  let H := fresh+104; let twoH := fresh+117; let I := fresh+130; let J := fresh+143
  let S2S1 := fresh+156; let r := fresh+169; let V := fresh+182; let rr := fresh+195
  let rrJ := fresh+208; let twoV := fresh+221; let X3 := fresh+234; let VX3 := fresh+247
  let rVX3 := fresh+260; let S1J := fresh+273; let twoS1J := fresh+286; let Y3 := fresh+299
  let Z1Z2 := fresh+312; let Z1Z2s := fresh+325; let t1 := fresh+338; let t2 := fresh+351
  let Z3 := fresh+364
  let q := fresh+377            -- 16 quotient groups (muls) 13 each: fresh+377 .. fresh+377+16*13-1
  let b := q + 16*13           -- carry/borrow bits region
  let cs : List VmConstraint2 :=
    [ fpMulCore Z1 Z1 Z1Z1 (q)
    , fpMulCore Z2 Z2 Z2Z2 (q+13)
    , fpMulCore X1 Z2Z2 U1 (q+26)
    , fpMulCore X2 Z1Z1 U2 (q+39)
    , fpMulCore Y1 Z2 Y1Z2 (q+52)
    , fpMulCore Y1Z2 Z2Z2 S1 (q+65)
    , fpMulCore Y2 Z1 Y2Z1 (q+78)
    , fpMulCore Y2Z1 Z1Z1 S2 (q+91)
    , fpSubCore U2 U1 H (b)
    , fpAddCore H H twoH (b+1)
    , fpMulCore twoH twoH I (q+104)
    , fpMulCore H I J (q+117)
    , fpSubCore S2 S1 S2S1 (b+2)
    , fpAddCore S2S1 S2S1 r (b+3)
    , fpMulCore U1 I V (q+130)
    , fpMulCore r r rr (q+143)
    , fpSubCore rr J rrJ (b+4)
    , fpAddCore V V twoV (b+5)
    , fpSubCore rrJ twoV X3 (b+6)
    , fpSubCore V X3 VX3 (b+7)
    , fpMulCore r VX3 rVX3 (q+156)
    , fpMulCore S1 J S1J (q+169)
    , fpAddCore S1J S1J twoS1J (b+8)
    , fpSubCore rVX3 twoS1J Y3 (b+9)
    , fpAddCore Z1 Z2 Z1Z2 (b+10)
    , fpMulCore Z1Z2 Z1Z2 Z1Z2s (q+182)
    , fpSubCore Z1Z2s Z1Z1 t1 (b+11)
    , fpSubCore t1 Z2Z2 t2 (b+12)
    , fpMulCore t2 H Z3 (q+195) ]
  (cs, (X3, Y3, Z3), b + 13)

/-! ### G2 gadgets — the Fp2-lifted curve ops (fresh-threaded, composing the §1 Fp2 gadgets). -/

/-- Scalar `k·(x0+x1 u)` for a SMALL `k`, as an `nAdd` chain doubling — here only `k∈{2}` (via a
single add). For `k=3`/`k=8` the caller chains `fp2addG`. This wrapper is the `k=2` case. -/
def fp2dblG (x : C2) (fresh : Nat) : List VmConstraint2 × C2 × Nat := fp2addG x x fresh

/-- **`g2DoubleGadget`** — Jacobian `[2]P` over Fp2, composed from the §1 Fp2 gadgets (scalars via
`fp2addG` chains). Returns `(constraints, (X3,Y3,Z3) : P2-bases, next fresh)`. -/
def g2DoubleGadget (X Y Z : C2) (fresh : Nat) : List VmConstraint2 × (C2 × C2 × C2) × Nat :=
  let (gA, A, f0) := fp2mulG X X fresh
  let (gB, B, f1) := fp2mulG Y Y f0
  let (gC, C, f2) := fp2mulG B B f1
  let (gXB, XB, f3) := fp2addG X B f2
  let (gXB2, XB2, f4) := fp2mulG XB XB f3
  let (gT1, T1, f5) := fp2subG XB2 A f4
  let (gT2, T2, f6) := fp2subG T1 C f5
  let (gD, D, f7) := fp2dblG T2 f6            -- D = 2·inner
  let (gA2, A2, f8) := fp2dblG A f7
  let (gE, E, f9) := fp2addG A2 A f8          -- E = 3A
  let (gF, F, fa) := fp2mulG E E f9
  let (gD2, D2, fb) := fp2dblG D fa           -- D2 = 2D
  let (gX3, X3, fc) := fp2subG F D2 fb        -- X3 = F − 2D
  let (gDX3, DX3, fd) := fp2subG D X3 fc
  let (gEE, EE, fe) := fp2mulG E DX3 fd
  let (gC2, C2, ff) := fp2dblG C fe
  let (gC4, C4, fg) := fp2dblG C2 ff
  let (gC8, C8, fh) := fp2dblG C4 fg          -- C8 = 8C
  let (gY3, Y3, fi) := fp2subG EE C8 fh       -- Y3 = EE − 8C
  let (gYZ, YZ, fj) := fp2mulG Y Z fi
  let (gZ3, Z3, fk) := fp2dblG YZ fj          -- Z3 = 2YZ
  ( gA ++ gB ++ gC ++ gXB ++ gXB2 ++ gT1 ++ gT2 ++ gD ++ gA2 ++ gE ++ gF ++ gD2 ++ gX3 ++ gDX3
      ++ gEE ++ gC2 ++ gC4 ++ gC8 ++ gY3 ++ gYZ ++ gZ3
  , (X3, Y3, Z3), fk )

/-- **`g2AddGadget`** — Jacobian `P+Q` over Fp2, composed from the §1 Fp2 gadgets. Returns
`(constraints, (X3,Y3,Z3), next fresh)`. -/
def g2AddGadget (X1 Y1 Z1 X2 Y2 Z2 : C2) (fresh : Nat) : List VmConstraint2 × (C2 × C2 × C2) × Nat :=
  let (g0, Z1Z1, f0) := fp2mulG Z1 Z1 fresh
  let (g1, Z2Z2, f1) := fp2mulG Z2 Z2 f0
  let (g2, U1, f2) := fp2mulG X1 Z2Z2 f1
  let (g3, U2, f3) := fp2mulG X2 Z1Z1 f2
  let (g4, Y1Z2, f4) := fp2mulG Y1 Z2 f3
  let (g5, S1, f5) := fp2mulG Y1Z2 Z2Z2 f4
  let (g6, Y2Z1, f6) := fp2mulG Y2 Z1 f5
  let (g7, S2, f7) := fp2mulG Y2Z1 Z1Z1 f6
  let (g8, H, f8) := fp2subG U2 U1 f7
  let (g9, twoH, f9) := fp2dblG H f8
  let (ga, I, fa) := fp2mulG twoH twoH f9
  let (gb, J, fb) := fp2mulG H I fa
  let (gc, S2S1, fc) := fp2subG S2 S1 fb
  let (gd, r, fd) := fp2dblG S2S1 fc
  let (ge, V, fe) := fp2mulG U1 I fd
  let (gf, rr, ff) := fp2mulG r r fe
  let (gg, rrJ, fg) := fp2subG rr J ff
  let (gh, twoV, fh) := fp2dblG V fg
  let (gi, X3, fi) := fp2subG rrJ twoV fh
  let (gj, VX3, fj) := fp2subG V X3 fi
  let (gk, rVX3, fk) := fp2mulG r VX3 fj
  let (gl, S1J, fl) := fp2mulG S1 J fk
  let (gm, twoS1J, fm) := fp2dblG S1J fl
  let (gn, Y3, fn) := fp2subG rVX3 twoS1J fm
  let (go, Z1Z2, fo) := fp2addG Z1 Z2 fn
  let (gp, Z1Z2s, fp) := fp2mulG Z1Z2 Z1Z2 fo
  let (gq, t1, fq) := fp2subG Z1Z2s Z1Z1 fp
  let (gr, t2, fr) := fp2subG t1 Z2Z2 fq
  let (gs, Z3, fs) := fp2mulG t2 H fr
  ( g0 ++ g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9 ++ ga ++ gb ++ gc ++ gd ++ ge ++ gf
      ++ gg ++ gh ++ gi ++ gj ++ gk ++ gl ++ gm ++ gn ++ go ++ gp ++ gq ++ gr ++ gs
  , (X3, Y3, Z3), fs )

/-! ## §4 — Forcing: the ξ-multiply gadget forces its Fp2 congruence (composing the Fp gate forcings). -/

/-- **`mulByXi` forces the ξ-multiply**: `r0 ≡ x0 − x1` and `r1 ≡ x0 + x1` (mod `p`) — the two Fp
coordinates of `(x0+x1 u)(u+1)`. Directly from `Bls12381Tower`'s `nSub/fpAddCore_forces`. -/
theorem mulByXi_forces (a : Assignment) (x0 x1 r0 r1 br cr : Nat)
    (hs : evalH (fpSubHead x0 x1 r0 br) a = 0)
    (ha : evalH (fpAddHead x0 x1 r1 cr) a = 0) :
    (p : ℤ) ∣ (fpVal a x0 - fpVal a x1 - fpVal a r0)
    ∧ (p : ℤ) ∣ (fpVal a x0 + fpVal a x1 - fpVal a r1) :=
  ⟨fpSubCore_forces a x0 x1 r0 br hs, fpAddCore_forces a x0 x1 r1 cr ha⟩

#assert_axioms mulByXi_forces

/-! ## §5 — KAT: generated gates ACCEPT the honest witness and REJECT tamper (both polarities).

Reuses `Bls12381Tower.acceptB` / `bumpAt` / `limbOf`. Witnesses are reference-derived. -/

open Bls12381Tower (acceptB bumpAt)

/-! ### `mulByXi` — layout x0=0, x1=13, r0=26, r1=39, br=52, cr=53. -/

def mulByXiAsg (x0v x1v : Nat) : Assignment := fun col =>
  let r0 := nSub x0v x1v
  let r1 := nAdd x0v x1v
  let br := (r0 + x1v - x0v) / pN
  let cr := (x0v + x1v - r1) / pN
  if col < 13 then limbOf x0v col
  else if col < 26 then limbOf x1v (col - 13)
  else if col < 39 then limbOf r0 (col - 26)
  else if col < 52 then limbOf r1 (col - 39)
  else if col = 52 then (br : ℤ)
  else if col = 53 then (cr : ℤ)
  else 0

def mulByXiGad : List VmConstraint2 := mulByXiGadget 0 13 26 39 52 53

#guard acceptB mulByXiGad (mulByXiAsg 12345 999) == true
#guard acceptB mulByXiGad (bumpAt (mulByXiAsg 12345 999) 26) == false   -- bump r0
#guard acceptB mulByXiGad (bumpAt (mulByXiAsg 12345 999) 39) == false   -- bump r1
-- carry/borrow exercised: x0 < x1 forces a borrow in r0, and x0+x1 no overflow here
#guard acceptB mulByXiGad (mulByXiAsg 999 12345) == true                -- borrow=1 case

/-! ### `fp6Add` — 6 independent `fpAddCore` over 6 Fp coords. Layout a:0..5·13, b:6·13.., r:12·13.., carries after. -/

def fp6AddAsg (av bv : List Nat) : Assignment := fun col =>
  -- a limbs at [0,78), b at [78,156), r at [156,234), carries at 234..239
  if col < 78 then limbOf (av.getD (col / 13) 0) (col % 13)
  else if col < 156 then limbOf (bv.getD ((col - 78) / 13) 0) ((col - 78) % 13)
  else if col < 234 then
    let i := (col - 156) / 13
    limbOf (nAdd (av.getD i 0) (bv.getD i 0)) ((col - 156) % 13)
  else if col < 240 then
    let i := col - 234
    let z := nAdd (av.getD i 0) (bv.getD i 0)
    (((av.getD i 0 + bv.getD i 0 - z) / pN : Nat) : ℤ)
  else 0

-- Fp6-add gadget over the KAT layout (a:0..5, b:6..11 as WORD bases 13·i; carries 234+i).
def fp6AddGadKAT : List VmConstraint2 :=
  (List.range 6).map (fun i => fpAddCore (13 * i) (78 + 13 * i) (156 + 13 * i) (234 + i))

def av6 : List Nat := [111, 222, 333, 444, 555, 666]
def bv6 : List Nat := [777, 888, 999, 1010, 1111, 1212]

#guard acceptB fp6AddGadKAT (fp6AddAsg av6 bv6) == true
#guard acceptB fp6AddGadKAT (bumpAt (fp6AddAsg av6 bv6) 156) == false   -- bump r[0] limb 0
#guard acceptB fp6AddGadKAT (bumpAt (fp6AddAsg av6 bv6) 195) == false   -- bump r[3] limb 0

/-! ### `g1Double` — the WHOLE 21-gate Jacobian doubling. Inputs X=0,Y=13,Z=26; scratch S=39. -/

def g1DoubleAsg (Xv Yv Zv : Nat) : Assignment := fun col =>
  let A := R.m Xv Xv; let B := R.m Yv Yv; let C := R.m B B
  let XB := R.ad Xv B; let XB2 := R.m XB XB
  let T1 := R.sb XB2 A; let T2 := R.sb T1 C
  let D := R.ad T2 T2; let A2 := R.ad A A; let E := R.ad A2 A
  let F := R.m E E; let D2 := R.ad D D; let X3 := R.sb F D2
  let DX3 := R.sb D X3; let EE := R.m E DX3
  let C2 := R.ad C C; let C4 := R.ad C2 C2; let C8 := R.ad C4 C4
  let Y3 := R.sb EE C8; let YZ := R.m Yv Zv; let Z3 := R.ad YZ YZ
  let qA := (Xv * Xv - A) / pN; let qB := (Yv * Yv - B) / pN; let qC := (B * B - C) / pN
  let qXB2 := (XB * XB - XB2) / pN; let qF := (E * E - F) / pN
  let qEE := (E * DX3 - EE) / pN; let qYZ := (Yv * Zv - YZ) / pN
  let cXB := (Xv + B - XB) / pN; let bT1 := (T1 + A - XB2) / pN; let bT2 := (T2 + C - T1) / pN
  let cD := (T2 + T2 - D) / pN; let cA2 := (A + A - A2) / pN; let cE := (A2 + A - E) / pN
  let cD2 := (D + D - D2) / pN; let bX3 := (X3 + D2 - F) / pN; let bDX3 := (DX3 + X3 - D) / pN
  let cC2 := (C + C - C2) / pN; let cC4 := (C2 + C2 - C4) / pN; let cC8 := (C4 + C4 - C8) / pN
  let bY3 := (Y3 + C8 - EE) / pN; let cZ3 := (YZ + YZ - Z3) / pN
  if col < 13 then limbOf Xv col
  else if col < 26 then limbOf Yv (col - 13)
  else if col < 39 then limbOf Zv (col - 26)
  else if col < 52 then limbOf A (col - 39)
  else if col < 65 then limbOf B (col - 52)
  else if col < 78 then limbOf C (col - 65)
  else if col < 91 then limbOf XB (col - 78)
  else if col < 104 then limbOf XB2 (col - 91)
  else if col < 117 then limbOf T1 (col - 104)
  else if col < 130 then limbOf T2 (col - 117)
  else if col < 143 then limbOf D (col - 130)
  else if col < 156 then limbOf A2 (col - 143)
  else if col < 169 then limbOf E (col - 156)
  else if col < 182 then limbOf F (col - 169)
  else if col < 195 then limbOf D2 (col - 182)
  else if col < 208 then limbOf X3 (col - 195)
  else if col < 221 then limbOf DX3 (col - 208)
  else if col < 234 then limbOf EE (col - 221)
  else if col < 247 then limbOf C2 (col - 234)
  else if col < 260 then limbOf C4 (col - 247)
  else if col < 273 then limbOf C8 (col - 260)
  else if col < 286 then limbOf Y3 (col - 273)
  else if col < 299 then limbOf YZ (col - 286)
  else if col < 312 then limbOf Z3 (col - 299)
  else if col < 325 then limbOf qA (col - 312)
  else if col < 338 then limbOf qB (col - 325)
  else if col < 351 then limbOf qC (col - 338)
  else if col < 364 then limbOf qXB2 (col - 351)
  else if col < 377 then limbOf qF (col - 364)
  else if col < 390 then limbOf qEE (col - 377)
  else if col < 403 then limbOf qYZ (col - 390)
  else if col = 403 then (cXB : ℤ)
  else if col = 404 then (bT1 : ℤ)
  else if col = 405 then (bT2 : ℤ)
  else if col = 406 then (cD : ℤ)
  else if col = 407 then (cA2 : ℤ)
  else if col = 408 then (cE : ℤ)
  else if col = 409 then (cD2 : ℤ)
  else if col = 410 then (bX3 : ℤ)
  else if col = 411 then (bDX3 : ℤ)
  else if col = 412 then (cC2 : ℤ)
  else if col = 413 then (cC4 : ℤ)
  else if col = 414 then (cC8 : ℤ)
  else if col = 415 then (bY3 : ℤ)
  else if col = 416 then (cZ3 : ℤ)
  else 0

/-- The doubling gadget at the KAT layout (X=0,Y=13,Z=26,S=39). -/
def g1DoubleGad : List VmConstraint2 := g1DoubleGadget 0 13 26 39

-- Honest witness: the affine generator with Z=1 doubled (a real curve point trace).
#guard acceptB g1DoubleGad (g1DoubleAsg R.G1gen.1 R.G1gen.2.1 1) == true
#guard acceptB g1DoubleGad (bumpAt (g1DoubleAsg R.G1gen.1 R.G1gen.2.1 1) 195) == false  -- bump X3
#guard acceptB g1DoubleGad (bumpAt (g1DoubleAsg R.G1gen.1 R.G1gen.2.1 1) 299) == false  -- bump Z3
-- A second, generic point (still a valid trace of the arithmetic).
#guard acceptB g1DoubleGad (g1DoubleAsg 123456789 987654321 555) == true
#guard acceptB g1DoubleGad (bumpAt (g1DoubleAsg 123456789 987654321 555) 273) == false       -- bump Y3

/-! ## §6 — Structural `#guard`s: the generators produce the budgeted gate counts. -/

#guard mulByXiGad.length == 2
#guard fp6AddGadKAT.length == 6
#guard g1DoubleGad.length == 21
#guard (fp6MulGadget (0,1) (2,3) (4,5) (6,7) (8,9) (10,11) 1000).1.length == 88
#guard (fp12MulGadget ((0,1),(2,3),(4,5)) ((6,7),(8,9),(10,11)) ((12,13),(14,15),(16,17))
          ((18,19),(20,21),(22,23)) 2000).1.length == 296
#guard (g1AddGadget 0 13 26 39 52 65 1000).1.length == 29
#guard (g2DoubleGadget (0,1) (2,3) (4,5) 1000).1.length == 84
#guard (g2AddGadget (0,1) (2,3) (4,5) (6,7) (8,9) (10,11) 1000).1.length == 154

/-- An `fp6Mul` gadget packaged as an `EffectVmDescriptor2` (drops into the deployed vocabulary). -/
def fp6MulDesc : EffectVmDescriptor2 :=
  { name        := "dregg-bls12381-fp6mul::demo"
  , traceWidth  := 2000
  , piCount     := 0
  , tables      := []
  , constraints := (fp6MulGadget (0,1) (2,3) (4,5) (6,7) (8,9) (10,11) 100).1
  , hashSites   := []
  , ranges      := [] }

#guard fp6MulDesc.constraints.length == 88

/-! ## §7 — The last mile to a folded BLS_OK (NOT built — the pairing's final arc, ~millions of gates).

With Fp2/Fp6/Fp12 + G1/G2 dbl/add GENERATED + KAT'd here, what remains is:

  1. **The Miller loop** — iterate the BLS12-381 loop parameter's ~64 bits: each bit a G2 DOUBLING
     (`g2DoubleGadget`) + a line evaluation (a sparse Fp12 element from the tangent, in the G1 point's
     coordinates) + an Fp12 SQUARING (cyclotomic; cheaper than `fp12MulGadget`) + a sparse Fp12
     multiply-in; set bits add a G2 ADDITION (`g2AddGadget`) + its line. All the pieces are the
     gadgets above composed. ≈ `64 · O(10)` Fp12 ops ≈ `10⁷` gates.
  2. **The final exponentiation** — `f^((p¹²−1)/r)`: the easy part (`f^(p⁶−1)·(p²+1)`, a Frobenius +
     one Fp12 inversion — a witnessed-inverse gate `f·f⁻¹ = 1` over `fp12MulGadget`) then the hard
     part (a fixed addition chain in the loop parameter of cyclotomic squarings + `fp12MulGadget`s).
     ≈ `10⁶`–`10⁷` gates.
  3. **Aggregate-verify wiring (the `BLS_OK` rewrite)** — `e(sig, g2)` and `e(H(m), agg_pk)` via two
     Miller-loop+final-exp instances, an Fp12 EQUALITY gate (coordinate-for-coordinate), `agg_pk =
     Σ pk_i` (G1 adds over the sync-committee participation bits, `g1AddGadget`), and `H(m)` the
     hash-to-G2. This is the constraint set `BLS_OK` would be DERIVED from, dropping the trusted bit.

A single sync-committee aggregate pairing check is on the order of **millions of AIR gates** — the
accepted zk-STARK cost. This file is the tower+curve floor under that arc; it does NOT claim a pairing
or a folded `BLS_OK`. The next mechanical step is the Miller-loop composition of these gadgets.
-/

end Dregg2.Circuit.Emit.Bls12381TowerExt
