/-
# Market.CertQpDescriptor — Lean-authored fixed-shape exact-integer CertQp AIR.

This is the first deployed descriptor stone for the real fhIR product
`portfolio_qp_public()`: six assets, seven OSQP rows (budget + six box rows), and
the exact rounded public `(P,q,A,l,u,epsilon)` baked into the descriptor.  The
private trace carries only `(x,y)` plus algebraic slacks/selectors.  It enforces
all three clauses of `CertQpExact::check`:

* primal interval residual;
* stationarity residual;
* normal-cone / projection residual.

The registered scale is `10^3`, not the runner's `10^9`.  At `10^3` every
complete gate residual is in the unique BabyBear zero-residue window under the
descriptor's enforced 10-bit primal / 12-bit shifted-dual policy and 24-bit
slack table.  A `10^9` registration needs multi-limb products, carries, and
comparators; that generalization is named rather than papered over.  As with
`CertQpRustDenotation`, PSD is a separate public-program compile gate.  This AIR
certifies the rounded fixed-point problem, not the source f64 problem.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Market.CertFDescriptor
import Market.CertQpGolden
import Market.CertQpRustDenotation
import Dregg2.Circuit.GateExpr

namespace Market.CertQpDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
open Market.CertFDescriptor
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

/-! ## 1. The fixed public program. -/

def qpN : Nat := 6
def qpMc : Nat := 7
def qpScaleDigits : Nat := 3
def qpScale : Int := 1000
def qpTolerance : Int := 1000 -- epsilon(=1 tick) * scale, at S^2
def qpEpsilon : Int := 1
def qpYShift : Int := 2048
def qpRangeBits : Nat := 24
def qpXBits : Nat := 10
def qpYBits : Nat := 12

/-- `portfolio_qp_public()` covariance rounded entrywise at `10^-3`, row-major. -/
def portfolioP : List Int :=
  [1000,100,67,50,40,33,
   100,1100,100,67,50,40,
   67,100,1200,100,67,50,
   50,67,100,1300,100,67,
   40,50,67,100,1400,100,
   33,40,50,67,100,1500]

/-- `q=-5*mu`, `mu_i=0.05+0.02i`, rounded at `10^-3`. -/
def portfolioQ : List Int := [-250,-350,-450,-550,-650,-750]

/-- Budget row followed by six identity rows, every coefficient at scale `S`. -/
def portfolioA : List Int :=
  [1000,1000,1000,1000,1000,1000,
   1000,0,0,0,0,0,
   0,1000,0,0,0,0,
   0,0,1000,0,0,0,
   0,0,0,1000,0,0,
   0,0,0,0,1000,0,
   0,0,0,0,0,1000]

def portfolioL : List Int := [1000,0,0,0,0,0,0]
def portfolioU : List Int := [1000,400,400,400,400,400,400]

structure CertQpProg where
  n : Nat
  mc : Nat
  scaleDigits : Nat
  scale : Int
  p : List Int
  q : List Int
  a : List Int
  l : List Int
  u : List Int
  epsilon : Int

def portfolioProg : CertQpProg :=
  { n := qpN, mc := qpMc, scaleDigits := qpScaleDigits, scale := qpScale
  , p := portfolioP, q := portfolioQ, a := portfolioA
  , l := portfolioL, u := portfolioU, epsilon := qpEpsilon }

namespace CertQpProg

def pAt (p : CertQpProg) (i j : Nat) : Int := p.p.getD (i * p.n + j) 0
def qAt (p : CertQpProg) (j : Nat) : Int := p.q.getD j 0
def aAt (p : CertQpProg) (i j : Nat) : Int := p.a.getD (i * p.n + j) 0
def lAt (p : CertQpProg) (i : Nat) : Int := p.l.getD i 0
def uAt (p : CertQpProg) (i : Nat) : Int := p.u.getD i 0
def tol (p : CertQpProg) : Int := p.epsilon * p.scale

end CertQpProg

#guard portfolioProg.n == 6
#guard portfolioProg.mc == 7
#guard portfolioProg.p.length == 36
#guard portfolioProg.a.length == 42
#guard portfolioProg.tol == 1000

/-! ## 2. Exact checker semantics (the integer carrier Rust executes). -/

structure FixedWitness (p : CertQpProg) where
  x : Fin p.n → Int
  y : Fin p.mc → Int

def ax (p : CertQpProg) (w : FixedWitness p) (i : Fin p.mc) : Int :=
  ∑ j : Fin p.n, p.aAt i j * w.x j

def stat (p : CertQpProg) (w : FixedWitness p) (j : Fin p.n) : Int :=
  (∑ k : Fin p.n, p.pAt j k * w.x k) + p.qAt j * p.scale +
    ∑ i : Fin p.mc, p.aAt i j * w.y i

def clampInt (z l u : Int) : Int := min (max z l) u

def projectionDiff (p : CertQpProg) (w : FixedWitness p) (i : Fin p.mc) : Int :=
  ax p w i - clampInt (ax p w i + w.y i * p.scale)
    (p.lAt i * p.scale) (p.uAt i * p.scale)

/-- The three exact clauses, pointwise.  This is the no-stored-flags denotation of
`CertQpExact::check`: every residual is recomputed from `(x,y)`. -/
structure ExactChecker (p : CertQpProg) (w : FixedWitness p) : Prop where
  primal : ∀ i : Fin p.mc, p.lAt i * p.scale - p.tol ≤ ax p w i ∧
    ax p w i ≤ p.uAt i * p.scale + p.tol
  stationarity : ∀ j : Fin p.n, -p.tol ≤ stat p w j ∧ stat p w j ≤ p.tol
  normalCone : ∀ i : Fin p.mc,
    -p.tol ≤ projectionDiff p w i ∧ projectionDiff p w i ≤ p.tol

/-! ## 3. Column layout. -/

def xCol (j : Nat) : Nat := j
def yCol (i : Nat) : Nat := qpN + i -- stores y + 2048
def primalLoCol (i : Nat) : Nat := qpN + qpMc + 2 * i
def primalHiCol (i : Nat) : Nat := qpN + qpMc + 2 * i + 1
def statLoCol (j : Nat) : Nat := qpN + qpMc + 2 * qpMc + 2 * j
def statHiCol (j : Nat) : Nat := qpN + qpMc + 2 * qpMc + 2 * j + 1
def normalBase : Nat := qpN + qpMc + 2 * qpMc + 2 * qpN
def normalStride : Nat := 10
def lowSelCol (i : Nat) : Nat := normalBase + normalStride * i
def midSelCol (i : Nat) : Nat := normalBase + normalStride * i + 1
def highSelCol (i : Nat) : Nat := normalBase + normalStride * i + 2
def lowRegionCol (i : Nat) : Nat := normalBase + normalStride * i + 3
def midLoRegionCol (i : Nat) : Nat := normalBase + normalStride * i + 4
def midHiRegionCol (i : Nat) : Nat := normalBase + normalStride * i + 5
def highRegionCol (i : Nat) : Nat := normalBase + normalStride * i + 6
def projCol (i : Nat) : Nat := normalBase + normalStride * i + 7
def normalLoCol (i : Nat) : Nat := normalBase + normalStride * i + 8
def normalHiCol (i : Nat) : Nat := normalBase + normalStride * i + 9
def returnCol : Nat := normalBase + normalStride * qpMc
def xUpperCol (j : Nat) : Nat := returnCol + 1 + j
def yUpperCol (i : Nat) : Nat := returnCol + 1 + qpN + i
def traceWidth : Nat := returnCol + 1 + qpN + qpMc

#guard traceWidth == 123

/-! ## 4. Expression and constraint generation. -/

def sumExpr (n : Nat) (f : Nat → EmittedExpr) : EmittedExpr :=
  (List.range n).foldl (fun acc i => .add acc (f i)) (.const 0)

def yExpr (i : Nat) : EmittedExpr :=
  esub (.var (yCol i)) (.const qpYShift)

def axExpr (p : CertQpProg) (i : Nat) : EmittedExpr :=
  sumExpr p.n fun j => .mul (.const (p.aAt i j)) (.var (xCol j))

def statExpr (p : CertQpProg) (j : Nat) : EmittedExpr :=
  .add
    (.add (sumExpr p.n fun k => .mul (.const (p.pAt j k)) (.var (xCol k)))
      (.const (p.qAt j * p.scale)))
    (sumExpr p.mc fun i => .mul (.const (p.aAt i j)) (yExpr i))

def shiftedExpr (p : CertQpProg) (i : Nat) : EmittedExpr :=
  .add (axExpr p i) (.mul (yExpr i) (.const p.scale))

def rangeLookup (col : Nat) : VmConstraint2 :=
  .lookup ⟨.range, [.var col]⟩

/- Named gate bodies are deliberately shared by emission and soundness below.  This
prevents the semantic bridge from proving facts about a hand-copied lookalike. -/
def upperBoundBody (col upperCol : Nat) (upper : Int) : EmittedExpr :=
  esub (.var upperCol) (esub (.const upper) (.var col))

def primalLoBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  esub (.var (primalLoCol i))
    (esub (axExpr p i) (.const (p.lAt i * p.scale - p.tol)))

def primalHiBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  esub (.var (primalHiCol i))
    (esub (.const (p.uAt i * p.scale + p.tol)) (axExpr p i))

def statLoBody (p : CertQpProg) (j : Nat) : EmittedExpr :=
  esub (.var (statLoCol j)) (.add (.const p.tol) (statExpr p j))

def statHiBody (p : CertQpProg) (j : Nat) : EmittedExpr :=
  esub (.var (statHiCol j)) (esub (.const p.tol) (statExpr p j))

def selectorBoolBody (col : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf col))

theorem selectorBoolBody_eq (col : Nat) :
    selectorBoolBody col = .mul (.var col) (esub (.var col) (.const 1)) := rfl

def selectorSumBody (i : Nat) : EmittedExpr :=
  esub (.add (.add (.var (lowSelCol i)) (.var (midSelCol i)))
    (.var (highSelCol i))) (.const 1)

def lowRegionBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  .mul (.var (lowSelCol i))
    (esub (.var (lowRegionCol i))
      (esub (.const (p.lAt i * p.scale)) (shiftedExpr p i)))

def midLoRegionBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  .mul (.var (midSelCol i))
    (esub (.var (midLoRegionCol i))
      (esub (shiftedExpr p i) (.const (p.lAt i * p.scale))))

def midHiRegionBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  .mul (.var (midSelCol i))
    (esub (.var (midHiRegionCol i))
      (esub (.const (p.uAt i * p.scale)) (shiftedExpr p i)))

def highRegionBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  .mul (.var (highSelCol i))
    (esub (.var (highRegionCol i))
      (esub (shiftedExpr p i) (.const (p.uAt i * p.scale))))

def projectionBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  esub (.var (projCol i))
    (.add (.add (.mul (.var (lowSelCol i)) (.const (p.lAt i * p.scale)))
                (.mul (.var (midSelCol i)) (shiftedExpr p i)))
          (.mul (.var (highSelCol i)) (.const (p.uAt i * p.scale))))

def normalLoBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  esub (.var (normalLoCol i))
    (.add (.const p.tol) (esub (axExpr p i) (.var (projCol i))))

def normalHiBody (p : CertQpProg) (i : Nat) : EmittedExpr :=
  esub (.var (normalHiCol i))
    (esub (.const p.tol) (esub (axExpr p i) (.var (projCol i))))

/-- Bound `0 <= col <= upper` using the faithful 24-bit table twice and the
exact affine equation `upperSlack = upper-col`.  This avoids hundreds of
descriptor-local bit columns while retaining a small enough no-wrap window. -/
def boundedRangeConstraints (col upperCol : Nat) (upper : Int) : List VmConstraint2 :=
  [ egate (upperBoundBody col upperCol upper)
  , rangeLookup col, rangeLookup upperCol ]

def primalConstraints (p : CertQpProg) : List VmConstraint2 :=
  ((List.range p.mc).map fun i =>
    [ egate (primalLoBody p i)
    , egate (primalHiBody p i)
    , rangeLookup (primalLoCol i)
    , rangeLookup (primalHiCol i) ]).flatten

def stationarityConstraints (p : CertQpProg) : List VmConstraint2 :=
  ((List.range p.n).map fun j =>
    [ egate (statLoBody p j)
    , egate (statHiBody p j)
    , rangeLookup (statLoCol j)
    , rangeLookup (statHiCol j) ]).flatten

def selectorConstraints (i : Nat) : List VmConstraint2 :=
  [ egate (selectorBoolBody (lowSelCol i))
  , egate (selectorBoolBody (midSelCol i))
  , egate (selectorBoolBody (highSelCol i))
  , egate (selectorSumBody i) ]

def normalConstraintsAt (p : CertQpProg) (i : Nat) : List VmConstraint2 :=
  selectorConstraints i ++
  [ -- selected region inequalities, witnessed by non-negative range-table slacks
    egate (lowRegionBody p i)
  , egate (midLoRegionBody p i)
  , egate (midHiRegionBody p i)
  , egate (highRegionBody p i)
  , -- projected = low*l + mid*shifted + high*u
    egate (projectionBody p i)
  , -- |z-projected| <= tolerance
    egate (normalLoBody p i)
  , egate (normalHiBody p i)
  ] ++
  [ rangeLookup (lowRegionCol i), rangeLookup (midLoRegionCol i)
  , rangeLookup (midHiRegionCol i), rangeLookup (highRegionCol i)
  , rangeLookup (projCol i), rangeLookup (normalLoCol i), rangeLookup (normalHiCol i) ]

def normalConstraints (p : CertQpProg) : List VmConstraint2 :=
  ((List.range p.mc).map fun i => normalConstraintsAt p i).flatten

def returnExpr (p : CertQpProg) : EmittedExpr :=
  sumExpr p.n fun j => .mul (.const (-p.qAt j)) (.var (xCol j))

def returnBody (p : CertQpProg) : EmittedExpr :=
  esub (.var returnCol) (returnExpr p)

def xBoundConstraints (p : CertQpProg) : List VmConstraint2 :=
  ((List.range p.n).map fun j =>
    boundedRangeConstraints (xCol j) (xUpperCol j) (2 ^ qpXBits - 1)).flatten

def yBoundConstraints (p : CertQpProg) : List VmConstraint2 :=
  ((List.range p.mc).map fun i =>
    boundedRangeConstraints (yCol i) (yUpperCol i) (2 ^ qpYBits - 1)).flatten

def certQpConstraints (p : CertQpProg) : List VmConstraint2 :=
  xBoundConstraints p
  ++ yBoundConstraints p
  ++ primalConstraints p
  ++ stationarityConstraints p
  ++ normalConstraints p
  ++ [ egate (returnBody p)
     , rangeLookup returnCol
     , .base (.piBinding .first returnCol 0) ]

/-- The complete Lean-authored descriptor.  `P,q,A,l,u,epsilon,scale` occur only
as expression constants; Rust receives no specialization authority. -/
def certQpDescriptorOf (p : CertQpProg) : EffectVmDescriptor2 :=
  { name := "cert-qp-portfolio6-s3"
  , traceWidth := traceWidth
  , piCount := 1
  , tables := [mainTableDef traceWidth, rangeTableDef qpRangeBits]
  , constraints := certQpConstraints p
  , hashSites := []
  , ranges := [] }

def portfolioDescriptor : EffectVmDescriptor2 := certQpDescriptorOf portfolioProg

#guard portfolioDescriptor.name == "cert-qp-portfolio6-s3"
#guard portfolioDescriptor.traceWidth == 123
#guard portfolioDescriptor.piCount == 1
#guard portfolioDescriptor.tables.length == 2
#guard portfolioDescriptor.hashSites.length == 0
#guard portfolioDescriptor.ranges.length == 0
#guard emitVmJson2 portfolioDescriptor == Market.CertQpGolden.CERT_QP_PORTFOLIO6_S3_GOLDEN

/-! ## 5. Semantic relation: not flags, the three recomputed clauses. -/

/-- An exact (integer, not merely modular) assignment to the descriptor's
auxiliary columns.  Every field is an equation/range used by the emitted AIR;
there are no trusted residual booleans. -/
structure ExactTrace (p : CertQpProg) (a : Assignment) : Prop where
  xBound : ∀ j < p.n, 0 ≤ a (xCol j) ∧ a (xCol j) < 2 ^ qpXBits
  yBound : ∀ i < p.mc, 0 ≤ a (yCol i) ∧ a (yCol i) < 2 ^ qpYBits
  primalLo : ∀ i < p.mc,
    a (primalLoCol i) =
      (∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) - (p.lAt i * p.scale - p.tol)
  primalHi : ∀ i < p.mc,
    a (primalHiCol i) =
      (p.uAt i * p.scale + p.tol) - (∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j))
  primalRanges : ∀ i < p.mc,
    0 ≤ a (primalLoCol i) ∧ a (primalLoCol i) < 2 ^ qpRangeBits ∧
    0 ≤ a (primalHiCol i) ∧ a (primalHiCol i) < 2 ^ qpRangeBits
  statLo : ∀ j < p.n,
    a (statLoCol j) = p.tol +
      ((∑ k ∈ Finset.range p.n, p.pAt j k * a (xCol k)) + p.qAt j * p.scale +
       ∑ i ∈ Finset.range p.mc, p.aAt i j * (a (yCol i) - qpYShift))
  statHi : ∀ j < p.n,
    a (statHiCol j) = p.tol -
      ((∑ k ∈ Finset.range p.n, p.pAt j k * a (xCol k)) + p.qAt j * p.scale +
       ∑ i ∈ Finset.range p.mc, p.aAt i j * (a (yCol i) - qpYShift))
  statRanges : ∀ j < p.n,
    0 ≤ a (statLoCol j) ∧ a (statLoCol j) < 2 ^ qpRangeBits ∧
    0 ≤ a (statHiCol j) ∧ a (statHiCol j) < 2 ^ qpRangeBits
  selectorOne : ∀ i < p.mc,
    (a (lowSelCol i) = 0 ∨ a (lowSelCol i) = 1) ∧
    (a (midSelCol i) = 0 ∨ a (midSelCol i) = 1) ∧
    (a (highSelCol i) = 0 ∨ a (highSelCol i) = 1) ∧
    a (lowSelCol i) + a (midSelCol i) + a (highSelCol i) = 1
  lowRegion : ∀ i < p.mc, a (lowSelCol i) = 1 →
    a (lowRegionCol i) = p.lAt i * p.scale -
      ((∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) +
        (a (yCol i) - qpYShift) * p.scale)
  midRegion : ∀ i < p.mc, a (midSelCol i) = 1 →
    a (midLoRegionCol i) =
      ((∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) +
        (a (yCol i) - qpYShift) * p.scale) - p.lAt i * p.scale ∧
    a (midHiRegionCol i) = p.uAt i * p.scale -
      ((∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) +
        (a (yCol i) - qpYShift) * p.scale)
  highRegion : ∀ i < p.mc, a (highSelCol i) = 1 →
    a (highRegionCol i) =
      ((∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) +
        (a (yCol i) - qpYShift) * p.scale) - p.uAt i * p.scale
  regionRanges : ∀ i < p.mc,
    0 ≤ a (lowRegionCol i) ∧ 0 ≤ a (midLoRegionCol i) ∧
    0 ≤ a (midHiRegionCol i) ∧ 0 ≤ a (highRegionCol i)
  projection : ∀ i < p.mc,
    a (projCol i) =
      a (lowSelCol i) * (p.lAt i * p.scale) +
      a (midSelCol i) *
        ((∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) +
          (a (yCol i) - qpYShift) * p.scale) +
      a (highSelCol i) * (p.uAt i * p.scale)
  normalLo : ∀ i < p.mc,
    a (normalLoCol i) = p.tol +
      (∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) - a (projCol i)
  normalHi : ∀ i < p.mc,
    a (normalHiCol i) = p.tol -
      ((∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) - a (projCol i))
  normalRanges : ∀ i < p.mc, 0 ≤ a (normalLoCol i) ∧ 0 ≤ a (normalHiCol i)
  returnEq : a returnCol =
    ∑ j ∈ Finset.range p.n, (-p.qAt j) * a (xCol j)

def witnessOf (p : CertQpProg) (a : Assignment) : FixedWitness p where
  x := fun j => a (xCol j)
  y := fun i => a (yCol i) - qpYShift

theorem ax_witnessOf_eq (p : CertQpProg) (a : Assignment) (i : Fin p.mc) :
    ax p (witnessOf p a) i =
      ∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j) := by
  unfold ax witnessOf
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => p.aAt i j * a (xCol j))]

theorem stat_witnessOf_eq (p : CertQpProg) (a : Assignment) (j : Fin p.n) :
    stat p (witnessOf p a) j =
      (∑ k ∈ Finset.range p.n, p.pAt j k * a (xCol k)) + p.qAt j * p.scale +
       ∑ i ∈ Finset.range p.mc, p.aAt i j * (a (yCol i) - qpYShift) := by
  unfold stat witnessOf
  rw [Fin.sum_univ_eq_sum_range
      (fun k : Nat => p.pAt j k * a (xCol k)),
    Fin.sum_univ_eq_sum_range
      (fun i : Nat => p.aAt i j * (a (yCol i) - qpYShift))]

theorem selector_cases {lo mid hi : Int}
    (hlo : lo = 0 ∨ lo = 1) (hmid : mid = 0 ∨ mid = 1) (hhi : hi = 0 ∨ hi = 1)
    (hsum : lo + mid + hi = 1) :
    (lo = 1 ∧ mid = 0 ∧ hi = 0) ∨
    (lo = 0 ∧ mid = 1 ∧ hi = 0) ∨
    (lo = 0 ∧ mid = 0 ∧ hi = 1) := by
  rcases hlo with rfl | rfl <;> rcases hmid with rfl | rfl <;>
    rcases hhi with rfl | rfl <;> omega

theorem exactTrace_projection_eq_clamp (p : CertQpProg) {a : Assignment}
    (hscale : 0 ≤ p.scale) (hlenu : ∀ i < p.mc, p.lAt i ≤ p.uAt i)
    (h : ExactTrace p a) (i : Fin p.mc) :
    a (projCol i) = clampInt
      (ax p (witnessOf p a) i + (witnessOf p a).y i * p.scale)
      (p.lAt i * p.scale) (p.uAt i * p.scale) := by
  have hi : (i : Nat) < p.mc := i.isLt
  have hsel := h.selectorOne i hi
  rcases selector_cases hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2 with hs | hs | hs
  · have hr := h.lowRegion i hi hs.1
    have hr0 := (h.regionRanges i hi).1
    have hshift :
        ax p (witnessOf p a) i + (witnessOf p a).y i * p.scale ≤ p.lAt i * p.scale := by
      rw [ax_witnessOf_eq]
      simp only [witnessOf]
      omega
    have hlu : p.lAt i * p.scale ≤ p.uAt i * p.scale :=
      mul_le_mul_of_nonneg_right (hlenu i hi) hscale
    rw [h.projection i hi, hs.1, hs.2.1, hs.2.2]
    simp only [one_mul, zero_mul, add_zero]
    rw [clampInt, max_eq_right hshift, min_eq_left hlu]
  · have hr := h.midRegion i hi hs.2.1
    have hrs := h.regionRanges i hi
    have hlo : p.lAt i * p.scale ≤
        ax p (witnessOf p a) i + (witnessOf p a).y i * p.scale := by
      rw [ax_witnessOf_eq]
      simp only [witnessOf]
      omega
    have hhi : ax p (witnessOf p a) i + (witnessOf p a).y i * p.scale ≤
        p.uAt i * p.scale := by
      rw [ax_witnessOf_eq]
      simp only [witnessOf]
      omega
    rw [h.projection i hi, hs.1, hs.2.1, hs.2.2]
    simp only [zero_mul, one_mul, zero_add, add_zero]
    rw [clampInt, max_eq_left hlo, min_eq_left hhi]
    rw [ax_witnessOf_eq]
    rfl
  · have hr := h.highRegion i hi hs.2.2
    have hr0 := (h.regionRanges i hi).2.2.2
    have hshift : p.uAt i * p.scale ≤
        ax p (witnessOf p a) i + (witnessOf p a).y i * p.scale := by
      rw [ax_witnessOf_eq]
      simp only [witnessOf]
      omega
    have hlu : p.lAt i * p.scale ≤ p.uAt i * p.scale :=
      mul_le_mul_of_nonneg_right (hlenu i hi) hscale
    rw [h.projection i hi, hs.1, hs.2.1, hs.2.2]
    simp only [zero_mul, one_mul, zero_add]
    rw [clampInt, max_eq_left (hlu.trans hshift), min_eq_right hshift]

/-- **All-three-clause soundness.**  An exact assignment to the emitted slack /
selector equations yields the actual recomputed exact checker predicate. -/
theorem exactTrace_implies_checker (p : CertQpProg) {a : Assignment}
    (hscale : 0 ≤ p.scale) (hlenu : ∀ i < p.mc, p.lAt i ≤ p.uAt i)
    (h : ExactTrace p a) :
    ExactChecker p (witnessOf p a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    have hlo := (h.primalRanges i hi).1
    have hhi := (h.primalRanges i hi).2.2.1
    have heqlo := h.primalLo i hi
    have heqhi := h.primalHi i hi
    rw [ax_witnessOf_eq]
    constructor <;> omega
  · intro j
    have hj := j.isLt
    have hlo := (h.statRanges j hj).1
    have hhi := (h.statRanges j hj).2.2.1
    have heqlo := h.statLo j hj
    have heqhi := h.statHi j hj
    rw [stat_witnessOf_eq]
    constructor <;> omega
  · intro i
    have hi := i.isLt
    have hlo := (h.normalRanges i hi).1
    have hhi := (h.normalRanges i hi).2
    have heqlo := h.normalLo i hi
    have heqhi := h.normalHi i hi
    rw [projectionDiff, ← exactTrace_projection_eq_clamp p hscale hlenu h i,
      ax_witnessOf_eq]
    constructor <;> omega

#assert_axioms selector_cases
#assert_axioms exactTrace_projection_eq_clamp
#assert_axioms exactTrace_implies_checker

/-! ## 6. Deployed-denotation bridge.

The theorem above starts at exact integer equations.  This section starts one
layer lower, at the actual `Satisfied2` denotation of the byte-pinned descriptor.
It extracts both field congruences and faithful range-table facts; the only
integer side condition left explicit is a bound on each *complete gate body*.
That is the precise no-wrap obligation, rather than a per-product heuristic. -/

def qpConstTrace (a : Assignment) : VmTrace :=
  { rows := List.replicate 8 a
  , pub := fun _ => a returnCol
  , tf := fun tid => if tid = .range then rangeRows qpRangeBits else [] }

@[simp] theorem qpConstTrace_rows_length (a : Assignment) :
    (qpConstTrace a).rows.length = 8 := by
  simp [qpConstTrace]

@[simp] theorem qpConstTrace_loc0 (a : Assignment) :
    (envAt (qpConstTrace a) 0).loc = a := by
  funext k
  simp [envAt, qpConstTrace, List.getD]

@[simp] theorem qpConstTrace_range (a : Assignment) :
    (qpConstTrace a).tf .range = rangeRows qpRangeBits := by
  simp [qpConstTrace]

/-- Evaluation of our left-folded expression sum is the ordinary integer sum. -/
theorem foldl_add_eval (a : Assignment) (f : Nat → EmittedExpr) :
    ∀ (l : List Nat) (acc : EmittedExpr),
      (l.foldl (fun acc i => .add acc (f i)) acc).eval a =
        acc.eval a + (l.map fun i => (f i).eval a).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons i is ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      simp only [EmittedExpr.eval, List.map_cons, List.sum_cons]
      ring

theorem range_map_sum_eq_finset (n : Nat) (g : Nat → Int) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      rw [Finset.sum_range_succ]
      simp

theorem sumExpr_eval (a : Assignment) (n : Nat) (f : Nat → EmittedExpr) :
    (sumExpr n f).eval a = ∑ i ∈ Finset.range n, (f i).eval a := by
  rw [sumExpr, foldl_add_eval]
  change 0 + ((List.range n).map fun i => (f i).eval a).sum = _
  rw [range_map_sum_eq_finset]
  simp

@[simp] theorem yExpr_eval (a : Assignment) (i : Nat) :
    (yExpr i).eval a = a (yCol i) - qpYShift := by
  simp [yExpr, esub, EmittedExpr.eval]
  ring

@[simp] theorem axExpr_eval (p : CertQpProg) (a : Assignment) (i : Nat) :
    (axExpr p i).eval a =
      ∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j) := by
  rw [axExpr, sumExpr_eval]
  simp only [EmittedExpr.eval]

@[simp] theorem statExpr_eval (p : CertQpProg) (a : Assignment) (j : Nat) :
    (statExpr p j).eval a =
      (∑ k ∈ Finset.range p.n, p.pAt j k * a (xCol k)) + p.qAt j * p.scale +
       ∑ i ∈ Finset.range p.mc, p.aAt i j * (a (yCol i) - qpYShift) := by
  simp only [statExpr, EmittedExpr.eval, yExpr_eval, sumExpr_eval]

@[simp] theorem shiftedExpr_eval (p : CertQpProg) (a : Assignment) (i : Nat) :
    (shiftedExpr p i).eval a =
      (∑ j ∈ Finset.range p.n, p.aAt i j * a (xCol j)) +
        (a (yCol i) - qpYShift) * p.scale := by
  simp [shiftedExpr, EmittedExpr.eval]

@[simp] theorem returnExpr_eval (p : CertQpProg) (a : Assignment) :
    (returnExpr p).eval a =
      ∑ j ∈ Finset.range p.n, (-p.qAt j) * a (xCol j) := by
  rw [returnExpr, sumExpr_eval]
  simp only [EmittedExpr.eval]

/-! Constraint-family membership bookkeeping.  These lemmas are the byte-list
link: all later extraction uses an element of `certQpConstraints`, not a freshly
stated equation. -/

theorem xBound_mem (p : CertQpProg) (j : Nat) (hj : j < p.n) :
    ∀ c ∈ boundedRangeConstraints (xCol j) (xUpperCol j) (2 ^ qpXBits - 1),
      c ∈ certQpConstraints p := by
  intro c hc
  have hflat : c ∈ xBoundConstraints p := by
    exact flatten_map_mem
      (fun j => boundedRangeConstraints (xCol j) (xUpperCol j) (2 ^ qpXBits - 1))
      (List.range p.n) c j (List.mem_range.mpr hj) hc
  simp only [certQpConstraints, List.mem_append]
  aesop

theorem yBound_mem (p : CertQpProg) (i : Nat) (hi : i < p.mc) :
    ∀ c ∈ boundedRangeConstraints (yCol i) (yUpperCol i) (2 ^ qpYBits - 1),
      c ∈ certQpConstraints p := by
  intro c hc
  have hflat : c ∈ yBoundConstraints p := by
    exact flatten_map_mem
      (fun i => boundedRangeConstraints (yCol i) (yUpperCol i) (2 ^ qpYBits - 1))
      (List.range p.mc) c i (List.mem_range.mpr hi) hc
  simp only [certQpConstraints, List.mem_append]
  aesop

theorem primal_mem (p : CertQpProg) (i : Nat) (hi : i < p.mc) :
    ∀ c ∈
      [ egate (primalLoBody p i), egate (primalHiBody p i)
      , rangeLookup (primalLoCol i), rangeLookup (primalHiCol i) ],
      c ∈ certQpConstraints p := by
  intro c hc
  have hflat : c ∈ primalConstraints p := by
    exact flatten_map_mem _ _ c i (List.mem_range.mpr hi) hc
  simp only [certQpConstraints, List.mem_append]
  aesop

theorem stationarity_mem (p : CertQpProg) (j : Nat) (hj : j < p.n) :
    ∀ c ∈
      [ egate (statLoBody p j), egate (statHiBody p j)
      , rangeLookup (statLoCol j), rangeLookup (statHiCol j) ],
      c ∈ certQpConstraints p := by
  intro c hc
  have hflat : c ∈ stationarityConstraints p := by
    exact flatten_map_mem _ _ c j (List.mem_range.mpr hj) hc
  simp only [certQpConstraints, List.mem_append]
  aesop

theorem normal_mem (p : CertQpProg) (i : Nat) (hi : i < p.mc) :
    ∀ c ∈ normalConstraintsAt p i, c ∈ certQpConstraints p := by
  intro c hc
  have hflat : c ∈ normalConstraints p := by
    exact flatten_map_mem _ _ c i (List.mem_range.mpr hi) hc
  simp only [certQpConstraints, List.mem_append]
  aesop

theorem return_mem (p : CertQpProg) : egate (returnBody p) ∈ certQpConstraints p := by
  simp [certQpConstraints]

/-- Any emitted arithmetic gate holds modulo BabyBear on the private assignment. -/
theorem qp_gate_vanishes {hash : List Int → Int} {p : CertQpProg} {a : Assignment}
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    {body : EmittedExpr} (hmem : egate body ∈ certQpConstraints p) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have hc : egate body ∈ (certQpDescriptorOf p).constraints := hmem
  have h := hsat.rowConstraints 0 (by simp) (egate body) hc
  simpa [egate, VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- A lookup in this descriptor is an exact 24-bit integer range fact because
the constant trace installs the faithful `rangeRows 24` table. -/
theorem qp_range_forced {hash : List Int → Int} {p : CertQpProg} {a : Assignment}
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    (col : Nat) (hmem : rangeLookup col ∈ certQpConstraints p) :
    0 ≤ a col ∧ a col < 2 ^ qpRangeBits := by
  have hc : rangeLookup col ∈ (certQpDescriptorOf p).constraints := hmem
  have h := hsat.rowConstraints 0 (by simp) (rangeLookup col) hc
  have hl : Lookup.holdsAt (qpConstTrace a).tf (envAt (qpConstTrace a) 0)
      ⟨.range, [.var col]⟩ := by
    simpa [rangeLookup, VmConstraint2.holdsAt] using h
  have hr := lookup_replaces_range qpRangeBits (qpConstTrace a).tf
    (qpConstTrace_range a) (envAt (qpConstTrace a) 0) col hl
  change 0 ≤ (envAt (qpConstTrace a) 0).loc col ∧
    (envAt (qpConstTrace a) 0).loc col < 2 ^ qpRangeBits at hr
  rw [qpConstTrace_loc0] at hr
  exact hr

/-- The complete-residual no-wrap contract.  Every item is exactly one emitted
gate body, so this neither assumes the desired checker clauses nor reasons from
per-factor bounds after the fact. -/
structure CertQpIntegerNoWrap (p : CertQpProg) (a : Assignment) : Prop where
  xUpper : ∀ j < p.n,
    InZeroResidueWindow (upperBoundBody (xCol j) (xUpperCol j) (2 ^ qpXBits - 1) |>.eval a)
  yUpper : ∀ i < p.mc,
    InZeroResidueWindow (upperBoundBody (yCol i) (yUpperCol i) (2 ^ qpYBits - 1) |>.eval a)
  primalLo : ∀ i < p.mc, InZeroResidueWindow ((primalLoBody p i).eval a)
  primalHi : ∀ i < p.mc, InZeroResidueWindow ((primalHiBody p i).eval a)
  statLo : ∀ j < p.n, InZeroResidueWindow ((statLoBody p j).eval a)
  statHi : ∀ j < p.n, InZeroResidueWindow ((statHiBody p j).eval a)
  selectorLow : ∀ i < p.mc,
    InZeroResidueWindow ((selectorBoolBody (lowSelCol i)).eval a)
  selectorMid : ∀ i < p.mc,
    InZeroResidueWindow ((selectorBoolBody (midSelCol i)).eval a)
  selectorHigh : ∀ i < p.mc,
    InZeroResidueWindow ((selectorBoolBody (highSelCol i)).eval a)
  selectorSum : ∀ i < p.mc, InZeroResidueWindow ((selectorSumBody i).eval a)
  lowRegion : ∀ i < p.mc, InZeroResidueWindow ((lowRegionBody p i).eval a)
  midLoRegion : ∀ i < p.mc, InZeroResidueWindow ((midLoRegionBody p i).eval a)
  midHiRegion : ∀ i < p.mc, InZeroResidueWindow ((midHiRegionBody p i).eval a)
  highRegion : ∀ i < p.mc, InZeroResidueWindow ((highRegionBody p i).eval a)
  projection : ∀ i < p.mc, InZeroResidueWindow ((projectionBody p i).eval a)
  normalLo : ∀ i < p.mc, InZeroResidueWindow ((normalLoBody p i).eval a)
  normalHi : ∀ i < p.mc, InZeroResidueWindow ((normalHiBody p i).eval a)
  returnPin : InZeroResidueWindow ((returnBody p).eval a)

theorem int_bool_of_gate {z : Int} (h : z * (z - 1) = 0) : z = 0 ∨ z = 1 := by
  rcases mul_eq_zero.mp h with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

/-- Turn a field-zero gate into an integer-zero gate under its complete-residual
window. -/
theorem qp_gate_exact {hash : List Int → Int} {p : CertQpProg} {a : Assignment}
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    {body : EmittedExpr} (hmem : egate body ∈ certQpConstraints p)
    (hwindow : InZeroResidueWindow (body.eval a)) :
    body.eval a = 0 :=
  eq_zero_of_modEq_zero_of_window (qp_gate_vanishes hsat hmem) hwindow

/-- The 24-bit range table itself makes an affine upper-bound gate a unique
integer equality; this is the non-circular entry point used to derive the
descriptor's tighter 10/12-bit private-input policy. -/
theorem upperBound_exact_of_ranges {hash : List Int → Int} {p : CertQpProg}
    {a : Assignment} (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    (col upperCol : Nat) (upper : Int)
    (hgate : egate (upperBoundBody col upperCol upper) ∈ certQpConstraints p)
    (hcol : rangeLookup col ∈ certQpConstraints p)
    (hupper : rangeLookup upperCol ∈ certQpConstraints p)
    (hu0 : 0 ≤ upper) (hup : upper < babyBearModulus) :
    (upperBoundBody col upperCol upper).eval a = 0 := by
  have hc := qp_range_forced hsat col hcol
  have hs := qp_range_forced hsat upperCol hupper
  have h24 : 2 * (2 : Int) ^ qpRangeBits < babyBearModulus := by
    norm_num [qpRangeBits, babyBearModulus]
  simp only [babyBearModulus] at hup h24
  apply qp_gate_exact hsat hgate
  simp only [InZeroResidueWindow, babyBearModulus, upperBoundBody, esub, EmittedExpr.eval]
  constructor <;> omega

theorem xBound_of_satisfied {hash : List Int → Int} {p : CertQpProg} {a : Assignment}
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    (j : Nat) (hj : j < p.n) :
    0 ≤ a (xCol j) ∧ a (xCol j) < 2 ^ qpXBits := by
  have hx := qp_range_forced hsat (xCol j)
    (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
  have hu := qp_range_forced hsat (xUpperCol j)
    (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
  have hz := upperBound_exact_of_ranges hsat (xCol j) (xUpperCol j) (2 ^ qpXBits - 1)
    (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
    (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
    (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
    (by norm_num [qpXBits]) (by norm_num [qpXBits, babyBearModulus])
  simp only [upperBoundBody, esub, EmittedExpr.eval] at hz
  exact ⟨hx.1, by omega⟩

theorem yBound_of_satisfied {hash : List Int → Int} {p : CertQpProg} {a : Assignment}
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    (i : Nat) (hi : i < p.mc) :
    0 ≤ a (yCol i) ∧ a (yCol i) < 2 ^ qpYBits := by
  have hy := qp_range_forced hsat (yCol i)
    (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
  have hu := qp_range_forced hsat (yUpperCol i)
    (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
  have hz := upperBound_exact_of_ranges hsat (yCol i) (yUpperCol i) (2 ^ qpYBits - 1)
    (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
    (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
    (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
    (by norm_num [qpYBits]) (by norm_num [qpYBits, babyBearModulus])
  simp only [upperBoundBody, esub, EmittedExpr.eval] at hz
  exact ⟨hy.1, by omega⟩

/-- Boolean selectors do not need a quadratic no-wrap bound: BabyBear primality
plus canonicality turns `z(z-1)=0 mod p` directly into `z∈{0,1}`. -/
theorem binary_of_selector_gate {hash : List Int → Int} {p : CertQpProg}
    {a : Assignment} (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a))
    (col : Nat) (hcanon : CanonCell (a col))
    (hmem : egate (selectorBoolBody col) ∈ certQpConstraints p) :
    a col = 0 ∨ a col = 1 := by
  have hmod := qp_gate_vanishes hsat hmem
  have hev : (selectorBoolBody col).eval a = a col * (a col - 1) := by
    simp only [selectorBoolBody_eq, esub, EmittedExpr.eval]
    ring
  rw [hev] at hmod
  have hd : (2013265921 : Int) ∣ a col * (a col - 1) :=
    Int.modEq_zero_iff_dvd.mp hmod
  rcases pPrimeInt.dvd_mul.mp hd with hz | hz
  · obtain ⟨k, hk⟩ := hz
    exact Or.inl (by rcases hcanon with ⟨h0, h1⟩; omega)
  · obtain ⟨k, hk⟩ := hz
    exact Or.inr (by rcases hcanon with ⟨h0, h1⟩; omega)

private theorem portfolio_x_bounds {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ j < qpN, 0 ≤ a (xCol j) ∧ a (xCol j) < 2 ^ qpXBits := by
  intro j hj
  exact xBound_of_satisfied hsat j (by simpa [portfolioDescriptor, certQpDescriptorOf,
    portfolioProg, qpN] using hj)

private theorem portfolio_y_bounds {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < qpMc, 0 ≤ a (yCol i) ∧ a (yCol i) < 2 ^ qpYBits := by
  intro i hi
  exact yBound_of_satisfied hsat i (by simpa [portfolioDescriptor, certQpDescriptorOf,
    portfolioProg, qpMc] using hi)

private theorem portfolio_primalLo_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((primalLoBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (primalLoCol i)
    (primal_mem portfolioProg i hi _ (by simp))
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, primalLoBody, esub,
    EmittedExpr.eval, axExpr_eval]
  interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.lAt, CertQpProg.tol,
      portfolioA, portfolioL, qpN, qpMc, qpScale, qpEpsilon, qpXBits,
      Finset.sum_range_succ] <;>
    omega

private theorem portfolio_primalHi_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((primalHiBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (primalHiCol i)
    (primal_mem portfolioProg i hi _ (by simp))
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, primalHiBody, esub,
    EmittedExpr.eval, axExpr_eval]
  interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.uAt, CertQpProg.tol,
      portfolioA, portfolioU, qpN, qpMc, qpScale, qpEpsilon, qpXBits,
      Finset.sum_range_succ] <;>
    omega

private theorem portfolio_statLo_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ j < portfolioProg.n, InZeroResidueWindow ((statLoBody portfolioProg j).eval a) := by
  intro j hj
  have hj6 : j < 6 := by simpa [portfolioProg, qpN] using hj
  have hr := qp_range_forced hsat (statLoCol j)
    (stationarity_mem portfolioProg j hj _ (by simp))
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  have hy0 := portfolio_y_bounds hsat 0 (by norm_num [qpMc])
  have hy1 := portfolio_y_bounds hsat 1 (by norm_num [qpMc])
  have hy2 := portfolio_y_bounds hsat 2 (by norm_num [qpMc])
  have hy3 := portfolio_y_bounds hsat 3 (by norm_num [qpMc])
  have hy4 := portfolio_y_bounds hsat 4 (by norm_num [qpMc])
  have hy5 := portfolio_y_bounds hsat 5 (by norm_num [qpMc])
  have hy6 := portfolio_y_bounds hsat 6 (by norm_num [qpMc])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpYBits] at hy0 hy1 hy2 hy3 hy4 hy5 hy6
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, statLoBody, esub,
    EmittedExpr.eval, statExpr_eval]
  interval_cases j <;>
    norm_num [portfolioProg, CertQpProg.pAt, CertQpProg.qAt, CertQpProg.aAt,
      CertQpProg.tol, portfolioP, portfolioQ, portfolioA, qpN, qpMc, qpScale,
      qpEpsilon, qpYShift, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_statHi_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ j < portfolioProg.n, InZeroResidueWindow ((statHiBody portfolioProg j).eval a) := by
  intro j hj
  have hj6 : j < 6 := by simpa [portfolioProg, qpN] using hj
  have hr := qp_range_forced hsat (statHiCol j)
    (stationarity_mem portfolioProg j hj _ (by simp))
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  have hy0 := portfolio_y_bounds hsat 0 (by norm_num [qpMc])
  have hy1 := portfolio_y_bounds hsat 1 (by norm_num [qpMc])
  have hy2 := portfolio_y_bounds hsat 2 (by norm_num [qpMc])
  have hy3 := portfolio_y_bounds hsat 3 (by norm_num [qpMc])
  have hy4 := portfolio_y_bounds hsat 4 (by norm_num [qpMc])
  have hy5 := portfolio_y_bounds hsat 5 (by norm_num [qpMc])
  have hy6 := portfolio_y_bounds hsat 6 (by norm_num [qpMc])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpYBits] at hy0 hy1 hy2 hy3 hy4 hy5 hy6
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, statHiBody, esub,
    EmittedExpr.eval, statExpr_eval]
  interval_cases j <;>
    norm_num [portfolioProg, CertQpProg.pAt, CertQpProg.qAt, CertQpProg.aAt,
      CertQpProg.tol, portfolioP, portfolioQ, portfolioA, qpN, qpMc, qpScale,
      qpEpsilon, qpYShift, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_selector_values {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc,
      (a (lowSelCol i) = 0 ∨ a (lowSelCol i) = 1) ∧
      (a (midSelCol i) = 0 ∨ a (midSelCol i) = 1) ∧
      (a (highSelCol i) = 0 ∨ a (highSelCol i) = 1) ∧
      a (lowSelCol i) + a (midSelCol i) + a (highSelCol i) = 1 := by
  intro i hi
  have hlo := binary_of_selector_gate hsat (lowSelCol i) (hcanon _)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
  have hmid := binary_of_selector_gate hsat (midSelCol i) (hcanon _)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
  have hhigh := binary_of_selector_gate hsat (highSelCol i) (hcanon _)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
  have hw : InZeroResidueWindow ((selectorSumBody i).eval a) := by
    simp only [InZeroResidueWindow, babyBearModulus, selectorSumBody, esub,
      EmittedExpr.eval]
    rcases hlo with hlo | hlo <;> rcases hmid with hmid | hmid <;>
      rcases hhigh with hhigh | hhigh <;> omega
  have hz := qp_gate_exact hsat
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt, selectorConstraints])) hw
  simp only [selectorSumBody, esub, EmittedExpr.eval] at hz
  refine ⟨hlo, hmid, hhigh, ?_⟩
  omega

private theorem portfolio_lowRegion_window {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((lowRegionBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (lowRegionCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hsel := (portfolio_selector_values hcanon hsat i hi).1
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  have hy := portfolio_y_bounds hsat i (by simpa [portfolioProg, qpMc] using hi)
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpYBits] at hy
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, lowRegionBody, esub,
    EmittedExpr.eval, shiftedExpr_eval]
  rcases hsel with hsel | hsel <;> rw [hsel] <;>
    interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.lAt, portfolioA,
      portfolioL, qpN, qpMc, qpScale, qpYShift, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_midLoRegion_window {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((midLoRegionBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (midLoRegionCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hsel := (portfolio_selector_values hcanon hsat i hi).2.1
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  have hy := portfolio_y_bounds hsat i (by simpa [portfolioProg, qpMc] using hi)
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpYBits] at hy
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, midLoRegionBody, esub,
    EmittedExpr.eval, shiftedExpr_eval]
  rcases hsel with hsel | hsel <;> rw [hsel] <;>
    interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.lAt, portfolioA,
      portfolioL, qpN, qpMc, qpScale, qpYShift, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_midHiRegion_window {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((midHiRegionBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (midHiRegionCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hsel := (portfolio_selector_values hcanon hsat i hi).2.1
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  have hy := portfolio_y_bounds hsat i (by simpa [portfolioProg, qpMc] using hi)
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpYBits] at hy
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, midHiRegionBody, esub,
    EmittedExpr.eval, shiftedExpr_eval]
  rcases hsel with hsel | hsel <;> rw [hsel] <;>
    interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.uAt, portfolioA,
      portfolioU, qpN, qpMc, qpScale, qpYShift, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_highRegion_window {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((highRegionBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (highRegionCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hsel := (portfolio_selector_values hcanon hsat i hi).2.2.1
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  have hy := portfolio_y_bounds hsat i (by simpa [portfolioProg, qpMc] using hi)
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpYBits] at hy
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, highRegionBody, esub,
    EmittedExpr.eval, shiftedExpr_eval]
  rcases hsel with hsel | hsel <;> rw [hsel] <;>
    interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.uAt, portfolioA,
      portfolioU, qpN, qpMc, qpScale, qpYShift, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_ax_bounds {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc,
      0 ≤ (∑ j ∈ Finset.range portfolioProg.n,
        portfolioProg.aAt i j * a (xCol j)) ∧
      (∑ j ∈ Finset.range portfolioProg.n,
        portfolioProg.aAt i j * a (xCol j)) ≤ 6138000 := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, portfolioA, qpN, qpMc,
      Finset.sum_range_succ] <;>
    omega

private theorem portfolio_lu_scaled_bounds (i : Nat) (hi : i < portfolioProg.mc) :
    (0 ≤ portfolioProg.lAt i * portfolioProg.scale ∧
      portfolioProg.lAt i * portfolioProg.scale ≤ 1000000) ∧
    (0 ≤ portfolioProg.uAt i * portfolioProg.scale ∧
      portfolioProg.uAt i * portfolioProg.scale ≤ 1000000) := by
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.lAt, CertQpProg.uAt, portfolioL,
      portfolioU, qpN, qpMc, qpScale]

private theorem portfolio_projection_window {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((projectionBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hr := qp_range_forced hsat (projCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hsels := portfolio_selector_values hcanon hsat i hi
  have hax := portfolio_ax_bounds hsat i hi
  have hy := portfolio_y_bounds hsat i (by simpa [portfolioProg, qpMc] using hi)
  norm_num [qpYBits] at hy
  norm_num [qpRangeBits] at hr
  have hlu := portfolio_lu_scaled_bounds i hi
  have hscale : portfolioProg.scale = 1000 := rfl
  simp only [InZeroResidueWindow, babyBearModulus, projectionBody, esub,
    EmittedExpr.eval, shiftedExpr_eval]
  rcases selector_cases hsels.1 hsels.2.1 hsels.2.2.1 hsels.2.2.2 with hs | hs | hs <;>
    rw [hs.1, hs.2.1, hs.2.2] <;>
    rw [hscale] at hlu ⊢ <;>
    norm_num [qpYShift] <;>
    omega

private theorem portfolio_normalLo_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((normalLoBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hn := qp_range_forced hsat (normalLoCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hp := qp_range_forced hsat (projCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpRangeBits] at hn hp
  simp only [InZeroResidueWindow, babyBearModulus, normalLoBody, esub,
    EmittedExpr.eval, axExpr_eval]
  interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.tol, portfolioA,
      qpN, qpMc, qpScale, qpEpsilon, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_normalHi_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ∀ i < portfolioProg.mc, InZeroResidueWindow ((normalHiBody portfolioProg i).eval a) := by
  intro i hi
  have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
  have hn := qp_range_forced hsat (normalHiCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hp := qp_range_forced hsat (projCol i)
    (normal_mem portfolioProg i hi _ (by simp [normalConstraintsAt]))
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpRangeBits] at hn hp
  simp only [InZeroResidueWindow, babyBearModulus, normalHiBody, esub,
    EmittedExpr.eval, axExpr_eval]
  interval_cases i <;>
    norm_num [portfolioProg, CertQpProg.aAt, CertQpProg.tol, portfolioA,
      qpN, qpMc, qpScale, qpEpsilon, Finset.sum_range_succ] <;>
    omega

private theorem portfolio_return_window {hash : List Int → Int} {a : Assignment}
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    InZeroResidueWindow ((returnBody portfolioProg).eval a) := by
  have hr := qp_range_forced hsat returnCol (by
    simp [certQpConstraints])
  have hx0 := portfolio_x_bounds hsat 0 (by norm_num [qpN])
  have hx1 := portfolio_x_bounds hsat 1 (by norm_num [qpN])
  have hx2 := portfolio_x_bounds hsat 2 (by norm_num [qpN])
  have hx3 := portfolio_x_bounds hsat 3 (by norm_num [qpN])
  have hx4 := portfolio_x_bounds hsat 4 (by norm_num [qpN])
  have hx5 := portfolio_x_bounds hsat 5 (by norm_num [qpN])
  norm_num [qpXBits] at hx0 hx1 hx2 hx3 hx4 hx5
  norm_num [qpRangeBits] at hr
  simp only [InZeroResidueWindow, babyBearModulus, returnBody, esub,
    EmittedExpr.eval, returnExpr_eval]
  norm_num [portfolioProg, CertQpProg.qAt, portfolioQ, qpN, qpMc, qpScale,
    Finset.sum_range_succ]
  omega

/-- **Concrete no-wrap discharge for `portfolio_qp_public()` at `S=10³`.**
Unlike the generic contract, this is derived from the descriptor's own faithful
range lookups, the emitted upper-bound gates, the fixed public matrices, and
canonical BabyBear cells.  It is not a witness-supplied flag. -/
theorem portfolio_noWrap_of_satisfied {hash : List Int → Int} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    CertQpIntegerNoWrap portfolioProg a := by
  refine
    { xUpper := ?_
      yUpper := ?_
      primalLo := portfolio_primalLo_window hsat
      primalHi := portfolio_primalHi_window hsat
      statLo := portfolio_statLo_window hsat
      statHi := portfolio_statHi_window hsat
      selectorLow := ?_
      selectorMid := ?_
      selectorHigh := ?_
      selectorSum := ?_
      lowRegion := portfolio_lowRegion_window hcanon hsat
      midLoRegion := portfolio_midLoRegion_window hcanon hsat
      midHiRegion := portfolio_midHiRegion_window hcanon hsat
      highRegion := portfolio_highRegion_window hcanon hsat
      projection := portfolio_projection_window hcanon hsat
      normalLo := portfolio_normalLo_window hsat
      normalHi := portfolio_normalHi_window hsat
      returnPin := portfolio_return_window hsat }
  · intro j hj
    have hz := upperBound_exact_of_ranges hsat (xCol j) (xUpperCol j)
      (2 ^ qpXBits - 1)
      (xBound_mem portfolioProg j hj _ (by simp [boundedRangeConstraints]))
      (xBound_mem portfolioProg j hj _ (by simp [boundedRangeConstraints]))
      (xBound_mem portfolioProg j hj _ (by simp [boundedRangeConstraints]))
      (by norm_num [qpXBits]) (by norm_num [qpXBits, babyBearModulus])
    rw [hz]
    norm_num [InZeroResidueWindow, babyBearModulus]
  · intro i hi
    have hz := upperBound_exact_of_ranges hsat (yCol i) (yUpperCol i)
      (2 ^ qpYBits - 1)
      (yBound_mem portfolioProg i hi _ (by simp [boundedRangeConstraints]))
      (yBound_mem portfolioProg i hi _ (by simp [boundedRangeConstraints]))
      (yBound_mem portfolioProg i hi _ (by simp [boundedRangeConstraints]))
      (by norm_num [qpYBits]) (by norm_num [qpYBits, babyBearModulus])
    rw [hz]
    norm_num [InZeroResidueWindow, babyBearModulus]
  · intro i hi
    have hs := (portfolio_selector_values hcanon hsat i hi).1
    rcases hs with hs | hs <;> simp [InZeroResidueWindow, babyBearModulus,
      selectorBoolBody_eq, esub, EmittedExpr.eval, hs]
  · intro i hi
    have hs := (portfolio_selector_values hcanon hsat i hi).2.1
    rcases hs with hs | hs <;> simp [InZeroResidueWindow, babyBearModulus,
      selectorBoolBody_eq, esub, EmittedExpr.eval, hs]
  · intro i hi
    have hs := (portfolio_selector_values hcanon hsat i hi).2.2.1
    rcases hs with hs | hs <;> simp [InZeroResidueWindow, babyBearModulus,
      selectorBoolBody_eq, esub, EmittedExpr.eval, hs]
  · intro i hi
    have hs := portfolio_selector_values hcanon hsat i hi
    simp only [InZeroResidueWindow, babyBearModulus, selectorSumBody, esub,
      EmittedExpr.eval]
    omega

/-- **`Satisfied2 → ExactTrace`.**  Faithful range lookups supply non-negativity;
the emitted upper-slack gates tighten private inputs to 10/12 bits; every other
integer equality is obtained by applying the complete-residual no-wrap contract
to the corresponding emitted gate. -/
theorem satisfied2_implies_exactTrace {hash : List Int → Int} (p : CertQpProg)
    {a : Assignment} (hnowrap : CertQpIntegerNoWrap p a)
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a)) :
    ExactTrace p a := by
  refine
    { xBound := ?_
      yBound := ?_
      primalLo := ?_
      primalHi := ?_
      primalRanges := ?_
      statLo := ?_
      statHi := ?_
      statRanges := ?_
      selectorOne := ?_
      lowRegion := ?_
      midRegion := ?_
      highRegion := ?_
      regionRanges := ?_
      projection := ?_
      normalLo := ?_
      normalHi := ?_
      normalRanges := ?_
      returnEq := ?_ }
  · intro j hj
    have hx := qp_range_forced hsat (xCol j)
      (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
    have hu := qp_range_forced hsat (xUpperCol j)
      (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
    have hz := qp_gate_exact hsat
      (xBound_mem p j hj _ (by simp [boundedRangeConstraints]))
      (hnowrap.xUpper j hj)
    simp only [upperBoundBody, esub, EmittedExpr.eval] at hz
    constructor
    · exact hx.1
    · have := hu.1; omega
  · intro i hi
    have hy := qp_range_forced hsat (yCol i)
      (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
    have hu := qp_range_forced hsat (yUpperCol i)
      (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
    have hz := qp_gate_exact hsat
      (yBound_mem p i hi _ (by simp [boundedRangeConstraints]))
      (hnowrap.yUpper i hi)
    simp only [upperBoundBody, esub, EmittedExpr.eval] at hz
    constructor
    · exact hy.1
    · have := hu.1; omega
  · intro i hi
    have hz := qp_gate_exact hsat
      (primal_mem p i hi _ (by simp)) (hnowrap.primalLo i hi)
    simp only [primalLoBody, esub, EmittedExpr.eval, axExpr_eval] at hz
    omega
  · intro i hi
    have hz := qp_gate_exact hsat
      (primal_mem p i hi _ (by simp)) (hnowrap.primalHi i hi)
    simp only [primalHiBody, esub, EmittedExpr.eval, axExpr_eval] at hz
    omega
  · intro i hi
    have hlo := qp_range_forced hsat (primalLoCol i)
      (primal_mem p i hi _ (by simp))
    have hhi := qp_range_forced hsat (primalHiCol i)
      (primal_mem p i hi _ (by simp))
    exact ⟨hlo.1, hlo.2, hhi.1, hhi.2⟩
  · intro j hj
    have hz := qp_gate_exact hsat
      (stationarity_mem p j hj _ (by simp)) (hnowrap.statLo j hj)
    simp only [statLoBody, esub, EmittedExpr.eval, statExpr_eval] at hz
    omega
  · intro j hj
    have hz := qp_gate_exact hsat
      (stationarity_mem p j hj _ (by simp)) (hnowrap.statHi j hj)
    simp only [statHiBody, esub, EmittedExpr.eval, statExpr_eval] at hz
    omega
  · intro j hj
    have hlo := qp_range_forced hsat (statLoCol j)
      (stationarity_mem p j hj _ (by simp))
    have hhi := qp_range_forced hsat (statHiCol j)
      (stationarity_mem p j hj _ (by simp))
    exact ⟨hlo.1, hlo.2, hhi.1, hhi.2⟩
  · intro i hi
    have hloz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
      (hnowrap.selectorLow i hi)
    have hmidz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
      (hnowrap.selectorMid i hi)
    have hhiz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
      (hnowrap.selectorHigh i hi)
    have hsum := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt, selectorConstraints]))
      (hnowrap.selectorSum i hi)
    have hlo : a (lowSelCol i) = 0 ∨ a (lowSelCol i) = 1 := by
      apply int_bool_of_gate
      simpa [selectorBoolBody_eq, esub, EmittedExpr.eval, sub_eq_add_neg] using hloz
    have hmid : a (midSelCol i) = 0 ∨ a (midSelCol i) = 1 := by
      apply int_bool_of_gate
      simpa [selectorBoolBody_eq, esub, EmittedExpr.eval, sub_eq_add_neg] using hmidz
    have hhi' : a (highSelCol i) = 0 ∨ a (highSelCol i) = 1 := by
      apply int_bool_of_gate
      simpa [selectorBoolBody_eq, esub, EmittedExpr.eval, sub_eq_add_neg] using hhiz
    simp only [selectorSumBody, esub, EmittedExpr.eval] at hsum
    refine ⟨hlo, hmid, hhi', ?_⟩
    omega
  · intro i hi hsel
    have hz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.lowRegion i hi)
    simp only [lowRegionBody, esub, EmittedExpr.eval, shiftedExpr_eval] at hz
    rw [hsel] at hz
    norm_num at hz
    omega
  · intro i hi hsel
    have hzlo := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.midLoRegion i hi)
    have hzhi := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.midHiRegion i hi)
    simp only [midLoRegionBody, esub, EmittedExpr.eval, shiftedExpr_eval] at hzlo
    simp only [midHiRegionBody, esub, EmittedExpr.eval, shiftedExpr_eval] at hzhi
    rw [hsel] at hzlo hzhi
    norm_num at hzlo hzhi
    constructor <;> omega
  · intro i hi hsel
    have hz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.highRegion i hi)
    simp only [highRegionBody, esub, EmittedExpr.eval, shiftedExpr_eval] at hz
    rw [hsel] at hz
    norm_num at hz
    omega
  · intro i hi
    have hlo := qp_range_forced hsat (lowRegionCol i)
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
    have hmlo := qp_range_forced hsat (midLoRegionCol i)
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
    have hmhi := qp_range_forced hsat (midHiRegionCol i)
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
    have hhi := qp_range_forced hsat (highRegionCol i)
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
    exact ⟨hlo.1, hmlo.1, hmhi.1, hhi.1⟩
  · intro i hi
    have hz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.projection i hi)
    simp only [projectionBody, esub, EmittedExpr.eval, shiftedExpr_eval] at hz
    omega
  · intro i hi
    have hz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.normalLo i hi)
    simp only [normalLoBody, esub, EmittedExpr.eval, axExpr_eval] at hz
    omega
  · intro i hi
    have hz := qp_gate_exact hsat
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
      (hnowrap.normalHi i hi)
    simp only [normalHiBody, esub, EmittedExpr.eval, axExpr_eval] at hz
    omega
  · intro i hi
    have hlo := qp_range_forced hsat (normalLoCol i)
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
    have hhi := qp_range_forced hsat (normalHiCol i)
      (normal_mem p i hi _ (by simp [normalConstraintsAt]))
    exact ⟨hlo.1, hhi.1⟩
  · have hz := qp_gate_exact hsat (return_mem p) hnowrap.returnPin
    simp only [returnBody, esub, EmittedExpr.eval, returnExpr_eval] at hz
    omega

/-- End-to-end all-three-clause soundness from the deployed IR denotation. -/
theorem satisfied2_implies_checker {hash : List Int → Int} (p : CertQpProg)
    {a : Assignment} (hscale : 0 ≤ p.scale)
    (hlenu : ∀ i < p.mc, p.lAt i ≤ p.uAt i)
    (hnowrap : CertQpIntegerNoWrap p a)
    (hsat : Satisfied2 hash (certQpDescriptorOf p) m0 f0 [] (qpConstTrace a)) :
    ExactChecker p (witnessOf p a) :=
  exactTrace_implies_checker p hscale hlenu
    (satisfied2_implies_exactTrace p hnowrap hsat)

/-- The concrete fixed portfolio needs no caller-provided no-wrap certificate:
the descriptor and canonical field representation force `ExactTrace`. -/
theorem portfolio_satisfied2_implies_exactTrace {hash : List Int → Int}
    {a : Assignment} (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ExactTrace portfolioProg a :=
  satisfied2_implies_exactTrace portfolioProg
    (portfolio_noWrap_of_satisfied hcanon hsat) hsat

/-- **Final deployed CertQp soundness theorem.**  A canonical witness accepted by
the byte-pinned `portfolio_qp_public()` descriptor satisfies primal interval,
stationarity, and normal-cone/projection exactly over `Int`, with private `(x,y)`
and no trusted clause flags or witness-supplied no-wrap premise. -/
theorem portfolio_satisfied2_implies_checker {hash : List Int → Int}
    {a : Assignment} (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    ExactChecker portfolioProg (witnessOf portfolioProg a) := by
  apply exactTrace_implies_checker portfolioProg
  · norm_num [portfolioProg, qpScale]
  · intro i hi
    have hi7 : i < 7 := by simpa [portfolioProg, qpMc] using hi
    interval_cases i <;>
      norm_num [portfolioProg, CertQpProg.lAt, CertQpProg.uAt, portfolioL,
        portfolioU, qpN, qpMc, qpScale]
  · exact portfolio_satisfied2_implies_exactTrace hcanon hsat

/-- The single published cell is the exact expected-return numerator forced by
the return gate; `(x,y)` themselves remain trace-private. -/
theorem portfolio_public_return_exact {hash : List Int → Int}
    {a : Assignment} (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash portfolioDescriptor m0 f0 [] (qpConstTrace a)) :
    (qpConstTrace a).pub 0 =
      ∑ j ∈ Finset.range portfolioProg.n,
        (-portfolioProg.qAt j) * a (xCol j) := by
  simpa [qpConstTrace] using
    (portfolio_satisfied2_implies_exactTrace hcanon hsat).returnEq

#assert_axioms foldl_add_eval
#assert_axioms range_map_sum_eq_finset
#assert_axioms sumExpr_eval
#assert_axioms qp_gate_vanishes
#assert_axioms qp_range_forced
#assert_axioms upperBound_exact_of_ranges
#assert_axioms binary_of_selector_gate
#assert_axioms portfolio_noWrap_of_satisfied
#assert_axioms satisfied2_implies_exactTrace
#assert_axioms satisfied2_implies_checker
#assert_axioms portfolio_satisfied2_implies_exactTrace
#assert_axioms portfolio_satisfied2_implies_checker
#assert_axioms portfolio_public_return_exact

end Market.CertQpDescriptor
