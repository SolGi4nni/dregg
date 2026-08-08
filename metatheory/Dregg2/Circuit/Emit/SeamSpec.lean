/-
# `Dregg2.Circuit.Emit.SeamSpec` — ⚑ A SEAM IS AN OBJECT, NOT A PARAGRAPH.

## The wound this exists to close, in its own shape

Four times this campaign has shipped *a claim true of the FOLD, attributed to the AIR*. The
canonical instance: `MinaWrapConjunctionAir.xiCorrectLegs` is `op.xiSqueeze = dv.xi` — a column
equality between two blocks that `no_arithmetic_call_names_an_xi_block` PROVES are free in that
descriptor. The forcing lives entirely in the 32 `cb.connect`s of
`circuit-prove/src/mina_wrap_finalize_fold.rs::fold_endo_into_finalize`. **Nothing there is
unsound** — the weld is elementwise at full limb width, stronger than any in-descriptor digest tie.
The defect is that no OBJECT carried "this conjunct is forced by seam S". Only prose did —
invisible to `#assert_axioms`, to the descriptor JSON, to `pinsTied`, to every census instrument in
the tree.

## What this module is

Three artifacts, one per layer of the repair:

1. **`SeamSpec`** — a seam as DATA: two claim-surface ends (each keyed by descriptor name AND
   semantic-fingerprint lanes), a pin list, and zero-pin lists. Emitted as JSON beside the
   descriptors; the Rust fold functions become READERS of it
   (`circuit-prove/src/seam.rs::apply_seam`) and author no index arithmetic.
2. **`SeamCertifies`** — the S2 composition obligation: `leftSays ∧ rightSays ∧ SeamEq →
   composedClaim`. ⚑ REFUTABLE BY CONSTRUCTION: `SeamEq` is a real hypothesis, and every deployed
   instance ships with a proof that DROPPING it makes the implication FALSE (not merely unproved).
   A composition theorem that proves without its seam hypothesis is `P → P` wearing a name, and
   this repo has shipped one.
3. **`PiPort` / `PortedAir`** — the `TiedAir` analogue for free-but-published blocks. An
   `EffectAir` DECLARES a PI block a PORT — *meaningful only under external forcing* — with a
   decidable island verdict (`portIslandFree`: no leg joins the port's columns to the rest of the
   trace), and a census (`seamCoversPort` + the `CoveredPort` constructor) that REFUSES a port no
   `SeamSpec` covers. So a free-but-published block either has a named seam or the build says so,
   and "closed by constraint" acquires a third honest value: **closed by seam S, theorem S2**.

## ⚠ What a `SeamSpec` does NOT claim

* It does not make the fold's `cb.connect`s an AIR constraint. The recursion circuit is Rust-authored
  wiring (House Law #1 category: wiring, not AIR); it proves on a box and inherits the undischarged
  FRI/STARK floor. What the object changes is that the seam's INDEX ARITHMETIC is Lean-emitted and
  theorem-carrying (S1), and its COMPOSITION is a named, refutable theorem (S2).
* `portIslandFree` is a CONNECTIVITY verdict, not a semantic one: it says no leg relates the port's
  columns to any other column, which is what "meaningful only under external forcing" means at the
  leg level. It cannot say the external forcing is the RIGHT one — that is S2's job.

## Axiom hygiene

Everything here is kernel-clean (`#assert_axioms`); the heavy per-descriptor island walks live with
the declarations in `MinaSeams.lean` (compiled, `#assert_compiled`, because the kernel measurably
cannot walk the sound-multiply legs' `readCols` — `MinaWrapConjunctionAir` §"the LEG level" is the
measurement). No `sorry`, no new axiom, no `#guard`.
-/
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.Emit.PastaFieldSound

namespace Dregg2.Circuit.Emit.Seam

open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg exprCols)
open Dregg2.Circuit.DescriptorIR2 (jsonArray)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)

set_option autoImplicit false

/-! ## §1 — THE SEAM, AS DATA. -/

/-- One end of a seam: a claim surface. `claim` names the claim LAYOUT (a leaf's claim is its
descriptor's PI vector; a fold root's is the layout its `expose` built); `claimLen` is its lane
count; `descName`/`descLanes` key the Lean-emitted descriptor that grounds the welded slots —
`descLanes` are the nine `Faithful9` lanes of `effect_vm_descriptor2_semantic_fingerprint`, so a
Rust reader can RECOMPUTE them from the descriptor it actually loaded and REFUSE a mismatch. A
display name is not a key; the lanes are. -/
structure SeamEnd where
  claim     : String
  claimLen  : Nat
  descName  : String
  descLanes : List ℤ
  deriving Repr, DecidableEq

/-- ⚑ **THE SEAM.** `pins` are elementwise welds `(leftSlot, rightSlot)`; `zeroLeft`/`zeroRight`
are slots pinned to the constant zero. All indices are CLAIM indices of the respective end. -/
structure SeamSpec where
  name      : String
  left      : SeamEnd
  right     : SeamEnd
  pins      : List (Nat × Nat)
  zeroLeft  : List Nat
  zeroRight : List Nat
  deriving Repr, DecidableEq

/-- Well-formedness: every index in range, nine fingerprint lanes per end, and the seam is not
empty (an empty seam "forces" nothing and must be unrepresentable, not merely unusual). -/
def SeamSpec.wf (s : SeamSpec) : Bool :=
  s.pins.all (fun p => decide (p.1 < s.left.claimLen) && decide (p.2 < s.right.claimLen))
  && s.zeroLeft.all (fun i => decide (i < s.left.claimLen))
  && s.zeroRight.all (fun i => decide (i < s.right.claimLen))
  && !(s.pins.isEmpty && s.zeroLeft.isEmpty && s.zeroRight.isEmpty)
  && s.left.descLanes.length == 9
  && s.right.descLanes.length == 9

/-! ## §2 — WHAT A SEAM ASSERTS OF TWO CLAIM VECTORS, AND THE S2 OBLIGATION. -/

/-- The equalities the fold's `cb.connect`s enforce, read off the spec: welded lanes agree,
zero-pinned lanes are zero. -/
def SeamEq (s : SeamSpec) (lv rv : List ℤ) : Prop :=
  (∀ p ∈ s.pins, lv.getD p.1 0 = rv.getD p.2 0)
  ∧ (∀ i ∈ s.zeroLeft, lv.getD i 0 = 0)
  ∧ (∀ i ∈ s.zeroRight, rv.getD i 0 = 0)

/-- ⚑ **S2 — THE COMPOSITION OBLIGATION.** The parent claim of a fold across seam `s` follows from
the two child sentences PLUS the seam equalities. `SeamEq` must be load-bearing: every deployed
instance carries a companion theorem that the implication with `SeamEq` DELETED is false. -/
def SeamCertifies (s : SeamSpec) (LeftSays RightSays : List ℤ → Prop)
    (Composed : List ℤ → List ℤ → Prop) : Prop :=
  ∀ lv rv, LeftSays lv → RightSays rv → SeamEq s lv rv → Composed lv rv

/-- The `EffectLowerCertified` move, for seams: a `CertifiedSeam` cannot be BUILT without its
well-formedness verdict and its composition theorem, so a seam object that certifies nothing is
unrepresentable rather than detectable. -/
structure CertifiedSeam (LeftSays RightSays : List ℤ → Prop)
    (Composed : List ℤ → List ℤ → Prop) where
  spec      : SeamSpec
  wf        : spec.wf = true := by decide
  certifies : SeamCertifies spec LeftSays RightSays Composed

/-! ## §3 — LIMB-BLOCK ARITHMETIC. The vocabulary the S1/S2 statements read claims in.

Every claim lane in this cone is an `SB = 8`-bit limb of an `SK = 32`-limb field element
(`PastaFieldSound.limbAt`). These lemmas are the two directions a seam needs: pointwise limb
equality transports block VALUES across a weld, and a digit prefix is a `mod 2^128` truncation —
the "low 128 bits" reading, as arithmetic rather than prose. -/

/-- The value of `n` base-`2^SB` digits read through `get`. -/
def digitsVal (get : Nat → ℤ) (n : Nat) : ℤ :=
  (List.range n).foldr (fun i acc => acc * (2 ^ SB : ℤ) + get i) 0

/-- The one Nat fact the digit fold needs: splitting a modulus `a · b` into digit and remainder. -/
private theorem mod_mul_split (s a b : Nat) :
    s % (a * b) = a * (s / a % b) + s % a := by
  conv_lhs => rw [← Nat.div_add_mod (s % (a * b)) a]
  rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ ⟨b, rfl⟩]

/-- Generalized fold identity for `digitsVal` over the genuine limbs of `s`. -/
private theorem digitsVal_limb_gen (s : Nat) :
    ∀ (n : Nat) (z : ℤ),
      (List.range n).foldr (fun i acc => acc * (2 ^ SB : ℤ) + limbAt s i) z
        = z * ((2 ^ (SB * n) : ℕ) : ℤ) + ((s % 2 ^ (SB * n) : ℕ) : ℤ) := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [Nat.mod_one]
  | succ n ih =>
      intro z
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [ih (z * (2 ^ SB : ℤ) + limbAt s n)]
      have hmod : (s % 2 ^ (SB * (n + 1)) : ℕ)
          = 2 ^ (SB * n) * (s / 2 ^ (SB * n) % 2 ^ SB) + s % 2 ^ (SB * n) := by
        rw [Nat.mul_succ, Nat.pow_add]
        exact mod_mul_split s (2 ^ (SB * n)) (2 ^ SB)
      rw [hmod, Nat.mul_succ, Nat.pow_add]
      unfold limbAt
      push_cast
      ring

/-- ⚑ **THE DIGIT LEMMA** — `n` genuine limbs of `s` recompose to `s mod 2^(SB·n)`. At `n = SK`
this is total recomposition of any canonical (`< 2^256`) value; at `n = 16` it is the low-128-bit
truncation the `v′` seam welds. -/
theorem digitsVal_limb (s : Nat) (n : Nat) :
    digitsVal (limbAt s) n = ((s % 2 ^ (SB * n) : ℕ) : ℤ) := by
  unfold digitsVal
  rw [digitsVal_limb_gen s n 0]
  simp

/-- Pointwise digit agreement transports the value. -/
theorem digitsVal_congr {f g : Nat → ℤ} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    digitsVal f n = digitsVal g n := by
  unfold digitsVal
  have key : ∀ (m : Nat), m ≤ n → ∀ (z : ℤ),
      (List.range m).foldr (fun i acc => acc * (2 ^ SB : ℤ) + f i) z
        = (List.range m).foldr (fun i acc => acc * (2 ^ SB : ℤ) + g i) z := by
    intro m
    induction m with
    | zero => intro _ z; rfl
    | succ k ih =>
        intro hm z
        rw [List.range_succ, List.foldr_append, List.foldr_append]
        simp only [List.foldr_cons, List.foldr_nil]
        rw [h k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hm)]
        exact ih (Nat.le_of_succ_le hm) _
  exact key n (Nat.le_refl n) 0

/-- ⚑ **LIMB INJECTIVITY ON THE CANONICAL RANGE** — two values below `2^(SB·SK)` with equal limbs
are equal. The reason an elementwise 32-limb weld carries the whole 255-bit value with **no digest
and no birthday bound**. -/
theorem limb_inj {s t : Nat} (hs : s < 2 ^ (SB * SK)) (ht : t < 2 ^ (SB * SK))
    (h : ∀ i, i < SK → limbAt s i = limbAt t i) : s = t := by
  have hv : digitsVal (limbAt s) SK = digitsVal (limbAt t) SK := digitsVal_congr h
  rw [digitsVal_limb, digitsVal_limb] at hv
  have : s % 2 ^ (SB * SK) = t % 2 ^ (SB * SK) := Nat.cast_injective hv
  rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at this

/-- **A rendered block**: the `SK` claim lanes at `lo` are the limbs of a canonical `s`. The bound
is part of the sentence — without it a claim vector renders `s` and `s + 2^256` identically and
"the value the block carries" is not a value. -/
def Renders (v : List ℤ) (lo : Nat) (s : Nat) : Prop :=
  s < 2 ^ (SB * SK) ∧ ∀ i, i < SK → v.getD (lo + i) 0 = limbAt s i

/-- Two rendered blocks welded elementwise carry ONE value. -/
theorem Renders.eq_of_weld {lv rv : List ℤ} {la ra s t : Nat}
    (hs : Renders lv la s) (ht : Renders rv ra t)
    (hweld : ∀ i, i < SK → lv.getD (la + i) 0 = rv.getD (ra + i) 0) : s = t := by
  refine limb_inj hs.1 ht.1 (fun i hi => ?_)
  rw [← hs.2 i hi, hweld i hi, ht.2 i hi]

/-- All-zero digits collapse the fold. -/
theorem digitsVal_zero (n : Nat) : digitsVal (fun _ => (0 : ℤ)) n = 0 := by
  unfold digitsVal
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldr_append]
      simpa using ih

/-- A rendered block whose lanes are all zero carries the value zero. -/
theorem Renders.eq_zero {v : List ℤ} {lo s : Nat} (h : Renders v lo s)
    (hz : ∀ i, i < SK → v.getD (lo + i) 0 = 0) : s = 0 := by
  have hd : ∀ i, i < SK → limbAt s i = (0 : ℤ) := fun i hi => by rw [← h.2 i hi, hz i hi]
  have hv : digitsVal (limbAt s) SK = digitsVal (fun _ => (0 : ℤ)) SK := digitsVal_congr hd
  rw [digitsVal_limb, digitsVal_zero] at hv
  have hs0 : s % 2 ^ (SB * SK) = 0 := by exact_mod_cast hv
  rwa [Nat.mod_eq_of_lt h.1] at hs0

/-- Limb `m + j` of `s` is limb `j` of `s / 2^(SB·m)` — the digit-index shift. -/
theorem limbAt_add (s m j : Nat) : limbAt s (m + j) = limbAt (s / 2 ^ (SB * m)) j := by
  unfold limbAt
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.mul_add]

/-- ⚑ **THE TRUNCATION WELD** — the general form of the "low 128 bits" reading. If a rendered block
`v` agrees with a rendered block `s` on its low `m` limbs and is ZERO on the rest, then
`v = s mod 2^(SB·m)`. At `m = 16` (with `SB = 8`) this is exactly the `v′` seam's sentence: the
welded prechallenge IS the low 128 bits of the terminal squeeze, with the zero-pins carrying the
half of the reading a bare 16-limb weld would not. -/
theorem prefix_weld {rv cv : List ℤ} {rlo clo v s m : Nat} (hm : m ≤ SK)
    (hr : Renders rv rlo v) (hs : Renders cv clo s)
    (hlow : ∀ i, i < m → rv.getD (rlo + i) 0 = cv.getD (clo + i) 0)
    (hhigh : ∀ i, m ≤ i → i < SK → rv.getD (rlo + i) 0 = 0) :
    v = s % 2 ^ (SB * m) := by
  -- (a) the low digits agree, so the values agree mod 2^(SB·m)
  have hlowd : ∀ i, i < m → limbAt v i = limbAt s i := fun i hi => by
    rw [← hr.2 i (Nat.lt_of_lt_of_le hi hm), hlow i hi, hs.2 i (Nat.lt_of_lt_of_le hi hm)]
  have hmodeq : v % 2 ^ (SB * m) = s % 2 ^ (SB * m) := by
    have := digitsVal_congr (n := m) hlowd
    rw [digitsVal_limb, digitsVal_limb] at this
    exact Nat.cast_injective this
  -- (b) the high digits of v vanish, so v < 2^(SB·m)
  have hhd : ∀ j, j < SK - m → limbAt (v / 2 ^ (SB * m)) j = 0 := by
    intro j hj
    rw [← limbAt_add v m j, ← hr.2 (m + j) (by omega)]
    exact hhigh (m + j) (by omega) (by omega)
  have hq0 : v / 2 ^ (SB * m) = 0 := by
    have hv : digitsVal (limbAt (v / 2 ^ (SB * m))) (SK - m)
        = digitsVal (fun _ => (0 : ℤ)) (SK - m) := digitsVal_congr hhd
    rw [digitsVal_limb, digitsVal_zero] at hv
    have hmod0 : v / 2 ^ (SB * m) % 2 ^ (SB * (SK - m)) = 0 := by
      exact_mod_cast hv
    have hlt : v / 2 ^ (SB * m) < 2 ^ (SB * (SK - m)) := by
      have h1 : v < 2 ^ (SB * SK) := hr.1
      have h2 : (2 : Nat) ^ (SB * SK) = 2 ^ (SB * m) * 2 ^ (SB * (SK - m)) := by
        rw [← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hm]
      exact Nat.div_lt_of_lt_mul (by rw [← h2]; exact h1)
    rwa [Nat.mod_eq_of_lt hlt] at hmod0
  have hvlt : v < 2 ^ (SB * m) := by
    rcases Nat.div_eq_zero_iff.mp hq0 with h0 | hlt
    · exact absurd h0 (by positivity : (0 : ℕ) < 2 ^ (SB * m)).ne'
    · exact hlt
  rw [← Nat.mod_eq_of_lt hvlt]
  exact hmodeq

/-! ## §4 — ⚑ PORTS: the `TiedAir` analogue for free-but-published blocks. -/

/-- A declared PORT: a published PI block whose value the AIR carries and compares but never
derives — *meaningful only under external forcing*. `lo/width` are PI slots; `colLo/colWidth` the
backing column ISLAND (for `xiCorrect` that is BOTH ξ blocks: the published one and the free twin
it is compared to). -/
structure PiPort where
  name     : String
  lo       : Nat
  width    : Nat
  colLo    : Nat
  colWidth : Nat
  deriving Repr, DecidableEq

/-- Port slot ranges are inside the declared PI surface and pairwise disjoint. -/
def portsWf (piCount : Nat) (ports : List PiPort) : Bool :=
  ports.all (fun p => decide (0 < p.width) && decide (p.lo + p.width ≤ piCount))
  && (ports.zipIdx.all fun (p, i) =>
        ports.zipIdx.all fun (q, j) =>
          i == j || decide (p.lo + p.width ≤ q.lo) || decide (q.lo + q.width ≤ p.lo))

/-- Does a leg JOIN the column island `[lo, lo+w)` to a column outside it? `pin` legs publish
(they tie a column to a PI slot, not to a column) and `limbs` legs range-check limbs one at a time
(each limb is an independent arity-1 lookup) — neither RELATES columns, so neither can join. Every
other leg kind relates the columns it reads.

⚑ **`.bind` IS ANSWERED AT THE EMISSION, NOT AT THE DECLARATION (2026-08-08).** `AirLeg.readCols`
returns a bind leg's whole IR surface — guard, `commit`, `vk`, `bound` — while the deployed
evaluator (`descriptor_ir2.rs`, `VmConstraint2::ProofBind`) emits polynomials over `vk` only under
a `vkPin` and over `commit` only under a `bound`. A `bound := none` seam therefore CANNOT join its
commit island to anything: no polynomial names those columns. Scoring the declaration here would
have made `portIslandFree` refuse exactly the blocks the port mechanism exists for — a seam's
declared-but-unforced commit lanes — and, worse, would have let a commit lane's DECLARATION count
as the external tie of some other island. The arm below walks the emitted polynomials one by one,
each joining only if it names columns on both sides of the island boundary
(`LightClientAnchorConnectivity.relatedCols`' `.proofBind` arm is the same reading, one rail
down). -/
def legJoinsAcross (lo w : Nat) : AirLeg → Bool
  | .pin _   => false
  | .limbs _ => false
  | .bind b  =>
      let inside : Nat → Bool := fun c => decide (lo ≤ c) && decide (c < lo + w)
      let crosses : List Nat → Bool := fun cs => cs.any inside && cs.any (fun c => !inside c)
      let g := exprCols b.guard
      -- guard·(guard−1): joins only what the guard expression itself reads.
      crosses g
        -- guard·(vkᵢ − pinᵢ), one polynomial per lane, only under a pin.
        || (b.vkPin.isSome && b.vk.any (fun lane =>
              crosses (g ++ exprCols lane)))
        -- guard·(commitᵢ − boundᵢ), one polynomial per lane, only under a bound.
        || (match b.bound with
            | none => false
            | some bs => (b.commit.zip bs).any (fun cb =>
                crosses (g ++ exprCols cb.1
                           ++ exprCols cb.2)))
  | l =>
      let inside : Nat → Bool := fun c => decide (lo ≤ c) && decide (c < lo + w)
      l.readCols.any inside && l.readCols.any (fun c => !inside c)

/-- ⚑ **THE ISLAND VERDICT** — no leg of the AIR joins the port's columns to the rest of the
trace. This is `no_arithmetic_call_names_an_xi_block` inverted into a reusable decidable: instead
of a theorem a reader must go find, a verdict a declaration must carry. -/
def portIslandFree (air : EffectAir) (p : PiPort) : Bool :=
  air.legs.all (fun l => !legJoinsAcross p.colLo p.colWidth l)

/-- ⚑ **A PORTED AIR** — an `EffectAir` carrying its port declarations in its TYPE. Cannot be
built unless every declared port is well-formed, actually PUBLISHED (a pin leg exists for every
slot, pinning a column of the port's own island), and genuinely FREE (the island verdict).

`free` is a plain field rather than an autoParam because at real descriptors it is discharged by
`native_decide` (the kernel measurably cannot walk the sound-multiply legs' `readCols`), and that
confession belongs at the declaration site, tagged `#assert_compiled` — not defaulted. -/
structure PortedAir where
  air     : EffectAir
  piCount : Nat
  ports   : List PiPort
  wf      : portsWf piCount ports = true := by decide
  pinned  : ∀ p ∈ ports, ∀ i, i < p.width →
              ∃ q : PiPinLeg, AirLeg.pin q ∈ air.legs ∧ q.idx = p.lo + i
                ∧ p.colLo ≤ q.col ∧ q.col < p.colLo + p.colWidth
  free    : ports.all (portIslandFree air) = true

/-! ## §5 — ⚑ THE CENSUS: a port no seam covers is UNREPRESENTABLE, not detectable. -/

/-- Seam `s` covers port `p` of descriptor `descName`: the matching end names the descriptor and
every port slot is a weld target (a pin endpoint or a zero-pin) on that end. -/
def seamCoversPort (s : SeamSpec) (descName : String) (p : PiPort) : Bool :=
  (s.left.descName == descName
    && (List.range p.width).all (fun i =>
          s.pins.any (fun q => q.1 == p.lo + i) || s.zeroLeft.any (fun z => z == p.lo + i)))
  || (s.right.descName == descName
    && (List.range p.width).all (fun i =>
          s.pins.any (fun q => q.2 == p.lo + i) || s.zeroRight.any (fun z => z == p.lo + i)))

/-- ⚑ **THE COVERED-PORT CONSTRUCTOR** — the census as a refusal. A value of this type cannot be
built for a port whose slots some seam does not cover, because `covers` is a decidable obligation
with a `by decide` default that fails. The `PinsTiedCensus` pattern, one layer up. -/
structure CoveredPort where
  descName : String
  port     : PiPort
  seam     : SeamSpec
  covers   : seamCoversPort seam descName port = true := by decide

/-- ⚑ **A NAMED OFF-CIRCUIT WELD AS A PORT'S COVER** — for the port shapes a `SeamSpec` cannot
express. A `proofBind` whose commitment is a DIGEST of a sub-proof's PI vector (the
`custom_proof_pi_commitment` shape) cannot be welded slot-for-slot: the cover is a consumer that
RECOMPUTES the digest from the sub-proof it verified and refuses the port's lanes against it —
`dregg_turn::executor::mina_head_verifier::check_transcript_binding` is the deployed instance.

What this object buys and what it does not, said plainly:

  * it makes the weld a NAMED, CENSUSED value in the authoring language — a port covered by
    `WeldCover w` names the Rust path and the sub-program fingerprint, so "covered by an executor
    check" is a checkable sentence instead of a docblock;
  * ⚠ Lean cannot check that the named Rust function exists or does what its name says. The teeth
    are on the other side: the welder's own both-polarity release tests (for the deployed
    instances, `mina_head_verifier.rs`'s REFUSAL 4/13/15 suites), which are named at each
    declaration site. A `WeldCover` whose welder has no test is a declaration wearing a cover —
    do not build one.

`subProgram` carries the nine `Faithful9` fingerprint lanes of the program whose sub-proof the
weld verifies against, so a re-emitted sub-descriptor is a visible drift here, not a silence. -/
structure WeldCover where
  descName   : String
  port       : PiPort
  welder     : String
  subProgram : List ℤ
  wf         : (!welder.isEmpty && subProgram.length == 9) = true := by decide

/-! ## §6 — JSON. Emitted beside the descriptors; Rust reads, Rust authors nothing. -/

private def jsonStr (s : String) : String := "\"" ++ s ++ "\""

def SeamEnd.toJson (e : SeamEnd) : String :=
  "{\"claim\":" ++ jsonStr e.claim
    ++ ",\"claim_len\":" ++ toString e.claimLen
    ++ ",\"descriptor\":" ++ jsonStr e.descName
    ++ ",\"lanes\":" ++ jsonArray (fun (v : ℤ) => toString v) e.descLanes ++ "}"

def SeamSpec.toJson (s : SeamSpec) : String :=
  "{\"name\":" ++ jsonStr s.name
    ++ ",\"left\":" ++ s.left.toJson
    ++ ",\"right\":" ++ s.right.toJson
    ++ ",\"pins\":" ++ jsonArray (fun (p : Nat × Nat) =>
          "[" ++ toString p.1 ++ "," ++ toString p.2 ++ "]") s.pins
    ++ ",\"zero_left\":" ++ jsonArray (fun (n : Nat) => toString n) s.zeroLeft
    ++ ",\"zero_right\":" ++ jsonArray (fun (n : Nat) => toString n) s.zeroRight ++ "}"

def PiPort.toJson (p : PiPort) : String :=
  "{\"name\":" ++ jsonStr p.name
    ++ ",\"lo\":" ++ toString p.lo ++ ",\"width\":" ++ toString p.width
    ++ ",\"col_lo\":" ++ toString p.colLo ++ ",\"col_width\":" ++ toString p.colWidth ++ "}"

/-- One descriptor's port declaration row for `ports.json`. -/
def portSetJson (descName : String) (piCount : Nat) (ports : List PiPort)
    (coveredBy : List String) : String :=
  "{\"descriptor\":" ++ jsonStr descName
    ++ ",\"pi_count\":" ++ toString piCount
    ++ ",\"ports\":" ++ jsonArray PiPort.toJson ports
    ++ ",\"covered_by\":" ++ jsonArray jsonStr coveredBy ++ "}"

/-! ## §7 — BOTH POLES, on toy objects. Every verdict here can go red, exhibited. -/

/-- A 4-column toy: a gate deriving col 1 from col 0, a pin publishing col 1 at slot 0, and a pin
publishing col 3 at slot 1 with NOTHING deriving col 3 — col 3 is an island. -/
private def demoAir : EffectAir :=
  { legs := [ .gate ⟨.var 1, .var 0⟩
            , .pin ⟨Dregg2.Circuit.Emit.EffectVmEmit.VmRow.first, 1, 0⟩
            , .pin ⟨Dregg2.Circuit.Emit.EffectVmEmit.VmRow.first, 3, 1⟩ ] }

private def demoIslandPort : PiPort := ⟨"island", 1, 1, 3, 1⟩
private def demoDerivedPort : PiPort := ⟨"derived", 0, 1, 1, 1⟩

/-- The island verdict HOLDS for the genuinely free block… -/
theorem demo_island_is_free : portIslandFree demoAir demoIslandPort = true := by decide

/-- …and REFUSES a "port" whose column a gate derives — the pole that makes the verdict a verdict.
A derived block is not a port; it is a claim, and claims are `pinsTied`/S-layer business. -/
theorem demo_derived_is_not_a_port : portIslandFree demoAir demoDerivedPort = false := by decide

private def demoSeam : SeamSpec :=
  { name := "demo", left := ⟨"l", 2, "dl", [0,0,0,0,0,0,0,0,0]⟩
  , right := ⟨"r", 2, "dr", [0,0,0,0,0,0,0,0,0]⟩
  , pins := [(0, 0)], zeroLeft := [], zeroRight := [1] }

theorem demoSeam_wf : demoSeam.wf = true := by decide

/-- An EMPTY seam is refused by `wf` — a seam that forces nothing is unrepresentable. -/
theorem an_empty_seam_is_not_wf :
    SeamSpec.wf { demoSeam with pins := [], zeroRight := [] } = false := by decide

/-- An out-of-range pin is refused. -/
theorem an_out_of_range_pin_is_not_wf :
    SeamSpec.wf { demoSeam with pins := [(2, 0)] } = false := by decide

/-- The census verdict holds when the seam's end covers the port's slots… -/
theorem demo_census_covers :
    seamCoversPort demoSeam "dl" ⟨"p", 0, 1, 0, 1⟩ = true := by decide

/-- …and goes red on a slot no pin and no zero-pin reaches (left slot 1 is welded by nothing). -/
theorem demo_census_refuses_an_uncovered_slot :
    seamCoversPort demoSeam "dl" ⟨"p", 1, 1, 0, 1⟩ = false := by decide

/-! ## §8 — axiom-hygiene tripwires. -/

#assert_axioms digitsVal_limb
#assert_axioms digitsVal_congr
#assert_axioms limb_inj
#assert_axioms Renders.eq_of_weld
#assert_axioms digitsVal_zero
#assert_axioms Renders.eq_zero
#assert_axioms limbAt_add
#assert_axioms prefix_weld
#assert_axioms demo_island_is_free
#assert_axioms demo_derived_is_not_a_port
#assert_axioms demoSeam_wf
#assert_axioms an_empty_seam_is_not_wf
#assert_axioms an_out_of_range_pin_is_not_wf
#assert_axioms demo_census_covers
#assert_axioms demo_census_refuses_an_uncovered_slot

end Dregg2.Circuit.Emit.Seam
