/-
# Dregg2.Circuit.Emit.PastaIpaFold — the GROUP side of the s-vector.

`PastaIPA.sVec_eq_bPoly` is the SCALAR-side statement: the `2^k`-entry vector `s` is the
coefficient vector of `b(X) = ∏_j (1 + c_j·X^{2^…})`, so `k` challenges determine all `2^k`
scalars and the accumulator may carry the `k`. This file is its twin on the other half of the
same object — what the `2^k` GROUP elements do.

## The two identities, and which one is the cost lever

**`msm_sVec_eq_fold`** (§2). `⟨s, G⟩` equals a `k`-round fold of the generators,
`G^{(j+1)} = G^{(j)}_lo + c_j · G^{(j)}_hi`, taking the FIRST challenge first and putting the
challenge on the HIGH half. That is o1-labs' own base fold (`poly-commitment/src/ipa.rs:1006`,
`combine_one_endo` = `g1 + x2·g2` via `commitment.rs:539` / `combine.rs:433`), and the
orientation is not guessed: the extractor asserts it on the real block (`[gt9]`) together with
three controls — reversed challenge order, swapped halves, and challenge inverses — each of
which comes out FALSE.

**`msmHorner_eq_msmN`** (§3). The same `⟨s, G⟩` evaluated by ONE shared doubling chain over the
bit planes: `acc ↦ 2·acc + Σ_{i : bit_b(a_i)} P_i`, MSB first.

**These two pull in opposite directions and only one of them is a speedup.** Counted in group
operations, the fold costs `2^k − 1` scalar multiplications — round `j` multiplies `2^{k−1−j}`
distinct points by `c_j`, and `2^{k−1} + … + 1 = 2^k − 1`. The naive MSM costs `2^k`. The fold
saves ONE. It is the right STRUCTURAL statement and the wrong evaluation strategy, because it
re-serialises the doubling chain `2^k − 1` times, once per point. §3 shares a single 255-step
doubling chain across all `2^k` terms and pays only one addition per SET BIT, which is where
the measured 7× comes from (`docs/MINA-REAL-BLOCK-GATE.md` §6.1). Expanding the scalar vector
is not the expensive half: `2^k` field multiplications are free next to one group operation.

## Scope

Both theorems are stated over an arbitrary `AddCommGroup`/`Module`, and are about REARRANGING a
sum. The kernel evaluation in `MinaWrapSgGate` computes over `PastaCurveComplete.rcbAddM` on
`Nat` triples, which carries no group instance in this tree; the transport is the SAME inherited
RCB residual (RCB'15 Thm 1: the unified formula is the complete group law on a prime-order short
Weierstrass curve) that every rung 5a–5f already carries. No new assumption is introduced, and
no rung below this one is re-opened.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`. `#guard` KATs reduce in the kernel.
Imports read-only (`PastaIPA`, for `sVec`/`sVec_length`).
-/
import Dregg2.Circuit.Emit.PastaIPA

namespace Dregg2.Circuit.Emit.PastaIpaFold

open Dregg2.Circuit.Emit.PastaIPA (sVec sVec_length)

set_option autoImplicit false

/-! ## §1 — The multi-scalar multiplication, and how it splits. -/

section Ring
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/-- `⟨a, P⟩ = Σ_i a_i • P_i`, in list order; extra entries on either side are dropped. -/
def msm : List R → List M → M
  | a :: as, P :: Ps => a • P + msm as Ps
  | _, _ => 0

theorem msm_nil_left (ps : List M) : msm ([] : List R) ps = 0 := by cases ps <;> rfl

theorem msm_nil_right (as : List R) : msm as ([] : List M) = 0 := by cases as <;> rfl

theorem msm_cons (a : R) (as : List R) (P : M) (ps : List M) :
    msm (a :: as) (P :: ps) = a • P + msm as ps := rfl

/-- `⟨a ++ b, p ++ q⟩ = ⟨a, p⟩ + ⟨b, q⟩` when the first blocks line up. -/
theorem msm_append (bs : List R) (qs : List M) : ∀ (as : List R) (ps : List M),
    as.length = ps.length → msm (as ++ bs) (ps ++ qs) = msm as ps + msm bs qs := by
  intro as
  induction as with
  | nil =>
    intro ps h
    cases ps with
    | nil => simp [msm_nil_left]
    | cons _ _ => simp at h
  | cons a as ih =>
    intro ps h
    cases ps with
    | nil => simp at h
    | cons P ps =>
      have h' : as.length = ps.length := by simpa using h
      simp only [List.cons_append, msm_cons, ih ps h', add_assoc]

/-- Scaling every scalar by `c` scales the whole MSM by `c`. -/
theorem msm_map_mul (c : R) : ∀ (as : List R) (ps : List M),
    msm (as.map (fun z => z * c)) ps = c • msm as ps := by
  intro as
  induction as with
  | nil => intro ps; simp [msm_nil_left]
  | cons a as ih =>
    intro ps
    cases ps with
    | nil => simp [msm_nil_right]
    | cons P ps =>
      simp only [List.map_cons, msm_cons, ih ps, smul_add, mul_smul, mul_comm a c]

/-- **The round distributes.** `Σ_i a_i • (lo_i + c • hi_i) = ⟨a, lo⟩ + c • ⟨a, hi⟩`. -/
theorem msm_zipWith_fold (c : R) : ∀ (as : List R) (lo hi : List M),
    lo.length = hi.length →
    msm as (List.zipWith (fun l h => l + c • h) lo hi) = msm as lo + c • msm as hi := by
  intro as
  induction as with
  | nil => intro lo hi _; simp [msm_nil_left]
  | cons a as ih =>
    intro lo hi hlen
    cases lo with
    | nil =>
      cases hi with
      | nil => simp [msm_nil_right]
      | cons _ _ => simp at hlen
    | cons l lo =>
      cases hi with
      | nil => simp at hlen
      | cons h hi =>
        have hlen' : lo.length = hi.length := by simpa using hlen
        simp only [List.zipWith_cons_cons, msm_cons, ih lo hi hlen', smul_add,
          smul_smul, mul_comm a c]
        abel

end Ring

/-! ## §2 — THE FOLDING IDENTITY: `⟨s, G⟩` is a `k`-round fold of the generators.

The recipe is o1-labs': halve, keep the LOW half, add `c_j` times the HIGH half, and consume
the challenges in the order the IPA produced them (`chal[0]` first). The extractor's `[gt9]`
controls refute all three ways of getting that wrong. -/

section Fold
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/-- One IPA base-folding round: `G ↦ G_lo + c · G_hi` (`ipa.rs:1006`). -/
def foldStep (c : R) (g : List M) : List M :=
  List.zipWith (fun l h => l + c • h) (g.take (g.length / 2)) (g.drop (g.length / 2))

/-- All `k` rounds, first challenge first. -/
def foldAll : List R → List M → List M
  | [], g => g
  | c :: cs, g => foldAll cs (foldStep c g)

theorem foldStep_length (c : R) (g : List M) (n : Nat) (h : g.length = 2 * n) :
    (foldStep c g).length = n := by
  have hd : g.length / 2 = n := by omega
  simp [foldStep, hd, h]
  omega

/-- **`msm_sVec_eq_fold`** — the group-side twin of `PastaIPA.sVec_eq_bPoly`. The `2^k`-term MSM
against the s-vector IS the `k`-round generator fold; the `2^k` group elements are contracted by
the same `k` challenges that determine the `2^k` scalars. -/
theorem msm_sVec_eq_fold (cs : List R) : ∀ (g : List M), g.length = 2 ^ cs.length →
    msm (sVec cs) g = (foldAll cs g).headD 0 := by
  induction cs with
  | nil =>
    intro g hg
    match g, hg with
    | [x], _ => simp [sVec, foldAll, msm_cons, msm_nil_left]
  | cons c rest ih =>
    intro g hg
    set n := 2 ^ rest.length with hn
    have hg2 : g.length = 2 * n := by
      rw [hg]; simp [hn, List.length_cons, pow_succ]; ring
    have hdiv : g.length / 2 = n := by omega
    have htake : (g.take n).length = n := by
      rw [List.length_take]; omega
    have hdrop : (g.drop n).length = n := by
      rw [List.length_drop]; omega
    have hs : (sVec (F := R) rest).length = n := by rw [sVec_length]
    have hsplit : g.take n ++ g.drop n = g := List.take_append_drop n g
    have hstep : foldStep c g = List.zipWith (fun l h => l + c • h) (g.take n) (g.drop n) := by
      rw [foldStep, hdiv]
    calc msm (sVec (c :: rest)) g
        = msm (sVec rest ++ (sVec rest).map (fun z => z * c)) (g.take n ++ g.drop n) := by
          rw [hsplit]; rfl
      _ = msm (sVec rest) (g.take n) + msm ((sVec rest).map (fun z => z * c)) (g.drop n) :=
          msm_append _ _ _ _ (by rw [hs, htake])
      _ = msm (sVec rest) (g.take n) + c • msm (sVec rest) (g.drop n) := by
          rw [msm_map_mul]
      _ = msm (sVec rest) (foldStep c g) := by
          rw [hstep, msm_zipWith_fold c _ _ _ (by rw [htake, hdrop])]
      _ = (foldAll rest (foldStep c g)).headD 0 :=
          ih _ (foldStep_length c g n hg2)
      _ = (foldAll (c :: rest) g).headD 0 := rfl

end Fold

/-! ## §3 — THE COST LEVER: one shared doubling chain over the bit planes.

§2 is the right statement about the object and the WRONG way to compute it: the fold pays
`2^k − 1` scalar multiplications, one per point per round, each with its own 255-step doubling
chain. Horner over the bit planes pays 255 doublings TOTAL plus one addition per set bit. -/

section Horner
variable {M : Type} [AddCommGroup M]

/-- `⟨a, P⟩` with `ℕ` scalars (the form the s-vector arrives in, as field-element values). -/
def msmN : List Nat → List M → M
  | a :: as, P :: Ps => a • P + msmN as Ps
  | _, _ => 0

theorem msmN_nil_left (ps : List M) : msmN [] ps = 0 := by cases ps <;> rfl

theorem msmN_nil_right (as : List Nat) : msmN as ([] : List M) = 0 := by cases as <;> rfl

theorem msmN_cons (a : Nat) (as : List Nat) (P : M) (ps : List M) :
    msmN (a :: as) (P :: ps) = a • P + msmN as ps := rfl

theorem msmN_zeros : ∀ (as : List Nat) (ps : List M),
    msmN (as.map (fun _ => 0)) ps = 0 := by
  intro as
  induction as with
  | nil => intro ps; simp [msmN_nil_left]
  | cons a as ih =>
    intro ps
    cases ps with
    | nil => simp [msmN_nil_right]
    | cons P ps => simp only [List.map_cons, msmN_cons, ih ps, zero_smul, add_zero]

/-- Scaling every scalar by `k` scales the MSM by `k`. -/
theorem msmN_smul (k : Nat) (f : Nat → Nat) : ∀ (as : List Nat) (ps : List M),
    msmN (as.map (fun a => k * f a)) ps = k • msmN (as.map f) ps := by
  intro as
  induction as with
  | nil => intro ps; simp [msmN_nil_left]
  | cons a as ih =>
    intro ps
    cases ps with
    | nil => simp [msmN_nil_right]
    | cons P ps =>
      simp only [List.map_cons, msmN_cons, ih ps, smul_add, mul_smul]

/-- Adding the scalar vectors adds the MSMs. -/
theorem msmN_add_scalars (f g : Nat → Nat) : ∀ (as : List Nat) (ps : List M),
    msmN (as.map (fun a => f a + g a)) ps = msmN (as.map f) ps + msmN (as.map g) ps := by
  intro as
  induction as with
  | nil => intro ps; simp [msmN_nil_left]
  | cons a as ih =>
    intro ps
    cases ps with
    | nil => simp [msmN_nil_right]
    | cons P ps =>
      simp only [List.map_cons, msmN_cons, ih ps, add_smul]
      abel

/-- One bit plane: add the points whose scalar has bit `i` set. `foldl`, not structural
recursion: the kernel's `whnf` blows its C stack on a 1024-deep structural recursion (measured,
`Stack overflow detected. Aborting.`), and `List.foldl` does not. -/
def bitPass (i : Nat) (as : List Nat) (ps : List M) (acc : M) : M :=
  (as.zip ps).foldl (fun a ap => if ap.1.testBit i then a + ap.2 else a) acc

theorem bitPass_cons (i a : Nat) (as : List Nat) (P : M) (ps : List M) (acc : M) :
    bitPass i (a :: as) (P :: ps) acc
      = bitPass i as ps (if a.testBit i then acc + P else acc) := rfl

theorem bitPass_eq (i : Nat) : ∀ (as : List Nat) (ps : List M) (acc : M),
    bitPass i as ps acc = acc + msmN (as.map (fun a => if a.testBit i then 1 else 0)) ps := by
  intro as
  induction as with
  | nil => intro ps acc; simp [bitPass, msmN_nil_left]
  | cons a as ih =>
    intro ps acc
    cases ps with
    | nil => simp [bitPass, msmN_nil_right]
    | cons P ps =>
      rw [bitPass_cons, ih ps]
      by_cases h : a.testBit i <;> simp [List.map_cons, msmN_cons, h, add_assoc]

/-- The Horner scan over a list of bit indices (MSB first). -/
def hornerAux (as : List Nat) (ps : List M) (idxs : List Nat) (acc : M) : M :=
  idxs.foldl (fun a i => bitPass i as ps (a + a)) acc

theorem hornerAux_cons (as : List Nat) (ps : List M) (i : Nat) (rest : List Nat) (acc : M) :
    hornerAux as ps (i :: rest) acc = hornerAux as ps rest (bitPass i as ps (acc + acc)) := rfl

/-- `⟨a, P⟩` by ONE doubling chain: `acc ↦ 2·acc + Σ_{i : bit_b(a_i)} P_i`, `b` from `nbits−1` to 0. -/
def msmHorner (nbits : Nat) (as : List Nat) (ps : List M) : M :=
  hornerAux as ps (List.range nbits).reverse 0

/-- `a % 2^(n+1)` splits into its top bit and its low `n` bits. -/
theorem nat_mod_pow_succ (a n : Nat) :
    a % 2 ^ (n + 1) = (if a.testBit n then 2 ^ n else 0) + a % 2 ^ n := by
  rw [Nat.mod_pow_succ, ← Nat.toNat_testBit a n]
  cases hb : a.testBit n <;> simp [hb] <;> ring

/-- The scan's invariant: after the top `n` bit planes, `acc` has been doubled `n` times and the
low `n` bits of every scalar have been paid in. -/
theorem hornerAux_range (as : List Nat) (ps : List M) : ∀ (n : Nat) (acc : M),
    hornerAux as ps (List.range n).reverse acc
      = (2 ^ n) • acc + msmN (as.map (fun a => a % 2 ^ n)) ps := by
  intro n
  induction n with
  | zero =>
    intro acc
    have hfun : (fun a : Nat => a % 2 ^ 0) = (fun _ : Nat => (0 : Nat)) := by
      funext a; rw [pow_zero, Nat.mod_one]
    rw [List.range_zero, List.reverse_nil]
    show acc = 2 ^ 0 • acc + msmN (as.map (fun a => a % 2 ^ 0)) ps
    rw [hfun, msmN_zeros, pow_zero, one_smul, add_zero]
  | succ n ih =>
    intro acc
    have hrev : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
      rw [List.range_succ, List.reverse_append]; rfl
    rw [hrev, hornerAux_cons, ih, bitPass_eq]
    have hsplit : (fun a : Nat => a % 2 ^ (n + 1))
        = (fun a : Nat => (if a.testBit n then 2 ^ n else 0) + a % 2 ^ n) := by
      funext a; exact nat_mod_pow_succ a n
    have hscale : (fun a : Nat => if a.testBit n then 2 ^ n else 0)
        = (fun a : Nat => 2 ^ n * (if a.testBit n then 1 else 0)) := by
      funext a; by_cases h : a.testBit n <;> simp [h]
    rw [hsplit, msmN_add_scalars, hscale, msmN_smul, pow_succ, mul_smul, two_smul]
    simp only [smul_add]
    abel

/-- **`msmHorner_eq_msmN`** — the bit-plane Horner scan computes the MSM, given a bit budget that
covers every scalar. This is the identity that makes the `2^15`-term SRS MSM tractable in the
kernel: 255 doublings TOTAL instead of 255 per term. -/
theorem msmHorner_eq_msmN (nbits : Nat) (as : List Nat) (ps : List M)
    (h : ∀ a ∈ as, a < 2 ^ nbits) : msmHorner nbits as ps = msmN as ps := by
  have hm : ∀ (l : List Nat), (∀ a ∈ l, a < 2 ^ nbits) → l.map (fun a => a % 2 ^ nbits) = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t iht =>
      intro hh
      rw [List.map_cons, Nat.mod_eq_of_lt (hh a (List.mem_cons_self ..)),
        iht (fun b hb => hh b (List.mem_cons_of_mem _ hb))]
  rw [msmHorner, hornerAux_range, smul_zero, zero_add, hm as h]

end Horner

/-! ## §3b — Contiguous chunking, so a `2^k`-term MSM can be split across theorems.

The kernel cannot take a `2^15`-term `decide` in one piece (elaborator peak RSS tracks the
largest single `decide`). These two say a cut into `n` contiguous slices of `c` loses nothing:
the slices reassemble the list IN ORDER, and each one is full. Proved once, generically, so no
`2^15`-element list equality is ever `decide`d. -/

/-- The `n` contiguous slices of width `c` reassemble the list, in order. -/
theorem flatMap_chunks {α : Type} (c : Nat) : ∀ (n : Nat) (l : List α), l.length = c * n →
    ((List.range n).flatMap (fun k => (l.drop (c * k)).take c)) = l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [this]
  | succ n ih =>
    intro l hl
    have hshift : ∀ k : Nat, (l.drop (c * (k + 1))).take c = ((l.drop c).drop (c * k)).take c := by
      intro k
      rw [List.drop_drop]
      congr 2
      ring
    have hlen : (l.drop c).length = c * n := by
      rw [List.length_drop, hl]; ring_nf; omega
    calc ((List.range (n + 1)).flatMap (fun k => (l.drop (c * k)).take c))
        = (l.drop (c * 0)).take c
          ++ ((List.range n).flatMap (fun k => (l.drop (c * (k + 1))).take c)) := by
          rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      _ = l.take c ++ ((List.range n).flatMap (fun k => ((l.drop c).drop (c * k)).take c)) := by
          simp only [Nat.mul_zero, List.drop_zero]
          congr 1
          apply List.flatMap_congr
          intro k _
          rw [hshift k]
      _ = l.take c ++ l.drop c := by rw [ih (l.drop c) hlen]
      _ = l := List.take_append_drop c l

/-- Every slice below the end is full — no ragged tail hiding inside a green partition. -/
theorem chunk_length {α : Type} (c n k : Nat) (l : List α) (hl : l.length = c * n) (hk : k < n) :
    ((l.drop (c * k)).take c).length = c := by
  rw [List.length_take, List.length_drop, hl]
  have : c * k + c ≤ c * n := by
    calc c * k + c = c * (k + 1) := by ring
      _ ≤ c * n := Nat.mul_le_mul_left c hk
  omega

/-! ## §3c — THE SAME SCAN OVER THE `Nat`-TRIPLE RCB ADD: the object that is actually EVALUATED.

§3 is stated at an arbitrary `AddCommGroup`, which no Pallas point in this tree carries. The
evaluated mirror below replaces `+` by `PastaCurveComplete.rcbAddM` and `0` by `Oproj`, term for
term: `bitPassM`/`hornerAuxM`/`msmHornerM` against `bitPass`/`hornerAux`/`msmHorner`. The transport
between the two is the SAME inherited RCB residual (RCB'15 Thm 1: the unified formula is the
complete group law on a prime-order short Weierstrass curve) that rungs 5a–5f carry. No new
assumption, and §3's `msmHorner_eq_msmN` is what says the scan computes the MSM at all.

⚑ THESE THREE LIVE HERE AND NOT IN A CONSUMER, because there are now TWO consumers and a second
copy would be a twin that agrees today:

* `MinaWrapSgCore.ChunkOk` — the KERNEL instance, 32 `decide`s, ~3.5 h of serial kernel;
* `Dregg2.Bridge.MinaWrapSg` — the COMPILED per-block checker, the same definitions under `#guard`.

Both must evaluate the same `msmHornerM` or the comparison between them means nothing. -/

section NatEval
open Dregg2.Circuit.Emit.PastaCurveComplete (rcbAddM Oproj)

/-- A Pasta point in projective `Nat` coordinates, the form the RCB reference add works on. -/
abbrev Pt := Nat × Nat × Nat

/-- One bit plane over the RCB complete add: fold in the points whose scalar has bit `i` set.
Mirror of `bitPass`. -/
def bitPassM (m b3 i : Nat) (as : List Nat) (ps : List Pt) (acc : Pt) : Pt :=
  (as.zip ps).foldl (fun a ap => if ap.1.testBit i then rcbAddM m b3 a ap.2 else a) acc

/-- The Horner scan over bit indices, MSB first. Mirror of `hornerAux`. -/
def hornerAuxM (m b3 : Nat) (as : List Nat) (ps : List Pt) (idxs : List Nat) (acc : Pt) : Pt :=
  idxs.foldl (fun a i => bitPassM m b3 i as ps (rcbAddM m b3 a a)) acc

/-- `⟨a, P⟩` by ONE doubling chain over the RCB complete add. Mirror of `msmHorner`.

⚑ In the KERNEL this must be fed at most 512 terms at a time: `whnf` builds the `foldl` accumulator
as a thunk chain of depth `nbits × terms` and blows the C stack outright at `255 × 1024`. COMPILED,
`List.foldl` is a tail loop and there is no such wall — the whole `2^15` goes through one call, and
the chunking in `MinaWrapSgCore` is an artefact of the kernel, not of the object. -/
def msmHornerM (m b3 nbits : Nat) (as : List Nat) (ps : List Pt) : Pt :=
  hornerAuxM m b3 as ps (List.range nbits).reverse Oproj

/-- The left-to-right sum of a list of points over the RCB complete add. -/
def ptsSumM (m b3 : Nat) (ps : List Pt) : Pt :=
  ps.foldl (fun acc P => rcbAddM m b3 acc P) Oproj

end NatEval

/-! ## §4 — The op counts these two identities actually buy, and the direction of the trade. -/

/-- Group scalar-multiplications the `k`-round generator fold performs: `2^k − 1`. -/
def foldScalarMuls (k : Nat) : Nat := 2 ^ k - 1

/-- Group scalar-multiplications the naive `2^k`-term MSM performs. -/
def naiveScalarMuls (k : Nat) : Nat := 2 ^ k

/-- Group ADDITIONS the bit-plane scan performs at `nbits` and `2^k` terms, at an average
Hamming weight of `nbits/2`: `nbits` doublings + one add per set bit. -/
def hornerAdds (k nbits : Nat) : Nat := nbits + 2 ^ k * (nbits / 2)

-- At Mina's wrap SRS (`k = 15`, `|srs.g| = 32768`, 255-bit scalars):
#guard foldScalarMuls 15 == 32767
#guard naiveScalarMuls 15 == 32768
-- The fold saves exactly ONE scalar multiplication. It is not the cost lever.
#guard naiveScalarMuls 15 - foldScalarMuls 15 == 1
-- One 255-bit double-and-add ladder is 2 complete adds per bit, so the naive/fold cost in
-- complete adds is ~16.7M, against ~4.2M for the scan: the measured ~7x.
#guard naiveScalarMuls 15 * (2 * 255) == 16711680
#guard hornerAdds 15 255 == 4161791

/-! ## §5 — Non-vacuity, over `ℤ` (both identities reduce in the kernel at concrete values),
including the SAME three orientation controls the extractor refutes in Rust on the real block. -/

/-- Four generators and two challenges — `2^2 = 4`. -/
def katG : List ℤ := [11, 13, 17, 19]
def katC : List ℤ := [5, 7]

-- The fold identity holds at concrete values.
#guard decide (msm (sVec katC) katG = (foldAll katC katG).headD 0)
-- and it is not an accident of the numbers: the MSM is what the coefficient vector says.
#guard sVec katC == ([1, 7, 5, 35] : List ℤ)
#guard decide (msm (sVec katC) katG = 11 + 7 * 13 + 5 * 17 + 35 * 19)

-- CONTROL (a) — challenges consumed in REVERSED order. Refuted, as `[gt9-ctl-a]` refutes it.
#guard decide (msm (sVec katC) katG ≠ (foldAll katC.reverse katG).headD 0)
-- CONTROL (b) — halves SWAPPED (`hi + c·lo`). Refuted, as `[gt9-ctl-b]` refutes it.
#guard decide (msm (sVec katC) katG ≠
  (foldAll katC [katG.getD 2 0, katG.getD 3 0, katG.getD 0 0, katG.getD 1 0]).headD 0)
-- CONTROL (c) — a perturbed generator does not fold to the same point.
#guard decide (msm (sVec katC) katG ≠ (foldAll katC [12, 13, 17, 19]).headD 0)

-- The Horner scan agrees with the MSM at concrete `ℕ` scalars, and needs the bit budget.
def katA : List Nat := [13, 200, 7, 255]
#guard decide (msmHorner 8 katA ([11, 13, 17, 19] : List ℤ) = msmN katA ([11, 13, 17, 19] : List ℤ))
#guard decide (msmN katA ([11, 13, 17, 19] : List ℤ) = 13 * 11 + 200 * 13 + 7 * 17 + 255 * 19)
-- Too few bits and the scan is WRONG — the hypothesis of `msmHorner_eq_msmN` is load-bearing.
#guard decide (msmHorner 4 katA ([11, 13, 17, 19] : List ℤ) ≠ msmN katA ([11, 13, 17, 19] : List ℤ))

#assert_axioms msm_append
#assert_axioms msm_map_mul
#assert_axioms msm_zipWith_fold
#assert_axioms foldStep_length
#assert_axioms msm_sVec_eq_fold
#assert_axioms msmN_zeros
#assert_axioms msmN_smul
#assert_axioms msmN_add_scalars
#assert_axioms bitPass_cons
#assert_axioms bitPass_eq
#assert_axioms hornerAux_cons
#assert_axioms nat_mod_pow_succ
#assert_axioms hornerAux_range
#assert_axioms msmHorner_eq_msmN
#assert_axioms flatMap_chunks
#assert_axioms chunk_length

end Dregg2.Circuit.Emit.PastaIpaFold
