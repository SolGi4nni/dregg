/-
# AutomataflRevealRefine — Leg S SAT implies two genuine public openings.

This file proves the semantic statement for the exact emitted value
`automataflRevealDesc11`.  The only cryptographic carrier needed for functional
correctness is the standard chip-table faithfulness hypothesis
`ChipTableSound hash (t.tf .poseidon2)`: it says the served chip row computes the
named `hash` function.  Collision resistance is *not* smuggled into that carrier.

Unconditionally, a satisfying trace publishes the exact equalities

```
commit_s = hash [11*fy_s+fx_s, 11*ty_s+tx_s, seat_s, nonce_s]
```

for `s=0,1`, with all four coordinates in `[0,11)`, and transports all nine
old-board packed felts.  A successful post-reveal swap therefore constructs an
explicit arity-4 collision.

## The floor, refuted, and what replaced it

`Hash4NoCollision` was the named carrier of the swap-refusal corollary, and its own
docstring already said it "globally cannot hold" at a one-BabyBear-felt codomain
(generic birthday ≈ `2^15.5`).  A documented wound is not a detected one: nothing in
the tree PROVED it false, so `#floor_ratchet` could not derive it as a refuted floor
and both consumers were vacuous while reading as green.  `hash4NoCollision_false_babyBear`
is that refutation, by the same pigeonhole core as
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`.

The consumers are now stated on `RevealColl` — a PER-INSTANCE non-collision residual at
the exact preimage pair the extractor produces, refutable AND satisfiable at deployed
parameters, and strictly implied by the deleted global floor.  No declaration in this
file assumes `Hash4NoCollision` any more.
-/
import Dregg2.Circuit.Emit.AutomataflRevealEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.AutomataflRevealRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AutomataflRevealEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)

set_option autoImplicit false

/-! ## Field/canonical glue. -/

def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

theorem eq_of_modEq_small {a b : ℤ} (ha : -16 ≤ a ∧ a ≤ 16) (hb : -16 ≤ b ∧ b ≤ 16)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  omega

theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (binExpr c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 := by
  simp only [binExpr, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- The deployed canonical-residue envelope, including public inputs. -/
structure RevealCanon (t : VmTrace) : Prop where
  cells : ∀ c, Canon ((envAt t 0).loc c)
  pubs : ∀ i, Canon (t.pub i)

/-! ## Structured descriptor membership. -/

theorem mem_boardCarry {j : Nat} (hj : j < PACK_FELTS) :
    .base (.piBinding VmRow.first (boardPack j) (PACK_PI_BASE + j))
      ∈ automataflRevealDesc11.constraints := by
  unfold automataflRevealDesc11 revealConstraints boardCarryConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

theorem mem_commitJoin {s : Nat} (hs : s < 2) :
    .base (.piBinding VmRow.first (COMMIT s) (JOIN_COMMIT_PI_BASE + s))
      ∈ automataflRevealDesc11.constraints := by
  unfold automataflRevealDesc11 revealConstraints commitJoinPins
  exact List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)

theorem mem_seat_family {s : Nat} (hs : s < 2) {g : VmConstraint2}
    (hg : g ∈ oneSeatConstraints s) : g ∈ automataflRevealDesc11.constraints := by
  unfold automataflRevealDesc11 revealConstraints
  interval_cases s
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg))
  · exact List.mem_append_left _ (List.mem_append_right _ hg)

theorem mem_one_coord {s : Nat} {g : VmConstraint2} (hg : g ∈ coordConstraints s) :
    g ∈ oneSeatConstraints s := by
  unfold oneSeatConstraints
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ hg)))

theorem mem_one_flat {s : Nat} {g : VmConstraint2} (hg : g ∈ flatConstraints s) :
    g ∈ oneSeatConstraints s := by
  unfold oneSeatConstraints
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hg)))

theorem mem_one_seat {s : Nat} {g : VmConstraint2} (hg : g ∈ seatConstraints s) :
    g ∈ oneSeatConstraints s := by
  unfold oneSeatConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg))

theorem mem_one_lookup {s : Nat} : revealLookup s ∈ oneSeatConstraints s := by
  unfold oneSeatConstraints
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem mem_one_pin {s : Nat} {g : VmConstraint2} (hg : g ∈ openPins s) :
    g ∈ oneSeatConstraints s := by
  unfold oneSeatConstraints
  exact List.mem_append_right _ hg

theorem mem_coord_range {s q : Nat} (hq : q < 4) {g : VmConstraint2}
    (hg : g ∈ coordRangeConstraints (coordCol s q) (coordLo s q) (coordHi s q)) :
    g ∈ coordConstraints s := by
  unfold coordConstraints
  rw [List.mem_flatMap]
  exact ⟨q, List.mem_range.mpr hq, hg⟩

theorem lo_bin_mem {c lo hi k : Nat} (hk : k < 4) :
    gate (binExpr (lo + k)) ∈ coordRangeConstraints c lo hi := by
  interval_cases k <;> simp [coordRangeConstraints]

theorem hi_bin_mem {c lo hi k : Nat} (hk : k < 4) :
    gate (binExpr (hi + k)) ∈ coordRangeConstraints c lo hi := by
  interval_cases k <;> simp [coordRangeConstraints]

theorem lo_recomp_mem {c lo hi : Nat} :
    gate (sub (.var c) (bitsExpr lo)) ∈ coordRangeConstraints c lo hi := by
  simp [coordRangeConstraints]

theorem hi_recomp_mem {c lo hi : Nat} :
    gate (sub (sub (.const 10) (.var c)) (bitsExpr hi))
      ∈ coordRangeConstraints c lo hi := by
  simp [coordRangeConstraints]

theorem frm_mem {s : Nat} :
    gate (sub (.var (FRM s)) (.add (.mul (.const 11) (.var (FY s))) (.var (FX s))))
      ∈ flatConstraints s := by simp [flatConstraints]

theorem to_mem {s : Nat} :
    gate (sub (.var (TO s)) (.add (.mul (.const 11) (.var (TY s))) (.var (TX s))))
      ∈ flatConstraints s := by simp [flatConstraints]

theorem seat_exact_mem {s : Nat} :
    gate (sub (.var (SEAT s)) (.const (s : ℤ))) ∈ seatConstraints s := by
  simp [seatConstraints]

theorem pin_mem {s k : Nat} (hk : k < 7) :
    .base (.piBinding VmRow.first
      ([FX s, FY s, TX s, TY s, SEAT s, NONCE s, COMMIT s].getD k (FX s))
      (OPEN_PI_BASE s + k)) ∈ openPins s := by
  interval_cases k <;> simp [openPins]

/-! ## Extractors from `Satisfied2`. -/

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

theorem reveal_gate (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hlen : 1 < t.rows.length) {g : EmittedExpr}
    (hmem : gate g ∈ automataflRevealDesc11.constraints) :
    g.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by omega) (gate g) hmem
  have hlast : (0 + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  simpa only [gate, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] using h

theorem pin_eq (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) (col pi : Nat)
    (hmem : .base (.piBinding VmRow.first col pi) ∈ automataflRevealDesc11.constraints) :
    (envAt t 0).loc col = t.pub pi := by
  have h := hsat.rowConstraints 0 (by omega) _ hmem
  have hm : (envAt t 0).loc col ≡ (envAt t 0).pub pi [ZMOD 2013265921] :=
    (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) col pi).mp h
  exact eq_of_modEq_canon (hc.cells col) (hc.pubs pi) hm

theorem bits_bounds {a : Assignment} {b : Nat}
    (hb : ∀ k, k < 4 → a (b + k) = 0 ∨ a (b + k) = 1) :
    0 ≤ a b + 2 * a (b + 1) + 4 * a (b + 2) + 8 * a (b + 3)
      ∧ a b + 2 * a (b + 1) + 4 * a (b + 2) + 8 * a (b + 3) ≤ 15 := by
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  simp only [Nat.add_zero] at h0
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> omega

/-- Every revealed coordinate is genuinely in `[0,11)`, derived from the emitted
low/slack range gates. -/
theorem coord_bounds (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) (s q : Nat) (hs : s < 2) (hq : q < 4) :
    0 ≤ (envAt t 0).loc (coordCol s q) ∧ (envAt t 0).loc (coordCol s q) < 11 := by
  let e := (envAt t 0).loc
  let c := coordCol s q
  let lo := coordLo s q
  let hi := coordHi s q
  have blo : ∀ k, k < 4 → e (lo + k) = 0 ∨ e (lo + k) = 1 := by
    intro k hk
    apply bin_of_gate
    · exact reveal_gate hsat hlen (mem_seat_family hs (mem_one_coord
        (mem_coord_range hq (lo_bin_mem hk))))
    · exact hc.cells _
  have bhi : ∀ k, k < 4 → e (hi + k) = 0 ∨ e (hi + k) = 1 := by
    intro k hk
    apply bin_of_gate
    · exact reveal_gate hsat hlen (mem_seat_family hs (mem_one_coord
        (mem_coord_range hq (hi_bin_mem hk))))
    · exact hc.cells _
  obtain ⟨hlo0, hlo15⟩ := bits_bounds blo
  obtain ⟨hhi0, hhi15⟩ := bits_bounds bhi
  have hloGate := reveal_gate hsat hlen (mem_seat_family hs (mem_one_coord
    (mem_coord_range hq lo_recomp_mem)))
  have hhiGate := reveal_gate hsat hlen (mem_seat_family hs (mem_one_coord
    (mem_coord_range hq hi_recomp_mem)))
  simp only [sub, bitsExpr, EmittedExpr.eval] at hloGate hhiGate
  have hloMod : e c ≡ e lo + 2 * e (lo + 1) + 4 * e (lo + 2) + 8 * e (lo + 3)
      [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hloGate
  have hbitsCanon : Canon (e lo + 2 * e (lo + 1) + 4 * e (lo + 2) + 8 * e (lo + 3)) :=
    ⟨hlo0, by omega⟩
  have hceq : e c = e lo + 2 * e (lo + 1) + 4 * e (lo + 2) + 8 * e (lo + 3) :=
    eq_of_modEq_canon (hc.cells c) hbitsCanon hloMod
  have hhiMod : 10 - e c ≡ e hi + 2 * e (hi + 1) + 4 * e (hi + 2) + 8 * e (hi + 3)
      [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hhiGate
  have hhieq : 10 - e c = e hi + 2 * e (hi + 1) + 4 * e (hi + 2) + 8 * e (hi + 3) :=
    eq_of_modEq_small (by constructor <;> omega) (by constructor <;> omega) hhiMod
  change 0 ≤ e c ∧ e c < 11
  constructor <;> omega

theorem flat_frm_eq (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) (s : Nat) (hs : s < 2) :
    (envAt t 0).loc (FRM s) =
      11 * (envAt t 0).loc (FY s) + (envAt t 0).loc (FX s) := by
  have hfx := coord_bounds hsat hc hlen s 0 hs (by omega)
  have hfy := coord_bounds hsat hc hlen s 1 hs (by omega)
  have hfx' : 0 ≤ (envAt t 0).loc (FX s) ∧ (envAt t 0).loc (FX s) < 11 := by
    simpa [coordCol] using hfx
  have hfy' : 0 ≤ (envAt t 0).loc (FY s) ∧ (envAt t 0).loc (FY s) < 11 := by
    simpa [coordCol] using hfy
  have hg := reveal_gate hsat hlen (mem_seat_family hs (mem_one_flat frm_mem))
  simp only [sub, EmittedExpr.eval] at hg
  have hm : (envAt t 0).loc (FRM s) ≡
      11 * (envAt t 0).loc (FY s) + (envAt t 0).loc (FX s) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  exact eq_of_modEq_canon (hc.cells _) (by constructor <;> omega) hm

theorem flat_to_eq (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) (s : Nat) (hs : s < 2) :
    (envAt t 0).loc (TO s) =
      11 * (envAt t 0).loc (TY s) + (envAt t 0).loc (TX s) := by
  have htx := coord_bounds hsat hc hlen s 2 hs (by omega)
  have hty := coord_bounds hsat hc hlen s 3 hs (by omega)
  have htx' : 0 ≤ (envAt t 0).loc (TX s) ∧ (envAt t 0).loc (TX s) < 11 := by
    simpa [coordCol] using htx
  have hty' : 0 ≤ (envAt t 0).loc (TY s) ∧ (envAt t 0).loc (TY s) < 11 := by
    simpa [coordCol] using hty
  have hg := reveal_gate hsat hlen (mem_seat_family hs (mem_one_flat to_mem))
  simp only [sub, EmittedExpr.eval] at hg
  have hm : (envAt t 0).loc (TO s) ≡
      11 * (envAt t 0).loc (TY s) + (envAt t 0).loc (TX s) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  exact eq_of_modEq_canon (hc.cells _) (by constructor <;> omega) hm

theorem seat_eq (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) (s : Nat) (hs : s < 2) :
    (envAt t 0).loc (SEAT s) = (s : ℤ) := by
  have hg := reveal_gate hsat hlen (mem_seat_family hs (mem_one_seat seat_exact_mem))
  simp only [sub, EmittedExpr.eval] at hg
  have hm : (envAt t 0).loc (SEAT s) ≡ (s : ℤ) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  exact eq_of_modEq_canon (hc.cells _) (by constructor <;> omega) hm

theorem hash_eq (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hSound : ChipTableSound hash (t.tf .poseidon2)) (hlen : 1 < t.rows.length)
    (s : Nat) (hs : s < 2) :
    (envAt t 0).loc (COMMIT s) = hash
      [(envAt t 0).loc (FRM s), (envAt t 0).loc (TO s),
       (envAt t 0).loc (SEAT s), (envAt t 0).loc (NONCE s)] := by
  have hlk := hsat.rowConstraints 0 (by omega) (revealLookup s)
    (mem_seat_family hs mem_one_lookup)
  have hmem :
      (chipLookupTuple [.var (FRM s), .var (TO s), .var (SEAT s), .var (NONCE s)]
        (COMMIT s) (LANES s)).map (fun e => e.eval (envAt t 0).loc) ∈ t.tf .poseidon2 := by
    simpa only [VmConstraint2.holdsAt, revealLookup, Lookup.holdsAt] using hlk
  have h := chip_lookup_sound hash (t.tf .poseidon2) hSound (envAt t 0).loc
    [.var (FRM s), .var (TO s), .var (SEAT s), .var (NONCE s)]
    (COMMIT s) (LANES s) (by simp [CHIP_RATE]) hmem
  simpa [EmittedExpr.eval] using h

/-! ## Public semantic relation and the capstone. -/

structure PublicOpening where
  fx : ℤ
  fy : ℤ
  tx : ℤ
  ty : ℤ
  seat : ℤ
  nonce : ℤ
  commit : ℤ
deriving DecidableEq

def publicOpening (t : VmTrace) (s : Nat) : PublicOpening :=
  ⟨t.pub (OPEN_PI_BASE s), t.pub (OPEN_PI_BASE s + 1),
   t.pub (OPEN_PI_BASE s + 2), t.pub (OPEN_PI_BASE s + 3),
   t.pub (OPEN_PI_BASE s + 4), t.pub (OPEN_PI_BASE s + 5),
   t.pub (OPEN_PI_BASE s + 6)⟩

def openingPreimage (m : PublicOpening) : List ℤ :=
  [11 * m.fy + m.fx, 11 * m.ty + m.tx, m.seat, m.nonce]

structure Opens (hash : List ℤ → ℤ) (expectedSeat : Nat) (m : PublicOpening) : Prop where
  fxBounds : 0 ≤ m.fx ∧ m.fx < 11
  fyBounds : 0 ≤ m.fy ∧ m.fy < 11
  txBounds : 0 ≤ m.tx ∧ m.tx < 11
  tyBounds : 0 ≤ m.ty ∧ m.ty < 11
  seatExact : m.seat = (expectedSeat : ℤ)
  commitExact : m.commit = hash (openingPreimage m)

def CarriesOldPack (t : VmTrace) : Prop :=
  ∀ j, j < PACK_FELTS → (envAt t 0).loc (boardPack j) = t.pub (PACK_PI_BASE + j)

/-- The constrained contiguous commitment slice consumed by the recursive app-root weld. -/
def CarriesCommitJoin (t : VmTrace) : Prop :=
  ∀ s, s < 2 → (publicOpening t s).commit = t.pub (JOIN_COMMIT_PI_BASE + s)

def LegSSemantics (hash : List ℤ → ℤ) (t : VmTrace) : Prop :=
  CarriesOldPack t ∧ CarriesCommitJoin t ∧
    Opens hash 0 (publicOpening t 0) ∧ Opens hash 1 (publicOpening t 1)

theorem oneSeat_sat_imp_opens
    (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) (s : Nat) (hs : s < 2) :
    Opens hash s (publicOpening t s) := by
  have hfx := coord_bounds hsat hc hlen s 0 hs (by omega)
  have hfy := coord_bounds hsat hc hlen s 1 hs (by omega)
  have htx := coord_bounds hsat hc hlen s 2 hs (by omega)
  have hty := coord_bounds hsat hc hlen s 3 hs (by omega)
  have pfx := pin_eq hsat hc hlen (FX s) (OPEN_PI_BASE s)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 0) (by omega))))
  have pfy := pin_eq hsat hc hlen (FY s) (OPEN_PI_BASE s + 1)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 1) (by omega))))
  have ptx := pin_eq hsat hc hlen (TX s) (OPEN_PI_BASE s + 2)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 2) (by omega))))
  have pty := pin_eq hsat hc hlen (TY s) (OPEN_PI_BASE s + 3)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 3) (by omega))))
  have pse := pin_eq hsat hc hlen (SEAT s) (OPEN_PI_BASE s + 4)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 4) (by omega))))
  have pno := pin_eq hsat hc hlen (NONCE s) (OPEN_PI_BASE s + 5)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 5) (by omega))))
  have pcm := pin_eq hsat hc hlen (COMMIT s) (OPEN_PI_BASE s + 6)
    (mem_seat_family hs (mem_one_pin (pin_mem (s := s) (k := 6) (by omega))))
  have hfrm := flat_frm_eq hsat hc hlen s hs
  have hto := flat_to_eq hsat hc hlen s hs
  have hseat := seat_eq hsat hc hlen s hs
  have hhash := hash_eq hsat hSound hlen s hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [publicOpening] using pfx ▸ hfx
  · simpa [publicOpening] using pfy ▸ hfy
  · simpa [publicOpening] using ptx ▸ htx
  · simpa [publicOpening] using pty ▸ hty
  · simpa [publicOpening] using pse.symm.trans hseat
  · show t.pub (OPEN_PI_BASE s + 6) = hash (openingPreimage (publicOpening t s))
    rw [← pcm, hhash, hfrm, hto, pfx, pfy, ptx, pty, pse, pno]
    rfl

/-- **Leg S capstone.** SAT of the emitted descriptor implies the exact two-opening
semantics and transports every old-board packed PI.  Collision resistance is absent:
the result is the exact hash equality itself. -/
theorem legS_sat_imp_semantics
    (hsat : Satisfied2 hash automataflRevealDesc11 minit mfin maddrs t)
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hc : RevealCanon t) (hlen : 1 < t.rows.length) :
    LegSSemantics hash t := by
  refine ⟨?_, ?_, oneSeat_sat_imp_opens hsat hSound hc hlen 0 (by omega),
    oneSeat_sat_imp_opens hsat hSound hc hlen 1 (by omega)⟩
  · intro j hj
    exact pin_eq hsat hc hlen _ _ (mem_boardCarry hj)
  · intro s hs
    exact (pin_eq hsat hc hlen _ _ (mem_seat_family hs
      (mem_one_pin (pin_mem (s := s) (k := 6) (by omega))))).symm.trans
        (pin_eq hsat hc hlen _ _ (mem_commitJoin hs))

end Extract

/-! ## Collision extraction and the exactly-named swap floor. -/

/-- ⚠ **BROKEN / VACUOUS AT REAL PARAMS — REFUTED by `hash4NoCollision_false_babyBear`
below, and NO LONGER ASSUMED ANYWHERE.** Stated as injectivity on the length-4 slice of
the infinite `List ℤ`; a one-BabyBear-felt codomain cannot be injective on it, so every
theorem conditioned on this was vacuously true at deployed parameters. KEPT for the record
(the campaign convention — the old carrier stays doc-marked beside its tooth); the honest
per-instance replacement is `RevealColl`. -/
def Hash4NoCollision (hash : List ℤ → ℤ) : Prop :=
  ∀ x y : List ℤ, x.length = 4 → y.length = 4 → hash x = hash y → x = y

/-- **⚑ THE TOOTH — `Hash4NoCollision` is FALSE at the deployed one-felt BabyBear codomain.**
Pigeonhole, no Poseidon2 collision exhibited: the diagonal `n ↦ [n,0,0,0]` embeds the infinite
`ℤ` into the length-4 slice, so the floor would make `n ↦ hash [n,0,0,0]` injective into a
range contained in `[0, p)` — a finite set. Same counting core as
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`; `p = 2^31 − 2^27 + 1 = 2013265921`.

The file's own prose already carried the finding ("globally it cannot hold, and generic
birthday search is about `2^15.5`"). It was never a theorem, so `#floor_ratchet` could not
derive this as a refuted floor and both consumers passed the gate while saying nothing. -/
theorem hash4NoCollision_false_babyBear (hash : List ℤ → ℤ)
    (hb : ∀ xs : List ℤ, 0 ≤ hash xs ∧ hash xs < (2013265921 : ℤ)) :
    ¬ Hash4NoCollision hash := by
  intro hCR
  have hinj : Function.Injective (fun n : ℤ => hash [n, 0, 0, 0]) := by
    intro a b h
    have hx : ([a, 0, 0, 0] : List ℤ) = [b, 0, 0, 0] := hCR _ _ rfl rfl h
    have h1 := congrArg (fun l : List ℤ => l.headI) hx
    simpa using h1
  have hfin : (Set.range (fun n : ℤ => hash [n, 0, 0, 0])).Finite := by
    refine (Set.finite_Ico (0 : ℤ) 2013265921).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨(hb _).1, (hb _).2⟩
  haveI : Finite (Set.range (fun n : ℤ => hash [n, 0, 0, 0])) := hfin.to_subtype
  have hg : Function.Injective
      (fun a : ℤ => (⟨hash [a, 0, 0, 0], a, rfl⟩ : Set.range (fun n : ℤ => hash [n, 0, 0, 0]))) :=
    fun a b h => hinj (congrArg Subtype.val h)
  haveI : Finite ℤ := Finite.of_injective _ hg
  exact not_finite ℤ

def SameOpeningData (a b : PublicOpening) : Prop :=
  a.fx = b.fx ∧ a.fy = b.fy ∧ a.tx = b.tx ∧ a.ty = b.ty ∧
  a.seat = b.seat ∧ a.nonce = b.nonce

theorem sameData_of_preimage_eq {hash : List ℤ → ℤ} {s : Nat} {a b : PublicOpening}
    (ha : Opens hash s a) (hb : Opens hash s b)
    (hpre : openingPreimage a = openingPreimage b) : SameOpeningData a b := by
  obtain ⟨hafx, hafy, hatx, haty, _, _⟩ := ha
  obtain ⟨hbfx, hbfy, hbtx, hbty, _, _⟩ := hb
  have h0 := congrArg (fun l : List ℤ => l[0]?) hpre
  have h1 := congrArg (fun l : List ℤ => l[1]?) hpre
  have h2 := congrArg (fun l : List ℤ => l[2]?) hpre
  have h3 := congrArg (fun l : List ℤ => l[3]?) hpre
  norm_num [openingPreimage] at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Unconditional RED theorem.** Two accepted openings with the same published
commitment but different revealed data exhibit a concrete arity-4 hash collision. -/
theorem swapped_opening_extracts_collision {hash : List ℤ → ℤ} {s : Nat}
    {a b : PublicOpening} (ha : Opens hash s a) (hb : Opens hash s b)
    (hcommit : a.commit = b.commit) (hswap : ¬ SameOpeningData a b) :
    ∃ x y : List ℤ, x.length = 4 ∧ y.length = 4 ∧ x ≠ y ∧ hash x = hash y := by
  refine ⟨openingPreimage a, openingPreimage b, by rfl, by rfl, ?_, ?_⟩
  · intro hpre
    exact hswap (sameData_of_preimage_eq ha hb hpre)
  · rw [← ha.commitExact, hcommit, hb.commitExact]

/-- **THE PER-INSTANCE RESIDUAL — the honest replacement for the global floor.** A collision
of the deployed arity-4 hash AT THE EXACT PAIR the extractor produces, and nowhere else. It
is what the refuted `Hash4NoCollision` implied (so every consumer below is strictly stronger
than its old form), and unlike that floor it is both refutable and satisfiable at deployed
parameters — see the two poles immediately after it. -/
def RevealColl (hash : List ℤ → ℤ) (a b : PublicOpening) : Prop :=
  openingPreimage a ≠ openingPreimage b ∧
    hash (openingPreimage a) = hash (openingPreimage b)

/-- **THE RESIDUAL IS DISCHARGEABLE (positive pole).** At one opening against itself there is
nothing to collide, so `¬ RevealColl` holds outright. A side condition that can never be
discharged is a broken keystone, not a repaired one. -/
theorem revealColl_self_false (hash : List ℤ → ℤ) (a : PublicOpening) :
    ¬ RevealColl hash a a := fun h => h.1 rfl

/-- **THE RESIDUAL IS REFUTABLE (negative pole).** At the constant hash any two openings with
distinct preimages DO collide, so `¬ RevealColl` is not free — it is a real hypothesis about
the deployed hash at a named pair. -/
theorem revealColl_of_constant_hash (a b : PublicOpening)
    (hne : openingPreimage a ≠ openingPreimage b) :
    RevealColl (fun _ => (0 : ℤ)) a b := ⟨hne, rfl⟩

/-- **THE OLD FLOOR IS STRICTLY STRONGER.** `Hash4NoCollision` kills every residual at once —
recorded so the port is visibly a WEAKENING of the hypothesis, not a change of subject. -/
theorem not_revealColl_of_hash4NoCollision {hash : List ℤ → ℤ} (hCR : Hash4NoCollision hash)
    (a b : PublicOpening) : ¬ RevealColl hash a b :=
  fun h => h.1 (hCR _ _ rfl rfl h.2)

/-- **Post-reveal swap: bind, or EXHIBIT the collision. FLOOR-FREE.** Two accepted openings of
the same commitment either reveal the same data or collide at their own preimage pair. This is
the unconditional form; `opening_unique_of_noResid` is the binding corollary. -/
theorem opening_unique_or_collides {hash : List ℤ → ℤ} {s : Nat} {a b : PublicOpening}
    (ha : Opens hash s a) (hb : Opens hash s b) (hcommit : a.commit = b.commit) :
    SameOpeningData a b ∨ RevealColl hash a b := by
  by_cases hpre : openingPreimage a = openingPreimage b
  · exact Or.inl (sameData_of_preimage_eq ha hb hpre)
  · refine Or.inr ⟨hpre, ?_⟩
    rw [← ha.commitExact, hcommit, hb.commitExact]

/-- **Post-reveal swap refusal, on the per-instance residual.** Under `¬ RevealColl` at the two
openings actually presented, a second opening of the same commitment has exactly the same
move/seat/nonce data. Replaces the `Hash4NoCollision`-carrying `opening_unique_of_noCollision`,
whose hypothesis is refuted at deployed parameters. -/
theorem opening_unique_of_noResid {hash : List ℤ → ℤ} {s : Nat} {a b : PublicOpening}
    (ha : Opens hash s a) (hb : Opens hash s b) (hcommit : a.commit = b.commit)
    (hno : ¬ RevealColl hash a b) : SameOpeningData a b :=
  (opening_unique_or_collides ha hb hcommit).resolve_right hno

/-- The descriptor-level swap tooth: once one satisfying opening exists, another
satisfying trace with the same seat commitment but different opening data is refused,
under the PER-INSTANCE residual at the two presented openings (was: the refuted global
`Hash4NoCollision`). -/
theorem legS_swap_refused {hash : List ℤ → ℤ}
    {minit₁ minit₂ : ℤ → ℤ} {mfin₁ mfin₂ : ℤ → ℤ × Nat}
    {maddrs₁ maddrs₂ : List ℤ} {t₁ t₂ : VmTrace} {s : Nat} (hs : s < 2)
    (hsat₁ : Satisfied2 hash automataflRevealDesc11 minit₁ mfin₁ maddrs₁ t₁)
    (hSound₁ : ChipTableSound hash (t₁.tf .poseidon2)) (hc₁ : RevealCanon t₁)
    (hlen₁ : 1 < t₁.rows.length)
    (hSound₂ : ChipTableSound hash (t₂.tf .poseidon2)) (hc₂ : RevealCanon t₂)
    (hlen₂ : 1 < t₂.rows.length)
    (hcommit : (publicOpening t₁ s).commit = (publicOpening t₂ s).commit)
    (hno : ¬ RevealColl hash (publicOpening t₁ s) (publicOpening t₂ s))
    (hswap : ¬ SameOpeningData (publicOpening t₁ s) (publicOpening t₂ s)) :
    ¬ Satisfied2 hash automataflRevealDesc11 minit₂ mfin₂ maddrs₂ t₂ := by
  intro hsat₂
  have h₁ := oneSeat_sat_imp_opens hsat₁ hSound₁ hc₁ hlen₁ s hs
  have h₂ := oneSeat_sat_imp_opens hsat₂ hSound₂ hc₂ hlen₂ s hs
  exact hswap (opening_unique_of_noResid h₁ h₂ hcommit hno)

#assert_axioms coord_bounds
#assert_axioms flat_frm_eq
#assert_axioms hash_eq
#assert_axioms oneSeat_sat_imp_opens
#assert_axioms legS_sat_imp_semantics
#assert_axioms swapped_opening_extracts_collision
#assert_axioms hash4NoCollision_false_babyBear
#assert_axioms revealColl_self_false
#assert_axioms revealColl_of_constant_hash
#assert_axioms not_revealColl_of_hash4NoCollision
#assert_axioms opening_unique_or_collides
#assert_axioms opening_unique_of_noResid
#assert_axioms legS_swap_refused

#print axioms legS_sat_imp_semantics
#print axioms swapped_opening_extracts_collision
#print axioms legS_swap_refused

end Dregg2.Circuit.Emit.AutomataflRevealRefine
