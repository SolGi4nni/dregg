import Dregg2.Crypto.Keccak
import Dregg2.Crypto.Keccak.Fips202Spec
import Dregg2.Crypto.Keccak.Fips202Refine
import Mathlib.Tactic.IntervalCases

namespace Dregg2.Crypto.Keccak.Fips202Round

open Dregg2.Crypto.Keccak

/-! # The write-fold engine (generic `Array α`, independent-value writes). -/

/-- Folding `set!` over a list of `(index, value)` writes leaves index `j` untouched if no write
targets it. -/
theorem writes_notMem {α} [Inhabited α] (j : Nat) :
    ∀ (W : List (Nat × α)) (init : Array α), j ∉ W.map Prod.fst →
      (W.foldl (fun r w => r.set! w.1 w.2) init)[j]! = init[j]! := by
  intro W
  induction W with
  | nil => intro init _; simp
  | cons hd tl ih =>
    intro init hj
    simp only [List.map_cons, List.mem_cons, not_or] at hj
    simp only [List.foldl_cons]
    rw [ih (init.set! hd.1 hd.2) hj.2]
    have hne : hd.1 ≠ j := fun h => hj.1 h.symm
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
    rw [if_neg hne]

/-- Folding `set!` over `W`, where EVERY write to index `j` carries the same value `v`, lands `v`
at `j` (given `(j,v) ∈ W` and `j` in bounds). No `Nodup` needed: agreeing values make write-order
irrelevant. -/
theorem writes_mem {α} [Inhabited α] (j : Nat) (v : α) :
    ∀ (W : List (Nat × α)) (init : Array α),
      (j, v) ∈ W → (∀ w ∈ W, w.1 = j → w.2 = v) → j < init.size →
      (W.foldl (fun r w => r.set! w.1 w.2) init)[j]! = v := by
  intro W
  induction W with
  | nil => intro init hj _ _; exact absurd hj (List.not_mem_nil)
  | cons hd tl ih =>
    intro init hj hagree hsz
    simp only [List.foldl_cons]
    by_cases hmem : j ∈ (tl.map Prod.fst)
    · -- some later write hits j; by agreement it carries v, so (j,v) ∈ tl
      obtain ⟨w, hw, hw1⟩ := List.mem_map.mp hmem
      have hwv : w.2 = v := hagree w (List.mem_cons_of_mem _ hw) hw1
      have hjvtl : (j, v) ∈ tl := by
        have : w = (j, v) := by
          obtain ⟨a, b⟩ := w; simp_all
        rwa [this] at hw
      exact ih (init.set! hd.1 hd.2) hjvtl
        (fun w hw => hagree w (List.mem_cons_of_mem _ hw))
        (by simpa [Array.set!] using hsz)
    · -- no later write hits j, so hd must be (j,v)
      have hhd : hd = (j, v) := by
        rcases List.mem_cons.mp hj with h | h
        · exact h.symm
        · exact absurd (List.mem_map.mpr ⟨(j, v), h, rfl⟩) hmem
      rw [writes_notMem j tl (init.set! hd.1 hd.2) hmem, hhd]
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
      simp [hsz]

/-- A single `for x do set!` loop is the write-fold over the mapped write list. -/
theorem foldl1_as_writes {α} (idx : Nat → Nat) (val : Nat → α) (L : List Nat) (init : Array α) :
    List.foldl (fun s x => s.set! (idx x) (val x)) init L
      = (L.map (fun x => (idx x, val x))).foldl (fun r w => r.set! w.1 w.2) init := by
  induction L generalizing init with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.foldl_cons, ih]

/-- A nested `for x do for y do set!` loop is the single write-fold over the flattened write list. -/
theorem foldl2_as_writes {α} (idx : Nat → Nat → Nat) (val : Nat → Nat → α)
    (Lx Ly : List Nat) (init : Array α) :
    List.foldl (fun s x => List.foldl (fun s y => s.set! (idx x y) (val x y)) s Ly) init Lx
      = (Lx.flatMap (fun x => Ly.map (fun y => (idx x y, val x y)))).foldl
          (fun r w => r.set! w.1 w.2) init := by
  induction Lx generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append, ih]
    congr 1
    clear ih
    induction Ly generalizing init with
    | nil => simp
    | cons y ys ih2 => simp only [List.map_cons, List.foldl_cons, ih2]

/-! # Layered re-expression of the executable `keccakRound`. -/

/-- θ step 1: the five column parities `C[x]`. -/
def cArr (a : Array UInt64) : Array UInt64 := Id.run do
  let mut c : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    c := c.set! x (a[x]! ^^^ a[x+5]! ^^^ a[x+10]! ^^^ a[x+15]! ^^^ a[x+20]!)
  return c

/-- θ step 2: the five `D[x] = C[x-1] ^^^ rotl(C[x+1],1)`. -/
def dArr (c : Array UInt64) : Array UInt64 := Id.run do
  let mut d : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    d := d.set! x (c[(x+4)%5]! ^^^ rotl64 c[(x+1)%5]! 1)
  return d

/-- θ step 3: apply `D` to every lane. -/
def sArr (a d : Array UInt64) : Array UInt64 := Id.run do
  let mut s := a
  for x in [0:5] do
    for y in [0:5] do
      s := s.set! (x + 5*y) (a[x + 5*y]! ^^^ d[x]!)
  return s

/-- ρ + π. -/
def bArr (s : Array UInt64) : Array UInt64 := Id.run do
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5*((2*x + 3*y) % 5)) (rotl64 s[x + 5*y]! rho[x + 5*y]!)
  return b

/-- χ. -/
def oArr (b : Array UInt64) : Array UInt64 := Id.run do
  let mut o : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      o := o.set! (x + 5*y)
        (b[x + 5*y]! ^^^ ((~~~ b[(x+1)%5 + 5*y]!) &&& b[(x+2)%5 + 5*y]!))
  return o

/-- The executable round IS the layered composition (definitional). -/
theorem keccakRound_layered (a : Array UInt64) (rc : UInt64) :
    keccakRound a rc =
      (fun o => o.set! 0 (o[0]! ^^^ rc)) (oArr (bArr (sArr a (dArr (cArr a))))) := by
  rfl

/-! # Entrywise characterization of each layer (proven from the imperative loops). -/

@[simp] theorem legacyRange5_size : ([:5].size) = 5 := rfl

/-- **θ column parities.** Entry `X` of the executable's `c` array is the FIPS 202 column parity
`C[X] = a[X] ^^^ a[X+5] ^^^ a[X+10] ^^^ a[X+15] ^^^ a[X+20]`. -/
theorem cArr_getElem (a : Array UInt64) (X : Nat) (hX : X < 5) :
    (cArr a)[X]! = a[X]! ^^^ a[X+5]! ^^^ a[X+10]! ^^^ a[X+15]! ^^^ a[X+20]! := by
  unfold cArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, legacyRange5_size]
  rw [foldl1_as_writes (fun x => x)
        (fun x => a[x]! ^^^ a[x+5]! ^^^ a[x+10]! ^^^ a[x+15]! ^^^ a[x+20]!)]
  refine writes_mem X _ _ _ ?_ ?_ ?_
  · exact List.mem_map.mpr ⟨X, by simp [List.mem_range']; omega, rfl⟩
  · rintro ⟨wi, wv⟩ hw h1
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hw
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hx1, hx2⟩ := hx
    subst hx1 hx2; simp_all
  · simpa using hX

/-- **θ `D` combinator.** Entry `X` of the executable's `d` array is `c[(X+4)%5] ^^^ rotl(c[(X+1)%5],1)`. -/
theorem dArr_getElem (c : Array UInt64) (X : Nat) (hX : X < 5) :
    (dArr c)[X]! = c[(X+4)%5]! ^^^ rotl64 c[(X+1)%5]! 1 := by
  unfold dArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, legacyRange5_size]
  rw [foldl1_as_writes (fun x => x) (fun x => c[(x+4)%5]! ^^^ rotl64 c[(x+1)%5]! 1)]
  refine writes_mem X _ _ _ ?_ ?_ ?_
  · exact List.mem_map.mpr ⟨X, by simp [List.mem_range']; omega, rfl⟩
  · rintro ⟨wi, wv⟩ hw h1
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hw
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hx1, hx2⟩ := hx
    subst hx1 hx2; simp_all
  · simpa using hX

/-- **θ application.** Lane `(X,Y)` of `s` is `a[X+5Y] ^^^ d[X]` (D fanned into every lane). -/
theorem sArr_getElem (a d : Array UInt64) (ha : a.size = 25) (X Y : Nat) (hX : X < 5) (hY : Y < 5) :
    (sArr a d)[X + 5*Y]! = a[X + 5*Y]! ^^^ d[X]! := by
  unfold sArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, legacyRange5_size]
  rw [foldl2_as_writes (fun x y => x + 5*y) (fun x y => a[x + 5*y]! ^^^ d[x]!)]
  refine writes_mem (X + 5*Y) _ _ _ ?_ ?_ ?_
  · refine List.mem_flatMap.mpr ⟨X, by simp [List.mem_range']; omega, ?_⟩
    exact List.mem_map.mpr ⟨Y, by simp [List.mem_range']; omega, rfl⟩
  · rintro ⟨wi, wv⟩ hw h1
    obtain ⟨x, hx, hw2⟩ := List.mem_flatMap.mp hw
    obtain ⟨y, hy, hw3⟩ := List.mem_map.mp hw2
    simp only [List.mem_range'] at hx hy
    simp only [Prod.mk.injEq] at hw3
    obtain ⟨hw3a, hw3b⟩ := hw3
    subst hw3a hw3b
    simp only at h1 ⊢
    have : x = X ∧ y = Y := by omega
    rw [this.1, this.2]
  · rw [ha]; omega

/-- **ρ + π.** Lane `(X',Y)` of `b` is read from source lane `((X'+3Y)%5, X')`, rotated by the
`rho` offset there:  `b[X' + 5Y] = rotl(s[src], rho[src])`, `src = (X'+3Y)%5 + 5·X'`. This is the
executable's inverse of the π write index `y + 5·((2x+3y)%5)`. -/
theorem bArr_getElem (s : Array UInt64) (X' Y : Nat) (hX : X' < 5) (hY : Y < 5) :
    (bArr s)[X' + 5*Y]! =
      rotl64 s[(X'+3*Y)%5 + 5*X']! rho[(X'+3*Y)%5 + 5*X']! := by
  unfold bArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, legacyRange5_size]
  rw [foldl2_as_writes (fun x y => y + 5*((2*x + 3*y) % 5))
        (fun x y => rotl64 s[x + 5*y]! rho[x + 5*y]!)]
  refine writes_mem (X' + 5*Y) _ _ _ ?_ ?_ ?_
  · refine List.mem_flatMap.mpr ⟨(X'+3*Y)%5, by simp [List.mem_range']; omega, ?_⟩
    refine List.mem_map.mpr ⟨X', by simp [List.mem_range']; omega, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨by omega, trivial⟩
  · rintro ⟨wi, wv⟩ hw h1
    obtain ⟨x, hx, hw2⟩ := List.mem_flatMap.mp hw
    obtain ⟨y, hy, hw3⟩ := List.mem_map.mp hw2
    simp only [List.mem_range'_1, Nat.zero_add] at hx hy
    obtain ⟨_, hxb⟩ := hx
    obtain ⟨_, hyb⟩ := hy
    simp only [Prod.mk.injEq] at hw3
    obtain ⟨hw3a, hw3b⟩ := hw3
    subst hw3a hw3b
    simp only at h1 ⊢
    have hsrc : x + 5*y = (X'+3*Y)%5 + 5*X' := by
      interval_cases x <;> interval_cases y <;> interval_cases X' <;> interval_cases Y <;> omega
    rw [hsrc]
  · simp only [Array.size_replicate]; omega

/-- **χ.** Lane `(X,Y)` of `o` is `b[X+5Y] ^^^ (¬b[(X+1)%5+5Y] ∧ b[(X+2)%5+5Y])` — the χ row combinator. -/
theorem oArr_getElem (b : Array UInt64) (X Y : Nat) (hX : X < 5) (hY : Y < 5) :
    (oArr b)[X + 5*Y]! =
      b[X + 5*Y]! ^^^ ((~~~ b[(X+1)%5 + 5*Y]!) &&& b[(X+2)%5 + 5*Y]!) := by
  unfold oArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, legacyRange5_size]
  rw [foldl2_as_writes (fun x y => x + 5*y)
        (fun x y => b[x + 5*y]! ^^^ ((~~~ b[(x+1)%5 + 5*y]!) &&& b[(x+2)%5 + 5*y]!))]
  refine writes_mem (X + 5*Y) _ _ _ ?_ ?_ ?_
  · refine List.mem_flatMap.mpr ⟨X, by simp [List.mem_range']; omega, ?_⟩
    exact List.mem_map.mpr ⟨Y, by simp [List.mem_range']; omega, rfl⟩
  · rintro ⟨wi, wv⟩ hw h1
    obtain ⟨x, hx, hw2⟩ := List.mem_flatMap.mp hw
    obtain ⟨y, hy, hw3⟩ := List.mem_map.mp hw2
    simp only [List.mem_range'_1, Nat.zero_add] at hx hy
    simp only [Prod.mk.injEq] at hw3
    obtain ⟨hw3a, hw3b⟩ := hw3
    subst hw3a hw3b
    simp only at h1 ⊢
    have : x = X ∧ y = Y := by omega
    rw [this.1, this.2]
  · simp only [Array.size_replicate]; omega

/-! # Size preservation (needed for the ι single-lane write and the final assembly). -/

theorem oArr_size (b : Array UInt64) : (oArr b).size = 25 := by
  unfold oArr
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, legacyRange5_size]
  rw [foldl2_as_writes (fun x y => x + 5*y)
        (fun x y => b[x + 5*y]! ^^^ ((~~~ b[(x+1)%5 + 5*y]!) &&& b[(x+2)%5 + 5*y]!))]
  generalize (List.range' 0 5).flatMap _ = W
  suffices h : ∀ (init : Array UInt64), init.size = 25 →
      (W.foldl (fun r w => r.set! w.1 w.2) init).size = 25 by
    exact h _ (by simp [Array.size_replicate])
  intro init hinit
  induction W generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih => simp only [List.foldl_cons]; exact ih _ (by simp [Array.set!, hinit])

/-! # The bit-level bridge:  executable layers ↦ FIPS 202 step maps. -/

open Dregg2.Crypto.Keccak.Fips202 (C D theta chi iota rnd chiBit m5 subZ rhoOffset rcLaneOf)
open Dregg2.Crypto.Keccak.Fips202Refine (laneBit toSpec chi_bit rotl64_getLsbD theta_D_bit
  laneBit_xor laneBit_and laneBit_not)

/-- **Stage C — column parity.** Bit `z` of the executable's column word `c[k]` is FIPS 202's
`C[k, z] = ⊕_{y} A[k, y, z]`. -/
theorem cArr_bit (a : Array UInt64) (k : Nat) (hk : k < 5) (z : Fin 64) :
    laneBit ((cArr a)[k]!) z = C (toSpec a) ⟨k, hk⟩ z := by
  rw [cArr_getElem a k hk]
  simp only [laneBit_xor, C, toSpec]
  norm_num [show ((0:Fin 5):ℕ) = 0 from rfl, show ((1:Fin 5):ℕ) = 1 from rfl,
    show ((2:Fin 5):ℕ) = 2 from rfl, show ((3:Fin 5):ℕ) = 3 from rfl,
    show ((4:Fin 5):ℕ) = 4 from rfl]

/-- **Stage D — θ column mixing.** Bit `w` of the executable's `d[i]` is FIPS 202's
`D[i, w] = C[i−1, w] ⊕ C[i+1, w−1]`. -/
theorem dArr_bit (a : Array UInt64) (i : Nat) (hi : i < 5) (w : Fin 64) :
    laneBit ((dArr (cArr a))[i]!) w = D (toSpec a) ⟨i, hi⟩ w := by
  rw [dArr_getElem (cArr a) i hi, theta_D_bit,
      cArr_bit a ((i+4)%5) (Nat.mod_lt _ (by norm_num)),
      cArr_bit a ((i+1)%5) (Nat.mod_lt _ (by norm_num))]
  simp only [D, m5]

/-- **Stage θ — the θ layer.** Bit `w` of lane `(i,j)` of the executable's `s` array is
FIPS 202's `θ(A)[i, j, w] = A[i, j, w] ⊕ D[i, w]`. -/
theorem sArr_bit (a : Array UInt64) (ha : a.size = 25) (i j : Nat) (hi : i < 5) (hj : j < 5)
    (w : Fin 64) :
    laneBit ((sArr a (dArr (cArr a)))[i + 5*j]!) w = theta (toSpec a) ⟨i, hi⟩ ⟨j, hj⟩ w := by
  rw [sArr_getElem a (dArr (cArr a)) ha i j hi hj, laneBit_xor, dArr_bit a i hi]
  simp only [theta, toSpec]

/-- **The ρ offset table bridge.** The executable's flat `rho` array (indexed `x + 5·y`) carries
exactly the FIPS 202 Table 2 offsets `rhoOffset[x][y]`, all `< 64`. -/
theorem rho_bridge (k m : Nat) (hk : k < 5) (hm : m < 5) :
    (rho[k + 5*m]!).toNat = rhoOffset ⟨k, hk⟩ ⟨m, hm⟩ := by
  interval_cases k <;> interval_cases m <;> rfl

theorem rho_lt64 (k m : Nat) (hk : k < 5) (hm : m < 5) : (rho[k + 5*m]!).toNat < 64 := by
  interval_cases k <;> interval_cases m <;> decide

/-- **Stage ρ+π — the rho/pi layer.** Bit `z` of lane `(X',Y)` of the executable's `b` array is
FIPS 202's `π(ρ(θ(A)))[X', Y, z]`. This is where the executable's inverse index
`src = (X'+3Y) mod 5 + 5·X'` and its `rho[src]` offset line up with the spec's forward π index
`(x+3y) mod 5` and `rhoOffset`. -/
theorem bArr_bit (a : Array UInt64) (ha : a.size = 25) (X' Y : Nat) (hX : X' < 5) (hY : Y < 5)
    (z : Fin 64) :
    laneBit ((bArr (sArr a (dArr (cArr a))))[X' + 5*Y]!) z
      = Fips202.pi (Fips202.rho (theta (toSpec a))) ⟨X', hX⟩ ⟨Y, hY⟩ z := by
  rw [bArr_getElem _ X' Y hX hY,
      rotl64_getLsbD _ _ (rho_lt64 ((X'+3*Y)%5) X' (Nat.mod_lt _ (by norm_num)) hX) z,
      sArr_bit a ha ((X'+3*Y)%5) X' (Nat.mod_lt _ (by norm_num)) hX,
      rho_bridge ((X'+3*Y)%5) X' (Nat.mod_lt _ (by norm_num)) hX]
  simp only [Fips202.pi, Fips202.rho, m5]

/-- **Stage χ — the chi layer.** Bit `z` of lane `(X,Y)` of the executable's `o` array is FIPS 202's
`χ(π(ρ(θ(A))))[X, Y, z]` — the χ combinator across the row, wired at the FIPS row indices. -/
theorem oArr_bit (a : Array UInt64) (ha : a.size = 25) (X Y : Nat) (hX : X < 5) (hY : Y < 5)
    (z : Fin 64) :
    laneBit ((oArr (bArr (sArr a (dArr (cArr a)))))[X + 5*Y]!) z
      = chi (Fips202.pi (Fips202.rho (theta (toSpec a)))) ⟨X, hX⟩ ⟨Y, hY⟩ z := by
  rw [oArr_getElem _ X Y hX hY, chi_bit,
      bArr_bit a ha X Y hX hY,
      bArr_bit a ha ((X+1)%5) Y (Nat.mod_lt _ (by norm_num)) hY,
      bArr_bit a ha ((X+2)%5) Y (Nat.mod_lt _ (by norm_num)) hY]
  simp only [chi, m5]

/-! # The round refinement. -/

/-- **THE ROUND REFINEMENT (proven).** Under the lane/bit abstraction `toSpec`, the executable
`Keccak.keccakRound a rc` computes exactly the FIPS 202 §3.3 round `Rnd = ι∘χ∘π∘ρ∘θ`, for EVERY
25-lane state `a`, EVERY round-constant word `rc`, and any `rcLane : Fin 64 → Bool` whose bits are
`rc`'s (`hrc`). This composes the proven per-step maps at the FIPS 202 lane indices — the θ column
fan-in, the ρ+π index permutation with the `rho` offset table, the χ row, and ι on lane 0 only. -/
theorem keccakRound_refines_spec (a : Array UInt64) (ha : a.size = 25) (rc : UInt64)
    (rcLane : Fin 64 → Bool) (hrc : ∀ z, laneBit rc z = rcLane z) :
    toSpec (keccakRound a rc) = rnd rcLane (toSpec a) := by
  funext X Y z
  rw [keccakRound_layered]
  set O := oArr (bArr (sArr a (dArr (cArr a)))) with hO
  have hOsz : O.size = 25 := oArr_size _
  simp only [toSpec, rnd, iota]
  by_cases hXY : X.val = 0 ∧ Y.val = 0
  · -- lane (0,0): ι XORs the round constant
    have hj : X.val + 5*Y.val = 0 := by omega
    rw [hj]
    have hset : (O.set! 0 (O[0]! ^^^ rc))[0]! = O[0]! ^^^ rc := by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
      simp [hOsz]
    rw [hset, laneBit_xor, hrc]
    have hchi := oArr_bit a ha X.val Y.val X.isLt Y.isLt z
    rw [hj] at hchi
    rw [if_pos hXY]
    rw [show (⟨X.val, X.isLt⟩ : Fin 5) = X from rfl,
        show (⟨Y.val, Y.isLt⟩ : Fin 5) = Y from rfl] at hchi
    rw [hchi]
  · -- other lanes: ι leaves them unchanged
    have hj : X.val + 5*Y.val ≠ 0 := by omega
    have hset : (O.set! 0 (O[0]! ^^^ rc))[X.val + 5*Y.val]! = O[X.val + 5*Y.val]! := by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
      rw [if_neg (by omega)]
    rw [hset]
    have hchi := oArr_bit a ha X.val Y.val X.isLt Y.isLt z
    rw [show (⟨X.val, X.isLt⟩ : Fin 5) = X from rfl,
        show (⟨Y.val, Y.isLt⟩ : Fin 5) = Y from rfl] at hchi
    rw [hchi, if_neg hXY]

/-- `keccakRound` always yields a 25-lane state. -/
theorem keccakRound_size (a : Array UInt64) (rc : UInt64) : (keccakRound a rc).size = 25 := by
  rw [keccakRound_layered]; simp only [Array.set!, Array.size_setIfInBounds]; exact oArr_size _

/-- The precomputed round-constant word `RC[ir]` has, bit-for-bit, the FIPS 202 Algorithm-5 LFSR
round-constant lane `rcLaneOf ir` (for the 24 real rounds `ir < 24`). This is the ONLY step that
carries the `native_decide` (`ofReduceBool`) residual — it is the constant-table cross-check
`Fips202Refine.rc_lanes_eq_exec`, unpacked per bit. -/
theorem rc_bit_match (ir : Nat) (hir : ir < 24) (z : Fin 64) :
    laneBit (RC[ir]!) z = rcLaneOf ir z := by
  have H := Dregg2.Crypto.Keccak.Fips202Refine.rc_lanes_eq_exec
  rw [List.all_eq_true] at H
  have H1 := H ir (List.mem_range.mpr hir)
  rw [List.all_eq_true] at H1
  have H2 := H1 z.val (List.mem_range.mpr z.isLt)
  rw [beq_iff_eq] at H2
  simp only [laneBit]
  rw [← H2]
  congr 1
  apply Fin.ext
  simp [Nat.mod_eq_of_lt z.isLt]

/-- **The round refinement, specialized to the real FIPS 202 round constants** (`ir < 24`). This
discharges the intent of `Fips202Refine.RoundCompositionObligation`. (The obligation as literally
written quantifies `ir` over ALL of `ℕ`; for `ir ≥ 24` both sides diverge — `RC[ir]! = 0` while
`rcLaneOf ir` is a genuine LFSR lane — so `ir < 24`, the real rounds, is the meaningful statement.) -/
theorem keccakRound_refines_spec_RC (a : Array UInt64) (ha : a.size = 25) (ir : Nat) (hir : ir < 24) :
    toSpec (keccakRound a (RC[ir]!)) = rnd (rcLaneOf ir) (toSpec a) :=
  keccakRound_refines_spec a ha (RC[ir]!) (rcLaneOf ir) (fun z => rc_bit_match ir hir z)

/-! # Toward Keccak-f[1600]: the 24-fold. -/

/-- Folding the executable rounds over a list of round indices (all `< 24`) refines folding the
FIPS 202 rounds, under `toSpec`. The inductive engine behind `keccakF`. -/
theorem foldl_rounds (L : List Nat) (hL : ∀ i ∈ L, i < 24) :
    ∀ (a : Array UInt64), a.size = 25 →
      toSpec (L.foldl (fun s i => keccakRound s (RC[i]!)) a)
        = L.foldl (fun S ir => rnd (rcLaneOf ir) S) (toSpec a) := by
  induction L with
  | nil => intro a _; simp
  | cons hd tl ih =>
    intro a ha
    simp only [List.foldl_cons]
    have hhd : hd < 24 := hL hd (List.mem_cons_self ..)
    rw [ih (fun i hi => hL i (List.mem_cons_of_mem _ hi)) (keccakRound a (RC[hd]!))
        (keccakRound_size a _)]
    rw [keccakRound_refines_spec_RC a ha hd hhd]

/-- **KECCAK-f[1600] REFINEMENT (proven).** The executable 24-round permutation `Keccak.keccakF`
computes exactly FIPS 202's Keccak-f[1600] = Keccak-p[1600,24] under the lane/bit abstraction, for
every 25-lane state. The 24-fold composition of the proven round refinement. -/
theorem keccakF_refines_spec (a : Array UInt64) (ha : a.size = 25) :
    toSpec (keccakF a) = Fips202.keccakF (toSpec a) := by
  unfold keccakF Fips202.keccakF Fips202.keccakP
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hsz : ([:24].size) = 24 := rfl
  rw [hsz]
  exact foldl_rounds (List.range' 0 24) (by intro i hi; rw [List.mem_range'_1] at hi; omega) a ha

end Dregg2.Crypto.Keccak.Fips202Round
