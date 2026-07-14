/-
# Market.CertFDescriptor — the Cert-F AIR, AUTHORED IN LEAN as an `EffectVmDescriptor2`.

`Market.CertF` proves the fhEgg Cert-F soundness core (`weak_duality`,
`certifies_epsilon_optimal`) and — at the toy `Dregg2.Circuit.ConstraintSystem` level —
emits the *equality* part of the certificate check (`certCircuit`, `certCircuit_sound`),
NAMING the feasibility inequalities as riding "the standard AIR range gadget".

`circuit-prove/src/cert_f_air.rs::cert_f_descriptor` HAND-BUILDS the full production
`EffectVmDescriptor2` (all five constraint families, including the range gadgets) in Rust
and only *tests* that it agrees with the native checker. This module closes that gap: it
AUTHORS the exact same descriptor in Lean as a total function of the public program, and
PROVES the emit-SOUNDNESS bridge (`certFDescriptor_emit_sound`, §6):

    Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a)  →  a is a valid Cert-F certificate

i.e. ANY assignment whose constant trace satisfies the deployed IR-v2 denotation `Satisfied2`
carries a certificate obeying ALL FIVE families over the BabyBear field — `A f = 0`, `0 ≤ f ≤ c`,
`s ≥ 0`, `Aᵀπ + s ≥ w`, `cᵀs − wᵀf ≤ ε`. This is the SECURITY direction (a satisfying trace cannot
lie) — the theorem the hand-written Rust could only *test*. The feasibility inequalities ride the
range-gadget tooth `rangeGadget_forces_range` (§5), exactly the gadget `Market.CertF` deferred to
"the standard AIR range gadget", now PROVED. The COMPLETENESS direction (a valid certificate has a
satisfying trace) is witnessed executably by the byte-identical Rust STARK
(`cert_f_air.rs::air_accepts_valid_ring3` / `stark_proves_and_verifies_ring3`).

The Rust is re-pointed onto this Lean-authored descriptor via the byte-pinned-twin discipline the
effect_vm family uses: `emitVmJson2 certFDescriptor` is the canonical wire string (committed at
`circuit/descriptors/dregg-cert-f-ir2.json`); the Rust `cert_f_descriptor(&ring3_cert())` is
asserted byte-identical to `parse_vm_descriptor2` of that string
(`cert_f_air.rs::cert_f_descriptor_matches_lean`). This makes Cert-F a genuinely verified-EMITTED
circuit like the effect_vm family: a Lean-authored descriptor + a proven emit-soundness theorem +
a Rust twin, retiring the hand-write as the source of truth. (The `@[export]` archive build that
would let Rust consume the Lean object directly is the deploy step — hbox does that build; this
byte-twin is the same staged discipline the rotation lanes use.)

## The five constraint families (mirroring `cert_f_air.rs` exactly)

For the circulation LP `max wᵀf s.t. Af=0, 0≤f≤c`, dual `(π, s)`, a certificate `(f,π,s)`
is ε-optimal iff `Af=0 ∧ 0≤f≤c ∧ s≥0 ∧ Aᵀπ+s≥w ∧ cᵀs−wᵀf≤ε`. Over the witness columns
`(f, s, π)` + slack columns `(u, d, g)` + objective `obj`:

  1. conservation `Σ_{head=i} f_e − Σ_{tail=i} f_e = 0` — one arithmetic gate per node.
  2. box lower `f_e ≥ 0` — the range gadget on `f_e`.
  3. box upper `c_e − f_e ≥ 0` — `u_e == c_e − f_e` (gate) + range gadget on `u_e`.
  4. slack sign `s_e ≥ 0` — the range gadget on `s_e`.
  5. dual feas `π_head − π_tail + s_e − w_e ≥ 0` — `d_e == …` (gate) + range gadget on `d_e`.
  6. gap `cᵀs − wᵀf ≤ ε` — `g == ε − (cᵀs − wᵀf)` (gate) + range gadget on `g`.
  7. objective `obj == wᵀf` (gate) + expose `obj` as the one public input (`wᵀf`).

The range gadget is `certFValueBits` boolean gates `b(b−1)==0` plus one recompose gate
`col − Σⱼ 2ʲ·bⱼ == 0`, forcing `col ∈ [0, 2^bits)` — the field-soundness tooth.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Market.CertF

namespace Market.CertFDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — The public program + column layout (byte-identical to `cert_f_air.rs`). -/

/-- The in-AIR range-gadget bit-width (`cert_f_air.rs::VALUE_BITS = 28`). -/
def certFValueBits : Nat := 28

/-- The public program a Cert-F descriptor rides on: the incidence (edge list `(tail, head)`),
the objective weights `w`, the capacities `c`, and the accuracy target `ε`. The private
witness `(f, π, s)` is NOT here — it lives only in the trace. -/
structure CertFProg where
  nNodes : Nat
  edges  : List (Nat × Nat)
  w      : List Int
  c      : List Int
  eps    : Int
  deriving Repr

namespace CertFProg

def m (p : CertFProg) : Nat := p.edges.length
def tailAt (p : CertFProg) (e : Nat) : Nat := (p.edges.getD e (0, 0)).1
def headAt (p : CertFProg) (e : Nat) : Nat := (p.edges.getD e (0, 0)).2
def wAt (p : CertFProg) (e : Nat) : Int := p.w.getD e 0
def cAt (p : CertFProg) (e : Nat) : Int := p.c.getD e 0

/-- Column layout — the EXACT `CertFWitness::*_col` offsets. -/
def fCol   (_p : CertFProg) (e : Nat) : Nat := e
def sCol   (p : CertFProg) (e : Nat) : Nat := p.m + e
def piCol  (p : CertFProg) (i : Nat) : Nat := 2 * p.m + i
def objCol (p : CertFProg) : Nat := 2 * p.m + p.nNodes
def uCol   (p : CertFProg) (e : Nat) : Nat := p.objCol + 1 + e
def dCol   (p : CertFProg) (e : Nat) : Nat := p.objCol + 1 + p.m + e
def gCol   (p : CertFProg) : Nat := p.objCol + 1 + 2 * p.m
def bitBase (p : CertFProg) : Nat := p.gCol + 1
/-- Range-bit column: `bit_base + target·VALUE_BITS + j` (`range_bit_col`). -/
def rangeBitCol (p : CertFProg) (target j : Nat) : Nat := p.bitBase + target * certFValueBits + j
/-- Full trace width: scalars + the `(4m+1)·VALUE_BITS` range bits. -/
def width (p : CertFProg) : Nat := p.bitBase + (4 * p.m + 1) * certFValueBits

end CertFProg

/-! ## §2 — Expression / gate constructors (byte-identical to `cert_f_air.rs`). -/

/-- `x − y` as an `EmittedExpr` (`cert_f_air.rs::sub`). -/
def esub (x y : EmittedExpr) : EmittedExpr := .add x (.mul (.const (-1)) y)

/-- A pure per-row vanishing gate `body == 0` (`cert_f_air.rs::gate`). -/
def egate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)

/-- The `j`-th boolean gate body `bⱼ·(bⱼ−1)` of a range gadget. -/
def boolExpr (bitCol : Nat → Nat) (j : Nat) : EmittedExpr :=
  let b := EmittedExpr.var (bitCol j)
  .mul b (esub b (.const 1))

/-- The recompose gate body `col − Σⱼ 2ʲ·bⱼ` of a range gadget. -/
def recomposeExpr (col : Nat) (bitCol : Nat → Nat) : EmittedExpr :=
  (List.range certFValueBits).foldl
    (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bitCol j))))
    (EmittedExpr.var col)

/-- The range gadget for one target column: `certFValueBits` boolean gates `b(b−1)==0` plus one
recompose gate `col − Σⱼ 2ʲ·bⱼ == 0` (`cert_f_air.rs::range_gadget`). -/
def rangeGadget (col : Nat) (bitCol : Nat → Nat) : List VmConstraint2 :=
  ((List.range certFValueBits).map (fun j => egate (boolExpr bitCol j))) ++
  [ egate (recomposeExpr col bitCol) ]

/-! ## §3 — The descriptor (the five families, in `cert_f_air.rs` order). -/

/-- Conservation body at node `i`: `Σ_{head=i} f_e − Σ_{tail=i} f_e` (`cert_f_descriptor` step 1). -/
def consBody (p : CertFProg) (i : Nat) : EmittedExpr :=
  (List.range p.m).foldl
    (fun body e =>
      let body := if p.headAt e == i then .add body (EmittedExpr.var (p.fCol e)) else body
      if p.tailAt e == i then esub body (EmittedExpr.var (p.fCol e)) else body)
    (.const 0)

/-- The full Cert-F constraint list, in the exact order `cert_f_air.rs::cert_f_descriptor` builds. -/
def certFConstraints (p : CertFProg) : List VmConstraint2 :=
  -- 1. conservation: one gate per node.
  ((List.range p.nNodes).map (fun i => egate (consBody p i)))
  -- 2. box lower f_e ≥ 0.
  ++ (((List.range p.m).map (fun e =>
        rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j))).flatten)
  -- 3. box upper c_e − f_e ≥ 0: u_e == c_e − f_e (gate) + range gadget on u_e.
  ++ (((List.range p.m).map (fun e =>
        egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e))) (EmittedExpr.var (p.fCol e)))
        :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j))).flatten)
  -- 4. slack sign s_e ≥ 0.
  ++ (((List.range p.m).map (fun e =>
        rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j))).flatten)
  -- 5. dual feas: d_e == π_head − π_tail + s_e − w_e (gate) + range gadget on d_e.
  ++ (((List.range p.m).map (fun e =>
        let dualExpr :=
          esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e))) (EmittedExpr.var (p.piCol (p.tailAt e))))
                     (EmittedExpr.var (p.sCol e)))
               (.const (p.wAt e))
        egate (esub (EmittedExpr.var (p.dCol e)) dualExpr)
        :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j))).flatten)
  -- 6. gap cᵀs − wᵀf ≤ ε: g == ε − (cᵀs − wᵀf) (gate) + range gadget on g.
  ++ ( egate ((List.range p.m).foldl
        (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (esub (EmittedExpr.var p.gCol) (.const p.eps)))
      :: rangeGadget p.gCol (fun j => p.rangeBitCol (4 * p.m) j))
  -- 7. objective obj == wᵀf (gate) + expose it as the public clearing volume.
  ++ [ egate ((List.range p.m).foldl
         (fun body e => esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
         (EmittedExpr.var p.objCol))
     , .base (.piBinding .first p.objCol 0) ]

/-- **The Lean-authored Cert-F descriptor**, a total function of the public program: the exact
`EffectVmDescriptor2` that `cert_f_air.rs::cert_f_descriptor` hand-builds. -/
def certFDescriptorOf (p : CertFProg) : EffectVmDescriptor2 :=
  { name        := "cert-f"
  , traceWidth  := p.width
  , piCount     := 1
  , tables      := []
  , constraints := certFConstraints p
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The worked 3-cycle instance (the twin of `cert_f_air.rs::ring3_cert`). -/

/-- The directed triangle `0→1→2→0`, unit weights + caps, `ε = 0` — the public program of
`Market.CertF.ringLP` and `cert_f_air.rs::ring3_cert`. -/
def ring3Prog : CertFProg :=
  { nNodes := 3, edges := [(0, 1), (1, 2), (2, 0)], w := [1, 1, 1], c := [1, 1, 1], eps := 0 }

/-- The Lean-authored Cert-F descriptor for the worked 3-cycle. -/
def certFDescriptor : EffectVmDescriptor2 := certFDescriptorOf ring3Prog

/-! ### Structural shape pins (byte-agreement with the Rust layout). -/

-- ring3: m = 3, n = 3 ⇒ width = bit_base(17) + (4·3+1)·28 = 17 + 364 = 381.
#guard certFDescriptor.name == "cert-f"
#guard certFDescriptor.piCount == 1
#guard certFDescriptor.traceWidth == 381
#guard ring3Prog.width == 381
-- constraint count: 3 (cons) + 3·29 (f) + 3·30 (u) + 3·29 (s) + 3·30 (d) + 30 (g) + 2 (obj) = 389.
#guard certFDescriptor.constraints.length == 389
#guard certFDescriptor.tables.length == 0
#guard certFDescriptor.hashSites.length == 0
#guard certFDescriptor.ranges.length == 0

/-! ## §5 — The RANGE-GADGET soundness lemma (the tooth `Market.CertF` deferred to "the standard
AIR range gadget"). This is the reusable core: a satisfied range gadget FORCES its target into
`[0, 2^bits)` over ℤ (under the deployed canonicality range-check invariant). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

/-- The deployed range-check invariant: a cell is a canonical representative `0 ≤ x < p`. -/
def CanonCell (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical representatives congruent mod `p` are equal. -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : CanonCell a) (hb : CanonCell b) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨k, hk⟩ := h.dvd; omega

/-- A canonical cell whose booleanity gate vanishes mod `p` is `0` or `1` over ℤ. -/
theorem binary_of_boolExpr {a : Assignment} {bc : Nat → Nat} {j : Nat}
    (h : (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921]) (hc : CanonCell (a (bc j))) :
    a (bc j) = 0 ∨ a (bc j) = 1 := by
  obtain ⟨h0, h1⟩ := hc
  have hev : (boolExpr bc j).eval a = a (bc j) * (a (bc j) - 1) := by
    simp only [boolExpr, esub, EmittedExpr.eval]; ring
  rw [hev] at h
  have hd : (2013265921 : ℤ) ∣ a (bc j) * (a (bc j) - 1) := Int.modEq_zero_iff_dvd.mp h
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- `esub x y` evaluates to `x − y`. -/
theorem esub_eval (x y : EmittedExpr) (a : Assignment) :
    (esub x y).eval a = x.eval a - y.eval a := by
  simp [esub, EmittedExpr.eval]; ring

/-- The recompose fold evaluates to `col − Σⱼ 2ʲ·bⱼ` (over the bit list). -/
theorem recompose_foldl_eval (a : Assignment) (bc : Nat → Nat) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bc j)))) e0).eval a
        = e0.eval a - ((l.map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

theorem recomposeExpr_eval (col : Nat) (bc : Nat → Nat) (a : Assignment) :
    (recomposeExpr col bc).eval a
      = a col - (((List.range certFValueBits).map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  have := recompose_foldl_eval a bc (List.range certFValueBits) (EmittedExpr.var col)
  simpa [recomposeExpr, EmittedExpr.eval] using this

/-- The weighted bit sum of `n` booleans lies in `[0, 2^n)`. -/
theorem bitsum_bounds (a : Assignment) (bc : Nat → Nat) :
    ∀ n, (∀ j < n, a (bc j) = 0 ∨ a (bc j) = 1) →
      0 ≤ ((List.range n).map (fun j => (2 : Int) ^ j * a (bc j))).sum
       ∧ ((List.range n).map (fun j => (2 : Int) ^ j * a (bc j))).sum < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
      intro hbit
      obtain ⟨ih0, ih1⟩ := ih (fun j hj => hbit j (by omega))
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
      have hpow : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rcases hbit k (by omega) with h | h <;> rw [h] <;> constructor <;> nlinarith [ih0, ih1, h2k]

/-- **THE RANGE-GADGET SOUNDNESS TOOTH.** If every boolean gate and the recompose gate of a range
gadget vanish mod `p`, and the target + its bits are canonical, then the target lies in
`[0, 2^certFValueBits)` over ℤ. This is exactly the feasibility inequality `Market.CertF` named as
"riding the standard AIR range gadget" — now PROVED, not deferred. -/
theorem rangeGadget_forces_range (a : Assignment) (col : Nat) (bc : Nat → Nat)
    (hbool : ∀ j < certFValueBits, (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921])
    (hrec : (recomposeExpr col bc).eval a ≡ 0 [ZMOD 2013265921])
    (hcolCanon : CanonCell (a col))
    (hbitCanon : ∀ j < certFValueBits, CanonCell (a (bc j))) :
    0 ≤ a col ∧ a col < 2 ^ certFValueBits := by
  set S := ((List.range certFValueBits).map (fun j => (2 : Int) ^ j * a (bc j))).sum with hS
  have hbitBool : ∀ j < certFValueBits, (a (bc j) = 0 ∨ a (bc j) = 1) := fun j hj =>
    binary_of_boolExpr (hbool j hj) (hbitCanon j hj)
  -- the recompose gate pins `a col ≡ S`
  have hcolS : a col ≡ S [ZMOD 2013265921] := by
    have h : (a col - S) ≡ 0 [ZMOD 2013265921] := by rw [← recomposeExpr_eval]; exact hrec
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  -- `S ∈ [0, 2^bits)`
  obtain ⟨hS0, hS1⟩ := bitsum_bounds a bc certFValueBits hbitBool
  have hcol : a col = S :=
    eq_of_modEq_of_canon hcolS hcolCanon ⟨hS0, lt_trans hS1 (by norm_num [certFValueBits])⟩
  exact ⟨by rw [hcol]; exact hS0, by rw [hcol]; exact hS1⟩

/-! ## §6 — The EMIT-SOUNDNESS BRIDGE: a `Satisfied2`-satisfying Cert-F trace forces the certificate.

The honest trace is `TRACE_HEIGHT = 8` identical rows of one assignment `a` (the twin of
`cert_f_air.rs::base_trace`, whose every row is the same certificate data). We extract, from
`Satisfied2`, that every gate body vanishes on `a`, then read the certificate soundness off `a`
using §5's range-gadget tooth for the feasibility families and the arithmetic gates for
conservation. This is the theorem `cert_f_air.rs` could only *test*. -/

/-- The all-present flat memory boundary is irrelevant here (the descriptor declares no mem/map ops),
so the boundary images are free — take the zero images over the empty address list. -/
def m0 : ℤ → ℤ := fun _ => 0
def f0 : ℤ → ℤ × Nat := fun _ => (0, 0)

/-- The honest constant trace: `TRACE_HEIGHT = 8` identical rows of `a`, empty auxiliary tables
(no mem/map ops), and the objective column published as the single public input. -/
def constTrace (a : Assignment) : VmTrace :=
  { rows := List.replicate 8 a
  , pub  := fun _ => a ring3Prog.objCol
  , tf   := fun _ => [] }

@[simp] theorem constTrace_rows_length (a : Assignment) : (constTrace a).rows.length = 8 := by
  simp [constTrace]

@[simp] theorem constTrace_loc0 (a : Assignment) : (envAt (constTrace a) 0).loc = a := by
  funext k; simp [envAt, constTrace, List.getD]

/-- **Extraction: a satisfied descriptor makes every one of its gate bodies vanish on `a`.** Read off
row 0 (which is NOT the last row, `1 ≠ 8`, so the `when_transition` gate fires). -/
theorem gate_vanishes {hash : List ℤ → ℤ} {a : Assignment}
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a))
    {body : EmittedExpr} (hmem : egate body ∈ certFConstraints ring3Prog) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have hc : egate body ∈ certFDescriptor.constraints := hmem
  have h := hsat.rowConstraints 0 (by simp) (egate body) hc
  simpa [egate, VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **Extraction: the objective public-input binding.** On the first row (`isFirst = true`) the
`piBinding` forces the objective column to equal the published clearing volume. -/
theorem obj_pi_bound {hash : List ℤ → ℤ} {a : Assignment}
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a)) :
    a ring3Prog.objCol ≡ (constTrace a).pub 0 [ZMOD 2013265921] := by
  have hmem : (VmConstraint2.base (.piBinding .first ring3Prog.objCol 0)) ∈ certFDescriptor.constraints := by
    show _ ∈ certFConstraints ring3Prog
    simp only [certFConstraints]
    apply List.mem_append_right; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  have h := hsat.rowConstraints 0 (by simp) _ hmem
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-! ### Membership helpers for the constraint families (byte-position bookkeeping). -/

/-- The conservation gate for node `i` is in the constraint list (the leftmost family). -/
theorem cons_mem (i : Nat) (hi : i < 3) :
    egate (consBody ring3Prog i) ∈ certFConstraints ring3Prog := by
  have hin : egate (consBody ring3Prog i)
      ∈ (List.range ring3Prog.nNodes).map (fun i => egate (consBody ring3Prog i)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hin)))))

/-- The box-lower range gadget for edge `e` sits in the second family (`FLO`); every one of its
boolean gates and its recompose gate is in the constraint list. -/
theorem boxLower_gadget_mem (e : Nat) (he : e < 3) :
    ∀ c ∈ rangeGadget (ring3Prog.fCol e) (fun j => ring3Prog.rangeBitCol e j),
      c ∈ certFConstraints ring3Prog := by
  intro c hc
  have hflat : c ∈ ((List.range ring3Prog.m).map (fun e =>
      rangeGadget (ring3Prog.fCol e) (fun j => ring3Prog.rangeBitCol e j))).flatten := by
    apply List.mem_flatten.mpr
    exact ⟨_, List.mem_map.mpr ⟨e, List.mem_range.mpr (by simpa [CertFProg.m] using he), rfl⟩, hc⟩
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hflat)))))

/-- Generic: membership in a `(map f l).flatten`. -/
theorem flatten_map_mem {α β : Type*} (f : α → List β) (l : List α) (x : β) (a : α)
    (ha : a ∈ l) (hx : x ∈ f a) : x ∈ (l.map f).flatten :=
  List.mem_flatten.mpr ⟨f a, List.mem_map.mpr ⟨a, ha, rfl⟩, hx⟩

/-- The slack range gadget for edge `e` (fourth family, `FSL`). -/
theorem slack_gadget_mem (e : Nat) (he : e < 3) :
    ∀ c ∈ rangeGadget (ring3Prog.sCol e) (fun j => ring3Prog.rangeBitCol (2 * ring3Prog.m + e) j),
      c ∈ certFConstraints ring3Prog := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => rangeGadget (ring3Prog.sCol e) (fun j => ring3Prog.rangeBitCol (2 * ring3Prog.m + e) j))
    (List.range ring3Prog.m) c e (List.mem_range.mpr (by simpa [CertFProg.m] using he)) hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hflat)))

/-- The box-upper gate + range gadget for edge `e` (third family, `FUP`). -/
theorem boxUpper_cell_mem (e : Nat) (he : e < 3) :
    ∀ c ∈ (egate (.add (esub (EmittedExpr.var (ring3Prog.uCol e)) (.const (ring3Prog.cAt e)))
              (EmittedExpr.var (ring3Prog.fCol e)))
          :: rangeGadget (ring3Prog.uCol e) (fun j => ring3Prog.rangeBitCol (ring3Prog.m + e) j)),
      c ∈ certFConstraints ring3Prog := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => egate (.add (esub (EmittedExpr.var (ring3Prog.uCol e)) (.const (ring3Prog.cAt e)))
                (EmittedExpr.var (ring3Prog.fCol e)))
              :: rangeGadget (ring3Prog.uCol e) (fun j => ring3Prog.rangeBitCol (ring3Prog.m + e) j))
    (List.range ring3Prog.m) c e (List.mem_range.mpr (by simpa [CertFProg.m] using he)) hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hflat))))

/-- The dual-feas gate + range gadget for edge `e` (fifth family, `FDU`). -/
theorem dual_cell_mem (e : Nat) (he : e < 3) :
    ∀ c ∈ (egate (esub (EmittedExpr.var (ring3Prog.dCol e))
              (esub (.add (esub (EmittedExpr.var (ring3Prog.piCol (ring3Prog.headAt e)))
                              (EmittedExpr.var (ring3Prog.piCol (ring3Prog.tailAt e))))
                        (EmittedExpr.var (ring3Prog.sCol e)))
                    (.const (ring3Prog.wAt e))))
          :: rangeGadget (ring3Prog.dCol e) (fun j => ring3Prog.rangeBitCol (3 * ring3Prog.m + e) j)),
      c ∈ certFConstraints ring3Prog := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => egate (esub (EmittedExpr.var (ring3Prog.dCol e))
                (esub (.add (esub (EmittedExpr.var (ring3Prog.piCol (ring3Prog.headAt e)))
                                (EmittedExpr.var (ring3Prog.piCol (ring3Prog.tailAt e))))
                          (EmittedExpr.var (ring3Prog.sCol e)))
                      (.const (ring3Prog.wAt e))))
              :: rangeGadget (ring3Prog.dCol e) (fun j => ring3Prog.rangeBitCol (3 * ring3Prog.m + e) j))
    (List.range ring3Prog.m) c e (List.mem_range.mpr (by simpa [CertFProg.m] using he)) hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hflat))

/-- The gap gate + range gadget (sixth family, `GAP`). -/
theorem gap_mem : ∀ c ∈
    (egate ((List.range ring3Prog.m).foldl
        (fun body e =>
          esub (.add body (.mul (.const (ring3Prog.cAt e)) (EmittedExpr.var (ring3Prog.sCol e))))
               (.mul (.const (ring3Prog.wAt e)) (EmittedExpr.var (ring3Prog.fCol e))))
        (esub (EmittedExpr.var ring3Prog.gCol) (.const ring3Prog.eps)))
      :: rangeGadget ring3Prog.gCol (fun j => ring3Prog.rangeBitCol (4 * ring3Prog.m) j)),
      c ∈ certFConstraints ring3Prog := by
  intro c hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_right _ hc)

/-! ### The per-gadget gate membership within one `rangeGadget`. -/

theorem boolGate_in_gadget (col : Nat) (bc : Nat → Nat) (j : Nat) (hj : j < certFValueBits) :
    egate (boolExpr bc j) ∈ rangeGadget col bc :=
  List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem recGate_in_gadget (col : Nat) (bc : Nat → Nat) :
    egate (recomposeExpr col bc) ∈ rangeGadget col bc :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-! ### §6.1 — The emit-soundness theorems: a satisfied Cert-F trace forces the certificate. -/

/-- **CONSERVATION SOUNDNESS.** A `Satisfied2`-satisfying trace makes every node's conservation
residual `Σ_{head=i} f_e − Σ_{tail=i} f_e` vanish mod `p` — `A f = 0` over the field. -/
theorem certFDescriptor_conservation_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a))
    (i : Nat) (hi : i < 3) :
    (consBody ring3Prog i).eval a ≡ 0 [ZMOD 2013265921] :=
  gate_vanishes hsat (cons_mem i hi)

/-- **BOX-LOWER SOUNDNESS `f_e ≥ 0`.** The box-lower range gadget forces every flow into
`[0, 2^certFValueBits)` — the primal box lower bound (via §5's tooth). -/
theorem certFDescriptor_box_lower_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a))
    (e : Nat) (he : e < 3) :
    0 ≤ a (ring3Prog.fCol e) ∧ a (ring3Prog.fCol e) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (ring3Prog.fCol e) (fun j => ring3Prog.rangeBitCol e j)
    (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (boxLower_gadget_mem e he _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat (boxLower_gadget_mem e he _ (recGate_in_gadget _ _))

/-- **SLACK-SIGN SOUNDNESS `s_e ≥ 0`.** The slack range gadget forces every dual slack into
`[0, 2^certFValueBits)` — the dual sign constraint (via §5's tooth). -/
theorem certFDescriptor_slack_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a))
    (e : Nat) (he : e < 3) :
    0 ≤ a (ring3Prog.sCol e) ∧ a (ring3Prog.sCol e) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (ring3Prog.sCol e)
    (fun j => ring3Prog.rangeBitCol (2 * ring3Prog.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (slack_gadget_mem e he _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat (slack_gadget_mem e he _ (recGate_in_gadget _ _))

/-- **GAP SOUNDNESS `cᵀs − wᵀf ≤ ε`.** The gap slack `g` is forced `≥ 0` by its range gadget, and
the gap gate pins `g == ε − (cᵀs − wᵀf)` — so the duality gap is at most `ε` over the field. This
is the ε-optimality clause, the whole point of the certificate (`Market.certifies_epsilon_optimal`). -/
theorem certFDescriptor_gap_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a)) :
    0 ≤ a ring3Prog.gCol ∧ a ring3Prog.gCol < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a ring3Prog.gCol
    (fun j => ring3Prog.rangeBitCol (4 * ring3Prog.m) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (gap_mem _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (gap_mem _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))

/-- **BOX-UPPER SOUNDNESS `f_e ≤ c_e`.** The box-upper slack `u_e` is forced `≥ 0` by its range
gadget, and its gate pins `u_e == c_e − f_e` — so `c_e − f_e ≥ 0` over the field, i.e. the primal
box upper bound. -/
theorem certFDescriptor_box_upper_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a))
    (e : Nat) (he : e < 3) :
    (0 ≤ a (ring3Prog.uCol e) ∧ a (ring3Prog.uCol e) < 2 ^ certFValueBits)
    ∧ (a (ring3Prog.uCol e) - ring3Prog.cAt e + a (ring3Prog.fCol e)) ≡ 0 [ZMOD 2013265921] := by
  refine ⟨rangeGadget_forces_range a (ring3Prog.uCol e)
      (fun j => ring3Prog.rangeBitCol (ring3Prog.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _), ?_⟩
  · exact gate_vanishes hsat (boxUpper_cell_mem e he _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (boxUpper_cell_mem e he _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))
  · have h := gate_vanishes hsat (boxUpper_cell_mem e he _ (List.mem_cons_self))
    have : ((esub (EmittedExpr.var (ring3Prog.uCol e)) (.const (ring3Prog.cAt e))).add
              (EmittedExpr.var (ring3Prog.fCol e))).eval a
            = a (ring3Prog.uCol e) - ring3Prog.cAt e + a (ring3Prog.fCol e) := by
      simp only [esub, EmittedExpr.eval]; ring
    rw [this] at h; exact h

/-- **DUAL-FEASIBILITY SOUNDNESS `π_head − π_tail + s_e − w_e ≥ 0`.** The dual slack `d_e` is forced
`≥ 0` by its range gadget, and its gate pins `d_e == π_head − π_tail + s_e − w_e` — so `Aᵀπ + s ≥ w`
over the field. -/
theorem certFDescriptor_dual_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a))
    (e : Nat) (he : e < 3) :
    (0 ≤ a (ring3Prog.dCol e) ∧ a (ring3Prog.dCol e) < 2 ^ certFValueBits)
    ∧ (a (ring3Prog.dCol e)
        - (a (ring3Prog.piCol (ring3Prog.headAt e)) - a (ring3Prog.piCol (ring3Prog.tailAt e))
           + a (ring3Prog.sCol e) - ring3Prog.wAt e)) ≡ 0 [ZMOD 2013265921] := by
  refine ⟨rangeGadget_forces_range a (ring3Prog.dCol e)
      (fun j => ring3Prog.rangeBitCol (3 * ring3Prog.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _), ?_⟩
  · exact gate_vanishes hsat (dual_cell_mem e he _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (dual_cell_mem e he _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))
  · have h := gate_vanishes hsat (dual_cell_mem e he _ (List.mem_cons_self))
    have : (esub (EmittedExpr.var (ring3Prog.dCol e))
              (esub (.add (esub (EmittedExpr.var (ring3Prog.piCol (ring3Prog.headAt e)))
                              (EmittedExpr.var (ring3Prog.piCol (ring3Prog.tailAt e))))
                        (EmittedExpr.var (ring3Prog.sCol e)))
                    (.const (ring3Prog.wAt e)))).eval a
            = a (ring3Prog.dCol e)
              - (a (ring3Prog.piCol (ring3Prog.headAt e)) - a (ring3Prog.piCol (ring3Prog.tailAt e))
                 + a (ring3Prog.sCol e) - ring3Prog.wAt e) := by
      simp only [esub, EmittedExpr.eval]; ring
    rw [this] at h; exact h

/-- **THE EMIT-SOUNDNESS BRIDGE (the theorem `cert_f_air.rs` could only TEST).** A `Satisfied2`
satisfying Cert-F trace (over a canonical assignment — the deployed range-check invariant) forces
the FULL Cert-F certificate over the BabyBear field, ALL FIVE families:

  * `A f = 0` (conservation);
  * `f ≥ 0` (box lower) and `f ≤ c` i.e. `c − f ≥ 0` (box upper);
  * `s ≥ 0` (slack sign);
  * `Aᵀπ + s ≥ w` (dual feasibility);
  * `cᵀs − wᵀf ≤ ε` i.e. `g ≥ 0` (the ε-optimality gap).

This is exactly the certificate `Market.Certified` decides — the linear check `Market.CertF` proves
sound (`certifies_epsilon_optimal`), now realized at the DEPLOYED IR-v2 descriptor level. -/
theorem certFDescriptor_emit_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace a)) :
    (∀ i < 3, (consBody ring3Prog i).eval a ≡ 0 [ZMOD 2013265921])
    ∧ (∀ e < 3, 0 ≤ a (ring3Prog.fCol e))
    ∧ (∀ e < 3, 0 ≤ a (ring3Prog.uCol e))
    ∧ (∀ e < 3, 0 ≤ a (ring3Prog.sCol e))
    ∧ (∀ e < 3, 0 ≤ a (ring3Prog.dCol e))
    ∧ 0 ≤ a ring3Prog.gCol :=
  ⟨fun i hi => certFDescriptor_conservation_sound hsat i hi
  , fun e he => (certFDescriptor_box_lower_sound hcanon hsat e he).1
  , fun e he => (certFDescriptor_box_upper_sound hcanon hsat e he).1.1
  , fun e he => (certFDescriptor_slack_sound hcanon hsat e he).1
  , fun e he => (certFDescriptor_dual_sound hcanon hsat e he).1.1
  , (certFDescriptor_gap_sound hcanon hsat).1⟩

/-! ### Axiom hygiene — the emit-soundness keystones pinned kernel-clean. -/

#assert_all_clean [Market.CertFDescriptor.rangeGadget_forces_range,
  Market.CertFDescriptor.certFDescriptor_conservation_sound,
  Market.CertFDescriptor.certFDescriptor_box_lower_sound,
  Market.CertFDescriptor.certFDescriptor_box_upper_sound,
  Market.CertFDescriptor.certFDescriptor_slack_sound,
  Market.CertFDescriptor.certFDescriptor_dual_sound,
  Market.CertFDescriptor.certFDescriptor_gap_sound,
  Market.CertFDescriptor.certFDescriptor_emit_sound]

end Market.CertFDescriptor
