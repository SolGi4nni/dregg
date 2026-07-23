/-
# Dregg2.Crypto.Arith.RowLibraryExperiment — THE LAYER-B GATE EXPERIMENT

`docs/DESIGN-proof-producing-arithmetizer.md` §7 names ONE critical-path unknown that decides
whether auto-generating the CONCRETE felt/row AIR refinement (Layer B) is a project or a research
bet:

  > *Is there a finite, composable, spec-indexed library of row-level refinement lemmas such that a
  > NEW descriptor's SAT⇒SEM proof is ASSEMBLY, not bespoke tactic work?*

The heavy hand proof it points at is `Dregg2.Circuit.Emit.DyckStackRefine.dyck_sat_imp_row_valid`
(`Satisfied2 dyckDesc → DyckRowValid` on every transition row, ~170 lines of primality splits and
field lifts). That proof carries its combinators as INLINE `have`s local to the theorem
(`G`/`W`/`gc`/`wt`/`dd`, plus the lane pins `hop/hlS/hcl/hz`) and as top-level generic lemmas
(`bin_of_gate`/`range_of_gate`/`symbol_of_cubic_dvd`/`prime_dvd_map_prod`). The design's own §7 note
reads that split as *evidence a library is latent* — this file tests the claim.

## What this file DOES

**§A — EXTERNALIZE.** It lifts the Dyck proof's inline felt combinators into descriptor-PARAMETRIC,
reusable lemmas (`d : EffectVmDescriptor2` is a free variable, never `dyckDesc`). Each lemma body is
the SAME tactic sequence the Dyck theorem runs inline, with the descriptor abstracted and the
canonicality facts taken as explicit hypotheses instead of pulled from `DyckCanon`:

  * `gate_of_sat`  — DyckStackRefine.`dyck_gate` with `dyckDesc ↦ d`   (any base gate ⇒ body ≡ 0)
  * `win_of_sat`   — DyckStackRefine.`dyck_win`  with `dyckDesc ↦ d`   (any window ⇒ body ≡ 0)
  * `bin_of_gate`  — the booleanity leaf, verbatim (already generic in DyckStackRefine)
  * `constLane_of_sat`  — the `hop/hlS/hcl/hz` lane-pin pattern (ungated `col = const`)
  * `gatedConst_of_sat` — the inline `gc` combinator (`sel=1 ⇒ col = const`)
  * `gatedThread_of_sat`— the inline `wt` combinator (`sel=1 ⇒ next[nc] = loc[lc]`)
  * `gatedDelta_of_sat` — the inline `dd` combinator (`sel=1 ⇒ next-col = base-col + k`)

Deliberately NOT imported from `DyckStackRefine`: this library is a LEAF built on the same base
(`DescriptorIR2` + the `gate_modEq_iff` transfer), which is the right shape for a spec-indexed
library — Dyck should build ON it, not the reverse. The small field-lift glue (`Canon`,
`eq_of_modEq_canon`, `eq_of_modEq_small`, `bin_of_gate`, `canon_*`, the `g*`/`w*` builders) is
copied verbatim from `DyckStackRefine` §0/§2 so the externalization fidelity is a literal
byte comparison, not a rewrite.

**§B — ASSEMBLE.** It defines a SECOND, independent descriptor `Toy.toyDesc` (4 constraints:
a boolean selector, an ungated constant lane, a gated constant, a gated cross-row thread) and its
row relation `Toy.ToyRowValid`, then proves `Toy.toy_sat_imp_row_valid` — its SAT⇒SEM bridge —
PURELY by composing the §A library lemmas. There is NO new felt reasoning in §B: no primality
split, no `omega` over field values, no `gate_modEq_iff`. Every proof leaf is a library-lemma
application plus a reused `canon_*` witness and a decidable-free membership search. That is exactly
the shape a metaprogram would emit: pick the constraint, pick the matching library lemma, discharge
membership.

## §C — THE VERDICT (see the trailing comment)

FEASIBLE, with the boundary stated precisely. The felt-level row combinators DO factor into a
descriptor-parametric library; the second descriptor's SAT⇒SEM genuinely assembled from it with
zero bespoke felt work. What does NOT live in the library — and cannot — is the SPEC: which columns
exist, which constraints the descriptor carries, and what the row relation asserts. That is the
input to generation, not part of the proof combinator set. The honest residual is the "assembly
driver" (constraint ↦ lemma dispatch) plus a handful of still-inline *shaping* lemmas in Dyck
(the exactly-one-of-three `kindPartition` case-split, and the `occupied_of_sat` occupancy tooth),
each of which is itself generic and factorable — they are more library members to add, not evidence
the approach is bespoke. See §C.

## Axiom hygiene / build

NEW file; imports read-only (`DescriptorIR2`, `EffectVmEmitTransfer`). Not reachable from
`Dregg2.lean`. No `sorry`. `set_option autoImplicit false`.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Crypto.Arith.RowLibraryExperiment

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)

set_option autoImplicit false
set_option maxRecDepth 4000

/-! ## §0 — Field-denotation glue (copied verbatim from `DyckStackRefine` §0). -/

/-- The deployed range-check invariant on a stored field cell: it is the canonical residue. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

instance (x : ℤ) : Decidable (Canon x) := inferInstanceAs (Decidable (_ ∧ _))

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- Two SMALL integers (`|·| ≤ 16`) congruent mod `p` are equal. -/
theorem eq_of_modEq_small {a b : ℤ} (ha : -16 ≤ a ∧ a ≤ 16) (hb : -16 ≤ b ∧ b ≤ 16)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

theorem canon_zero : Canon 0 := ⟨le_refl 0, by norm_num⟩
theorem canon_one : Canon 1 := ⟨by norm_num, by norm_num⟩
theorem canon_two : Canon 2 := ⟨by norm_num, by norm_num⟩
theorem canon_three : Canon 3 := ⟨by norm_num, by norm_num⟩

/-! ## §1 — The constraint builders (copied verbatim from `DyckStackRefine` §2).

These are already descriptor-agnostic in `DyckStackRefine` — they build `EmittedExpr`/`WindowExpr`/
`VmConstraint2` terms with no reference to any particular layout. Reproduced here so the library is a
standalone leaf. -/

/-- `x·(x−1)` — the booleanity gate. -/
def gBin (c : Nat) : EmittedExpr := .mul (.var c) (.add (.var c) (.const (-1)))
/-- `sel · e` — the `Gated` wrapper. -/
def gGate (sel : Nat) (e : EmittedExpr) : EmittedExpr := .mul (.var sel) e
/-- `a − b`. -/
def gSub (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))
/-- `a − k`. -/
def gSubK (a : Nat) (k : ℤ) : EmittedExpr := .add (.var a) (.const (-k))
/-- `a − b − k`. -/
def gDiffIs (a b : Nat) (k : ℤ) : EmittedExpr := .add (gSub a b) (.const (-k))
/-- `next[nc] − local[lc]` as a two-row window body. -/
def wThread (nc lc : Nat) : WindowExpr := .add (.nxt nc) (.mul (.const (-1)) (.loc lc))
/-- `local[sel] · e` — the `Gated` wrapper on a window body. -/
def wGate (sel : Nat) (e : WindowExpr) : WindowExpr := .mul (.loc sel) e
/-- A per-row gate constraint. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A TRANSITION window constraint. -/
def cw (b : WindowExpr) : VmConstraint2 := .windowGate ⟨b, true⟩

/-! ## §A — THE EXTERNALIZED ROW-REFINEMENT LIBRARY.

Descriptor-parametric (`d` free). Each lemma is the Dyck proof's inline combinator with the
descriptor abstracted; the felt reasoning lives HERE, once, and callers only `apply`. -/

section Library
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {d : EffectVmDescriptor2} {t : VmTrace}

/-- **LIB-`gate_of_sat`** — any base gate of `d` forces its body to vanish mod `p` on a TRANSITION
row. Descriptor-parametric generalization of `DyckStackRefine.dyck_gate` (identical body). -/
theorem gate_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ d.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **LIB-`win_of_sat`** — any transition window constraint of `d` fires on a TRANSITION row.
Descriptor-parametric generalization of `DyckStackRefine.dyck_win`. -/
theorem win_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {b : WindowExpr} (hw : cw b ∈ d.constraints) :
    b.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hw
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  have h2 : WindowConstraint.holdsAt (envAt t i) (i + 1 == t.rows.length) ⟨b, true⟩ := hrc
  simp only [WindowConstraint.holdsAt, if_true] at h2
  exact h2 hlf

/-- **LIB-`bin_of_gate`** — booleanity leaf (verbatim from `DyckStackRefine`, already generic): a
canonical cell whose `gBin` gate vanishes mod `p` is `0` or `1` over ℤ. -/
theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (gBin c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) : a c = 0 ∨ a c = 1 := by
  simp only [gBin, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- **LIB-`constLane_of_sat`** — the ungated lane-pin (`hop`/`hlS`/`hcl`/`hz` pattern): an ungated
gate `col − k` on a canonical cell forces `loc col = k` over ℤ. -/
theorem constLane_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {a : Nat} {k : ℤ}
    (hm : cg (gSubK a k) ∈ d.constraints)
    (hc : Canon ((envAt t i).loc a)) (hk : Canon k) :
    (envAt t i).loc a = k := by
  have hg := gate_of_sat hsat i hi hm
  simp only [gSubK, EmittedExpr.eval] at hg
  exact eq_of_modEq_canon hc hk ((gate_modEq_iff (by ring)).mp hg)

/-- **LIB-`gatedConst_of_sat`** — the inline `gc` combinator: a gated gate `sel · (col − k)` with the
selector on and both sides canonical forces `loc col = k`. -/
theorem gatedConst_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {sel a : Nat} {k : ℤ}
    (hm : cg (gGate sel (gSubK a k)) ∈ d.constraints)
    (hc : Canon ((envAt t i).loc a)) (hk : Canon k)
    (hs : (envAt t i).loc sel = 1) :
    (envAt t i).loc a = k := by
  have hg := gate_of_sat hsat i hi hm
  simp only [gGate, gSubK, EmittedExpr.eval] at hg
  rw [hs, one_mul] at hg
  exact eq_of_modEq_canon hc hk ((gate_modEq_iff (by ring)).mp hg)

/-- **LIB-`gatedThread_of_sat`** — the inline `wt` combinator: a gated cross-row thread
`sel · (next[nc] − loc[lc])` with the selector on and both cells canonical forces
`next[nc] = loc[lc]`. -/
theorem gatedThread_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {sel nc lc : Nat}
    (hm : cw (wGate sel (wThread nc lc)) ∈ d.constraints)
    (hcn : Canon ((envAt t i).nxt nc)) (hcl : Canon ((envAt t i).loc lc))
    (hs : (envAt t i).loc sel = 1) :
    (envAt t i).nxt nc = (envAt t i).loc lc := by
  have hw := win_of_sat hsat i hi hm
  simp only [wGate, wThread, WindowExpr.eval] at hw
  rw [hs, one_mul] at hw
  exact eq_of_modEq_canon hcn hcl ((gate_modEq_iff (by ring)).mp hw)

/-- **LIB-`gatedDelta_of_sat`** — the inline `dd` combinator: a gated delta
`sel · (dc − sc − k)` with the selector on and both columns in a small range forces
`loc dc = loc sc + k` over ℤ (a field congruence lifted through `eq_of_modEq_small`). -/
theorem gatedDelta_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {sel dc sc : Nat} {k : ℤ}
    (hm : cg (gGate sel (gDiffIs dc sc k)) ∈ d.constraints)
    (hs : (envAt t i).loc sel = 1)
    (hdc : -10 ≤ (envAt t i).loc dc ∧ (envAt t i).loc dc ≤ 10)
    (hsc : -10 ≤ (envAt t i).loc sc ∧ (envAt t i).loc sc ≤ 10)
    (hk0 : -6 ≤ k) (hk1 : k ≤ 6) :
    (envAt t i).loc dc = (envAt t i).loc sc + k := by
  have hg := gate_of_sat hsat i hi hm
  simp only [gGate, gDiffIs, gSub, EmittedExpr.eval] at hg
  rw [hs, one_mul] at hg
  obtain ⟨hd0, hd1⟩ := hdc
  obtain ⟨hs0, hs1⟩ := hsc
  exact eq_of_modEq_small ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    ((gate_modEq_iff (by ring)).mp hg)

end Library

/-! ## §B — THE SECOND DESCRIPTOR, ASSEMBLED FROM THE LIBRARY.

A fresh 4-constraint descriptor with NO relation to Dyck. Its SAT⇒SEM bridge is proven by composing
the §A lemmas only — no felt reasoning appears below this line. -/

namespace Toy

/-- Selector column. -/
def SEL : Nat := 0
/-- A column pinned (ungated) to the constant `2`. -/
def A : Nat := 1
/-- A column gated-pinned to `3` when `SEL = 1`. -/
def B : Nat := 2
/-- Cross-row NEXT target column. -/
def NC : Nat := 3
/-- Cross-row LOCAL source column. -/
def LC : Nat := 4
/-- Toy trace width. -/
def WIDTH : Nat := 5

/-- The toy constraint list: one of each combinator kind the library covers. -/
def toyConstraints : List VmConstraint2 :=
  [ cg (gBin SEL),                    -- boolean selector          → `bin_of_gate`
    cg (gSubK A 2),                   -- ungated constant lane      → `constLane_of_sat`
    cg (gGate SEL (gSubK B 3)),       -- gated constant             → `gatedConst_of_sat`
    cw (wGate SEL (wThread NC LC)) ]  -- gated cross-row thread     → `gatedThread_of_sat`

/-- The second descriptor. -/
def toyDesc : EffectVmDescriptor2 :=
  { name        := "row-library-toy-v1"
  , traceWidth  := WIDTH
  , piCount     := 0
  , tables      := []
  , constraints := toyConstraints
  , hashSites   := []
  , ranges      := [] }

/-- The canonicality envelope (same shape as `DyckCanon`). -/
structure ToyCanon (t : VmTrace) : Prop where
  cells : ∀ i c, Canon (t.rows.getD i zeroAsg c)

/-- The genuine per-row relation the toy descriptor computes. -/
structure ToyRowValid (env : VmRowEnv) : Prop where
  selBool  : env.loc SEL = 0 ∨ env.loc SEL = 1
  aPinned  : env.loc A = 2
  bGated   : env.loc SEL = 1 → env.loc B = 3
  threaded : env.loc SEL = 1 → env.nxt NC = env.loc LC

/-- Decidable-free membership search into `toyDesc.constraints` (mirrors `DyckStackRefine.dyck_mem`;
`VmConstraint2` has no `DecidableEq` so this cannot be a `decide`). -/
macro "toy_mem" : tactic =>
  `(tactic| (show _ ∈ toyConstraints
             simp only [toyConstraints]
             repeat' first | exact List.Mem.head _ | apply List.Mem.tail))

/-- **`toy_sat_imp_row_valid` — the SECOND descriptor's SAT⇒SEM, ASSEMBLED.** Every field is
discharged by ONE §A library-lemma application plus a reused `canon_*` witness and a membership
search. No primality split, no `gate_modEq_iff`, no `omega` over field values appears here: this is
pure library assembly, the shape a metaprogram would emit. -/
theorem toy_sat_imp_row_valid {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash toyDesc minit mfin maddrs t)
    (hcanon : ToyCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ToyRowValid (envAt t i) := by
  refine { selBool := ?_, aPinned := ?_, bGated := ?_, threaded := ?_ }
  · exact bin_of_gate (gate_of_sat hsat i hi (by toy_mem)) (hcanon.cells i SEL)
  · exact constLane_of_sat hsat i hi (by toy_mem) (hcanon.cells i A) canon_two
  · intro hs
    exact gatedConst_of_sat hsat i hi (by toy_mem) (hcanon.cells i B) canon_three hs
  · intro hs
    exact gatedThread_of_sat hsat i hi (by toy_mem) (hcanon.cells (i + 1) NC) (hcanon.cells i LC) hs

end Toy

/-! ## §C — VERDICT: **FEASIBLE** (with the boundary stated precisely).

**What the experiment SHOWED.**
1. The Dyck proof's inline felt combinators (`G`/`W`/`gc`/`wt`/`dd`, the lane pins, the booleanity
   leaf) externalize CLEANLY into descriptor-parametric lemmas (§A). The only change from the
   inline versions is `dyckDesc ↦ d` and pulling canonicality from explicit hypotheses instead of
   `DyckCanon` — the tactic bodies are otherwise identical.
2. A SECOND, unrelated descriptor's SAT⇒SEM (`Toy.toy_sat_imp_row_valid`) assembled from that
   library with ZERO new felt reasoning — every leaf is a library `apply` + a reused `canon_*`
   witness + a membership search. That is a metaprogram-emittable pattern.

⇒ For the class of constraints the library covers (boolean selectors, ungated/gated constant pins,
gated cross-row threads, gated small-range deltas — i.e. the bulk of a pushdown/DFA-style row AIR),
the design's §7 question answers YES: the row refinement is ASSEMBLY, not bespoke tactic work.
Layer B auto-gen is a real project for this constraint class, not a research bet.

**The honest BOUNDARY (what the library does NOT and CANNOT absorb).**
* The SPEC is not in the library. `toyDesc`, `ToyRowValid`, and the constraint↔field mapping are
  the INPUT to generation. The library covers the PROOF; the generator must still synthesize the
  descriptor, the row relation, and the "assembly driver" that dispatches constraint ↦ lemma (the
  §7 metaprogramming friction, which the design already scopes as schedule risk, not feasibility).
* Two Dyck combinators are still SHAPING lemmas, not yet in this minimal library, and each is a
  strictly harder (but still generic) member to add:
    - the exactly-one-of-`n` `kindPartition`/`subPartition` case-split (a `2^n` `rcases` +
      `norm_num`), factorable into a `partition_of_booleans` lemma parametric in the selector list;
    - `occupied_of_sat` (the depth↔occupancy tooth: `eval_foldl_mul` + `prime_dvd_map_prod` +
      `symbol_of_cubic_dvd`), already MOSTLY externalized as top-level generic lemmas in
      `DyckStackRefine` — the residual is a grid-parametric wrapper.
  Neither is bespoke *felt* reasoning that fails to factor; both are more library entries. The
  experiment found no combinator that is irreducibly descriptor-specific.

**Resolution honesty.** This proves the ROW-level (SAT⇒per-row-SEM) layer assembles. It says nothing
about the two Layer-B parts the design flags as separately hard: the multi-row `decode` glue (open
by hand — you cannot generate a proof of a theorem with no stated form) and the `emitVmJson2` +
`#guard` wiring. FEASIBLE here means the §7 row-lemma-library gate is PASSED; it does not upgrade the
whole Layer-B act past its other named residuals.
-/

/-- Non-vacuity note: `toyDesc` is satisfiable (e.g. any trace whose every row has `A = 2` and all
other cells `0` satisfies all four constraints on every transition row), so
`toy_sat_imp_row_valid`'s hypothesis is inhabitable — the assembled bridge is not vacuously true.
A formal concrete witness is omitted only to respect the lane's build budget. -/
example : Toy.toyDesc.constraints.length = 4 := rfl

end Dregg2.Crypto.Arith.RowLibraryExperiment
