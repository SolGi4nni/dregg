/-
# Dregg2.Circuit.MapOpWideKeyCanonDischarge — `KeyCanon` DISCHARGED from the emitted lex-8
  block's own range machinery, at every weld site of the wide-MapOp-key epoch.

**This is Lean-authored AIR.** `MapOpWideKey.KeyCanon k := ∀ i : Fin 8, 0 ≤ k i ∧ k i < p` is
carried as a BARE HYPOTHESIS at four weld theorems (`absentBracket_of_lexBlocks`,
`absentBracket_realizable`, `MapOpWideKeyGate.absentGateW_of_lexBlocks`,
`MapOpWideKeyGate.aafiBracketW_of_lexBlocks`) because `LexCompare8Emit.lexLt8_refines` consumes
it — and nothing in Lean forced it. This module removes the assumption.

## What the emitted object actually range-checks (measured, not assumed)

`lex_lookup_tuples` (a `rfl`) reads the tooth set straight off `lexLt8Constraints`: the block's
ONLY ℤ-exact teeth are the three 27-bit lookups on columns **30 (`aLo`), 37 (`bLo`), 39
(`delta`)** — the WITNESS cells. **No key cell (0..15) is looked up at all.** Every other
constraint is a row GATE, and a gate says `body.eval ≡ 0 [ZMOD p]`, never an ℤ fact.

## The no-go, machine-checked (`lexBlock_invariant_under_p_shift`)

Because the key cells carry no lookup, adding `p` to any one of them preserves satisfaction of
the WHOLE block. So `KeyCanon` on the raw ℤ cells is **not derivable from any enlargement of the
gate set** — including the design's W3 "range-check sixteen cells per compare". A power-of-two
range table cannot express `[0, p)` either (`2^27 < p < 2^31`), so no lookup tooth over the
existing table family forces it. Canonicity of a raw cell is a MODEL artifact: in the deployed
prover every trace cell IS a BabyBear element, so it is free there and unforceable here.

## The discharge (what the emitted object DOES force)

What the block genuinely pins is the **canonical (residue) reading** of the keys, and it pins it
with NO hypothesis: `lexLt8_refines_canon` is the hypothesis-free `lexLt8_refines` —

    (∃ env, key cells = a, b ∧ lexBlockHolds lexTf env) ↔ toLex (canonKey a) < toLex (canonKey b)

with `canonKey k i := k i % p`, whose `KeyCanon` is a THEOREM (`canonKey_isCanon`). The proof is
a transport, not a re-derivation: gate bodies are polynomials (`EmittedExpr` is
var/const/add/mul), so satisfaction is invariant under cell-wise congruence mod `p` as long as
the LOOKED-UP columns are held fixed (`block_congr_general` — a general lemma about any
constraint list of that shape, discharged for this block by the `lex_shape` structural pin). The
canonical reading of the deciding limb is exactly what the `p`-boundary gate (`P·Q·lo = 0`, whose
load-bearingness `LexCompare8Emit.boundary_canary_top_refuses` already pins) makes unique.

Every weld site is then re-derived hypothesis-free at the canonical reading
(`*_canon`), and each ORIGINAL hypothesis-carrying statement comes back as a corollary of it
(`*_of_canon` — `canonKey k = k` under `KeyCanon k`), so nothing downstream loses a theorem.

## The load-bearing canary (the precedent's shape:
`ShieldedValueRangeDischarge.wraparound_mint_{accepted_by_base,refused_by_ranged}`)

`forgeKk` reads `p + 5` in lane 0 — residue 5, raw value above `p`. On the committed chain
`forgeChain = [0 → 6, 6 → p+5, p+5 → p+6]` (`ImtSorted`, and it PRESENTS `p+5`):

  * `forge_blocks_hold` — the emitted gadget ACCEPTS both bracket rows `(0, p+5)` and `(p+5, 6)`;
  * `forge_raw_bracket_false` — the second raw bracket is a LIE (`p+5 > 6`);
  * ⚑ `rawBracketClaim_false` — hence the `KeyCanon`-free RAW weld (`RawBracketClaim`, which is
    `absentBracket_of_lexBlocks` verbatim minus the three canonicity hypotheses) is FALSE: it
    "proves" the key `p+5` ABSENT from a chain that PRESENTS it — a non-membership forgery;
  * ⚑ `canon_weld_survives` — the DISCHARGED weld, on the SAME trace, is TRUE.

That pair is what makes this a discharge rather than a re-labelling.

## Floors

NONE added. The range/table content is STRUCTURAL (`rangeRows` is definitionally `[0, 2^27)`);
no crypto enters this file at all — not even `Poseidon2SpongeCR`, which the weld sites carry only
through their Merkle arguments. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.

## Byte safety

NEW file, additive. No descriptor, emit, golden or JSON byte is touched; `lexLt8Descriptor` and
its `LEX_LT8_GOLDEN` are read-only inputs. No `sorry`/`admit`/`native_decide`.
-/
import Dregg2.Circuit.MapOpWideKeyGate

namespace Dregg2.Circuit.MapOpWideKeyCanonDischarge

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (TraceFamily VmConstraint2 Lookup MapOpKind MAP_TREE_DEPTH)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.Emit.LexCompare8Emit (lexBlockHolds lexTf lexTf_range lexLt8Constraints
  lexLt8_sound lexLt8_complete lexLt8_refines LexCanon lexKeyA lexKeyB LEX_RANGE_TID)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key imtAbsent_excludes_digest8)
open Dregg2.Circuit.MapOpWideKey (KeyCanon MapOpW)
open Dregg2.Circuit.MapOpWideKeyGate (ReconcileGatesW wideEnc leafOfW)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute)

set_option autoImplicit false

/-! ## §1 — WHAT THE EMITTED BLOCK RANGE-CHECKS TODAY (read off the object, by `rfl`). -/

/-- The lookup tuples of a constraint list, in order — the object's ℤ-exact teeth. -/
def lookupTuples : List VmConstraint2 → List (List EmittedExpr)
  | [] => []
  | .lookup l :: rest => l.tuple :: lookupTuples rest
  | _ :: rest => lookupTuples rest

/-- **★ THE MEASUREMENT.** The emitted lex-8 block's ONLY ℤ-exact teeth are three single-column
27-bit lookups, on the WITNESS columns `aLo = 30`, `bLo = 37`, `delta = 39`. Not one of the 16
KEY cells (`0..15`) is range-checked — which is exactly why `KeyCanon` is unforced. A `rfl` on
the deployed constraint list, not a reading of the prose. -/
theorem lex_lookup_tuples :
    lookupTuples lexLt8Constraints
      = [[EmittedExpr.var 30], [EmittedExpr.var 37], [EmittedExpr.var 39]] := rfl

/-! ## §2 — The canonical (residue) reading of a key, and its `KeyCanon`. -/

/-- The canonical representative of a felt cell: the residue the deployed BabyBear trace would
have carried in that column. -/
def canonFelt (x : ℤ) : ℤ := x % 2013265921

/-- The canonical reading of an 8-felt key group. -/
def canonKey (k : Fin 8 → ℤ) : Fin 8 → ℤ := fun i => canonFelt (k i)

theorem canonFelt_nonneg (x : ℤ) : 0 ≤ canonFelt x := Int.emod_nonneg x (by norm_num)

theorem canonFelt_lt (x : ℤ) : canonFelt x < 2013265921 := Int.emod_lt_of_pos x (by norm_num)

/-- The canonical reading is congruent to the raw cell — the only fact a GATE can see. -/
theorem canonFelt_modEq (x : ℤ) : canonFelt x ≡ x [ZMOD 2013265921] := by
  show (x % 2013265921) % 2013265921 = x % 2013265921
  exact Int.emod_emod_of_dvd x dvd_rfl

theorem canonFelt_id {x : ℤ} (h0 : 0 ≤ x) (h1 : x < 2013265921) : canonFelt x = x :=
  Int.emod_eq_of_lt h0 h1

/-- **`KeyCanon` of the canonical reading is a THEOREM** — the hypothesis every weld site carried
is FREE once the key is read the way a field element is read. -/
theorem canonKey_isCanon (k : Fin 8 → ℤ) : KeyCanon (canonKey k) :=
  fun _ => ⟨canonFelt_nonneg _, canonFelt_lt _⟩

/-- …and on a canonical key the reading is the IDENTITY, so the discharged statements SUBSUME the
hypothesis-carrying ones. -/
theorem canonKey_id {k : Fin 8 → ℤ} (h : KeyCanon k) : canonKey k = k :=
  funext fun i => canonFelt_id (h i).1 (h i).2

theorem canonKey_idem (k : Fin 8 → ℤ) : canonKey (canonKey k) = canonKey k :=
  canonKey_id (canonKey_isCanon k)

/-! ## §3 — The transport: gates are polynomials, so satisfaction is congruence-blind off the
looked-up columns. -/

/-- Polynomial evaluation is congruence-blind: `EmittedExpr` is var/const/add/mul, so cell-wise
congruent assignments give congruent values. This is the whole reason a GATE cannot see a raw
ℤ cell — only its residue. -/
theorem eval_congr (e : EmittedExpr) {a b : Assignment}
    (h : ∀ c, a c ≡ b c [ZMOD 2013265921]) : e.eval a ≡ e.eval b [ZMOD 2013265921] := by
  induction e with
  | var v => exact h v
  | const c => exact Int.ModEq.refl _
  | add e₁ e₂ ih₁ ih₂ =>
      show e₁.eval a + e₂.eval a ≡ e₁.eval b + e₂.eval b [ZMOD 2013265921]
      exact Int.ModEq.add ih₁ ih₂
  | mul e₁ e₂ ih₁ ih₂ =>
      show e₁.eval a * e₂.eval a ≡ e₁.eval b * e₂.eval b [ZMOD 2013265921]
      exact Int.ModEq.mul ih₁ ih₂

/-- The shape a constraint must have to be transportable across a congruence that MOVES the
columns in `S`: either a row gate (mod-`p`, congruence-blind), or a single-column lookup on a
column OUTSIDE `S` (ℤ-exact, so it must be held fixed). -/
def GateOrLookupOutside (S : Nat → Prop) (c : VmConstraint2) : Prop :=
  (∃ body : EmittedExpr, c = .base (.gate body))
    ∨ (∃ (tid : Dregg2.Circuit.DescriptorIR2.TableId) (k : Nat),
        c = .lookup ⟨tid, [.var k]⟩ ∧ ¬ S k)

/-- **The general transport.** For a constraint list of that shape, row satisfaction survives any
cell-wise congruent re-reading of the row that FIXES every looked-up column. (Stated for a
non-boundary row — the gadget's own denotation.) -/
theorem block_congr_general (S : Nat → Prop) (L : List VmConstraint2) (tf : TraceFamily)
    (env env' : VmRowEnv)
    (hcong : ∀ c : Nat, env'.loc c ≡ env.loc c [ZMOD 2013265921])
    (hfix : ∀ k : Nat, ¬ S k → env'.loc k = env.loc k)
    (hL : ∀ c ∈ L, GateOrLookupOutside S c)
    (h : ∀ c ∈ L, c.holdsAt (fun _ => 0) tf env false false) :
    ∀ c ∈ L, c.holdsAt (fun _ => 0) tf env' false false := by
  intro c hc
  rcases hL c hc with ⟨body, rfl⟩ | ⟨tid, k, rfl, hk⟩
  · have hg : body.eval env.loc ≡ 0 [ZMOD 2013265921] := h _ hc
    show body.eval env'.loc ≡ 0 [ZMOD 2013265921]
    exact (eval_congr body hcong).trans hg
  · have hl : [env.loc k] ∈ tf tid := h _ hc
    show [env'.loc k] ∈ tf tid
    rw [hfix k hk]
    exact hl

/-- **The structural pin the transport needs**: every constraint of the emitted lex-8 block is a
row gate or a lookup on a column `≥ 16` — i.e. no KEY cell is ever looked up. (The machine-checked
form of §1's measurement, in the shape `block_congr_general` consumes.) -/
theorem lex_shape : ∀ c ∈ lexLt8Constraints, GateOrLookupOutside (· < 16) c := by
  intro c hc
  fin_cases hc <;>
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨_, _, rfl, by norm_num⟩

/-- **The block-level transport**: a satisfying row stays satisfying under any congruent
re-reading of the 16 KEY cells. -/
theorem lexBlock_congr (env env' : VmRowEnv)
    (hcong : ∀ c : Nat, env'.loc c ≡ env.loc c [ZMOD 2013265921])
    (hfix : ∀ k : Nat, 16 ≤ k → env'.loc k = env.loc k)
    (h : lexBlockHolds lexTf env) : lexBlockHolds lexTf env' :=
  block_congr_general (· < 16) lexLt8Constraints lexTf env env' hcong
    (fun k hk => hfix k (Nat.le_of_not_lt hk)) lex_shape h

/-! ### §3b — THE NO-GO: no gate set can force `KeyCanon` on a raw ℤ cell. -/

/-- The row with `p` added to one key cell (a NON-canonical re-reading of that column). -/
def pShift (j : Nat) (env : VmRowEnv) : VmRowEnv :=
  ⟨fun c => if c = j then env.loc c + 2013265921 else env.loc c, env.nxt, env.pub⟩

/-- **★ THE GENERAL NO-GO.** For ANY constraint list — any enlargement whatever of the gate set —
whose lookups avoid column `j`, satisfaction is invariant under adding `p` to column `j`. A gate
is a mod-`p` fact and cannot see a raw ℤ cell; only a LOOKUP ON THAT CELL can, and no
power-of-two range table has content `[0, p)` (`2^27 < p < 2^31`). This is the general form of the
refutation: `KeyCanon` is not reachable by authoring more teeth of the gate kind. -/
theorem gate_teeth_cannot_force_canonicity (L : List VmConstraint2) (tf : TraceFamily) (j : Nat)
    (hL : ∀ c ∈ L, GateOrLookupOutside (· = j) c) (env : VmRowEnv)
    (h : ∀ c ∈ L, c.holdsAt (fun _ => 0) tf env false false) :
    ∀ c ∈ L, c.holdsAt (fun _ => 0) tf (pShift j env) false false := by
  refine block_congr_general (· = j) L tf env (pShift j env) ?_ ?_ hL h
  · intro c
    show (if c = j then env.loc c + 2013265921 else env.loc c) ≡ env.loc c [ZMOD 2013265921]
    by_cases hcj : c = j
    · rw [if_pos hcj]
      exact (Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩)
    · rw [if_neg hcj]
  · intro k hk
    show (if k = j then env.loc k + 2013265921 else env.loc k) = env.loc k
    rw [if_neg hk]

/-- The emitted block's shape at the single-column view: for a KEY column `j < 16`, every
constraint is a gate or a lookup on some OTHER column. -/
theorem lex_shape_at (j : Nat) (hj : j < 16) :
    ∀ c ∈ lexLt8Constraints, GateOrLookupOutside (· = j) c := by
  intro c hc
  rcases lex_shape c hc with hg | ⟨tid, k, hk, hk16⟩
  · exact Or.inl hg
  · refine Or.inr ⟨tid, k, hk, ?_⟩
    have hk' : 16 ≤ k := Nat.le_of_not_lt hk16
    intro hkj
    omega

/-- **★ THE NO-GO AT THE EMITTED BLOCK.** Adding `p` to ANY key cell preserves satisfaction of the
WHOLE emitted lex-8 block. So `KeyCanon` on the raw ℤ cells is not a consequence of the emitted
object, and (by the general form above) cannot be made one by adding gate teeth. This is the
refutation of the design's W3 note that "the emit must range-check sixteen cells per compare":
sixteen more range teeth would not discharge the hypothesis; reading the key canonically does. -/
theorem lexBlock_invariant_under_p_shift (j : Nat) (hj : j < 16) (env : VmRowEnv)
    (h : lexBlockHolds lexTf env) : lexBlockHolds lexTf (pShift j env) :=
  gate_teeth_cannot_force_canonicity lexLt8Constraints lexTf j (lex_shape_at j hj) env h

/-! ## §4 — ⚑ THE DISCHARGE: the emitted block's refinement, with NO canonicity hypothesis. -/

/-- The canonical re-reading of a row's 16 key cells. -/
def canonEnv (env : VmRowEnv) : VmRowEnv :=
  ⟨fun c => if c < 16 then canonFelt (env.loc c) else env.loc c, env.nxt, env.pub⟩

private theorem canonEnv_cong (env : VmRowEnv) :
    ∀ c : Nat, (canonEnv env).loc c ≡ env.loc c [ZMOD 2013265921] := by
  intro c
  show (if c < 16 then canonFelt (env.loc c) else env.loc c) ≡ env.loc c [ZMOD 2013265921]
  by_cases hc : c < 16
  · rw [if_pos hc]; exact canonFelt_modEq _
  · rw [if_neg hc]

private theorem canonEnv_fix (env : VmRowEnv) :
    ∀ k : Nat, 16 ≤ k → (canonEnv env).loc k = env.loc k := by
  intro k hk
  have hne : ¬ (k < 16) := by omega
  show (if k < 16 then canonFelt (env.loc k) else env.loc k) = env.loc k
  rw [if_neg hne]

private theorem canonEnv_canon (env : VmRowEnv) : LexCanon (canonEnv env) := by
  intro k hk
  show 0 ≤ (if k < 16 then canonFelt (env.loc k) else env.loc k)
    ∧ (if k < 16 then canonFelt (env.loc k) else env.loc k) < 2013265921
  rw [if_pos hk]
  exact ⟨canonFelt_nonneg _, canonFelt_lt _⟩

private theorem canonEnv_keyA (env : VmRowEnv) : lexKeyA (canonEnv env) = canonKey (lexKeyA env) := by
  funext i
  show (if i.val < 16 then canonFelt (env.loc i.val) else env.loc i.val) = canonFelt (env.loc i.val)
  rw [if_pos (by omega : i.val < 16)]

private theorem canonEnv_keyB (env : VmRowEnv) : lexKeyB (canonEnv env) = canonKey (lexKeyB env) := by
  funext i
  show (if 8 + i.val < 16 then canonFelt (env.loc (8 + i.val)) else env.loc (8 + i.val))
    = canonFelt (env.loc (8 + i.val))
  rw [if_pos (by omega : 8 + i.val < 16)]

/-- **⚑ SOUNDNESS, HYPOTHESIS-FREE.** A row satisfying the emitted block carries keys whose
CANONICAL readings are genuinely lex-ordered — for EVERY trace, canonical or not. The bound comes
from the emitted object: the three 27-bit lookups plus the `p`-boundary gate pin the deciding
limb's residue into `[0, p)`, and the prefix gates pin the residues above it equal. -/
theorem lexLt8_sound_canon (env : VmRowEnv) (h : lexBlockHolds lexTf env) :
    toLex (canonKey (lexKeyA env)) < toLex (canonKey (lexKeyB env)) := by
  have hb : lexBlockHolds lexTf (canonEnv env) :=
    lexBlock_congr env (canonEnv env) (canonEnv_cong env) (canonEnv_fix env) h
  have hlt := lexLt8_sound lexTf lexTf_range (canonEnv env) (canonEnv_canon env) hb
  rwa [canonEnv_keyA, canonEnv_keyB] at hlt

/-- The key-cell re-reading completeness uses: columns `0..7` carry the RAW `a`, columns `8..15`
the RAW `b`, and every witness column is the canonical witness's own cell. -/
private def rawKeyLoc (a b : Fin 8 → ℤ) (base : Assignment) : Assignment := fun c =>
  if c < 8 then a ⟨c % 8, by omega⟩
  else if c < 16 then b ⟨c % 8, by omega⟩
  else base c

private theorem rawKeyLoc_lo (a b : Fin 8 → ℤ) (base : Assignment) (i : Fin 8) :
    rawKeyLoc a b base i.val = a i := by
  show (if i.val < 8 then a ⟨i.val % 8, by omega⟩
    else if i.val < 16 then b ⟨i.val % 8, by omega⟩ else base i.val) = a i
  rw [if_pos i.isLt]
  congr 1
  apply Fin.ext
  show i.val % 8 = i.val
  omega

private theorem rawKeyLoc_hi (a b : Fin 8 → ℤ) (base : Assignment) (i : Fin 8) :
    rawKeyLoc a b base (8 + i.val) = b i := by
  have h1 : ¬ (8 + i.val < 8) := by omega
  have h2 : 8 + i.val < 16 := by omega
  show (if 8 + i.val < 8 then a ⟨(8 + i.val) % 8, by omega⟩
    else if 8 + i.val < 16 then b ⟨(8 + i.val) % 8, by omega⟩ else base (8 + i.val)) = b i
  rw [if_neg h1, if_pos h2]
  congr 1
  apply Fin.ext
  show (8 + i.val) % 8 = i.val
  omega

private theorem rawKeyLoc_out (a b : Fin 8 → ℤ) (base : Assignment) (c : Nat) (hc : 16 ≤ c) :
    rawKeyLoc a b base c = base c := by
  have h1 : ¬ (c < 8) := by omega
  have h2 : ¬ (c < 16) := by omega
  show (if c < 8 then a ⟨c % 8, by omega⟩
    else if c < 16 then b ⟨c % 8, by omega⟩ else base c) = base c
  rw [if_neg h1, if_neg h2]

/-- The completeness twin, hypothesis-free: a canonically-ordered pair admits a satisfying row
whose key columns carry the RAW cells (the witness is the canonical one, re-read). -/
theorem lexLt8_complete_canon (a b : Fin 8 → ℤ)
    (hlt : toLex (canonKey a) < toLex (canonKey b)) :
    ∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = a i)
      ∧ (∀ i : Fin 8, env.loc (8 + i.val) = b i) ∧ lexBlockHolds lexTf env := by
  obtain ⟨env, hka, hkb, hblk⟩ :=
    lexLt8_complete (canonKey a) (canonKey b) (canonKey_isCanon a) (canonKey_isCanon b) hlt
  refine ⟨⟨rawKeyLoc a b env.loc, env.nxt, env.pub⟩, rawKeyLoc_lo a b env.loc,
    rawKeyLoc_hi a b env.loc, ?_⟩
  refine lexBlock_congr env _ (fun c => ?_) (fun k hk => ?_) hblk
  · show rawKeyLoc a b env.loc c ≡ env.loc c [ZMOD 2013265921]
    rcases Nat.lt_or_ge c 8 with h8 | h8
    · have hi : (⟨c, h8⟩ : Fin 8).val = c := rfl
      rw [← hi, rawKeyLoc_lo a b env.loc ⟨c, h8⟩, hka ⟨c, h8⟩]
      exact (canonFelt_modEq (a ⟨c, h8⟩)).symm
    · rcases Nat.lt_or_ge c 16 with h16 | h16
      · have hlt8 : c - 8 < 8 := by omega
        have hi : 8 + (⟨c - 8, hlt8⟩ : Fin 8).val = c := by show 8 + (c - 8) = c; omega
        rw [← hi, rawKeyLoc_hi a b env.loc ⟨c - 8, hlt8⟩, hkb ⟨c - 8, hlt8⟩]
        exact (canonFelt_modEq (b ⟨c - 8, hlt8⟩)).symm
      · rw [rawKeyLoc_out a b env.loc c h16]
  · show rawKeyLoc a b env.loc k = env.loc k
    exact rawKeyLoc_out a b env.loc k hk

/-- **⚑⚑ THE DISCHARGE — `lexLt8_refines` with the canonicity hypotheses GONE.** The emitted
block is satisfiable with key columns `a`, `b` IFF their CANONICAL readings are lex-ordered. No
`KeyCanon` on either side: the statement is now about every trace, and what it asserts is exactly
what the emitted object forces. -/
theorem lexLt8_refines_canon (a b : Fin 8 → ℤ) :
    (∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = a i)
        ∧ (∀ i : Fin 8, env.loc (8 + i.val) = b i)
        ∧ lexBlockHolds lexTf env)
      ↔ toLex (canonKey a) < toLex (canonKey b) := by
  constructor
  · rintro ⟨env, hka, hkb, hblk⟩
    have hlt := lexLt8_sound_canon env hblk
    have hA : lexKeyA env = a := funext fun i => hka i
    have hB : lexKeyB env = b := funext fun i => hkb i
    rwa [hA, hB] at hlt
  · exact lexLt8_complete_canon a b

/-- The ORIGINAL `lexLt8_refines` is a COROLLARY: on canonical keys the canonical reading is the
identity. Nothing downstream loses a theorem by the discharge. -/
theorem lexLt8_refines_of_canon (a b : Fin 8 → ℤ) (ha : KeyCanon a) (hb : KeyCanon b) :
    (∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = a i)
        ∧ (∀ i : Fin 8, env.loc (8 + i.val) = b i)
        ∧ lexBlockHolds lexTf env)
      ↔ toLex a < toLex b := by
  rw [lexLt8_refines_canon a b, canonKey_id ha, canonKey_id hb]

/-! ## §5 — The four weld sites, RE-DERIVED with no bare hypothesis.

Each `*_canon` below is the corresponding weld theorem with the three `KeyCanon` hypotheses
DELETED and the key groups read canonically; each `*_of_canon` recovers the original statement
from it. The canonical reading is not a weakening: the committed IMT leaf keys ARE field
elements, so `canonKey` is the identity on them (`canonKey_id`), and the queried key is the one
the AIR compares. -/

/-- **⚑ THE WELD (soundness), DISCHARGED** — `MapOpWideKey.absentBracket_of_lexBlocks` with no
canonicity assumption. Two satisfied `lexLt8` blocks plus a committed low leaf FORCE the queried
key (canonically read) absent from the whole committed spine. -/
theorem absentBracket_of_lexBlocks_canon
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (val : ℤ)
    (hmem : (⟨toLex (canonKey lowAddr), val, toLex (canonKey lowNext)⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    (toLex (canonKey kk) : Digest8Key) ∉ imtAddrs c := by
  have hlo : (toLex (canonKey lowAddr) : Digest8Key) < toLex (canonKey kk) :=
    (lexLt8_refines_canon lowAddr kk).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩
  have hhi : (toLex (canonKey kk) : Digest8Key) < toLex (canonKey lowNext) :=
    (lexLt8_refines_canon kk lowNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩
  exact imtAbsent_excludes_digest8 hs ⟨_, hmem, hlo, hhi⟩

/-- The hypothesis-carrying original, recovered. -/
theorem absentBracket_of_lexBlocks_of_canon
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hcLow : KeyCanon lowAddr) (hcK : KeyCanon kk) (hcNext : KeyCanon lowNext)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (val : ℤ)
    (hmem : (⟨toLex lowAddr, val, toLex lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    (toLex kk : Digest8Key) ∉ imtAddrs c := by
  have h := absentBracket_of_lexBlocks_canon envLo envHi lowAddr kk lowNext
    hLoA hLoB hLoBlk hHiA hHiB hHiBlk c hs val (by rwa [canonKey_id hcLow, canonKey_id hcNext])
  rwa [canonKey_id hcK] at h

/-- **⚑ THE WELD (completeness / anti-DoS), DISCHARGED** — an honest bracket at the CANONICAL
reading admits both `lexLt8` witness rows, with the key columns carrying the raw cells. -/
theorem absentBracket_realizable_canon
    (lowAddr kk lowNext : Fin 8 → ℤ)
    (hlo : (toLex (canonKey lowAddr) : Digest8Key) < toLex (canonKey kk))
    (hhi : (toLex (canonKey kk) : Digest8Key) < toLex (canonKey lowNext)) :
    (∃ envLo : VmRowEnv, (∀ i : Fin 8, envLo.loc i.val = lowAddr i)
        ∧ (∀ i : Fin 8, envLo.loc (8 + i.val) = kk i) ∧ lexBlockHolds lexTf envLo)
    ∧ (∃ envHi : VmRowEnv, (∀ i : Fin 8, envHi.loc i.val = kk i)
        ∧ (∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i) ∧ lexBlockHolds lexTf envHi) :=
  ⟨(lexLt8_refines_canon lowAddr kk).mpr hlo, (lexLt8_refines_canon kk lowNext).mpr hhi⟩

/-- **⚑ THE GATE SITE, DISCHARGED** — `MapOpWideKeyGate.absentGateW_of_lexBlocks` with no
canonicity assumption: two satisfied blocks plus two adjacent committed paths ARE a widened
`.absent` gate at the canonical key. -/
theorem absentGateW_of_lexBlocks_canon (hash : List ℤ → ℤ) (dep : Nat) (r v : ℤ)
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (stepsLo stepsHi : List (Bool × ℤ)) (vlo vhi : ℤ)
    (hlLo : stepsLo.length = dep) (hlHi : stepsHi.length = dep)
    (hadj : pathPos stepsHi = pathPos stepsLo + 1)
    (hpLo : pathRecompute hash (leafOfW hash wideEnc (toLex (canonKey lowAddr), vlo)) stepsLo = r)
    (hpHi : pathRecompute hash (leafOfW hash wideEnc (toLex (canonKey lowNext), vhi)) stepsHi = r) :
    ReconcileGatesW hash wideEnc dep r (toLex (canonKey kk)) v r MapOpKind.absent :=
  ⟨⟨stepsLo, stepsHi, toLex (canonKey lowAddr), vlo, toLex (canonKey lowNext), vhi, hlLo, hlHi,
    hadj, hpLo, hpHi,
    (lexLt8_refines_canon lowAddr kk).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩,
    (lexLt8_refines_canon kk lowNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩, rfl⟩

/-- **⚑ THE AAFI/`.absent` ROW, DISCHARGED** — `MapOpWideKeyGate.aafiBracketW_of_lexBlocks` with
no canonicity assumption: the emitted blocks give BOTH the widened AAFI gate's pointer bracket and
the chain-level exclusion, at the canonical key. -/
theorem aafiBracketW_of_lexBlocks_canon
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (val : ℤ)
    (hmem : (⟨toLex (canonKey lowAddr), val, toLex (canonKey lowNext)⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ((toLex (canonKey lowAddr) : Digest8Key) < toLex (canonKey kk)
        ∧ (toLex (canonKey kk) : Digest8Key) < toLex (canonKey lowNext))
      ∧ (toLex (canonKey kk) : Digest8Key) ∉ imtAddrs c :=
  ⟨⟨(lexLt8_refines_canon lowAddr kk).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩,
    (lexLt8_refines_canon kk lowNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩,
   absentBracket_of_lexBlocks_canon envLo envHi lowAddr kk lowNext
     hLoA hLoB hLoBlk hHiA hHiB hHiBlk c hs val hmem⟩

/-! ### §5b — the reading at the IR node: what W1–W4 must WIRE (a wiring obligation, not a
range-tooth obligation). -/

/-- **`keyAtCanon`** — the widened map-op row's key at the CANONICAL reading: the key the
discharged weld speaks in. `MapOpW.keyAt` is the RAW reading of the same columns. -/
def keyAtCanon (m : MapOpW) (a : Assignment) : Digest8Key :=
  toLex (canonKey (fun i : Fin 8 => (m.key i).eval a))

/-- On a canonically-read key group the two readings COINCIDE — the discharge costs the deployed
row nothing: it is the same key, now stated without an unforced hypothesis. -/
theorem keyAtCanon_eq_keyAt (m : MapOpW) (a : Assignment)
    (h : KeyCanon (fun i : Fin 8 => (m.key i).eval a)) : keyAtCanon m a = m.keyAt a := by
  show toLex (canonKey (fun i : Fin 8 => (m.key i).eval a))
    = toLex (fun i : Fin 8 => (m.key i).eval a)
  rw [canonKey_id h]

/-- **The W3 obligation, stated exactly.** If the emit wires the compare block's a-side columns to
the row's key group, the discharged weld's queried key IS the row's canonical key. That wiring —
same columns into the block and into the map-op key group / arity-17 leaf absorb — is ALL the
emit must add for the discharge to bite; no per-cell range teeth are needed (and none would
help: `gate_teeth_cannot_force_canonicity`). -/
theorem keyAtCanon_of_block (m : MapOpW) (a : Assignment) (env : VmRowEnv) (kk : Fin 8 → ℤ)
    (hcol : ∀ i : Fin 8, env.loc i.val = kk i)
    (hwire : ∀ i : Fin 8, (m.key i).eval a = env.loc i.val) :
    keyAtCanon m a = toLex (canonKey kk) := by
  have hk : (fun i : Fin 8 => (m.key i).eval a) = kk := funext fun i => by rw [hwire i, hcol i]
  show toLex (canonKey (fun i : Fin 8 => (m.key i).eval a)) = toLex (canonKey kk)
  rw [hk]

/-! ## §6 — ⚑ THE LOAD-BEARING CANARY: the `KeyCanon`-free RAW weld is FALSE, the discharged one
holds — on the SAME accepted trace.

`p = 2013265921`. `forgeKk` reads `p + 5` in lane 0: residue 5, raw value ABOVE the modulus. The
gadget accepts both bracket rows because it can only see residues; the RAW bracket
`p+5 < 6` it appears to certify is a lie, and the chain PRESENTS `p+5`. -/

/-- The all-zero key (canonical). -/
def forgeLow : Fin 8 → ℤ := fun _ => 0
/-- ⚑ The NON-canonical queried key: lane 0 carries `p + 5` (residue 5). -/
def forgeKk : Fin 8 → ℤ := fun i => if i.val = 0 then 2013265926 else 0
/-- The low leaf's pointer: lane 0 carries `6` (canonical). -/
def forgeNext : Fin 8 → ℤ := fun i => if i.val = 0 then 6 else 0
/-- The chain's top sentinel: lane 0 carries `p + 6`, above the forged key in the RAW order. -/
def forgeTop : Fin 8 → ℤ := fun i => if i.val = 0 then 2013265927 else 0

private theorem lex_lt_at0 {x y : Fin 8 → ℤ} (h : x 0 < y 0) : (toLex x : Digest8Key) < toLex y :=
  ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩

theorem forgeLow_canon : canonKey forgeLow = forgeLow :=
  canonKey_id (by show ∀ i : Fin 8, 0 ≤ forgeLow i ∧ forgeLow i < 2013265921; decide)

theorem forgeNext_canon : canonKey forgeNext = forgeNext :=
  canonKey_id (by show ∀ i : Fin 8, 0 ≤ forgeNext i ∧ forgeNext i < 2013265921; decide)

/-- The forged key's CANONICAL reading: lane 0 becomes `5`. -/
theorem forgeKk_canon0 : canonKey forgeKk 0 = 5 := by decide

/-- The committed chain `0 → 6 → p+5 → p+6`. It PRESENTS the raw key `p+5`. -/
def forgeChain : List (ImtLeaf Digest8Key ℤ) :=
  [ ⟨toLex forgeLow, 1, toLex forgeNext⟩
  , ⟨toLex forgeNext, 1, toLex forgeKk⟩
  , ⟨toLex forgeKk, 1, toLex forgeTop⟩ ]

theorem forgeChain_sorted : ImtSorted forgeChain := by
  refine ⟨lex_lt_at0 (by decide), rfl, lex_lt_at0 (by decide), rfl, lex_lt_at0 (by decide)⟩

/-- The low leaf the bracket opens against is committed (and is already canonical). -/
theorem forgeLow_leaf_mem :
    (⟨toLex forgeLow, 1, toLex forgeNext⟩ : ImtLeaf Digest8Key ℤ) ∈ forgeChain := by
  simp [forgeChain]

/-- **The chain PRESENTS the forged key** — raw `p + 5` is a committed address. -/
theorem forgeKk_present : (toLex forgeKk : Digest8Key) ∈ imtAddrs forgeChain := by
  simp [forgeChain, imtAddrs]

/-- **The emitted gadget ACCEPTS both bracket rows** — the low bracket `(0, p+5)` and the high
bracket `(p+5, 6)`, with the key columns carrying the RAW cells. It sees `0 < 5` and `5 < 6`. -/
theorem forge_blocks_hold :
    (∃ envLo : VmRowEnv, (∀ i : Fin 8, envLo.loc i.val = forgeLow i)
        ∧ (∀ i : Fin 8, envLo.loc (8 + i.val) = forgeKk i) ∧ lexBlockHolds lexTf envLo)
    ∧ (∃ envHi : VmRowEnv, (∀ i : Fin 8, envHi.loc i.val = forgeKk i)
        ∧ (∀ i : Fin 8, envHi.loc (8 + i.val) = forgeNext i) ∧ lexBlockHolds lexTf envHi) :=
  absentBracket_realizable_canon forgeLow forgeKk forgeNext
    (lex_lt_at0 (by decide)) (lex_lt_at0 (by decide))

/-- **…and the high bracket it appears to certify is a LIE in the RAW order** (`p + 5 > 6`). -/
theorem forge_raw_bracket_false : ¬ ((toLex forgeKk : Digest8Key) < toLex forgeNext) :=
  fun h => lt_asymm h (lex_lt_at0 (by decide))

/-- **`RawBracketClaim`** — `MapOpWideKey.absentBracket_of_lexBlocks` VERBATIM with its three
`KeyCanon` hypotheses deleted and the key read RAW: the statement the epoch would have if the
bare hypothesis were simply dropped. -/
def RawBracketClaim : Prop :=
  ∀ (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ),
    (∀ i : Fin 8, envLo.loc i.val = lowAddr i) →
    (∀ i : Fin 8, envLo.loc (8 + i.val) = kk i) →
    lexBlockHolds lexTf envLo →
    (∀ i : Fin 8, envHi.loc i.val = kk i) →
    (∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i) →
    lexBlockHolds lexTf envHi →
    ∀ (c : List (ImtLeaf Digest8Key ℤ)), ImtSorted c → ∀ val : ℤ,
      (⟨toLex lowAddr, val, toLex lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c →
      (toLex kk : Digest8Key) ∉ imtAddrs c

/-- **⚑⚑ THE CANARY, ACCEPT SIDE.** The un-hypothesized RAW weld is FALSE: on the accepted trace
above it "proves" the key `p + 5` ABSENT from a chain that PRESENTS it — a non-membership
forgery. `KeyCanon` was load-bearing, and nothing in the emitted object was forcing it. -/
theorem rawBracketClaim_false : ¬ RawBracketClaim := by
  intro H
  obtain ⟨⟨envLo, hLoA, hLoB, hLoBlk⟩, ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩ := forge_blocks_hold
  exact H envLo envHi forgeLow forgeKk forgeNext hLoA hLoB hLoBlk hHiA hHiB hHiBlk
    forgeChain forgeChain_sorted 1 forgeLow_leaf_mem forgeKk_present

/-- **⚑⚑ THE CANARY, REFUSE SIDE.** The DISCHARGED weld, on the SAME trace, is TRUE: it excludes
the key the emitted block actually compared — the canonical reading `5` — which the chain does
NOT present. The discharge is not decorative: it is what stands between the accepted row and the
forged absence. -/
theorem canon_weld_survives : (toLex (canonKey forgeKk) : Digest8Key) ∉ imtAddrs forgeChain := by
  obtain ⟨⟨envLo, hLoA, hLoB, hLoBlk⟩, ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩ := forge_blocks_hold
  refine absentBracket_of_lexBlocks_canon envLo envHi forgeLow forgeKk forgeNext
    hLoA hLoB hLoBlk hHiA hHiB hHiBlk forgeChain forgeChain_sorted 1 ?_
  rw [forgeLow_canon, forgeNext_canon]
  exact forgeLow_leaf_mem

/-- The canary is non-vacuous in the discriminating direction too: the raw and canonical readings
of the queried key are genuinely DIFFERENT keys. -/
theorem forge_readings_differ : (toLex (canonKey forgeKk) : Digest8Key) ≠ toLex forgeKk := by
  intro h
  have h0 : canonKey forgeKk 0 = forgeKk 0 := congrFun h 0
  rw [forgeKk_canon0] at h0
  exact absurd h0 (by decide)

/-! ## §7 — axiom hygiene. -/

#assert_axioms lex_lookup_tuples
#assert_axioms canonKey_isCanon
#assert_axioms canonKey_id
#assert_axioms eval_congr
#assert_axioms block_congr_general
#assert_axioms lex_shape
#assert_axioms lexBlock_congr
#assert_axioms gate_teeth_cannot_force_canonicity
#assert_axioms lex_shape_at
#assert_axioms lexBlock_invariant_under_p_shift
#assert_axioms lexLt8_sound_canon
#assert_axioms lexLt8_complete_canon
#assert_axioms lexLt8_refines_canon
#assert_axioms lexLt8_refines_of_canon
#assert_axioms absentBracket_of_lexBlocks_canon
#assert_axioms absentBracket_of_lexBlocks_of_canon
#assert_axioms absentBracket_realizable_canon
#assert_axioms absentGateW_of_lexBlocks_canon
#assert_axioms aafiBracketW_of_lexBlocks_canon
#assert_axioms keyAtCanon_eq_keyAt
#assert_axioms keyAtCanon_of_block
#assert_axioms forgeChain_sorted
#assert_axioms forge_blocks_hold
#assert_axioms forge_raw_bracket_false
#assert_axioms rawBracketClaim_false
#assert_axioms canon_weld_survives
#assert_axioms forge_readings_differ

end Dregg2.Circuit.MapOpWideKeyCanonDischarge
