# Lean corpus quality review — arklib-kzg-vacuity

The sufficient-test discipline we spent this workstream applying to ArkLib, turned
inward on our own mechanization. Every file was read in full (semantic review, not a
lint) and rebuilt against real ArkLib @ `d72f8392` (Lean v4.31.0, the repaired
`Binding.lean` for the reduction files). Every headline theorem was re-checked with
`#print axioms`.

**Global verdict: the corpus passes its own test.** All twelve `.lean` files build
`sorry`-free. Every trust-bearing theorem depends on exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`, no
`ofReduceBool`, no `Lean.ofReduceBool` anywhere. No headline theorem is vacuous, a
restated `≤ 1`, or true by a definitional dodge; each survives-attack / bound claim
quantifies over a richly-inhabited type, and the vacuity findings ship with canaries
that prove the experiment is not constantly `1`. Two genuine quality nits were found
and fixed (unused `Fact` hypotheses); one broken divergent duplicate was found and
removed.

`Classical.choice` in the closure is not a smell here — it is the *content*: the
findings' whole point is that `Exists.choose` (an unbounded, choice-definable extractor)
is a legal inhabitant of the unrestricted adversary type, so `Classical.choice` appearing
in `not_tSdhAssumption` et al. is the attack, mechanized.

---

## Per-file verdict

### `KzgVacuity.lean` — the headline finding — **A. Load-bearing.**
The t-SDH / ARSDH vacuity, mechanized against ArkLib's real `Groups.tSdhAssumption`,
`Groups.arsdhAssumption`, and the `KZG.binding` / `KZG.function_binding` consumers.

- **Sufficient test: PASSES, and self-applies it.** `not_tSdhAssumption` exhibits a
  concrete adversary (`tauExtractingAdversary`) winning with probability *exactly 1*
  (`tSdhExperiment_tauExtractingAdversary`), refuting the assumption for every
  `error < 1`. The `experiment_discriminates` / `tSdhExperiment_givingUpAdversary = 0`
  canaries prove the `= 1` is a fact about *this* adversary, not an artifact of the
  probability machinery — i.e. the file runs the sufficient test on itself.
- **No smuggled hypotheses.** `binding_hypotheses_unsatisfiable` *derives* `g₂ ≠ 1`
  from `binding`'s own pairing-nondegeneracy hypothesis (a bilinear pairing kills the
  identity); it does not assume it. The ARSDH branch's `hpD : D + 2 ≤ p` is exactly the
  `p ≥ n + 2` that `function_binding` already carries — honest, and named.
- Docstrings match statements (t-SDH and ARSDH each shown false-below-1 *and*
  trivial-at/above-1, i.e. "no content at any parameter" — which is exactly what the two
  theorems together prove).
- Note: the git build tree's copy (`KzgVacuityFable.lean`) is a *stale subset* — the docs
  version is the newer superset (adds the whole ARSDH section + the ≥1 regime). The docs
  file is canonical; verified fresh here.

### `RepairSurvives.lean` (top-level) — **A. Load-bearing. CANONICAL.**
The de-vacuation reduction survives the exact attack.

- `repair_survives_attack` is a genuine conjunction: (1) the trapdoor-extracting attack
  *still* refutes `tSdhAssumption` below 1, AND (2) the repaired reduction bound
  `KZG.CommitmentScheme.binding_reduces_to_tSdh` holds *unconditionally*
  (`bindingExperiment ≤ tSdhExperiment` of the explicit reduction). Part (2) never takes
  `tSdhAssumption` as a hypothesis, so the choice-adversary has nothing to inhabit — the
  point, proven, not asserted.
- No unused hypotheses: `tSdhError`/`herr` feed part (1); `hg₁` and `SampleableType G₁`
  feed part (2)'s reduction. The `local instance bindingOracleInterface` mirror is
  necessary (the library's instance is `local`) and its docstring explains exactly why.
- Byte-matches the build tree copy; `binding_reduces_to_tSdh` / `binding` themselves are
  axiom-clean in the repaired tree.

### `candidates/RepairSurvives.lean` — **BROKEN DUPLICATE. Removed (safe consolidation).**
Proof body is identical to the canonical top-level file; the only divergence is five extra
trailing `#print axioms` lines. One of them references
`KZG.CommitmentScheme.bindingCondExt_yields_tSdhCondition`, which **does not exist** in the
patched ArkLib (`grep -rln` across the whole tree: absent) — so the file **fails to
elaborate** (`error: Unknown constant …`). It is a strict content-duplicate of the working
canonical file, and broken. Removed via `git rm`; git history preserves it. If the two
valid extra receipts (`t_sdh_cond_of_two_valid_openings`, `binding_reduces_to_tSdh`) are
wanted, append them to the canonical top-level file — they elaborate cleanly there.

### `candidates/GgmCandidate.lean` — the static GGM core — **A. Load-bearing.**
Committed (static, q=0) generic adversary; Schwartz–Zippel `(D+1)/(p-1)` bound over the
*full* `GenericAdversary` type. Reused (not reproved) by `GgmAdaptive` and
`GgmRandomEncoding` as the root-event core.

- `ggm_tSdh_sound` genuinely quantifies over every committed `(c, f)` — including any
  `Classical.choice`-defined one. The header states plainly why the attack cannot be typed
  here (the adversary receives no group element, so there is no `∃ a, · = g^a` to invert).
- **Fixed:** `ggm_bound_lt_one` carried an unused `[Fact (Nat.Prime p)]` (the `<1` fact is
  pure arithmetic). Added `omit [Fact (Nat.Prime p)] in` — the idiom the sibling
  `GgmRandomEncoding.rand_encoding_bound_lt_one` already uses, so this is a
  consistency fix as much as a cleanup. Re-verified: builds warning-free, still
  `[propext, Classical.choice, Quot.sound]`.

### `candidates/GgmAdaptive.lean` — the crown jewel — **A. Load-bearing.**
The adaptive (Shoup / Boneh–Boyen) GGM bound: `q` oracle queries, bound
`(fuel·Δ + (D+1))/(p−1)`.

- **Sufficient test: PASSES.** The bound is not a restated `≤ 1` — it is genuinely
  parameterized and separately shown `< 1` at real parameters
  (`adaptive_bound_lt_one`). It quantifies over the full `Strat` type (any
  `List Bool → Move ⊕ output`). The crux — identical-until-bad (`runAux_congr_of_agree`) —
  is **proven by induction on fuel, not assumed**. `adaptive_generalizes_static` anchors
  non-vacuity: at `fuel = 0` the hypotheses discharge automatically and the bound *is* the
  static `(D+1)/(p-1)`, so the theorem is genuinely instantiable with satisfiable
  hypotheses.
- **Honest hypotheses, clearly stated** (not smuggled): `hdeg_out` (output handle degree
  ≤ D) and `hdeg_pairs` (queried-difference degree ≤ Δ) are the SRS degree invariant, in
  the *statement*, discharged structurally by `GgmDegreeInvariant` (see its residual note
  below). The win predicate guards `τ + c ≠ 0` so Lean's total `0⁻¹ = 0` cannot smuggle a
  spurious win — noted in the source.
- **Fixed:** `adaptive_bound_lt_one` had the same unused `[Fact (Nat.Prime p)]`; same
  `omit` fix, re-verified axiom-clean.
- Scope honesty: this is a **counting/set-level** bound (ℚ), which the header states
  outright ("no probability monad — same honest idiom as the static file"). The
  "SECURITY BOUND" phrasing reads at that resolution; the probability-monad step is a
  named residual carried in `GgmArkLibTransport`. No fix needed — the docstrings do not
  overclaim a probability reduction.

### `candidates/GgmDegreeInvariant.lean` — residual closer (degree) — **A−. Load-bearing.**
Makes the `hdeg_out` / `hdeg_pairs` hypotheses structural via `TableOp` / `PairedOp`
inductives and degree invariants proved by induction.

- Exemplary "prove the floor false" discipline: `flat_2D_bound_false` **proves the naive
  `2·D` flat-table bound FALSE** (nested products build `X⁴` at `D=1`), so the honest flat
  bound is exponential (`D·2^#mul`) and `2·D` is recovered only under the pairing
  discipline (`degree_invariant_paired`). This is us refusing to launder a false floor.
- **Named residual (honest, flagged):** the invariants are proved about `buildTable` /
  `buildPaired`, which *mirror* `GgmAdaptive.runAux`'s table growth but are separate
  definitions. The connection to the actual `symOutput` / `badPolys` is by inspection
  ("mirror", "structural home" — the docstrings say so), **not** a mechanized theorem.
  Contrast `GgmRandomEncoding`, which *does* mechanize the `runAux ↔ runTable` link. Not a
  bug or overclaim (the prose is honest), but it is the corpus's single most load-bearing
  seam and should be named as such in the paper. RECOMMEND (optional strengthening): prove
  the mirror faithful to `runAux` to literally discharge the hypotheses.
- Minor style: this file alone does `import Mathlib` (whole) where the rest use targeted
  imports. Harmless for a scratch file; RECOMMEND narrowing for consistency, not fixed
  (risk/verification cost outweighs benefit for a non-load-bearing property).

### `candidates/GgmRandomEncoding.lean` — residual closer (all-pairs) — **A. Load-bearing.**
Strengthens the per-query bad event to the random-encoding *global* all-pairs event,
`(C(n,2)·2D + (D+1))/(p−1)`.

- The table-size is a **theorem** (`card_handlePolys_le`), not a hypothesis, and
  `runAux_pairs_mem_runTable` **mechanically connects** `runAux`'s queried pairs to the
  handle table (the link `GgmDegreeInvariant` leaves to inspection). `Sym2` counting pays
  the correct `C(n,2)`, and `natDegree_sub_le` (max, not sum) is used correctly so
  differences of degree-≤2D handles stay ≤2D. Reuses the crux and the static core.
- `hdeg_handles` (≤2D) is the same honest SRS-degree hypothesis, in the statement.

### `candidates/GgmArkLibTransport.lean` — residual closer (transport) — **A. Load-bearing.**
Connects the field-level GGM bound to ArkLib's *actual* `Groups.tSdhCondition`.

- Proves the exponent encoding `a ↦ g^a.val` injective/bijective in a prime-order group
  (from ArkLib's own lemmas) and hence `groupWinSet_eq_realWinSet` — an **exact** set
  identity, so the counting bound is about precisely the event `tSdhExperiment` scores.
- **Exemplary residual honesty:** the header explicitly names the one unproven step
  (threading VCVio's `ProbComp` game monad) as "no new mathematics — plumbing," and does
  *not* claim the literal `tSdhExperiment ≤ …` inequality. This is "describe at current
  resolution," done right.

### `candidates/AlgebraicTSdh.lean` — panel candidate (novel) — **A−. Keep (probability anchor).**
The static algebraic adversary, bounded at the **probability level** (`ℝ≥0∞` over ArkLib's
`sampleNonzeroZMod`), reaching `alg_survives_attack : algExperiment < 1`.

- Complementary rather than redundant: it is the **only** file that closes the
  probability-monad step for the algebraic/static case that `GgmArkLibTransport` leaves as
  a named residual for the adaptive case. Clean, canary included
  (`algExperiment_zeroPoly = 0`), no smuggled/unused hypotheses.
- Curation: keep. If the paper presents GGM as *the* repair, this is the strongest of the
  three panel candidates and the natural bridge to the probability level.

### `candidates/AgmSound.lean` — panel candidate — **B+. Exploratory (keep or consolidate).**
Part 1 (`extractPoly_root_and_ne_zero`, `tau_mem_roots`) is a genuine FKL extraction: a
valid algebraic representation of a t-SDH win *is* a q-DLOG solution (nonzero degree-≤D+1
polynomial vanishing at τ). Part 2 (`repr_valid_of_extraction`) is the negative result
"adding a representation field is free data, so it does not close the vacuity."

- Both parts axiom-clean and genuine. Part 2's point is subsumed by the broader vacuity
  story; Part 1's positive direction is covered more completely by `AlgebraicTSdh` +
  `GgmCandidate`. `G₂`/`g₂` appear in Part 2's `variable` block but are used by no theorem
  there (Lean includes only used variables per-decl, so this is not a hypothesis smell —
  just a slightly wide block).
- Curation: **exploratory.** Keep as supporting evidence for the "representation is free
  data" claim, or consolidate its Part 1 into the panel appendix. Not in the minimal core.

### `candidates/KzgQDlogVacuity.lean` — panel candidate — **B. Exploratory (keep or drop).**
Shows that a q-strong-DLOG assumption *stated in ArkLib's unrestricted-adversary idiom* is
also vacuous (false below 1, trivial above), by the identical `Classical.choice`
extraction. Clean, canaried.

- Honest caveat, prominently: the refuted `qDlogAssumption` is **defined by this file
  itself** (ArkLib has no q-DLOG assumption), so this refutes a self-authored object — a
  *modeling demonstration* ("reduce-to-q-DLOG does not by itself escape the hole"), not a
  finding against ArkLib's actual code. The docstring says so.
- Curation: **most exploratory.** Keep as a one-paragraph modeling point in the panel, or
  drop; it carries no claim the core files do not.

---

## Curation call

**Canonical set for the paper's mechanized core + the PR (7 files):**

| File | Role |
|---|---|
| `KzgVacuity.lean` | THE finding: t-SDH + ARSDH vacuity; `binding`/`function_binding` unsatisfiable |
| `RepairSurvives.lean` (top-level) | the de-vacuation reduction survives the exact attack (the PR) |
| `candidates/GgmCandidate.lean` | static GGM core (SZ root event), reused by the two below |
| `candidates/GgmAdaptive.lean` | the adaptive GGM bound (crown jewel) |
| `candidates/GgmDegreeInvariant.lean` | discharges the degree hypotheses (structural, via faithful mirror) |
| `candidates/GgmRandomEncoding.lean` | strengthened all-pairs / random-encoding bound |
| `candidates/GgmArkLibTransport.lean` | transports the field bound to ArkLib's real `tSdhCondition` |

**Panel candidates (supporting alternative repairs; keep behind the GGM core):**
`AlgebraicTSdh.lean` (keep — the probability-level anchor), `AgmSound.lean` (exploratory),
`KzgQDlogVacuity.lean` (exploratory / droppable).

**Removed:** `candidates/RepairSurvives.lean` — broken divergent duplicate of the canonical
top-level file (references a nonexistent constant; does not elaborate).

**Duplicate resolution:** the two `RepairSurvives.lean` differ only in trailing
`#print axioms` lines; the **top-level** one is canonical (byte-matches the build tree and
elaborates clean), the `candidates/` one is broken and removed.

---

## What was fixed vs recommended

**Fixed (edited + rebuilt `sorry`-free + re-`#print axioms` clean after each edit):**
1. `GgmCandidate.ggm_bound_lt_one` — removed unused `[Fact (Nat.Prime p)]` via `omit … in`.
2. `GgmAdaptive.adaptive_bound_lt_one` — same unused `[Fact (Nat.Prime p)]`, same fix.
   Both now match the `omit` idiom `GgmRandomEncoding` already uses; downstream consumers
   (`GgmArkLibTransport`, `GgmRandomEncoding`) rebuilt clean against the changed olean.
3. Removed the broken duplicate `candidates/RepairSurvives.lean` (safe consolidation).

**Recommended (judgment calls, left for ember):**
- `GgmDegreeInvariant`: optionally prove the `buildTable`/`buildPaired` mirror faithful to
  `GgmAdaptive.runAux` so the degree invariant *literally* discharges `hdeg_out`/`hdeg_pairs`
  (today it is by-inspection). This is the corpus's one load-bearing seam.
- `GgmDegreeInvariant`: narrow `import Mathlib` to targeted imports for consistency.
- Panel trim: keep `AlgebraicTSdh`; fold `AgmSound` Part 1 into the panel appendix; consider
  dropping `KzgQDlogVacuity` (self-defined assumption, demonstrative only).

## Verification record
Real ArkLib @ `d72f8392`, Lean v4.31.0, VCVio/CompPoly `v4.31.0`. Every file rebuilt with
`lake env lean` (dependency-ordered LEAN_PATH); every headline theorem `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. Reduction files built against the repaired
`Binding.lean` (`binding_reduces_to_tSdh` present, axiom-clean).
