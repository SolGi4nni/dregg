# STARK-FLOOR-REDUCTION — reducing `transferV3`'s two OOD residuals to the irreducible crypto floor

**Honest scope, first sentence.** The `transferV3` STARK-soundness landing
(`FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals`) currently rests on TWO named
hypotheses — `hood` and `hnonexc` — carried as premises of `OodInterpF`. This doc maps, per
residual, whether each is (1) PROVABLE in Lean with no assumption, (2) REDUCIBLE to a game against
the in-tree `∀`-adversary with a concrete advantage bound, or (3) a GENUINELY IRREDUCIBLE crypto
floor. The end state is the SAME minimal shape the PQ-metatheory apex bottoms out at:
`{Poseidon2SpongeCR, FRI-LDT-soundness, a Fiat–Shamir/RO game with ε ≤ deg/|F|}`.

The residual frontier is, verbatim
(`metatheory/Dregg2/Circuit/FieldIntegerLift.lean:131-142`):

```lean
theorem ood_forces_mainAirAccept_field_of_residuals (d …) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize) (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (hood   : ∀ c ∈ d.constraints, isArith c →
        (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ)
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t
```

`hZrow` (domain geometry) and `hCrow` (trace-column interpolation) are ALREADY discharged in-tree
(`vanishingPoly_eval_rowPt`; `TraceColumnInterp.constraintPoly_eval_eq_arithResidual`). The frontier
is exactly `hood` + `hnonexc`.

---

## 1. `hood` — the per-constraint OOD identity. Three sub-obligations (a,b,c).

`hood` asserts, per arithmetic constraint `c`, the pointwise identity
`constraintPoly(ζ) = vanishingPoly(ζ)·qp_c(ζ)`. In deployment `verifyAlgo` delivers only the
BATCHED, COMMITTED image of this — `TableOpening.constraintEval = A.mul vanishingAtZeta quotientAtZeta`
(`FriVerifier.lean:650`; forced by acceptance via `verifyAlgo_accept_forces_table_identity`,
`OodQuotientConsistency.lean:144`). Bridging that opaque field element to the per-constraint
`constraintPoly` bundles three things.

### (a) RLC de-batching — **PROVABLE (Schwartz–Zippel), no assumption.**

`verifyAlgo` folds all declared constraints into ONE `constraintEval` per table via a Fiat–Shamir
random-linear-combination challenge `λ`; `MainAirAcceptF` wants the identity PER constraint. The
split back is the identical `card_roots'` route already proved for the LogUp bus.

- **In-tree template:** `LogUpSoundness.lean` — `busNum`, `degree_busNum_lt` (:197),
  `exceptionalSet_card_lt` (:223), `logup_forged_lookup_sound` (:274). The RLC batch identity
  `Σ_c λ^c · R_c(ζ) = 0` where some `R_c ≠ 0` is exactly "a nonzero polynomial in the batching
  challenge `λ` vanishes at the sampled `λ`" — root-counting over `λ` with the exceptional set named,
  the same shape as `busNum`'s roots in `α`.
- **Exact route:** define `batchResidual(Λ) = Σ_c Λ^c · (constraintPoly_c − Z·qp_c)` as a
  polynomial in a fresh indeterminate `Λ`; if any per-constraint residual is nonzero then
  `batchResidual ≠ 0` (leading term argument, exactly `busNum_ne_zero_of_forged`'s pattern of
  evaluating at a distinguishing point); then `exceptionalSet_card_le`
  (`OodQuotientConsistency.lean:90`) bounds the bad-`λ` set by `natDegree batchResidual ≤ #constraints`.
- **Residual soundness-error term:** ε_RLC ≤ (#constraints − 1)/|F| = (#constraints−1)/2013265921.
- **Status:** tractable now; pure re-instantiation of the LogUp Schwartz–Zippel lemma over the
  batching challenge. NO new assumption. The one piece of unmodeled plumbing is exhibiting the
  descriptor's actual `λ`-column and per-constraint residual layout (same "column-layout is
  unmodeled" residual `LogUpSoundness §8` names for `hbus`).

### (b) Commitment-opening binding — **IRREDUCIBLE FLOOR (`Poseidon2SpongeCR`).**

That the opened `constraintEval` equals the committed polynomial evaluated at ζ (a prover cannot
open the Merkle/FRI commitment to a different value) is a hash-binding fact, not algebra.

- **In-tree machinery:** `AggAirSound.combine_digest_binds` (:205) and
  `FriSoundness.oracle_binding` / `equivocation_breaks_binding` (§4) — both rest on
  `Poseidon2SpongeCR` (`Poseidon2Binding.lean`), the ONE named hash floor, used as a `Prop`
  hypothesis, never an `axiom`. A colliding commitment is exactly what lets the prover equivocate the
  opened value.
- **Status:** genuine, legitimately-named crypto assumption — the same class as lattice/DL. Bottoms
  out here; reduce it TO `Poseidon2SpongeCR`, do not try to prove it away.

### (c) Low-degreeness of the committed poly — **IRREDUCIBLE FLOOR (FRI-LDT), partly formalized.**

`qp_c` (and the composition poly) being genuinely low-degree — so that the residual `R = C − Z·qp`
is low-degree and the exceptional set is SMALL relative to |F| — is the FRI deliverable.

- **In-tree machinery:** `FriSoundness.lean` FORMALIZES the BBHR18/BCIKS20 argument: RS distance
  (§1), the fold operator (§2), the KEY LEMMA `fold_close_of_two_alpha` (§3, distance preserved by
  folding), and `fri_fold_soundness` (§4: an accepting-yet-far transcript forces the challenge into a
  ≤1-element exceptional set OR a hash collision). `FriProximity` + `friProximity_discharge` is the
  interface the AIR check consumes (`air_binds_of_proximity`).
- **The honest gap:** `BabyBearFriField.lean:9` and `BabyBearFriSetup.lean` note the discharge is
  currently INSTANTIATED only at a toy setup (`babyBear_friProximity_discharge` at `δ = 0`, the
  0-close honest codeword), NOT bound to the deployed `2^27` domain / rate / query count nor to the
  live `verifyBatch`. The elementary two-point fold constant (`4×`) is proved; the tight
  proximity-gaps / Johnson-bound constant is a QUANTITATIVE improvement, noted not open.
- **Status:** genuine crypto floor (FRI soundness is conjectural at list-decoding radius). The
  algebraic content is proved; what remains is the deployed-parameter binding + the query-count
  soundness accounting. This is the HARD residual — do not pretend it is closed.

---

## 2. `hnonexc` — Fiat–Shamir non-exceptionality. **REDUCIBLE TO A GAME (ε ≤ deg/|F|).**

`hnonexc` asserts the OOD point ζ ∉ `exceptionalSet(R_c)` = roots of the per-constraint residual. ζ
is transcript-derived (Fiat–Shamir over the committed data). This is NOT provable unconditionally
(the escape is real: `OodQuotientConsistency.ood_exceptional_escape` :256 exhibits a tampered
quotient that PASSES at an exceptional ζ) — but it reduces to a bounded-advantage RO game, exactly
as the PQ apex handles its challenge-sampling.

- **The cardinality half is PROVED:** `exceptionalSet_card_le R ≤ R.natDegree`
  (`OodQuotientConsistency.lean:90`) and the concrete `babybear_ood_soundness_error` (:225):
  `#exceptionalSet ≤ natDegree R ∧ |BabyBear| = 2013265921`. So for a uniform ζ, a tampered
  quotient escapes with probability ≤ deg R / 2013265921.
- **This IS a `winProb` game in the in-tree framework.** The `ForkingFamily` machinery
  (`ProbCrypto.lean:230-327`) is a `World × Chal → Bool` accept game with `winProb`
  (`ProbCrypto.lean:71`, `#favorable / #Ω`), the collision term `invChal = 1/|Chal|` (:271), and
  proved advantage inequalities (`ForkingFamily.bound` :313 via `winProb_le_of_imp`). A STARK-OOD
  game instantiates it directly:
  - `World l` = (committed proof / trace / residual polynomials) — the prover's prefix,
  - `Chal l` = the OOD point space = `BabyBear` (or the FS challenge domain),
  - `acc l w ζ` = "ζ ∈ exceptionalSet(R_w)" — the bad event (prover escapes),
  - the favorable set is exactly `exceptionalSet(R_w)`, so `winProb(acc l w) = #exceptionalSet /
    |Chal| ≤ natDegree R / |F|` — a DIRECT corollary of `exceptionalSet_card_le` + `winProb`'s
    definition, no forking needed.
  The advantage bound is `Negl` when deg/|F| is negligible (BabyBear |F| ≈ 2×10⁹; multi-round FRI
  repetition drives it down further), discharged by the same `Negl`/`negl_add` calculus
  `ProtocolSoundnessQuant.lean` uses for the signature consumers.
- **Rough game statement:**
  `oodEscapeAdv : ForkingFamily := { World := committed residuals, Chal := BabyBear,
   acc := fun w ζ => decide (ζ ∈ exceptionalSet w.R) }` with
  `theorem ood_escape_negl : Negl oodEscapeAdv.forgerAdv` whose bound is `forgerAdv l ≤ deg/|F|`
  from `exceptionalSet_card_le`. This is a round-by-round / state-restoration soundness game in the
  Ben-Sasson–Chiesa–Spooner sense: each FS-derived challenge (RLC `λ`, OOD ζ, FRI fold βs, query
  indices) is one round, each with its own small exceptional set; the total soundness error is the
  UNION-BOUND sum of the per-round `deg/|F|` terms plus the FRI query-rejection term — additively, as
  `negl_add` composes. The commitment-binding part of the game bottoms out at `Poseidon2SpongeCR` as
  in 1(b) (the RO/commitment is instantiated by the hash floor, not a programmable RO axiom).

---

## 3. The residual floor after full reduction

After discharging (a) and (2) as Lean lemmas/games, `transferV3` STARK soundness rests on exactly:

```
{ Poseidon2SpongeCR                    -- Merkle/commitment binding (hood.b) — hash floor
, FRI-LDT-soundness @ deployed params  -- committed-poly low-degreeness (hood.c) — the hard one
, a Fiat–Shamir/RO game, ε ≤ deg/|F|   -- RLC de-batch (hood.a) + OOD non-exceptionality (hnonexc)
                                          + FRI query-count rejection, union-bounded and Negl }
```

This is the SAME minimal shape as the PQ-metatheory apex (`{MSIS/MLWE/DL/hash floor} + {O2H/forking
RO game, ε negligible}`). Nothing dregg-specific remains; every residual is a standard,
legitimately-named STARK/FRI assumption or a proved Schwartz–Zippel bound.

---

## 4. Is a STARK soundness GAME expressible in the in-tree `∀`-adversary framework?

**Yes, fully.** Two complementary frames already exist:

- **Quantitative (advantage) frame — the right one for OOD/FS.** `ProbCrypto.ForkingFamily` +
  `winProb` + `Negl` + `ProtocolSoundnessQuant`'s `hybridBreakAdv_le_hybrid` pattern express a
  round-by-round soundness game with a real `winProb` advantage and a proved `≤ deg/|F|` bound. The
  OOD-escape game in §2 is a near-trivial instantiation (the favorable set IS `exceptionalSet`,
  already cardinality-bounded). FRI's own soundness is already in exactly this idiom
  (`fri_fold_soundness`: accept-yet-far ⟹ challenge in ≤1-element set OR hash collision).
- **Qualitative (∀A) frame — for the top-level statement.** `Metatheory.Adversary.Adversary`
  (`Model.lean:73`) bundles every control surface under one `∀ A`, and
  `CoinductiveAdversary` gives the unbounded-interleaving lift. A STARK-soundness apex would add a
  field "for every proving adversary A, `verifyAlgo` accepts A's proof ⟹ `MainAirAcceptF` except with
  advantage ≤ (union-bounded ε)", discharged by the quantitative game above. Mechanically the same
  reframing `Model.lean §2` did for the four existing surfaces.

---

## 5. Prioritized implementation plan

1. **RLC de-batch via Schwartz–Zippel (hood.a) — DO FIRST.** Highest tractability, zero new
   assumption. Instantiate `LogUpSoundness`'s `card_roots'` route on the batching challenge `Λ`;
   land ε_RLC ≤ (#constraints−1)/|F| via `exceptionalSet_card_le`. Blocked only on the descriptor's
   RLC column layout (the same unmodeled-plumbing residual `hbus` names).
2. **OOD non-exceptionality game (hnonexc) — DO SECOND.** Package `babybear_ood_soundness_error`
   as a `ForkingFamily`/`winProb` game (`acc := ζ ∈ exceptionalSet`), prove `forgerAdv ≤ deg/|F|`
   and `Negl` under the union bound. Purely a repackaging of an existing cardinality lemma into the
   existing probability calculus — very tractable.
3. **Merkle-opening binding via `Poseidon2SpongeCR` (hood.b) — DO THIRD.** Reduce the
   `constraintEval = committedPoly(ζ)` link to `oracle_binding`/`combine_digest_binds` under the
   named hash floor. Tractable; it is a reduction to an existing floor, not a new proof.
4. **FRI-LDT at deployed parameters (hood.c) — THE HARD RESIDUAL, LAST.** Bind
   `friProximity_discharge` to the real `2^27` domain / rate / `numQueries 19` / `powBits 16`
   (`ir2LeafWrapConfig`), and prove the query-count soundness accounting
   (`concreteFriChecks_rejects_query_count`, `friQueryCheck_rejects_bad_final`) composes to the
   list-decoding soundness error. The algebra is done (`FriSoundness §1-4`); the deployed-parameter
   binding and the conjectural list-decoding radius are the genuine open crypto work.

---

## 6. Honest verdict — how much of `{hood, hnonexc}` is reducible NOW

- **`hnonexc`: FULLY reducible now.** The cardinality bound is already proved
  (`exceptionalSet_card_le`, `babybear_ood_soundness_error`); reducing it to a `winProb` game with
  ε ≤ deg/|F| is repackaging, not new mathematics. This is NOT a crypto assumption — it is a proved
  Schwartz–Zippel bound awaiting its game wrapper.
- **`hood.a` (RLC de-batch): reducible now.** A direct re-instantiation of the committed LogUp
  Schwartz–Zippel route. Not an assumption.
- **`hood.b` (commitment binding): reduces to `Poseidon2SpongeCR` now.** A genuine, legitimately-named
  hash floor — the reduction is tractable, the floor itself is a real assumption (correctly named,
  not laziness).
- **`hood.c` (low-degreeness / FRI-LDT): a GENUINE crypto assumption, only partly formalized.** The
  BBHR18/BCIKS20 algebra is proved in `FriSoundness`, but it is instantiated at a toy setup, not the
  deployed parameters, and FRI soundness at list-decoding radius is conjectural. This is the ONE
  residual that is a real, hard, open assumption — not reducible by cleverness, only by the standard
  FRI soundness argument at real parameters.

**Bottom line.** ≈ three of the four sub-obligations (`hnonexc`, `hood.a`, `hood.b`) are reducible
now to `{proved Schwartz–Zippel bound as a winProb game}` + `{Poseidon2SpongeCR}` with no new
dregg-specific assumption. The single genuine irreducible floor is `hood.c` = FRI-LDT soundness at
deployed parameters — the same floor every STARK bottoms out at, and the same shape as the PQ apex's
crypto floor. `{hood, hnonexc}` is NOT a real floor as it stands; after reduction it collapses to
the minimal, honestly-named STARK floor.
