import Dregg2.Circuit.FriDeployedHeightPairing

/-!
# `FriCommitPow` — pricing `commit_proof_of_work_bits`, and reading BOTH branches at ONE `m`

`FriLedger.lean` names two residuals in its own prose and prices neither. This module prices both,
because together they are the difference between "a ≥100-bit parameterization is impossible" — which
is **FALSE** — and the true statement, which is a much narrower fact about one extension degree with
one knob left at zero.

## ⚑ SCOPE — inherited verbatim from `FriDeployedHeightPairing`, and it has not weakened

Every theorem here is an **arithmetic** statement about a formula transcribed from BCIKS20 (eprint
2020/654 Lemma 8.2 / Thm 8.3) and ethSTARK (eprint 2021/582 eq. 20), composed in `Nat`. **None of
them is a soundness claim against an adversary.** There is no prover strategy, no random-oracle
query bound, and no `ε` quantified over `Q`-bounded provers anywhere in this file. The honest
reading of every number below is: *this is what our own calculator says at the knobs named*. A
bigger number here is a bigger CALCULATOR READING, and nothing more.

That scope is why this file may honestly ADD a grinding column: it is not claiming grinding is
sound, it is recording what the composition arithmetic does with a knob the deployed prover already
implements and the deployed configs already set — to `0`.

## ⚑ RESIDUAL 1 — `commit_proof_of_work_bits` was UNPRICED

plonky3 carries **two** grinding knobs (`fri/src/config.rs:18,20`):

* `query_proof_of_work_bits` — ground ONCE before the query indices are sampled
  (`fri/src/prover.rs:98`, checked `verifier.rs:254`). This is `FriParams.powBits`, and the ledger's
  `johnsonBits` column ALREADY ADDS IT.
* `commit_proof_of_work_bits` — ground **per fold round**, after the round commitment is observed
  and **before the folding challenge `β` is drawn** (`fri/src/prover.rs:224`, checked
  `verifier.rs:222`, with the witness count pinned to the commit count at `verifier.rs:206`). It
  grinds against exactly the phase BCIKS20's `ε_C` bounds. **Every dregg config sets it to `0`**
  (all ten construction sites; `circuit/src/plonky3_prover.rs:168` hard-codes the `0`).

### Why adding it is a CORRECTION, not an inflation

The two columns were **already in different conventions**, and that is the defect:

* `johnsonBits = q·lb/2 + powBits` adds its grinding bits. That is only meaningful in the
  **work-factor** convention — an adversary with `T` hash queries re-samples the query indices `T`
  times, so it wins with probability `≈ T·α^s`, and grinding `ζ` bits raises the work to
  `2^ζ/α^s`. The `+ powBits` IS that `2^ζ`.
* `commitBits = ⌊−log₂ ε_C⌋` adds nothing, because there was nothing to add: the knob ships at `0`.

Under Fiat–Shamir the commit-phase `β` is re-samplable by exactly the same move: a prover that
changes a round commitment (or merely finds a *second* valid PoW witness — `check_witness` admits
many, each absorbing to a different state) redraws `β`. Each redraw costs `2^commit_pow`
permutations. So in the SAME convention the query column already uses, the commit branch is
`−log₂ ε_C + commit_pow`. `commitPowBranch` below is that, and nothing more.

⚑ **What this is NOT.** It is not a reduction, and the `+ commit_pow` is not discharged against any
adversary object — no more and no less than the `+ powBits` that has sat in `johnsonBits` since the
column was written. If one is laundering, both are; they are now at least laundering identically,
which is the minimum a `min` of two branches requires to mean anything.

## ⚑ RESIDUAL 2 — the two branches were read at INCOMPATIBLE `m`

BCIKS20 Thm 8.3 is one theorem with one proximity parameter `m ≥ 3`, appearing in BOTH terms:
`ε_FRI = ε_C(m) + α(m)^s` with `α = √ρ·(1 + 1/2m)`. The tree reads them at different `m`:

* `friCommitLedger` takes `bciksM` and the callers pass **`7`**;
* `friLedger.johnsonBits`' `q·lb/2` is `−s·log₂ α` at **`m → ∞`** — its own docstring says so.

`m → ∞` makes `α` as small as it can be, so `johnsonBits` is an **over-claim at every finite `m`**,
and `m = 7` is an arbitrary pessimisation of the branch that BINDS. Composing a `min` across two
different `m` is not eq. (20); it is a number from no theorem. `johnsonBitsAtM` restores the link
and `compositeBits` takes the `min` at ONE `m`, which the analyst is free to CHOOSE (`m` is
universally quantified in the paper's hypothesis, so any `m ≥ 3` gives a true bound and the best is
ours to take).

Consequence, proved below: the deployed posture is **57**, not the `50` in circulation — the `50`
was 7 bits PESSIMISTIC, from the mixed-`m` composition. Correcting a knob-ledger in the *favourable*
direction deserves the same suspicion as the reverse, so `the_deployed_composite_is_57` carries its
own two-sided brackets and `commit_pow_saturates_at_the_deployed_geometry` immediately shows the
correction does **not** rescue the posture.
-/

namespace Dregg2.Circuit.FriCommitPow

open Dregg2.Circuit.FriLedger
open Dregg2.Circuit.FriLedgerSound
open Dregg2.Circuit.FriDeployedHeightPairing
open Dregg2.Circuit.FriVerifier (FriParams ir2LeafWrapConfig)

/-! ## §1. THE TWO NEW COLUMNS -/

/-- **THE COMMIT BRANCH, WITH GRINDING.** `⌊−log₂ ε_C⌋ + commit_pow`, in the work-factor convention
`johnsonBits` already uses for its own `powBits`. At `commitPow = 0` this is exactly
`friCommitLedger`'s existing column, so the extension is CONSERVATIVE by construction — it cannot
change any number the tree already reports (`commitPowBranch_at_zero_is_the_old_column`). -/
def commitPowBranch (cfg : FriParams) (logD0 bciksM commitPow : Nat) : Nat :=
  (friCommitLedger cfg logD0 bciksM).commitBits + commitPow

/-- The numerator of `α^(2s)`'s reciprocal: `2^(s·lb) · (2m)^(2s)`. -/
def johnsonAlphaNum (cfg : FriParams) (m : Nat) : Nat :=
  2 ^ (cfg.numQueries * cfg.logBlowup) * (2 * m) ^ (2 * cfg.numQueries)

/-- The denominator: `(2m+1)^(2s)`. -/
def johnsonAlphaDen (cfg : FriParams) (m : Nat) : Nat :=
  (2 * m + 1) ^ (2 * cfg.numQueries)

/-- **THE JOHNSON BRANCH AT A FINITE `m`.** With `α = √ρ·(1 + 1/2m)` and `ρ = 2^(−lb)`,

  `α^(2s) = (2m+1)^(2s) / (2^(s·lb) · (2m)^(2s))`,

so the greatest `b` with `α^s ≤ 2^(−b)` is `⌊log₂ X / 2⌋` for `X = (num − 1)/den`. Squaring keeps
everything in `Nat` with **no division inside the power** — the same discipline `friCommitLedger`
uses, and the halving is a floor, so the reported figure rounds DOWN. Adding `cfg.powBits` is the
query grinding, exactly as `friLedger.johnsonBits` does.

⚑ This is **strictly below** the exported `johnsonBits` at every finite `m`, because that column is
the `m → ∞` limit (`the_exported_johnson_column_overstates_at_every_finite_m`). It is a CORRECTION
of an over-claim, not a new optimism. -/
def johnsonBitsAtM (cfg : FriParams) (m : Nat) : Nat :=
  Nat.log2 ((johnsonAlphaNum cfg m - 1) / johnsonAlphaDen cfg m) / 2 + cfg.powBits

/-- **ethSTARK eq. (20), at ONE `m`, with BOTH grinding terms.**
`λ ≥ min{−log₂ ε_C + commit_pow, ζ − s·log₂ α} − 1`. -/
def compositeBits (cfg : FriParams) (logD0 m commitPow : Nat) : Nat :=
  min (commitPowBranch cfg logD0 m commitPow) (johnsonBitsAtM cfg m) - 1

/-! ## §2. BRACKET LEMMAS — `Nat.log2` is well-founded-recursive and does not reduce in the kernel,
so every reading below is proved by EXHIBITING its defining bracket. `native_decide` would drag
`Lean.ofReduceBool` into a soundness column's trust base and is not used. -/

private theorem commitBits_bracket (cfg : FriParams) (logD0 m b : ℕ)
    (h₁ : 2 ^ b ≤ (2 ^ 8 * ledgerP ^ cfg.extDeg - 1) / (friCommitLedger cfg logD0 m).epsCNum)
    (h₂ : (2 ^ 8 * ledgerP ^ cfg.extDeg - 1) / (friCommitLedger cfg logD0 m).epsCNum
        < 2 ^ (b + 1)) :
    (friCommitLedger cfg logD0 m).commitBits = b := by
  show Nat.log2 _ = b
  rw [log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂

/-- `johnsonBitsAtM cfg m = L / 2 + cfg.powBits` from the bracket `2^L ≤ X < 2^(L+1)`. -/
private theorem johnsonAlphaBits_bracket (cfg : FriParams) (m L : ℕ)
    (h₁ : 2 ^ L ≤ (johnsonAlphaNum cfg m - 1) / johnsonAlphaDen cfg m)
    (h₂ : (johnsonAlphaNum cfg m - 1) / johnsonAlphaDen cfg m < 2 ^ (L + 1)) :
    johnsonBitsAtM cfg m = L / 2 + cfg.powBits := by
  show Nat.log2 _ / 2 + _ = _
  rw [log2_eq_log_two, Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂]

/-! ## §3. ⚑ THE HEADLINE — commit PoW MOVES the branch that `numQueries` and `powBits` cannot

`FriLedgerSound.query_and_pow_cannot_pass_epsC` proves `numQueries` and `powBits` leave `ε_C`
EXACTLY where it is. That theorem is TRUE and it was read as "the commit branch cannot be moved
except by `extDeg`". It never said that: it is scoped to the two knobs it names, and
`FriLedger.lean`'s own text flags the third knob as *"unpriced — a named residual, not a swept
one"*. Here is the residual, priced. -/

/-- **⚑ COMMIT-PHASE GRINDING MOVES THE COMMIT BRANCH, BIT FOR BIT.** The exact companion to
`query_and_pow_cannot_pass_epsC`: the same deployed pairing, the same `ε_C`, and a knob that adds
to it one-for-one, for every value at once.

Stated `∀ k` deliberately — a table of instances would leave open that it saturates somewhere. It
does not; `ε_C` is untouched and the branch is a sum. **What saturates is the COMPOSITE**, and that
is the next theorem. -/
theorem commit_pow_moves_the_commit_branch (k : ℕ) :
    commitPowBranch ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM k = 51 + k := by
  show (friCommitLedger _ _ _).commitBits + k = 51 + k
  rw [deployed_wrap_commitBits]

/-- **THE EXTENSION IS CONSERVATIVE.** At `commitPow = 0` the new branch IS the old column, so no
number the tree already publishes moves because this file exists. -/
theorem commitPowBranch_at_zero_is_the_old_column (cfg : FriParams) (logD0 m : ℕ) :
    commitPowBranch cfg logD0 m 0 = (friCommitLedger cfg logD0 m).commitBits :=
  Nat.add_zero _

/-! ## §4. THE `m` CORRECTION -/

/-- **⚑ THE EXPORTED JOHNSON COLUMN OVER-CLAIMS AT EVERY FINITE `m`** — the witness at the deployed
config. `friLedger.johnsonBits` reports `73`; at `m = 7` (the very `m` the commit column is read at)
the honest figure is `71`, and at the `m = 3` that maximises the composite it is `68`.

So the tree's `min{51, 73}` compares a branch at `m = 7` against a branch at `m = ∞`. Neither
number is wrong; the `min` is not eq. (20). -/
theorem the_exported_johnson_column_overstates_at_every_finite_m :
    (friLedger ir2LeafWrapRotatedConfig).johnsonBits = 73 ∧
      johnsonBitsAtM ir2LeafWrapRotatedConfig 7 = 71 ∧
      johnsonBitsAtM ir2LeafWrapRotatedConfig 3 = 68 := by
  refine ⟨by norm_num [friLedger, ir2LeafWrapRotatedConfig], ?_, ?_⟩
  · rw [show (71 : ℕ) = 110 / 2 + 16 from by norm_num]
    refine johnsonAlphaBits_bracket _ _ 110 ?_ ?_ <;>
      norm_num [johnsonAlphaNum, johnsonAlphaDen, ir2LeafWrapRotatedConfig]
  · rw [show (68 : ℕ) = 105 / 2 + 16 from by norm_num]
    refine johnsonAlphaBits_bracket _ _ 105 ?_ ?_ <;>
      norm_num [johnsonAlphaNum, johnsonAlphaDen, ir2LeafWrapRotatedConfig]

/-- **⚑ THE DEPLOYED COMPOSITE IS `57`, NOT `50`.** Read at ONE `m = 3`, both branches honest:
commit `58`, Johnson `68`, composite `57`. The circulating `50` is
`FriDeployedHeightPairing.the_commit_column_binds_at_the_deployed_pairing`'s `min{51, 73} − 1`, and
its 7-bit pessimism is entirely the mixed-`m` composition.

⚑ `57` is still nowhere near `100`. This corrects a number; it does not rescue a posture. -/
theorem the_deployed_composite_is_57 :
    compositeBits ir2LeafWrapRotatedConfig deployedWrapLogD0 3 0 = 57 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 3).commitBits = 58 ∧
      johnsonBitsAtM ir2LeafWrapRotatedConfig 3 = 68 := by
  have hc : (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 3).commitBits = 58 := by
    refine commitBits_bracket _ _ _ 58 ?_ ?_ <;>
      norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapRotatedConfig, deployedWrapLogD0,
        wrapLogCeil, ir2InnerLogBlowup]
  have hj : johnsonBitsAtM ir2LeafWrapRotatedConfig 3 = 68 :=
    the_exported_johnson_column_overstates_at_every_finite_m.2.2
  refine ⟨?_, hc, hj⟩
  show min ((friCommitLedger _ _ _).commitBits + 0) _ - 1 = 57
  rw [hc, hj]
  decide

/-- **⚑ AND THE KNOB SATURATES — the anti-inflation tooth.** Grinding the commit phase at the
DEPLOYED geometry buys `57 → 67` and then **stops**: at `commit_pow = 16` the composite is `67`, and
at `32`, and at `64`, because the Johnson branch (`68`) has taken over the `min`.

This is the theorem that stops "commit PoW" being read as a free ride to any target. On the
deployed knobs it is worth **+10 bits and no more**; passing `67` requires buying queries too, which
is a different knob with a proof-size price.

⚑ `32` and `64` are deliberately chosen ABOVE `maxGrindBits` (§5). They are not proposed settings —
no prover can grind them — and that is the point: the saturation is a property of the `min`, so it
holds even at grinding costs the field could never supply. A reader who doubts the `30`-bit cap
still gets `67`. -/
theorem commit_pow_saturates_at_the_deployed_geometry :
    compositeBits ir2LeafWrapRotatedConfig deployedWrapLogD0 3 16 = 67 ∧
      compositeBits ir2LeafWrapRotatedConfig deployedWrapLogD0 3 32 = 67 ∧
      compositeBits ir2LeafWrapRotatedConfig deployedWrapLogD0 3 64 = 67 := by
  have hc : (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 3).commitBits = 58 :=
    the_deployed_composite_is_57.2.1
  have hj : johnsonBitsAtM ir2LeafWrapRotatedConfig 3 = 68 :=
    the_exported_johnson_column_overstates_at_every_finite_m.2.2
  refine ⟨?_, ?_, ?_⟩ <;>
    · show min ((friCommitLedger _ _ _).commitBits + _) _ - 1 = 67
      rw [hc, hj]
      decide

/-! ## §5. ⚑ THE GRINDING CAP — the ledger must not price a config the prover cannot run

plonky3's `grind` (`challenger/src/grinding_challenger.rs:107`) opens with

  `assert!((1u64 << bits) < F::ORDER_U64)`

and the witness is ONE base-field element (`type Witness = F`), so the search space is `|F_base|`
and the PoW target must fit strictly inside it. Over BabyBear that caps **both** proof-of-work knobs
at **30 bits** — `2^30 < p < 2^31`. It is a structural limit of the witness type, not a policy: at
`31` the prover asserts out, and there is no larger witness to grind on.

⚑ This is exactly the guard that keeps this file from committing the wound it was written to avoid.
A `commitPow` column with no cap would happily report `140` bits at `commit_pow = 60` — a number for
an object no prover can produce. `grindableBits` below is the cap, `maxGrindBits_is_the_babybear_
witness_cap` pins it to the modulus the rest of the ledger is stated over, and **every config
theorem in §6 carries `≤ maxGrindBits` as a conjunct**, so a knob set that cannot be ground cannot
be quoted from here as a posture. -/

/-- The largest PoW bit count a BabyBear witness admits: `2^b < p`. -/
def maxGrindBits : Nat := 30

/-- **⚑ THE CAP IS THE MODULUS, NOT A CHOICE.** `2^30 < p` and `2^31 ≥ p`, so `30` is exactly
plonky3's `(1 << bits) < F::ORDER_U64` over BabyBear — tight on both sides. -/
theorem maxGrindBits_is_the_babybear_witness_cap :
    2 ^ maxGrindBits < ledgerP ∧ ¬ (2 ^ (maxGrindBits + 1) < ledgerP) := by
  constructor <;> decide

/-! ## §6. ⚑ THE CORRECTION OF THE RECORD — a ≥100-bit parameterization EXISTS

The claim in circulation was that `query_and_pow_cannot_pass_epsC` makes ≥100 bits impossible. It
does not, and the two configs below are the refutation: each is a CONSTRUCTIVE witness, with its own
two-sided brackets on both branches, at a trace height the tree already runs.

⚑ Neither is "deployed". They are readings of knob sets the prover CAN be handed — the arity, the
blowup, the query count and both PoW knobs are all `FriParameters` fields plonky3 already honours,
and `create_config_with_fri_full` already exposes the commit knob. What the ext-`8` config needs
that the ext-`4` one does not is the extension-degree change, which is a rebuild, a VK rotation and
a fresh gnark setup — a flag day, named as such, not a knob turn. -/

/-- **⚑ ≥100 BITS AT `extDeg = 4` — NO FIELD-EXTENSION FLAG DAY, AND THE GRIND IS RUNNABLE.**

`logBlowup 2`, `110` queries, arity `8`, query-PoW `16`, **commit-PoW `28`**, at `|D⁽⁰⁾| = 2^17`
(trace `2^15` × blowup `2^2`), `m = 3`: commit branch `74 + 28 = 102`, Johnson branch `101`,
composite **`100`**.

This is the theorem that refutes the impossibility claim in the form it was made — it changes no
field, no extension degree, and no trusted setup. The `28 ≤ maxGrindBits` conjunct is load-bearing,
not decoration: the first draft of this theorem used `commit_pow = 34` at `logBlowup 4`, which reads
`100` and **cannot be ground at all** — `grind` asserts out above `30`. The cap is what caught it.

Its price is the `5 × 2^28` grind (measured whole-machine at `0.85 M – 7.9 M` Poseidon2-BabyBear
witness trials/s, i.e. `≈ 1–26 min` per proof, `circuit/tests/commit_pow_cost_measure.rs`) and `110`
queries against the deployed `19` — a ~1.75× proof. Both are tabulated in `docs/FRI-SECURE-PARAMETERIZATION.md`. -/
theorem ext4_reaches_100_without_a_field_flag_day :
    compositeBits { logBlowup := 2, numQueries := 110, powBits := 16, maxLogArity := 3,
                    logFinalPolyLen := 0, extDeg := 4 } 17 3 28 = 100 ∧ 28 ≤ maxGrindBits := by
  have hc : (friCommitLedger { logBlowup := 2, numQueries := 110, powBits := 16, maxLogArity := 3,
                               logFinalPolyLen := 0, extDeg := 4 } 17 3).commitBits = 74 := by
    refine commitBits_bracket _ _ _ 74 ?_ ?_ <;> norm_num [friCommitLedger, ceilDiv, ledgerP]
  have hj : johnsonBitsAtM { logBlowup := 2, numQueries := 110, powBits := 16, maxLogArity := 3,
                             logFinalPolyLen := 0, extDeg := 4 } 3 = 101 := by
    rw [show (101 : ℕ) = 171 / 2 + 16 from by norm_num]
    refine johnsonAlphaBits_bracket _ _ 171 ?_ ?_ <;>
      norm_num [johnsonAlphaNum, johnsonAlphaDen]
  refine ⟨?_, by decide⟩
  show min ((friCommitLedger _ _ _).commitBits + 28) _ - 1 = 100
  rw [hc, hj]
  decide

/-- **⚑ ≥128 BITS AT `extDeg = 8`, WITH THE COMMIT KNOB STILL AT ZERO.**

`logBlowup 6` (the deployed blowup), `38` queries, arity `8`, query-PoW `16`, **commit-PoW `0`**, at
`|D⁽⁰⁾| = 2^21` (trace `2^15` × blowup `2^6`), `m = 28`: commit branch `163`, Johnson branch `129`,
composite **`128`**.

The commit branch is `35` bits of slack here — at `extDeg = 8` the term that has bound every reading
in this tree stops binding at all, and the posture becomes query-limited, which is the regime the
`numQueries` knob was always for. `commitPow = 0` is not an oversight in this row: it is the point.

⚑ `extDeg = 8` is real in plonky3 (`p3-baby-bear` implements `BinomialExtensionData<8>`), and it is
a FLAG DAY: every descriptor re-emits, every VK rotates, and the gnark wrap needs a fresh Groth16
setup. -/
theorem ext8_reaches_128 :
    compositeBits { logBlowup := 6, numQueries := 38, powBits := 16, maxLogArity := 3,
                    logFinalPolyLen := 0, extDeg := 8 } 21 28 0 = 128 := by
  have hc : (friCommitLedger { logBlowup := 6, numQueries := 38, powBits := 16, maxLogArity := 3,
                               logFinalPolyLen := 0, extDeg := 8 } 21 28).commitBits = 163 := by
    refine commitBits_bracket _ _ _ 163 ?_ ?_ <;> norm_num [friCommitLedger, ceilDiv, ledgerP]
  have hj : johnsonBitsAtM { logBlowup := 6, numQueries := 38, powBits := 16, maxLogArity := 3,
                             logFinalPolyLen := 0, extDeg := 8 } 28 = 129 := by
    rw [show (129 : ℕ) = 226 / 2 + 16 from by norm_num]
    refine johnsonAlphaBits_bracket _ _ 226 ?_ ?_ <;>
      norm_num [johnsonAlphaNum, johnsonAlphaDen]
  show min ((friCommitLedger _ _ _).commitBits + 0) _ - 1 = 128
  rw [hc, hj]
  decide

/-! ## §7. NON-VACUITY / MUTATION CANARIES

A ledger extension is worthless if the brackets would have accepted any number, or if the new column
agreed with the old one everywhere it was checked. -/

/-- **⚑ THE FIVE READINGS ARE PAIRWISE DISTINCT AND ORDERED.** `50` (the tree's mixed-`m`), `57`
(honest, deployed), `67` (deployed + saturated commit grinding), `100` (ext-4 + grinding), `128`
(ext-8). A single wrong digit in `johnsonBitsAtM` or `commitPowBranch` reds at least one. -/
theorem the_five_readings_are_distinct_and_ordered :
    (min 51 73 - 1 : ℕ) = 50 ∧
      compositeBits ir2LeafWrapRotatedConfig deployedWrapLogD0 3 0 = 57 ∧
      compositeBits ir2LeafWrapRotatedConfig deployedWrapLogD0 3 16 = 67 ∧
      compositeBits { logBlowup := 2, numQueries := 110, powBits := 16, maxLogArity := 3,
                      logFinalPolyLen := 0, extDeg := 4 } 17 3 28 = 100 ∧
      compositeBits { logBlowup := 6, numQueries := 38, powBits := 16, maxLogArity := 3,
                      logFinalPolyLen := 0, extDeg := 8 } 21 28 0 = 128 :=
  ⟨by decide, the_deployed_composite_is_57.1, commit_pow_saturates_at_the_deployed_geometry.1,
    ext4_reaches_100_without_a_field_flag_day.1, ext8_reaches_128⟩

/-- **⚑ THE IMPOSSIBILITY CLAIM, REFUTED AS A `Prop`.** Stated in the shape it was believed:
"no knob set reaches 100". One witness suffices, it is an `extDeg = 4` one — so the refutation does
not even need the field change that was thought to be the only lever — and its grinding is inside
the cap, so it is a config a prover can actually produce. -/
theorem a_hundred_bit_parameterization_exists :
    ∃ (cfg : FriParams) (logD0 m commitPow : ℕ),
      cfg.extDeg = 4 ∧ commitPow ≤ maxGrindBits ∧ 100 ≤ compositeBits cfg logD0 m commitPow :=
  ⟨{ logBlowup := 2, numQueries := 110, powBits := 16, maxLogArity := 3,
     logFinalPolyLen := 0, extDeg := 4 }, 17, 3, 28, rfl,
   ext4_reaches_100_without_a_field_flag_day.2,
   ext4_reaches_100_without_a_field_flag_day.1.ge⟩

/-! ## §8. Axiom hygiene. `#assert_axioms` checks the AXIOM closure and is blind to hypotheses and
to whether the transcribed formula is the paper's. Kernel-clean here means "the arithmetic is
right", never "the security claim is discharged". -/

#assert_axioms commit_pow_moves_the_commit_branch
#assert_axioms commitPowBranch_at_zero_is_the_old_column
#assert_axioms the_exported_johnson_column_overstates_at_every_finite_m
#assert_axioms the_deployed_composite_is_57
#assert_axioms commit_pow_saturates_at_the_deployed_geometry
#assert_axioms ext4_reaches_100_without_a_field_flag_day
#assert_axioms ext8_reaches_128
#assert_axioms the_five_readings_are_distinct_and_ordered
#assert_axioms maxGrindBits_is_the_babybear_witness_cap
#assert_axioms a_hundred_bit_parameterization_exists

end Dregg2.Circuit.FriCommitPow
