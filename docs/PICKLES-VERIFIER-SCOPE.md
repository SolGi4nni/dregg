# PICKLES-VERIFIER-SCOPE.md — from a single Kimchi verify to Mina's Pickles recursion

**Status:** scoping doc + **P0/P1/P2 BUILT** (2026-07-27) + **P6 BUILT, the Fq-state sponge with
it, and P3 (`finalize_other_proof`) BUILT** (2026-07-28). P4/P5/P7/P8/P9 remain unbuilt scoping;
P10 is the inherited terminal floor. **P4 is the security crux and is NOT started** — read the P3
block's caveat before treating `finalize_other_proof` as meaning anything about soundness.
Audience: ember + the K7 (Pickles) build.
This is the follow-on named in `docs/MINA-KIMCHI-VERIFIER-PLAN.md` item 6 ("Pickles/recursion tip …
recursion is the follow-on") and the frontier `KimchiVerify.lean` freezes at `prevLen = 0`.

### BUILD STATUS — `metatheory/Dregg2/Circuit/Emit/PicklesRecursion.lean`

P0, P1 and P2 are Lean-authored, `lake build`-green on hbox and `#assert_namespace_axioms`-clean
(91 theorems ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no `native_decide`).

- **P0** — `both_shapes_run` runs K5's `kimchiVerifyDecisionGates` at BOTH `Fp = ZMod pN`
  (Step, Vesta-committed, `k=16`) and `Fq = ZMod qN` (Wrap, Pallas-committed, `k=15`);
  `wrap_field_decision_discriminates` (10 tampers), `sides_discriminate`, `cycle_is_a_swap`,
  `wrapOmega15_is_the_wrap_domain` (the real `2^15` wrap-domain generator, exact order, via the
  `sqIter` ladder — since 2026-07-28 the ladder lives in `KimchiVerify`, not here, because the C8
  recursion fold needs it upstream and two ladders is one too many). **`wrap_prev_challenges_refused`
  proved the real Wrap object's `prev_challenges = 2` was REFUSED by K5's v1 `shapeOk`** — the
  `prevLen = 0` frontier, measured. **[SUPERSEDED 2026-07-28 by P6: the theorem is now
  `wrap_prev_challenges_admitted`, and its old statement is FALSE of the shipped decision.]**
  Residuals: **no real Wrap fixture**, witness domain `2^5` (kernel cost). The Fq-state sponge
  residual is CLOSED — `PastaPoseidonFq`.
- **P1** — `accumulator_check_splits`: the assembled `msm(points, scalars)` of
  `batch_dlog_accumulator_check` IS `Σ r^i·comm_i − Σ r^i·⟨sVec chals_i, G⟩`, plus
  `accumulator_check_complete` / `_one` / `_two_sound`. The per-proof block is K4c's `sVec`;
  `accumulator_block_is_bPoly` / `_compression` are the `sVec_eq_bPoly` / `deferral_compression`
  reuse. Residuals: the terminal `msm == 0` is P10; `r` is `OsRng`-sampled so general-`k` batching
  soundness is statistical and NOT proven.
- **P2** — the two `Deferred_values` records + `wrapData_roundtrip`, the `Shifted_value`
  Type1/Type2 bridge (`type1_eq_iff` / `type2_eq_iff` — comparing shifted representatives IS
  comparing field values, the algebraic half of P4), the concrete Pasta shift constants
  (`pasta_shift_constants`: `2^255 + 1` / `2^255`), `branchData_roundtrip`.

### BUILD STATUS — P6 + the Fq-state sponge (2026-07-28)

Two new modules, both `lake build`-green on hbox and `#assert_namespace_axioms`-clean:

- **`metatheory/Dregg2/Circuit/Emit/PastaPoseidonFq.lean`** (22 theorems pinned) — the phase-1
  sponge that was a NAMED CARRIER. The `fq_kimchi` MDS (3×3) and round constants (55×3) are dumped
  from `mina_poseidon::pasta::fq_kimchi::static_params()` at o1-labs `proof-systems`
  **`f6d958dc05`** (`poseidon/src/pasta/fq_kimchi.rs`) — **sourced, not invented**, as the prior
  lane insisted. The Poseidon schedule is written ONCE, parametrically over `⟨modulus, mds, rcs⟩`,
  and `core_is_Ref_at_Fp` PROVES the Fp instantiation is `PastaPoseidon.Ref.hash` for every input
  — so the Fq sponge is that schedule at other constants, not a second hand-copy of the schedule
  that ate the 2026-07-27 double-permute defect. 12 KATs at BOTH parities + 5 double-permute
  anti-values, all emitted by the upstream `ArithmeticSponge` state machine itself.
  ⚑ **β, γ, α′, ζ′ and the phase-1 digest of a REAL Kimchi proof are RE-DERIVED end-to-end**
  (`fqPhase1`) from the verifier-index digest and the real commitment coordinates. Nothing in that
  chain is consumed as given, and tampers at each stage of the tape are pinned.
  **Naming trap, read through:** `fq_kimchi` is the phase-1 sponge of a **Vesta**-committed (Step)
  proof and the phase-2 sponge of a **Pallas**-committed (Wrap) proof — `curve.rs:62-72,87-97`. One
  instantiation closes the missing half on both sides of the cycle.
- **`metatheory/Dregg2/Circuit/Emit/KimchiRecursionGate.lean`** (14 theorems pinned) — **P6**, on a
  REAL `prev_challenges = 2` Kimchi proof that `kimchi::verifier::verify` accepts
  (`create_recursive` + two genuine `RecursionChallenge` accumulators; extractor mirrored at
  `metatheory/fixtures/kimchi-extractors/pickles_p6_fq_export.rs`, fixture at
  `metatheory/kimchi_p6_prev2_proof.json`). `rec_decision_accepts` runs the composed
  `kimchiVerifyDecisionFieldRec` over `ZMod pN`; eight tampers flip it.

And in **`KimchiVerify.lean`** the freeze itself is gone:

- `shapeOkRec` is the upstream check `proof.prev_challenges.len() == index.prev_challenges`
  (`verifier.rs:810-813`). `shapeOk` survives as its instantiation at a non-recursive index — a
  parameter value, not a wall.
- `transcriptScheduleRec nPrev` puts the `nPrev` recursion commitments in the phase-1 transcript
  (`verifier.rs:165-168`) and the prev-challenge digest in the phase-2 one (`:290-299`).
  **Two corrections landed with it:** `ft_eval1` is absorbed BEFORE the public evaluations (the old
  listing had them swapped), and the prev-challenge digest was missing from the listing entirely.
  Neither changed a VALUE at `nPrev = 0` — which is exactly why neither was caught.
- `prevChalFoldOk` RECOMPUTES the b-poly evaluations of the carried challenges at ζ and ζω and
  compares them to the two leading entries of the `combined_inner_product` columns. `bEvalSq` (the
  `commitment.rs:429-433` squaring ladder) is what makes that kernel-tractable at `k = 16`, and
  `bEvalSq_eq_bEval` proves it is K4c's `bEval`, so `sVec_eq_bPoly` still applies to it.
- The `sqIter` ladder MOVED from `PicklesRecursion` (downstream) to `KimchiVerify`; the duplicate
  is deleted, not kept.

**What P6 does NOT do.** The fixture is Step-shape (Vesta-committed, `k = 16`), not Wrap. The
accumulator commitments are checked only as transcript inputs — that `comm = ⟨b_poly_coeffs, G⟩`
is `accumulator_check`, bottoming out at P10. `Wrap_hack` padding to 2 is modelled only as the
count, not as the dummy-challenge construction (that is P7's dummy proof).

### BUILD STATUS — P3 (2026-07-28) — **two lanes met here; read which file owns what**

`metatheory/Dregg2/Circuit/Emit/PicklesFinalize.lean` (39 theorems pinned) is the **P3 authoring
site**: the `derive_plonk` arms, the four-way `finalizeOtherProof`, a universally-quantified
completeness theorem (not a KAT), the tamper poles, and a MEASURED reading of
`plonk_checks::checked` — **its comparison list is `[perm]`, one entry, in both implementations**
(`plonk_checks.rs:363-366`, siblings commented out; `plonk_checks.ml:541-543`). `derive_plonk`
computes `zeta_to_srs_length` and `zeta_to_domain_size` and `checked` compares **neither**. That
file also carries P4 as MEASURED-not-proved; read its §Z before citing anything there as recursion
soundness.

`metatheory/Dregg2/Circuit/Emit/PicklesDerivePlonkRealGate.lean` (5 theorems pinned) is the
**reality gate for those derivations**, and defines none of them. It instantiates
`PicklesFinalize`'s `permScalarR` / `zetaToDomainSizeR` / `zetaToSrsLengthR` at the real
`prev_challenges = 2` proof of `KimchiRecursionGate` and compares against values o1-labs' own code
computed: `perm` against **`ConstraintSystem::perm_scalars`** (`permutation.rs:392-430`), `zkp(ζ)`
against the index's `permutation_vanishing_polynomial_m` (which is what makes the `perm` comparison
a differential rather than a restatement of K5's formula), `ζ^max_poly_size` at the **real 65536**
through the `sqIter` ladder, and `b_correct`'s `bEval` against their **`b_poly`** at `k = 16`.
Eight per-argument tampers. `PicklesFinalize`'s own note — *"Not a real fixture … the concrete pole
runs at `ZMod 97`"* — is the gap this closes.

**The finding both lanes reached independently:** `derive_plonk`'s `perm`
(`plonk_checks.rs:259-266`) is character-for-character o1-labs' `ConstraintSystem::perm_scalars`
**and** K5's `permScalar`. One expression, three call sites. So P3's "new scalar derivations" are
two exponentiations plus a K5 reuse.

⚑ **P4 is the crux and is NOT proved.** Without the transcript-equality binding,
`finalize_other_proof` discharges a `Deferred_values` an attacker CHOSE, as long as it is
internally consistent.

**Not claimed:** this is not a Pickles verifier. P3 (`finalize_other_proof`) and P4 (the
transcript-equality binding — the soundness of P3) are unbuilt; see §Z of the Lean file for the
per-item handoff.

It maps every piece of a Pickles verifier onto **have** (an instantiation of a primitive the K-lanes
already built) vs **new** (recursion machinery with no analog in the single-proof verifier), with
source pins, and turns "meaningfully further than the Kimchi verifier" into an ordered task list.

## Provenance (what was read)

- **We have** (`/Users/ember/dev/breadstuffs`, HEAD `429a5afdce`):
  `metatheory/Dregg2/Circuit/Emit/` — `PastaField` (K1, **Fp AND Fq**), `PastaCurve` (K2, **Pallas AND
  Vesta** + endo), `PastaCurveComplete` (K4a, RCB add both curves), `PastaScalarMul` (K4b, GLV `[k]P`
  both curves), `PastaPoseidon` (K3, Poseidon-over-Pasta sponge, **Fp state only**), `PastaIPA` (K4c,
  the IPA deferral + `sVec_eq_bPoly`), `KimchiVerify` (K5, the single-proof decision, `prevLen = 0`),
  `KimchiRealProofGate` (K5 run on a real proof over `ZMod pN`, `k = 16`). Docs:
  `KIMCHI-VERIFY-SPEC.md`, `MINA-REALITY-GATE.md`.
- **o1-labs `proof-systems`** (`/Users/ember/dev/proof-systems`, HEAD `f6d958dc05`, `git describe`
  `0.7.0-11-gf6d958dc05`; the K-lanes cite `36a8b510` = same `0.7.0` version, different rev — **the
  cited line pins `commitment.rs:426-476` and `ipa.rs:301-502` did NOT drift**). This is the
  polynomial-commitment / IPA backend. **CORRECTION to the task framing:** there is **no Rust
  "pickles crate"** here. The only `pickles`-named target is `o1vm`'s MIPS-zkVM flavour
  (`o1vm/src/pickles/`), unrelated to Step/Wrap. Step/Wrap recursion lives in OCaml (mina) and is
  re-implemented in Rust in openmina (mina-rust). `arrabbiata/` is a *Nova/folding* scheme — a
  different recursion approach, not Pickles.
- **o1-labs `mina`** (`/Users/ember/dev/mina/src/lib/pickles`, vendored source, no local git rev) —
  the **canonical** Pickles (Step/Wrap, tick/tock, `Deferred_values`, `inductive_rule`, the VK).
  > **[ADDED 2026-07-27 — a staleness fact this document did not disclose.]** "No local git rev" was
  > honest and is the right handling; what was not said is **how old the snapshot is**. `~/dev/mina`
  > is **not a git repository at all** (`.git` absent) and its files date to **March 2024** — e.g.
  > `src/lib/pickles/common.ml` is `Mar 25 2024`. **Every OCaml Pickles pin in this document is
  > against a ~2-year-old snapshot, and the whole document describes it in the present tense.**
  > Consequence, stated as the audit stated it (§6.6): the 12 OCaml pins can be **path- and
  > line-checked but not pinned to a revision** — they are **[UNVERIFIED]** against today's upstream.
  > By contrast `~/dev/mina-rust` matches its cited rev exactly, and the `proof-systems` pin
  > `36a8b510cd` was confirmed an ancestor of the checkout's HEAD `f6d958dc05` with an **empty**
  > `git diff` over all six cited files — so the "pins un-drifted" claim for *those* is if anything
  > stronger than this document states.
- **openmina `mina-rust`** (`/Users/ember/dev/mina-rust`, HEAD `82480cd468`, v0.19.0) —
  `crates/ledger/src/proofs/` — a clean **Rust** Pickles verifier (the easiest cross-check; it is
  what actually verifies a real mainnet block/tx today).

---

## TL;DR — the three things this doc must print

### 1. The have-vs-new split

**HAVE — the whole arithmetic floor for BOTH sides of the cycle already exists.** Pickles is two
Kimchi verifiers on the two Pasta curves that check each other. The single-proof lanes were built
field-/curve-generic, so:

| Pickles needs | Already built | Note |
|---|---|---|
| Fp arithmetic (Step scalars) **and** Fq arithmetic (Wrap scalars) | **K1** `PastaField` (both `pN`, `qN`) | both primes forced |
| Pallas point ops (Step-native) **and** Vesta (Wrap-native) + the endo | **K2** `PastaCurve` (both curves, `φ = [λ]`) | both `#guard`'d on-curve |
| RCB complete add + GLV `[k]P` on **both** curves | **K4a/K4b** `PastaCurveComplete`/`PastaScalarMul` | `pallas*`/`vesta*` instantiations |
| the IPA `⟨s,G⟩` sg-accumulation identity | **K4c** `PastaIPA.sVec_eq_bPoly` + `deferral_compression` | **IS** `b_poly_coefficients`; the head start |
| the b-poly evaluator (`b_correct` deferred check) | **K4c** `bEval` | = OCaml `challenge_polynomial` |
| `combined_inner_product` + `ft_eval0` (the `cip`/`ft` deferred checks) | **K5** `combinedInnerProduct`, `ftEval0` | reproduce a real proof's scalars over `ZMod pN` |
| the single-Kimchi-verify decision | **K5** `kimchiVerifyDecision(Field)` | instantiated at the **Step** shape (Vesta-committed, `k=16`) |
| the Fiat–Shamir Poseidon sponge | **K3** `PastaPoseidon` (Fp state) + **`PastaPoseidonFq`** (Fq state, real `fq_kimchi` params, 2026-07-28) | **both flavours now** — one parametric core, the Fp instantiation PROVEN equal to K3's (`core_is_Ref_at_Fp`) |

**NEW — the recursion glue, none of which the single-proof verifier contains:** the two
`Deferred_values` records + the shifted-value field bridge; `finalize_other_proof` (the four-way
cross-check that discharges the opposite proof's non-native scalar arithmetic); the
**transcript-equality binding** that makes the exposed public-input scalars *sound*; `prev_challenges
> 0` (the `RecursionChallenge` fold, retiring the `prevLen = 0` freeze); the base case (dummy proof +
`is_base_case` bypass); the wrap-VK model + `branch_data`/domain selection; and Mina's concrete
instantiation (real Step/Wrap VKs, the tx-snark merge tree, the block step rule, the tip verify).

### 2. The ordered task list (dependency order; effort honest; see §7 for detail)

- **P0** — Instantiate K5 at the **Wrap** shape (Pallas-committed, Fq scalars, `k=15`). *Medium.* **BUILT.**
- **P1** — Close `accumulator_check` (the sg discharge) on top of `sVec_eq_bPoly`. *Small–medium.* **BUILT** (batching wrapper + reduction; terminal MSM still P10).
- **P2** — The `Deferred_values` data model + Type1/Type2 shifted-value bridge. *Small–medium.* **BUILT.**
- **P3** — `finalize_other_proof`: the four re-checks (`xi`/`cip`/`b`/`plonk`) on ONE side. *Medium.* **BUILT 2026-07-28** (`PicklesFinalize` + `PicklesDerivePlonkRealGate`).
- **P4** — **The transcript-equality binding** (`assert_eq_plonk` + digest/bp-challenge equality) —
  the soundness of P3. *Hard — the single hardest buildable piece.*
- **P5** — Mirror P3+P4 to the other side (field swap Fp↔Fq). *Small (mirror).*
- **P6** — `prev_challenges > 0`: the `RecursionChallenge` fold; retire the `prevLen = 0` freeze. *Medium.* **BUILT 2026-07-28.**
- **P7** — Base case + inductive gating (dummy proof, `is_base_case`, `proof_must_verify`). *Small–medium.*
- **P8** — Wrap-VK model + `branch_data`/domain selection + `max_proofs_verified` encodings. *Medium.*
- **P9** — Mina's instantiation: real VKs, tx-snark merge tree, block step rule, protocol-state hash,
  the tip verify (`verify_block` = accumulator_check + native wrap verify). *Medium–large.*
- **P10** — *(terminal, inherited — not "built")* the IPA `msm == 0` opening-soundness floor. *N/A.*

### 3. The single hardest piece

**P4 — the deferred-values cross-check as a SOUND theorem: the transcript-equality binding.** The
whole recursion is sound only because the scalars a proof exposes in its *public input* are pinned,
across a non-native field boundary, to the challenges the group sub-verifier actually sampled —
`assert_eq_plonk` (`wrap_verifier.ml:492-499`), the sponge-digest equality, and the
per-round bulletproof-challenge equality (`wrap_main.ml:430-439`, `step_verifier.ml:1271-1285`),
carried over the `Shifted_value` Type1/Type2 bridge (`common.ml:91-103`). This has **no analog in
K5** (which consumes challenges as given), it spans both fields, and it is where security lives. The
absolute-hardest thing (P10, the IPA opening-soundness floor) is *inherited, not dischargeable* — the
same floor every STARK-backed light client carries — so it is a named terminal residual, not a task.

---

## §A — The Step/Wrap construction (which K-lane instantiates which side)

Pickles is a **2-cycle of two circuits**, each an in-circuit Kimchi verifier for the other, on the
opposite Pasta curve — so each side's scalar-field arithmetic is *native* to the other side. The
cycle is fixed in the backend and the field-witness impls:

- **Tick = Step**, **Tock = Wrap** [S — `mina/src/lib/pickles/impls.ml:5,33-34,146-153`;
  `mina/src/lib/pickles/backend/backend.ml:1-9`]. Field order: `Tick.Field = Fp < Fq = Tock.Field`
  [`impls.ml:51`].
- **Step** is Fp-native, does group ops on **Pallas** (`Pallas.BaseField = Fp`), produces a
  **Vesta**-committed Kimchi proof, **16 IPA rounds** (max degree `2^16`)
  [`mina/src/lib/pickles/step_main_inputs.ml:114-115`; `common.ml:6-14`;
  `kimchi_pasta_basic.ml:16-17`; `mina-rust/crates/ledger/src/proofs/field.rs:90-107`
  (`Parameters = PallasParameters`, `OtherCurve = Vesta`, `NROUNDS = 16`); `mod.rs:33-34`].
- **Wrap** is Fq-native, does group ops on **Vesta** (`Vesta.BaseField = Fq`), produces a
  **Pallas**-committed Kimchi proof, **15 IPA rounds** (max degree `2^15`)
  [`mina/src/lib/pickles/wrap_main_inputs.ml:104-105`; `field.rs:109-125`
  (`Parameters = VestaParameters`, `OtherCurve = Pallas`, `NROUNDS = 15`)].
- **Direction:** **Step** proves the application statement AND recursively verifies **0/1/2 previous
  Wrap proofs** [`mina/src/lib/pickles/step_main.ml:28-121`]; **Wrap** wraps **exactly one** Step
  proof [`mina/src/lib/pickles/wrap_main.ml:401-414`]. The object a node consumes for a block/tx is
  the **outermost Wrap proof**, verified as a single Tock/Pallas Kimchi proof
  [`mina/src/lib/pickles/verify.ml:132,206,210`; `mina-rust/.../verification.rs:499-521`].

**The K-lane mapping (both sides are already floored):**

| Pickles side | field | native curve (in-circuit point ops) | commits its proof on | K-lanes that instantiate it |
|---|---|---|---|---|
| **Step** (tick, 16 rounds) | Fp (`pN`) | Pallas | Vesta | K1(Fp), K2(Pallas)+K4a(`pallasCompleteAdd`)+K4b(`pallasLadder`), K3(Fp sponge), K4c, **K5 (already at this shape)** |
| **Wrap** (tock, 15 rounds) | Fq (`qN`) | Vesta | Pallas | K1(Fq), K2(Vesta)+K4a(`vestaCompleteAdd`)+K4b(`vestaLadder`), **K3 Fq-sponge = residual**, K4c, **K5 re-instantiated (P0)** |

The key observation: **K1/K2/K4a/K4b already cover BOTH curves and BOTH fields** (they were authored
generic and instantiated twice). The only arithmetic gap is **K3's sponge, built for the Fp state
only** — the Wrap side needs the same Poseidon permutation over the Fq state (a mechanical mirror,
already a named K3/`KimchiVerify` §12.3 residual). Our `KimchiRealProofGate` (`k=16`, Vesta-committed,
Fp scalars) is exactly a **Step-shape** proof; verifying a real Mina block additionally needs the
**Wrap-shape** verify (P0).

---

## §B — The DEFERRED-VALUES cross-check (the heart; genuinely NEW)

**The principle** [S — `mina/src/lib/pickles/composition_types/composition_types.ml:24-32`]: a
verifier circuit does the *group* part of verifying the other proof, but the *scalar-field*
arithmetic (combined inner product, the b-poly evaluation, the plonk-derived scalars) is in a field
**non-native to that circuit**. So it does not compute those; it **exposes them in its own public
input** as `Deferred_values`, and the **next circuit — which runs on the other curve, where that
field is native — recomputes and checks them**. Each proof defers its own scalar arithmetic one hop.

### The two records (symmetric, one per curve)

**Wrap-side `Deferred_values`** carries the **Step proof's Fp scalars** [S —
`composition_types.ml:215-268`], **Step-side** carries the **Wrap proof's Fq scalars** [S —
`composition_types.ml:1152-1164`]. In Rust: `DeferredValues<F>` +`Plonk<F>`
[`mina-rust/.../public_input/prepared_statement.rs:14-35`], and the in-circuit `Unfinalized`
[`mina-rust/.../unfinalized.rs:102-116`]. Field-by-field, with where each is **re-checked**:

| Deferred field | what it is | recomputed + checked by (in-circuit / native) |
|---|---|---|
| `plonk = {alpha, beta, gamma, zeta}` | the four Fiat–Shamir IOP challenges | re-squeezed; bound by `assert_eq_plonk` (§B binding) |
| `plonk.{zeta_to_srs_length, zeta_to_domain_size, perm}` | derived scalar exponentiations / perm scalar | `plonk_checks_passed` via `derive_plonk` [`step.rs:874`; `plonk_checks.rs:238-271`; OCaml `wrap_verifier.ml:1028-1037`] |
| `combined_inner_product` | `Σ_i Σ_j r^i ξ^j f_j(pt_i)` | `combined_inner_product_correct` — recompute via `ft_eval0` + fold all evals with ξ [`step.rs:748-845`; OCaml `wrap_verifier.ml:951-1009`]. **Reuses K5 `combinedInnerProduct`/`ftEval0`.** |
| `b` | `challenge_poly(ζ) + r·challenge_poly(ζω)` | `b_correct` [`step.rs:854-862`; OCaml `wrap_verifier.ml:1015-1026`]. **Reuses K4c `bEval` (= `challenge_polynomial`, `wrap_verifier.ml:14-35`).** |
| `xi` | the poly-combining ("polyscale") challenge | `xi_correct = field.equal(squeeze(), xi)` [`step.rs:694-697`; OCaml `wrap_verifier.ml:895-902`] |
| `bulletproof_challenges` | the `k` IPA round challenges | endo-mapped, feed `b_correct`; **cross-checked against the group verifier's** [`step.rs:1759-1772`] |
| `branch_data` *(wrap only)* | `{proofs_verified, domain_log2}` | selects the eval domain; validated in `run_checks` [`step.rs:598-604`; `verification.rs:644-651`] |

### Emit vs re-check (the symmetry — this is the new formal content)

Two `incrementally_verify_proof` (emit) + two `finalize_other_proof` (discharge), one per curve:

- **Wrap.`incrementally_verify_proof`** [`wrap_verifier.ml:501-732`] samples β,γ,α,ζ, builds `ft_comm`,
  runs the IPA **group** check `check_bulletproof`, and **binds** the sampled challenges to the
  exposed deferred `plonk` via `assert_eq_plonk` [`wrap_verifier.ml:492-499`]. → emits the **Step
  proof's Fp** deferred values.
- **Step.`finalize_other_proof`** [`step_verifier.ml:887-1149`; Rust `step.rs:519-887`, AND of the
  four sub-checks at `step.rs:876-884`] recomputes and **discharges** those Fp values (`Shifted_value`
  **Type1** over Fp). → closes the Wrap→Step hop.
- Mirror: **Step.`incrementally_verify_proof`** [`step_verifier.ml:498-517`] emits the **Wrap proof's
  Fq** deferred values; **Wrap.`finalize_other_proof`** [`wrap_verifier.ml:820-1049`, Type2 over Fq]
  discharges them. → closes the Step→Wrap hop.
- **Native mirror (the tip):** `expand_deferred` recomputes, out of circuit, exactly what the next
  circuit would check [OCaml `wrap_deferred_values.ml:19-210`; Rust `step.rs:1915-2072`,
  `verification.rs:676-719`]. This is the concrete reference a Lean deferred-values model must match.

**Reuse payoff:** three of the four `finalize_other_proof` sub-checks are already built — `b_correct`
is K4c `bEval`; `combined_inner_product_correct` is K5 `combinedInnerProduct` + `ftEval0`;
`xi_correct` is one sponge squeeze (K3) + a field equality. The genuinely new work is (a) the
`plonk_checks`/`derive_plonk` scalar derivations, (b) the **binding** (§ next), and (c) the
`Shifted_value` Type1/Type2 encoding that lets an Fp value be carried and compared inside an
Fq-native circuit [OCaml `common.ml:91-103`; `step_verifier.ml:826` / `wrap_verifier.ml:789-791`].

### The binding (why the exposed scalars are sound) — the single hardest piece

The public-input `Deferred_values` are attacker-chosen bytes until they are pinned to the group
sub-verifier. That pinning is: `assert_eq_plonk` (sampled β,γ,α,ζ **=** exposed `plonk`)
[`wrap_verifier.ml:492-499`, called `:717-731`]; the sponge-digest equality [`wrap_main.ml:430-432`];
and the per-round bulletproof-challenge equality [`wrap_main.ml:433-439`; `step_verifier.ml:1271-1285`].
Proving `finalize_other_proof ∧ (these asserts) ⟹ the deferred scalar arithmetic is genuinely the
opposite proof's` — across the non-native field via the shifted-value bridge — is the new soundness
theorem, and the hardest buildable item (P4).

---

## §C — The accumulator / sg bulletproof accumulation (mostly HAVE)

This is the **head start**. The deferred `⟨s,G⟩` MSM (the IPA cost center) is not recomputed each
recursion step; the `k` round challenges are accumulated and the `2^k`-term MSM is discharged once.
The math is exactly **K4c**:

- **`sVec_eq_bPoly`** (`PastaIPA.lean:113`) is the identity `Σ_i (sVec cs)_i · x^i = ∏_j (1 + cs_j
  x^{2^…})` — i.e. the `2^k` s-vector is the b-poly coefficient vector reconstructible from `k`
  challenges. This mirrors `b_poly` [`proof-systems/poly-commitment/src/commitment.rs:426-436`] and
  `b_poly_coefficients` (the `s ↦ s ++ c·s` doubling) [`commitment.rs:464-476`], and proof-systems'
  own consistency test [`commitment.rs:912-939`]. **Pins verified un-drifted at HEAD `f6d958dc05`.**
- The discharge is `sg == MSM(urs.g, b_poly_coefficients(challenges))`, batched across proofs, one
  pairing-free `msm(points, scalars) == 0` [Rust `accumulator_check.rs` (whole, 64 lines) →
  `urs_utils.rs:11-68`, `b_poly_coefficients` at `:54`, `msm == 0` at `:67`; OCaml
  `Ipa.Step.accumulator_check`, `verify.ml:135-143`, `common.ml:197-211`]. In `SRS::verify` the split
  is the `sg` term [`ipa.rs:410-411`] plus `⟨sg_rand·s, G⟩` [`ipa.rs:402,419-424`].
- The deferred obligation carried across recursion is `RecursionChallenge { chals, comm }` —
  "the accumulated commitment `U = ⟨h,G⟩` … the 'deferred' part of IPA verification"
  [`proof-systems/kimchi/src/proof.rs:213-218,225,241,437-442`].

**Residual to close (P1):** K4c proves the *identity* and the *compression* (`deferral_compression`);
what remains is the batching wrapper — the RNG/Fiat–Shamir batching scalars `rs` [`urs_utils.rs:25-32`;
`ipa.rs:356-357`, the `[R-design]` deviation of `KIMCHI-VERIFY-SPEC.md`] and the multi-proof batch —
plus the terminal `msm == 0` itself, which is the inherited IPA/FRI opening-soundness floor (P10),
not dischargeable in-kernel.

---

## §D — Mina's specific instantiation (what verifying a REAL block/tx needs; NEW plumbing)

**The wrap VK = a Kimchi verifier index over Pallas.** `Poly.t = {max_proofs_verified,
actual_wrap_domain_size, wrap_index : Plonk_verification_key_evals, wrap_vk}` [S —
`mina/src/lib/pickles_base/side_loaded_verification_key.ml:140-157`]. `index_to_field_elements`
[`:159-183`] serializes `wrap_index` as **8 commitment groups**: `sigma_comm(7) ++
coefficients_comm(15) ++ [generic; poseidon; complete_add; mul; emul; endomul_scalar]` — these ARE
the wrap verifier index. Reconstruction of the runnable `Impls.Wrap.Verification_key` (Tock/Pallas):
`of_repr` [`mina/src/lib/pickles/side_loaded_verification_key.ml:206-262`] — `max_poly_size = 2^15`
[`:234`], `prev_challenges = 2` ("Wrap_hack", `:236`), `lookup_index = None` [`:255`].

**Domains + widths a verifier must know** [S]: `max_proofs_verified ∈ {0,1,2}`
[`pickles_base/proofs_verified.ml:5-17`], encoded in-circuit as a 2-bit prefix mask or 3-bit one-hot
[`:70-143`]; wrap domain `∈ {2^13, 2^14, 2^15}` keyed by `proofs_verified` (`0→13, 1→14, 2→15`)
[`common.ml:27-45`]; step blinding domain `2^6`, wrap `2^7` [`step_main_inputs.ml:97`,
`wrap_main_inputs.ml:101`]; the wrap statement public-input layout (5 Fp + 2 challenge + 3
scalar-challenge + 3 digest + 16 bulletproof-challenge + 1 branch-data + 8 feature-flag)
[`composition_types.ml:814-943`]; `branch_data` packs `{2-bit proofs_verified, 8-bit domain_log2}`
into one field [`branch_data.ml:45-84,135-136`].

**The real VKs + the tx-snark** [S — mina-rust]: the mainnet/devnet **blockchain** and **transaction**
verifier indices are embedded JSON [`verifiers.rs:176-279`, files `crates/ledger/src/proofs/data/
{mainnet,devnet}_{blockchain,transaction}_verifier_index.json`]; SRS via the **generic**
`SRS::<F::OtherCurve>::create(<F as FieldWitness>::Scalar::SRS_DEPTH)`
[`crates/ledger/src/verifier/mod.rs:42`, also `:55`].
**[CORRECTED 2026-07-27 — this read `SRS::<Vesta>::create(2^15)`, an instantiation the code does not
produce.]** The call is generic, and with `Fp::SRS_DEPTH = 32768` / `Fq::SRS_DEPTH = 65536`
(`field.rs:106,127`) and `Fp::OtherCurve = Vesta` / `Fq::OtherCurve = Pallas` (`field.rs:93,113`) it
yields **`SRS::<Vesta>::create(65536)`** (from `Fp`, whose `Scalar = Fq`) or
**`SRS::<Pallas>::create(32768)`** (from `Fq`, whose `Scalar = Fp`). The old rendering **paired the
wrong curve with the wrong depth**. The one concrete instantiation in the tree is
`SRS::<Pallas>::create(degree)` at `verifiers.rs:407`. Consistent with §A and with
`kimchi_pasta_basic.ml:16-17` (`Wrap = Nat.N15`, `Step = Nat.N16`) and
`mod.rs:33-34` (`BACKEND_TICK_ROUNDS_N = 16`, `BACKEND_TOCK_ROUNDS_N = 15`): **Step is Fp-native,
committed on Vesta, k = 16, SRS 2^16; Wrap is Fq-native, committed on Pallas, k = 15, SRS 2^15.**
The transaction snark is a **merge tree**: a
base leaf is `InductiveRule::empty` (zero previous proofs) [`transaction.rs:4289`], and `merge_main`
recursively combines two child statements/proofs 2-to-1 [`merge.rs:36`]. The **block** step rule wires
**two** previous proofs — the previous blockchain-state proof and the txn-snark proof —
[`block.rs:1788-1799`], with the genesis base case at `block.rs:1684,1784-1786`.

---

## §E — Base case + inductive structure (NEW gating)

- **Inductive rule** [S — `mina/src/lib/pickles/inductive_rule.ml:9-23,103-120`]:
  `Previous_proof_statement = {public_input; proof; proof_must_verify : Boolean}`; a rule has
  `prevs` (tags of previous proofs) + `main`.
- **Base case = a previous slot with `proof_must_verify = false`, fed a dummy proof.** The verify gate
  is `verified && finalized ||| not should_verify` [OCaml `step_main.ml:121`; Rust
  `step.rs:1893-1894` `verified.and(finalized).or(should_verify.neg())`] — a non-verifying slot passes
  unconditionally. `is_base_case = not should_verify` also **bypasses the bulletproof-challenge
  equality**, substituting the exposed challenge for the recomputed one [`step_verifier.ml:1281`; Rust
  `step.rs:1765-1772,1881`]. Dummy content: `dummy.ml:9-54` (`Ipa.{Wrap,Step}.{challenges,sg}`), Rust
  `unfinalized.rs:286-297,308-368`, `dummy/mod.rs` (`trivial_vk.bin`, `sideloaded_proof.bin`).
- **The tip (end-to-end real verify)** [OCaml `verify.ml:21-213`; Rust `verification.rs:750-785`
  `verify_block`, `:858-896` `verify_impl`]: (1) natively recompute the Tick deferred values
  (`expand_deferred`); (2) `accumulator_check` (the §C sg check on Vesta); (3) reconstruct the wrap
  statement public input and `batch_verify` the **Wrap (Pallas) Kimchi proof**. Steps (2)+(3) are HAVE
  (K4c + K5); step (1) is the NEW deferred-values native mirror.
- **Where `prev_challenges` re-enters native Kimchi verify** (the `prevLen = 0` frontier) [Rust
  `prover.rs:30-177` `make_padded_proof_from_p2p`]: `old_bulletproof_challenges` +
  `challenge_polynomial_commitments` become `RecursionChallenge<Pallas>` folded into the outer proof's
  combined-inner-product relation, padded to 2 (Wrap_hack). With `prev_challenges = 0` this term
  vanishes; modeling the fold + padding is P6.

---

## §7 — The ordered task list (detail: what to build, effort, have-vs-new)

Discipline reminder: **House Law #1** — every constraint/decision below is **Lean-authored** (the
K-lanes are Lean gadgets/`@[export]` decisions; Rust only calls the artifact). None of this is a Rust
AIR. State the substrate out loud at task #1.

**Phase 0 — instantiate the two Kimchi verifiers on both curves (mostly HAVE)**

- **P0 — K5 at the Wrap shape.** *Medium.* Re-instantiate `kimchiVerifyDecision(Field)` for a
  Pallas-committed, Fq-scalar, `k=15` proof (the object a node actually verifies). K5 is field-generic
  so the decision body is reuse; the real work is the **Fq-state Poseidon sponge** (mirror K3 to the
  Fq permutation — `KimchiVerify` §12.3 residual) and a **real Wrap-proof fixture** (extract from a
  mainnet block via mina-rust's `verify_block` path). *Have:* K1(Fq), K2(Vesta/Pallas), K5 body.
  *New:* the Fq sponge instance, the wrap VK domains (§D), the wrap fixture.
- **P1 — Close `accumulator_check`.** *Small–medium.* On top of `sVec_eq_bPoly`/`deferral_compression`,
  add the batching scalars + multi-proof batch to model `batch_dlog_accumulator_check` down to the
  `msm == 0` [`urs_utils.rs:11-68`]. *Have:* the identity (K4c). *New:* the batching wrapper; the
  terminal MSM is the inherited floor (P10).

**Phase 1 — the deferred-values cross-check (the genuinely NEW core)**

- **P2 — The `Deferred_values` data model + shifted-value bridge.** *Small–medium.* The two records
  [`composition_types.ml:215-268,1152-1164`], `Plonk` minimal/in-circuit [`:45-61,102-123`], and the
  `Shifted_value` Type1/Type2 encoding that carries an Fp scalar inside an Fq circuit and back
  [`common.ml:91-103`]. *New*, but pure data + one algebraic encoding.
- **P3 — `finalize_other_proof` (one side).** *Medium.* The four checks discharging the Step proof's
  Fp values inside a Wrap circuit: `xi_correct` (K3 squeeze + eq), `combined_inner_product_correct`
  (**K5** `combinedInnerProduct`+`ftEval0`), `b_correct` (**K4c** `bEval`), `plonk_checks_passed`
  (`derive_plonk` — new scalar derivations) [`wrap_verifier.ml:820-1049`; `step.rs:519-887`]. *Have:*
  3 of 4 check cores. *New:* `derive_plonk`, the assembly, the accept theorem + a tamper falsifier.
- **P4 — The transcript-equality binding (the hardest piece).** *Hard.* `assert_eq_plonk`
  [`wrap_verifier.ml:492-499`] + sponge-digest equality + per-round bulletproof-challenge equality
  [`wrap_main.ml:430-439`; `step_verifier.ml:1271-1285`], proven to pin the public-input deferred
  scalars to the group sub-verifier across the non-native field. This is the soundness of P3 and the
  new formal content with no K5 analog.
- **P5 — Mirror to the other side.** *Small.* Step-discharges-Wrap (Fp↔Fq swap, Type1↔Type2)
  [`step_verifier.ml:887-1149`]. Mechanical once P3/P4 exist.

**Phase 2 — recursion structure + Mina specifics (NEW plumbing)**

- **P6 — `prev_challenges > 0`.** *Medium.* Retire K5's `shapeOk … decide (prevLen = 0)` freeze: fold
  `RecursionChallenge` b-poly evals into the transcript (C3) + `combined_inner_product` (C8), model
  `messages_for_next_{step,wrap}_proof` / `old_bulletproof_challenges` accumulation + Wrap_hack padding
  to 2 [`prover.rs:30-177`; `composition_types.ml:369,819`]. *Have:* K4c b-poly. *New:* the fold + the
  passthrough/accumulation.
- **P7 — Base case + inductive gating.** *Small–medium.* The dummy proof, `is_base_case` bypass,
  `proof_must_verify` gate, genesis base case [`step_main.ml:36-37,106,121`; `dummy.ml`; `block.rs:1684`].
- **P8 — Wrap-VK model + domains.** *Medium.* `index_to_field_elements` (8 commitment groups),
  `of_repr` reconstruction, `wrap_domains` {2^13,2^14,2^15} by `proofs_verified`, the one-hot/prefix
  masks, `branch_data` packing [`side_loaded_verification_key.ml`; `proofs_verified.ml`;
  `common.ml:27-45`; `branch_data.ml`]. Mechanical serialization + domain selection.
- **P9 — Mina's concrete instantiation.** *Medium–large.* Load the real mainnet/devnet blockchain +
  transaction verifier indices [`verifiers.rs:176-279`, `data/*.json`]; model the tx-snark merge tree
  (`InductiveRule::empty` leaf + `merge_main`) and the block step rule (2 prevs); hash the protocol
  state; wire the tip `verify_block` = `accumulator_check` (P1) + native Wrap verify (P0)
  [`verification.rs:750-785`]. Lots of concrete plumbing, each piece mechanical; this is what makes it
  a real **Mina light client** (and, per `MINA-KIMCHI-VERIFIER-PLAN.md`, transitively any chain
  settling a Kimchi proof to Mina).

**Phase 3 — the terminal floor**

- **P10 — The IPA/FRI opening-soundness floor.** *Not built — inherited.* `msm == 0` [`ipa.rs:501`]
  is the same undischarged floor `KimchiVerify` §12.1 and every STARK-backed light client carries. It
  is the honest terminal residual, named — not a task with an effort.

---

## §8 — Honesty ledger (what this doc does and does not claim)

- The **arithmetic floor for both Step and Wrap already exists** (K1 both fields, K2 both curves,
  K4a/b both curves) — the two-curve requirement is *instantiation*, not new algebra. The one
  arithmetic gap is K3's Fq-state sponge (P0), already a named residual.
- The **sg-accumulation math is proven** (K4c `sVec_eq_bPoly`); `accumulator_check` is a batching
  wrapper (P1) over it plus the inherited terminal MSM (P10).
- The **genuinely new work is recursion glue** — the deferred-values cross-check (P2–P5), the
  `prev_challenges` fold (P6), the base case (P7), the wrap-VK/domains (P8), and Mina's concrete
  wiring (P9). Of these, the **binding that makes the cross-check sound (P4) is the single hardest**
  buildable piece.
- Nothing here discharges the terminal IPA/FRI opening-soundness floor (P10). "Verifies a real Mina
  block" end-to-end still rests on it, exactly as the single-proof `KimchiVerify` does. Describe any
  Pickles verify at that resolution.
