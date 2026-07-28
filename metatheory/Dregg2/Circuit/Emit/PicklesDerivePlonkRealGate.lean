/-
# `PicklesDerivePlonkRealGate` — P3's `derive_plonk`, DIFFERENTIAL against o1-labs' own scalars

## Why this file exists, and what it is NOT

`PicklesFinalize` (the same day, another lane) authors P3: the `derive_plonk` arms, the four-way
`finalizeOtherProof`, a universally-quantified completeness theorem, the tamper poles, and the
MEASURED reading of `plonk_checks::checked` (its comparison list is `[perm]` — one entry — in both
implementations). **That file is the P3 authoring site and nothing here re-authors any of it.**
Its own §"WHAT IS NOT CLAIMED" says the concrete pole runs at `ZMod 97` with an 8-point domain,
because a negative pole needs a concrete ring and no generic theorem supplies one.

This file supplies the other half: **the same derivations, on a REAL Kimchi proof, checked against
values o1-labs' code computed.** It defines no `derive_plonk` of its own — it instantiates
`PicklesFinalize`'s `permScalarR`, `zetaToDomainSizeR` and `zetaToSrsLengthR` at the
`prev_challenges = 2` fixture of `KimchiRecursionGate`
(`metatheory/kimchi_p6_prev2_proof.json`, a proof `kimchi::verifier::verify` accepts).

What the differential adds that a `ZMod 97` pole cannot:

* `perm` is compared against **`ConstraintSystem::perm_scalars`** (`permutation.rs:392-430`) —
  o1-labs' own function, run by the extractor on this proof. So
  `derivePlonk_perm_is_K5_permScalar` is not only an identity between two Lean definitions; the
  value both compute is the value their Rust computes.
* `zkp(ζ)` is compared against the index's `permutation_vanishing_polynomial_m`, which is what
  makes the `perm` comparison a differential rather than a restatement of K5's own formula.
* `zeta_to_srs_length` is checked at the **REAL `max_poly_size = 65536`**, through the `sqIter`
  ladder, so the exponent is intact rather than reduced to something kernel-cheap.
* `b_correct`'s value is compared against o1-labs' **`b_poly`** on the endo-mapped IPA round
  challenges — K4c's `bEval` against their implementation, at `k = 16`.

## What this does NOT establish

Nothing about soundness. P4 — the transcript-equality binding — is `PicklesFinalize`'s §P4 and is
MEASURED there, not proved; without it `finalize_other_proof` discharges a `Deferred_values` an
attacker chose, as long as it is internally consistent. And the fixture is a **Step-shape**
(Vesta-committed, `k = 16`) Kimchi proof, not a Pickles statement: there is no exposed
`Deferred_values` record here to compare against, only the derivations. The real Mina Wrap object
lives in `MinaRealBlockGate`.

## Axiom hygiene

`#assert_namespace_axioms`-clean; no `sorry`, no `native_decide`.

NEW standalone file. Import line for the root (do NOT edit `Dregg2.lean` from a lane):
`import Dregg2.Circuit.Emit.PicklesDerivePlonkRealGate`
-/
import Dregg2.Circuit.Emit.PicklesFinalize

namespace Dregg2.Circuit.Emit.PicklesDerivePlonkRealGate

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaIPA (bEval)
open Dregg2.Circuit.Emit.KimchiVerify (zkPolyR sqIter sqIter_eq bEvalSq bEvalSq_eq_bEval)
open Dregg2.Circuit.Emit.PicklesFinalize (permScalarR zetaToDomainSizeR zetaToSrsLengthR)

set_option autoImplicit false
set_option maxRecDepth 4000

abbrev Fp := ZMod pN

/-! ## §1 — The real proof's values (the `KimchiRecursionGate` fixture). -/

def N : Nat := 32
/-- `log2 max_poly_size`; `max_poly_size = 65536` for this index. -/
def SRSLOG2 : Nat := 16
def OMEGA : Fp := (5772676229766982871441818714777438643955918462675337216809979342233538361548 : Fp)
def ZETA : Fp := (9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp)
def BETA : Fp := (207191000514447567911742581240638307123 : Fp)
def GAMMA : Fp := (212090136106687690782051664536927829615 : Fp)
def UU : Fp := (4029829395372224514861218209502654028970733683372586849261102654660655230746 : Fp)
def ZETAW : Fp := ZETA * OMEGA
/-- `α^21` — `PERM_ALPHA0` (`plonk_checks.ml:218`), the alpha the permutation block starts at. -/
def A0 : Fp := (27127124423890897709471374909862003647116284891598004634947951661445215106972 : Fp)
def ZZW : Fp := (28413617518552286544998492970805240901385119401424696642596595430411951585052 : Fp)
def WZ : List Fp :=
  [(8571631469098177892965262307737168137771792367786739004103898273114062670285 : Fp), (10498381543777762020631802150870211762003709095234594899293761913383977328132 : Fp), (12226728938788036639480999661017599962364448487055773636731396600382488581196 : Fp), (5707378856581365824447872698174223853012679496314514995080294844551197875781 : Fp), (22725874598313407611264545143412740301204078004768953753255037423937170617111 : Fp), (4871479349103771792541760605837981763914640577439617428271699200123592435433 : Fp), (27468350421930086744186305050869116760687727483048562429320842326053428252096 : Fp), (7852482877623881408152923783758059858364119588906157757585163529302380664242 : Fp), (17712610987890872765251184085675488375257638256291780270440669271574683981428 : Fp), (2809562589381152287364102553008182578660398152321259224004064607433802554541 : Fp), (12725230491694275861102765549546304969337542628803076138803407761907282369647 : Fp), (7651341330198429039504127155456038660566040141866927464365340559790747382195 : Fp), (17789473230049229564004961520174629180440520442392892001760357346090014021052 : Fp), (13124202080984823270185709766370374334406100446141282230912582756427552375713 : Fp), (7807586433423507120930971828781208694777921411506294439127181997722987231222 : Fp)]
def SZ : List Fp :=
  [(9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp), (20222061864450867255710902152931194513000988722830211032226108406269483319592 : Fp), (7476278879333289444878543626839011543831373682982983342588005018880166909098 : Fp), (12928632103618224043023991788970990076655059964985295017406175964126481123944 : Fp), (5818431057815805527205661029874349337966454987084644709243167839448640882189 : Fp), (9554744463517008369767910484965602220431146377570871885328571004953370013735 : Fp)]
/-- The `k = 16` ENDO-MAPPED IPA round challenges (`ipa.rs:1261-1275`) — the ones `b_poly`
consumes, not the raw prechallenges. -/
def IPACHALS : List Fp :=
  [(5056624989650071945510843492349367812655828174568651286218330639906126361486 : Fp), (7466629998166954248924030500188715388747660444003779384927335439335555330832 : Fp), (14105317996238849186514750124126394825539719100082994500426704338842395836499 : Fp), (4090484525785319220729443785077395385330308644175387324216003198837598669024 : Fp), (8000110848951949682439215651514254615393689943087120121888642610606560900601 : Fp), (14914435723144649742991829309417976473412427436123855412014671817970806799302 : Fp), (8741986856067679707381697727096638922600943514580644531191308109511508052855 : Fp), (5075491121909819361982177498266972006683567168886169162665934665228822953126 : Fp), (21509154994384831386291527152782981435165811490039225395163916198565580470767 : Fp), (18059389524567045131188606209645871133666393320454406145335626893148901569366 : Fp), (11645741172093393772936208279125478149695271311583431420892219722537648587365 : Fp), (9849436060144484658495570381039983122374165952929208375378223699925925899453 : Fp), (11983473014393898554416407521711858140096251518262962821643767835773120793849 : Fp), (7854208093664783017073258578553263970997306397774495842793061497769652039535 : Fp), (4943808111387688341134512802064527713645781730967684443406332787732340715337 : Fp), (20408912629520259399184599790221141686348286578950587440087173216040983656853 : Fp)]
/-- ⚑ The values o1-labs' code computed on this proof: `perm` from
`ConstraintSystem::perm_scalars` (`permutation.rs:392-430`), `zkp(ζ)` from the index's
`permutation_vanishing_polynomial_m`, the two exponentiations, and `b` from `b_poly`. -/
def PERM : Fp := (3689186282540999277776618142275107381498133388538252043432910702427755744802 : Fp)
def ZETA_TO_N : Fp := (28086548619216293777210234024331763939734207338256053651617457673367727816099 : Fp)
def ZETA_TO_SRS : Fp := (7945674355346637519592705100895268306497308077000118737506721895482606305170 : Fp)
def ZKP : Fp := (5695743597299628848924088017028051764937220979982039214838438968246638385787 : Fp)
def BDEF : Fp := (4855498836239450438294765887489322664852053920215454396392742509652073569254 : Fp)

/-! ## §2 — The differential. -/

/-- ⚑ **`derive_plonk_matches_rust`** — `PicklesFinalize`'s three `derive_plonk` arms reproduce the
values o1-labs' code computed on a real proof. `zkp(ζ)` first, because it is the input that makes
`perm` a differential and not a restatement of K5's own formula. -/
theorem derive_plonk_matches_rust :
    zkPolyR N OMEGA ZETA = ZKP
    ∧ permScalarR N OMEGA ZETA BETA GAMMA A0 WZ SZ ZZW = PERM
    ∧ zetaToDomainSizeR N ZETA = ZETA_TO_N
    ∧ zetaToSrsLengthR SRSLOG2 ZETA = ZETA_TO_SRS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **`zeta_to_srs_is_the_real_power`** — and the ladder value really is `ζ^65536`: `sqIter_eq`
proves the ladder computes the power for every base and height, so this is an equation about
`ζ ^ 2^16` with the exponent intact, not 16 squarings that happen to agree. -/
theorem zeta_to_srs_is_the_real_power : ZETA ^ (2 ^ SRSLOG2 : Nat) = ZETA_TO_SRS := by
  rw [← sqIter_eq]
  exact derive_plonk_matches_rust.2.2.2

/-- **`derive_plonk_discriminates`** — every input `perm` reads moves it: β, γ, α^21, `z(ζω)`, a σ
evaluation, a witness evaluation, and ζ (through `zkp`). Per-argument non-vacuity on the real
values, which is what a generic completeness theorem cannot give. -/
theorem derive_plonk_discriminates :
    permScalarR N OMEGA ZETA (BETA + 1) GAMMA A0 WZ SZ ZZW ≠ PERM
    ∧ permScalarR N OMEGA ZETA BETA (GAMMA + 1) A0 WZ SZ ZZW ≠ PERM
    ∧ permScalarR N OMEGA ZETA BETA GAMMA (A0 + 1) WZ SZ ZZW ≠ PERM
    ∧ permScalarR N OMEGA ZETA BETA GAMMA A0 WZ SZ (ZZW + 1) ≠ PERM
    ∧ permScalarR N OMEGA ZETA BETA GAMMA A0 WZ (SZ.set 4 0) ZZW ≠ PERM
    ∧ permScalarR N OMEGA ZETA BETA GAMMA A0 (WZ.set 2 0) SZ ZZW ≠ PERM
    ∧ permScalarR N OMEGA (ZETA + 1) BETA GAMMA A0 WZ SZ ZZW ≠ PERM
    ∧ zetaToSrsLengthR 15 ZETA ≠ ZETA_TO_SRS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`b_correct_matches_rust`** — K4c's `bEval` reproduces o1-labs' `b_poly` in the `b_correct`
combination `challenge_poly(ζ) + r·challenge_poly(ζω)` (`step.rs:855-859`;
`wrap_verifier.ml:1019-1022`) at `k = 16`, and moves when a round challenge, the evalscale, or the
evaluation-point order moves. -/
theorem b_correct_matches_rust :
    bEvalSq ZETA IPACHALS + UU * bEvalSq ZETAW IPACHALS = BDEF
    ∧ bEvalSq ZETA (IPACHALS.set 9 0) + UU * bEvalSq ZETAW (IPACHALS.set 9 0) ≠ BDEF
    ∧ bEvalSq ZETA IPACHALS + (UU + 1) * bEvalSq ZETAW IPACHALS ≠ BDEF
    ∧ bEvalSq ZETAW IPACHALS + UU * bEvalSq ZETA IPACHALS ≠ BDEF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`b_correct_is_K4c_bEval`** — and the value checked above IS K4c's `bEval`, the function
`PicklesFinalize.bActualOf` and `PastaIPA.sVec_eq_bPoly` are about. `bEvalSq` is the same
b-polynomial up the squaring ladder (`bEvalSq_eq_bEval`, proved for every point and every challenge
list) and exists only because `Monoid.npow` at `2^15` is 32768 kernel recursion steps — a COST
device, not a second definition. No `decide` here. -/
theorem b_correct_is_K4c_bEval :
    bEval ZETA IPACHALS + UU * bEval ZETAW IPACHALS = BDEF := by
  rw [← bEvalSq_eq_bEval, ← bEvalSq_eq_bEval]
  exact b_correct_matches_rust.1

/-! ## §3 — Residuals.

1. **P4 is not touched here and is not touched there.** `PicklesFinalize` §P4 MEASURES the
   transcript-equality binding — what it pins, what it leaves free, and that each assert family is
   load-bearing — and states in its own §Z that this is not soundness. Nothing in this file bears
   on it. Without P4, `finalize_other_proof` discharges a `Deferred_values` an attacker chose.
2. **No exposed `Deferred_values` here.** The fixture is a Kimchi proof, not a Pickles statement,
   so only the DERIVATIONS are checked. The four-way assembly and its acceptance live in
   `PicklesFinalize`; the real Mina Wrap object lives in `MinaRealBlockGate`.
3. **Step shape only.** Vesta-committed, `k = 16`. The Fq/Type2 mirror is P5.
4. **`plonk_checks::checked` compares only `perm`** — `PicklesFinalize` §P3.4's measurement. The
   two exponentiations are DERIVED and then not compared by the upstream check, so their
   differential here is evidence about the derivation, not about a check that runs.
5. **The IPA/FRI opening-soundness floor (P10)** is inherited, undischarged. -/

#assert_namespace_axioms Dregg2.Circuit.Emit.PicklesDerivePlonkRealGate

end Dregg2.Circuit.Emit.PicklesDerivePlonkRealGate
