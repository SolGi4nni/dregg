/-
# `PicklesFinalizeOtherProof` — **P3**: `derive_plonk`, and the four-way discharge assembled

## What this file is

`docs/PICKLES-VERIFIER-SCOPE.md` P3: `finalize_other_proof` (`wrap_verifier.ml:820-1049`; Rust
`step.rs:519-887`, the AND of four sub-checks at `step.rs:876-884`) discharges the OPPOSITE proof's
scalar arithmetic inside a circuit where that field is native. Three of its four check cores were
already built and are REUSED here rather than re-derived:

| sub-check | core | where it came from |
|---|---|---|
| `xi_correct` (`step.rs:694-697`) | one sponge squeeze + a field equality | K3 / `PastaPoseidonFq` |
| `combined_inner_product_correct` (`step.rs:748-845`) | `cipR` + `ftEval0R` | **K5** |
| `b_correct` (`step.rs:854-862`) | `bEval` (= `challenge_polynomial`, `wrap_verifier.ml:14-35`) | **K4c** |
| `plonk_checks_passed` (`step.rs:874`) | `derive_plonk` | **NEW — this file** |

So the only genuinely new arithmetic is `derive_plonk`, and it turns out to be three scalars
(`plonk_checks.rs:238-290`): the permutation scalar `perm`, `zeta_to_domain_size = ζ^n`, and
`zeta_to_srs_length = ζ^max_poly_size`, each then carried in `Shifted_value` form (P2).

## The payoff that makes this cheap: `derive_plonk`'s `perm` IS K5's `permScalar`

`derive_plonk` inlines (`plonk_checks.rs:259-266`)

    perm = −( z(ζω)·β·α^21·zkp(ζ) · Π_{i<6} (γ + β·σ_i(ζ) + w_i(ζ)) )

which is character-for-character o1-labs' own `ConstraintSystem::perm_scalars`
(`permutation.rs:392-430`) and character-for-character K5's `permScalar`
(`KimchiVerify` §4) — one expression, three call sites. `derive_plonk_perm_is_permScalar` proves
the identity for every input, so the Pickles deferred `perm` is the scalar K5 already multiplies
the σ₆ COMMITMENT by in the `f_comm` MSM. `α^21` is `PERM_ALPHA0` (`plonk_checks.ml:218`), which
is the `alpha0` the reality gates already pin.

## Grounding — what is REAL here and what is not

**Real:** every value below is from the same `prev_challenges = 2` Kimchi proof as
`KimchiRecursionGate` (`metatheory/kimchi_p6_prev2_proof.json`), which `kimchi::verifier::verify`
accepts. `perm` is dumped from o1-labs' **own** `ConstraintSystem::perm_scalars`, so
`derive_plonk_matches_rust` is a DIFFERENTIAL against their code, not a self-consistency check.
`ζ^max_poly_size` at `max_poly_size = 65536` is checked through the `sqIter` ladder
(`KimchiVerify` §7b), so the exponent is real rather than reduced to something kernel-cheap.

**NOT real, and this is the whole caveat:** `finalize_other_proof` compares the recomputed values
against the ones the OTHER proof EXPOSED in its public input, and there is no Pickles proof in this
tree — no Step or Wrap statement, no `Deferred_values` record from a real prover. So the exposed
side is instantiated with the derived values, i.e. with what an honest prover would expose. That
makes `finalize_accepts` a statement about the ASSEMBLY (the four checks compose, and the three
reused cores accept the real proof's scalars), **not** evidence that a real Pickles statement would
pass. The tampers are what carry the weight: each one breaks exactly one sub-check.

**And P4 is untouched.** `finalize_other_proof` is sound only if the exposed scalars are PINNED to
the challenges the group sub-verifier actually sampled — `assert_eq_plonk`
(`wrap_verifier.ml:492-499`), the sponge-digest equality and the per-round bulletproof-challenge
equality (`wrap_main.ml:430-439`). Nothing here bears on that. A `finalize_other_proof` without
P4 accepts a `Deferred_values` an attacker chose, as long as it is internally consistent. That is
the point of P4 being called the security crux, and it is NOT claimed here in any degree.

## Axiom hygiene

`#assert_namespace_axioms`-clean; no `sorry`, no `native_decide`.

NEW standalone file. Import line for the root (do NOT edit `Dregg2.lean` from a lane):
`import Dregg2.Circuit.Emit.PicklesFinalizeOtherProof`
-/
import Dregg2.Circuit.Emit.PicklesRecursion

namespace Dregg2.Circuit.Emit.PicklesFinalizeOtherProof

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaIPA (bEval)
open Dregg2.Circuit.Emit.KimchiVerify
  (PERMUTS COLUMNS zkPolyR permScalar permScalarR permScalarR_eq cipR ftEval0R sqIter sqIter_eq
   bEvalSq bEvalSq_eq_bEval)
open Dregg2.Circuit.Emit.PicklesRecursion
  (Shift1 type1OfField type1ToField type1_to_of type1_eq_iff shift1Fp)

set_option autoImplicit false
set_option maxRecDepth 4000

abbrev Fp := ZMod pN

/-! ## §1 — `derive_plonk` (`plonk_checks.rs:238-290`).

`PERM_ALPHA0 = 21` (`plonk_checks.rs:221`, OCaml `plonk_checks.ml:218`); `alpha_pow(21)` is the
`alpha0` the reality gates pin. `zkp` is the permutation vanishing polynomial at ζ — K5's `zkPolyR`.
The three derived scalars are `perm`, `zeta_to_domain_size` and `zeta_to_srs_length`; the rest of
`InCircuit` is a passthrough of the four minimal challenges. -/

/-- `PERM_ALPHA0` — the alpha index the permutation argument starts at. -/
def PERM_ALPHA0 : Nat := 21

/-- **`derivePlonkPerm`** — `derive_plonk`'s permutation scalar (`plonk_checks.rs:259-266`),
written in its own terms so the next theorem is not true by construction. -/
def derivePlonkPerm {R : Type} [CommRing R] (n : Nat) (omega zeta beta gamma alphaPow21 : R)
    (w s : List R) (zZetaOmega : R) : R :=
  let zkp := zkPolyR n omega zeta
  0 - (List.range (PERMUTS - 1)).foldl
        (fun acc i => acc * (gamma + beta * s.getD i 0 + w.getD i 0))
        (zZetaOmega * beta * alphaPow21 * zkp)

/-- ⚑ **`derive_plonk_perm_is_permScalar`** — the Pickles deferred `perm` IS K5's `permScalar`, for
every input. `plonk_checks.rs:259-266` = `permutation.rs:422-429` = `KimchiVerify` §4: one
expression, three call sites, and the σ₆-commitment scalar K5 already computes is the scalar the
recursion defers. This is the reuse that makes P3 cheap. -/
theorem derive_plonk_perm_is_permScalarR {R : Type} [CommRing R]
    (n : Nat) (omega zeta beta gamma alphaPow21 : R) (w s : List R) (zZetaOmega : R) :
    derivePlonkPerm n omega zeta beta gamma alphaPow21 w s zZetaOmega
      = permScalarR n omega zeta beta gamma alphaPow21 w s zZetaOmega := rfl

/-- And at any FIELD the mirror is the shipped `permScalar` itself (`permScalarR_eq`), so the chain
`derive_plonk.perm = permScalarR = permScalar` closes. The `CommRing` step is what lets the real
proof — which lives in `ZMod pN`, with no `Field` instance in this tree — be checked at all; it is
the same device K5 uses for `cipR`/`ftEval0R`. -/
theorem derive_plonk_perm_is_permScalar {K : Type} [Field K]
    (n : Nat) (omega zeta beta gamma alphaPow21 : K) (w s : List K) (zZetaOmega : K) :
    derivePlonkPerm n omega zeta beta gamma alphaPow21 w s zZetaOmega
      = permScalar n omega zeta beta gamma alphaPow21 w s zZetaOmega := rfl

/-- **`derivePlonk`** — the three derived scalars, in `Shifted_value` Type1 form (Fp side,
`step_verifier.ml:826`; `common.ml:91-103`). `srsLog2` is `log2 max_poly_size`, so
`zeta_to_srs_length` goes up the squaring ladder rather than through `Monoid.npow`. -/
structure Plonk (R : Type) where
  perm : R
  zetaToDomainSize : R
  zetaToSrsLength : R
  deriving DecidableEq

/-- `derive_plonk` proper, un-shifted. -/
def derivePlonk {R : Type} [CommRing R] (n srsLog2 : Nat)
    (omega zeta beta gamma alphaPow21 : R) (w s : List R) (zZetaOmega : R) : Plonk R :=
  { perm := derivePlonkPerm n omega zeta beta gamma alphaPow21 w s zZetaOmega
    zetaToDomainSize := zeta ^ n
    zetaToSrsLength := sqIter srsLog2 zeta }

/-- **`derivePlonkShifted`** — the same three scalars as the circuit CARRIES them: Type1 shifted
(P2). `type1_eq_iff` is why comparing shifted representatives is comparing field values. -/
def derivePlonkShifted {R : Type} [CommRing R] (sh : Shift1 R) (n srsLog2 : Nat)
    (omega zeta beta gamma alphaPow21 : R) (w s : List R) (zZetaOmega : R) : Plonk R :=
  let p := derivePlonk n srsLog2 omega zeta beta gamma alphaPow21 w s zZetaOmega
  { perm := type1OfField sh p.perm
    zetaToDomainSize := type1OfField sh p.zetaToDomainSize
    zetaToSrsLength := type1OfField sh p.zetaToSrsLength }

/-- **`shifted_comparison_is_field_comparison`** — comparing the carried Type1 representatives of
the derived `plonk` record IS comparing the field scalars, so `plonk_checks_passed` below loses
nothing by working in shifted form. (The half this does NOT give is P4: that the exposed
representative is the one the group sub-verifier sampled.) -/
theorem shifted_comparison_is_field_comparison {R : Type} [CommRing R]
    (sh : Shift1 R) (h : sh.ok) (n srsLog2 : Nat)
    (omega zeta beta gamma alphaPow21 : R) (w s : List R) (zZetaOmega : R)
    (omega' zeta' beta' gamma' alphaPow21' : R) (w' s' : List R) (zZetaOmega' : R) :
    derivePlonkShifted sh n srsLog2 omega zeta beta gamma alphaPow21 w s zZetaOmega
        = derivePlonkShifted sh n srsLog2 omega' zeta' beta' gamma' alphaPow21' w' s' zZetaOmega'
      ↔ derivePlonk n srsLog2 omega zeta beta gamma alphaPow21 w s zZetaOmega
        = derivePlonk n srsLog2 omega' zeta' beta' gamma' alphaPow21' w' s' zZetaOmega' := by
  constructor
  · intro he
    have hp := congrArg Plonk.perm he
    have hd := congrArg Plonk.zetaToDomainSize he
    have hs := congrArg Plonk.zetaToSrsLength he
    simp only [derivePlonkShifted] at hp hd hs
    rw [type1_eq_iff sh h] at hp hd hs
    simp only [derivePlonk] at hp hd hs
    simp only [derivePlonk, Plonk.mk.injEq]
    exact ⟨hp, hd, hs⟩
  · intro he
    simp only [derivePlonkShifted, he]

/-! ## §2 — The four-way discharge (`step.rs:876-884`). -/

/-- **`bDeferred`** — `b_correct`'s value: `challenge_poly(ζ) + evalscale·challenge_poly(ζω)`
(`wrap_verifier.ml:1015-1026`; `step.rs:854-862`), on the proof's own IPA round challenges.
`bEvalSq` is K4c's `bEval` up the squaring ladder (`bEvalSq_eq_bEval`). -/
def bDeferred {R : Type} [CommRing R] (zeta zetaOmega evalscale : R) (chals : List R) : R :=
  bEvalSq zeta chals + evalscale * bEvalSq zetaOmega chals

/-- **`bDeferred_is_bEval`** — and it is K4c's b-polynomial, so `sVec_eq_bPoly` applies. -/
theorem bDeferred_is_bEval {R : Type} [CommRing R] (zeta zetaOmega evalscale : R) (chals : List R) :
    bDeferred zeta zetaOmega evalscale chals
      = bEval zeta chals + evalscale * bEval zetaOmega chals := by
  simp [bDeferred, bEvalSq_eq_bEval]

/-- **`finalizeOtherProofOk`** — the AND of the four sub-checks (`step.rs:876-884`), each
recomputing a value the other proof exposed:

* `xi_correct` — the polyscale ξ equals the squeeze (`step.rs:694-697`). The squeeze is the
  sponge's; here the check is the EQUALITY, with the squeezed value supplied.
* `combined_inner_product_correct` — recompute via `ftEval0R` + the ξ/r-weighted eval fold
  (`step.rs:748-845`). K5's `cipR`/`ftEval0R`, including the witnessed C5 inverse.
* `b_correct` — `bDeferred` (`step.rs:854-862`). K4c.
* `plonk_checks_passed` — the exposed `plonk` record equals `derivePlonk` (`step.rs:874`). NEW. -/
def finalizeOtherProofOk {R : Type} [CommRing R] [DecidableEq R]
    (n srsLog2 : Nat)
    (omega zeta zetaOmega beta gamma alphaPow21 alpha1 alpha2 : R)
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed : R)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (xiSqueezed xiExposed : R)
    (ipaChals : List R) (bExposed : R)
    (plonkExposed : Plonk R) : Bool :=
  -- xi_correct
  decide (xiExposed = xiSqueezed)
  -- combined_inner_product_correct (C5's witnessed inverse first, then C5 and C8)
  && decide (((zeta - omega ^ (n - 3)) * (zeta - 1)) * denomInv = 1)
  && decide (ftEval0R n omega zeta beta gamma alphaPow21 alpha1 alpha2 w s shift
       zZeta zZetaOmega pZeta linConstTerm denomInv = ftEval0Claimed)
  && decide (cipR polyscale evalscale evZeta evZetaOmega = cipClaimed)
  -- b_correct
  && decide (bDeferred zeta zetaOmega evalscale ipaChals = bExposed)
  -- plonk_checks_passed
  && decide (derivePlonk n srsLog2 omega zeta beta gamma alphaPow21 w s zZetaOmega = plonkExposed)

/-- **`finalizeOtherProofOk_is_the_four_checks`** — the assembly IS the conjunction, by `rfl`; the
translation-validation shape `kimchiVerifyDecision_refines` uses. Nothing is hidden in the fold. -/
theorem finalizeOtherProofOk_is_the_four_checks {R : Type} [CommRing R] [DecidableEq R]
    (n srsLog2 : Nat)
    (omega zeta zetaOmega beta gamma alphaPow21 alpha1 alpha2 : R)
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed : R)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (xiSqueezed xiExposed : R) (ipaChals : List R) (bExposed : R) (plonkExposed : Plonk R) :
    finalizeOtherProofOk n srsLog2 omega zeta zetaOmega beta gamma alphaPow21 alpha1 alpha2
        w s shift zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed
        polyscale evalscale evZeta evZetaOmega cipClaimed xiSqueezed xiExposed
        ipaChals bExposed plonkExposed
      = (decide (xiExposed = xiSqueezed)
         && decide (((zeta - omega ^ (n - 3)) * (zeta - 1)) * denomInv = 1)
         && decide (ftEval0R n omega zeta beta gamma alphaPow21 alpha1 alpha2 w s shift
              zZeta zZetaOmega pZeta linConstTerm denomInv = ftEval0Claimed)
         && decide (cipR polyscale evalscale evZeta evZetaOmega = cipClaimed)
         && decide (bDeferred zeta zetaOmega evalscale ipaChals = bExposed)
         && decide (derivePlonk n srsLog2 omega zeta beta gamma alphaPow21 w s zZetaOmega
              = plonkExposed)) := rfl

/-! ## §3 — The real proof's values (same fixture as `KimchiRecursionGate`). -/

def N : Nat := 32
/-- `log2 max_poly_size` — `max_poly_size = 65536` for this index. -/
def SRSLOG2 : Nat := 16
def OMEGA : Fp := (5772676229766982871441818714777438643955918462675337216809979342233538361548 : Fp)
def ZETA : Fp := (9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp)
def BETA : Fp := (207191000514447567911742581240638307123 : Fp)
def GAMMA : Fp := (212090136106687690782051664536927829615 : Fp)
def VV : Fp := (19544871314116795727517838875197793037815458944822650859500043150633165651675 : Fp)
def UU : Fp := (4029829395372224514861218209502654028970733683372586849261102654660655230746 : Fp)
def ZETAW : Fp := ZETA * OMEGA
def A0 : Fp := (27127124423890897709471374909862003647116284891598004634947951661445215106972 : Fp)
def A1 : Fp := (20593720338113534389521454660804407486551671373149076281591404732999708584299 : Fp)
def A2 : Fp := (8840729502544819637001421052144459133411006294815526850138860654886814951281 : Fp)
def PZ : Fp := (16699068735930530700816957931718769427327118752981787273017885401731235465874 : Fp)
def ZZ : Fp := (8244319662825206332411783431566334535933848287177687988960906513771535583867 : Fp)
def ZZW : Fp := (28413617518552286544998492970805240901385119401424696642596595430411951585052 : Fp)
def LCT : Fp := (25176125367283258483645567069047624719408919843921778995401288234605086066529 : Fp)
def DINV : Fp := (25101255547495239008933771641747459570350673925858386801666806526121716601105 : Fp)
def FT0 : Fp := (20512491975096102969445730753856641614900814594917083726254351557943483283533 : Fp)
def CIP : Fp := (17740189269356222263044292859403678013788533553867958003390301420202884439406 : Fp)
def SHIFT : List Fp :=
  [(1 : Fp), (328286983623303317637963920346571898945724874896624808297627776768640590563 : Fp), (91433028157768305433241271390810941046493237899366836746431422160024463706 : Fp), (240213425742950025341713987028051046476975246675775993287051503548513551377 : Fp), (417757293700961807788464308236931191792053554682199437460107260306038610067 : Fp), (430348682428487492383428014506756320686619984007091686553051322507181255952 : Fp), (326625242707153437805405281465150497418605074624614708160829052937679007395 : Fp)]
def WZ : List Fp :=
  [(8571631469098177892965262307737168137771792367786739004103898273114062670285 : Fp), (10498381543777762020631802150870211762003709095234594899293761913383977328132 : Fp), (12226728938788036639480999661017599962364448487055773636731396600382488581196 : Fp), (5707378856581365824447872698174223853012679496314514995080294844551197875781 : Fp), (22725874598313407611264545143412740301204078004768953753255037423937170617111 : Fp), (4871479349103771792541760605837981763914640577439617428271699200123592435433 : Fp), (27468350421930086744186305050869116760687727483048562429320842326053428252096 : Fp), (7852482877623881408152923783758059858364119588906157757585163529302380664242 : Fp), (17712610987890872765251184085675488375257638256291780270440669271574683981428 : Fp), (2809562589381152287364102553008182578660398152321259224004064607433802554541 : Fp), (12725230491694275861102765549546304969337542628803076138803407761907282369647 : Fp), (7651341330198429039504127155456038660566040141866927464365340559790747382195 : Fp), (17789473230049229564004961520174629180440520442392892001760357346090014021052 : Fp), (13124202080984823270185709766370374334406100446141282230912582756427552375713 : Fp), (7807586433423507120930971828781208694777921411506294439127181997722987231222 : Fp)]
def SZ : List Fp :=
  [(9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp), (20222061864450867255710902152931194513000988722830211032226108406269483319592 : Fp), (7476278879333289444878543626839011543831373682982983342588005018880166909098 : Fp), (12928632103618224043023991788970990076655059964985295017406175964126481123944 : Fp), (5818431057815805527205661029874349337966454987084644709243167839448640882189 : Fp), (9554744463517008369767910484965602220431146377570871885328571004953370013735 : Fp)]
def EVZ : List Fp :=
  [(17828066129561323373660284225674803269361090018363714112424067158784994066545 : Fp), (16155731223796678648794054144832062005213694877342714024327684304535284029140 : Fp), (16699068735930530700816957931718769427327118752981787273017885401731235465874 : Fp), (20512491975096102969445730753856641614900814594917083726254351557943483283533 : Fp), (8244319662825206332411783431566334535933848287177687988960906513771535583867 : Fp), (20289014582057077051388428879908383452560950442292165868545185027925730367812 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (8571631469098177892965262307737168137771792367786739004103898273114062670285 : Fp), (10498381543777762020631802150870211762003709095234594899293761913383977328132 : Fp), (12226728938788036639480999661017599962364448487055773636731396600382488581196 : Fp), (5707378856581365824447872698174223853012679496314514995080294844551197875781 : Fp), (22725874598313407611264545143412740301204078004768953753255037423937170617111 : Fp), (4871479349103771792541760605837981763914640577439617428271699200123592435433 : Fp), (27468350421930086744186305050869116760687727483048562429320842326053428252096 : Fp), (7852482877623881408152923783758059858364119588906157757585163529302380664242 : Fp), (17712610987890872765251184085675488375257638256291780270440669271574683981428 : Fp), (2809562589381152287364102553008182578660398152321259224004064607433802554541 : Fp), (12725230491694275861102765549546304969337542628803076138803407761907282369647 : Fp), (7651341330198429039504127155456038660566040141866927464365340559790747382195 : Fp), (17789473230049229564004961520174629180440520442392892001760357346090014021052 : Fp), (13124202080984823270185709766370374334406100446141282230912582756427552375713 : Fp), (7807586433423507120930971828781208694777921411506294439127181997722987231222 : Fp), (20289014582057077051388428879908383452560950442292165868545185027925730367812 : Fp), (9078907305375965279209769890514743833327199224670571986768068574461575630289 : Fp), (25921719874203727096156156288667062352253990073718036720365320572862775753574 : Fp), (0 : Fp), (18356861751261349991905764075586754938406398590636969255978658382003051951990 : Fp), (13179727622465582573293242809585732996106571457748717391976898382232294436228 : Fp), (0 : Fp), (25921719874203727096156156288667062352253990073718036720365320572862775753574 : Fp), (6052604870250643519473179927009829222218132816447047991178712382974383753526 : Fp), (20945428815659233701212024708587265909556312157081095187979538381888430709871 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp), (20222061864450867255710902152931194513000988722830211032226108406269483319592 : Fp), (7476278879333289444878543626839011543831373682982983342588005018880166909098 : Fp), (12928632103618224043023991788970990076655059964985295017406175964126481123944 : Fp), (5818431057815805527205661029874349337966454987084644709243167839448640882189 : Fp), (9554744463517008369767910484965602220431146377570871885328571004953370013735 : Fp)]
def EVZW : List Fp :=
  [(3629545005364862799166977133458596102488702259123600044870959423427549231674 : Fp), (27510814418027099036823053573729904301397885501827492330796950478768959623636 : Fp), (22694988732487413569768414879304127220669743293048209292526588138156754519444 : Fp), (17308066366979432850743499843247684254717537646415512986039646514623943698673 : Fp), (28413617518552286544998492970805240901385119401424696642596595430411951585052 : Fp), (1505835031738489045669102623006506571614583572836545138415851735303544274280 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (5870691909402545263935066565046749018277504469022294653337212965826477555878 : Fp), (14737523738739915296332600783793473448999582029258305824291997712669282146479 : Fp), (7157463226911189607398504455636319912250854056680509938956891187356624411351 : Fp), (9673568260648711027815695816658608332432200180621793869269384731761497053443 : Fp), (8064661002098320303132917405207446410031037811317120498298608427478522936404 : Fp), (8547602688265030976104763696574280978880067477267074777580201575244485218808 : Fp), (1057584007922130536451983665572778898835419095801769237370991267361816924830 : Fp), (9094953297114810626338292529965261983227768658956878444491618348365948402783 : Fp), (11382464379156029713420570811206833358436500618164598282515462637937649572306 : Fp), (24209233962049081420270986979316504955351575023532551164192074227389074501314 : Fp), (5346139787901258809305404649217643906162746388548120246186895744726941521558 : Fp), (4418109022700263677774933597005093291985178241700946732110599328557438290004 : Fp), (7838213741029448028466990066039464327531111128113298710520550622320150892990 : Fp), (3682512507270624800776302659289365504313614845709736300238392151996555107787 : Fp), (11480739924566123960794658987674936286415521001293697063541849862289585666586 : Fp), (1505835031738489045669102623006506571614583572836545138415851735303544274280 : Fp), (5034121113520778284972002483993798646064648912337978424709914744467820676100 : Fp), (27269981938155456094235412090840710748008173511162234574384705182860694071637 : Fp), (0 : Fp), (6769649595146946434089025987842128673914211382721694432890448164750400964153 : Fp), (17042131674503717092565488838833941750937300527053808999672968454649844765507 : Fp), (0 : Fp), (27269981938155456094235412090840710748008173511162234574384705182860694071637 : Fp), (3356080742347185523314668322662532430709765941558652283139943162978547117400 : Fp), (1633408555468561104850794562346222135402666810555637149499188019800679063476 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (25112291877082749676115840494627210270009314399046677500547639994784416827233 : Fp), (25753815309776636893912018711466599782002461501972077920944173182670042524739 : Fp), (2862439684383872514568578117528550260380704281116603134876740328313902580774 : Fp), (23571244234724671444354123361617570561877099444212437802192226209657361424063 : Fp), (282588898942660134324302820374004985158659318752464045339180032946058454389 : Fp), (18188311822459808878175961661027514544805035333747043068419065145317553572056 : Fp)]
/-- The `k = 16` ENDO-MAPPED IPA round challenges (`ipa.rs:1261-1275`), the ones `b_poly`
consumes — not the raw prechallenges. -/
def IPACHALS : List Fp :=
  [(5056624989650071945510843492349367812655828174568651286218330639906126361486 : Fp), (7466629998166954248924030500188715388747660444003779384927335439335555330832 : Fp), (14105317996238849186514750124126394825539719100082994500426704338842395836499 : Fp), (4090484525785319220729443785077395385330308644175387324216003198837598669024 : Fp), (8000110848951949682439215651514254615393689943087120121888642610606560900601 : Fp), (14914435723144649742991829309417976473412427436123855412014671817970806799302 : Fp), (8741986856067679707381697727096638922600943514580644531191308109511508052855 : Fp), (5075491121909819361982177498266972006683567168886169162665934665228822953126 : Fp), (21509154994384831386291527152782981435165811490039225395163916198565580470767 : Fp), (18059389524567045131188606209645871133666393320454406145335626893148901569366 : Fp), (11645741172093393772936208279125478149695271311583431420892219722537648587365 : Fp), (9849436060144484658495570381039983122374165952929208375378223699925925899453 : Fp), (11983473014393898554416407521711858140096251518262962821643767835773120793849 : Fp), (7854208093664783017073258578553263970997306397774495842793061497769652039535 : Fp), (4943808111387688341134512802064527713645781730967684443406332787732340715337 : Fp), (20408912629520259399184599790221141686348286578950587440087173216040983656853 : Fp)]
/-- `b` from o1-labs' own `b_poly` on those challenges. -/
def BDEF : Fp := (4855498836239450438294765887489322664852053920215454396392742509652073569254 : Fp)
/-- ⚑ The three `derive_plonk` outputs, dumped from o1-labs' code: `perm` from
`ConstraintSystem::perm_scalars` (`permutation.rs:392-430`), and the two exponentiations. -/
def PERM : Fp := (3689186282540999277776618142275107381498133388538252043432910702427755744802 : Fp)
def ZETA_TO_N : Fp := (28086548619216293777210234024331763939734207338256053651617457673367727816099 : Fp)
def ZETA_TO_SRS : Fp := (7945674355346637519592705100895268306497308077000118737506721895482606305170 : Fp)
/-- `zkp(ζ)` from the index's `permutation_vanishing_polynomial_m`. -/
def ZKP : Fp := (5695743597299628848924088017028051764937220979982039214838438968246638385787 : Fp)

/-! ## §4 — The `derive_plonk` differential against o1-labs' own scalars. -/

/-- ⚑ **`derive_plonk_matches_rust`** — the three derived scalars reproduce the values o1-labs'
code computed on this proof: `perm` against `ConstraintSystem::perm_scalars`, `ζ^n`, and
`ζ^max_poly_size` at the REAL `max_poly_size = 65536` (through the `sqIter` ladder, so the exponent
is not reduced to something kernel-cheap). `zkp(ζ)` is K5's `zkPolyR` against the index's
`permutation_vanishing_polynomial_m`, which is what makes `perm` a differential rather than a
restatement. -/
theorem derive_plonk_matches_rust :
    zkPolyR N OMEGA ZETA = ZKP
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA A0 WZ SZ ZZW).perm = PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA A0 WZ SZ ZZW).zetaToDomainSize = ZETA_TO_N
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA A0 WZ SZ ZZW).zetaToSrsLength = ZETA_TO_SRS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **`zeta_to_srs_is_the_real_power`** — and the ladder value really is `ζ^65536`, not merely 16
squarings that happen to agree: `sqIter_eq` proves the ladder computes the power for every base and
every height, so this is an equation about `ζ ^ 2^16` with the exponent intact. -/
theorem zeta_to_srs_is_the_real_power : ZETA ^ (2 ^ SRSLOG2 : Nat) = ZETA_TO_SRS := by
  rw [← sqIter_eq]
  exact derive_plonk_matches_rust.2.2.2

/-- **`perm_is_K5_permScalar_on_the_real_proof`** — the reuse, instantiated: the deferred `perm`
this proof would carry is exactly the σ₆-commitment scalar K5 computes for the same proof. -/
theorem perm_is_K5_permScalar_on_the_real_proof :
    permScalarR N OMEGA ZETA BETA GAMMA A0 WZ SZ ZZW = PERM :=
  derive_plonk_matches_rust.2.1

/-- **`derive_plonk_discriminates`** — every input `derive_plonk` reads moves `perm`: β, γ, α^21,
`z(ζω)`, a σ evaluation, a witness evaluation, and ζ (through `zkp`). Non-vacuity per argument,
not "some tamper somewhere". -/
theorem derive_plonk_discriminates :
    (derivePlonk N SRSLOG2 OMEGA ZETA (BETA + 1) GAMMA A0 WZ SZ ZZW).perm ≠ PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA (GAMMA + 1) A0 WZ SZ ZZW).perm ≠ PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA (A0 + 1) WZ SZ ZZW).perm ≠ PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA A0 WZ SZ (ZZW + 1)).perm ≠ PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA A0 WZ (SZ.set 4 0) ZZW).perm ≠ PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA ZETA BETA GAMMA A0 (WZ.set 2 0) SZ ZZW).perm ≠ PERM
    ∧ (derivePlonk N SRSLOG2 OMEGA (ZETA + 1) BETA GAMMA A0 WZ SZ ZZW).perm ≠ PERM := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`b_correct_matches_rust`** — `b_correct`'s value reproduces o1-labs' `b_poly` on the endo-mapped
round challenges, and moves when a round challenge or the evalscale moves. -/
theorem b_correct_matches_rust :
    bDeferred ZETA ZETAW UU IPACHALS = BDEF
    ∧ bDeferred ZETA ZETAW UU (IPACHALS.set 9 0) ≠ BDEF
    ∧ bDeferred ZETA ZETAW (UU + 1) IPACHALS ≠ BDEF
    ∧ bDeferred ZETAW ZETA UU IPACHALS ≠ BDEF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §5 — The assembled discharge, on the real proof.

⚑ Read §"Grounding" in the header before reading `finalize_accepts`. The EXPOSED side is
instantiated with the derived values — what an honest prover would expose — because no real
Pickles statement exists in this tree. The theorem says the four checks COMPOSE and that the three
reused cores accept this proof's real scalars. It does not say a real Pickles statement passes, and
it says nothing at all about P4. -/

/-- The exposed `plonk` record an honest prover would carry for this proof. -/
def PLONK_EXPOSED : Plonk Fp := ⟨PERM, ZETA_TO_N, ZETA_TO_SRS⟩

/-- **`finalize_accepts`** — the four-way discharge accepts. -/
theorem finalize_accepts :
    finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0
        VV UU EVZ EVZW CIP VV VV IPACHALS BDEF PLONK_EXPOSED = true := by decide

/-- ⚑ **`finalize_discriminates`** — six tampers, one per sub-check plus the witnessed inverse: a
wrong ξ, a bogus inverse, a wrong `ft(ζ)`, a wrong `cip`, a wrong `b`, and each of the three
`plonk` slots. Every one flips the discharge to `false`, so no sub-check is inert. -/
theorem finalize_discriminates :
    finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 VV UU EVZ EVZW CIP VV (VV + 1)
        IPACHALS BDEF PLONK_EXPOSED = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT (DINV + 1) FT0 VV UU EVZ EVZW CIP VV VV
        IPACHALS BDEF PLONK_EXPOSED = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV (FT0 + 1) VV UU EVZ EVZW CIP VV VV
        IPACHALS BDEF PLONK_EXPOSED = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 VV UU EVZ EVZW (CIP + 1) VV VV
        IPACHALS BDEF PLONK_EXPOSED = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 VV UU EVZ EVZW CIP VV VV
        IPACHALS (BDEF + 1) PLONK_EXPOSED = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 VV UU EVZ EVZW CIP VV VV
        IPACHALS BDEF ⟨PERM + 1, ZETA_TO_N, ZETA_TO_SRS⟩ = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 VV UU EVZ EVZW CIP VV VV
        IPACHALS BDEF ⟨PERM, ZETA_TO_N + 1, ZETA_TO_SRS⟩ = false
    ∧ finalizeOtherProofOk N SRSLOG2 OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 VV UU EVZ EVZW CIP VV VV
        IPACHALS BDEF ⟨PERM, ZETA_TO_N, ZETA_TO_SRS + 1⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6 — Residuals (what P3 does NOT reach).

1. **P4 — the transcript-equality binding — is UNTOUCHED and is the security crux.** Without it,
   `finalize_other_proof` discharges a `Deferred_values` record an attacker chose, as long as it
   is internally consistent. `assert_eq_plonk` (`wrap_verifier.ml:492-499`), the sponge-digest
   equality and the per-round bulletproof-challenge equality (`wrap_main.ml:430-439`,
   `step_verifier.ml:1271-1285`) are what pin the exposed scalars to the SAMPLED ones.
   §1's `shifted_comparison_is_field_comparison` is the ALGEBRAIC half only, and says so.
2. **No real Pickles statement exists in this tree**, so the exposed side of every check above is
   the derived value. `finalize_accepts` is about the assembly, not about a real Step/Wrap object.
3. **P5 (the mirror to the other side) is not built.** This is the Fp/Type1 direction only.
4. **`xi_correct`'s squeeze is supplied, not run.** The equality is checked; producing ξ from the
   phase-2 sponge on THIS proof is `KimchiPoseidonGate`'s `deriveVU`, not wired in here.
5. **The lookup / joint_combiner and feature-flag fields of `InCircuit` are absent** — v1 has
   `lookup_index = None`, as everywhere in this stack.
6. **The IPA/FRI opening-soundness floor (P10)** is inherited, undischarged. -/

#assert_namespace_axioms Dregg2.Circuit.Emit.PicklesFinalizeOtherProof

end Dregg2.Circuit.Emit.PicklesFinalizeOtherProof
