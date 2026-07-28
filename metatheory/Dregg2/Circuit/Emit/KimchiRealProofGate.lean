/-
# Dregg2.Circuit.Emit.KimchiRealProofGate — the REALITY GATE for `kimchiVerifyDecision`

This feeds a **REAL Kimchi proof** — produced by o1-labs `proof-systems` @ `36a8b510`
(v0.7.0), a generic circuit with 5 public inputs, `ProverProof::create`, which the REAL
`kimchi::verifier::verify` ACCEPTS — through the assembled `KimchiVerify` machinery and
records, honestly, exactly what runs on real values and what cannot.

The real field values are emitted by `proof-systems/kimchi/examples/reality_gate_export.rs`
(committed alongside this gate) and pasted below as decimal literals `< pN`. See
`docs/MINA-REALITY-GATE.md` for the full source, mapping, and the ordered gap-to-close.

## The load-bearing honesty (what this file establishes vs. does NOT)

  * The **field of the proof is Fp = Vesta::ScalarField = `ZMod pN`** (all evaluations,
    challenges, ft_eval0, cip; modulus `pN`, mina-curves `curves/src/pasta/fields/fp.rs`). The
    `KimchiVerify` header label `Fq = ZMod qN` (the Vesta BASE field) was a mislabel; it is now
    CORRECTED to `Fp = ZMod pN` at the source. This gate uses the correct `ZMod pN`.

  * The shipped C4–C8 formulas (`combinedInnerProduct`, `ftEval0`, `publicEval`, …) are
    `[Field F]`-typed. **There is no `Field (ZMod pN)` instance in the tree** (no in-kernel
    primality proof of the 255-bit `pN`; `native_decide` is forbidden), so the shipped defs
    **cannot be instantiated at the real Pasta field**. To exercise the REAL values,
    `KimchiVerify` §9b supplies `CommRing`-typed MIRRORS (`cipR`, `ftEval0R`) whose bodies are
    byte-identical to the shipped defs and are TIED to them by `rfl` for every field (`cipR_eq`,
    `ftEval0R_eq`) — so evaluating a mirror at `ZMod pN` runs the shipped def's exact computation,
    at a `CommRing` where the shipped `[Field F]` signature cannot be typed. The single field
    inverse `ftEval0` needs is SUPPLIED as a witness `denomInv` and CHECKED (`denom·denomInv = 1`)
    in the ring, so NO `Field`/primality instance is required. This is a **differential** (the
    shipped def's arithmetic reproduces the real proof's value), not a proof the Field-typed def runs.

  * **The composed decision `kimchiVerifyDecisionField` (KimchiVerify §9b) now CONSUMES these field
    values** — §6b evaluates it on the real proof: C1 (shape) ∧ C8 (`cip = combinedInnerProduct`) ∧
    the witnessed-inverse ∧ C5 (`ft_eval0`), all over the real `ZMod pN`, plus the three carriers.
    `real_field_decision_accepts` shows a real proof's arithmetic ACCEPTS through one decision;
    `real_field_decision_discriminates` shows each tampered value REJECTS. The prior
    `kimchiVerifyDecision` (C1 + three carrier Bools) and `ipaDeferralOk` (C9) also run the SHIPPED
    defs on real proof data (the shape counts and `k = 16` IPA rounds).

  * C3 (transcript order) is a proven theorem in `KimchiVerify`; the sponge VALUES that
    produce the real β,γ,α,ζ,v,u are the K3 carrier + the un-instantiated Fr-sponge — this
    gate records the real challenges but CANNOT re-derive them (no differential possible).

## Axiom hygiene
`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `by decide`/`rfl`/`#guard`
only, no `sorry`/`native_decide`. Imports `KimchiVerify`; NOT imported by the `Dregg2` root.
-/
import Dregg2.Circuit.Emit.KimchiVerify

namespace Dregg2.Circuit.Emit.KimchiRealProofGate

open Dregg2.Circuit.Emit.KimchiVerify
  (kimchiVerifyDecision kimchiVerifyDecisionField combinedInnerProduct ftEval0 zkPoly
   cipR cipR_eq zkPolyR ftEval0R ftEval0R_eq ipaDeferralOk PERMUTS
   genericGateConstraint gateLinConst kimchiVerifyDecisionGates frEvalPointOrder frSpongeDigest)
open Dregg2.Circuit.Emit.PastaIPA (IpaDeferred absorbChallenges)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon

set_option autoImplicit false

/-- The real Pasta SCALAR field the proof lives in: `Fp = Vesta::ScalarField = ZMod pN`. -/
abbrev Fp := ZMod pN

/-! ## §1 — CommRing mirrors of the shipped C8/C5 formulas now live in `KimchiVerify` (§9b).

`ZMod pN` is a `CommRing` but not a proven `Field` here, so the `[Field F]`-typed shipped defs
(`combinedInnerProduct`, `ftEval0`) cannot be instantiated at it. `KimchiVerify.cipR` / `ftEval0R`
have byte-identical bodies over `[CommRing R]`; `cipR_eq` / `ftEval0R_eq` prove they equal the
shipped defs for EVERY field, so running a mirror at `ZMod pN` is running the shipped def's exact
computation. `kimchiVerifyDecisionField` (KimchiVerify §9b) is the composed accept that CONSUMES
these values — evaluated on the real proof in §5b below. (These were previously local to this gate,
validated BESIDE the decision; they are now part of the verifier assembly and threaded THROUGH it.) -/

/-! ## §2 — the REAL proof's field values (decimal, `< pN`), emitted by
`proof-systems/kimchi/examples/reality_gate_export.rs`. Source:
o1-labs/proof-systems @ 36a8b510 v0.7.0; `create_circuit` generic, 5 public inputs;
`ProverProof::create`; real `verify()` ACCEPTS; challenges/evals via `proof.oracles(...)`. -/

def N : Nat := 32
def OMEGA : Fp := (5772676229766982871441818714777438643955918462675337216809979342233538361548 : Fp)
def ZETA  : Fp := (16541114414374186410966727919716922283785106442391124222423037735912461503993 : Fp)
def BETA  : Fp := (239562823171939722776420885671503160963 : Fp)
def GAMMA : Fp := (391462078498551171403677683818839197 : Fp)
def ALPHA : Fp := (12283777653757111779373624386322982273139173087625232714007348641978771922692 : Fp)
def VV    : Fp := (9326955095485193907346986499244555502576459017726625035732458936937218762551 : Fp)   -- polyscale (v)
def UU    : Fp := (14385607627523733277175972462049357721772389249056937739160008356523876135853 : Fp)  -- evalscale (u)
def A0 : Fp := (14537941037240622553696450817487476407215602853032603201592003435126362555592 : Fp)
def A1 : Fp := (23177721271127567139785997877595719540328251499843605602402851352633368593053 : Fp)
def A2 : Fp := (7560487309470955894190649419637003973652191482341828688267993090614788914018 : Fp)
def SHIFT : List Fp := [(1 : Fp), (328286983623303317637963920346571898945724874896624808297627776768640590563 : Fp), (91433028157768305433241271390810941046493237899366836746431422160024463706 : Fp), (240213425742950025341713987028051046476975246675775993287051503548513551377 : Fp), (417757293700961807788464308236931191792053554682199437460107260306038610067 : Fp), (430348682428487492383428014506756320686619984007091686553051322507181255952 : Fp), (326625242707153437805405281465150497418605074624614708160829052937679007395 : Fp)]

-- C5/ftEval0 inputs
def PZ  : Fp := (26721404708901961892555744407146855255897463866912334121986446595141554099206 : Fp)
def ZZ  : Fp := (14908019327547832049053253335688031334836545726269840248359597514473981705670 : Fp)
def ZZW : Fp := (26299411995272010678557053079537170268419244114551598717318971433527609193211 : Fp)
def LCT : Fp := (12851225662969507270287768723621767515285066287102240641482029623767117733710 : Fp)   -- linConstTerm (C6 custom-gate carrier)
def DINV : Fp := (11359818066214259879059209882863327611167755308779150164502843777579862382822 : Fp)  -- denominator⁻¹ (supplied)
def DENOM : Fp := (4090893205039698037770549507787037695346582045934940767285955333478413720676 : Fp)
def FT0 : Fp := (4818413338202460091328447768070851017173477173576229777698353938180176055892 : Fp)     -- Rust oracles().ft_eval0
def WZ : List Fp := [(7124519407909476644061601315873560214171268546132147259749224767879511208526 : Fp), (9813870773946315016106397139522346734954310769450916401595122454777721695031 : Fp), (7957617585896985994558221298908444378524211062340684608379169058813459124125 : Fp), (25892320666495842991909428413718662491009959969139547015940434937720716797071 : Fp), (26009138774403902370617648263807440121147954769105221107578863101047182292538 : Fp), (27466170664826345097164396266307382202229875220353670695282326298096484999838 : Fp), (7261810992396815825306710508414309282211989790400581651923269472036607170331 : Fp), (9240242236120294292031913178789773014559483743118763280533267242642482286538 : Fp), (24071623849593521746666714637464562110070118428993134428847353045256863934406 : Fp), (8046093920254362244164683683806466735405167663914543927349685779444710749657 : Fp), (3369444797809033379666201783477116655079366548616332814949704010845941543745 : Fp), (19802659069966914682212348789938551805534491314942875900339717901145992996629 : Fp), (22615186636492186784266137470305613897599345442760345917705903292752096906310 : Fp), (27511253389181890047238778469066881135811028288809975329899823904146893298316 : Fp), (21541426521135312050214770894195162752168226972449017315542391488004636105261 : Fp)]
def SZ : List Fp := [(16541114414374186410966727919716922283785106442391124222423037735912461503993 : Fp), (8876573005941968478547146115745284835532102400748670531326405672563516635209 : Fp), (7257365216172337705995069980889501915496007701498661427924617664889119321498 : Fp), (26768285395752967238006275000953076092445053802944015698901042879979183995436 : Fp), (19684055716448937491261643334590454679456791870441580166015711126655560885123 : Fp), (20110303701090081505261870391676216480447424717267129704428681171086133555003 : Fp)]

-- C8/combined_inner_product inputs (es-order: public, ft, z, 6 selectors, 15 w, 15 coeff, 6 s)
def CIP : Fp := (4210050102189683816394537272740493692602739350784094460972305803318076804165 : Fp)   -- Rust oracles().combined_inner_product
def EVZ : List Fp := [(26721404708901961892555744407146855255897463866912334121986446595141554099206 : Fp), (4818413338202460091328447768070851017173477173576229777698353938180176055892 : Fp), (14908019327547832049053253335688031334836545726269840248359597514473981705670 : Fp), (21523647510476461082775560673900638015389610829876962091991347483461677918650 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (7124519407909476644061601315873560214171268546132147259749224767879511208526 : Fp), (9813870773946315016106397139522346734954310769450916401595122454777721695031 : Fp), (7957617585896985994558221298908444378524211062340684608379169058813459124125 : Fp), (25892320666495842991909428413718662491009959969139547015940434937720716797071 : Fp), (26009138774403902370617648263807440121147954769105221107578863101047182292538 : Fp), (27466170664826345097164396266307382202229875220353670695282326298096484999838 : Fp), (7261810992396815825306710508414309282211989790400581651923269472036607170331 : Fp), (9240242236120294292031913178789773014559483743118763280533267242642482286538 : Fp), (24071623849593521746666714637464562110070118428993134428847353045256863934406 : Fp), (8046093920254362244164683683806466735405167663914543927349685779444710749657 : Fp), (3369444797809033379666201783477116655079366548616332814949704010845941543745 : Fp), (19802659069966914682212348789938551805534491314942875900339717901145992996629 : Fp), (22615186636492186784266137470305613897599345442760345917705903292752096906310 : Fp), (27511253389181890047238778469066881135811028288809975329899823904146893298316 : Fp), (21541426521135312050214770894195162752168226972449017315542391488004636105261 : Fp), (21523647510476461082775560673900638015389610829876962091991347483461677918650 : Fp), (14876826499927746420619957460417871224337714316167249057194716327742166069782 : Fp), (14339739372910117097055178347975360900796132882571957458238212400319256396964 : Fp), (0 : Fp), (10428546187583547847415769788085032812360587405448710807098257575265481105637 : Fp), (25471840246801199573420822989476966025909527346791990446921924239261473928458 : Fp), (0 : Fp), (14339739372910117097055178347975360900796132882571957458238212400319256396964 : Fp), (268543563508814661782389556221255161770790716797645799478251963711454836409 : Fp), (17380910312639246412359616313475054687267645675747851345163762625442468509395 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (16541114414374186410966727919716922283785106442391124222423037735912461503993 : Fp), (8876573005941968478547146115745284835532102400748670531326405672563516635209 : Fp), (7257365216172337705995069980889501915496007701498661427924617664889119321498 : Fp), (26768285395752967238006275000953076092445053802944015698901042879979183995436 : Fp), (19684055716448937491261643334590454679456791870441580166015711126655560885123 : Fp), (20110303701090081505261870391676216480447424717267129704428681171086133555003 : Fp)]
def EVZW : List Fp := [(16439454869322104257790949803285360505437428967298140163974964039939064698582 : Fp), (14603788181917971557903613167324663367245585828947949002467211007261841479401 : Fp), (26299411995272010678557053079537170268419244114551598717318971433527609193211 : Fp), (677033687852569553188401330475165470487231430516801750084597838910095990668 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (22626747742589742176643848329134655730790247756794354951574771274556839047740 : Fp), (55259840651304119695738670840658847439197302763348807789709971250864526664 : Fp), (16770973281709655920145258520234590892383612378892716970434339124396067276791 : Fp), (642795910751881739326669410126934507436078693122046554479412381931888690240 : Fp), (3949518463888785340079982509801439413382334157018638132145161897193276358864 : Fp), (7808231744317858616707211799272727220963040534551443415208219416288299587977 : Fp), (15603562815152879298510474711916994608897006110191273231824508494529638738547 : Fp), (7402190389627147331798766844534393610483003560834938790433091572622382470844 : Fp), (8746957981949226270408483392506370348408613402471674688227009459672649604721 : Fp), (8942738249917550372323519119036269892194747879256135188716375637872076241625 : Fp), (14458726026020088712727579622733315923082252609093525758942422118312884708028 : Fp), (26582068571025616749697128883667509962333986830660186366533638316525708545513 : Fp), (13177354028472469160732535381443287686856854136950307591411369065491716465383 : Fp), (18112697466813162521994557688924215684425837602961091554996343622827121212254 : Fp), (26835206691721217485957258119540608961639375172446156680699806097302917160087 : Fp), (677033687852569553188401330475165470487231430516801750084597838910095990668 : Fp), (21415915549926751788448362549795246044033246061400227901065371992927301899369 : Fp), (2510702253134099022481461234125576973109936806847110938296434923807555243656 : Fp), (0 : Fp), (2945359617046938871092208755084389127134122802551682486836614436257949228783 : Fp), (8667554230760703328266845832362529278742977893129959409706020776030672800518 : Fp), (0 : Fp), (2510702253134099022481461234125576973109936806847110938296434923807555243656 : Fp), (23926617803060850810929823783920823017143182868247338839361806916734857143025 : Fp), (14558273464854581070451263342531307533011223498233324383379249648546571258084 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (3244125326228303370290757275281477329338024240392647494306206084848861676007 : Fp), (14829846334526131219993935707497929474635774740315885111097426873536011168675 : Fp), (26534459386517748364931040211755106964822790568202227434763166266261168713350 : Fp), (6266080746487092788209186828197923556446954274308172730172773762342589059686 : Fp), (19188014156135155674398288397006168938577973196898434006945528962503445581479 : Fp), (6214115658677698426529896383361450251740828614258737252179180238181561657301 : Fp)]

-- C6 (gate-constraint linConstTerm): the generic selector eval + the 15 coefficient evals at ζ
-- (from the es-order EVZ: generic_selector = EVZ[3], coefficients = EVZ[24..39]).
def GENSEL : Fp := (21523647510476461082775560673900638015389610829876962091991347483461677918650 : Fp)
def COEFFZ : List Fp := [(21523647510476461082775560673900638015389610829876962091991347483461677918650 : Fp), (14876826499927746420619957460417871224337714316167249057194716327742166069782 : Fp), (14339739372910117097055178347975360900796132882571957458238212400319256396964 : Fp), (0 : Fp), (10428546187583547847415769788085032812360587405448710807098257575265481105637 : Fp), (25471840246801199573420822989476966025909527346791990446921924239261473928458 : Fp), (0 : Fp), (14339739372910117097055178347975360900796132882571957458238212400319256396964 : Fp), (268543563508814661782389556221255161770790716797645799478251963711454836409 : Fp), (17380910312639246412359616313475054687267645675747851345163762625442468509395 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp)]

-- C3 (Fr-sponge phase-2): the real `ft_eval1` + public evals at ζ, ζω as `Nat` (K3's field-arithmetic
-- reference is over `Nat`). ft_eval1 = EVZW[1], p_zeta = EVZ[0], p_zetaomega = EVZW[0].
def FT1_N : Nat := 14603788181917971557903613167324663367245585828947949002467211007261841479401
def PZ_N  : Nat := 26721404708901961892555744407146855255897463866912334121986446595141554099206
def PZW_N : Nat := 16439454869322104257790949803285360505437428967298140163974964039939064698582

-- C9/IPA: k = 16 round prechallenges
def IPACHALS : List Fp := [(168502751509754561397993864161548947823 : Fp), (144220330568312657585943353657462097902 : Fp), (91292439177747023325472740697379656487 : Fp), (147121632673930992127923268535506615029 : Fp), (225299100781512827642804456210571796454 : Fp), (294043513123946384926411848757827173154 : Fp), (276991882787246093537087304496998026642 : Fp), (291962780853000263004592818019147672662 : Fp), (311343200217828145558973689741535632240 : Fp), (298364334135430525080770736626347152204 : Fp), (158645794374916865482305699262608665720 : Fp), (73375543542916306943514784365698208573 : Fp), (131506715783630830901612046105457933057 : Fp), (66115544769647647077265635444168405186 : Fp), (65325994132922353780164031665758551851 : Fp), (18226844549987877151250366196707599048 : Fp)]

/-! ## §3 — C1: the SHIPPED `kimchiVerifyDecision` on the REAL shape (0,5,15,6,15,7,1).

Runs the shipped decision on the real proof's actual counts. Only C1 (shape) + the three
carrier Bools; the field values do NOT enter `kimchiVerifyDecision`. -/

/-- The real proof's shape ACCEPTS (with the three carriers asserted). -/
theorem c1_real_accepts :
    kimchiVerifyDecision 0 5 15 6 15 7 1 true true true = true := by decide

/-- Each single tamper of the real shape REJECTS (the shape checks are load-bearing on real
counts): public-len 5 → 0, w-count 15 → 14, recursion prev-len 0 → 1, carriers flipped. -/
theorem c1_real_discriminates :
    kimchiVerifyDecision 0 5 15 6 15 7 1 true true true = true
    ∧ kimchiVerifyDecision 0 0 15 6 15 7 1 true true true = false   -- real public_len is load-bearing
    ∧ kimchiVerifyDecision 0 5 14 6 15 7 1 true true true = false   -- w-count
    ∧ kimchiVerifyDecision 1 5 15 6 15 7 1 true true true = false   -- prev-len (recursion)
    ∧ kimchiVerifyDecision 0 5 15 6 15 7 1 false true true = false  -- transcript carrier
    ∧ kimchiVerifyDecision 0 5 15 6 15 7 1 true false true = false  -- ipa carrier
    ∧ kimchiVerifyDecision 0 5 15 6 15 7 1 true true false = false  -- deferral carrier
    := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4 — C8: the REAL `combined_inner_product` is reproduced by the shipped formula.

`cipR` (= shipped `combinedInnerProduct`, `cipR_eq`) over the real `ZMod pN` challenges v,u and
the 45-entry es-order eval lists reproduces the Rust `oracles().combined_inner_product` EXACTLY.
This is the headline reality-gate result: the C8 aggregation transcription is faithful on the
full real eval set (15 w + 15 coeff + 6 σ + 6 selectors + z + ft + public, at ζ and ζω). -/

/-- **C8 accepts the real proof's aggregated opening value.** -/
theorem c8_real_matches : cipR VV UU EVZ EVZW = CIP := by decide

/-- Non-vacuity: bumping the FIRST real eval breaks the match (the differential has teeth). -/
theorem c8_discriminates_on_real : cipR VV UU (EVZ.set 0 (0 : Fp)) EVZW ≠ CIP := by decide

/-! ## §5 — C5/ftEval0: the REAL `ft_eval0` is reproduced by the shipped formula.

`ftEval0R` (= shipped `ftEval0` with the single field inverse supplied, `ftEval0R_eq`) over the
real ζ,β,γ,α₀,α₁,α₂, the 15 w-evals, 6 σ-evals, 7 shifts, z(ζ),z(ζω), p(ζ), and the C6
`linConstTerm` carrier + the `denomInv` carrier reproduces Rust's `oracles().ft_eval0`. The two
carriers (`LCT`, `DINV`) are GROUNDED below. -/

/-- The supplied `DENOM` is exactly Lean's ω-power denominator `(ζ − ω^{n−3})(ζ − 1)`
(cross-checks that Rust's `w() = ω^{n−3}`). -/
theorem denom_form_ok : DENOM = (ZETA - OMEGA ^ (N - 3)) * (ZETA - 1) := by decide

/-- `DINV` is the genuine multiplicative inverse of `DENOM` in `ZMod pN`. -/
theorem denom_inv_ok : DENOM * DINV = 1 := by decide

/-- **C5/ftEval0 accepts the real proof's `ft_eval0`** (linConstTerm + denomInv carried). -/
theorem c5_ft_real_matches :
    ftEval0R N OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV = FT0 := by decide

/-- Non-vacuity: bumping the linConstTerm carrier breaks the match. -/
theorem c5_discriminates_on_carrier :
    ftEval0R N OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ (LCT + 1) DINV ≠ FT0 := by
  decide

/-- Non-vacuity: bumping a WITNESS eval (`w₀`) breaks the match — the ftEval0 SHELL (σ/w folds,
numerator/denominator, public subtraction), not just the carried linConstTerm, is load-bearing. -/
theorem c5_discriminates_on_witness :
    ftEval0R N OMEGA ZETA BETA GAMMA A0 A1 A2 (WZ.set 0 (0 : Fp)) SZ SHIFT ZZ ZZW PZ LCT DINV ≠ FT0 := by
  decide

/-! ## §6 — C9: the SHIPPED `ipaDeferralOk` on the REAL k = 16 IPA rounds. -/

/-- The real proof's IPA opening has `k = 16` rounds; folding the 16 real prechallenges records
a deferral of exactly `k` challenges and `2^16` deferred terms (never materialized). -/
theorem c9_real_deferral :
    ipaDeferralOk
        (absorbChallenges (⟨[], ((0 : Fp), (0 : Fp), (0 : Fp))⟩ : IpaDeferred Fp (Fp × Fp × Fp))
          IPACHALS) 16 = true := by decide

/-- Non-vacuity: claiming `k = 15` (wrong round count) REJECTS. -/
theorem c9_deferral_discriminates :
    ipaDeferralOk
        (absorbChallenges (⟨[], ((0 : Fp), (0 : Fp), (0 : Fp))⟩ : IpaDeferred Fp (Fp × Fp × Fp))
          IPACHALS) 15 = false := by decide

/-! ## §6b — THE COMPOSED DECISION on the REAL proof (the reality-gate advance).

`kimchiVerifyDecisionField` (KimchiVerify §9b) = the shipped shape/carrier decision
(`kimchiVerifyDecision`) CONJOINED with the C8 aggregation check, the witnessed-inverse check, and
the C5 `ft(ζ)` check — all over `ZMod pN` as a `CommRing`. Here it is EVALUATED on the real proof's
actual field values: the real shape `(0,5,15,6,15,7,1)`, `N`, the real `v,u`, the 45-entry es-order
eval lists, `CIP`; the real ζ,β,γ,α's, the 15 w / 6 σ / 7 shift, `z(ζ),z(ζω),p(ζ)`, the `LCT`+`DINV`
carriers, `FT0`; and the three carriers asserted `true`. The decision ACCEPTS — so a real proof's
ARITHMETIC (C1 + C8 + C5 over the real Pasta scalar field) flows THROUGH one accept, in-kernel. -/

/-- **The composed decision ACCEPTS the real proof's arithmetic** — C1 (shape) ∧ C8 (`cip`) ∧
witnessed-inverse ∧ C5 (`ft_eval0`), all over the real `ZMod pN`, plus the three asserted carriers. -/
theorem real_field_decision_accepts :
    kimchiVerifyDecisionField (R := Fp)
        0 5 15 6 15 7 1 N
        VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2
        WZ SZ SHIFT
        ZZ ZZW PZ LCT DINV FT0
        true true true = true := by decide

/-- **Non-vacuity of the composition** — every single tamper of a value that FLOWS THROUGH the
decision rejects: the prover-supplied `cip` (C8), an es-order eval feeding `cip`, the `ft_eval0`
(C5), a witness eval feeding the C5 shell, the inverse witness `DINV`, a C1 shape count, and a
carrier. A tampered value REJECTS in-kernel — the arithmetic is load-bearing, not decorative. -/
theorem real_field_decision_discriminates :
    kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = true
    ∧ kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW (CIP + 1)
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false   -- tampered cip (C8)
    ∧ kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU (EVZ.set 0 (0 : Fp)) EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false   -- tampered es-order eval → cip
    ∧ kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV (FT0 + 1) true true true = false   -- tampered ft_eval0 (C5)
    ∧ kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 (WZ.set 0 (0 : Fp)) SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false   -- tampered witness eval → C5 shell
    ∧ kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT (DINV + 1) FT0 true true true = false   -- bogus inverse witness
    ∧ kimchiVerifyDecisionField (R := Fp) 0 0 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false   -- tampered C1 shape (public 5→0)
    ∧ kimchiVerifyDecisionField (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 false true true = false   -- tampered carrier
    := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6c — C6: the linConstTerm is DERIVED from the REAL generic gate (carrier RETIRED for this proof).

`linConstTerm = PolishToken::evaluate(constant_term)` and `index_terms = []`
(`linearization.rs:364`), so it is `Σ_gate selector·(alpha-combined constraint)`. This proof fires
ONLY the generic gate: its 5 custom-gate selectors (poseidon/complete_add/mul/emul/endomul_scalar)
are all zero at ζ, so the entire gate constant term IS the generic gate constraint over the real
coefficient + witness evals. `genericGateConstraint` reproduces the Rust `lin_const_term` (LCT)
EXACTLY, and the composed `kimchiVerifyDecisionGates` now checks `ft_eval0` from that constraint, not
from the LCT carrier. -/

/-- **The real proof's custom-gate selectors are all zero at ζ** (so nothing but the generic gate
contributes to `linConstTerm`): EVZ[4..9] = poseidon/complete_add/mul/emul/endomul_scalar selectors. -/
theorem custom_selectors_zero :
    EVZ.getD 4 1 = 0 ∧ EVZ.getD 5 1 = 0 ∧ EVZ.getD 6 1 = 0
    ∧ EVZ.getD 7 1 = 0 ∧ EVZ.getD 8 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **C6 headline: the transcribed generic gate constraint REPRODUCES the Rust `lin_const_term`.**
`genericGateConstraint genSel alpha coeff w = generic_selector·(constraint1 + alpha·constraint2)`
over the real ζ-evals equals the carrier value `LCT` EXACTLY — the `linConstTerm` carrier is
retired for this proof (its value is now DERIVED from the emitted generic gate). -/
theorem generic_gate_matches_lct : genericGateConstraint GENSEL ALPHA COEFFZ WZ = LCT := by decide

/-- Non-vacuity: bumping a coefficient eval (`c₀`) breaks the reproduction — the generic gate
constraint, not a carried constant, is what determines `linConstTerm`. -/
theorem generic_gate_discriminates_on_coeff :
    genericGateConstraint GENSEL ALPHA (COEFFZ.set 0 (0 : Fp)) WZ ≠ LCT := by decide

/-- Non-vacuity: bumping a witness eval (`w₀`) also breaks it (the double-generic `w·coeff` folds
are load-bearing). -/
theorem generic_gate_discriminates_on_witness :
    genericGateConstraint GENSEL ALPHA COEFFZ (WZ.set 0 (0 : Fp)) ≠ LCT := by decide

/-- **The gate-derived decision ACCEPTS the real proof** — `kimchiVerifyDecisionGates` with the real
generic selector + coefficient evals, custom selectors = 0 (custom bodies irrelevant, shown here as
0): C1 ∧ C8 ∧ witnessed-inverse ∧ C5-with-`ft_eval0`-from-the-generic-gate, all over `ZMod pN`. The
`linConstTerm` is no longer a carrier — it is the transcribed generic gate constraint. -/
theorem real_gate_decision_accepts :
    kimchiVerifyDecisionGates (R := Fp)
        0 5 15 6 15 7 1 N
        VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 ALPHA
        WZ SZ SHIFT COEFFZ
        GENSEL 0 0 0 0 0
        0 0 0 0 0
        ZZ ZZW PZ DINV FT0
        true true true = true := by decide

/-- Non-vacuity of the gate composition: tampering a coefficient eval (feeding the generic gate)
changes the derived `linConstTerm`, so `ft_eval0` no longer matches and the decision REJECTS. -/
theorem real_gate_decision_discriminates :
    kimchiVerifyDecisionGates (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 ALPHA WZ SZ SHIFT COEFFZ
        GENSEL 0 0 0 0 0 0 0 0 0 0 ZZ ZZW PZ DINV FT0 true true true = true
    ∧ kimchiVerifyDecisionGates (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 ALPHA WZ SZ SHIFT (COEFFZ.set 0 (0 : Fp))
        GENSEL 0 0 0 0 0 0 0 0 0 0 ZZ ZZW PZ DINV FT0 true true true = false   -- tampered coeff → linConstTerm → ft_eval0
    ∧ kimchiVerifyDecisionGates (R := Fp) 0 5 15 6 15 7 1 N VV UU EVZ EVZW CIP
        OMEGA ZETA BETA GAMMA A0 A1 A2 ALPHA WZ SZ SHIFT COEFFZ
        (GENSEL + 1) 0 0 0 0 0 0 0 0 0 0 ZZ ZZW PZ DINV FT0 true true true = false   -- tampered generic selector
    := by refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §6d — C3: the Fr-sponge INSTANTIATED over `Fp = pN` (K3's permutation), run on real evals.

The phase-2 Fr-sponge IS K3's Poseidon-over-Fp sponge (`Vesta::sponge_params() = fp_kimchi`), so its
digest is `Ref.hash` of the absorb stream. Here it CONSUMES the real proof's `ft_eval1` + public
evals (the first real absorbs after the fq-sponge digest), non-vacuously: bumping the real `ft_eval1`
changes the sponge output. The full 45-eval absorb (`frSpongeDigest`, `frEvalPointOrder`) is
instantiated in `KimchiVerify §9d`; the fq-sponge `digest` value (here a placeholder `0`) and the
`challenge()`→v/u endo map are the named residuals (`KimchiVerify §12`). -/

/-- The Fr-sponge phase-2 point order (`frEvalPointOrder`) is 43 points: `z`, 6 selectors, 15 w,
15 coeff, 6 σ (`plonk_sponge.rs:88-99`). -/
theorem fr_eval_point_order_len : frEvalPointOrder.length = 43 := by decide

/-! **The K3 Fr-sponge consumes the real transcript values non-vacuously** (`#guard` KATs — the same
kernel-evaluated check K3 uses for its Poseidon gold vectors; the deeper `by decide` proof-term path
overflows on the 255-bit permutation). Absorbing the real `ft_eval1` + the two real public evals and
squeezing (`Ref.hash`, the phase-2 Fr-sponge over `Fp`) gives a digest that CHANGES when the real
`ft_eval1`, or a real public eval, is bumped — the Fr-sponge is a genuine function of the real proof's
evaluation values (the fq-sponge digest prefix + endo map are the §12 residuals). -/
#guard Ref.hash [FT1_N, PZ_N, PZW_N] != Ref.hash [FT1_N + 1, PZ_N, PZW_N]   -- bump real ft_eval1
#guard Ref.hash [FT1_N, PZ_N, PZW_N] != Ref.hash [FT1_N, PZ_N + 1, PZW_N]   -- bump real p_zeta
#guard Ref.hash [FT1_N, PZ_N, PZW_N] != Ref.hash [FT1_N, PZ_N, PZW_N + 1]   -- bump real p_zetaomega

/-! ## §7 — C3: the real challenges (recorded; the squeeze ORDER is proven in `KimchiVerify`, the
Fr-sponge is instantiated §6d/§9d over the real evals; the fq-sponge digest VALUE + endo map remain
carried — NO full v/u differential). -/

/-- β and γ are SMALL (raw 128-bit sponge squeezes); α,ζ,v,u are full 255-bit `to_field(endo_r)`
images — matching `KimchiVerify.squeeze_order`'s raw-vs-endo flags on a REAL proof. -/
theorem c3_raw_vs_endo_shape_real :
    (BETA.val < 2 ^ 128 ∧ GAMMA.val < 2 ^ 128)
    ∧ (2 ^ 128 < ZETA.val ∧ 2 ^ 128 < ALPHA.val ∧ 2 ^ 128 < VV.val ∧ 2 ^ 128 < UU.val) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §8 — Axiom hygiene. -/

#assert_axioms cipR_eq
#assert_axioms ftEval0R_eq
#assert_axioms c1_real_accepts
#assert_axioms c1_real_discriminates
#assert_axioms c8_real_matches
#assert_axioms c8_discriminates_on_real
#assert_axioms denom_form_ok
#assert_axioms denom_inv_ok
#assert_axioms c5_ft_real_matches
#assert_axioms c5_discriminates_on_carrier
#assert_axioms c5_discriminates_on_witness
#assert_axioms real_field_decision_accepts
#assert_axioms real_field_decision_discriminates
#assert_axioms custom_selectors_zero
#assert_axioms generic_gate_matches_lct
#assert_axioms generic_gate_discriminates_on_coeff
#assert_axioms generic_gate_discriminates_on_witness
#assert_axioms real_gate_decision_accepts
#assert_axioms real_gate_decision_discriminates
#assert_axioms fr_eval_point_order_len
#assert_axioms c9_real_deferral
#assert_axioms c9_deferral_discriminates
#assert_axioms c3_raw_vs_endo_shape_real

end Dregg2.Circuit.Emit.KimchiRealProofGate
