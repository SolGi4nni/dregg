/-
# `KimchiRecursionGate` — **P6**: `prev_challenges > 0` ACCEPTED and CHECKED, on a REAL proof

## What this file is

`PicklesRecursion.wrap_prev_challenges_refused` (`5c1423632`) proved the sharpest "we do not
verify Mina" fact this tree had: the object a Mina node consumes carries `prev_challenges = 2`
(Wrap_hack, `side_loaded_verification_key.ml:236`) and K5's shape decision **refused it**, with
every other count correct. This file supersedes that theorem, and not by relaxing an assert.

The fixture is a **REAL Kimchi proof with `prev_challenges = 2`**, produced by
`ProverProof::create_recursive` over Vesta with two genuine `RecursionChallenge` accumulators
(`chals` sampled by `OsRng`, `comm = ⟨b_poly_coefficients(chals), G⟩` via `commit_non_hiding` —
the recipe of o1-labs' own `kimchi/src/tests/recursion.rs`), against a verifier index built with
`prev_challenges = 2`, and **accepted by the real `kimchi::verifier::verify`** before anything was
exported. Extractor: `kimchi/examples/pickles_p6_fq_export.rs` @ `f6d958dc05`, mirrored in this
repo at `metatheory/fixtures/kimchi-extractors/`; its ground-truth line is
`[ground truth] real verifier ACCEPTED a real proof with prev_challenges = 2`.

## What is CHECKED here that the freeze made unaskable

1. **The shape.** `shapeOkRec 2 2 …` accepts; `shapeOkRec 0 2 …` and `shapeOkRec 2 0 …` refuse.
   The freeze was not a weak version of `verifier.rs:810-813`; it was a different predicate.
2. **The fold.** Each carried `RecursionChallenge` contributes `b_poly(chals, ·)` at ζ and ζω
   (`proof.rs:459-494`) and those land at the HEAD of the `combined_inner_product` poly list
   (`verifier.rs:496-500`). Here they are RECOMPUTED from the 2 × 16 carried challenges with K4c's
   `bEval` and shown equal to the two leading entries of the real proof's evaluation columns —
   `prev_fold_is_bpoly`. A prover that writes its own numbers into those two slots is refused
   (`prev_fold_discriminates`).
3. **C8 over the FOLDED list.** The real `combined_inner_product` is reproduced over all **47**
   entries (45 at `prev_challenges = 0`, plus the two recursion evaluations) — `c8_rec_matches`.
4. **The prev-challenge DIGEST.** `verifier.rs:290-299` opens a FRESH Fr-sponge, absorbs every
   carried `chals`, and squeezes once. With two 16-challenge sets that is a **32-element**
   absorb — an EVEN length, i.e. exactly the branch K3's sponge was wrong on until `c27d690aa`.
   `prev_challenge_digest_derived` reproduces the real digest through the repaired sponge, and
   pins that the pre-repair schedule does NOT (`prev_challenge_digest_rejects_double_permute`).
   At `prev_challenges = 0` this value is `Ref.hash []`, which is why nothing noticed.
5. **β and γ.** Derived, not carried — `PastaPoseidonFq.fqPhase1`, whose absorb tape begins with
   the two recursion commitments. Same fixture, same proof.
6. **The composed accept.** `kimchiVerifyDecisionFieldRec` at `idxPrevLen = 2` over `ZMod pN`:
   shape ∧ fold ∧ C8 ∧ the witnessed inverse ∧ C5 `ft(ζ)`. Eight tampers flip it.

## What this is NOT

Not a Pickles verifier, and not a Wrap-shape verify. This is a **Step-shape** (Vesta-committed,
Fp-scalar) Kimchi proof that exercises the recursion path; a real Wrap fixture still does not
exist in this tree (`PicklesRecursion` §Z), and P3/P4 — `finalize_other_proof` and the
transcript-equality binding that makes the deferred values sound — are untouched. The
accumulator commitments are checked here only as **transcript inputs**: that `comm` really is
`⟨b_poly_coefficients(chals), G⟩` is `accumulator_check`, whose terminal `msm == 0` is the
inherited IPA opening-soundness floor (P10), not discharged anywhere.

Also unchanged: C3's phase-2 (v, u) derivation, C4's `p(ζ)` recomputation, C6's gate bodies and
C7's commitment MSM are as `KimchiPoseidonGate`/`KimchiRealProofGate` leave them; this file adds
the recursion leg, not a new floor under the others.

## Axiom hygiene

`#assert_namespace_axioms`-clean; no `sorry`, no `native_decide`. Sponge evaluations are `#guard`
(kernel evaluation), the K3 instrument; everything else is `by decide` over `ZMod pN`.

NEW standalone file. Import line for the root (do NOT edit `Dregg2.lean` from a lane):
`import Dregg2.Circuit.Emit.KimchiRecursionGate`
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaPoseidonFq

namespace Dregg2.Circuit.Emit.KimchiRecursionGate

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaIPA (bEval)
open Dregg2.Circuit.Emit.KimchiVerify
  (COLUMNS PERMUTS shapeOk shapeOkRec kimchiVerifyDecisionField kimchiVerifyDecisionFieldRec
   prevChalEvals prevChalFoldOk bEvalSq bEvalSq_eq_bEval cipR ftEval0R transcriptScheduleRec)

set_option autoImplicit false
set_option maxRecDepth 8000

/-- The Step-side scalar field: `Fp = Vesta::ScalarField = ZMod pN`. -/
abbrev Fp := ZMod pN

/-! ## §1 — The REAL `prev_challenges = 2` proof's values (decimal, `< pN`). -/

/-- Domain size (`2^5`; `max_poly_size = 65536`, so `chunk_size = 1`). -/
def N : Nat := 32
def OMEGA : Fp := (5772676229766982871441818714777438643955918462675337216809979342233538361548 : Fp)
def ZETA : Fp := (9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp)
/-- `ζω`, the second evaluation point (`verifier.rs:302`). -/
def ZETAW : Fp := ZETA * OMEGA
def BETA : Fp := (207191000514447567911742581240638307123 : Fp)
def GAMMA : Fp := (212090136106687690782051664536927829615 : Fp)
def VV : Fp := (19544871314116795727517838875197793037815458944822650859500043150633165651675 : Fp)
def UU : Fp := (4029829395372224514861218209502654028970733683372586849261102654660655230746 : Fp)
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
/-- The C8 evaluation column at ζ — **47** entries: the 2 recursion b-poly evaluations,
then public, ft, z, the 6 selectors, 15 w, 15 coefficients, 6 σ (`verifier.rs:496-600`). -/
def EVZ : List Fp :=
  [(17828066129561323373660284225674803269361090018363714112424067158784994066545 : Fp), (16155731223796678648794054144832062005213694877342714024327684304535284029140 : Fp), (16699068735930530700816957931718769427327118752981787273017885401731235465874 : Fp), (20512491975096102969445730753856641614900814594917083726254351557943483283533 : Fp), (8244319662825206332411783431566334535933848287177687988960906513771535583867 : Fp), (20289014582057077051388428879908383452560950442292165868545185027925730367812 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (8571631469098177892965262307737168137771792367786739004103898273114062670285 : Fp), (10498381543777762020631802150870211762003709095234594899293761913383977328132 : Fp), (12226728938788036639480999661017599962364448487055773636731396600382488581196 : Fp), (5707378856581365824447872698174223853012679496314514995080294844551197875781 : Fp), (22725874598313407611264545143412740301204078004768953753255037423937170617111 : Fp), (4871479349103771792541760605837981763914640577439617428271699200123592435433 : Fp), (27468350421930086744186305050869116760687727483048562429320842326053428252096 : Fp), (7852482877623881408152923783758059858364119588906157757585163529302380664242 : Fp), (17712610987890872765251184085675488375257638256291780270440669271574683981428 : Fp), (2809562589381152287364102553008182578660398152321259224004064607433802554541 : Fp), (12725230491694275861102765549546304969337542628803076138803407761907282369647 : Fp), (7651341330198429039504127155456038660566040141866927464365340559790747382195 : Fp), (17789473230049229564004961520174629180440520442392892001760357346090014021052 : Fp), (13124202080984823270185709766370374334406100446141282230912582756427552375713 : Fp), (7807586433423507120930971828781208694777921411506294439127181997722987231222 : Fp), (20289014582057077051388428879908383452560950442292165868545185027925730367812 : Fp), (9078907305375965279209769890514743833327199224670571986768068574461575630289 : Fp), (25921719874203727096156156288667062352253990073718036720365320572862775753574 : Fp), (0 : Fp), (18356861751261349991905764075586754938406398590636969255978658382003051951990 : Fp), (13179727622465582573293242809585732996106571457748717391976898382232294436228 : Fp), (0 : Fp), (25921719874203727096156156288667062352253990073718036720365320572862775753574 : Fp), (6052604870250643519473179927009829222218132816447047991178712382974383753526 : Fp), (20945428815659233701212024708587265909556312157081095187979538381888430709871 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (9377928592262762340785098454665373801944814931811295719101005621860091375496 : Fp), (20222061864450867255710902152931194513000988722830211032226108406269483319592 : Fp), (7476278879333289444878543626839011543831373682982983342588005018880166909098 : Fp), (12928632103618224043023991788970990076655059964985295017406175964126481123944 : Fp), (5818431057815805527205661029874349337966454987084644709243167839448640882189 : Fp), (9554744463517008369767910484965602220431146377570871885328571004953370013735 : Fp)]
/-- The same column at ζω. -/
def EVZW : List Fp :=
  [(3629545005364862799166977133458596102488702259123600044870959423427549231674 : Fp), (27510814418027099036823053573729904301397885501827492330796950478768959623636 : Fp), (22694988732487413569768414879304127220669743293048209292526588138156754519444 : Fp), (17308066366979432850743499843247684254717537646415512986039646514623943698673 : Fp), (28413617518552286544998492970805240901385119401424696642596595430411951585052 : Fp), (1505835031738489045669102623006506571614583572836545138415851735303544274280 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (5870691909402545263935066565046749018277504469022294653337212965826477555878 : Fp), (14737523738739915296332600783793473448999582029258305824291997712669282146479 : Fp), (7157463226911189607398504455636319912250854056680509938956891187356624411351 : Fp), (9673568260648711027815695816658608332432200180621793869269384731761497053443 : Fp), (8064661002098320303132917405207446410031037811317120498298608427478522936404 : Fp), (8547602688265030976104763696574280978880067477267074777580201575244485218808 : Fp), (1057584007922130536451983665572778898835419095801769237370991267361816924830 : Fp), (9094953297114810626338292529965261983227768658956878444491618348365948402783 : Fp), (11382464379156029713420570811206833358436500618164598282515462637937649572306 : Fp), (24209233962049081420270986979316504955351575023532551164192074227389074501314 : Fp), (5346139787901258809305404649217643906162746388548120246186895744726941521558 : Fp), (4418109022700263677774933597005093291985178241700946732110599328557438290004 : Fp), (7838213741029448028466990066039464327531111128113298710520550622320150892990 : Fp), (3682512507270624800776302659289365504313614845709736300238392151996555107787 : Fp), (11480739924566123960794658987674936286415521001293697063541849862289585666586 : Fp), (1505835031738489045669102623006506571614583572836545138415851735303544274280 : Fp), (5034121113520778284972002483993798646064648912337978424709914744467820676100 : Fp), (27269981938155456094235412090840710748008173511162234574384705182860694071637 : Fp), (0 : Fp), (6769649595146946434089025987842128673914211382721694432890448164750400964153 : Fp), (17042131674503717092565488838833941750937300527053808999672968454649844765507 : Fp), (0 : Fp), (27269981938155456094235412090840710748008173511162234574384705182860694071637 : Fp), (3356080742347185523314668322662532430709765941558652283139943162978547117400 : Fp), (1633408555468561104850794562346222135402666810555637149499188019800679063476 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (25112291877082749676115840494627210270009314399046677500547639994784416827233 : Fp), (25753815309776636893912018711466599782002461501972077920944173182670042524739 : Fp), (2862439684383872514568578117528550260380704281116603134876740328313902580774 : Fp), (23571244234724671444354123361617570561877099444212437802192226209657361424063 : Fp), (282588898942660134324302820374004985158659318752464045339180032946058454389 : Fp), (18188311822459808878175961661027514544805035333747043068419065145317553572056 : Fp)]
/-- The 2 × 16 carried IPA challenges — the `chals` of the two `RecursionChallenge`s. -/
def CHALSS : List (List Fp) :=
  [ [(18092295062020000152459079118559759050839978579931252904788383294223876010588 : Fp), (11517171405074676300473604226182287193481270927469726659704582597289895489817 : Fp), (12123978471853094157535022882399214415421961184868594147661073514660340258883 : Fp), (502804048384366980734776909225486366837349466925480002352535013409837945352 : Fp), (5909848795438591083947249604578171120921207382903297138965035922013232035306 : Fp), (15919008302543915366895562878042988357663270837781851789870918694265395181856 : Fp), (19964653882171262151686238597011792543134272476389210950573369188268118634204 : Fp), (10859861602825842246684494350443834938213237187937979522421431153004295730944 : Fp), (15344194245673113444826805593699307504191900487761254346534556070286139255628 : Fp), (1042915265610491964395708674262017603436221144734157164847966612656191127741 : Fp), (1935748257122024797610509210698528728576517697762669173457382090705403231065 : Fp), (21157362143743318378930981480351642071037275802929386935978543248262590185379 : Fp), (9488101931718861981577929816487196439822159931473166882075197306764454106568 : Fp), (10974960082905982645092122440167946532168200458451251362098354513129068284424 : Fp), (20430995063655784588680757770725945499703280063987703371040590623598588283627 : Fp), (19118188074578440139967533519220462792944894081277525751551936047011926281324 : Fp)],
    [(1310533582577817395450138227740926400276263376408513239938906754208323920578 : Fp), (16608832612103565331115073616117457368461983082571658376132575851674168650038 : Fp), (14874754841705686645399867054427180735136727334622860786285916206221422169553 : Fp), (25637072538357747518040346610373810887081897727417286684780051331189253266754 : Fp), (12356560433623274547923258924699742646985700567961581359957893594110899898452 : Fp), (18226513345872164409859688490688806400091198795481868828476970605190721836990 : Fp), (10388738566490882665634702018733743858157403770264540697147459964396211559511 : Fp), (18445177337717610454273630462851414116101824652960343124835159999166883789665 : Fp), (15397115508563272018155004969304851999499043020383336258381873330530157186256 : Fp), (15871521513516401428611484595670559673799766727338773240876503304417918108093 : Fp), (23179865599491884146749177556971678011873714086584394215589347895733868362273 : Fp), (23804539990118273741078713052506760196837135980809300189292669573684885721547 : Fp), (20880074965887080381993925074237422852183150421154657235569905276099819317681 : Fp), (5738282683921853539582658175368925170614271875074710960450577915983072541713 : Fp), (4601823898619806531881325071066546181703625617827725315538615342001031738201 : Fp), (16523275336894859116928811335428822729708784100048322437367218091219632724265 : Fp)] ]
/-- The same challenges as `Nat`s, in the order the prev-challenge Fr-sponge absorbs them
(`verifier.rs:292-296`: every set, concatenated, into ONE fresh sponge). -/
def CHALS_FLAT : List Nat :=
  [18092295062020000152459079118559759050839978579931252904788383294223876010588, 11517171405074676300473604226182287193481270927469726659704582597289895489817, 12123978471853094157535022882399214415421961184868594147661073514660340258883, 502804048384366980734776909225486366837349466925480002352535013409837945352, 5909848795438591083947249604578171120921207382903297138965035922013232035306, 15919008302543915366895562878042988357663270837781851789870918694265395181856, 19964653882171262151686238597011792543134272476389210950573369188268118634204, 10859861602825842246684494350443834938213237187937979522421431153004295730944, 15344194245673113444826805593699307504191900487761254346534556070286139255628, 1042915265610491964395708674262017603436221144734157164847966612656191127741, 1935748257122024797610509210698528728576517697762669173457382090705403231065, 21157362143743318378930981480351642071037275802929386935978543248262590185379, 9488101931718861981577929816487196439822159931473166882075197306764454106568, 10974960082905982645092122440167946532168200458451251362098354513129068284424, 20430995063655784588680757770725945499703280063987703371040590623598588283627, 19118188074578440139967533519220462792944894081277525751551936047011926281324, 1310533582577817395450138227740926400276263376408513239938906754208323920578, 16608832612103565331115073616117457368461983082571658376132575851674168650038, 14874754841705686645399867054427180735136727334622860786285916206221422169553, 25637072538357747518040346610373810887081897727417286684780051331189253266754, 12356560433623274547923258924699742646985700567961581359957893594110899898452, 18226513345872164409859688490688806400091198795481868828476970605190721836990, 10388738566490882665634702018733743858157403770264540697147459964396211559511, 18445177337717610454273630462851414116101824652960343124835159999166883789665, 15397115508563272018155004969304851999499043020383336258381873330530157186256, 15871521513516401428611484595670559673799766727338773240876503304417918108093, 23179865599491884146749177556971678011873714086584394215589347895733868362273, 23804539990118273741078713052506760196837135980809300189292669573684885721547, 20880074965887080381993925074237422852183150421154657235569905276099819317681, 5738282683921853539582658175368925170614271875074710960450577915983072541713, 4601823898619806531881325071066546181703625617827725315538615342001031738201, 16523275336894859116928811335428822729708784100048322437367218091219632724265]
/-- The real `prev_challenge_digest` (`verifier.rs:290-299`). -/
def PREV_CHAL_DIGEST : Nat := 21480403436622942531077638234364512525972774451255123199038919736314193534786

/-! ## §2 — C1: the shape decision ACCEPTS `prev_challenges = 2`.

This is the supersession of `wrap_prev_challenges_refused`. That theorem's content — that the real
count is 2 and the frozen predicate said `= 0` — was true and is now false of the shipped
decision, because the shipped decision is no longer that predicate. -/

/-- **`c1_rec_accepts`** — the real proof's counts, against an index that declares 2 previous
challenges: ACCEPTED. And the mismatches that `verifier.rs:810-813` exists to stop are refused:
a 2-challenge proof against a 0-challenge index, a 0-challenge proof against a 2-challenge index,
and a count that disagrees by one. -/
theorem c1_rec_accepts :
    shapeOkRec 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = true
    ∧ shapeOkRec 0 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false
    ∧ shapeOkRec 2 0 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false
    ∧ shapeOkRec 2 1 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **`c1_rec_supersedes_the_freeze`** — stated against the OLD predicate by name: `shapeOk` (the
non-recursive instantiation) still refuses this proof, and that is now a statement about the INDEX
it is instantiated at, not about what the verifier can express. Both halves are needed: if only the
first held, the freeze would merely have moved. -/
theorem c1_rec_supersedes_the_freeze :
    shapeOk 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false
    ∧ shapeOkRec 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`transcript_carries_the_recursion`** — the phase-1 sponge of THIS proof absorbs the two
recursion commitments before the public commitment, so the schedule the decision names is the
schedule the challenges came out of (`PastaPoseidonFq.fq_tape_shape` is the same fact on the real
coordinates). -/
theorem transcript_carries_the_recursion :
    ((transcriptScheduleRec 2).takeWhile
        (fun s => match s with | .squeeze _ _ => false | _ => true)).length = 2 + 2 + COLUMNS := by
  decide

/-! ## §3 — P6: the `RecursionChallenge` FOLD, recomputed and CHECKED. -/

/-- **`prev_fold_shape`** — two carried challenge sets of 16 rounds each (`k = ceil_log2(|srs.g|)`,
`= 16` for this index), so each contributes a `2^16`-coefficient b-polynomial — the deferred
`⟨s,G⟩` obligation K4c compresses. -/
theorem prev_fold_shape :
    CHALSS.length = 2
    ∧ (CHALSS.getD 0 []).length = 16
    ∧ (CHALSS.getD 1 []).length = 16
    ∧ CHALS_FLAT.length = 32
    ∧ EVZ.length = 47
    ∧ EVZW.length = 47 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`prev_fold_is_bpoly`** — THE P6 RESULT. The two leading entries of the real proof's
evaluation columns ARE `b_poly(chals_i, ζ)` and `b_poly(chals_i, ζω)`, recomputed here from the
carried challenges with K4c's `bEval`. The recursion is not admitted on the prover's word. -/
theorem prev_fold_is_bpoly :
    prevChalFoldOk ZETA ZETAW CHALSS EVZ EVZW = true := by decide

/-- The same fact spelled out entry by entry, so the `take`/`map` shape cannot hide a length
mismatch that made the comparison vacuous. Stated through `bEvalSq` — the squaring ladder of
`commitment.rs:429-433` — because `Monoid.npow` at `2^15` is 32768 kernel recursion steps; the next
theorem is the same four equations about K4c's `bEval` itself. -/
theorem prev_fold_entries :
    EVZ.getD 0 0 = bEvalSq ZETA (CHALSS.getD 0 [])
    ∧ EVZ.getD 1 0 = bEvalSq ZETA (CHALSS.getD 1 [])
    ∧ EVZW.getD 0 0 = bEvalSq ZETAW (CHALSS.getD 0 [])
    ∧ EVZW.getD 1 0 = bEvalSq ZETAW (CHALSS.getD 1 [])
    ∧ prevChalEvals ZETA CHALSS = [EVZ.getD 0 0, EVZ.getD 1 0] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`prev_fold_entries_are_bEval`** — and those four values ARE K4c's `bEval`, so the object the
gate compares against is the one `sVec_eq_bPoly` proves is the deferred `⟨s,G⟩` coefficient vector.
No `decide` here: it is `bEvalSq_eq_bEval` (proved for every point and every challenge list)
applied to the theorem above. -/
theorem prev_fold_entries_are_bEval :
    EVZ.getD 0 0 = bEval ZETA (CHALSS.getD 0 [])
    ∧ EVZ.getD 1 0 = bEval ZETA (CHALSS.getD 1 [])
    ∧ EVZW.getD 0 0 = bEval ZETAW (CHALSS.getD 0 [])
    ∧ EVZW.getD 1 0 = bEval ZETAW (CHALSS.getD 1 []) := by
  obtain ⟨h0, h1, h2, h3, _⟩ := prev_fold_entries
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← bEvalSq_eq_bEval]; exact h0
  · rw [← bEvalSq_eq_bEval]; exact h1
  · rw [← bEvalSq_eq_bEval]; exact h2
  · rw [← bEvalSq_eq_bEval]; exact h3

/-- **`prev_fold_discriminates`** — the fold check is not true for free. Tampering either leading
evaluation, either carried challenge, or the evaluation point breaks it; and swapping the two
proofs' evaluations breaks it, which a length-only check would not catch. -/
theorem prev_fold_discriminates :
    prevChalFoldOk ZETA ZETAW CHALSS (EVZ.set 0 0) EVZW = false
    ∧ prevChalFoldOk ZETA ZETAW CHALSS EVZ (EVZW.set 1 0) = false
    ∧ prevChalFoldOk ZETA ZETAW
        [(CHALSS.getD 0 []).set 3 0, CHALSS.getD 1 []] EVZ EVZW = false
    ∧ prevChalFoldOk ZETA ZETAW [CHALSS.getD 1 [], CHALSS.getD 0 []] EVZ EVZW = false
    ∧ prevChalFoldOk ZETAW ZETA CHALSS EVZ EVZW = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`prev_fold_is_prefix_only`** — an honest LIMIT of the fold check, stated rather than left to
be discovered: `prevChalFoldOk` constrains only the leading `chalss.length` entries, so a prover
that DECLARES fewer challenge sets than the proof carries passes it. That is exactly why
`kimchiVerifyDecisionFieldRec` also checks `chalss.length = idxPrevLen` — and the second clause is
that count doing the work the fold cannot. -/
theorem prev_fold_is_prefix_only :
    prevChalFoldOk ZETA ZETAW [CHALSS.getD 0 []] EVZ EVZW = true
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 [CHALSS.getD 0 []]
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §4 — The prev-challenge DIGEST: the even-length branch, live.

`verifier.rs:290-299` builds the value with a FRESH `EFrSponge` — for a Vesta-committed proof that
is `fp_kimchi` over `ZMod pN`, i.e. K3's sponge — absorbing every carried `chals` and squeezing
once. `FrSponge::digest` is `self.sponge.squeeze()` (`plonk_sponge.rs:52-54`), so the value is
exactly `Ref.hash (chals_0 ++ chals_1)`.

With `prev_challenges = 2 × 16` that is a **32-element absorb**. Until `c27d690aa` this tree's
sponge permuted once too often on every nonzero even length, so this digest would have been wrong
and the whole phase-2 transcript with it — and the only reason nothing caught it is that the
value being pinned at the time was `Ref.hash []`. -/

/-! ⚑ **`prev_challenge_digest_derived`** — the real digest, reproduced. (`#guard`: 17 permutations
of a 255-bit state.) -/
#guard PastaPoseidon.Ref.hash CHALS_FLAT == PREV_CHAL_DIGEST

/-! The pre-repair schedule does NOT reproduce it — the negative pin, on a 32-element input, aimed
at the exact defect. -/
#guard (PastaPoseidon.Ref.perm (PastaPoseidon.Ref.absorbAll [0, 0, 0] CHALS_FLAT)).getD 0 0
  != PREV_CHAL_DIGEST

/-! Non-vacuity: perturbing ONE carried challenge — the last one, in the second proof's set —
moves the digest, so every challenge of every carried proof is inside the transcript. -/
#guard PastaPoseidon.Ref.hash (CHALS_FLAT.set 31 0) != PREV_CHAL_DIGEST
#guard PastaPoseidon.Ref.hash (CHALS_FLAT.set 0 0) != PREV_CHAL_DIGEST
/-! And that the empty case — what the freeze made this value be — is a DIFFERENT number, so the
v1 pin could not have detected any of the above. -/
#guard PastaPoseidon.Ref.hash [] != PREV_CHAL_DIGEST

/-! ## §5 — C8 over the FOLDED poly list, and C5 `ft(ζ)`. -/

/-- **`c8_rec_matches`** — the real `combined_inner_product` is reproduced over all 47 entries,
recursion evaluations included. At 45 entries (the non-recursive shape) it is a different value —
the second clause — so the two leading entries are load-bearing in the aggregation, not decoration
sitting beside it. -/
theorem c8_rec_matches :
    cipR VV UU EVZ EVZW = CIP
    ∧ cipR VV UU (EVZ.drop 2) (EVZW.drop 2) ≠ CIP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`c5_rec_matches`** — `ft(ζ)` on this proof, with the witnessed inverse checked in-ring. -/
theorem c5_rec_matches :
    ((ZETA - OMEGA ^ (N - 3)) * (ZETA - 1)) * DINV = 1
    ∧ ftEval0R N OMEGA ZETA BETA GAMMA A0 A1 A2 WZ SZ SHIFT ZZ ZZW PZ LCT DINV = FT0 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §6 — THE COMPOSED ACCEPT: a real `prev_challenges = 2` proof, accepted. -/

/-- ⚑ **`rec_decision_accepts`** — `kimchiVerifyDecisionFieldRec` at `idxPrevLen = 2` over
`ZMod pN`: the shape assert against a recursive index, the count, the `RecursionChallenge` fold,
C8 over the folded list, the witnessed inverse and C5. This is the theorem
`wrap_prev_challenges_refused` was the negation of. -/
theorem rec_decision_accepts :
    kimchiVerifyDecisionFieldRec (R := Fp)
        2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP
        OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0
        true true true = true := by decide

/-- **`rec_decision_discriminates`** — eight tampers, each aimed at a different conjunct: the
declared index count, the proof's count, a carried challenge, a recursion evaluation, a
non-recursion evaluation, the aggregation, the inverse, and `ft(ζ)`. -/
theorem rec_decision_discriminates :
    kimchiVerifyDecisionFieldRec (R := Fp) 0 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 1 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
        [(CHALSS.getD 0 []).set 7 0, CHALSS.getD 1 []]
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU (EVZ.set 1 0) EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU (EVZ.set 20 0) EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW (CIP + 1) OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT (DINV + 1) FT0 true true true = false
    ∧ kimchiVerifyDecisionFieldRec (R := Fp) 2 2 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 CHALSS
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV (FT0 + 1) true true true = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`rec_extends_not_replaces`** — the same decision at `idxPrevLen = 0` with no carried
challenges IS the pre-existing `kimchiVerifyDecisionField`, so the single-proof leg is untouched by
P6 (it is `kimchiVerifyDecisionFieldRec_at_zero` instantiated at this fixture's arguments, stated
here so the claim is visible beside the recursive accept). -/
theorem rec_extends_not_replaces :
    kimchiVerifyDecisionFieldRec (R := Fp) 0 0 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2 []
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true
      = kimchiVerifyDecisionField (R := Fp) 0 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
        VV UU EVZ EVZW CIP OMEGA ZETA BETA GAMMA A0 A1 A2
        WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true :=
  KimchiVerify.kimchiVerifyDecisionFieldRec_at_zero (R := Fp)
    0 5 COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
    VV UU EVZ EVZW CIP OMEGA ZETA ZETAW BETA GAMMA A0 A1 A2
    WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true

/-! ## §7 — Residuals (the honest distance from here to verifying a Mina block).

1. **Wrap shape, not built.** This is a Step-shape (Vesta-committed, `k = 16`) proof. The object a
   node consumes is a Pallas-committed Wrap proof with `k = 15`, and no real Wrap fixture exists
   in this tree.
2. **The accumulator commitments are transcript inputs only.** `comm = ⟨b_poly_coefficients(chals),
   G⟩` is `accumulator_check` (`PicklesRecursion` P1) and bottoms out at `msm == 0` — P10.
3. **P3 / P4 untouched.** `finalize_other_proof` and the transcript-equality binding are what make
   deferred values SOUND; nothing here bears on them.
4. **Batching.** One proof, not `batch_verify`; the `OsRng` batching scalars remain out of scope.
5. **The IPA/FRI opening-soundness floor (P10)** is inherited, as everywhere in this stack. -/

#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiRecursionGate

end Dregg2.Circuit.Emit.KimchiRecursionGate
