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
def ZETA : Fp := (3242641747343358285403216843779007425102558896530829051099340042431498988749 : Fp)
/-- `ζω`, the second evaluation point (`verifier.rs:302`). -/
def ZETAW : Fp := ZETA * OMEGA
def BETA : Fp := (240548146413621476668740835522772226069 : Fp)
def GAMMA : Fp := (241703423401682125519342778721978438694 : Fp)
def VV : Fp := (4186707569988943034807380272994050367599666141577665462651549664359921881213 : Fp)
def UU : Fp := (19947958055847190924269739849420343684098151417245777565348665223269623922120 : Fp)
def A0 : Fp := (13864706159109512016390652994724174925751643578188816340594549151376649122091 : Fp)
def A1 : Fp := (23827664632000405375055855582294609045652013723260997041026303226271186180561 : Fp)
def A2 : Fp := (6013612635319254545406818096247831444904526133820888581105286916152790969071 : Fp)
def PZ : Fp := (19995033465063115652663564020970136650572877752113024793295052918290025874336 : Fp)
def ZZ : Fp := (6816511055334519322928239986873399304883340785105701361826118708084670628036 : Fp)
def ZZW : Fp := (16588736169657859832818982166016886800948328821512341467744675454709578364626 : Fp)
def LCT : Fp := (25728814620824280381592223824862971856945026619561256975586757515831425822777 : Fp)
def DINV : Fp := (21910620102277114762178503851787683933303661777884796090327531050619004741906 : Fp)
def FT0 : Fp := (22195176326693713956833489056421560337057901975039017443885748072596415964672 : Fp)
def CIP : Fp := (10796838930333281746730029294849637252225970147510513348832332023353889909529 : Fp)
def SHIFT : List Fp :=
  [(1 : Fp), (328286983623303317637963920346571898945724874896624808297627776768640590563 : Fp), (91433028157768305433241271390810941046493237899366836746431422160024463706 : Fp), (240213425742950025341713987028051046476975246675775993287051503548513551377 : Fp), (417757293700961807788464308236931191792053554682199437460107260306038610067 : Fp), (430348682428487492383428014506756320686619984007091686553051322507181255952 : Fp), (326625242707153437805405281465150497418605074624614708160829052937679007395 : Fp)]
def WZ : List Fp :=
  [(8976388248201069003102901818801981600249617146180483267716608582055541364753 : Fp), (8948916756689964736948589315734843554883338726627607264641813035121872317170 : Fp), (28037687677311475821470887261428671190791417530442210690503821889680634858950 : Fp), (6905295967871998254482587446168454284922887945403389907724707120470678551266 : Fp), (24032064025700948928224366908276496011980228778602717815208173715957291130489 : Fp), (5720732212924924891585669860429286239181433839409586891399476543713228352815 : Fp), (17232064625162991721336259495572914091606172831263938581791446759806710841 : Fp), (7476064053943939306378380298614258021819341015903448507750857523811484689928 : Fp), (28781031611337315619366833422848367763807109012663202836743102425337513724144 : Fp), (9550332455471888987573149004804301332091909867224078632270158012677742682538 : Fp), (12364102073817466443391654963047238310055299728470088427996769228389681232171 : Fp), (11585767430912540524073694170518936617385997523348027476192740146832735950662 : Fp), (2414632477031840417032237293791696621647295602133002466235054596124256178358 : Fp), (11146308807695915887564952700505399439523449940432645983336790311623285570621 : Fp), (2093890603749602009277080126608454023899295150776133537754163090927237581398 : Fp)]
def SZ : List Fp :=
  [(3242641747343358285403216843779007425102558896530829051099340042431498988749 : Fp), (18658358405031214352312144889667117381276959402002818378327966023504607026687 : Fp), (28729595420714182371411507978042245369444140470839319180196133968372759490846 : Fp), (14690591478389100958513750681168950621978414516383353898178930826883735030827 : Fp), (3501620372520985624258080681588205728224604586020735580563568059832246872306 : Fp), (28826196839263832232909169556880642834182528982160835285675233284415621027384 : Fp)]
/-- The C8 evaluation column at ζ — **47** entries: the 2 recursion b-poly evaluations,
then public, ft, z, the 6 selectors, 15 w, 15 coefficients, 6 σ (`verifier.rs:496-600`). -/
def EVZ : List Fp :=
  [(553286606650676908098126481479669253089233879265701624480816752609716668075 : Fp), (3791075778026204124965426822637358985546576055378308738745854009695291361854 : Fp), (19995033465063115652663564020970136650572877752113024793295052918290025874336 : Fp), (22195176326693713956833489056421560337057901975039017443885748072596415964672 : Fp), (6816511055334519322928239986873399304883340785105701361826118708084670628036 : Fp), (2219518907432254778061496016585971797286200046309960058619682386745738677979 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (8976388248201069003102901818801981600249617146180483267716608582055541364753 : Fp), (8948916756689964736948589315734843554883338726627607264641813035121872317170 : Fp), (28037687677311475821470887261428671190791417530442210690503821889680634858950 : Fp), (6905295967871998254482587446168454284922887945403389907724707120470678551266 : Fp), (24032064025700948928224366908276496011980228778602717815208173715957291130489 : Fp), (5720732212924924891585669860429286239181433839409586891399476543713228352815 : Fp), (17232064625162991721336259495572914091606172831263938581791446759806710841 : Fp), (7476064053943939306378380298614258021819341015903448507750857523811484689928 : Fp), (28781031611337315619366833422848367763807109012663202836743102425337513724144 : Fp), (9550332455471888987573149004804301332091909867224078632270158012677742682538 : Fp), (12364102073817466443391654963047238310055299728470088427996769228389681232171 : Fp), (11585767430912540524073694170518936617385997523348027476192740146832735950662 : Fp), (2414632477031840417032237293791696621647295602133002466235054596124256178358 : Fp), (11146308807695915887564952700505399439523449940432645983336790311623285570621 : Fp), (2093890603749602009277080126608454023899295150776133537754163090927237581398 : Fp), (2219518907432254778061496016585971797286200046309960058619682386745738677979 : Fp), (12943767501998803892061770852537602212291378372249878404017685787876720091064 : Fp), (5334751602443414987943658466544791583690559369897227437312330325491082513091 : Fp), (0 : Fp), (15238199623967972761106465033981527133222956963148534150818262473699445813128 : Fp), (4569940895120358698262093739396816610046699839597675521712138096883507272403 : Fp), (0 : Fp), (5334751602443414987943658466544791583690559369897227437312330325491082513091 : Fp), (18278519104442218880005429319082393795981937742147105841330016113367802604155 : Fp), (6098317833727255364582277555187893913129557283953183107393986279932431268322 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (3242641747343358285403216843779007425102558896530829051099340042431498988749 : Fp), (18658358405031214352312144889667117381276959402002818378327966023504607026687 : Fp), (28729595420714182371411507978042245369444140470839319180196133968372759490846 : Fp), (14690591478389100958513750681168950621978414516383353898178930826883735030827 : Fp), (3501620372520985624258080681588205728224604586020735580563568059832246872306 : Fp), (28826196839263832232909169556880642834182528982160835285675233284415621027384 : Fp)]
/-- The same column at ζω. -/
def EVZW : List Fp :=
  [(6031807245423889575028145268604597241206483329481930409143280618060830637674 : Fp), (11142058567801800315966838525802060138509478632036557938003043601108812255177 : Fp), (19903540908219688933804402399231635780350616540972299269489580979626555552246 : Fp), (11101915443780821457556723444379868753529346804668145201496334253953294573899 : Fp), (16588736169657859832818982166016886800948328821512341467744675454709578364626 : Fp), (6967805125177524458365915891918297937797435989640738730682101374299954556760 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (13403376089947071150624481422519467275350189621673792620276624537444883370119 : Fp), (18477370566305554346483018908880678451233333116910922921927636137954866251658 : Fp), (5276327991100616814572979163251037173860205469769915550949578096562322513307 : Fp), (22369107330854858880791711972315306195200720355750881486141342582808971401900 : Fp), (17182046479472106386853102192197021016798838155820765192088974082641116956715 : Fp), (5530654714788981686397830252140845964684207138783348014563194115916447695016 : Fp), (18889344502688144416091369842216559161358816530053276433499754876038809739034 : Fp), (22709634378387679851879966724920724547079453504809321708565909707768383844061 : Fp), (22723683333025591407532868319877265334666252997738899144881814215895381406886 : Fp), (7577199958295809529260089609483448583491598746064231733900390757283385861265 : Fp), (22687934428335209163423424614295965768721949908708596131969606848996842472375 : Fp), (16744693838703268122309548282464436672623920941575373189134203955848067138023 : Fp), (18071145827976893219188765675178396059934159450447538416096982411810389825227 : Fp), (18642227843035595124004479936770227782363530200589473274251849651983667732037 : Fp), (22209933134580143156617203998815250778898197486698304817772286597062170426053 : Fp), (6967805125177524458365915891918297937797435989640738730682101374299954556760 : Fp), (18283300127225085199997948760947332898830293919250548704298813703017295520545 : Fp), (13204248163811004170595847914465540342631939681544190909203513275227546580043 : Fp), (0 : Fp), (6424366152801871746988544938132780268450425891297593958717605364840843928356 : Fp), (7507885385509059036301400438013065564970876863547988919079023799836374567327 : Fp), (0 : Fp), (13204248163811004170595847914465540342631939681544190909203513275227546580043 : Fp), (2539525981707040514701050423240896278099177118853178897547650213894874470251 : Fp), (20356617691112802530278490314278626101871728646143176836514234529518062424039 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (0 : Fp), (3300434977468224527436494964523212999936128245481517992528070373004910304169 : Fp), (9565816594759743653997123796859082737328196737893281493877609514935934185457 : Fp), (28775241026100644757681344034069258969951594353733400006881092396352895398698 : Fp), (19811582106629238513680209259864531709193737621786355813757268688158159926919 : Fp), (14574395836343914294354842939695092309895730417627136318031721650510762796427 : Fp), (2059501150522323314101889662213571576554529004805567149555351363326836072899 : Fp)]
/-- The 2 × 16 carried IPA challenges — the `chals` of the two `RecursionChallenge`s. -/
def CHALSS : List (List Fp) :=
  [ [(13534394658088920002056490396437331589125363224433998944103785083248673514042 : Fp), (26561092365052448704331650576818516483568548716723736563017965473762327657535 : Fp), (3013001210057895849893850358524107903465455406877524210109774881231927220720 : Fp), (8510194698857431987085919702154645169595103615986267677372685534315294168419 : Fp), (14765508651964718553241122615354738302770021625480300281334807186463526797731 : Fp), (28718879534918634392762244779912801375804764065061838918837012960151218532879 : Fp), (16462710270401021537155183889726060402932042198664760574993819744742465016485 : Fp), (13131808481229151413519463080762992254600149765047138600683035388510580879304 : Fp), (27408020392290618071967829577920976034744251282796824560566512306762837636621 : Fp), (17280801084627116327147226631876654934093020310661023277313621614269340194430 : Fp), (11605737267636852077289814215157531205612743115214709421831393888104268334572 : Fp), (27577465431833535856909693762851988865302761420624435151024297149600154530250 : Fp), (16187122190836604910114238179413465853065805662552600088150763376003759141698 : Fp), (8695320185626030719878066738077423690922128683706889111218852675578678699681 : Fp), (1552522260301604259952043181704331500665582446752437695130617382641298790746 : Fp), (21130466238337180981188032359120920763713321084302424865587554799333093648683 : Fp)],
    [(8920706082783643895138545416189481882016891436137317900756579868729308923233 : Fp), (24345630436084318307358685711112794591815835954382124096364695721707942240248 : Fp), (11998266626265627346538101999552721325582499984026770928821575027212688631187 : Fp), (15275423059405999952198264534047969449041781761294759268750816189663698126085 : Fp), (10717310568664961762473283979153231177454804818810994192439025234597784647252 : Fp), (16725813892446757390859998011710666026408849425207232910136311897171822124696 : Fp), (26157920074478578910070076842269039754151822778399079997615245375948231832435 : Fp), (9426811871617013289354601138104201516829991497511391770820098608014809833006 : Fp), (25399616598739682846323372000351735912230542638198786435193269963869784662862 : Fp), (6392516755438435350898857341332226410215136389041222426422196914775923332061 : Fp), (27582451488022923358117733129449765581713451495673111555274363817832388099932 : Fp), (20808420234831642871183509504107369191885950429489617997132773773024347820380 : Fp), (25181742471183761472128098664735407607450631878674217439127881871740024115609 : Fp), (23139992800549343650488445618359033116933600307548287934957508246100902587960 : Fp), (24976508378138392908713585237875929696509262303180454007917798480840998021326 : Fp), (23438514166486396023065229965206569387647421701617614679262288921713457216467 : Fp)] ]
/-- The same challenges as `Nat`s, in the order the prev-challenge Fr-sponge absorbs them
(`verifier.rs:292-296`: every set, concatenated, into ONE fresh sponge). -/
def CHALS_FLAT : List Nat :=
  [13534394658088920002056490396437331589125363224433998944103785083248673514042, 26561092365052448704331650576818516483568548716723736563017965473762327657535, 3013001210057895849893850358524107903465455406877524210109774881231927220720, 8510194698857431987085919702154645169595103615986267677372685534315294168419, 14765508651964718553241122615354738302770021625480300281334807186463526797731, 28718879534918634392762244779912801375804764065061838918837012960151218532879, 16462710270401021537155183889726060402932042198664760574993819744742465016485, 13131808481229151413519463080762992254600149765047138600683035388510580879304, 27408020392290618071967829577920976034744251282796824560566512306762837636621, 17280801084627116327147226631876654934093020310661023277313621614269340194430, 11605737267636852077289814215157531205612743115214709421831393888104268334572, 27577465431833535856909693762851988865302761420624435151024297149600154530250, 16187122190836604910114238179413465853065805662552600088150763376003759141698, 8695320185626030719878066738077423690922128683706889111218852675578678699681, 1552522260301604259952043181704331500665582446752437695130617382641298790746, 21130466238337180981188032359120920763713321084302424865587554799333093648683, 8920706082783643895138545416189481882016891436137317900756579868729308923233, 24345630436084318307358685711112794591815835954382124096364695721707942240248, 11998266626265627346538101999552721325582499984026770928821575027212688631187, 15275423059405999952198264534047969449041781761294759268750816189663698126085, 10717310568664961762473283979153231177454804818810994192439025234597784647252, 16725813892446757390859998011710666026408849425207232910136311897171822124696, 26157920074478578910070076842269039754151822778399079997615245375948231832435, 9426811871617013289354601138104201516829991497511391770820098608014809833006, 25399616598739682846323372000351735912230542638198786435193269963869784662862, 6392516755438435350898857341332226410215136389041222426422196914775923332061, 27582451488022923358117733129449765581713451495673111555274363817832388099932, 20808420234831642871183509504107369191885950429489617997132773773024347820380, 25181742471183761472128098664735407607450631878674217439127881871740024115609, 23139992800549343650488445618359033116933600307548287934957508246100902587960, 24976508378138392908713585237875929696509262303180454007917798480840998021326, 23438514166486396023065229965206569387647421701617614679262288921713457216467]
/-- The real `prev_challenge_digest` (`verifier.rs:290-299`). -/
def PREV_CHAL_DIGEST : Nat := 5930015970704746696928432828207287416872696149855186865514660785627112055547

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
