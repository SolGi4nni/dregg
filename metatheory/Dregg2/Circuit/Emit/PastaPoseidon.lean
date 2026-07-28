/-
# Dregg2.Circuit.Emit.PastaPoseidon — a Lean-GENERATED Poseidon-over-Pasta-Fp sponge
(the Fiat–Shamir transcript primitive of an in-Lean Kimchi (Mina) proof verifier; task K3 of
`docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## Why this file exists (the carrier it is aimed at)

Kimchi's Fiat–Shamir transcript is `Poseidon.hash` over the **Pallas base field Fp** with the
**Kimchi sponge constants** (`PlonkSpongeConstantsKimchi`): every proof commitment is absorbed and
every challenge is squeezed through this permutation. This file is that primitive, GENERATED
(House Law #1) over K1's forced Fp arithmetic (`PastaField`, commit `1ba1d6613`): the S-box, the
MDS matvec, and the round-constant add are def-generators whose gates are PROVEN to force the real
Poseidon round function mod the real Pasta prime, the round composes, and the whole 55-round
permutation is forced by a `List.range` fold induction (the `Sha256FoldForcing` discipline —
`foldl_cstep_forces` — at field instead of bit granularity). Poseidon is FIELD ops (muls/adds), not
bit ops, so there is no bit-column machinery here: value heads only, exactly as advertised in K1.

This is the SPONGE slice, honestly named: a KAT'd + forced Poseidon permutation + sponge over Fp.
It is NOT an IPA MSM (K4), NOT a Kimchi verifier (K5).

## The EXACT Kimchi Poseidon params (VERIFIED against the pinned source + a Python recomputation)

SOURCE: `mina-poseidon` of o1-labs `proof-systems` at rev `36a8b510` — the EXACT rev pinned by this
repo's `circuit-prove/sketches/mina-pasta-hash-probe/Cargo.toml` (and by `storage/Cargo.toml` for
poly-commitment) — files `poseidon/src/constants.rs`, `poseidon/src/permutation.rs`,
`poseidon/src/poseidon.rs`, `poseidon/src/pasta/fp_kimchi.rs`:

  * width 3 = rate 2 + capacity 1 (`SPONGE_WIDTH`/`SPONGE_RATE`/`SPONGE_CAPACITY`).
  * S-box exponent **α = 7** (`PERM_SBOX = 7`; `sbox()` computes `x·x²·(x²)²` — here the gate chain
    `t2 = x·x`, `t3 = t2·x`, `t4 = t2·t2`, `z = t3·t4`, four `fpMul`s).
  * round split: **55 full rounds, 0 partial rounds** (`PERM_ROUNDS_FULL = 55`,
    `PERM_ROUNDS_PARTIAL = 0`, `PERM_HALF_ROUNDS_FULL = 0`), full MDS (`PERM_FULL_MDS = true`),
    **no initial ARK** (`PERM_INITIAL_ARK = false`).
  * round `r` (`full_round`, `permutation.rs:55-70`), in order: **(1) S-box on all 3 lanes,
    (2) the 3×3 MDS matvec, (3) add `round_constants[r]`**. The permutation is the fold of the 55
    rounds (`poseidon_block_cipher`, the `PERM_HALF_ROUNDS_FULL == 0 ∧ ¬PERM_INITIAL_ARK` branch).
  * the MDS matrix and the 55×3 round constants below were DUMPED from the pinned crate
    (`fp_kimchi::static_params()`, via a scratch bin on the probe's lockfile) as decimal Fp values.
  * sponge semantics (`ArithmeticSponge` absorb/squeeze, `poseidon.rs:107-146`): zero initial
    state; absorb ADDS each input into `state[n]` (`n < rate`), permuting when an element ARRIVES
    to find the rate already full — never on the way out, so a final full block is left unpermuted;
    squeeze from `Absorbed(_)` permutes once and reads `state[0]`. This is o1js `Poseidon.hash`
    exactly (the probe's `main.rs` documents why, including the empty-input case permuting the zero
    state once). `Ref.absorbFrom` is that state machine transcribed, lane counter and all.

VERIFICATION (re-measured 2026-07-27, after the even-length defect below): the reference reproduces
all NINE of the probe's o1js-1.9.1 gold KATs (`bridge/mina-zkapp/scripts/poseidon-kat.mjs`, pasted
in the probe's `main.rs`) bit-exactly — empty, `[0]`, `[1]`, `[2]`, `[0,1,2]`, `[1,2,3,4,5]`
(multi-block), `[p−1]`, `[p−1,p−1]`, `[123456789, 987654321]` — and the probe's tenth gold, the o1js
`MerkleTree` depth-2 root over leaves `[1,2,3,4]`. **§5 pins all ten in-kernel**, both even-length
vectors included, plus the two DOUBLE-PERMUTE values as rejects.

⚑ WHAT THIS PARAGRAPH USED TO SAY, AND WHY IT WAS FALSE. Until 2026-07-27 it claimed "an
independent Python recomputation … reproduces ALL NINE" while `Ref.absorbAll` permuted twice on
every input of nonzero EVEN length (see `absorbFrom`). It reproduced SEVEN. The two it failed were
`[123456789, 987654321]` and `[p−1, p−1]` — precisely the only two even-length golds, and precisely
the two the `#guard` set did not pin, so the instrument could not go red. (The Python was not
independent; it shared the bug.) The claim "the `#guard`s below pin six of them" was also wrong —
there were seven. Recorded here rather than deleted: the lesson is that a KAT set whose omissions
line up exactly with a definition's untested branch is not evidence, and the header sentence that
asserts coverage is the one to check against the pins.

## The gadget shape (over K1's heads)

  * `sboxLaneGates` — four `fpMulCore` value gates (K1's degree-2 `fpMulHead`): `t2 = x·x`,
    `t3 = t2·x`, `t4 = t2·t2`, `z = t3·t4` ⟹ `z ≡ x⁷ (mod p)`.
  * `fpSMulCore` — multiply by a BAKED Fp constant `m` (the MDS entries): degree-1 head
    `m·xVal − p·qVal − zVal` (a constant `fpMul` needs no cross terms).
  * `rcAddCore` — add a BAKED Fp constant `rc`: head `xVal + rc − zVal − p·c` (`c` = carry bit).
  * `mdsRowGates` — one MDS row: three `fpSMulCore` + two `fpAddCore`.
  * `roundGates` — 3 sbox lanes (12 gates) + 3 MDS rows (15 gates) + 3 RC lanes (3 gates) = 30 value gates, 468 aux columns
    (layout in §3); `permGates` — the 55 rounds folded (`List.range 55` flatMap, 25 740 columns,
    1650 value gates). The rounds compose free — round `r+1`'s input lanes ARE round `r`'s RC-output
    lanes (`rcZ (auxB r) 0 = inB (r+1)` definitionally).
  * the sponge: `absorbBlockGates` (two `fpAddCore` — add the two rate inputs into the state
    lanes) + `permGates`; squeeze reads rate lane 0 (no gates — a projection).

## What is AUTHORED + built vs NAMED mechanical continuation

AUTHORED + built: the baked Kimchi params (`mdsN`/`rcsN`); the `Nat` reference (`Ref.sbox`/
`Ref.round`/`Ref.perm`/`Ref.absorbFrom`/`Ref.absorbAll`/`Ref.hash`); the generators
(`sboxLaneGates`/`fpSMulCore`/
`rcAddCore`/`mdsRowGates`/`roundGates`/`permGates`/`absorbBlockGates`); the forcing lemmas —
`sboxLane_forces` (S-box), `fpSMulCore_forces`/`rcAddCore_forces` (atomics), `mdsRow_forces`,
`round_forces` (the round composing), and **`perm_forces`** (the whole 55-round permutation, by the
fold induction `permFrom_forces`), all as `ZMod pN` equalities composing K1's ℤ-congruence forcings;
`absorbBlock_forces` for the sponge's absorb add. AUTHORED + KAT'd both-polarity: the reference is
#guard-anchored to SIX real o1js `Poseidon.hash` gold vectors (plus a tamper non-vacuity #guard),
and one FULL ROUND of the real `hash([1])` trace (round 0 over input state `[1,0,0]`, honest
witness computed by the reference itself) is ACCEPTED by the generated gates and REJECTED under two
distinct limb bumps. NAMED continuation: the whole-permutation accept-KAT in-kernel (residual 2);
the hash-level gate fold (residual 3); the shared K1 residuals (residual 4).

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. The `#guard` KATs reduce in the kernel. NEW standalone file; imports
`PastaField` (K1); NOT imported by the `Dregg2` root (built directly as
`Dregg2.Circuit.Emit.PastaPoseidon`).
-/
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.PastaPoseidon

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN p numLimbs fpValue fpVal fpVal_eq fpAddHead fpMulHead
  fpAddCore fpMulCore fpAddCore_forces fpMulCore_forces gateBodyEvalZero acceptB bumpAt)

set_option autoImplicit false

/-! ## §0 — The baked Kimchi Poseidon params (dumped from `mina-poseidon` rev `36a8b510`,
`pasta::fp_kimchi::static_params()`; see the header for the source + the verification). -/

/-- Full rounds (`PERM_ROUNDS_FULL`). Partial rounds = 0, so this is the whole schedule. -/
def rounds : Nat := 55
/-- Sponge rate (`SPONGE_RATE`); width 3 = rate + capacity 1. -/
def rate : Nat := 2
/-- S-box exponent (`PERM_SBOX`). -/
def sboxAlpha : Nat := 7
/-- The Kimchi MDS matrix, row-major (`static_params().mds`, dumped from the pinned crate). -/
def mdsN : List (List Nat) :=
  [ [12035446894107573964500871153637039653510326950134440362813193268448863222019,
    25461374787957152039031444204194007219326765802730624564074257060397341542093,
    27667907157110496066452777015908813333407980290333709698851344970789663080149],
    [4491931056866994439025447213644536587424785196363427220456343191847333476930,
    14743631939509747387607291926699970421064627808101543132147270746750887019919,
    9448400033389617131295304336481030167723486090288313334230651810071857784477],
    [10525578725509990281643336361904863911009900817790387635342941550657754064843,
    27437632000253211280915908546961303399777448677029255413769125486614773776695,
    27566319851776897085443681456689352477426926500749993803132851225169606086988] ]

/-- The 55×3 Kimchi round constants (`static_params().round_constants`, dumped from the pinned
crate; row `r` is added to the state AFTER the MDS of round `r`). -/
def rcsN : List (List Nat) :=
  [     [21155079691556475130150866428468322463125560312786319980770950159250751855431,
     16883442198399350202652499677723930673110172289234921799701652810789093522349,
     17030687036425314703519085065002231920937594822150793091243263847382891822670],
    [25216718237129482752721276445368692059997901880654047883630276346421457427360,
     9054264347380455706540423067244764093107767235485930776517975315876127782582,
     26439087121446593160953570192891907825526260324480347638727375735543609856888],
    [15251000790817261169639394496851831733819930596125214313084182526610855787494,
     10861916012597714684433535077722887124099023163589869801449218212493070551767,
     18597653523270601187312528478986388028263730767495975370566527202946430104139],
    [15831416454198644276563319006805490049460322229057756462580029181847589006611,
     15171856919255965617705854914448645702014039524159471542852132430360867202292,
     15488495958879593647482715143904752785889816789652405888927117106448507625751],
    [19039802679983063488134304670998725949842655199289961967801223969839823940152,
     4720101937153217036737330058775388037616286510783561045464678919473230044408,
     10226318327254973427513859412126640040910264416718766418164893837597674300190],
    [20878756131129218406920515859235137275859844638301967889441262030146031838819,
     7178475685651744631172532830973371642652029385893667810726019303466125436953,
     1996970955918516145107673266490486752153434673064635795711751450164177339618],
    [15205545916434157464929420145756897321482314798910153575340430817222504672630,
     25660296961552699573824264215804279051322332899472350724416657386062327210698,
     13842611741937412200312851417353455040950878279339067816479233688850376089318],
    [1383799642177300432144836486981606294838630135265094078921115713566691160459,
     1135532281155277588005319334542025976079676424839948500020664227027300010929,
     4384117336930380014868572224801371377488688194169758696438185377724744869360],
    [21725577575710270071808882335900370909424604447083353471892004026180492193649,
     676128913284806802699862508051022306366147359505124346651466289788974059668,
     25186611339598418732666781049829183886812651492845008333418424746493100589207],
    [10402240124664763733060094237696964473609580414190944671778761753887884341073,
     11918307118590866200687906627767559273324023585642003803337447146531313172441,
     16895677254395661024186292503536662354181715337630376909778003268311296637301],
    [23818602699032741669874498456696325705498383130221297580399035778119213224810,
     4285193711150023248690088154344086684336247475445482883105661485741762600154,
     19133204443389422404056150665863951250222934590192266371578950735825153238612],
    [5515589673266504033533906836494002702866463791762187140099560583198974233395,
     11830435563729472715615302060564876527985621376031612798386367965451821182352,
     7510711479224915247011074129666445216001563200717943545636462819681638560128],
    [24694843201907722940091503626731830056550128225297370217610328578733387733444,
     27361655066973784653563425664091383058914302579694897188019422193564924110528,
     21606788186194534241166833954371013788633495786419718955480491478044413102713],
    [19934060063390905409309407607814787335159021816537006003398035237707924006757,
     8495813630060004961768092461554180468161254914257386012937942498774724649553,
     27524960680529762202005330464726908693944660961000958842417927307941561848461],
    [15178481650950399259757805400615635703086255035073919114667254549690862896985,
     16164780354695672259791105197274509251141405713012804937107314962551600380870,
     10529167793600778056702353412758954281652843049850979705476598375597148191979],
    [721141070179074082553302896292167103755384741083338957818644728290501449040,
     22044408985956234023934090378372374883099115753118261312473550998188148912041,
     27068254103241989852888872162525066148367014691482601147536314217249046186315],
    [3880429241956357176819112098792744584376727450211873998699580893624868748961,
     17387097125522937623262508065966749501583017524609697127088211568136333655623,
     6256814421247770895467770393029354017922744712896100913895513234184920631289],
    [2942627347777337187690939671601251987500285937340386328746818861972711408579,
     24031654937764287280548628128490074801809101323243546313826173430897408945397,
     14401457902976567713827506689641442844921449636054278900045849050301331732143],
    [20170632877385406450742199836933900257692624353889848352407590794211839130727,
     24056496193857444725324410428861722338174099794084586764867109123681727290181,
     11257913009612703357266904349759250619633397075667824800196659858304604714965],
    [22228158921984425749199071461510152694025757871561406897041788037116931009246,
     9152163378317846541430311327336774331416267016980485920222768197583559318682,
     13906695403538884432896105059360907560653506400343268230130536740148070289175],
    [7220714562509721437034241786731185291972496952091254931195414855962344025067,
     27608867305903811397208862801981345878179337369367554478205559689592889691927,
     13288465747219756218882697408422850918209170830515545272152965967042670763153],
    [8251343892709140154567051772980662609566359215743613773155065627504813327653,
     22035238365102171608166944627493632660244312563934708756134297161332908879090,
     13560937766273321037807329177749403409731524715067067740487246745322577571823],
    [21652518608959234550262559135285358020552897349934571164032339186996805408040,
     22479086963324173427634460342145551255011746993910136574926173581069603086891,
     13676501958531751140966255121288182631772843001727158043704693838707387130095],
    [5680310394102577950568930199056707827608275306479994663197187031893244826674,
     25125360450906166639190392763071557410047335755341060350879819485506243289998,
     22659254028501616785029594492374243581602744364859762239504348429834224676676],
    [23101411405087512171421838856759448177512679869882987631073569441496722536782,
     24149774013240355952057123660656464942409328637280437515964899830988178868108,
     5782097512368226173095183217893826020351125522160843964147125728530147423065],
    [13540762114500083869920564649399977644344247485313990448129838910231204868111,
     20421637734328811337527547703833013277831804985438407401987624070721139913982,
     7742664118615900772129122541139124149525273579639574972380600206383923500701],
    [1109643801053963021778418773196543643970146666329661268825691230294798976318,
     16580663920817053843121063692728699890952505074386761779275436996241901223840,
     14638514680222429058240285918830106208025229459346033470787111294847121792366],
    [17080385857812672649489217965285727739557573467014392822992021264701563205891,
     26176268111736737558502775993925696791974738793095023824029827577569530708665,
     4382756253392449071896813428140986330161215829425086284611219278674857536001],
    [13934033814940585315406666445960471293638427404971553891617533231178815348902,
     27054912732979753314774418228399230433963143177662848084045249524271046173121,
     28916070403698593376490976676534962592542013020010643734621202484860041243391],
    [24820015636966360150164458094894587765384135259446295278101998130934963922381,
     7969535238488580655870884015145760954416088335296905520306227531221721881868,
     7690547696740080985104189563436871930607055124031711216224219523236060212249],
    [9712576468091272384496248353414290908377825697488757134833205246106605867289,
     12148698031438398980683630141370402088785182722473169207262735228500190477924,
     14359657643133476969781351728574842164124292705609900285041476162075031948227],
    [23563839965372067275137992801035780013422228997724286060975035719045352435470,
     4184634822776323233231956802962638484057536837393405750680645555481330909086,
     16249511905185772125762038789038193114431085603985079639889795722501216492487],
    [11001863048692031559800673473526311616702863826063550559568315794438941516621,
     4702354107983530219070178410740869035350641284373933887080161024348425080464,
     23751680507533064238793742311430343910720206725883441625894258483004979501613],
    [28670526516158451470169873496541739545860177757793329093045522432279094518766,
     3568312993091537758218792253361873752799472566055209125947589819564395417072,
     1819755756343439646550062754332039103654718693246396323207323333948654200950],
    [5372129954699791301953948907349887257752247843844511069896766784624930478273,
     17512156688034945920605615850550150476471921176481039715733979181538491476080,
     25777105342317622165159064911913148785971147228777677435200128966844208883059],
    [25350392006158741749134238306326265756085455157012701586003300872637887157982,
     20096724945283767296886159120145376967480397366990493578897615204296873954844,
     8063283381910110762785892100479219642751540456251198202214433355775540036851],
    [4393613870462297385565277757207010824900723217720226130342463666351557475823,
     9874972555132910032057499689351411450892722671352476280351715757363137891038,
     23590926474329902351439438151596866311245682682435235170001347511997242904868],
    [17723373371137275859467518615551278584842947963894791032296774955869958211070,
     2350345015303336966039836492267992193191479606566494799781846958620636621159,
     27755207882790211140683010581856487965587066971982625511152297537534623405016],
    [6584607987789185408123601849106260907671314994378225066806060862710814193906,
     609759108847171587253578490536519506369136135254150754300671591987320319770,
     28435187585965602110074342250910608316032945187476441868666714022529803033083],
    [16016664911651770663938916450245705908287192964254704641717751103464322455303,
     17551273293154696089066968171579395800922204266630874071186322718903959339163,
     20414195497994754529479032467015716938594722029047207834858832838081413050198],
    [19773307918850685463180290966774465805537520595602496529624568184993487593855,
     24598603838812162820757838364185126333280131847747737533989799467867231166980,
     11040972566103463398651864390163813377135738019556270484707889323659789290225],
    [5189242080957784038860188184443287562488963023922086723850863987437818393811,
     1435203288979376557721239239445613396009633263160237764653161500252258220144,
     13066591163578079667911016543985168493088721636164837520689376346534152547210],
    [17345901407013599418148210465150865782628422047458024807490502489711252831342,
     22139633362249671900128029132387275539363684188353969065288495002671733200348,
     1061056418502836172283188490483332922126033656372467737207927075184389487061],
    [10241738906190857416046229928455551829189196941239601756375665129874835232299,
     27808033332417845112292408673209999320983657696373938259351951416571545364415,
     18820154989873674261497645724903918046694142479240549687085662625471577737140],
    [7983688435214640842673294735439196010654951226956101271763849527529940619307,
     17067928657801807648925755556866676899145460770352731818062909643149568271566,
     24472070825156236829515738091791182856425635433388202153358580534810244942762],
    [25752201169361795911258625731016717414310986450004737514595241038036936283227,
     26041505376284666160132119888949817249574689146924196064963008712979256107535,
     23977050489096115210391718599021827780049209314283111721864956071820102846008],
    [26678257097278788410676026718736087312816016749016738933942134600725962413805,
     10480026985951498884090911619636977502506079971893083605102044931823547311729,
     21126631300593007055117122830961273871167754554670317425822083333557535463396],
    [1564862894215434177641156287699106659379648851457681469848362532131406827573,
     13247162472821152334486419054854847522301612781818744556576865965657773174584,
     8673615954922496961704442777870253767001276027366984739283715623634850885984],
    [2794525076937490807476666942602262298677291735723129868457629508555429470085,
     4656175953888995612264371467596648522808911819700660048695373348629527757049,
     23221574237857660318443567292601561932489621919104226163978909845174616477329],
    [1878392460078272317716114458784636517603142716091316893054365153068227117145,
     2370412714505757731457251173604396662292063533194555369091306667486647634097,
     17409784861870189930766639925394191888667317762328427589153989811980152373276],
    [25869136641898166514111941708608048269584233242773814014385564101168774293194,
     11361209360311194794795494027949518465383235799633128250259863567683341091323,
     14913258820718821235077379851098720071902170702113538811112331615559409988569],
    [12957012022018304419868287033513141736995211906682903915897515954290678373899,
     17128889547450684566010972445328859295804027707361763477802050112063630550300,
     23329219085372232771288306767242735245018143857623151155581182779769305489903],
    [1607741027962933685476527275858938699728586794398382348454736018784568853937,
     2611953825405141009309433982109911976923326848135736099261873796908057448476,
     7372230383134982628913227482618052530364724821976589156840317933676130378411],
    [20203606758501212620842735123770014952499754751430660463060696990317556818571,
     4678361398979174017885631008335559529633853759463947250620930343087749944307,
     27176462634198471376002287271754121925750749676999036165457559387195124025594],
    [6361981813552614697928697527332318530502852015189048838072565811230204474643,
     13815234633287489023151647353581705241145927054858922281829444557905946323248,
     10888828634279127981352133512429657747610298502219125571406085952954136470354] ]

/-- MDS entry `j,i` (row `j`, column `i`) as a `Nat`; `0` out of range. -/
def mc (j i : Nat) : Nat := (mdsN.getD j []).getD i 0

#guard mdsN.length == 3
#guard rcsN.length == rounds
#guard (rcsN.all (fun r => r.length == 3)) == true
#guard (mdsN.all (fun r => r.length == 3)) == true

/-! ## §1 — The `Nat` reference (kernel-reducible), anchored to the o1js gold KATs in §5. -/

namespace Ref

/-- The Kimchi S-box `x^α`, `α = 7`. -/
def sbox (x : Nat) : Nat := x ^ sboxAlpha % pN

/-- One Poseidon round over the 3-lane state: S-box, then MDS matvec, then add the round's
constants — `full_round` of the pinned `permutation.rs`. `rc` is the round's 3 constants. -/
def round (rc : List Nat) (hs : List Nat) : List Nat :=
  (List.range 3).map (fun j =>
    (mc j 0 * sbox (hs.getD 0 0) + mc j 1 * sbox (hs.getD 1 0) + mc j 2 * sbox (hs.getD 2 0)
      + rc.getD j 0) % pN)

/-- Rounds `r0 .. r0+n−1` folded over the state (the `List.range` shape the fold forcing
induction threads). -/
def permFrom (r0 n : Nat) (hs : List Nat) : List Nat :=
  (List.range n).foldl (fun st i => round (rcsN.getD (r0 + i) []) st) hs

/-- The full Kimchi Poseidon permutation: the 55 rounds folded, no initial ARK
(`poseidon_block_cipher` of the pinned `permutation.rs`). -/
def perm (hs : List Nat) : List Nat := permFrom 0 rounds hs

/-- Add input `x` into state lane `j` (the sponge's absorb add; field addition). -/
def absorbAt (st : List Nat) (j x : Nat) : List Nat := st.set j ((st.getD j 0 + x) % pN)

/-- **The absorb loop, transcribed from the upstream STATE MACHINE** (`poseidon.rs:107-126`), with
`n` the `SpongeState.Absorbed n` lane counter. Upstream permutes inside `absorb` only when an
element ARRIVES and finds the rate already full — never on the way out. So a final full rate block
is absorbed and left unpermuted; `squeeze` (the `[]` clause) supplies the one closing permutation
from `Absorbed(_)`.

⚑ THIS SHAPE IS THE FIX, AND IT IS STRUCTURAL. Until 2026-07-27 the loop was a three-clause
block recursion whose `x :: y :: rest` clause permuted the finished block and then recursed into
`rest`; at `rest = []` that fell into the `[]` clause and permuted a SECOND time, so every input of
nonzero EVEN length got one permutation too many. The lane counter cannot express that bug: the
permutation is triggered by an arriving element, exactly as upstream, so there is no "is this the
last block?" case to get wrong. (The clause-ordering repair — insert a `[x, y]` case ahead of the
cons-cons case — computes the same function, but rebuilds the fix on the same fragility that broke
it.) §5 pins both even-length o1js golds and REJECTS the two double-permute values. -/
def absorbFrom (st : List Nat) (n : Nat) : List Nat → List Nat
  | [] => perm st
  | x :: rest =>
      if n = rate then absorbFrom (absorbAt (perm st) 0 x) 1 rest
      else absorbFrom (absorbAt st n x) (n + 1) rest

/-- The o1js/`ArithmeticSponge` absorb+squeeze state machine for one hash: absorb at `rate = 2`
(zero-padding a partial final block is a no-op because absorb ADDS), permuting when a full block
is absorbed and more input arrives; the final squeeze permutes once and the caller reads lane 0.
For `[]` this permutes the zero state once, exactly as `ArithmeticSponge.squeeze` from
`Absorbed(0)` does. Starts at `Absorbed(0)`, the state `ArithmeticSponge.new` installs. -/
def absorbAll (st : List Nat) (xs : List Nat) : List Nat := absorbFrom st 0 xs

/-- o1js `Poseidon.hash` over Fp: zero initial state, absorb, one squeeze = lane 0. -/
def hash (xs : List Nat) : Nat := (absorbAll [0, 0, 0] xs).getD 0 0

end Ref

/-! ## §2 — The gate heads + generators (GENERATED per gadget, over K1's Fp heads). -/

/-- **`fpSMulHead`** — `m·xVal − p·qVal − zVal`, `m` a BAKED Fp constant (an MDS entry). Degree 1
(a constant `fpMul` has no cross terms); the quotient-witness reduction is K1's. Zero forces
`m·x ≡ z (mod p)`. -/
def fpSMulHead (xB zB qB : Nat) (m : ℤ) : Head :=
  ((fpValue xB).scale m).append (((fpValue qB).scale (-p)).append ((fpValue zB).scale (-1)))

/-- **`rcAddHead`** — `xVal + rc − zVal − p·c`, `rc` a BAKED Fp constant (a round constant),
`c` the carry bit. Zero forces `x + rc ≡ z (mod p)`. -/
def rcAddHead (xB zB cCol : Nat) (rc : ℤ) : Head :=
  (((fpValue xB).append ((fpValue zB).scale (-1))).addLin (-p) cCol).addConst rc

/-- `fpSMul` value gate. -/
def fpSMulCore (xB zB qB : Nat) (m : ℤ) : VmConstraint2 := cgH (fpSMulHead xB zB qB m)
/-- `rcAdd` value gate. -/
def rcAddCore (xB zB cCol : Nat) (rc : ℤ) : VmConstraint2 := cgH (rcAddHead xB zB cCol rc)

/-- **One S-box lane** — `z ≡ x⁷ (mod p)` as four K1 `fpMul` value gates:
`t2 = x·x` (at `b`, quotient `b+9`), `t3 = t2·x` (`b+18`, `b+27`), `t4 = t2·t2` (`b+36`, `b+45`),
`z = t3·t4` (`b+54`, `b+63`). -/
def sboxLaneGates (xB b : Nat) : List VmConstraint2 :=
  [ fpMulCore xB xB b (b + 9)
  , fpMulCore b xB (b + 18) (b + 27)
  , fpMulCore b b (b + 36) (b + 45)
  , fpMulCore (b + 18) (b + 36) (b + 54) (b + 63) ]

/-- The S-box lane's output column base. -/
def sboxOut (b : Nat) : Nat := b + 54

/-- **One MDS row** — `z ≡ m₀·x₀ + m₁·x₁ + m₂·x₂ (mod p)`: three constant-muls (`tᵢ` at `b`,
`b+18`, `b+36`) summed by two K1 `fpAdd`s (`s₁ = t₀ + t₁` at `b+54` carry `b+63`;
`z = s₁ + t₂` at `b+64` carry `b+73`). -/
def mdsRowGates (x0B x1B x2B b : Nat) (m0 m1 m2 : Nat) : List VmConstraint2 :=
  [ fpSMulCore x0B b (b + 9) (m0 : ℤ)
  , fpSMulCore x1B (b + 18) (b + 27) (m1 : ℤ)
  , fpSMulCore x2B (b + 36) (b + 45) (m2 : ℤ)
  , fpAddCore b (b + 18) (b + 54) (b + 63)
  , fpAddCore (b + 54) (b + 36) (b + 64) (b + 73) ]

/-- The MDS row's output column base. -/
def mdsOut (b : Nat) : Nat := b + 64

/-! ## §3 — The round layout + the folded round/permutation generators.

Per round over aux base `aux` (468 columns): S-box lane `j` at `aux + 72·j` (216 cols), MDS row
`j` at `aux + 216 + 74·j` (222 cols), RC lane `j` output at `aux + 438 + 9·j` with its carry at
`aux + 438 + 27 + j` (30 cols). The RC outputs sit at a 9-column stride, so the round's output
lanes ARE `StateIsZ`-shaped at `rcZ aux 0` — and `rcZ aux 0 = aux + 438` is the next round's
input base (`inB (r+1) = auxB r + 438` definitionally): the rounds compose free. -/

/-- S-box lane `j` block base. -/
def sbZ (aux j : Nat) : Nat := aux + 72 * j
/-- MDS row `j` block base. -/
def mdZ (aux j : Nat) := aux + 216 + 74 * j
/-- RC lane `j` output base. -/
def rcZ (aux j : Nat) := aux + 438 + 9 * j
/-- RC lane `j` carry column. -/
def rcC (aux j : Nat) := aux + 438 + 27 + j
/-- Aux columns consumed per round. -/
def roundAux : Nat := 468

/-- **One Poseidon round** (30 value gates): 3 S-box lanes (input lanes at `in0`, `in0+9`,
`in0+18`), 3 MDS rows over the S-box outputs, 3 RC adds of `rc`'s constants onto the MDS outputs. -/
def roundGates (in0 aux : Nat) (rc : List Nat) : List VmConstraint2 :=
  sboxLaneGates in0 (sbZ aux 0) ++ sboxLaneGates (in0 + 9) (sbZ aux 1)
    ++ sboxLaneGates (in0 + 18) (sbZ aux 2)
    ++ mdsRowGates (sboxOut (sbZ aux 0)) (sboxOut (sbZ aux 1)) (sboxOut (sbZ aux 2))
         (mdZ aux 0) (mc 0 0) (mc 0 1) (mc 0 2)
    ++ mdsRowGates (sboxOut (sbZ aux 0)) (sboxOut (sbZ aux 1)) (sboxOut (sbZ aux 2))
         (mdZ aux 1) (mc 1 0) (mc 1 1) (mc 1 2)
    ++ mdsRowGates (sboxOut (sbZ aux 0)) (sboxOut (sbZ aux 1)) (sboxOut (sbZ aux 2))
         (mdZ aux 2) (mc 2 0) (mc 2 1) (mc 2 2)
    ++ [ rcAddCore (mdsOut (mdZ aux 0)) (rcZ aux 0) (rcC aux 0) ((rc.getD 0 0 : Nat) : ℤ)
       , rcAddCore (mdsOut (mdZ aux 1)) (rcZ aux 1) (rcC aux 1) ((rc.getD 1 0 : Nat) : ℤ)
       , rcAddCore (mdsOut (mdZ aux 2)) (rcZ aux 2) (rcC aux 2) ((rc.getD 2 0 : Nat) : ℤ) ]

/-- The aux base of round `r` (the input state lives at columns `0..26`). -/
def auxB (r : Nat) : Nat := 27 + roundAux * r
/-- The input-lane base of round `r`: round `0` reads the state columns `0..26`; round `r+1`
reads round `r`'s RC outputs (`rcZ (auxB r) 0 = auxB r + 438` definitionally). -/
def inB : Nat → Nat
  | 0 => 0
  | r + 1 => auxB r + 438

/-- Round `r`'s gates at the folded layout (round constants `rcsN[r]`). -/
def roundGatesAt (r : Nat) : List VmConstraint2 := roundGates (inB r) (auxB r) (rcsN.getD r [])

/-- Rounds `r0 .. r0+n−1` folded. -/
def permGatesFrom (r0 n : Nat) : List VmConstraint2 :=
  (List.range n).flatMap (fun i => roundGatesAt (r0 + i))

/-- **The whole 55-round Kimchi Poseidon permutation** — 1650 value gates over 25 740 columns. -/
def permGates : List VmConstraint2 := permGatesFrom 0 rounds

/-- **One sponge absorb block** (rate 2): add the two inputs into state lanes 0 and 1
(two K1 `fpAdd` value gates). Squeeze reads lane 0 — a projection, no gates. -/
def absorbBlockGates (stB x0B x1B outB c0 c1 : Nat) : List VmConstraint2 :=
  [ fpAddCore stB x0B outB c0, fpAddCore (stB + 9) x1B (outB + 9) c1 ]

/-! ## §4 — The gates FORCE the Poseidon function (mod the real Pasta prime, `ZMod pN` reading).

K1's atomic forcings are ℤ congruences (`p ∣ u − v`); the composition currency here is equality
in `ZMod pN`. `zmod_eq_of_dvd` is the bridge. No `native_decide`; the quotient/carry witnesses
keep every step a ℤ identity. -/

/-- Bridge: `p ∣ u − v` IS `(v : ZMod pN) = u`. -/
theorem zmod_eq_of_dvd {u v : ℤ} (h : (p : ℤ) ∣ u - v) : (v : ZMod pN) = (u : ZMod pN) := by
  rw [ZMod.intCast_eq_intCast_iff]
  exact Int.modEq_iff_dvd.mpr h

/-- `fpMulCore` zero forces `z = x·y` in `ZMod pN` (K1's `fpMulCore_forces`, recast). -/
theorem fpMulCore_zmod (a : Assignment) (xB yB zB qB : Nat)
    (hg : evalH (fpMulHead xB yB zB qB) a = 0) :
    (fpVal a zB : ZMod pN) = (fpVal a xB : ZMod pN) * fpVal a yB := by
  have h := zmod_eq_of_dvd (fpMulCore_forces a xB yB zB qB hg)
  rw [h]; push_cast; ring

/-- `fpAddCore` zero forces `z = x + y` in `ZMod pN` (K1's `fpAddCore_forces`, recast). -/
theorem fpAddCore_zmod (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fpAddHead xB yB zB cCol) a = 0) :
    (fpVal a zB : ZMod pN) = (fpVal a xB : ZMod pN) + fpVal a yB := by
  have h := zmod_eq_of_dvd (fpAddCore_forces a xB yB zB cCol hg)
  rw [h]; push_cast; ring

/-- **`fpSMulCore` forces `m·x ≡ z (mod p)`** (the ℤ congruence, K1 style). -/
theorem fpSMulCore_forces (a : Assignment) (xB zB qB : Nat) (m : ℤ)
    (hg : evalH (fpSMulHead xB zB qB m) a = 0) :
    (p : ℤ) ∣ m * fpVal a xB - fpVal a zB := by
  simp only [fpSMulHead, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨fpVal a qB, by linarith⟩

/-- **`rcAddCore` forces `x + rc ≡ z (mod p)`** (the ℤ congruence, K1 style). -/
theorem rcAddCore_forces (a : Assignment) (xB zB cCol : Nat) (rc : ℤ)
    (hg : evalH (rcAddHead xB zB cCol rc) a = 0) :
    (p : ℤ) ∣ fpVal a xB + rc - fpVal a zB := by
  simp only [rcAddHead, evalH_addConst, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨a cCol, by linarith⟩

/-- `fpSMulCore` zero forces `z = m·x` in `ZMod pN`. -/
theorem fpSMulCore_zmod (a : Assignment) (xB zB qB : Nat) (m : ℤ)
    (hg : evalH (fpSMulHead xB zB qB m) a = 0) :
    (fpVal a zB : ZMod pN) = ((m : ℤ) : ZMod pN) * fpVal a xB := by
  have h := zmod_eq_of_dvd (fpSMulCore_forces a xB zB qB m hg)
  rw [h]; push_cast; ring

/-- `rcAddCore` zero forces `z = x + rc` in `ZMod pN`. -/
theorem rcAddCore_zmod (a : Assignment) (xB zB cCol : Nat) (rc : ℤ)
    (hg : evalH (rcAddHead xB zB cCol rc) a = 0) :
    (fpVal a zB : ZMod pN) = (fpVal a xB : ZMod pN) + ((rc : ℤ) : ZMod pN) := by
  have h := zmod_eq_of_dvd (rcAddCore_forces a xB zB cCol rc hg)
  rw [h]; push_cast; ring

-- acceptB algebra (the `Sha256FoldForcing` discipline, re-derived locally over K1's `acceptB`)

/-- Acceptance distributes over `++`. -/
theorem acceptB_append (l1 l2 : List VmConstraint2) (a : Assignment) :
    acceptB (l1 ++ l2) a = (acceptB l1 a && acceptB l2 a) := by
  simp [acceptB, List.all_append]

/-- A `cgH` gate's body evaluates to its head's value. -/
theorem gateBodyEvalZero_cgH (a : Assignment) (h : Head) :
    gateBodyEvalZero a (cgH h) = decide (evalH h a = 0) := by
  simp only [cgH, cg, gateBodyEvalZero, headToExpr_eval]

/-- From acceptance of a constraint list, any `cgH` member's head evaluates to zero. -/
theorem evalH_of_accept (a : Assignment) (h : Head) (gs : List VmConstraint2)
    (hg : cgH h ∈ gs) (hacc : acceptB gs a = true) : evalH h a = 0 := by
  simp only [acceptB, List.all_eq_true] at hacc
  have hb := hacc _ hg
  rw [gateBodyEvalZero_cgH] at hb
  exact of_decide_eq_true hb

/-- **`sboxLane_forces`** — the four accepted mul gates FORCE `z = x⁷` in `ZMod pN` (the real
Kimchi S-box, `sbox()` of the pinned `poseidon.rs`: `x·x²·(x²)²`). -/
theorem sboxLane_forces (a : Assignment) (xB b : Nat)
    (hacc : acceptB (sboxLaneGates xB b) a = true) :
    (fpVal a (sboxOut b) : ZMod pN) = (fpVal a xB : ZMod pN) ^ sboxAlpha := by
  have h2 := fpMulCore_zmod a xB xB b (b + 9)
    (evalH_of_accept a _ _ (List.Mem.head _) hacc)
  have h3 := fpMulCore_zmod a b xB (b + 18) (b + 27)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.head _)) hacc)
  have h4 := fpMulCore_zmod a b b (b + 36) (b + 45)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hacc)
  have hz := fpMulCore_zmod a (b + 18) (b + 36) (b + 54) (b + 63)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) hacc)
  show (fpVal a (b + 54) : ZMod pN) = (fpVal a xB : ZMod pN) ^ 7
  rw [hz, h3, h4, h2]; ring

/-- **`mdsRow_forces`** — the accepted row gates FORCE `z = m₀·x₀ + m₁·x₁ + m₂·x₂` in `ZMod pN`
(one row of the MDS matvec, `apply_mds_matrix` of the pinned `permutation.rs`). -/
theorem mdsRow_forces (a : Assignment) (x0B x1B x2B b : Nat) (m0 m1 m2 : Nat)
    (hacc : acceptB (mdsRowGates x0B x1B x2B b m0 m1 m2) a = true) :
    (fpVal a (mdsOut b) : ZMod pN)
      = (m0 : ZMod pN) * fpVal a x0B + (m1 : ZMod pN) * fpVal a x1B
        + (m2 : ZMod pN) * fpVal a x2B := by
  have h0 := fpSMulCore_zmod a x0B b (b + 9) (m0 : ℤ)
    (evalH_of_accept a _ _ (List.Mem.head _) hacc)
  have h1 := fpSMulCore_zmod a x1B (b + 18) (b + 27) (m1 : ℤ)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.head _)) hacc)
  have h2 := fpSMulCore_zmod a x2B (b + 36) (b + 45) (m2 : ℤ)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hacc)
  have hs := fpAddCore_zmod a b (b + 18) (b + 54) (b + 63)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) hacc)
  have hz := fpAddCore_zmod a (b + 54) (b + 36) (b + 64) (b + 73)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))) hacc)
  show (fpVal a (b + 64) : ZMod pN)
      = (m0 : ZMod pN) * fpVal a x0B + (m1 : ZMod pN) * fpVal a x1B
        + (m2 : ZMod pN) * fpVal a x2B
  rw [hz, hs, h0, h1, h2]; push_cast; ring

/-- **The composable state relation** — the three 9-limb lanes at `base`, `base+9`, `base+18`
hold (`ZMod pN`) the reference state `hs`. The `ℤ ↔ p_felt` gap and the `z < p` canonical
compare are the shared K1 residuals (§7); the congruence content is what the gates force. -/
def StateIsZ (a : Assignment) (base : Nat) (hs : List Nat) : Prop :=
  (fpVal a base : ZMod pN) = ((hs.getD 0 0 : Nat) : ZMod pN) ∧
  (fpVal a (base + 9) : ZMod pN) = ((hs.getD 1 0 : Nat) : ZMod pN) ∧
  (fpVal a (base + 18) : ZMod pN) = ((hs.getD 2 0 : Nat) : ZMod pN)

/-- Lane `j` of the reference round, as a Nat identity (the `getD` on the mapped range). -/
theorem getD_round (rc hs : List Nat) (j : Nat) (hj : j < 3) :
    (Ref.round rc hs).getD j 0 =
      (mc j 0 * Ref.sbox (hs.getD 0 0) + mc j 1 * Ref.sbox (hs.getD 1 0)
        + mc j 2 * Ref.sbox (hs.getD 2 0) + rc.getD j 0) % pN := by
  interval_cases j <;> rfl

/-- **`round_forces`** — the accepted 30 round gates FORCE the output lanes to the reference
`Ref.round` of the input state: S-box, then MDS, then round-constant add, in `ZMod pN`. -/
theorem round_forces (a : Assignment) (in0 aux : Nat) (rc hs : List Nat)
    (hst : StateIsZ a in0 hs)
    (hacc : acceptB (roundGates in0 aux rc) a = true) :
    StateIsZ a (rcZ aux 0) (Ref.round rc hs) := by
  obtain ⟨hst0, hst1, hst2⟩ := hst
  unfold roundGates at hacc
  rw [acceptB_append, Bool.and_eq_true] at hacc; obtain ⟨hacc, hRc⟩ := hacc
  rw [acceptB_append, Bool.and_eq_true] at hacc; obtain ⟨hacc, hM2⟩ := hacc
  rw [acceptB_append, Bool.and_eq_true] at hacc; obtain ⟨hacc, hM1⟩ := hacc
  rw [acceptB_append, Bool.and_eq_true] at hacc; obtain ⟨hacc, hM0⟩ := hacc
  rw [acceptB_append, Bool.and_eq_true] at hacc; obtain ⟨hacc, hSb2⟩ := hacc
  rw [acceptB_append, Bool.and_eq_true] at hacc; obtain ⟨hSb0, hSb1⟩ := hacc
  have h0 := sboxLane_forces a in0 (sbZ aux 0) hSb0
  have h1 := sboxLane_forces a (in0 + 9) (sbZ aux 1) hSb1
  have h2 := sboxLane_forces a (in0 + 18) (sbZ aux 2) hSb2
  have hm0 := mdsRow_forces a (sboxOut (sbZ aux 0)) (sboxOut (sbZ aux 1)) (sboxOut (sbZ aux 2))
    (mdZ aux 0) (mc 0 0) (mc 0 1) (mc 0 2) hM0
  have hm1 := mdsRow_forces a (sboxOut (sbZ aux 0)) (sboxOut (sbZ aux 1)) (sboxOut (sbZ aux 2))
    (mdZ aux 1) (mc 1 0) (mc 1 1) (mc 1 2) hM1
  have hm2 := mdsRow_forces a (sboxOut (sbZ aux 0)) (sboxOut (sbZ aux 1)) (sboxOut (sbZ aux 2))
    (mdZ aux 2) (mc 2 0) (mc 2 1) (mc 2 2) hM2
  have hr0 := rcAddCore_zmod a (mdsOut (mdZ aux 0)) (rcZ aux 0) (rcC aux 0) ((rc.getD 0 0 : Nat) : ℤ)
    (evalH_of_accept a _ _ (List.Mem.head _) hRc)
  have hr1 := rcAddCore_zmod a (mdsOut (mdZ aux 1)) (rcZ aux 1) (rcC aux 1) ((rc.getD 1 0 : Nat) : ℤ)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.head _)) hRc)
  have hr2 := rcAddCore_zmod a (mdsOut (mdZ aux 2)) (rcZ aux 2) (rcC aux 2) ((rc.getD 2 0 : Nat) : ℤ)
    (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hRc)
  refine ⟨?_, ?_, ?_⟩
  · show (fpVal a (rcZ aux 0) : ZMod pN) = (((Ref.round rc hs).getD 0 0 : Nat) : ZMod pN)
    rw [getD_round rc hs 0 (by norm_num), ZMod.natCast_mod]
    rw [hr0, hm0, h0, h1, h2, hst0, hst1, hst2]
    simp only [Ref.sbox]
    push_cast
    simp only [ZMod.natCast_mod]
    push_cast
    ring
  · show (fpVal a (rcZ aux 1) : ZMod pN) = (((Ref.round rc hs).getD 1 0 : Nat) : ZMod pN)
    rw [getD_round rc hs 1 (by norm_num), ZMod.natCast_mod]
    rw [hr1, hm1, h0, h1, h2, hst0, hst1, hst2]
    simp only [Ref.sbox]
    push_cast
    simp only [ZMod.natCast_mod]
    push_cast
    ring
  · show (fpVal a (rcZ aux 2) : ZMod pN) = (((Ref.round rc hs).getD 2 0 : Nat) : ZMod pN)
    rw [getD_round rc hs 2 (by norm_num), ZMod.natCast_mod]
    rw [hr2, hm2, h0, h1, h2, hst0, hst1, hst2]
    simp only [Ref.sbox]
    push_cast
    simp only [ZMod.natCast_mod]
    push_cast
    ring

/-- Round `n` appended to the gate fold (the fold induction's step shape). -/
theorem permGatesFrom_succ (r0 n : Nat) :
    permGatesFrom r0 (n + 1) = permGatesFrom r0 n ++ roundGatesAt (r0 + n) := by
  simp [permGatesFrom, List.range_succ, List.flatMap_append]

/-- Round `n` appended to the reference fold. -/
theorem permFrom_succ (r0 n : Nat) (hs : List Nat) :
    Ref.permFrom r0 (n + 1) hs = Ref.round (rcsN.getD (r0 + n) []) (Ref.permFrom r0 n hs) := by
  simp [Ref.permFrom, List.range_succ]

/-- **The fold forcing** — rounds `r0 .. r0+n−1`'s accepted gates FORCE the state through the
reference rounds, by `List.range` induction composing `round_forces` per step (the
`Sha256FoldForcing.foldl_cstep_forces` move, gate-count-independent). -/
theorem permFrom_forces (a : Assignment) : ∀ (n r0 : Nat) (hs : List Nat),
    StateIsZ a (inB r0) hs →
    acceptB (permGatesFrom r0 n) a = true →
    StateIsZ a (inB (r0 + n)) (Ref.permFrom r0 n hs) := by
  intro n
  induction n with
  | zero => intro r0 hs hst _; exact hst
  | succ n ih =>
    intro r0 hs hst hacc
    rw [permGatesFrom_succ, acceptB_append, Bool.and_eq_true] at hacc
    have hstep := round_forces a (inB (r0 + n)) (auxB (r0 + n)) (rcsN.getD (r0 + n) [])
      (Ref.permFrom r0 n hs) (ih r0 hs hst hacc.1) hacc.2
    rw [permFrom_succ, Nat.add_succ]
    exact hstep

/-- **`perm_forces`** — the whole 55-round permutation's accepted gates FORCE the final state to
the reference `Ref.perm` of the initial state, in `ZMod pN`. -/
theorem perm_forces (a : Assignment) (hs : List Nat)
    (hst : StateIsZ a 0 hs) (hacc : acceptB permGates a = true) :
    StateIsZ a (inB rounds) (Ref.perm hs) :=
  permFrom_forces a rounds 0 hs hst hacc

/-- **`absorbBlock_forces`** — the accepted absorb gates FORCE the new state lanes to the field
sum of state + input (the sponge's absorb add; squeeze needs no gate). -/
theorem absorbBlock_forces (a : Assignment) (stB x0B x1B outB c0 c1 : Nat)
    (hacc : acceptB (absorbBlockGates stB x0B x1B outB c0 c1) a = true) :
    (fpVal a outB : ZMod pN) = (fpVal a stB : ZMod pN) + fpVal a x0B ∧
    (fpVal a (outB + 9) : ZMod pN) = (fpVal a (stB + 9) : ZMod pN) + fpVal a x1B := by
  exact ⟨fpAddCore_zmod a stB x0B outB c0 (evalH_of_accept a _ _ (List.Mem.head _) hacc),
    fpAddCore_zmod a (stB + 9) x1B (outB + 9) c1
      (evalH_of_accept a _ _ (List.Mem.tail _ (List.Mem.head _)) hacc)⟩

#assert_axioms zmod_eq_of_dvd
#assert_axioms fpSMulCore_forces
#assert_axioms rcAddCore_forces
#assert_axioms sboxLane_forces
#assert_axioms mdsRow_forces
#assert_axioms getD_round
#assert_axioms round_forces
#assert_axioms permGatesFrom_succ
#assert_axioms permFrom_succ
#assert_axioms permFrom_forces
#assert_axioms perm_forces
#assert_axioms absorbBlock_forces

/-! ## §5 — KATs: the reference reproduces REAL o1js `Poseidon.hash` gold vectors (in-kernel
`#guard`), and the generated round gates ACCEPT the honest round-0 witness of the `hash([1])`
trace and REJECT limb bumps. Gold values: o1js 1.9.1 (`bridge/mina-zkapp/scripts/poseidon-kat.mjs`),
pasted in `circuit-prove/sketches/mina-pasta-hash-probe/src/main.rs`.

PROVENANCE, at the resolution the 2026-07-27 defect earned: every value below was re-emitted by the
PINNED `mina-poseidon` crate at rev `36a8b510` (the probe's own dependency, driven through
`ArithmeticSponge::absorb`/`squeeze` — i.e. by the upstream state machine itself, not by a
re-implementation), and independently by a Python reference over the same dumped constants. Both
agree on all ten. The previous header cited "an independent Python recomputation" that agreed with
this file on seven of nine because it shared this file's bug — so upstream-emitted values, not a
second implementation of the same reading, are what the even-length pins rest on. -/

-- ── ALL TEN gold vectors. ODD/EMPTY lengths (0, 1, 3, 5) ───────────────────────────────────
#guard Ref.hash [] ==
  21565680844461314807147611702860246336805372493508489110556896454939225549736
#guard Ref.hash [0] ==
  21565680844461314807147611702860246336805372493508489110556896454939225549736
#guard Ref.hash [1] ==
  7555220006856562833147743033256142154591945963958408607501861037584894828141
#guard Ref.hash [2] ==
  21684304481040958849270710845151658168046794458221536315647897641876555971838
#guard Ref.hash [0, 1, 2] ==
  23424253158290730161371606799079106362420197187036669822385682777728739646385
#guard Ref.hash [1, 2, 3, 4, 5] ==
  18001630098669009746006492126580468118637657922305117967646200390172668909548
#guard Ref.hash [pN - 1] ==
  24518824681776829458756587711529610422801475896601056123110828936099743112011

-- ── ⚑ THE EVEN LENGTHS — the branch that was WRONG and UNPINNED until 2026-07-27. ──────────
-- The probe's two even-length o1js golds (`main.rs` `compress_LR` and `pminus1_pair`).
#guard Ref.hash [123456789, 987654321] ==
  6772978760933812024160307839154538618423125613299338612712092411478945181912
#guard Ref.hash [pN - 1, pN - 1] ==
  20810074891993247493960274286147277584611699933767320058174718289332701361363
-- The probe's tenth gold: the o1js `MerkleTree` depth-2 root over leaves `[1,2,3,4]`, i.e. THREE
-- composed length-2 hashes (`main.rs:211`, `merkle_compress_matches_o1js_merkletree`). This is the
-- vector K6's node hash rests on, and it is the even-length case used the way o1js uses it.
#guard Ref.hash [Ref.hash [1, 2], Ref.hash [3, 4]] ==
  7015600548940256149412569585750804788713845761673517466748455515265959704439
-- Even MULTI-block (2 permutations): the cons-cons path followed by an even TAIL — the exact
-- shape the old block recursion mis-scheduled. Values from the pinned `mina-poseidon` crate
-- (rev `36a8b510`) itself, not from o1js's gold list, and labelled as such.
#guard Ref.hash [1, 2, 3, 4] ==
  17999926647250094709265028274613333425009490119803674735075942677461815400090
#guard Ref.hash [1, 2, 3, 4, 5, 6] ==
  7959985017624114422670972688388085510647704392438374328769526015682157146350

-- ── ⚑ THE NEGATIVE PIN THAT CAN FIRE, AIMED AT THE EVEN-LENGTH PATH. ──────────────────────
-- These are the values the DOUBLE-PERMUTING definition actually produced (measured, both
-- semantics, same constants). They are not "some wrong number": they are the specific outputs of
-- the specific defect. If the extra permutation ever comes back — by a reordered clause, a
-- restructured recursion, or a lane counter off by one — these three `#guard`s go RED and say so.
#guard Ref.hash [123456789, 987654321] !=
  23397677932345629730936879514936877232937627317971664105867317815527328737417
#guard Ref.hash [pN - 1, pN - 1] !=
  8219658745770503307740253059558344825226897798820789573635148578028951530372
#guard Ref.hash [1, 2, 3, 4] !=
  26993694416056582790582409423103415288705444050638970371145280293842306269458
-- And the structural statement of the same fact, independent of any constant: absorbing a FULL
-- final rate block must leave exactly ONE closing permutation, so a length-2 hash is the singly
-- permuted absorbed state — NOT `perm (perm ...)`.
#guard Ref.absorbAll [0, 0, 0] [1, 2] ==
  Ref.perm (Ref.absorbAt (Ref.absorbAt [0, 0, 0] 0 1) 1 2)
#guard Ref.absorbAll [0, 0, 0] [1, 2] !=
  Ref.perm (Ref.perm (Ref.absorbAt (Ref.absorbAt [0, 0, 0] 0 1) 1 2))

-- ⚑ AND THE REJECTS ABOVE ARE AIMED AT A REACHABLE VALUE, PROVED IN-KERNEL RATHER THAN ASSERTED.
-- Applying ONE EXTRA permutation to the correctly-absorbed state reproduces, exactly, the three
-- numbers the `!=` guards reject. So those guards are not pinned to arbitrary wrong numbers: they
-- are pinned to precisely what the defect emits, and they go red if and only if it returns. (This
-- is the mutation test, expressed as a permanent pin — no need to reintroduce the bug to show the
-- instrument bites, and no window in which a shared tree carries a deliberately broken sponge.)
#guard (Ref.perm (Ref.absorbAll [0, 0, 0] [123456789, 987654321])).getD 0 0 ==
  23397677932345629730936879514936877232937627317971664105867317815527328737417
#guard (Ref.perm (Ref.absorbAll [0, 0, 0] [pN - 1, pN - 1])).getD 0 0 ==
  8219658745770503307740253059558344825226897798820789573635148578028951530372
#guard (Ref.perm (Ref.absorbAll [0, 0, 0] [1, 2, 3, 4])).getD 0 0 ==
  26993694416056582790582409423103415288705444050638970371145280293842306269458

-- non-vacuity: a tampered input does NOT reproduce the gold `seq012` vector
#guard Ref.hash [0, 1, 3] !=
  23424253158290730161371606799079106362420197187036669822385682777728739646385
-- the S-box spot check (`α = 7`)
#guard Ref.sbox 2 == 128

/-! ### The round gate KAT — round 0 of the real `hash([1])` computation (input state `[1,0,0]`,
round constants `rcsN[0]`). The honest witness is computed BY the reference itself (S-box
intermediates, MDS rows, carries, quotients), so acceptance is non-vacuous: the trace it accepts
is the trace that ends at the o1js gold `hash([1])` after 54 more forced rounds. -/

/-- The limb cells of a value `v` at column base `b`. -/
def limbCells (b v : Nat) : List (Nat × ℤ) :=
  (List.range numLimbs).map (fun i => (b + i, PastaField.Ref.limbOf v i))

/-- The cells of an `fpMul`-shaped block (result `z` at `b`, quotient `q` at `b+9`). -/
def mulCells (b z q : Nat) : List (Nat × ℤ) := limbCells b z ++ limbCells (b + 9) q

/-- The cells of an `fpAdd`-shaped block (result `z` at `b`, carry `c` at `b+9`). -/
def addCells (b z c : Nat) : List (Nat × ℤ) := limbCells b z ++ [(b + 9, (c : ℤ))]

/-- The honest S-box-lane cells for input `x` (the `x·x²·(x²)²` chain). -/
def sboxCells (aux j x : Nat) : List (Nat × ℤ) :=
  let b := sbZ aux j
  let t2 := x * x % pN; let q2 := x * x / pN
  let t3 := t2 * x % pN; let q3 := t2 * x / pN
  let t4 := t2 * t2 % pN; let q4 := t2 * t2 / pN
  let z := t3 * t4 % pN; let qz := t3 * t4 / pN
  mulCells b t2 q2 ++ mulCells (b + 18) t3 q3 ++ mulCells (b + 36) t4 q4 ++ mulCells (b + 54) z qz

/-- The honest MDS-row cells for row `j` over the S-boxed lanes `s0 s1 s2`. -/
def mdsCells (aux j s0 s1 s2 : Nat) : List (Nat × ℤ) :=
  let b := mdZ aux j
  let t0 := mc j 0 * s0 % pN; let q0 := mc j 0 * s0 / pN
  let t1 := mc j 1 * s1 % pN; let q1 := mc j 1 * s1 / pN
  let t2 := mc j 2 * s2 % pN; let q2 := mc j 2 * s2 / pN
  let sA := (t0 + t1) % pN; let cA := (t0 + t1) / pN
  let z := (sA + t2) % pN; let cz := (sA + t2) / pN
  mulCells b t0 q0 ++ mulCells (b + 18) t1 q1 ++ mulCells (b + 36) t2 q2
    ++ addCells (b + 54) sA cA ++ addCells (b + 64) z cz

/-- The honest RC-lane cells (`z = m + rc`, carry). -/
def rcCells (aux j m r : Nat) : List (Nat × ℤ) :=
  let z := (m + r) % pN; let c := (m + r) / pN
  limbCells (rcZ aux j) z ++ [(rcC aux j, (c : ℤ))]

/-- The MDS row `j` output over the S-boxed lanes (the reference value the row gates pin). -/
def mdsRowVal (j s0 s1 s2 : Nat) : Nat :=
  (mc j 0 * s0 + mc j 1 * s1 + mc j 2 * s2) % pN

/-- The full honest round witness: input lanes `x0 x1 x2` at columns `0..26` pattern (bases
`in0`, stride 9) + every intermediate of the round at aux base `aux`. -/
def roundCells (in0 aux : Nat) (x0 x1 x2 : Nat) (rc : List Nat) : List (Nat × ℤ) :=
  limbCells in0 x0 ++ limbCells (in0 + 9) x1 ++ limbCells (in0 + 18) x2
    ++ sboxCells aux 0 x0 ++ sboxCells aux 1 x1 ++ sboxCells aux 2 x2
    ++ mdsCells aux 0 (Ref.sbox x0) (Ref.sbox x1) (Ref.sbox x2)
    ++ mdsCells aux 1 (Ref.sbox x0) (Ref.sbox x1) (Ref.sbox x2)
    ++ mdsCells aux 2 (Ref.sbox x0) (Ref.sbox x1) (Ref.sbox x2)
    ++ rcCells aux 0 (mdsRowVal 0 (Ref.sbox x0) (Ref.sbox x1) (Ref.sbox x2)) (rc.getD 0 0)
    ++ rcCells aux 1 (mdsRowVal 1 (Ref.sbox x0) (Ref.sbox x1) (Ref.sbox x2)) (rc.getD 1 0)
    ++ rcCells aux 2 (mdsRowVal 2 (Ref.sbox x0) (Ref.sbox x1) (Ref.sbox x2)) (rc.getD 2 0)

/-- An assignment from association cells (`0` elsewhere). -/
def asgOf (cells : List (Nat × ℤ)) : Assignment := fun col => (cells.lookup col).getD 0

/-- The honest round-0 witness of `hash([1])`: input state `[1, 0, 0]`, aux base `27`. -/
def katRoundAsg : Assignment := asgOf (roundCells 0 27 1 0 0 (rcsN.getD 0 []))

-- ACCEPT: the generated round gates accept the honest witness of the real trace.
#guard acceptB (roundGates 0 27 (rcsN.getD 0 [])) katRoundAsg == true
-- REJECT: bump the input lane (1 → 2) and the first S-box result limb — both break the gates.
#guard acceptB (roundGates 0 27 (rcsN.getD 0 [])) (bumpAt katRoundAsg 0) == false
#guard acceptB (roundGates 0 27 (rcsN.getD 0 [])) (bumpAt katRoundAsg 27) == false

/-! ## §6 — Structural `#guard`s (the generators produce the budgeted shapes). -/

#guard (sboxLaneGates 0 27).length == 4
#guard (mdsRowGates 0 9 18 216 1 2 3).length == 5
#guard (absorbBlockGates 0 27 36 45 54 55).length == 2
#guard (roundGates 0 27 (rcsN.getD 0 [])).length == 30
#guard permGates.length == 1650

/-! ## §7 — The PRECISE named residuals + the continuation (K4 and up).

RESIDUALS (named; none sorry-ed):
  1. **The `z < p` canonical compare and the limb range checks are NOT emitted per intermediate.**
     The value gates here force the CONGRUENCE (proved, `ZMod pN`); K1's `pastaLimbRange`
     generator and the named `z < p` compare compose unchanged on top (each intermediate's
     9-limb block admits them). The honest witnesses above ARE canonical.
  2. **The whole-permutation accept-KAT is intractable in-kernel** — 1650 value gates over a
     25 740-column witness (the same wall as SHA's `sha256Compress'`), so it is FORCED
     (`perm_forces`, the fold induction) instead of `#guard`ed; the gate-level KAT is one full
     round of the real `hash([1])` trace, both polarities.
  3. **The hash-level gate fold (absorb blocks ‖ perm folds ‖ squeeze) is NOT composed.** The
     absorb add is forced (`absorbBlock_forces`), the permutation is forced (`perm_forces`), and
     squeeze is a projection; threading them through `Ref.absorbFrom`'s lane-counter loop is the
     same induction shape again, named for the transcript task that needs it.
  4. **The shared K1 residuals** — the `ℤ ↔ p_felt` field-width gap (the gates are read over ℤ;
     the cross-sums overflow BabyBear) and inherited primality of the modulus — stand unchanged
     (`PastaField` §6, `LightClientEthAir` §6).

CONTINUATION: K4 (the IPA opening MSM — the cost center) and K5 (the Kimchi verify equation)
consume this sponge for every Fiat–Shamir challenge; the absorb/permute forcing pair is the
composable unit. NOT claimed: an IPA, a verifier, or native-field soundness.
-/

end Dregg2.Circuit.Emit.PastaPoseidon
