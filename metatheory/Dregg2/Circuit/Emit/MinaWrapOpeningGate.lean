import Dregg2.Circuit.Emit.MinaWrapAggregationGate
import Dregg2.Circuit.Emit.MinaRealBlockTranscript
/-!
# Dregg2.Circuit.Emit.MinaWrapOpeningGate — RUNG 5f: **the rung that OPENS a commitment.**

Everything before this in `docs/MINA-REAL-BLOCK-GATE.md` §6.1 checks that our arithmetic agrees
with kimchi's on real objects. 5a-5d assemble commitments; 5e derives one. **None of them says a
commitment is a commitment TO anything.** This file states the equation that does, on Mina devnet
block **539508**.

## The object

`SRS::verify` (`poly-commitment/src/ipa.rs:118-300`) folds TWO independent statements into one
randomised MSM, with independent randomisers `rand_base` and `sg_rand_base`:

```text
(A)  sg == <s, srs.g>                                             -- the sg / accumulator leg
(B)  c·Q + delta − z1·sg − z1·b0·U − z2·H == O                    -- THE OPENING RELATION
     where  Q  = Σ_j (chal_invⱼ·Lⱼ + chalⱼ·Rⱼ) + Σ_i ξⁱ·Cᵢ + cip·U
            U  = groupMap(sponge.challenge_fq())
            b0 = Σ_j evalscaleʲ · b_poly(chal, evaluation_pointⱼ)
```

**(B) is this rung.** With `rand_base = 1` it is exactly `check_bulletproof`'s verifier equation.
The 47-term `Σ ξⁱ·Cᵢ` inside `Q` is 5d's aggregate — which carries the block's `w_comm`, `z_comm`,
`t_comm` (through `ft_comm`), the index's `sigma_comm`/`coefficients_comm`/selector commitments,
and 5e's `public_comm`. `cip` is `combined_inner_product`, which `MinaRealBlockGate`'s C8 already
proved is the `(ξ, r)`-fold of the block's **claimed evaluations**. So (B) holding says: the
polynomials those commitments commit to really do take the claimed values at ζ and ζω.

## What was blocking it, and what unblocked it

Every scalar in (B) that is not in the proof is an **Fq-sponge output**: `u_base` is the group map
applied to `challenge_fq()`, and `c` and the 15 IPA challenges are `opening.challenges::<EFqSponge>`.
Until `MinaRealBlockTranscript` landed there was no sponge on this block to continue. There is now:
§3 below picks the phase-1 sponge up at the state `SRS::verify` receives it in — `o.fq_sponge`,
the state right after ζ′ — and runs it forward through `absorb_fr(shift_scalar(cip))`,
`challenge_fq`, the 15 `absorb_g(L)/absorb_g(R)/squeeze` rounds and `absorb_g(delta)`. **All 16
challenges of the opening argument are derived here, not carried.**

## What this rung establishes, and what it still assumes — say both

**Establishes**, in-kernel, over the real group law mod the real prime, on a real Mina block:
the IPA verifier's opening equation holds for this proof at the challenges its own transcript
samples.

**Assumes, and does not discharge:**

1. **P10, the opening-soundness floor.** (B) is the verifier's *check*; that a prover which
   passes it must KNOW an opening is the IPA/dlog extraction argument, which is undischarged here
   and everywhere in this stack. "We opened a commitment" means "the opening check passes", not
   "the opening is sound".
2. **(A), the `<s, srs.g>` leg — rung 5h, DEFERRED BY MEASUREMENT.** (B) uses `sg` as the IPA's
   final `G`; that `sg` really is `<b_poly_coefficients(chal), srs.g>` is a 2^15-term SRS MSM,
   extrapolated at **~18 hours and ~7 TB** of elaborator memory in-kernel (§6.1). It is measured
   TRUE in Rust by the extractor (`[gt8]`) and discharged out-of-circuit by openmina's own
   `accumulator_check`; it is **not** checked in this kernel. Without (A), (B) is a statement
   about an opening against a `G` the proof supplied.
3. **Poseidon's collision resistance**, as everywhere a transcript is used.
4. **`p` is prime** — §4's non-residue certificates are Euler's criterion.
5. The SRS itself: that `srs.g` and `srs.h` are what they claim is not checked by anything here.

## Cost, measured

34 × 255-bit RCB ladders per instance of the relation (2×15 `lr` + the aggregate + `u_base` + `sg`
+ `h`) ≈ 13 s of kernel at §6.1's 0.19 s/ladder unit; `delta` enters with coefficient 1 and costs
no ladder. The sponge continuation is ~50 Poseidon permutations, `#guard`-evaluated as
`MinaRealBlockTranscript`'s are. Ten instances of the relation plus the transcript: **153 s
measured on hbox**, peak RSS ~13.6 GB — the prediction and the measurement agree, which is what
makes the 5h extrapolation in §6.1 worth anything.

## What pins the gold

The extractor asserts (B) **directly, deterministically, with arkworks group arithmetic**, before
emitting: `[gt6]` is `residual.is_zero()`, and `[gt7]` re-runs it at `z1 + 1` and at
`combined + G` and requires BOTH to be non-zero. `[gt8]` asserts (A). All of it sits behind
`kimchi::verifier::verify = Ok(())` and `SRS::verify = true` on the same object.

Axiom-clean: `by decide` and `#guard`; no `sorry`, no `native_decide`. NEW file. NOT imported by
the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapOpeningGate`
-/

namespace Dregg2.Circuit.Emit.MinaWrapOpeningGate

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt padd msmComm)
open Dregg2.Circuit.Emit.PastaPoseidonFq (SpongeSt fpParams newSponge absorbMany challenge squeeze1)
open Dregg2.Circuit.Emit.KimchiVerify (endoMap)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

open Dregg2.Circuit.Emit.MinaRealBlockTranscript (fpTape ZCOMM_XY TCOMM_XY FQ_DIGEST ENDO_R)
open Dregg2.Circuit.Emit.MinaRealBlockGate (ZETA ZETAW UU CIP)
open Dregg2.Circuit.Emit.MinaWrapAggregationGate (COMBINED_GOLD)

/-- Pallas's BASE field (coordinates). -/
abbrev Fp := ZMod pN
/-- Pallas's SCALAR field (the challenges and the opening scalars). -/
abbrev Fq := ZMod qN

/-! ## §1 — the block's opening proof, as group elements and scalars -/

/-- `opening.lr[j].0` — the 15 left points of the IPA rounds. -/
def LR_L : List Pt :=
  [
   (12705196385221718857249566903302388911932169156760698169778314503830480905186,
     28676455647181200636592094890595789161840381997703070105214846542534415910188, 1),
   (4705544492877352833802724936888203427040313136399132779974600991269612431589,
     365616094589686249353551781622234892018375199638455572065098302278474597989, 1),
   (21620071166591841416832495831474902273925946201984141970162743716428975243077,
     7576556682066454025794779899803015607740321542827941681151750187115391894877, 1),
   (16393814524815529141610722331027650864620106214531211825384109433889627324458,
     21400036658053469886678683091373094785051897882518079080952211293084004947170, 1),
   (20570211305411226208866085077679791164125014315342217370663830240828878681573,
     9437392047320478085544595016716540005433473346336999428180126983624643561941, 1),
   (18410460502725211225801818505872632153183774762233436736294697896864965742565,
     7684506446542967332562301247109157570857488350591917865325061770796033147854, 1),
   (23620387791338998882891575717300124354357000490145862326531625214073765485549,
     23210232735450164119367813351331118834279258699685885522308094682199977866498, 1),
   (15247068588025160108557648506763615116024251537772296149431501207355180373960,
     10710440786616267499892393980878308428463788189991713196207913938394952081060, 1),
   (9754008399281586338637138980763767515244526382830005053136893661133609062364,
     14056212197661529059088701341479244073853760238469291869169507690790438302028, 1),
   (2069717232489723856651444061689868715791746868858595050790392168766069890929,
     13923875722161356526024836636890477538394013791072100330341040760602013280069, 1),
   (20548766741201388766676891141594125587859025400809840923620418279525990760781,
     25114061108286876906517873321070379982596083030863311852871013158697473792464, 1),
   (21821809708776962249662826652624014372201513878863143128444133000538319895548,
     13203255256985644549892832746558178920347118013079630772791065219216535823186, 1),
   (8226361457772299676241905954195795308932723184824143958275916304101624180093,
     3729321605895608994000970759254938034587044418139150381901153968055381521062, 1),
   (495409107725859366346238356670383348282199648674957521846503771354641998196,
     6251722737873856038930266368261232194858000324321267701679355466501744850440, 1),
   (22289485113942734534436748012495097929396852903393149912956055621811733655753,
     8338435645997067545360976075186656882550532874670669649334297553041050028490, 1)
  ]

/-- `opening.lr[j].1` — the 15 right points. -/
def LR_R : List Pt :=
  [
   (16485136775402428201130891298819062422937635379349789537966516171135101900196,
     6401154122195611756145322097945546148867063322768950336569604389789470850209, 1),
   (23157333829832602547200077459765486915680538466511135973329744283137083185940,
     1070251312977551270621835430210766914871635418924505020086155791974834401321, 1),
   (16934640944379076186190279055541226709937602959929065555930571485238257957385,
     25673629764540170899680095029968460507241044756309405540531656309085750474514, 1),
   (27749247763363718810258340123879367687790248717374740372582444301773110351699,
     13017247186226881043529544253823670113575796014156027542751032099543661042572, 1),
   (5341494414830701567200845498263286365354713029840754850272599800605835330960,
     6298076938553391185168094237732150746382998033568844828258157260256114371820, 1),
   (16932751156224386753406660925235434848111284419725446159607237839110426004853,
     577607632592678937204084000517000578281223675107269019434515295915807951461, 1),
   (2489422501835765585976760985214649227036638701247851881172620205312426384051,
     20690686967009567734967180801542191658049316255769305913397663888037130114029, 1),
   (418180052411313428877957404949580945501433167412419237700820618347897428969,
     15652015672386304816373488881731793662991595227201876963530836578583991974262, 1),
   (14560396737106445490968993340363018107592479644398438716060981805926048574069,
     6505278251659198853925162845771166528132291727069448673092240739598615334845, 1),
   (20304047555143993501274380921228238556548683382682266177156610708040543176344,
     4162351939864852852249837073516056149990862779213762088563569740586622791222, 1),
   (13140654777961702598814698470597496542203440083699787395252301995098880599817,
     22821703866788945932824364516282743016560971627131829421124269304793726825187, 1),
   (8648305575867923008426003227154950521293531825288233241742976671295011755911,
     8180838443811438432322561516015907425811243375175815512326385969355819209433, 1),
   (14829037518174134104342470514245276599721914040448825406583930842822365460510,
     24283450112426122185231529021775847258597743466293170041242858234150361636818, 1),
   (9275296795581609358765910979003232572695370161243062333883646572835513095800,
     18968825592651885800160568125902314155095106863960971575207909907673137896150, 1),
   (16609224480140811211167002994743501580304736476294011188537287450761566180505,
     2037506404132372398645256042577064112249481997731150895709040332148441703641, 1)
  ]

/-- `opening.sg` — the IPA's final `G`, and the accumulator the next Step inherits. -/
def SG : Pt :=
  (27645747947874706201841804187493007015446820953018417773890030413191100025813,
   22431124833386818350144521797175752507845644373717877723958129425730786166045, 1)

/-- `opening.delta` — the blinding-balance point; the only term with coefficient 1. -/
def DELTA : Pt :=
  (12549709920810273664906708092233375320551866741711935112842501996657168435128,
   20309267457022842418190650121197025811257123750798938466729537503415872118371, 1)

/-- `srs.h`. -/
def SRS_H : Pt :=
  (15427374333697483577096356340297985232933727912694971579453397496858943128065,
   2509910240642018366461735648111399592717548684137438645981418079872989533888, 1)

/-- `opening.z1`, `opening.z2` — the two scalars the prover reveals. -/
def Z1 : Nat := 16490346539804888485998938294158148162583740026821366682111033051254152354788
def Z2 : Nat := 1216205103802880734129998039293467119990830792228647687148210515475027380695

/-- `combined_inner_product`, as a `Nat`; §2 ties it to the gate's `CIP`. -/
def CIP_N : Nat := 4948131480779179767533860900716273683919559147195747550813387244823367375127

/-- `shift_scalar::<Pallas>(cip)` — what `SRS::verify` absorbs, not `cip` itself
(`commitment.rs:255-270`). For Pallas `q > p`, so the branch is `x − 2^255`. -/
def CIP_SHIFTED : Nat := 4948131480779179767533860900716273684010679778258760290444080737653528451353

/-! ## §2 — the IPA challenges, DERIVED (§3) and then USED -/

/-- The 15 raw 128-bit prechallenges of `opening.prechallenges`. -/
def IPA_PRECHALS : List Nat :=
  [
   335463759998289021554486315776626316383,
   145771725570402131453621392050817190218,
   34026178414024467235944510181845778156,
   92104851529502536353677184026445674947,
   203144013748865977605758607597481799256,
   21702598095217462533259867124210997621,
   26904637620167869735681445259287791759,
   10928729257034792185542617904065921856,
   130593374187714210972663864170509124742,
   151897950215122739874067024283705137278,
   153045058644023891846888214296363876825,
   50703466457718574522075472736884795778,
   290416957972600375130098509948467846459,
   151563995648509574393966775326234520922,
   173064192737643576295729286679728910936
  ]

/-- `ScalarChallenge(sponge.challenge()).to_field(endo_r)` after `absorb_g(delta)` — the `c` that
scales the whole of `Q`. -/
def C_PRE : Nat := 232004425888406313426001224040053945968

/-- The 15 IPA challenges (`chal`) and their inverses (`chal_inv`), as `Nat`s. -/
def CHAL : List Nat :=
  [
   13716375629442026426586768669803580042774243418224686117117473050072128151997,
   27574752040238069148617826156335116866776275665883918068627526281206272526720,
   10577619571761247205510805515934401156785760328538239837948850894994914132824,
   15834486710256743467632357968999873989156161851984972342406657564368088601702,
   25599952473050885700826766846776955293052215071182458949156281454767674603914,
   2463408475137952737136872275645340461770450086470480559499306029424826024666,
   10335177585121292428625633083235424257374604191202166292733186677365502110040,
   192987810272167092643854434840984455257691229060478562486808664779237521370,
   17556318333445062092238965286972640600066488894577280079407272952255236975848,
   9780633805985511155425654618273422234291713898883934856587940805772084327116,
   10268150599961762810861706642185888310762545510044709041533868252584962964903,
   12288850941832568453498597088006544707356656948693366554115893332559703051523,
   17212937220662889438085961271185286913363650176772135165433738850599594967805,
   7281256013121462542225859007803369412480061528370359646400035612081773569295,
   20023054730103874666635395395754884771484059349789212023038596446694905549611
  ]
def CHAL_INV : List Nat :=
  [
   21466948455963616163790101955279423470336264514262056201986405509978742831495,
   8304071013187886303239246681375157903029909592611747123039537685701855855924,
   22672129578732625836163342717945189818344178319110249713197530479241015671964,
   11239348122595580004260248046021092617645141507892057534000625691349950468089,
   10083478573671510039430838993338716366693391392794319476111776367151870294452,
   10542157899025188911028375153959442384355944955364846445946033789077144751233,
   19023038199650666876689556135726152581907134881076312602723943240290310695199,
   18868871832056895119034930224865015320501539816041578349016633968477808242635,
   11075763739263100779404420040667659786828685032674189036791799224994708659319,
   2711435955189236181556052418994248972055989113827930515853719032356318217553,
   25582724740309632061361400748950739284294620195014492730013130299957730706564,
   5447348108651581937378175340267068210181779652836863111272748667265797314141,
   3826899869923526791734089819658120433474484134537185779118324775943673331932,
   8936536974738732369735527062983334574226788342108011075082102955479461109308,
   846298062177672635329066837377963984857914826129650591108597636391342236000
  ]

def CHAL_F : List Fq := CHAL.map (fun x => (x : Fq))
def CHAL_INV_F : List Fq := CHAL_INV.map (fun x => (x : Fq))

def C : Nat := 11142905993417508785552824934005674472259482775645716017272317556028503490369
def B0 : Nat := 8959513835325565174995450957597499793792733131117505895288870852340268010913

/-- `<s, sum_i evalscale^i pows(evaluation_point[i])>`'s scalar half — kimchi's `b_poly`
(`commitment.rs:370-380`): `prod_i (1 + chals[i]·x^(2^(k-1-i)))`. The tower is built by repeated
squaring, so a `k = 15` evaluation costs 15 squarings, not `x^16384`. -/
def sqTower (x : Fq) : Nat → List Fq
  | 0 => []
  | (n + 1) => x :: sqTower (x * x) n

def bPoly (chals : List Fq) (x : Fq) : Fq :=
  let k := chals.length
  let tw := sqTower x k
  (List.range k).foldl (fun acc i => acc * (1 + chals.getD i 0 * tw.getD (k - 1 - i) 0)) 1

/-! ## §3 — ⚑ THE TRANSCRIPT CONTINUES: every challenge of the opening argument, DERIVED.

`MinaRealBlockTranscript.wrapPhase1` ran the Fq-sponge to ζ′ and stopped. `oracles(...)` takes
its `digest()` on a CLONE (`verifier.rs:283`), so the sponge `SRS::verify` receives is exactly
that state. It is rebuilt here from the transcript module's own tape and pinned by the digest
before a single further absorb. -/

/-- The state `o.fq_sponge` is in when `SRS::verify` gets it. -/
def wrapPhase1State : SpongeSt :=
  let s0 := absorbMany fpParams newSponge fpTape
  let s1 := (challenge fpParams s0).1
  let s2 := (challenge fpParams s1).1
  let s3 := absorbMany fpParams s2 ZCOMM_XY
  let s4 := (challenge fpParams s3).1
  let s5 := absorbMany fpParams s4 TCOMM_XY
  (challenge fpParams s5).1

/-! It IS the transcript's phase-1 state: its digest is the `FQ_DIGEST` phase 2 chains on. -/
#guard Dregg2.Circuit.Emit.PastaPoseidonFq.digestInto fpParams wrapPhase1State qN == FQ_DIGEST

/-- `absorb_fr` on the Pallas Fq-sponge (`sponge.rs:221-252`). Pallas's scalar modulus `q`
EXCEEDS its base modulus `p`, so the branch taken is the one that splits: absorb the high bits,
then the low bit. Two absorbs, not one. -/
def absorbFr (s : SpongeSt) (x : Nat) : SpongeSt := absorbMany fpParams s [x / 2, x % 2]

/-- `(L.x, L.y, R.x, R.y)` per IPA round — `absorb_g`'s stream (`sponge.rs:198-211`). -/
def LR_XY : List (List Nat) :=
  [
   [12705196385221718857249566903302388911932169156760698169778314503830480905186, 28676455647181200636592094890595789161840381997703070105214846542534415910188,
    16485136775402428201130891298819062422937635379349789537966516171135101900196, 6401154122195611756145322097945546148867063322768950336569604389789470850209],
   [4705544492877352833802724936888203427040313136399132779974600991269612431589, 365616094589686249353551781622234892018375199638455572065098302278474597989,
    23157333829832602547200077459765486915680538466511135973329744283137083185940, 1070251312977551270621835430210766914871635418924505020086155791974834401321],
   [21620071166591841416832495831474902273925946201984141970162743716428975243077, 7576556682066454025794779899803015607740321542827941681151750187115391894877,
    16934640944379076186190279055541226709937602959929065555930571485238257957385, 25673629764540170899680095029968460507241044756309405540531656309085750474514],
   [16393814524815529141610722331027650864620106214531211825384109433889627324458, 21400036658053469886678683091373094785051897882518079080952211293084004947170,
    27749247763363718810258340123879367687790248717374740372582444301773110351699, 13017247186226881043529544253823670113575796014156027542751032099543661042572],
   [20570211305411226208866085077679791164125014315342217370663830240828878681573, 9437392047320478085544595016716540005433473346336999428180126983624643561941,
    5341494414830701567200845498263286365354713029840754850272599800605835330960, 6298076938553391185168094237732150746382998033568844828258157260256114371820],
   [18410460502725211225801818505872632153183774762233436736294697896864965742565, 7684506446542967332562301247109157570857488350591917865325061770796033147854,
    16932751156224386753406660925235434848111284419725446159607237839110426004853, 577607632592678937204084000517000578281223675107269019434515295915807951461],
   [23620387791338998882891575717300124354357000490145862326531625214073765485549, 23210232735450164119367813351331118834279258699685885522308094682199977866498,
    2489422501835765585976760985214649227036638701247851881172620205312426384051, 20690686967009567734967180801542191658049316255769305913397663888037130114029],
   [15247068588025160108557648506763615116024251537772296149431501207355180373960, 10710440786616267499892393980878308428463788189991713196207913938394952081060,
    418180052411313428877957404949580945501433167412419237700820618347897428969, 15652015672386304816373488881731793662991595227201876963530836578583991974262],
   [9754008399281586338637138980763767515244526382830005053136893661133609062364, 14056212197661529059088701341479244073853760238469291869169507690790438302028,
    14560396737106445490968993340363018107592479644398438716060981805926048574069, 6505278251659198853925162845771166528132291727069448673092240739598615334845],
   [2069717232489723856651444061689868715791746868858595050790392168766069890929, 13923875722161356526024836636890477538394013791072100330341040760602013280069,
    20304047555143993501274380921228238556548683382682266177156610708040543176344, 4162351939864852852249837073516056149990862779213762088563569740586622791222],
   [20548766741201388766676891141594125587859025400809840923620418279525990760781, 25114061108286876906517873321070379982596083030863311852871013158697473792464,
    13140654777961702598814698470597496542203440083699787395252301995098880599817, 22821703866788945932824364516282743016560971627131829421124269304793726825187],
   [21821809708776962249662826652624014372201513878863143128444133000538319895548, 13203255256985644549892832746558178920347118013079630772791065219216535823186,
    8648305575867923008426003227154950521293531825288233241742976671295011755911, 8180838443811438432322561516015907425811243375175815512326385969355819209433],
   [8226361457772299676241905954195795308932723184824143958275916304101624180093, 3729321605895608994000970759254938034587044418139150381901153968055381521062,
    14829037518174134104342470514245276599721914040448825406583930842822365460510, 24283450112426122185231529021775847258597743466293170041242858234150361636818],
   [495409107725859366346238356670383348282199648674957521846503771354641998196, 6251722737873856038930266368261232194858000324321267701679355466501744850440,
    9275296795581609358765910979003232572695370161243062333883646572835513095800, 18968825592651885800160568125902314155095106863960971575207909907673137896150],
   [22289485113942734534436748012495097929396852903393149912956055621811733655753, 8338435645997067545360976075186656882550532874670669649334297553041050028490,
    16609224480140811211167002994743501580304736476294011188537287450761566180505, 2037506404132372398645256042577064112249481997731150895709040332148441703641]
  ]

/-- `delta`'s coordinates. -/
def DELTA_XY : List Nat := [12549709920810273664906708092233375320551866741711935112842501996657168435128, 20309267457022842418190650121197025811257123750798938466729537503415872118371]

/-- **`ipaTranscript`** — `ipa.rs:186-201` + `OpeningProof::challenges` (`ipa.rs:1013-1035`):
absorb `shift_scalar(cip)`, squeeze `t` in FULL (`challenge_fq`, the group map's preimage — not
the 128-bit `challenge`), then per round absorb `L` and `R` and squeeze a 128-bit prechallenge,
then absorb `delta` and squeeze `c′`. -/
def ipaTranscript (cipS : Nat) (rounds : List (List Nat)) (dxy : List Nat) :
    Nat × List Nat × Nat :=
  let s := absorbFr wrapPhase1State cipS
  let ts := squeeze1 fpParams s
  let r := rounds.foldl
    (fun (acc : SpongeSt × List Nat) blk =>
      let s' := absorbMany fpParams acc.1 blk
      let ch := challenge fpParams s'
      (ch.1, acc.2 ++ [ch.2])) (ts.1, [])
  let sd := absorbMany fpParams r.1 dxy
  (ts.2, r.2, (challenge fpParams sd).2)

/-- `challenge_fq()`'s output — the group map's preimage, a FULL `Fp` element. -/
def T_FQ : Nat := 28506219073229703934904942026880877226428838281173670526112543109172136437102

/-! ⚑ **THE RESULT**: `t`, all 15 IPA prechallenges and `c′` of a REAL Mina block's opening
argument fall out of the sponge the block's own transcript leaves behind. -/
#guard ipaTranscript CIP_SHIFTED LR_XY DELTA_XY == (T_FQ, IPA_PRECHALS, C_PRE)

/-! Non-vacuity, one per stage of the stream. -/
-- the absorbed `combined_inner_product` is inside the transcript: move it and `t` moves
#guard (ipaTranscript (CIP_SHIFTED + 1) LR_XY DELTA_XY).1 != T_FQ
-- an IPA round point moves its own challenge and every later one, but not `t`
#guard (ipaTranscript CIP_SHIFTED (LR_XY.set 0 ((LR_XY.getD 0 []).set 0 0)) DELTA_XY).1 == T_FQ
#guard (ipaTranscript CIP_SHIFTED (LR_XY.set 0 ((LR_XY.getD 0 []).set 0 0)) DELTA_XY).2.1
    != IPA_PRECHALS
-- the LAST round is read too (a fold that stopped early would pass the first control)
#guard (ipaTranscript CIP_SHIFTED (LR_XY.set 14 ((LR_XY.getD 14 []).set 3 0)) DELTA_XY).2.1
    != IPA_PRECHALS
-- `delta` is absorbed AFTER the rounds: it moves `c′` and leaves the 15 prechallenges alone
#guard (ipaTranscript CIP_SHIFTED LR_XY (DELTA_XY.set 0 0)).2.1 == IPA_PRECHALS
#guard (ipaTranscript CIP_SHIFTED LR_XY (DELTA_XY.set 0 0)).2.2 != C_PRE
-- and the split absorb of `absorb_fr` is the right one: absorbing `cip` unsplit is a DIFFERENT
-- transcript, so `sponge.rs`'s `q > p` branch is load-bearing rather than cosmetic
#guard (let s := absorbMany fpParams wrapPhase1State [CIP_SHIFTED]
        (squeeze1 fpParams s).2) != T_FQ

/-- **`derived_ipa_challenges`** — the 15 prechallenges endo-lift to the `chal` the relation
scales `L` and `R` by. -/
theorem derived_ipa_challenges : IPA_PRECHALS.map (endoMap ENDO_R) = CHAL_F := by decide

/-- **`derived_c`** — and `c′` lifts to `c`, the scalar the whole of `Q` is multiplied by. -/
theorem derived_c : endoMap ENDO_R C_PRE = (C : Fq) := by decide

/-- **`derived_endo_discriminates_here`** — the lift is not true for free at these values. -/
theorem derived_endo_discriminates_here :
    endoMap ENDO_R (C_PRE + 1) ≠ (C : Fq)
    ∧ endoMap ENDO_R (IPA_PRECHALS.getD 0 0) ≠ (CHAL.getD 1 0 : Fq) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §3b — the remaining scalars, derived from the derived challenges -/

/-- **`chal_inv_are_inverses`** — `chal_inv` really is `batch_inversion(chal)`; the `L` scalars
are the inverses of the `R` scalars, which is the whole shape of the IPA fold. -/
theorem chal_inv_are_inverses :
    (CHAL_F.zip CHAL_INV_F).all (fun p => decide (p.1 * p.2 = 1)) = true := by decide

/-- ⚑ **`b0_is_the_b_polynomial`** — `b0` is `b_poly(chal, ζ) + r·b_poly(chal, ζω)` at the gate's
OWN ζ and evalscale `r`, both of which `MinaRealBlockTranscript` derives. So the `u_base`
coefficient in the relation descends from the transcript too. -/
theorem b0_is_the_b_polynomial :
    bPoly CHAL_F ZETA + UU * bPoly CHAL_F ZETAW = (B0 : Fq) := by decide

/-- **`b0_reads_every_challenge`** — and moving the first or the last challenge moves it. -/
theorem b0_reads_every_challenge :
    bPoly (CHAL_F.set 0 (CHAL_F.getD 0 0 + 1)) ZETA
        + UU * bPoly (CHAL_F.set 0 (CHAL_F.getD 0 0 + 1)) ZETAW ≠ (B0 : Fq)
    ∧ bPoly (CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)) ZETA
        + UU * bPoly (CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)) ZETAW ≠ (B0 : Fq) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`cip_is_the_gates_cip`** — the `combined_inner_product` this relation folds is the one
`MinaRealBlockGate`'s C8 proved is the `(ξ, r)`-fold of the block's claimed evaluations. Without
this the relation would be about an unrelated number. -/
theorem cip_is_the_gates_cip : (CIP_N : Fq) = CIP := by decide

/-- **`cip_shifted_is_shift_scalar`** — and what the sponge absorbed is that value minus `2^255`,
`shift_scalar`'s `q > p` branch. -/
theorem cip_shifted_is_shift_scalar : (CIP_SHIFTED : Fq) + (2 : Fq) ^ 255 = CIP := by decide

/-! ## §4 — `u_base`, through the group map

`ipa.rs:190-194`: `U = of_coordinates(group_map.to_group(challenge_fq()))`. The map is SvdW06
(`groupmap/src/lib.rs:65-125`): three candidate x-coordinates, take the first whose `x³ + 5` is a
square. The in-kernel version takes the inverse and the square root as WITNESSES and certifies the
skipped candidates as non-residues by Euler's criterion. -/

/-- `BWParameters<Pallas>` — `setup()`'s output, five `Fp` constants. -/
def GM_U : Fp := (1 : Fp)
def GM_FU : Fp := (6 : Fp)
def GM_SQRT3 : Fp := (17006931536212783554987228065028097629383328157457783420645920607630467569011 : Fp)
def GM_SQRT3_MU2 : Fp := (8503465768106391777493614032514048814691664078728891710322960303815233784505 : Fp)
def GM_INV3U2 : Fp := (19298681539552699237261830834781317975575370987961040477303117842899978420225 : Fp)
/-- `alpha = ((t² + fu)·t²)⁻¹`, as a witness. -/
def GM_ALPHA : Fp := (8001933596451875073242048131335426505261128173692347258528157138590321294079 : Fp)
/-- the square root `arkworks`' `sqrt()` returned for the selected candidate. -/
def GM_Y : Fp := (25813443087253962394072244031100642980583105487873972469944046669628245627812 : Fp)

/-- **`group_map_params_are_what_setup_builds`** — every one of the five constants satisfies the
equation `setup()` defines it by, so they are not five opaque numbers. `u = 1` because `f(1) = 6`
is the first non-zero value of the search. -/
theorem group_map_params_are_what_setup_builds :
    GM_U = 1 ∧ GM_FU = GM_U ^ 3 + 5 ∧ GM_FU ≠ 0
    ∧ GM_SQRT3 * GM_SQRT3 = -(3 * GM_U * GM_U)
    ∧ GM_SQRT3_MU2 * 2 = GM_SQRT3 - GM_U
    ∧ GM_INV3U2 * (3 * GM_U * GM_U) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `potential_xs_helper` (`groupmap/src/lib.rs:65-89`), verbatim in shape. -/
def potentialXs (t2 alpha : Fp) : Fp × Fp × Fp :=
  let x1 := GM_SQRT3_MU2 - t2 * t2 * alpha * GM_SQRT3
  let x2 := -GM_U - x1
  let x3 := let s := t2 + GM_FU; GM_U - s * s * (alpha * s) * GM_INV3U2
  (x1, x2, x3)

/-- `t` from §3, in `Fp`. -/
def T_FP : Fp := (T_FQ : Fp)

/-- **`gm_alpha_is_the_inverse`** — `alpha` is the inverse `potential_xs` computes, at the `t`
the sponge produced. -/
theorem gm_alpha_is_the_inverse :
    GM_ALPHA * ((T_FP * T_FP + GM_FU) * (T_FP * T_FP)) = 1 := by decide

/-- `x ^ e mod m` by square-and-multiply over an MSB-first bit list. `ZMod`'s `^` is `npowRec`,
which is linear in the exponent and therefore unusable at `(p−1)/2`. -/
def powModBits (m b : Nat) (bits : List Bool) : Nat :=
  bits.foldl (fun acc bit => let s := acc * acc % m; if bit then s * b % m else s) (1 % m)

def natBitsMsb : Nat → Nat → List Bool
  | _, 0 => []
  | n, (f + 1) => if n = 0 then [] else natBitsMsb (n / 2) f ++ [n % 2 == 1]

/-- Euler's criterion: `x` is a non-residue mod `p` iff `x^((p−1)/2) = p − 1`. Sound because `p`
is prime — an ambient assumption of this whole stack, named in the header. -/
def isNonResidue (x : Nat) : Bool := powModBits pN x (natBitsMsb ((pN - 1) / 2) 256) == pN - 1

/-- **`group_map_selects_the_third_candidate`** — the first two candidates' `x³ + 5` are
NON-RESIDUES, so `get_xy`'s search really does fall through to the third. Without this the choice
of branch would be transcribed rather than derived. -/
theorem group_map_selects_the_third_candidate :
    (isNonResidue (ZMod.val ((potentialXs (T_FP * T_FP) GM_ALPHA).1 ^ 3 + 5))
      && isNonResidue (ZMod.val ((potentialXs (T_FP * T_FP) GM_ALPHA).2.1 ^ 3 + 5))) = true := by
  decide

/-- **`nonresidue_test_discriminates`** — and the test is not true for free. The SELECTED
candidate's `x³ + 5` is NOT a non-residue by the same certificate, and neither are `1` or `4`.
Without this, `group_map_selects_the_third_candidate` would be consistent with an `isNonResidue`
that says yes to everything, and the branch derivation would be theatre. -/
theorem nonresidue_test_discriminates :
    (isNonResidue (ZMod.val ((potentialXs (T_FP * T_FP) GM_ALPHA).2.2 ^ 3 + 5))
      || isNonResidue 1 || isNonResidue 4) = false := by decide

/-- **`group_map_y_is_a_square_root`** — and the third candidate's `x³ + 5` IS a square, with
`GM_Y` a root of it. -/
theorem group_map_y_is_a_square_root :
    GM_Y * GM_Y = (potentialXs (T_FP * T_FP) GM_ALPHA).2.2 ^ 3 + 5 := by decide

/-- **`U_BASE`** — the IPA's `U`, built rather than read: its x-coordinate is the SvdW map applied
to the full squeeze the sponge in §3 produced, and its y is `GM_Y`, the root §4 checked. -/
def U_BASE : Pt := (ZMod.val (potentialXs (T_FP * T_FP) GM_ALPHA).2.2, ZMod.val GM_Y, 1)

/-- ⚑ **`u_base_is_o1labs_u_base`** — and the point that construction lands on IS the `u_base`
o1-labs' `SRS::verify` computes on this block. -/
theorem u_base_is_o1labs_u_base :
    projEqM pN U_BASE (7847223366405709834624373952445684657634586309849412081950229810208103281928, 25813443087253962394072244031100642980583105487873972469944046669628245627812, 1) = true := by decide

/-- **`u_base_is_on_pallas`**. -/
theorem u_base_is_on_pallas : projOnCurveM pN curveB U_BASE = true := by decide

/-! **Residual, named**: which of the two roots `sqrt()` returns is arkworks' Tonelli-Shanks
convention, and `GM_Y` is transcribed from it rather than derived. `tamper_u_base_sign` below is
what makes that a bounded gap rather than an unexamined one: the OTHER root breaks the relation,
so the sign is load-bearing and is pinned by o1-labs' own output. -/

/-! ## §5 — ⚑ THE RUNG: the opening relation -/

/-- `Σ_j (c·chal_invⱼ)·Lⱼ + (c·chalⱼ)·Rⱼ` — the 30 IPA round terms. A sum is order-insensitive,
so `L`s and `R`s may be grouped. -/
def lrTerms (c : Nat) (chals chalInvs : List Nat) : List (Nat × Pt) :=
  ((LR_L.zip chalInvs) ++ (LR_R.zip chals)).map (fun p => (c * p.2 % qN, p.1))

/-- The full 34-term list of `(scalar, point)` pairs of statement (B), `delta` excluded (it has
coefficient 1 and is added directly). -/
def residualTerms (c z1 z2 : Nat) (chals chalInvs : List Nat) (cc ub sg : Pt) :
    List (Nat × Pt) :=
  lrTerms c chals chalInvs
    ++ [(c % qN, cc),
        ((c * CIP_N % qN + qN - z1 * B0 % qN) % qN, ub),
        ((qN - z1 % qN) % qN, sg),
        ((qN - z2 % qN) % qN, SRS_H)]

/-- **`openingResidual`** — `c·Q + delta − z1·sg − z1·b0·U − z2·H`, over K4a's unified complete
add and K4b's 255-bit ladder. -/
def openingResidual (c z1 z2 : Nat) (chals chalInvs : List Nat) (cc ub sg dl : Pt) : Pt :=
  padd (msmComm (residualTerms c z1 z2 chals chalInvs cc ub sg)) dl

/-- The relation at the block's own values, with the aggregate 5d proved our fold reproduces. -/
def realResidual : Pt :=
  openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA

/-- **`opening_inputs_are_real_pallas_points`** — the 15 `L`, 15 `R`, `sg`, `delta`, `u_base`,
`srs.h` and the aggregate are all on `y² = x³ + 5` over `Fp`, and `sg` and `delta` are distinct
finite points. -/
theorem opening_inputs_are_real_pallas_points :
    (LR_L.all (projOnCurveM pN curveB) && LR_R.all (projOnCurveM pN curveB)
      && projOnCurveM pN curveB SG && projOnCurveM pN curveB DELTA
      && projOnCurveM pN curveB SRS_H && projOnCurveM pN curveB COMBINED_GOLD
      && !isInfM pN SG && !isInfM pN DELTA && !projEqM pN SG DELTA) = true := by decide

/-- ⚑⚑ **`opening_relation_holds`** — **the IPA opening relation of a REAL Mina devnet block
holds in the Lean kernel.** 34 × 255-bit RCB ladders and 35 complete adds over the block's own
`lr` chain, its `sg`, its `delta`, the 47-term aggregate of all its commitments, and the
`u_base` §4 derived; at the `c`, `chal` and `b0` §3 derived from its own transcript. The result
is the point at infinity.

This is the first statement in this campaign whose truth says a COMMITTED polynomial has the
evaluation the proof claims — subject to the two assumptions the header names and does not
discharge: P10, and rung 5h's `sg == <s, srs.g>`. -/
theorem opening_relation_holds : isInfM pN realResidual = true := by decide

/-! ## §6 — tamper poles

Each moves exactly one input of the relation and the residual stops being `O`. Without these,
§5 would be consistent with a fold that collapses to the identity for structural reasons. -/

/-- **`tamper_z1`** — one added to the prover's `z1`. It appears in three terms at once. -/
theorem tamper_z1 :
    isInfM pN (openingResidual C (Z1 + 1) Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA)
      = false := by decide

/-- **`tamper_z2`** — one added to `z2`, the `srs.h` blinding-balance scalar. -/
theorem tamper_z2 :
    isInfM pN (openingResidual C Z1 (Z2 + 1) CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA)
      = false := by decide

/-- **`tamper_c`** — one added to the challenge `c` that scales the whole of `Q`. -/
theorem tamper_c :
    isInfM pN (openingResidual (C + 1) Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA)
      = false := by decide

/-- **`tamper_first_ipa_challenge`** — one added to `chal[0]`, which scales `R[0]`. -/
theorem tamper_first_ipa_challenge :
    isInfM pN (openingResidual C Z1 Z2 (CHAL.set 0 (CHAL.getD 0 0 + 1)) CHAL_INV
      COMBINED_GOLD U_BASE SG DELTA) = false := by decide

/-- **`tamper_last_ipa_challenge_inverse`** — and one added to `chal_inv[14]`, which scales
`L[14]`. So both ends of the 15-round chain and both sides of each round are read. -/
theorem tamper_last_ipa_challenge_inverse :
    isInfM pN (openingResidual C Z1 Z2 CHAL (CHAL_INV.set 14 (CHAL_INV.getD 14 0 + 1))
      COMBINED_GOLD U_BASE SG DELTA) = false := by decide

/-- ⚑ **`tamper_aggregate`** — the 47-term aggregate replaced by a DIFFERENT real Pallas point of
the same block (`ft_comm`, which is one of its 47 summands). This is the pole that says the
commitments are what is being opened: change what was committed and the opening fails. -/
theorem tamper_aggregate :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV
      Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD U_BASE SG DELTA) = false := by decide

/-- **`tamper_sg`** — `sg` replaced by `delta`. `sg` is the IPA's final `G`; the relation is a
statement about it, and rung 5h is what would say it is `<s, srs.g>`. -/
theorem tamper_sg :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE DELTA DELTA)
      = false := by decide

/-- **`tamper_delta_dropped`** — the `+delta` term omitted (the identity in its place). -/
theorem tamper_delta_dropped :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG Oproj)
      = false := by decide

/-- ⚑ **`tamper_u_base_sign`** — `u_base` negated, i.e. the OTHER square root of §4's `x³ + 5`.
This is what bounds the residual §4 names: the sign arkworks' `sqrt()` chooses is load-bearing,
so it is pinned by o1-labs' own output rather than free. -/
theorem tamper_u_base_sign :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD
      (U_BASE.1, (pN - U_BASE.2.1 % pN) % pN, U_BASE.2.2) SG DELTA) = false := by decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapOpeningGate

end Dregg2.Circuit.Emit.MinaWrapOpeningGate
