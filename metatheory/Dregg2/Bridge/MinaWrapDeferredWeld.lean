/-
# Dregg2.Bridge.MinaWrapDeferredWeld — **the reality gate: `expandDeferred` reproduces FIVE of the
six missing public-input words of devnet block 539508 from that block's own binprot bytes, and the
sixth to within one named scalar.**

## Why this file is separate from the function it welds

`MinaWrapDeferred` is pure functions and imports one heavy module. This file carries **the block's
`prev_evals`** — 43 evaluation columns, the public-input pair, `ft_eval1`, the accumulator
challenges — which is 90 field elements of ONE block, and it belongs off the hot path for the same
reason `MinaWrapChallengesWeld` is separate from `MinaWrapChallenges`.

## ⚑⚑ Provenance of the fixtures, and why it is not circular

`OLD_CHALS`, `BP_CHALS`, `FT_EVAL1`, `PUB_EVAL`, `EVALS`, `SPONGE_DIGEST`, the four raw challenges
and `DOMAIN_LOG2` were extracted from **`metatheory/fixtures/pickles-extractors/mina_devnet_block.json`**
— the committed base64url `protocolStateProof` of block 539508 — by re-walking
`bridge/src/mina_pickles.rs` `decode_proof_at` field for field. The walk consumed the object with
**zero trailing bytes**, which is the structural check that the layout is the right one.

The TARGETS are `MinaWrapPublicCommGate.PUBLIC_INPUT`, extracted independently by openmina's own
`PreparedStatement::to_public_input` on the same block, on a path that never reads the proof's
`prev_evals`. So §3 is a genuine differential: two extractions, two code paths, and the six words
of one are computed from the ninety values of the other.

## What §2 fixes for free

`SPONGE_DIGEST`, `BP_CHALS` and the four plonk challenges appear in BOTH artefacts. §2 pins them
equal, which is what makes the rest of the fixture credible: a binprot walk that had desynchronised
by even one field would not reproduce sixteen 128-bit challenges and a 255-bit digest.

## ⚑⚑ WHAT IS MEASURED AND WHAT IS NOT — read before quoting this file

  * **`b`, `zeta_to_srs_length`, `zeta_to_domain_size`, `perm`, `xi`: MEASURED.** Computed from the
    block's own bytes with no carrier at all, equal to `PUBLIC_INPUT` slots 1, 2, 3, 4 and 9.
  * **`combined_inner_product`: DERIVED TO WITHIN `FT_EVAL0`.** `FT_EVAL0` was SOLVED from slot 0,
    not derived — the fold is affine in it and it enters at exactly one index. So §4's equality at
    slot 0 is **NOT a discrimination on slot 0**; it is a discrimination on the other 46 legs, and
    §4b is the part that carries content. Said here, in the file, rather than left for a reader to
    infer from a green pin.
  * **The slot order at 5-7: MEASURED, and `MinaWrapPublicInput` is WRONG.** See §5.

## ⚑ COMPILED, NOT KERNEL — and now SAID OUT LOUD (2026-08-02)

Every claim below rests on the compiled evaluator, exactly as it always did: `#guard e` is
implemented as `unsafe evalExpr Bool` (Lean 4.30, `Lean/Elab/Tactic/Guard.lean:154-167`), the same
engine `native_decide` runs on. What changed is that the claims are now **named theorems** with an
axiom record, pinned by `#assert_compiled`, instead of anonymous commands that trusted the compiler
*silently* and were structurally invisible to `#assert_axioms`. Same expressions, same objects, same
evaluator, same cost — plus a name, a term in the environment, and a countable oracle.

**Which conversions gained a ∀ and which only gained a name** (`metatheory/docs/GUARD-DISCIPLINE.md`
§3). THREE gained a bounded quantifier, and each is strictly stronger than the instances it
replaces, because a transcribed instance cannot see the shape of its own index set:

  * `every_evaluation_column_is_absorbed` — all **43** columns move ξ, where two `#guard`s named
    column 42 and column 20's ζω half. An omitted column was indistinguishable from a refusing one.
  * `every_bulletproof_challenge_is_read` — all **16** challenges move `b`, where two `#guard`s
    named the first and the last.
  * `only_the_to_data_order_reproduces_perm` — of all **six** assignments of (β, γ, α) to slots
    5/6/7, exactly `to_data`'s reproduces slot 4. Two `#guard`s tested one wrong rotation and the
    right one; §5's own header says these guards "are the ONLY thing standing between the tree and a
    silent re-rotation", and four of the six rotations were not being stood in front of.

Everything else gained a name.
-/
import Dregg2.Bridge.MinaWrapDeferred

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.MinaWrapDeferredWeld

open Dregg2.Bridge.MinaWrapDeferred
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.MinaWrapPublicCommGate (PUBLIC_INPUT)
open Dregg2.Bridge.MinaWrapPublicInput
  (DeferredWords WIRE_539508 DEFERRED_539508 w539508 publicInputWords)

/-! ## §1 — block 539508's wire values, from its own binprot bytes. -/

/-- `statement.proof_state.sponge_digest_before_evaluations`, its four 64-bit limbs recombined. -/
def SPONGE_DIGEST : Nat :=
  27860000640749903405624349274249037823232876972870997514980343477933149550480

/-- `deferred_values.plonk.beta` — ⚑ public-input slot **5**. -/
def BETA_CHAL : Nat := 313463181614075351545075628406585839803
/-- `deferred_values.plonk.gamma` — ⚑ slot **6**. -/
def GAMMA_CHAL : Nat := 192135724619941679018606360956682553776
/-- `deferred_values.plonk.alpha` — ⚑ slot **7**, and this is the correction. -/
def ALPHA_CHAL : Nat := 20020606918071128765989674557881900859
/-- `deferred_values.plonk.zeta` — slot 8. -/
def ZETA_CHAL : Nat := 330389166796541696025267191640936493743
/-- `branch_data.domain_log2`. The `proofs_verified` tag is `N2`, and `3 + 4·16 = 67` is slot 29. -/
def DOMAIN_LOG2 : Nat := 16

/-- `messages_for_next_step_proof.old_bulletproof_challenges` — 2 x 16 RAW prechallenges. -/
def OLD_CHALS : List (List Nat) :=
  [[246088548388370465826188609571120644945, 304886007426414668966520405437490482221, 78214607324456480305080765119574159856, 310210561860528923542099259638393429027, 77008582040394992121293080239742250463, 131705629466194987673867262423656147653, 10008617063007508484362356212753607347, 248086302381825450806294705933140551136, 206338930091052573777256619222405971664, 288070644839764683439673129269416077397, 291648837855762743919918106968749090735, 151620828428911969479688369566924538379, 126495001039113466647896602327996906795, 129981349183449530282033777221431849234, 210631704228865981160184700268146336306, 285758433042695075839680351070333281066],
   [72193556383399114794102751663722277561, 208397833051479970954121953055935003648, 284088324873815167699897539723907232431, 130754423508617427361211970680981063414, 12629979472167747768145757411275615502, 115802936833608424569433670663583580561, 287221779115651200068936300456870986685, 337668736938073777539697020554736229997, 336243948411800164137724929581741681279, 193037524707142260272200138958218921162, 879977992082014515838338683384189423, 331911014105023590363751997711787111103, 278866074756277250792273868489957001050, 299394825515884141493890100769485323268, 29854656339660184324763940406493803795, 36418869339753156498653349833951852753]]

/-- `deferred_values.bulletproof_challenges` — 16 RAW prechallenges. ⚑ These are ALSO
public-input slots 13-28, so this fixture is checkable against `PUBLIC_INPUT` and §2 checks it. -/
def BP_CHALS : List Nat :=
  [303470030041837608182625021184247144292, 215040174751140842097626313263132934235, 116786039988294977482203225277061489760, 145647732904612004311939035064002596244, 118655921900489766024613108925676069222, 169092797198025184551686556020669572432, 226564282767834168403398696183657136270, 260600631046412867950114853686082369627, 334719724349459140876552267973395295867, 298815148206820034167176397994576632602, 323043114272259398565633317155132713683, 224654319660684979785255210812981548402, 292739584116245352526725496552824504571, 203919802211036713134713941032303566966, 302871052620997892963571361622783641311, 197159688177129719009894883897915324660]

/-- `prev_evals.ft_eval1`. -/
def FT_EVAL1 : Nat := 705114072662770467621654650915493219338965323669924470176537678109614717742

/-- `prev_evals.evals.public_input` — `(x̂(ζ), x̂(ζω))`. -/
def PUB_EVAL : Nat × Nat :=
  (23064178406611954644685674222472802365564725951259441771751720744990940515426,
   364277622860971384824294687820583388399033201074016793181334378533214929342)

/-- The 43 evaluation columns, `(at ζ, at ζω)`, in `to_absorption_sequence` order:
`z`, generic/poseidon/complete_add/mul/emul/endomul_scalar selectors, `w`×15,
`coefficients`×15, `s`×6. Each wire array had exactly ONE chunk (`arrayn` read length 1 for all
86 of them), so `evals_of_split_evals` is the identity here and the 47-entry fold applies. -/
def EVALS : List (Nat × Nat) :=
  [(18030026932263353777304215543806301431189284692226452450136232363903906692702,
    19751429210774684217189591281144448753196446705812392989801693711891477206266),
   (6930616955770521636810986930243660912797854426882038052501054941184099816748,
    19044228697660142026031121555953028583915186487967805832221157211148770345742),
   (24961218385889714224141847415023464502997613880574576180844025232203258533633,
    4635333474930626881838912832708259570357012168728660302474121383551563369066),
   (27435770877392099619092444785345732708063108268428989455166066935998234870616,
    17288662927190472120721932315228936333147213652074394460709933953368178674039),
   (27911866998467439332943144031911900833351075092574927389175402135818501611811,
    4154423181090837359995231437389065024195612349457896493081419653392042798144),
   (25482900594133273334514810721468238942079377552442169875609929104570481157030,
    27440140965971686961884013766999107407995302848978971879948839818670863120311),
   (24328785757597966895935973321875509309166782793021937738246411870288221929681,
    4225246515404285393317402841259377342093821827969366561402779561159072322782),
   (14656023297659363189323173040919583318466247425625324717039799211572600932301,
    21777682079071850583657204664591308070189684753697649957126096629376676283639),
   (27368157705800923838382361626128770119086905323011496928933999306098744337007,
    1708159119730473330102114600076986788316635527984442464358538880509306828141),
   (28194145996677751045563516554767680109300035771073854157036151330291389628451,
    15087031770967687035699731242024597251687747230055232863373466055620930838719),
   (14485875546576396051054694647987767739953358972989016420849951707114410363539,
    25679503178389224812851854546814559253374922198776110659787208258454184648769),
   (28662758265265894279197778184038944569561374625501681455706273954533178000343,
    9642494272274870571321428254946317691282050572159656975159449756241417342761),
   (4275728999213743927750935083872582360607461310593233804565233706182325595702,
    11513666134597527286845246899394713951063893675622507023465778396973181110512),
   (9904901331242822404275554897584714169851887461226286153280724882341755290604,
    15808373148677102878503188567599735963593992306754236375353075723205660000218),
   (25227878819256684226777121317441758162843237083484637931052241013822437520591,
    8447385657079285262245795438688572281676156695346632221665713573034646866807),
   (19924350719168002999355805678752841753755196592814498804960366355780570160105,
    21207129489545134879469074266810489281353789310889030329920235389092686659660),
   (14385834514773100836671415731764754617221259288774408188709252574948157353676,
    16105744634820669416158757030774590452529393069961964748533430719587298449841),
   (18554146162478719000069059464355172517997353702707188695030543891857684877129,
    8271256860744877780456272922277687196134802781304255404224766772613095733121),
   (17826804867051395990849500067857420419587388817262309777482889419152688405997,
    17678630537943532845817165721505213412920971730279118694281158406305744739863),
   (19907827170313361315426635008787383056536825309327508916458284890863643560440,
    28490376344516722050583463403117475587116625433895253103929120841247104098795),
   (18925816493266147485653454912903002771365454937230816223560409237041559412789,
    16453340641573730910919969492836014342728587668527334341695408055625777642372),
   (15078301676111738115063887904290020143156670728370123449246113427138857799534,
    24070279632082427774240689731320556699639602525677920270316501404110631450835),
   (21858321797478633945334677560531082036573690854515143285064873055593635608100,
    26797279597128385326496788792872880046722993224481778997028314962130427328085),
   (10982386797872250816507516273150858717445580543608570961017964166766912357518,
    22144323724905472099817365027518364059123520600776900715053917197209962243178),
   (15672853388963890691004564409694582184957128917771375830968558986331484945024,
    3600971205311081473783077909115259202914652374023203169931774516125424694736),
   (5315588644352199664229773222730745973250212357341544447168629542729241477248,
    9205333067658250087842065193702200964017104883432972023464758918494925922936),
   (4467058271695582791849400331091365019153566420935594567871890476414233624041,
    26079371232986980070456427999040561685666404282860400935473966114781637165734),
   (12628817332753607472662461015185143890820482429452043355587214410206787556285,
    11475461590977665915093132247343276943647402596103763370965062370086864976323),
   (24864635212913773070273200507613663089159631254954376019000731210373043866331,
    2717303991248290698234852499335605310925150433332110300629872906934504967647),
   (16962673776224555802822875780236611763280720033876978459681219646537333255914,
    15781747063086238528831404063526119299019548815896074434969743240186461231925),
   (16024259719998006868907174736085569590472839472670834383393428909073036559833,
    12896241341878602081868109642976768565529967021947996026153697458674736065517),
   (8609609539613786094918827816922692856321085507743669336008059364859040952299,
    16149186929535320599027263618703946607112269564500133255822211201627853789913),
   (5927662474877939642529680396272780563945334170840047517287859634574097816592,
    8417695635862742282400098500886032224784858457336449948186195317019015682239),
   (2315678209337686083506044668033122783655931426847176897457399750193379046076,
    13715433061054774319436022891590318547959878612818467007151689534137584913764),
   (8938575348494847612024907239197567032323584550964160531763618062954597848969,
    7784635729880893059222866221969099522885254369146384109194489060744668577675),
   (21646985152365472089988255862299478295879653476134050661034652332848485490323,
    23496418293340237644517544901833350210664732607624635126230647113289235732860),
   (12234250361854934035558943344885789181083094504631887139482841678232736814340,
    22020858637137225295036704699225146397420820939762731371984057011359250234258),
   (17964283671218709759876742473263322603626234974224788907793649331156427349105,
    14025935911920703453231138399633251023209017514678479112142216744588212641876),
   (9368944973963794231306196653394363758648252039210837223749951355122200431368,
    287788395294039455815826016723284560147609768804142972091052860728347139357),
   (22234868482971940800249135257213471785540627663862074981997985568168033883197,
    24967860314002098491437933676467134934673517800539653565153035547772756319737),
   (11911706154530287817265396171291996598615047398664796453775036699977587640909,
    23944653698821920753553538258732112363303349722886493635372878748758963877383),
   (17554563485109745892383503406445706654095654357876232895016935172895207107691,
    9835212129497933872141435100218704678131973673509878807993426911247745284058),
   (25065090211325399844525617400627471115023962902532167174286557647854766336925,
    26272315791388468086407401663212362833853705599276717939564596476398680437733)]

/-- The STEP proof's `ft_eval0`. ⚑⚑ **SOLVED FROM SLOT 0, NOT DERIVED.** `cipOf` is affine in this
argument and it enters at exactly one index, so this value is whatever makes §4 hold. It is stated
as a fixture so the shape of the fold can be exercised on real data; it is NOT evidence about slot
0, and §4 says so again at the pin. Deriving it is `KimchiVerify.ftEval0R` over the same `EVALS`,
whose own inputs beyond the wire are the seven Tick coset `shifts` and
`Plonk_checks.Scalars.Tick.constant_term`. -/
def FT_EVAL0 : Nat :=
  12860882127990787910914768203327690381994825197883726185224886388119357098804

/-- The real block, as `MinaWrapDeferred` wants it. -/
def E539508 : WrapEvals :=
  { spongeDigest := SPONGE_DIGEST, oldChals := OLD_CHALS, ftEval1 := FT_EVAL1,
    pubEval := PUB_EVAL, evals := EVALS, bpChals := BP_CHALS,
    betaChal := BETA_CHAL, gammaChal := GAMMA_CHAL, alphaChal := ALPHA_CHAL,
    zetaChal := ZETA_CHAL, domainLog2 := DOMAIN_LOG2 }

/-- The real block's tape passes the shape gate — so §9 of `MinaWrapDeferred` is not refusing
everything. -/
theorem block_539508_passes_the_shape_gate : wrapEvalsOk E539508 = true := by native_decide

/-! ## §2 — ⚑ THE FIXTURE IS THE SAME BLOCK: five wire values appear in BOTH extractions.

`PUBLIC_INPUT` came out of openmina's `PreparedStatement::to_public_input`; the values below came
out of a re-walk of the binprot proof. They agree. A walk that had desynchronised by one field
would not reproduce a 255-bit digest and sixteen 128-bit challenges. -/

/-- The `Fr`-sponge's SEED is public-input slot 10. -/
theorem sponge_digest_is_slot_10 : SPONGE_DIGEST = w539508 10 := by native_decide
/-- The sixteen bulletproof challenges are slots 13-28, in order. -/
theorem bp_chals_are_slots_13_to_28 :
    BP_CHALS = (List.range 16).map (fun j => w539508 (13 + j)) := by native_decide
/-- ζ′ is slot 8 — the one plonk challenge both readings already agreed about. -/
theorem zeta_chal_is_slot_8 : ZETA_CHAL = w539508 8 := by native_decide
/-- `branch_data` packs to slot 29: `pvBits 3 + 4 · 16 = 67`. -/
theorem branch_data_packs_to_slot_29 : 3 + 4 * DOMAIN_LOG2 = w539508 29 := by native_decide

/-! ## §3 — ⚑⚑ FIVE OF THE SIX WORDS, FROM THE BLOCK'S OWN BYTES, WITH NO CARRIER.

Nothing below reads `FT_EVAL0` and nothing below reads the slot it is compared against. -/

/-- The six words the block's bytes produce. -/
def D : DeferredWords := expandDeferred E539508 FT_EVAL0

/-- ⚑ **`xi`** — slot 9. The whole `Fr`-sponge: the seed, the fresh 32-challenge sub-sponge, the
`ft_eval1` and public-input absorbs, and all 43 columns in `to_absorption_sequence` order. A single
wrong element anywhere in that stream moves it. -/
theorem xi_is_slot_9 : D.xi = w539508 9 := by native_decide

/-- ⚑ **`b`** — slot 1. This one is downstream of the sponge's SECOND squeeze, so it also pins that
two successive `challenge()`s are lanes 0 and 1 of one permutation rather than two permutations. -/
theorem b_is_slot_1 : D.b = w539508 1 := by native_decide

/-- ⚑ **`zeta_to_srs_length`** — slot 2. `ζ^(2^16)` with the constant 16, through the endo lift and
the Type1 shift. -/
theorem zeta_to_srs_length_is_slot_2 : D.zetaToSrsLength = w539508 2 := by native_decide

/-- ⚑ **`zeta_to_domain_size`** — slot 3. `ζ^(2^domain_log2)`, and it coincides with slot 2 because
this block's `domain_log2` IS 16 — the coincidence `MinaWrapPublicInput` observed. -/
theorem zeta_to_domain_size_is_slot_3 : D.zetaToDomainSize = w539508 3 := by native_decide

/-- ⚑⚑ **`perm`** — slot 4, and the densest of the five: it reads β, γ, α, ζ, the derived ω, `z(ζω)`,
six `σ(ζ)` and six `w(ζ)`, in `derive_plonk`'s fold order, NEGATED, then Type1-shifted. -/
theorem perm_is_slot_4 : D.perm = w539508 4 := by native_decide

/-- …and the five together, as one object, so a reader cannot take four. (A corollary now, where the
`#guard` was a sixth independent compiled run of the same five sponges.) -/
theorem the_five_words_together :
    D.b = w539508 1 ∧ D.zetaToSrsLength = w539508 2 ∧ D.zetaToDomainSize = w539508 3
    ∧ D.perm = w539508 4 ∧ D.xi = w539508 9 :=
  ⟨b_is_slot_1, zeta_to_srs_length_is_slot_2, zeta_to_domain_size_is_slot_3, perm_is_slot_4,
   xi_is_slot_9⟩

/-! ### §3b — NON-VACUITY: each of the five moves when its own inputs move.

Without these, "the function returns the right five numbers" is compatible with a function that
returns five constants. One control per distinct leg of the derivation. -/

/-- The sponge SEED is read: slot 10 is not decoration. -/
theorem xi_reads_the_seed :
    (expandDeferred { E539508 with spongeDigest := SPONGE_DIGEST + 1 } FT_EVAL0).xi
      ≠ w539508 9 := by native_decide
/-- `ft_eval1` is absorbed BEFORE ξ is squeezed, so it moves ξ. -/
theorem xi_reads_ft_eval1 :
    (expandDeferred { E539508 with ftEval1 := FT_EVAL1 + 1 } FT_EVAL0).xi ≠ w539508 9 := by
  native_decide
/-- So is the accumulator-challenge digest — 32 challenges compressed into one absorb. -/
theorem xi_reads_the_accumulator_digest :
    (expandDeferred { E539508 with
        oldChals := OLD_CHALS.set 0 ((OLD_CHALS.getD 0 []).set 0 0) } FT_EVAL0).xi
      ≠ w539508 9 := by native_decide

/-- ⚑ **∀-GAIN.** **EVERY ONE** of the 43 evaluation columns is absorbed into the ξ stream — not
just the last one. The two `#guard`s this replaces named column 42 ("a stream that stopped early
passes every earlier control and fails this one") and column 20; between them they could not
distinguish a column the absorb SKIPS from a column that is genuinely read, because a skipped index
is exactly as invisible as one nobody transcribed. The bounded quantifier ranges over the whole
column set, so a dropped column is now a red build. -/
theorem every_evaluation_column_is_absorbed :
    ∀ j, j < 43 → (expandDeferred { E539508 with evals := EVALS.set j (0, 0) } FT_EVAL0).xi
      ≠ w539508 9 := by native_decide

/-- The LAST evaluation column, the instance the `#guard` asserted — now a corollary of the ∀. -/
theorem xi_reads_the_last_column :
    (expandDeferred { E539508 with evals := EVALS.set 42 (0, 0) } FT_EVAL0).xi ≠ w539508 9 :=
  every_evaluation_column_is_absorbed 42 (by decide)

/-- …and the ζω half of a column, not only the ζ half. (NOT an instance of the ∀ above, which zeroes
both halves — this is the finer claim that the second component enters the stream at all.) -/
theorem xi_reads_the_zetaw_half :
    (expandDeferred { E539508 with
        evals := EVALS.set 20 ((EVALS.getD 20 (0, 0)).1, 0) } FT_EVAL0).xi ≠ w539508 9 := by
  native_decide

/-- ζ′ moves both zeta powers. -/
theorem zeta_chal_moves_zeta_to_srs_length :
    (expandDeferred { E539508 with zetaChal := ZETA_CHAL + 1 } FT_EVAL0).zetaToSrsLength
      ≠ w539508 2 := by native_decide
/-- …and the DOMAIN moves only `zeta_to_domain_size`: at `domain_log2 = 15` slots 2 and 3 stop
coinciding. This is the pin that says the srs exponent is the CONSTANT 16 and not the domain. -/
theorem srs_exponent_is_the_constant_16 :
    (expandDeferred { E539508 with domainLog2 := 15 } FT_EVAL0).zetaToSrsLength = w539508 2 := by
  native_decide
theorem domain_size_exponent_is_the_domain :
    (expandDeferred { E539508 with domainLog2 := 15 } FT_EVAL0).zetaToDomainSize ≠ w539508 3 := by
  native_decide

/-- `perm` reads β in its own role. -/
theorem perm_reads_beta :
    (expandDeferred { E539508 with betaChal := BETA_CHAL + 1 } FT_EVAL0).perm ≠ w539508 4 := by
  native_decide
/-- `perm` reads γ in its own role. -/
theorem perm_reads_gamma :
    (expandDeferred { E539508 with gammaChal := GAMMA_CHAL + 1 } FT_EVAL0).perm ≠ w539508 4 := by
  native_decide
/-- `perm` reads α in its own role. -/
theorem perm_reads_alpha :
    (expandDeferred { E539508 with alphaChal := ALPHA_CHAL + 1 } FT_EVAL0).perm ≠ w539508 4 := by
  native_decide
/-- …and it reads `z(ζω)` (column 0's SECOND component). -/
theorem perm_reads_z_at_zetaw :
    (expandDeferred { E539508 with
        evals := EVALS.set 0 ((EVALS.getD 0 (0, 0)).1, 0) } FT_EVAL0).perm ≠ w539508 4 := by
  native_decide
/-- …and the σ column. -/
theorem perm_reads_sigma :
    (expandDeferred { E539508 with evals := EVALS.set 37 (0, 0) } FT_EVAL0).perm
      ≠ w539508 4 := by native_decide
/-- …and the LAST of the six `w` it folds over, at index 7+5 = 12. -/
theorem perm_reads_the_last_w :
    (expandDeferred { E539508 with evals := EVALS.set 12 (0, 0) } FT_EVAL0).perm
      ≠ w539508 4 := by native_decide

/-- ⚑ **∀-GAIN.** **EVERY ONE** of the sixteen bulletproof challenges is read by `b`. The two
`#guard`s this replaces named the first and the last, which is the classic pair that cannot see a
hole in the middle of its own range. -/
theorem every_bulletproof_challenge_is_read :
    ∀ j, j < 16 → (expandDeferred { E539508 with bpChals := BP_CHALS.set j 0 } FT_EVAL0).b
      ≠ w539508 1 := by native_decide

/-- The first, the instance the `#guard` asserted — now a corollary of the ∀. -/
theorem b_reads_the_first_challenge :
    (expandDeferred { E539508 with bpChals := BP_CHALS.set 0 0 } FT_EVAL0).b ≠ w539508 1 :=
  every_bulletproof_challenge_is_read 0 (by decide)
/-- …and the last. -/
theorem b_reads_the_last_challenge :
    (expandDeferred { E539508 with bpChals := BP_CHALS.set 15 0 } FT_EVAL0).b ≠ w539508 1 :=
  every_bulletproof_challenge_is_read 15 (by decide)
/-- ⚑ …and it is downstream of the sponge: a moved seed moves `b` as well as ξ, which is what makes
`r` the sponge's second squeeze rather than an independent constant. -/
theorem b_is_downstream_of_the_sponge :
    (expandDeferred { E539508 with spongeDigest := SPONGE_DIGEST + 1 } FT_EVAL0).b
      ≠ w539508 1 := by native_decide

/-! ### §3c — the derived ω is the right root of unity, and the generator is not a guess.

`rootOfUnity` derives `Backend.Tick.Field.domain_generator` from arkworks' `GENERATOR = 5`. Its
EXACT order is pinned here; §3's `perm` is the independent falsifier, since a wrong ω changes
`zkp(ζ)` and therefore slot 4. -/

/-- Order exactly `2^16`: a 2^16-th root… -/
theorem omega_16_is_a_2_16th_root : powMod (rootOfUnity 16) (2 ^ 16) pN = 1 := by native_decide
/-- …that is not a 2^15-th root. -/
theorem omega_16_is_not_a_2_15th_root : powMod (rootOfUnity 16) (2 ^ 15) pN ≠ 1 := by native_decide
/-- …and the ladder is consistent across sizes: `ω_16^2 = ω_15`. -/
theorem omega_ladder_16_to_15 : rootOfUnity 16 * rootOfUnity 16 % pN = rootOfUnity 15 := by
  native_decide

/-! ## §4 — `combined_inner_product`, and EXACTLY what it does and does not say.

⚑⚑ `FT_EVAL0` was solved from slot 0. `cipOf` is affine in it and it enters at index 3, so the
equality below is **arithmetic, not evidence about slot 0**. What it does say is that the OTHER 46
legs — two accumulator b-polynomials at both points, the public evaluation pair, `ft_eval1`, all 43
columns, ξ, r, the fold order and the Type1 shift — jointly put slot 0 within one scalar's reach,
at exactly the index kimchi's `ft_eval0` occupies. §4b is where the content is. -/

theorem cip_is_slot_0 : D.cip = w539508 0 := by native_decide

/-! ### §4b — non-vacuity of the fold: with `FT_EVAL0` HELD FIXED, every other leg moves it.

These are discriminations, because nothing here re-solves for `FT_EVAL0`. -/

/-- The accumulator challenges enter the fold as b-polynomial evaluations at the HEAD of the poly
list (`wrap.ml:60-66`), before the public polynomial — `MinaRealBlockGate` §3 pins the same prefix
on the Wrap side of this block. ⚑ This control is NOT isolating: `oldChals` also feeds
`challengesDigest`, so it moves ξ and r too. It says the value is read, not by which path. -/
theorem cip_reads_the_accumulator_challenges :
    (expandDeferred { E539508 with
        oldChals := OLD_CHALS.set 1 ((OLD_CHALS.getD 1 []).set 15 0) } FT_EVAL0).cip
      ≠ w539508 0 := by native_decide
/-- The public evaluation pair is at index 2. -/
theorem cip_reads_the_public_evaluation :
    (expandDeferred { E539508 with pubEval := (PUB_EVAL.1 + 1, PUB_EVAL.2) } FT_EVAL0).cip
      ≠ w539508 0 := by native_decide
/-- `ft_eval1` is at index 3 of the ζω column — the slot `FT_EVAL0` occupies in the ζ column. -/
theorem cip_reads_ft_eval1 :
    (expandDeferred { E539508 with ftEval1 := FT_EVAL1 + 1 } FT_EVAL0).cip ≠ w539508 0 := by
  native_decide
/-- The first of the 43 columns. -/
theorem cip_reads_the_first_column :
    (expandDeferred { E539508 with evals := EVALS.set 0 (0, 0) } FT_EVAL0).cip
      ≠ w539508 0 := by native_decide
/-- …and the last. -/
theorem cip_reads_the_last_column :
    (expandDeferred { E539508 with evals := EVALS.set 42 (0, 0) } FT_EVAL0).cip
      ≠ w539508 0 := by native_decide
/-- And the carried scalar itself is read, so slot 0 is not being reproduced without it. -/
theorem cip_reads_the_carried_ft_eval0 :
    (expandDeferred E539508 (FT_EVAL0 + 1)).cip ≠ w539508 0 := by native_decide

/-! ## §5 — ⚑⚑ THE SLOT ORDER AT 5-7: MEASURED, and the sibling was CORRECTED.

`MinaWrapPublicInput.publicInputWords` USED TO PLACE `alpha` at slot 5, `beta` at 6, `gamma` at 7.
`Wrap.Statement.to_data` (`composition_types.ml:856-866`) places `beta, gamma, alpha`. That file
flagged the mapping as **a stated reading, not a measurement**, and named the falsifier: an
extractor emitting the wire values and comparing. This is that extractor's output, and on
2026-07-30 the sibling was corrected in place — `publicInputWords` and `WIRE_539508` both now read
`to_data`'s order, and the transitional duplicate `publicInputWordsCorrected` is deleted.

The disagreement was invisible to every instrument that file had:

  * its round trip is definitional — `WIRE_539508` is projected OUT of `PUBLIC_INPUT` at the slots
    it claims, so `layout_reassembles_the_pinned_words` holds under ANY permutation of the three
    names;
  * `publicInputWords_reads_every_field` is a PERMUTATION-BLIND control: bumping `alpha` still
    moves the list, it just moves the wrong slot;
  * the width signature cannot help — all three are 128-bit challenges.

What DOES see it is `perm`, which reads β, γ and α in three distinct roles. So the theorems below are
the ONLY thing standing between the tree and a silent re-rotation, and they must stay.

⚑ UPDATED 2026-08-02. That sentence was written under two `#guard`s, which stood in front of exactly
TWO of the six assignments of (β, γ, α) to slots 5/6/7 — `to_data`'s, and one wrong rotation. Four
rotations had nothing in front of them, and an untested rotation is indistinguishable from a refused
one. `only_the_to_data_order_reproduces_perm` now quantifies over all six. -/

/-- ⚑ The wire's β is at slot 5 — NOT `alpha, beta, gamma`. -/
theorem beta_is_slot_5 : BETA_CHAL = w539508 5 := by native_decide
/-- …its γ at slot 6. -/
theorem gamma_is_slot_6 : GAMMA_CHAL = w539508 6 := by native_decide
/-- …and its α′ at slot 7. -/
theorem alpha_is_slot_7 : ALPHA_CHAL = w539508 7 := by native_decide

/-- ⚑ …and the corrected `WIRE_539508` now carries β under its own name. Before the fix these three
fields held each other's values. -/
theorem wire_beta_is_beta : WIRE_539508.beta = BETA_CHAL := by native_decide
/-- …γ under its own name. -/
theorem wire_gamma_is_gamma : WIRE_539508.gamma = GAMMA_CHAL := by native_decide
/-- …and α′ under its own name. -/
theorem wire_alpha_is_alpha : WIRE_539508.alpha = ALPHA_CHAL := by native_decide

/-- ⚑⚑ **∀-GAIN, and this is the one §5's own header asked for.** That header says these guards
"are the ONLY thing standing between the tree and a silent re-rotation" — but two `#guard`s stood in
front of exactly TWO of the six assignments of (β, γ, α) to slots 5/6/7: `to_data`'s, and one wrong
rotation. Four rotations had nothing in front of them, and an untested rotation is indistinguishable
from a refused one.

This quantifies over **all six**: `permOf` reproduces slot 4 **iff** the assignment is `to_data`'s
`(5, 6, 7)`. Both polarities in one statement — it is simultaneously the discrimination (five
rotations fail) and the proof that the discrimination is not a function that rejects everything (one
succeeds), which is what the two `#guard`s needed each other for. -/
theorem only_the_to_data_order_reproduces_perm :
    ∀ p ∈ [(5, 6, 7), (5, 7, 6), (6, 5, 7), (6, 7, 5), (7, 5, 6), (7, 6, 5)],
      ((expandDeferred { E539508 with
          betaChal := w539508 p.1, gammaChal := w539508 p.2.1,
          alphaChal := w539508 p.2.2 } FT_EVAL0).perm = w539508 4) ↔ p = (5, 6, 7) := by
  native_decide

/-- The RETIRED naming — reading slot 5 as α, slot 6 as β and slot 7 as γ — does NOT reproduce slot
4. The instance the `#guard` asserted, kept in the retired direction so a regression is caught; now
a corollary of the ∀ above. -/
theorem the_retired_naming_does_not_reproduce_perm :
    (expandDeferred { E539508 with
        betaChal := w539508 6, gammaChal := w539508 7,
        alphaChal := w539508 5 } FT_EVAL0).perm ≠ w539508 4 := by
  intro hp
  exact absurd ((only_the_to_data_order_reproduces_perm (6, 7, 5) (by decide)).mp hp) (by decide)

/-- …and under the CORRECTED naming it does, so the theorem above is a discrimination and not a
function that rejects everything. -/
theorem the_corrected_naming_reproduces_perm :
    (expandDeferred { E539508 with
        betaChal := WIRE_539508.beta, gammaChal := WIRE_539508.gamma,
        alphaChal := WIRE_539508.alpha } FT_EVAL0).perm = w539508 4 := by native_decide

/-- The corrected layout reassembles the pinned forty. Definitional in the round-trip direction —
which is precisely why the round trip was never the test — but it pins that the correction did not
lose a slot. -/
theorem the_layout_reassembles_the_pinned_forty :
    publicInputWords WIRE_539508 D = PUBLIC_INPUT := by native_decide

/-! ## §6 — ⚑ THE CENSUS, CLOSED TO 39 + 1.

With `expandDeferred` the forty words stand as:

| slots | source | status |
|---|---|---|
| 1, 2, 3, 4, 9 | `expandDeferred` | ✅ **MEASURED** from wire bytes, no carrier |
| 0 | `expandDeferred` ⊕ `ft_eval0` | ⚠ one scalar short — see §4 |
| 5-8 | wire, `to_data` order | ✅ MEASURED (§5); the previously-stated order was wrong |
| 10, 13-28, 29 | wire | ✅ MEASURED (§2) |
| 11, 12 | `MinaStateHashWordGate` | ✅ derived, per block |
| 30-39 | zero | ✅ constant |

So **39 of 40 are computable from bytes a peer serves**, and the fortieth is computable from those
same bytes plus kimchi's `ft_eval0`, which is a computation and not a source.

⚑ And that makes `public_comm` reachable: `MinaWrapChallenges.WrapAbsorbed.pubComm` is
`MinaWrapPublicInput.publicCommOf` over these forty words, so it is a function of the wire modulo
the one scalar above.

⚠ **But it is not the only non-decodable argument, and `MinaWrapChallengesWeld` says so:
`cipShifted` is the other.** That one is the WRAP proof's OWN `combined_inner_product` — a
different object in a different field from slot 0's, computed by the Wrap verifier over the Wrap
proof's own evaluations, which `decode_proof_at` also walks. `MinaRealBlockGate` §4 reproduces it
on this block with `KimchiVerify.cipR`, carrying the WRAP-side `LCT`. So after this file the
per-block path's residual is **two `ft_eval0`s** — the Step one (this file's `FT_EVAL0`, for
`public_comm`) and the Wrap one (for `cipShifted`).

⚑ **UPDATE 2026-07-30 — `Dregg2.Bridge.MinaWrapFtEval0Weld` addresses both, and they were not the
same size.** The linearization constant term is not carried at all: `KimchiVerify.gateLinConst`
transcribes all six v1 gate bodies, the real block's six gate SELECTORS are all non-zero, and that
file measures the derived constant term against `MinaRealBlockGate.LCT`. Consequently:

  * the **WRAP** `ft_eval0` — and with it `cipShifted`, via `shift_scalar` — is derived from the
    block's own bytes, and the sentence above about "a linearization constant term this tree
    carries" is retired on that side;
  * the **STEP** `ft_eval0` is derived to within ONE config object, the seven Tick coset `shifts`
    at `domain_log2 = 16`, which are Blake2b-derived per domain and are an extractor line rather
    than a formalization. `FT_EVAL0` above stays SOLVED-FROM-SLOT-0 until that line lands, and is
    the comparand it must hit. -/

/-- The forty words this file assembles ARE the pinned public input, so `publicCommOf` at them is
`PUBLIC_COMM_GOLD` by `MinaWrapPublicInput`'s own §4 pin. Stated as the list equality, because that
is the whole content: the MSM is already welded one file over. -/
theorem the_assembled_words_are_forty : (publicInputWords WIRE_539508 D).length = 40 := by
  native_decide

/-- …and the six words it contributes are exactly `DEFERRED_539508`, the projection
`MinaWrapPublicInput` could only exhibit. -/
theorem the_six_words_are_the_pinned_projection : D = DEFERRED_539508 := by native_decide

/-! ## §7 — the axiom record. ⚑ EVERY fact above rests on the COMPILED evaluator, and now says so.

`#assert_compiled` (`Dregg2/Tactics.lean`) passes iff every axiom the named theorem rests on is
either kernel-clean or a `native_decide` oracle, **and at least one oracle is present** — so it
cannot launder a kernel-clean fact downward, and a `sorry` or a fresh `axiom` is still a hard error.
Read it literally: it says "this is true by compiled evaluation, and I am saying so out loud." That
was already true of the `#guard`s these replace; the pin makes it COUNTABLE.

The corollaries (`xi_reads_the_last_column`, `b_reads_the_first_challenge`,
`b_reads_the_last_challenge`, `the_retired_naming_does_not_reproduce_perm`, `the_five_words_together`)
inherit their parents' oracles, so they are pinned by the same command. -/

#assert_compiled block_539508_passes_the_shape_gate
#assert_compiled sponge_digest_is_slot_10
#assert_compiled bp_chals_are_slots_13_to_28
#assert_compiled zeta_chal_is_slot_8
#assert_compiled branch_data_packs_to_slot_29
#assert_compiled xi_is_slot_9
#assert_compiled b_is_slot_1
#assert_compiled zeta_to_srs_length_is_slot_2
#assert_compiled zeta_to_domain_size_is_slot_3
#assert_compiled perm_is_slot_4
#assert_compiled the_five_words_together
#assert_compiled xi_reads_the_seed
#assert_compiled xi_reads_ft_eval1
#assert_compiled xi_reads_the_accumulator_digest
#assert_compiled every_evaluation_column_is_absorbed
#assert_compiled xi_reads_the_last_column
#assert_compiled xi_reads_the_zetaw_half
#assert_compiled zeta_chal_moves_zeta_to_srs_length
#assert_compiled srs_exponent_is_the_constant_16
#assert_compiled domain_size_exponent_is_the_domain
#assert_compiled perm_reads_beta
#assert_compiled perm_reads_gamma
#assert_compiled perm_reads_alpha
#assert_compiled perm_reads_z_at_zetaw
#assert_compiled perm_reads_sigma
#assert_compiled perm_reads_the_last_w
#assert_compiled every_bulletproof_challenge_is_read
#assert_compiled b_reads_the_first_challenge
#assert_compiled b_reads_the_last_challenge
#assert_compiled b_is_downstream_of_the_sponge
#assert_compiled omega_16_is_a_2_16th_root
#assert_compiled omega_16_is_not_a_2_15th_root
#assert_compiled omega_ladder_16_to_15
#assert_compiled cip_is_slot_0
#assert_compiled cip_reads_the_accumulator_challenges
#assert_compiled cip_reads_the_public_evaluation
#assert_compiled cip_reads_ft_eval1
#assert_compiled cip_reads_the_first_column
#assert_compiled cip_reads_the_last_column
#assert_compiled cip_reads_the_carried_ft_eval0
#assert_compiled beta_is_slot_5
#assert_compiled gamma_is_slot_6
#assert_compiled alpha_is_slot_7
#assert_compiled wire_beta_is_beta
#assert_compiled wire_gamma_is_gamma
#assert_compiled wire_alpha_is_alpha
#assert_compiled only_the_to_data_order_reproduces_perm
#assert_compiled the_retired_naming_does_not_reproduce_perm
#assert_compiled the_corrected_naming_reproduces_perm
#assert_compiled the_layout_reassembles_the_pinned_forty
#assert_compiled the_assembled_words_are_forty
#assert_compiled the_six_words_are_the_pinned_projection

end Dregg2.Bridge.MinaWrapDeferredWeld
