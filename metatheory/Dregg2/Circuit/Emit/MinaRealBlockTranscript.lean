/-
# `MinaRealBlockTranscript` — **C3 on the REAL Mina block**: the challenges, RE-DERIVED

## What this file closes

`docs/MINA-REAL-BLOCK-GATE.md` §3 listed one carrier under "what could NOT be fed":

> **C3 (the Fiat–Shamir transcript)** — the challenges are *recorded*, not *re-derived*. … Until it
> lands, β/γ/α/ζ/ξ/r on the real block are carried, not recomputed. This is the single largest
> remaining hole in the gate: every scalar we check is checked *given* the challenges.

They are recomputed here. Every scalar `MinaRealBlockGate` consumes as a challenge —
β, γ, α, ζ, ζω, ξ (`v`/polyscale) and r (`u`/evalscale) — now comes out of the two Poseidon
sponges of `ProverProof::oracles` run over the real block's own commitments and evaluations, and
`real_block_accepts_on_derived_challenges` restates the gate's accept with the carried values
textually replaced by the derived ones.

## Which sponge is which — the Pallas mirror

The Wrap proof is **Pallas**-committed, so by `curve.rs:62-72,87-104` the two phases are the
MIRROR of the Vesta-committed Step fixture `PastaPoseidonFq` §6 was built on:

| phase | field | params | outputs |
|---|---|---|---|
| 1 (`DefaultFqSponge`) | Pallas BASE `Fp = ZMod pN` | `other_curve_sponge_params()` = **`fp_kimchi`** (K3's constants) | β, γ, α′, ζ′, digest |
| 2 (`DefaultFrSponge`) | Pallas SCALAR `Fq = ZMod qN` | `sponge_params()` = **`fq_kimchi`** (`PastaPoseidonFq`) | v′, u′ |

So `PastaPoseidonFq`'s parametric `Core` runs BOTH: at `fpParams` for phase 1 and at `fqParams`
for phase 2. There is still exactly one absorb schedule in the tree, and `core_is_Ref_at_Fp` proves
the `fpParams` instantiation IS `PastaPoseidon.Ref` — so phase 1 here is K3's sponge, by theorem,
not by re-transcription.

## The two ORDER facts, verified against `verifier.rs` and MEASURED on this object

Both are invisible at `prev_challenges = 0`; the real block carries **2**.

1. **`ft_eval1` is absorbed BEFORE the public evaluations** — `verifier.rs:382` then `:391-392`.
2. **The prev-challenge digest sits between the fq digest and `ft_eval1`** — `verifier.rs:290-299`,
   a FRESH `EFrSponge` (here `fq_kimchi` over `Fq`) over every carried `chals`, squeezed once.

Neither is taken on a doc's word: the extractor replays both sponges with the REAL upstream
`DefaultFqSponge`/`DefaultFrSponge` and asserts each challenge against `oracles(...)`, and it
asserts that each of the two mis-orderings produces a DIFFERENT v′. The Lean side pins the same two
controls (§5).

## What is NOT established

* **No group element is touched.** The commitments enter the transcript as `(x, y)` COORDINATES;
  that they are the commitments they claim to be is the Wrap group check, which does not exist
  (`docs/MINA-REAL-BLOCK-GATE.md` §6 item 5), and it bottoms out at the IPA `msm == 0` floor (P10).
  Deriving C3 removes a carrier; it does not verify Mina.
* **The sponge is a `Nat` REFERENCE**, kernel-reducible, as K3's is. The AIR gadget that FORCES it
  (K3 §2-§4's `round_forces`/`perm_forces`) is not mirrored over the Fq heads.
* **Poseidon's collision resistance is assumed**, as everywhere in this stack; a transcript is only
  as sound as its random oracle.
* The `digest()` zero-bias (`sponge.rs:388-397`) is transcribed, not analysed.

## Axiom hygiene

`#assert_namespace_axioms`-clean; no `sorry`, no `native_decide`. Sponge evaluations are `#guard`
(kernel evaluation) — the K3 instrument, for the reason K3 measured: the `decide` proof-term path
overflows on a 255-bit 55-round permutation. Everything else is `by decide` over `ZMod qN`.

NEW standalone file. Import line for the root (do NOT edit `Dregg2.lean` from a lane):
`import Dregg2.Circuit.Emit.MinaRealBlockTranscript`
-/
import Dregg2.Circuit.Emit.MinaRealBlockGate
import Dregg2.Circuit.Emit.PastaPoseidonFq

namespace Dregg2.Circuit.Emit.MinaRealBlockTranscript

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq
  (fpParams fqParams newSponge absorbMany challenge digestInto)
open Dregg2.Circuit.Emit.KimchiVerify
  (endoMap COLUMNS PERMUTS kimchiVerifyDecisionFieldRec)
open Dregg2.Circuit.Emit.MinaRealBlockGate
  (Fq IDX_PREV PREV PUBLIC N OMEGA ZETA BETA GAMMA ALPHA VV UU A0 A1 A2 SHIFT CIP
   LCT DINV PZ FT0 FT1 ZZ ZZW WZ SZ EVZ EVZW CHALS0 CHALS1 CHALSS)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The phase-1 (Fq-sponge) absorb tape: REAL Pallas commitment coordinates in `Fp`. -/

/-- `index.digest::<EFqSponge>()` of the devnet blockchain VK (`verifier_index.rs:399-410`),
an `Fp` element — the first thing absorbed (`verifier.rs:161-163`). -/
def VKDIGEST : Nat := 27413372650305777331568266454809682207773200268004525410015286142538704636274

/-- The 2 `RecursionChallenge` commitments, `(x, y)` each in Pallas's BASE field `Fp`
(`verifier.rs:165-168` → `absorb_commitment` → `absorb_g`, `sponge.rs:198-211`). -/
def PREVCOMM_XY : List Nat :=
  [
    10103620841892308673082250846732108732474498364560765800007373095989303064281,
    19115273123489121585168139515944013217702764045475753425697749658664613315008,
    27291379157878199742119768381245655695299089028826549443942683778513132254725,
    25913404566952095352785050278254198528026315194424697297457189276858740906912 ]

/-- The public-input commitment, `(x, y)` (`verifier.rs:170-171`); ONE chunk, `chunk_size = 1`. -/
def PUBCOMM_XY : List Nat :=
  [
    470504819593367149019961354587501248284062504999182333530678460612240353949,
    6206102871863652151110650262665750758598688015582085691166368065469448164243 ]

/-- The 15 witness commitments, `(x, y)` each (`verifier.rs:173-177`). -/
def WCOMM_XY : List Nat :=
  [
    12030559674460798896999368013255417347275781434663776722408263280793332363801,
    20504119476266398644328436672590651122103295099465936887664454233597704791073,
    5217620033620423779711900821964936697146177088478349847087348940689933454354,
    2853094362483614008025714603430720102170176166196600155512350119945009310815,
    16826989906463220417879834043375722287581475034513505221640366508396272861857,
    22776490400080185241963379845000967559699840014886274622245999677517652836841,
    10195812486077238687369657852618168978391488260243432227858218879916876091057,
    19198407919208952893728287895231328255688248183770179801871869902853410749724,
    1033496553443235978589045297469160872010913418329848372072994116541535641068,
    1496896889603887248151716073492791572455854344882464665116856229490182093674,
    15823310089854448628647482478571799895364250904308734745982827705978234018542,
    5320923384880651025081281206601732871428143978783113310893418338332749663769,
    2910745483863183220714162163493838857342252775190653395584287436606170677171,
    13121781550389507695334379817138848959297803531209529011246230438190732222138,
    6961961973157090044616521060310556884395824536235438715814023966231501004690,
    2661130173084119742664883693130340769034774592808734754363656444629964892659,
    14329363957622748830392506981647066671519797094681081279625222968211030396906,
    10083320397135960231179408638642081575560788204266193790330940275886585448805,
    11169393352170449520647446013790146796778644852110677487644212454629348384380,
    17411859202646739958129990580389451121138920979756732125047905247271243878110,
    21770185939033956193586041773032048833570941442869695703178818463751839728317,
    1668636014444251900835182954769305502676324014259431669441704027572426482440,
    22578601624843807617415742214544839188953259145720491295042785398227474958044,
    4514250134370679979123480528697189828078698996525000802245861371306674118910,
    19599683610366525446659645552891457828933634923005472071941174944176120630620,
    12542896905976752492593731278089480753120930334491015284821829134052399752069,
    1256015518491031757673945583441538940536424159363835635060696043232311555604,
    4088340054853255975892792053933625699729928859082855680821824525869795856254,
    5699138341070355458194087139125137010848875492268988311860677667320391748135,
    23024696408439911566687609751593083460187358720697430363455199088596838461892 ]

/-- `z_comm`, absorbed between γ and α′ (`verifier.rs:249-250`). -/
def ZCOMM_XY : List Nat :=
  [
    3834100979779285401634906795517683834701095266964414321596828472247136072754,
    14252428545215977021007186475539470449385660381536277782963895353841633232483 ]

/-- The 7 chunks of `t_comm`, absorbed between α′ and ζ′ (`verifier.rs:259-269`). -/
def TCOMM_XY : List Nat :=
  [
    23382640723964694244614085791475445140174010552771292844771632654515403160637,
    1834425776058360070273876000949243701887690872386450124343969476133859769530,
    20421658267027367715396074495602338935050916716372351871694070908013011010291,
    24431848814686580882043032326478904323942350405263998684862417862435806498393,
    8437767720651266631202563727333255559581696471435778762846494362061787126045,
    11276986670832462284960651932652973464490945278737402618488498179480309617836,
    7946241131025672692298578151903787293968439645740063827867729888285820337110,
    10927595987986011294975437109092797646265671668037593639956868614001961557309,
    26564729323297090951288357447546753591584304754088897300539740329975354266862,
    2181201359162068961615983739336332714150726042358881483612526948087798181421,
    4110088031160970227382256682674593565642387053186990253717819687287700780866,
    23181278874497781495038467624138916413686045969349349775091313531417351742833,
    15154573345641821923530881260783904955491958425041230890861501704167338868255,
    22756676604486925033925604003249612792946449252929603692866839983627837642314 ]

/-- **`fpTape`** — the phase-1 tape up to β, ASSEMBLED from the labelled pieces in `verifier.rs`
order rather than pasted as one opaque list. -/
def fpTape : List Nat := VKDIGEST :: (PREVCOMM_XY ++ PUBCOMM_XY ++ WCOMM_XY)

/-- **`fp_tape_shape`** — 1 + 2·2 + 2 + 2·15 = 37 elements, and the prev-challenge block is the
FIRST thing after the index digest. At `prev_challenges = 0` the tape would be 33 long and those
four leading coordinates would not exist — the Wrap object is not that object. -/
theorem fp_tape_shape :
    fpTape.length = 37
    ∧ PREVCOMM_XY.length = 2 * IDX_PREV
    ∧ PUBCOMM_XY.length = 2
    ∧ WCOMM_XY.length = 2 * COLUMNS
    ∧ ZCOMM_XY.length = 2
    ∧ TCOMM_XY.length = 2 * 7
    ∧ fpTape.getD 0 0 = VKDIGEST
    ∧ fpTape.getD 1 0 = PREVCOMM_XY.getD 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 — The REAL challenges (the values the derivations below must produce, and the only
place they appear as literals). -/

/-- β, the first RAW 128-bit squeeze (`verifier.rs:233`). -/
def BETA_N : Nat := 206592757362253898583616358017451306168
/-- γ, the second RAW squeeze (`verifier.rs:236`) — lane 1 of β's state, no permutation. -/
def GAMMA_N : Nat := 174310886925763234187009919074310029385
/-- α′, the quotient PRECHALLENGE (`verifier.rs:254`). -/
def ALPHA_CHAL : Nat := 236930296339114446697708165458510007618
/-- ζ′, the evaluation-point PRECHALLENGE (`verifier.rs:273`). -/
def ZETA_CHAL : Nat := 202626382494475214331136861225910351908
/-- `fq_sponge.digest()` (`verifier.rs:283`), reinterpreted in the SCALAR field `Fq = ZMod qN` —
the mirror of the Step side, where the same call lands in `ZMod pN`. -/
def FQ_DIGEST : Nat := 15201292348477204917612940259114193872425963052441042699162252511089443044175
/-- The prev-challenge digest (`verifier.rs:290-299`). -/
def PREV_CHAL_DIGEST : Nat := 630903196966238467659939138608661521820006636543074276401148790273070366183
/-- ξ′ (`v_chal`, "polyscale") — the first phase-2 squeeze (`verifier.rs:396`). -/
def V_CHAL : Nat := 330305781815358857211111367912836029937
/-- r′ (`u_chal`, "evalscale") — the second (`verifier.rs:402`). -/
def U_CHAL : Nat := 25455272712921947007977874297033672595
/-- `Pallas::endos().1` — the SCALAR-field endomorphism coefficient `ScalarChallenge::to_field`
uses (`sponge.rs:95-98`, `curve.rs:98-100`). -/
def ENDO_R : Fq := (26005156700822196841419187675678338661165322343552424574062261873906994770353 : Fq)

/-! ## §3 — PHASE 1: β, γ, α′, ζ′ and the digest, RE-DERIVED on the real block.

`fpParams` is `⟨pN, PastaPoseidon.mdsN, PastaPoseidon.rcsN⟩` — `fp_kimchi`, which
`PastaPoseidonFq.core_is_Ref_at_Fp` proves IS `PastaPoseidon.Ref` for every input. So this is K3's
sponge, driven by `PastaPoseidonFq`'s transcription of the upstream `SpongeState` machine. -/

/-- **`wrapPhase1`** — the whole phase-1 oracle run of `verifier.rs:159-283`: absorb the tape,
squeeze β, squeeze γ, absorb `z_comm`, squeeze α′, absorb `t_comm`, squeeze ζ′, take the digest
into `ZMod qN`. NOTHING is consumed as given. -/
def wrapPhase1 : Nat × Nat × Nat × Nat × Nat :=
  let s0 := absorbMany fpParams newSponge fpTape
  let (s1, beta) := challenge fpParams s0
  let (s2, gamma) := challenge fpParams s1
  let s3 := absorbMany fpParams s2 ZCOMM_XY
  let (s4, alphaChal) := challenge fpParams s3
  let s5 := absorbMany fpParams s4 TCOMM_XY
  let (s6, zetaChal) := challenge fpParams s5
  (beta, gamma, alphaChal, zetaChal, digestInto fpParams s6 qN)

/-- The same run over substitutable tapes, for the non-vacuity pins. -/
def wrapPhase1With (tape zc tc : List Nat) : Nat × Nat × Nat × Nat × Nat :=
  let s0 := absorbMany fpParams newSponge tape
  let (s1, beta) := challenge fpParams s0
  let (s2, gamma) := challenge fpParams s1
  let s3 := absorbMany fpParams s2 zc
  let (s4, alphaChal) := challenge fpParams s3
  let s5 := absorbMany fpParams s4 tc
  let (s6, zetaChal) := challenge fpParams s5
  (beta, gamma, alphaChal, zetaChal, digestInto fpParams s6 qN)

/-! ⚑ **THE PHASE-1 RESULT**: all five phase-1 outputs of a REAL Mina devnet block fall out of the
`fp_kimchi` sponge over the block's own commitment coordinates. -/
#guard wrapPhase1 == (BETA_N, GAMMA_N, ALPHA_CHAL, ZETA_CHAL, FQ_DIGEST)
#guard wrapPhase1With fpTape ZCOMM_XY TCOMM_XY == wrapPhase1

/-! Non-vacuity, aimed at each stage of the tape. -/
-- the index digest is inside the transcript: change it and β moves
#guard wrapPhase1With (fpTape.set 0 0) ZCOMM_XY TCOMM_XY != wrapPhase1
-- ⚑ so is a RECURSION commitment coordinate — the two accumulators the block inherits are bound
-- into β, not carried beside it
#guard wrapPhase1With (fpTape.set 1 0) ZCOMM_XY TCOMM_XY != wrapPhase1
#guard wrapPhase1With (fpTape.set 4 0) ZCOMM_XY TCOMM_XY != wrapPhase1
-- and the last witness commitment coordinate
#guard wrapPhase1With (fpTape.set 36 0) ZCOMM_XY TCOMM_XY != wrapPhase1
-- `z_comm` is absorbed AFTER β and γ: it moves α′ and leaves β, γ alone
#guard ((wrapPhase1With fpTape (ZCOMM_XY.set 0 0) TCOMM_XY).1,
        (wrapPhase1With fpTape (ZCOMM_XY.set 0 0) TCOMM_XY).2.1) == (BETA_N, GAMMA_N)
#guard (wrapPhase1With fpTape (ZCOMM_XY.set 0 0) TCOMM_XY).2.2.1 != ALPHA_CHAL
-- `t_comm` is absorbed after α′: it moves ζ′ only
#guard (wrapPhase1With fpTape ZCOMM_XY (TCOMM_XY.set 13 0)).2.2.1 == ALPHA_CHAL
#guard (wrapPhase1With fpTape ZCOMM_XY (TCOMM_XY.set 13 0)).2.2.2.1 != ZETA_CHAL

/-- **`wrap_challenge_widths`** — β and γ are the RAW 128-bit squeezes (`squeeze_order`'s `false`
flags) and so are the α′/ζ′/ξ′/r′ prechallenges; the digest is a full field element. Checked
against DERIVED values, not asserted about carried ones. -/
theorem wrap_challenge_widths :
    BETA_N < 2 ^ 128 ∧ GAMMA_N < 2 ^ 128 ∧ ALPHA_CHAL < 2 ^ 128 ∧ ZETA_CHAL < 2 ^ 128
    ∧ V_CHAL < 2 ^ 128 ∧ U_CHAL < 2 ^ 128
    ∧ 2 ^ 128 < FQ_DIGEST ∧ FQ_DIGEST < qN := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4 — The prev-challenge digest: a FRESH `fq_kimchi` sponge over the 30 carried challenges.

`verifier.rs:290-299` opens a new `EFrSponge` — for a PALLAS-committed proof that is `fq_kimchi`
over `ZMod qN`, i.e. `PastaPoseidonFq`'s instantiation — absorbs every carried `chals` and squeezes
once. `FrSponge::digest` is `self.sponge.squeeze()` (`plonk_sponge.rs:50-52`), so the value is
exactly `Core.hash fqParams (chals₀ ++ chals₁)`. With 2 × 15 that is a **30-element absorb** — an
EVEN length, the branch the 2026-07-27 double-permute defect lived on. -/

/-- The 2 × 15 carried IPA challenges as `Nat`s, in the order the fresh sponge absorbs them
(`verifier.rs:292-296`: every set, concatenated, into ONE sponge). -/
def CHALS_FLAT : List Nat :=
  [
    4217715546138285440595333264337958018717768993789247502007629761805518854215,
    6248977549222504277637236958909629598777099997191783233828727182143689375819,
    12179190518229830143008067698820503257533783479892297056248564357411037035138,
    2625443789183716985039244828016277761062151498835152188608543851760317734287,
    13463707305755601123674655815105226911429591674039844567795273856246111091255,
    11630395180871655945276456245482171522021997278700795046777982539281070247759,
    16917788272323116361375188560090192184208703873978659673648847564035270581602,
    16891170529673841642707168938436220475385521037615257475090356088298102325790,
    3254042747367790262144094692264384369164183474699044321876808404403208425606,
    24908897979769350609906134300744530776964507625985672331698170646721573127582,
    25067929466187309535079705846731932811553050309001651569390922820144461433050,
    6817620349262468812703522914131113094810297064030897654669501328841837498953,
    11941689106963266206137456480971909916404331504511670413783470520895194213835,
    4140669351756734486527798292256546574798173309334109855263613228914529584871,
    15064129046689123166853020021092041919340493651024183573798282973784348670423,
    20322755958031388227760131503272881564811982751441845222720003100337185306026,
    12133231881150098703022639200739419567411246357961434335478794369892489546040,
    14117904848773170097919981713011274785086493097606417041596100780403254493971,
    8270092446564841343707599778287907782738166404867961282003711509052836846083,
    27114432580065977814544270702702110607670125117367546304951013448281438147962,
    331370462499011204577740780766005140495889457435568713643138608169252183382,
    10902572437397490442865657068152025616728169735780573296329613553800276069409,
    6497032410663406481196890788490559581235895861905992293736749324184555636939,
    18945844672662404506954582663866511041617307500282971793217815043194652073972,
    18940652583157365775172048949705868599776473454592623258599533901745304593109,
    16227563982892741163429559044459372540952653656903516125153229335126966063365,
    18291253902596534854699839079171905713884121001226205605807868773871954638459,
    23476568855294328756782185964621142577148061979607709163096622950406538171559,
    5868678840473604132370804657656176703666376129379852514332362893206470466647,
    23570295956267107706026418624788455094422895775652585995345924242434022971491 ]

/-- **`chals_flat_is_the_carried_challenges`** — and those `Nat`s ARE the gate's own `CHALS0`/
`CHALS1`, the lists `prevChalFoldOk` recomputes the b-polynomial from. One object, two views. -/
theorem chals_flat_is_the_carried_challenges :
    CHALS_FLAT.length = 2 * 15
    ∧ CHALS_FLAT.map (fun n => (n : Fq)) = CHALS0 ++ CHALS1
    ∧ CHALSS = [CHALS0, CHALS1] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ⚑ The real `prev_challenge_digest`, reproduced. -/
#guard PastaPoseidonFq.Core.hash fqParams CHALS_FLAT == PREV_CHAL_DIGEST

/-! The pre-repair (double-permuting) schedule does NOT reproduce it — the negative pin, on an
even-length input, in the field where it has never been exercised. -/
#guard (PastaPoseidonFq.Core.perm fqParams
          (PastaPoseidonFq.Core.absorbAll fqParams [0, 0, 0] CHALS_FLAT)).getD 0 0
  != PREV_CHAL_DIGEST
/-! Every carried challenge of every carried proof is inside it. -/
#guard PastaPoseidonFq.Core.hash fqParams (CHALS_FLAT.set 0 0) != PREV_CHAL_DIGEST
#guard PastaPoseidonFq.Core.hash fqParams (CHALS_FLAT.set 29 0) != PREV_CHAL_DIGEST
/-! And it is NOT the empty-sponge value the `prev_challenges = 0` shape would give — which is why
a listing that omitted this absorb could describe the right sponge state and still be wrong here. -/
#guard PastaPoseidonFq.Core.hash fqParams [] != PREV_CHAL_DIGEST

/-! ## §5 — PHASE 2: ξ′ and r′, RE-DERIVED — and the tape is the C8 columns.

The `absorb_evaluations` stream (`plonk_sponge.rs:87-155`) is `z`, the 6 gate selectors, w[0..15],
coefficients[0..15], σ[0..6], each ζ then ζω. Those are EXACTLY entries 4.. of the gate's own C8
evaluation columns (whose first four are the 2 recursion b-polys, the public evaluation and `ft`),
so the tape is not a second copy of the evaluations: it is `EVZ`/`EVZW` themselves, read through
`ZMod.val`. A prover cannot present one set of evaluations to the transcript and another to the
aggregation. -/

/-- The gate's C8 columns as `Nat`s — `ZMod.val` of the very lists `cipR` folds. -/
def EVZ_N : List Nat := EVZ.map ZMod.val
def EVZW_N : List Nat := EVZW.map ZMod.val

/-- **`evalsTape`** — `absorb_evaluations`' stream: the C8 columns after their 4-entry prefix,
interleaved ζ then ζω. -/
def evalsTape : List Nat :=
  (List.range (EVZ_N.length - 4)).flatMap
    (fun i => [EVZ_N.getD (i + 4) 0, EVZW_N.getD (i + 4) 0])

/-- **`fqTape2`** — the phase-2 absorb tape (`verifier.rs:287-393`): the fq digest, the
prev-challenge digest, `ft_eval1`, the public evaluation at ζ then at ζω, then the evaluations.
⚑ `ft_eval1` is `EVZW_N[3]` and the public evaluations are `EVZ_N[2]`/`EVZW_N[2]` — the same
entries C8 aggregates. -/
def fqTape2 : List Nat :=
  [FQ_DIGEST, PREV_CHAL_DIGEST, EVZW_N.getD 3 0, EVZ_N.getD 2 0, EVZW_N.getD 2 0] ++ evalsTape

/-- **`fq_tape2_is_the_c8_columns`** — the tape's non-digest entries ARE the gate's C8 inputs:
`ft_eval1` is the ζω entry C8 folds, `ft_eval0` its ζ partner, the public evaluation is `PZ`, and
the stream is 43 points × 2 = 86 long, for 91 absorbed elements. -/
theorem fq_tape2_is_the_c8_columns :
    EVZ_N.length = 47
    ∧ EVZW_N.length = 47
    ∧ EVZ_N.getD 2 0 = ZMod.val PZ
    ∧ EVZ_N.getD 3 0 = ZMod.val FT0
    ∧ EVZW_N.getD 3 0 = ZMod.val FT1
    ∧ evalsTape.length = 2 * 43
    ∧ fqTape2.length = 91 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`wrapPhase2`** — absorb the tape into the `fq_kimchi` sponge and squeeze twice: ξ′ then r′.
They are lanes 0 and 1 of ONE permuted state (`poseidon.rs:122-140`, rate 2). -/
def wrapPhase2 : Nat × Nat :=
  let s0 := absorbMany fqParams newSponge fqTape2
  let (s1, v) := challenge fqParams s0
  let (_, u) := challenge fqParams s1
  (v, u)

/-- The same over a substitutable tape, for the order controls. -/
def wrapPhase2With (tape : List Nat) : Nat × Nat :=
  let s0 := absorbMany fqParams newSponge tape
  let (s1, v) := challenge fqParams s0
  let (_, u) := challenge fqParams s1
  (v, u)

/-! ⚑ **THE PHASE-2 RESULT**: ξ′ and r′ of a REAL Mina devnet block, derived. -/
#guard wrapPhase2 == (V_CHAL, U_CHAL)
#guard wrapPhase2With fqTape2 == wrapPhase2

/-! ⚑ **ORDER CONTROL 1** — `ft_eval1` absorbed AFTER the public evaluations, the shape the
pre-2026-07-27 listing had. It moves ξ′. At `prev_challenges = 0` on the old fixtures this was
never exercised against a real object. -/
#guard wrapPhase2With
    ([FQ_DIGEST, PREV_CHAL_DIGEST, EVZ_N.getD 2 0, EVZW_N.getD 2 0, EVZW_N.getD 3 0] ++ evalsTape)
  != wrapPhase2

/-! ⚑ **ORDER CONTROL 2** — the prev-challenge digest omitted entirely, the shape the listing had
before it was added. It moves ξ′ too. Both controls are dead at `prev_challenges = 0`: there the
omitted value is the empty-sponge digest and the absorb is not free, but nothing in this tree had a
real object carrying two accumulators to notice on. -/
#guard wrapPhase2With
    ([FQ_DIGEST, EVZW_N.getD 3 0, EVZ_N.getD 2 0, EVZW_N.getD 2 0] ++ evalsTape) != wrapPhase2

/-! The digest chaining is load-bearing in both directions. -/
#guard wrapPhase2With (fqTape2.set 0 0) != wrapPhase2
#guard wrapPhase2With (fqTape2.set 1 0) != wrapPhase2
-- an evaluation the aggregation folds is also inside the transcript that samples ξ
#guard wrapPhase2With (fqTape2.set 90 0) != wrapPhase2

/-! ## §6 — The endomorphism lifts, and the tie to what the GATE consumed.

`ScalarChallenge::to_field(endo_r)` (`sponge.rs:67-98`) is `KimchiVerify.endoMap`, already proved
faithful to `to_field_with_length` over any `CommRing`. These four equations are what turn the
derived 128-bit prechallenges into the field elements `MinaRealBlockGate` §3-§7 fed to the
b-polynomial fold, C8 and C5. -/

/-- **`derived_alpha`** — α′ ↦ α. -/
theorem derived_alpha : endoMap ENDO_R ALPHA_CHAL = ALPHA := by decide
/-- **`derived_zeta`** — ζ′ ↦ ζ, the evaluation point everything else is stated at. -/
theorem derived_zeta : endoMap ENDO_R ZETA_CHAL = ZETA := by decide
/-- **`derived_v`** — ξ′ ↦ ξ, C8's `polyscale`. -/
theorem derived_v : endoMap ENDO_R V_CHAL = VV := by decide
/-- **`derived_u`** — r′ ↦ r, C8's `evalscale`. -/
theorem derived_u : endoMap ENDO_R U_CHAL = UU := by decide

/-- **`derived_beta`** / **`derived_gamma`** — β and γ are used RAW, so the derived `Nat` is the
field element C5 consumed. -/
theorem derived_beta : (BETA_N : Fq) = BETA := by decide
theorem derived_gamma : (GAMMA_N : Fq) = GAMMA := by decide

/-- **`derived_alpha_powers`** — and α is what C5's three permutation alphas are powers of:
`all_alphas.get_alphas(Permutation, 3)` hands out α²¹, α²² and α²³ on this index. Without this the
derivation of α would stop short of anything the gate checks. -/
theorem derived_alpha_powers : ALPHA ^ 21 = A0 ∧ ALPHA ^ 22 = A1 ∧ ALPHA ^ 23 = A2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`derived_endo_discriminates`** — the endo map is not true for free at these values: a
one-bit-different prechallenge lands elsewhere, and the four challenges are pairwise distinct
images (so `derived_*` is not four copies of one equation). -/
theorem derived_endo_discriminates :
    endoMap ENDO_R (ZETA_CHAL + 1) ≠ ZETA
    ∧ endoMap ENDO_R (ALPHA_CHAL + 1) ≠ ALPHA
    ∧ endoMap ENDO_R V_CHAL ≠ UU
    ∧ endoMap ENDO_R ALPHA_CHAL ≠ ZETA := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7 — ⚑ THE COMPOSED ACCEPT, ON DERIVED CHALLENGES.

`MinaRealBlockGate.real_block_accepts` is the assembled P6 decision accepting the real block. It is
restated here with EVERY challenge argument replaced by the transcript's own output: β and γ by the
raw phase-1 squeezes, ζ and ζω by the endo image of ζ′, the three permutation alphas by powers of
the endo image of α′, and C8's ξ and r by the endo images of the phase-2 squeezes. No `decide` runs
again — this is the gate's theorem with the carriers rewritten away. -/

/-- ⚑ **`real_block_accepts_on_derived_challenges`** — the composed decision ACCEPTS a real Mina
block **at the challenges the Fiat–Shamir transcript derives**. -/
theorem real_block_accepts_on_derived_challenges :
    kimchiVerifyDecisionFieldRec IDX_PREV PREV PUBLIC COLUMNS (PERMUTS - 1) COLUMNS 7 1 N
      (endoMap ENDO_R V_CHAL) (endoMap ENDO_R U_CHAL) EVZ EVZW CIP
      OMEGA (endoMap ENDO_R ZETA_CHAL) ((endoMap ENDO_R ZETA_CHAL) * OMEGA)
      (BETA_N : Fq) (GAMMA_N : Fq)
      ((endoMap ENDO_R ALPHA_CHAL) ^ 21) ((endoMap ENDO_R ALPHA_CHAL) ^ 22)
      ((endoMap ENDO_R ALPHA_CHAL) ^ 23) CHALSS
      WZ SZ SHIFT ZZ ZZW PZ LCT DINV FT0 true true true = true := by
  rw [derived_v, derived_u, derived_zeta, derived_beta, derived_gamma, derived_alpha,
    derived_alpha_powers.1, derived_alpha_powers.2.1, derived_alpha_powers.2.2]
  exact MinaRealBlockGate.real_block_accepts

/-! ## §8 — Residuals, named.

1. **No group element is touched, still.** The transcript eats `(x, y)` coordinates; nothing checks
   that the pair is on the curve, that `public_comm` is the commitment to the public input, or that
   a `RecursionChallenge`'s `comm` is `⟨b_poly_coefficients(chals), G⟩`. That last one is
   `accumulator_check`, whose terminal `msm == 0` is the inherited IPA opening-soundness floor
   (P10). C3 being derived does not move item 5 of `docs/MINA-REAL-BLOCK-GATE.md` §6.
2. **The verifier-index digest is an input.** `index.digest::<EFqSponge>()` is itself a sponge over
   every commitment of the VK (`verifier_index.rs:399-450`); it is absorbed here as a value. A model
   of the Wrap VK (P8/P9) is what would make it derived.
3. **No AIR gadget over the Fq/Fp sponge heads.** This is the `Nat` reference; `PastaPoseidonFq` §7
   residual 1 is unchanged.
4. **Phase-2's `public_evals` are taken from the C8 columns, which C4 does not yet recompute** —
   `p(ζ)` is `verifier.rs:336-379`'s Lagrange evaluation of the 40-element public input, and no
   check in this tree evaluates it from the public input itself.
5. **One proof, not `batch_verify`**; the `OsRng` batching scalars remain out of scope. -/

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaRealBlockTranscript

end Dregg2.Circuit.Emit.MinaRealBlockTranscript

