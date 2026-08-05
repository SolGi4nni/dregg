/-
# `Dregg2.Circuit.Emit.MinaBlockFqTranscript` — the in-AIR Fq sponge fed a REAL MINA BLOCK'S
transcript, squeezing the two challenges that block's proof actually uses.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Not one gate, column or constraint is authored here: the emitted
descriptor is `MinaWrapVerifierSponge.absorbProg` — the SAME 2 048-instruction program, the SAME
`programAir qLimb`, the SAME instruction ROM — with a different set of boundary pins. Rust proves
the artifact and authors nothing. House Law #1.

## THE RESIDUAL THIS CLOSES

`MinaWrapVerifierSponge` §9 named it: *"neither fixes that the values came from a Kimchi
transcript. That is the generator gap."* The absorption it emitted was `(0,0,0) → absorb [1,2] →
squeeze` — a sponge proving it is a sponge over numbers we chose.

**The values below were not chosen.** They are the phase-2 (`fq_kimchi`-over-`ZMod qN`) absorption
tape of the Wrap proof of

  * network **mina devnet**, state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`,
    blockchain length **539508**, fetched 2026-07-28 from a public devnet node;
  * ground truth, asserted in Rust before a number was emitted: openmina's own embedded devnet
    `BlockVerifier`, `accumulator_check(&srs, &[proof]) = true`, and
    **`kimchi::verifier::verify::<Pallas, …> = Ok(())`** — o1-labs' own verifier — plus
    `[c3] phase-2 Fr-sponge (fq_kimchi over Fq) replay over 91 absorbed elements reproduces v', u'`,
    which is an `assert!` and not a print;
  * extractor `metatheory/fixtures/pickles-extractors` (`src/main.rs:1049-1140`), consumed from
    `metatheory/mina_real_block_proof.json`.

⚑ **WHY OUR Fq SPONGE IS THE RIGHT ONE FOR A BLOCK.** `PastaPoseidonFq`'s naming table: a Mina
block's proof is the **Wrap** proof, Pallas-committed, so its phase-1 sponge is `fp_kimchi` and its
**phase-2 sponge is `fq_kimchi` over `ZMod qN` — this machine's constants.** Its two outputs are
`v` (polyscale) and `u` (evalscale), the challenges that combine the opening. `PastaPoseidonFq` §7
listed *"the Wrap-side phase-2 use is by the table, not by a fixture … needs a real Wrap fixture,
which still does not exist in this tree"* — it exists, and this is it.

## ⚑ WHAT IS IN THE AIR AND WHAT IS NOT — the honest split, stated before the theorems

The block's phase-2 tape is **91 elements**, which at rate 2 costs **46 permutations**. One
permutation is 1 650 emitted rows; 46 is 75 900 rows, a 207 MB witness. **One** of those 46 is
emitted here — the LAST one, the closing squeeze — together with the absorb that feeds it.

That is a FIXTURE-SIZE fact and not a soundness one, and the distinction is checkable:
`the_permutation_program_computes_the_kimchi_permutation` holds for EVERY input register file, so
the emitted descriptor is already the right statement about the other 45; what is missing is 45 more
WITNESSES. The 45 are carried here by `PastaPoseidonFq.Core` — the reference the AIR program is
proved to compute — and the join is `the_link_input_is_the_real_tape_prefix`.

⚑ **AND THE JOIN IS NOT TRUSTED ON ITS OWN.** The AIR's input state `LINK_S` is DERIVED from the
91-element tape, never typed; and a wrong `LINK_S` cannot produce the right `v`/`u`, so the output
pin checked against the block's own oracles is a gate on the whole prefix. The Rust harness checks
both ends against `mina_real_block_proof.json` — an artifact this file cannot influence.

## WHICH GATE REFUSES WHAT (measured on the wire in `circuit/tests/pasta_fq_wrap_transcript_proves.rs`)

`MinaWrapVerifierSponge` §9's pole inversion is inherited verbatim and matters more here:

  * the **ROM bus** refuses a wrong round constant — the 55×3 `fq_kimchi` constants are IMMEDIATES,
    hence descriptor cells (`the_rom_pins_the_round_constant_schedule`);
  * the **pc thread** refuses a reordered instruction;
  * the **boundary pins** refuse a wrong absorbed value or a wrong squeeze — the absorbed value is a
    register operand with a zero immediate, so the ROM is silent about WHICH value it is
    (`the_absorbed_value_is_not_a_rom_constant`). **The transcript binding therefore rests on the
    PIN, not on the bus**, and that is the mechanism the tamper test must fire.

## Axiom hygiene

Kernel-clean where the kernel reaches; the facts that are 46 Poseidon permutations of a 255-bit
state are `native_decide` + `#assert_compiled` — a confession that they rest on the compiled
evaluator, which is what a `#guard` would have hidden. No `sorry`, no `#guard`.

Import line for the root: `import Dregg2.Circuit.Emit.MinaBlockFqTranscript`
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierSponge

namespace Dregg2.Circuit.Emit.MinaBlockFqTranscript

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt qLimb)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams)

set_option autoImplicit false
set_option maxRecDepth 400000

/-! ## §1 — THE TAPE, from the block.

⚑ Assembled by `pickles-extractors/src/main.rs:1083-1087` as
`[fq_digest, prev_challenge_digest, ft_eval1] ++ public_evals[0] ++ public_evals[1] ++ evals_tape`,
where `evals_tape` is the 86-element `absorb_evaluations` order (`z`, the six selectors, `w[15]`,
`coefficients[15]`, `s[6]`, each at ζ then ζω). The extractor asserts TWO order controls move `v′`:
`ft_eval1` after the public evaluations, and dropping the prev-challenge digest. So the ORDER below
is not a reading of the source — it is the order the real object's own challenges came out of. -/

/-- The 91 field elements the real block's Wrap proof absorbs into its phase-2 `fq_kimchi` sponge. -/
def WRAP_TAPE2 : List Nat :=
  [
    15201292348477204917612940259114193872425963052441042699162252511089443044175,  -- fq_digest — the phase-1 sponge digest of the SAME proof
    630903196966238467659939138608661521820006636543074276401148790273070366183,  -- prev_challenge_digest — 2 RecursionChallenge accumulators, folded
    28155104853570418623791710384917893870113870215094008739334981617926633024152,  -- ft_eval1
    11090203480785459933028184905911281390387616235389803013122300906165701510005,  -- public_evals[0] (zeta)
    14605652823947705187330850190450734801314158295043389107883736369979449599424,  -- public_evals[1] (zeta_omega)
    28416128832493449022787015787472083804995350625800671585362604203170297603321,  -- evals[0]
    11129278808702418813819913219602235145901771822561154715079095547577311982408,
    1927184667573946196882536775478232476090289718300837237666732406827082696846,
    14057127486417497142712617157073381598146028573494944128221830309811829387719,
    10961545952687831694800729976743099915493104958708085379754961344970278498990,
    22651568075922656258556602616923864323635457962174814516858560100430202072144,
    19273493614812096382843864137175255449483458290012704025389054300435248729442,
    229655201963991198213495608742423820808686310297089823314531946447623434130,
    1195501512746387623696890853508004161528805271222296635552640902110278482989,
    23119500706649516008027628065715377439076604315132984729792960333344713421325,
    16923371226594018172647199151754921179019944018841128524673732352247151652647,
    4246652717072868138510107172969557346794546945339977496314488051260205700356,
    20508417494143447197130053467337553797776880673667072384643447083280387857283,
    28513023147517945961686466190449203965432741086842644471972605050452494168032,
    10147518268551509113412971664125967424773492262603325548290108484859858563971,
    25718866410029790701152150063304790645075965725964049876312559414479779061972,
    9971934459624574017831330607746870794348852745926218174772972125650720517119,
    20803220024285994193973701286700194154824210529877076072530939591211070630643,
    5498199022414063411922335182972930862383545507410462945805512918806112693929,
    18393697063020502925980761642645106516072482093133099216332926386490790506871,
    2959739707360294758844882268291338428013283013241611353892721806047382874764,
    21502774688429492638523286733650310446602903259121611850143528219818443879835,
    24433451113246204392860479233495856035189050393014662139000226824092372399717,
    12235777327706625627366525529607645696081684070793301149493359729254283575917,
    5716284018551260496752359362305581715307544820949297814294834926453747887189,
    19034025110072047859159451275299755062914513409341795424204230811454059269392,
    19589287715766372320965211021468080883162299418993028472390024363452399195059,
    5278356165001895702056593534095483661631418632014744175820449720397303888311,
    2228214401514847824251217005147463498461409483761802219931468749059047863169,
    26305540344391767806307562693128700160433298800506948690877121555087535455110,
    19394443214189628111006741173961078199292326904776110416895744052796882933329,
    24535475115273831279353310660056066558480867742937801742346589089504843872646,
    6629679071195830316599335452091905203843943588851777886104206588694509869571,
    16724469185678446079079218224389990299729893172967425826669744377863166213554,
    10259102355387028716720611076638617354362062170118334067947667000965978212841,
    8298646419468965983439055962277089237336348220115060651241340224926452022747,
    3393445151574487951551236928154672745697910422014923047390988709289585698828,
    16030341667496515077144163481238009605891777541068025008422495515743139738912,
    16213484004747824391187979638880746762537767145372127282312349599557426920774,
    19216223437324956675753961586572928245734540351516826480698587931999257927437,
    21214879179115338594521954462563039704254487597628000737126670870816049514957,
    2280234943847817705242650572699534313453698943208641090246091072395528869228,
    24834512868290478959339619542081241644301747067317954302300874585410111775220,
    1140252356548062423548862729872012296666023208809720455663166516450832335857,
    25033092993242804043993529682446760822567588303364468318089027597912165542256,
    6492223165704917194701380793617999937016163942189564306822510078169074415011,
    162283894516092935762879815229351089890839196129378445540308688632258365609,
    21008772876230699713368801123686955661651007197695676667973065308810618265500,
    11497171915900849686603337024977009671581374029701489777951047292788032711531,
    1518069428232535009717450923991106394269682025730317025479387402983005136430,
    22937647827457293366522349781799371608491039570339348968062471281877178490950,
    28931173153282862567443237437149505898715368053646211042363155538731329220402,
    25276042029415000067452182393390229139917473291133382741724381283623317383440,
    20408447456465856963551292865939880219820095528706997523845482446023784095670,
    16542184928575919658695631855631449862579791598070964575072898111344554424545,
    9726399592462409502147728317525782557462613859067883543060805990580148984238,
    9465672208407380755631114480425011546717054919408778028351899820351690902440,
    6995511826060680267506108573654887251428525794765817396075639866530335981677,
    24220329555273500885567100510810664728502434643131857193566568548058069919840,
    24534291712448030453333534501811782376296221066286511658628652481276689755474,
    20783154562833646855376525098478768858205875920275498684051941783444956161524,
    6877191248312691249682271017682835268121282363801534854883774321966737779294,
    14341686643286633507236119062526180133361798302543786387988541648226060603384,
    8430698101548772034677449867910792660080456634385858326044802991376092525888,
    22395238394896559298007524326925935054032002354454829716169739439095620866883,
    8631014844848912136477549144839050347203147513082259177934033794611733459005,
    25367774631215073544215174707960834349679778759453868468205717679197411974856,
    2492427048822195605308811882945392052008198441135573117037825671764576967160,
    9516996471676816490145611982807745817277695089303859947571664541063765889026,
    23976579510836973948465407577616444552529641759375869534681014482619375761170,
    3129615503199909356699423941934892952073139748619491233913004132198070469481,
    10153788422230401945513196615300913717970983140744226104667545057469543243864,
    10420576377226454117987203548198810820078728471606474150657125648359810545167,
    4625621513560175984273442747170006042727825653245811690707759229663877513307,
    4092042567587533630330563597343519057951757576999329152983801530795996793302,
    11461081468863241002321311364313736750202038463319084194929825052489591657762,
    26769662245038254208815966370331984451087765712926012410732770364753873887759,
    7280593825400665615249900323063235348730250822285497833693135450852802071036,
    1833364812298695055868818288152832872109230335909541395497046368690771202829,
    2845398783703847210017121072210830992662521686726315572651480098408894822211,
    3734719539420070565730776946341743913734655647345941175902788953705853028779,
    1772818656689192745983863955618253190605112764908488289042661460746677435528,
    3410907740173549587200517698353157339957773657956648259583912299367960920754,
    15909778669631376514816198814095280384014390783061722109369876686134111423750,
    12385978812211689722969378614395923784689560997309794525971870850009054573226,
    17505320526635328822879187106947217055599935964967983271860605200499954398921
  ]

/-- The two challenges `proof.oracles(...)` returned on this block, as `ScalarChallenge` values
(before the endomorphism lifts them): `v′` is the polyscale, `u′` the evalscale. -/
def WRAP_V_CHAL : Nat := 330305781815358857211111367912836029937
def WRAP_U_CHAL : Nat := 25455272712921947007977874297033672595

/-- ⚑ **THE TAPE'S SHAPE**, so a truncated or over-long paste is a red rather than a different
(still true) sentence: 91 elements, every one a canonical `ZMod qN` element, and the first is the
phase-1 digest of the same proof — the element that makes the phase-2 sponge a CONTINUATION of the
phase-1 one rather than a fresh transcript. -/
theorem wrap_tape2_shape :
    WRAP_TAPE2.length = 91
    ∧ (WRAP_TAPE2.all (fun x => decide (x < qN))) = true
    ∧ WRAP_TAPE2.getD 0 0 = 15201292348477204917612940259114193872425963052441042699162252511089443044175
    ∧ WRAP_V_CHAL < 2 ^ 128 ∧ WRAP_U_CHAL < 2 ^ 128 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 — THE REFERENCE SPONGE OVER THE REAL TAPE IS THE BLOCK'S OWN `v′`/`u′`.

⚑ This is the weld to o1-labs at its strongest available point. `PastaPoseidonFq.Core` carries the
`fq_kimchi` MDS and 55×3 round constants dumped from `mina_poseidon::pasta::fq_kimchi::
static_params()`, and `SpongeSt`/`challenge` transcribe the `ArithmeticSponge` state machine. Below,
that object — with NOTHING adjusted — reproduces two numbers a Mina devnet node's own proof
committed to, computed by openmina's verifier on a proof o1-labs' `kimchi::verifier::verify`
accepts. A single wrong round constant, a single wrong MDS entry, or the absorb schedule permuting
once too often would move both. -/

/-- The whole phase-2 oracle run: absorb the tape, squeeze `v′`, squeeze `u′`. ⚑ `u′` costs NO
permutation — it is lane 1 of `v′`'s state, which is `squeeze1`'s `Squeezed 1` branch. -/
def wrapPhase2 : Nat × Nat :=
  let s0 := PastaPoseidonFq.absorbMany fqParams PastaPoseidonFq.newSponge WRAP_TAPE2
  let (s1, v) := PastaPoseidonFq.challenge fqParams s0
  let (_, u) := PastaPoseidonFq.challenge fqParams s1
  (v, u)

/-- ⚑ **THE Fq SPONGE RECOMPUTES A REAL MINA BLOCK'S TRANSCRIPT.** -/
theorem the_fq_sponge_reproduces_the_real_blocks_challenges :
    wrapPhase2 = (WRAP_V_CHAL, WRAP_U_CHAL) := by native_decide

/-- Non-vacuity, at the head of the tape: perturbing the phase-1 digest — the element that binds
the two sponges together — moves both challenges. Without this the theorem above could be true of a
sponge that ignored its input. -/
theorem a_tampered_tape_head_moves_both_challenges :
    (let s0 := PastaPoseidonFq.absorbMany fqParams PastaPoseidonFq.newSponge (WRAP_TAPE2.set 0 0)
     let (s1, v) := PastaPoseidonFq.challenge fqParams s0
     let (_, u) := PastaPoseidonFq.challenge fqParams s1
     (v, u)) ≠ (WRAP_V_CHAL, WRAP_U_CHAL) := by native_decide

/-- …and at its tail: perturbing the LAST absorbed element, which is the one this file puts on the
machine, moves them too. -/
theorem a_tampered_tape_tail_moves_both_challenges :
    (let s0 := PastaPoseidonFq.absorbMany fqParams PastaPoseidonFq.newSponge (WRAP_TAPE2.set 90 0)
     let (s1, v) := PastaPoseidonFq.challenge fqParams s0
     let (_, u) := PastaPoseidonFq.challenge fqParams s1
     (v, u)) ≠ (WRAP_V_CHAL, WRAP_U_CHAL) := by native_decide

/-! ## §3 — WHAT THE EMITTED PROGRAM COMPUTES AT AN ARBITRARY STATE.

`MinaWrapVerifierSponge.the_absorb_program_computes_the_kimchi_sponge` needed a FRESH sponge
(`st 0 = st 1 = st 2 = 0`), because it was answering "is this `Core.hash`". A transcript link starts
from a state 45 permutations deep, so the fresh hypothesis has to go — and it turns out it was never
load-bearing. The theorem below is the same statement with the three zero hypotheses and the two
canonicity hypotheses DELETED, and it implies the old one. -/

/-- ⚑ **THE ABSORB PROGRAM IS `perm ∘ absorb`, AT EVERY STATE.** No hypotheses: the machine reduces
mod `qN` on the add, which is exactly what `Core.absorbAt` does. -/
theorem the_absorb_program_permutes_the_absorbed_state (st : RegFile) :
    [ runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.perm fqParams
          [(st 0 + st 3) % qN, (st 1 + st 4) % qN, st 2] := by
  have h0 : runProgAt qN st absorbInstrs 0 = (st 0 + st 3) % qN := by
    simp [runProgAt, absorbInstrs, stepRegsAt, opResultAt, yValue, NREG, refAdd]
  have h1 : runProgAt qN st absorbInstrs 1 = (st 1 + st 4) % qN := by
    simp [runProgAt, absorbInstrs, stepRegsAt, opResultAt, yValue, NREG, refAdd]
  have h2 : runProgAt qN st absorbInstrs 2 = st 2 := by
    simp [runProgAt, absorbInstrs, stepRegsAt, NREG]
  have hperm := the_permutation_program_computes_the_kimchi_permutation
    (runProgAt qN st absorbInstrs) PastaPoseidon.rounds
  rw [h0, h1, h2] at hperm
  have hsplit : runProgAt qN st absorbCore
      = runProgAt qN (runProgAt qN st absorbInstrs) permInstrs := by
    rw [absorbCore, runProgAt_append]
  rw [hsplit, permInstrs]
  exact hperm

/-- ⚑ **AND IT SUBSUMES THE FRESH-SPONGE THEOREM.** Stated so the generalisation is a fact and not
a claim in a docblock: the `[1,2]` absorption's denotation is this one at `st 0 = st 1 = st 2 = 0`. -/
theorem the_general_theorem_subsumes_the_fresh_one (st : RegFile)
    (h0 : st 0 = 0) (h1 : st 1 = 0) (h2 : st 2 = 0) (_hx₀ : st 3 < qN) (_hx₁ : st 4 < qN) :
    [ runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.absorbAll fqParams [0, 0, 0] [st 3, st 4] := by
  have hspec : PastaPoseidonFq.Core.absorbAll fqParams [0, 0, 0] [st 3, st 4]
      = PastaPoseidonFq.Core.perm fqParams [(0 + st 3) % qN, (0 + st 4) % qN, 0] := rfl
  rw [hspec, the_absorb_program_permutes_the_absorbed_state st, h0, h1, h2]

/-! ## §4 — THE LINK: the last absorb of the real tape, on the machine.

The tape's 91st element arrives at a full rate block, so the upstream state machine permutes, adds
it into lane 0, and the squeeze permutes again. `LINK_S` is the state after that FIRST permutation —
**derived from the tape, never typed** — and the machine's program is the existing `absorbProg` with
`x₁ = 0`, since adding zero into lane 1 is the identity the state machine's counter already implies.

⚑ So the emitted instance is: **absorb the real 91st element into a real 45-permutation-deep sponge
state, permute, and read lanes 0 and 1.** Those two lanes' low 128 bits are `v′` and `u′`. -/

/-- The sponge after the first 90 tape elements — mode `Absorbed 2`, a full rate block. -/
def linkPre : PastaPoseidonFq.SpongeSt :=
  PastaPoseidonFq.absorbMany fqParams PastaPoseidonFq.newSponge (WRAP_TAPE2.take 90)

/-- ⚑ **THE MACHINE'S INPUT STATE, DERIVED.** The arrival permutation the 91st element triggers. -/
def LINK_S : List Nat := PastaPoseidonFq.Core.perm fqParams linkPre.st

/-- The 91st and last absorbed element of the real tape. -/
def LINK_X : Nat := WRAP_TAPE2.getD 90 0

/-- The six-entry register file the witness starts from: the three real state lanes, the real
absorbed element in `R3`, and `0` in `R4` — the second absorb slot, a no-op. -/
def linkInitVec : List Nat :=
  [LINK_S.getD 0 0, LINK_S.getD 1 0, LINK_S.getD 2 0, LINK_X, 0, 0]

/-- ⚑ **THE JOIN.** Absorbing the whole 91-element tape leaves the sponge in exactly the state the
machine's input pins describe — `LINK_S` with `LINK_X` added into lane 0, lane counter 1. This is
what makes the emitted instance a link of the REAL transcript and not a permutation of some numbers
that happen to be 255 bits wide. -/
theorem the_link_input_is_the_real_tape_prefix :
    PastaPoseidonFq.absorbMany fqParams PastaPoseidonFq.newSponge WRAP_TAPE2
      = ⟨PastaPoseidonFq.Core.absorbAt fqParams LINK_S 0 LINK_X,
         PastaPoseidonFq.Mode.absorbed 1⟩ := by native_decide

/-- The trace, from the STRICT generator — `runRowsVecAt`, the one
`runRowsVecAt_is_runRowsAt` welds to `runRowsAt`. Rust fills no cell. -/
def linkTrace : List (List ℤ) := runRowsVecAt qN qLimb linkInitVec 0 absorbProg

/-- ⚑ **AND THE EMITTED TRACE IS `runRowsAt`'s** — the object every denotation above is a statement
about. -/
theorem linkTrace_is_the_program_run :
    linkTrace = runRowsAt qN qLimb (regsOf linkInitVec) 0 absorbProg := by
  rw [linkTrace, runRowsVecAt_is_runRowsAt]

/-- The register file the link ends in, run strictly. -/
def linkOutVec : List Nat := runProgVecAt qN linkInitVec absorbCore

/-- The raw squeeze of lane 0 — `v′` before the two-limb truncation. Computed by the interpreter
from the machine's inputs; never asserted. -/
def LINK_V_RAW : Nat := regsOf linkOutVec (allocAt PastaPoseidon.rounds 0)

/-- …and lane 1, which is `u′`'s raw squeeze and costs no permutation. -/
def LINK_U_RAW : Nat := regsOf linkOutVec (allocAt PastaPoseidon.rounds 1)

/-- ⚑ **THE EMITTED LINK'S OUTPUT IS THE KIMCHI SPONGE'S.** Kernel-clean, and an instance of the
GENERAL theorem — so the artifact inherits a statement that holds at every state, not a checked
point. -/
theorem the_link_output_is_the_permuted_absorbed_state :
    [ LINK_V_RAW, LINK_U_RAW, regsOf linkOutVec (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.perm fqParams
          [(LINK_S.getD 0 0 + LINK_X) % qN, (LINK_S.getD 1 0 + 0) % qN, LINK_S.getD 2 0] := by
  have h : regsOf linkOutVec = runProgAt qN (regsOf linkInitVec) absorbCore := by
    rw [linkOutVec, regsOf_runProgVecAt]
  show [ regsOf linkOutVec (allocAt PastaPoseidon.rounds 0)
       , regsOf linkOutVec (allocAt PastaPoseidon.rounds 1)
       , regsOf linkOutVec (allocAt PastaPoseidon.rounds 2) ] = _
  rw [h]
  exact the_absorb_program_permutes_the_absorbed_state (regsOf linkInitVec)

/-- ⚑⚑ **THE RESULT: THE MACHINE SQUEEZES THE BLOCK'S OWN CHALLENGES.** The two raw lanes the
emitted 2 048-row trace ends on, truncated to the two high-entropy limbs `challenge()` keeps, ARE
the `v′` and `u′` `proof.oracles(...)` returned on Mina devnet block 539508. -/
theorem the_machine_squeezes_the_real_blocks_v_and_u :
    LINK_V_RAW % 2 ^ 128 = WRAP_V_CHAL ∧ LINK_U_RAW % 2 ^ 128 = WRAP_U_CHAL := by
  native_decide

/-- Non-vacuity of the machine half: change the absorbed element in the register file and the
squeeze moves. This is the fact the boundary PIN enforces on the wire — the ROM says nothing about
the absorbed value (`the_absorbed_value_is_not_a_rom_constant`). -/
theorem a_tampered_absorbed_element_moves_the_machines_squeeze :
    regsOf (runProgVecAt qN (linkInitVec.set 3 (LINK_X + 1)) absorbCore)
        (allocAt PastaPoseidon.rounds 0) ≠ LINK_V_RAW := by native_decide

/-- …and so does a change to the incoming state lane the block's own prefix determined. -/
theorem a_tampered_input_state_moves_the_machines_squeeze :
    regsOf (runProgVecAt qN (linkInitVec.set 0 0) absorbCore)
        (allocAt PastaPoseidon.rounds 0) ≠ LINK_V_RAW := by native_decide

/-! ## §5 — THE EMITTED DESCRIPTOR.

⚑ **SEVEN pin blocks, 224 public inputs** — the `[1,2]` absorption's six plus lane 1 of the squeeze,
because a Wrap link produces TWO challenges from one permutation and pinning only `v′` would leave
`u′` a claim about a register nothing reads.

⚑ **AND THE PROGRAM IS BYTE-IDENTICAL.** `linkAir` is `programAir qLimb absorbProg` — the same
2 048 instructions, so the same instruction ROM, so the same 55×3 `fq_kimchi` round constants as
cells of the descriptor. The Rust harness asserts the two descriptors' ROM manifests are equal row
for row; that is what makes "the constants that hashed `[1,2]` are the constants that recomputed the
block" a checked statement rather than a shared source file. -/

def LINK_PI_COUNT : Nat := 7 * SK

theorem LINK_PI_COUNT_eq : LINK_PI_COUNT = 224 := rfl

/-- The pins: the three incoming state lanes, the absorbed element, the zero second slot, and BOTH
squeezed lanes. -/
def linkPins : List AirLeg :=
  pinBlock VmRow.first 0 0 ++ pinBlock VmRow.first 1 SK ++ pinBlock VmRow.first 2 (2 * SK)
    ++ pinBlock VmRow.first 3 (3 * SK) ++ pinBlock VmRow.first 4 (4 * SK)
    ++ pinBlock VmRow.last 4 (5 * SK) ++ pinBlock VmRow.last 5 (6 * SK)

def linkAir : EffectAir :=
  { programAir qLimb absorbProg with legs := (programAir qLimb absorbProg).legs ++ linkPins }

theorem linkAir_mainRailOk : linkAir.mainRailOk = true := by
  unfold linkAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk qLimb absorbProg, ?_⟩
  simp only [linkPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

/-- ⚑ **THE EMITTED WRAP-LINK DESCRIPTOR.** -/
def linkDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fq-wraplink::v1" PROG_WIDTH LINK_PI_COUNT [] linkAir

/-- The 224 public inputs, every one computed from the tape or from the interpreter. -/
def linkPIs : List ℤ :=
  (List.range SK).map (limbAt (LINK_S.getD 0 0))
    ++ (List.range SK).map (limbAt (LINK_S.getD 1 0))
    ++ (List.range SK).map (limbAt (LINK_S.getD 2 0))
    ++ (List.range SK).map (limbAt LINK_X)
    ++ (List.range SK).map (fun _ => (0 : ℤ))
    ++ (List.range SK).map (limbAt LINK_V_RAW)
    ++ (List.range SK).map (limbAt LINK_U_RAW)

theorem linkPIs_length : linkPIs.length = 224 := by
  simp [linkPIs, SK]

/-- ⚑ **THE SECOND ABSORB SLOT IS PINNED TO ZERO.** Without this the descriptor would be a sentence
about a link that absorbed TWO elements, one of them unconstrained — and the statement "this is the
tape's last element" would be false of it. -/
theorem the_link_absorbs_exactly_one_element :
    ((linkPIs.drop (4 * SK)).take SK).all (fun v => decide (v = 0)) = true := by decide

/-! ## §5b — THE CENSUS CORRECTION, TO THE FIGURE.

`MinaWrapVerifierSponge.the_census_underprices_the_round` bracketed the error at 42–43%; the
docblocks then said "43%", which rounds the wrong way for a number that gets quoted. The exact
split is stated here because this file is where the 46-permutation price is computed from it. -/

/-- ⚑ **A PERMUTATION IS 1 650 OPS: 1 155 MULTIPLIES AND 495 ADDITIONS.** The census
(`ROWS_PER_POSEIDON_PERM = 1155`) counted the multiplies and none of the additions — not "most" of
them, ALL 495: the two sums each 3×3 MDS row needs and the round constant on top, 9 per round. The
last two clauses bracket the ratio inside `(1.428, 1.429)`, i.e. the census is low by **42.9%**, not
43% and not 42%. -/
theorem the_permutation_opcode_split_exactly :
    PastaPoseidon.rounds * 21 = 1155
    ∧ PastaPoseidon.rounds * 9 = 495
    ∧ 1155 + 495 = ROWS_PER_PERM_MEASURED
    ∧ ROWS_PER_PERM_MEASURED = 1650
    ∧ 1428 * MinaWrapVerifierAir.ROWS_PER_POSEIDON_PERM < 1000 * ROWS_PER_PERM_MEASURED
    ∧ 1000 * ROWS_PER_PERM_MEASURED < 1429 * MinaWrapVerifierAir.ROWS_PER_POSEIDON_PERM := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **AND WHAT THIS BLOCK'S PHASE-2 SPONGE COSTS.** 91 elements at rate 2 is 45 arrival
permutations plus the closing squeeze — **46**, which is 75 900 emitted instructions. The tape is a
third of one `MinaWrapVerifierAir` transcript-stage permutation budget and would be a 207 MB witness
at the measured row width; that is the whole reason one link is emitted rather than all of them. -/
def WRAP_TAPE2_PERMS : Nat := 46

theorem the_block_tape_costs_46_permutations :
    WRAP_TAPE2.length = 91
    ∧ (WRAP_TAPE2.length - 1) / 2 + 1 = WRAP_TAPE2_PERMS
    ∧ WRAP_TAPE2_PERMS * ROWS_PER_PERM_MEASURED = 75900
    ∧ WRAP_TAPE2_PERMS * ROWS_PER_PERM_MEASURED < MAX_ROM_CELLS / ROM_ARITY := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6 — RESIDUALS, NAMED.

1. **One permutation of 46 is in the AIR.** The other 45 are `PastaPoseidonFq.Core` — the reference
   the AIR program is PROVED to compute at every state, so this is a witness-size residual, not an
   algebra one. Emitting all 46 is 75 900 rows / ~207 MB against a repository whose largest tracked
   file is 10 MB; a chain of 46 instances welded by input/output pin equality is the shape that
   closes it, and it is not built here.
2. **`native_decide` carries the tape.** The 46-permutation evaluations are compiled, not kernel,
   and say so via `#assert_compiled`. `decide` on a 255-bit 55-round permutation is what
   `PastaPoseidon` measured as overflowing the proof-term path.
3. **This is one stage of six.** The five MSM stages of a Wrap verification need curve arithmetic
   that is not programmed; `v′` and `u′` are consumed by them and this file does not consume them.
4. **The endomorphism lift is not here.** `v′ ↦ v` and `u′ ↦ u` are `ScalarChallenge::to_field`;
   the block's `endo_r` is in the fixture and the lift is `PicklesRecursion`'s, not this file's.
-/

#assert_axioms wrap_tape2_shape
#assert_axioms the_absorb_program_permutes_the_absorbed_state
#assert_axioms the_general_theorem_subsumes_the_fresh_one
#assert_axioms linkTrace_is_the_program_run
#assert_axioms the_link_output_is_the_permuted_absorbed_state
#assert_axioms LINK_PI_COUNT_eq
#assert_axioms linkAir_mainRailOk
#assert_axioms linkPIs_length
#assert_axioms the_link_absorbs_exactly_one_element
#assert_axioms the_permutation_opcode_split_exactly
#assert_axioms the_block_tape_costs_46_permutations

-- ⚑ COMPILER-TRUSTED, and said out loud: each is 46 Kimchi permutations of a 255-bit state.
#assert_compiled the_fq_sponge_reproduces_the_real_blocks_challenges
#assert_compiled a_tampered_tape_head_moves_both_challenges
#assert_compiled a_tampered_tape_tail_moves_both_challenges
#assert_compiled the_link_input_is_the_real_tape_prefix
#assert_compiled the_machine_squeezes_the_real_blocks_v_and_u
#assert_compiled a_tampered_absorbed_element_moves_the_machines_squeeze
#assert_compiled a_tampered_input_state_moves_the_machines_squeeze

end Dregg2.Circuit.Emit.MinaBlockFqTranscript
