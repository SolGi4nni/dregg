//! ⚑⚑⚑ **SLOT 12 WAS THREE GAPS. TWO ARE CLOSED; THIS BINARY IS WHERE THE THIRD IS READ.**
//!
//! Does openmina's own `MessagesForNextStepProof::hash()` reproduce segment D's squeeze when it is
//! handed segment D's OWN preimage — 56 index coordinates, `N_HM_APP = 2` app-state words, **ONE**
//! `[Gx; Gy]`, `bRounds = 16` lifts?
//!
//! **It does, to the digit.** So there is no SPONGE gap at slot 12 and never was: this tree's model
//! of `hash_messages_for_next_step_proof` and Mina's own hasher agree on the same preimage. What
//! disagreed is what each side FILLS that preimage with, and upstream settles the shape three times:
//!
//!   * `step.rs:2848-2857` — `MessagesForNextStepProof { app_state: Rc::clone(&app_state), …,
//!     challenge_polynomial_commitments: prevs.iter().map(|v| … .sg).collect(),
//!     old_bulletproof_challenges: bulletproof_challenges }`. **The real app state**, and **one
//!     entry per `verify_one`, unpadded** — while the SAME function pads `unfinalized_proofs` and
//!     `messages_for_next_wrap_proof` to 2 explicitly (`:2764-2772`, `:2861-2868`). The omission
//!     here is deliberate.
//!   * `verification.rs:438-454` — `app_state: _, // unused`. The wire's `()` is ERASED and the
//!     caller's real app state substituted. `gates::gate_c`'s `app_state: &()` therefore drops two
//!     fields Mina would have hashed.
//!   * `wrap.rs:658-666` — `actual_proofs_verified = <the record>.old_bulletproof_challenges.len()`,
//!     and `:729-737` pads that record to `MAX_PROOFS_VERIFIED_N` with `dummy_ipa_wrap_sg()` for
//!     the WRAP proof's own recursion slots. The record's arity DEFINES the count; it is not 2 by
//!     construction, and `step.rs:2676-2679` says so outright (2 for block/merge, **1 for zkapp
//!     with proof authorization, 0 otherwise**).
//!
//! ⚑ **THE INDEX GAP THAT RAN THE OTHER WAY IS CLOSED (2026-08-07).** `step.rs:2718` —
//! `let dlog_plonk_index = w.exists(merge::dlog_plonk_index(wrap_prover))` — makes the OUTER hash's
//! index **the instance's own wrap verification key**, while each `expand_proof` gets the previous
//! branch's (`:2725,2734`). Segment D absorbed `MinaStepPrevCommitments.INDEX_XY` — Mina devnet
//! block 539508's wrap key, right for segment C and wrong for segment D — because `hmOutSpec` was a
//! `Sponge.copy` off segment C's post-index state. It now absorbs its own 56 coordinates out of
//! `MinaWrapOwnVerifierKey`, which is what [`wrap_own_index_words`] reads, and the step circuit
//! grew 10 349 → 10 715 rows for them (still inside `2 ^ 14`).
//!
//! ⚠ **AND THE ARITY IS CLOSED TOO**, in `marshal::STEP_RECURSION_SLOTS`: `prove_step` folds ONE
//! Tick recursion challenge and `gate_c` reports `MATCH=true`.
//!
//! ⚠⚠ **WHAT IS STILL OPEN, AND THIS PROBE IS WHERE TO READ IT.** The two sides now agree on the
//! index, on the app state and on the ARITY, and they still differ on WHICH VALUES fill the one
//! remaining slot. Segment D absorbs the step assembly's own `G` (`solveG`'s output, `§19`) and its
//! own sixteen `to_field_checked` lifts; the wire record the extractor marshals carries the WRAP
//! proof's recursion-slot commitment and the STEP proof's own recursion prechallenges. Those are
//! different numbers, so `gate_c`'s digest and this file's digest are different — and the control
//! at the bottom is what shows the difference is exactly those two fields and nothing else.
//!
//! RUN: `cargo run --release --bin segd_slot12_probe` (from this crate).

use ark_ff::{BigInteger256, PrimeField};
use ledger::proofs::public_input::messages::MessagesForNextStepProof;
use ledger::proofs::transaction::{make_group, InnerCurve, PlonkVerificationKeyEvals};
use mina_curves::pasta::Fp;
use std::str::FromStr;

fn f(s: &str) -> Fp {
    Fp::from_str(s).unwrap()
}

/// ⚑ **THE STEP STATEMENT'S PUBLISHED WORD 54, READ OUT OF THE TRACKED LEAN FIXTURE — NOT COPIED
/// HERE.** `SEGD_WORDS` below IS a snapshot of the assembly's value layer, and a
/// snapshot is exactly the shape that drifts silently. (The 56 index words stopped being a snapshot
/// on 2026-08-07 — [`wrap_own_index_words`] reads them out of the tracked module.) This read is what makes the drift LOUD: the
/// digest this binary recomputes is compared against `KimchiStepWrapChainFixture.STEP_PUBLIC_IN`'s
/// entry 64 (`wrap_verifier.ml:542-548` expands packed word 54 into entry 64), so if the step
/// assembly moves and this file is not re-snapshotted, the run REFUSES instead of agreeing with its
/// own stale copy.
fn step_statement_word_54() -> Fp {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../Dregg2/Circuit/Emit/KimchiStepWrapChainFixture.lean"
    );
    let src = std::fs::read_to_string(path).expect("the installed step-statement fixture");
    let at = src
        .find("def STEP_PUBLIC_IN")
        .expect("STEP_PUBLIC_IN in the fixture");
    let open = src[at..].find('[').expect("its list literal") + at;
    let close = src[open..].find(']').expect("its closing bracket") + open;
    let entries: Vec<&str> = src[open + 1..close]
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    assert_eq!(
        entries.len(),
        67,
        "a Types.Step.Statement is 67 published entries"
    );
    f(entries[64])
}

/// ⚑⚑ **THE 56 INDEX COORDINATES, READ OUT OF THE TRACKED LEAN MODULE — NOT SNAPSHOTTED HERE.**
///
/// `MinaWrapOwnVerifierKey.INDEX_WORDS` is what `KimchiStepMainCore.idxOVal` feeds segment D, and
/// it is written by `gates::wrap_own_vk_lean` out of `vk_evals_of_wrap_index(wrap_index)` in
/// `pickles_kimchi_marshal`. Reading it here rather than pasting it makes this probe a measurement
/// OF the installed assembly: re-emit the wrap circuit without re-installing the module and the two
/// sides come apart, and this run REFUSES instead of agreeing with a stale paste.
///
/// ⚠ This file carried a 56-entry `INDEX_XY` const until 2026-08-07, and it held Mina devnet block
/// 539508's `wrap-transaction` key — segment C's index, which is what segment D absorbed back when
/// it was a `Sponge.copy` of segment C.
fn wrap_own_index_words() -> Vec<Fp> {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../Dregg2/Circuit/Emit/MinaWrapOwnVerifierKey.lean"
    );
    let src = std::fs::read_to_string(path).expect("the installed wrap-own-vk module");
    let at = src
        .find("def INDEX_WORDS")
        .expect("INDEX_WORDS in MinaWrapOwnVerifierKey");
    let open = src[at..].find('[').expect("its list literal") + at;
    let close = src[open..].find(']').expect("its closing bracket") + open;
    let words: Vec<Fp> = src[open + 1..close]
        .split(',')
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .map(f)
        .collect();
    assert_eq!(
        words.len(),
        56,
        "a `PlonkVerificationKeyEvals` is 28 points, i.e. 56 coordinates"
    );
    words
}

/// The PREVIOUS branch's `dlog_plonk_index`, EVALUATED — Mina devnet block 539508's
/// `wrap-transaction` key, i.e. `Dregg2.Bridge.MinaStepPrevCommitments.INDEX_WORDS`. That module
/// COMPUTES its list out of `COMBINE_XY` and `MinaWrapGroupGate.SIGMA6` rather than writing it, so
/// this cannot be a read the way [`wrap_own_index_words`] is; it is a snapshot of a THIRD PARTY'S
/// key at a named block, which is the one kind of constant that does not drift under us.
///
/// It is here only as CONTROL 2's input: segment D must NOT hash under it. It is what segment D DID
/// hash under until 2026-08-07, when `hmOutSpec` was a `Sponge.copy` off segment C.
fn prev_branch_index_words() -> Vec<Fp> {
    let w: Vec<Fp> = PREV_BRANCH_INDEX_XY.iter().map(|t| f(t)).collect();
    assert_eq!(w.len(), 56, "28 points, 56 coordinates");
    w
}

fn main() {
    // ── the 56 index coordinates, in `to_fields` order: sigma[0..7], coefficients[0..15],
    //    generic, psm, complete_add, mul, emul, endomul_scalar ──
    let idx: Vec<Fp> = wrap_own_index_words();
    let pt = |k: usize| InnerCurve::<Fp>::of_affine(make_group(idx[2 * k], idx[2 * k + 1]));
    let vk = PlonkVerificationKeyEvals::<Fp> {
        sigma: std::array::from_fn(pt),
        coefficients: std::array::from_fn(|i| pt(7 + i)),
        generic: pt(22),
        psm: pt(23),
        complete_add: pt(24),
        mul: pt(25),
        emul: pt(26),
        endomul_scalar: pt(27),
    };

    // ── segment D's own twenty words ──
    let segd: Vec<Fp> = SEGD_WORDS.iter().map(|s| f(s)).collect();
    assert_eq!(segd.len(), 20);
    // ⚑ ONE COPY OF THE APP STATE. `gates::STEP_RULE_APP_STATE` is what `gate_c` now hands
    // `MessagesForNextStepProof::hash()`; this snapshot's first two words have to BE it, or the two
    // sides of slot 12 are about different records and this probe would be measuring neither.
    let app_state: Vec<Fp> = pickles_reality_gate_export::gates::step_rule_app_state();
    assert_eq!(
        app_state,
        segd[0..2].to_vec(),
        "`gates::STEP_RULE_APP_STATE` and this file's segment-D snapshot disagree about the step \
         rule's app state; one of them has drifted from `KimchiStepMainCore.hmOVal`"
    );
    let g = InnerCurve::<Fp>::of_affine(make_group(segd[2], segd[3]));
    let chals: [Fp; 16] = std::array::from_fn(|i| segd[4 + i]);

    let msg = MessagesForNextStepProof {
        app_state: &app_state,
        dlog_plonk_index: &vk,
        challenge_polynomial_commitments: vec![g.clone()],
        old_bulletproof_challenges: vec![chals],
    };
    let limbs = msg.hash();
    let got = Fp::from_bigint(BigInteger256::new(limbs)).unwrap();

    // ⚑ the tracked fixture is the authority; the constant below is only the snapshot's own claim
    // about itself, and the two are checked against each other before anything is reported.
    let want = step_statement_word_54();
    assert_eq!(
        want,
        f(LEAN_DIGEST),
        "the step statement's published word 54 has MOVED away from this file's snapshot of \
         segment D's preimage. Re-snapshot SEGD_WORDS from \
         `KimchiStepMainCore.hmOutSpec` (`metatheory/wip/SegDPreimage.lean` prints it) rather than \
         trusting this run."
    );
    println!("openmina hash over segment D's preimage : {got}");
    println!("segment D's own squeeze (word 54)       : {want}");
    println!("AGREE: {}", got == want);
    assert_eq!(
        got, want,
        "openmina's own MessagesForNextStepProof::hash() no longer reproduces segment D's squeeze \
         on segment D's preimage — that would be a VALUE gap, which slot 12 has never had"
    );

    // ── CONTROL 1: the shape the extractor used before 2026-08-07 — `app_state = ()`, TWO slots.
    //    Both of those are repaired now (`gates::STEP_RULE_APP_STATE`, `STEP_RECURSION_SLOTS`), so
    //    this is history rather than a live gap; it stays because a control that can no longer be
    //    reached is how a repair silently un-lands.
    let msg0 = MessagesForNextStepProof {
        app_state: &(),
        dlog_plonk_index: &vk,
        challenge_polynomial_commitments: vec![g.clone(), g.clone()],
        old_bulletproof_challenges: vec![chals, chals],
    };
    let got0 = Fp::from_bigint(BigInteger256::new(msg0.hash())).unwrap();
    println!("same preimage at the OLD arity/app-state: {got0}");
    println!("CONTROL DIFFERS: {}", got0 != want);
    assert_ne!(
        got0, want,
        "the pre-repair shape must not reproduce word 54"
    );

    // ── CONTROL 2: ⚑ THE ONE THAT IS STILL LIVE. Same index, same app state, same arity — and the
    //    previous branch's key instead of dregg's own. This is the gap segment D's own index closed,
    //    and it must still MOVE the digest, or absorbing the right key bought nothing.
    let prevk: Vec<Fp> = prev_branch_index_words();
    let ppt = |k: usize| InnerCurve::<Fp>::of_affine(make_group(prevk[2 * k], prevk[2 * k + 1]));
    let vk_prev = PlonkVerificationKeyEvals::<Fp> {
        sigma: std::array::from_fn(ppt),
        coefficients: std::array::from_fn(|i| ppt(7 + i)),
        generic: ppt(22),
        psm: ppt(23),
        complete_add: ppt(24),
        mul: ppt(25),
        emul: ppt(26),
        endomul_scalar: ppt(27),
    };
    let msg1 = MessagesForNextStepProof {
        app_state: &app_state,
        dlog_plonk_index: &vk_prev,
        challenge_polynomial_commitments: vec![g.clone()],
        old_bulletproof_challenges: vec![chals],
    };
    let got1 = Fp::from_bigint(BigInteger256::new(msg1.hash())).unwrap();
    println!("same preimage under the PREVIOUS branch's key: {got1}");
    println!("KEY IS LOAD-BEARING: {}", got1 != want);
    assert_ne!(
        got1, want,
        "segment D's squeeze did not move when the absorbed wrap key was swapped for the previous \
         branch's — then absorbing the instance's own key is not what this digest is about"
    );
}

const LEAN_DIGEST: &str =
    "6630120479152978827537802736102265787787040179311113512596700137082353666021";

const SEGD_WORDS: [&str; 20] = [
    "23",
    "5000045",
    "13980990493653343887188526224845534277666530181182894119531706342730520353090",
    "3636427260763282242334456773748705380410960294066724261519117101369630051985",
    "13298120385880101632804899235274912307840456423938922955120495301498316578351",
    "8289939846934432412406520811125027661192536248989393460004591507014623245264",
    "16507974886157821370057269824221505104661559035404485801216026437156308439221",
    "27823738100883696338665205954507772226288156714098199396034823606426867378183",
    "15109243972511771873639334951859416270646300267563754656784952021425825273065",
    "28602807629104320512152270339291472957438833402896700792462416494143929328731",
    "8771739828660376542060100415309829251651708038642654868530502148069788235391",
    "28266262949624795057624160564451058799024139634893106534279558981944535592462",
    "3269832453904305005710755582626600541027892870753181468807371201702754043991",
    "11815321850260030900814077744422086512760027352656156909000721250590535634561",
    "18454564914198825833517319256392459974096528596315740112963248072114624464802",
    "8084985475553426942213530696202661318624096480080839370256426413333384069149",
    "18771146088492579893966200277509600017160518037328815388276685612322619873348",
    "20706779084675423513743804157882741881502985385683518596057837639229553267807",
    "11623982426494355638488915775810588712956849699317926839873682325885675195747",
    "23100719878972830622576231631500939470045160573100007690092904626774477171434",
];

/// Mina devnet block 539508's `wrap-transaction` verification key, 56 coordinates. See
/// [`prev_branch_index_words`].
const PREV_BRANCH_INDEX_XY: [&str; 56] = [
    "10238517694385979400441067096422230638797003193155225134939062071676615297964",
    "3900210177105842176653843375981629413475496388856003483451534127124171623991",
    "15745569438365094165820543421253218295900016638241048359684559871986848996300",
    "22464607937190784244764989161879410897924893574994295722141162970704138921684",
    "1348810928739486739550565580977632677189634152439878210885155462708474268139",
    "21909548691958096430140910202097691643019658230610581755067301416225068831101",
    "7162949178191457163330541908341973291353419054359843509870622177186154831109",
    "28251733110730332090087383815976602648219818115081659013706571196678057838606",
    "14828479449944575961876792004758925054348372899995888067442819198428246388139",
    "25611501809232636111767340003539510947477274670250905801777345176045700782203",
    "8743318142348947557626461239892801571835016752674911973903408971652722769361",
    "17169127825548115406432078625029683985045882054108087967646003545701384822997",
    "14533069567859997931411338798235390554646264745565930216225706045991714547029",
    "230076843026232836139391506383317233661567084986689891555547340509935178276",
    "17604975070393268522741884040314934259857325626778301999113489011159580765364",
    "17038202213383175764498908207865223931558897286427890188578695361555563473773",
    "3629213040537781701150823170145380192583936597459527369785224168714974501154",
    "8967498922905016531705096735466268931827878423034496453575837306125485943592",
    "26629970381965241897282560250933008696433594742695899977030242829782513135375",
    "9739183580260344617466979875346260310769325103327953257156394960775266554566",
    "27951503287423751919712121095792104915117737379594415816405228985740763378230",
    "16859977354613052254445941772213940998400671999100803159807414487565853509402",
    "24564626843488319919500904353351783519278685431443895532004759612756541167124",
    "6894717885193921115746283271411840268874481546230145946078422154586646993790",
    "21097804363354425878220962894775119920206121345704028932119438848871264424680",
    "22183198279623402680222102419263275324196163927923119890371040246232456607676",
    "28133329390722676823609700606655986836956419495821107970810258390695099502881",
    "1959036676278517161890138452385797121793525561906778075243702699983729666862",
    "12160866745240813956716089835359244952231316345615235096984889044149071065034",
    "9435402212832378946561648668198360482420414240218944966090969465787264524907",
    "4553125220630386866536673088952173463994717929684098347875570662002529751583",
    "26479401893816489483181665154094527286688400684291728677451425076681205206921",
    "15242167493270380075594800822907054421648334928459578079597652483754631538534",
    "12112565980258790950711338310816680956717745728863488719502692296298919843326",
    "17816717724783781224621217114780070384305374196336428615119130460312030662710",
    "8987336457985823771915972080423303259580319582856580168594155238119763833941",
    "22773652833227420169167171502886345233490081908372707509170391777508327649539",
    "27800782081073374487918820149511719006280279339342059247076731774950404926196",
    "13322016142261673328103021151884132126539838823176318065735479485979378830990",
    "28108429549031047740384716268717266777323693987249464588150837128016978114117",
    "21653356320857381006968735007818291248602525606697163836668798436313155259567",
    "14973083266869769883145738252765549430619775182650626026062456519446666029535",
    "5953795165810567480458521026869249512810795572323766633824559722220986191161",
    "15901911886607693013161673396738069538954749595972174355871589616905356113255",
    "24520983069735898256276925645671976288036990947174381745390989718145111659035",
    "7886722312494759881281503674899925356215530043385313314588020090486316053004",
    "4769154752149556066230820330886643270882173161025745140702742835888634479396",
    "13452803353367938068237548133967328903864891688948026343225226820305166787867",
    "13805384444512076770002989510975754788187213458051321078716086741317379509579",
    "15607277084273474338836773571403635801105736341964995465583685300893782640264",
    "28399397168984168516318441257753832010966733359830277905893072343997159553477",
    "25449667763879462852100978128524499066487315609880734458875244513989285430921",
    "7815551422170048242546256550860518974557789604652241254080089687054669188281",
    "890463350541575175773277669201627422969786359695021685876185905984520754873",
    "2153859778758829261248299182898345054593593782686804112833600356728172931805",
    "713943172506841607399564506540804291592984762176494418658357787378120446532",
];
