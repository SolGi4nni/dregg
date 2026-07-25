/-
# Dregg2.Crypto.BN254.Groth16 — the deployed Groth16 verify EQUATION as a Lean predicate.

This is the object that will INSTANTIATE the abstract `verifyProof` oracle in
`Market.ProtocolAssurance` and, with knowledge-soundness, discharge `SettlementVerifier25Refines`.
It matches `chain/contracts/DreggGroth16Verifier25.sol :: verifyProof` STEP-FOR-STEP:

1. **Pedersen proof-of-knowledge gate** (gnark's committed-witness PoK), a 2-pairing check:
   `e(commit, GSigma) · e(pok, G) = 1`  (Solidity `PRECOMPILE_VERIFY` over the pairs
   `(commit, PEDERSEN_GSIGMA)`, `(pok, PEDERSEN_G)`).
2. **Public-input MSM**: `L = CONSTANT + commit + Σ_{i<25} input_i · PUB_i + pubCommit · PUB_25`,
   where `pubCommit = keccak(commit ‖ …) mod r` is the hash-to-field of the Pedersen commitment
   (matching `publicInputMSM` + the `publicCommitments[0]` term).
3. **Groth16 4-pairing gate**:
   `e(A, B) · e(C, −δ) · e(α, −β) · e(L, −γ) = 1`
   (Solidity feeds `A,B` then the pre-negated constants `DELTA_NEG`, `BETA_NEG`, `GAMMA_NEG`, so we
   store `δ,β,γ` already negated — byte-for-byte the deployed layout).

The verification key `vk25` below carries the ACTUAL deployed constants; the KATs check every VK
point lies on its curve (`α, CONSTANT, PUB_*` on `E/Fq`; `β,γ,δ,G,GSigma` on the twist `E'/Fp2`) —
so this is not a re-authored VK but the deployed one, tied by ground-truth arithmetic.  The public
inputs are `Fr = ZMod rBN254` — the SAME scalar field the wrapped-R1CS gadgets in
`Dregg2.Circuit.R1csFr` arithmetize over, so the circuit and its verifier meet on one field.

House law #1: this is Lean-authored math; the pairing it calls is the Lean `pairing` of `Pairing.lean`.
-/
import Dregg2.Crypto.BN254.Pairing
import Dregg2.Circuit.R1csFr

namespace Dregg2.Crypto.BN254

open Dregg2.Circuit.R1csFr (Fr)

set_option autoImplicit false

/-! ## §1 G2 negation (computable) and the VK / proof structures. -/

/-- G2 point negation `(x, y) ↦ (x, −y)` — computable, curve-preserving (used to relate the stored
`−δ,−β,−γ` to `δ,β,γ`; here we store the negatives directly, matching Solidity). -/
def negG2 (Q : G2Aff) : G2Aff := ⟨Q.x, -Q.y⟩

/-- The deployed 25-lane verifying key.  `betaNeg/gammaNeg/deltaNeg` are stored ALREADY NEGATED
(the Solidity `*_NEG_*` constants); `pub : Fin 26 → G1Aff` are `PUB_0 … PUB_25`. -/
structure VerifyingKey25 where
  alpha : G1Aff
  betaNeg : G2Aff
  gammaNeg : G2Aff
  deltaNeg : G2Aff
  pedG : G2Aff
  pedGSigma : G2Aff
  constIC : G1Aff
  pub : Fin 26 → G1Aff

/-- A Groth16 proof for the deployed wrapper: the three Groth16 points plus the gnark Pedersen
commitment and its proof-of-knowledge. -/
structure Proof25 where
  A : G1Aff
  B : G2Aff
  C : G1Aff
  commit : G1Aff
  pok : G1Aff

/-! ## §2 The verify predicate — parametrized by the G1 group ops (ECADD / ECMUL).

The MSM uses G1 addition and Fr-scalar-multiplication.  Deployed, these are the `PRECOMPILE_ADD` /
`PRECOMPILE_MUL` (`alt_bn128` `ECADD`/`ECMUL`); in Lean their carrier is Mathlib's
`WeierstrassCurve.Affine.Point` `AddCommGroup` (available under the field seam
`[Fact (Nat.Prime pBN254)]`).  We take them as explicit parameters so the EQUATION is stated exactly,
and the group-law discharge is a named brick, not baked in. -/

variable (addG1 : G1Aff → G1Aff → G1Aff) (smulG1 : Fr → G1Aff → G1Aff)

/-- The public-input multi-scalar-multiplication `L` (matches `publicInputMSM`):
`CONSTANT + commit + Σ_{i<25} input_i·PUB_i + pubCommit·PUB_25`. -/
def publicInputMSM (vk : VerifyingKey25) (commit : G1Aff)
    (input : Fin 25 → Fr) (pubCommit : Fr) : G1Aff :=
  let base := addG1 vk.constIC commit
  let withInputs :=
    (List.finRange 25).foldl
      (fun acc i => addG1 acc (smulG1 (input i) (vk.pub i.castSucc))) base
  addG1 withInputs (smulG1 pubCommit (vk.pub (Fin.last 25)))

/-- **The deployed Groth16 acceptance predicate.**  Conjunction of the Pedersen PoK 2-pairing gate
and the Groth16 4-pairing gate over the Lean `pairing`. -/
def groth16Accept (vk : VerifyingKey25) (pf : Proof25)
    (input : Fin 25 → Fr) (pubCommit : Fr) : Prop :=
  -- (1) Pedersen proof-of-knowledge gate.
  (pairing pf.commit vk.pedGSigma * pairing pf.pok vk.pedG = 1)
  ∧
  -- (2+3) MSM then the Groth16 4-pairing gate.
  (let L := publicInputMSM addG1 smulG1 vk pf.commit input pubCommit
   pairing pf.A pf.B * pairing pf.C vk.deltaNeg
     * pairing vk.alpha vk.betaNeg * pairing L vk.gammaNeg = 1)

/-! ## §3 The deployed verification key (the ACTUAL constants from DreggGroth16Verifier25.sol). -/

/-- The 26 public-input base points `PUB_0 … PUB_25` (deployed constants, coords `⟨X, Y⟩`). -/
def pubList : List G1Aff :=
  [ ⟨13166436972134405837473708910690171824590235426750105421790020904855932116502,
     9833526814774131442195139301111156188236350007793204273737712320422803796284⟩,
    ⟨1108081866668005630402350987423263544571037689523417357050922601326192200463,
     7217323957786452550797206247469125455030155953462345748585556918366795028061⟩,
    ⟨17039230888717837083094027107555383007537231975840979327662559290945607929852,
     16000324461926287436839565908222988460698408175664965751734967336208886578218⟩,
    ⟨16372494365656483002825364539799471530512804297725353697246693210311933283126,
     1242382141626955414707540062072739156148282931926744945219007262154094626920⟩,
    ⟨4053471697291383770278137527880950399769849907754420734075799375120469979881,
     15517359064005809730257314343501327927704286814287537108327476246130990601213⟩,
    ⟨13368489423264280722122808932040099941587171749927983413707948393098989205302,
     2988441659604953735764212345715442666493782886792160301754470233210632275329⟩,
    ⟨14020047391385080965001691348952707897134319672027484170070848289889485392376,
     16386291405613506283348920375155794683440695147595174504099209929923594790285⟩,
    ⟨19651293915120069849861139370762507185866189742626176540998285689425315960377,
     20717286581041304880867343173613827590422948210859464654239397760301802715819⟩,
    ⟨21367116029342960301213243856950947530553257254088836496934801303792991148590,
     12623238421189368949756707502014109694120131484139720087658490168432191794004⟩,
    ⟨11090282832531623741325223605792486410809452681296354326358813137542676075017,
     2353105836701112903342601082433206143300366883634190574541751875310875045642⟩,
    ⟨4194432299269502324710450975325654286803314639719399136717721897549601912133,
     284041581908672570999504164824843822415582090941203589049454273776947933122⟩,
    ⟨8935013016588295466376851027768798857373283201998093155161977637228391728229,
     20384389182116680545620540767214658186927454649242035950222396760258703368766⟩,
    ⟨19684425500093052294751885928000733934815893347253551296692970951594683081684,
     2286216875411815938931354632354982991639982316705272414073001607689142528880⟩,
    ⟨17460989753426354456303872430404707770496211331091968691522680917779689719402,
     12725784536655328477580475954842939349945696655575569743884196962232977194206⟩,
    ⟨14874406841959474553471087562462027746703153292223091976874963557182528441383,
     1311716599771232068242919702012599591704933892542590083936465676092503865296⟩,
    ⟨11741130682347121185152218386051511138664839613945826787238510548951490803438,
     13764182816583697392960213753094095960456831254335919451119128190208767114762⟩,
    ⟨6761173660748841802154992371094681530909368754988435700290181031525083089871,
     19210518374369941518815328345294183698872815894940015428379314178562536881040⟩,
    ⟨17997844196174891532900137386766507442930422059163134919329616436867007331950,
     851976965230870014827892523024906586177753582226924690841745584988600188540⟩,
    ⟨11879441266068667213616269904614757531104087406501943773070128924009359502988,
     13687530871177301540947378742874668630121716220177426626273252369488158713212⟩,
    ⟨14224638824691047602859497962849645000519881015356807936538032735800494536708,
     14229796463029546602037506529056446904942700438017896319141966172955065537362⟩,
    ⟨19324031304467778658496463456554714210644966612381666111407965449057161838328,
     4221999373547316459644818495541104584495648810026441328679573214320764683930⟩,
    ⟨1231004293649417137800545181245372939355950033642826482058934901221130499597,
     19974026542898583336847184638175769014587258369235170810554881537415017196447⟩,
    ⟨921055842579251466143839625633818970422641994343429795147029386328494758367,
     3162236491179949285987540548606684847024494104716930029377632076314196059937⟩,
    ⟨8051894549505747314563322588774557825497937066817618610938685332551006059174,
     3043010977460768858360547048510185918418874601848300804660271975800668218214⟩,
    ⟨7848740768819107881428772432944602305649575542618623168740111172258607263264,
     15992344112717850503777272578835276587653470511632101745260487698728098941499⟩,
    ⟨7851125206963537960366673390796083353732755347791881668227649891986410018523,
     3096611908419292553298124677577482312098136944522856714126318585734291355155⟩ ]

/-- The deployed 25-lane verifying key (`DreggGroth16Verifier25.sol` constants). -/
def vk25 : VerifyingKey25 where
  alpha := ⟨15209444214440235001497022803899506217275852229402859607686962191434917642572,
            1091755402984342610088655190734135721186867525659407867470308178820439766949⟩
  betaNeg := ⟨⟨11395472108698723996803407492865864718754151120479587304461691562011982893142,
               3243254179175403195609745536112098997269772186789571806854896686080274266374⟩,
              ⟨1259382906897478740872080785675893097097269424690521544376754622098215026377,
               6520810524982860063719325620439402964082088444041887629090836443894817680010⟩⟩
  gammaNeg := ⟨⟨1288164266865020764375503006344826796021197074002415380245559633684942894213,
                10464157757004265227457199731666733604245957797743189563643530275922370318662⟩,
               ⟨5965263104300816949521265631825307774492358618826924250316812752070742238941,
                16556411267806895471518723945470149238477670053886079859952901074906168745454⟩⟩
  deltaNeg := ⟨⟨17314451162115111991917720589218329688241187980246286996085152544275260356045,
                19566450740185756979283374402904273630371464587733862879502184922826039703389⟩,
               ⟨21577205425954588298287989209292243883490202642175266628510229282365983152185,
                8463008961692897856635208640708231823479661657216940008715801137424180558812⟩⟩
  pedG := ⟨⟨3189894578709697486602576983688453346995707255213710128090632887792894813894,
            3273169252337667368459401106413530680040500540929255870942551019463198518517⟩,
           ⟨21321684663066370055064100153828659553695199342381689665083939315268712648764,
            14788331201071208232853500169336869448924605361165970308056900960193040756810⟩⟩
  pedGSigma := ⟨⟨16190009397896497543260171627884270543422244138847106855151958082516588010561,
                 2093810357996412624890873062920708677733201121310372709322865193996294221458⟩,
                ⟨1323250568051741821431329247872991974080047497092275839254247405587268400817,
                 18038320268595940582909906874758271739681542157584117647558171835148132578289⟩⟩
  constIC := ⟨5152971939803875179778655179180428678773811055551906673714207965335463550300,
              13352564913843099952936515822851099986383475419359114164826460984070653442255⟩
  pub := fun i => pubList.getD i.val ⟨0, 0⟩

/-! ## §4 KATs — every deployed VK point is on its curve (ground-truth, not a re-authoring). -/

-- α, CONSTANT on `E/Fq`.
#guard OnCurveG1 vk25.alpha.x vk25.alpha.y
#guard OnCurveG1 vk25.constIC.x vk25.constIC.y
-- −β, −γ, −δ, G, GSigma on the twist `E'/Fp2` (negation preserves the curve, so the stored
-- negatives are on-curve iff the originals are).
#guard OnCurveG2 vk25.betaNeg.x vk25.betaNeg.y
#guard OnCurveG2 vk25.gammaNeg.x vk25.gammaNeg.y
#guard OnCurveG2 vk25.deltaNeg.x vk25.deltaNeg.y
#guard OnCurveG2 vk25.pedG.x vk25.pedG.y
#guard OnCurveG2 vk25.pedGSigma.x vk25.pedGSigma.y
-- ALL 26 public-input base points `PUB_0 … PUB_25` lie on `E/Fq` (one check over the whole list).
#guard pubList.all (fun p => decide (OnCurveG1 p.x p.y))
#guard pubList.length = 26

/-! ## §5 The bridge to `SettlementVerifier25Refines` (the plan — what instantiates the oracle).

`Market.ProtocolAssurance.SettlementVerifier25Refines` (`ProtocolAssurance.lean:872`) is
    `∀ proofBytes pub, settlementVerifierAccept verifyProof proofBytes pub = true →`
    `  ∃ c : DrexClearing, stateLanes c.pre = pub.genesisRoot ∧ stateLanes c.post = pub.finalRoot`
    `                      ∧ c.nodes.length = pub.numTurns`
with `verifyProof : List Nat → List Nat → Bool` an ABSTRACT oracle and `pub.toInputs` the exact
25-lane public input (`genesis[0..8) ++ final[8..16) ++ [numTurns] ++ chainDigest[17..25)`).

**How THIS model instantiates the oracle** (the ordered discharge plan):

1. **Decode + evaluate.**  Define `verifyProof := fun proofBytes inputs =>`
   `decodeProof proofBytes` (parse `Proof25` from the EIP-197 byte layout) `matched with`
   `decodeInputs inputs` (the 25 `Nat` lanes → `Fin 25 → Fr` by `(·) mod r`; each lane `< babyBearP`
   `< r`, so the reduction is the identity — a small proven lemma), computing
   `pubCommit = keccak(commit ‖ …) mod r`, and returning the DECIDABLE `groth16Accept … = 1`.
   This makes `settlementVerifierAccept verifyProof` the deployed accept path over the Lean `pairing`.

2. **Groth16 knowledge-soundness (THE floor).**  `groth16Accept (vk25) pf input pubCommit`  ⟹
   ∃ a witness `w` satisfying the WRAPPED R1CS relation `R25`, i.e. the object modeled by
   `Dregg2.Circuit.R1csFr` (`gHolds`) whose public inputs are exactly `input`.  This is the
   knowledge-soundness of Groth16 over BN254 — the genuine cryptographic FLOOR, provable from
   (a) `pairing` bilinearity + non-degeneracy (the named goals in `Pairing.lean`) and (b) the
   `q`-type / AGM assumption Groth16's extractor rests on.  This is the piece that is NOT free and
   is the multi-day theorem this whole tower sets up; it is stated at that resolution, not faked.

3. **Circuit meaning → clearing.**  A satisfying `R25` witness whose public inputs decode the
   eight-lane `genesisRoot/finalRoot` and `numTurns` yields, via the already-landed shielded-ring
   apex extraction (`ProtocolAssurance.shieldedRingApexStep_of_accept` +
   `starkMarketClaimExtraction_of_shielded_descriptor`), a `DrexClearing` with
   `stateLanes c.pre = genesisRoot`, `stateLanes c.post = finalRoot`, `c.nodes.length = numTurns`.
   The `stateLanes` codec is the deployed eight-lane state commitment (`Lane8`), matched to the
   circuit's public-input encoding — a faithful-codec obligation already NAMED in ProtocolAssurance.

**Provable NOW vs the KS floor.**  Provable now (foundation, this session): the field tower is a
`CommRing` tower kernel-clean; the curves + deployed VK points are on-curve (KATs); the pairing and
the verify EQUATION are DEFINED and match the deployed contract step-for-step; the Jacobian point
steps are validated on-curve.  The KS floor (step 2) + bilinearity/non-degeneracy (Pairing §6) +
the byte-decode lemmas (step 1) + the codec faithfulness (step 3) are the ordered remaining work.
The intended instantiation site is exactly this file's `groth16Accept`/`vk25`. -/

end Dregg2.Crypto.BN254
