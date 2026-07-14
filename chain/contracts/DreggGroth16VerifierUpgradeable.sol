// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IGroth16Verifier25} from "./IGroth16Verifier25.sol";
import {IGroth16VerifierRegistry} from "./IGroth16VerifierRegistry.sol";

/// UPGRADEABLE-VK Groth16(BN254) verifier for the dregg 25-lane settlement
/// statement, with a VK-EPOCH REGISTRY.
///
/// ── WHAT THIS IS ────────────────────────────────────────────────────────
/// The gnark-GENERATED verifier (`DreggGroth16Verifier25.sol`) hard-codes the
/// verifying key (α in G1; β, γ, δ in G2, stored NEGATED; the Pedersen
/// commitment key G, Gσ in G2; and the 27 IC points = the constant + 26
/// public-input bases) as Solidity CONSTANTS. Every VK epoch (a GAP-flip, the
/// nullifier flip, a re-genesis) therefore forces a redeploy of the verifier
/// AND — because `DreggSettlement` pins the verifier at construction — the
/// settlement contract too.
///
/// This contract moves the VK into STORAGE, keyed by a `uint256 epoch`:
///   * `mapping(uint256 => VerifyingKey) _vks`  — the VK per epoch,
///   * `currentEpoch`                            — the pointer a fresh proof
///                                                 targets,
///   * `advanceEpoch(newVk)`                     — write the NEXT epoch's VK
///                                                 and bump the pointer (ONE tx).
/// A proof is checked against the epoch it targets, so proofs minted under an
/// old VK stay verifiable at their epoch after a flip; already-settled roots
/// (recorded permanently by `DreggSettlement`) are unaffected either way.
///
/// The pairing MATH is byte-identical to the generated verifier — the same
/// commitment proof-of-knowledge gate, the same public-input MSM, and the
/// same final equation
///     e(A, B) · e(C, −δ) · e(α, −β) · e(L, −γ) == 1
/// — reproduced reading the VK from STORAGE instead of from code constants.
/// Epoch 0 is seeded (in the constructor) with the LIVE deployed VK, copied
/// byte-for-byte from `DreggGroth16Verifier25.sol`, so the current live proof
/// still verifies unchanged.
///
/// ── THE GATE (load-bearing security) ────────────────────────────────────
/// A MUTABLE VK is a security control: a malicious setter can install a VK
/// that accepts any proof (a forged one over any statement). `advanceEpoch` /
/// `setVerifyingKey` are therefore `onlyOwner`. This adds NO new trust over
/// the status quo — today the deployer already chooses the baked-in VK by
/// deploying the generated verifier — it simply names the setter and makes it
/// swappable.
///
///   * PRIVATE / TESTNET: `onlyOwner` (this contract) is sufficient — the
///     owner is the operator who would have redeployed anyway.
///   * PUBLIC / MAINNET: the owner MUST be a GOVERNANCE contract behind a
///     TIMELOCK (e.g. an OpenZeppelin `TimelockController` owned by a
///     multisig / token governor). A mutable VK with an EOA owner is an
///     accept-anything backdoor; the timelock is what makes a flip observable
///     and vetoable before it takes effect. This is documented as the deploy
///     requirement for any public instance — see
///     `docs/deos/UPGRADEABLE-VK-REGISTRY.md`.
///
/// The owner gate is the ONLY thing standing between the registry and a
/// forged-VK acceptance, so it is a real modifier, tested in both polarities.
contract DreggGroth16VerifierUpgradeable is IGroth16VerifierRegistry {
    // ── BN254 field / scalar orders (same as the generated verifier) ──────
    /// Base field order P.
    uint256 internal constant P =
        0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47;
    /// Scalar field order R. Public inputs must be < R (canonical residue).
    uint256 internal constant R =
        0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

    // Precompile addresses.
    uint256 internal constant PRECOMPILE_ADD = 0x06;
    uint256 internal constant PRECOMPILE_MUL = 0x07;
    uint256 internal constant PRECOMPILE_VERIFY = 0x08;

    /// A G1 point (affine). Coordinates in Fp.
    struct G1Point {
        uint256 x;
        uint256 y;
    }

    /// A G2 point (affine) over Fp2 = Fp[i]/(i²+1), coordinates written as the
    /// pair (c0, c1) meaning c0 + c1·i — matching the generated verifier's
    /// `_X_0`/`_X_1` constant naming. β, γ, δ are stored NEGATED (exactly the
    /// values gnark's `ExportSolidity` bakes in); G, Gσ are stored as-is.
    struct G2Point {
        uint256 x0;
        uint256 x1;
        uint256 y0;
        uint256 y1;
    }

    /// A full verifying key. `ic` has 27 entries: `ic[0]` is the constant term
    /// and `ic[1..26]` are the 26 public-input bases (25 statement lanes + 1
    /// Pedersen-commitment public input).
    struct VerifyingKey {
        G1Point alpha;
        G2Point betaNeg;
        G2Point gammaNeg;
        G2Point deltaNeg;
        G2Point pedersenG;
        G2Point pedersenGSigma;
        G1Point[27] ic;
    }

    // ── registry state ────────────────────────────────────────────────────
    address public owner;
    uint256 public currentEpoch;
    mapping(uint256 => VerifyingKey) private _vks;
    mapping(uint256 => bool) private _vkSet;

    error NotOwner(address caller);
    error ZeroOwner();
    error MalformedVerifyingKey(string reason);
    error EpochAlreadySet(uint256 epoch);

    event OwnershipTransferred(address indexed from, address indexed to);
    event EpochAdvanced(uint256 indexed epoch, address indexed by);
    event VerifyingKeySet(uint256 indexed epoch, address indexed by);

    modifier onlyOwner() {
        if (msg.sender != owner) revert NotOwner(msg.sender);
        _;
    }

    /// Seeds epoch 0 with the LIVE deployed VK (byte-identical to
    /// `DreggGroth16Verifier25.sol`) and installs the deployer as owner. The
    /// seed is validated (in-field + G1 on-curve), so a transcription slip
    /// reverts the deploy rather than shipping a silently-wrong VK.
    constructor() {
        owner = msg.sender;
        emit OwnershipTransferred(address(0), msg.sender);

        VerifyingKey memory vk = _epoch0VK();
        _validate(vk);
        _store(0, vk);
        _vkSet[0] = true;
        currentEpoch = 0;
        emit VerifyingKeySet(0, msg.sender);
    }

    // ── ownership ─────────────────────────────────────────────────────────
    function transferOwnership(address to) external onlyOwner {
        if (to == address(0)) revert ZeroOwner();
        emit OwnershipTransferred(owner, to);
        owner = to;
    }

    // ── epoch administration (THE GATE) ───────────────────────────────────

    /// Write the NEXT epoch's VK and bump the current-epoch pointer. This is
    /// the whole VK-epoch flip: one transaction, no redeploy. `onlyOwner`;
    /// for a public instance the owner MUST be governance + timelock.
    function advanceEpoch(VerifyingKey calldata newVk)
        external
        onlyOwner
        returns (uint256 epoch)
    {
        _validate(newVk);
        epoch = currentEpoch + 1;
        if (_vkSet[epoch]) revert EpochAlreadySet(epoch);
        _store(epoch, newVk);
        _vkSet[epoch] = true;
        currentEpoch = epoch;
        emit EpochAdvanced(epoch, msg.sender);
        emit VerifyingKeySet(epoch, msg.sender);
    }

    /// Write a VK for a specific epoch WITHOUT moving the pointer (seeding a
    /// not-yet-current epoch, or correcting one before it goes live). Refuses
    /// to overwrite an already-set epoch — mutating a live epoch's VK in place
    /// would silently invalidate/forge everything proven under it. `onlyOwner`.
    function setVerifyingKey(uint256 epoch, VerifyingKey calldata vk)
        external
        onlyOwner
    {
        if (_vkSet[epoch]) revert EpochAlreadySet(epoch);
        _validate(vk);
        _store(epoch, vk);
        _vkSet[epoch] = true;
        emit VerifyingKeySet(epoch, msg.sender);
    }

    function isEpochSet(uint256 epoch) external view returns (bool) {
        return _vkSet[epoch];
    }

    /// Read back an epoch's stored VK (e.g. to copy, perturb, or re-install).
    function getVerifyingKey(uint256 epoch)
        external
        view
        returns (VerifyingKey memory)
    {
        return _vks[epoch];
    }

    // ── verification ──────────────────────────────────────────────────────

    /// `IGroth16Verifier25` drop-in: verify against the CURRENT epoch's VK.
    function verifyProof(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint256[25] calldata publicInputs
    ) external view returns (bool) {
        return _verify(currentEpoch, a, b, c, commitments, commitmentPok, publicInputs);
    }

    /// Verify against a TARGETED epoch's VK (old epochs stay verifiable).
    function verifyProofAtEpoch(
        uint256 epoch,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint256[25] calldata publicInputs
    ) external view returns (bool) {
        return _verify(epoch, a, b, c, commitments, commitmentPok, publicInputs);
    }

    // ── the pairing (byte-identical math over the STORAGE VK) ──────────────

    function _verify(
        uint256 epoch,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint256[25] calldata input
    ) internal view returns (bool) {
        if (!_vkSet[epoch]) return false;
        VerifyingKey storage vk = _vks[epoch];

        // HashToField for the committed public input, exactly as the generated
        // verifier: keccak over the packed commitment point (the
        // `publicAndCommitmentCommitted` list is empty for this circuit, so it
        // contributes no bytes), reduced mod R.
        uint256 pubCommit = uint256(
            keccak256(abi.encodePacked(commitments[0], commitments[1]))
        ) % R;

        // Pedersen commitment proof-of-knowledge gate:
        //   e(commitment, Gσ) · e(pok, G) == 1.
        if (!_checkPedersen(vk, commitments, commitmentPok)) return false;

        // Public-input linear combination L (the MSM), then the final pairing.
        (uint256 lx, uint256 ly, bool okMsm) = _msm(vk, input, pubCommit, commitments);
        if (!okMsm) return false;

        return _checkPairing(vk, a, b, c, lx, ly);
    }

    /// e(commitment, Gσ) · e(pok, G) == 1. G2 words go in EIP-197 order
    /// (imaginary coordinate first), matching the generated verifier.
    function _checkPedersen(
        VerifyingKey storage vk,
        uint256[2] calldata commitments,
        uint256[2] calldata pok
    ) internal view returns (bool) {
        uint256[12] memory p;
        p[0] = commitments[0];
        p[1] = commitments[1];
        p[2] = vk.pedersenGSigma.x1;
        p[3] = vk.pedersenGSigma.x0;
        p[4] = vk.pedersenGSigma.y1;
        p[5] = vk.pedersenGSigma.y0;
        p[6] = pok[0];
        p[7] = pok[1];
        p[8] = vk.pedersenG.x1;
        p[9] = vk.pedersenG.x0;
        p[10] = vk.pedersenG.y1;
        p[11] = vk.pedersenG.y0;

        uint256[1] memory out;
        bool ok;
        assembly ("memory-safe") {
            ok := staticcall(gas(), PRECOMPILE_VERIFY, p, 0x180, out, 0x20)
        }
        return ok && out[0] == 1;
    }

    /// L = IC[0] + commitment + Σ_{i<25} input[i]·IC[i+1] + pubCommit·IC[26].
    /// (The gnark commitment adds the raw commitment point into the constant
    /// term, exactly as `publicInputMSM` in the generated verifier.)
    function _msm(
        VerifyingKey storage vk,
        uint256[25] calldata input,
        uint256 pubCommit,
        uint256[2] calldata commitments
    ) internal view returns (uint256 lx, uint256 ly, bool ok) {
        // IC[0] + commitment
        (lx, ly, ok) = _ecAdd(vk.ic[0].x, vk.ic[0].y, commitments[0], commitments[1]);
        if (!ok) return (0, 0, false);

        for (uint256 i = 0; i < 25; i++) {
            uint256 s = input[i];
            if (s >= R) return (0, 0, false); // non-canonical public input
            (uint256 mx, uint256 my, bool k1) = _ecMul(vk.ic[i + 1].x, vk.ic[i + 1].y, s);
            if (!k1) return (0, 0, false);
            (lx, ly, ok) = _ecAdd(lx, ly, mx, my);
            if (!ok) return (0, 0, false);
        }

        if (pubCommit >= R) return (0, 0, false);
        (uint256 cx, uint256 cy, bool k2) = _ecMul(vk.ic[26].x, vk.ic[26].y, pubCommit);
        if (!k2) return (0, 0, false);
        (lx, ly, ok) = _ecAdd(lx, ly, cx, cy);
    }

    /// e(A, B) · e(C, −δ) · e(α, −β) · e(L, −γ) == 1. Proof word order matches
    /// the generated verifier / adapter: A, B, C already in EIP-197 order.
    function _checkPairing(
        VerifyingKey storage vk,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256 lx,
        uint256 ly
    ) internal view returns (bool) {
        uint256[24] memory p;
        // e(A, B)
        p[0] = a[0];
        p[1] = a[1];
        p[2] = b[0][0];
        p[3] = b[0][1];
        p[4] = b[1][0];
        p[5] = b[1][1];
        // e(C, −δ)
        p[6] = c[0];
        p[7] = c[1];
        p[8] = vk.deltaNeg.x1;
        p[9] = vk.deltaNeg.x0;
        p[10] = vk.deltaNeg.y1;
        p[11] = vk.deltaNeg.y0;
        // e(α, −β)
        p[12] = vk.alpha.x;
        p[13] = vk.alpha.y;
        p[14] = vk.betaNeg.x1;
        p[15] = vk.betaNeg.x0;
        p[16] = vk.betaNeg.y1;
        p[17] = vk.betaNeg.y0;
        // e(L, −γ)
        p[18] = lx;
        p[19] = ly;
        p[20] = vk.gammaNeg.x1;
        p[21] = vk.gammaNeg.x0;
        p[22] = vk.gammaNeg.y1;
        p[23] = vk.gammaNeg.y0;

        uint256[1] memory out;
        bool ok;
        assembly ("memory-safe") {
            ok := staticcall(gas(), PRECOMPILE_VERIFY, p, 0x300, out, 0x20)
        }
        return ok && out[0] == 1;
    }

    function _ecAdd(uint256 x1, uint256 y1, uint256 x2, uint256 y2)
        internal
        view
        returns (uint256 rx, uint256 ry, bool ok)
    {
        uint256[4] memory inp = [x1, y1, x2, y2];
        assembly ("memory-safe") {
            ok := staticcall(gas(), PRECOMPILE_ADD, inp, 0x80, inp, 0x40)
            rx := mload(inp)
            ry := mload(add(inp, 0x20))
        }
    }

    function _ecMul(uint256 x, uint256 y, uint256 s)
        internal
        view
        returns (uint256 rx, uint256 ry, bool ok)
    {
        uint256[3] memory inp = [x, y, s];
        assembly ("memory-safe") {
            ok := staticcall(gas(), PRECOMPILE_MUL, inp, 0x60, inp, 0x40)
            rx := mload(inp)
            ry := mload(add(inp, 0x20))
        }
    }

    // ── VK well-formedness gate (malformed VK reverts at set time) ─────────

    /// Reject an out-of-field or off-curve VK. Every coordinate must be a
    /// reduced Fp residue (< P); every G1 point (α and the 27 IC points) must
    /// satisfy y² = x³ + 3. (G2 on-curve is left to the pairing precompile,
    /// which rejects a bad β/γ/δ/G/Gσ at verify time — fail-closed.)
    function _validate(VerifyingKey memory vk) internal pure {
        _g1(vk.alpha, "alpha");
        _g2InField(vk.betaNeg, "betaNeg");
        _g2InField(vk.gammaNeg, "gammaNeg");
        _g2InField(vk.deltaNeg, "deltaNeg");
        _g2InField(vk.pedersenG, "pedersenG");
        _g2InField(vk.pedersenGSigma, "pedersenGSigma");
        for (uint256 i = 0; i < 27; i++) {
            _g1(vk.ic[i], "ic");
        }
    }

    function _g1(G1Point memory pt, string memory tag) internal pure {
        if (pt.x >= P || pt.y >= P) revert MalformedVerifyingKey(tag);
        // y² == x³ + 3 (BN254 G1). Rejects garbage/off-curve bases.
        uint256 lhs = mulmod(pt.y, pt.y, P);
        uint256 rhs = addmod(mulmod(mulmod(pt.x, pt.x, P), pt.x, P), 3, P);
        if (lhs != rhs) revert MalformedVerifyingKey(tag);
    }

    function _g2InField(G2Point memory pt, string memory tag) internal pure {
        if (pt.x0 >= P || pt.x1 >= P || pt.y0 >= P || pt.y1 >= P) {
            revert MalformedVerifyingKey(tag);
        }
    }

    function _store(uint256 epoch, VerifyingKey memory vk) internal {
        VerifyingKey storage s = _vks[epoch];
        s.alpha = vk.alpha;
        s.betaNeg = vk.betaNeg;
        s.gammaNeg = vk.gammaNeg;
        s.deltaNeg = vk.deltaNeg;
        s.pedersenG = vk.pedersenG;
        s.pedersenGSigma = vk.pedersenGSigma;
        for (uint256 i = 0; i < 27; i++) {
            s.ic[i] = vk.ic[i];
        }
    }

    // ── epoch-0 seed: the LIVE deployed VK, byte-identical to
    //    DreggGroth16Verifier25.sol (α, β̄, γ̄, δ̄, G, Gσ, and the 27 IC points).
    function _epoch0VK() internal pure returns (VerifyingKey memory vk) {
        vk.alpha = G1Point(
            15209444214440235001497022803899506217275852229402859607686962191434917642572,
            1091755402984342610088655190734135721186867525659407867470308178820439766949
        );
        vk.betaNeg = G2Point(
            11395472108698723996803407492865864718754151120479587304461691562011982893142,
            3243254179175403195609745536112098997269772186789571806854896686080274266374,
            1259382906897478740872080785675893097097269424690521544376754622098215026377,
            6520810524982860063719325620439402964082088444041887629090836443894817680010
        );
        vk.gammaNeg = G2Point(
            1288164266865020764375503006344826796021197074002415380245559633684942894213,
            10464157757004265227457199731666733604245957797743189563643530275922370318662,
            5965263104300816949521265631825307774492358618826924250316812752070742238941,
            16556411267806895471518723945470149238477670053886079859952901074906168745454
        );
        vk.deltaNeg = G2Point(
            17314451162115111991917720589218329688241187980246286996085152544275260356045,
            19566450740185756979283374402904273630371464587733862879502184922826039703389,
            21577205425954588298287989209292243883490202642175266628510229282365983152185,
            8463008961692897856635208640708231823479661657216940008715801137424180558812
        );
        vk.pedersenG = G2Point(
            3189894578709697486602576983688453346995707255213710128090632887792894813894,
            3273169252337667368459401106413530680040500540929255870942551019463198518517,
            21321684663066370055064100153828659553695199342381689665083939315268712648764,
            14788331201071208232853500169336869448924605361165970308056900960193040756810
        );
        vk.pedersenGSigma = G2Point(
            16190009397896497543260171627884270543422244138847106855151958082516588010561,
            2093810357996412624890873062920708677733201121310372709322865193996294221458,
            1323250568051741821431329247872991974080047497092275839254247405587268400817,
            18038320268595940582909906874758271739681542157584117647558171835148132578289
        );

        // ic[0] = the constant term; ic[1..26] = PUB_0 .. PUB_25.
        vk.ic[0] = G1Point(
            5152971939803875179778655179180428678773811055551906673714207965335463550300,
            13352564913843099952936515822851099986383475419359114164826460984070653442255
        );
        vk.ic[1] = G1Point(
            13166436972134405837473708910690171824590235426750105421790020904855932116502,
            9833526814774131442195139301111156188236350007793204273737712320422803796284
        );
        vk.ic[2] = G1Point(
            1108081866668005630402350987423263544571037689523417357050922601326192200463,
            7217323957786452550797206247469125455030155953462345748585556918366795028061
        );
        vk.ic[3] = G1Point(
            17039230888717837083094027107555383007537231975840979327662559290945607929852,
            16000324461926287436839565908222988460698408175664965751734967336208886578218
        );
        vk.ic[4] = G1Point(
            16372494365656483002825364539799471530512804297725353697246693210311933283126,
            1242382141626955414707540062072739156148282931926744945219007262154094626920
        );
        vk.ic[5] = G1Point(
            4053471697291383770278137527880950399769849907754420734075799375120469979881,
            15517359064005809730257314343501327927704286814287537108327476246130990601213
        );
        vk.ic[6] = G1Point(
            13368489423264280722122808932040099941587171749927983413707948393098989205302,
            2988441659604953735764212345715442666493782886792160301754470233210632275329
        );
        vk.ic[7] = G1Point(
            14020047391385080965001691348952707897134319672027484170070848289889485392376,
            16386291405613506283348920375155794683440695147595174504099209929923594790285
        );
        vk.ic[8] = G1Point(
            19651293915120069849861139370762507185866189742626176540998285689425315960377,
            20717286581041304880867343173613827590422948210859464654239397760301802715819
        );
        vk.ic[9] = G1Point(
            21367116029342960301213243856950947530553257254088836496934801303792991148590,
            12623238421189368949756707502014109694120131484139720087658490168432191794004
        );
        vk.ic[10] = G1Point(
            11090282832531623741325223605792486410809452681296354326358813137542676075017,
            2353105836701112903342601082433206143300366883634190574541751875310875045642
        );
        vk.ic[11] = G1Point(
            4194432299269502324710450975325654286803314639719399136717721897549601912133,
            284041581908672570999504164824843822415582090941203589049454273776947933122
        );
        vk.ic[12] = G1Point(
            8935013016588295466376851027768798857373283201998093155161977637228391728229,
            20384389182116680545620540767214658186927454649242035950222396760258703368766
        );
        vk.ic[13] = G1Point(
            19684425500093052294751885928000733934815893347253551296692970951594683081684,
            2286216875411815938931354632354982991639982316705272414073001607689142528880
        );
        vk.ic[14] = G1Point(
            17460989753426354456303872430404707770496211331091968691522680917779689719402,
            12725784536655328477580475954842939349945696655575569743884196962232977194206
        );
        vk.ic[15] = G1Point(
            14874406841959474553471087562462027746703153292223091976874963557182528441383,
            1311716599771232068242919702012599591704933892542590083936465676092503865296
        );
        vk.ic[16] = G1Point(
            11741130682347121185152218386051511138664839613945826787238510548951490803438,
            13764182816583697392960213753094095960456831254335919451119128190208767114762
        );
        vk.ic[17] = G1Point(
            6761173660748841802154992371094681530909368754988435700290181031525083089871,
            19210518374369941518815328345294183698872815894940015428379314178562536881040
        );
        vk.ic[18] = G1Point(
            17997844196174891532900137386766507442930422059163134919329616436867007331950,
            851976965230870014827892523024906586177753582226924690841745584988600188540
        );
        vk.ic[19] = G1Point(
            11879441266068667213616269904614757531104087406501943773070128924009359502988,
            13687530871177301540947378742874668630121716220177426626273252369488158713212
        );
        vk.ic[20] = G1Point(
            14224638824691047602859497962849645000519881015356807936538032735800494536708,
            14229796463029546602037506529056446904942700438017896319141966172955065537362
        );
        vk.ic[21] = G1Point(
            19324031304467778658496463456554714210644966612381666111407965449057161838328,
            4221999373547316459644818495541104584495648810026441328679573214320764683930
        );
        vk.ic[22] = G1Point(
            1231004293649417137800545181245372939355950033642826482058934901221130499597,
            19974026542898583336847184638175769014587258369235170810554881537415017196447
        );
        vk.ic[23] = G1Point(
            921055842579251466143839625633818970422641994343429795147029386328494758367,
            3162236491179949285987540548606684847024494104716930029377632076314196059937
        );
        vk.ic[24] = G1Point(
            8051894549505747314563322588774557825497937066817618610938685332551006059174,
            3043010977460768858360547048510185918418874601848300804660271975800668218214
        );
        vk.ic[25] = G1Point(
            7848740768819107881428772432944602305649575542618623168740111172258607263264,
            15992344112717850503777272578835276587653470511632101745260487698728098941499
        );
        vk.ic[26] = G1Point(
            7851125206963537960366673390796083353732755347791881668227649891986410018523,
            3096611908419292553298124677577482312098136944522856714126318585734291355155
        );
    }
}
