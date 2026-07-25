import Dregg2.Crypto.Keccak.Fips202Round
import Dregg2.Crypto.Keccak.Fips202Refine
import Dregg2.Crypto.Keccak.Fips202Lfsr
import Dregg2.Crypto.Keccak.Fips202SpongeRefine
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlKemKeygenRefine
import Dregg2.Crypto.MlDsaKeygenRefine
import Dregg2.Crypto.VerifyCoreHashFrame
import Dregg2.Crypto.Fips204ChallengeHash
import Dregg2.Crypto.VerifyCoreUseHint
import Dregg2.Crypto.MlKemNttFaithful
import Dregg2.Crypto.MlKemKeygenAcvp
import Dregg2.Crypto.MlKemEncapsAcvp
import Dregg2.Crypto.MlDsaKeygenAcvp
import Dregg2.Crypto.MlDsaSigGenAcvp
import Dregg2.Crypto.MlDsaSigVerAcvp

-- ===== KECCAK / FIPS 202 refinement chain =====
#print axioms Dregg2.Crypto.Keccak.Fips202Refine.rc_lanes_eq_exec
#print axioms Dregg2.Crypto.Keccak.Fips202Lfsr.rc_lanes_all
#print axioms Dregg2.Crypto.Keccak.Fips202Round.keccakRound_refines_spec
#print axioms Dregg2.Crypto.Keccak.Fips202Round.keccakF_refines_spec
#print axioms Dregg2.Crypto.Keccak.Fips202SpongeRefine.absorb_refines_spec
#print axioms Dregg2.Crypto.Keccak.Fips202SpongeRefine.squeeze_refines_spec
#print axioms Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines

-- ===== ML-KEM keygen refinement =====
#print axioms Dregg2.Crypto.MlKemKeygenRefine.kpkeKeyGen_refines_ring
#print axioms Dregg2.Crypto.MlKemKeygenRefine.kpkeKeyGen_refines_ring_of_rholen

-- ===== ML-DSA keygen refinement =====
#print axioms Dregg2.Crypto.MlDsaKeygenRefine.mldsaKeygen_pk_refines_ring
#print axioms Dregg2.Crypto.MlDsaKeygenRefine.mldsaKeygen_refines_ring
#print axioms Dregg2.Crypto.MlDsaKeygenRefine.expandS_sized_witness

-- ===== ML-DSA verify framing =====
#print axioms Dregg2.Crypto.VerifyCoreHashFrame.verifyCore_eq_specVerifyB
#print axioms Dregg2.Crypto.VerifyCoreHashFrame.verifyCore_eq_specVerifyB_deployed
#print axioms Dregg2.Crypto.VerifyCoreHashFrame.hashFrame
#print axioms Dregg2.Crypto.VerifyCoreHashFrame.hashFrame_deployed
#print axioms Dregg2.Crypto.VerifyCoreHashFrame.challengeMatches_eq_specHash
#print axioms Dregg2.Crypto.Fips204ChallengeHash.challengeHash_frames
#print axioms Dregg2.Crypto.Fips204ChallengeHash.challengeHash_frames_deployed
#print axioms Dregg2.Crypto.VerifyCoreEqSpec.w1Row_recovers_arg

-- ===== deployed-core ACVP KATs =====
#print axioms Dregg2.Crypto.MlKemKeygenAcvp.keygen_matches_acvp_tc26
#print axioms Dregg2.Crypto.MlKemKeygenAcvp.keygen_matches_acvp_tc27
#print axioms Dregg2.Crypto.MlKemEncapsAcvp.encaps_matches_acvp_group
#print axioms Dregg2.Crypto.MlKemEncapsAcvp.encaps_decaps_roundtrip_acvp_group
#print axioms Dregg2.Crypto.MlDsaKeygenAcvp.keygen_matches_acvp_tc26
#print axioms Dregg2.Crypto.MlDsaSigGenAcvp.sign_matches_acvp_group
#print axioms Dregg2.Crypto.MlDsaSigGenAcvp.sign_verify_agree_acvp_group
#print axioms Dregg2.Crypto.MlDsaSigVerAcvp.verifyCore_matches_acvp_sigVer

-- ===== deliberate non-vacuity WITNESSES (not foralls) =====
#print axioms Dregg2.Crypto.Keccak.shake256_empty_kat
#print axioms Dregg2.Crypto.MlKemRing.nttLeftInverse_sample
#print axioms Dregg2.Crypto.MlKemRing.nttMulHom_sample
