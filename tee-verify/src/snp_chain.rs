//! AMD SEV-SNP certificate-chain trust — the `dregg_cell`-free core of the SNP
//! verifier ([`crate::snp::SnpVerifier`]).
//!
//! This module holds everything needed to anchor a SEV-SNP report to the **real AMD
//! root chain** — the pinned roots, the RSA-PSS link primitive, and the
//! `VCEK ← ASK ← ARK` chain verify — with no dependency on `dregg-cell` (hence none on
//! `dregg-circuit`). That separation lets the chain logic be built and tested standalone
//! (see `tee-verify/tests/`-adjacent standalone harness) even when a sibling crate in the
//! workspace is red.
//!
//! ## Pinned roots (provenance)
//!
//! The [`SnpProduct`] roots embedded below are the AMD **Key Distribution Service (KDS)**
//! `cert_chain` responses, fetched verbatim on **2026-07-13** from
//! `https://kdsintf.amd.com/vcek/v1/<Product>/cert_chain`. Each file is the KDS response
//! byte-for-byte: two PEM `CERTIFICATE` blocks, **ASK first** (the SEV signing key,
//! `CN=SEV-<Product>`) then **ARK** (the self-signed root, `CN=ARK-<Product>`). Both are
//! RSA-4096 signed with RSASSA-PSS / MGF1-SHA-384. Independently checked at pin time with
//! OpenSSL: each ARK is self-signed (`openssl verify` OK) and each ASK verifies under its
//! ARK. ARK SHA-256 fingerprints (the trust anchors):
//!
//! - Milan ARK: `69D063B45344D26A2E94E1F4210DE49EF555308287D4C174445C95639A540BCD`
//! - Genoa ARK: `4C6598D19C18719C5DFD4A7D335F674E5BFE1D8F800CEA2CF270C10D103DB2F1`
//! - Turin ARK: `1F084161A44BB6D93778A904877D4819CAFA5D05EF4193B2DED9DD9C73DD3F6A`
//!
//! These are chip-family constants (they change only when AMD rotates a product root),
//! so pinning them is exactly analogous to how [`crate`] pins the AWS Nitro root G1.

use p384::ecdsa::VerifyingKey;
use x509_parser::prelude::*;

/// The `id-RSASSA-PSS` signature-algorithm OID (`1.2.840.113549.1.1.10`) — how AMD's ARK
/// and ASK sign (RSA-4096, MGF1-SHA-384, salt 48). `x509-parser`'s `verify_signature`
/// supports only PKCS#1 v1.5 / ECDSA / Ed25519 (see its `verify.rs`), so a chain link
/// signed with this OID is routed to [`verify_rsa_pss_sha384`] instead.
const RSASSA_PSS_OID: &str = "1.2.840.113549.1.1.10";

/// Verify an **RSASSA-PSS / SHA-384** signature (the AMD ARK/ASK certificate-link
/// algorithm) with the `rsa` crate — the maintained impl `x509-parser` lacks. `issuer_spki`
/// is the issuer's `SubjectPublicKeyInfo.subjectPublicKey` bytes (a DER `RSAPublicKey`,
/// PKCS#1); `message` is the signed TBS DER; `signature` is the raw signature. Uses the
/// SHA-384 salt length (48 = digest output size, which `VerifyingKey::new` selects) — the
/// AMD ARK/ASK PSS parameter.
pub fn verify_rsa_pss_sha384(
    issuer_spki: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), String> {
    use rsa::pkcs1::DecodeRsaPublicKey;
    use rsa::pss::{Signature as PssSignature, VerifyingKey};
    use rsa::signature::Verifier;
    use sha2::Sha384;

    let pk = rsa::RsaPublicKey::from_pkcs1_der(issuer_spki)
        .map_err(|e| format!("issuer RSA public key (PKCS#1) decode: {e}"))?;
    let vk = VerifyingKey::<Sha384>::new(pk);
    let sig =
        PssSignature::try_from(signature).map_err(|e| format!("PSS signature decode: {e}"))?;
    vk.verify(message, &sig)
        .map_err(|e| format!("RSA-PSS-SHA384 signature verify FAILED: {e}"))
}

/// Verify one certificate-chain link: `child`'s signature under `issuer`'s public key,
/// dispatching on `child`'s signature algorithm. AMD's `id-RSASSA-PSS` ARK/ASK links go to
/// [`verify_rsa_pss_sha384`] (the `rsa` crate); everything else (the ECDSA-P384 VCEK link,
/// and the ECDSA self-PKI used in tests) goes through `x509-parser`'s `verify_signature`.
/// Either arm fails **closed** — an unsupported algorithm or a bad signature is an `Err`.
pub fn verify_cert_link(
    child: &X509Certificate<'_>,
    issuer: &X509Certificate<'_>,
) -> Result<(), String> {
    if child.signature_algorithm.algorithm.to_id_string() == RSASSA_PSS_OID {
        verify_rsa_pss_sha384(
            issuer.public_key().subject_public_key.data.as_ref(),
            child.tbs_certificate.as_ref(),
            child.signature_value.data.as_ref(),
        )
    } else {
        child
            .verify_signature(Some(issuer.public_key()))
            .map_err(|e| format!("chain link signature: {e:?}"))
    }
}

/// The operator-pinned AMD roots. `ark_der` is the self-signed AMD Root Key; `ask_der`
/// is the AMD SEV Signing Key (intermediate, signed by ARK). These are chip-family
/// constants fetched once from the AMD KDS and pinned — the per-chip VCEK is presented
/// alongside each report.
#[derive(Debug, Clone)]
pub struct SnpTrust {
    pub ark_der: Vec<u8>,
    pub ask_der: Vec<u8>,
}

/// Decode a single PEM `CERTIFICATE` block to its DER bytes. Only the first block is
/// read; a non-`CERTIFICATE` label is an error (fail-closed on malformed input).
fn pem_cert_to_der(pem: &str, what: &str) -> Result<Vec<u8>, String> {
    let (_, block) = x509_parser::pem::parse_x509_pem(pem.as_bytes())
        .map_err(|e| format!("{what} PEM parse: {e}"))?;
    if block.label != "CERTIFICATE" {
        return Err(format!(
            "{what} PEM label is {:?}, expected CERTIFICATE",
            block.label
        ));
    }
    Ok(block.contents)
}

/// The AMD **Key Distribution Service (KDS)** endpoint that serves the ASK+ARK PEM chain
/// for a SEV product line (`"Milan"`, `"Genoa"`, …). A GET returns the ASK (SEV
/// intermediate) followed by the self-signed ARK (SEV root), both PEM `CERTIFICATE`
/// blocks. Fetch this once per chip family, split the two blocks, and pin them via
/// [`SnpTrust::from_kds_cert_chain`]. The matching per-chip **VCEK** is fetched from
/// `https://kdsintf.amd.com/vcek/v1/{product}/{hwid}?blSPL=..&teeSPL=..&snpSPL=..&ucodeSPL=..`
/// and rides appended to each report (`report(1184) ‖ vcek_der`). No fetch happens here —
/// this only names the source URL so an operator (or a fetch tool outside the TCB) can
/// retrieve the roots and install them.
pub fn amd_kds_cert_chain_url(product: &str) -> String {
    format!("https://kdsintf.amd.com/vcek/v1/{product}/cert_chain")
}

/// A pinned AMD SEV-SNP product line. Each variant carries the KDS `cert_chain` embedded
/// below (fetched 2026-07-13 — see the module docs for provenance + fingerprints).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SnpProduct {
    /// 3rd-gen EPYC (Zen 3).
    Milan,
    /// 4th-gen EPYC (Zen 4).
    Genoa,
    /// 5th-gen EPYC (Zen 5).
    Turin,
}

/// AMD KDS `cert_chain` PEM (ASK then ARK), fetched verbatim 2026-07-13 from
/// `https://kdsintf.amd.com/vcek/v1/Milan/cert_chain`.
const AMD_MILAN_CERT_CHAIN_PEM: &str = include_str!("amd_milan_cert_chain.pem");
/// AMD KDS `cert_chain` PEM (ASK then ARK), fetched verbatim 2026-07-13 from
/// `https://kdsintf.amd.com/vcek/v1/Genoa/cert_chain`.
const AMD_GENOA_CERT_CHAIN_PEM: &str = include_str!("amd_genoa_cert_chain.pem");
/// AMD KDS `cert_chain` PEM (ASK then ARK), fetched verbatim 2026-07-13 from
/// `https://kdsintf.amd.com/vcek/v1/Turin/cert_chain`.
const AMD_TURIN_CERT_CHAIN_PEM: &str = include_str!("amd_turin_cert_chain.pem");

impl SnpProduct {
    /// The embedded KDS `cert_chain` PEM (ASK then ARK) for this product.
    pub fn cert_chain_pem(self) -> &'static str {
        match self {
            SnpProduct::Milan => AMD_MILAN_CERT_CHAIN_PEM,
            SnpProduct::Genoa => AMD_GENOA_CERT_CHAIN_PEM,
            SnpProduct::Turin => AMD_TURIN_CERT_CHAIN_PEM,
        }
    }

    /// The KDS `cert_chain` URL this product's roots were pinned from.
    pub fn cert_chain_url(self) -> String {
        amd_kds_cert_chain_url(match self {
            SnpProduct::Milan => "Milan",
            SnpProduct::Genoa => "Genoa",
            SnpProduct::Turin => "Turin",
        })
    }
}

impl SnpTrust {
    /// Build pinned roots from operator-provided PEM: the self-signed AMD **ARK** (SEV
    /// root) and the **ASK** (SEV intermediate). Each argument must contain a single PEM
    /// `CERTIFICATE` block; the DER is extracted and stored for chain verification.
    ///
    /// The real certificates come from the AMD KDS — see [`amd_kds_cert_chain_url`]. The
    /// `cert_chain` endpoint returns ASK then ARK; split the two blocks and pass the ARK
    /// block as `ark_pem` and the ASK block as `ask_pem`. Prefer
    /// [`SnpTrust::from_kds_cert_chain`] to avoid splitting by hand.
    pub fn from_pem(ark_pem: &str, ask_pem: &str) -> Result<SnpTrust, String> {
        Ok(SnpTrust {
            ark_der: pem_cert_to_der(ark_pem, "ARK")?,
            ask_der: pem_cert_to_der(ask_pem, "ASK")?,
        })
    }

    /// Build pinned roots from a KDS `cert_chain` response verbatim — the two-block PEM
    /// **ASK then ARK** (the order AMD's `/vcek/v1/<Product>/cert_chain` returns). Exactly
    /// two `CERTIFICATE` blocks are required; the first is the ASK, the second the ARK.
    /// Fail-closed: a wrong block count or a non-`CERTIFICATE` label is an `Err`.
    pub fn from_kds_cert_chain(chain_pem: &str) -> Result<SnpTrust, String> {
        let mut ders: Vec<Vec<u8>> = Vec::new();
        for block in x509_parser::pem::Pem::iter_from_buffer(chain_pem.as_bytes()) {
            let block = block.map_err(|e| format!("KDS cert_chain PEM parse: {e}"))?;
            if block.label != "CERTIFICATE" {
                return Err(format!(
                    "KDS cert_chain block label is {:?}, expected CERTIFICATE",
                    block.label
                ));
            }
            ders.push(block.contents);
        }
        if ders.len() != 2 {
            return Err(format!(
                "KDS cert_chain must hold exactly 2 certs (ASK then ARK), got {}",
                ders.len()
            ));
        }
        let ark_der = ders.pop().expect("len==2"); // second block = ARK (self-signed root)
        let ask_der = ders.pop().expect("len==2"); // first block  = ASK (SEV intermediate)
        Ok(SnpTrust { ark_der, ask_der })
    }

    /// The pinned AMD roots for a SEV-SNP product line — the real ARK/ASK embedded from
    /// the AMD KDS (see the module docs for provenance). This is the anchored trust the
    /// verifier is built with in production.
    pub fn for_product(product: SnpProduct) -> Result<SnpTrust, String> {
        SnpTrust::from_kds_cert_chain(product.cert_chain_pem())
    }
}

/// Verify VCEK ← ASK ← pinned-ARK and return the VCEK's P-384 public key.
///
/// Structured like [`crate::verify_cert_chain`]: each link's signature is checked
/// against its issuer's key (via [`verify_cert_link`]) and every cert's validity window is
/// checked at wall-clock now (SNP reports carry no timestamp of their own). AMD's ARK/ASK
/// sign RSA-4096 **PSS** — `x509-parser` cannot verify PSS, so [`verify_cert_link`] routes
/// those links to [`verify_rsa_pss_sha384`] (the `rsa` crate); the ECDSA-P384 VCEK link
/// stays on `x509-parser`. Either way this path fails **closed** (an unsupported signature
/// or a bad one is an `Err`, never a silent accept).
pub fn verify_snp_cert_chain(vcek_der: &[u8], trust: &SnpTrust) -> Result<VerifyingKey, String> {
    if vcek_der.is_empty() {
        return Err("no VCEK certificate appended to the SNP report bytes".into());
    }
    let (_, ark) =
        X509Certificate::from_der(&trust.ark_der).map_err(|e| format!("pinned ARK parse: {e}"))?;
    let (_, ask) =
        X509Certificate::from_der(&trust.ask_der).map_err(|e| format!("pinned ASK parse: {e}"))?;
    let (_, vcek) = X509Certificate::from_der(vcek_der).map_err(|e| format!("VCEK parse: {e}"))?;

    let now = ASN1Time::now();
    for (name, cert) in [("ARK", &ark), ("ASK", &ask), ("VCEK", &vcek)] {
        if !cert.validity().is_valid_at(now) {
            return Err(format!("{name} certificate is not valid now"));
        }
    }

    // ARK is self-signed (the trust anchor); ASK is signed by ARK; VCEK by ASK. Each link
    // dispatches by signature algorithm (RSA-PSS for the real AMD ARK/ASK, ECDSA otherwise).
    verify_cert_link(&ark, &ark).map_err(|e| format!("ARK self-signature: {e}"))?;
    verify_cert_link(&ask, &ark).map_err(|e| format!("ASK←ARK signature: {e}"))?;
    verify_cert_link(&vcek, &ask).map_err(|e| format!("VCEK←ASK signature: {e}"))?;

    let point = vcek.public_key().subject_public_key.data.as_ref();
    VerifyingKey::from_sec1_bytes(point).map_err(|e| format!("VCEK P-384 key: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The three pinned product roots load, hold exactly ASK+ARK, and each ARK is
    /// self-signed under the **real AMD RSA-PSS-SHA384 link** (`verify_cert_link` routing
    /// `id-RSASSA-PSS` to the `rsa` crate). The ASK verifies under its ARK. This exercises
    /// the real AMD root crypto with NO hardware and NO network at test time — the roots
    /// are embedded.
    #[test]
    fn real_amd_roots_load_and_self_verify() {
        for product in [SnpProduct::Milan, SnpProduct::Genoa, SnpProduct::Turin] {
            let trust = SnpTrust::for_product(product)
                .unwrap_or_else(|e| panic!("{product:?} roots load: {e}"));

            let (_, ark) = X509Certificate::from_der(&trust.ark_der).expect("ARK parse");
            let (_, ask) = X509Certificate::from_der(&trust.ask_der).expect("ASK parse");

            // ARK is self-signed with RSA-PSS-SHA384 (real AMD root crypto).
            verify_cert_link(&ark, &ark)
                .unwrap_or_else(|e| panic!("{product:?} ARK self-signature: {e}"));
            // ASK ← ARK, again the real RSA-PSS-SHA384 link.
            verify_cert_link(&ask, &ark).unwrap_or_else(|e| panic!("{product:?} ASK←ARK: {e}"));

            // The subjects are what AMD names them: ARK-<Product> (self) and SEV-<Product>.
            let ark_cn: Vec<_> = ark.subject().iter_common_name().collect();
            let ask_cn: Vec<_> = ask.subject().iter_common_name().collect();
            assert!(
                ark_cn[0].as_str().unwrap().starts_with("ARK-"),
                "{product:?} ARK CN = {:?}",
                ark_cn[0].as_str()
            );
            assert!(
                ask_cn[0].as_str().unwrap().starts_with("SEV-"),
                "{product:?} ASK CN = {:?}",
                ask_cn[0].as_str()
            );
            // ARK is its own issuer (self-signed root).
            assert_eq!(
                ark.issuer(),
                ark.subject(),
                "{product:?} ARK not self-issued"
            );
            // ASK is issued by the ARK.
            assert_eq!(ask.issuer(), ark.subject(), "{product:?} ASK issuer != ARK");
        }
    }

    /// A **forged / wrong ARK** rejects: swap in a different product's ARK and the real
    /// ASK no longer chains (the RSA-PSS-SHA384 link fails closed). Cross every pair.
    #[test]
    fn wrong_product_ark_rejects_real_ask() {
        let products = [SnpProduct::Milan, SnpProduct::Genoa, SnpProduct::Turin];
        for &p in &products {
            let real = SnpTrust::for_product(p).expect("roots");
            let (_, real_ask) = X509Certificate::from_der(&real.ask_der).expect("ASK parse");
            for &q in &products {
                if p == q {
                    continue;
                }
                let other = SnpTrust::for_product(q).expect("roots");
                let (_, wrong_ark) =
                    X509Certificate::from_der(&other.ark_der).expect("wrong ARK parse");
                assert!(
                    verify_cert_link(&real_ask, &wrong_ark).is_err(),
                    "{p:?} ASK must NOT verify under {q:?} ARK"
                );
            }
        }
    }

    /// A **tampered ARK** rejects: flip a byte in the DER and it no longer parses/verifies
    /// as a self-signed root.
    #[test]
    fn tampered_ark_rejects() {
        let trust = SnpTrust::for_product(SnpProduct::Milan).expect("roots");
        // Corrupt a byte deep in the ARK TBS (not the PEM framing).
        let mut bad = trust.ark_der.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 0xFF;
        match X509Certificate::from_der(&bad) {
            Ok((_, ark)) => assert!(
                verify_cert_link(&ark, &ark).is_err(),
                "tampered ARK must not self-verify"
            ),
            Err(_) => { /* corruption broke DER parse — also fail-closed */ }
        }
    }

    /// A **tampered ASK** rejects under the genuine ARK (the RSA-PSS-SHA384 link catches
    /// the flipped TBS byte).
    #[test]
    fn tampered_ask_rejects_under_real_ark() {
        let trust = SnpTrust::for_product(SnpProduct::Genoa).expect("roots");
        let (_, ark) = X509Certificate::from_der(&trust.ark_der).expect("ARK");
        let mut bad = trust.ask_der.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 0xFF;
        match X509Certificate::from_der(&bad) {
            Ok((_, ask)) => assert!(
                verify_cert_link(&ask, &ark).is_err(),
                "tampered ASK must not verify under real ARK"
            ),
            Err(_) => {}
        }
    }

    /// `from_kds_cert_chain` requires exactly two CERTIFICATE blocks and pins ARK=second,
    /// ASK=first (KDS order). Round-trips against the embedded Milan chain.
    #[test]
    fn kds_cert_chain_splits_ask_then_ark() {
        let trust = SnpTrust::from_kds_cert_chain(AMD_MILAN_CERT_CHAIN_PEM).expect("split");
        let (_, ark) = X509Certificate::from_der(&trust.ark_der).expect("ARK");
        let (_, ask) = X509Certificate::from_der(&trust.ask_der).expect("ASK");
        assert!(ark
            .subject()
            .iter_common_name()
            .next()
            .unwrap()
            .as_str()
            .unwrap()
            .starts_with("ARK-"));
        assert!(ask
            .subject()
            .iter_common_name()
            .next()
            .unwrap()
            .as_str()
            .unwrap()
            .starts_with("SEV-"));
        // A single-block PEM is rejected (fail-closed on wrong count).
        assert!(SnpTrust::from_kds_cert_chain(
            "-----BEGIN CERTIFICATE-----\nMIIB\n-----END CERTIFICATE-----\n"
        )
        .is_err());
    }

    /// `verify_snp_cert_chain` still fail-closes on an empty VCEK even with real pinned
    /// roots (the VCEK is per-chip and rides the report; without it no chain completes).
    #[test]
    fn real_roots_reject_empty_vcek() {
        let trust = SnpTrust::for_product(SnpProduct::Turin).expect("roots");
        assert!(verify_snp_cert_chain(&[], &trust).is_err());
    }

    /// The RSA-PSS-SHA384 link primitive — a genuine PSS-SHA384 signature over a stand-in
    /// TBS verifies; a tampered message, signature, or wrong issuer key is refused. This is
    /// the exact algorithm AMD's ARK/ASK sign with (`x509-parser` cannot do PSS). AMD uses
    /// RSA-4096; the test uses 2048 for keygen speed — identical code path.
    #[test]
    fn rsa_pss_sha384_link_primitive_roundtrips_and_rejects_tamper() {
        use rsa::pkcs1::EncodeRsaPublicKey;
        use rsa::pss::{Signature as PssSignature, SigningKey};
        use rsa::signature::{RandomizedSigner, SignatureEncoding};
        use rsa::RsaPrivateKey;
        use sha2::Sha384;

        let mut rng = rand::thread_rng();
        let sk = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen");
        let spki = sk
            .to_public_key()
            .to_pkcs1_der()
            .expect("pkcs1 der")
            .as_bytes()
            .to_vec();

        let signing = SigningKey::<Sha384>::new(sk);
        let msg = b"a stand-in for a certificate TBS DER (AMD ARK/ASK PSS-SHA384)";
        let sig: PssSignature = signing.sign_with_rng(&mut rng, msg);
        let sig_bytes = sig.to_bytes();

        verify_rsa_pss_sha384(&spki, msg, &sig_bytes).expect("valid PSS link");

        let mut bad_msg = msg.to_vec();
        bad_msg[0] ^= 0xFF;
        assert!(verify_rsa_pss_sha384(&spki, &bad_msg, &sig_bytes).is_err());

        let mut bad_sig = sig_bytes.to_vec();
        let n = bad_sig.len();
        bad_sig[n - 1] ^= 0xFF;
        assert!(verify_rsa_pss_sha384(&spki, msg, &bad_sig).is_err());

        let other = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen 2");
        let other_spki = other
            .to_public_key()
            .to_pkcs1_der()
            .unwrap()
            .as_bytes()
            .to_vec();
        assert!(verify_rsa_pss_sha384(&other_spki, msg, &sig_bytes).is_err());
    }

    #[test]
    fn amd_kds_url_names_the_real_source() {
        assert_eq!(
            amd_kds_cert_chain_url("Milan"),
            "https://kdsintf.amd.com/vcek/v1/Milan/cert_chain"
        );
        assert_eq!(
            SnpProduct::Genoa.cert_chain_url(),
            "https://kdsintf.amd.com/vcek/v1/Genoa/cert_chain"
        );
    }
}
