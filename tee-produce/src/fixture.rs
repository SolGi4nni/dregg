//! **`FixtureBackend` is NOT an attestation producer.** It is a transport/wiring
//! test aid: it serves the ONE real attestation document this repo captured from a
//! live AWS Nitro Enclave (`tee-verify/tests/data/nitro_att.bin` — us-east-1,
//! c5.xlarge, debug-mode, its app bound `user_data = [0xAB; 32]`), so the
//! produce→transport→verify loop can be exercised end-to-end with genuine
//! vendor-signed bytes and NO enclave anywhere.
//!
//! Because the document is captured, it binds exactly one `report_data`
//! ([`FIXTURE_REPORT_DATA`]). This backend therefore REFUSES any request for a
//! different commitment: handing out a document whose `report_data` does not match
//! the request would be dishonest wiring (and the predicate rail would refuse it
//! downstream anyway). It cannot attest anything — it can only replay the one
//! session that really happened.

use crate::QuoteBackend;

/// The 32 bytes the live capture enclave bound into its document's `user_data` —
/// the only `report_data` [`FixtureBackend`] can serve.
pub const FIXTURE_REPORT_DATA: [u8; 32] = [0xAB; 32];

/// The real captured Nitro attestation document (COSE_Sign1 CBOR), verbatim.
pub const CAPTURED_NITRO_DOC: &[u8] = include_bytes!("../../tee-verify/tests/data/nitro_att.bin");

/// The captured-fixture quote source. Test/dev only — see the module docs: this
/// is a wiring aid that replays one real document, not a producer.
#[derive(Debug, Clone, Copy, Default)]
pub struct FixtureBackend;

impl QuoteBackend for FixtureBackend {
    fn attestation_document(&self, report_data: [u8; 32]) -> Result<Vec<u8>, String> {
        if report_data != FIXTURE_REPORT_DATA {
            return Err(format!(
                "FixtureBackend replays ONE captured live-enclave document, which binds \
                 report_data {} — it cannot attest {} (it is a transport test aid, not \
                 an attestation producer; fail-closed)",
                hex::encode(FIXTURE_REPORT_DATA),
                hex::encode(report_data),
            ));
        }
        Ok(CAPTURED_NITRO_DOC.to_vec())
    }
}
