//! The REAL AWS Nitro Security Module backend (`nitro` feature): asks the NSM for
//! a signed attestation document via the `/dev/nsm` ioctl driver
//! (`aws-nitro-enclaves-nsm-api`), binding the caller's 32-byte commitment into
//! the document's `user_data` — the field `dregg-tee-verify` extracts as
//! `report_data` and the `dregg_cell::tee_attest` predicate compares against the
//! landed attestation-slot commitment.
//!
//! Only meaningful INSIDE a running Nitro Enclave: everywhere else `/dev/nsm`
//! does not exist, `nsm_init` fails, and this backend returns `Err` — fail-closed,
//! never a fabricated document. On a non-unix target the NSM driver crate does not
//! build at all, so the backend compiles to an unconditional fail-closed stub.

use crate::QuoteBackend;

/// The live NSM quote source. Construct with [`NitroNsmBackend::new`]; each
/// request opens the NSM device, performs one `GetAttestationDoc`, and closes it.
#[derive(Debug, Clone, Copy, Default)]
pub struct NitroNsmBackend;

impl NitroNsmBackend {
    /// A backend that will talk to `/dev/nsm` when (and only when) it exists.
    pub fn new() -> NitroNsmBackend {
        NitroNsmBackend
    }
}

#[cfg(unix)]
impl QuoteBackend for NitroNsmBackend {
    fn attestation_document(&self, report_data: [u8; 32]) -> Result<Vec<u8>, String> {
        use aws_nitro_enclaves_nsm_api::api::{Request, Response};
        use aws_nitro_enclaves_nsm_api::driver::{nsm_exit, nsm_init, nsm_process_request};

        let fd = nsm_init();
        if fd < 0 {
            return Err(
                "cannot open /dev/nsm (not running inside a Nitro Enclave) — fail-closed"
                    .to_string(),
            );
        }
        let response = nsm_process_request(
            fd,
            Request::Attestation {
                // The binding contract: the commitment rides user_data, which the
                // verifier extracts as report_data. nonce/public_key stay empty —
                // freshness is bound INTO the commitment by the caller.
                user_data: Some(serde_bytes::ByteBuf::from(report_data.to_vec())),
                nonce: None,
                public_key: None,
            },
        );
        nsm_exit(fd);
        match response {
            Response::Attestation { document } if !document.is_empty() => Ok(document),
            Response::Attestation { .. } => {
                Err("NSM returned an empty attestation document".to_string())
            }
            Response::Error(code) => Err(format!("NSM refused the attestation request: {code:?}")),
            other => Err(format!("unexpected NSM response: {other:?}")),
        }
    }
}

#[cfg(not(unix))]
impl QuoteBackend for NitroNsmBackend {
    fn attestation_document(&self, _report_data: [u8; 32]) -> Result<Vec<u8>, String> {
        Err(
            "the Nitro NSM driver is unix-only (no /dev/nsm on this target) — fail-closed"
                .to_string(),
        )
    }
}
