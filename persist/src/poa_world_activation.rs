//! Durable active-world authority for Path of Angels.
//!
//! `Dregg2.Games.PathOfAngels.WorldActivation` owns the transition semantics. This module owns
//! only native Ed25519 verification, construction of the Lean request from durable history,
//! strict decoding of the canonical Lean response, sealed append-only storage, and full-byte head
//! compare-and-swap. There is no Rust transition twin and no public raw `Prepared` constructor.

use dregg_lean_ffi::poa_world_activation_ffi::{authorize_poa_world, judge_poa_world_activation};
use ed25519_dalek::{Signature, VerifyingKey};
use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{PersistentStore, PoaWorldIdentityV2, Result, StoreError};

pub(crate) const POA_WORLD_ACTIVATION_HEAD_V1: TableDefinition<&str, &[u8]> =
    TableDefinition::new("poa_world_activation_head_v1");
pub(crate) const POA_WORLD_ACTIVATION_HISTORY_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("poa_world_activation_history_v1");
pub(crate) const POA_WORLD_CURATOR_PIN_V1: TableDefinition<&str, &[u8]> =
    TableDefinition::new("poa_world_curator_pin_v1");

const HEAD_KEY: &str = "active";
const CURATOR_PIN_KEY: &str = "installed";
const FRAME_MAGIC: [u8; 4] = *b"PWA1";
const FRAME_VERSION: u8 = 1;
const FRAME_HEADER_LEN: usize = 12;
const FRAME_SEAL_LEN: usize = 32;
const MAX_FRAME_BYTES: usize = 32 * 1024 * 1024;
const MAX_LEAN_WIRE_BYTES: usize = 16 * 1024 * 1024;
const MAX_HISTORY_RECORDS: u64 = 4096;
const FRAME_DOMAIN: &[u8] = b"dregg-poa-world-activation-frame-v1\0";
const HEAD_CAS_DOMAIN: &[u8] = b"dregg-poa-world-activation-head-cas-v1\0";

const INPUT_FORMAT: &str = "POA-WORLD-ACTIVATION-IN-1";
const OUTPUT_FORMAT: &str = "POA-WORLD-ACTIVATION-OUT-1";
const AUTHORIZE_INPUT_FORMAT: &str = "POA-WORLD-AUTHORIZE-IN-1";
pub const POA_WORLD_ACTIVATION_STATEMENT_SCHEMA_V1: &str = "POA-WORLD-ACTIVATION-STATEMENT-1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PoaWorldActivationKindV1 {
    Advance,
    Rollback,
}

impl PoaWorldActivationKindV1 {
    const fn label(self) -> &'static str {
        match self {
            Self::Advance => "advance",
            Self::Rollback => "rollback",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaWorldActivationStatementV1 {
    world: PoaWorldIdentityV2,
    counter: u64,
    predecessor_head: [u8; 32],
    kind: PoaWorldActivationKindV1,
    rollback_target: Option<[u8; 32]>,
}

impl PoaWorldActivationStatementV1 {
    pub fn new(
        world: PoaWorldIdentityV2,
        counter: u64,
        predecessor_head: [u8; 32],
        kind: PoaWorldActivationKindV1,
        rollback_target: Option<[u8; 32]>,
    ) -> Result<Self> {
        validate_world(&world)?;
        if counter == 0 {
            return Err(integrity("PoA world activation counter must be nonzero"));
        }
        match (kind, rollback_target) {
            (PoaWorldActivationKindV1::Advance, Some(_)) => {
                return Err(integrity("PoA advance carries a rollback target"));
            }
            (PoaWorldActivationKindV1::Rollback, None) => {
                return Err(integrity("PoA rollback omitted its target"));
            }
            _ => {}
        }
        Ok(Self {
            world,
            counter,
            predecessor_head,
            kind,
            rollback_target,
        })
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        &self.world
    }

    pub const fn counter(&self) -> u64 {
        self.counter
    }

    pub const fn predecessor_head(&self) -> [u8; 32] {
        self.predecessor_head
    }

    pub const fn kind(&self) -> PoaWorldActivationKindV1 {
        self.kind
    }

    pub const fn rollback_target(&self) -> Option<[u8; 32]> {
        self.rollback_target
    }

    /// Exact canonical bytes covered by the curator's Ed25519 signature.
    pub fn signing_message(&self) -> Result<Vec<u8>> {
        validate_world(&self.world)?;
        serde_json::to_vec(&JsonStatement::from(self))
            .map_err(|error| integrity(format!("PoA activation statement JSON failed: {error}")))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedPoaWorldActivationEnvelopeV1 {
    statement: PoaWorldActivationStatementV1,
    curator_key: [u8; 32],
    signature: Vec<u8>,
}

impl SignedPoaWorldActivationEnvelopeV1 {
    pub fn new(
        statement: PoaWorldActivationStatementV1,
        curator_key: [u8; 32],
        signature: [u8; 64],
    ) -> Result<Self> {
        let envelope = Self {
            statement,
            curator_key,
            signature: signature.to_vec(),
        };
        envelope.validate_shape()?;
        Ok(envelope)
    }

    pub const fn statement(&self) -> &PoaWorldActivationStatementV1 {
        &self.statement
    }

    pub const fn curator_key(&self) -> [u8; 32] {
        self.curator_key
    }

    pub fn signature(&self) -> &[u8] {
        &self.signature
    }

    pub fn canonical_json(&self) -> Result<Vec<u8>> {
        serde_json::to_vec(&JsonEnvelope::from(self))
            .map_err(|error| integrity(format!("PoA activation envelope JSON failed: {error}")))
    }

    pub fn digest(&self) -> Result<[u8; 32]> {
        Ok(sha256(&self.canonical_json()?))
    }

    fn validate_shape(&self) -> Result<()> {
        validate_world(&self.statement.world)?;
        if self.statement.counter == 0 {
            return Err(integrity("PoA world activation counter must be nonzero"));
        }
        match (self.statement.kind, self.statement.rollback_target) {
            (PoaWorldActivationKindV1::Advance, Some(_)) => {
                return Err(integrity("PoA advance carries a rollback target"));
            }
            (PoaWorldActivationKindV1::Rollback, None) => {
                return Err(integrity("PoA rollback omitted its target"));
            }
            _ => {}
        }
        if self.signature.len() != 64 {
            return Err(integrity(
                "PoA curator signature must contain exactly 64 bytes",
            ));
        }
        Ok(())
    }

    fn verify_signature(&self, external_curator_key_pin: [u8; 32]) -> Result<()> {
        self.validate_shape()?;
        if self.curator_key != external_curator_key_pin {
            return Err(integrity(
                "PoA activation curator key differs from external pin",
            ));
        }
        let key = VerifyingKey::from_bytes(&external_curator_key_pin)
            .map_err(|_| integrity("PoA external curator key pin is not valid Ed25519"))?;
        let signature_bytes: [u8; 64] = self
            .signature
            .as_slice()
            .try_into()
            .map_err(|_| integrity("PoA curator signature has wrong length"))?;
        key.verify_strict(
            &self.statement.signing_message()?,
            &Signature::from_bytes(&signature_bytes),
        )
        .map_err(|_| integrity("PoA curator signature verification failed"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaWorldActivationRecordV1 {
    envelope: SignedPoaWorldActivationEnvelopeV1,
    envelope_digest: [u8; 32],
}

impl PoaWorldActivationRecordV1 {
    fn new(envelope: SignedPoaWorldActivationEnvelopeV1) -> Result<Self> {
        let envelope_digest = envelope.digest()?;
        Ok(Self {
            envelope,
            envelope_digest,
        })
    }

    pub const fn envelope(&self) -> &SignedPoaWorldActivationEnvelopeV1 {
        &self.envelope
    }

    pub const fn envelope_digest(&self) -> [u8; 32] {
        self.envelope_digest
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        self.envelope.statement.world()
    }

    pub const fn counter(&self) -> u64 {
        self.envelope.statement.counter()
    }

    fn validate(&self, external_curator_key_pin: [u8; 32]) -> Result<()> {
        self.envelope.verify_signature(external_curator_key_pin)?;
        if self.envelope_digest != self.envelope.digest()? {
            return Err(integrity("PoA activation envelope digest mismatch"));
        }
        Ok(())
    }
}

/// Exact native-signature + Lean-acceptance evidence stored beside one activation.
///
/// The only production constructor is `PersistentStore::prepare_poa_world_activation_v1`, which
/// derives the request from a freshly audited durable prefix and strictly checks the real Lean
/// response. `expected_head_cas_bytes` is process-local preparation evidence and is never sealed
/// recursively into the stored frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaWorldActivationV1 {
    record: PoaWorldActivationRecordV1,
    lean_request: Vec<u8>,
    lean_response: Vec<u8>,
    lean_request_digest: [u8; 32],
    lean_response_digest: [u8; 32],
    expected_head_cas_bytes: Option<Vec<u8>>,
}

/// Private storage codec. Keeping `Deserialize` off the public `Prepared` type is load-bearing:
/// otherwise any caller could manufacture the allegedly sealed authority with `postcard` despite
/// the absence of a public Rust constructor.
#[derive(Serialize, Deserialize)]
struct StoredPreparedPoaWorldActivationV1 {
    record: PoaWorldActivationRecordV1,
    lean_request: Vec<u8>,
    lean_response: Vec<u8>,
    lean_request_digest: [u8; 32],
    lean_response_digest: [u8; 32],
}

impl From<&PreparedPoaWorldActivationV1> for StoredPreparedPoaWorldActivationV1 {
    fn from(prepared: &PreparedPoaWorldActivationV1) -> Self {
        Self {
            record: prepared.record.clone(),
            lean_request: prepared.lean_request.clone(),
            lean_response: prepared.lean_response.clone(),
            lean_request_digest: prepared.lean_request_digest,
            lean_response_digest: prepared.lean_response_digest,
        }
    }
}

impl StoredPreparedPoaWorldActivationV1 {
    fn into_prepared(self) -> PreparedPoaWorldActivationV1 {
        PreparedPoaWorldActivationV1 {
            record: self.record,
            lean_request: self.lean_request,
            lean_response: self.lean_response,
            lean_request_digest: self.lean_request_digest,
            lean_response_digest: self.lean_response_digest,
            expected_head_cas_bytes: None,
        }
    }
}

impl PreparedPoaWorldActivationV1 {
    fn from_verified_lean(
        record: PoaWorldActivationRecordV1,
        lean_request: Vec<u8>,
        lean_response: Vec<u8>,
        expected_head_cas_bytes: Option<Vec<u8>>,
    ) -> Result<Self> {
        validate_wire_component(&lean_request, "PoA Lean activation request")?;
        validate_wire_component(&lean_response, "PoA Lean activation response")?;
        let prepared = Self {
            record,
            lean_request_digest: sha256(&lean_request),
            lean_response_digest: sha256(&lean_response),
            lean_request,
            lean_response,
            expected_head_cas_bytes,
        };
        prepared.validate_components()?;
        Ok(prepared)
    }

    pub const fn record(&self) -> &PoaWorldActivationRecordV1 {
        &self.record
    }

    pub fn lean_request(&self) -> &[u8] {
        &self.lean_request
    }

    pub fn lean_response(&self) -> &[u8] {
        &self.lean_response
    }

    pub const fn lean_request_digest(&self) -> [u8; 32] {
        self.lean_request_digest
    }

    pub const fn lean_response_digest(&self) -> [u8; 32] {
        self.lean_response_digest
    }

    fn validate_components(&self) -> Result<()> {
        validate_wire_component(&self.lean_request, "PoA Lean activation request")?;
        validate_wire_component(&self.lean_response, "PoA Lean activation response")?;
        if self.lean_request_digest != sha256(&self.lean_request)
            || self.lean_response_digest != sha256(&self.lean_response)
        {
            return Err(integrity("PoA Lean activation wire digest mismatch"));
        }
        Ok(())
    }
}

/// Durable head plus the exact sealed bytes required for the next full-byte CAS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaActiveWorldHeadV1 {
    prepared: PreparedPoaWorldActivationV1,
    frame_digest: [u8; 32],
    cas_bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaWorldActivationInstallStatusV1 {
    Installed,
    AlreadyRecorded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaWorldActivationInstallOutcomeV1 {
    status: PoaWorldActivationInstallStatusV1,
    active_head: PoaActiveWorldHeadV1,
}

impl PoaWorldActivationInstallOutcomeV1 {
    pub const fn status(&self) -> PoaWorldActivationInstallStatusV1 {
        self.status
    }

    pub const fn active_head(&self) -> &PoaActiveWorldHeadV1 {
        &self.active_head
    }
}

impl PoaActiveWorldHeadV1 {
    pub const fn prepared(&self) -> &PreparedPoaWorldActivationV1 {
        &self.prepared
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        self.prepared.record.world()
    }

    pub const fn counter(&self) -> u64 {
        self.prepared.record.counter()
    }

    pub const fn frame_digest(&self) -> [u8; 32] {
        self.frame_digest
    }

    pub fn cas_bytes(&self) -> &[u8] {
        &self.cas_bytes
    }
}

pub(crate) fn initialize_poa_world_activation_tables_v1_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_WORLD_ACTIVATION_HEAD_V1)?;
    let _ = write.open_table(POA_WORLD_ACTIVATION_HISTORY_V1)?;
    let _ = write.open_table(POA_WORLD_CURATOR_PIN_V1)?;
    Ok(())
}

/// Append one already native-verified and Lean-authorized activation in the finalized outer
/// writer. The full exact head bytes captured during preparation are compared before mutation.
pub(crate) fn stage_fresh_poa_world_activation_in(
    write: &WriteTransaction,
    candidate: &PreparedPoaWorldActivationV1,
) -> Result<()> {
    initialize_poa_world_activation_tables_v1_in(write)?;
    let external_curator_key_pin = require_installed_curator_pin_in(write)?;
    let audited = audit_tables_in(write, external_curator_key_pin)?;
    validate_prepared_against_prefix(candidate, external_curator_key_pin, &audited)?;

    let current_bytes = {
        let heads = write.open_table(POA_WORLD_ACTIVATION_HEAD_V1)?;
        heads.get(HEAD_KEY)?.map(|bytes| bytes.value().to_vec())
    };
    if current_bytes != candidate.expected_head_cas_bytes {
        return Err(integrity("PoA active-world full-byte CAS mismatch"));
    }

    let counter = candidate.record.counter();
    let frame = encode_frame(candidate)?;
    {
        let history = write.open_table(POA_WORLD_ACTIVATION_HISTORY_V1)?;
        if history.get(counter)?.is_some() {
            return Err(integrity("PoA activation counter already recorded"));
        }
    }
    {
        let mut history = write.open_table(POA_WORLD_ACTIVATION_HISTORY_V1)?;
        history.insert(counter, frame.as_slice())?;
        let mut heads = write.open_table(POA_WORLD_ACTIVATION_HEAD_V1)?;
        heads.insert(HEAD_KEY, frame.as_slice())?;
    }
    Ok(())
}

/// Verify crash replay against the exact immutable history frame without moving the active head.
pub(crate) fn verify_replayed_poa_world_activation_in(
    write: &WriteTransaction,
    candidate: &PreparedPoaWorldActivationV1,
) -> Result<()> {
    initialize_poa_world_activation_tables_v1_in(write)?;
    let external_curator_key_pin = require_installed_curator_pin_in(write)?;
    audit_tables_in(write, external_curator_key_pin)?;
    candidate.record.validate(external_curator_key_pin)?;
    candidate.validate_components()?;
    let expected = encode_frame(candidate)?;
    let history = write.open_table(POA_WORLD_ACTIVATION_HISTORY_V1)?;
    let stored = history
        .get(candidate.record.counter())?
        .ok_or_else(|| integrity("replayed PoA activation is not recorded"))?;
    if stored.value() != expected.as_slice() {
        return Err(integrity("replayed PoA activation is not full-byte exact"));
    }
    Ok(())
}

#[derive(Clone)]
struct AuditedStoredActivation {
    prepared: PreparedPoaWorldActivationV1,
    frame: Vec<u8>,
}

fn audit_tables_in(
    write: &WriteTransaction,
    external_curator_key_pin: [u8; 32],
) -> Result<Vec<AuditedStoredActivation>> {
    let history = write.open_table(POA_WORLD_ACTIVATION_HISTORY_V1)?;
    let heads = write.open_table(POA_WORLD_ACTIVATION_HEAD_V1)?;
    if heads.len()? > 1 {
        return Err(integrity("PoA active-world table contains multiple heads"));
    }
    if history.len()? > MAX_HISTORY_RECORDS {
        return Err(integrity("PoA activation history exceeds bound"));
    }

    let mut audited = Vec::new();
    let mut final_frame = None;
    for entry in history.iter()? {
        let (counter, bytes) = entry?;
        let frame = bytes.value().to_vec();
        let prepared = decode_frame(&frame)?;
        if prepared.record.counter() != counter.value() {
            return Err(integrity("PoA activation history key/counter mismatch"));
        }
        validate_prepared_against_prefix(&prepared, external_curator_key_pin, &audited)?;
        final_frame = Some(frame.clone());
        audited.push(AuditedStoredActivation { prepared, frame });
    }

    let head = heads.get(HEAD_KEY)?.map(|bytes| bytes.value().to_vec());
    if head != final_frame {
        return Err(integrity(
            "PoA active-world head is not the final history frame",
        ));
    }
    Ok(audited)
}

impl PersistentStore {
    /// Install the independently distributed curator pin exactly once. Production callers source
    /// this from node/genesis configuration; request handlers must never expose this method.
    pub fn install_poa_world_curator_pin_v1(&self, trusted_pin: [u8; 32]) -> Result<()> {
        validate_curator_pin(trusted_pin)?;
        let write = self.db.begin_write()?;
        initialize_poa_world_activation_tables_v1_in(&write)?;
        {
            let mut pins = write.open_table(POA_WORLD_CURATOR_PIN_V1)?;
            let entry_count = pins.len()?;
            let installed = pins
                .get(CURATOR_PIN_KEY)?
                .map(|value| value.value().to_vec());
            match (entry_count, installed) {
                (0, None) => {
                    pins.insert(CURATOR_PIN_KEY, trusted_pin.as_slice())?;
                }
                (1, Some(installed)) if installed.as_slice() == trusted_pin => {}
                (1, Some(_)) => {
                    return Err(integrity(
                        "PoA curator pin is already installed and cannot be substituted",
                    ));
                }
                _ => return Err(integrity("PoA curator-pin table has invalid shape")),
            }
        }
        write.commit()?;
        Ok(())
    }

    pub fn load_poa_world_curator_pin_v1(&self) -> Result<Option<[u8; 32]>> {
        let read = self.db.begin_read()?;
        let pins = read.open_table(POA_WORLD_CURATOR_PIN_V1)?;
        let entry_count = pins.len()?;
        let installed = pins
            .get(CURATOR_PIN_KEY)?
            .map(|value| value.value().to_vec());
        match (entry_count, installed) {
            (0, None) => Ok(None),
            (1, Some(bytes)) => decode_curator_pin(&bytes).map(Some),
            _ => Err(integrity("PoA curator-pin table has invalid shape")),
        }
    }

    /// Build an activation solely from a freshly audited durable prefix, verify the exact signed
    /// statement under the installed pin, invoke the real Lean authority, and strictly decode its
    /// canonical accepted response. This is the only production `Prepared` constructor.
    pub fn prepare_poa_world_activation_v1(
        &self,
        untrusted_envelope: SignedPoaWorldActivationEnvelopeV1,
    ) -> Result<PreparedPoaWorldActivationV1> {
        let write = self.db.begin_write()?;
        initialize_poa_world_activation_tables_v1_in(&write)?;
        let external_curator_key_pin = require_installed_curator_pin_in(&write)?;
        let audited = audit_tables_in(&write, external_curator_key_pin)?;
        let prepared =
            prepare_against_prefix(external_curator_key_pin, &audited, untrusted_envelope)?;
        write.abort()?;
        Ok(prepared)
    }

    /// Atomically install a native-signature-verified, Lean-authorized activation. An exact retry
    /// of any already-recorded envelope succeeds without moving the active head; a different
    /// envelope at the same counter refuses.
    pub fn install_poa_world_activation_v1(
        &self,
        untrusted_envelope: SignedPoaWorldActivationEnvelopeV1,
    ) -> Result<PoaWorldActivationInstallOutcomeV1> {
        let write = self.db.begin_write()?;
        initialize_poa_world_activation_tables_v1_in(&write)?;
        let external_curator_key_pin = require_installed_curator_pin_in(&write)?;
        let audited = audit_tables_in(&write, external_curator_key_pin)?;
        untrusted_envelope.verify_signature(external_curator_key_pin)?;

        if let Some(recorded) = audited.iter().find(|stored| {
            stored.prepared.record.counter() == untrusted_envelope.statement().counter()
        }) {
            if recorded.prepared.record.envelope() != &untrusted_envelope {
                return Err(integrity(
                    "PoA activation counter is already occupied by another envelope",
                ));
            }
            write.abort()?;
            let active_head = self
                .load_poa_active_world_v1()?
                .ok_or_else(|| integrity("PoA exact retry found no active head"))?;
            return Ok(PoaWorldActivationInstallOutcomeV1 {
                status: PoaWorldActivationInstallStatusV1::AlreadyRecorded,
                active_head,
            });
        }

        let prepared =
            prepare_against_prefix(external_curator_key_pin, &audited, untrusted_envelope)?;
        stage_fresh_poa_world_activation_in(&write, &prepared)?;
        write.commit()?;
        let active_head = self
            .load_poa_active_world_v1()?
            .ok_or_else(|| integrity("PoA activation commit produced no active head"))?;
        Ok(PoaWorldActivationInstallOutcomeV1 {
            status: PoaWorldActivationInstallStatusV1::Installed,
            active_head,
        })
    }

    /// Observational read only. Authority-sensitive callers use the installed-pin audit or the
    /// same-writer exact-world gate below.
    pub fn load_poa_active_world_v1(&self) -> Result<Option<PoaActiveWorldHeadV1>> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(POA_WORLD_ACTIVATION_HEAD_V1)?;
        let Some(bytes) = heads.get(HEAD_KEY)? else {
            return Ok(None);
        };
        let cas_bytes = bytes.value().to_vec();
        let prepared = decode_frame(&cas_bytes)?;
        Ok(Some(PoaActiveWorldHeadV1 {
            prepared,
            frame_digest: sha256_domain(HEAD_CAS_DOMAIN, &cas_bytes),
            cas_bytes,
        }))
    }

    /// Reopen audit: reverify every native signature, reconstruct every request from the durable
    /// prefix, re-invoke Lean, and require its response byte-for-byte equals the sealed evidence.
    pub fn audit_poa_world_activation_v1(&self) -> Result<()> {
        let write = self.db.begin_write()?;
        initialize_poa_world_activation_tables_v1_in(&write)?;
        let external_curator_key_pin = require_installed_curator_pin_in(&write)?;
        audit_tables_in(&write, external_curator_key_pin)?;
        write.abort()?;
        Ok(())
    }
}

/// Exact all-five-field world equality inside the finalized EventBatch writer. The durable
/// lineage is fully signature- and Lean-replayed before the head is trusted.
pub(crate) fn load_poa_active_world_exact_in(
    write: &WriteTransaction,
) -> Result<PoaWorldIdentityV2> {
    let external_curator_key_pin = require_installed_curator_pin_in(write)?;
    let audited = audit_tables_in(write, external_curator_key_pin)?;
    let active = audited
        .last()
        .ok_or_else(|| integrity("PoA active world is not installed"))?
        .prepared
        .record()
        .world()
        .clone();
    let request = build_world_authorization_request(external_curator_key_pin, &audited, &active)?;
    let request = std::str::from_utf8(&request)
        .map_err(|_| integrity("PoA exact-world authorization request is not UTF-8"))?;
    let authorized = authorize_poa_world(request)
        .map_err(|error| integrity(format!("PoA exact-world Lean judge failed: {error}")))?;
    if !authorized {
        return Err(integrity(
            "PoA activation head is not the exact Lean-authorized active world",
        ));
    }
    Ok(active)
}

/// Exact all-five-field world equality inside the finalized EventBatch writer. The durable
/// lineage is fully signature- and Lean-replayed before the head is trusted.
pub(crate) fn require_poa_active_world_exact_in(
    write: &WriteTransaction,
    candidate: &PoaWorldIdentityV2,
) -> Result<()> {
    if &load_poa_active_world_exact_in(write)? != candidate {
        return Err(integrity("PoA batch world is not the exact active world"));
    }
    Ok(())
}

/// Require that `candidate` was the exact active world at some authenticated point in the
/// durable activation lineage.
///
/// This is the replay counterpart to [`require_poa_active_world_exact_in`]. A finalized batch is
/// admitted only under the current head, but rebuilding that batch after a later legitimate world
/// rotation must not make its historical coordinate invalid. We therefore:
///
/// 1. audit the *entire* stored lineage under the install-once curator pin (native signatures,
///    sealed requests/responses, and every Lean-authored transition edge);
/// 2. select an exact all-five-field occurrence of the candidate world; and
/// 3. ask Lean to replay the prefix ending at that activation and prove that candidate was its
///    active world.
///
/// The returned counter identifies the authenticated historical activation. EventBatch V2 does
/// not yet carry that counter, so the caller must still perform full-byte replay against the
/// immutable batch row to bind this historical authority to the finalized commit.
pub(crate) fn require_poa_historical_world_exact_in(
    write: &WriteTransaction,
    candidate: &PoaWorldIdentityV2,
) -> Result<u64> {
    validate_world(candidate)?;
    let external_curator_key_pin = require_installed_curator_pin_in(write)?;
    let audited = audit_tables_in(write, external_curator_key_pin)?;
    let activation_index = audited
        .iter()
        .rposition(|stored| stored.prepared.record.world() == candidate)
        .ok_or_else(|| {
            integrity("PoA batch world never appeared in the authenticated activation lineage")
        })?;
    let historical_prefix = &audited[..=activation_index];
    let request =
        build_world_authorization_request(external_curator_key_pin, historical_prefix, candidate)?;
    let request = std::str::from_utf8(&request)
        .map_err(|_| integrity("PoA historical-world authorization request is not UTF-8"))?;
    let authorized = authorize_poa_world(request)
        .map_err(|error| integrity(format!("PoA historical-world Lean judge failed: {error}")))?;
    if !authorized {
        return Err(integrity(
            "PoA batch world was not active at its authenticated historical activation",
        ));
    }
    Ok(audited[activation_index].prepared.record.counter())
}

fn require_installed_curator_pin_in(write: &WriteTransaction) -> Result<[u8; 32]> {
    let pins = write.open_table(POA_WORLD_CURATOR_PIN_V1)?;
    if pins.len()? != 1 {
        return Err(integrity(
            "PoA requires exactly one durably installed curator pin",
        ));
    }
    let value = pins
        .get(CURATOR_PIN_KEY)?
        .ok_or_else(|| integrity("PoA curator pin is not installed"))?;
    decode_curator_pin(value.value())
}

fn decode_curator_pin(bytes: &[u8]) -> Result<[u8; 32]> {
    let pin: [u8; 32] = bytes
        .try_into()
        .map_err(|_| integrity("PoA installed curator pin has wrong length"))?;
    validate_curator_pin(pin)?;
    Ok(pin)
}

fn validate_curator_pin(pin: [u8; 32]) -> Result<()> {
    if pin == [0; 32] {
        return Err(integrity("PoA curator pin cannot be zero"));
    }
    VerifyingKey::from_bytes(&pin)
        .map_err(|_| integrity("PoA curator pin is not a valid Ed25519 key"))?;
    Ok(())
}

fn prepare_against_prefix(
    external_curator_key_pin: [u8; 32],
    audited: &[AuditedStoredActivation],
    untrusted_envelope: SignedPoaWorldActivationEnvelopeV1,
) -> Result<PreparedPoaWorldActivationV1> {
    untrusted_envelope.verify_signature(external_curator_key_pin)?;
    let expected_head_cas_bytes = audited.last().map(|stored| stored.frame.clone());
    let record = PoaWorldActivationRecordV1::new(untrusted_envelope)?;
    let lean_request = build_lean_request(external_curator_key_pin, audited, record.envelope())?;
    let lean_request_text = std::str::from_utf8(&lean_request)
        .map_err(|_| integrity("PoA Lean activation request is not UTF-8"))?;
    let lean_response = judge_poa_world_activation(lean_request_text)
        .map_err(|error| integrity(format!("PoA Lean activation judge failed: {error}")))?
        .into_bytes();
    validate_accepted_response(audited, &record, &lean_response)?;
    PreparedPoaWorldActivationV1::from_verified_lean(
        record,
        lean_request,
        lean_response,
        expected_head_cas_bytes,
    )
}

fn validate_prepared_against_prefix(
    prepared: &PreparedPoaWorldActivationV1,
    external_curator_key_pin: [u8; 32],
    prefix: &[AuditedStoredActivation],
) -> Result<()> {
    prepared.record.validate(external_curator_key_pin)?;
    prepared.validate_components()?;
    let exact_request =
        build_lean_request(external_curator_key_pin, prefix, prepared.record.envelope())?;
    if exact_request != prepared.lean_request {
        return Err(integrity(
            "PoA sealed Lean request was not derived from the durable prefix",
        ));
    }
    let request = std::str::from_utf8(&prepared.lean_request)
        .map_err(|_| integrity("PoA sealed Lean request is not UTF-8"))?;
    let replayed_response = judge_poa_world_activation(request)
        .map_err(|error| integrity(format!("PoA Lean activation reaudit failed: {error}")))?;
    if replayed_response.as_bytes() != prepared.lean_response {
        return Err(integrity(
            "PoA Lean activation response changed during durable reaudit",
        ));
    }
    validate_accepted_response(prefix, &prepared.record, &prepared.lean_response)
}

fn build_lean_request(
    external_curator_key_pin: [u8; 32],
    prefix: &[AuditedStoredActivation],
    envelope: &SignedPoaWorldActivationEnvelopeV1,
) -> Result<Vec<u8>> {
    let state = JsonState {
        history: prefix
            .iter()
            .map(|stored| JsonRecord::from(&stored.prepared.record))
            .collect(),
    };
    let input = JsonInput {
        format: INPUT_FORMAT.to_owned(),
        external_curator_key_pin: hex(&external_curator_key_pin),
        native_signature_verified: true,
        state,
        envelope: JsonEnvelope::from(envelope),
    };
    let bytes = serde_json::to_vec(&input)
        .map_err(|error| integrity(format!("PoA Lean activation input JSON failed: {error}")))?;
    validate_wire_component(&bytes, "PoA Lean activation request")?;
    Ok(bytes)
}

fn build_world_authorization_request(
    external_curator_key_pin: [u8; 32],
    prefix: &[AuditedStoredActivation],
    candidate: &PoaWorldIdentityV2,
) -> Result<Vec<u8>> {
    let input = JsonAuthorityInput {
        format: AUTHORIZE_INPUT_FORMAT.to_owned(),
        external_curator_key_pin: hex(&external_curator_key_pin),
        native_signatures_verified: true,
        state: JsonState {
            history: prefix
                .iter()
                .map(|stored| JsonRecord::from(&stored.prepared.record))
                .collect(),
        },
        candidate: JsonWorld::from(candidate),
    };
    let bytes = serde_json::to_vec(&input)
        .map_err(|error| integrity(format!("PoA exact-world input JSON failed: {error}")))?;
    validate_wire_component(&bytes, "PoA exact-world authorization request")?;
    Ok(bytes)
}

fn validate_accepted_response(
    prefix: &[AuditedStoredActivation],
    record: &PoaWorldActivationRecordV1,
    response: &[u8],
) -> Result<()> {
    validate_wire_component(response, "PoA Lean activation response")?;
    let decoded: JsonAcceptedOutput = serde_json::from_slice(response).map_err(|error| {
        integrity(format!(
            "PoA Lean activation response is not accepted: {error}"
        ))
    })?;
    let canonical = serde_json::to_vec(&decoded)
        .map_err(|error| integrity(format!("PoA Lean activation output JSON failed: {error}")))?;
    if canonical != response {
        return Err(integrity("PoA Lean activation response is not canonical"));
    }
    let mut expected_history: Vec<JsonRecord> = prefix
        .iter()
        .map(|stored| JsonRecord::from(&stored.prepared.record))
        .collect();
    expected_history.push(JsonRecord::from(record));
    let expected = JsonAcceptedOutput {
        format: OUTPUT_FORMAT.to_owned(),
        status: "accepted".to_owned(),
        state: JsonState {
            history: expected_history,
        },
        active_world: JsonWorld::from(record.world()),
    };
    if decoded != expected {
        return Err(integrity(
            "PoA Lean response does not contain the exact durable prefix and final signed record",
        ));
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonWorld {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
}

impl From<&PoaWorldIdentityV2> for JsonWorld {
    fn from(world: &PoaWorldIdentityV2) -> Self {
        Self {
            federation_id: hex(&world.federation_id()),
            content_root: hex(&world.content_root()),
            activation_digest: hex(&world.activation_digest()),
            content_session: hex(&world.content_session()),
            content_epoch: world.content_epoch(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonStatement {
    schema: String,
    world: JsonWorld,
    counter: u64,
    predecessor_head: String,
    kind: String,
    rollback_target: Option<String>,
}

impl From<&PoaWorldActivationStatementV1> for JsonStatement {
    fn from(statement: &PoaWorldActivationStatementV1) -> Self {
        Self {
            schema: POA_WORLD_ACTIVATION_STATEMENT_SCHEMA_V1.to_owned(),
            world: JsonWorld::from(statement.world()),
            counter: statement.counter(),
            predecessor_head: hex(&statement.predecessor_head()),
            kind: statement.kind().label().to_owned(),
            rollback_target: statement.rollback_target().map(|digest| hex(&digest)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonEnvelope {
    statement: JsonStatement,
    curator_key: String,
    signature: String,
}

impl From<&SignedPoaWorldActivationEnvelopeV1> for JsonEnvelope {
    fn from(envelope: &SignedPoaWorldActivationEnvelopeV1) -> Self {
        Self {
            statement: JsonStatement::from(envelope.statement()),
            curator_key: hex(&envelope.curator_key()),
            signature: hex(envelope.signature()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonRecord {
    envelope: JsonEnvelope,
    envelope_digest: String,
}

impl From<&PoaWorldActivationRecordV1> for JsonRecord {
    fn from(record: &PoaWorldActivationRecordV1) -> Self {
        Self {
            envelope: JsonEnvelope::from(record.envelope()),
            envelope_digest: hex(&record.envelope_digest()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonState {
    history: Vec<JsonRecord>,
}

#[derive(Serialize)]
struct JsonInput {
    format: String,
    external_curator_key_pin: String,
    native_signature_verified: bool,
    state: JsonState,
    envelope: JsonEnvelope,
}

#[derive(Serialize)]
struct JsonAuthorityInput {
    format: String,
    external_curator_key_pin: String,
    native_signatures_verified: bool,
    state: JsonState,
    candidate: JsonWorld,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonAcceptedOutput {
    format: String,
    status: String,
    state: JsonState,
    active_world: JsonWorld,
}

fn validate_world(world: &PoaWorldIdentityV2) -> Result<()> {
    if world.federation_id() == [0; 32]
        || world.content_root() == [0; 32]
        || world.activation_digest() == [0; 32]
        || world.content_session() == [0; 32]
        || world.content_epoch() == 0
    {
        return Err(integrity("PoA active world contains a zero identity"));
    }
    Ok(())
}

fn validate_wire_component(bytes: &[u8], what: &str) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_LEAN_WIRE_BYTES {
        return Err(integrity(format!("{what} exceeds bound")));
    }
    Ok(())
}

fn encode_frame(value: &PreparedPoaWorldActivationV1) -> Result<Vec<u8>> {
    value.validate_components()?;
    let payload = postcard::to_stdvec(&StoredPreparedPoaWorldActivationV1::from(value))?;
    if payload.is_empty() || payload.len() > MAX_FRAME_BYTES {
        return Err(integrity("PoA activation frame exceeds bound"));
    }
    let payload_len = u32::try_from(payload.len())
        .map_err(|_| integrity("PoA activation frame length exceeds u32"))?;
    let mut frame = Vec::with_capacity(FRAME_HEADER_LEN + payload.len() + FRAME_SEAL_LEN);
    frame.extend_from_slice(&FRAME_MAGIC);
    frame.push(FRAME_VERSION);
    frame.extend_from_slice(&[0; 3]);
    frame.extend_from_slice(&payload_len.to_le_bytes());
    frame.extend_from_slice(&payload);
    frame.extend_from_slice(&sha256_domain(FRAME_DOMAIN, &frame));
    Ok(frame)
}

fn decode_frame(bytes: &[u8]) -> Result<PreparedPoaWorldActivationV1> {
    if bytes.len() < FRAME_HEADER_LEN + FRAME_SEAL_LEN {
        return Err(integrity("PoA activation frame is truncated"));
    }
    if bytes[..4] != FRAME_MAGIC || bytes[4] != FRAME_VERSION || bytes[5..8] != [0; 3] {
        return Err(integrity("PoA activation frame has wrong magic/version"));
    }
    let payload_len = u32::from_le_bytes(
        bytes[8..12]
            .try_into()
            .map_err(|_| integrity("PoA activation frame length is malformed"))?,
    ) as usize;
    let expected = FRAME_HEADER_LEN
        .checked_add(payload_len)
        .and_then(|length| length.checked_add(FRAME_SEAL_LEN))
        .ok_or_else(|| integrity("PoA activation frame length overflow"))?;
    if payload_len == 0 || payload_len > MAX_FRAME_BYTES || expected != bytes.len() {
        return Err(integrity("PoA activation frame length mismatch"));
    }
    let payload_end = bytes.len() - FRAME_SEAL_LEN;
    if sha256_domain(FRAME_DOMAIN, &bytes[..payload_end]) != bytes[payload_end..] {
        return Err(integrity("PoA activation frame seal mismatch"));
    }
    let payload = &bytes[FRAME_HEADER_LEN..payload_end];
    let stored: StoredPreparedPoaWorldActivationV1 = postcard::from_bytes(payload)?;
    if postcard::to_stdvec(&stored)? != payload {
        return Err(integrity("PoA activation frame is not canonical"));
    }
    let decoded = stored.into_prepared();
    decoded.validate_components()?;
    Ok(decoded)
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    out
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn sha256_domain(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    hasher.finalize().into()
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_lean_ffi::poa_world_activation_ffi::poa_world_activation_available;
    use ed25519_dalek::{Signer, SigningKey};
    use tempfile::tempdir;

    fn signing_key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn world(epoch: u64, root: u8, activation: u8, session: u8) -> PoaWorldIdentityV2 {
        PoaWorldIdentityV2::new([1; 32], [root; 32], [activation; 32], [session; 32], epoch)
            .unwrap()
    }

    fn signed(
        key: &SigningKey,
        world: PoaWorldIdentityV2,
        counter: u64,
        predecessor: [u8; 32],
        kind: PoaWorldActivationKindV1,
        rollback_target: Option<[u8; 32]>,
    ) -> SignedPoaWorldActivationEnvelopeV1 {
        let statement =
            PoaWorldActivationStatementV1::new(world, counter, predecessor, kind, rollback_target)
                .unwrap();
        let signature = key.sign(&statement.signing_message().unwrap()).to_bytes();
        SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            key.verifying_key().to_bytes(),
            signature,
        )
        .unwrap()
    }

    fn prepare(
        store: &PersistentStore,
        pin: [u8; 32],
        envelope: SignedPoaWorldActivationEnvelopeV1,
    ) -> PreparedPoaWorldActivationV1 {
        store.install_poa_world_curator_pin_v1(pin).unwrap();
        store.prepare_poa_world_activation_v1(envelope).unwrap()
    }

    fn stage(store: &PersistentStore, candidate: &PreparedPoaWorldActivationV1) -> Result<()> {
        let write = store.db.begin_write()?;
        stage_fresh_poa_world_activation_in(&write, candidate)?;
        write.commit()?;
        Ok(())
    }

    fn require_native() -> bool {
        poa_world_activation_available()
    }

    #[test]
    fn signing_message_is_exact_canonical_lean_statement_wire() {
        let statement = PoaWorldActivationStatementV1::new(
            world(4, 10, 11, 12),
            4,
            [0; 32],
            PoaWorldActivationKindV1::Advance,
            None,
        )
        .unwrap();
        let text = String::from_utf8(statement.signing_message().unwrap()).unwrap();
        assert_eq!(
            text,
            format!(
                "{{\"schema\":\"POA-WORLD-ACTIVATION-STATEMENT-1\",\"world\":{{\"federation_id\":\"{}\",\"content_root\":\"{}\",\"activation_digest\":\"{}\",\"content_session\":\"{}\",\"content_epoch\":4}},\"counter\":4,\"predecessor_head\":\"{}\",\"kind\":\"advance\",\"rollback_target\":null}}",
                "01".repeat(32),
                "0a".repeat(32),
                "0b".repeat(32),
                "0c".repeat(32),
                "00".repeat(32),
            )
        );
    }

    #[test]
    fn no_installed_pin_or_activation_refuses_all_authority_paths() {
        let store = PersistentStore::open_in_memory().unwrap();
        let key = signing_key(5);
        let envelope = signed(
            &key,
            world(1, 10, 11, 12),
            1,
            [0; 32],
            PoaWorldActivationKindV1::Advance,
            None,
        );
        assert!(
            store
                .prepare_poa_world_activation_v1(envelope.clone())
                .is_err()
        );
        assert!(store.install_poa_world_activation_v1(envelope).is_err());
        assert!(store.audit_poa_world_activation_v1().is_err());
        let write = store.db.begin_write().unwrap();
        assert!(require_poa_active_world_exact_in(&write, &world(1, 10, 11, 12)).is_err());
        write.abort().unwrap();
    }

    #[test]
    fn malformed_curator_pin_table_cannot_be_normalized_by_installation() {
        let store = PersistentStore::open_in_memory().unwrap();
        let write = store.db.begin_write().unwrap();
        initialize_poa_world_activation_tables_v1_in(&write).unwrap();
        {
            let mut pins = write.open_table(POA_WORLD_CURATOR_PIN_V1).unwrap();
            pins.insert("unexpected", [0xA5; 32].as_slice()).unwrap();
        }
        write.commit().unwrap();

        let key = signing_key(14);
        assert!(
            store
                .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
                .is_err()
        );
        assert!(store.load_poa_world_curator_pin_v1().is_err());
    }

    #[test]
    fn atomic_install_and_exact_retry_are_idempotent_but_wrong_world_refuses() {
        if !require_native() {
            return;
        }
        let store = PersistentStore::open_in_memory().unwrap();
        let key = signing_key(13);
        let pin = key.verifying_key().to_bytes();
        store.install_poa_world_curator_pin_v1(pin).unwrap();
        let envelope = signed(
            &key,
            world(4, 10, 11, 12),
            4,
            [0; 32],
            PoaWorldActivationKindV1::Advance,
            None,
        );
        let installed = store
            .install_poa_world_activation_v1(envelope.clone())
            .unwrap();
        assert_eq!(
            installed.status(),
            PoaWorldActivationInstallStatusV1::Installed
        );
        let retry = store.install_poa_world_activation_v1(envelope).unwrap();
        assert_eq!(
            retry.status(),
            PoaWorldActivationInstallStatusV1::AlreadyRecorded
        );
        assert_eq!(
            installed.active_head().cas_bytes(),
            retry.active_head().cas_bytes()
        );
        let write = store.db.begin_write().unwrap();
        require_poa_active_world_exact_in(&write, installed.active_head().world()).unwrap();
        assert!(require_poa_active_world_exact_in(&write, &world(4, 99, 11, 12)).is_err());
        write.abort().unwrap();
    }

    #[test]
    fn absent_native_export_refuses_preparation_without_a_rust_twin() {
        if require_native() {
            return;
        }
        let store = PersistentStore::open_in_memory().unwrap();
        let key = signing_key(6);
        let pin = key.verifying_key().to_bytes();
        store.install_poa_world_curator_pin_v1(pin).unwrap();
        assert!(
            store
                .prepare_poa_world_activation_v1(signed(
                    &key,
                    world(4, 10, 11, 12),
                    4,
                    [0; 32],
                    PoaWorldActivationKindV1::Advance,
                    None,
                ),)
                .is_err()
        );
    }

    #[test]
    fn signed_successor_is_durable_and_exact_world_check_is_in_transaction() {
        if !require_native() {
            return;
        }
        let store = PersistentStore::open_in_memory().unwrap();
        let key = signing_key(7);
        let pin = key.verifying_key().to_bytes();
        let bootstrap = prepare(
            &store,
            pin,
            signed(
                &key,
                world(4, 10, 11, 12),
                4,
                [0; 32],
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        stage(&store, &bootstrap).unwrap();
        let successor = prepare(
            &store,
            pin,
            signed(
                &key,
                world(5, 20, 21, 22),
                5,
                bootstrap.record.envelope_digest(),
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        stage(&store, &successor).unwrap();
        store.audit_poa_world_activation_v1().unwrap();

        let head = store.load_poa_active_world_v1().unwrap().unwrap();
        assert_eq!(head.counter(), 5);
        assert_eq!(head.world(), successor.record.world());
        let write = store.db.begin_write().unwrap();
        require_poa_active_world_exact_in(&write, successor.record.world()).unwrap();
        assert!(require_poa_active_world_exact_in(&write, bootstrap.record.world()).is_err());
        assert_eq!(
            require_poa_historical_world_exact_in(&write, bootstrap.record.world()).unwrap(),
            bootstrap.record.counter()
        );
        assert_eq!(
            require_poa_historical_world_exact_in(&write, successor.record.world()).unwrap(),
            successor.record.counter()
        );
        assert!(require_poa_historical_world_exact_in(&write, &world(4, 99, 98, 97)).is_err());
        verify_replayed_poa_world_activation_in(&write, &bootstrap).unwrap();
        write.abort().unwrap();
    }

    #[test]
    fn stale_preparation_full_byte_cas_counter_skip_and_stale_epoch_refuse() {
        if !require_native() {
            return;
        }
        let store = PersistentStore::open_in_memory().unwrap();
        let key = signing_key(8);
        let pin = key.verifying_key().to_bytes();
        let bootstrap = prepare(
            &store,
            pin,
            signed(
                &key,
                world(4, 10, 11, 12),
                4,
                [0; 32],
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        stage(&store, &bootstrap).unwrap();
        let successor_a = prepare(
            &store,
            pin,
            signed(
                &key,
                world(5, 20, 21, 22),
                5,
                bootstrap.record.envelope_digest(),
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        let successor_b = prepare(
            &store,
            pin,
            signed(
                &key,
                world(5, 30, 31, 32),
                5,
                bootstrap.record.envelope_digest(),
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        stage(&store, &successor_a).unwrap();
        assert!(stage(&store, &successor_b).is_err());

        assert!(
            store
                .prepare_poa_world_activation_v1(signed(
                    &key,
                    world(7, 40, 41, 42),
                    7,
                    successor_a.record.envelope_digest(),
                    PoaWorldActivationKindV1::Advance,
                    None,
                ),)
                .is_err()
        );
        assert!(
            store
                .prepare_poa_world_activation_v1(signed(
                    &key,
                    world(5, 40, 41, 42),
                    6,
                    successor_a.record.envelope_digest(),
                    PoaWorldActivationKindV1::Advance,
                    None,
                ),)
                .is_err()
        );
    }

    #[test]
    fn native_signature_and_external_key_substitution_refuse_before_lean_authority() {
        let store = PersistentStore::open_in_memory().unwrap();
        let honest = signing_key(9);
        let attacker = signing_key(10);
        let pin = honest.verifying_key().to_bytes();
        store.install_poa_world_curator_pin_v1(pin).unwrap();
        assert!(
            store
                .install_poa_world_curator_pin_v1(attacker.verifying_key().to_bytes())
                .is_err()
        );
        assert!(
            store
                .prepare_poa_world_activation_v1(signed(
                    &attacker,
                    world(1, 10, 11, 12),
                    1,
                    [0; 32],
                    PoaWorldActivationKindV1::Advance,
                    None,
                ),)
                .is_err()
        );

        let mut bad_signature = signed(
            &honest,
            world(1, 10, 11, 12),
            1,
            [0; 32],
            PoaWorldActivationKindV1::Advance,
            None,
        );
        bad_signature.signature[0] ^= 1;
        assert!(
            store
                .prepare_poa_world_activation_v1(bad_signature)
                .is_err()
        );
        assert!(store.load_poa_active_world_v1().unwrap().is_none());
    }

    #[test]
    fn rollback_requires_recorded_digest_and_exact_target_world() {
        if !require_native() {
            return;
        }
        let store = PersistentStore::open_in_memory().unwrap();
        let key = signing_key(11);
        let pin = key.verifying_key().to_bytes();
        let bootstrap = prepare(
            &store,
            pin,
            signed(
                &key,
                world(4, 10, 11, 12),
                4,
                [0; 32],
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        stage(&store, &bootstrap).unwrap();
        let successor = prepare(
            &store,
            pin,
            signed(
                &key,
                world(5, 20, 21, 22),
                5,
                bootstrap.record.envelope_digest(),
                PoaWorldActivationKindV1::Advance,
                None,
            ),
        );
        stage(&store, &successor).unwrap();

        assert!(
            store
                .prepare_poa_world_activation_v1(signed(
                    &key,
                    bootstrap.record.world().clone(),
                    6,
                    successor.record.envelope_digest(),
                    PoaWorldActivationKindV1::Rollback,
                    Some([99; 32]),
                ),)
                .is_err()
        );
        assert!(
            store
                .prepare_poa_world_activation_v1(signed(
                    &key,
                    world(4, 99, 11, 12),
                    6,
                    successor.record.envelope_digest(),
                    PoaWorldActivationKindV1::Rollback,
                    Some(bootstrap.record.envelope_digest()),
                ),)
                .is_err()
        );

        let rollback = prepare(
            &store,
            pin,
            signed(
                &key,
                bootstrap.record.world().clone(),
                6,
                successor.record.envelope_digest(),
                PoaWorldActivationKindV1::Rollback,
                Some(bootstrap.record.envelope_digest()),
            ),
        );
        stage(&store, &rollback).unwrap();
        assert_eq!(
            store.load_poa_active_world_v1().unwrap().unwrap().world(),
            bootstrap.record.world()
        );
    }

    #[test]
    fn reopen_reinvokes_lean_and_truncation_corruption_or_evidence_tamper_refuses() {
        if !require_native() {
            return;
        }
        let dir = tempdir().unwrap();
        let path = dir.path().join("world.redb");
        let key = signing_key(12);
        let pin = key.verifying_key().to_bytes();
        {
            let store = PersistentStore::open(&path).unwrap();
            let bootstrap = prepare(
                &store,
                pin,
                signed(
                    &key,
                    world(4, 10, 11, 12),
                    4,
                    [0; 32],
                    PoaWorldActivationKindV1::Advance,
                    None,
                ),
            );
            stage(&store, &bootstrap).unwrap();
            store.audit_poa_world_activation_v1().unwrap();
        }
        let store = PersistentStore::open(&path).unwrap();
        store.audit_poa_world_activation_v1().unwrap();

        let original = store
            .load_poa_active_world_v1()
            .unwrap()
            .unwrap()
            .cas_bytes()
            .to_vec();
        let write = store.db.begin_write().unwrap();
        {
            let mut heads = write.open_table(POA_WORLD_ACTIVATION_HEAD_V1).unwrap();
            heads
                .insert(HEAD_KEY, &original[..original.len() - 1])
                .unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_world_activation_v1().is_err());

        let mut evidence_tamper = decode_frame(&original).unwrap();
        evidence_tamper.lean_response.push(b' ');
        evidence_tamper.lean_response_digest = sha256(&evidence_tamper.lean_response);
        let validly_resealed_tamper = encode_frame(&evidence_tamper).unwrap();
        let write = store.db.begin_write().unwrap();
        {
            let mut heads = write.open_table(POA_WORLD_ACTIVATION_HEAD_V1).unwrap();
            heads
                .insert(HEAD_KEY, validly_resealed_tamper.as_slice())
                .unwrap();
            let mut history = write.open_table(POA_WORLD_ACTIVATION_HISTORY_V1).unwrap();
            history
                .insert(4, validly_resealed_tamper.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        assert!(store.audit_poa_world_activation_v1().is_err());
    }
}
