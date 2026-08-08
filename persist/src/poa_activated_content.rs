//! Restart-safe, exact activated-content authority for Path of Angels.
//!
//! The signed active-world lineage remains owned by `poa_world_activation`. While holding one
//! redb writer, this module fully audits that lineage, asks Lean to bind an exact canonical
//! manifest to that all-five-field world, then seals the exact request material and Lean response.
//! Loading replays both authorities. No Rust code implements manifest membership or Galley policy
//! semantics, and no deserializable type can manufacture gameplay policy authority.

use dregg_lean_ffi::poa_activated_content_ffi::{
    MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES, PoaActivatedContentVerdict,
    authorize_poa_activated_content,
};
use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::poa_world_activation::{
    require_poa_active_world_exact_in, require_poa_historical_world_exact_in,
};
use crate::{PersistentStore, PoaWorldIdentityV2, Result, StoreError};

pub(crate) const POA_ACTIVATED_CONTENT_V1: TableDefinition<&[u8], &[u8]> =
    TableDefinition::new("poa_activated_content_v1");

const INPUT_FORMAT: &str = "POA-ACTIVATED-CONTENT-IN-1";
const OUTPUT_FORMAT: &str = "POA-ACTIVATED-CONTENT-OUT-1";
const FRAME_MAGIC: [u8; 4] = *b"PAC1";
const FRAME_VERSION: u8 = 1;
const FRAME_HEADER_LEN: usize = 9;
const FRAME_SEAL_LEN: usize = 32;
const FRAME_DOMAIN: &[u8] = b"dregg-poa-activated-content-frame-v1\0";
const WORLD_KEY_LEN: usize = 32 * 4 + 8;
const MAX_MANIFEST_BYTES: usize = 1024 * 1024;
const MAX_FRAME_BYTES: usize = 8 * 1024 * 1024;
const MAX_RECORDS: u64 = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaActivatedContentInstallStatusV1 {
    Installed,
    AlreadyInstalled,
}

/// An opaque, non-serializable report about a successful exact install.
#[derive(Debug, PartialEq, Eq)]
pub struct PoaActivatedContentInstallOutcomeV1 {
    status: PoaActivatedContentInstallStatusV1,
    world: PoaWorldIdentityV2,
    component_sha256: [u8; 32],
}

impl PoaActivatedContentInstallOutcomeV1 {
    pub const fn status(&self) -> PoaActivatedContentInstallStatusV1 {
        self.status
    }

    pub const fn world(&self) -> &PoaWorldIdentityV2 {
        &self.world
    }

    pub const fn component_sha256(&self) -> [u8; 32] {
        self.component_sha256
    }
}

/// The only persistence-side evidence from which Galley gameplay policy authority may be made.
/// Fields are private; the type implements neither `Clone` nor serde traits. Its sole producer
/// performs a same-writer active-world audit and exact Lean replay from the sealed manifest.
#[derive(Debug)]
pub(crate) struct PreparedPoaActivatedGalleyPolicyV1 {
    world: PoaWorldIdentityV2,
    policy_json: Vec<u8>,
    genesis_projection_json: Vec<u8>,
    manifest_root: [u8; 32],
    component_sha256: [u8; 32],
}

impl PreparedPoaActivatedGalleyPolicyV1 {
    pub(crate) fn into_parts(self) -> (PoaWorldIdentityV2, Vec<u8>, Vec<u8>, [u8; 32], [u8; 32]) {
        (
            self.world,
            self.policy_json,
            self.genesis_projection_json,
            self.manifest_root,
            self.component_sha256,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct StoredActivatedContentV1 {
    world: PoaWorldIdentityV2,
    manifest_json: Vec<u8>,
    lean_response: Vec<u8>,
}

#[derive(Serialize)]
struct JsonInput<'a> {
    format: &'static str,
    world: JsonWorld,
    manifest_json: &'a str,
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
struct JsonOutput {
    format: String,
    world: JsonWorld,
    manifest_root: String,
    component_sha256: String,
    policy_json: String,
    genesis_projection_json: String,
}

struct AuthorizedContent {
    response: Vec<u8>,
    component_sha256: [u8; 32],
    policy_json: Vec<u8>,
    genesis_projection_json: Vec<u8>,
}

pub(crate) fn initialize_poa_activated_content_tables_v1_in(
    write: &WriteTransaction,
) -> Result<()> {
    let _ = write.open_table(POA_ACTIVATED_CONTENT_V1)?;
    Ok(())
}

fn prepare_poa_galley_policy_for_world_v1_in(
    write: &WriteTransaction,
    world: PoaWorldIdentityV2,
    require_current: bool,
) -> Result<PreparedPoaActivatedGalleyPolicyV1> {
    initialize_poa_activated_content_tables_v1_in(write)?;
    if require_current {
        require_poa_active_world_exact_in(write, &world)?;
    } else {
        require_poa_historical_world_exact_in(write, &world)?;
    }
    let key = world_key(&world);
    let frame = {
        let table = write.open_table(POA_ACTIVATED_CONTENT_V1)?;
        table
            .get(key.as_slice())?
            .ok_or_else(|| integrity("PoA world has no installed content manifest"))?
            .value()
            .to_vec()
    };
    let stored = decode_frame(&frame)?;
    if stored.world != world {
        return Err(integrity("PoA activated-content row changed worlds"));
    }
    let authorized = audit_stored(&stored)?;
    Ok(PreparedPoaActivatedGalleyPolicyV1 {
        manifest_root: world.content_root(),
        world,
        policy_json: authorized.policy_json,
        genesis_projection_json: authorized.genesis_projection_json,
        component_sha256: authorized.component_sha256,
    })
}

/// Derive the current world's exact Galley policy beneath the caller's writer
/// snapshot. No world, manifest bytes, policy JSON, or approval bit comes from
/// the caller.
pub(crate) fn prepare_active_poa_galley_policy_v1_in(
    write: &WriteTransaction,
) -> Result<PreparedPoaActivatedGalleyPolicyV1> {
    let world = crate::poa_world_activation::load_poa_active_world_exact_in(write)?;
    prepare_poa_galley_policy_for_world_v1_in(write, world, true)
}

/// Replay counterpart for a batch already durably committed under an earlier
/// signed world. The exact historical world comes from the stored batch.
pub(crate) fn prepare_historical_poa_galley_policy_v1_in(
    write: &WriteTransaction,
    world: &PoaWorldIdentityV2,
) -> Result<PreparedPoaActivatedGalleyPolicyV1> {
    prepare_poa_galley_policy_for_world_v1_in(write, world.clone(), false)
}

impl PersistentStore {
    /// Install one exact canonical manifest for the currently active world. An identical retry is
    /// idempotent; any different bytes under the same all-five-field world are an integrity error.
    pub fn install_poa_activated_content_v1(
        &self,
        manifest_json: Vec<u8>,
    ) -> Result<PoaActivatedContentInstallOutcomeV1> {
        validate_manifest_transport(&manifest_json)?;
        let active = self
            .load_poa_active_world_v1()?
            .ok_or_else(|| integrity("PoA activated content requires an active world"))?;
        let world = active.world().clone();

        let write = self.db.begin_write()?;
        initialize_poa_activated_content_tables_v1_in(&write)?;
        require_poa_active_world_exact_in(&write, &world)?;
        let authorized = authorize_exact(&world, &manifest_json)?;
        let stored = StoredActivatedContentV1 {
            world: world.clone(),
            manifest_json,
            lean_response: authorized.response,
        };
        let frame = encode_frame(&stored)?;
        let key = world_key(&world);
        let status = {
            let mut table = write.open_table(POA_ACTIVATED_CONTENT_V1)?;
            let existing = table
                .get(key.as_slice())?
                .map(|guard| guard.value().to_vec());
            match existing.as_deref() {
                Some(existing) if existing == frame.as_slice() => {
                    PoaActivatedContentInstallStatusV1::AlreadyInstalled
                }
                Some(_) => {
                    return Err(integrity(
                        "PoA activated-content exact retry differs from installed bytes",
                    ));
                }
                None => {
                    table.insert(key.as_slice(), frame.as_slice())?;
                    PoaActivatedContentInstallStatusV1::Installed
                }
            }
        };
        write.commit()?;
        Ok(PoaActivatedContentInstallOutcomeV1 {
            status,
            world,
            component_sha256: authorized.component_sha256,
        })
    }

    /// Reopen audit: for every row, verify key/frame canonicality, replay the authenticated
    /// historical world, reinvoke Lean, and require the exact sealed response.
    pub fn audit_poa_activated_content_v1(&self) -> Result<()> {
        let write = self.db.begin_write()?;
        initialize_poa_activated_content_tables_v1_in(&write)?;
        let rows = {
            let table = write.open_table(POA_ACTIVATED_CONTENT_V1)?;
            if table.len()? > MAX_RECORDS {
                return Err(integrity("PoA activated-content table exceeds audit bound"));
            }
            let mut rows = Vec::with_capacity(table.len()? as usize);
            for entry in table.iter()? {
                let (key, value) = entry?;
                rows.push((key.value().to_vec(), value.value().to_vec()));
            }
            rows
        };
        for (key, frame) in rows {
            let stored = decode_frame(&frame)?;
            if key != world_key(&stored.world) {
                return Err(integrity("PoA activated-content world key mismatch"));
            }
            require_poa_historical_world_exact_in(&write, &stored.world)?;
            audit_stored(&stored)?;
        }
        write.abort()?;
        Ok(())
    }

    /// Load the active world's exact Galley member as an unforgeable prepared carrier. The caller
    /// can only turn this into `AuthenticatedPoaGalleyPolicyV1` through the narrow Galley adapter.
    pub(crate) fn prepare_active_poa_galley_policy_v1(
        &self,
    ) -> Result<PreparedPoaActivatedGalleyPolicyV1> {
        let write = self.db.begin_write()?;
        let prepared = prepare_active_poa_galley_policy_v1_in(&write)?;
        write.abort()?;
        Ok(prepared)
    }

    /// Public authority-producing entry point. Callers receive a sealed policy carrier, never
    /// manifest bytes, an `audited` bit, or a constructor accepting raw policy JSON.
    pub fn load_authenticated_poa_galley_policy_v1(
        &self,
    ) -> Result<crate::poa_galley_authority::AuthenticatedPoaGalleyPolicyV1> {
        crate::poa_galley_authority::AuthenticatedPoaGalleyPolicyV1::from_activated_content(
            self.prepare_active_poa_galley_policy_v1()?,
        )
    }
}

fn audit_stored(stored: &StoredActivatedContentV1) -> Result<AuthorizedContent> {
    validate_manifest_transport(&stored.manifest_json)?;
    let authorized = authorize_exact(&stored.world, &stored.manifest_json)?;
    if authorized.response != stored.lean_response {
        return Err(integrity(
            "PoA activated-content Lean response changed during durable reaudit",
        ));
    }
    Ok(authorized)
}

fn authorize_exact(world: &PoaWorldIdentityV2, manifest_json: &[u8]) -> Result<AuthorizedContent> {
    let manifest = std::str::from_utf8(manifest_json)
        .map_err(|_| integrity("PoA activated-content manifest is not UTF-8"))?;
    let input = JsonInput {
        format: INPUT_FORMAT,
        world: JsonWorld::from(world),
        manifest_json: manifest,
    };
    let input_bytes = serde_json::to_vec(&input)
        .map_err(|error| integrity(format!("PoA activated-content input JSON failed: {error}")))?;
    if input_bytes.len() > MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES {
        return Err(integrity("PoA activated-content input exceeds wire bound"));
    }
    let input_text = std::str::from_utf8(&input_bytes)
        .map_err(|_| integrity("PoA activated-content input is not UTF-8"))?;
    let response = match authorize_poa_activated_content(input_text).map_err(|error| {
        integrity(format!(
            "PoA activated-content Lean authority failed: {error}"
        ))
    })? {
        PoaActivatedContentVerdict::Rejected => {
            return Err(integrity(
                "PoA activated-content manifest was rejected by Lean",
            ));
        }
        PoaActivatedContentVerdict::Authorized(authority) => authority.as_str().as_bytes().to_vec(),
    };
    let output: JsonOutput = serde_json::from_slice(&response).map_err(|error| {
        integrity(format!(
            "PoA activated-content response is not canonical output: {error}"
        ))
    })?;
    if serde_json::to_vec(&output).map_err(|error| {
        integrity(format!(
            "PoA activated-content output reencode failed: {error}"
        ))
    })? != response
    {
        return Err(integrity("PoA activated-content response is noncanonical"));
    }
    if output.format != OUTPUT_FORMAT || output.world != JsonWorld::from(world) {
        return Err(integrity(
            "PoA activated-content response changed format or all-five-field world",
        ));
    }
    let manifest_root = parse_hex32(&output.manifest_root, "manifest root")?;
    if manifest_root != world.content_root() {
        return Err(integrity(
            "PoA activated-content response root differs from active world",
        ));
    }
    let component_sha256 = parse_hex32(&output.component_sha256, "component digest")?;
    if output.policy_json.is_empty() || output.genesis_projection_json.is_empty() {
        return Err(integrity(
            "PoA activated-content response omitted policy or genesis projection",
        ));
    }
    Ok(AuthorizedContent {
        response,
        component_sha256,
        policy_json: output.policy_json.into_bytes(),
        genesis_projection_json: output.genesis_projection_json.into_bytes(),
    })
}

fn validate_manifest_transport(bytes: &[u8]) -> Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_MANIFEST_BYTES {
        return Err(integrity(
            "PoA activated-content manifest is empty or exceeds 1 MiB",
        ));
    }
    std::str::from_utf8(bytes)
        .map_err(|_| integrity("PoA activated-content manifest is not UTF-8"))?;
    Ok(())
}

fn world_key(world: &PoaWorldIdentityV2) -> [u8; WORLD_KEY_LEN] {
    let mut key = [0u8; WORLD_KEY_LEN];
    key[..32].copy_from_slice(&world.federation_id());
    key[32..64].copy_from_slice(&world.content_root());
    key[64..96].copy_from_slice(&world.activation_digest());
    key[96..128].copy_from_slice(&world.content_session());
    key[128..].copy_from_slice(&world.content_epoch().to_be_bytes());
    key
}

fn encode_frame(value: &StoredActivatedContentV1) -> Result<Vec<u8>> {
    let payload = postcard::to_stdvec(value)?;
    let payload_len: u32 = payload
        .len()
        .try_into()
        .map_err(|_| integrity("PoA activated-content frame payload exceeds u32"))?;
    let mut frame = Vec::with_capacity(FRAME_HEADER_LEN + payload.len() + FRAME_SEAL_LEN);
    frame.extend_from_slice(&FRAME_MAGIC);
    frame.push(FRAME_VERSION);
    frame.extend_from_slice(&payload_len.to_be_bytes());
    frame.extend_from_slice(&payload);
    let seal = sha256_domain(FRAME_DOMAIN, &frame);
    frame.extend_from_slice(&seal);
    if frame.len() > MAX_FRAME_BYTES {
        return Err(integrity("PoA activated-content frame exceeds bound"));
    }
    Ok(frame)
}

fn decode_frame(frame: &[u8]) -> Result<StoredActivatedContentV1> {
    if frame.len() > MAX_FRAME_BYTES
        || frame.len() < FRAME_HEADER_LEN + FRAME_SEAL_LEN
        || frame[..4] != FRAME_MAGIC
        || frame[4] != FRAME_VERSION
    {
        return Err(integrity("PoA activated-content frame header is invalid"));
    }
    let payload_len = u32::from_be_bytes(
        frame[5..9]
            .try_into()
            .map_err(|_| integrity("PoA activated-content frame length is invalid"))?,
    ) as usize;
    let expected = FRAME_HEADER_LEN
        .checked_add(payload_len)
        .and_then(|length| length.checked_add(FRAME_SEAL_LEN))
        .ok_or_else(|| integrity("PoA activated-content frame length overflow"))?;
    if frame.len() != expected {
        return Err(integrity("PoA activated-content frame length mismatch"));
    }
    let seal_offset = expected - FRAME_SEAL_LEN;
    if sha256_domain(FRAME_DOMAIN, &frame[..seal_offset]) != frame[seal_offset..] {
        return Err(integrity("PoA activated-content frame seal mismatch"));
    }
    let payload = &frame[FRAME_HEADER_LEN..seal_offset];
    let stored: StoredActivatedContentV1 = postcard::from_bytes(payload)?;
    if postcard::to_stdvec(&stored)? != payload {
        return Err(integrity(
            "PoA activated-content frame payload is noncanonical",
        ));
    }
    Ok(stored)
}

fn parse_hex32(value: &str, label: &str) -> Result<[u8; 32]> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(integrity(format!(
            "PoA activated-content {label} is not lowercase hex32"
        )));
    }
    let mut output = [0u8; 32];
    for (index, chunk) in value.as_bytes().chunks_exact(2).enumerate() {
        output[index] = (hex_nibble(chunk[0]).expect("validated hex") << 4)
            | hex_nibble(chunk[1]).expect("validated hex");
    }
    Ok(output)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn hex(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for byte in bytes {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
    output
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
    use crate::{
        PoaWorldActivationKindV1, PoaWorldActivationStatementV1, SignedPoaWorldActivationEnvelopeV1,
    };
    use dregg_lean_ffi::poa_activated_content_ffi::poa_activated_content_runtime_available;
    use dregg_lean_ffi::poa_world_activation_ffi::poa_world_activation_available;
    use ed25519_dalek::{Signer, SigningKey};
    use tempfile::tempdir;

    fn h(byte: u8) -> String {
        format!("{byte:02x}").repeat(32)
    }

    fn policy_json(federation: u8, epoch: u64, dregg_mint: u64) -> String {
        format!(
            concat!(
                "{{\"deployment_id\":\"{}\",\"federation_id\":\"{}\",",
                "\"daily_id\":\"{}\",\"genesis_head\":\"{}\",\"dregg_mint\":{},",
                "\"snapshot_slot\":14,\"content_epoch\":{},\"event_id\":\"{}\",",
                "\"rules_digest\":\"{}\",\"public_activity_id\":\"{}\",",
                "\"scene_content_id\":\"{}\",\"public_action_content_id\":\"{}\",",
                "\"sponsor_action_content_id\":\"{}\",\"complete_content_id\":\"{}\",",
                "\"public_service\":3,\"sponsor_service\":2,\"service_target\":12,",
                "\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",",
                "\"canon_revision\":1}}"
            ),
            h(10),
            h(federation),
            h(11),
            h(12),
            dregg_mint,
            epoch,
            h(15),
            h(16),
            h(17),
            h(18),
            h(19),
            h(20),
            h(21),
            h(22),
            h(23),
            h(24),
        )
    }

    fn manifest_json(federation: u8, session: u8, epoch: u64, policy: &str) -> Vec<u8> {
        let component_digest: [u8; 32] = Sha256::digest(policy.as_bytes()).into();
        let quoted_policy = serde_json::to_string(policy).unwrap();
        format!(
            concat!(
                "{{\"format\":\"POA-ACTIVATED-CONTENT-MANIFEST-1\",",
                "\"scope\":{{\"federation_id\":\"{}\",\"content_session\":\"{}\",",
                "\"content_epoch\":{}}},\"legacy_whole_pack_sha256\":null,",
                "\"components\":[{{\"name\":\"poa.galley-maintenance-daily.policy.v1\",",
                "\"sha256\":\"{}\",\"bytes_utf8\":{}}}]}}"
            ),
            h(federation),
            h(session),
            epoch,
            hex(&component_digest),
            quoted_policy,
        )
        .into_bytes()
    }

    fn world_for_manifest(
        manifest: &[u8],
        activation: u8,
        session: u8,
        epoch: u64,
    ) -> PoaWorldIdentityV2 {
        PoaWorldIdentityV2::new(
            [1; 32],
            Sha256::digest(manifest).into(),
            [activation; 32],
            [session; 32],
            epoch,
        )
        .unwrap()
    }

    fn signed(
        key: &SigningKey,
        world: PoaWorldIdentityV2,
        counter: u64,
        predecessor: [u8; 32],
    ) -> SignedPoaWorldActivationEnvelopeV1 {
        let statement = PoaWorldActivationStatementV1::new(
            world,
            counter,
            predecessor,
            PoaWorldActivationKindV1::Advance,
            None,
        )
        .unwrap();
        let signature = key.sign(&statement.signing_message().unwrap()).to_bytes();
        SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            key.verifying_key().to_bytes(),
            signature,
        )
        .unwrap()
    }

    /// ⚑ **ARMED GUARD** (2026-08-08) — see `poa_world_activation::tests::require_native`. Absent
    /// export ⇒ PANIC naming the capability, never a silent `return` that prints `ok`.
    fn native_available() -> bool {
        dregg_lean_ffi::demand_lean(
            poa_world_activation_available() && poa_activated_content_runtime_available(),
            "the PoA activated-content runtime (world-activation + activated-content)",
        )
    }

    #[test]
    fn no_active_world_refuses_before_content_can_confer_authority() {
        let store = PersistentStore::open_in_memory().unwrap();
        let policy = policy_json(1, 1, 13);
        let manifest = manifest_json(1, 2, 1, &policy);
        assert!(store.install_poa_activated_content_v1(manifest).is_err());
        assert!(store.prepare_active_poa_galley_policy_v1().is_err());
    }

    #[test]
    fn exact_install_retry_restart_and_hostile_substitutions() {
        if !native_available() {
            return;
        }
        let directory = tempdir().unwrap();
        let path = directory.path().join("poa-content.redb");
        let key = SigningKey::from_bytes(&[41; 32]);
        let policy = policy_json(1, 1, 13);
        let manifest = manifest_json(1, 2, 1, &policy);
        let world = world_for_manifest(&manifest, 3, 2, 1);

        {
            let store = PersistentStore::open(&path).unwrap();
            store
                .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
                .unwrap();
            store
                .install_poa_world_activation_v1(signed(&key, world.clone(), 1, [0; 32]))
                .unwrap();
            let installed = store
                .install_poa_activated_content_v1(manifest.clone())
                .unwrap();
            assert_eq!(
                installed.status(),
                PoaActivatedContentInstallStatusV1::Installed
            );
            assert_eq!(installed.world(), &world);
            let retry = store
                .install_poa_activated_content_v1(manifest.clone())
                .unwrap();
            assert_eq!(
                retry.status(),
                PoaActivatedContentInstallStatusV1::AlreadyInstalled
            );

            let mut trailing = manifest.clone();
            trailing.push(b' ');
            assert!(store.install_poa_activated_content_v1(trailing).is_err());

            let stale_digest = String::from_utf8(manifest.clone())
                .unwrap()
                .replace("\\\"dregg_mint\\\":13", "\\\"dregg_mint\\\":14")
                .into_bytes();
            assert_ne!(stale_digest, manifest);
            assert!(
                store
                    .install_poa_activated_content_v1(stale_digest)
                    .is_err()
            );

            let rehashed_policy = policy_json(1, 1, 14);
            let rehashed_manifest = manifest_json(1, 2, 1, &rehashed_policy);
            assert!(
                store
                    .install_poa_activated_content_v1(rehashed_manifest)
                    .is_err()
            );

            let prepared = store.prepare_active_poa_galley_policy_v1().unwrap();
            let (prepared_world, prepared_policy, projection, root, component_digest) =
                prepared.into_parts();
            assert_eq!(prepared_world, world);
            assert_eq!(prepared_policy, policy.as_bytes());
            assert!(!projection.is_empty());
            assert_eq!(root, world.content_root());
            let expected_component_digest: [u8; 32] = Sha256::digest(policy.as_bytes()).into();
            assert_eq!(component_digest, expected_component_digest);
            let authenticated = store.load_authenticated_poa_galley_policy_v1().unwrap();
            assert_eq!(authenticated.world(), &world);
            assert_eq!(authenticated.manifest_root(), world.content_root());
            assert_eq!(authenticated.component_sha256(), expected_component_digest);
            store.audit_poa_activated_content_v1().unwrap();
        }

        let reopened = PersistentStore::open(&path).unwrap();
        reopened.audit_poa_world_activation_v1().unwrap();
        reopened.audit_poa_activated_content_v1().unwrap();
        let prepared = reopened.prepare_active_poa_galley_policy_v1().unwrap();
        let (reopened_world, reopened_policy, _, _, _) = prepared.into_parts();
        assert_eq!(reopened_world, world);
        assert_eq!(reopened_policy, policy.as_bytes());
        assert_eq!(
            reopened
                .load_authenticated_poa_galley_policy_v1()
                .unwrap()
                .world(),
            &world
        );
    }

    #[test]
    fn world_rotation_never_reuses_stale_policy_carrier() {
        if !native_available() {
            return;
        }
        let store = PersistentStore::open_in_memory().unwrap();
        let key = SigningKey::from_bytes(&[42; 32]);
        store
            .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
            .unwrap();

        let policy1 = policy_json(1, 1, 13);
        let manifest1 = manifest_json(1, 2, 1, &policy1);
        let world1 = world_for_manifest(&manifest1, 3, 2, 1);
        let first = store
            .install_poa_world_activation_v1(signed(&key, world1, 1, [0; 32]))
            .unwrap();
        store.install_poa_activated_content_v1(manifest1).unwrap();

        let policy2 = policy_json(1, 2, 13);
        let manifest2 = manifest_json(1, 4, 2, &policy2);
        let world2 = world_for_manifest(&manifest2, 5, 4, 2);
        store
            .install_poa_world_activation_v1(signed(
                &key,
                world2.clone(),
                2,
                first.active_head().prepared().record().envelope_digest(),
            ))
            .unwrap();

        assert!(store.prepare_active_poa_galley_policy_v1().is_err());
        store.audit_poa_activated_content_v1().unwrap();
        store.install_poa_activated_content_v1(manifest2).unwrap();
        let (loaded_world, loaded_policy, _, _, _) = store
            .prepare_active_poa_galley_policy_v1()
            .unwrap()
            .into_parts();
        assert_eq!(loaded_world, world2);
        assert_eq!(loaded_policy, policy2.as_bytes());
    }

    #[test]
    fn sealed_frame_tamper_is_detected() {
        let stored = StoredActivatedContentV1 {
            world: PoaWorldIdentityV2::new([1; 32], [2; 32], [3; 32], [4; 32], 1).unwrap(),
            manifest_json: b"manifest".to_vec(),
            lean_response: b"response".to_vec(),
        };
        let mut frame = encode_frame(&stored).unwrap();
        frame[FRAME_HEADER_LEN] ^= 1;
        assert!(decode_frame(&frame).is_err());
    }
}
