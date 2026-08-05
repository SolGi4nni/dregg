//! Operator ceremony for quorum-authorized Path of Angels replay compaction.
//!
//! Compaction deletes generic commit rows only after every signer independently reconstructs the
//! exact doomed prefix from its own replica.  The coordinator exports a preview; validators re-run
//! that preview locally and produce hybrid Ed25519 + ML-DSA shares; the coordinator verifies a
//! genuine enrolled quorum and submits the exact anchor to the single redb compaction transaction.
//! No HTTP request, local boolean, or node-local test key can authorize deletion.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::{Read as _, Write as _};
use std::path::{Path, PathBuf};

use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use dregg_persist::{
    PersistentStore, PoaCompactCheckpointStatementV1, PoaCompactTrustPolicyV1,
    PoaCompactTrustRootV1, SignedPoaCompactCheckpointAnchorV1,
};
use dregg_types::{HybridQuorumSig, PublicKey, Signature, SigningKey};
use poa_curator::PoaDeploymentScope;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

const PREVIEW_SCHEMA: &str = "dregg-poa-compact-preview-v1";
const SHARE_SCHEMA: &str = "dregg-poa-compact-share-v1";
const HISTORY_SCHEMA: &str = "dregg-poa-compact-trust-history-v1";
const RESULT_SCHEMA: &str = "dregg-poa-compact-result-v1";
const TRUST_PIN_SCHEMA: &str = "dregg-poa-compact-trust-pin-v1";
const MAX_CEREMONY_FILE_BYTES: u64 = 16 * 1024 * 1024;
const BASE_HISTORY_DOMAIN: &[u8] = b"dregg-poa-compact-trust-base-v1\0";
const ROTATION_MESSAGE_DOMAIN: &[u8] = b"dregg-poa-compact-trust-rotation-v1\0";
const ROTATION_DIGEST_DOMAIN: &[u8] = b"dregg-poa-compact-trust-rotation-digest-v1\0";
const PREVIEW_DIGEST_DOMAIN: &[u8] = b"dregg-poa-compact-preview-file-v1\0";
const SIGNING_MESSAGE_DIGEST_DOMAIN: &[u8] = b"dregg-poa-compact-signing-message-v1\0";

/// Environment variable pinning the exact PoA deployment manifest used on node boot.
pub const POA_DEPLOYMENT_MANIFEST_ENV: &str = "POA_DEPLOYMENT_MANIFEST";
/// Environment variable naming the disjoint main-network data directory.
pub const POA_MAIN_DATA_DIR_ENV: &str = "POA_MAIN_DATA_DIR";
/// Optional independently authenticated append-only committee history.
pub const POA_COMPACT_TRUST_HISTORY_ENV: &str = "POA_COMPACT_TRUST_HISTORY";
/// Exact independently pinned head of `POA_COMPACT_TRUST_HISTORY`; the pair is all-or-nothing.
pub const POA_COMPACT_TRUST_HISTORY_HEAD_ENV: &str = "POA_COMPACT_TRUST_HISTORY_HEAD";

#[derive(Clone, Debug)]
pub struct AuthenticatedPoaCompactPolicyV1 {
    policy: PoaCompactTrustPolicyV1,
    roots: BTreeMap<u64, PoaCompactTrustRootV1>,
    history_heads: BTreeMap<u64, [u8; 32]>,
    history_head: [u8; 32],
}

impl AuthenticatedPoaCompactPolicyV1 {
    pub fn policy(&self) -> &PoaCompactTrustPolicyV1 {
        &self.policy
    }

    pub fn root_at_epoch(&self, epoch: u64) -> Option<&PoaCompactTrustRootV1> {
        self.roots.get(&epoch)
    }

    pub fn latest_root(&self) -> &PoaCompactTrustRootV1 {
        self.roots
            .last_key_value()
            .map(|(_, root)| root)
            .expect("authenticated policy always has its deployment root")
    }

    fn history_head_at_epoch(&self, epoch: u64) -> Option<[u8; 32]> {
        self.history_heads.get(&epoch).copied()
    }

    pub const fn history_head(&self) -> [u8; 32] {
        self.history_head
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactPreviewFileV1 {
    schema: String,
    requested_height: u64,
    trust_history_head: String,
    signing_message_sha256: String,
    statement: PoaCompactCheckpointStatementV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactShareFileV1 {
    schema: String,
    preview_sha256: String,
    signing_message_sha256: String,
    signer_public_key: String,
    ml_dsa_public_key: String,
    signature: String,
    pq_signature: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactTrustHistoryFileV1 {
    schema: String,
    deployment_id: String,
    transitions: Vec<PoaCompactTrustTransitionV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactTrustTransitionV1 {
    predecessor_digest: String,
    old_committee_epoch: u64,
    new_committee_epoch: u64,
    new_federation_id: String,
    new_threshold: usize,
    new_committee: Vec<PoaCompactCommitteeMemberV1>,
    hybrid_quorum: Vec<PoaCompactHybridSignatureV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactCommitteeMemberV1 {
    public_key: String,
    ml_dsa_public_key: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactHybridSignatureV1 {
    public_key: String,
    ml_dsa_public_key: String,
    signature: String,
    pq_signature: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PoaCompactTrustPinV1 {
    schema: String,
    deployment_id: String,
    committee_epoch: u64,
    history_head: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaCompactCeremonyReportV1 {
    pub schema: &'static str,
    pub status: &'static str,
    pub requested_height: u64,
    pub old_floor: u64,
    pub new_floor: u64,
    pub compacted_records: u64,
    pub statement_sha256: String,
}

/// Load the node's independently authenticated PoA compact policy from its pinned deployment
/// environment.  No PoA environment means a generic/uncompacted node and returns `None`; a partial
/// environment is an error rather than a downgrade.
pub fn load_runtime_poa_compact_policy_from_env(
    data_dir: &Path,
) -> Result<Option<AuthenticatedPoaCompactPolicyV1>, String> {
    let manifest = std::env::var_os(POA_DEPLOYMENT_MANIFEST_ENV).map(PathBuf::from);
    let main_data = std::env::var_os(POA_MAIN_DATA_DIR_ENV).map(PathBuf::from);
    match (manifest, main_data) {
        (None, None) => Ok(None),
        (Some(manifest), Some(main_data)) => {
            let history = std::env::var_os(POA_COMPACT_TRUST_HISTORY_ENV).map(PathBuf::from);
            let expected_history_head = std::env::var_os(POA_COMPACT_TRUST_HISTORY_HEAD_ENV)
                .map(|value| {
                    value.into_string().map_err(|_| {
                        format!("{POA_COMPACT_TRUST_HISTORY_HEAD_ENV} is not valid UTF-8")
                    })
                })
                .transpose()?;
            load_authenticated_poa_compact_policy(
                data_dir,
                &manifest,
                &main_data,
                history.as_deref(),
                expected_history_head.as_deref(),
            )
            .map(Some)
        }
        _ => Err(format!(
            "{POA_DEPLOYMENT_MANIFEST_ENV} and {POA_MAIN_DATA_DIR_ENV} must be supplied together; refusing a partial PoA compaction trust root"
        )),
    }
}

/// Derive the complete trust policy from the exact verified PoA deployment and, optionally, an
/// append-only rotation history whose every edge is signed by the preceding hybrid committee.
pub fn load_authenticated_poa_compact_policy(
    data_dir: &Path,
    deployment_manifest: &Path,
    main_data_dir: &Path,
    trust_history: Option<&Path>,
    expected_history_head: Option<&str>,
) -> Result<AuthenticatedPoaCompactPolicyV1, String> {
    // Rotation authentication is hybrid even for read-only preview and node boot.  Keep the
    // production verifier installation inside the policy loader so no caller can accidentally
    // reach ML-DSA verification through a test-only or absent-core path.
    crate::install_verified_pq_cores();
    validate_history_source_pair(trust_history, expected_history_head)?;
    let genesis_path = deployment_manifest
        .parent()
        .ok_or_else(|| "PoA deployment manifest has no containing directory".to_owned())?
        .join("bundle/genesis.json");
    let scope =
        PoaDeploymentScope::load_verified(deployment_manifest, &genesis_path, main_data_dir)
            .map_err(|error| format!("PoA compact deployment trust refused: {error}"))?;
    scope
        .verify_serving_data_dir(data_dir, None)
        .map_err(|error| format!("PoA compact serving identity refused: {error}"))?;

    let deployment_id = decode_hex_array::<32>(scope.deployment_id(), "deployment_id")?;
    let federation_id = decode_hex_array::<32>(scope.federation_id(), "federation_id")?;
    let genesis_bytes = scope
        .verified_genesis_bytes()
        .map_err(|error| format!("PoA compact genesis authority refused: {error}"))?;
    let genesis: serde_json::Value = serde_json::from_slice(genesis_bytes)
        .map_err(|error| format!("PoA compact genesis JSON refused: {error}"))?;
    let committee_epoch = genesis
        .get("committee_epoch")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "PoA compact genesis committee_epoch is absent".to_owned())?;
    let threshold_u64 = genesis
        .get("threshold")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "PoA compact genesis threshold is absent".to_owned())?;
    let threshold = usize::try_from(threshold_u64)
        .map_err(|_| "PoA compact genesis threshold does not fit usize".to_owned())?;
    let validators = genesis
        .get("validators")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "PoA compact genesis validators are absent".to_owned())?;
    let mut committee = Vec::with_capacity(validators.len());
    let mut ml_dsa_committee = Vec::with_capacity(validators.len());
    for (index, validator) in validators.iter().enumerate() {
        let public = validator
            .get("public_key")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| format!("PoA compact genesis validator {index} lacks public_key"))?;
        let ml_dsa = validator
            .get("ml_dsa_public_key")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| {
                format!(
                    "PoA compact genesis validator {index} lacks an enrolled ML-DSA key; hybrid compaction authority cannot downgrade"
                )
            })?;
        committee.push(PublicKey(decode_hex_array::<32>(
            public,
            "validator public_key",
        )?));
        ml_dsa_committee.push(MlDsaPublicKey(decode_hex_array::<
            { dregg_pq::ML_DSA_PK_LEN },
        >(
            ml_dsa, "validator ml_dsa_public_key"
        )?));
    }
    let base = PoaCompactTrustRootV1::new(
        deployment_id,
        federation_id,
        committee_epoch,
        committee,
        ml_dsa_committee,
        threshold,
    )
    .map_err(|error| format!("PoA compact genesis trust root refused: {error}"))?;

    let mut roots = BTreeMap::from([(committee_epoch, base)]);
    let mut history_head = base_history_digest(&scope)?;
    let mut history_heads = BTreeMap::from([(committee_epoch, history_head)]);
    if let Some(path) = trust_history {
        let bytes = read_bounded_regular(path)?;
        let history: PoaCompactTrustHistoryFileV1 = parse_canonical_json(&bytes, path)?;
        if history.schema != HISTORY_SCHEMA
            || decode_hex_array::<32>(&history.deployment_id, "history deployment_id")?
                != deployment_id
        {
            return Err("PoA compact trust history has the wrong schema or deployment".to_owned());
        }
        for transition in history.transitions {
            apply_authenticated_transition(
                &mut roots,
                &mut history_head,
                deployment_id,
                &transition,
            )?;
            history_heads.insert(transition.new_committee_epoch, history_head);
        }
    }
    if let Some(expected) = expected_history_head {
        let expected = decode_hex_array::<32>(expected, "expected trust history head")?;
        if expected != history_head {
            return Err(
                "PoA compact trust history does not equal its independently pinned exact head"
                    .to_owned(),
            );
        }
    }
    let policy = PoaCompactTrustPolicyV1::new(roots.values().cloned().collect())
        .map_err(|error| format!("PoA compact trust policy refused: {error}"))?;
    enforce_sticky_history_pins(data_dir, deployment_id, &history_heads)?;
    Ok(AuthenticatedPoaCompactPolicyV1 {
        policy,
        roots,
        history_heads,
        history_head,
    })
}

/// Export the exact locally reconstructed statement validators will sign.
pub fn export_poa_compact_preview(
    data_dir: &Path,
    deployment_manifest: &Path,
    main_data_dir: &Path,
    trust_history: Option<&Path>,
    expected_history_head: Option<&str>,
    requested_height: u64,
    output: &Path,
) -> Result<(), String> {
    let context = load_authenticated_poa_compact_policy(
        data_dir,
        deployment_manifest,
        main_data_dir,
        trust_history,
        expected_history_head,
    )?;
    let root = context.latest_root();
    let store = open_authenticated_store(data_dir, &context)?;
    let statement = store
        .prepare_poa_compact_checkpoint_statement_v1(requested_height, root)
        .map_err(|error| format!("PoA compact preview refused: {error}"))?
        .ok_or_else(|| {
            "PoA compact preview has no non-empty checkpoint-subsumed prefix; no ceremony is needed"
                .to_owned()
        })?;
    let preview = PoaCompactPreviewFileV1::new(requested_height, context.history_head(), statement);
    write_canonical_new_or_identical(output, &preview)
}

/// Independently reconstruct and hybrid-sign a preview using this validator's enrolled node key.
pub fn sign_poa_compact_preview(
    data_dir: &Path,
    key_file: &Path,
    deployment_manifest: &Path,
    main_data_dir: &Path,
    trust_history: Option<&Path>,
    expected_history_head: Option<&str>,
    preview_path: &Path,
    output: &Path,
) -> Result<(), String> {
    crate::install_verified_pq_cores();
    let context = load_authenticated_poa_compact_policy(
        data_dir,
        deployment_manifest,
        main_data_dir,
        trust_history,
        expected_history_head,
    )?;
    let preview_bytes = read_bounded_regular(preview_path)?;
    let preview: PoaCompactPreviewFileV1 = parse_canonical_json(&preview_bytes, preview_path)?;
    let resolved_key = if key_file.is_absolute() {
        key_file.to_path_buf()
    } else {
        data_dir.join(key_file)
    };
    sign_loaded_poa_compact_preview(
        data_dir,
        &resolved_key,
        &context,
        preview,
        &preview_bytes,
        output,
    )
}

/// Recover an exact durably journaled share before checking whether its committee is still active.
/// A journal is the validator's signing commit point: rotation may forbid any new signature from
/// that committee, but cannot make an already committed exact response unrecoverable.
fn sign_loaded_poa_compact_preview(
    data_dir: &Path,
    resolved_key: &Path,
    context: &AuthenticatedPoaCompactPolicyV1,
    preview: PoaCompactPreviewFileV1,
    preview_bytes: &[u8],
    output: &Path,
) -> Result<(), String> {
    let historical_root = preview.validate_historical(context)?;
    let seed = read_private_seed(resolved_key)?;
    let signing_key = SigningKey::from_bytes(&seed);
    let (ml_dsa_public, ml_dsa_signing) = MlDsaSigningKey::from_seed(&seed);
    let signer_index = historical_root
        .committee()
        .iter()
        .position(|member| *member == signing_key.public_key())
        .ok_or_else(|| {
            "local node key is not enrolled in this historical compaction committee".to_owned()
        })?;
    if historical_root.ml_dsa_committee().get(signer_index) != Some(&ml_dsa_public) {
        return Err(
            "local node key's derived ML-DSA half differs from the historical aligned roster"
                .to_owned(),
        );
    }

    let preview_digest = sha256_domain(PREVIEW_DIGEST_DOMAIN, preview_bytes);
    let journal_path = signer_journal_path(
        data_dir,
        preview.statement.committee_epoch(),
        preview.statement.old_floor(),
        signing_key.public_key(),
    );
    if journal_path.exists() {
        let bytes = read_bounded_regular(&journal_path)?;
        let prior: PoaCompactShareFileV1 = parse_canonical_json(&bytes, &journal_path)?;
        if prior.preview_sha256 != hex(&preview_digest)
            || prior.signer_public_key != hex(&signing_key.public_key().0)
            || prior.ml_dsa_public_key != hex(&ml_dsa_public.0)
        {
            return Err(
                "PoA compact signer equivocation or journal identity substitution refused: this member already signed a different preview at the same epoch/floor"
                    .to_owned(),
            );
        }
        prior.validate(&preview, preview_digest, historical_root)?;
        return write_exact_new_or_identical(output, &bytes);
    }

    // No prior signing commit exists. Only the active root may authorize a new share, and the
    // validator must reconstruct the exact fresh preview from its own current replica.
    preview.validate(context)?;
    let active_root = context.latest_root();
    let active_index = active_root
        .committee()
        .iter()
        .position(|member| *member == signing_key.public_key())
        .ok_or_else(|| {
            "local node key is not enrolled in the active compaction committee".to_owned()
        })?;
    if active_root.ml_dsa_committee().get(active_index) != Some(&ml_dsa_public) {
        return Err(
            "local node key's derived ML-DSA half differs from the active aligned roster"
                .to_owned(),
        );
    }
    let store = open_authenticated_store(data_dir, context)?;
    require_fresh_local_preview(&store, active_root, &preview)?;

    let message = preview.statement.signing_message();
    let share = PoaCompactShareFileV1 {
        schema: SHARE_SCHEMA.to_owned(),
        preview_sha256: hex(&preview_digest),
        signing_message_sha256: hex(&signing_message_digest(&message)),
        signer_public_key: hex(&signing_key.public_key().0),
        ml_dsa_public_key: hex(&ml_dsa_public.0),
        signature: hex(&dregg_types::sign(&signing_key, &message).0),
        pq_signature: hex(&ml_dsa_signing
            .sign(&message)
            .ok_or_else(|| "ML-DSA signing refused".to_owned())?),
    };
    let bytes = canonical_json_bytes(&share)?;
    persist_signer_journal(&journal_path, &bytes)?;
    write_exact_new_or_identical(output, &bytes)
}

/// Verify imported shares, compact atomically, reopen under the same external policy, and return
/// an exact-retry-aware report.
pub fn finalize_poa_compact_preview(
    data_dir: &Path,
    deployment_manifest: &Path,
    main_data_dir: &Path,
    trust_history: Option<&Path>,
    expected_history_head: Option<&str>,
    preview_path: &Path,
    share_paths: &[PathBuf],
) -> Result<PoaCompactCeremonyReportV1, String> {
    crate::install_verified_pq_cores();
    let context = load_authenticated_poa_compact_policy(
        data_dir,
        deployment_manifest,
        main_data_dir,
        trust_history,
        expected_history_head,
    )?;
    let preview_bytes = read_bounded_regular(preview_path)?;
    let preview: PoaCompactPreviewFileV1 = parse_canonical_json(&preview_bytes, preview_path)?;
    finalize_loaded_poa_compact_preview(data_dir, &context, preview, &preview_bytes, share_paths)
}

/// Finalization deliberately authenticates a historical ceremony before it tests exact retry.
/// A response may be lost just before an externally authorized committee rotation; the exact
/// committed anchor must remain replayable, while the retired committee must never authorize a
/// fresh deletion.
fn finalize_loaded_poa_compact_preview(
    data_dir: &Path,
    context: &AuthenticatedPoaCompactPolicyV1,
    preview: PoaCompactPreviewFileV1,
    preview_bytes: &[u8],
    share_paths: &[PathBuf],
) -> Result<PoaCompactCeremonyReportV1, String> {
    let historical_root = preview.validate_historical(context)?;
    let preview_digest = sha256_domain(PREVIEW_DIGEST_DOMAIN, &preview_bytes);
    let quorum = load_shares(share_paths, &preview, preview_digest, historical_root)?;
    let anchor = SignedPoaCompactCheckpointAnchorV1::new(preview.statement.clone(), quorum);
    let store = open_authenticated_store(data_dir, &context)?;

    if store
        .has_exact_poa_compact_checkpoint_anchor_v1(&anchor, context.policy())
        .map_err(|error| format!("PoA compact exact-retry audit refused: {error}"))?
    {
        return Ok(report(&preview, "already_committed_exact_retry", 0));
    }
    preview.validate(context)?;
    let root = context.latest_root();
    require_fresh_local_preview(&store, root, &preview)?;
    let expected = preview
        .statement
        .new_floor()
        .checked_sub(preview.statement.old_floor())
        .ok_or_else(|| "PoA compact preview floor regressed".to_owned())?;
    let compacted = store
        .compact_below_with_poa_anchor_v1(
            preview.requested_height,
            anchor.clone(),
            context.policy(),
        )
        .map_err(|error| format!("PoA compact transaction refused: {error}"))?;
    if compacted != expected {
        return Err(format!(
            "PoA compact transaction removed {compacted} records but the signed statement binds {expected}"
        ));
    }
    drop(store);
    let reopened = open_authenticated_store(data_dir, &context)?;
    if !reopened
        .has_exact_poa_compact_checkpoint_anchor_v1(&anchor, context.policy())
        .map_err(|error| format!("PoA compact post-restart audit refused: {error}"))?
    {
        return Err("PoA compact post-restart audit did not recover the exact anchor".to_owned());
    }
    Ok(report(&preview, "committed", compacted))
}

fn report(
    preview: &PoaCompactPreviewFileV1,
    status: &'static str,
    compacted_records: u64,
) -> PoaCompactCeremonyReportV1 {
    PoaCompactCeremonyReportV1 {
        schema: RESULT_SCHEMA,
        status,
        requested_height: preview.requested_height,
        old_floor: preview.statement.old_floor(),
        new_floor: preview.statement.new_floor(),
        compacted_records,
        statement_sha256: preview.signing_message_sha256.clone(),
    }
}

fn open_authenticated_store(
    data_dir: &Path,
    context: &AuthenticatedPoaCompactPolicyV1,
) -> Result<PersistentStore, String> {
    PersistentStore::open_with_poa_compact_trust_v1(&data_dir.join("dregg.redb"), context.policy())
        .map_err(|error| {
            format!("failed to open PoA store under authenticated compact policy: {error}")
        })
}

fn require_fresh_local_preview(
    store: &PersistentStore,
    root: &PoaCompactTrustRootV1,
    preview: &PoaCompactPreviewFileV1,
) -> Result<(), String> {
    let current = store
        .prepare_poa_compact_checkpoint_statement_v1(preview.requested_height, root)
        .map_err(|error| format!("local PoA compact re-preview refused: {error}"))?
        .ok_or_else(|| "local PoA compact re-preview is empty or already crossed".to_owned())?;
    if current != preview.statement {
        return Err(
            "stale or foreign PoA compact preview: local exact checkpoint/prefix statement differs"
                .to_owned(),
        );
    }
    Ok(())
}

impl PoaCompactPreviewFileV1 {
    fn new(
        requested_height: u64,
        history_head: [u8; 32],
        statement: PoaCompactCheckpointStatementV1,
    ) -> Self {
        Self {
            schema: PREVIEW_SCHEMA.to_owned(),
            requested_height,
            trust_history_head: hex(&history_head),
            signing_message_sha256: hex(&signing_message_digest(&statement.signing_message())),
            statement,
        }
    }

    fn validate_historical<'a>(
        &self,
        context: &'a AuthenticatedPoaCompactPolicyV1,
    ) -> Result<&'a PoaCompactTrustRootV1, String> {
        let history_head = decode_hex_array::<32>(&self.trust_history_head, "trust_history_head")?;
        let root = context
            .root_at_epoch(self.statement.committee_epoch())
            .ok_or_else(|| {
                "PoA compact preview names a committee epoch absent from authenticated history"
                    .to_owned()
            })?;
        if self.schema != PREVIEW_SCHEMA
            || context.history_head_at_epoch(self.statement.committee_epoch()) != Some(history_head)
            || decode_hex_array::<32>(&self.signing_message_sha256, "signing_message_sha256")?
                != signing_message_digest(&self.statement.signing_message())
        {
            return Err(
                "PoA compact preview schema, authenticated epoch history, or signing digest differs"
                    .to_owned(),
            );
        }
        if self.statement.deployment_id() != root.deployment_id()
            || self.statement.federation_id() != root.federation_id()
            || self.statement.old_floor() >= self.statement.new_floor()
        {
            return Err(
                "PoA compact preview does not bind its authenticated historical trust root/floor"
                    .to_owned(),
            );
        }
        Ok(root)
    }

    fn validate(&self, context: &AuthenticatedPoaCompactPolicyV1) -> Result<(), String> {
        let root = self.validate_historical(context)?;
        if self.statement.committee_epoch() != context.latest_root().committee_epoch()
            || root.committee_epoch() != context.latest_root().committee_epoch()
            || decode_hex_array::<32>(&self.trust_history_head, "trust_history_head")?
                != context.history_head()
        {
            return Err(
                "PoA compact preview does not bind the active latest trust root".to_owned(),
            );
        }
        Ok(())
    }
}

impl PoaCompactShareFileV1 {
    fn validate(
        &self,
        preview: &PoaCompactPreviewFileV1,
        preview_digest: [u8; 32],
        root: &PoaCompactTrustRootV1,
    ) -> Result<HybridQuorumSig, String> {
        let message = preview.statement.signing_message();
        if self.schema != SHARE_SCHEMA
            || decode_hex_array::<32>(&self.preview_sha256, "preview_sha256")? != preview_digest
            || decode_hex_array::<32>(&self.signing_message_sha256, "share signing_message_sha256")?
                != signing_message_digest(&message)
        {
            return Err("PoA compact share binds a different preview or message".to_owned());
        }
        let share = HybridQuorumSig {
            pubkey: PublicKey(decode_hex_array::<32>(
                &self.signer_public_key,
                "share signer_public_key",
            )?),
            signature: Signature(decode_hex_array::<64>(&self.signature, "share signature")?),
            ml_dsa_pubkey: decode_hex_vec(&self.ml_dsa_public_key, "share ml_dsa_public_key")?,
            pq_signature: decode_hex_vec(&self.pq_signature, "share pq_signature")?,
        };
        let Some(index) = root
            .committee()
            .iter()
            .position(|member| *member == share.pubkey)
        else {
            return Err("PoA compact share signer is outside the authenticated roster".to_owned());
        };
        if share.ml_dsa_pubkey.as_slice() != root.ml_dsa_committee()[index].0.as_slice()
            || !share.pubkey.verify(&message, &share.signature)
            || !root.ml_dsa_committee()[index].verify(&message, &share.pq_signature)
        {
            return Err(
                "PoA compact share has an invalid or roster-substituted hybrid signature"
                    .to_owned(),
            );
        }
        Ok(share)
    }
}

impl PoaCompactHybridSignatureV1 {
    fn decode(&self) -> Result<HybridQuorumSig, String> {
        Ok(HybridQuorumSig {
            pubkey: PublicKey(decode_hex_array::<32>(
                &self.public_key,
                "rotation public_key",
            )?),
            signature: Signature(decode_hex_array::<64>(
                &self.signature,
                "rotation signature",
            )?),
            ml_dsa_pubkey: decode_hex_vec(&self.ml_dsa_public_key, "rotation ml_dsa_public_key")?,
            pq_signature: decode_hex_vec(&self.pq_signature, "rotation pq_signature")?,
        })
    }
}

fn load_shares(
    paths: &[PathBuf],
    preview: &PoaCompactPreviewFileV1,
    preview_digest: [u8; 32],
    root: &PoaCompactTrustRootV1,
) -> Result<Vec<HybridQuorumSig>, String> {
    if paths.is_empty() {
        return Err("PoA compact finalization has no signature shares".to_owned());
    }
    let mut shares = Vec::with_capacity(paths.len());
    for path in paths {
        let bytes = read_bounded_regular(path)?;
        let encoded: PoaCompactShareFileV1 = parse_canonical_json(&bytes, path)?;
        shares.push(encoded.validate(preview, preview_digest, root)?);
    }
    reject_duplicate_signers(&shares)?;
    if !dregg_federation::receipt::verify_hybrid_quorum_sigs(
        &shares,
        &preview.statement.signing_message(),
        root.committee(),
        root.ml_dsa_committee(),
        root.threshold(),
    ) {
        return Err("PoA compact shares do not form the authenticated hybrid quorum".to_owned());
    }
    shares.sort_by_key(|share| share.pubkey.0);
    Ok(shares)
}

fn reject_duplicate_signers(shares: &[HybridQuorumSig]) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    if shares.iter().any(|share| !seen.insert(share.pubkey.0)) {
        return Err("PoA compact ceremony contains duplicate signer shares".to_owned());
    }
    Ok(())
}

fn validate_history_source_pair(
    trust_history: Option<&Path>,
    expected_history_head: Option<&str>,
) -> Result<(), String> {
    match (trust_history, expected_history_head) {
        (Some(_), Some(_)) | (None, None) => Ok(()),
        _ => Err(format!(
            "{POA_COMPACT_TRUST_HISTORY_ENV} and {POA_COMPACT_TRUST_HISTORY_HEAD_ENV} must be supplied together; refusing an unpinned or history-less rotation"
        )),
    }
}

/// Apply exactly one committee-history edge after authenticating it under the current history
/// head.  Mutation happens only after every structural, roster, threshold, and hybrid-quorum check
/// succeeds, so a malformed edge cannot partially advance either retained value.
fn apply_authenticated_transition(
    roots: &mut BTreeMap<u64, PoaCompactTrustRootV1>,
    history_head: &mut [u8; 32],
    deployment_id: [u8; 32],
    transition: &PoaCompactTrustTransitionV1,
) -> Result<(), String> {
    let prior = roots
        .last_key_value()
        .map(|(_, root)| root)
        .ok_or_else(|| "PoA compact trust history lost its base".to_owned())?;
    let predecessor = decode_hex_array::<32>(
        &transition.predecessor_digest,
        "transition predecessor_digest",
    )?;
    if predecessor != *history_head
        || transition.old_committee_epoch != prior.committee_epoch()
        || transition.new_committee_epoch
            != transition
                .old_committee_epoch
                .checked_add(1)
                .ok_or_else(|| "PoA compact committee epoch overflow".to_owned())?
    {
        return Err(
            "PoA compact trust history is not one exact contiguous predecessor chain".to_owned(),
        );
    }
    let next_root = transition_root(transition, deployment_id)?;
    let message = transition_signing_message(transition, deployment_id)?;
    let quorum = transition
        .hybrid_quorum
        .iter()
        .map(PoaCompactHybridSignatureV1::decode)
        .collect::<Result<Vec<_>, _>>()?;
    reject_duplicate_signers(&quorum)?;
    if !dregg_federation::receipt::verify_hybrid_quorum_sigs(
        &quorum,
        &message,
        prior.committee(),
        prior.ml_dsa_committee(),
        prior.threshold(),
    ) {
        return Err(
            "PoA compact trust rotation lacks a genuine preceding hybrid quorum".to_owned(),
        );
    }
    // The authorization witness is deliberately not part of semantic history identity: ML-DSA
    // signatures are hedged and multiple valid threshold subsets exist.  Every replica which
    // verifies any genuine quorum over the same transition must derive the same next head.
    let next_head = transition_digest(*history_head, &message);
    if roots.contains_key(&transition.new_committee_epoch) {
        return Err("PoA compact trust history repeats an epoch".to_owned());
    }
    roots.insert(transition.new_committee_epoch, next_root);
    *history_head = next_head;
    Ok(())
}

fn transition_root(
    transition: &PoaCompactTrustTransitionV1,
    deployment_id: [u8; 32],
) -> Result<PoaCompactTrustRootV1, String> {
    if transition.new_committee.is_empty() {
        return Err("PoA compact trust transition has an empty committee".to_owned());
    }
    let mut committee = Vec::with_capacity(transition.new_committee.len());
    let mut ml_dsa = Vec::with_capacity(transition.new_committee.len());
    for member in &transition.new_committee {
        committee.push(PublicKey(decode_hex_array::<32>(
            &member.public_key,
            "transition public_key",
        )?));
        ml_dsa.push(MlDsaPublicKey(decode_hex_array::<
            { dregg_pq::ML_DSA_PK_LEN },
        >(
            &member.ml_dsa_public_key,
            "transition ml_dsa_public_key",
        )?));
    }
    PoaCompactTrustRootV1::new(
        deployment_id,
        decode_hex_array::<32>(&transition.new_federation_id, "new_federation_id")?,
        transition.new_committee_epoch,
        committee,
        ml_dsa,
        transition.new_threshold,
    )
    .map_err(|error| format!("PoA compact transition root refused: {error}"))
}

fn transition_signing_message(
    transition: &PoaCompactTrustTransitionV1,
    deployment_id: [u8; 32],
) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(ROTATION_MESSAGE_DOMAIN);
    out.extend_from_slice(&deployment_id);
    out.extend_from_slice(&decode_hex_array::<32>(
        &transition.predecessor_digest,
        "transition predecessor_digest",
    )?);
    out.extend_from_slice(&transition.old_committee_epoch.to_le_bytes());
    out.extend_from_slice(&transition.new_committee_epoch.to_le_bytes());
    out.extend_from_slice(&decode_hex_array::<32>(
        &transition.new_federation_id,
        "transition new_federation_id",
    )?);
    out.extend_from_slice(
        &u64::try_from(transition.new_threshold)
            .map_err(|_| "transition threshold does not fit u64".to_owned())?
            .to_le_bytes(),
    );
    out.extend_from_slice(
        &u64::try_from(transition.new_committee.len())
            .map_err(|_| "transition committee size does not fit u64".to_owned())?
            .to_le_bytes(),
    );
    for member in &transition.new_committee {
        out.extend_from_slice(&decode_hex_array::<32>(
            &member.public_key,
            "transition public_key",
        )?);
        out.extend_from_slice(&decode_hex_array::<{ dregg_pq::ML_DSA_PK_LEN }>(
            &member.ml_dsa_public_key,
            "transition ml_dsa_public_key",
        )?);
    }
    Ok(out)
}

fn transition_digest(predecessor: [u8; 32], message: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(ROTATION_DIGEST_DOMAIN);
    hasher.update(predecessor);
    hasher.update(message);
    hasher.finalize().into()
}

fn base_history_digest(scope: &PoaDeploymentScope) -> Result<[u8; 32], String> {
    let mut hasher = Sha256::new();
    hasher.update(BASE_HISTORY_DOMAIN);
    hasher.update(
        scope
            .verified_manifest_bytes()
            .map_err(|error| format!("PoA compact manifest authority refused: {error}"))?,
    );
    hasher.update(
        scope
            .verified_genesis_bytes()
            .map_err(|error| format!("PoA compact genesis authority refused: {error}"))?,
    );
    Ok(hasher.finalize().into())
}

/// Retain an append-only local witness of every authenticated history head this node has already
/// accepted.  These files do not authorize a root (the verified deployment and signed history do
/// that); they only make later omission or prefix rollback fail closed before redb is opened.
fn enforce_sticky_history_pins(
    data_dir: &Path,
    deployment_id: [u8; 32],
    authenticated_heads: &BTreeMap<u64, [u8; 32]>,
) -> Result<(), String> {
    let directory = data_dir.join("poa-compact-trust-pins-v1");
    if directory.exists() {
        let metadata = fs::symlink_metadata(&directory)
            .map_err(|error| format!("cannot inspect PoA compact trust pin directory: {error}"))?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
            return Err("PoA compact trust pin path is not a real directory".to_owned());
        }
        for entry in fs::read_dir(&directory)
            .map_err(|error| format!("cannot read PoA compact trust pin directory: {error}"))?
        {
            let entry = entry
                .map_err(|error| format!("cannot inspect PoA compact trust pin entry: {error}"))?;
            let name = entry.file_name();
            let name = name
                .to_str()
                .ok_or_else(|| "PoA compact trust pin filename is not UTF-8".to_owned())?;
            // An interrupted pre-publication temporary carries no authority and may be retried.
            if name.starts_with(".pending-") {
                continue;
            }
            let bytes = read_bounded_regular(&entry.path())?;
            let pin: PoaCompactTrustPinV1 = parse_canonical_json(&bytes, &entry.path())?;
            if pin.schema != TRUST_PIN_SCHEMA
                || pin.deployment_id != hex(&deployment_id)
                || name != format!("epoch-{}.pin.json", pin.committee_epoch)
            {
                return Err(
                    "PoA compact trust pin has the wrong schema, deployment, or filename"
                        .to_owned(),
                );
            }
            let retained = decode_hex_array::<32>(&pin.history_head, "retained history head")?;
            if authenticated_heads.get(&pin.committee_epoch) != Some(&retained) {
                return Err(
                    "PoA compact trust history omitted or changed a previously retained authenticated epoch"
                        .to_owned(),
                );
            }
        }
    }

    for (committee_epoch, history_head) in authenticated_heads {
        let pin = PoaCompactTrustPinV1 {
            schema: TRUST_PIN_SCHEMA.to_owned(),
            deployment_id: hex(&deployment_id),
            committee_epoch: *committee_epoch,
            history_head: hex(history_head),
        };
        let path = directory.join(format!("epoch-{committee_epoch}.pin.json"));
        persist_sticky_file(&path, &canonical_json_bytes(&pin)?, "trust pin")?;
    }
    Ok(())
}

fn signer_journal_path(data_dir: &Path, epoch: u64, old_floor: u64, signer: PublicKey) -> PathBuf {
    data_dir.join("poa-compact-ceremony-v1").join(format!(
        "epoch-{epoch}-floor-{old_floor}-{}.share.json",
        hex(&signer.0)
    ))
}

fn persist_signer_journal(path: &Path, bytes: &[u8]) -> Result<(), String> {
    persist_sticky_file(path, bytes, "signer journal")
}

fn persist_sticky_file(path: &Path, bytes: &[u8], label: &str) -> Result<(), String> {
    let parent = path
        .parent()
        .ok_or_else(|| format!("PoA compact {label} has no parent"))?;
    if parent.exists() {
        let meta = fs::symlink_metadata(parent)
            .map_err(|error| format!("cannot inspect {label} directory: {error}"))?;
        if !meta.file_type().is_dir() || meta.file_type().is_symlink() {
            return Err(format!(
                "PoA compact {label} directory is not a real directory"
            ));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            if meta.mode() & 0o077 != 0 {
                return Err(format!(
                    "PoA compact {label} directory is accessible by group or other users"
                ));
            }
        }
    } else {
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt as _;
            let mut builder = fs::DirBuilder::new();
            builder.mode(0o700);
            builder
                .create(parent)
                .map_err(|error| format!("cannot create protected {label} directory: {error}"))?;
        }
        #[cfg(not(unix))]
        {
            fs::create_dir(parent)
                .map_err(|error| format!("cannot create {label} directory: {error}"))?;
        }
    }
    let mut nonce = [0_u8; 16];
    getrandom::fill(&mut nonce).map_err(|error| format!("cannot mint {label} nonce: {error}"))?;
    let temporary = parent.join(format!(".pending-{}", hex(&nonce)));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|error| format!("cannot create {label} temporary: {error}"))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|error| format!("cannot persist {label} temporary: {error}"))?;
    match fs::hard_link(&temporary, path) {
        Ok(()) => {
            fs::remove_file(&temporary)
                .map_err(|error| format!("cannot remove {label} temporary: {error}"))?;
            let dir = OpenOptions::new()
                .read(true)
                .open(parent)
                .map_err(|error| format!("cannot open {label} directory: {error}"))?;
            dir.sync_all()
                .map_err(|error| format!("cannot sync {label} directory: {error}"))?;
            Ok(())
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            let _ = fs::remove_file(&temporary);
            let prior = read_bounded_regular(path)?;
            if prior == bytes {
                Ok(())
            } else {
                Err(format!(
                    "concurrent PoA compact {label} equivocation refused"
                ))
            }
        }
        Err(error) => {
            let _ = fs::remove_file(&temporary);
            Err(format!("cannot publish {label}: {error}"))
        }
    }
}

fn write_canonical_new_or_identical<T: Serialize>(path: &Path, value: &T) -> Result<(), String> {
    write_exact_new_or_identical(path, &canonical_json_bytes(value)?)
}

fn canonical_json_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>, String> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("cannot encode ceremony JSON: {error}"))?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn write_exact_new_or_identical(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if path.exists() {
        let existing = read_bounded_regular(path)?;
        if existing == bytes {
            return Ok(());
        }
        return Err(format!(
            "refusing to overwrite different ceremony artifact {}",
            path.display()
        ));
    }
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|error| format!("cannot persist {}: {error}", path.display()))
}

fn read_private_seed(path: &Path) -> Result<zeroize::Zeroizing<[u8; 32]>, String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect private key {}: {error}", path.display()))?;
    if before.file_type().is_symlink() || !before.file_type().is_file() || before.len() != 32 {
        return Err(format!(
            "private key {} is not a 32-byte regular non-symlink file",
            path.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if before.mode() & 0o077 != 0 {
            return Err(format!(
                "private key {} is accessible by group or other users",
                path.display()
            ));
        }
    }

    let mut file = OpenOptions::new()
        .read(true)
        .open(path)
        .map_err(|error| format!("cannot open private key {}: {error}", path.display()))?;
    let after = file.metadata().map_err(|error| {
        format!(
            "cannot inspect opened private key {}: {error}",
            path.display()
        )
    })?;
    if !after.file_type().is_file() || after.len() != 32 {
        return Err(format!(
            "opened private key {} is not exactly 32 bytes",
            path.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if before.dev() != after.dev() || before.ino() != after.ino() || after.mode() & 0o077 != 0 {
            return Err(format!(
                "private key {} changed identity or permissions while opening",
                path.display()
            ));
        }
    }
    let mut seed = zeroize::Zeroizing::new([0_u8; 32]);
    file.read_exact(seed.as_mut())
        .map_err(|error| format!("cannot read private key {}: {error}", path.display()))?;
    let mut extra = [0_u8; 1];
    if file
        .read(&mut extra)
        .map_err(|error| format!("cannot finish private key read {}: {error}", path.display()))?
        != 0
    {
        return Err(format!("private key {} grew while reading", path.display()));
    }
    Ok(seed)
}

fn read_bounded_regular(path: &Path) -> Result<Vec<u8>, String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink()
        || !metadata.file_type().is_file()
        || metadata.len() > MAX_CEREMONY_FILE_BYTES
    {
        return Err(format!(
            "{} is not a bounded regular non-symlink file",
            path.display()
        ));
    }
    fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))
}

fn parse_canonical_json<T>(bytes: &[u8], path: &Path) -> Result<T, String>
where
    T: for<'de> Deserialize<'de> + Serialize,
{
    let value: T = serde_json::from_slice(bytes)
        .map_err(|error| format!("invalid ceremony JSON {}: {error}", path.display()))?;
    if canonical_json_bytes(&value)? != bytes {
        return Err(format!(
            "ceremony JSON {} is not the exact canonical encoding",
            path.display()
        ));
    }
    Ok(value)
}

fn decode_hex_array<const N: usize>(value: &str, label: &str) -> Result<[u8; N], String> {
    let bytes = decode_hex_vec(value, label)?;
    bytes
        .try_into()
        .map_err(|_| format!("{label} is not exactly {N} bytes"))
}

fn decode_hex_vec(value: &str, label: &str) -> Result<Vec<u8>, String> {
    if !value.is_ascii() || !value.len().is_multiple_of(2) {
        return Err(format!("{label} is not canonical even-length hex"));
    }
    (0..value.len() / 2)
        .map(|index| {
            u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
                .map_err(|_| format!("{label} is not canonical lowercase hex"))
        })
        .collect::<Result<Vec<_>, _>>()
        .and_then(|bytes| {
            if hex(&bytes) == value {
                Ok(bytes)
            } else {
                Err(format!("{label} is not canonical lowercase hex"))
            }
        })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn signing_message_digest(message: &[u8]) -> [u8; 32] {
    sha256_domain(SIGNING_MESSAGE_DIGEST_DOMAIN, message)
}

fn sha256_domain(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Ledger;
    use dregg_persist::CommitRecord;
    use tempfile::TempDir;

    struct Member {
        ed: SigningKey,
        pq_public: MlDsaPublicKey,
        pq: MlDsaSigningKey,
    }

    fn members(count: usize) -> Vec<Member> {
        members_from(0x31, count)
    }

    fn members_from(first_seed_byte: u8, count: usize) -> Vec<Member> {
        (0..count)
            .map(|index| {
                let seed = [first_seed_byte + u8::try_from(index).unwrap(); 32];
                let ed = SigningKey::from_bytes(&seed);
                let (pq_public, pq) = MlDsaSigningKey::from_seed(&seed);
                Member { ed, pq_public, pq }
            })
            .collect()
    }

    fn context(member_set: &[Member]) -> AuthenticatedPoaCompactPolicyV1 {
        let committee: Vec<_> = member_set
            .iter()
            .map(|member| member.ed.public_key())
            .collect();
        let pq: Vec<_> = member_set
            .iter()
            .map(|member| member.pq_public.clone())
            .collect();
        let federation =
            dregg_federation::derive_federation_id_hybrid_with_epoch(&committee, &pq, 0);
        let root = PoaCompactTrustRootV1::new(
            [0xD9; 32],
            federation,
            0,
            committee,
            pq,
            dregg_federation::quorum_threshold(member_set.len()),
        )
        .unwrap();
        AuthenticatedPoaCompactPolicyV1 {
            policy: PoaCompactTrustPolicyV1::new(vec![root.clone()]).unwrap(),
            roots: BTreeMap::from([(0, root)]),
            history_heads: BTreeMap::from([(0, [0xA9; 32])]),
            history_head: [0xA9; 32],
        }
    }

    fn record(ordinal: u64) -> CommitRecord {
        let tag = u8::try_from(ordinal + 1).unwrap();
        CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [tag; 32],
            block_executed_up_to: ordinal + 1,
            turn_hash: [tag.wrapping_add(0x20); 32],
            creator: [tag.wrapping_add(0x40); 32],
            receipt_hash: [tag.wrapping_add(0x60); 32],
            ledger_root: dregg_persist::canonical_ledger_root(&Ledger::new()),
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn populated(path: &Path, context: &AuthenticatedPoaCompactPolicyV1) -> PersistentStore {
        let store =
            PersistentStore::open_with_poa_compact_trust_v1(path, context.policy()).unwrap();
        for ordinal in 0..4 {
            store
                .commit_finalized_turn(ordinal, &record(ordinal))
                .unwrap();
        }
        store.checkpoint_ledger(&Ledger::new(), 10).unwrap();
        store
    }

    fn signed_anchor(
        statement: PoaCompactCheckpointStatementV1,
        member_set: &[Member],
        count: usize,
    ) -> SignedPoaCompactCheckpointAnchorV1 {
        let message = statement.signing_message();
        let shares = member_set
            .iter()
            .take(count)
            .map(|member| HybridQuorumSig {
                pubkey: member.ed.public_key(),
                signature: dregg_types::sign(&member.ed, &message),
                ml_dsa_pubkey: member.pq_public.0.to_vec(),
                pq_signature: member.pq.sign(&message).unwrap(),
            })
            .collect();
        SignedPoaCompactCheckpointAnchorV1::new(statement, shares)
    }

    fn hybrid_share(member: &Member, message: &[u8]) -> HybridQuorumSig {
        HybridQuorumSig {
            pubkey: member.ed.public_key(),
            signature: dregg_types::sign(&member.ed, message),
            ml_dsa_pubkey: member.pq_public.0.to_vec(),
            pq_signature: member.pq.sign(message).unwrap(),
        }
    }

    fn write_share_files<'a>(
        directory: &Path,
        label: &str,
        preview: &PoaCompactPreviewFileV1,
        preview_bytes: &[u8],
        selected: impl Iterator<Item = &'a Member>,
    ) -> Vec<PathBuf> {
        let preview_digest = sha256_domain(PREVIEW_DIGEST_DOMAIN, preview_bytes);
        let message = preview.statement.signing_message();
        selected
            .enumerate()
            .map(|(index, member)| {
                let share = hybrid_share(member, &message);
                let file = PoaCompactShareFileV1 {
                    schema: SHARE_SCHEMA.to_owned(),
                    preview_sha256: hex(&preview_digest),
                    signing_message_sha256: hex(&signing_message_digest(&message)),
                    signer_public_key: hex(&share.pubkey.0),
                    ml_dsa_public_key: hex(&share.ml_dsa_pubkey),
                    signature: hex(&share.signature.0),
                    pq_signature: hex(&share.pq_signature),
                };
                let path = directory.join(format!("{label}-{index}.share.json"));
                fs::write(&path, canonical_json_bytes(&file).unwrap()).unwrap();
                path
            })
            .collect()
    }

    fn signed_transition(
        predecessor: [u8; 32],
        deployment_id: [u8; 32],
        old_epoch: u64,
        old_members: &[Member],
        new_members: &[Member],
    ) -> PoaCompactTrustTransitionV1 {
        let new_epoch = old_epoch + 1;
        let new_committee: Vec<_> = new_members
            .iter()
            .map(|member| PoaCompactCommitteeMemberV1 {
                public_key: hex(&member.ed.public_key().0),
                ml_dsa_public_key: hex(&member.pq_public.0),
            })
            .collect();
        let new_ed: Vec<_> = new_members
            .iter()
            .map(|member| member.ed.public_key())
            .collect();
        let new_pq: Vec<_> = new_members
            .iter()
            .map(|member| member.pq_public.clone())
            .collect();
        let mut transition = PoaCompactTrustTransitionV1 {
            predecessor_digest: hex(&predecessor),
            old_committee_epoch: old_epoch,
            new_committee_epoch: new_epoch,
            new_federation_id: hex(&dregg_federation::derive_federation_id_hybrid_with_epoch(
                &new_ed,
                new_pq.as_slice(),
                new_epoch,
            )),
            new_threshold: dregg_federation::quorum_threshold(new_members.len()),
            new_committee,
            hybrid_quorum: Vec::new(),
        };
        transition.hybrid_quorum = encoded_transition_quorum(
            &transition,
            deployment_id,
            old_members
                .iter()
                .take(dregg_federation::quorum_threshold(old_members.len())),
        );
        transition
    }

    fn encoded_transition_quorum<'a>(
        transition: &PoaCompactTrustTransitionV1,
        deployment_id: [u8; 32],
        selected: impl Iterator<Item = &'a Member>,
    ) -> Vec<PoaCompactHybridSignatureV1> {
        let message = transition_signing_message(transition, deployment_id).unwrap();
        selected
            .map(|member| {
                let share = hybrid_share(member, &message);
                PoaCompactHybridSignatureV1 {
                    public_key: hex(&share.pubkey.0),
                    ml_dsa_public_key: hex(&share.ml_dsa_pubkey),
                    signature: hex(&share.signature.0),
                    pq_signature: hex(&share.pq_signature),
                }
            })
            .collect()
    }

    fn rotated_context(
        old_members: &[Member],
        next_members: &[Member],
    ) -> (AuthenticatedPoaCompactPolicyV1, PoaCompactTrustTransitionV1) {
        let base = context(old_members);
        let deployment_id = base.policy().deployment_id();
        let transition = signed_transition(
            base.history_head(),
            deployment_id,
            0,
            old_members,
            next_members,
        );
        let mut roots = base.roots.clone();
        let mut head = base.history_head();
        apply_authenticated_transition(&mut roots, &mut head, deployment_id, &transition).unwrap();
        (
            AuthenticatedPoaCompactPolicyV1 {
                policy: PoaCompactTrustPolicyV1::new(roots.values().cloned().collect()).unwrap(),
                roots,
                history_heads: BTreeMap::from([(0, base.history_head()), (1, head)]),
                history_head: head,
            },
            transition,
        )
    }

    fn mutate_statement_field(
        statement: &PoaCompactCheckpointStatementV1,
        field: &str,
        value: serde_json::Value,
    ) -> PoaCompactCheckpointStatementV1 {
        let mut encoded = serde_json::to_value(statement).unwrap();
        encoded[field] = value;
        serde_json::from_value(encoded).unwrap()
    }

    #[test]
    fn quorum_anchor_converges_across_three_replicas_and_exact_retry_survives_restart() {
        let member_set = members(4);
        let context = context(&member_set);
        let dirs: Vec<_> = (0..3).map(|_| TempDir::new().unwrap()).collect();
        let paths: Vec<_> = dirs
            .iter()
            .map(|dir| dir.path().join("dregg.redb"))
            .collect();
        let stores: Vec<_> = paths.iter().map(|path| populated(path, &context)).collect();
        let root = context.latest_root();
        let statements: Vec<_> = stores
            .iter()
            .map(|store| {
                store
                    .prepare_poa_compact_checkpoint_statement_v1(4, root)
                    .unwrap()
                    .unwrap()
            })
            .collect();
        assert!(
            statements
                .iter()
                .all(|statement| statement == &statements[0])
        );
        let anchor = signed_anchor(statements[0].clone(), &member_set, 3);
        for store in stores {
            assert_eq!(
                store
                    .compact_below_with_poa_anchor_v1(4, anchor.clone(), context.policy())
                    .unwrap(),
                3
            );
        }
        for path in paths {
            let reopened =
                PersistentStore::open_with_poa_compact_trust_v1(&path, context.policy()).unwrap();
            assert_eq!(reopened.commit_compacted_floor().unwrap(), 3);
            assert!(
                reopened
                    .has_exact_poa_compact_checkpoint_anchor_v1(&anchor, context.policy())
                    .unwrap()
            );
            assert_eq!(
                reopened
                    .compact_below_with_poa_anchor_v1(4, anchor.clone(), context.policy())
                    .unwrap(),
                0
            );
        }
    }

    #[test]
    fn lost_response_exact_retry_survives_rotation_but_retired_fresh_witness_refuses() {
        let old_members = members(4);
        let next_members = members_from(0x51, 4);
        let base = context(&old_members);
        let (rotated, _) = rotated_context(&old_members, &next_members);
        let dir = TempDir::new().unwrap();
        let store = populated(&dir.path().join("dregg.redb"), &base);
        let statement = store
            .prepare_poa_compact_checkpoint_statement_v1(4, base.latest_root())
            .unwrap()
            .unwrap();
        drop(store);

        let preview = PoaCompactPreviewFileV1::new(4, base.history_head(), statement);
        let preview_bytes = canonical_json_bytes(&preview).unwrap();
        let quorum_count = dregg_federation::quorum_threshold(old_members.len());
        let original_shares = write_share_files(
            dir.path(),
            "original",
            &preview,
            &preview_bytes,
            old_members.iter().take(quorum_count),
        );
        let committed = finalize_loaded_poa_compact_preview(
            dir.path(),
            &base,
            preview.clone(),
            &preview_bytes,
            &original_shares,
        )
        .unwrap();
        assert_eq!(committed.status, "committed");

        // The response is lost and external history rotates before the coordinator retries.
        // Historical authentication plus exact stored-anchor comparison recovers success.
        let retry = finalize_loaded_poa_compact_preview(
            dir.path(),
            &rotated,
            preview.clone(),
            &preview_bytes,
            &original_shares,
        )
        .unwrap();
        assert_eq!(retry.status, "already_committed_exact_retry");

        // The same historical statement with a different valid old-committee quorum is not the
        // exact stored anchor and therefore cannot turn retired authority into fresh authority.
        let different_shares = write_share_files(
            dir.path(),
            "different",
            &preview,
            &preview_bytes,
            old_members.iter().skip(1).take(quorum_count),
        );
        assert!(
            finalize_loaded_poa_compact_preview(
                dir.path(),
                &rotated,
                preview,
                &preview_bytes,
                &different_shares,
            )
            .is_err()
        );
        let reopened = open_authenticated_store(dir.path(), &rotated).unwrap();
        assert_eq!(reopened.commit_compacted_floor().unwrap(), 3);
    }

    #[test]
    fn partial_quorum_duplicate_and_stale_preview_refuse_without_deletion() {
        let member_set = members(4);
        let context = context(&member_set);
        let dir = TempDir::new().unwrap();
        let store = populated(&dir.path().join("dregg.redb"), &context);
        let statement = store
            .prepare_poa_compact_checkpoint_statement_v1(4, context.latest_root())
            .unwrap()
            .unwrap();
        let partial = signed_anchor(statement.clone(), &member_set, 2);
        assert!(
            store
                .compact_below_with_poa_anchor_v1(4, partial, context.policy())
                .is_err()
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);

        let mut duplicate = signed_anchor(statement.clone(), &member_set, 3);
        let repeated = duplicate.hybrid_quorum()[0].clone();
        duplicate = SignedPoaCompactCheckpointAnchorV1::new(
            statement.clone(),
            vec![repeated.clone(), repeated.clone(), repeated],
        );
        assert!(
            store
                .compact_below_with_poa_anchor_v1(4, duplicate, context.policy())
                .is_err()
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);

        // The latest covering checkpoint is part of the statement, so even a state-equivalent
        // newer checkpoint makes the previously signed preview stale.
        store.checkpoint_ledger(&Ledger::new(), 11).unwrap();
        let stale = signed_anchor(statement, &member_set, 3);
        assert!(
            store
                .compact_below_with_poa_anchor_v1(4, stale, context.policy())
                .is_err()
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);
    }

    #[test]
    fn signer_journal_is_sticky_against_equivocation() {
        let member_set = members(1);
        let dir = TempDir::new().unwrap();
        let path = signer_journal_path(dir.path(), 0, 0, member_set[0].ed.public_key());
        persist_signer_journal(&path, b"first\n").unwrap();
        persist_signer_journal(&path, b"first\n").unwrap();
        assert!(persist_signer_journal(&path, b"second\n").is_err());
        assert_eq!(fs::read(path).unwrap(), b"first\n");
    }

    #[test]
    fn lost_signing_response_reexports_exact_share_after_rotation_only() {
        let old_members = members(4);
        let next_members = members_from(0x51, 4);
        let base = context(&old_members);
        let (rotated, _) = rotated_context(&old_members, &next_members);
        let dir = TempDir::new().unwrap();
        let key = dir.path().join("old-member.key");
        fs::write(&key, [0x31_u8; 32]).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).unwrap();
        }

        let store = populated(&dir.path().join("dregg.redb"), &base);
        let statement = store
            .prepare_poa_compact_checkpoint_statement_v1(4, base.latest_root())
            .unwrap()
            .unwrap();
        drop(store);
        let preview = PoaCompactPreviewFileV1::new(4, base.history_head(), statement);
        let preview_bytes = canonical_json_bytes(&preview).unwrap();

        let first_output = dir.path().join("first.share.json");
        sign_loaded_poa_compact_preview(
            dir.path(),
            &key,
            &base,
            preview.clone(),
            &preview_bytes,
            &first_output,
        )
        .unwrap();
        let first_bytes = fs::read(&first_output).unwrap();

        // The signing response is lost, then the externally authorized committee rotates. The
        // old key can recover only the byte-identical share already committed in its journal.
        let recovered_output = dir.path().join("recovered.share.json");
        sign_loaded_poa_compact_preview(
            dir.path(),
            &key,
            &rotated,
            preview.clone(),
            &preview_bytes,
            &recovered_output,
        )
        .unwrap();
        assert_eq!(fs::read(recovered_output).unwrap(), first_bytes);

        // A different historical preview at the same epoch/floor cannot use recovery as a way to
        // mint a retired-committee signature, and no response artifact is published.
        let mut different = preview;
        different.requested_height += 1;
        let different_bytes = canonical_json_bytes(&different).unwrap();
        let refused_output = dir.path().join("refused.share.json");
        assert!(
            sign_loaded_poa_compact_preview(
                dir.path(),
                &key,
                &rotated,
                different,
                &different_bytes,
                &refused_output,
            )
            .is_err()
        );
        assert!(!refused_output.exists());
    }

    #[cfg(unix)]
    #[test]
    fn sticky_journal_refuses_preexisting_shared_writable_directory() {
        use std::os::unix::fs::PermissionsExt as _;

        let member_set = members(1);
        let dir = TempDir::new().unwrap();
        let journal = dir.path().join("poa-compact-ceremony-v1");
        fs::create_dir(&journal).unwrap();
        fs::set_permissions(&journal, fs::Permissions::from_mode(0o770)).unwrap();
        let path = signer_journal_path(dir.path(), 0, 0, member_set[0].ed.public_key());
        assert!(persist_signer_journal(&path, b"hostile\n").is_err());
        assert!(!path.exists());
    }

    #[test]
    fn wrong_deployment_epoch_federation_checkpoint_and_roster_refuse_without_deletion() {
        let member_set = members(4);
        let context = context(&member_set);
        let dir = TempDir::new().unwrap();
        let store = populated(&dir.path().join("dregg.redb"), &context);
        let statement = store
            .prepare_poa_compact_checkpoint_statement_v1(4, context.latest_root())
            .unwrap()
            .unwrap();

        let wrong_statements = [
            mutate_statement_field(
                &statement,
                "deployment_id",
                serde_json::json!(vec![0xE1_u8; 32]),
            ),
            mutate_statement_field(&statement, "committee_epoch", serde_json::json!(1)),
            mutate_statement_field(
                &statement,
                "federation_id",
                serde_json::json!(vec![0xE2_u8; 32]),
            ),
            mutate_statement_field(
                &statement,
                "checkpoint_height",
                serde_json::json!(statement.checkpoint_height() + 1),
            ),
        ];
        for wrong in wrong_statements {
            let anchor = signed_anchor(wrong, &member_set, 3);
            assert!(
                store
                    .compact_below_with_poa_anchor_v1(4, anchor, context.policy())
                    .is_err()
            );
            assert_eq!(store.commit_compacted_floor().unwrap(), 0);
        }

        let outsider = members_from(0x70, 1).pop().unwrap();
        let message = statement.signing_message();
        let wrong_roster_quorum = vec![
            hybrid_share(&member_set[0], &message),
            hybrid_share(&member_set[1], &message),
            hybrid_share(&outsider, &message),
        ];
        let anchor = SignedPoaCompactCheckpointAnchorV1::new(statement, wrong_roster_quorum);
        assert!(
            store
                .compact_below_with_poa_anchor_v1(4, anchor, context.policy())
                .is_err()
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);
    }

    #[test]
    fn retired_committee_preview_is_refused_before_share_or_finalization_at_floor_zero() {
        let old_members = members(4);
        let next_members = members_from(0x51, 4);
        let (rotated, _) = rotated_context(&old_members, &next_members);
        let dir = TempDir::new().unwrap();
        let store = populated(&dir.path().join("dregg.redb"), &rotated);
        let retired_root = rotated.root_at_epoch(0).unwrap();
        let retired_statement = store
            .prepare_poa_compact_checkpoint_statement_v1(4, retired_root)
            .unwrap()
            .unwrap();
        let retired_preview =
            PoaCompactPreviewFileV1::new(4, rotated.history_head(), retired_statement.clone());

        // Every executable stage calls this validation before signing, importing shares, or
        // opening the compaction transaction. Historical roots remain only for replaying anchors.
        assert!(retired_preview.validate(&rotated).is_err());
        assert!(
            require_fresh_local_preview(&store, rotated.latest_root(), &retired_preview).is_err()
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);

        let active_statement = store
            .prepare_poa_compact_checkpoint_statement_v1(4, rotated.latest_root())
            .unwrap()
            .unwrap();
        let active_preview =
            PoaCompactPreviewFileV1::new(4, rotated.history_head(), active_statement);
        active_preview.validate(&rotated).unwrap();
    }

    #[test]
    fn history_source_and_sticky_epoch_pins_refuse_rotation_rollback_before_store_open() {
        let placeholder = Path::new("history.json");
        assert!(validate_history_source_pair(None, None).is_ok());
        assert!(validate_history_source_pair(Some(placeholder), None).is_err());
        assert!(validate_history_source_pair(None, Some(&"11".repeat(32))).is_err());

        let old_members = members(4);
        let next_members = members_from(0x51, 4);
        let base = context(&old_members);
        let deployment_id = base.policy().deployment_id();
        let transition = signed_transition(
            base.history_head(),
            deployment_id,
            0,
            &old_members,
            &next_members,
        );
        let mut roots = base.roots.clone();
        let mut rotated_head = base.history_head();
        apply_authenticated_transition(&mut roots, &mut rotated_head, deployment_id, &transition)
            .unwrap();
        let base_heads = BTreeMap::from([(0, base.history_head())]);
        let rotated_heads = BTreeMap::from([(0, base.history_head()), (1, rotated_head)]);
        let data = TempDir::new().unwrap();

        enforce_sticky_history_pins(data.path(), deployment_id, &base_heads).unwrap();
        enforce_sticky_history_pins(data.path(), deployment_id, &rotated_heads).unwrap();
        assert!(!data.path().join("dregg.redb").exists());
        assert!(enforce_sticky_history_pins(data.path(), deployment_id, &base_heads).is_err());
        assert!(!data.path().join("dregg.redb").exists());

        let substituted = BTreeMap::from([
            (0, base.history_head()),
            (1, sha256_domain(b"hostile-history-head", &rotated_head)),
        ]);
        assert!(enforce_sticky_history_pins(data.path(), deployment_id, &substituted).is_err());
    }

    #[test]
    fn transition_head_is_canonical_across_valid_quorum_witnesses() {
        let old_members = members(4);
        let next_members = members_from(0x51, 4);
        let base = context(&old_members);
        let deployment_id = base.policy().deployment_id();
        let first = signed_transition(
            base.history_head(),
            deployment_id,
            0,
            &old_members,
            &next_members,
        );
        let mut second = first.clone();
        second.hybrid_quorum =
            encoded_transition_quorum(&second, deployment_id, old_members.iter().skip(1));
        assert_ne!(first.hybrid_quorum, second.hybrid_quorum);

        let mut first_roots = base.roots.clone();
        let mut first_head = base.history_head();
        apply_authenticated_transition(&mut first_roots, &mut first_head, deployment_id, &first)
            .unwrap();
        let mut second_roots = base.roots.clone();
        let mut second_head = base.history_head();
        apply_authenticated_transition(&mut second_roots, &mut second_head, deployment_id, &second)
            .unwrap();
        assert_eq!(first_roots, second_roots);
        assert_eq!(first_head, second_head);
    }

    #[test]
    fn private_seed_requires_owner_only_regular_file() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("node.key");
        fs::write(&path, [0x71_u8; 32]).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
            assert!(read_private_seed(&path).is_err());
            fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        }
        let seed = read_private_seed(&path).unwrap();
        assert_eq!(&*seed, &[0x71_u8; 32]);
    }

    #[test]
    fn committee_rotations_require_exact_predecessor_hybrid_quorum_and_no_downgrade() {
        let old_members = members(4);
        let next_members = members_from(0x51, 4);
        let context = context(&old_members);
        let deployment_id = context.policy().deployment_id();
        let mut roots = context.roots.clone();
        let mut head = context.history_head();
        let base_roots = roots.clone();
        let base_head = head;
        let valid = signed_transition(base_head, deployment_id, 0, &old_members, &next_members);

        apply_authenticated_transition(&mut roots, &mut head, deployment_id, &valid).unwrap();
        assert_eq!(roots.len(), 2);
        assert_eq!(roots.last_key_value().unwrap().0, &1);
        assert_ne!(head, base_head);

        let retained_roots = roots.clone();
        let retained_head = head;
        assert!(
            apply_authenticated_transition(&mut roots, &mut head, deployment_id, &valid).is_err()
        );
        assert_eq!(roots, retained_roots);
        assert_eq!(head, retained_head);

        let mut skipped = valid.clone();
        skipped.new_committee_epoch = 2;
        let mut trial_roots = base_roots.clone();
        let mut trial_head = base_head;
        assert!(
            apply_authenticated_transition(
                &mut trial_roots,
                &mut trial_head,
                deployment_id,
                &skipped,
            )
            .is_err()
        );
        assert_eq!(trial_roots, base_roots);
        assert_eq!(trial_head, base_head);

        let mut partial = valid.clone();
        partial.hybrid_quorum.pop();
        assert!(
            apply_authenticated_transition(
                &mut trial_roots,
                &mut trial_head,
                deployment_id,
                &partial,
            )
            .is_err()
        );
        assert_eq!(trial_roots, base_roots);
        assert_eq!(trial_head, base_head);

        let mut downgraded = valid;
        downgraded.new_threshold = 1;
        assert!(
            apply_authenticated_transition(
                &mut trial_roots,
                &mut trial_head,
                deployment_id,
                &downgraded,
            )
            .is_err()
        );
        assert_eq!(trial_roots, base_roots);
        assert_eq!(trial_head, base_head);
    }
}
