//! Operator-only activation of the Path of Angels Galley world.
//!
//! Until this module existed, `install_poa_world_curator_pin_v1`,
//! `install_poa_world_activation_v1` and `install_poa_activated_content_v1` were
//! `pub` with every call site inside `#[cfg(test)]`: a fully audited cold start
//! that production never invoked. The live validator therefore failed at
//! `prepare_active_poa_galley_policy_v1_in` with "PoA world has no installed
//! content manifest", the HTTP surface answered 503, and the browser rendered
//! GALLEY SEALED. This is the ceremony that opens the organ.
//!
//! # What this module decides, and what it must not
//!
//! It owns **ceremony plumbing only**. It authenticates the immutable
//! deployment/genesis/POAG1 tuple with `poa-curator` exactly as
//! [`crate::poa_signal_genesis`] does, derives the world identity that tuple
//! plus the authored manifest determines, and then calls the three existing
//! `dregg-persist` installers in order. It contains no manifest parser, no
//! policy parser, no transition, and no signature minting:
//!
//! * the **manifest bytes are passed through verbatim**. Lean
//!   (`ActivatedContent.decodeManifest`) re-encodes them and demands byte
//!   equality, recomputes every component SHA-256 and recomputes the manifest
//!   root. A manifest this module mis-handles refuses; it never reinterprets.
//! * the **curator signature is an input**. The node holds no curator key. The
//!   signature is verified inside `install_poa_world_activation_v1` against the
//!   independently distributed pin loaded from `--curator-key-pin`, over bytes
//!   that `dregg-persist` derives itself
//!   (`PoaWorldActivationStatementV1::signing_message`). Nothing here can make
//!   an unsigned world active.
//! * the **world identity is derived, not accepted**. `federation_id` comes
//!   from the verified deployment manifest, `activation_digest` from the
//!   verified POAG1 content-epoch envelope, `content_root` from SHA-256 of the
//!   manifest file, `content_epoch` from the verified envelope. The signed
//!   envelope's world must equal that derivation field for field, so a curator
//!   signature over a foreign world refuses **before** the store is opened.
//!
//! `content_session` is the one world field with no independent source in this
//! repo. It is an operator input (`--content-session`) that must equal the
//! authored manifest's `scope.content_session`; Lean refuses the install
//! otherwise (`Manifest.matchesWorldB`). It is not checked here, because
//! checking it would require a second manifest grammar in Rust.
//!
//! # The ceremony: two node commands with a curator signature between them
//!
//! ```text
//! 1. dregg-node poa-galley-world-preview …   → the exact world + signing message
//! 2. the curator signs that message with the pinned Ed25519 key
//!                                            → activation.sig.json
//! 3. dregg-node init-poa-galley-world  …     → pin, activation, manifest
//! ```
//!
//! Step 1 exists so the curator never has to re-derive `activation_digest` or
//! re-implement the canonical statement encoding: the node prints the exact
//! bytes to sign, using the same code that will verify them.
//!
//! # Exactly what the curator ceremony must emit
//!
//! Two files, and nothing else. The curator never sees the database.
//!
//! **1. The key pin** — `poa/config/curator-key.json`, which already exists and
//! is unchanged by this ceremony:
//!
//! ```json
//! {"schema":"POA-CURATOR-KEY-V1","curator_pubkey":"<64 lowercase hex>"}
//! ```
//!
//! The same pin gates the POAG1 content epoch and, once installed, every world
//! activation for the life of the store: `install_poa_world_curator_pin_v1`
//! accepts an identical retry and refuses substitution forever.
//!
//! **2. The signed activation** — `POA-WORLD-ACTIVATION-ENVELOPE-V1`, exactly
//! these ten fields, no others (unknown fields refuse):
//!
//! ```json
//! {
//!   "schema": "POA-WORLD-ACTIVATION-ENVELOPE-V1",
//!   "world": {
//!     "federation_id": "<hex32>", "content_root": "<hex32>",
//!     "activation_digest": "<hex32>", "content_session": "<hex32>",
//!     "content_epoch": 1
//!   },
//!   "counter": 1,
//!   "predecessor_head": "<hex32, all zeroes for the first world>",
//!   "kind": "advance",
//!   "rollback_target": null,
//!   "curator_key": "<hex32, equal to the pin>",
//!   "signature": "<hex64>"
//! }
//! ```
//!
//! `world`, `counter`, `predecessor_head`, `kind` and `rollback_target` must be
//! copied verbatim from the preview document. The `signature` is Ed25519 over
//! **the preview's `signing_message` bytes**, which are
//! `PoaWorldActivationStatementV1::signing_message` — canonical, compact,
//! key-ordered JSON:
//!
//! ```json
//! {"schema":"POA-WORLD-ACTIVATION-STATEMENT-1","world":{"federation_id":"…","content_root":"…","activation_digest":"…","content_session":"…","content_epoch":1},"counter":1,"predecessor_head":"…","kind":"advance","rollback_target":null}
//! ```
//!
//! Signing anything else — the envelope file, a pretty-printed statement, a
//! digest of the statement — produces a signature that
//! `install_poa_world_activation_v1` refuses. The preview's
//! `signing_message_sha256` is there so the two sides can compare one number
//! before the key is touched.

use std::fs;
use std::path::{Path, PathBuf};

use dregg_persist::poa_world_activation::{
    POA_WORLD_ACTIVATION_STATEMENT_SCHEMA_V1, PoaWorldActivationInstallStatusV1,
};
use dregg_persist::{
    PersistentStore, PoaActivatedContentInstallStatusV1, PoaWorldActivationKindV1,
    PoaWorldActivationStatementV1, PoaWorldIdentityV2, SignedPoaWorldActivationEnvelopeV1,
};
use poa_curator::{ContentEpochEnvelope, CuratorKeyPin, PoaDeploymentScope, Poag1Bundle};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

/// Schema of the preview document this module emits for the curator to sign.
pub const PREVIEW_SCHEMA: &str = "POA-WORLD-ACTIVATION-PREVIEW-V1";
/// Schema of the signed envelope document the curator ceremony must emit.
pub const ENVELOPE_SCHEMA: &str = "POA-WORLD-ACTIVATION-ENVELOPE-V1";

const MAX_MANIFEST_BYTES: u64 = 1024 * 1024;
const ADVANCE: &str = "advance";
const ROLLBACK: &str = "rollback";

/// Inputs shared by the preview and the install. Every one of them is an
/// immutable file the operator already holds for `init-poa-signal`, plus the
/// authored activated-content manifest.
#[derive(Clone, Debug)]
pub struct PoaGalleyWorldArgs {
    pub data_dir: PathBuf,
    pub deployment_manifest: PathBuf,
    pub genesis: PathBuf,
    pub main_data_dir: PathBuf,
    pub poag1_manifest: PathBuf,
    pub content_envelope: PathBuf,
    pub curator_key_pin: PathBuf,
    /// The exact canonical `POA-ACTIVATED-CONTENT-MANIFEST-1` bytes.
    pub content_manifest: PathBuf,
    /// Lowercase hex32; must equal the manifest's `scope.content_session`.
    pub content_session: String,
    /// Caller-owned expected POAG1 content epoch (rollback refusal).
    pub expected_content_epoch: u64,
    /// Caller-owned expected POAG1 content-epoch envelope counter.
    pub expected_activation_counter: u64,
}

/// The activation statement coordinates the curator is asked to sign.
#[derive(Clone, Debug)]
pub struct PoaGalleyActivationCoordinates {
    /// World-activation lineage counter. `1` for the first world; each later
    /// activation must advance it.
    pub counter: u64,
    /// Digest of the predecessor activation envelope; all zeroes for the first.
    pub predecessor_head: String,
    /// `advance` or `rollback`.
    pub kind: String,
    /// Required for `rollback`, forbidden for `advance`.
    pub rollback_target: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaGalleyGenesisReport {
    pub curator_pin: [u8; 32],
    pub world: PoaWorldIdentityV2,
    pub world_counter: u64,
    pub activation_status: PoaWorldActivationInstallStatusV1,
    pub content_status: PoaActivatedContentInstallStatusV1,
    /// SHA-256 of the installed Galley policy component. There is deliberately
    /// no `manifest_sha256` field: it is `world.content_root()` by construction,
    /// and a second copy is a value that can later disagree with itself.
    pub component_sha256: [u8; 32],
    /// SHA-256 of the exact bytes the curator signed.
    pub statement_sha256: [u8; 32],
}

/// Everything the immutable inputs determine, established before any store is
/// opened and before any signature is consulted.
#[derive(Clone, Debug)]
struct AuthenticatedGalleyWorld {
    curator_pin: [u8; 32],
    world: PoaWorldIdentityV2,
    manifest_bytes: Vec<u8>,
}

/// Emit the exact world identity and the exact canonical bytes the curator must
/// sign. Opens nothing, mutates nothing, and holds no key material.
pub fn preview_poa_galley_world(
    args: &PoaGalleyWorldArgs,
    coordinates: &PoaGalleyActivationCoordinates,
) -> Result<String, String> {
    let authenticated = authenticate_inputs(args)?;
    let statement = build_statement(&authenticated.world, coordinates)?;
    let signing_message = statement
        .signing_message()
        .map_err(|error| format!("PoA Galley activation statement refused: {error}"))?;
    let signing_message = String::from_utf8(signing_message)
        .map_err(|_| "PoA Galley activation signing message is not UTF-8".to_owned())?;
    let preview = PreviewDocument {
        schema: PREVIEW_SCHEMA,
        statement_schema: POA_WORLD_ACTIVATION_STATEMENT_SCHEMA_V1,
        world: WorldDocument::from(&authenticated.world),
        counter: coordinates.counter,
        predecessor_head: coordinates.predecessor_head.clone(),
        kind: coordinates.kind.clone(),
        rollback_target: coordinates.rollback_target.clone(),
        curator_key: hex(&authenticated.curator_pin),
        signing_message_sha256: hex(&sha256(signing_message.as_bytes())),
        signing_message,
    };
    serde_json::to_string_pretty(&preview)
        .map_err(|error| format!("cannot encode PoA Galley activation preview: {error}"))
}

/// Install, in order, the curator pin, the signed world activation, and the
/// activated-content manifest, then re-audit both authorities and prove the
/// Galley policy carrier the HTTP surface uses can actually be produced.
pub fn initialize_poa_galley_world(
    args: &PoaGalleyWorldArgs,
    signed_activation: &Path,
) -> Result<PoaGalleyGenesisReport, String> {
    let authenticated = authenticate_inputs(args)?;
    let document = load_envelope_document(signed_activation)?;
    let (envelope, statement_digest) = document.into_verified_envelope(&authenticated)?;
    let world_counter = envelope.statement().counter();

    // Opening happens only after every immutable byte, the derived world and the
    // envelope's shape have been accepted.
    let store = PersistentStore::open(&args.data_dir.join("dregg.redb"))
        .map_err(|error| format!("failed to open PoA store: {error}"))?;
    store
        .install_poa_world_curator_pin_v1(authenticated.curator_pin)
        .map_err(|error| format!("PoA curator pin refused: {error}"))?;
    let activation = store
        .install_poa_world_activation_v1(envelope)
        .map_err(|error| format!("PoA world activation refused: {error}"))?;
    if activation.active_head().world() != &authenticated.world {
        return Err("installed PoA activation head is not the derived Galley world".into());
    }
    let content = store
        .install_poa_activated_content_v1(authenticated.manifest_bytes)
        .map_err(|error| format!("PoA activated content refused: {error}"))?;

    store
        .audit_poa_world_activation_v1()
        .map_err(|error| format!("PoA world-activation post-install audit failed: {error}"))?;
    store
        .audit_poa_activated_content_v1()
        .map_err(|error| format!("PoA activated-content post-install audit failed: {error}"))?;
    // The organ is "open" exactly when this producer succeeds: it is the same
    // call `observe_active_poa_galley_v1` makes at step 1 of every HTTP read.
    let policy = store
        .load_authenticated_poa_galley_policy_v1()
        .map_err(|error| format!("PoA Galley policy carrier refused after install: {error}"))?;
    if policy.world() != &authenticated.world
        || policy.manifest_root() != authenticated.world.content_root()
    {
        return Err("authenticated PoA Galley policy does not bind the installed world".into());
    }

    Ok(PoaGalleyGenesisReport {
        curator_pin: authenticated.curator_pin,
        world: authenticated.world,
        world_counter,
        activation_status: activation.status(),
        content_status: content.status(),
        component_sha256: policy.component_sha256(),
        statement_sha256: statement_digest,
    })
}

fn authenticate_inputs(args: &PoaGalleyWorldArgs) -> Result<AuthenticatedGalleyWorld, String> {
    let data_metadata = fs::metadata(&args.data_dir)
        .map_err(|error| format!("PoA data directory is unavailable: {error}"))?;
    if !data_metadata.is_dir() {
        return Err("PoA data path is not a directory".into());
    }

    let deployment = PoaDeploymentScope::load_verified(
        &args.deployment_manifest,
        &args.genesis,
        &args.main_data_dir,
    )
    .map_err(|error| format!("PoA deployment/genesis tuple refused: {error}"))?;
    deployment
        .verify_serving_data_dir(&args.data_dir, None)
        .map_err(|error| format!("PoA serving directory refused: {error}"))?;
    let federation_id = parse_hex32(deployment.federation_id(), "deployment federation_id")?;

    let bundle = Poag1Bundle::load(&args.poag1_manifest)
        .map_err(|error| format!("POAG1 bundle refused: {error}"))?;
    let bound = bundle
        .bind_deployment_scope(deployment)
        .map_err(|error| format!("POAG1 deployment binding refused: {error}"))?;
    let content_envelope = ContentEpochEnvelope::load(&args.content_envelope)
        .map_err(|error| format!("PoA content envelope refused: {error}"))?;
    let key_pin = CuratorKeyPin::load(&args.curator_key_pin)
        .map_err(|error| format!("PoA curator key pin refused: {error}"))?;
    let verified = content_envelope
        .verify(
            &bound,
            &key_pin,
            args.expected_content_epoch,
            args.expected_activation_counter,
        )
        .map_err(|error| format!("PoA content signature refused: {error}"))?;
    // The pin this ceremony installs is the key that just verified the POAG1
    // content-epoch signature, not a second parse of the same file: one key
    // gates content epochs and world activations for the life of the store.
    let curator_pin = verified.public_key().0;
    let activation_digest = parse_hex32(
        bare_sha(&verified.activation_digest(), "activation digest")?.as_str(),
        "activation digest",
    )?;

    let manifest_bytes = read_content_manifest(&args.content_manifest)?;
    let content_root = sha256(&manifest_bytes);
    let content_session = parse_hex32(&args.content_session, "content session")?;
    if verified.envelope().content_epoch != args.expected_content_epoch {
        return Err("verified POAG1 content epoch is not the expected epoch".into());
    }

    let world = PoaWorldIdentityV2::new(
        federation_id,
        content_root,
        activation_digest,
        content_session,
        args.expected_content_epoch,
    )
    .map_err(|error| format!("derived PoA Galley world refused: {error}"))?;

    Ok(AuthenticatedGalleyWorld {
        curator_pin,
        world,
        manifest_bytes,
    })
}

/// Read the exact canonical manifest bytes. Surrounding whitespace is refused
/// here rather than at the Lean re-encode, because "your editor added a newline"
/// deserves a better message than a bare content-manifest rejection.
fn read_content_manifest(path: &Path) -> Result<Vec<u8>, String> {
    let metadata = fs::metadata(path)
        .map_err(|error| format!("PoA activated-content manifest is unavailable: {error}"))?;
    if !metadata.is_file() {
        return Err("PoA activated-content manifest is not a regular file".into());
    }
    if metadata.len() == 0 || metadata.len() > MAX_MANIFEST_BYTES {
        return Err("PoA activated-content manifest is empty or exceeds 1 MiB".into());
    }
    let bytes = fs::read(path)
        .map_err(|error| format!("PoA activated-content manifest is unreadable: {error}"))?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|_| "PoA activated-content manifest is not UTF-8".to_owned())?;
    if text.trim() != text {
        return Err(
            "PoA activated-content manifest has leading or trailing whitespace; the canonical \
             manifest is exact bytes and a stray newline changes content_root"
                .into(),
        );
    }
    Ok(bytes)
}

fn build_statement(
    world: &PoaWorldIdentityV2,
    coordinates: &PoaGalleyActivationCoordinates,
) -> Result<PoaWorldActivationStatementV1, String> {
    let kind = match coordinates.kind.as_str() {
        ADVANCE => PoaWorldActivationKindV1::Advance,
        ROLLBACK => PoaWorldActivationKindV1::Rollback,
        other => {
            return Err(format!(
                "PoA activation kind {other} is not advance/rollback"
            ));
        }
    };
    let rollback_target = coordinates
        .rollback_target
        .as_deref()
        .map(|target| parse_hex32(target, "rollback target"))
        .transpose()?;
    PoaWorldActivationStatementV1::new(
        world.clone(),
        coordinates.counter,
        parse_hex32(&coordinates.predecessor_head, "predecessor head")?,
        kind,
        rollback_target,
    )
    .map_err(|error| format!("PoA Galley activation statement refused: {error}"))
}

#[derive(Serialize)]
struct PreviewDocument {
    schema: &'static str,
    statement_schema: &'static str,
    world: WorldDocument,
    counter: u64,
    predecessor_head: String,
    kind: String,
    rollback_target: Option<String>,
    curator_key: String,
    signing_message: String,
    signing_message_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct WorldDocument {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
}

impl From<&PoaWorldIdentityV2> for WorldDocument {
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

/// The exact document the curator ceremony must emit. Unknown fields refuse.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct EnvelopeDocument {
    schema: String,
    world: WorldDocument,
    counter: u64,
    predecessor_head: String,
    kind: String,
    rollback_target: Option<String>,
    curator_key: String,
    signature: String,
}

impl EnvelopeDocument {
    /// Bind the curator's signed statement to the world the immutable inputs
    /// determined. The Ed25519 verification itself belongs to
    /// `install_poa_world_activation_v1`; this only refuses a signature that is
    /// about some other world, key, or shape before the store is opened.
    fn into_verified_envelope(
        self,
        authenticated: &AuthenticatedGalleyWorld,
    ) -> Result<(SignedPoaWorldActivationEnvelopeV1, [u8; 32]), String> {
        if self.schema != ENVELOPE_SCHEMA {
            return Err(format!(
                "PoA activation envelope schema {} is not {ENVELOPE_SCHEMA}",
                self.schema
            ));
        }
        let expected_world = WorldDocument::from(&authenticated.world);
        if self.world != expected_world {
            return Err(
                "signed PoA activation names a different world than the authenticated \
                 deployment, POAG1 content epoch and manifest determine"
                    .into(),
            );
        }
        let curator_key = parse_hex32(&self.curator_key, "envelope curator key")?;
        if curator_key != authenticated.curator_pin {
            return Err("signed PoA activation names a key other than the installed pin".into());
        }
        let signature = parse_hex64(&self.signature, "envelope signature")?;
        let statement = build_statement(
            &authenticated.world,
            &PoaGalleyActivationCoordinates {
                counter: self.counter,
                predecessor_head: self.predecessor_head,
                kind: self.kind,
                rollback_target: self.rollback_target,
            },
        )?;
        let statement_digest = sha256(
            &statement
                .signing_message()
                .map_err(|error| format!("PoA Galley activation statement refused: {error}"))?,
        );
        let envelope = SignedPoaWorldActivationEnvelopeV1::new(statement, curator_key, signature)
            .map_err(|error| format!("PoA activation envelope refused: {error}"))?;
        Ok((envelope, statement_digest))
    }
}

fn load_envelope_document(path: &Path) -> Result<EnvelopeDocument, String> {
    let metadata = fs::metadata(path)
        .map_err(|error| format!("PoA activation envelope is unavailable: {error}"))?;
    if !metadata.is_file() {
        return Err("PoA activation envelope is not a regular file".into());
    }
    if metadata.len() == 0 || metadata.len() > 64 * 1024 {
        return Err("PoA activation envelope is empty or exceeds 64 KiB".into());
    }
    let bytes = fs::read(path)
        .map_err(|error| format!("PoA activation envelope is unreadable: {error}"))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("PoA activation envelope is not the exact document: {error}"))
}

fn bare_sha(value: &str, label: &str) -> Result<String, String> {
    let bare = value
        .strip_prefix("sha256:")
        .ok_or_else(|| format!("{label} is not a tagged SHA-256 digest"))?;
    parse_hex32(bare, label)?;
    Ok(bare.to_owned())
}

fn parse_hex32(value: &str, label: &str) -> Result<[u8; 32], String> {
    let bytes = parse_hex(value, 32, label)?;
    let mut output = [0u8; 32];
    output.copy_from_slice(&bytes);
    Ok(output)
}

fn parse_hex64(value: &str, label: &str) -> Result<[u8; 64], String> {
    let bytes = parse_hex(value, 64, label)?;
    let mut output = [0u8; 64];
    output.copy_from_slice(&bytes);
    Ok(output)
}

fn parse_hex(value: &str, length: usize, label: &str) -> Result<Vec<u8>, String> {
    if value.len() != length * 2
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!(
            "{label} is not exactly {length} lowercase hex bytes"
        ));
    }
    Ok(value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]))
        .collect())
}

fn hex_nibble(value: u8) -> u8 {
    match value {
        b'0'..=b'9' => value - b'0',
        b'a'..=b'f' => value - b'a' + 10,
        _ => unreachable!("hex was validated"),
    }
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    output
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    fn repo() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .to_path_buf()
    }

    fn authored_manifest() -> Vec<u8> {
        fs::read(repo().join("poa/artifacts/galley/epoch-1/manifest.json"))
            .expect("authored Galley manifest")
    }

    fn authored_policy() -> Vec<u8> {
        fs::read(repo().join("poa/artifacts/galley/epoch-1/policy.json"))
            .expect("authored Galley policy")
    }

    fn authored_world(manifest: &[u8]) -> PoaWorldIdentityV2 {
        // `content_session` and `federation_id` must be the manifest's own scope
        // or Lean refuses; the activation digest is only required to be nonzero.
        PoaWorldIdentityV2::new(
            parse_hex32(
                "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a",
                "federation",
            )
            .unwrap(),
            sha256(manifest),
            [0xa1; 32],
            parse_hex32(
                "504f412d47414c4c45592d310000000000000000000000000000000000000000",
                "session",
            )
            .unwrap(),
            1,
        )
        .expect("authored Galley world")
    }

    #[test]
    fn authored_manifest_embeds_the_authored_policy_byte_for_byte() {
        let manifest = String::from_utf8(authored_manifest()).expect("manifest is UTF-8");
        let policy = String::from_utf8(authored_policy()).expect("policy is UTF-8");
        let quoted = serde_json::to_string(&policy).expect("quoted policy");
        assert!(
            manifest.contains(&format!("\"bytes_utf8\":{quoted}")),
            "the manifest must carry the authored policy verbatim",
        );
        assert!(
            manifest.contains(&format!(
                "\"sha256\":\"{}\"",
                hex(&sha256(policy.as_bytes()))
            )),
            "the component digest must be SHA-256 of the authored policy bytes",
        );
        assert!(
            manifest.contains("\"name\":\"poa.galley-maintenance-daily.policy.v1\""),
            "the reserved Galley component name is fixed by ActivatedContent.lean:54",
        );
        assert_eq!(
            manifest.trim(),
            manifest,
            "canonical bytes carry no padding"
        );
        assert_eq!(policy.trim(), policy, "canonical bytes carry no padding");
    }

    /// The end-to-end proof that the *authored production content* opens the
    /// organ: install it under a test curator pin and require that the exact
    /// producer used by every HTTP read succeeds.
    ///
    /// The real pin (`poa/config/curator-key.json`) cannot appear here — this
    /// process holds no curator key, which is the point — so this exercises the
    /// store-side half with a locally generated key. The deployment-binding half
    /// is covered by `authenticate_inputs` and its own refusal tests.
    #[test]
    fn authored_content_opens_the_galley_organ() {
        let manifest = authored_manifest();
        let world = authored_world(&manifest);
        let curator = SigningKey::from_bytes(&[0x67; 32]);
        let store = PersistentStore::open_in_memory().expect("store");
        store
            .install_poa_world_curator_pin_v1(curator.verifying_key().to_bytes())
            .expect("curator pin");
        let statement = PoaWorldActivationStatementV1::new(
            world.clone(),
            1,
            [0; 32],
            PoaWorldActivationKindV1::Advance,
            None,
        )
        .expect("statement");
        let signature = curator.sign(&statement.signing_message().expect("signing message"));
        let envelope = SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            curator.verifying_key().to_bytes(),
            signature.to_bytes(),
        )
        .expect("envelope");
        store
            .install_poa_world_activation_v1(envelope)
            .expect("active world");
        store
            .install_poa_activated_content_v1(manifest)
            .expect("activated content");

        let policy = store
            .load_authenticated_poa_galley_policy_v1()
            .expect("the authored manifest must yield a Galley policy carrier");
        assert_eq!(policy.world(), &world);
        assert_eq!(policy.manifest_root(), world.content_root());
        assert_eq!(policy.component_sha256(), sha256(&authored_policy()));

        // Step 1 of every `/api/poa/galley/v1/*` read. Before this ceremony it
        // failed with "PoA world has no installed content manifest" -> 503.
        let observation = store
            .observe_active_poa_galley_v1([0x33; 32])
            .expect("the installed world must be observable");
        assert_eq!(observation.world(), &world);
        assert_eq!(observation.sequence(), 0);
        assert_eq!(
            observation.actions().len(),
            1,
            "a fresh player is offered exactly one public play",
        );
        assert_eq!(observation.actions()[0].expires_after_sequence(), 0);
        assert!(observation.events().is_empty());
    }

    #[test]
    fn a_manifest_with_a_stray_newline_refuses_before_anything_opens() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("manifest.json");
        let mut bytes = authored_manifest();
        bytes.push(b'\n');
        fs::write(&path, &bytes).expect("write");
        let error = read_content_manifest(&path).expect_err("trailing newline must refuse");
        assert!(error.contains("trailing whitespace"), "{error}");
    }

    #[test]
    fn envelope_document_binds_key_world_and_shape() {
        let manifest = authored_manifest();
        let authenticated = AuthenticatedGalleyWorld {
            curator_pin: [0x71; 32],
            world: authored_world(&manifest),
            manifest_bytes: manifest,
        };
        let world = WorldDocument::from(&authenticated.world);
        let good = EnvelopeDocument {
            schema: ENVELOPE_SCHEMA.to_owned(),
            world: world.clone(),
            counter: 1,
            predecessor_head: "00".repeat(32),
            kind: ADVANCE.to_owned(),
            rollback_target: None,
            curator_key: hex(&authenticated.curator_pin),
            signature: "ab".repeat(64),
        };
        good.into_verified_envelope(&authenticated)
            .expect("well formed envelope");

        let mut foreign_world = world.clone();
        foreign_world.content_root = "cd".repeat(32);
        let error = EnvelopeDocument {
            schema: ENVELOPE_SCHEMA.to_owned(),
            world: foreign_world,
            counter: 1,
            predecessor_head: "00".repeat(32),
            kind: ADVANCE.to_owned(),
            rollback_target: None,
            curator_key: hex(&authenticated.curator_pin),
            signature: "ab".repeat(64),
        }
        .into_verified_envelope(&authenticated)
        .expect_err("a signature over a foreign world must refuse");
        assert!(error.contains("different world"), "{error}");

        let error = EnvelopeDocument {
            schema: ENVELOPE_SCHEMA.to_owned(),
            world: world.clone(),
            counter: 1,
            predecessor_head: "00".repeat(32),
            kind: ADVANCE.to_owned(),
            rollback_target: None,
            curator_key: "0f".repeat(32),
            signature: "ab".repeat(64),
        }
        .into_verified_envelope(&authenticated)
        .expect_err("a foreign curator key must refuse");
        assert!(error.contains("installed pin"), "{error}");

        let error = EnvelopeDocument {
            schema: ENVELOPE_SCHEMA.to_owned(),
            world,
            counter: 1,
            predecessor_head: "00".repeat(32),
            kind: ADVANCE.to_owned(),
            rollback_target: Some("11".repeat(32)),
            curator_key: hex(&authenticated.curator_pin),
            signature: "ab".repeat(64),
        }
        .into_verified_envelope(&authenticated)
        .expect_err("an advance carrying a rollback target must refuse");
        assert!(error.contains("rollback target"), "{error}");
    }

    #[test]
    fn envelope_document_refuses_unknown_fields() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("activation.sig.json");
        fs::write(
            &path,
            br#"{"schema":"POA-WORLD-ACTIVATION-ENVELOPE-V1","world":{"federation_id":"00","content_root":"00","activation_digest":"00","content_session":"00","content_epoch":1},"counter":1,"predecessor_head":"00","kind":"advance","rollback_target":null,"curator_key":"00","signature":"00","audited":true}"#,
        )
        .expect("write");
        let error = load_envelope_document(&path).expect_err("unknown field must refuse");
        assert!(error.contains("exact document"), "{error}");
    }
}
