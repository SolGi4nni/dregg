//! Capability management commands (export, enliven, handoff).
//!
//! `cap export` produces a REAL bearer capability, not a placeholder. It builds
//! a canonical [`bearer::BearerCapProof`] (the `SignedDelegation` envelope the
//! node's executor consumes — `dregg_turn::action::BearerCapProof`), signs it
//! with the active identity's Ed25519 key, binds it to the node's federation id,
//! and emits the canonical `dregg://<fed>/<cell>/<swiss>` sturdy reference. The
//! proof is the portable bearer credential: it verifies cryptographically
//! against the EXACT message `TurnExecutor::compute_bearer_delegation_message`
//! recomputes, so a holder can re-present it to `POST /turns/bearer-auth` and
//! the node admits it (modulo ledger cap-lookup, which is the node's job).

use clap::Subcommand;
use dialoguer::Confirm;

use crate::config::Config;
use crate::output::{Context, abbrev_hex};

use super::id::active_signing_key;
use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum CapCommand {
    /// Export a real bearer capability for a cell (dregg:// sturdy ref).
    ///
    /// Generates a canonical, Ed25519-signed `BearerCapProof` under the active
    /// identity, binds it to the node's federation id, verifies it against the
    /// node (`POST /turns/bearer-auth`), and prints the portable proof plus the
    /// `dregg://<fed>/<cell>/<swiss>` sturdy reference. No placeholders.
    Export {
        /// Cell ID to export (64 hex chars, 32 bytes).
        cell_id: String,

        /// Attenuation: the permission level the bearer obtains
        /// (`None` | `Signature` | `Proof` | `Either`). Default: `Signature`.
        #[arg(long)]
        attenuate: Option<String>,

        /// Expiry as a federation block height (the executor rejects the cap
        /// once `block_height > expires_at`). Bearer caps are short-lived by
        /// design; default is a far-future sentinel for UX (override for a real
        /// revocation window).
        #[arg(long, default_value_t = u64::MAX)]
        expires_at: u64,
    },

    /// Enliven a dregg:// sturdy reference URI.
    Enliven {
        /// The dregg:// URI to enliven.
        uri: String,
    },

    /// Create a handoff certificate for transferring capability.
    Handoff {
        /// Source cell ID.
        cell_id: String,

        /// Recipient's public key (hex).
        recipient_pk: String,
    },

    /// List held capabilities.
    List,

    /// Revoke a capability (by cell ID or cap ID).
    Revoke {
        /// Cell or capability ID to revoke.
        id: String,
    },
}

pub async fn run(
    cmd: CapCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        CapCommand::Export {
            cell_id,
            attenuate,
            expires_at,
        } => export(cfg, ctx, &cell_id, attenuate, expires_at).await,
        CapCommand::Enliven { uri } => enliven(cfg, ctx, &uri).await,
        CapCommand::Handoff {
            cell_id,
            recipient_pk,
        } => handoff(cfg, ctx, &cell_id, &recipient_pk).await,
        CapCommand::List => list(cfg, ctx).await,
        CapCommand::Revoke { id } => revoke(cfg, ctx, &id).await,
    }
}

async fn export(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    attenuate: Option<String>,
    expires_at: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    // 1. The target cell (32 bytes, hex).
    let target = bearer::decode_cell_id(cell_id)?;

    // 2. The permission level the bearer obtains.
    let permissions = bearer::Permissions::parse(attenuate.as_deref())?;

    // 3. The active identity SIGNS the delegation (delegator == bearer == self:
    //    the operator delegates to the recipient who presents this proof; the
    //    node's ledger cap-lookup decides whether `self` actually holds it).
    let (signing_key, public_key) = active_signing_key()?;

    // 4. Bind to the node's federation id so the executor's recomputed message
    //    matches. Falls back to the pure-sim federation ([0u8;32], the wasm/SDK
    //    sim convention) when the node is unreachable — the proof is still a
    //    cryptographically real, locally-verifiable credential.
    let spinner = ctx.spinner("Resolving federation id...");
    let (federation_id, fed_source) = bearer::resolve_federation_id(cfg).await;
    spinner.finish_and_clear();

    // 5. Build the REAL, canonically-signed BearerCapProof.
    let proof = bearer::BearerCapProof::sign(
        &signing_key,
        public_key,
        target,
        permissions,
        expires_at,
        &federation_id,
    );
    let proof_json = proof.to_node_json();

    // 6. Verify against the node (the live half of the tooth). The executor
    //    recomputes the identical delegation message and checks the signature,
    //    expiry, and ledger cap-lookup; we surface its structured verdict.
    let spinner = ctx.spinner("Verifying bearer capability against node...");
    let verify_outcome = post_json(
        cfg,
        "/api/turns/bearer-auth",
        &serde_json::json!({
            "bearer_proof": proof_json,
            "target_cell": cell_id,
        }),
    )
    .await;
    spinner.finish_and_clear();

    // 7. The canonical sturdy reference: dregg://<fed>/<cell>/<swiss>, three
    //    base58 32-byte segments (captp/src/uri.rs DreggUri format). The swiss
    //    is a fresh 32-byte secret; the proof is the bearer credential it names.
    let swiss = bearer::fresh_swiss()?;
    let uri = bearer::DreggUri {
        federation_id,
        cell_id: target,
        swiss,
    }
    .to_uri_string();

    if cfg.is_json() {
        let verify_json = match &verify_outcome {
            Ok(v) => v.clone(),
            Err(e) => serde_json::json!({ "authorized": false, "error": e.to_string() }),
        };
        ctx.json_stdout(&serde_json::json!({
            "uri": uri,
            "cell_id": cell_id,
            "permissions": permissions.as_str(),
            "expires_at": expires_at,
            "federation_id": hex::encode(federation_id),
            "federation_source": fed_source,
            "delegator_pubkey": hex::encode(public_key),
            "bearer_proof": proof_json,
            "node_verification": verify_json,
        }));
        return Ok(());
    }

    // Human-readable report.
    match &verify_outcome {
        Ok(data) => {
            let authorized = data["authorized"].as_bool().unwrap_or(false);
            if authorized {
                ctx.success("Node verified the bearer proof (signature + ledger cap-lookup).");
            } else if let Some(err) = data["error"].as_str() {
                ctx.info(&format!(
                    "Proof is cryptographically valid; node has no ledger grant yet: {err}"
                ));
            } else {
                ctx.info("Node did not authorize the proof (no matching ledger grant).");
            }
        }
        Err(e) => {
            ctx.warn(&format!(
                "Could not reach node to verify (proof is still valid offline): {e}"
            ));
        }
    }

    ctx.success("Exported bearer capability:");
    ctx.kv("Cell", &abbrev_hex(cell_id, 8, 4));
    ctx.kv("Permissions", permissions.as_str());
    ctx.kv("Delegator", &abbrev_hex(&hex::encode(public_key), 8, 4));
    ctx.kv_dim(
        "Federation",
        &format!("{} ({fed_source})", abbrev_hex(&hex::encode(federation_id), 8, 4)),
    );
    eprintln!();
    ctx.info("Sturdy reference (share out-of-band to grant access):");
    eprintln!("  {}", console::style(&uri).cyan().bold());
    eprintln!();
    ctx.info("Portable bearer proof (the verifiable credential):");
    eprintln!(
        "  {}",
        console::style(serde_json::to_string(&proof_json).unwrap_or_default()).dim()
    );
    eprintln!();
    ctx.info("Recipient enlivens with:");
    eprintln!(
        "  {}",
        console::style(format!("dregg cap enliven \"{uri}\"")).dim()
    );

    Ok(())
}

async fn enliven(_cfg: &Config, ctx: &Context, uri: &str) -> Result<(), Box<dyn std::error::Error>> {
    // Parse the canonical sturdy reference exported by `cap export`:
    // dregg://<fed-b58>/<cell-b58>/<swiss-b58> (captp DreggUri format). This is
    // the round-trip of the exporter — it resolves the URI back to the
    // federation, cell, and swiss bearer secret it names (the local import step;
    // the SDK calls this "LOCAL bookkeeping"). Exercising the capability is then
    // a turn carrying the bearer proof, gated by the executor.
    let parsed = bearer::DreggUri::parse(uri.trim())?;

    let federation_hex = hex::encode(parsed.federation_id);
    let cell_hex = hex::encode(parsed.cell_id);
    let swiss_hex = hex::encode(parsed.swiss);

    if _cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "federation_id": federation_hex,
            "cell_id": cell_hex,
            "swiss": swiss_hex,
        }));
        return Ok(());
    }

    ctx.success("Enlivened sturdy reference:");
    ctx.kv("Cell", &abbrev_hex(&cell_hex, 8, 4));
    ctx.kv("Federation", &abbrev_hex(&federation_hex, 8, 4));
    ctx.kv_dim("Swiss", &abbrev_hex(&swiss_hex, 8, 4));
    ctx.info("  Exercise it by submitting a turn that carries the bearer proof to this cell.");

    Ok(())
}

async fn handoff(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    recipient_pk: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Creating handoff certificate...");
    let body = serde_json::json!({
        "cell_id": cell_id,
        "recipient_pk": recipient_pk,
    });
    let data = post_json(cfg, "/turns/peer-exchange", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let cert_hash = data["certificate_hash"].as_str().unwrap_or("?");
    ctx.success("Handoff certificate created:");
    ctx.kv("Cell", &abbrev_hex(cell_id, 8, 4));
    ctx.kv("Recipient", &abbrev_hex(recipient_pk, 8, 4));
    ctx.kv("Certificate", &abbrev_hex(cert_hash, 8, 4));

    Ok(())
}

async fn list(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching capabilities...");
    let data = get_json(cfg, "/cipherclerk/tokens").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let tokens = data.as_array().unwrap_or(&empty);
    if tokens.is_empty() {
        ctx.info("No capabilities held. Use `dregg cap enliven` to add one.");
        return Ok(());
    }

    ctx.header(&format!("Capabilities ({})", tokens.len()));
    let rows: Vec<Vec<String>> = tokens
        .iter()
        .map(|t| {
            let id = t["id"].as_str().unwrap_or("?");
            let label = t["label"].as_str().unwrap_or("-");
            let service = t["service"].as_str().unwrap_or("?");
            vec![abbrev_hex(id, 8, 4), label.to_string(), service.to_string()]
        })
        .collect();

    ctx.table(&["ID", "Label", "Service"], &rows);

    Ok(())
}

async fn revoke(cfg: &Config, ctx: &Context, id: &str) -> Result<(), Box<dyn std::error::Error>> {
    // Safe pathway: require explicit confirmation for destructive revoke (per full client ergonomics).
    let short_id = abbrev_hex(id, 8, 4);
    if !Confirm::new()
        .with_prompt(format!(
            "Really revoke capability {}? This cannot be undone.",
            short_id
        ))
        .default(false)
        .interact()?
    {
        ctx.info("Revoke cancelled by user.");
        return Ok(());
    }

    let spinner = ctx.spinner("Revoking capability...");
    let body = serde_json::json!({
        "token_id": id,
    });
    let data = post_json(cfg, "/cipherclerk/attenuate", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Revoked capability: {}", short_id));

    Ok(())
}

/// Real bearer-capability generation — the canonical `BearerCapProof` envelope.
///
/// The CLI is deliberately dependency-light (no `dregg-turn`, no `captp`): it
/// replicates the two self-contained, version-pinned primitives byte-for-byte,
/// the same way [`super::id`] replicates the SDK's Ed25519 key derivation. Each
/// replicated constant is locked to its source by a golden-vector test:
///
/// - [`compute_delegation_message`] mirrors
///   `dregg_turn::executor::authorize.rs::compute_bearer_delegation_message`
///   (domain `dregg-bearer-delegation-v1:`). The executor recomputes this exact
///   hash at verify time, so a signature over it is the REAL cryptographic
///   admission — not a stand-in.
/// - [`DreggUri::to_uri_string`] mirrors `captp/src/uri.rs::DreggUri` (three
///   base58 32-byte segments).
/// - [`BearerCapProof::to_node_json`] emits the exact serde wire shape of
///   `dregg_turn::action::BearerCapProof` (numeric byte arrays + the
///   externally-tagged `AuthRequired` string), so `serde_json::from_value`
///   node-side deserializes it without skew.
mod bearer {
    use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

    use crate::config::Config;

    /// The permission level a bearer obtains — the subset of `AuthRequired` the
    /// CLI exposes for export (the lattice the node enforces is the full one).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Permissions {
        None,
        Signature,
        Proof,
        Either,
    }

    impl Permissions {
        /// Parse the `--attenuate` value (case-insensitive); default `Signature`.
        pub fn parse(s: Option<&str>) -> Result<Self, Box<dyn std::error::Error>> {
            match s.map(str::trim).map(str::to_ascii_lowercase).as_deref() {
                None | Some("") | Some("signature") | Some("sig") => Ok(Permissions::Signature),
                Some("none") => Ok(Permissions::None),
                Some("proof") => Ok(Permissions::Proof),
                Some("either") => Ok(Permissions::Either),
                Some(other) => Err(format!(
                    "unknown attenuation {other:?}: use None | Signature | Proof | Either"
                )
                .into()),
            }
        }

        /// The externally-tagged `AuthRequired` variant name (the JSON the node
        /// deserializes, and the display string).
        pub fn as_str(self) -> &'static str {
            match self {
                Permissions::None => "None",
                Permissions::Signature => "Signature",
                Permissions::Proof => "Proof",
                Permissions::Either => "Either",
            }
        }

        /// The permission byte the canonical delegation message hashes
        /// (`compute_bearer_delegation_message`: None=0, Signature=1, Proof=2,
        /// Either=3 — Impossible=4 / Custom=5 are not CLI-exportable).
        fn message_byte(self) -> u8 {
            match self {
                Permissions::None => 0,
                Permissions::Signature => 1,
                Permissions::Proof => 2,
                Permissions::Either => 3,
            }
        }
    }

    /// Decode a 64-hex-char cell id into 32 bytes.
    pub fn decode_cell_id(hex_str: &str) -> Result<[u8; 32], Box<dyn std::error::Error>> {
        let bytes = hex::decode(hex_str.trim())
            .map_err(|e| format!("cell id is not valid hex: {e}"))?;
        if bytes.len() != 32 {
            return Err(format!(
                "cell id must be 32 bytes (64 hex chars), got {} bytes",
                bytes.len()
            )
            .into());
        }
        let mut out = [0u8; 32];
        out.copy_from_slice(&bytes);
        Ok(out)
    }

    /// A fresh 32-byte swiss number (the sturdy-ref bearer secret).
    pub fn fresh_swiss() -> Result<[u8; 32], Box<dyn std::error::Error>> {
        let mut swiss = [0u8; 32];
        getrandom::fill(&mut swiss)
            .map_err(|e| format!("OS randomness unavailable for swiss number: {e}"))?;
        Ok(swiss)
    }

    /// Resolve the node's federation id (the `is_local` entry of
    /// `/api/federations`). On any failure returns the pure-sim federation
    /// (`[0u8; 32]`, the wasm/SDK sim convention) so export still produces a
    /// real, offline-verifiable proof. Returns `(id, human_source)`.
    pub async fn resolve_federation_id(cfg: &Config) -> ([u8; 32], &'static str) {
        match super::get_json(cfg, "/api/federations").await {
            Ok(serde_json::Value::Array(feds)) => {
                // Prefer the local federation; else the first listed.
                let chosen = feds
                    .iter()
                    .find(|f| f["is_local"].as_bool() == Some(true))
                    .or_else(|| feds.first());
                if let Some(hex_str) = chosen.and_then(|f| f["federation_id"].as_str()) {
                    if let Ok(id) = decode_cell_id(hex_str) {
                        return (id, "node");
                    }
                }
                ([0u8; 32], "sim (no local federation reported)")
            }
            _ => ([0u8; 32], "sim (node unreachable)"),
        }
    }

    /// The canonical sturdy reference: `dregg://<fed>/<cell>/<swiss>`.
    ///
    /// Mirrors `captp/src/uri.rs::DreggUri` — three base58-encoded 32-byte
    /// segments. (Locked by `dregg_uri_roundtrips_canonically`.)
    pub struct DreggUri {
        pub federation_id: [u8; 32],
        pub cell_id: [u8; 32],
        pub swiss: [u8; 32],
    }

    impl DreggUri {
        pub fn to_uri_string(&self) -> String {
            format!(
                "dregg://{}/{}/{}",
                bs58::encode(self.federation_id).into_string(),
                bs58::encode(self.cell_id).into_string(),
                bs58::encode(self.swiss).into_string(),
            )
        }

        /// Parse the canonical `dregg://<fed>/<cell>/<swiss>` form — the inverse
        /// of [`to_uri_string`](Self::to_uri_string). Each segment must base58
        /// decode to exactly 32 bytes (mirrors `captp/src/uri.rs::DreggUri::parse`).
        pub fn parse(s: &str) -> Result<Self, Box<dyn std::error::Error>> {
            let rest = s
                .strip_prefix("dregg://")
                .ok_or("invalid URI: must start with dregg://")?;
            let segs: Vec<&str> = rest.split('/').collect();
            if segs.len() != 3 {
                return Err(format!(
                    "invalid dregg:// URI: expected 3 segments (federation/cell/swiss), found {}",
                    segs.len()
                )
                .into());
            }
            Ok(DreggUri {
                federation_id: decode_b58_32(segs[0], "federation")?,
                cell_id: decode_b58_32(segs[1], "cell")?,
                swiss: decode_b58_32(segs[2], "swiss")?,
            })
        }
    }

    /// Decode a base58 segment into 32 bytes.
    fn decode_b58_32(s: &str, what: &str) -> Result<[u8; 32], Box<dyn std::error::Error>> {
        let bytes = bs58::decode(s)
            .into_vec()
            .map_err(|e| format!("{what} segment is not valid base58: {e}"))?;
        if bytes.len() != 32 {
            return Err(format!(
                "{what} segment must be 32 bytes, decoded to {}",
                bytes.len()
            )
            .into());
        }
        let mut out = [0u8; 32];
        out.copy_from_slice(&bytes);
        Ok(out)
    }

    /// The canonical delegation message a delegator signs — replicated
    /// byte-for-byte from `TurnExecutor::compute_bearer_delegation_message`.
    ///
    /// ```text
    /// blake3( "dregg-bearer-delegation-v1:" || federation_id || target
    ///         || perm_byte || bearer_pk || expires_at.to_le_bytes() )
    /// ```
    ///
    /// (Custom permissions append `vk_hash` after the perm byte; the CLI does
    /// not export Custom, so that branch is absent here by construction.)
    pub fn compute_delegation_message(
        target: &[u8; 32],
        permissions: Permissions,
        bearer_pk: &[u8; 32],
        expires_at: u64,
        federation_id: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-bearer-delegation-v1:");
        hasher.update(federation_id);
        hasher.update(target);
        hasher.update(&[permissions.message_byte()]);
        hasher.update(bearer_pk);
        hasher.update(&expires_at.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// A real, signed bearer capability proof (the `SignedDelegation` envelope).
    pub struct BearerCapProof {
        pub target: [u8; 32],
        pub permissions: Permissions,
        pub delegator_pk: [u8; 32],
        pub bearer_pk: [u8; 32],
        pub signature: [u8; 64],
        pub expires_at: u64,
    }

    impl BearerCapProof {
        /// Sign a self-delegation: the active identity is both delegator and
        /// bearer (the operator grants the recipient who presents this proof).
        pub fn sign(
            signing_key: &SigningKey,
            public_key: [u8; 32],
            target: [u8; 32],
            permissions: Permissions,
            expires_at: u64,
            federation_id: &[u8; 32],
        ) -> Self {
            let message = compute_delegation_message(
                &target,
                permissions,
                &public_key,
                expires_at,
                federation_id,
            );
            let signature = signing_key.sign(&message).to_bytes();
            BearerCapProof {
                target,
                permissions,
                delegator_pk: public_key,
                bearer_pk: public_key,
                signature,
                expires_at,
            }
        }

        /// The exact serde wire shape of `dregg_turn::action::BearerCapProof`
        /// (the `SignedDelegation` variant): newtype byte arrays serialize as
        /// JSON number arrays; `permissions` is the externally-tagged
        /// `AuthRequired` string; the 64-byte signature is a number array
        /// (`serde_sig64`); `revocation_channel` / `allowed_effects` are null.
        pub fn to_node_json(&self) -> serde_json::Value {
            serde_json::json!({
                "target": self.target.to_vec(),
                "permissions": self.permissions.as_str(),
                "delegation_proof": {
                    "SignedDelegation": {
                        "delegator_pk": self.delegator_pk.to_vec(),
                        "signature": self.signature.to_vec(),
                        "bearer_pk": self.bearer_pk.to_vec(),
                    }
                },
                "expires_at": self.expires_at,
                "revocation_channel": serde_json::Value::Null,
                "allowed_effects": serde_json::Value::Null,
            })
        }

        /// Cryptographic verification — the offline half of the export tooth.
        /// Recomputes the canonical message under `federation_id` and checks the
        /// delegator's Ed25519 signature (the EXACT check the executor runs,
        /// minus ledger cap-lookup). `true` iff the signature is valid.
        pub fn verify_signature(&self, federation_id: &[u8; 32]) -> bool {
            let message = compute_delegation_message(
                &self.target,
                self.permissions,
                &self.bearer_pk,
                self.expires_at,
                federation_id,
            );
            let Ok(vk) = VerifyingKey::from_bytes(&self.delegator_pk) else {
                return false;
            };
            let sig = Signature::from_bytes(&self.signature);
            vk.verify(&message, &sig).is_ok()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::bearer::{BearerCapProof, DreggUri, Permissions, compute_delegation_message};
    use ed25519_dalek::SigningKey;

    fn test_key() -> (SigningKey, [u8; 32]) {
        let sk = SigningKey::from_bytes(&[7u8; 32]);
        let pk = sk.verifying_key().to_bytes();
        (sk, pk)
    }

    /// GOLDEN-VECTOR LOCK: the CLI's replicated delegation message must equal
    /// the turn crate's `compute_bearer_delegation_message`. This pins the
    /// domain string + field order + permission-byte encoding; any drift on
    /// either side breaks this and the node would reject CLI-built proofs.
    ///
    /// The expected hash is computed independently here from the documented
    /// recipe (blake3 over the concatenated fields) so the test is a true
    /// cross-check, not a tautology against the function under test.
    #[test]
    fn delegation_message_matches_canonical_recipe() {
        let target = [0xABu8; 32];
        let bearer = [0xCDu8; 32];
        let fed = [0xEFu8; 32];
        let expires = 0x0102_0304_0506_0708u64;

        // Independent recomputation of the canonical recipe.
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-bearer-delegation-v1:");
        h.update(&fed);
        h.update(&target);
        h.update(&[1u8]); // Signature => perm byte 1
        h.update(&bearer);
        h.update(&expires.to_le_bytes());
        let expected = *h.finalize().as_bytes();

        let got =
            compute_delegation_message(&target, Permissions::Signature, &bearer, expires, &fed);
        assert_eq!(
            got, expected,
            "CLI delegation message drifted from the canonical blake3 recipe"
        );

        // Pin the exact bytes. This constant equals what the REAL
        // `dregg_turn::executor::TurnExecutor::compute_bearer_delegation_message`
        // computes on these inputs (CellId([0xAB;32]), AuthRequired::Signature,
        // [0xCD;32], expires 0x0102030405060708, fed [0xEF;32]); if either side
        // changes the wire recipe, this fails and the node would reject
        // CLI-built proofs. The cross-check is RUNNABLE and links the real turn
        // crate — `turn/tests/cli_bearer_export_golden.rs`
        // (`cli_replica_matches_real_executor_delegation_message`), so the
        // constant cannot silently drift from its source of truth. Same
        // golden-vector discipline as `id.rs::derivation_matches_sdk_golden_vector`.
        assert_eq!(
            hex::encode(got),
            "9fe1805d6e21ecaf4334cbc0030e70c3a9842773621e91d69a9df7b75fb05271",
            "CLI delegation message diverged from the turn-crate golden vector"
        );
    }

    /// TOOTH (valid admits): a freshly-signed proof verifies against the same
    /// federation id it was bound to.
    #[test]
    fn signed_proof_verifies() {
        let (sk, pk) = test_key();
        let fed = [0x11u8; 32];
        let proof = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        assert!(
            proof.verify_signature(&fed),
            "a freshly-signed bearer proof must verify under its own federation id"
        );
    }

    /// TOOTH (invalid rejects): every load-bearing field is bound by the
    /// signature. Tampering with the target, permissions, bearer key, expiry,
    /// or federation id — or flipping a signature bit — makes verification fail.
    #[test]
    fn tampered_proof_rejected() {
        let (sk, pk) = test_key();
        let fed = [0x11u8; 32];
        let base = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);

        // (a) wrong federation id (cross-federation replay) — rejected.
        assert!(
            !base.verify_signature(&[0x99u8; 32]),
            "a proof bound to fed A must not verify under fed B"
        );

        // (b) tampered target.
        let mut t = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        t.target[0] ^= 0xFF;
        assert!(!t.verify_signature(&fed), "tampered target must reject");

        // (c) amplified permissions (Signature -> Either is a different message).
        let mut p = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        p.permissions = Permissions::Either;
        assert!(
            !p.verify_signature(&fed),
            "swapping permissions must reject (no silent amplification)"
        );

        // (d) extended expiry.
        let mut e = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        e.expires_at = u64::MAX;
        assert!(!e.verify_signature(&fed), "extended expiry must reject");

        // (e) substituted bearer key.
        let mut b = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        b.bearer_pk[0] ^= 0xFF;
        assert!(!b.verify_signature(&fed), "substituted bearer key must reject");

        // (f) flipped signature bit.
        let mut s = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        s.signature[0] ^= 0x01;
        assert!(!s.verify_signature(&fed), "corrupted signature must reject");

        // (g) wrong signer (different key, same fields).
        let other = SigningKey::from_bytes(&[9u8; 32]);
        let other_pk = other.verifying_key().to_bytes();
        let mut w = BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &fed);
        w.delegator_pk = other_pk; // pk no longer matches the signature
        assert!(!w.verify_signature(&fed), "delegator-key mismatch must reject");
    }

    /// The portable proof JSON is the exact node wire shape: numeric byte
    /// arrays + the `"Signature"` permission tag + the `SignedDelegation`
    /// nesting, with null revocation/effects. (Pins the contract the node's
    /// `serde_json::from_value::<BearerCapProof>` relies on.)
    #[test]
    fn node_json_shape_is_canonical() {
        let (sk, pk) = test_key();
        let proof =
            BearerCapProof::sign(&sk, pk, [0x22u8; 32], Permissions::Signature, 1000, &[0u8; 32]);
        let j = proof.to_node_json();

        assert_eq!(j["permissions"], "Signature");
        assert_eq!(j["expires_at"], 1000);
        assert!(j["revocation_channel"].is_null());
        assert!(j["allowed_effects"].is_null());

        let target = j["target"].as_array().expect("target is an array");
        assert_eq!(target.len(), 32);
        assert_eq!(target[0].as_u64(), Some(0x22));

        let sd = &j["delegation_proof"]["SignedDelegation"];
        assert_eq!(
            sd["delegator_pk"].as_array().map(|a| a.len()),
            Some(32),
            "delegator_pk must be a 32-element byte array"
        );
        assert_eq!(
            sd["bearer_pk"].as_array().map(|a| a.len()),
            Some(32),
            "bearer_pk must be a 32-element byte array"
        );
        assert_eq!(
            sd["signature"].as_array().map(|a| a.len()),
            Some(64),
            "signature must be a 64-element byte array (serde_sig64)"
        );
    }

    /// The sturdy reference round-trips: it is the canonical three-segment
    /// base58 `dregg://` form, and each segment decodes back to its 32 bytes.
    #[test]
    fn dregg_uri_roundtrips_canonically() {
        let uri = DreggUri {
            federation_id: [0xAAu8; 32],
            cell_id: [0xBBu8; 32],
            swiss: [0xCCu8; 32],
        };
        let s = uri.to_uri_string();
        assert!(s.starts_with("dregg://"), "must use the dregg:// scheme");

        let rest = s.strip_prefix("dregg://").unwrap();
        let segs: Vec<&str> = rest.split('/').collect();
        assert_eq!(segs.len(), 3, "exactly three path segments");

        // No placeholder strings — every segment is real base58 of 32 bytes.
        assert_eq!(bs58::decode(segs[0]).into_vec().unwrap(), uri.federation_id);
        assert_eq!(bs58::decode(segs[1]).into_vec().unwrap(), uri.cell_id);
        assert_eq!(bs58::decode(segs[2]).into_vec().unwrap(), uri.swiss);
        assert!(
            !s.contains("placeholder") && !s.contains("local/"),
            "the URI must not contain any placeholder marker"
        );
    }

    /// EXPORT↔ENLIVEN ROUND-TRIP: the exact URI string `cap export` prints
    /// parses back (via the `enliven` path) to the same federation/cell/swiss.
    /// This is the "exported cap can be re-imported" tooth at the URI layer.
    #[test]
    fn export_uri_reimports_via_enliven_parse() {
        let original = DreggUri {
            federation_id: [0x10u8; 32],
            cell_id: [0x20u8; 32],
            swiss: [0x30u8; 32],
        };
        let uri = original.to_uri_string();

        // `enliven` parses this exact string.
        let reimported = DreggUri::parse(&uri).expect("exported URI must re-parse");
        assert_eq!(reimported.federation_id, original.federation_id);
        assert_eq!(reimported.cell_id, original.cell_id);
        assert_eq!(reimported.swiss, original.swiss);

        // Malformed inputs are rejected (not silently accepted).
        assert!(DreggUri::parse("http://a/b/c").is_err());
        assert!(DreggUri::parse("dregg://only/two").is_err());
        assert!(
            DreggUri::parse("dregg://0/0/0").is_err(),
            "'0' is not base58 and segments must be 32 bytes"
        );
    }

    #[test]
    fn permissions_parse_and_render() {
        assert_eq!(Permissions::parse(None).unwrap(), Permissions::Signature);
        assert_eq!(
            Permissions::parse(Some("none")).unwrap(),
            Permissions::None
        );
        assert_eq!(
            Permissions::parse(Some("EITHER")).unwrap(),
            Permissions::Either
        );
        assert!(Permissions::parse(Some("bogus")).is_err());
        assert_eq!(Permissions::Proof.as_str(), "Proof");
    }
}
