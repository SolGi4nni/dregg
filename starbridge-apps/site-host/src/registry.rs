//! The registry of published site cells — the hosting DATA plane the write
//! control plane ([`crate::publish`]) writes into.
//!
//! Publishing inserts a cap-gated, receipted [`SiteCell`] through a durable
//! [`StorageBackend`](crate::storage::StorageBackend); serving resolves an inbound
//! request's host label to the named cell and serves its content — re-checking the
//! served bytes against the published commitment (serve == commit). Each publish (and
//! each `unpublish`) appends a [`PublishReceipt`] to the site's **append-only** history
//! — retained whether or not the registry is signed. When the registry is [`signed`],
//! the receipt carries an ed25519 attestation over its body so a non-witness verifies
//! a publish against the registry's public key with no trust in the host
//! ([`verify_receipt`]).

use std::sync::Arc;

use ed25519_dalek::{Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::site::{SiteContent, content_root, is_valid_name};
use crate::storage::{MemoryStore, StorageBackend, StorageError};

/// The cap-token prefix a publish capability carries: `site-host/<name>`. A holder
/// of `site-host/blog` may publish (only) the site named `blog` — the publish
/// turn's attenuation.
pub const PUBLISH_CAP_PREFIX: &str = "site-host/";

/// How a host label resolves to a site name.
///
/// Parameterized: the serving apex is configuration, never a hardcoded product
/// domain. `<name>.<apex>` resolves to `<name>`; the bare apex and its `www` alias
/// resolve to `None`. With no apex configured, only the local-testing bare-label
/// fallback applies (`curl -H 'Host: blog'`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HostConfig {
    /// The hosting apex, e.g. `example.test`. `None` = local-only (bare-label).
    pub apex: Option<String>,
}

impl HostConfig {
    /// A config with no apex (local bare-label resolution only).
    pub fn local() -> HostConfig {
        HostConfig { apex: None }
    }

    /// A config serving `<name>.<apex>`.
    pub fn with_apex(apex: impl Into<String>) -> HostConfig {
        HostConfig {
            apex: Some(apex.into()),
        }
    }

    /// The canonical URL a published `name` is served at (uses the apex if set,
    /// otherwise a host-relative label a local gateway resolves).
    pub fn url_for(&self, name: &str) -> String {
        match &self.apex {
            Some(apex) => format!("https://{name}.{apex}/"),
            None => format!("http://{name}/"),
        }
    }

    /// Extract the site `<name>` label from a request `Host` under this config.
    ///
    /// `<name>.<apex>[:port]` -> `Some(name)`. The bare apex and `www.<apex>`
    /// resolve to `None`. For local testing without DNS, a bare single label (no
    /// dot) resolves to that label.
    pub fn site_name_from_host(&self, host: &str) -> Option<String> {
        let host = host.split(':').next().unwrap_or(host).trim();
        if host.is_empty() {
            return None;
        }
        if let Some(apex) = &self.apex {
            let dotted = format!(".{apex}");
            if let Some(label) = host.strip_suffix(&dotted) {
                if label.is_empty() || label == "www" || label.contains('.') {
                    return None;
                }
                return Some(label.to_ascii_lowercase());
            }
            if host == apex {
                return None;
            }
        }
        // Local-testing fallback: a bare single label (no dots) is the name.
        if !host.contains('.') {
            return Some(host.to_ascii_lowercase());
        }
        None
    }
}

/// A capability authorizing a publish: a holder of `site-host/<name>` may publish
/// the site named `<name>`. Bound to both the holder (the future `owner`) and the
/// site name — it cannot be exercised to publish a different site.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublishCap {
    /// The cap holder (becomes the published cell's `owner`).
    pub holder: String,
    /// The cap token: `site-host/<name>`.
    pub cap: String,
}

impl PublishCap {
    /// A publish cap for `holder` over the site named `name`.
    pub fn for_site(holder: impl Into<String>, name: &str) -> PublishCap {
        PublishCap {
            holder: holder.into(),
            cap: format!("{PUBLISH_CAP_PREFIX}{name}"),
        }
    }

    /// The site name this cap authorizes, if it is a well-formed token.
    pub fn site(&self) -> Option<&str> {
        self.cap
            .strip_prefix(PUBLISH_CAP_PREFIX)
            .filter(|n| !n.is_empty())
    }

    /// Whether this cap authorizes publishing the site `name`.
    pub fn authorizes(&self, name: &str) -> bool {
        self.site() == Some(name)
    }
}

/// The verifiable record a publish (or unpublish) leaves: who published which site,
/// at what content commitment, in what order. When the registry is [`signed`],
/// `attest` carries an ed25519 signature over the record so a non-witness re-verifies
/// it ([`verify_receipt`]).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublishReceipt {
    /// The registry-monotonic sequence of this publish (publish order).
    pub seq: u64,
    /// The site name published.
    pub name: String,
    /// The owner (the cap holder) that published it.
    pub owner: String,
    /// The content commitment the published cell carries (the served-bytes root, or
    /// the empty string for a delete tombstone).
    pub content_root: String,
    /// How many assets the published site holds (`0` for a delete tombstone).
    pub asset_count: usize,
    /// Whether this receipt records an `unpublish` (a delete tombstone in the
    /// append-only history) rather than a publish.
    #[serde(default)]
    pub deleted: bool,
    /// The ed25519 attestation over this record, when the registry is signed. `None`
    /// for the unsigned free/local default (a bare projection).
    #[serde(default)]
    pub attest: Option<ReceiptAttestation>,
}

impl PublishReceipt {
    /// The 32-byte body hash the attestation signs: a domain-tagged blake3 over the
    /// binding fields (a server cannot re-sign a different `(name, owner, root)`
    /// under the same signature).
    pub fn body_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("site-host-publish-receipt-v1");
        h.update(&self.seq.to_le_bytes());
        h.update(&(self.name.len() as u64).to_le_bytes());
        h.update(self.name.as_bytes());
        h.update(&(self.owner.len() as u64).to_le_bytes());
        h.update(self.owner.as_bytes());
        h.update(&(self.content_root.len() as u64).to_le_bytes());
        h.update(self.content_root.as_bytes());
        h.update(&(self.asset_count as u64).to_le_bytes());
        h.update(&[self.deleted as u8]);
        *h.finalize().as_bytes()
    }
}

/// An ed25519 attestation over a [`PublishReceipt::body_hash`]: the signer's public
/// key and the detached signature. Re-verified by [`verify_receipt`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptAttestation {
    /// The signer's ed25519 verifying key (the registry's `receipt_signer`).
    pub signer: [u8; 32],
    /// The detached ed25519 signature over the receipt body hash (64 bytes).
    pub sig: Vec<u8>,
}

/// Re-verify a signed publish receipt with no trust in the host: recompute the body
/// hash and check the attestation's signature under its own key, then confirm the
/// key is the one `expected_signer` (the registry's advertised public key). A bare
/// (unsigned) receipt has nothing to verify -> `false`.
pub fn verify_receipt(receipt: &PublishReceipt, expected_signer: [u8; 32]) -> bool {
    let Some(att) = &receipt.attest else {
        return false;
    };
    if att.signer != expected_signer {
        return false;
    }
    let Ok(vk) = VerifyingKey::from_bytes(&att.signer) else {
        return false;
    };
    let Ok(sig_bytes): Result<[u8; 64], _> = att.sig.as_slice().try_into() else {
        return false;
    };
    let sig = ed25519_dalek::Signature::from_bytes(&sig_bytes);
    vk.verify(&receipt.body_hash(), &sig).is_ok()
}

/// Why a publish was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublishError {
    /// The presented cap does not authorize publishing `name`.
    CapRefused { cap: String, name: String },
    /// The site has no assets — there is nothing to serve.
    EmptyContent,
    /// The site name is not a usable subdomain label.
    InvalidName(String),
    /// A durable-storage operation failed (the publish did not commit).
    Storage(String),
    /// An `unpublish` targeted a site the caller does not own (its cell's `owner`
    /// differs from the cap holder), or a site that is not published.
    NotOwner { name: String },
}

impl std::fmt::Display for PublishError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PublishError::CapRefused { cap, name } => {
                write!(f, "cap `{cap}` does not authorize publishing site `{name}`")
            }
            PublishError::EmptyContent => write!(f, "cannot publish a site with no assets"),
            PublishError::InvalidName(n) => write!(f, "`{n}` is not a valid site name"),
            PublishError::Storage(m) => write!(f, "durable storage failed: {m}"),
            PublishError::NotOwner { name } => {
                write!(f, "not the owner of site `{name}` (or it is not published)")
            }
        }
    }
}

impl std::error::Error for PublishError {}

impl From<StorageError> for PublishError {
    fn from(e: StorageError) -> PublishError {
        PublishError::Storage(e.to_string())
    }
}

/// A published site: the route name, the owner (cap holder), the content
/// commitment, and the content itself.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiteCell {
    /// The route name — the subdomain label served at `<name>.<apex>`.
    pub name: String,
    /// The owner cell/agent that published this site (the cap holder). Provable via
    /// the publish receipt, which binds `(name, owner, content_root)`.
    pub owner: String,
    /// The real sorted-Poseidon2 content commitment — the anchor a trustless
    /// projection opens each served asset against.
    pub content_root: String,
    /// The site content (path -> asset).
    pub content: SiteContent,
}

impl SiteCell {
    /// Assemble a site cell from its parts, computing the [`content_root`].
    pub fn new(
        name: impl Into<String>,
        owner: impl Into<String>,
        content: SiteContent,
    ) -> SiteCell {
        let content_root = content_root(&content);
        SiteCell {
            name: name.into(),
            owner: owner.into(),
            content_root,
            content,
        }
    }

    /// **Serve == commit.** Recompute the content commitment over the CURRENTLY-held
    /// bytes and check it equals the published `content_root`. A `true` proves the
    /// bytes about to be served are exactly the bytes the receipt attests; a `false`
    /// means the stored content and its commitment have diverged (corruption, or a
    /// host that swapped bytes after publish).
    ///
    /// This is the concrete, pre-circuit half of the acknowledged on-chain seam: it
    /// lets a client — and the host itself — re-witness that served bytes match the
    /// receipt, before the in-circuit light-client witness exists. It does NOT (yet)
    /// bind the host to serve these bytes over the network; it binds the stored cell
    /// to its own commitment.
    pub fn verify_commitment(&self) -> bool {
        content_root(&self.content) == self.content_root
    }

    /// Serve a request path against this cell's content (read-only). A resolved
    /// asset is a `200`; a miss is a `404` with a length-bounded reflected path.
    pub fn serve(&self, path: &str) -> ServedAsset {
        match self.content.resolve(path) {
            Some(asset) => ServedAsset {
                status: 200,
                content_type: asset.content_type.clone(),
                body: asset.body.clone(),
            },
            None => ServedAsset {
                status: 404,
                content_type: "text/plain; charset=utf-8".to_string(),
                body: format!(
                    "no asset `{}` in site `{}`",
                    bounded_reflect(path),
                    self.name
                )
                .into_bytes(),
            },
        }
    }

    /// Serve `path`, but FIRST enforce serve == commit ([`verify_commitment`]). If the
    /// stored bytes no longer match the published root, refuse with a `500` rather
    /// than serve bytes that do not match the receipt — the host does not silently
    /// serve divergent content.
    pub fn serve_verified(&self, path: &str) -> ServedAsset {
        if !self.verify_commitment() {
            return ServedAsset {
                status: 500,
                content_type: "text/plain; charset=utf-8".to_string(),
                body: format!(
                    "served bytes for site `{}` do not match the published commitment",
                    self.name
                )
                .into_bytes(),
            };
        }
        self.serve(path)
    }
}

/// The result of serving one asset request against a [`SiteCell`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServedAsset {
    pub status: u16,
    pub content_type: String,
    pub body: Vec<u8>,
}

/// Cap an echoed, attacker-controlled path to 80 bytes so a reflected `404` body
/// cannot be inflated by a long request path.
fn bounded_reflect(s: &str) -> String {
    const MAX: usize = 80;
    if s.len() <= MAX {
        return s.to_string();
    }
    let mut cut = MAX;
    while cut > 0 && !s.is_char_boundary(cut) {
        cut -= 1;
    }
    format!("{}…", &s[..cut])
}

/// The registry of published site cells, backed by a durable
/// [`StorageBackend`](crate::storage::StorageBackend).
pub struct SiteRegistry {
    store: Arc<dyn StorageBackend>,
    /// The ed25519 key publish receipts are sealed under. `None` = unsigned
    /// free/local default ([`PublishReceipt::attest`] is then `None`).
    signing_key: Option<SigningKey>,
}

impl Default for SiteRegistry {
    fn default() -> SiteRegistry {
        SiteRegistry {
            store: Arc::new(MemoryStore::new()),
            signing_key: None,
        }
    }
}

impl SiteRegistry {
    /// A fresh, empty, unsigned registry backed by an in-memory store (the free/local
    /// default — **not durable**; use [`with_backend`](Self::with_backend) for a
    /// durable deployment).
    pub fn new() -> SiteRegistry {
        SiteRegistry::default()
    }

    /// A registry whose publishes are sealed under the ed25519 key derived from
    /// `seed`, backed by an in-memory store.
    pub fn signed(seed: [u8; 32]) -> SiteRegistry {
        SiteRegistry {
            store: Arc::new(MemoryStore::new()),
            signing_key: Some(SigningKey::from_bytes(&seed)),
        }
    }

    /// An unsigned registry backed by an explicit (e.g. durable
    /// [`FsStore`](crate::storage::FsStore)) storage backend.
    pub fn with_backend(store: Arc<dyn StorageBackend>) -> SiteRegistry {
        SiteRegistry {
            store,
            signing_key: None,
        }
    }

    /// A signed registry backed by an explicit storage backend — the durable,
    /// re-witnessable deployment shape.
    pub fn signed_with_backend(seed: [u8; 32], store: Arc<dyn StorageBackend>) -> SiteRegistry {
        SiteRegistry {
            store,
            signing_key: Some(SigningKey::from_bytes(&seed)),
        }
    }

    /// Whether the backing store is durable across restarts.
    pub fn is_durable(&self) -> bool {
        self.store.is_durable()
    }

    /// The public key a non-witness verifies this registry's receipts under, if
    /// signed.
    pub fn receipt_signer(&self) -> Option<[u8; 32]> {
        self.signing_key
            .as_ref()
            .map(|k| k.verifying_key().to_bytes())
    }

    /// Seal a receipt body with the registry's key (when signed), leaving `attest`
    /// `None` for the unsigned default.
    fn seal(&self, receipt: &mut PublishReceipt) {
        if let Some(key) = &self.signing_key {
            let sig = key.sign(&receipt.body_hash());
            receipt.attest = Some(ReceiptAttestation {
                signer: key.verifying_key().to_bytes(),
                sig: sig.to_bytes().to_vec(),
            });
        }
    }

    /// Publish a minisite as a cap-gated, receipted turn.
    ///
    /// Gates on `cap` (must be a `site-host/<name>` cap for `name`), validates the
    /// name and non-empty content, durably writes the [`SiteCell`] (owner = the cap
    /// holder), appends the [`PublishReceipt`] to the site's append-only history
    /// (retained whether or not the registry is signed), and returns it. Republishing
    /// an existing name with the right cap replaces the cell (a new commitment, a new
    /// receipt appended — the prior receipt is retained in history).
    pub fn publish(
        &self,
        cap: &PublishCap,
        name: &str,
        content: SiteContent,
    ) -> Result<PublishReceipt, PublishError> {
        if !is_valid_name(name) {
            return Err(PublishError::InvalidName(name.to_string()));
        }
        if !cap.authorizes(name) {
            return Err(PublishError::CapRefused {
                cap: cap.cap.clone(),
                name: name.to_string(),
            });
        }
        if content.is_empty() {
            return Err(PublishError::EmptyContent);
        }

        let cell = SiteCell::new(name, cap.holder.clone(), content);
        let seq = self.store.next_seq()?;
        let mut receipt = PublishReceipt {
            seq,
            name: cell.name.clone(),
            owner: cell.owner.clone(),
            content_root: cell.content_root.clone(),
            asset_count: cell.content.len(),
            deleted: false,
            attest: None,
        };
        self.seal(&mut receipt);
        // Write the cell first, then the receipt: a crash between leaves a published
        // cell without its receipt (recoverable) rather than a receipt for a cell that
        // was never written (a phantom attestation).
        self.store.put_cell(&cell)?;
        self.store.append_receipt(&receipt)?;
        Ok(receipt)
    }

    /// **Unpublish** a site — a cap-gated, receipted delete. Gates on `cap` and on
    /// OWNERSHIP (the stored cell's `owner` must equal the cap holder), deletes the
    /// cell, and appends a delete tombstone receipt to the append-only history so the
    /// removal is itself provable. Returns the tombstone receipt.
    pub fn unpublish(&self, cap: &PublishCap, name: &str) -> Result<PublishReceipt, PublishError> {
        if !cap.authorizes(name) {
            return Err(PublishError::CapRefused {
                cap: cap.cap.clone(),
                name: name.to_string(),
            });
        }
        let Some(cell) = self.store.get_cell(name)? else {
            return Err(PublishError::NotOwner {
                name: name.to_string(),
            });
        };
        if cell.owner != cap.holder {
            return Err(PublishError::NotOwner {
                name: name.to_string(),
            });
        }
        let seq = self.store.next_seq()?;
        let mut receipt = PublishReceipt {
            seq,
            name: name.to_string(),
            owner: cap.holder.clone(),
            content_root: String::new(),
            asset_count: 0,
            deleted: true,
            attest: None,
        };
        self.seal(&mut receipt);
        self.store.delete_cell(name)?;
        self.store.append_receipt(&receipt)?;
        Ok(receipt)
    }

    /// The latest retained receipt for `name`, if published (retained for signed AND
    /// unsigned registries).
    pub fn receipt(&self, name: &str) -> Option<PublishReceipt> {
        self.store.latest_receipt(name).ok().flatten()
    }

    /// The full append-only receipt history for `name`, oldest first (every publish +
    /// unpublish, retained regardless of signing).
    pub fn receipt_history(&self, name: &str) -> Vec<PublishReceipt> {
        self.store.receipt_history(name).unwrap_or_default()
    }

    /// Look up a published site cell by name.
    pub fn get(&self, name: &str) -> Option<SiteCell> {
        self.store.get_cell(name).ok().flatten()
    }

    /// The names of all published sites (sorted).
    pub fn names(&self) -> Vec<String> {
        self.store.list_cells().unwrap_or_default()
    }

    /// Resolve + serve one request given the request's `Host` header and config,
    /// enforcing serve == commit ([`SiteCell::serve_verified`]).
    pub fn resolve(&self, cfg: &HostConfig, host: &str, path: &str) -> ServedAsset {
        let Some(name) = cfg.site_name_from_host(host) else {
            return ServedAsset {
                status: 404,
                content_type: "text/plain; charset=utf-8".to_string(),
                body: format!("no site for host `{}`", bounded_reflect(host)).into_bytes(),
            };
        };
        match self.get(&name) {
            Some(cell) => cell.serve_verified(path),
            None => ServedAsset {
                status: 404,
                content_type: "text/plain; charset=utf-8".to_string(),
                body: format!("no site named `{name}`").into_bytes(),
            },
        }
    }
}

/// A convenience alias mirroring the ed25519 verifying-key type for downstream
/// verifiers that hold a raw 32-byte signer.
pub type Signer32 = [u8; 32];

#[cfg(test)]
mod tests {
    use super::*;

    fn bundle() -> SiteContent {
        SiteContent::new()
            .with("/index.html", "<h1>hello</h1>")
            .with("/style.css", "h1{color:teal}")
    }

    #[test]
    fn publish_get_and_serve_round_trip() {
        let reg = SiteRegistry::new();
        let cap = PublishCap::for_site("agent:alice", "blog");
        let r = reg.publish(&cap, "blog", bundle()).unwrap();
        assert_eq!(r.content_root.len(), 64);
        assert_eq!(r.asset_count, 2);
        assert!(r.attest.is_none(), "unsigned default");
        assert!(!r.deleted);

        let cell = reg.get("blog").unwrap();
        assert_eq!(cell.owner, "agent:alice");
        assert_eq!(cell.content_root, r.content_root);
        assert!(cell.verify_commitment(), "serve == commit holds");

        let served = cell.serve_verified("/");
        assert_eq!(served.status, 200);
        assert_eq!(served.body, b"<h1>hello</h1>");
    }

    #[test]
    fn unsigned_registry_still_retains_receipts() {
        let reg = SiteRegistry::new();
        let cap = PublishCap::for_site("agent:alice", "blog");
        reg.publish(&cap, "blog", bundle()).unwrap();
        // The gap that used to exist: an unsigned registry retained NO receipts.
        assert!(
            reg.receipt("blog").is_some(),
            "receipt retained even unsigned"
        );
        assert_eq!(reg.receipt_history("blog").len(), 1);
    }

    #[test]
    fn republish_appends_history_and_retains_the_prior_receipt() {
        let reg = SiteRegistry::signed([9u8; 32]);
        let cap = PublishCap::for_site("agent:alice", "blog");
        let r0 = reg.publish(&cap, "blog", bundle()).unwrap();
        let r1 = reg
            .publish(&cap, "blog", SiteContent::new().with("/index.html", "v2"))
            .unwrap();
        assert!(r1.seq > r0.seq, "monotonic publish order");
        let hist = reg.receipt_history("blog");
        assert_eq!(hist.len(), 2, "prior receipt retained in history");
        assert_eq!(hist[0].seq, r0.seq);
        assert_eq!(hist[1].seq, r1.seq);
        assert_eq!(
            reg.get("blog").unwrap().content.resolve("/").unwrap().body,
            b"v2"
        );
    }

    #[test]
    fn unpublish_is_cap_and_owner_gated_and_receipted() {
        let reg = SiteRegistry::signed([3u8; 32]);
        let signer = reg.receipt_signer().unwrap();
        let cap = PublishCap::for_site("agent:alice", "blog");
        reg.publish(&cap, "blog", bundle()).unwrap();

        // A different owner's cap for the same name cannot delete it.
        let mallory = PublishCap::for_site("agent:mallory", "blog");
        assert!(matches!(
            reg.unpublish(&mallory, "blog"),
            Err(PublishError::NotOwner { .. })
        ));
        assert!(reg.get("blog").is_some(), "not deleted by a non-owner");

        // The owner deletes it; a signed tombstone receipt is appended + re-witnessable.
        let tomb = reg.unpublish(&cap, "blog").unwrap();
        assert!(tomb.deleted);
        assert!(verify_receipt(&tomb, signer), "tombstone re-witnesses");
        assert!(reg.get("blog").is_none(), "deleted");
        // History retains publish THEN delete.
        let hist = reg.receipt_history("blog");
        assert_eq!(hist.len(), 2);
        assert!(!hist[0].deleted && hist[1].deleted);

        // Unpublishing an absent site is refused.
        assert!(matches!(
            reg.unpublish(&cap, "blog"),
            Err(PublishError::NotOwner { .. })
        ));
    }

    #[test]
    fn signed_receipt_re_witnesses_and_tamper_fails() {
        let reg = SiteRegistry::signed([42u8; 32]);
        let signer = reg.receipt_signer().unwrap();
        let cap = PublishCap::for_site("agent:alice", "blog");
        let r = reg.publish(&cap, "blog", bundle()).unwrap();
        assert!(
            verify_receipt(&r, signer),
            "the signed receipt re-witnesses"
        );

        // A tampered field breaks the signature.
        let mut evil = r.clone();
        evil.owner = "agent:mallory".to_string();
        assert!(
            !verify_receipt(&evil, signer),
            "tampered owner fails verify"
        );

        // A flipped delete flag also breaks it (bound into the body hash).
        let mut evil2 = r.clone();
        evil2.deleted = true;
        assert!(
            !verify_receipt(&evil2, signer),
            "tampered delete flag fails"
        );

        // A different expected signer fails.
        assert!(!verify_receipt(&r, [7u8; 32]));
    }

    #[test]
    fn serve_verified_refuses_divergent_bytes() {
        // A cell whose stored bytes were swapped after commitment: serve_verified
        // returns 500 instead of serving bytes that do not match the receipt.
        let mut cell = SiteCell::new(
            "blog",
            "agent:alice",
            SiteContent::new().with("/index.html", "real"),
        );
        assert!(cell.verify_commitment());
        // Tamper: mutate content but keep the OLD root.
        cell.content = SiteContent::new().with("/index.html", "SWAPPED");
        assert!(!cell.verify_commitment(), "commitment now diverges");
        let served = cell.serve_verified("/");
        assert_eq!(served.status, 500, "divergent bytes refused");
    }

    #[test]
    fn cap_and_name_gates_bite() {
        let reg = SiteRegistry::new();
        // wrong-site cap
        let wrong = PublishCap::for_site("agent:alice", "other");
        assert!(matches!(
            reg.publish(&wrong, "blog", bundle()),
            Err(PublishError::CapRefused { .. })
        ));
        // invalid name
        let ok = PublishCap::for_site("agent:alice", "Bad.Name");
        assert!(matches!(
            reg.publish(&ok, "Bad.Name", bundle()),
            Err(PublishError::InvalidName(_))
        ));
        // empty content
        let cap = PublishCap::for_site("agent:alice", "blog");
        assert!(matches!(
            reg.publish(&cap, "blog", SiteContent::new()),
            Err(PublishError::EmptyContent)
        ));
        assert!(reg.get("blog").is_none());
    }

    #[test]
    fn host_resolution_is_apex_parameterized() {
        let cfg = HostConfig::with_apex("example.test");
        assert_eq!(
            cfg.site_name_from_host("blog.example.test").as_deref(),
            Some("blog")
        );
        assert_eq!(
            cfg.site_name_from_host("Blog.example.test:443").as_deref(),
            Some("blog")
        );
        assert_eq!(cfg.site_name_from_host("example.test"), None);
        assert_eq!(cfg.site_name_from_host("www.example.test"), None);
        assert_eq!(cfg.site_name_from_host("a.b.example.test"), None);
        // bare-label local fallback
        assert_eq!(cfg.site_name_from_host("blog").as_deref(), Some("blog"));
        assert_eq!(cfg.url_for("blog"), "https://blog.example.test/");

        let local = HostConfig::local();
        assert_eq!(
            local.site_name_from_host("blog:8080").as_deref(),
            Some("blog")
        );
        assert_eq!(local.site_name_from_host("blog.other.test"), None);
    }
}
