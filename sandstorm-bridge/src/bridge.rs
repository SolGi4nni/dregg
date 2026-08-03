//! The dregg **http-bridge shim** — run an `.spk` grain as a served workload.
//!
//! The key fact the integration turns on (plan §1.5): the vast majority of catalog
//! apps are *not* native Cap'n Proto — they are an ordinary HTTP server on
//! `localhost:8000` inside the chroot, fronted by `sandstorm-http-bridge`. The bridge
//! owns the grain's single outside socket, implements the `WebSession` capnp
//! interface, and proxies HTTP-over-RPC to that local server — injecting the
//! identity/permission headers (`X-Sandstorm-User-Id`, `-Username`, `-Permissions`,
//! `-Session-Id`) the app reads to know who is calling and what they may do.
//!
//! The dregg shim is that bridge, with the permission headers **derived from the
//! holder's dregg cap**: the facets of the cap a session presents *become* the
//! `X-Sandstorm-Permissions` value. So the app's permission model is enforced by the
//! cap lattice (and is witnessed), not by an ambient identity the host asserts.
//!
//! This module is the `WebSession`→HTTP surface + the cap→headers derivation + the
//! grain `/var` ↔ cell umem wiring, exercised in-process. A real grain runs the
//! `.spk` chroot in a `Caged`/`MicroVm` tier; here a [`GrainWorkload`] stands in for
//! the app's `:8000` server so the shim contract (verbs, headers, persistence) is
//! exercised without executing untrusted code. The contract is exactly what a real
//! workload sees.
//!
//! A session's capability is a real `dregg-auth` `dga1_` credential; its
//! permission set is derived on the rail via [`crate::webauth_rail::derive_permissions`].

use std::collections::BTreeMap;

use dregg_auth::credential::PublicKey;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

use crate::cell::{DataRoot, InclusionProof, Umem};
use crate::limits::ResourceLease;
use crate::net::{EgressDecision, NetworkPolicy};
use crate::webauth_rail::derive_permissions;

/// Percent-encode a string exactly as `sandstorm-http-bridge` does for the
/// `X-Sandstorm-Username` header — `kj::encodeUriComponent`, which is JavaScript's
/// `encodeURIComponent`. Every byte outside the unreserved set `A-Za-z0-9-_.!~*'()`
/// is emitted as `%XX` (uppercase hex of the UTF-8 byte). Confirmed verbatim
/// against `capnproto/c++/src/kj/encoding.c++`. A display name with a space or any
/// non-ASCII character must arrive at the app encoded this way, or our header bytes
/// diverge from the real bridge's.
pub(crate) fn uri_encode_component(s: &str) -> String {
    fn unreserved(b: u8) -> bool {
        b.is_ascii_alphanumeric()
            || matches!(
                b,
                b'-' | b'_' | b'.' | b'!' | b'~' | b'*' | b'\'' | b'(' | b')'
            )
    }
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if unreserved(b) {
            out.push(b as char);
        } else {
            out.push('%');
            out.push(
                char::from_digit((b >> 4) as u32, 16)
                    .unwrap()
                    .to_ascii_uppercase(),
            );
            out.push(
                char::from_digit((b & 0x0f) as u32, 16)
                    .unwrap()
                    .to_ascii_uppercase(),
            );
        }
    }
    out
}

/// An HTTP method the `WebSession` surface carries (`web-session.capnp`: get / post /
/// put / delete / …). The non-GET verbs matter for apps like Davros (WebDAV).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Method {
    Get,
    Post,
    Put,
    Delete,
}

/// An HTTP request entering the grain (after the gateway routes the session to it).
#[derive(Clone, Debug)]
pub struct HttpRequest {
    pub method: Method,
    /// The path within the grain (`/`, `/pad/x`, …).
    pub path: String,
    pub body: Vec<u8>,
}

impl HttpRequest {
    pub fn get(path: impl Into<String>) -> Self {
        HttpRequest {
            method: Method::Get,
            path: path.into(),
            body: Vec::new(),
        }
    }
    pub fn post(path: impl Into<String>, body: impl Into<Vec<u8>>) -> Self {
        HttpRequest {
            method: Method::Post,
            path: path.into(),
            body: body.into(),
        }
    }
}

/// The grain's HTTP response (`web-session.capnp:WebSession.Response`, simplified).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HttpResponse {
    pub status: u16,
    pub body: Vec<u8>,
}

impl HttpResponse {
    pub fn ok(body: impl Into<Vec<u8>>) -> Self {
        HttpResponse {
            status: 200,
            body: body.into(),
        }
    }
    pub fn forbidden() -> Self {
        HttpResponse {
            status: 403,
            body: b"forbidden".to_vec(),
        }
    }
}

/// The request as it reaches the app's `:8000` server — the bridge has injected the
/// `X-Sandstorm-*` headers derived from the session's dregg cap. The app reads these
/// to learn the caller and their permissions, never raw identities.
#[derive(Clone, Debug)]
pub struct BridgedRequest {
    pub method: Method,
    pub path: String,
    pub body: Vec<u8>,
    /// `X-Sandstorm-User-Id` / `-Username` / `-Permissions` / `-Session-Id`.
    pub headers: BTreeMap<String, String>,
}

impl BridgedRequest {
    /// The permission set the bridge handed the app (`X-Sandstorm-Permissions`),
    /// parsed back into the facet list — what the app is allowed to do this request.
    pub fn permissions(&self) -> Vec<String> {
        self.headers
            .get("X-Sandstorm-Permissions")
            .filter(|s| !s.is_empty())
            .map(|s| s.split(',').map(|p| p.to_string()).collect())
            .unwrap_or_default()
    }

    fn has(&self, facet: &str) -> bool {
        self.permissions().iter().any(|p| p == facet)
    }
}

/// The grain's in-sandbox HTTP app — the `:8000` server the bridge proxies to. Its
/// `/var` is the cell umem heap, passed in so writes persist into the committed cell.
pub trait GrainWorkload {
    /// Serve one request. `var` is the grain's `/var` (the cell umem heap); mutate it
    /// to persist state. The request carries the cap-derived permission headers.
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse;
}

/// The dregg http-bridge: derive identity/permission headers from a session's cap,
/// hand the request to the grain workload over its `/var`, and commit the resulting
/// umem state to a `data_root` (the witnessed checkpoint of what the request changed).
pub struct HttpBridge;

/// The principal a session presents to a grain: who they are + the `dga1_` grain
/// capability they present. The token is verified on the real `dregg-auth`
/// rail at [`HttpBridge::serve`]; the permission set it admits (for this grain,
/// this presenter, right now) becomes the app's permissions.
#[derive(Clone, Debug)]
pub struct Session {
    pub user_id: String,
    pub username: String,
    pub session_id: String,
    /// The presented `dga1_…` grain capability token.
    pub token: String,
    /// The subject the presenter claims — must match the token's `subject` caveat.
    pub presenter_subject: String,
}

impl Session {
    /// Build a session presenting a `dga1_` grain capability token as `presenter`.
    pub fn presenting(
        user_id: impl Into<String>,
        username: impl Into<String>,
        session_id: impl Into<String>,
        token: impl Into<String>,
        presenter: impl Into<String>,
    ) -> Session {
        Session {
            user_id: user_id.into(),
            username: username.into(),
            session_id: session_id.into(),
            token: token.into(),
            presenter_subject: presenter.into(),
        }
    }

    /// The permission set this session's cap admits over `grain_cell_id`, derived on
    /// the real rail (see [`derive_permissions`]). Empty when the credential is
    /// forged, for another grain, presented by a non-owner, expired, or grants none
    /// of the declared facets.
    pub fn permissions(
        &self,
        host_pub: &PublicKey,
        grain_cell_id: &str,
        declared_permissions: &[String],
        now: u64,
    ) -> Vec<String> {
        derive_permissions(
            &self.token,
            host_pub,
            grain_cell_id,
            &self.presenter_subject,
            declared_permissions,
            now,
        )
    }
}

/// The result of serving one request through the bridge: the app's response plus the
/// new committed `data_root` (so the caller can record the witnessed state change).
///
/// ## The independent anchor the bare `Served` lacks
///
/// A `Served` alone does **not** make the serve trustless: the visitor gets the bytes AND
/// the `new_data_root` from the *same* host, so a host that renders card `Y`, writes `Y`
/// into `/var`, and returns body `Y` with `new_data_root = commit({key: Y})` is fully
/// self-consistent — the visitor re-hashing `Y` reproduces `root(Y)` and matches. Nothing
/// external says `root(Y)` is the state the OWNER committed. Trustlessness needs (a) an
/// independent anchor on the root, and (b) a way to check the served card is the value at
/// the served key under that root without re-hashing the whole heap. Those are
/// [`RootAttestation`] (an ed25519 owner signature over the root) + a [`InclusionProof`]
/// (a single-leaf Merkle path) — bundled as an [`AttestedServed`].
#[derive(Clone, Debug)]
pub struct Served {
    pub response: HttpResponse,
    pub new_data_root: DataRoot,
}

/// The canonical bytes the grain OWNER signs to attest a **served** `data_root`: a
/// domain-separated, NUL-delimited `(grain_cell_id ‖ data_root)`. Mirrors
/// [`crate::grain::attestation_message`] (the backup pedigree tooth), specialized to the
/// serve path — binding the root to the specific grain, so an attestation for one grain's
/// root cannot be replayed as another's. Both fields are NUL-free (a `cell:…` id, a
/// `heap1…` root), so the delimiter is unambiguous.
pub fn served_root_message(grain_cell_id: &str, data_root: &str) -> Vec<u8> {
    let mut msg = Vec::new();
    msg.extend_from_slice(b"grain-served-root-attestation:v1");
    msg.push(0);
    msg.extend_from_slice(grain_cell_id.as_bytes());
    msg.push(0);
    msg.extend_from_slice(data_root.as_bytes());
    msg
}

/// **The independent anchor on a served root** — an ed25519 signature by the grain OWNER's
/// key over `(grain_cell_id ‖ data_root)` ([`served_root_message`]). It is the serve-path
/// analog of [`crate::grain::GrainBackup`]'s attestation: the decisive tooth that a
/// hostile serving host cannot forge, because it lacks the owner's key.
///
/// A visitor verifies it with [`RootAttestation::verify`] against the owner's public key
/// **obtained independently** — from the cell's ledger commitment, NOT from the serving
/// host's response. A host that fabricates a card `Y` and a matching `root(Y)` can sign
/// `root(Y)` only under its OWN key; that attestation fails to verify under the owner's
/// key, so the fabrication is caught.
#[derive(Clone, Debug)]
pub struct RootAttestation {
    /// The grain the root belongs to (bound into the signed message).
    pub grain_cell_id: String,
    /// The committed root this attestation vouches for.
    pub data_root: DataRoot,
    /// The ed25519 public key (32 bytes) that produced the signature — carried for
    /// routing; [`verify`](Self::verify) does NOT trust it blindly, it must equal the
    /// externally-supplied *expected* owner key.
    pub signer: [u8; 32],
    /// The ed25519 signature (64 bytes) over [`served_root_message`].
    pub signature: Vec<u8>,
}

impl RootAttestation {
    /// The OWNER attests a committed served root: sign `(grain_cell_id ‖ data_root)` with
    /// the owner's key. In a real deployment this key is the owner's registered identity
    /// key (the same `subject` principal the webauth rail seals grain caps to), held by the
    /// owner's device / the host's identity registry — the same seam noted on
    /// [`crate::grain::GrainCell::backup`]. A hostile serving host does not hold it.
    pub fn sign(owner_key: &SigningKey, grain_cell_id: &str, data_root: &DataRoot) -> Self {
        let sig = owner_key.sign(&served_root_message(grain_cell_id, &data_root.0));
        RootAttestation {
            grain_cell_id: grain_cell_id.to_string(),
            data_root: data_root.clone(),
            signer: owner_key.verifying_key().to_bytes(),
            signature: sig.to_bytes().to_vec(),
        }
    }

    /// Verify the attestation against the owner's **expected** public key — the key the
    /// visitor obtains independently (from the cell's ledger commitment, never from the
    /// serving host). Checks the self-declared `signer` equals the expected key AND the
    /// signature verifies over `(grain_cell_id ‖ data_root)`. `false` on any mismatch — an
    /// attestation minted under a different key (a tampering host's own key) is rejected.
    pub fn verify(&self, expected_owner: &VerifyingKey) -> bool {
        if self.signer != expected_owner.to_bytes() {
            return false;
        }
        let sig_bytes: [u8; 64] = match self.signature.as_slice().try_into() {
            Ok(b) => b,
            Err(_) => return false,
        };
        let sig = Signature::from_bytes(&sig_bytes);
        expected_owner
            .verify(
                &served_root_message(&self.grain_cell_id, &self.data_root.0),
                &sig,
            )
            .is_ok()
    }
}

/// A served response bundled with everything a visitor needs to verify authenticity
/// **against an owner key + root obtained independently** (the ledger), even when the
/// serving host is hostile: the owner's [`RootAttestation`] over the committed root, plus
/// an [`InclusionProof`] that the served card is the value at its key under that root.
///
/// The visitor's check (see [`AttestedServed::witnessed_authentic`]): given the owner's
/// public key from an independent channel, `(owner signed root R) ∧ (card is the value at
/// key under R)` ⇒ the card is authentic. A host that swaps card+root together fails the
/// first conjunct (it cannot sign under the owner's key); a host that lies about the leaf
/// fails the second (the Merkle path will not fold to `R`).
#[derive(Clone, Debug)]
pub struct AttestedServed {
    pub response: HttpResponse,
    pub new_data_root: DataRoot,
    /// The owner's signature over `new_data_root` — the independent anchor.
    pub attestation: RootAttestation,
    /// The `/var` key the served card was materialized under (the leaf being proven).
    pub witness_key: Option<String>,
    /// The single-leaf Merkle proof that `witness_key`'s value is included under
    /// `new_data_root`. `None` when no witness key was requested (e.g. a `403`).
    pub inclusion: Option<InclusionProof>,
}

impl AttestedServed {
    /// **The trustless-serve verification a visitor runs**, holding only the owner's public
    /// key from an independent channel (the ledger — NOT this host), the served card bytes,
    /// and this bundle. Returns `true` iff BOTH:
    ///
    /// 1. the owner attested this exact `new_data_root` for this grain (the root has an
    ///    independent anchor — a hostile host cannot forge it without the owner's key), and
    /// 2. `card` is exactly the value at `witness_key` under `new_data_root` (the served
    ///    bytes are the committed leaf — proven by the Merkle path, no whole-heap re-hash).
    ///
    /// This is authentic-IFF: it holds even if the serving host is hostile, and it does NOT
    /// trust anything the host asserts about the root — only the owner's independent
    /// signature and the visitor's own re-hash of the card.
    pub fn witnessed_authentic(&self, expected_owner: &VerifyingKey, card: &[u8]) -> bool {
        if !self.attestation.verify(expected_owner) {
            return false;
        }
        match (&self.witness_key, &self.inclusion) {
            (Some(key), Some(proof)) => {
                crate::cell::verify_inclusion(&self.new_data_root, key, card, proof)
            }
            _ => false,
        }
    }

    /// **The trustless-serve check chained to the LEDGER, not the host.** Identical to
    /// [`witnessed_authentic`](Self::witnessed_authentic) except the trusted root is the
    /// grain cell's committed **heap-root** obtained independently from the federation (the
    /// real dregg heap-root — the encoded [`dregg_circuit::heap_root::compute_heap_root`]
    /// felt = [`crate::grain::grain_cell_commitment`]), NOT `self.new_data_root` (which the
    /// serving host chose). `ledger_heap_root_hex` is the **hex** wire form the federation
    /// returns (the codec fix decodes it). See [`verify_served_against_ledger`] for the
    /// checks.
    ///
    /// This is the seam the witness review named, healed in the real scheme: authenticity
    /// chains to the cell's committed heap-root, a genuine ledger value in the same
    /// Poseidon2 scheme the inclusion proofs fold in — so a host cannot substitute its own
    /// root. It closes the pole owner-attestation-alone could not: a host that somehow held
    /// the owner key could sign a fabricated root, but it cannot rewrite the federation's
    /// stored heap-root, so a served card that is not a leaf under the LEDGER's heap-root is
    /// caught here regardless of what attestation the host bundles. (Named remaining seam:
    /// the federation WRITE of the heap-root as a distinct fetchable value.)
    pub fn verify_against_ledger(
        &self,
        ledger_heap_root_hex: &str,
        owner_pubkey: &VerifyingKey,
        card: &[u8],
    ) -> bool {
        match (&self.witness_key, &self.inclusion) {
            (Some(key), Some(proof)) => verify_served_against_ledger(
                card,
                key,
                proof,
                ledger_heap_root_hex,
                owner_pubkey,
                &self.attestation,
            ),
            _ => false,
        }
    }
}

/// Encode a raw 32-byte heap root as the LEDGER's hex wire form — lowercase, no
/// separators, byte-for-byte the `hex_encode` the federation returns for a cell
/// commitment (`node/src/api.rs`, `bytes.iter().map(|b| format!("{b:02x}"))`). This is
/// how a grain's published heap-root arrives at a visitor.
pub fn heap_root_hex(root: [u8; 32]) -> String {
    data_encoding::HEXLOWER.encode(&root)
}

/// Decode the LEDGER's hex heap-root back to raw 32 bytes. Accepts upper- or lowercase
/// hex (`HEXLOWER_PERMISSIVE`); `None` on malformed input or a non-32-byte length — the
/// codec fix for the api-returns-hex reality (the value must be decoded, not consumed as
/// if it were raw bytes).
fn heap_root_from_hex(hex: &str) -> Option<[u8; 32]> {
    let bytes = data_encoding::HEXLOWER_PERMISSIVE
        .decode(hex.as_bytes())
        .ok()?;
    bytes.as_slice().try_into().ok()
}

/// A faithful (partial) mirror of node's `CellDetailResponse` (`node/src/api.rs:506`) — the
/// body of `GET /api/cell/{id}`. Only the fields the visitor's READ path needs are modeled;
/// serde ignores the rest, so a real node's full response deserializes into it unchanged. The
/// LIVE wire uses node's own type; node is not a dependency of this crate.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct CellDetailResponse {
    /// Whether the cell was found in the ledger.
    #[serde(default)]
    pub found: bool,
    /// The cell's committed root, hex-encoded — node's `state_commitment` field
    /// (`node/src/api.rs:523`). The value the visitor verifies a served card against.
    #[serde(default)]
    pub state_commitment: String,
}

/// Why [`fetch_ledger_root`] could not extract a committed root from a cell-detail response.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LedgerFetchError {
    /// The response body was not valid `CellDetailResponse` JSON.
    Malformed,
    /// The cell was not found in the ledger (`found: false`).
    NotFound,
    /// The cell exists but carries no committed value yet.
    NoCommitment,
    /// The `state_commitment` field was not valid 32-byte hex.
    BadCommitmentHex,
}

impl std::fmt::Display for LedgerFetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            LedgerFetchError::Malformed => "cell-detail response is not valid JSON",
            LedgerFetchError::NotFound => "cell not found in the federation ledger",
            LedgerFetchError::NoCommitment => "cell has no committed value yet",
            LedgerFetchError::BadCommitmentHex => "state_commitment is not valid 32-byte hex",
        })
    }
}

impl std::error::Error for LedgerFetchError {}

/// **The READ half of the cloud-witness bridge: extract the committed root a visitor verifies
/// against, from a `GET /api/cell/{id}` response.** Parses the response body (node's
/// [`CellDetailResponse`]) and decodes its `state_commitment` hex field to raw 32 bytes. This
/// is the value the grain owner published with [`crate::grain::publish_grain_root`], so
/// `fetch_ledger_root(response_after(publish_grain_root(.., R))) == R`: the visitor's
/// independent root equals the root the served card is a leaf under. Feed the returned bytes
/// (via [`heap_root_hex`]) to [`verify_served_against_ledger`].
///
/// The root here is sourced from the FEDERATION response, never the serving host — that is
/// what makes the witness independent. (The residual seam: on a stock node `state_commitment`
/// is the whole-cell BLAKE3 digest that *absorbs* this heap-root rather than exposing it
/// directly; a deployment surfaces the published heap-root as the cell's committed value — the
/// SCHEME and hex wire already match what `publish_grain_root` writes. See
/// [`crate::grain::grain_cell_commitment`].)
pub fn fetch_ledger_root(cell_detail_json: &str) -> Result<[u8; 32], LedgerFetchError> {
    let detail: CellDetailResponse =
        serde_json::from_str(cell_detail_json).map_err(|_| LedgerFetchError::Malformed)?;
    if !detail.found {
        return Err(LedgerFetchError::NotFound);
    }
    if detail.state_commitment.is_empty() {
        return Err(LedgerFetchError::NoCommitment);
    }
    heap_root_from_hex(&detail.state_commitment).ok_or(LedgerFetchError::BadCommitmentHex)
}

/// **The visitor's independent verify — authenticity chained to the LEDGER's heap-root.**
///
/// The visitor holds: the served `card` bytes + its `witness_key` + `inclusion` proof +
/// the owner's `attestation` (all reachable via the serving host), AND — crucially — the
/// `ledger_heap_root_hex` and `owner_pubkey` obtained from an **independent channel**: the
/// federation. `ledger_heap_root_hex` is the grain cell's committed **heap-root**, in the
/// real dregg scheme (the encoded [`dregg_circuit::heap_root::compute_heap_root`] felt =
/// [`crate::grain::grain_cell_commitment`] of the `/var` at the last honest commit), as a
/// **hex string** — the wire form the federation returns (`hex_encode`, mirroring the
/// `state_commitment` codec), which this function DECODES (the hex-vs-raw codec fix).
/// `owner_pubkey` is the cell owner's registered key. Neither comes from the serving host.
///
/// The heap-root is the value a real deployment's ledger carries for the cell's heap (the
/// `heap_root` register the canonical `state_commitment` absorbs). The named seam: the
/// federation must publish this heap-root as a distinct fetchable value (its membership in
/// the whole-cell `state_commitment` is a separate check); the SCHEME here already matches
/// what the ledger carries.
///
/// Returns `true` iff BOTH:
/// 1. the owner attested **exactly the ledger's committed heap-root** — `attestation`
///    verifies under `owner_pubkey` AND its `data_root` equals the heap-root rebuilt from
///    the decoded ledger bytes (so a host's attestation over some *other* root is
///    rejected), and
/// 2. `card` is the value at `witness_key` under the **ledger heap-root** (the inclusion
///    proof folds — in the real Poseidon2/felt heap scheme — to the ledger heap-root, not
///    the host's served root).
///
/// The decisive property: a hostile host that serves card `Y`, commits `root(Y)`, and
/// bundles its own self-consistent attestation over `root(Y)` is CAUGHT — the ledger's
/// committed heap-root is `root(X)` (the last honestly-committed state the federation
/// stored), and `Y` is not a leaf under `root(X)`, so (2) fails. This holds even against a
/// host that possessed the owner key: it can forge an attestation but it cannot rewrite the
/// federation's independently-stored commitment. A malformed hex ledger value is rejected.
pub fn verify_served_against_ledger(
    card: &[u8],
    witness_key: &str,
    inclusion: &InclusionProof,
    ledger_heap_root_hex: &str,
    owner_pubkey: &VerifyingKey,
    attestation: &RootAttestation,
) -> bool {
    // Decode the LEDGER's hex heap-root to raw bytes (the api-returns-hex codec fix). A
    // malformed value cannot authenticate anything.
    let Some(ledger_root) = heap_root_from_hex(ledger_heap_root_hex) else {
        return false;
    };
    let ledger_data_root = DataRoot::from_root_bytes(ledger_root);
    // (1) The owner attested EXACTLY the ledger's committed heap-root — the independent
    //     anchor, bound to the root the FEDERATION stored, not whatever root the host served.
    if !(attestation.verify(owner_pubkey) && attestation.data_root == ledger_data_root) {
        return false;
    }
    // (2) The served card is the value at `witness_key` under the LEDGER heap-root — the
    //     inclusion proof must fold (in the real Poseidon2 heap scheme) to the ledger
    //     heap-root, so a card served under any other root is rejected here (the
    //     tamper-against-ledger tooth).
    crate::cell::verify_inclusion(&ledger_data_root, witness_key, card, inclusion)
}

impl HttpBridge {
    /// Build the bridged request: inject the `X-Sandstorm-*` headers from the session
    /// and its derived permission set. The app never sees a raw identity, only these.
    ///
    /// The four headers are the identity+authority core of the real
    /// `sandstorm-http-bridge` contract (per `sandstorm-http-bridge.c++`):
    /// `X-Sandstorm-Permissions` is a comma-separated list of permission *names*
    /// (not indices), and `X-Sandstorm-Username` is `encodeUriComponent`-encoded.
    /// The real bridge additionally sets optional context headers (`-Tab-Id`,
    /// `-Preferred-Handle`, `-User-Picture`, `-User-Pronouns`, `-Session-Type`,
    /// `-Base-Path`, `-Api`); a dregg session carries no analog, so the shim omits
    /// them.
    fn headers_for(req: &HttpRequest, session: &Session, permissions: &[String]) -> BridgedRequest {
        let mut facets = permissions.to_vec();
        facets.sort();
        let mut headers = BTreeMap::new();
        headers.insert("X-Sandstorm-User-Id".into(), session.user_id.clone());
        headers.insert(
            "X-Sandstorm-Username".into(),
            uri_encode_component(&session.username),
        );
        headers.insert("X-Sandstorm-Session-Id".into(), session.session_id.clone());
        headers.insert("X-Sandstorm-Permissions".into(), facets.join(","));
        BridgedRequest {
            method: req.method,
            path: req.path.clone(),
            body: req.body.clone(),
            headers,
        }
    }

    /// Build the bridged request from a session's `dga1_` cap: derive the permission
    /// set on the real rail (under the host root, bound to this grain/presenter/time)
    /// and inject the `X-Sandstorm-*` headers from it. A credential that grants no
    /// declared facet yields an empty permission header.
    pub fn bridge_request(
        req: &HttpRequest,
        session: &Session,
        host_pub: &PublicKey,
        grain_cell_id: &str,
        declared_permissions: &[String],
        now: u64,
    ) -> BridgedRequest {
        let permissions = session.permissions(host_pub, grain_cell_id, declared_permissions, now);
        Self::headers_for(req, session, &permissions)
    }

    /// Serve one request end-to-end: derive the session cap's permission set on the
    /// real rail, bridge the headers from it, run the workload over the grain's
    /// `/var` umem, and commit the new `data_root`. An empty permission set — forged
    /// credential, wrong grain, non-owner presenter, expired, or no declared facet
    /// granted — is answered `403` with no effect.
    pub fn serve(
        workload: &dyn GrainWorkload,
        grain_cell_id: &str,
        session: &Session,
        host_pub: &PublicKey,
        declared_permissions: &[String],
        now: u64,
        var: &mut Umem,
        req: &HttpRequest,
    ) -> Served {
        let permissions = session.permissions(host_pub, grain_cell_id, declared_permissions, now);
        if permissions.is_empty() {
            return Served {
                response: HttpResponse::forbidden(),
                new_data_root: var.commit(),
            };
        }
        let bridged = Self::headers_for(req, session, &permissions);
        let response = workload.serve(&bridged, var);
        Served {
            new_data_root: var.commit(),
            response,
        }
    }

    /// **Trustless serve** — [`serve`](Self::serve), plus the two teeth that make "the host
    /// cannot tamper with what it serves" actually TRUE against a hostile host:
    ///
    /// * the committed root is **owner-attested** ([`RootAttestation::sign`] with
    ///   `owner_key`) — an independent anchor the serving host cannot forge, and
    /// * an **inclusion proof** for `witness_key` (the key the served card is materialized
    ///   under) is emitted, so a visitor verifies the card is the value at that key under
    ///   the attested root without the rest of `/var`.
    ///
    /// The visitor then runs [`AttestedServed::witnessed_authentic`] with the owner's key
    /// obtained *independently* (the ledger). `owner_key` models the OWNER co-signing the
    /// committed state; a hostile host lacks it and can only attest under its own key, which
    /// the visitor's owner-key check rejects. (Publishing the attested root to the
    /// federation ledger — the visitor's independent channel for the owner key + root — is
    /// the named deferred seam; the attestation itself is real here.)
    #[allow(clippy::too_many_arguments)]
    pub fn serve_attested(
        workload: &dyn GrainWorkload,
        grain_cell_id: &str,
        session: &Session,
        host_pub: &PublicKey,
        declared_permissions: &[String],
        now: u64,
        var: &mut Umem,
        req: &HttpRequest,
        owner_key: &SigningKey,
        witness_key: Option<&str>,
    ) -> AttestedServed {
        let served = Self::serve(
            workload,
            grain_cell_id,
            session,
            host_pub,
            declared_permissions,
            now,
            var,
            req,
        );
        let attestation = RootAttestation::sign(owner_key, grain_cell_id, &served.new_data_root);
        let inclusion = witness_key.and_then(|k| var.prove(k));
        AttestedServed {
            response: served.response,
            new_data_root: served.new_data_root,
            attestation,
            witness_key: witness_key.map(|s| s.to_string()),
            inclusion,
        }
    }

    /// **L4 + L7** — serve a request bounded by the grain's funded lease. Identical to
    /// [`serve`](Self::serve) but, after the workload mutates `/var`, the new total
    /// storage is admitted against the lease; a write that would exceed the storage
    /// quota is rolled back and answered `507`.
    #[allow(clippy::too_many_arguments)]
    pub fn serve_bounded(
        workload: &dyn GrainWorkload,
        grain_cell_id: &str,
        session: &Session,
        host_pub: &PublicKey,
        declared_permissions: &[String],
        now: u64,
        var: &mut Umem,
        lease: &mut ResourceLease,
        req: &HttpRequest,
    ) -> Served {
        let permissions = session.permissions(host_pub, grain_cell_id, declared_permissions, now);
        if permissions.is_empty() {
            return Served {
                response: HttpResponse::forbidden(),
                new_data_root: var.commit(),
            };
        }
        let snapshot = var.clone();
        let bridged = Self::headers_for(req, session, &permissions);
        let response = workload.serve(&bridged, var);
        if lease.admit_storage(var.stored_bytes() as u64).is_err() {
            // Over the storage quota — roll the write back and refuse it.
            *var = snapshot;
            return Served {
                response: HttpResponse {
                    status: 507,
                    body: b"insufficient storage: grain over lease quota".to_vec(),
                },
                new_data_root: var.commit(),
            };
        }
        Served {
            new_data_root: var.commit(),
            response,
        }
    }

    /// **L2 + L7** — the bridge is the grain's *only* egress path. Any outbound the
    /// grain attempts is routed through here and checked against its [`NetworkPolicy`].
    /// A grain with no powerbox-granted [`crate::net::OutboundCap`] for `host:port` is
    /// denied (deny-default, no ambient network). There is no other egress surface: a
    /// grain that cannot route through the bridge cannot reach the network at all.
    pub fn egress(policy: &NetworkPolicy, host: &str, port: u16) -> EgressDecision {
        policy.check_outbound(host, port)
    }
}

/// A representative http-bridge app: a permissioned notes store (the shape of
/// Etherpad/Davros — read needs `view`, write needs `edit`). It reads its permissions
/// from the bridge headers and persists notes into `/var` (the cell umem), so the
/// catalog-app contract (verbs + permission gating + persistence) is exercised.
pub struct NotesApp;

impl GrainWorkload for NotesApp {
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
        let key = format!("notes{}", req.path);
        match req.method {
            Method::Get => {
                if !req.has("view") {
                    return HttpResponse::forbidden();
                }
                match var.get(&key) {
                    Some(b) => HttpResponse::ok(b.to_vec()),
                    None => HttpResponse {
                        status: 404,
                        body: b"not found".to_vec(),
                    },
                }
            }
            Method::Post | Method::Put => {
                if !req.has("edit") {
                    return HttpResponse::forbidden();
                }
                var.put(key, req.body.clone());
                HttpResponse::ok(b"stored".to_vec())
            }
            Method::Delete => {
                if !req.has("edit") {
                    return HttpResponse::forbidden();
                }
                let existed = var.remove(&key);
                HttpResponse::ok(if existed {
                    b"deleted".to_vec()
                } else {
                    b"absent".to_vec()
                })
            }
        }
    }
}

/// A **hosted-grain card server** — the WebSession leg of trustless cloud hosting. The
/// grain holds a `deos-view` card (a [`GrainRun`]: a CI run / rented-grain surface) and,
/// on a GET of the card's path, renders it to a full browser-loadable HTML document
/// ([`render_card_document`]) and serves that as the response — the SAME card the native
/// cockpit paints, now served over the web.
///
/// **Witnessed — and what that requires.** The served HTML is materialized into the
/// grain's `/var` (the cell umem heap) at [`Self::key`], so the `data_root` the bridge
/// commits is the commitment of *exactly the bytes served at that key*. But a bare
/// [`HttpBridge::serve`] is NOT trustless on its own: the visitor gets the bytes AND the
/// root from the same host, so a hostile host can render card `Y`, commit `root(Y)`, and
/// return both self-consistently — the re-hash matches, and nothing external says `root(Y)`
/// is the state the owner committed. Two things close that, and the visitor MUST have both
/// from an INDEPENDENT channel (the cell's ledger), not the host's response:
///
/// * an **owner attestation** over the served root ([`HttpBridge::serve_attested`] →
///   [`RootAttestation`]) — the independent anchor a tampering host cannot forge (it lacks
///   the owner's key), and
/// * a **single-leaf inclusion proof** ([`crate::cell::Umem::prove`]) that the served card
///   is the value at [`Self::key`] under that root — so the check needs only the card bytes,
///   NOT a re-hash of the whole (real, stateful) `/var`, which a flat digest would require.
///
/// The property is therefore: *witnessed IFF the visitor obtains the owner's public key and
/// the committed root independently (the ledger) and runs
/// [`AttestedServed::witnessed_authentic`]* — then `(owner signed root R) ∧ (card is the
/// value at key under R)` ⇒ the card is authentic even if the serving host is hostile. The
/// write is content-addressed and idempotent: serving the same card twice yields the same
/// root.
///
/// **Cap-gated.** The powerbox cap-gate is [`HttpBridge::serve`]: an empty permission set
/// (no cap, a cap for another grain, a forged/leaked credential, or one granting no
/// declared facet) is answered `403` before the workload ever runs, so the card is not
/// served. The workload additionally requires the `view` facet on the derived header,
/// mirroring [`NotesApp`].
pub struct CardGrainWorkload {
    /// The document `<title>` (the page heads the browser tab with it).
    pub title: String,
    /// The grain path the card is served at (a GET here → the card; anything else → 404).
    pub path: String,
    /// The card to serve — a `deos-view` grain-run surface rendered via [`grain_run_view`].
    pub run: deos_view::GrainRun,
}

impl CardGrainWorkload {
    /// Host a `deos-view` [`GrainRun`] card, served at `path` with document title `title`.
    pub fn new(
        title: impl Into<String>,
        path: impl Into<String>,
        run: deos_view::GrainRun,
    ) -> Self {
        CardGrainWorkload {
            title: title.into(),
            path: path.into(),
            run,
        }
    }

    /// Render the held card to a full, browser-loadable HTML document — the SAME
    /// `ViewNode` the native cockpit paints, projected to HTML by the web renderer.
    pub fn render(&self) -> String {
        let tree = deos_view::grain_run_view(&self.run);
        deos_view::render_card_document(&self.title, &tree, &[])
    }

    /// The `/var` key the served card bytes are materialized under — the leaf a visitor
    /// proves inclusion of. A light client verifies the served card is the value at THIS
    /// key under the owner-attested root ([`crate::cell::verify_inclusion`] with
    /// [`crate::cell::Umem::prove`]'s proof) — it needs only the card bytes, this key, the
    /// proof, and the independently-obtained root, never the rest of `/var`.
    pub fn key(&self) -> String {
        format!("card{}", self.path)
    }
}

impl GrainWorkload for CardGrainWorkload {
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
        match req.method {
            // The card's path: render + witness + serve. (The shim's `HttpResponse`
            // carries no header map — the real bridge sets `Content-Type: text/html`
            // from the app; here the body is a complete `<!doctype html>` document, so
            // it is self-describing.)
            Method::Get if req.path == self.path => {
                if !req.has("view") {
                    return HttpResponse::forbidden();
                }
                let html = self.render();
                // Materialize the served bytes into `/var` so the committed `data_root`
                // witnesses exactly what was served (content-addressed + idempotent).
                var.put(self.key(), html.clone().into_bytes());
                HttpResponse::ok(html.into_bytes())
            }
            // A hosted card grain serves only its one card path; everything else is 404.
            _ => HttpResponse {
                status: 404,
                body: b"not found".to_vec(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::webauth_rail::HostAuthority;

    fn host() -> HostAuthority {
        HostAuthority::from_seed([11u8; 32])
    }

    fn declared() -> Vec<String> {
        vec!["view".into(), "edit".into()]
    }

    fn editor_session(host: &HostAuthority, grain: &str) -> Session {
        let token = host
            .mint_grain_cap(grain, "u:alice", &["view", "edit"], None)
            .encode();
        Session::presenting("u:alice", "alice", "sess:1", token, "u:alice")
    }
    fn viewer_session(host: &HostAuthority, grain: &str) -> Session {
        let token = host
            .mint_grain_cap(grain, "u:bob", &["view"], None)
            .encode();
        Session::presenting("u:bob", "bob", "sess:2", token, "u:bob")
    }

    #[test]
    fn headers_are_derived_from_the_cap_facets() {
        let host = host();
        let s = editor_session(&host, "cell:grain1");
        let b = HttpBridge::bridge_request(
            &HttpRequest::get("/x"),
            &s,
            &host.public(),
            "cell:grain1",
            &declared(),
            1000,
        );
        assert_eq!(b.headers.get("X-Sandstorm-User-Id").unwrap(), "u:alice");
        assert_eq!(
            b.headers.get("X-Sandstorm-Permissions").unwrap(),
            "edit,view"
        );
        assert_eq!(b.permissions(), vec!["edit", "view"]);
    }

    /// The `X-Sandstorm-Username` header is `encodeUriComponent`-encoded, matching
    /// the real `sandstorm-http-bridge` (`kj::encodeUriComponent`). A display name
    /// with a space and a non-ASCII character arrives percent-encoded exactly as
    /// the real bridge emits it. Unreserved `A-Za-z0-9-_.!~*'()` pass through
    /// untouched.
    #[test]
    fn username_header_is_uri_encoded_like_the_real_bridge() {
        let host = host();
        let token = host
            .mint_grain_cap("cell:grain1", "u:zoë", &["view"], None)
            .encode();
        let s = Session::presenting("u:zoë", "Zoë Smith", "sess:1", token, "u:zoë");
        let b = HttpBridge::bridge_request(
            &HttpRequest::get("/x"),
            &s,
            &host.public(),
            "cell:grain1",
            &declared(),
            1000,
        );
        // 'Z','o' unreserved; 'ë' = UTF-8 C3 AB; ' ' = %20; 'S','m','i','t','h' pass.
        assert_eq!(
            b.headers.get("X-Sandstorm-Username").unwrap(),
            "Zo%C3%AB%20Smith"
        );
        // The User-Id is an opaque id, not URI-encoded (the real bridge leaves it raw).
        assert_eq!(b.headers.get("X-Sandstorm-User-Id").unwrap(), "u:zoë");
        // Unreserved punctuation survives intact.
        let s2 = Session {
            username: "a-b_c.d!e~f*g'h(i)".into(),
            ..s
        };
        let b2 = HttpBridge::bridge_request(
            &HttpRequest::get("/x"),
            &s2,
            &host.public(),
            "cell:grain1",
            &declared(),
            1000,
        );
        assert_eq!(
            b2.headers.get("X-Sandstorm-Username").unwrap(),
            "a-b_c.d!e~f*g'h(i)"
        );
    }

    #[test]
    fn a_request_round_trips_through_the_shim() {
        let host = host();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        // An editor POSTs a note...
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &editor_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/hello", b"hi there".to_vec()),
        );
        assert_eq!(r.response.status, 200);
        // ...and a viewer reads it back through the bridge.
        let r2 = HttpBridge::serve(
            &NotesApp,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::get("/hello"),
        );
        assert_eq!(r2.response.status, 200);
        assert_eq!(r2.response.body, b"hi there");
    }

    #[test]
    fn the_permission_header_gates_the_app() {
        let host = host();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        // A viewer (no `edit` facet) cannot write — the app reads the header and 403s.
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/x", b"nope".to_vec()),
        );
        assert_eq!(r.response.status, 403);
        // Nothing persisted.
        assert!(var.is_empty());
    }

    #[test]
    fn a_cap_for_another_grain_is_inert() {
        let host = host();
        let mut var = Umem::new();
        // The session holds a genuine cap over a *different* grain — the `grain`
        // caveat fails here, so it confers nothing.
        let session = editor_session(&host, "cell:OTHER");
        let r = HttpBridge::serve(
            &NotesApp,
            "cell:grain1",
            &session,
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/x", b"x".to_vec()),
        );
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }

    /// A cap minted under a root other than the host's fails the ed25519 chain
    /// verify and is refused `403` at the bridge.
    #[test]
    fn a_forged_cap_at_the_l7_bridge_is_refused() {
        let host = host();
        let grain = "cell:grain1";
        // The attacker mints under their OWN root (they lack the host root key).
        let attacker = HostAuthority::from_seed([200u8; 32]);
        let forged = attacker
            .mint_grain_cap(grain, "u:mallory", &["view", "edit"], None)
            .encode();
        let session = Session::presenting("u:mallory", "mallory", "s:x", forged, "u:mallory");
        let mut var = Umem::new();
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &session,
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/pwn", b"owned".to_vec()),
        );
        // Not host-rooted → refused, nothing persisted.
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }

    /// A presenter who is not the subject the token is sealed to gets nothing —
    /// a stolen/leaked token is inert at the bridge.
    #[test]
    fn a_leaked_token_presented_by_a_non_owner_is_refused() {
        let host = host();
        let grain = "cell:grain1";
        // The host mints a cap sealed to alice; mallory steals the token.
        let token = host
            .mint_grain_cap(grain, "u:alice", &["view", "edit"], None)
            .encode();
        let session = Session::presenting("u:mallory", "mallory", "s:y", token, "u:mallory");
        let mut var = Umem::new();
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &session,
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::get("/secret"),
        );
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }

    #[test]
    fn grain_state_persists_in_the_cell_data_root() {
        let host = host();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        let empty_root = var.commit();
        let served = HttpBridge::serve(
            &NotesApp,
            grain,
            &editor_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &HttpRequest::post("/doc", b"v1".to_vec()),
        );
        // The write moved the committed data_root (the witnessed state change).
        assert_ne!(served.new_data_root, empty_root);

        // Simulate sleep→wake: a fresh umem restored from the same contents commits
        // to the same root, and the note is still there.
        let mut restored = var.clone();
        assert_eq!(restored.commit(), served.new_data_root);
        let read = HttpBridge::serve(
            &NotesApp,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut restored,
            &HttpRequest::get("/doc"),
        );
        assert_eq!(read.response.body, b"v1");
    }

    #[test]
    fn a_grain_with_no_outbound_cap_cannot_egress() {
        use crate::net::NetworkPolicy;
        // L2/L7: the bridge is the only egress path, and a confined grain has no cap.
        let policy = NetworkPolicy::confined();
        assert!(!HttpBridge::egress(&policy, "evil.example.com", 443).is_allowed());
        assert!(!HttpBridge::egress(&policy, "169.254.169.254", 80).is_allowed());
    }

    #[test]
    fn egress_is_allowed_only_through_a_granted_cap() {
        use crate::net::{NetworkPolicy, OutboundCap};
        let mut policy = NetworkPolicy::confined();
        policy.grant_outbound(OutboundCap::to("api.weather.test", 443));
        // The granted service is reachable through the bridge...
        assert!(HttpBridge::egress(&policy, "api.weather.test", 443).is_allowed());
        // ...but nothing else is.
        assert!(!HttpBridge::egress(&policy, "evil.example.com", 443).is_allowed());
    }

    #[test]
    fn a_storage_bomb_is_refused_and_rolled_back() {
        use crate::limits::ResourceLease;
        let host = host();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        // A lease that funds only 16 bytes of /var.
        let mut lease = ResourceLease::bounded(u64::MAX, u64::MAX, u64::MAX, 16);
        // A hostile grain tries to write 1 KiB — over its storage quota.
        let big = vec![0u8; 1024];
        let served = HttpBridge::serve_bounded(
            &NotesApp,
            grain,
            &editor_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &mut lease,
            &HttpRequest::post("/huge", big),
        );
        // Refused (507) and nothing persisted — the host disk is protected.
        assert_eq!(served.response.status, 507);
        assert!(var.is_empty());
        assert_eq!(lease.storage_bytes_now(), 0);
    }

    #[test]
    fn a_within_quota_write_through_serve_bounded_persists() {
        use crate::limits::ResourceLease;
        let host = host();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        let mut lease = ResourceLease::bounded(u64::MAX, u64::MAX, u64::MAX, 4096);
        let served = HttpBridge::serve_bounded(
            &NotesApp,
            grain,
            &editor_session(&host, grain),
            &host.public(),
            &declared(),
            1000,
            &mut var,
            &mut lease,
            &HttpRequest::post("/ok", b"small".to_vec()),
        );
        assert_eq!(served.response.status, 200);
        assert!(!var.is_empty());
    }

    /// A `deos-view` grain-run card with an all-`Done` pipeline (terminal receipt present),
    /// so its rendered HTML carries the distinctive "checks green" gate line + the title.
    fn sample_card() -> CardGrainWorkload {
        use deos_view::{GrainRun, LeaseStatus, LeaseView, StepStatus, StepView};
        let run = GrainRun {
            title: "verify breadstuffs".to_string(),
            lease: LeaseView {
                host: "grain-host-7".to_string(),
                metered: 512,
                budget: 1000,
                status: LeaseStatus::Active,
            },
            pipeline: vec![
                StepView {
                    name: "fetch".to_string(),
                    status: StepStatus::Done,
                    receipt: Some("a1b2c3".to_string()),
                },
                StepView {
                    name: "build".to_string(),
                    status: StepStatus::Done,
                    receipt: Some("d4e5f6".to_string()),
                },
                StepView {
                    name: "report".to_string(),
                    status: StepStatus::Done,
                    receipt: Some("aabbcc".to_string()),
                },
            ],
            bounty: None,
        };
        CardGrainWorkload::new("my CI run — dregg.works", "/", run)
    }

    /// THE CLOUD-SERVING WELD, both poles. A hosted grain serves its own `deos-view` card
    /// over the WebSession/HTTP surface — cap-gated (the powerbox cap) and witnessed (the
    /// committed `data_root` is the commitment of exactly the served bytes).
    #[test]
    fn a_hosted_grain_serves_its_deos_view_card_cap_gated_and_witnessed() {
        let host = host();
        let grain = "cell:card-grain";
        let card = sample_card();
        let declared = vec!["view".to_string()];

        // ── POLE 1: WITH the powerbox cap (a `view` grant for THIS grain) → the card is
        //    served (200) AND the returned data_root witnesses the served bytes. ──
        let mut var = Umem::new();
        let empty_root = var.commit();
        let served = HttpBridge::serve(
            &card,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut var,
            &HttpRequest::get("/"),
        );
        assert_eq!(served.response.status, 200, "the card is served");
        let body = String::from_utf8(served.response.body.clone()).unwrap();
        // The SAME card content the native cockpit paints, now in the served HTML.
        assert!(body.starts_with("<!doctype html>"), "a full HTML document");
        assert!(
            body.contains("my CI run — dregg.works"),
            "the card's page title is served"
        );
        assert!(
            body.contains("checks green"),
            "the derived CI-gate line paints in the served card"
        );
        assert!(
            body.contains("verify breadstuffs"),
            "the run title paints in the served card"
        );

        // WITNESSED: the committed data_root moved off empty, and a light client that
        // re-hashes the served bytes (put them in a fresh umem at the known key, commit)
        // re-derives the SAME root — the host cannot serve one card and commit another.
        assert_ne!(
            served.new_data_root, empty_root,
            "the serve committed state"
        );
        let mut light_client = Umem::new();
        light_client.put(card.key(), served.response.body.clone());
        assert_eq!(
            light_client.commit(),
            served.new_data_root,
            "re-hashing the served bytes reproduces the committed data_root (witnessed)"
        );
        // TAMPER-EVIDENT: flip one served byte → a different root (the commitment binds).
        let mut tampered = served.response.body.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 0x01;
        let mut forger = Umem::new();
        forger.put(card.key(), tampered);
        assert_ne!(
            forger.commit(),
            served.new_data_root,
            "a tampered card cannot match the committed root"
        );

        // ── POLE 2: with EMPTY permissions (no powerbox cap for this grain — the session
        //    holds a genuine `view` cap for a DIFFERENT grain, so it confers nothing here)
        //    → 403 and the card is NOT served (nothing materialized into /var). ──
        let mut var2 = Umem::new();
        let no_cap = HttpBridge::serve(
            &card,
            grain,
            &viewer_session(&host, "cell:OTHER-grain"),
            &host.public(),
            &declared,
            1000,
            &mut var2,
            &HttpRequest::get("/"),
        );
        assert_eq!(no_cap.response, HttpResponse::forbidden(), "no cap → 403");
        assert!(
            var2.is_empty(),
            "the card was not served — nothing witnessed"
        );
    }

    /// A deterministic grain-OWNER signing key. In a real deployment this is the owner's
    /// registered identity key (the `subject` the webauth rail seals grain caps to), NOT a
    /// key the serving host holds.
    fn owner_key() -> SigningKey {
        SigningKey::from_bytes(&[77u8; 32])
    }

    /// **THE TRUSTLESS-SERVE WELD — the property "the host cannot tamper with what it
    /// serves" made TRUE, at all three poles.** The old witnessed check re-hashed the whole
    /// (single-entry) `/var` and only flipped a byte within a self-served root — it never
    /// modeled a host swapping card+root together, nor a stateful `/var`. These do.
    #[test]
    fn a_served_card_is_authentic_only_against_an_independent_owner_key_and_inclusion_proof() {
        let host = host();
        let grain = "cell:card-grain";
        let card = sample_card();
        let declared = vec!["view".to_string()];
        let owner = owner_key();
        // The visitor obtains the owner's pubkey from an INDEPENDENT channel (the cell's
        // ledger commitment), never from the serving host's response.
        let owner_pub = owner.verifying_key();

        // ── POLE (i): HONEST serve into a NON-DEGENERATE /var. The owner co-signs the
        //    committed root; the bridge emits the card's inclusion proof. The visitor —
        //    holding only the owner pubkey (independent), the served card, and the bundle —
        //    verifies BOTH the owner-attestation over the root AND the card as the leaf
        //    under it. Accepted. ──
        let mut var = Umem::new();
        // Pre-existing grain state: this is a REAL stateful /var, not the empty-umem crutch.
        var.put("notes/a", b"alpha".to_vec());
        var.put("notes/b", b"beta".to_vec());
        var.put("prefs/theme", b"dark".to_vec());
        let attested = HttpBridge::serve_attested(
            &card,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut var,
            &HttpRequest::get("/"),
            &owner,
            Some(&card.key()),
        );
        assert_eq!(attested.response.status, 200, "the card is served");
        let card_bytes = attested.response.body.clone();
        // The whole-heap root is NOT the single-leaf root — the card is one leaf among four.
        let mut lone = Umem::new();
        lone.put(card.key(), card_bytes.clone());
        assert_ne!(
            lone.commit(),
            attested.new_data_root,
            "a real stateful /var: the served root is over the whole heap, not one leaf"
        );
        // THE VISITOR'S CHECK — owner-attestation ∧ inclusion, against the independent key.
        assert!(
            attested.witnessed_authentic(&owner_pub, &card_bytes),
            "honest serve: owner signed the root AND the card is the leaf under it → authentic"
        );
        // The inclusion proof also checks in isolation (host-state-free), against the
        // whole-heap root — the visitor never needs notes/*, prefs/* to verify the card.
        assert!(crate::cell::verify_inclusion(
            &attested.new_data_root,
            &card.key(),
            &card_bytes,
            attested.inclusion.as_ref().unwrap(),
        ));

        // ── POLE (ii): TAMPER — a HOSTILE host serves a fabricated card `Y` and commits a
        //    matching `root(Y)`, self-consistent under a re-hash. But it CANNOT produce a
        //    valid OWNER attestation over `root(Y)` — it lacks the owner's key — so it signs
        //    under its OWN key. The visitor verifies against the owner pubkey → the
        //    owner-attestation check FAILS → tamper CAUGHT. This is the pole the old test
        //    missed. ──
        struct TamperCard;
        impl GrainWorkload for TamperCard {
            fn serve(&self, _req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
                // The host renders and commits a DIFFERENT card than the owner's.
                let forged = b"<!doctype html><title>evil</title>attacker-controlled".to_vec();
                var.put("card/", forged.clone());
                HttpResponse::ok(forged)
            }
        }
        // The attacker's key — NOT the owner's. This is all a hostile host can sign with.
        let attacker = SigningKey::from_bytes(&[201u8; 32]);
        let mut evil_var = Umem::new();
        let tampered = HttpBridge::serve_attested(
            &TamperCard,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut evil_var,
            &HttpRequest::get("/"),
            &attacker, // the host has no owner key
            Some("card/"),
        );
        let evil_bytes = tampered.response.body.clone();
        // The tamper is INTERNALLY self-consistent: re-hashing Y reproduces root(Y), and the
        // attacker's own inclusion proof folds to root(Y). A visitor that trusted the host's
        // own attestation would be fooled — which is exactly why it must not.
        assert!(crate::cell::verify_inclusion(
            &tampered.new_data_root,
            "card/",
            &evil_bytes,
            tampered.inclusion.as_ref().unwrap(),
        ));
        assert!(
            tampered.attestation.verify(&attacker.verifying_key()),
            "the tamper is self-consistent under the ATTACKER's own key"
        );
        // But against the OWNER's independent key it collapses: the owner never signed
        // root(Y), and the attacker cannot forge that signature.
        assert!(
            !tampered.attestation.verify(&owner_pub),
            "the owner did not attest root(Y) — the host cannot forge it"
        );
        assert!(
            !tampered.witnessed_authentic(&owner_pub, &evil_bytes),
            "TAMPER CAUGHT: card+root swapped together, but no valid OWNER attestation over root(Y)"
        );

        // ── POLE (iii): the inclusion proof is load-bearing over a NON-DEGENERATE /var — a
        //    wrong card at the card key does not verify under the honest attested root, even
        //    though the owner-attestation itself checks (the two teeth are independent). ──
        let mut wrong = card_bytes.clone();
        let last = wrong.len() - 1;
        wrong[last] ^= 0x01;
        assert!(
            attested.attestation.verify(&owner_pub),
            "the honest root is genuinely owner-attested",
        );
        assert!(
            !attested.witnessed_authentic(&owner_pub, &wrong),
            "a card that is not the committed leaf fails the inclusion tooth under the real root"
        );
    }

    /// **THE LEDGER-ANCHORED SERVE WELD — authenticity chained to the FEDERATION's stored
    /// HEAP-ROOT (the real dregg scheme), not the serving host's response.** The prior weld
    /// anchored on the owner key but still let the visitor take the ROOT from the host. This
    /// closes that: the visitor takes the cell's committed **heap-root** from the LEDGER
    /// ([`grain_cell_commitment`] of the last honest `/var` = the encoded
    /// `dregg_circuit::heap_root::compute_heap_root`, the `heap_root` the whole-cell
    /// `state_commitment` absorbs), as a **hex** wire value it decodes — so even a host that
    /// serves a self-consistent card+root+attestation is caught. The named remaining seam is
    /// the federation WRITE of the heap-root as a distinct fetchable value; the SCHEME here
    /// is the real one the ledger carries (a Poseidon2/felt heap-root, not sha256).
    #[test]
    fn a_served_card_is_authentic_only_against_the_ledgers_committed_root() {
        use crate::grain::grain_cell_commitment;
        let host = host();
        let grain = "cell:card-grain";
        let card = sample_card();
        let declared = vec!["view".to_string()];
        let owner = owner_key();
        // The visitor obtains the owner pubkey from the cell record (independent channel).
        let owner_pub = owner.verifying_key();

        // ── The OWNER's last honest commit: serve the real card into a stateful /var and
        //    commit root(X). The federation carries grain_cell_commitment(/var) — the cell's
        //    heap-root, the `heap_root` the whole-cell state_commitment absorbs — keyed by the
        //    grain's cell id (the named seam: it must be PUBLISHED as a distinct fetchable
        //    value). The visitor reads THIS (as hex), never the serving host. ──
        let mut var = Umem::new();
        var.put("notes/a", b"alpha".to_vec());
        var.put("prefs/theme", b"dark".to_vec());
        let honest = HttpBridge::serve_attested(
            &card,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut var,
            &HttpRequest::get("/"),
            &owner,
            Some(&card.key()),
        );
        assert_eq!(honest.response.status, 200);
        let card_bytes = honest.response.body.clone();

        // ── POLE (iii) — THE BINDING: the value the federation carries == the /var HEAP-ROOT
        //    (the real dregg scheme) the inclusion proofs fold to. grain_cell_commitment is
        //    the encoded dregg heap-root felt, and its wire form is the DataRoot the honest
        //    serve committed. It is a GENUINE cell heap-root — the dregg_circuit heap-root
        //    primitive dregg_cell::compute_heap_root wraps — NOT a bespoke sha256 tree. ──
        let ledger_root = grain_cell_commitment(&var);
        assert_eq!(
            DataRoot::from_root_bytes(ledger_root),
            honest.new_data_root,
            "the ledger's committed heap-root is the same root the served card is a leaf under"
        );
        assert_eq!(
            ledger_root,
            var.commit_root_bytes(),
            "grain_cell_commitment IS the /var heap-root inclusion proofs are checked against"
        );
        // The SHAPE: it is the real 8-felt Poseidon2 heap-root, not sha256 and not the
        // retired 1-felt lane-0 projection — the encoded
        // dregg_circuit::heap_root::compute_canonical_heap_root_8 over the /var LANE leaves
        // (the exact primitive dregg_cell::state::compute_heap_root wraps).
        assert_eq!(
            ledger_root,
            dregg_cell::commitment::digest8_to_bytes32(
                dregg_circuit::heap_root::compute_canonical_heap_root_8(var.heap_leaves()).limbs()
            ),
            "grain_cell_commitment == the real 8-felt dregg heap-root over the /var lane leaves"
        );

        // The federation returns the heap-root as HEX (`hex_encode`, like `state_commitment`);
        // the visitor DECODES it (the codec fix) — round-trips to the same raw bytes.
        let ledger_hex = heap_root_hex(ledger_root);
        assert_eq!(
            ledger_hex,
            data_encoding::HEXLOWER.encode(&ledger_root),
            "the ledger heap-root wire form is lowercase hex, matching node/src/api.rs"
        );

        // ── POLE (i) — HONEST: the visitor reads the LEDGER heap-root (hex, decoded) + owner
        //    key (both independent), and verifies the served card is a leaf under the LEDGER
        //    heap-root. Accepted. ──
        assert!(
            verify_served_against_ledger(
                &card_bytes,
                &card.key(),
                honest.inclusion.as_ref().unwrap(),
                &ledger_hex,
                &owner_pub,
                &honest.attestation,
            ),
            "honest serve: card is the committed leaf under the ledger's heap-root → authentic"
        );
        assert!(
            honest.verify_against_ledger(&ledger_hex, &owner_pub, &card_bytes),
            "same check via the AttestedServed convenience method"
        );
        // A malformed hex ledger value authenticates nothing (the codec rejects it).
        assert!(
            !honest.verify_against_ledger("not-hex!!", &owner_pub, &card_bytes),
            "a malformed hex ledger heap-root is rejected"
        );

        // ── POLE (ii) — TAMPER: a hostile host serves a DIFFERENT card Y, commits root(Y),
        //    and bundles its OWN self-consistent attestation. Grant the host even the OWNER
        //    key (the strongest case) — so `witnessed_authentic` against the HOST's served
        //    root is FOOLED — yet against the LEDGER's committed root(X) the serve collapses:
        //    Y is not a leaf under root(X). CAUGHT. This is the pole owner-attestation-alone
        //    cannot close. ──
        struct TamperCard;
        impl GrainWorkload for TamperCard {
            fn serve(&self, _req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
                let forged = b"<!doctype html><title>evil</title>attacker-controlled".to_vec();
                var.put("card/", forged.clone());
                HttpResponse::ok(forged)
            }
        }
        let mut evil_var = Umem::new();
        let tampered = HttpBridge::serve_attested(
            &TamperCard,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut evil_var,
            &HttpRequest::get("/"),
            &owner, // strong adversary: even holding the owner key
            Some("card/"),
        );
        let evil_bytes = tampered.response.body.clone();
        // Against the HOST's OWN served root, the tamper is self-consistent — the
        // owner-attestation-alone check (which trusts self.new_data_root) is FOOLED. Exactly
        // why chaining to the host's served root does not suffice.
        assert!(
            tampered.witnessed_authentic(&owner_pub, &evil_bytes),
            "against the HOST's own served root the tamper looks authentic (the unclosed pole)"
        );
        // But against the LEDGER's committed root(X) it collapses: Y is not a leaf under X.
        assert!(
            !tampered.verify_against_ledger(&ledger_hex, &owner_pub, &evil_bytes),
            "TAMPER CAUGHT: the served card is not a leaf under the LEDGER's committed heap-root"
        );
        // The inclusion tooth in isolation is decisive: even handed the GENUINE owner
        // attestation over the ledger root (so the attestation conjunct passes), the tampered
        // card+proof fail inclusion under root(X).
        assert!(
            honest.attestation.data_root == DataRoot::from_root_bytes(ledger_root),
            "the honest attestation is over exactly the ledger root",
        );
        assert!(
            !verify_served_against_ledger(
                &evil_bytes,
                "card/",
                tampered.inclusion.as_ref().unwrap(),
                &ledger_hex,
                &owner_pub,
                &honest.attestation, // a genuine owner attestation over the ledger heap-root
            ),
            "the inclusion tooth alone rejects a card that is not a leaf under the ledger heap-root"
        );

        // A wrong card at the RIGHT key likewise fails inclusion under the ledger root.
        let mut wrong = card_bytes.clone();
        let last = wrong.len() - 1;
        wrong[last] ^= 0x01;
        assert!(
            !verify_served_against_ledger(
                &wrong,
                &card.key(),
                honest.inclusion.as_ref().unwrap(),
                &ledger_hex,
                &owner_pub,
                &honest.attestation,
            ),
            "a card that is not the committed leaf fails the inclusion tooth under the ledger heap-root"
        );
    }

    /// **THE FEDERATION WRITE-PATH WELD — the grain PUBLISHES its heap-root to the ledger,
    /// and a visitor SOURCES the verification root from the federation response, not the
    /// serving host.** The prior ledger test assumed the committed heap-root was already
    /// present; this closes the last-named seam by actually producing the WRITE
    /// ([`crate::grain::publish_grain_root`] → the exact owner-signed `/cells/update-commitment`
    /// body node accepts) and the READ ([`fetch_ledger_root`] → the root pulled back out of a
    /// `GET /api/cell/{id}` response), and shows they are consistent end to end.
    #[test]
    fn the_published_grain_root_round_trips_through_the_federation_and_anchors_the_serve() {
        use crate::grain::{
            grain_cell_commitment, publish_grain_root, verify_update_commitment_signature,
        };
        let host = host();
        let grain = "cell:published-grain";
        let card = sample_card();
        let declared = vec!["view".to_string()];

        // The grain OWNER's registered identity key. Under node's sovereign-cell convention
        // the 32-byte cell id IS this key's public half (node verifies the update signature
        // against cell_id-as-pubkey), so that is the federation cell id we publish under.
        let owner = owner_key();
        let owner_pub = owner.verifying_key();
        let fed_cell_id = owner_pub.to_bytes();

        // ── The OWNER's honest checkpoint: serve the real card into a stateful /var,
        //    committing the grain's heap-root. This is the state the owner will publish. ──
        let mut var = Umem::new();
        var.put("notes/a", b"alpha".to_vec());
        let honest = HttpBridge::serve_attested(
            &card,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut var,
            &HttpRequest::get("/"),
            &owner,
            Some(&card.key()),
        );
        assert_eq!(honest.response.status, 200);
        let card_bytes = honest.response.body.clone();
        let published_root = grain_cell_commitment(&var);

        // ── POLE (ii) — OWNER-SIGNED WRITE: build the /cells/update-commitment body. The
        //    new_commitment is the published heap-root; the signature is over
        //    (cell_id ‖ old ‖ new), verifiable against the owner key — node would accept it. ──
        let req = publish_grain_root(&fed_cell_id, &var, &owner, [0u8; 32]);
        assert_eq!(
            req.new_commitment,
            heap_root_hex(published_root),
            "the published new_commitment is the grain's heap-root, hex as node returns commitments"
        );
        assert!(
            verify_update_commitment_signature(&req),
            "owner-signed over (cell_id ‖ old ‖ new), verifies against cell_id-as-pubkey — node accepts"
        );
        // A wrong signing key → rejected (its signature does not verify against cell_id-as-pubkey).
        let imposter = SigningKey::from_bytes(&[0x99u8; 32]);
        let forged = publish_grain_root(&fed_cell_id, &var, &imposter, [0u8; 32]);
        assert!(
            !verify_update_commitment_signature(&forged),
            "a request signed by a non-owner key is rejected — cell_id-as-pubkey does not verify it"
        );
        // A mutated commitment under a genuine signature is likewise rejected.
        let mut tampered_req = req.clone();
        tampered_req.new_commitment = heap_root_hex([0xabu8; 32]);
        assert!(
            !verify_update_commitment_signature(&tampered_req),
            "mutating the committed value breaks the owner signature — node rejects it"
        );

        // ── POLE (i) — READ back through the FEDERATION: model the GET /api/cell/{id}
        //    response node returns AFTER accepting the update — the cell now carries
        //    new_commitment as its committed value. The visitor parses it with
        //    fetch_ledger_root, sourcing the root from the FEDERATION, not the serving host. ──
        let cell_detail_json = serde_json::json!({
            "id": data_encoding::HEXLOWER.encode(&fed_cell_id),
            "found": true,
            "state_commitment": req.new_commitment,
            // extra node fields the visitor's parser ignores:
            "balance": 0, "nonce": 1, "program_kind": "None"
        })
        .to_string();
        let fetched = fetch_ledger_root(&cell_detail_json).expect("ledger root parses");
        assert_eq!(
            fetched, published_root,
            "ROUND-TRIP: fetch_ledger_root(response_after(publish_grain_root(R))) == R"
        );
        // A not-found / malformed / no-commitment response yields no root.
        assert_eq!(
            fetch_ledger_root(r#"{"found":false}"#),
            Err(crate::bridge::LedgerFetchError::NotFound)
        );

        // ── POLE (i cont.) — the honest served card verifies against the FEDERATION-sourced
        //    root (never the serving host's asserted root). ──
        let ledger_hex = heap_root_hex(fetched);
        assert!(
            verify_served_against_ledger(
                &card_bytes,
                &card.key(),
                honest.inclusion.as_ref().unwrap(),
                &ledger_hex,
                &owner_pub,
                &honest.attestation,
            ),
            "honest serve anchored on the PUBLISHED (federation) root → authentic"
        );
        assert!(
            honest.verify_against_ledger(&ledger_hex, &owner_pub, &card_bytes),
            "same, via the AttestedServed convenience method"
        );

        // ── POLE (iii) — TAMPER END-TO-END: a hostile host serves a DIFFERENT card, commits
        //    its own root, and self-attests (grant it even the owner key). Against the
        //    PUBLISHED ledger root the serve collapses — the forged card is not a leaf under
        //    it — even though the host self-attests. ──
        struct TamperCard;
        impl GrainWorkload for TamperCard {
            fn serve(&self, _req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
                let forged = b"<!doctype html><title>evil</title>attacker".to_vec();
                var.put("card/", forged.clone());
                HttpResponse::ok(forged)
            }
        }
        let mut evil_var = Umem::new();
        let tampered = HttpBridge::serve_attested(
            &TamperCard,
            grain,
            &viewer_session(&host, grain),
            &host.public(),
            &declared,
            1000,
            &mut evil_var,
            &HttpRequest::get("/"),
            &owner, // strongest adversary: even holding the owner key
            Some("card/"),
        );
        let evil_bytes = tampered.response.body.clone();
        // Self-consistent against the HOST's own served root (the pole the ledger closes)...
        assert!(
            tampered.witnessed_authentic(&owner_pub, &evil_bytes),
            "against its own served root the tamper looks authentic (the unclosed pole)"
        );
        // ...but rejected against the PUBLISHED ledger root sourced from the federation.
        assert!(
            !tampered.verify_against_ledger(&ledger_hex, &owner_pub, &evil_bytes),
            "TAMPER CAUGHT END-TO-END: the served card is not a leaf under the PUBLISHED ledger root"
        );
    }
}
