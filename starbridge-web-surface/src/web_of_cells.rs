//! The `dregg://` web of cells — a link is a capability, a fetch is a verified
//! attested cross-cell read.
//!
//! `docs/desktop-os-research/DISTRIBUTED-SERVO-FACETS.md` Facet 1, in one
//! paragraph: the open web's link is a **location** (`https://host/path`) — you
//! trust DNS to find the host, TLS to authenticate the host, and then you trust
//! *whatever bytes the host hands back*. A `dregg://<cell>` link is not a location
//! but a **capability into a specific cell**; resolving it is not "GET the path"
//! but a **verified cross-cell read** that returns **attested content** — the
//! bytes are content-addressed (`content_hash == blake3(bytes)`) AND accompanied
//! by a receipt + a quorum-signed [`dregg_types::AttestedRoot`] the client checks.
//! So you verify *the page is the page the origin committed* — third-party-
//! checkable, from any source — not "the bytes a TLS-authenticated server chose to
//! send this time."
//!
//! ## What is real here
//!
//! - The fetch reads the served bytes' **content commitment out of the surface
//!   cell's real state** (slot 0 of the [`dregg_cell::Cell`] in a real
//!   [`dregg_cell::Ledger`]) — a genuine cell read, not a mock GET. The cell IS
//!   the origin; its committed `content_hash` is what binds the bytes.
//! - The attestation is the **genuine** [`dregg_types::AttestedRoot`] +
//!   [`dregg_types::merkle_root_of_receipt_hashes`]: the serve leaves a receipt,
//!   the receipt hashes into the federation's receipt-stream Merkle root, and the
//!   client verifies via the REAL [`AttestedRoot::verify_receipt_stream`]. We
//!   build NO bespoke attestation.
//! - The **trusted-path origin chrome** ([`OriginChrome`]) is derived from the
//!   LEDGER (the cell id + its committed URL + its rights lineage), never from the
//!   fetched content — dregg's structural answer to browser-chrome phishing
//!   (`DISTRIBUTED-SERVO-FACETS.md §1.3`).
//!
//! ## The seam to the full executor turn
//!
//! `DISTRIBUTED-SERVO-FACETS.md §2.2`: for the attestation to bind, the origin
//! cell's serve-turn must write the content hash into committed state — a
//! cell-program convention (the `ServedResourceCell` template). Here the serve is
//! modeled as a verified cell-read against a real ledger whose surface cell
//! carries that commitment in slot 0; wiring the serve as a full `Effect`-bearing
//! `TurnExecutor` turn (so the receipt is the executor's own, chained on the
//! per-agent receipt chain) is the named follow-up reported in the BUILD STATUS
//! note. The verification chain (content → commitment → receipt → receipt-stream
//! root → quorum-signed AttestedRoot) is the genuine shape either way.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_types::{merkle_root_of_receipt_hashes, AttestedRoot, CellId, PublicKey, SigningKey};

/// A parsed `dregg://<cell>` link — a sturdy ref into a cell.
///
/// `DISTRIBUTED-SERVO-FACETS.md §1`: "a link is a bearer cap into a specific cell
/// on a specific federation." This is the minimal form this crate resolves: the
/// `cell` is the origin (its content-addressed [`CellId`] — already unforgeable).
/// The full `dregg://<fed>/<cell>/<swiss>` shape (federation + attenuating swiss
/// number) lives in `captp/src/uri.rs::DreggUri`; this crate models the
/// resolve+attest half against a local ledger and names that as the seam.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DreggUri {
    /// The origin cell this link denotes.
    pub cell: CellId,
}

impl DreggUri {
    /// Construct a `dregg://` ref to `cell`.
    pub fn new(cell: CellId) -> Self {
        DreggUri { cell }
    }

    /// Render as a `dregg://<hex-cell>` string (the link as it appears in an
    /// address bar). The hex is the content-addressed cell id — the address IS
    /// the access grant, and the identity.
    pub fn to_uri_string(&self) -> String {
        let mut s = String::from("dregg://");
        for b in self.cell.0.iter() {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }
}

/// The attested-content envelope a `dregg://` fetch returns — the one new wire
/// object, every field a genuine primitive (`DISTRIBUTED-SERVO-FACETS.md §2.1`).
///
/// The binding that makes it "the page the origin committed": the served bytes'
/// `content_hash` is a field of the origin cell's committed state, the serve's
/// `receipt_hash` commits that, and the `receipt_hash` is a leaf of the
/// federation's quorum-signed `attested_root.receipt_stream_root`. Verifying the
/// chain `content → content_hash → receipt → receipt_stream_root → quorum-signed
/// AttestedRoot` proves the origin cell published exactly these bytes — checkable
/// by a third party who was never on the channel (unlike TLS).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestedResource {
    /// The page body.
    pub content_bytes: Vec<u8>,
    /// Content-addressing: `blake3(content_bytes)`. The body is self-certifying.
    pub content_hash: [u8; 32],
    /// The hash of the serve-receipt that committed this content — a leaf of the
    /// federation's receipt-stream Merkle tree. Binds `content_hash` to a
    /// specific verified turn.
    pub receipt_hash: [u8; 32],
    /// The genuine federation attestation: the quorum-signed,
    /// receipt-stream-bound root. The client recomputes the receipt-stream root
    /// over the served receipt set and checks it equals `attested_root
    /// .receipt_stream_root` via [`AttestedRoot::verify_receipt_stream`].
    pub attested_root: AttestedRoot,
    /// The canonical-order receipt-hash set the federation committed (the leaves
    /// of `attested_root.receipt_stream_root`). Carried so the client can run the
    /// real `verify_receipt_stream` reconstruction. In production this is folded
    /// from the light-client's view of the cell's turn chain; here it is the
    /// served receipt set.
    pub receipt_set: Vec<[u8; 32]>,
}

impl AttestedResource {
    /// **CLIENT-SIDE verification** — run before a byte reaches the renderer.
    ///
    /// `DISTRIBUTED-SERVO-FACETS.md §2 hop [6]`, each check a genuine primitive:
    ///
    /// 1. `content_hash == blake3(content_bytes)` — content-addressed;
    /// 2. `receipt_hash` is one of the committed `receipt_set` — the receipt
    ///    that served THIS content is in the attested stream;
    /// 3. `attested_root.verify_receipt_stream(receipt_set)` — the federation's
    ///    quorum-signed root binds exactly this receipt set (the REAL
    ///    receipt-stream Merkle reconstruction);
    /// 4. `attested_root.has_quorum()` — the structural quorum check (count ≥
    ///    threshold / QC size). (Full Ed25519/BLS crypto verification of the
    ///    signatures is a higher layer per the `AttestedRoot` doc; this is the
    ///    structural gate this crate runs.)
    ///
    /// Returns `Ok(())` only when ALL hold; otherwise the specific
    /// [`FetchError`] — on which the caller renders a visible "dregg: unattested
    /// content" body and NEVER the bytes.
    ///
    /// **Note (red-team LC-1):** this keyless path is the STRUCTURAL gate. It now
    /// refuses a degenerate `threshold:0` / empty-signature "quorum" (which the bare
    /// `has_quorum()` count accepted), but it still cannot tell a fabricated root by
    /// attacker-chosen keys from the federation's. A client that holds the committee
    /// MUST use [`verify_anchored`](Self::verify_anchored) — the committee-anchored
    /// cryptographic gate — as its acceptance check.
    pub fn verify(&self) -> Result<(), FetchError> {
        self.verify_content_chain()?;
        // (4) the structural quorum gate — but a degenerate `threshold:0` /
        // empty-signature root is NEVER acceptance (LC-1: `threshold:0` passed the
        // bare count check). A real attestation carries either a BLS QC or at least
        // a non-empty Ed25519 quorum meeting a positive threshold.
        let ar = &self.attested_root;
        if ar.threshold_qc.is_none() && (ar.threshold == 0 || ar.quorum_signatures.is_empty()) {
            return Err(FetchError::NoQuorum);
        }
        if !ar.has_quorum() {
            return Err(FetchError::NoQuorum);
        }
        Ok(())
    }

    /// **COMMITTEE-ANCHORED CLIENT VERIFICATION (the LC-1 acceptance gate).** Runs
    /// the content chain (steps 1–3 of [`verify`](Self::verify)) and then gates on the
    /// federation's **cryptographic** quorum against the client's TRUSTED `committee`
    /// — `attested_root.is_valid(committee)` — NOT a count. The committee is the set
    /// of validator public keys the client holds from genesis/checkpoint config
    /// (e.g. [`WebOfCells::committee`]); it is NEVER read from the fetched resource.
    ///
    /// This is the check a `dregg://` consumer must run before a byte reaches the
    /// renderer. A malicious content server that fabricates an `AttestedRoot` with
    /// its own keys, or a `threshold:0` root, is REFUSED here: the forged signatures
    /// do not verify under the committee keys, and a threshold/QC-less root carries
    /// no quorum.
    pub fn verify_anchored(&self, committee: &[PublicKey]) -> Result<(), FetchError> {
        self.verify_content_chain()?;
        // Unanchored clients accept nothing — a count-only / fabricated quorum is
        // never acceptance (LC-1).
        if committee.is_empty() {
            return Err(FetchError::Unattested);
        }
        let ar = &self.attested_root;
        // This path requires a real Ed25519 committee quorum. A BLS `threshold_qc`
        // is only STRUCTURALLY checked by `is_valid` (a separate, known MED finding),
        // so refuse a QC-only root here rather than let it bypass the committee gate.
        if ar.threshold_qc.is_some() {
            return Err(FetchError::Unattested);
        }
        if ar.threshold == 0 {
            return Err(FetchError::Unattested);
        }
        // The cryptographic committee gate: every counted signature must verify under
        // a key IN the committee, and the distinct verified signers must meet the
        // threshold (`AttestedRoot::is_valid`).
        if !ar.is_valid(committee) {
            return Err(FetchError::Unattested);
        }
        Ok(())
    }

    /// Steps 1–3 of the verification chain (content-addressing, receipt-in-stream,
    /// receipt-stream root reconstruction) — the part shared by [`verify`](Self::verify)
    /// and [`verify_anchored`](Self::verify_anchored).
    fn verify_content_chain(&self) -> Result<(), FetchError> {
        // (1) content-addressed.
        let recomputed = *blake3::hash(&self.content_bytes).as_bytes();
        if recomputed != self.content_hash {
            return Err(FetchError::ContentHashMismatch);
        }
        // (2) the serve-receipt is in the committed set.
        if !self.receipt_set.contains(&self.receipt_hash) {
            return Err(FetchError::ReceiptNotInStream);
        }
        // (3) the federation's quorum-signed root binds exactly this receipt set
        //     (the REAL receipt-stream Merkle reconstruction).
        if !self.attested_root.verify_receipt_stream(&self.receipt_set) {
            return Err(FetchError::ReceiptStreamRootMismatch);
        }
        Ok(())
    }
}

/// What can go wrong resolving / verifying a `dregg://` fetch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FetchError {
    /// No cell at that `dregg://` ref in the ledger (a dead link).
    OriginNotFound,
    /// The origin cell carries no committed content (slot 0 is empty) — there is
    /// nothing to serve.
    NoContentCommitted,
    /// `blake3(content_bytes) != content_hash` — the bytes were tampered.
    ContentHashMismatch,
    /// The served content's commitment does not match the origin cell's committed
    /// `content_hash` — the node served bytes the origin never committed.
    ContentDoesNotMatchCommitment,
    /// The serve-receipt is not a leaf of the attested receipt stream.
    ReceiptNotInStream,
    /// The recomputed receipt-stream root ≠ the root the federation signed.
    ReceiptStreamRootMismatch,
    /// The attested root does not carry a quorum (count < threshold, or a degenerate
    /// `threshold:0` / empty-signature root).
    NoQuorum,
    /// The attested root is not cryptographically valid against the client's TRUSTED
    /// committee — its quorum signatures do not verify under the committee keys (a
    /// fabricated root by attacker-chosen keys), the committee is empty (unanchored),
    /// or the root carries no real Ed25519 committee quorum. Returned by
    /// [`AttestedResource::verify_anchored`] (red-team LC-1).
    Unattested,
    /// The origin cell's nonce overflowed, so the amend could not produce a
    /// distinct serve-receipt leaf (a silent overwrite is refused — this is the
    /// surface analogue of the kernel's P2-2 replay guard).
    NonceOverflow,
}

/// The trusted-path origin chrome for a `dregg://` page — drawn by the SHELL from
/// the ledger, never the page.
///
/// `DISTRIBUTED-SERVO-FACETS.md §1.3`: the origin badge for a web-of-cells page is
/// *stronger* than a TLS lock — it names the exact object and its attenuation
/// (the cell id, the rights it holds), drawn from the live ledger, in chrome the
/// DOM cannot reach. A page cannot paint a fake `https://yourbank.com 🔒` because
/// every field here is read from cell state, not from the fetched content.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OriginChrome {
    /// The origin cell id (content-addressed, unforgeable) — the exact object the
    /// link denotes, rendered as hex in the badge.
    pub cell: CellId,
    /// The committed URL the origin cell carries (its `notify_url_changed` value,
    /// bound to the cell), if any — what the surface is *actually* at, not what
    /// the page claims.
    pub committed_url: Option<String>,
    /// The rights lineage: the authority the origin cell's content is served
    /// under (e.g. a read-only `Signature` facet vs. an open `None`) — the
    /// structured provenance a flat TLS lock cannot show.
    pub rights: AuthRequired,
    /// Whether the federation finalized the content (the attestation carried a
    /// quorum) — the "finalized" status the badge shows.
    pub finalized: bool,
}

impl OriginChrome {
    /// Render the badge as the shell would draw it (a one-line trusted-path
    /// string). Derived entirely from ledger-read fields — the page contributes
    /// nothing.
    pub fn badge(&self) -> String {
        use std::fmt::Write as _;
        let mut hex = String::with_capacity(8);
        for b in self.cell.0.iter().take(4) {
            let _ = write!(hex, "{b:02x}");
        }
        let url = self
            .committed_url
            .as_deref()
            .unwrap_or("(no committed url)");
        let fin = if self.finalized {
            "finalized"
        } else {
            "UNATTESTED"
        };
        format!("dregg://{hex}… · {url} · rights={:?} · {fin}", self.rights)
    }
}

/// A local web-of-cells: a real [`dregg_cell::Ledger`] of origin cells, each
/// serving content committed in its state, with a federation attestation.
///
/// This is the resolver end of `DISTRIBUTED-SERVO-FACETS.md §2`: it `publish`es a
/// `dregg://` page (commits the content hash into a real surface cell + binds a
/// committed URL), and `fetch`es a `dregg://` ref into an [`AttestedResource`] the
/// client verifies, with the [`OriginChrome`] drawn from the ledger. The ledger
/// is REAL `dregg_cell` state; the attestation is REAL `dregg_types` primitives.
pub struct WebOfCells {
    ledger: Ledger,
    /// A monotone height for the federation's attestation period (each publish
    /// advances it — `finality_round`/`height` is the monotone freshness field
    /// §2.2 names).
    height: u64,
    /// The federation's quorum SIGNING keys (deterministic, derived from a seed).
    /// `attest` signs the real [`AttestedRoot::signing_message`] with each, so the
    /// produced quorum signatures CRYPTOGRAPHICALLY verify against the committee
    /// public keys (`[`Self::committee`]`) — a client that holds the committee can
    /// gate on [`AttestedResource::verify_anchored`] (`is_valid(known_keys)`), not a
    /// count (red-team LC-1).
    quorum_sks: Vec<SigningKey>,
    /// The node-side content byte store: the bytes a serve ships out-of-band,
    /// keyed by the origin cell. They live BESIDE the real ledger (only the
    /// content COMMITMENT is in verified cell state) — exactly as a §2.1 envelope
    /// ships `content_bytes` + a state commitment. `pub(crate)` so the
    /// node-drift adversarial test can simulate a lying node.
    pub(crate) bytes_store: Vec<(CellId, Vec<u8>)>,
    /// The node-side committed-URL store (the trusted-chrome source bound to each
    /// origin cell — the `notify_url_changed` value's stand-in).
    url_store: Vec<(CellId, String)>,
}

/// Slot 0 of a surface cell holds the content commitment (`blake3` of the served
/// bytes) — the `DISTRIBUTED-SERVO-FACETS.md §2.2` convention realized as a real
/// cell-state field (the surface descriptor's content-commitment slot, per
/// `ARCHITECTURES.md`).
const CONTENT_COMMITMENT_SLOT: usize = 0;

impl WebOfCells {
    /// A fresh web-of-cells with an empty ledger and a `threshold`-of-N quorum.
    ///
    /// The quorum signing keys are deterministic (derived from a per-index seed) so
    /// the committee is reproducible across runs, and `attest` produces REAL Ed25519
    /// signatures over the attested root — the client gates on the committee keys
    /// (`is_valid`), never a count.
    pub fn new(quorum_size: usize) -> Self {
        // Deterministic quorum signing keys. A fixed domain-separated seed keeps the
        // committee reproducible while the produced signatures are genuine Ed25519.
        let quorum_sks = (0..quorum_size)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = 0xF0 ^ (i as u8);
                seed[31] = (i as u8).wrapping_mul(31).wrapping_add(7);
                SigningKey::from_bytes(&seed)
            })
            .collect();
        WebOfCells {
            ledger: Ledger::new(),
            height: 0,
            quorum_sks,
            bytes_store: Vec::new(),
            url_store: Vec::new(),
        }
    }

    /// The federation's committee public keys — the trusted validator set a `dregg://`
    /// client holds (from genesis/checkpoint config) and gates acceptance against via
    /// [`AttestedResource::verify_anchored`]. NEVER read from a fetched resource.
    pub fn committee(&self) -> Vec<PublicKey> {
        self.quorum_sks.iter().map(|sk| sk.public_key()).collect()
    }

    /// The federation's current monotone attestation height (the `finality_round` a
    /// fetch attests at; each [`Self::publish`]/[`Self::amend`] advances it). The
    /// `at_root` a versioned snapshot dates itself to — a stable, monotone freshness
    /// field (`DISTRIBUTED-SERVO-FACETS.md §2.2`).
    pub fn height(&self) -> u64 {
        self.height
    }

    /// Seed an origin cell with permissive permissions (so a publish's `set_field`
    /// is authorized), returning its [`CellId`]. The deterministic key derivation
    /// mirrors the firmament's `seed_surface` so origins are addressable by seed.
    fn seed_origin(&mut self, seed: u8) -> CellId {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(11);
        let mut cell = Cell::with_balance(pk, [0u8; 32], 10_000);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let id = cell.id();
        self.ledger.insert_cell(cell).expect("seed origin cell");
        id
    }

    /// **Publish** a `dregg://` page: commit `content`'s hash into a fresh origin
    /// cell's state (slot 0) and bind a `committed_url`, returning the
    /// [`DreggUri`] that denotes it.
    ///
    /// This is the `ServedResourceCell` shape (`§2.2`): the served blob's hash is
    /// recorded in a slot the receipt commits, so the attestation can bind. The
    /// commitment is written into REAL cell state via [`dregg_cell`]'s
    /// `set_field`; the content bytes themselves are held by the node (carried
    /// out-of-band, exactly as a real serve ships bytes + a state commitment).
    pub fn publish(&mut self, seed: u8, content: &[u8], committed_url: &str) -> DreggUri {
        let cell_id = self.seed_origin(seed);
        let content_hash = *blake3::hash(content).as_bytes();

        // Commit the content hash into the origin cell's state (slot 0) — a real
        // cell-state write, the genuine "the origin committed this content".
        let cell = self.ledger.get_mut(&cell_id).expect("just-seeded origin");
        cell.state.set_field(CONTENT_COMMITMENT_SLOT, content_hash);
        // Bind the committed URL to the cell (the trusted-chrome source). We store
        // it in the cell's extended field map keyed by a stable domain tag so the
        // chrome reads it from state, not from the page. (A simple, real
        // cell-state binding; the production path binds libservo's
        // notify_url_changed value the same way.)
        self.bind_url(&cell_id, committed_url);
        // The content bytes live with the node, keyed by the origin cell.
        self.store_bytes(&cell_id, content.to_vec());

        self.height += 1;
        DreggUri::new(cell_id)
    }

    /// **Amend** an already-published `dregg://` page: advance the SAME origin cell's
    /// committed/finalized content to `new_content` (a verified state advance), so a
    /// transclusion that quotes it re-fetches the NEW finalized value at a NEW height.
    ///
    /// This is the "the source finalizes a new height" half of the live quote
    /// (`DISTRIBUTED-SERVO-FACETS.md §2.2`): unlike [`Self::publish`] (which seeds a
    /// FRESH origin cell), `amend` re-commits into the EXISTING cell `uri.cell` —
    /// content commitment (slot 0) updated, nonce bumped (so the serve-receipt is a
    /// DISTINCT leaf), the node byte store re-pointed, and the federation height
    /// advanced (a new attestation period). The `dregg://` ref is UNCHANGED (same
    /// content-addressed cell id) — exactly Nelson's unbreakable link: the citation
    /// still resolves, but to the source's NEW committed value. Returns the advanced
    /// federation height.
    ///
    /// Refuses (`OriginNotFound`) if the ref was never published.
    pub fn amend(&mut self, uri: &DreggUri, new_content: &[u8]) -> Result<u64, FetchError> {
        let new_hash = *blake3::hash(new_content).as_bytes();
        // Advance the EXISTING origin cell's committed state: re-commit the content
        // hash (slot 0) and bump the nonce, so the serve-receipt for the new content
        // is a distinct receipt leaf (a genuine state advance, not a silent overwrite).
        {
            let cell = self
                .ledger
                .get_mut(&uri.cell)
                .ok_or(FetchError::OriginNotFound)?;
            cell.state.set_field(CONTENT_COMMITMENT_SLOT, new_hash);
            if !cell.state.increment_nonce() {
                return Err(FetchError::NonceOverflow);
            }
        }
        // Re-point the node's out-of-band byte store to the new content (keyed by the
        // same origin cell), and advance the federation's attestation height.
        self.replace_bytes(&uri.cell, new_content.to_vec());
        self.height += 1;
        Ok(self.height)
    }

    /// **Fetch** a `dregg://` ref: read the origin cell's committed content
    /// commitment, serve the bytes, and wrap them in an [`AttestedResource`] whose
    /// receipt hashes into a genuine quorum-signed [`AttestedRoot`].
    ///
    /// `DISTRIBUTED-SERVO-FACETS.md §2`: the resolve reads the origin cell out of
    /// the ledger (`enliven`'s local analogue), confirms the served bytes match
    /// the cell's committed `content_hash` (the serve-turn binding), and produces
    /// the attestation the client verifies BEFORE rendering. Returns the envelope
    /// + the [`OriginChrome`] (drawn from the ledger). The caller MUST call
    ///   [`AttestedResource::verify`] and only render on `Ok`.
    pub fn fetch(&self, uri: &DreggUri) -> Result<(AttestedResource, OriginChrome), FetchError> {
        // [2]-[3] resolve the locator: read the origin cell out of the real
        // ledger (the local analogue of dialing the node + enlivening the swiss).
        let cell = self
            .ledger
            .get(&uri.cell)
            .ok_or(FetchError::OriginNotFound)?;

        // The committed content commitment (slot 0). An empty (all-zero) slot = no
        // content committed.
        let committed_hash = *cell
            .state
            .get_field(CONTENT_COMMITMENT_SLOT)
            .ok_or(FetchError::NoContentCommitted)?;
        if committed_hash == [0u8; 32] {
            return Err(FetchError::NoContentCommitted);
        }

        // [4]-[5] serve the bytes (held by the node) and bind them: the served
        // bytes' hash MUST equal the cell's committed hash (the serve-turn
        // binding). A node that served bytes the origin never committed is caught
        // HERE (before the client even verifies).
        let content_bytes = self
            .served_bytes(&uri.cell)
            .ok_or(FetchError::NoContentCommitted)?;
        let content_hash = *blake3::hash(&content_bytes).as_bytes();
        if content_hash != committed_hash {
            return Err(FetchError::ContentDoesNotMatchCommitment);
        }

        // The serve leaves a RECEIPT: a domain-separated hash binding the content
        // to this origin cell + its nonce (the "a specific verified turn served
        // this content" commitment). This is the leaf that hashes into the
        // federation's receipt-stream root.
        let receipt_hash = self.serve_receipt_hash(&uri.cell, &content_hash, cell.state.nonce());

        // The federation's attestation: a GENUINE AttestedRoot whose
        // receipt_stream_root is the REAL merkle_root_of_receipt_hashes over the
        // committed receipt set (here, the one serve-receipt). The client
        // reconstructs + checks this via the real verify_receipt_stream.
        let receipt_set = vec![receipt_hash];
        let attested_root = self.attest(&receipt_set);

        let resource = AttestedResource {
            content_bytes,
            content_hash,
            receipt_hash,
            attested_root: attested_root.clone(),
            receipt_set,
        };

        // [TRUSTED CHROME] drawn from the LEDGER — cell id + committed URL + the
        // rights the content is served under + finality — never the page.
        let chrome = OriginChrome {
            cell: uri.cell,
            committed_url: self.committed_url(&uri.cell),
            rights: cell.permissions.access.clone(),
            finalized: attested_root.has_quorum(),
        };

        Ok((resource, chrome))
    }

    /// Build a GENUINE quorum-signed [`AttestedRoot`] binding `receipt_set` via
    /// the REAL [`merkle_root_of_receipt_hashes`].
    ///
    /// The `merkle_root` (ledger-state root) is a domain-separated hash of the
    /// height (a real, monotone commitment); the `receipt_stream_root` is the
    /// genuine receipt-stream Merkle root (issue #80's v4 binding) — what makes
    /// "the receipt chain IS the persistence layer" enforceable. The quorum
    /// signatures are GENUINE Ed25519 signatures by the committee signing keys over
    /// the root's canonical `signing_message()` — so a client that holds the
    /// committee can gate on `is_valid(committee)` (red-team LC-1: never a count).
    fn attest(&self, receipt_set: &[[u8; 32]]) -> AttestedRoot {
        let receipt_stream_root = merkle_root_of_receipt_hashes(receipt_set);
        // A real monotone ledger-state root commitment for this height.
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-webofcells-state-root-v1");
        h.update(&self.height.to_le_bytes());
        let merkle_root = *h.finalize().as_bytes();

        let threshold = self.quorum_sks.len();

        // Build the root with all signed fields set FIRST (signatures empty), so the
        // canonical signing message we sign is exactly the one `is_valid` recomputes.
        let mut root = AttestedRoot::new_legacy(
            merkle_root,
            self.height,
            0, // timestamp (structural)
            Vec::new(),
            None,
            threshold,
        );
        // The v4 receipt-stream binding — the genuine #80 field the client checks.
        root.receipt_stream_root = Some(receipt_stream_root);
        root.finality_round = Some(self.height);

        // Real quorum: each committee key signs the canonical message. `is_valid`
        // recomputes this exact message and verifies every signature against the
        // committee — so a fabricated root by attacker keys (or a threshold:0 root)
        // is REJECTED by the anchored client.
        let message = root.signing_message();
        root.quorum_signatures = self
            .quorum_sks
            .iter()
            .map(|sk| (sk.public_key(), dregg_types::sign(sk, &message)))
            .collect();
        root
    }

    /// The serve-receipt hash: a domain-separated commitment to (origin cell +
    /// content + nonce). The "a specific verified turn served this content" leaf.
    fn serve_receipt_hash(&self, cell: &CellId, content_hash: &[u8; 32], nonce: u64) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-webofcells-serve-receipt-v1");
        h.update(&cell.0);
        h.update(content_hash);
        h.update(&nonce.to_le_bytes());
        *h.finalize().as_bytes()
    }

    // ── node-side content + URL byte stores (the bytes a serve ships out-of-band,
    //    keyed by the origin cell — a real serve holds these beside its ledger). ──

    fn store_bytes(&mut self, cell: &CellId, bytes: Vec<u8>) {
        self.bytes_store.push((*cell, bytes));
    }
    /// Replace the node's stored bytes for an existing origin cell (the amend path) —
    /// `served_bytes` then returns the NEW content. Falls back to a store if absent.
    fn replace_bytes(&mut self, cell: &CellId, bytes: Vec<u8>) {
        match self.bytes_store.iter_mut().find(|(c, _)| c == cell) {
            Some(entry) => entry.1 = bytes,
            None => self.bytes_store.push((*cell, bytes)),
        }
    }
    fn served_bytes(&self, cell: &CellId) -> Option<Vec<u8>> {
        self.bytes_store
            .iter()
            .find(|(c, _)| c == cell)
            .map(|(_, b)| b.clone())
    }
    fn bind_url(&mut self, cell: &CellId, url: &str) {
        self.url_store.push((*cell, url.to_string()));
    }
    fn committed_url(&self, cell: &CellId) -> Option<String> {
        self.url_store
            .iter()
            .find(|(c, _)| c == cell)
            .map(|(_, u)| u.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fetch_a_dregg_ref_end_to_end_and_verify_attestation() {
        // Publish a page, fetch its dregg:// ref, and verify the attestation chain
        // end-to-end: content-addressed, receipt-in-stream, real receipt-stream
        // root reconstruction, quorum.
        let mut web = WebOfCells::new(3);
        let body = b"<!doctype html><title>dregg page</title><h1>served from a cell</h1>";
        let uri = web.publish(1, body, "dregg://home");

        let (resource, chrome) = web.fetch(&uri).expect("fetch resolves");

        // The served bytes ARE the published bytes.
        assert_eq!(resource.content_bytes, body);
        // The content is content-addressed.
        assert_eq!(resource.content_hash, *blake3::hash(body).as_bytes());
        // The full client-side verification passes (the genuine chain).
        assert!(
            resource.verify().is_ok(),
            "the attestation chain must verify"
        );
        // The attestation carries the v4 receipt-stream binding (issue #80).
        assert!(resource.attested_root.is_v4_receipt_complete());
        // And it binds EXACTLY the served receipt set (the REAL reconstruction).
        assert!(resource
            .attested_root
            .verify_receipt_stream(&resource.receipt_set));

        // The trusted chrome is drawn from the ledger.
        assert_eq!(chrome.cell, uri.cell);
        assert_eq!(chrome.committed_url.as_deref(), Some("dregg://home"));
        assert!(chrome.finalized);
    }

    #[test]
    fn committee_anchored_verify_accepts_genuine_and_refuses_forgeries() {
        // **THE LC-1 GATE.** The wired consumer must hold the committee keys and gate on the
        // CRYPTOGRAPHIC `is_valid(committee)`, never a count. A genuine fetch verifies against the
        // real committee; a fabricated `threshold:0` root and a root signed by attacker keys are
        // both REFUSED by the anchored gate.
        let mut web = WebOfCells::new(3);
        let uri = web.publish(11, b"<h1>attested page</h1>", "dregg://anchored");
        let committee = web.committee();

        let (genuine, _chrome) = web.fetch(&uri).expect("fetch resolves");
        // The genuine attestation verifies both the structural and the committee-anchored way.
        assert!(genuine.verify().is_ok(), "structural verify holds");
        assert!(
            genuine.verify_anchored(&committee).is_ok(),
            "the committee-anchored crypto gate accepts the genuine quorum"
        );

        // (a) THRESHOLD:0 — a malicious content server forges a root with `threshold:0` and no
        // signatures over the SAME content chain (steps 1–3 still pass). The bare count check
        // `has_quorum()` is FOOLED; both `verify()` (now hardened) and `verify_anchored` refuse.
        let mut forged_zero = genuine.clone();
        forged_zero.attested_root.threshold = 0;
        forged_zero.attested_root.quorum_signatures = Vec::new();
        assert!(
            forged_zero.attested_root.has_quorum(),
            "the count-only check is fooled by threshold:0 — exactly the LC-1 hole"
        );
        assert_eq!(
            forged_zero.verify(),
            Err(FetchError::NoQuorum),
            "the hardened structural verify refuses a threshold:0 root"
        );
        assert_eq!(
            forged_zero.verify_anchored(&committee),
            Err(FetchError::Unattested),
            "the committee gate refuses a threshold:0 root"
        );

        // (b) ATTACKER KEYS — a fabricated root with a real signature, but by a key NOT in the
        // committee. The count-only `verify()` is fooled (1 sig ≥ threshold 1); the committee gate
        // REFUSES because the signer is not a trusted validator.
        let (atk_sk, atk_pk) = dregg_types::generate_keypair();
        let mut forged_keys = genuine.clone();
        forged_keys.attested_root.threshold = 1;
        let msg = forged_keys.attested_root.signing_message();
        forged_keys.attested_root.quorum_signatures =
            vec![(atk_pk, dregg_types::sign(&atk_sk, &msg))];
        assert!(
            forged_keys.verify().is_ok(),
            "the count-only check is fooled by an attacker-signed root"
        );
        assert_eq!(
            forged_keys.verify_anchored(&committee),
            Err(FetchError::Unattested),
            "the committee gate refuses a root signed by keys outside the committee"
        );

        // (c) UNANCHORED — a client with no committee accepts nothing on the anchored path.
        assert_eq!(
            genuine.verify_anchored(&[]),
            Err(FetchError::Unattested),
            "an unanchored client refuses even a genuine resource"
        );

        // (d) WRONG COMMITTEE — the genuine resource is refused against a DIFFERENT (foreign)
        // committee (the anchor is the client's own trusted set, never the resource's claimed
        // signers). The keys are freshly generated, so they are genuinely not this federation's.
        let foreign: Vec<PublicKey> = (0..3).map(|_| dregg_types::generate_keypair().1).collect();
        assert_eq!(
            genuine.verify_anchored(&foreign),
            Err(FetchError::Unattested),
            "a different committee does not attest this federation's root"
        );
    }

    #[test]
    fn amend_advances_the_same_ref_to_a_new_finalized_value() {
        // The live-quote source advance: publish a constitution at threshold 3, then
        // AMEND it to threshold 5. The dregg:// ref is UNCHANGED (same cell), but it
        // re-fetches the NEW committed value with a fresh, still-verifying attestation
        // and an advanced height — "the source finalizes a new height".
        let mut web = WebOfCells::new(3);
        let v0 = b"constitution: quorum threshold = 3";
        let uri = web.publish(7, v0, "dregg://constitution");

        let (r0, c0) = web.fetch(&uri).expect("v0 fetch");
        assert_eq!(r0.content_bytes, v0);
        assert!(r0.verify().is_ok(), "v0 attestation verifies");
        assert!(c0.finalized);
        let receipt_v0 = r0.receipt_hash;
        let h0 = web.height;

        // Amend the SAME source cell to the new threshold (a verified state advance).
        let v1 = b"constitution: quorum threshold = 5";
        let new_height = web.amend(&uri, v1).expect("amend resolves");
        assert!(new_height > h0, "the federation height advanced");

        // The SAME dregg:// ref now resolves to the NEW finalized value (the
        // unbreakable link: same citation, advanced source).
        let (r1, c1) = web.fetch(&uri).expect("v1 fetch (same ref)");
        assert_eq!(
            r1.content_bytes, v1,
            "the quote now shows the amended value"
        );
        assert_ne!(r1.content_hash, r0.content_hash, "a new content commitment");
        assert!(
            r1.verify().is_ok(),
            "v1 attestation still verifies (recomputable)"
        );
        assert!(c1.finalized);
        // The serve-receipt advanced (nonce bumped) — a DISTINCT cited receipt, so a
        // holder of the v0 quote can SEE the source moved (no silent live read).
        assert_ne!(r1.receipt_hash, receipt_v0, "the cited receipt advanced");
    }

    #[test]
    fn amend_of_an_unpublished_ref_is_origin_not_found() {
        let mut web = WebOfCells::new(3);
        let mut k = [0u8; 32];
        k[0] = 88;
        let dead = DreggUri::new(CellId::derive_raw(&k, &[0u8; 32]));
        assert_eq!(web.amend(&dead, b"x"), Err(FetchError::OriginNotFound));
    }

    #[test]
    fn tampered_content_fails_verification() {
        // The anti-ghost tooth: if a (malicious) node hands back bytes whose hash
        // doesn't match the committed content_hash, the CLIENT verification
        // rejects — the page never renders.
        let mut web = WebOfCells::new(3);
        let uri = web.publish(2, b"the real page", "dregg://real");
        let (mut resource, _chrome) = web.fetch(&uri).expect("fetch resolves");

        // Tamper the bytes (but keep the old content_hash — a lying node).
        resource.content_bytes = b"injected phishing content".to_vec();
        assert_eq!(resource.verify(), Err(FetchError::ContentHashMismatch));
    }

    #[test]
    fn a_forged_receipt_stream_root_is_rejected() {
        // If the attested root's receipt_stream_root doesn't match the served
        // receipt set (a federation that signed a DIFFERENT stream), the real
        // verify_receipt_stream reconstruction fails.
        let mut web = WebOfCells::new(3);
        let uri = web.publish(3, b"page three", "dregg://three");
        let (mut resource, _chrome) = web.fetch(&uri).expect("fetch resolves");

        // Forge the root binding to a different receipt set.
        resource.attested_root.receipt_stream_root =
            Some(merkle_root_of_receipt_hashes(&[[0x42u8; 32]]));
        assert_eq!(
            resource.verify(),
            Err(FetchError::ReceiptStreamRootMismatch)
        );
    }

    #[test]
    fn a_node_serving_uncommitted_bytes_is_caught_at_fetch() {
        // The serve-turn binding: the resolver itself refuses to serve bytes whose
        // hash != the origin cell's committed content_hash. We simulate a node
        // whose byte store drifted from the committed hash by overwriting the
        // stored bytes post-publish.
        let mut web = WebOfCells::new(3);
        let uri = web.publish(4, b"committed bytes", "dregg://four");

        // Drift the node's byte store away from the committed commitment.
        for entry in web.bytes_store.iter_mut() {
            if entry.0 == uri.cell {
                entry.1 = b"different bytes the origin never committed".to_vec();
            }
        }
        assert_eq!(
            web.fetch(&uri),
            Err(FetchError::ContentDoesNotMatchCommitment)
        );
    }

    #[test]
    fn a_dead_link_is_origin_not_found() {
        let web = WebOfCells::new(3);
        let mut k = [0u8; 32];
        k[0] = 99;
        let dead = DreggUri::new(CellId::derive_raw(&k, &[0u8; 32]));
        assert_eq!(web.fetch(&dead), Err(FetchError::OriginNotFound));
    }

    #[test]
    fn the_origin_chrome_is_derived_from_the_ledger_not_the_page() {
        // The anti-phishing property: the chrome badge names the cell id + the
        // committed URL bound in state — NOT anything from content_bytes. Even if
        // the page body contains a fake "https://yourbank.com" string, the badge
        // shows the dregg:// cell origin.
        let mut web = WebOfCells::new(3);
        let body = b"<h1>https://yourbank.com login</h1>"; // a phishing page body
        let uri = web.publish(5, body, "dregg://not-your-bank");
        let (_resource, chrome) = web.fetch(&uri).expect("fetch resolves");

        let badge = chrome.badge();
        // The badge is the dregg:// cell origin + the committed URL — never the
        // page's fake bank string.
        assert!(badge.starts_with("dregg://"));
        assert!(badge.contains("dregg://not-your-bank"));
        assert!(!badge.contains("yourbank.com"));
    }

    #[test]
    fn the_uri_string_is_the_content_addressed_cell() {
        let mut web = WebOfCells::new(1);
        let uri = web.publish(6, b"x", "dregg://x");
        let s = uri.to_uri_string();
        assert!(s.starts_with("dregg://"));
        // 64 hex chars for the 32-byte cell id.
        assert_eq!(s.len(), "dregg://".len() + 64);
    }
}
