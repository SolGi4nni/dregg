//! # THE OBJECT + THE VERIFICATION LADDER
//!
//! A faithful Rust mirror of `extension/src/netlayer.ts` — the SAME four fail-closed
//! gates, in the SAME order, computed the SAME way, so a mirror that renders an object
//! and an extension that renders it agree about whether it verifies.
//!
//! ```text
//!   (1) blake3(content_bytes) == addr        MANDATORY, always run
//!   (2) receipt_hash ∈ receipt_set           when an attestation is present
//!   (3) recompute(receipt_set) == signed root
//!   (4) quorum: committee-anchored (Ed25519) if a committee is configured,
//!       else the structural count gate
//! ```
//!
//! ## THE ONE THING THIS MIRROR CANNOT DO, AND SAYS SO
//!
//! Running the ladder server-side does **not** promote the tier. The netlayer returns
//! `tier: "extension"` because *the reader's own agent* ran it. Here the SERVER ran it and
//! the reader has only this page's word for the result — that is precisely
//! DREGG-QUIET-UPGRADE.md §5's `trust="server"`, and it is why [`crate::trust`] hard-codes
//! the tier to `server` no matter how many gates pass. A [`VerifyReport`] is therefore not
//! a verdict the reader holds; it is a *disclosure of what the origin claims it checked*,
//! and the page prints it gate by gate so the claim is inspectable rather than a badge.
//!
//! ## THE STORED SHAPE
//!
//! An [`Envelope`] separates the content bytes (whose blake3 IS the address) from the
//! attestation ABOUT those bytes — the same split `netlayer.ts`'s `AttestedEnvelope`
//! makes. The content bytes deserialize to a [`MirrorObject`], which carries the object's
//! **view-tree** in the raw `deos.ui.*` JSON shape that `deos_view::parse_view_tree` eats
//! (the CELL-HOSTED-VIEWTREE shape: a cell's committed heap stores its own view-tree).
//! The mirror does not invent a per-kind schema and does not carry a second renderer — it
//! serves the tree the object commits to.
//!
//! A real consequence worth stating on the page: because the bind values (a poll's tally,
//! a descent's scores) live INSIDE the hashed bytes, **the origin cannot show a different
//! number under the same link** without breaking the digest. What an origin *can* still do
//! is refuse, stall, or serve a stale-but-valid object — which is exactly the residual the
//! tier-`server` label names.

use serde::Deserialize;

/// One quorum signature over the receipt-stream root (mirror of
/// `netlayer.ts`'s `AttestedRootWire.quorumSignatures[]`).
#[derive(Debug, Clone, Deserialize)]
pub struct QuorumSig {
    /// The signer's Ed25519 public key, hex (32 bytes).
    pub signer: String,
    /// The signature over the receipt-stream root string, hex (64 bytes).
    pub sig: String,
}

/// The federation attestation over a receipt stream (mirror of `AttestedRootWire`, itself
/// a mirror of `dregg_types::AttestedRoot`).
#[derive(Debug, Clone, Deserialize)]
pub struct Attestation {
    /// The hash of the serve-receipt that committed this content (hex leaf).
    pub receipt_hash: String,
    /// The committed receipt-hash set — the Merkle leaves the federation signed.
    pub receipt_set: Vec<String>,
    /// The quorum-signed Merkle root over that set (hex).
    pub receipt_stream_root: String,
    /// The Ed25519 quorum threshold: distinct valid signers required. 0 ⇒ degenerate,
    /// which is NEVER acceptance (netlayer.ts's LC-1 note).
    pub threshold: usize,
    /// The quorum signatures.
    #[serde(default)]
    pub quorum_signatures: Vec<QuorumSig>,
    /// A BLS threshold-QC marker. Present ⇒ the ANCHORED gate refuses (a QC-only root
    /// cannot be committee-checked here — mirrors `verify_anchored`'s QC refusal).
    #[serde(default)]
    pub threshold_qc: Option<serde_json::Value>,
}

/// The stored envelope: the content bytes whose blake3 IS the address, plus the (optional)
/// attestation ABOUT those bytes. Kept separate exactly like `AttestedEnvelope` — an
/// attestation folded INTO the hashed bytes would be circular.
#[derive(Debug, Clone)]
pub struct Envelope {
    /// The canonical object bytes. `blake3(content)` is the content address, full stop.
    pub content: Vec<u8>,
    /// The federation attestation, when the serving node has one. `None` is not a failure
    /// — it is a *disclosed absence*: gates 2–4 report `Skipped` and the page says so.
    pub attestation: Option<Attestation>,
}

impl Envelope {
    /// An envelope with no attestation (the shape a devnet-less mirror serves today).
    pub fn unattested(content: impl Into<Vec<u8>>) -> Envelope {
        Envelope {
            content: content.into(),
            attestation: None,
        }
    }

    /// The content address of these bytes — `blake3(content)` in lowercase hex.
    pub fn addr_hex(&self) -> String {
        content_addr(&self.content)
    }
}

/// The content-address function. THE gate: the address IS this digest, which is the whole
/// reason X / Discord / any gateway can be an untrusted transport.
pub fn content_addr(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// The object body — the canonical JSON whose blake3 is the address.
#[derive(Debug, Clone, Deserialize)]
pub struct MirrorObject {
    /// The kind token. MUST equal the kind in the URL, or the resolve fails closed: a
    /// mirror that rendered a `story` under a `/poll/` path would let a link's visible
    /// kind lie about what the reader is looking at.
    pub kind: String,
    /// The object's title, shown as the page heading.
    pub title: String,
    /// The view-tree in the raw `deos.ui.*` JSON shape (`{kind, props, children}`) —
    /// parsed by `deos_view::parse_view_tree`, rendered by `deos_view::web::render_html`.
    pub view: serde_json::Value,
    /// The bind values in tree-walk (pre-order) order — the committed snapshot this
    /// object commits to. INSIDE the hashed bytes, so the tally is part of the address.
    #[serde(default)]
    pub binds: Vec<u64>,
    /// An optional author note, rendered as prose above the card.
    #[serde(default)]
    pub note: Option<String>,
}

/// Which gate of the ladder a report line is about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gate {
    /// (1) `blake3(content) == addr`.
    ContentAddress,
    /// (2) the serve-receipt is a leaf of the attested stream.
    ReceiptMembership,
    /// (3) the recomputed receipt-stream root equals the signed root.
    ReceiptStreamRoot,
    /// (4) the quorum gate (committee-anchored, or the structural count gate).
    Quorum,
}

impl Gate {
    /// The gate's name as printed on the page's disclosure list.
    pub const fn label(self) -> &'static str {
        match self {
            Gate::ContentAddress => "content address: blake3(bytes) == the address in the link",
            Gate::ReceiptMembership => "serve-receipt is a leaf of the attested stream",
            Gate::ReceiptStreamRoot => "recomputed receipt-stream root == the signed root",
            Gate::Quorum => "federation quorum over that root",
        }
    }
}

/// What happened at one gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateOutcome {
    /// The gate ran and held.
    Passed(String),
    /// The gate did not run, and why. NOT a pass — the page prints the reason.
    Skipped(String),
    /// The gate ran and REFUSED. The object is never rendered (fail-closed).
    Failed(String),
}

impl GateOutcome {
    /// Did this gate refuse?
    pub fn is_failure(&self) -> bool {
        matches!(self, GateOutcome::Failed(_))
    }
}

/// The full disclosure of what the ORIGIN checked. Not a verdict the reader holds — see
/// the module doc.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Every gate of the ladder, in order, with its outcome.
    pub gates: Vec<(Gate, GateOutcome)>,
}

impl VerifyReport {
    /// Did any gate refuse? A `true` here means the object is NOT rendered.
    pub fn refused(&self) -> bool {
        self.gates.iter().any(|(_, o)| o.is_failure())
    }

    /// The first refusal's reason, for the error page.
    pub fn refusal(&self) -> Option<(Gate, &str)> {
        self.gates.iter().find_map(|(g, o)| match o {
            GateOutcome::Failed(why) => Some((*g, why.as_str())),
            _ => None,
        })
    }

    /// Did the object carry a federation attestation at all? `false` ⇒ gates 2–4 were
    /// skipped, and the page says so in those words.
    pub fn attested(&self) -> bool {
        self.gates
            .iter()
            .any(|(g, o)| *g == Gate::Quorum && matches!(o, GateOutcome::Passed(_)))
    }
}

/// The mirror's acceptance anchor: the TRUSTED committee, from configuration — never read
/// from the fetched resource (netlayer.ts's standing note). Empty ⇒ the structural gate.
#[derive(Debug, Clone, Default)]
pub struct Committee {
    /// Trusted validator Ed25519 public keys, hex.
    pub keys: Vec<String>,
}

/// Run the ladder over an envelope for a requested address.
///
/// `want_addr_hex` is the FULL 64-hex address the link resolved to (after any short-prefix
/// disambiguation — the prefix is never what the digest is compared against).
pub fn verify(env: &Envelope, want_addr_hex: &str, committee: &Committee) -> VerifyReport {
    let mut gates = Vec::new();

    // ── (1) THE CONTENT-ADDRESSED GATE (MANDATORY) ───────────────────────────
    let recomputed = content_addr(&env.content);
    if recomputed != want_addr_hex.to_ascii_lowercase() {
        gates.push((
            Gate::ContentAddress,
            GateOutcome::Failed(format!(
                "served bytes hash to {recomputed}, not to the address in the link"
            )),
        ));
        // Every later gate is meaningless once the bytes are not the object.
        for g in [
            Gate::ReceiptMembership,
            Gate::ReceiptStreamRoot,
            Gate::Quorum,
        ] {
            gates.push((
                g,
                GateOutcome::Skipped("not reached: the content-address gate refused".into()),
            ));
        }
        return VerifyReport { gates };
    }
    gates.push((
        Gate::ContentAddress,
        GateOutcome::Passed(format!("blake3 = {recomputed}")),
    ));

    let Some(att) = env.attestation.as_ref() else {
        for g in [
            Gate::ReceiptMembership,
            Gate::ReceiptStreamRoot,
            Gate::Quorum,
        ] {
            gates.push((
                g,
                GateOutcome::Skipped(
                    "this object carried no federation attestation · NOT CHECKED".into(),
                ),
            ));
        }
        return VerifyReport { gates };
    };

    // ── (2) the serve-receipt is in the committed set ─────────────────────────
    let want = att.receipt_hash.to_ascii_lowercase();
    if !att
        .receipt_set
        .iter()
        .any(|h| h.to_ascii_lowercase() == want)
    {
        gates.push((
            Gate::ReceiptMembership,
            GateOutcome::Failed("serve-receipt is not a leaf of the attested stream".into()),
        ));
        for g in [Gate::ReceiptStreamRoot, Gate::Quorum] {
            gates.push((
                g,
                GateOutcome::Skipped("not reached: the receipt-membership gate refused".into()),
            ));
        }
        return VerifyReport { gates };
    }
    gates.push((
        Gate::ReceiptMembership,
        GateOutcome::Passed(format!(
            "{} receipt(s) in the stream",
            att.receipt_set.len()
        )),
    ));

    // ── (3) the signed root binds exactly this receipt set ───────────────────
    let root = receipt_stream_root(&att.receipt_set);
    if root != att.receipt_stream_root.to_ascii_lowercase() {
        gates.push((
            Gate::ReceiptStreamRoot,
            GateOutcome::Failed("recomputed receipt-stream root != the signed root".into()),
        ));
        gates.push((
            Gate::Quorum,
            GateOutcome::Skipped("not reached: the stream-root gate refused".into()),
        ));
        return VerifyReport { gates };
    }
    gates.push((
        Gate::ReceiptStreamRoot,
        GateOutcome::Passed(format!("root = {root}")),
    ));

    // ── (4) the quorum gate ──────────────────────────────────────────────────
    gates.push((Gate::Quorum, check_quorum(att, committee)));
    VerifyReport { gates }
}

/// The quorum gate — a line-for-line mirror of `netlayer.ts`'s `checkQuorum`.
///
/// * COMMITTEE-ANCHORED (a committee is configured): a QC-only root refuses; the threshold
///   must be positive; only DISTINCT signers whose key is in the trusted committee AND
///   whose Ed25519 signature over the root verifies are counted.
/// * STRUCTURAL (no committee): the count gate. A degenerate `threshold: 0` / empty
///   signature set is NEVER acceptance.
fn check_quorum(att: &Attestation, committee: &Committee) -> GateOutcome {
    if !committee.keys.is_empty() {
        if att.threshold_qc.is_some() {
            return GateOutcome::Failed("QC-only root is not committee-anchored".into());
        }
        if att.threshold == 0 {
            return GateOutcome::Failed("no positive threshold".into());
        }
        let trusted: Vec<String> = committee
            .keys
            .iter()
            .map(|k| k.to_ascii_lowercase())
            .collect();
        let mut seen: Vec<String> = Vec::new();
        for s in &att.quorum_signatures {
            let signer = s.signer.to_ascii_lowercase();
            if !trusted.contains(&signer) {
                continue; // a signature by a non-committee key never counts
            }
            if seen.contains(&signer) {
                continue; // distinct signers only
            }
            if verify_ed25519(&signer, att.receipt_stream_root.as_bytes(), &s.sig) {
                seen.push(signer);
            }
        }
        if seen.len() < att.threshold {
            return GateOutcome::Failed(format!(
                "committee quorum not met: {} valid distinct signer(s) < threshold {}",
                seen.len(),
                att.threshold
            ));
        }
        return GateOutcome::Passed(format!(
            "committee-anchored: {}/{} trusted signers verified",
            seen.len(),
            att.threshold
        ));
    }

    if att.threshold_qc.is_none() && (att.threshold == 0 || att.quorum_signatures.is_empty()) {
        return GateOutcome::Failed("degenerate / empty quorum".into());
    }
    if att.threshold_qc.is_none() && att.quorum_signatures.len() < att.threshold {
        return GateOutcome::Failed("signature count below threshold".into());
    }
    GateOutcome::Passed(format!(
        "structural (no trusted committee configured): {} signature(s) >= threshold {}; \
         signatures were COUNTED, not cryptographically anchored",
        att.quorum_signatures.len(),
        att.threshold
    ))
}

/// One Ed25519 check: `sig` (hex) over `msg` by `signer_hex`. Any malformed input is a
/// refusal, never a pass.
fn verify_ed25519(signer_hex: &str, msg: &[u8], sig_hex: &str) -> bool {
    let (Some(pk), Some(sg)) = (unhex::<32>(signer_hex), unhex::<64>(sig_hex)) else {
        return false;
    };
    let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(&pk) else {
        return false;
    };
    vk.verify_strict(msg, &ed25519_dalek::Signature::from_bytes(&sg))
        .is_ok()
}

/// Decode exactly `N` bytes of hex, or `None`.
fn unhex<const N: usize>(s: &str) -> Option<[u8; N]> {
    let b = s.as_bytes();
    if b.len() != N * 2 {
        return None;
    }
    let mut out = [0u8; N];
    for (i, slot) in out.iter_mut().enumerate() {
        let hi = (b[2 * i] as char).to_digit(16)?;
        let lo = (b[2 * i + 1] as char).to_digit(16)?;
        *slot = (hi * 16 + lo) as u8;
    }
    Some(out)
}

/// Reconstruct the receipt-stream Merkle root from the leaf set — the
/// `merkle_root_of_receipt_hashes` shape `netlayer.ts` recomputes: a binary tree over the
/// leaves, each interior node `blake3(left_hex_string ++ right_hex_string)` over the
/// concatenated hex TEXT, duplicating the last leaf on an odd row. Empty set ⇒
/// `blake3("")`. Deterministic in leaf order.
///
/// Byte-for-byte agreement with the TS is load-bearing: an attestation the extension
/// accepts must be one the mirror accepts, or the two surfaces disagree about the same
/// object.
pub fn receipt_stream_root(receipt_set: &[String]) -> String {
    if receipt_set.is_empty() {
        return content_addr(b"");
    }
    let mut level: Vec<String> = receipt_set.iter().map(|h| h.to_ascii_lowercase()).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i < level.len() {
            let left = &level[i];
            let right = if i + 1 < level.len() {
                &level[i + 1]
            } else {
                &level[i] // duplicate the last on an odd row
            };
            next.push(content_addr(format!("{left}{right}").as_bytes()));
            i += 2;
        }
        level = next;
    }
    level.remove(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn obj_bytes() -> Vec<u8> {
        br#"{"kind":"poll","title":"t","view":{"kind":"text","props":{"text":"hi"}}}"#.to_vec()
    }

    #[test]
    fn content_address_gate_refuses_substituted_bytes() {
        let env = Envelope::unattested(obj_bytes());
        let good = env.addr_hex();
        assert!(!verify(&env, &good, &Committee::default()).refused());

        let hostile = Envelope::unattested(b"{\"kind\":\"poll\",\"title\":\"LIES\"}".to_vec());
        let r = verify(&hostile, &good, &Committee::default());
        assert!(r.refused());
        assert_eq!(r.refusal().unwrap().0, Gate::ContentAddress);
    }

    #[test]
    fn absent_attestation_is_skipped_not_passed() {
        let env = Envelope::unattested(obj_bytes());
        let r = verify(&env, &env.addr_hex(), &Committee::default());
        assert!(!r.refused());
        assert!(
            !r.attested(),
            "an absent attestation must NOT read as attested"
        );
        let (_, quorum) = r.gates.iter().find(|(g, _)| *g == Gate::Quorum).unwrap();
        assert!(matches!(quorum, GateOutcome::Skipped(_)));
    }

    #[test]
    fn degenerate_quorum_is_never_acceptance() {
        let leaf = content_addr(b"receipt-1");
        let env = Envelope {
            content: obj_bytes(),
            attestation: Some(Attestation {
                receipt_hash: leaf.clone(),
                receipt_set: vec![leaf.clone()],
                receipt_stream_root: receipt_stream_root(&[leaf]),
                threshold: 0,
                quorum_signatures: vec![],
                threshold_qc: None,
            }),
        };
        let r = verify(&env, &env.addr_hex(), &Committee::default());
        assert!(r.refused());
        assert_eq!(r.refusal().unwrap().0, Gate::Quorum);
    }

    #[test]
    fn stream_root_mismatch_refuses() {
        let leaf = content_addr(b"receipt-1");
        let env = Envelope {
            content: obj_bytes(),
            attestation: Some(Attestation {
                receipt_hash: leaf.clone(),
                receipt_set: vec![leaf],
                receipt_stream_root: content_addr(b"a different root entirely"),
                threshold: 1,
                quorum_signatures: vec![QuorumSig {
                    signer: "00".repeat(32),
                    sig: "00".repeat(64),
                }],
                threshold_qc: None,
            }),
        };
        let r = verify(&env, &env.addr_hex(), &Committee::default());
        assert_eq!(r.refusal().unwrap().0, Gate::ReceiptStreamRoot);
    }

    #[test]
    fn anchored_gate_refuses_a_forged_signature() {
        let leaf = content_addr(b"receipt-1");
        let root = receipt_stream_root(std::slice::from_ref(&leaf));
        let committee = Committee {
            keys: vec!["11".repeat(32)],
        };
        let env = Envelope {
            content: obj_bytes(),
            attestation: Some(Attestation {
                receipt_hash: leaf.clone(),
                receipt_set: vec![leaf],
                receipt_stream_root: root,
                threshold: 1,
                // A signer IN the committee, but the signature is garbage.
                quorum_signatures: vec![QuorumSig {
                    signer: "11".repeat(32),
                    sig: "ab".repeat(64),
                }],
                threshold_qc: None,
            }),
        };
        let r = verify(&env, &env.addr_hex(), &committee);
        assert!(r.refused());
        assert_eq!(r.refusal().unwrap().0, Gate::Quorum);
    }

    #[test]
    fn merkle_root_duplicates_the_last_leaf_on_an_odd_row() {
        let a = content_addr(b"a");
        let b = content_addr(b"b");
        let c = content_addr(b"c");
        // 3 leaves: [h(a||b), h(c||c)] -> h(that pair).
        let l0 = content_addr(format!("{a}{b}").as_bytes());
        let l1 = content_addr(format!("{c}{c}").as_bytes());
        let want = content_addr(format!("{l0}{l1}").as_bytes());
        assert_eq!(receipt_stream_root(&[a, b, c]), want);
    }
}
