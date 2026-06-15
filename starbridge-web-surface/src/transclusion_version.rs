//! Versioned transclusion — the SNAPSHOT/LIVE dial (the Rust realization of the Lean
//! `transclusion_stable_under_source_advance` I-confluence crown, made into a *dial*).
//!
//! A `dregg://` transclusion cites an IMMUTABLE PAST receipt, so the quoted reading
//! never changes as the source advances ([`crate::transclusion`]'s "the unbreakable
//! link"). That immutability is the SNAPSHOT half of a dial the docuverse always
//! wanted but the open web could never offer:
//!
//! - **SNAPSHOT** ([`VersionedTransclusion::snapshot`]) — pin a SPECIFIC version (the
//!   source's committed value at a cited receipt-height). I-CONFLUENT: it stays at
//!   the pinned past value no matter how far the source advances. This IS the Lean
//!   `transclusion_stable_under_source_advance` — the citation that does not rot,
//!   reporting the cited past truthfully forever. The reader sees a stable quote and
//!   the provenance dates it (supersession is *visible*, never silent).
//! - **LIVE** ([`VersionedTransclusion::live`]) — re-resolve to the source's CURRENT
//!   finalized value on every read. As the source `amend`s, the live quote follows
//!   ([`crate::web_of_cells::WebOfCells::amend`] advances the SAME ref to a new
//!   finalized height; the live read re-fetches it). The "leptos reactive-transclusion"
//!   consumer the base module names rides exactly this.
//!
//! The dial is the SAME object with a [`Pinning`] discriminant. Both modes resolve
//! through the REAL one-hop [`TranscludedField::include`] — neither reinvents the
//! finalized read, the provenance, or the attestation chain. A forge is refused in
//! either mode (the genuine verify gate fires on every resolve).
//!
//! ## How the snapshot stays pinned (the I-confluence realization)
//!
//! A snapshot is taken by resolving the source ONCE (a genuine
//! [`TranscludedField::include`]) and CACHING the resulting verified
//! [`TranscludedField`] together with the federation height it was finalized at. Its
//! [`VersionedTransclusion::read`] returns that cached, already-verified quote — it
//! does NOT re-fetch, so it is immune to the source advancing (the realization of "the
//! cited receipt is an immutable past; the read never changes"). The cached quote
//! re-verifies forever (the receipt it pins remains a valid leaf of the attestation it
//! captured), so the snapshot is faithful-by-construction, not a frozen copy that
//! could drift from its own provenance.
//!
//! A live quote caches NOTHING; its `read` performs a fresh
//! [`TranscludedField::include`] each time, so it always shows the source's current
//! finalized value with the current cited receipt.

use crate::transclusion::{Provenance, TranscludedField, TransclusionError};
use crate::web_of_cells::{DreggUri, WebOfCells};

/// The dial position — whether a versioned transclusion is pinned to a past version
/// (snapshot) or re-resolves live.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pinning {
    /// SNAPSHOT — pinned to the source's value at `at_height` (the receipt-height the
    /// snapshot was taken at). I-confluent: stable as the source advances.
    Snapshot {
        /// The federation finalized-height the snapshot pins (the `at_root` the quote
        /// is dated to). Captured when the snapshot is taken; never changes.
        at_height: u64,
    },
    /// LIVE — re-resolves to the source's current finalized value on every read.
    Live,
}

impl Pinning {
    /// Is this the snapshot (pinned-past) mode?
    pub fn is_snapshot(&self) -> bool {
        matches!(self, Pinning::Snapshot { .. })
    }

    /// Is this the live (re-resolving) mode?
    pub fn is_live(&self) -> bool {
        matches!(self, Pinning::Live)
    }

    /// The pinned height, if this is a snapshot (`None` for a live quote).
    pub fn pinned_height(&self) -> Option<u64> {
        match self {
            Pinning::Snapshot { at_height } => Some(*at_height),
            Pinning::Live => None,
        }
    }
}

/// The result of reading a versioned transclusion — the verified quote (its displayed
/// bytes ARE the source's committed bytes) plus the dial position it was read under.
///
/// For a SNAPSHOT this is the pinned-past value (stable across reads even as the
/// source advances); for a LIVE quote this is the source's value at the moment of the
/// read. Either way `field` is a genuine verified [`TranscludedField`] carrying real
/// [`Provenance`] — the dial changes WHICH committed value you see, never whether it
/// is verified.
#[derive(Clone, Debug)]
pub struct VersionedRead {
    /// The verified one-hop transclusion this read resolved to (its `quoted_bytes()`
    /// are the displayed value; it re-verifies via the genuine attestation chain).
    pub field: TranscludedField,
    /// The dial position this read was served under (snapshot@height vs live).
    pub pinning: Pinning,
}

impl VersionedRead {
    /// The bytes this read displays — the source's committed content (pinned-past for
    /// a snapshot, current for a live quote). Content-addressed; not a copy.
    pub fn displayed_bytes(&self) -> &[u8] {
        self.field.quoted_bytes()
    }

    /// The provenance citation this read carries (source ref + cited receipt + content
    /// commitment + finalized) — present for BOTH snapshot and live reads.
    pub fn cite(&self) -> &Provenance {
        self.field.cite()
    }

    /// **Re-verify** this read's faithfulness — the genuine
    /// content→commitment→receipt→root→quorum chain ([`TranscludedField::verify`]). A
    /// snapshot re-verifies forever (its pinned receipt stays a valid leaf); a live
    /// read verifies the current value. A forge is caught here in either mode.
    pub fn verify(&self) -> Result<(), TransclusionError> {
        self.field
            .verify()
            .map_err(TransclusionError::ProvenanceUnverified)
    }
}

/// A versioned transclusion — the snapshot/live DIAL over the real one-hop quote.
///
/// Construct with [`VersionedTransclusion::snapshot`] (pin the current finalized
/// version, immune to later source advance) or [`VersionedTransclusion::live`]
/// (re-resolve on every read). [`VersionedTransclusion::read`] serves the dial:
/// the cached pinned quote for a snapshot, a fresh finalized read for a live quote.
#[derive(Clone, Debug)]
pub struct VersionedTransclusion {
    /// The `dregg://` source this quotes.
    source: DreggUri,
    /// The dial position (snapshot@height vs live).
    pinning: Pinning,
    /// For a SNAPSHOT: the cached, already-verified quote taken at pin time — the
    /// immutable-past value the snapshot reports forever. `None` for a live quote
    /// (which caches nothing and re-resolves each read).
    pinned: Option<TranscludedField>,
}

impl VersionedTransclusion {
    /// **Take a SNAPSHOT** — pin the source's CURRENT finalized value, dated to the
    /// current federation height. The snapshot resolves the source ONCE through the
    /// genuine [`TranscludedField::include`] (verifying its attestation chain + its
    /// finalized-ness) and caches the verified quote; every later
    /// [`VersionedTransclusion::read`] returns that pinned value UNCHANGED, however far
    /// the source advances.
    ///
    /// This IS the Lean `transclusion_stable_under_source_advance` as a dial position:
    /// the citation pins an immutable past receipt, so the quoted reading never
    /// changes. Refuses (same gates as `include`) if the source does not resolve to a
    /// verified finalized read — a forge cannot be snapshotted.
    pub fn snapshot(web: &WebOfCells, source: &DreggUri) -> Result<Self, TransclusionError> {
        // Resolve ONCE through the REAL one-hop primitive — the genuine finalized read
        // + provenance verification + finalized gate. A forge/absent source refuses here.
        let field = TranscludedField::include(web, source)?;
        // Date the snapshot to the current federation height (the `at_root` the pin is
        // taken at), drawn from the web's monotone attestation height.
        let at_height = web.height();
        Ok(VersionedTransclusion {
            source: source.clone(),
            pinning: Pinning::Snapshot { at_height },
            pinned: Some(field),
        })
    }

    /// **A LIVE quote** — re-resolve to the source's current finalized value on every
    /// read. Caches nothing; binds only the source ref. Each
    /// [`VersionedTransclusion::read`] performs a fresh
    /// [`TranscludedField::include`], so as the source `amend`s the live quote follows.
    ///
    /// (Construction does not fetch — a live quote is a standing intent to re-read;
    /// the first `read` is where resolution + verification happen.)
    pub fn live(source: &DreggUri) -> Self {
        VersionedTransclusion {
            source: source.clone(),
            pinning: Pinning::Live,
            pinned: None,
        }
    }

    /// The `dregg://` source this quotes.
    pub fn source(&self) -> &DreggUri {
        &self.source
    }

    /// The dial position (snapshot@height vs live).
    pub fn pinning(&self) -> Pinning {
        self.pinning
    }

    /// **Read the quote through the dial.**
    ///
    /// - **SNAPSHOT**: returns the cached pinned-past value (already verified at pin
    ///   time) — does NOT re-fetch, so it is STABLE no matter how far the source
    ///   advanced since the pin. The realization of I-confluence: the cited receipt is
    ///   an immutable past; the read never changes.
    /// - **LIVE**: performs a fresh genuine [`TranscludedField::include`] against
    ///   `web`, returning the source's CURRENT finalized value (verified now). A
    ///   forge/absent source refuses (the genuine gate fires on every live read).
    ///
    /// Both modes return a [`VersionedRead`] carrying real [`Provenance`]; the dial
    /// changes WHICH committed value you see, never whether it is verified.
    pub fn read(&self, web: &WebOfCells) -> Result<VersionedRead, TransclusionError> {
        match &self.pinning {
            Pinning::Snapshot { .. } => {
                // The pinned, already-verified quote — returned UNCHANGED (the
                // immutable-past read). A snapshot always has its cached field.
                let field = self
                    .pinned
                    .clone()
                    .expect("a snapshot caches its pinned verified quote");
                Ok(VersionedRead {
                    field,
                    pinning: self.pinning,
                })
            }
            Pinning::Live => {
                // Re-resolve LIVE through the REAL one-hop primitive — the source's
                // current finalized value, verified now.
                let field = TranscludedField::include(web, &self.source)?;
                Ok(VersionedRead {
                    field,
                    pinning: Pinning::Live,
                })
            }
        }
    }

    /// The pinned-past quote of a snapshot (the cached verified [`TranscludedField`]),
    /// or `None` for a live quote. The snapshot's immutable value, available without a
    /// `web` (it never needs to re-fetch).
    pub fn pinned(&self) -> Option<&TranscludedField> {
        self.pinned.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transclusion::TransclusionError;
    use crate::web_of_cells::{FetchError, WebOfCells};
    use dregg_types::CellId;

    fn dead_uri(seed: u8) -> DreggUri {
        let mut k = [0u8; 32];
        k[0] = seed;
        DreggUri::new(CellId::derive_raw(&k, &[0u8; 32]))
    }

    /// Publish a source document and return the web + its `dregg://` ref.
    fn published(seed: u8, body: &[u8]) -> (WebOfCells, DreggUri) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, body, "dregg://versioned-source");
        (web, uri)
    }

    // (1) THE DIAL — a SNAPSHOT stays at its pinned value after the source amends
    //     (I-confluent / stable); a LIVE quote re-resolves to the NEW value. Both carry
    //     provenance.
    #[test]
    fn snapshot_is_stable_and_live_re_resolves_after_amend() {
        let v0 = b"constitution: quorum threshold = 3";
        let (mut web, uri) = published(7, v0);

        // Take a SNAPSHOT of v0, and stand up a LIVE quote of the same ref.
        let snap = VersionedTransclusion::snapshot(&web, &uri).expect("snapshot v0");
        let live = VersionedTransclusion::live(&uri);
        assert!(snap.pinning().is_snapshot());
        assert!(live.pinning().is_live());
        let pinned_height = snap
            .pinning()
            .pinned_height()
            .expect("snapshot has a pinned height");

        // Read both at v0 — they agree (same current value).
        let snap_r0 = snap.read(&web).expect("snapshot reads v0");
        let live_r0 = live.read(&web).expect("live reads v0");
        assert_eq!(snap_r0.displayed_bytes(), v0);
        assert_eq!(live_r0.displayed_bytes(), v0);
        // BOTH carry provenance (the cited receipt + content commitment).
        assert_eq!(snap_r0.cite().source, uri);
        assert_eq!(live_r0.cite().source, uri);
        assert!(snap_r0.cite().finalized && live_r0.cite().finalized);
        let pinned_receipt = snap_r0.cite().receipt_hash;

        // The source ADVANCES: amend it to v1 (a verified state advance — the SAME ref
        // now finalizes a new value at a new height).
        let v1 = b"constitution: quorum threshold = 5";
        let new_height = web.amend(&uri, v1).expect("amend resolves");
        assert!(
            new_height > pinned_height,
            "the source advanced past the pin"
        );

        // THE SNAPSHOT IS STABLE — it STILL shows v0 (the pinned past value), with the
        // SAME cited receipt. The quote did not rot; it reports the immutable past.
        let snap_r1 = snap.read(&web).expect("snapshot reads (post-amend)");
        assert_eq!(
            snap_r1.displayed_bytes(),
            v0,
            "the snapshot stays at its pinned past value as the source advances (I-confluent)"
        );
        assert_eq!(
            snap_r1.cite().receipt_hash,
            pinned_receipt,
            "the snapshot's cited receipt is unchanged (the immutable past)"
        );
        assert_eq!(
            snap.pinning().pinned_height(),
            Some(pinned_height),
            "the pinned height never changes"
        );

        // THE LIVE QUOTE RE-RESOLVES — it now shows v1 (the source's current finalized
        // value), with a DIFFERENT cited receipt (the source moved, visibly).
        let live_r1 = live.read(&web).expect("live re-reads (post-amend)");
        assert_eq!(
            live_r1.displayed_bytes(),
            v1,
            "the live quote follows the source to its new finalized value"
        );
        assert_ne!(
            live_r1.cite().receipt_hash,
            pinned_receipt,
            "the live read's cited receipt advanced with the source"
        );

        // Both still verify (the dial changes the value, never the faithfulness).
        assert!(snap_r1.verify().is_ok(), "the pinned snapshot re-verifies");
        assert!(
            live_r1.verify().is_ok(),
            "the live read verifies the current value"
        );
    }

    // (1b) The snapshot survives MANY source advances — it is I-confluent against
    //      arbitrary further turns (the unbreakable link, iterated).
    #[test]
    fn snapshot_survives_many_advances() {
        let (mut web, uri) = published(8, b"v0");
        let snap = VersionedTransclusion::snapshot(&web, &uri).expect("snapshot v0");

        for v in [b"v1".as_slice(), b"v2", b"v3", b"v4"] {
            web.amend(&uri, v).expect("amend");
            // The snapshot STILL reads v0 after each advance.
            assert_eq!(
                snap.read(&web).expect("snapshot reads").displayed_bytes(),
                b"v0",
                "the snapshot is stable across arbitrary source advances"
            );
        }
        // …while a live quote of the same ref now sees v4.
        let live = VersionedTransclusion::live(&uri);
        assert_eq!(
            live.read(&web).expect("live reads").displayed_bytes(),
            b"v4"
        );
    }

    // (2) THE PINNED SNAPSHOT NEEDS NO RE-FETCH — its value is available even from a
    //     fresh web that never published the source (it is a captured immutable past,
    //     not a live read). This is the I-confluence "coordination-free" property.
    #[test]
    fn a_snapshot_reads_its_pinned_value_without_re_fetching() {
        let (web, uri) = published(9, b"pinned bytes");
        let snap = VersionedTransclusion::snapshot(&web, &uri).expect("snapshot");

        // The pinned quote is directly available (no web needed).
        let pinned = snap.pinned().expect("a snapshot caches its pinned quote");
        assert_eq!(pinned.quoted_bytes(), b"pinned bytes");
        assert!(
            pinned.verify().is_ok(),
            "the pinned quote re-verifies on its own"
        );

        // Reading against a DIFFERENT, empty web still yields the pinned value (the
        // snapshot does not re-resolve — it reports its captured immutable past).
        let empty = WebOfCells::new(3);
        let r = snap
            .read(&empty)
            .expect("snapshot reads against an empty web");
        assert_eq!(r.displayed_bytes(), b"pinned bytes");
        assert!(r.pinning.is_snapshot());
    }

    // (3) A FORGE IS REFUSED in BOTH modes — the genuine verify gate fires on snapshot
    //     (at pin time) and on every live read.
    #[test]
    fn a_forge_is_refused_in_both_modes() {
        let (web, _uri) = published(10, b"real");

        // (a) SNAPSHOT of an ABSENT source refuses at pin time (no finalized read).
        let absent = dead_uri(200);
        match VersionedTransclusion::snapshot(&web, &absent) {
            Err(TransclusionError::Fetch(FetchError::OriginNotFound)) => {}
            other => panic!("snapshotting an absent source must refuse, got {other:?}"),
        }

        // (b) LIVE read of an ABSENT source refuses on the read.
        let live = VersionedTransclusion::live(&absent);
        match live.read(&web) {
            Err(TransclusionError::Fetch(FetchError::OriginNotFound)) => {}
            other => panic!("a live read of an absent source must refuse, got {other:?}"),
        }

        // (c) A FORGED snapshot — tamper the pinned quote's bytes; the re-verify catches
        //     it (a snapshot is not a frozen copy that can drift from its provenance).
        let (web2, uri2) = published(11, b"genuine");
        let mut snap = VersionedTransclusion::snapshot(&web2, &uri2).expect("snapshot");
        if let Some(field) = snap.pinned.as_mut() {
            field.resource.content_bytes = b"FORGED snapshot bytes".to_vec();
        }
        let r = snap
            .read(&web2)
            .expect("read still returns the (tampered) cached field");
        assert!(
            matches!(
                r.verify(),
                Err(TransclusionError::ProvenanceUnverified(
                    FetchError::ContentHashMismatch
                ))
            ),
            "a tampered snapshot fails the genuine content→commitment chain on re-verify"
        );
    }

    // (4) THE DIAL IS LEGIBLE — snapshot vs live is a first-class, inspectable position.
    #[test]
    fn the_dial_position_is_legible() {
        let (web, uri) = published(12, b"x");
        let snap = VersionedTransclusion::snapshot(&web, &uri).expect("snapshot");
        let live = VersionedTransclusion::live(&uri);

        assert!(snap.pinning().is_snapshot() && !snap.pinning().is_live());
        assert!(live.pinning().is_live() && !live.pinning().is_snapshot());
        assert_eq!(snap.pinning().pinned_height(), Some(web.height()));
        assert_eq!(live.pinning().pinned_height(), None);
        // The read echoes the dial position it was served under.
        assert!(snap.read(&web).unwrap().pinning.is_snapshot());
        assert!(live.read(&web).unwrap().pinning.is_live());
    }
}
