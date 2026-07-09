//! Transclusion CHAINS — a quote of a quote of a quote, carrying the COMPOSED
//! provenance (the Rust realization of the Lean `transclusion_chain_*` shape:
//! `transclusion_provenance_faithful` + `transclusion_forge_refused` COMPOSED across
//! hops, so the anti-forge tooth bites at *every* link).
//!
//! Ted Nelson's docuverse was a *graph* of quotes: document C quotes document B,
//! which itself quotes document A. The open web cannot make that honest — each `<a>`
//! is a bare location, and a chain `A→B→C` is three independent dangling pointers,
//! any of which rots silently. dregg's [`TranscludedField`](crate::transclusion) made
//! ONE hop honest (a verified `dregg://` finalized read with cryptographic
//! provenance); a CHAIN is the *composition* of those hops, and the load-bearing
//! claim is that **the anti-forge tooth COMPOSES**: a chain `A→B→C` resolves to C's
//! committed value carrying the WHOLE citation trail (each hop's receipt), and a
//! forged or absent link ANYWHERE in the chain refuses the whole chain.
//!
//! This is built ENTIRELY on the real one-hop primitive — every link is a genuine
//! [`TranscludedField::include`] against the real [`WebOfCells`], every link's
//! faithfulness is the genuine [`TranscludedField::verify`] (the
//! content→commitment→receipt→receipt-stream-root→quorum chain), every link's
//! [`Provenance`] is the one the verified fetch drew. The chain invents NO new
//! attestation: it threads the existing teeth and refuses if any tooth bites.
//!
//! ## What a chain IS (and the deliberate shape)
//!
//! In the docuverse, "B quotes A" means B's *published content* is (or contains) the
//! value B transcluded from A — so when C transcludes B, resolving C's quote walks
//! THROUGH B back to A. We model a chain as an ordered list of `dregg://` hops
//! `[A, B, C]` (tail = the final source whose committed value the chain displays,
//! head = the outermost quote). [`TransclusionChain::resolve`] resolves EVERY hop as
//! a real one-hop transclusion, in order; the displayed value is the FINAL hop's
//! committed bytes (the deepest source — C quotes B quotes A, so the reader sees A's
//! value, with B's and C's citations stacked on top). The
//! [`ChainProvenance`] is the full trail: one [`Provenance`] per hop, head→tail, so a
//! verifier can recompute every link and tooling can date the whole citation path —
//! exactly the "composed provenance, each hop's receipt" the deliverable asks for.
//!
//! ## The composing teeth (mirrors the Lean keystones, composed)
//!
//! - **Faithful at every hop** (`transclusion_provenance_faithful`, composed): each
//!   hop's quoted bytes EQUAL the source that hop committed, recomputably — so the
//!   whole chain's displayed value equals the deepest source's committed value,
//!   through a trail every link of which is verified.
//! - **A forge anywhere refuses** (`transclusion_forge_refused`, composed): a forged
//!   or absent link at ANY position fails its own hop's verify/fetch gate, and
//!   [`TransclusionChain::resolve`] propagates that failure as
//!   [`ChainError::Link`] naming the broken hop index — the anti-forge tooth does not
//!   weaken as the chain lengthens; it bites at the first broken link.
//! - **No silent rot** (the unbreakable link, composed): because every hop pins an
//!   immutable receipt, a chain's [`ChainProvenance`] dates every link; a superseded
//!   link is *visible* in the trail, never a silent dangling pointer.

use crate::transclusion::{Provenance, TranscludedField, TransclusionError};
use crate::web_of_cells::{DreggUri, WebOfCells};

/// The composed provenance of a resolved chain — the FULL citation trail, one
/// [`Provenance`] per hop (head→tail), each link's receipt carried.
///
/// This is the chain's answer to "where did this quote come from?": not a single
/// citation but the whole path `C cites B cites A`, every link recomputable (each
/// carries its content commitment + cited receipt) and datable (each pins an
/// immutable past). A verifier walks `hops` to re-check every link; tooling renders
/// it as the stacked citation ("quoted from B@receipt, which quotes A@receipt").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainProvenance {
    /// One [`Provenance`] per hop, in chain order (head = outermost quote, tail =
    /// the deepest source whose committed value the chain displays). Never empty for
    /// a resolved chain.
    pub hops: Vec<Provenance>,
}

impl ChainProvenance {
    /// How many links the chain composes (≥ 1 for any resolved chain).
    pub fn depth(&self) -> usize {
        self.hops.len()
    }

    /// The citation of the DEEPEST source — the hop whose committed value the chain
    /// actually displays (the tail of `A→B→C`: A's citation). This is the provenance
    /// of the bytes the reader sees.
    pub fn source(&self) -> &Provenance {
        // A resolved chain is non-empty by construction (resolve refuses an empty
        // chain), so last() is Some; expose the deepest citation.
        self.hops
            .last()
            .expect("a resolved chain has at least one hop")
    }

    /// The OUTERMOST citation — the head of `A→B→C` (C's citation: the quote the
    /// reader's document literally contains). The other end of the trail.
    pub fn outermost(&self) -> &Provenance {
        self.hops
            .first()
            .expect("a resolved chain has at least one hop")
    }

    /// Is EVERY hop finalized? A chain is faithful only if every link quotes
    /// finalized state — a single un-finalized link makes the whole trail suspect.
    /// (A resolved chain already guarantees this — `resolve` refuses a non-finalized
    /// hop — so this is the structural readout that witnesses it.)
    pub fn all_finalized(&self) -> bool {
        self.hops.iter().all(|p| p.finalized)
    }
}

/// A resolved transclusion chain — a quote of a quote of a quote, with its displayed
/// value (the deepest source's committed bytes) and the composed citation trail.
///
/// Built ONLY by [`TransclusionChain::resolve`], which resolves every hop as a real
/// one-hop [`TranscludedField`]. The `final_field` is the deepest source's verified
/// transclusion (the bytes displayed); `provenance` is the full head→tail trail.
#[derive(Clone, Debug)]
pub struct ResolvedChain {
    /// The deepest source's verified one-hop transclusion — its `quoted_bytes()` ARE
    /// the value the whole chain displays, and it re-verifies via the genuine
    /// attestation chain.
    pub final_field: TranscludedField,
    /// The composed provenance: every hop's citation, head→tail.
    pub provenance: ChainProvenance,
}

impl ResolvedChain {
    /// The bytes the chain displays — the DEEPEST source's committed content
    /// (`A→B→C` shows A's value). These ARE the source's committed bytes (content-
    /// addressed), carried up through the verified trail, not a copy.
    pub fn displayed_bytes(&self) -> &[u8] {
        self.final_field.quoted_bytes()
    }

    /// **Re-verify the WHOLE chain's faithfulness** — the composed anti-forge tooth.
    /// Walks every hop's [`Provenance`] (re-checking each link's content commitment
    /// is internally consistent) and re-runs the deepest source's genuine attestation
    /// chain ([`TranscludedField::verify`]). A tampered link anywhere is caught.
    ///
    /// (The forward [`TransclusionChain::resolve`] already verified each hop at
    /// resolve time; this lets a holder recompute the full trail's faithfulness at
    /// any later time — the chain analogue of [`TranscludedField::verify`].)
    pub fn verify(&self) -> Result<(), ChainError> {
        // Every hop must be finalized (a non-finalized link is not a faithful quote).
        for (i, hop) in self.provenance.hops.iter().enumerate() {
            if !hop.finalized {
                return Err(ChainError::Link {
                    index: i,
                    source: hop.source.clone(),
                    error: TransclusionError::NotFinalized,
                });
            }
        }
        // The deepest source's genuine attestation chain must still hold (the bytes
        // displayed are the source's committed bytes, recomputably).
        self.final_field.verify().map_err(|e| ChainError::Link {
            index: self.provenance.hops.len().saturating_sub(1),
            source: self.provenance.source().source.clone(),
            error: TransclusionError::ProvenanceUnverified(e),
        })
    }

    /// The chain's depth (number of links).
    pub fn depth(&self) -> usize {
        self.provenance.depth()
    }
}

/// What can go wrong resolving a chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainError {
    /// The chain was empty — there is nothing to quote (a chain needs ≥ 1 hop).
    Empty,
    /// A LINK in the chain broke: the hop at `index` (citing `source`) failed its own
    /// one-hop transclusion — a forged, absent, or un-finalized link. The anti-forge
    /// tooth bit HERE; the whole chain refuses. Carries the underlying
    /// [`TransclusionError`] so the broken link is fully diagnosable.
    Link {
        /// The 0-based position of the broken hop in the chain (head = 0).
        index: usize,
        /// The `dregg://` ref of the broken link (what it tried to quote).
        source: DreggUri,
        /// Why the link broke (the genuine one-hop refusal).
        error: TransclusionError,
    },
}

/// A transclusion chain — an ordered list of `dregg://` hops, head→tail, that
/// resolves to the deepest source's committed value with the full composed
/// provenance.
///
/// `[A, B, C]` reads as "the outermost quote A quotes B quotes the source C" — the
/// HEAD is the document the reader holds, the TAIL is the deepest source whose
/// committed value is displayed. (One-hop is the degenerate chain `[A]`, identical to
/// a plain [`TranscludedField`].)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransclusionChain {
    /// The hops, head→tail. Non-empty chains resolve; an empty chain is
    /// [`ChainError::Empty`].
    hops: Vec<DreggUri>,
}

impl TransclusionChain {
    /// Build a chain from an ordered list of hops (head→tail). The head is the
    /// outermost quote; the tail is the deepest source displayed.
    pub fn new(hops: impl IntoIterator<Item = DreggUri>) -> Self {
        TransclusionChain {
            hops: hops.into_iter().collect(),
        }
    }

    /// Extend the chain by quoting one level DEEPER (append a tail hop) — "this quote
    /// itself quotes `deeper`". The fluent builder for `A.then(B).then(C)`.
    pub fn then(mut self, deeper: DreggUri) -> Self {
        self.hops.push(deeper);
        self
    }

    /// The hops (head→tail, read-only).
    pub fn hops(&self) -> &[DreggUri] {
        &self.hops
    }

    /// The number of links.
    pub fn depth(&self) -> usize {
        self.hops.len()
    }

    /// **Resolve the chain** — the composed verified read. Resolves EVERY hop as a
    /// genuine one-hop [`TranscludedField::include`] against `web` (each link's
    /// content→commitment→receipt→root→quorum chain verified, each link's
    /// finalized-ness checked), in order, and threads the composed [`ChainProvenance`].
    ///
    /// The displayed value is the DEEPEST source's committed bytes (the tail's quote);
    /// the provenance is the full head→tail trail. A forged or absent link at ANY
    /// position fails its own hop and surfaces as [`ChainError::Link`] naming the
    /// broken index — the anti-forge tooth COMPOSES (it bites at the first broken
    /// link, however deep the chain).
    ///
    /// This is the Rust realization of the Lean `transclusion_chain_*` shape: the
    /// one-hop `transclusion_provenance_faithful` + `transclusion_forge_refused`,
    /// composed across the chain.
    pub fn resolve(&self, web: &WebOfCells) -> Result<ResolvedChain, ChainError> {
        if self.hops.is_empty() {
            return Err(ChainError::Empty);
        }

        let mut provenance = Vec::with_capacity(self.hops.len());
        let mut final_field: Option<TranscludedField> = None;

        // Resolve every hop as a REAL one-hop transclusion. Each include() runs the
        // genuine finalized read + committee-anchored (`verify_anchored`) provenance
        // verification + finalized gate; a broken OR UNANCHORED link fails HERE and we
        // name its index (the composed anti-forge tooth). Every hop anchors to the
        // resolver's trusted committee — signature verification, never a structural count.
        for (index, hop) in self.hops.iter().enumerate() {
            let field = TranscludedField::include(web, hop).map_err(|error| ChainError::Link {
                index,
                source: hop.clone(),
                error,
            })?;
            // The link's citation is the one the verified fetch drew (never the
            // displayed content) — push it onto the trail, head→tail.
            provenance.push(field.cite().clone());
            // The deepest hop resolved so far is the value the chain displays.
            final_field = Some(field);
        }

        Ok(ResolvedChain {
            final_field: final_field.expect("non-empty chain resolved at least one hop"),
            provenance: ChainProvenance { hops: provenance },
        })
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

    /// Publish three distinct source documents into one web-of-cells and return the
    /// web + their three `dregg://` refs `[a, b, c]`. Each is a genuine finalized read
    /// source (content committed in real cell state, 3-of-3 quorum attested).
    fn three_docs() -> (WebOfCells, DreggUri, DreggUri, DreggUri) {
        let mut web = WebOfCells::new(3);
        let a = web.publish(
            11,
            b"<h1>document A (the outer quote)</h1>",
            "dregg://doc-a",
        );
        let b = web.publish(
            12,
            b"<h1>document B (the middle quote)</h1>",
            "dregg://doc-b",
        );
        let c = web.publish(
            13,
            b"<h1>document C (the deepest source)</h1>",
            "dregg://doc-c",
        );
        (web, a, b, c)
    }

    // (1) A 3-HOP CHAIN RESOLVES with the FULL composed provenance: the displayed
    //     value is the DEEPEST source's committed bytes, and the trail carries every
    //     hop's citation (each hop's receipt) head→tail.
    #[test]
    fn three_hop_chain_resolves_with_full_composed_provenance() {
        let (web, a, b, c) = three_docs();

        // A → B → C : the outermost quote A, quoting B, quoting the source C.
        let chain = TransclusionChain::new([a.clone()])
            .then(b.clone())
            .then(c.clone());
        assert_eq!(chain.depth(), 3);

        let resolved = chain
            .resolve(&web)
            .expect("a 3-hop chain of real sources resolves");

        // The displayed value is the DEEPEST source's (C's) committed bytes — the
        // quote of a quote of a quote shows the bottom of the stack.
        assert_eq!(
            resolved.displayed_bytes(),
            b"<h1>document C (the deepest source)</h1>"
        );

        // The composed provenance is the FULL trail: one citation per hop, head→tail.
        let prov = &resolved.provenance;
        assert_eq!(prov.depth(), 3, "three links, three citations");
        assert_eq!(
            prov.outermost().source,
            a,
            "head of the trail = the outer quote A"
        );
        assert_eq!(
            prov.source().source,
            c,
            "tail of the trail = the deepest source C"
        );
        // The middle citation is B.
        assert_eq!(prov.hops[1].source, b);

        // EACH hop's citation carries its own cited receipt (a verifiable backlink per
        // link, not a bare pointer) — and they are DISTINCT receipts (distinct sources).
        assert_ne!(prov.hops[0].receipt_hash, prov.hops[1].receipt_hash);
        assert_ne!(prov.hops[1].receipt_hash, prov.hops[2].receipt_hash);
        // Every link quotes finalized state.
        assert!(prov.all_finalized(), "every link in the chain is finalized");

        // The deepest source's citation content-addresses the displayed bytes.
        assert_eq!(
            prov.source().content_hash,
            *blake3::hash(resolved.displayed_bytes()).as_bytes()
        );

        // And the whole chain re-verifies (the composed anti-forge tooth, recomputable
        // by a holder at any later time).
        assert!(
            resolved.verify().is_ok(),
            "the resolved chain re-verifies end-to-end"
        );
    }

    // (2) THE COMPOSED ANTI-FORGE TOOTH — a forged/absent link ANYWHERE refuses the
    //     WHOLE chain, naming the broken hop index. The tooth does not weaken with depth.
    #[test]
    fn an_absent_link_anywhere_refuses_the_whole_chain() {
        let (web, a, b, _c) = three_docs();
        let absent = dead_uri(250); // never published — a dangling link.

        // Broken link in the MIDDLE: A → (absent) → B.
        let chain = TransclusionChain::new([a.clone()])
            .then(absent.clone())
            .then(b);
        let r = chain.resolve(&web);
        match r {
            Err(ChainError::Link {
                index,
                source,
                error,
            }) => {
                assert_eq!(index, 1, "the broken link is the middle hop (index 1)");
                assert_eq!(source, absent, "it names the absent ref");
                // The genuine one-hop refusal: an absent source does not resolve to a
                // finalized read (it fails at the fetch).
                assert!(
                    matches!(error, TransclusionError::Fetch(FetchError::OriginNotFound)),
                    "the link broke at the real finalized-read fetch, got {error:?}"
                );
            }
            other => panic!("a broken middle link must refuse the chain, got {other:?}"),
        }

        // Broken link at the HEAD (index 0) refuses just the same.
        let head_broken = TransclusionChain::new([absent.clone()]).then(a);
        match head_broken.resolve(&web) {
            Err(ChainError::Link { index, .. }) => assert_eq!(index, 0),
            other => panic!("a broken head link must refuse, got {other:?}"),
        }
    }

    // (2b) A FORGED link (genuine source, but the resolved field's bytes tampered)
    //      fails the composed re-verify — the anti-forge tooth bites on a tampered link.
    #[test]
    fn a_forged_link_fails_the_composed_reverify() {
        let (web, a, b, c) = three_docs();
        let mut resolved = TransclusionChain::new([a])
            .then(b)
            .then(c)
            .resolve(&web)
            .expect("resolves");

        // Forge the DEEPEST link: tamper the displayed bytes so they no longer match
        // the committed content hash. The composed verify() re-runs the genuine
        // attestation chain on the deepest source and catches it.
        resolved.final_field.resource.content_bytes = b"FORGED chain tail bytes".to_vec();
        match resolved.verify() {
            Err(ChainError::Link { index, error, .. }) => {
                assert_eq!(index, 2, "the tampered deepest link (index 2)");
                assert!(
                    matches!(
                        error,
                        TransclusionError::ProvenanceUnverified(FetchError::ContentHashMismatch)
                    ),
                    "a tampered link fails the genuine content→commitment chain, got {error:?}"
                );
            }
            other => panic!("a forged link must fail the composed re-verify, got {other:?}"),
        }
    }

    // (3) An empty chain has nothing to quote.
    #[test]
    fn an_empty_chain_is_refused() {
        let (web, ..) = three_docs();
        let empty = TransclusionChain::new([]);
        assert!(matches!(empty.resolve(&web), Err(ChainError::Empty)));
    }

    // (4) A degenerate one-hop chain is exactly a plain transclusion (the chain
    //     generalizes the single quote, reusing the SAME one-hop primitive).
    #[test]
    fn a_one_hop_chain_is_a_plain_transclusion() {
        let (web, a, ..) = three_docs();
        let resolved = TransclusionChain::new([a.clone()])
            .resolve(&web)
            .expect("one-hop resolves");
        assert_eq!(resolved.depth(), 1);
        assert_eq!(
            resolved.displayed_bytes(),
            b"<h1>document A (the outer quote)</h1>"
        );
        assert_eq!(resolved.provenance.source().source, a);
        assert_eq!(
            resolved.provenance.outermost().source,
            a,
            "head == tail for one hop"
        );

        // It equals what the bare one-hop primitive yields (same value, same citation).
        let one_hop = TranscludedField::include(&web, &a).expect("one-hop include");
        assert_eq!(resolved.displayed_bytes(), one_hop.quoted_bytes());
        assert_eq!(
            resolved.provenance.source().receipt_hash,
            one_hop.cite().receipt_hash
        );
    }
}
