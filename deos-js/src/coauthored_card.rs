//! **Two principals co-drive ONE shared card** — the multiplayer-cards killer
//! primitive made tangible, end to end and `cargo test`-able.
//!
//! The membrane (`starbridge-v2::shared_fork`) already mints → carries → rehydrates a
//! cap-bounded fork of a world for a second principal; the card editor
//! ([`crate::card_editor`]) already turns inspection of a card into authoring (each
//! view edit a receipted patch on the card's `view_source` document); and the patch
//! core ([`dregg_doc`]) already merges two divergent document histories by **pushout**
//! — a conflict is a first-class [`dregg_doc::ConflictRegion`] antichain, never a
//! silent overwrite. This module is the smallest weld that PROVES those three meet on
//! one object: **a shared deos-js card two distinct principals each fork, each edit
//! (in their own view), then STITCH.**
//!
//! ## The loop
//!
//! 1. **One shared card.** [`SharedCard::seed`] builds a card (an [`Applet`] + its
//!    [`AppletManifest`]) whose `view_source` is a [`ViewTree`] — the same
//!    `{kind, props, children}` JSON a renderer paints.
//! 2. **Two forks.** Principal `A` and principal `B` each take a fork
//!    ([`SharedCard::fork_for`]) — a [`CardEditor`] over a clone of the card's view,
//!    bounded by that principal's own `held` authority (the cap tooth: a principal
//!    can only author a card it is authorized to). The two forks share a common
//!    prefix (the seed view) and then diverge.
//! 3. **Each drives its view.** `A` relabels a text node; `B` adds a button — each a
//!    real receipted patch on its OWN fork's `view_source` document
//!    ([`CardEditor::edit_view`]).
//! 4. **Stitch by pushout.** [`SharedCard::stitch`] folds the two forks' divergent
//!    `view_source` histories ([`crate::program_doc::ProgramSource::merge`], the
//!    `dregg_doc` pushout). A **clean** merge keeps BOTH edits; a **true conflict**
//!    (both principals edit the same node) surfaces as a [`dregg_doc::ConflictRegion`]
//!    — two live, attributed alternatives a reader resolves later, never a last-writer
//!    overwrite.
//!
//! gpui-free + `cargo test`-able: the card edits are real receipted patches through
//! the embedded executor, and the stitch is the genuine `dregg_doc` pushout — so the
//! tests prove two-principal co-drive without a GPU.

use dregg_cell::AuthRequired;
use dregg_doc::{Author, Rendered};

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{CardEditor, EditError, ViewEdit, ViewPatch, ViewTree};
use crate::portable::{AffordanceSpec, AppletManifest, ApplyOp};
use crate::program_doc::ProgramSource;
use dregg_cell::Requirement;

/// The model slot the seed card's counter lives in (a real field the card's `inc`
/// affordance bumps — proves the card is a live, fireable applet, not a static blob).
pub const COUNT_SLOT: Slot = 0;

/// **A shared card two principals co-author.** Holds the seed manifest (the common
/// prefix both forks branch from) and the public/token domain a fork's editor mints
/// over. Each [`SharedCard::fork_for`] hands a principal its own [`CardEditor`] —
/// bounded by that principal's `held` — over a fresh clone of the seed view.
#[derive(Clone)]
pub struct SharedCard {
    /// The seed program (the shared prefix every fork branches from). Its
    /// `view_source` is the JSON of the seed [`ViewTree`].
    manifest: AppletManifest,
    /// The authority a gesture on this card requires (the authoring cap tooth a
    /// principal's `held` must satisfy to author).
    edit_authority: Requirement,
}

/// One principal's live fork of the shared card — its own [`CardEditor`] (bounded by
/// `held`) plus the principal's identity (`who`, the [`Author`] every patch on this
/// fork is attributed to). Two of these, forked from one [`SharedCard`], are the two
/// co-drivers.
pub struct CardFork {
    /// The principal authoring this fork — the blame identity its patches carry.
    pub who: Author,
    /// The editor over this principal's own clone of the card's view.
    pub editor: CardEditor,
}

impl CardFork {
    /// The fork's current view source (its document fold) — what the stitch folds.
    pub fn view_source(&self) -> String {
        self.editor.view_source()
    }

    /// Lift this fork's view-source document as a mergeable [`ProgramSource`] —
    /// the branch the stitch consumes. Re-seeded from the fork's own (already-driven)
    /// view source under its principal, so the stitch sees this principal's reading.
    fn as_branch(&self) -> ProgramSource {
        ProgramSource::seed(self.who, &self.view_source())
    }
}

/// The outcome of stitching two co-drivers' forks — the merged reading of the shared
/// card's view, surfaced as [`dregg_doc`] segments so a caller can ask whether the
/// two principals' edits folded clean (both kept) or collided (a resolvable conflict).
#[derive(Clone, Debug)]
pub struct CardStitch {
    /// The merged rendered view (clean runs + any first-class conflict regions).
    pub rendered: Rendered,
}

impl CardStitch {
    /// **Stitch two driven view-sources** (each branched from a shared seed prefix) by
    /// the `dregg_doc` pushout — the string-driven core both [`SharedCard::stitch`] (the
    /// local, two-live-fork path) and the DISTRIBUTED carry
    /// (`starbridge_v2::distributed_card`, where the two sources arrive over an instance
    /// boundary as a card-fork envelope) delegate to.
    ///
    /// Both branches re-root on the SAME `seed` (authored neutrally as `Author(0)`), so
    /// the pushout sees a real common ancestor: disjoint edits fold CLEAN (both kept); an
    /// overlapping edit (both principals touched the same node) surfaces a first-class
    /// [`dregg_doc::ConflictRegion`] (two attributed, live alternatives — never a silent
    /// last-writer-wins). `who_a`/`who_b` are the two principals' blame identities.
    pub fn from_sources(
        seed: &str,
        who_a: Author,
        driven_a: &str,
        who_b: Author,
        driven_b: &str,
    ) -> CardStitch {
        let seed_author = Author(0);
        let mut branch_a = ProgramSource::seed(seed_author, seed);
        branch_a.edit(who_a, driven_a);
        let mut branch_b = ProgramSource::seed(seed_author, seed);
        branch_b.edit(who_b, driven_b);
        // The pushout: fold B's divergent patches into A's branch (a conflict is a
        // first-class region, not a failure — see `ProgramSource::merge`).
        CardStitch {
            rendered: branch_a.merge(&branch_b),
        }
    }

    /// True iff the two principals' edits collided on the same node — surfaced as a
    /// first-class [`dregg_doc::ConflictRegion`] antichain (NOT a silent overwrite).
    pub fn has_conflict(&self) -> bool {
        self.rendered.has_conflict()
    }

    /// The flat marked rendering — clean content, with any conflict shown as its two
    /// attributed alternatives between markers (the legible "two people wrote this
    /// differently — here's both" face). Used by callers/tests to read the merge.
    pub fn marked(&self) -> String {
        self.rendered.to_marked_string()
    }

    /// True iff `needle` appears in some live alternative of some conflict region (so
    /// a true-conflict caller can confirm BOTH collided readings survived as touchable
    /// alternatives, attributed — the loser is never hidden).
    pub fn conflict_carries(&self, needle: &str) -> bool {
        self.rendered
            .conflicts()
            .any(|c| c.alternatives.iter().any(|a| a.text.contains(needle)))
    }
}

impl SharedCard {
    /// **Seed a shared card.** Build the card's seed view-tree (a labelled counter:
    /// one text node + one `inc` button bound to a real affordance) and capture it as
    /// the manifest both principals fork from. `edit_authority` is the authoring cap a
    /// fork's `held` must satisfy.
    pub fn seed(edit_authority: Requirement) -> Self {
        let seed_view = ViewTree::VStack {
            children: vec![
                ViewTree::Text {
                    props: crate::card_editor::TextProps {
                        text: "shared counter".into(),
                    },
                },
                ViewTree::Bind {
                    props: crate::card_editor::BindProps {
                        slot: COUNT_SLOT,
                        label: "count".into(),
                    },
                },
            ],
        };
        let manifest = AppletManifest {
            seed_fields: vec![(COUNT_SLOT, 0)],
            affordances: vec![AffordanceSpec {
                name: "inc".into(),
                required: edit_authority.clone(),
                op: ApplyOp::AddToSlot { slot: COUNT_SLOT },
            }],
            // The seed applet is mounted at ROOT: it must clear its own affordances
            // so the seeded card is immediately fireable by its author. This used to
            // read `edit_authority`, which made the cap tooth `is_attenuation(X, X)` —
            // true by construction. The two are now different types, so the held
            // authority has to be named.
            held: AuthRequired::None,
            view_source: seed_view.to_json(),
        };
        SharedCard {
            manifest,
            edit_authority,
        }
    }

    /// **Rebuild a shared card from a carried seed view-source.** The distributed
    /// twin of [`SharedCard::seed`]: where `seed` bakes the fixed counter view, this
    /// reconstitutes the SAME shared card a peer minted — from the exact
    /// `seed_view_source` string that crossed an instance boundary (a card-fork
    /// envelope) — so a second principal on a DIFFERENT instance can take its own
    /// [`CardFork`] over the identical seed prefix and stitch faithfully.
    ///
    /// The seed view IS the carried source verbatim; the model/affordances are seeded
    /// to the shared card's standard counter shape (the seed both peers branch from),
    /// so a fork the receiver hands a principal re-folds, fires, and STITCHES against
    /// the originator's fork by the same `dregg_doc` pushout (the carried seed is the
    /// real common ancestor → disjoint edits fold clean, an overlap is a
    /// [`dregg_doc::ConflictRegion`]). `edit_authority` is the authoring cap a fork's
    /// `held` must satisfy (carried alongside the seed in the envelope).
    pub fn seed_from_source(edit_authority: Requirement, seed_view_source: &str) -> Self {
        let manifest = AppletManifest {
            seed_fields: vec![(COUNT_SLOT, 0)],
            affordances: vec![AffordanceSpec {
                name: "inc".into(),
                required: edit_authority.clone(),
                op: ApplyOp::AddToSlot { slot: COUNT_SLOT },
            }],
            held: AuthRequired::None,
            view_source: seed_view_source.to_string(),
        };
        SharedCard {
            manifest,
            edit_authority,
        }
    }

    /// The seed view source (the shared prefix both forks branch from).
    pub fn seed_view_source(&self) -> &str {
        &self.manifest.view_source
    }

    /// **Hand principal `who` its own fork** of the shared card — a [`CardEditor`]
    /// over a fresh clone of the seed view, bounded by the principal's `held`
    /// authority. The fork shares the seed view as its common prefix; the principal
    /// then drives its own divergent edits. A principal whose `held` does not satisfy
    /// the card's `edit_authority` can take the fork but every [`CardEditor::edit_view`]
    /// it attempts is refused in-band (the cap tooth) — so an unauthorized co-driver
    /// contributes no patch to the stitch.
    pub fn fork_for(&self, who: Author, held: AuthRequired) -> CardFork {
        // Each fork mints its OWN applet-cell (a distinct sovereign cell per principal,
        // the deep-clone the membrane fork would carry), seeded from the shared
        // manifest, so a fire on one fork never touches the other.
        let card = mint_seed_applet(&self.manifest, who, held.clone());
        let editor = CardEditor::adopt(
            card,
            self.manifest.clone(),
            who,
            held,
            self.edit_authority.clone(),
        );
        CardFork { who, editor }
    }

    /// **STITCH two co-drivers' forks** by the `dregg_doc` pushout. Folds fork `a`'s
    /// and fork `b`'s divergent `view_source` histories (each branched from the shared
    /// seed prefix) into one merged reading. Disjoint edits fold CLEAN (both kept); an
    /// overlapping edit (both principals touched the same node) surfaces as a
    /// first-class [`dregg_doc::ConflictRegion`] — two attributed, live alternatives,
    /// never a silent last-writer-wins.
    ///
    /// The seed is the shared prefix: `a`'s branch is taken as the base (re-rooted on
    /// the seed) and `b`'s divergent patches are stitched in, so the merge is symmetric
    /// in *content* (both readings are surfaced) while attributing each side.
    pub fn stitch(&self, a: &CardFork, b: &CardFork) -> CardStitch {
        let _ = b.as_branch(); // keep the branch-shape API exercised/honest
                               // Delegate to the string-driven core: the stitch consumes exactly the shared
                               // seed prefix + each principal's driven view-source fold. (The same three
                               // strings a card-fork envelope carries across an instance boundary — so the
                               // DISTRIBUTED stitch is byte-identical to this local one; see
                               // `starbridge_v2::distributed_card`.)
        CardStitch::from_sources(
            self.seed_view_source(),
            a.who,
            &a.view_source(),
            b.who,
            &b.view_source(),
        )
    }
}

/// Mint the seed applet-cell for a fork: a fresh sovereign cell seeded from the shared
/// manifest's model + affordances, under principal `who`'s `held` authority. A distinct
/// cell per principal (the per-fork deep clone), so each principal drives its own.
fn mint_seed_applet(manifest: &AppletManifest, who: Author, held: AuthRequired) -> Applet {
    // A per-principal public key / token domain (derived from the author id) so the two
    // forks are genuinely distinct sovereign cells, not aliases of one.
    let mut pk = [0u8; 32];
    pk[..8].copy_from_slice(&who.0.to_le_bytes());
    let token = blake3::hash(b"coauthored-card").into();

    let seed_fields: Vec<(Slot, dregg_cell::state::FieldElement)> = manifest
        .seed_fields
        .iter()
        .map(|(slot, v)| (*slot, pack_u64(*v)))
        .collect();
    let affordances: Vec<Affordance> = manifest
        .affordances
        .iter()
        .map(|spec| Affordance {
            name: spec.name.clone(),
            required: spec.required.clone(),
            apply: spec.op.clone().into_closure(),
        })
        .collect();
    Applet::mint(pk, token, &seed_fields, affordances, held)
}

/// Apply a view edit on a fork, surfacing the cap-tooth refusal as the caller's error
/// (a convenience the tests use to assert the unauthorized-co-driver path).
pub fn drive_view(fork: &mut CardFork, patch: ViewPatch) -> Result<ViewEdit, EditError> {
    fork.editor.edit_view(patch)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The authoring authority the shared card requires, and a principal that holds it.
    fn authority() -> Requirement {
        Requirement::Root
    }

    /// Principal A's identity. Principal B's identity. Distinct authors → distinct
    /// blame, distinct sovereign cells.
    const ALICE: Author = Author(0xA);
    const BOB: Author = Author(0xB);

    #[test]
    fn two_principals_clean_merge_keeps_both_edits() {
        // ONE shared card; TWO principals each take a fork bounded by their own held.
        let card = SharedCard::seed(authority());
        let mut a = card.fork_for(ALICE, AuthRequired::None);
        let mut b = card.fork_for(BOB, AuthRequired::None);

        // A RELABELS the card's title (a real receipted patch on A's own view doc).
        let edit_a = drive_view(
            &mut a,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice's counter".into(),
            },
        )
        .expect("A is authorized to author the card");
        // The edit is a RECEIPTED patch: the provenance turn advanced A's chain, and
        // blame attributes the new view to A.
        assert!(
            edit_a.receipt.turn_hash != [0u8; 32],
            "A's view edit left a real provenance receipt"
        );
        assert!(
            edit_a
                .tree
                .walk()
                .iter()
                .any(|n| n.label() == Some("alice's counter")),
            "A's fork re-folded with the relabel: {:?}",
            edit_a.tree
        );

        // B ADDS A BUTTON (a DISJOINT edit — different node) on B's own view doc.
        let edit_b = drive_view(
            &mut b,
            ViewPatch::AddButton {
                label: "increment".into(),
                turn: "inc".into(),
                arg: 1,
            },
        )
        .expect("B is authorized to author the card");
        assert!(
            edit_b.tree.has_button_for("inc"),
            "B's fork re-folded with the new button: {:?}",
            edit_b.tree
        );

        // STITCH the two forks by pushout. Disjoint edits → CLEAN merge.
        let stitch = card.stitch(&a, &b);
        assert!(
            !stitch.has_conflict(),
            "disjoint co-drives fold clean: {}",
            stitch.marked()
        );

        // BOTH principals' edits survive the merge — co-drive, not last-writer-wins.
        let merged = stitch.marked();
        assert!(
            merged.contains("alice's counter"),
            "A's relabel kept in the stitched view: {merged}"
        );
        assert!(
            merged.contains("increment") || merged.contains("\"inc\""),
            "B's added button kept in the stitched view: {merged}"
        );
    }

    #[test]
    fn two_principals_true_conflict_surfaces_a_resolvable_region() {
        // ONE shared card; TWO principals each fork it.
        let card = SharedCard::seed(authority());
        let mut a = card.fork_for(ALICE, AuthRequired::None);
        let mut b = card.fork_for(BOB, AuthRequired::None);

        // BOTH relabel the SAME node, differently — the canonical overlapping edit.
        drive_view(
            &mut a,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice's title".into(),
            },
        )
        .expect("A authorized");
        drive_view(
            &mut b,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "bob's title".into(),
            },
        )
        .expect("B authorized");

        // STITCH: the collision is a FIRST-CLASS conflict region, not a silent
        // overwrite — both attributed alternatives survive as a touchable antichain.
        let stitch = card.stitch(&a, &b);
        assert!(
            stitch.has_conflict(),
            "two edits to the same node MUST surface a conflict: {}",
            stitch.marked()
        );
        assert!(
            stitch.conflict_carries("alice's title"),
            "A's reading survives as a live alternative: {}",
            stitch.marked()
        );
        assert!(
            stitch.conflict_carries("bob's title"),
            "B's reading survives as a live alternative (loser never hidden): {}",
            stitch.marked()
        );
    }

    #[test]
    fn an_unauthorized_co_driver_contributes_no_patch_the_cap_tooth() {
        // Authoring this card requires the unrestricted `None` authority (the most
        // powerful in the lattice — `is_attenuation` admits a gesture only when the
        // card's `edit_authority` is narrower-or-equal to the principal's `held`).
        // A holds `None` and clears it; B holds only the stricter `Signature` and so
        // is refused in-band — no patch, no receipt (the cap-bounded tooth).
        let card = SharedCard::seed(Requirement::Root);
        // A HOLDS the required (broadest) authority; B holds only a narrower one.
        let mut a = card.fork_for(ALICE, AuthRequired::None);
        let mut b = card.fork_for(BOB, AuthRequired::Signature);

        drive_view(
            &mut a,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice owns this".into(),
            },
        )
        .expect("A holds the authoring authority");

        let refused = drive_view(
            &mut b,
            ViewPatch::AddButton {
                label: "sneak".into(),
                turn: "inc".into(),
                arg: 1,
            },
        );
        assert!(
            matches!(refused, Err(EditError::Unauthorized)),
            "the unauthorized co-driver's edit is refused in-band by the cap tooth"
        );

        // B's fork is unchanged (its view is still the seed prefix) — its edit never
        // reached the document, so the stitch carries only A's authorized reading.
        assert_eq!(
            b.view_source(),
            card.seed_view_source(),
            "the refused co-driver's view document never advanced"
        );
        let stitch = card.stitch(&a, &b);
        assert!(
            !stitch.has_conflict(),
            "no conflict — B contributed nothing: {}",
            stitch.marked()
        );
        assert!(
            stitch.marked().contains("alice owns this"),
            "only A's authorized edit is in the merged view: {}",
            stitch.marked()
        );
    }
}
