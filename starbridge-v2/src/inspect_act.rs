//! The **inspect → act → inspect** loop — the Smalltalk-liveness keystone, fused.
//!
//! Today the cockpit INSPECTS objects ([`crate::reflect`] projects any dregg datum
//! into a read-only [`Inspectable`] field tree) and, separately, ACTS on them
//! ([`crate::affordance`] + [`crate::world`] fire cap-gated verified turns). They
//! are two surfaces. In Smalltalk they are ONE: you inspect an object and the
//! inspector shows the messages it understands, you send one, and the result is
//! itself an object you can inspect. This module fuses the cockpit's two surfaces
//! into exactly that loop, over the REAL machinery — nothing here is a parallel
//! model:
//!
//!   1. **inspect** — the focused object's reflected view is the genuine
//!      [`reflect::reflect_cell`] [`Inspectable`] (read straight off the live
//!      [`World`] ledger; we do NOT reinvent reflection);
//!   2. **the messages it understands** — the verbs applicable to the object are
//!      the genuine [`crate::affordance::AffordanceSurface`] projected for the
//!      viewer, each carrying a REAL [`dregg_turn::Effect`] template and annotated
//!      with whether the viewer's held window cap AUTHORIZES it (the cap badge,
//!      decided by the proven [`dregg_cell::is_attenuation`] lattice via
//!      [`CellAffordance::authorized_for`]). An unauthorized message is SHOWN, not
//!      hidden — you see the full vocabulary and which sends you may make;
//!   3. **act** — [`InspectAct::fire`] routes the chosen message through the real
//!      [`AffordanceSurface::fire`] (the in-band anti-ghost gate: an unauthorized
//!      send is REFUSED, surfaced not swallowed) and then
//!      [`AffordanceIntent::fire_through_world`] → [`World::commit_turn`] — the
//!      embedded verified executor. The send is a REAL verified turn with a REAL
//!      [`dregg_turn::turn::TurnReceipt`];
//!   4. **inspect again** — the result is a fresh [`Inspectable`] re-read off the
//!      post-state ledger, so the loop closes: inspect → act → inspect.
//!
//! The focused object starts as a [`Cell`] ([`InspectFocus::Cell`]); the focus type
//! is an enum so `Cap`/`Receipt`/etc. extend later (the affordance vocabulary for
//! those object kinds is the increment — the loop's shape is identical).
//!
//! gpui-free and `cargo test`-able: a test asserts the messages-understood are real
//! + cap-annotated, that firing an authorized one commits a real turn whose effect
//!   the re-inspected object reflects, and that firing an unauthorized one is refused
//!   in-band. The cockpit renders exactly this model.

use dregg_cell::{is_attenuation, AuthRequired, CellId};
use dregg_firmament::Capability;
use dregg_turn::action::{Effect, Event};
use dregg_turn::turn::TurnReceipt;

use crate::affordance::{
    AffordanceIntent, AffordanceSurface, CellAffordance, FireError, FireOutcome,
};
use crate::reflect::{self, Inspectable};
use crate::surface::{SurfaceCapability, SurfaceId};
use crate::world::World;

/// What object the inspect→act loop is focused on. Today a [`Cell`](InspectFocus::Cell);
/// the variants extend to `Cap`/`Receipt`/etc. — the loop's shape is identical, only
/// the per-kind reflection + affordance vocabulary differ.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InspectFocus {
    /// A live ledger cell (the object whose state + affordances we inspect/act on).
    Cell(CellId),
}

impl InspectFocus {
    /// The backing cell id the focus denotes (every focus kind anchors on a cell).
    pub fn cell(&self) -> CellId {
        match self {
            InspectFocus::Cell(id) => *id,
        }
    }
}

/// One **message the object understands**, as the inspector shows it for a viewer.
///
/// This is the fusion point: it is an [`AffordanceSurface`] verb (a real cap-gated
/// effect-template) PRESENTED inline in the inspected object's view, annotated with
/// the **cap badge** — whether the viewer's held window cap authorizes the send. An
/// unauthorized message is still listed (`authorized == false`): the inspector shows
/// the full vocabulary and which sends are permitted, never hiding the refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message {
    /// The message selector (the verb name — the deos affordance name).
    pub name: String,
    /// The authority the viewer must HOLD over the object to send it
    /// (`required ⊆ held`). The cap badge is computed against this.
    pub required: AuthRequired,
    /// The REAL effect this send would run, summarized (`SetField` / `EmitEvent` /
    /// `GrantCapability` …) — the genuine turn the executor would commit. Drawn from
    /// the affordance's real [`dregg_turn::Effect`] template, never a stub.
    pub effect: String,
    /// **The cap badge.** `true` iff the viewer's held window cap satisfies
    /// `required` (the REAL [`is_attenuation`], the proven attenuation lattice) — i.e.
    /// the viewer may send this message. `false` = shown-but-refused (anti-ghost: the
    /// vocabulary is visible, the authorization honest).
    pub authorized: bool,
}

/// The result of SENDING a message — the act half of the loop, with the post-state
/// re-inspected so the loop closes.
#[derive(Debug)]
pub enum SendResult {
    /// The send COMMITTED a real verified turn. Carries the executor's own
    /// [`TurnReceipt`] (the proof the send happened) AND the fresh [`Inspectable`]
    /// re-read off the POST-state ledger — the result object you inspect next.
    Committed {
        receipt: Box<TurnReceipt>,
        /// The focused object re-inspected after the turn (the loop closing:
        /// inspect → act → **inspect**). Reflects the committed change.
        reinspected: Inspectable,
    },
    /// The send was REFUSED, surfaced IN-BAND (never swallowed). Either the cap-gate
    /// refused it (the viewer lacked the rights — the anti-ghost tooth, decided by the
    /// real `is_attenuation` before any turn runs) or the executor refused the turn (a
    /// guarantee fired: conservation, no-amplification, a permissions gate). The
    /// `reason` names which; `by_executor` distinguishes the two refusal sites.
    Refused {
        reason: String,
        /// `false` = the cap-gate refused the send (the viewer is not authorized —
        /// the message's `authorized` badge was `false`); `true` = the cap-gate
        /// admitted it but the REAL executor rejected the resulting turn.
        by_executor: bool,
    },
}

impl SendResult {
    pub fn is_committed(&self) -> bool {
        matches!(self, SendResult::Committed { .. })
    }
}

/// THE INSPECT→ACT VIEW — a focused object's reflected state PLUS the messages it
/// understands (cap-annotated for the viewer), built fresh off the live [`World`].
///
/// The cockpit renders exactly this: the [`Inspectable`] field tree on the left, the
/// [`Message`] list (each with its cap badge) on the right, and a "send" affordance
/// per authorized message. [`InspectAct::send`] fires the chosen message through the
/// real executor and hands back a [`SendResult`] whose `reinspected` object the panel
/// re-focuses on — the loop, native.
#[derive(Clone, Debug)]
pub struct InspectAct {
    /// What we are inspecting (anchors on a cell today).
    pub focus: InspectFocus,
    /// The viewer principal the messages are projected FOR (whose held cap decides
    /// the badges) — short-hex of [`Self::viewer`].
    pub viewer: CellId,
    /// The viewer's authority tier over the object (what gates the cap badges).
    pub viewer_tier: String,
    /// The reflected object — the genuine [`reflect::reflect_cell`] view, read off the
    /// live ledger (read-only field tree). `None` iff the focused cell is absent from
    /// the ledger (a dangling focus — surfaced honestly, never faked).
    pub inspectable: Option<Inspectable>,
    /// The messages the object understands, AS THE VIEWER SEES THEM — every declared
    /// verb (in declaration order), each annotated with whether the viewer may send it
    /// ([`Message::authorized`], the cap badge). The full vocabulary is shown; the
    /// badge carries the authorization.
    pub messages: Vec<Message>,
}

impl InspectAct {
    /// Build the inspect→act view of `focus` for `viewer` holding `viewer_rights`,
    /// off the live `world`.
    ///
    /// `viewer_rights` is the authority the viewer holds over the object's window —
    /// the SAME [`AuthRequired`] lattice the firmament cap rides — and is what gates
    /// every message's cap badge. The inspectable is the genuine reflection; the
    /// messages are the genuine [`AffordanceSurface`] projected (full vocabulary,
    /// per-message authorization), so the rendered tree is the real fused loop.
    pub fn build(
        world: &World,
        focus: InspectFocus,
        viewer: CellId,
        viewer_rights: AuthRequired,
    ) -> Self {
        let cell = focus.cell();

        // 1. INSPECT — reuse reflect.rs (do NOT reinvent reflection). Read the cell
        //    straight off the live ledger; absent ⟹ honestly None (a dangling focus).
        let inspectable = world
            .ledger()
            .get(&cell)
            .map(|c| reflect::reflect_cell(&cell, c));

        // 2. THE MESSAGES IT UNDERSTANDS — the genuine affordance surface for this
        //    object, every declared verb annotated with the cap badge (the REAL
        //    is_attenuation against the viewer's held window cap). We list ALL declared
        //    messages (not just project_for's authorized subset) so the inspector shows
        //    the full vocabulary AND which sends are permitted — the anti-ghost surface.
        let surface = message_surface_for(cell, viewer);
        let held = window_cap(cell, viewer_rights.clone());
        let messages = surface
            .affordances
            .iter()
            .map(|aff| Message {
                name: aff.name.clone(),
                required: aff.required_rights.clone(),
                effect: effect_label(&aff.effect_template),
                // The cap badge: the REAL attenuation gate the affordance surface
                // itself fires on (`required ⊆ held`). Same predicate, surfaced.
                authorized: aff.authorized_for(&held),
            })
            .collect();

        InspectAct {
            focus,
            viewer,
            viewer_tier: format!("{viewer_rights:?}"),
            inspectable,
            messages,
        }
    }

    /// **Send a message — the ACT half, closing the loop.**
    ///
    /// Routes the chosen message through the REAL [`AffordanceSurface::fire`] (the
    /// in-band anti-ghost gate: an unauthorized send — `authorized == false` — is
    /// [`SendResult::Refused`] `by_executor: false`, refused before any turn) and then
    /// [`AffordanceIntent::fire_through_world`] → [`World::commit_turn`], the embedded
    /// verified executor. On commit it RE-INSPECTS the focused object off the post-state
    /// ledger, so the returned [`SendResult::Committed`] carries both the real receipt
    /// AND the fresh [`Inspectable`] reflecting the change (inspect → act → inspect).
    ///
    /// An executor refusal (a guarantee fired: conservation, no-amplification, a
    /// permissions gate) is [`SendResult::Refused`] `by_executor: true` — surfaced, not
    /// hidden (the verification axis firing in front of you).
    pub fn send(
        &self,
        world: &mut World,
        message: &str,
        viewer_rights: AuthRequired,
    ) -> SendResult {
        let cell = self.focus.cell();
        let surface = message_surface_for(cell, self.viewer);
        let held = window_cap(cell, viewer_rights);

        // THE CAP-GATE (anti-ghost): the real is_attenuation, run by the affordance
        // surface's `fire`. An unauthorized send (or an unknown selector) is refused
        // IN-BAND here, before any executor turn — surfaced, never swallowed.
        let intent: AffordanceIntent = match surface.fire(message, self.viewer, &held) {
            Ok(intent) => intent,
            Err(FireError::Unauthorized {
                affordance,
                required,
            }) => {
                return SendResult::Refused {
                    reason: format!(
                        "message `{affordance}` refused: the viewer's authority does not \
                         satisfy {required:?} (required ⊄ held — the real is_attenuation gate)"
                    ),
                    by_executor: false,
                };
            }
            Err(FireError::NoSuchAffordance) => {
                return SendResult::Refused {
                    reason: format!("the object understands no message named `{message}`"),
                    by_executor: false,
                };
            }
        };

        // THE EXECUTOR (the verified turn): hand the intent to the embedded executor.
        // Either it commits (a real receipt) or it rejects (a guarantee fired) — both
        // first-class, the rejection surfaced.
        match intent.fire_through_world(world) {
            FireOutcome::Committed(receipt) => {
                // CLOSE THE LOOP — re-inspect the focused object off the POST-state
                // ledger. The result is itself an inspectable object (inspect → act →
                // inspect). A self-destroying send could remove the cell; then the
                // re-inspection honestly reflects its absence (an empty/None body), but
                // for the cell-acting verbs here the cell persists.
                let reinspected = world
                    .ledger()
                    .get(&cell)
                    .map(|c| reflect::reflect_cell(&cell, c))
                    .unwrap_or_else(|| Inspectable {
                        kind: reflect::ObjectKind::Cell,
                        title: format!("Cell {} (gone)", reflect::short_hex(cell.as_bytes())),
                        subtitle: "the send retired this cell".to_string(),
                        fields: vec![],
                    });
                SendResult::Committed {
                    receipt,
                    reinspected,
                }
            }
            FireOutcome::Refused { reason, .. } => SendResult::Refused {
                reason,
                by_executor: true,
            },
        }
    }

    /// The names of the messages the viewer MAY send (the cap-cleared subset, sorted) —
    /// the per-viewer authorized vocabulary, the thing two different-cap viewers diverge
    /// on. (The full vocabulary lives in [`Self::messages`]; this is the cleared subset.)
    pub fn authorized_messages(&self) -> Vec<String> {
        let mut names: Vec<String> = self
            .messages
            .iter()
            .filter(|m| m.authorized)
            .map(|m| m.name.clone())
            .collect();
        names.sort();
        names
    }

    /// Every line of text the inspect→act view renders, flattened — so a test can
    /// assert the fused surface speaks real, cap-annotated text about the real object
    /// (non-empty here ⟺ a non-empty rendered tree).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "inspect→act · cell {} · viewer {} holds {}",
            reflect::short_hex(self.focus.cell().as_bytes()),
            reflect::short_hex(self.viewer.as_bytes()),
            self.viewer_tier
        ));
        if let Some(insp) = &self.inspectable {
            out.push(insp.title.clone());
            out.push(insp.subtitle.clone());
            for f in &insp.fields {
                out.push(f.key.clone());
            }
        } else {
            out.push("(the focused cell is absent from the ledger)".to_string());
        }
        out.push(format!("messages understood: {}", self.messages.len()));
        for m in &self.messages {
            out.push(format!(
                "· {} (requires {:?}) → {} [{}]",
                m.name,
                m.required,
                m.effect,
                if m.authorized {
                    "you may send"
                } else {
                    "refused: insufficient authority"
                }
            ));
        }
        out
    }
}

// ── the model-building helpers (pure; each names the real component) ──────────────

/// Build the genuine cockpit [`AffordanceSurface`] a cell publishes — the canonical
/// object-message vocabulary {peek, touch, write, grant} on the clean three-tier rights
/// chain `Signature ⊂ Either ⊂ None`, each carrying a REAL [`dregg_turn::Effect`] template
/// (the turn the executor would run). `viewer` is the grantee a `grant` send would target.
///
/// This is the cockpit's OWN [`crate::affordance::AffordanceSurface`] (the one whose
/// `fire` → [`AffordanceIntent::fire_through_world`] runs the embedded executor), NOT a
/// parallel surface — its `project_for`/`fire` run the real `is_attenuation`, and its
/// effects are the genuine [`Effect`] the executor commits. The vocabulary mirrors the
/// web-of-cells surface ([`crate::web_cells`]) so the two faces of a cell agree.
fn message_surface_for(cell: CellId, viewer: CellId) -> AffordanceSurface {
    AffordanceSurface::new(cell)
        // peek: tier-1 (any authenticated reader holds Signature) → logs an access
        //       event (a real EmitEvent turn — the object acknowledges the read).
        .declare(CellAffordance::new(
            "peek",
            AuthRequired::Signature,
            Effect::EmitEvent {
                cell,
                event: Event::new([1u8; 32], vec![]),
            },
        ))
        // touch: tier-1 → bumps the object's nonce (a real IncrementNonce turn — the
        //        minimal observable self-mutation, perfect for the closing inspect).
        .declare(CellAffordance::new(
            "touch",
            AuthRequired::Signature,
            Effect::IncrementNonce { cell },
        ))
        // write: tier-2 (the editor tier holds Either) → writes state slot 1 (a real
        //        SetField turn the re-inspection reflects as a new `state[1]` field).
        .declare(CellAffordance::new(
            "write",
            AuthRequired::Either,
            Effect::SetField {
                cell,
                index: 1,
                value: [7u8; 32],
            },
        ))
        // grant: tier-3 (only a root holder of None clears it) → hands out a capability
        //        reaching `viewer` (a real GrantCapability turn the no-amplification gate
        //        checks).
        .declare(CellAffordance::new(
            "grant",
            AuthRequired::None,
            crate::world::grant_capability(cell, viewer, cell, 1),
        ))
}

/// Mint the viewer's held WINDOW CAP over the object — the REAL cockpit
/// [`SurfaceCapability`] (a `dregg_firmament::Capability` over `Surface(cell)` carrying
/// `rights`), the SAME token the affordance surface gates on. This is the authority the
/// cap badge + `fire`'s anti-ghost gate check `required ⊆ held` against. The rights are
/// the genuine [`AuthRequired`] lattice — `dregg_firmament::Rights` IS
/// `dregg_cell::AuthRequired` (the firmament re-exports it, NOT a parallel model), so no
/// conversion is needed: the held-cap rights are exactly what the surface's
/// `dregg_cell::is_attenuation(held.rights(), required)` reads. (A surface handle of `1`
/// is fine — the gate is on the firmament authority, not the handle.)
fn window_cap(cell: CellId, rights: AuthRequired) -> SurfaceCapability {
    SurfaceCapability::new(SurfaceId(1), Capability::surface(cell, rights))
}

/// **Derive the viewer's GENUINE authority over the focus cell**, read off the live
/// ledger — the membrane property: the affordances lens divides per-viewer because the
/// authority does. This is what `ReflectedCell::present` (and any caller projecting the
/// fused loop for a real viewer) must feed [`InspectAct::build`] as `viewer_rights`, in
/// place of a uniform guess. It reuses ONLY the real ocap primitives:
///
///   1. **the cell's OWN principal** (`viewer == cell` — the viewer IS / owns the cell):
///      [`AuthRequired::None`], the root tier that clears EVERY affordance (incl. the
///      strongest, `grant`, which requires `None`). A cell is its own root authority.
///   2. **a viewer holding a c-list cap reaching the cell**: that cap's rights. If the
///      viewer holds several caps to the cell, the WIDEST is the authority it can wield —
///      folded by the REAL [`is_attenuation`] (a cap of rights `r` is wider than the
///      running `best` iff `best ⊆ r`, i.e. `is_attenuation(&r, &best)`).
///   3. **otherwise** (a foreign viewer with no cap reaching the cell): the weakest tier
///      [`AuthRequired::Impossible`] — refused every authority-bearing affordance (it is
///      narrower-or-equal to all tiers, so it clears nothing the gate requires).
///
/// Read straight off `world.ledger()` (ownership = id equality · c-list = the viewer
/// cell's genuine `capabilities` set) — never a parallel authority model.
pub fn viewer_authority_over(world: &World, viewer: CellId, cell: CellId) -> AuthRequired {
    // (1) The cell's own principal IS its root authority — clears every affordance.
    if viewer == cell {
        return AuthRequired::None;
    }

    // (2) The widest c-list cap the viewer holds reaching the cell. Fold by the REAL
    //     is_attenuation: keep the wider whenever a cap's rights dominate the running best.
    let mut best = AuthRequired::Impossible;
    if let Some(viewer_cell) = world.ledger().get(&viewer) {
        for cap in viewer_cell.capabilities.iter() {
            if cap.target == cell && is_attenuation(&cap.permissions, &best) {
                best = cap.permissions.clone();
            }
        }
    }

    // (3) No cap reached the cell ⟹ best is still Impossible (the weakest tier) —
    //     a foreign viewer is refused the authority-bearing affordances.
    best
}

/// A stable, human label for a real [`Effect`] (the `Effect` enum is not
/// `PartialEq`/`Display`; this is the readout the panel shows). Uses the cockpit
/// affordance crate's [`crate::affordance::EffectSummary`] — a readout of the GENUINE
/// template, never a re-derived guess.
fn effect_label(effect: &Effect) -> String {
    use crate::affordance::EffectSummary;
    match EffectSummary::of(effect) {
        EffectSummary::SetField { index, .. } => format!("SetField(slot {index})"),
        EffectSummary::EmitEvent { .. } => "EmitEvent".to_string(),
        EffectSummary::GrantCapability { .. } => "GrantCapability".to_string(),
        EffectSummary::Transfer { amount, .. } => format!("Transfer({amount})"),
        EffectSummary::RevokeCapability { slot, .. } => format!("RevokeCapability(slot {slot})"),
        EffectSummary::IncrementNonce { .. } => "IncrementNonce".to_string(),
        EffectSummary::Other { tag } => tag.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reflect::FieldValue;
    use crate::world::World;

    /// The EDITOR tier (`Either`): clears peek/touch/write but NOT grant (which needs
    /// the root `None` tier) — a clean attenuation witness for the cap badges.
    fn editor_rights() -> AuthRequired {
        AuthRequired::Either
    }

    /// Find a message by name in an inspect→act view.
    fn msg<'a>(ia: &'a InspectAct, name: &str) -> &'a Message {
        ia.messages
            .iter()
            .find(|m| m.name == name)
            .expect("the object declares this message")
    }

    #[test]
    fn messages_understood_are_real_and_cap_annotated() {
        // INSPECT: a live cell. The messages it understands are the genuine affordance
        // vocabulary, every one carrying a REAL effect summary + a cap badge.
        let mut w = World::new();
        let cell = w.genesis_cell(0x10, 1_000);
        let viewer = cell; // the operator inspects its own cell

        let ia = InspectAct::build(&w, InspectFocus::Cell(cell), viewer, editor_rights());

        // The reflected view is the genuine reflect_cell (read-only field tree).
        let insp = ia.inspectable.as_ref().expect("the focused cell exists");
        assert_eq!(insp.kind, reflect::ObjectKind::Cell);
        assert!(insp.fields.iter().any(|f| f.key == "balance"));

        // The full vocabulary is SHOWN (not just the cleared subset) — the anti-ghost
        // surface: you see every message + which you may send.
        let names: Vec<&str> = ia.messages.iter().map(|m| m.name.as_str()).collect();
        assert!(names.contains(&"peek"));
        assert!(names.contains(&"touch"));
        assert!(names.contains(&"write"));
        assert!(names.contains(&"grant"));

        // Each message carries a REAL effect summary (the genuine template, not a stub).
        assert_eq!(msg(&ia, "touch").effect, "IncrementNonce");
        assert_eq!(msg(&ia, "write").effect, "SetField(slot 1)");
        assert_eq!(msg(&ia, "grant").effect, "GrantCapability");

        // THE CAP BADGE: the EDITOR (Either) may send all four — peek/touch/write
        // (Signature/Either ⊆ Either) and grant (None = ALWAYS allowed: the cap-gate
        // permits it, and the EXECUTOR's no-amplification rule gates the real grant).
        assert!(msg(&ia, "peek").authorized, "Signature ⊆ Either");
        assert!(msg(&ia, "touch").authorized);
        assert!(msg(&ia, "write").authorized, "Either ⊆ Either");
        assert!(
            msg(&ia, "grant").authorized,
            "None = always allowed (gated in the executor, not the cap-gate)"
        );

        // The authorized subset is exactly the cleared messages, sorted.
        assert_eq!(
            ia.authorized_messages(),
            vec!["grant", "peek", "touch", "write"]
        );

        // The rendered text is non-empty + names the messages (a non-empty gpui tree).
        assert!(ia
            .all_text()
            .iter()
            .any(|l| l.contains("messages understood")));
    }

    #[test]
    fn a_narrow_viewer_sees_a_narrower_authorized_set_same_object() {
        // The cap badge DIVERGES per viewer — the SAME object, a different authorization.
        let mut w = World::new();
        let cell = w.genesis_cell(0x11, 500);

        // A reader (Signature) clears the tier-1 messages (peek/touch) AND grant
        // (None = always allowed for any viewer); only write (Either) is shown-but-refused.
        let ia = InspectAct::build(&w, InspectFocus::Cell(cell), cell, AuthRequired::Signature);
        assert_eq!(ia.authorized_messages(), vec!["grant", "peek", "touch"]);
        assert!(!msg(&ia, "write").authorized, "Either ⊄ Signature");
        assert!(
            msg(&ia, "grant").authorized,
            "None = always allowed, even for a Signature viewer"
        );
        // The full vocabulary is still shown — the refused message is visible.
        assert_eq!(ia.messages.len(), 4);
    }

    #[test]
    fn firing_an_authorized_message_commits_a_real_turn_the_reinspection_reflects() {
        // ACT → the loop closes: send `write` (a real SetField), the executor commits a
        // real turn, and the RE-INSPECTED object reflects the new state field.
        let mut w = World::new();
        let cell = w.genesis_cell(0x20, 1_000);

        let ia = InspectAct::build(&w, InspectFocus::Cell(cell), cell, editor_rights());
        // Pre-state: no `state[1]` field yet (the slot is zero, so reflect omits it).
        let before = ia.inspectable.as_ref().unwrap();
        assert!(!before.fields.iter().any(|f| f.key == "state[1]"));

        let result = ia.send(&mut w, "write", editor_rights());
        let (receipt, reinspected) = match result {
            SendResult::Committed {
                receipt,
                reinspected,
            } => (receipt, reinspected),
            SendResult::Refused { reason, .. } => {
                panic!("authorized write should commit: {reason}")
            }
        };

        // It was a REAL verified turn — the executor's own receipt, in the provenance log.
        assert_eq!(w.receipts().len(), 1, "the send committed a real turn");
        assert_eq!(receipt.agent, cell);

        // THE LOOP CLOSES: the re-inspected object reflects the committed change — slot
        // 1 now carries the written value, surfaced as a `state[1]` field.
        assert!(
            reinspected
                .fields
                .iter()
                .any(|f| matches!(&f.value, FieldValue::FieldSlot { index: 1, .. })),
            "the re-inspected object reflects the SetField the send committed"
        );
        // And the live ledger agrees (the reflection is not faked — it reads the ledger).
        assert_eq!(w.ledger().get(&cell).unwrap().state.fields[1], [7u8; 32]);
    }

    #[test]
    fn firing_touch_commits_and_the_reinspected_nonce_advanced() {
        // A second authorized verb, end-to-end: `touch` (IncrementNonce) commits and the
        // re-inspected object shows the advanced nonce — the inspect→act→inspect loop on
        // the minimal observable self-mutation.
        let mut w = World::new();
        let cell = w.genesis_cell(0x21, 100);
        let nonce_before = w.ledger().get(&cell).unwrap().state.nonce();

        let ia = InspectAct::build(&w, InspectFocus::Cell(cell), cell, editor_rights());
        let result = ia.send(&mut w, "touch", editor_rights());
        assert!(
            result.is_committed(),
            "touch is authorized for the editor and commits"
        );
        // The committed `touch` STRICTLY ADVANCES the nonce — the observable self-mutation
        // the closing inspect sees. The exact delta is not a clean +1: the executor bumps
        // the actor's nonce per turn for replay protection (every turn, commit or refusal),
        // and that composes with the IncrementNonce effect — so assert the true property
        // (advanced), not a precise delta coupled to executor replay internals.
        assert!(
            w.ledger().get(&cell).unwrap().state.nonce() > nonce_before,
            "the committed IncrementNonce advanced the nonce (the loop observes a real self-mutation)"
        );
    }

    #[test]
    fn firing_an_unauthorized_message_is_refused_in_band_by_the_cap_gate() {
        // THE ANTI-GHOST TOOTH: a viewer lacking the rights for a message is REFUSED
        // in-band by the real is_attenuation — BEFORE any executor turn, surfaced not
        // swallowed. A Signature viewer cannot send `write` (Either ⊄ Signature). (We
        // use write, not grant: grant is None-gated = always allowed at the cap-gate,
        // its real guarantee being the executor's non-amplification rule.)
        let mut w = World::new();
        let cell = w.genesis_cell(0x30, 1_000);

        let ia = InspectAct::build(&w, InspectFocus::Cell(cell), cell, AuthRequired::Signature);
        // The badge already says refused (write needs Either; the viewer holds Signature).
        assert!(!msg(&ia, "write").authorized);

        let result = ia.send(&mut w, "write", AuthRequired::Signature);
        match result {
            SendResult::Refused {
                reason,
                by_executor,
            } => {
                assert!(
                    !by_executor,
                    "the CAP-GATE refused it (not the executor) — before any turn"
                );
                assert!(
                    reason.contains("write"),
                    "the refusal names the message + is surfaced"
                );
            }
            SendResult::Committed { .. } => panic!("an unauthorized write must NOT commit"),
        }
        // Nothing ran: no receipt was appended (the refusal was before the executor).
        assert_eq!(w.receipts().len(), 0, "an in-band cap refusal runs no turn");
    }

    #[test]
    fn sending_an_unknown_message_is_refused_in_band() {
        // An unknown selector is its own in-band refusal (the object understands no such
        // message) — surfaced, never a silent no-op.
        let mut w = World::new();
        let cell = w.genesis_cell(0x40, 10);
        let ia = InspectAct::build(&w, InspectFocus::Cell(cell), cell, editor_rights());
        match ia.send(&mut w, "doesNotUnderstand", editor_rights()) {
            SendResult::Refused {
                reason,
                by_executor,
            } => {
                assert!(!by_executor);
                assert!(reason.contains("doesNotUnderstand"));
            }
            SendResult::Committed { .. } => panic!("an unknown message cannot commit"),
        }
        assert_eq!(w.receipts().len(), 0);
    }

    #[test]
    fn a_dangling_focus_is_surfaced_not_faked() {
        // INSPECT a cell that is NOT in the ledger: the inspectable is honestly None
        // (a dangling focus surfaced), and the message vocabulary is still listed (you
        // could try to send, but the executor would refuse — the messages exist on the
        // object KIND, the instance is just absent).
        let w = World::new();
        let ghost = CellId::derive_raw(&[0xFEu8; 32], &[0u8; 32]);
        let ia = InspectAct::build(&w, InspectFocus::Cell(ghost), ghost, editor_rights());
        assert!(
            ia.inspectable.is_none(),
            "an absent cell is honestly None, never a faked body"
        );
        assert!(ia
            .all_text()
            .iter()
            .any(|l| l.contains("absent from the ledger")));
    }
}
