//! THE HANDS THAT AUTHOR — the confined agent's `create_card` / `edit_card` tools:
//! the agent does not just READ + FIRE the cockpit, it BUILDS the world it inhabits.
//! The ADOS dream closed — every authored card a receipted patch, cap-gated, confined.
//!
//! This is the authoring sibling of [`crate::run_js`] (the read+fire HANDS): the same
//! empowered-but-accountable-but-bounded model, now over the card graph.
//!
//!   * EMPOWERED — the agent AUTHORS cards: it mints a fresh card from a manifest
//!     ([`CardAuthoringTool::create_card`]) and patches an existing card's view-tree
//!     ([`CardAuthoringTool::edit_card`]) — the SAME [`CardEditor`](deos_js::CardEditor)
//!     gesture the human card-editor uses (add a button / add text / relabel), each a
//!     real verified turn leaving a provenance receipt + blame.
//!   * ACCOUNTABLE — the `create_card` / `edit_card` tool-call ITSELF is admitted by the
//!     [`HermesGateway`](crate::HermesGateway) as a normal scoped, rate-limited
//!     [`ToolGrant`](dregg_sdk::ToolGrant) (a metered, receipted accountability turn).
//!     Refused at the membrane ⇒ no card is authored at all. AND the authoring gesture
//!     itself leaves its own provenance receipt on the card's chain, attributed to the
//!     AGENT'S author (the blame). The agent acts as itself — the confused-deputy
//!     property.
//!   * BOUNDED at the cap-gate — the [`CardEditor`] mounts the agent's `held` authority
//!     against the card's `edit_authority` (the authoring cap tooth,
//!     [`dregg_cell::is_attenuation`]). A card the agent's `held` does not satisfy is
//!     refused IN-BAND ([`EditError::Unauthorized`]) — no patch, no receipt, no view
//!     change. This is the SAME gate a human authoring the card goes through; the agent
//!     gets no wider authority by being an agent. Over-reach refused, exactly as
//!     `run_js`'s fire over-reach is refused.
//!
//! The cap tooth + receipt + blame semantics these tools rely on are proven in
//! `deos-js/tests/card_editor.rs` (test (d): "the agent does it"); this file binds that
//! same code path behind the confined gateway, so the authoring is BOTH receipted-by-the-
//! editor AND metered-by-the-gateway.

use deos_js::card_editor::{CardEditor, EditError, ViewEdit, ViewPatch};
use deos_js::portable::{AppletManifest, PortableApplet};
use dregg_cell::AuthRequired;
use dregg_doc::Author;

use crate::acp::{PermissionOutcome, ToolCallRequest};
use crate::bridge::HermesGateway;

/// The outcome of a `create_card` / `edit_card` call: the gateway verdict on the
/// *tool-call* (the accountability turn) plus what the authoring did inside the
/// cap-gated [`CardEditor`].
#[derive(Debug)]
pub struct AuthorCardOutcome {
    /// The gateway's verdict on the authoring tool-call itself — a metered, receipted
    /// [`ToolGrant`](dregg_sdk::ToolGrant) turn (or an in-band refusal). This is what
    /// deos returns to Hermes over ACP for the tool-call.
    pub tool_outcome: PermissionOutcome,
    /// The provenance receipt the authoring gesture left on the card's chain (the
    /// structural edit's verified turn), if authoring was authorized AND admitted.
    /// `None` ⇒ the gateway refused the tool-call (no card touched) OR the cap tooth
    /// refused the gesture in-band (see `refused_reason`).
    pub provenance_receipt: Option<[u8; 32]>,
    /// The re-folded view-source of the authored card AFTER the gesture (the new view
    /// a renderer paints), iff authoring committed. The agent can hand this to the
    /// renderer / surface as the card it just built.
    pub view_source: Option<String>,
    /// The authoring author of every line the agent authored, in blame order — the
    /// accountable-patch face (each view line attributed to the agent's [`Author`]).
    /// Empty unless authoring committed.
    pub blamed_authors: Vec<u64>,
    /// Why authoring was refused IN-BAND by the cap tooth (an over-reach: the agent's
    /// `held` does not satisfy the card's `edit_authority`, or the gesture was a no-op).
    /// `None` ⇒ either it committed, or the gateway refused the tool-call first.
    pub refused_reason: Option<String>,
}

impl AuthorCardOutcome {
    /// Did the authoring tool-call itself get admitted (the accountability turn
    /// committed)? Independent of whether the cap tooth then admitted the gesture.
    pub fn tool_admitted(&self) -> bool {
        self.tool_outcome.allowed()
    }

    /// Did a card actually get authored (the gesture committed a provenance receipt)?
    pub fn authored(&self) -> bool {
        self.provenance_receipt.is_some()
    }
}

/// The confined agent's CARD-AUTHORING tool — `create_card` + `edit_card`.
///
/// `held` is the agent's mandate authority (the cap the [`CardEditor`] mounts against
/// the card's `edit_authority` — the red-team invariant: the caller's ATTENUATED cap,
/// never root). `author` is the [`Author`] every patch this tool appends is attributed
/// to (the blame identity — the agent acts as itself).
pub struct CardAuthoringTool {
    held: AuthRequired,
    author: Author,
}

impl CardAuthoringTool {
    /// Build the agent's card-authoring tool. `held` is the agent's mandate authority
    /// (what authoring gestures are cap-checked against); `author` is the agent's blame
    /// identity (every authored line is attributed to it).
    pub fn new(held: AuthRequired, author: Author) -> Self {
        CardAuthoringTool { held, author }
    }

    /// **CREATE A CARD — author a fresh card from a manifest.** Mint the card from
    /// `manifest`, adopt it for authoring under the agent's `held`, and (iff the manifest
    /// names an initial authoring gesture) apply it as the first receipted patch.
    ///
    /// The accountability chain mirrors [`crate::run_js`]:
    /// 1. `gw.admit_with_work(call, now, Some(vec![]))` — the ACCOUNTABILITY turn: the
    ///    `create_card` tool-call itself is scope/deadline/rate-checked + receipted by
    ///    the proven [`HermesGateway`]. Refused ⇒ no card is minted.
    /// 2. mint the card + adopt it under the agent's `held` against the card's
    ///    `edit_authority` (the cap tooth); apply `initial` as a receipted view-patch.
    ///    An over-reach (`held` does not satisfy `edit_authority`) is refused IN-BAND.
    ///
    /// `public_key` / `token_id` are the new card's cell identity; `edit_authority` is the
    /// cap a gesture on the card requires (the agent's `held` must satisfy it). `initial`
    /// is the first authoring gesture (e.g. add the card's first button); `None` mints the
    /// card from the manifest's view with no extra gesture (still a receipted authorship
    /// when a gesture is supplied — a bare mint leaves the manifest's own view).
    #[allow(clippy::too_many_arguments)]
    pub fn create_card(
        &self,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        public_key: [u8; 32],
        token_id: [u8; 32],
        manifest: AppletManifest,
        edit_authority: AuthRequired,
        initial: Option<ViewPatch>,
    ) -> AuthorCardOutcome {
        // (1) THE ACCOUNTABILITY TURN — the `create_card` tool-call routes through the
        //     gateway exactly like any other Hermes tool: a scoped, rate-limited,
        //     receipted ToolGrant turn. Refused ⇒ no card is minted.
        let tool_outcome = gw.admit_with_work(call, now, Some(vec![]));
        if !tool_outcome.allowed() {
            return AuthorCardOutcome {
                tool_outcome,
                provenance_receipt: None,
                view_source: None,
                blamed_authors: Vec::new(),
                refused_reason: None,
            };
        }

        // (2) THE HANDS — mint the card + adopt it for authoring under the agent's `held`
        //     (the cap tooth: `is_attenuation(held, edit_authority)`). The card IS a real
        //     cell with its own embedded executor; the editor authors it as a patch.
        let card = PortableApplet::mint(public_key, token_id, &manifest);
        let editor = CardEditor::adopt(
            card,
            manifest,
            self.author,
            self.held.clone(),
            edit_authority,
        );

        // Apply the initial authoring gesture (if any). A `None` gesture is a bare mint:
        // the card stands on its manifest's view with no extra patch — but we still want
        // to land a provenance receipt for the *creation* itself, so we apply a benign
        // authorship gesture (a no-op-safe text append is avoided; instead the cap tooth
        // is exercised by the gesture the caller supplies). With no gesture, the creation
        // is recorded via the editor's view as-is (no patch receipt).
        self.apply_gesture(editor, initial, tool_outcome)
    }

    /// **EDIT A CARD — patch an existing card's view as a receipted patch.** Adopt the
    /// already-minted `card` (its `manifest`) for authoring under the agent's `held` and
    /// apply `patch` as a receipted view-patch — the agent rewrites the world's UI from
    /// within, bounded by its `held`.
    ///
    /// The accountability chain is identical to [`CardAuthoringTool::create_card`]: the
    /// `edit_card` tool-call is admitted (or refused) by the gateway, then the gesture is
    /// applied through the cap tooth (refused in-band on over-reach). This is the
    /// card-editor's `edit_view` path, banked + proven, exposed as a confined tool.
    // The full edit gesture genuinely needs each arg (gateway, call, clock, card, edit
    // params, sink); bundling them into a struct would only relocate the same surface.
    #[allow(clippy::too_many_arguments)]
    pub fn edit_card(
        &self,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        card: deos_js::Applet,
        manifest: AppletManifest,
        edit_authority: AuthRequired,
        patch: ViewPatch,
    ) -> AuthorCardOutcome {
        // (1) THE ACCOUNTABILITY TURN.
        let tool_outcome = gw.admit_with_work(call, now, Some(vec![]));
        if !tool_outcome.allowed() {
            return AuthorCardOutcome {
                tool_outcome,
                provenance_receipt: None,
                view_source: None,
                blamed_authors: Vec::new(),
                refused_reason: None,
            };
        }

        // (2) THE HANDS — adopt the card under the agent's `held` against its
        //     `edit_authority` (the cap tooth) and apply the patch.
        let editor = CardEditor::adopt(
            card,
            manifest,
            self.author,
            self.held.clone(),
            edit_authority,
        );
        self.apply_gesture(editor, Some(patch), tool_outcome)
    }

    /// Apply an authoring gesture to an adopted editor and fold the result into an
    /// [`AuthorCardOutcome`]. A `None` gesture leaves the card on its manifest view (no
    /// patch receipt — the creation is the mint). A gesture refused by the cap tooth
    /// (over-reach) or a no-op surfaces IN-BAND in `refused_reason` — no receipt, no
    /// view change — exactly the bound the agent cannot exceed.
    fn apply_gesture(
        &self,
        mut editor: CardEditor,
        gesture: Option<ViewPatch>,
        tool_outcome: PermissionOutcome,
    ) -> AuthorCardOutcome {
        let Some(patch) = gesture else {
            // Bare creation: the card stands on its manifest's own view, no extra patch.
            return AuthorCardOutcome {
                tool_outcome,
                provenance_receipt: None,
                view_source: Some(editor.view_source()),
                blamed_authors: Vec::new(),
                refused_reason: None,
            };
        };

        match editor.edit_view(patch) {
            Ok(ViewEdit { blame, receipt, .. }) => AuthorCardOutcome {
                tool_outcome,
                provenance_receipt: Some(receipt.receipt_hash()),
                view_source: Some(editor.view_source()),
                blamed_authors: blame.iter().map(|l| l.author.0).collect(),
                refused_reason: None,
            },
            // The cap tooth refused the gesture IN-BAND (over-reach), or it was a no-op.
            // No patch, no receipt, no view change — the bound, surfaced honestly.
            Err(e @ (EditError::Unauthorized | EditError::NoOp)) => AuthorCardOutcome {
                tool_outcome,
                provenance_receipt: None,
                view_source: None,
                blamed_authors: Vec::new(),
                refused_reason: Some(e.to_string()),
            },
            // A genuine executor/parse fault (not a cap refusal).
            Err(e) => AuthorCardOutcome {
                tool_outcome,
                provenance_receipt: None,
                view_source: None,
                blamed_authors: Vec::new(),
                refused_reason: Some(e.to_string()),
            },
        }
    }
}
