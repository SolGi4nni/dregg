//! THE HANDS — a Hermes `run_js` tool: the confined agent runs deos-js to crawl
//! + act on the cockpit, as the operator's co-pilot.
//!
//! ember's framing (RED-TEAM 7, `tests/red_team_empowered_accountable.rs`): the
//! agent SHOULD run JS freely over a cockpit too complex for a human alone. The
//! agent running JS with its OWN broad authority over its OWN world is the WANTED
//! feature, not an escalation. So this surface does NOT lock the agent's JS down;
//! it makes the model **empowered-but-accountable-but-bounded**:
//!
//!   * EMPOWERED — the agent runs ARBITRARY JS (real SpiderMonkey via deos-js):
//!     it crawls the image (`deos.world.cells()` / `cell.reflect()`) and fires
//!     affordances (a real cap-gated verified turn → `TurnReceipt`).
//!   * ACCOUNTABLE — the `run_js` tool-call itself is admitted by the
//!     [`HermesGateway`](crate::HermesGateway) as a normal scoped, rate-limited
//!     [`ToolGrant`](dregg_sdk::ToolGrant): a metered, receipted tool turn. AND
//!     every affordance fire inside the JS is its own verified turn leaving a
//!     receipt (the audit/rewind tape) — accounted as the AGENT'S OWN cell (the
//!     confused-deputy property: the agent acts as itself, never as deos-root).
//!   * BOUNDED at the membrane — the deos-js runtime is mounted under the AGENT'S
//!     `held` authority (the mandate's caps), NEVER root. The cap tooth in
//!     [`deos_js::Applet::fire`] refuses, in-band, any affordance whose `required`
//!     authority the agent's `held` does not satisfy (an over-reach) — no turn,
//!     no receipt. Cross-vessel reach is likewise blocked (a turn binds the
//!     agent's own cell). This honors `docs/deos/AGENT-CONFINEMENT-REDTEAM.md`:
//!     mount the JS runtime under the caller's ATTENUATED cap, never root.
//!
//! ## Two binding paths
//!
//! * EMBEDDED ([`RunJsTool::run`]/[`RunJsTool::run_on`]) — binds the runtime to
//!   deos-js's OWN embedded engine (a fresh [`DreggEngine`](dregg_sdk::embed::DreggEngine)
//!   carrying the agent's applet cell). The agent crawls + drives its own private
//!   world. Proves the agent-runs-JS-bound-to-its-cap shape standalone.
//! * ATTACHED ([`RunJsTool::run_attached_on`]) — binds the runtime to a PROVIDED
//!   live [`WorldSink`] (starbridge-v2's running cockpit `World`, or a fork of it),
//!   so the agent crawls + drives the operator's ACTUAL cells. Every JS-driven turn
//!   is a real verified turn on the LIVE ledger, receipted, still bounded by the
//!   agent's `held` (the cap tooth in [`deos_js::AttachedApplet::fire`], mounted
//!   under the attenuated cap, never the World's root). THIS is "the agent's hands
//!   on the real glass."

use deos_js::card_editor::CardEditor;
use deos_js::portable::{AppletManifest, PortableApplet};
use deos_js::{Affordance, Applet, AttachedApplet, FireError, JsRuntime, WorldSink};
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, CellId};
use dregg_doc::Author;

use crate::acp::{PermissionOutcome, ToolCallRequest};
use crate::bridge::HermesGateway;

/// The slot the spike's counter applet writes (slot 0 = the model's scalar).
const COUNTER_SLOT: usize = 0;

/// The outcome of a `run_js` call: the gateway verdict on the *tool-call* (the
/// accountability turn) plus what the JS did inside its bounded runtime (the
/// affordance fires it committed under the agent's `held`).
#[derive(Debug)]
pub struct RunJsOutcome {
    /// The gateway's verdict on the `run_js` tool-call itself — a metered,
    /// receipted [`ToolGrant`](dregg_sdk::ToolGrant) turn (or an in-band refusal).
    /// This is what deos returns to Hermes over ACP for the tool-call.
    pub tool_outcome: PermissionOutcome,
    /// The script's i32 result (the JS completion value), if it produced one.
    pub result: Option<i32>,
    /// How many affordance fires committed a real verified turn inside the JS
    /// (the audit-tape length — the receipts the agent's JS left).
    pub fires_committed: usize,
    /// The receipt hashes of the committed fires, in order (the rewindable tape).
    pub receipts: Vec<[u8; 32]>,
    /// A native/eval error from the JS run, if any (a genuine fault, NOT a
    /// cap-gate refusal — a refusal is an expected, JS-observable `-1`).
    pub js_error: Option<String>,
}

impl RunJsOutcome {
    /// Did the `run_js` tool-call itself get admitted (the accountability turn
    /// committed)? Independent of what the JS did inside.
    pub fn tool_admitted(&self) -> bool {
        self.tool_outcome.allowed()
    }
}

/// Why a `run_js` call could not even start (distinct from a JS-internal fault,
/// which surfaces in [`RunJsOutcome::js_error`]).
#[derive(Debug)]
pub enum RunJsError {
    /// SpiderMonkey failed to boot or the script failed to compile/evaluate.
    Engine(String),
}

impl std::fmt::Display for RunJsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunJsError::Engine(e) => write!(f, "deos-js engine error: {e}"),
        }
    }
}
impl std::error::Error for RunJsError {}

/// The `run_js` tool — the confined agent's HANDS on deos.
///
/// `held` is the agent's mandate authority (the deos-js applet is mounted under
/// it — the red-team invariant: the caller's ATTENUATED cap, never root). The
/// agent's broad-but-not-root world is its applet cell, seeded with `seed_fields`
/// and the named `affordances` (each affordance's `required` authority is the cap
/// tooth a fire is checked against). The agent's cell IS the applet cell, so a
/// committed fire is accounted as the agent itself.
pub struct RunJsTool {
    held: AuthRequired,
    public_key: [u8; 32],
    token_id: [u8; 32],
    seed_fields: Vec<(usize, FieldElement)>,
    affordances_spec: Vec<(String, AuthRequired)>,
}

impl RunJsTool {
    /// Build the agent's `run_js` tool over its own world: the applet cell is the
    /// agent's cell (`public_key`/`token_id`), mounted under the agent's `held`.
    ///
    /// `affordances_spec` is the agent's affordance surface — `(name, required)`
    /// pairs. A fire of `name` carries an `apply` that bumps the counter slot by
    /// the JS-supplied arg (the spike's mutating shape); `required` is the cap the
    /// fire is gated on. An affordance whose `required` the agent's `held` does
    /// not satisfy can be *named* by JS but never *fires* — the over-reach the
    /// cap tooth refuses in-band.
    pub fn new(
        held: AuthRequired,
        public_key: [u8; 32],
        token_id: [u8; 32],
        seed_fields: Vec<(usize, FieldElement)>,
        affordances_spec: Vec<(String, AuthRequired)>,
    ) -> Self {
        RunJsTool {
            held,
            public_key,
            token_id,
            seed_fields,
            affordances_spec,
        }
    }

    /// Build the agent's bounded applet (its own world, mounted under its `held`).
    /// A fresh deos-js applet on its own embedded verified executor. Each declared
    /// affordance bumps the counter slot by `arg` and is gated on its `required`.
    fn build_applet(&self) -> Applet {
        let affordances: Vec<Affordance> = self
            .affordances_spec
            .iter()
            .map(|(name, required)| Affordance {
                name: name.clone(),
                required: required.clone(),
                apply: Box::new(|model, arg| {
                    let cur = model.field_u64(COUNTER_SLOT) as i64;
                    let next = (cur + arg).max(0) as u64;
                    vec![(COUNTER_SLOT, deos_js::applet::pack_u64(next))]
                }),
            })
            .collect();

        Applet::mint(
            self.public_key,
            self.token_id,
            &self.seed_fields,
            affordances,
            self.held.clone(),
        )
    }

    /// THE HANDS — admit the `run_js` tool-call as a metered, receipted gateway
    /// turn, then (iff admitted) run `script` on a deos-js runtime bound to the
    /// agent's `held`.
    ///
    /// 1. `gw.admit_with_work(call, now, Some(vec![]))` — the ACCOUNTABILITY turn:
    ///    the `run_js` tool-call itself is scope/deadline/rate-checked and
    ///    receipted by the proven [`HermesGateway`]. Refused ⇒ no JS runs at all
    ///    (the tool is not even granted this turn).
    /// 2. boot a real SpiderMonkey runtime, install the agent's applet (mounted
    ///    under `held`), and `eval` the agent's `script`. Inside, `deos.world` /
    ///    `cell.reflect()` crawl the image (reads, no turn) and `app.fire(...)`
    ///    fires affordances — each a real verified turn under the agent's `held`,
    ///    each refused in-band (a JS-observable `-1`) if it over-reaches `held`.
    ///
    /// Returns a [`RunJsOutcome`] carrying the tool verdict, the script result,
    /// and the committed-fire receipt tape (what the agent's JS actually did).
    pub fn run(
        &self,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        script: &str,
    ) -> Result<RunJsOutcome, RunJsError> {
        // SpiderMonkey's `JSEngine::init()` is PROCESS-GLOBAL (one-shot). Boot a
        // runtime here for the standalone-call path; the multi-call path shares
        // one via [`RunJsTool::run_on`].
        let mut rt = JsRuntime::new().map_err(RunJsError::Engine)?;
        self.run_on(&mut rt, gw, call, now, script)
    }

    /// As [`RunJsTool::run`], but on a CALLER-OWNED [`JsRuntime`]. SpiderMonkey's
    /// engine init is process-global and one-shot, so a host (or a test) that runs
    /// multiple `run_js` calls boots ONE runtime and threads it here. Each `eval`
    /// runs on a fresh global, so reusing the runtime is sound.
    pub fn run_on(
        &self,
        rt: &mut JsRuntime,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        script: &str,
    ) -> Result<RunJsOutcome, RunJsError> {
        // (1) THE ACCOUNTABILITY TURN — the `run_js` tool-call routes through the
        //     gateway exactly like any other Hermes tool: a scoped, rate-limited,
        //     receipted ToolGrant turn. `Some(vec![])` keeps the gateway turn a
        //     pure metered admission (the JS's own fires carry the real witness).
        let tool_outcome = gw.admit_with_work(call, now, Some(vec![]));
        if !tool_outcome.allowed() {
            // Refused at the membrane — the agent is not granted `run_js` this
            // turn. No JS runs; no world is touched.
            return Ok(RunJsOutcome {
                tool_outcome,
                result: None,
                fires_committed: 0,
                receipts: Vec::new(),
                js_error: None,
            });
        }

        // (2) THE HANDS — install the agent's applet BOUND to the agent's `held`
        //     (the red-team invariant: the caller's attenuated cap, never root)
        //     and eval the script. The applet IS the agent's own cell.
        let applet = self.build_applet();
        deos_js::js::set_current_applet(applet);

        let eval = rt.eval(script);

        // Take the applet back to read the receipt tape (what the JS committed).
        let applet = deos_js::js::take_current_applet();
        let (fires_committed, receipts) = applet
            .as_ref()
            .map(|a| (a.receipt_count(), a.receipts().to_vec()))
            .unwrap_or((0, Vec::new()));

        let (result, js_error) = match eval {
            Ok(r) => (r, None),
            Err(e) => (None, Some(e)),
        };

        Ok(RunJsOutcome {
            tool_outcome,
            result,
            fires_committed,
            receipts,
            js_error,
        })
    }

    /// THE HANDS ON THE REAL GLASS — admit the `run_js` tool-call as a metered,
    /// receipted gateway turn, then (iff admitted) run `script` on a deos-js runtime
    /// ATTACHED to a PROVIDED live World (`sink`), bound to the agent's `held`.
    ///
    /// Identical accountability + boundedness to [`RunJsTool::run_on`], but the JS
    /// drives the LIVE World rather than deos-js's own embedded engine:
    ///   * `deos.world.cells()` / `cell.reflect()` crawl the ATTACHED World's REAL
    ///     cells (the operator's, or a fork's);
    ///   * `app.fire(...)` commits a real verified turn ON THAT World (through the
    ///     `sink`'s [`WorldSink::fire_effects`]) — a receipt that lands on the live
    ///     ledger. The cap tooth in [`AttachedApplet::fire`] still refuses an
    ///     over-reach in-band (no turn reaches the World), and a fire binds the
    ///     agent's OWN cell (no cross-vessel reach). The red-team invariant holds.
    ///
    /// `sink` is the host's live World reduced to the crawl + commit surface (the
    /// cockpit supplies `starbridge_v2::agent_attach::WorldSinkAdapter`). `agent` is
    /// the agent's cell on that World (the agent of every committed turn).
    pub fn run_attached_on(
        &self,
        rt: &mut JsRuntime,
        sink: Box<dyn WorldSink>,
        agent: CellId,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        script: &str,
    ) -> Result<RunJsOutcome, RunJsError> {
        // (1) THE ACCOUNTABILITY TURN — the same metered, receipted ToolGrant.
        let tool_outcome = gw.admit_with_work(call, now, Some(vec![]));
        if !tool_outcome.allowed() {
            return Ok(RunJsOutcome {
                tool_outcome,
                result: None,
                fires_committed: 0,
                receipts: Vec::new(),
                js_error: None,
            });
        }

        // (2) THE HANDS — attach the runtime to the live World under the agent's
        //     `held` (the cap tooth, mounted under the attenuated cap, never root),
        //     and eval the script. Each affordance fire commits a real verified turn
        //     ON THE LIVE WORLD; an over-reach is refused in-band.
        let applet = AttachedApplet::attach(
            sink,
            agent,
            self.held.clone(),
            self.affordances_spec.clone(),
            COUNTER_SLOT,
        );

        match rt.run_attached(applet, script) {
            Ok(outcome) => Ok(RunJsOutcome {
                tool_outcome,
                result: outcome.result,
                fires_committed: outcome.fires_committed,
                receipts: outcome.receipts,
                js_error: None,
            }),
            Err(e) => Ok(RunJsOutcome {
                tool_outcome,
                result: None,
                fires_committed: 0,
                receipts: Vec::new(),
                js_error: Some(e),
            }),
        }
    }

    /// A direct, gateway-free fire of one named affordance under the agent's
    /// `held` — the cap tooth in isolation (for an over-reach assertion that
    /// does not need the JS round-trip). Returns the [`FireError`] on refusal.
    pub fn fire_direct(&self, affordance: &str, arg: i64) -> Result<[u8; 32], FireError> {
        let mut applet = self.build_applet();
        applet.fire(affordance, arg).map(|r| r.receipt_hash())
    }
}

/// The outcome of a `run_js` AUTHORING call: the gateway verdict on the
/// *tool-call* (the accountability turn) plus what the agent-decided JS did to
/// the card inside its cap-gated [`CardEditor`] (the receipted patches it landed,
/// the re-folded view-source, and the blame).
#[derive(Debug)]
pub struct RunJsAuthorOutcome {
    /// The gateway's verdict on the `run_js` tool-call itself — a metered,
    /// receipted [`ToolGrant`](dregg_sdk::ToolGrant) turn (or an in-band refusal).
    /// This is what deos returns to Hermes over ACP for the tool-call.
    pub tool_outcome: PermissionOutcome,
    /// The script's i32 completion value, if any (the JS `editView` paths return
    /// the re-folded tree object; a final `?1:0`-style assertion surfaces here).
    pub result: Option<i32>,
    /// How many authoring gestures committed a real provenance turn on the card's
    /// chain (the receipted-patch count — each `deos.editor.editView` that landed).
    pub patches_committed: usize,
    /// The provenance receipt hashes the agent's authoring left, in order (the
    /// rewindable patch tape).
    pub receipts: Vec<[u8; 32]>,
    /// The card's re-folded view-source AFTER the agent's authoring (the new view a
    /// renderer paints), iff the run completed. `None` on an engine fault.
    pub view_source: Option<String>,
    /// The authoring author of every view line, in blame order — the accountable-
    /// patch face (each view line attributed to its [`Author`]). Empty on a fault.
    pub blamed_authors: Vec<u64>,
    /// A native/eval error from the JS run, if any (a genuine fault, NOT a cap-gate
    /// refusal — an over-reach is the expected, JS-observable `null` from `editView`).
    pub js_error: Option<String>,
}

impl RunJsAuthorOutcome {
    /// Did the `run_js` tool-call itself get admitted (the accountability turn
    /// committed)? Independent of what the JS authored inside.
    pub fn tool_admitted(&self) -> bool {
        self.tool_outcome.allowed()
    }

    /// Did the agent's JS actually author the card (at least one receipted patch)?
    pub fn authored(&self) -> bool {
        self.patches_committed > 0
    }
}

/// THE HANDS THAT AUTHOR VIA JS — a confined agent's `run_js` tool whose script
/// AUTHORS a card through the `deos.editor.*` surface (the SAME path the
/// scripted `deos-view::agent_authors_a_card_live` keystone runs, now behind the
/// proven gateway). This is the JS-decided sibling of [`CardAuthoringTool`]
/// (which takes a structured `ViewPatch`): here the AGENT WRITES THE `editView`
/// JS — `deos.editor.editView(card, { op: "addButton", … })` — and the runtime
/// folds it into a receipted patch.
///
/// The empowered-but-accountable-but-bounded model is identical to [`RunJsTool`]:
///   * EMPOWERED — the agent runs ARBITRARY authoring JS (real SpiderMonkey).
///   * ACCOUNTABLE — the `run_js` tool-call is admitted by the [`HermesGateway`]
///     as a metered, receipted [`ToolGrant`] turn; refused ⇒ no JS runs. AND each
///     `editView` that lands leaves its own provenance receipt on the card's
///     chain, blamed on the agent's [`Author`].
///   * BOUNDED — the [`CardEditor`] mounts the agent's `held` against the card's
///     `edit_authority` (the authoring cap tooth, [`dregg_cell::is_attenuation`]).
///     An over-reach is refused IN-BAND (`editView` returns null), NO patch, NO
///     receipt, the view untouched — the same gate a human authoring goes through.
pub struct RunJsAuthoringTool {
    held: AuthRequired,
    author: Author,
}

impl RunJsAuthoringTool {
    /// Build the agent's authoring `run_js` tool. `held` is the agent's mandate
    /// authority (what authoring gestures are cap-checked against the card's
    /// `edit_authority`); `author` is the agent's blame identity (every authored
    /// line is attributed to it — the agent acts as itself).
    pub fn new(held: AuthRequired, author: Author) -> Self {
        RunJsAuthoringTool { held, author }
    }

    /// THE HANDS THAT AUTHOR — admit the `run_js` tool-call as a metered, receipted
    /// gateway turn, then (iff admitted) adopt `card` (its `manifest`) for authoring
    /// under the agent's `held` against the card's `edit_authority`, and run the
    /// agent-decided `script` through [`JsRuntime::run_authoring`]. The script
    /// authors the card via `deos.editor.editView(card, …)`; each gesture that lands
    /// is a receipted provenance patch, an over-reach refused in-band.
    ///
    /// `rt` is a CALLER-OWNED [`JsRuntime`] (SpiderMonkey's engine init is
    /// process-global + one-shot, so the host boots ONE and threads it here).
    pub fn run_on(
        &self,
        rt: &mut JsRuntime,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        card: Applet,
        manifest: AppletManifest,
        edit_authority: AuthRequired,
        script: &str,
    ) -> RunJsAuthorOutcome {
        // (1) THE ACCOUNTABILITY TURN — the `run_js` tool-call routes through the
        //     gateway exactly like any other Hermes tool: a scoped, rate-limited,
        //     receipted ToolGrant turn. `Some(vec![])` keeps the gateway turn a pure
        //     metered admission (the editor's own patches carry the real witness).
        let tool_outcome = gw.admit_with_work(call, now, Some(vec![]));
        if !tool_outcome.allowed() {
            // Refused at the membrane — no JS runs; no card is authored.
            return RunJsAuthorOutcome {
                tool_outcome,
                result: None,
                patches_committed: 0,
                receipts: Vec::new(),
                view_source: None,
                blamed_authors: Vec::new(),
                js_error: None,
            };
        }

        // (2) THE HANDS — adopt the card under the agent's `held` against the card's
        //     `edit_authority` (the cap tooth) and run the agent-decided authoring JS.
        let editor = CardEditor::adopt(
            card,
            manifest,
            self.author,
            self.held.clone(),
            edit_authority,
        );

        match rt.run_authoring(editor, script) {
            Ok((result, editor)) => {
                let receipts: Vec<[u8; 32]> = editor.card().receipts().to_vec();
                let patches_committed = editor.card().receipt_count();
                let blamed_authors: Vec<u64> =
                    editor.view_blame().iter().map(|l| l.author.0).collect();
                RunJsAuthorOutcome {
                    tool_outcome,
                    result,
                    patches_committed,
                    receipts,
                    view_source: Some(editor.view_source()),
                    blamed_authors,
                    js_error: None,
                }
            }
            // A genuine engine/eval fault (boot/compile failure) — distinct from a
            // cap-gate refusal, which is the expected in-band `null` from editView.
            Err(e) => RunJsAuthorOutcome {
                tool_outcome,
                result: None,
                patches_committed: 0,
                receipts: Vec::new(),
                view_source: None,
                blamed_authors: Vec::new(),
                js_error: Some(e),
            },
        }
    }

    /// Convenience: mint a fresh card from `manifest` (cell identity
    /// `public_key`/`token_id`), then [`RunJsAuthoringTool::run_on`] the agent's
    /// authoring `script` against it.
    #[allow(clippy::too_many_arguments)]
    pub fn run_on_fresh(
        &self,
        rt: &mut JsRuntime,
        gw: &mut HermesGateway<'_>,
        call: &ToolCallRequest,
        now: i64,
        public_key: [u8; 32],
        token_id: [u8; 32],
        manifest: AppletManifest,
        edit_authority: AuthRequired,
        script: &str,
    ) -> RunJsAuthorOutcome {
        let card = PortableApplet::mint(public_key, token_id, &manifest);
        self.run_on(
            rt,
            gw,
            call,
            now,
            card,
            manifest,
            edit_authority,
            script,
        )
    }
}
