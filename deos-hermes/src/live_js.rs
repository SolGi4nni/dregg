//! THE LIVE BRAIN'S HANDS ON THE GLASS — wire a real `hermes-acp` model's `run_js`
//! tool-call to a real execution of the model's chosen JavaScript against a LIVE
//! World, via [`RunJsTool::run_attached_on`].
//!
//! [`crate::acp_client::AcpClient`] answers every `session/request_permission`
//! through the [`HermesGateway`](crate::HermesGateway). For most tools that is the
//! whole story (the metered turn IS the side-effect's witness). For `run_js` the
//! model chose a *script* — its hands — and we want that script to actually RUN on
//! the cockpit's live World: a real crawl + real verified turns landing real
//! receipts on the live ledger.
//!
//! [`LiveJsHands`] is that bridge. It owns:
//!   * the agent's [`RunJsTool`] (its affordance surface + `held` authority — the
//!     cap tooth, mounted under the attenuated cap, never the World's root); and
//!   * a SINK FACTORY — a closure that produces a fresh `Box<dyn WorldSink>` over
//!     the SAME live World each call ([`RunJsTool::run_attached_on`] consumes the
//!     sink per call; the factory hands it a fresh view of the shared World).
//!
//! Its [`LiveJsHands::hook`] returns a `run_js` hook for
//! [`AcpClient::with_run_js_hook`](crate::acp_client::AcpClient::with_run_js_hook):
//! given the model's `run_js` tool-call, it extracts the `script` the model wrote
//! (from `rawInput.script`), runs the gateway accountability turn AND the script
//! against the live World, and returns the ACP verdict + a record of the receipts
//! the brain's JS landed.
//!
//! The red-team invariant is KEPT end-to-end: the model is EMPOWERED (it writes
//! arbitrary JS), ACCOUNTABLE (the `run_js` tool-call is a metered, receipted
//! gateway turn), and BOUNDED (every affordance fire inside the JS is gated by the
//! agent's `held` in `AttachedApplet::fire`; an over-reach is refused in-band, no
//! turn reaches the World; the World's own executor is the second gate).

use deos_js::portable::AppletManifest;
use deos_js::{Applet, JsRuntime, WorldSink};
use dregg_cell::{AuthRequired, CellId};

use crate::acp::{PermissionOutcome, ToolCallRequest};
use crate::acp_client::{JsRunRecord, RunJsHook};
use crate::bridge::HermesGateway;
use crate::run_js::{RunJsAuthoringTool, RunJsTool};

/// Pull the model's chosen JS out of a `run_js` tool-call's `rawInput`. The brain
/// writes its script under `script` (the `run_js` tool's one argument). Falls back
/// to `code`/`js` for tolerance, else an empty script (a no-op the gate still
/// meters — the model produced a `run_js` call with no body).
pub fn script_of_call(call: &ToolCallRequest) -> String {
    for key in ["script", "code", "js"] {
        if let Some(s) = call.arguments.get(key).and_then(|v| v.as_str()) {
            return s.to_string();
        }
    }
    String::new()
}

/// The live brain's hands: an agent [`RunJsTool`] + its accountability
/// [`HermesGateway`] + a factory for fresh live [`WorldSink`]s over the cockpit's
/// shared World + a process-global [`JsRuntime`].
///
/// It owns its OWN gateway because the `run_js` hook the [`AcpClient`] calls cannot
/// also borrow the client's gateway (a self-borrow). This gateway is what meters +
/// receipts the `run_js` accountability turns; it is built over the same grantor as
/// the session gateway, so the two share the grantor's ledger of receipts.
///
/// `sink_factory` MUST hand back a sink over the SAME live World every call (clone
/// the cockpit's `Rc<RefCell<World>>` inside it) so every `run_js` lands on the one
/// ledger the cockpit renders. `agent` is the cell every committed turn binds.
pub struct LiveJsHands<'gw, F>
where
    F: FnMut() -> Box<dyn WorldSink>,
{
    tool: RunJsTool,
    agent: CellId,
    gateway: HermesGateway<'gw>,
    sink_factory: F,
    rt: JsRuntime,
}

impl<'gw, F> LiveJsHands<'gw, F>
where
    F: FnMut() -> Box<dyn WorldSink> + 'gw,
{
    /// Build the hands over an agent `tool`, its accountability `gateway`, the
    /// `agent` cell every turn binds, and a `sink_factory` producing fresh live
    /// sinks. Boots the process-global SpiderMonkey engine (one-shot) — call once
    /// per process.
    pub fn new(
        tool: RunJsTool,
        agent: CellId,
        gateway: HermesGateway<'gw>,
        sink_factory: F,
    ) -> Result<Self, String> {
        let rt = JsRuntime::new()?;
        Ok(LiveJsHands {
            tool,
            agent,
            gateway,
            sink_factory,
            rt,
        })
    }

    /// Run ONE `run_js` tool-call: the gateway accountability turn AND the model's
    /// chosen script against the live World. Returns the ACP verdict deos sends
    /// back (admitted iff the gateway admitted the tool-call) and a record of what
    /// the brain's JS did (the script + the receipts it landed on the live ledger).
    pub fn run_call(
        &mut self,
        call: &ToolCallRequest,
        now: i64,
    ) -> (PermissionOutcome, JsRunRecord) {
        let script = script_of_call(call);
        let sink = (self.sink_factory)();

        let mut record = JsRunRecord {
            tool_call_id: call.tool_call_id.clone(),
            script: script.clone(),
            ..Default::default()
        };

        match self.tool.run_attached_on(
            &mut self.rt,
            sink,
            self.agent,
            &mut self.gateway,
            call,
            now,
            &script,
        ) {
            Ok(outcome) => {
                record.result = outcome.result;
                record.fires_committed = outcome.fires_committed;
                record.receipts = outcome.receipts.clone();
                record.js_error = outcome.js_error.clone();
                (outcome.tool_outcome, record)
            }
            Err(e) => {
                // The runtime couldn't even start the script (a boot/compile fault).
                // Surface it as a reject naming the engine fault — no turn, no glass.
                record.js_error = Some(e.to_string());
                (
                    PermissionOutcome::Reject {
                        tool_call_id: call.tool_call_id.clone(),
                        reason: format!("run_js engine fault: {e}"),
                    },
                    record,
                )
            }
        }
    }

    /// Consume the hands into a `run_js` [`RunJsHook`] for
    /// [`AcpClient::with_run_js_hook`](crate::acp_client::AcpClient::with_run_js_hook).
    /// Each invocation runs the model's chosen script on the live World.
    pub fn into_hook(mut self) -> RunJsHook<'gw>
    where
        F: 'gw,
    {
        Box::new(move |call: &ToolCallRequest, now: i64| self.run_call(call, now))
    }
}

/// THE LIVE BRAIN'S HANDS THAT AUTHOR — wire a real `hermes-acp` model's `run_js`
/// tool-call to a real run of the model-DECIDED `deos.editor.editView(...)` JS
/// against a card, via [`RunJsAuthoringTool`].
///
/// This is the authoring sibling of [`LiveJsHands`]: where that runs the model's
/// crawl/fire script on a live World, [`LiveAuthoringHands`] runs the model's
/// AUTHORING script — the agent, given a card + a goal ("add a reset button",
/// "relabel the title"), WRITES the `editView` JS itself, and the edit lands as a
/// receipted provenance patch bounded by its `held` vs the card's `edit_authority`.
/// This closes the keystone loop with a LIVE brain deciding the edit, not a
/// scripted snippet (the `deos-view::agent_authors_a_card_live` fixture).
///
/// It owns:
///   * the agent's [`RunJsAuthoringTool`] (its `held` + blame [`Author`]);
///   * a CARD FACTORY — a closure producing the `(card, manifest, edit_authority)`
///     the brain authors this call. Each `run_js` adopts a fresh [`CardEditor`], so
///     the factory hands the same card's current state (clone the cockpit's card).
///   * a process-global [`JsRuntime`] (SpiderMonkey init is one-shot).
///
/// The red-team invariant holds end-to-end: EMPOWERED (the model writes arbitrary
/// authoring JS), ACCOUNTABLE (the `run_js` tool-call is a metered, receipted
/// gateway turn + each `editView` leaves a provenance receipt blamed on the agent),
/// BOUNDED (the cap tooth in [`CardEditor`] refuses an over-reach in-band — no
/// patch reaches the card).
pub struct LiveAuthoringHands<'gw, F>
where
    F: FnMut() -> (Applet, AppletManifest, AuthRequired),
{
    tool: RunJsAuthoringTool,
    gateway: HermesGateway<'gw>,
    card_factory: F,
    rt: JsRuntime,
}

impl<'gw, F> LiveAuthoringHands<'gw, F>
where
    F: FnMut() -> (Applet, AppletManifest, AuthRequired) + 'gw,
{
    /// Build the authoring hands over an agent `tool`, its accountability `gateway`,
    /// and a `card_factory` producing the `(card, manifest, edit_authority)` the
    /// brain authors. Boots the process-global SpiderMonkey engine — call once per
    /// process.
    pub fn new(
        tool: RunJsAuthoringTool,
        gateway: HermesGateway<'gw>,
        card_factory: F,
    ) -> Result<Self, String> {
        let rt = JsRuntime::new()?;
        Ok(Self::with_runtime(tool, gateway, card_factory, rt))
    }

    /// As [`LiveAuthoringHands::new`], but on a CALLER-OWNED [`JsRuntime`].
    /// SpiderMonkey's engine init is process-global + one-shot, so a host (or test)
    /// that has already booted a runtime threads it here instead of booting another
    /// (a second `JsRuntime::new()` errors `AlreadyInitialized`).
    pub fn with_runtime(
        tool: RunJsAuthoringTool,
        gateway: HermesGateway<'gw>,
        card_factory: F,
        rt: JsRuntime,
    ) -> Self {
        LiveAuthoringHands {
            tool,
            gateway,
            card_factory,
            rt,
        }
    }

    /// Run ONE `run_js` authoring tool-call: the gateway accountability turn AND the
    /// model-decided `editView` script against the card the factory hands back.
    /// Returns the ACP verdict deos sends back and a record of what the brain's JS
    /// authored (the script + the provenance receipts it landed).
    pub fn run_call(
        &mut self,
        call: &ToolCallRequest,
        now: i64,
    ) -> (PermissionOutcome, JsRunRecord) {
        let script = super::live_js::script_of_call(call);
        let (card, manifest, edit_authority) = (self.card_factory)();

        let mut record = JsRunRecord {
            tool_call_id: call.tool_call_id.clone(),
            script: script.clone(),
            ..Default::default()
        };

        let outcome = self.tool.run_on(
            &mut self.rt,
            &mut self.gateway,
            call,
            now,
            card,
            manifest,
            edit_authority,
            &script,
        );

        record.result = outcome.result;
        // The authoring patches the brain's JS committed (mirrors the fire tape).
        record.fires_committed = outcome.patches_committed;
        record.receipts = outcome.receipts.clone();
        record.js_error = outcome.js_error.clone();
        (outcome.tool_outcome, record)
    }

    /// Consume the hands into a `run_js` [`RunJsHook`] for
    /// [`AcpClient::with_run_js_hook`](crate::acp_client::AcpClient::with_run_js_hook).
    /// Each invocation runs the model-decided authoring script against the card.
    pub fn into_hook(mut self) -> RunJsHook<'gw>
    where
        F: 'gw,
    {
        Box::new(move |call: &ToolCallRequest, now: i64| self.run_call(call, now))
    }
}
