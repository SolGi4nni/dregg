//! THE BRIDGE — a Hermes ACP tool-call becomes a cap-gated, receipted dregg turn.
//!
//! [`HermesGateway`] is the deos-side seam. It owns the grantor handle (the
//! [`AgentRuntime`](dregg_sdk::AgentRuntime) + root [`HeldToken`](dregg_sdk::HeldToken))
//! and a [`GrantRegistry`] (deos's per-kind mandate). For each Hermes
//! [`ToolKind`], it lazily ADMITS a cap-gated worker under that kind's
//! [`ToolGrant`](dregg_sdk::ToolGrant) — a real `ToolGateway` over the verified
//! executor. Every inbound [`ToolCallRequest`] is then routed through
//! [`ToolGateway::invoke`](dregg_sdk::ToolGateway::invoke):
//!
//! * ADMITTED — the metered `calls_made : c → c+1` write COMMITS through the
//!   cap-gated worker on the verified executor, yielding a real [`ToolReceipt`]
//!   (the `turn_hash` is the receipt id). deos returns [`PermissionOutcome::Allow`]
//!   to Hermes over ACP, and the call proceeds.
//! * REFUSED — `delegAdmit` returned false (scope / deadline / rate). NO turn,
//!   NO spend. deos returns [`PermissionOutcome::Reject`] naming the leg that
//!   bit — the IN-BAND refusal Hermes sees.
//!
//! The enforcement is ENTIRELY the proven `ToolGateway`'s; this module only maps
//! the ACP tool-call onto the gate and the gate's verdict back onto ACP. No new
//! policy, no new crypto, no bypass.

use std::collections::HashMap;

use dregg_sdk::{
    AgentRuntime, GatewayRefusal, HeldToken, ToolCallError, ToolGateway, ToolGrant,
};
use dregg_turn::Effect;

use crate::acp::{PermissionOutcome, ToolCallRequest, ToolKind};
use crate::grant_registry::GrantRegistry;

/// The deos-side bridge: one [`ToolGateway`] per [`ToolKind`], lazily admitted,
/// fronting every Hermes tool-call over ACP.
pub struct HermesGateway<'rt> {
    /// The grantor: the runtime that admits workers and runs their turns.
    runtime: &'rt AgentRuntime,
    /// The root token the grantor delegates each worker's mandate from.
    root_token: HeldToken,
    /// deos's per-kind mandate over this Hermes session.
    registry: GrantRegistry,
    /// The cap-gated worker per kind, admitted on first use under that kind's
    /// grant. (One `ToolGateway` = one delegated worker + one metered counter.)
    gateways: HashMap<ToolKind, ToolGateway>,
}

impl<'rt> HermesGateway<'rt> {
    /// Open a bridge for a Hermes session: deos (the grantor, holding
    /// `root_token` on `runtime`) confines the session under `registry`.
    pub fn new(
        runtime: &'rt AgentRuntime,
        root_token: HeldToken,
        registry: GrantRegistry,
    ) -> HermesGateway<'rt> {
        HermesGateway {
            runtime,
            root_token,
            registry,
            gateways: HashMap::new(),
        }
    }

    /// The grant deos pinned for a kind (for inspection / a session dock).
    pub fn grant_for(&self, kind: ToolKind) -> &ToolGrant {
        self.registry.grant_for(kind)
    }

    /// Lazily admit (or fetch) the cap-gated worker for a kind. The worker's
    /// biscuit credential is scoped to EXACTLY the kind's `tool_method`, and its
    /// cell carries the `mandate_program` rate/monotonic backstop — both
    /// installed by the proven [`ToolGateway::admit`].
    fn gateway_for(&mut self, kind: ToolKind) -> Result<&mut ToolGateway, ToolCallError> {
        if !self.gateways.contains_key(&kind) {
            let grant = self.registry.grant_for(kind).clone();
            let gw = ToolGateway::admit(self.runtime, &self.root_token, grant)
                .map_err(ToolCallError::Sdk)?;
            self.gateways.insert(kind, gw);
        }
        Ok(self
            .gateways
            .get_mut(&kind)
            .expect("just inserted the gateway for this kind"))
    }

    /// THE SEAM — admit a Hermes ACP tool-call as a cap-gated, metered,
    /// receipted dregg turn (or refuse it in-band).
    ///
    /// `now` is the presentation clock/height (the ACP request arrival time);
    /// `work` is the effects the tool's actual payload performs on the worker
    /// cell (pass an empty `Vec` for a pure metered admission — the metering
    /// alone IS the receipted proof the call was authorized).
    ///
    /// The call's [`ToolKind`] (from its name) selects the mandate; the
    /// gate's `delegAdmit` then folds SCOPE ∧ DEADLINE ∧ RATE. The returned
    /// [`PermissionOutcome`] is exactly what deos sends back to Hermes over the
    /// ACP `session/request_permission`.
    pub fn admit_call(
        &mut self,
        call: &ToolCallRequest,
        now: i64,
        work: Vec<Effect>,
    ) -> PermissionOutcome {
        let kind = call.kind;
        // The in-band tool id the gate checks scope against is synthesized from
        // the call's kind — the ACP wire does not carry our scalar id, so the
        // grantor's per-kind id IS the scope key. (A call whose name maps to a
        // different kind lands on a different gateway and would be out-of-scope
        // there; here we route to the matching one, so scope passes and the
        // RATE + DEADLINE legs do the live confinement.)
        let tool_id = self.registry.tool_id_for(kind);

        let gw = match self.gateway_for(kind) {
            Ok(gw) => gw,
            Err(e) => {
                return PermissionOutcome::Reject {
                    tool_call_id: call.tool_call_id.clone(),
                    reason: format!("could not admit worker for {kind:?}: {e}"),
                };
            }
        };

        match gw.invoke(tool_id, now, work) {
            Ok(receipt) => PermissionOutcome::Allow {
                tool_call_id: call.tool_call_id.clone(),
                receipt: hex32(&receipt.receipt.turn_hash),
                remaining: receipt.remaining,
            },
            Err(ToolCallError::Refused(refusal)) => PermissionOutcome::Reject {
                tool_call_id: call.tool_call_id.clone(),
                reason: describe_refusal(&refusal),
            },
            Err(ToolCallError::Sdk(e)) => PermissionOutcome::Reject {
                tool_call_id: call.tool_call_id.clone(),
                reason: format!("executor rejected the metered turn: {e}"),
            },
        }
    }

    /// Calls made so far on a kind's mandate (0 if never invoked).
    pub fn calls_made(&self, kind: ToolKind) -> i64 {
        self.gateways.get(&kind).map_or(0, |gw| gw.calls_made())
    }
}

/// A human-readable refusal reason naming the mandate leg that bit — the text
/// deos surfaces to Hermes / the editor on a [`PermissionOutcome::Reject`].
fn describe_refusal(refusal: &GatewayRefusal) -> String {
    match refusal {
        GatewayRefusal::OutOfScope { presented, granted } => {
            format!("out of scope: tool {presented} not granted (mandate covers {granted})")
        }
        GatewayRefusal::PastDeadline { now, deadline } => {
            format!("past deadline: presented at {now}, mandate expired at {deadline}")
        }
        GatewayRefusal::OverRate {
            calls_made,
            rate_limit,
        } => format!("rate exhausted: {calls_made} of {rate_limit} calls used this mandate window"),
    }
}

/// Hex-encode a 32-byte receipt hash as the ACP-visible receipt id.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
