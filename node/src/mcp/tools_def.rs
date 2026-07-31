//! `mcp::tools_def` — split out of the former monolithic `mcp.rs` (pure module move).

use super::*;

/// The legible tool GROUP a tool belongs to. dregg's MCP surface is large
/// (46 tools); rather than a flat dump, each tool advertises a group so a
/// client UI / agent can present the toolset as a coherent place. Groups map to
/// the agent's four modes of inhabiting dregg: orient, act, delegate, verify —
/// plus the app and privacy surfaces.
pub(super) fn tool_group(tool: &str) -> &'static str {
    match tool {
        "dregg_get_status"
        | "dregg_check_capabilities"
        | "dregg_read_cell"
        | "dregg_list_cells"
        | "dregg_get_cap_graph"
        | "dregg_get_trustline_status"
        | "dregg_get_channel_status"
        | "dregg_get_receipt_chain"
        | "dregg_get_blocklace_status"
        | "dregg_get_constitution"
        | "dregg_check_resource_budget"
        | "dregg_list_auctions"
        | "dregg_verify_provenance" => "orient",

        "dregg_create_agent"
        | "dregg_authorize"
        | "dregg_submit_turn"
        | "dregg_post_intent"
        | "dregg_fulfill_intent"
        | "dregg_make_sovereign"
        | "dregg_bilateral_action"
        | "dregg_debit_shared_resource"
        | "dregg_extend_trustline"
        | "dregg_place_bid"
        | "dregg_captp_deliver" => "act",

        "dregg_grant_capability"
        | "dregg_revoke_capability"
        | "dregg_delegate"
        | "dregg_create_bearer_cap"
        | "dregg_exercise_bearer_cap"
        | "dregg_exercise_handoff_cert"
        | "dregg_propose_membership" => "delegate",

        "dregg_verify_sovereign_proof"
        | "dregg_prove_sovereign_turn"
        | "dregg_compose_proofs"
        | "dregg_prove_predicate"
        | "dregg_sign_sovereign_witness"
        | "dregg_peer_exchange"
        | "dregg_compress_history" => "verify",

        "dregg_seal_data"
        | "dregg_unseal_data"
        | "dregg_create_stealth_address"
        | "dregg_private_transfer"
        | "dregg_encrypt_intent"
        // The ENCRYPTED CALL AUCTION: orders arrive as BFV ciphertexts the trader built in its
        // own process, and only (p*, V*) is ever opened. It belongs with privacy, not with the
        // plaintext gallery auction (`dregg_list_auctions` / `dregg_place_bid`).
        | "dregg_dark_clearing_open"
        | "dregg_dark_clearing_submit"
        | "dregg_dark_clearing_clear"
        | "dregg_dark_clearing_result" => "privacy",

        "dregg_register_name"
        | "dregg_publish_subscription"
        | "dregg_issue_credential"
        | "dregg_register_service"
        | "dregg_deploy_factory"
        | "dregg_create_from_factory"
        | "dregg_create_cell_from_factory_effect" => "apps",

        _ => "other",
    }
}

/// A short human-friendly display title for a tool (MCP `title`). The
/// programmatic `name` stays stable; the title aids legibility in clients.
pub(super) fn tool_title(tool: &str) -> &'static str {
    match tool {
        "dregg_get_status" => "Node Status",
        "dregg_create_agent" => "Register Agent Cell",
        "dregg_authorize" => "Authorize Action (ZK)",
        "dregg_submit_turn" => "Submit Verified Turn",
        "dregg_grant_capability" => "Grant Capability",
        "dregg_revoke_capability" => "Revoke Capability",
        "dregg_post_intent" => "Post Intent",
        "dregg_fulfill_intent" => "Fulfill Intent",
        "dregg_delegate" => "Delegate Sub-Capability",
        "dregg_check_capabilities" => "List My Capabilities",
        "dregg_read_cell" => "Read Cell State",
        "dregg_list_cells" => "List Ledger Cells",
        "dregg_get_cap_graph" => "Read Capability Graph",
        "dregg_get_trustline_status" => "Read Trustline Status",
        "dregg_get_channel_status" => "Read Channel Status",
        "dregg_get_receipt_chain" => "Read Receipt Chain",
        "dregg_seal_data" => "Seal Data (Encrypt)",
        "dregg_dark_clearing_open" => "Open Encrypted Auction",
        "dregg_dark_clearing_submit" => "Submit Encrypted Order",
        "dregg_dark_clearing_clear" => "Clear Encrypted Auction",
        "dregg_dark_clearing_result" => "Read Cleared Price",
        "dregg_unseal_data" => "Unseal Data (Decrypt)",
        "dregg_make_sovereign" => "Make Cell Sovereign",
        "dregg_peer_exchange" => "Sovereign Peer Exchange",
        "dregg_compress_history" => "IVC-Compress History",
        "dregg_create_bearer_cap" => "Create Bearer Capability",
        "dregg_exercise_bearer_cap" => "Exercise Bearer Capability",
        "dregg_deploy_factory" => "Deploy Factory",
        "dregg_create_from_factory" => "Create Cell From Factory",
        "dregg_verify_provenance" => "Verify Cell Provenance",
        "dregg_prove_sovereign_turn" => "Prove Sovereign Turn (STARK)",
        "dregg_verify_sovereign_proof" => "Verify Sovereign Proof",
        "dregg_create_stealth_address" => "Create Stealth Address",
        "dregg_private_transfer" => "Private Transfer",
        "dregg_encrypt_intent" => "Post Encrypted Intent",
        "dregg_prove_predicate" => "Prove Predicate (ZK)",
        "dregg_compose_proofs" => "Compose Proofs",
        "dregg_get_blocklace_status" => "Blocklace / Finality Status",
        "dregg_get_constitution" => "Federation Constitution",
        "dregg_propose_membership" => "Propose Membership Change",
        "dregg_check_resource_budget" => "Check Resource Budget",
        "dregg_debit_shared_resource" => "Debit Shared Resource",
        "dregg_extend_trustline" => "Extend Trustline (Line of Credit)",
        "dregg_list_auctions" => "List Auctions",
        "dregg_place_bid" => "Place Sealed Bid",
        "dregg_captp_deliver" => "CapTP Deliver",
        "dregg_exercise_handoff_cert" => "Exercise Handoff Cert",
        "dregg_sign_sovereign_witness" => "Sign Sovereign Witness",
        "dregg_bilateral_action" => "Bilateral Action (Both Receipts)",
        "dregg_register_name" => "Register Name",
        "dregg_publish_subscription" => "Publish Subscription Update",
        "dregg_issue_credential" => "Issue Credential",
        "dregg_register_service" => "Register Service Path",
        "dregg_create_cell_from_factory_effect" => "Create Cell (Factory Effect)",
        _ => "dregg Tool",
    }
}

/// Behavioural annotations for a tool. Derived from its capability scope and
/// known semantics: `read` tools are read-only & idempotent; capability
/// administration is destructive; bridge / federation / captp reach the open
/// world. An agent reads these to decide whether a call is safe to probe,
/// retryable, or reaches beyond the local node.
pub(super) fn tool_annotations(tool: &str) -> McpToolAnnotations {
    let scope = tool_required_scope(tool);
    let read_only = scope == "read";

    // Destructive = irreversibly removes authority / state. Only meaningful for
    // mutating tools; left None for read-only tools (per spec, destructiveHint
    // is only relevant when readOnlyHint is false).
    let destructive_hint = if read_only {
        None
    } else {
        Some(matches!(
            tool,
            "dregg_revoke_capability" | "dregg_propose_membership" | "dregg_private_transfer"
        ))
    };

    // Idempotent: re-invoking with the same args has no additional effect.
    // Reads are idempotent; `create_agent` is explicitly idempotent (registers
    // once); pure proof/verify/seal computations are deterministic functions.
    let idempotent_hint = read_only
        || matches!(
            tool,
            "dregg_create_agent"
                | "dregg_make_sovereign"
                | "dregg_verify_sovereign_proof"
                | "dregg_prove_predicate"
                | "dregg_prove_sovereign_turn"
                | "dregg_create_stealth_address"
                | "dregg_seal_data"
                | "dregg_unseal_data"
                | "dregg_compose_proofs"
        );

    // Open world: touches state beyond this node (other federations / peers /
    // capability-transfer protocols / external marketplaces).
    let open_world_hint = Some(matches!(
        tool,
        "dregg_peer_exchange"
            | "dregg_captp_deliver"
            | "dregg_exercise_handoff_cert"
            | "dregg_propose_membership"
            | "dregg_post_intent"
            | "dregg_fulfill_intent"
            | "dregg_encrypt_intent"
            | "dregg_list_auctions"
            | "dregg_place_bid"
    ));

    McpToolAnnotations {
        read_only_hint: read_only,
        destructive_hint,
        idempotent_hint,
        open_world_hint,
    }
}

/// The declared `outputSchema` for a tool's `structuredContent` (MCP 2025-06-18).
///
/// Most dregg tools that change state return the SAME structured "receipt" shape
/// (turn hash + commit flag + the Effect-VM STARK proof material). Declaring it
/// once, by reuse, lets a client validate the typed result and — crucially for an
/// agent's VERIFY mode — know up front that a turn carries a proof to check. Read
/// tools and a few bespoke shapes return `None` (their `structuredContent` is the
/// state object itself, whose shape is self-describing).
pub(super) fn tool_output_schema(tool: &str) -> Option<Value> {
    // The common verified-turn receipt shape produced by `run_*_action` /
    // `tool_submit_turn` / capability + app tools.
    let receipt = || {
        serde_json::json!({
            "type": "object",
            "description": "A dregg verified-turn receipt: the committed state transition plus \
                            its Effect-VM STARK proof material (verify via dregg://receipts or \
                            the standalone dregg-verifier).",
            "properties": {
                "committed": { "type": "boolean", "description": "Whether the turn committed to the ledger." },
                "turn_hash": { "type": "string", "description": "Hex hash of the committed turn." },
                "post_state_root": { "type": "string", "description": "Hex post-state root the proof binds to." },
                "effect_vm_proof_hex": { "type": "string", "description": "Hex-encoded Effect-VM STARK proof of the transition." },
                "effect_vm_public_inputs": { "type": "array", "items": { "type": "integer" }, "description": "The proof's public inputs." },
                "effect_vm_witness_hash_hex": { "type": "string", "description": "Hex witness hash binding the trace." }
            },
            "required": ["committed"]
        })
    };
    match tool {
        // Tools that submit a verified turn and return the receipt shape.
        "dregg_submit_turn"
        | "dregg_grant_capability"
        | "dregg_revoke_capability"
        | "dregg_delegate"
        | "dregg_make_sovereign"
        | "dregg_register_name"
        | "dregg_publish_subscription"
        | "dregg_register_service"
        | "dregg_issue_credential"
        | "dregg_exercise_bearer_cap"
        | "dregg_fulfill_intent" => Some(receipt()),
        _ => None,
    }
}

/// The public tool list: the raw definitions DECORATED with title, behavioural
/// annotations, an output schema, and a `group` tag in the input schema's
/// metadata. This is what `tools/list` serves.
pub(super) fn tool_definitions() -> Vec<McpToolDef> {
    let mut defs = tool_definitions_raw();
    for d in defs.iter_mut() {
        d.title = Some(tool_title(d.name));
        d.annotations = Some(tool_annotations(d.name));
        d.output_schema = tool_output_schema(d.name);
        // Stamp the legible group + required capability scope into the schema's
        // top-level metadata so an agent self-orienting from tools/list alone
        // can see which mode each tool belongs to and what authority it needs.
        let scope = tool_required_scope(d.name);
        if let Value::Object(map) = &mut d.input_schema {
            map.insert(
                "x-dregg-group".to_string(),
                Value::String(tool_group(d.name).to_string()),
            );
            map.insert(
                "x-dregg-scope".to_string(),
                Value::String(scope.to_string()),
            );
            // Declare the ocap `_cap` argument in the SCHEMA, not just prose.
            // When capability enforcement is on, a covering tools-access biscuit
            // (scope verb '{scope}') must be presented here; an agent reading
            // tools/list — and a schema-validating client — discovers the
            // requirement without having to read dregg://about. Optional in the
            // schema (enforcement may be off), but its presence makes the ocap
            // model legible right at the tool boundary.
            if let Some(props) = map.get_mut("properties").and_then(|p| p.as_object_mut()) {
                props.insert(
                    "_cap".to_string(),
                    serde_json::json!({
                        "type": "object",
                        "description": format!(
                            "ocap credential. When capability enforcement is on, present a \
                             tools-access biscuit covering this tool's '{scope}' scope, minted by \
                             this node under its mcp_cap_issuer_pubkey (see dregg://identity). \
                             Omit when enforcement is off."
                        ),
                        "properties": {
                            "biscuit": {
                                "type": "string",
                                "description": "The encoded 'eb2_…' biscuit string."
                            }
                        },
                        "required": ["biscuit"]
                    }),
                );
            }
        }
    }
    defs
}

pub(super) fn tool_definitions_raw() -> Vec<McpToolDef> {
    vec![
        McpToolDef {
            name: "dregg_get_status",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get node status (height, peers, health)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_create_agent",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Register this node's cipherclerk as a cell in the local ledger (idempotent). Returns the content-addressed cell_id.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable label for the agent (informational only; identity is content-addressed from the cipherclerk pubkey)" },
                    "initial_balance": { "type": "integer", "description": "Initial computron balance for the cell when first created. Ignored on subsequent calls." }
                },
                "required": ["name"]
            }),
        },
        McpToolDef {
            name: "dregg_authorize",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Prove authorization for an action using ZK proof",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action to authorize (e.g. read, write)" },
                    "resource": { "type": "string", "description": "The resource to act upon" },
                    "mode": { "type": "string", "enum": ["trusted", "selective", "private"], "description": "Verification mode: trusted (fastest), selective (partial ZK), private (full ZK)" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "dregg_submit_turn",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Submit an atomic turn (set of actions) for execution. Pass an `effects` array to actually perform work (transfers, set_field, etc.); omit it for a no-op turn that just chains a receipt.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell ID" },
                    "method": { "type": "string", "description": "The method to invoke on the cell" },
                    "fee": { "type": "integer", "description": "Fee in computrons (default: 0)" },
                    "memo": { "type": "string", "description": "Optional memo attached to the turn" },
                    "effects": {
                        "type": "array",
                        "description": "Optional list of effects: { type: 'transfer', from, to, amount } | { type: 'increment_nonce', cell } | { type: 'set_field', cell, index, value }",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell", "method"]
            }),
        },
        McpToolDef {
            name: "dregg_grant_capability",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Grant a capability to another agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "to_agent": { "type": "string", "description": "Hex-encoded public key of the recipient agent" },
                    "target_cell": { "type": "string", "description": "Hex-encoded cell ID the capability applies to" },
                    "permissions": { "type": "string", "description": "Comma-separated permissions (e.g. read,write)" }
                },
                "required": ["to_agent", "target_cell", "permissions"]
            }),
        },
        McpToolDef {
            name: "dregg_revoke_capability",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Revoke a previously granted capability",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cap_slot": { "type": "integer", "description": "The capability slot number to revoke" }
                },
                "required": ["cap_slot"]
            }),
        },
        McpToolDef {
            name: "dregg_post_intent",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Post an intent to the marketplace (request a capability/service)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action needed (e.g. read, write, execute)" },
                    "resource": { "type": "string", "description": "The resource pattern (e.g. documents/*)" },
                    "max_fee": { "type": "integer", "description": "Maximum fee willing to pay (computrons)" },
                    "expiry_blocks": { "type": "integer", "description": "Number of blocks until intent expires" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "dregg_fulfill_intent",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Fulfill a matching intent from the marketplace",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "intent_id": { "type": "string", "description": "Hex-encoded 32-byte intent ID to fulfill" }
                },
                "required": ["intent_id"]
            }),
        },
        McpToolDef {
            name: "dregg_delegate",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Delegate a bounded sub-capability to another agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "capability": { "type": "integer", "description": "Token slot number to delegate from" },
                    "to_agent": { "type": "string", "description": "Hex-encoded public key of the delegatee" },
                    "restrictions": { "type": "object", "description": "Restriction object (services, expiry, etc.)" },
                    "max_staleness": { "type": "integer", "description": "Maximum staleness in blocks before re-delegation required" }
                },
                "required": ["capability", "to_agent"]
            }),
        },
        McpToolDef {
            name: "dregg_check_capabilities",
            title: None,
            output_schema: None,
            annotations: None,
            description: "List all capabilities held by the current agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_read_cell",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Read a cell's state (balance, fields, permissions)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "dregg_list_cells",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Survey the cells in the local ledger (the map of what you can act on). \
                          Returns each cell's id, balance, nonce, capability count, and kind \
                          (cell | sovereign | trustline | channel). Paginated via an opaque cursor.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cursor": { "type": "string", "description": "Opaque pagination cursor from a previous call's next_cursor (decimal offset). Omit to start at the beginning." },
                    "limit": { "type": "integer", "minimum": 1, "maximum": 200, "description": "Max cells to return (default 20)." }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_get_cap_graph",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Read the OUTGOING capability edges held by a cell — which targets it can \
                          reach, under what permission (none/signature/proof/...), with what facet \
                          and expiry. The ocap reachability map for planning delegation/exercise. \
                          Defaults to your own agent cell when cell_id is omitted.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID whose capability graph to read. Omit for your own agent cell." }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_get_trustline_status",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Read the self-authenticating position of a trustline cell (ORGANS §1): \
                          its line ceiling, directional parties (issuer→holder), collateral mode \
                          (fullReserve | pureCredit), and the escrow backing the line. A cell is a \
                          trustline IFF its program VK re-derives from its own terms — never a \
                          tamper-able slot.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "trustline_cell": { "type": "string", "description": "Hex-encoded 32-byte trustline cell ID (see dregg_list_cells, kind=trustline)." }
                },
                "required": ["trustline_cell"]
            }),
        },
        McpToolDef {
            name: "dregg_get_channel_status",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Read the self-authenticating terms of a channel-group cell (ORGANS §4): \
                          its governance admin key and group tag. A cell is a channel IFF its \
                          program VK re-derives from its own terms.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "channel_cell": { "type": "string", "description": "Hex-encoded 32-byte channel cell ID (see dregg_list_cells, kind=channel)." }
                },
                "required": ["channel_cell"]
            }),
        },
        McpToolDef {
            name: "dregg_get_receipt_chain",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get the agent's auditable receipt chain (action history)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "limit": { "type": "integer", "description": "Maximum number of receipts to return (default: 50)" }
                },
                "required": []
            }),
        },
        // ─── THE ENCRYPTED CALL AUCTION ───────────────────────────────────────────
        // `crate::dark_clearing_service`. Gated to the Lean-emitted
        // `dark-bazaar-private-n4k4` family (N=4 orders, K=4 buckets, 4-bit quantities);
        // fails closed on committee / verified_core / certificate. No tool here can
        // return an order.
        McpToolDef {
            name: "dregg_dark_clearing_open",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Open an ENCRYPTED call auction: run a real Shamir BFV key ceremony and \
                          pin the ordered trader roster. Returns the public collective key a \
                          trader encrypts against. Gated to the Lean-emitted \
                          dark-bazaar-private-n4k4 family (exactly 4 traders).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "traders": {
                        "type": "array",
                        "items": { "type": "string" },
                        "description": "Exactly 4 hex-encoded 32-byte Ed25519 verifying keys, in roster order. Only these keys may submit."
                    }
                },
                "required": ["traders"]
            }),
        },
        McpToolDef {
            name: "dregg_dark_clearing_submit",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Submit ONE encrypted order to an open auction. The envelope is built \
                          and signed in YOUR process; this node never accepts, stores, logs, or \
                          returns a plaintext order. Returns a chained receipt of digests.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "session": { "type": "string", "description": "Hex 32-byte session nonce from dregg_dark_clearing_open." },
                    "envelope_b64": { "type": "string", "description": "Base64 of the exact fhegg-fhe SignedOrderSubmission wire bytes (BFV ciphertext + Ed25519 attribution). No plaintext order field is present in it." }
                },
                "required": ["session", "envelope_b64"]
            }),
        },
        McpToolDef {
            name: "dregg_dark_clearing_clear",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Clear a complete encrypted book: homomorphic fold, masked quorum \
                          boundary opening, MPC crossing. Reveals ONLY the clearing price bucket \
                          p* and cleared volume V*, with a quorum-co-signed attested receipt. \
                          Refuses fail-closed if the committee, the verified core, or the \
                          certificate is unavailable.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "session": { "type": "string", "description": "Hex 32-byte session nonce." }
                },
                "required": ["session"]
            }),
        },
        McpToolDef {
            name: "dregg_dark_clearing_result",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Read a cleared auction's result: (p*, V*) plus the attestation digests. \
                          There is nothing else to read — no order, no curve, no per-bucket volume.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "session": { "type": "string", "description": "Hex 32-byte session nonce." }
                },
                "required": ["session"]
            }),
        },
        McpToolDef {
            name: "dregg_seal_data",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Encrypt data that only a specific agent can decrypt",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "data": { "type": "string", "description": "The plaintext data to seal" },
                    "recipient": { "type": "string", "description": "Hex-encoded public key of the intended recipient" }
                },
                "required": ["data", "recipient"]
            }),
        },
        McpToolDef {
            name: "dregg_unseal_data",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Decrypt sealed data addressed to this agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "sealed_box": { "type": "string", "description": "Hex-encoded sealed box bytes" }
                },
                "required": ["sealed_box"]
            }),
        },
        // ─── Sovereign Cells ───────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_make_sovereign",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Transition a cell to sovereign mode (cell stores its own state, federation only holds commitment)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID to transition" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "dregg_peer_exchange",
            title: None,
            output_schema: None,
            annotations: None,
            // ⚑ MEASURED 2026-07-30: the handler contacts NO peer and produces NO proof. An
            // agent plans from this string, so it must describe the handler, not the design.
            description: "Build and sign a LOCAL peer-exchange transition object for another                           sovereign cell. Contacts no peer, receives nothing, and produces NO                           proof — the peer is registered under a placeholder zero commitment.                           Returns `built_local_transition`, never an `exchanged` verdict.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte local cell ID" },
                    "peer_cell_id": { "type": "string", "description": "Hex-encoded 32-byte peer cell ID" },
                    "new_commitment": { "type": "string", "description": "Hex-encoded 32-byte new state commitment after exchange" }
                },
                "required": ["cell_id", "peer_cell_id", "new_commitment"]
            }),
        },
        McpToolDef {
            name: "dregg_compress_history",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Fold the node's RETAINED finalized turns into ONE whole-chain recursive STARK proof (real IVC compression: prove_turn_chain_recursive + light-client byte-envelope verify) and check it against YOUR configured VK anchor. `vk_anchor` is REQUIRED: this tool will not verify against a fingerprint it computed itself. Reports `verification: valid` ONLY when the byte envelope re-verified under the caller-supplied anchor; the key is absent otherwise. Fails closed for any turn with no retained wrap-input FinalizedTurn (e.g. turns committed before retention or without full-turn proving).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID" },
                    "vk_anchor": { "type": "string", "description": "REQUIRED. The 64-hex root-circuit VK fingerprint YOUR configuration pins — the light-client trust anchor, held beforehand and never read off the artifact. This node will not derive it for you: an anchor recomputed from the fold under test makes the VK pin compare a value with itself, which cannot fail. Obtain it from genesis/checkpoint config, or once from an honest setup fold (`produce_history_envelope`) that you then hold fixed." },
                    "turn_count": { "type": "integer", "description": "Number of most recent turns to compress, in chain order (default: all; minimum fold is 2)" }
                },
                "required": ["cell_id", "vk_anchor"]
            }),
        },
        // ─── Bearer Capabilities ───────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_create_bearer_cap",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Create a bearer capability proof (immediate grant, no c-list storage required)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell the cap grants access to" },
                    "permissions": { "type": "string", "description": "Permission level: none, signature, proof, either" },
                    "expires_at": { "type": "integer", "description": "Block height at which the bearer cap expires" },
                    "bearer_pk": { "type": "string", "description": "Hex-encoded 32-byte public key of the intended bearer" }
                },
                "required": ["target_cell", "permissions", "expires_at", "bearer_pk"]
            }),
        },
        McpToolDef {
            name: "dregg_exercise_bearer_cap",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Exercise a bearer capability to perform an action without c-list storage. Pass an `effects` array to actually perform work (e.g. transfer from the target cell).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell" },
                    "method": { "type": "string", "description": "Method to invoke on the target cell" },
                    "delegation_chain": { "type": "string", "description": "Hex-encoded delegation chain signature" },
                    "bearer_pk": { "type": "string", "description": "Hex-encoded 32-byte bearer public key" },
                    "expires_at": { "type": "integer", "description": "Expiry height of the bearer cap" },
                    "permissions": { "type": "string", "description": "Permission level the bearer cap commits to (default: 'signature' for backward compat)" },
                    "effects": {
                        "type": "array",
                        "description": "List of effects to execute under the bearer authorization (typically a single transfer). Each effect is { type, ... } per the parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell", "method", "delegation_chain", "bearer_pk", "expires_at"]
            }),
        },
        // ─── Factories ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_deploy_factory",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Deploy a factory descriptor to the ProgramRegistry (defines what new cells can be created)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory verification key" },
                    "child_vk_strategy": { "type": "string", "enum": ["fixed", "derived", "approved_set"], "description": "How child VKs are determined" },
                    "max_creations_per_epoch": { "type": "integer", "description": "Maximum cells this factory can create per epoch (0 = unlimited)" },
                    "sovereign": { "type": "boolean", "description": "Whether created cells are sovereign (default: false)" }
                },
                "required": ["factory_vk"]
            }),
        },
        McpToolDef {
            name: "dregg_create_from_factory",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Create a new cell from a deployed factory (with provenance tracking)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory VK to create from" },
                    "cell_name": { "type": "string", "description": "Human-readable name for the new cell" },
                    "sovereign": { "type": "boolean", "description": "Whether the new cell is sovereign (default: false)" }
                },
                "required": ["factory_vk"]
            }),
        },
        McpToolDef {
            name: "dregg_verify_provenance",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Report what this node knows about a cell's origin. ⚑ It does NOT verify factory provenance: this node stores no `Provenance` record, so the cell's committed program VK and the factory derivation_param_hash are both unavailable and `factory_derivation_verified` is always false with a named reason. It reports ledger membership (hosted / sovereign) truthfully.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID to check" },
                    "expected_factory_vk": { "type": "string", "description": "Hex-encoded 32-byte expected factory VK (optional filter)" }
                },
                "required": ["cell_id"]
            }),
        },
        // ─── Effect VM ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_prove_sovereign_turn",
            title: None,
            output_schema: None,
            annotations: None,
            description: "RETIRED (fail-closed): the standalone v1 Effect-VM prove lane has no producer and this tool always answers `proved: false`. The catalogue used to advertise 'Generate a STARK proof for a sovereign cell's multi-effect turn via the Effect VM' — a capability an agent reading this list would plan around and that does not exist. Finalized turns prove ROTATED through the node commit pipeline.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte sovereign cell ID" },
                    "effects": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "type": { "type": "string", "enum": ["credit", "debit", "set_field", "grant_cap"], "description": "Effect type" },
                                "amount": { "type": "integer", "description": "Amount for credit/debit effects" },
                                "field": { "type": "string", "description": "Field name for set_field" },
                                "value": { "type": "string", "description": "Field value for set_field" }
                            },
                            "required": ["type"]
                        },
                        "description": "List of effects to prove"
                    },
                    "pre_state_hash": { "type": "string", "description": "Hex-encoded 32-byte pre-state commitment" }
                },
                "required": ["cell_id", "effects", "pre_state_hash"]
            }),
        },
        McpToolDef {
            name: "dregg_verify_sovereign_proof",
            title: None,
            output_schema: None,
            annotations: None,
            description: "RETIRED (fail-closed): the v1 Effect-VM StarkProof wire format is gone and this tool always answers `valid: false`. It verifies nothing and never did since the lane was retired. Descriptor-IR2 proofs verify through `verify_vm_descriptor2`, which must anchor against the emitted descriptor — not available from a raw-bytes surface that is handed no descriptor.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "proof_hex": { "type": "string", "description": "Hex-encoded proof bytes" },
                    "public_inputs": {
                        "type": "array",
                        "items": { "type": "integer" },
                        "description": "Public input values (BabyBear field elements as u32)"
                    }
                },
                "required": ["proof_hex", "public_inputs"]
            }),
        },
        // ─── Privacy ───────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_create_stealth_address",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Generate a one-time stealth address for a recipient (unlinkable receive address)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "recipient_spend_pubkey": { "type": "string", "description": "Hex-encoded 32-byte recipient spend public key" },
                    "recipient_view_pubkey": { "type": "string", "description": "Hex-encoded 32-byte recipient view public key" }
                },
                "required": ["recipient_spend_pubkey", "recipient_view_pubkey"]
            }),
        },
        McpToolDef {
            name: "dregg_private_transfer",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Perform a private value transfer using Pedersen commitments (hides amount)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "from_cell": { "type": "string", "description": "Hex-encoded 32-byte sender cell ID" },
                    "to_cell": { "type": "string", "description": "Hex-encoded 32-byte recipient cell ID" },
                    "amount": { "type": "integer", "description": "Transfer amount (hidden in commitment)" },
                    "blinding": { "type": "string", "description": "Hex-encoded 32-byte blinding factor (random if omitted)" }
                },
                "required": ["from_cell", "to_cell", "amount"]
            }),
        },
        McpToolDef {
            name: "dregg_encrypt_intent",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Post an SSE-encrypted intent (body hidden, matchable via search tokens)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action needed (e.g. read, write, execute)" },
                    "resource": { "type": "string", "description": "The resource pattern (e.g. documents/*)" },
                    "expiry_blocks": { "type": "integer", "description": "Number of blocks until intent expires" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "dregg_prove_predicate",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Prove a predicate over private data (e.g. balance >= threshold) without revealing the value",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "predicate_type": { "type": "string", "enum": ["gte", "lte", "eq", "range", "membership"], "description": "Type of predicate to prove" },
                    "attribute": { "type": "string", "description": "Name of the attribute being proven" },
                    "threshold": { "type": "integer", "description": "Threshold value for comparison predicates" },
                    "private_value": { "type": "integer", "description": "The private value (not revealed in proof)" },
                    "state_root": { "type": "integer", "description": "Current state root (BabyBear field element as u32)" }
                },
                "required": ["predicate_type", "attribute", "private_value", "state_root"]
            }),
        },
        // ─── Proof Composition ─────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_compose_proofs",
            title: None,
            output_schema: None,
            annotations: None,
            description: "RETIRED (fail-closed): no real proof-composition engine exists; this tool always returns an error and never claims validity. Use dregg_compress_history for a real whole-chain fold.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "mode": { "type": "string", "enum": ["and", "or", "chain", "aggregate"], "description": "Composition mode" },
                    "proofs": {
                        "type": "array",
                        "items": { "type": "string" },
                        "description": "Hex-encoded proof bytes to compose"
                    },
                    "public_inputs": {
                        "type": "array",
                        "items": {
                            "type": "array",
                            "items": { "type": "integer" }
                        },
                        "description": "Public inputs for each proof (array of arrays)"
                    }
                },
                "required": ["mode", "proofs"]
            }),
        },
        // ─── Blocklace ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_get_blocklace_status",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get blocklace consensus status (tip, finality level, participants, wave)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_get_constitution",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Get the current federation constitution (membership set, threshold, version)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_propose_membership",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Propose a membership change (join/leave/threshold change) to the federation",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "enum": ["join", "leave"], "description": "Whether to propose joining or leaving" },
                    "participant": { "type": "string", "description": "Hex-encoded 32-byte public key of the participant (for join: new member; for leave: departing member)" },
                    "reason": { "type": "string", "description": "Human-readable reason for the proposal" }
                },
                "required": ["action", "participant"]
            }),
        },
        // ─── Shared Resources ──────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_check_resource_budget",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Query remaining budget allowance for a shared resource (bounded-counter coordination)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID of the agent" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "dregg_debit_shared_resource",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Optimistic debit from a shared resource (Tier 2: consensus-free if within local budget slice)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID of the agent" },
                    "amount": { "type": "integer", "description": "Amount to debit from the shared resource" },
                    "memo": { "type": "string", "description": "Optional memo for the debit operation" }
                },
                "required": ["cell_id", "amount"]
            }),
        },
        // ─── Trustlines (ORGANS §1) ──────────────────────────────────────────────
        McpToolDef {
            name: "dregg_extend_trustline",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Extend a holder a bilateral line of credit (ORGANS §1): birth a per-line trustline cell, escrow the full line from this node's agent cell (the funded birth — you are REALLY debited), grant the holder their line capability, and open it. The holder draws/repays against the line and settlement redeems drawn value as a real conserving transfer. Returns the trustline cell id, the escrowed amount, and the four birth turn hashes.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "holder": { "type": "string", "description": "Hex-encoded 32-byte holder (counterparty) cell ID. Must already exist in the ledger (settlement needs a real target)." },
                    "line": { "type": "integer", "description": "The credit line N to extend, in computrons. Escrowed in full at open (fullReserve collateral) — the issuer is debited line + the adopt fee." },
                    "salt": { "type": "string", "description": "Optional salt disambiguating multiple lines to the same holder (vary it to open a second concurrent line)." }
                },
                "required": ["holder", "line"]
            }),
        },
        // ─── Gallery ───────────────────────────────────────────────────────────────
        McpToolDef {
            name: "dregg_list_auctions",
            title: None,
            output_schema: None,
            annotations: None,
            description: "List active gallery auctions (commit-reveal sealed-bid)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "status": { "type": "string", "enum": ["commit", "reveal", "settled", "all"], "description": "Filter by auction phase (default: all)" }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_place_bid",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Place a sealed bid on a gallery auction (commit phase: bid amount hidden behind commitment)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "auction_id": { "type": "string", "description": "Hex-encoded 32-byte auction ID" },
                    "amount": { "type": "integer", "description": "Bid amount (will be committed, not revealed until reveal phase)" },
                    "nonce": { "type": "string", "description": "Hex-encoded 32-byte random nonce for commitment (generated if omitted)" }
                },
                "required": ["auction_id", "amount"]
            }),
        },
        // ─── CapTP Delivery (γ.1 / Seam 3) ─────────────────────────────────────────
        McpToolDef {
            name: "dregg_captp_deliver",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Construct and submit a Turn whose root action is authorized by `Authorization::CapTpDelivered` (introducer-signed HandoffCertificate + sender Ed25519 sig over the canonical delivery message). The node cipherclerk plays the recipient/sender; the introducer key is constructed in-process for testing. Returns the turn hash and the cert nonce.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell (the action target & gateway-mirror agent)" },
                    "introducer_sk": { "type": "string", "description": "Hex-encoded 32-byte introducer Ed25519 secret seed (testing-only). When omitted, a fresh ephemeral introducer key is generated." },
                    "introducer_federation": { "type": "string", "description": "Hex-encoded 32-byte introducer federation id. Defaults to BLAKE3(introducer_pk)." },
                    "target_federation": { "type": "string", "description": "Hex-encoded 32-byte target federation id (default: zero federation, matching the executor default)." },
                    "permissions": { "type": "string", "enum": ["none","signature","proof","either"], "description": "Permission level encoded in the cert (default: signature)" },
                    "expires_at": { "type": "integer", "description": "Optional cert expiry (block height)." },
                    "swiss": { "type": "string", "description": "Hex-encoded 32-byte swiss number (default: random)." },
                    "effects": {
                        "type": "array",
                        "description": "Effects to attach to the captp.route action (typically a single effect). Each effect is per the parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell"]
            }),
        },
        // ─── CapTP Handoff Cert Exercise (γ.1 extension) ────────────────────────────
        McpToolDef {
            name: "dregg_exercise_handoff_cert",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Exercise a CapTP HandoffCertificate: constructs a Turn authorized by \
                `Authorization::CapTpDelivered` (mirroring `dregg_captp_deliver`) carrying the \
                caller's effects; the executor's `verify_captp_delivered` validates the \
                introducer-signed cert + the recipient's delivery signature. \
                The node cipherclerk is the recipient/sender; the introducer key is supplied \
                or generated ephemerally. An optional `effects` array lets the caller attach \
                downstream effects (e.g. a Transfer). Returns the turn hash, cert nonce, STARK \
                proof, and all Effect-VM fields.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell." },
                    "introducer_sk": { "type": "string", "description": "Hex-encoded 32-byte introducer Ed25519 secret seed (testing-only). Omit for a fresh ephemeral key." },
                    "introducer_pk": { "type": "string", "description": "Hex-encoded 32-byte introducer public key. Ignored when introducer_sk is supplied (derived from it). When both are omitted, a fresh ephemeral key is generated." },
                    "recipient_pk": { "type": "string", "description": "Hex-encoded 32-byte recipient public key. Defaults to the node cipherclerk's public key." },
                    "introducer_federation": { "type": "string", "description": "Hex-encoded 32-byte introducer federation id. Defaults to BLAKE3(introducer_pk)." },
                    "target_federation": { "type": "string", "description": "Hex-encoded 32-byte target federation id. Default: zero federation." },
                    "permissions": { "type": "string", "enum": ["none","signature","proof","either"], "description": "Permission level encoded in the cert. Default: signature." },
                    "expires_at": { "type": "integer", "description": "Optional cert expiry block height." },
                    "swiss": { "type": "string", "description": "Hex-encoded 32-byte swiss number (default: random)." },
                    "effects": {
                        "type": "array",
                        "description": "Effects to attach to the delivered turn (e.g. a Transfer). Per parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell"]
            }),
        },
        // ─── Sovereign Cell Witness (reshaped) ─────────────────────────────────────
        McpToolDef {
            name: "dregg_sign_sovereign_witness",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Build a properly-signed `SovereignCellWitness` for a sovereign cell currently in the local ledger, together with the TURN it witnesses. Signs the canonical message (cell_id || old_commitment || new_commitment || effects_hash || timestamp || sequence) with the node cipherclerk's Ed25519 key. `effects_hash` is DERIVED from `effects` via `Turn::sovereign_effects_hash` — it is not a caller parameter, because a caller-chosen binding binds nothing. Pass `attach_proof=true` to also generate an Effect-VM STARK proof binding the transition. Returns `witnessed_turn_postcard_hex` (submit this) plus the witness and structured fields.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte sovereign cell ID. Must be registered via `dregg_make_sovereign` first." },
                    "new_commitment": { "type": "string", "description": "Hex-encoded 32-byte post-state commitment claimed by the witness. REQUIRED: this node does not execute the effects, so it cannot derive the post-state, and a fabricated commitment is refused by the executor (SovereignCommitmentMismatch)." },
                    "effects": { "type": "array", "description": "The effects this witness authorizes — the same descriptors `dregg_act` takes: {type: transfer|increment_nonce|set_field, ...}. The witness's effects_hash is derived from these; submitting it against any other effect set is rejected with EffectsHashMismatch.", "items": { "type": "object" } },
                    "attach_proof": { "type": "boolean", "description": "If true, also generate a STARK transition_proof binding (old, new, effects_hash) via EffectVmAir. Default: false." },
                    "vm_effect_amount": { "type": "integer", "description": "If `attach_proof` is set, the (single-effect VM) amount to use for the synthetic transition. Default: 0." }
                },
                "required": ["cell_id", "new_commitment", "effects"]
            }),
        },
        // ─── Slot caveats / StateConstraint surface ───────────────────────────────
        // (Note: extends dregg_read_cell to include the cell program's
        // declared `StateConstraint` set — no new tool needed for the read
        // path; clients invoking dregg_read_cell will see `program.kind` and
        // `program.state_constraints` in the JSON response.)
        // ─── γ.2 bilateral binding receipts ────────────────────────────────────────
        McpToolDef {
            name: "dregg_bilateral_action",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Submit a Turn with a single bilateral effect (Transfer / GrantCapability / Introduce) and return the WitnessedReceipts for BOTH cells involved. The executor's bilateral schedule binds the from-side and to-side accumulator roots; this tool surfaces the per-side trace + proof bytes so callers can verify the bilateral identity end-to-end.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "mode": { "type": "string", "enum": ["transfer","grant","introduce"], "description": "Which bilateral effect to emit." },
                    "from": { "type": "string", "description": "Hex-encoded 32-byte 'from' cell (transfer source / grant donor / introduce introducer)." },
                    "to": { "type": "string", "description": "Hex-encoded 32-byte 'to' cell (transfer recipient / grant recipient / introduce recipient)." },
                    "target": { "type": "string", "description": "(introduce only) Hex-encoded 32-byte target cell the introduction references." },
                    "amount": { "type": "integer", "description": "(transfer only) Computron amount to transfer." },
                    "permissions": { "type": "string", "enum": ["none","signature","proof","either"], "description": "(grant / introduce) Permission level for the granted capability. Default: signature." }
                },
                "required": ["mode","from","to"]
            }),
        },
        // ─── Starbridge-app builders (cross-app-e2e closure) ───────────────────────
        // These four tools wrap the canonical `build_*_action` helpers from
        // the four anchor starbridge-apps so the cross-app-e2e demo can drive
        // a real running node over MCP and have each receipt carry a STARK
        // proof (via `generate_effect_vm_proof`). See `apply.rs` parallel:
        // the executor turns the action's `SetField`s into ledger writes,
        // and we project those same `SetField`s into VM Effects to anchor
        // the proof.
        McpToolDef {
            name: "dregg_register_name",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Register a name in a starbridge-nameservice registry cell via the canonical credential-attested builder. Wraps `starbridge_nameservice::build_register_with_credential_action` (the attested-tier variant). Receipt carries STARK proof binding the three SetField updates (name_hash, owner_hash, expiry).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable name being registered (e.g. 'bob.dev')." },
                    "registry_cell": { "type": "string", "description": "Hex-encoded 32-byte registry cell ID. Defaults to the node's agent cell." },
                    "owner": { "type": "string", "description": "Hex-encoded 32-byte owner public key. Defaults to the node's cipherclerk public key." },
                    "expiry_height": { "type": "integer", "description": "Block height at which the name registration expires." },
                    "issuer_cell": { "type": "string", "description": "Hex-encoded 32-byte issuer cell whose credential set the registration attests to. Defaults to the node's agent cell (self-attestation for demos)." },
                    "credential_schema_id": { "type": "string", "description": "Hex-encoded 32-byte schema commitment from the identity app. Defaults to BLAKE3('kyc-v1') for demos." },
                    "credential_presentation_proof_hex": { "type": "string", "description": "Hex-encoded credential presentation proof bytes (non-empty witness blob carried into action.witness_blobs)." }
                },
                "required": ["name", "expiry_height"]
            }),
        },
        McpToolDef {
            name: "dregg_publish_subscription",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Publish a bounty-state notification to a starbridge-subscription cell via the canonical bounty-lifecycle builder. Wraps `starbridge_subscription::build_bounty_state_publish_action`. Receipt carries STARK proof binding the three SetField updates (seq_head, message_root, latest_payload).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "subscription_cell": { "type": "string", "description": "Hex-encoded 32-byte subscription cell ID. Defaults to the node's agent cell." },
                    "new_head": { "type": "integer", "description": "New value of slot 0 (seq_head); the caller computes from prior state." },
                    "new_message_root": { "type": "string", "description": "Hex-encoded 32-byte new message_root after folding the payload hash." },
                    "bounty_id": { "type": "string", "description": "Hex-encoded 32-byte bounty identifier." },
                    "prior_state": { "type": "string", "enum": ["posted","claimed","fulfilled","settled","canceled"], "description": "Prior bounty state." },
                    "new_state": { "type": "string", "enum": ["posted","claimed","fulfilled","settled","canceled"], "description": "New bounty state." },
                    "actor_pk_hash": { "type": "string", "description": "Hex-encoded 32-byte BLAKE3 hash of the actor's pubkey (the party causing the state change)." }
                },
                "required": ["new_head", "new_message_root", "bounty_id", "prior_state", "new_state", "actor_pk_hash"]
            }),
        },
        McpToolDef {
            name: "dregg_issue_credential",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Issue a credential and anchor the issuance on a starbridge-identity issuer cell via the canonical builder. Wraps `dregg_credentials::issue` + `starbridge_identity::build_issue_credential_action`. Receipt carries STARK proof binding the two SetField updates (issuance_counter, revocation_root) and the credential id is returned for downstream binding.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "issuer_cell": { "type": "string", "description": "Hex-encoded 32-byte issuer cell ID. Defaults to the node's agent cell." },
                    "schema": { "type": "string", "enum": ["kyc","gov_id","employment"], "description": "Which built-in schema to use. Defaults to 'kyc'." },
                    "holder_id": { "type": "string", "description": "Hex-encoded 32-byte holder id (typically BLAKE3(holder_pk)). Defaults to the node's own pubkey-derived holder id." },
                    "attributes": { "type": "object", "description": "Attribute map { name: string|integer }. Only attributes in the schema are accepted." },
                    "new_counter": { "type": "integer", "description": "New ISSUANCE_COUNTER_SLOT value (MonotonicSequence enforced; typically old+1). Defaults to 1." },
                    "revocation_root": { "type": "string", "description": "Hex-encoded 32-byte new REVOCATION_ROOT_SLOT value. Defaults to zero (no revocations yet)." },
                    "issued_at": { "type": "integer", "description": "Unix-seconds issuance timestamp. Defaults to 1_700_000_000 for determinism." },
                    "not_after": { "type": "integer", "description": "Optional Unix-seconds expiry. Omit for no expiry." }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "dregg_register_service",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Register a service entry at a named path on a starbridge-governed-namespace cell via the canonical builder. Wraps `starbridge_governed_namespace::build_register_service_action`. The underlying action is event-only (EmitEvent('service-registered', [path_hash, target])); the EffectVmAir carries a canonical EmitEvent row variant (#110) so the STARK proof binds the actual (topic_hash, payload_hash) of the emitted event into PI[EMIT_EVENT_TOPIC_HASH] / PI[EMIT_EVENT_PAYLOAD_HASH]. No synthesised state mutation is required.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "namespace_cell": { "type": "string", "description": "Hex-encoded 32-byte governed-namespace cell ID. Defaults to the node's agent cell." },
                    "path": { "type": "string", "description": "Path being registered (e.g. '/bob.dev')." },
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte cell ID the path resolves to. Defaults to the node's agent cell." }
                },
                "required": ["path"]
            }),
        },
        // ─── Factory creation via canonical Effect::CreateCellFromFactory ──────────
        McpToolDef {
            name: "dregg_create_cell_from_factory_effect",
            title: None,
            output_schema: None,
            annotations: None,
            description: "Emit a canonical `Effect::CreateCellFromFactory` inside a Turn so the new cell is created through the factory descriptor's validate_creation path (instead of the legacy direct insertion). Use this from the wasm/extension surface when a factory has been deployed and you want all child-cell creations to flow through the descriptor's constraints.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory VK." },
                    "owner_pubkey": { "type": "string", "description": "Hex-encoded 32-byte owner pubkey for the new cell. Defaults to this node's cipherclerk pubkey." },
                    "token_id": { "type": "string", "description": "Hex-encoded 32-byte token-domain id (default: BLAKE3(\"dregg-mcp-factory-token\"))." },
                    "sovereign": { "type": "boolean", "description": "Whether the new cell is sovereign (default: false)." },
                    "program_vk": { "type": "string", "description": "Hex-encoded 32-byte child program VK (must match the factory's Fixed strategy when set)." },
                    "initial_fields": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "index": { "type": "integer" },
                                "value": { "type": "integer" }
                            },
                            "required": ["index","value"]
                        },
                        "description": "Initial field overrides as { index, value } pairs (u32 index, u64 value)."
                    }
                },
                "required": ["factory_vk"]
            }),
        },
    ]
}

// =============================================================================
// Tool dispatch
// =============================================================================

/// The capability scope an MCP tool requires: an action VERB the caller's
/// `Authorization::Token` must cover. The resource (the granting authority) is
/// the node's own identity cell — the node is its own granting authority and
/// issues scoped tools-access biscuits against its key.
///
/// The verbs partition the ~45 tools by the authority they exercise:
/// - `"read"`   — pure observation (status / reads / list / verify), no mutation;
/// - `"write"`  — mutates cell/ledger/intent state on behalf of the caller;
/// - `"admin"`  — capability/identity administration (grant/revoke/delegate,
///   factories, sovereignty, federation governance) — the most powerful verb.
///
/// A capability credential that grants `"admin"` for the node's cell covers the
/// admin tools; one that grants only `"read"` does NOT — the executor rejects an
/// admin `tools/call` presenting a read-only token. A tool absent from this
/// table is treated as `"admin"` (fail-closed: an unmapped tool requires the
/// strongest authority rather than silently passing).
pub(super) fn tool_required_scope(tool: &str) -> &'static str {
    match tool {
        // ── read: observation only ───────────────────────────────────────────
        "dregg_get_status"
        | "dregg_check_capabilities"
        | "dregg_read_cell"
        | "dregg_list_cells"
        | "dregg_get_cap_graph"
        | "dregg_get_trustline_status"
        | "dregg_get_channel_status"
        | "dregg_get_receipt_chain"
        | "dregg_verify_provenance"
        | "dregg_verify_sovereign_proof"
        | "dregg_get_blocklace_status"
        | "dregg_get_constitution"
        | "dregg_check_resource_budget"
        | "dregg_list_auctions"
        | "dregg_dark_clearing_result" => "read",

        // ── write: state mutation on the caller's behalf ─────────────────────
        "dregg_authorize"
        | "dregg_submit_turn"
        | "dregg_post_intent"
        | "dregg_fulfill_intent"
        | "dregg_seal_data"
        | "dregg_unseal_data"
        | "dregg_prove_sovereign_turn"
        | "dregg_create_stealth_address"
        | "dregg_private_transfer"
        | "dregg_encrypt_intent"
        | "dregg_prove_predicate"
        | "dregg_compose_proofs"
        | "dregg_debit_shared_resource"
        | "dregg_place_bid"
        | "dregg_captp_deliver"
        | "dregg_exercise_handoff_cert"
        | "dregg_sign_sovereign_witness"
        | "dregg_bilateral_action"
        | "dregg_extend_trustline"
        | "dregg_register_name"
        | "dregg_publish_subscription"
        | "dregg_register_service"
        // Submitting an encrypted order and running the clear are caller-behalf state
        // mutations; standing up a session (a real BFV key ceremony that pins a trader
        // roster) is administration.
        | "dregg_dark_clearing_submit"
        | "dregg_dark_clearing_clear" => "write",

        // ── admin: capability / identity / governance administration ─────────
        "dregg_create_agent"
        | "dregg_grant_capability"
        | "dregg_revoke_capability"
        | "dregg_delegate"
        | "dregg_make_sovereign"
        | "dregg_peer_exchange"
        | "dregg_compress_history"
        | "dregg_create_bearer_cap"
        | "dregg_exercise_bearer_cap"
        | "dregg_deploy_factory"
        | "dregg_create_from_factory"
        | "dregg_create_cell_from_factory_effect"
        | "dregg_propose_membership"
        | "dregg_issue_credential"
        | "dregg_dark_clearing_open" => "admin",

        // Fail-closed: an unmapped tool requires the strongest authority.
        _ => "admin",
    }
}
