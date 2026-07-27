//! One real Chutes -> Dungeon turn.
//!
//! Chutes speaks the OpenAI-compatible tool-call wire through `dregg-narrator`.
//! The tool schema exposes only the commands legal in the Dungeon's current room.
//! The returned tool call is then re-admitted through Dungeon's existing closed
//! command parser before `narrate_turn` submits it to the real world executor.
//! Model prose is committed into the receipt, but it never becomes an effect.
//!
//! The hosted call is also made through `metered_converse`: the model must have an
//! operator-pinned Chutes price and the reservation must fit the local hard ceiling
//! before any HTTP request is sent.
//!
//! Run with the normal Chutes narrator variables plus a price pin:
//!
//! ```text
//! DREGG_NARRATOR_ENDPOINT=https://llm.chutes.ai/v1 \
//! DREGG_NARRATOR_API_KEY=... \
//! DREGG_NARRATOR_MODEL=... \
//! DREGG_NARRATOR_PRICE_INPUT_PER_1K=... \
//! DREGG_NARRATOR_PRICE_OUTPUT_PER_1K=... \
//! cargo run --example dungeon_chutes_turn
//! ```

use std::path::PathBuf;

use dregg_narrator::{
    BudgetLedger, ConverseBackend, ConverseRequest, ConverseResponse, ModelRegistry, NarratorError,
    OpenAiCompatClient, ToolDef, metered_converse,
};
use dungeon_on_dregg::narrator::{
    BrainRefusal, NarrateError, Narrated, NarratedReceipt, bound_narration_commit, legal_commands,
    narrate_turn, narration_commitment, parse_confined_response, scene_view,
};
use serde_json::json;
use spween::Scene;
use spween_dregg::{Value, WorldCell};

/// The one tool a Chutes model may invoke. Its per-room enum is the first wall;
/// Dungeon's own closed parser and executor are the second and third walls.
pub const DUNGEON_TURN_TOOL: &str = "submit_dungeon_turn";
pub const CHUTES_PROVIDER: &str = "chutes";
const NARRATION_PROVENANCE_DOMAIN: &str = "dregg.chutes-narration.v1";

/// Proof that this actor explicitly selected Chutes narration for this session.
/// Production callers should construct it only at an explicit UI/command boundary,
/// never from model output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChutesTurnOptIn {
    actor: String,
    session: String,
}

impl ChutesTurnOptIn {
    pub fn new(actor: impl Into<String>, session: impl Into<String>) -> Result<Self, WeldError> {
        let actor = actor.into();
        let session = session.into();
        validate_identity("actor", &actor)?;
        validate_identity("session", &session)?;
        Ok(Self { actor, session })
    }

    pub fn actor(&self) -> &str {
        &self.actor
    }

    pub fn session(&self) -> &str {
        &self.session
    }
}

/// Trusted operator provenance surfaced alongside the executor receipt. This is
/// intentionally not copied from untrusted model prose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChutesNarrationProvenance {
    pub provider: &'static str,
    pub model: String,
    pub actor: String,
    pub session: String,
    pub requested_room: Option<String>,
    pub input_tokens: u32,
    pub output_tokens: u32,
}

/// The authoritative Dungeon receipt, presentation-only prose, and the trusted
/// provider identity which the narration commitment binds.
#[derive(Clone, Debug)]
pub struct ChutesTurnReceipt {
    pub narrated: NarratedReceipt,
    pub display_narration: String,
    pub provenance: ChutesNarrationProvenance,
}

impl ChutesTurnReceipt {
    pub fn verify_provenance(&self) -> bool {
        let bound = bound_narration(
            &self.provenance.model,
            &self.provenance.actor,
            &self.provenance.session,
            self.provenance.requested_room.as_deref(),
            &self.display_narration,
        );
        self.provenance.provider == CHUTES_PROVIDER
            && self.narrated.narration == bound
            && self.narrated.narration_commit == narration_commitment(&bound)
            && bound_narration_commit(&self.narrated.receipt)
                == Some(self.narrated.narration_commit)
    }
}

/// Transactional player-credit boundary. `commit` and `release` are infallible
/// because a provider call must never leave player credit in limbo. This is
/// separate from [`BudgetLedger`], which records real operator USD spend even
/// when a paid response is later rejected as malformed.
pub trait NarrationCreditGate {
    type Hold;

    fn hold(&self, opt_in: &ChutesTurnOptIn) -> Result<Self::Hold, String>;
    fn commit(&self, hold: Self::Hold);
    fn release(&self, hold: Self::Hold);
}

/// A refusal at one of the real boundaries in the Chutes -> Dungeon path.
#[derive(Debug)]
pub enum WeldError {
    /// The current scene has ended or is not part of the closed command vocabulary.
    NoLegalCommands,
    /// The hosted call was unpriced, over budget, or failed.
    Provider(NarratorError),
    /// A player-credit hold could not be created before contacting the provider.
    Credit(String),
    /// The provider response did not contain the one required typed tool call.
    Protocol(String),
    /// Dungeon's existing closed channel rejected the command or narration.
    Refused(BrainRefusal),
    /// The world moved while inference was in flight; a command for an old room is stale.
    StaleScene {
        requested: Option<String>,
        current: Option<String>,
    },
    /// Any same-room world change also makes the model's snapshot stale.
    StaleWorld {
        requested_nonce: u64,
        current_nonce: u64,
    },
    /// The real Dungeon executor refused the proposed turn.
    World(NarrateError),
}

impl std::fmt::Display for WeldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WeldError::NoLegalCommands => {
                write!(f, "the current dungeon room has no legal commands")
            }
            WeldError::Provider(err) => write!(f, "metered Chutes call failed: {err}"),
            WeldError::Credit(why) => write!(f, "player narration credit unavailable: {why}"),
            WeldError::Protocol(why) => {
                write!(f, "Chutes response violated the turn protocol: {why}")
            }
            WeldError::Refused(err) => {
                write!(f, "Dungeon closed channel refused the proposal: {err}")
            }
            WeldError::StaleScene { requested, current } => write!(
                f,
                "dungeon scene changed during inference ({requested:?} -> {current:?}); refusing stale command"
            ),
            WeldError::StaleWorld {
                requested_nonce,
                current_nonce,
            } => write!(
                f,
                "dungeon world changed during inference (nonce {requested_nonce} -> {current_nonce}); refusing stale command"
            ),
            WeldError::World(err) => write!(f, "Dungeon executor refused the proposal: {err}"),
        }
    }
}

impl std::error::Error for WeldError {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WorldHead {
    snapshot: Vec<u64>,
    /// The committed cell nonce changes on every admitted turn even if a
    /// future game verb happens to restore the same story-variable snapshot.
    nonce: u64,
}

fn world_head(world: &WorldCell) -> WorldHead {
    WorldHead {
        snapshot: world.snapshot(),
        nonce: world
            .cell_snapshot()
            .map(|cell| cell.state.nonce())
            .unwrap_or_default(),
    }
}

fn validate_identity(label: &str, value: &str) -> Result<(), WeldError> {
    let valid = !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"-_.:/@".contains(&byte));
    if valid {
        Ok(())
    } else {
        Err(WeldError::Protocol(format!(
            "{label} must be 1..=128 safe ASCII identity bytes"
        )))
    }
}

fn validate_model(model: &str) -> Result<(), WeldError> {
    if model.is_empty()
        || model.len() > 512
        || model
            .chars()
            .any(|ch| ch.is_control() || matches!(ch, '{' | '}'))
    {
        return Err(WeldError::Protocol(
            "model identity is empty, too long, or contains unsafe delimiters".to_string(),
        ));
    }
    Ok(())
}

fn bound_narration(
    model: &str,
    actor: &str,
    session: &str,
    room: Option<&str>,
    display_narration: &str,
) -> String {
    // An array has stable ordering, allowing an independent verifier to rebuild
    // the exact bytes without depending on JSON object key ordering.
    serde_json::to_string(&json!([
        NARRATION_PROVENANCE_DOMAIN,
        CHUTES_PROVIDER,
        model,
        actor,
        session,
        room,
        display_narration,
    ]))
    .expect("serializing strings into a JSON array is infallible")
}

/// Build the actual OpenAI-compatible request for the current Dungeon scene.
///
/// The JSON Schema enum is derived from [`legal_commands`], rather than duplicating
/// room rules in this seam. An ended/unknown room refuses before the provider call.
pub fn chutes_request(
    model: &str,
    view: &dungeon_on_dregg::narrator::SceneView,
    max_tokens: u32,
) -> Result<ConverseRequest, WeldError> {
    validate_model(model)?;
    let commands: Vec<String> = legal_commands(view)
        .iter()
        .map(|offered| offered.keyword.clone())
        .collect();
    if commands.is_empty() {
        return Err(WeldError::NoLegalCommands);
    }

    let room = view.room.as_deref().unwrap_or("(ended)");
    let command_list = legal_commands(view)
        .iter()
        .map(|offered| format!("`{}` ({})", offered.keyword, offered.prompt))
        .collect::<Vec<_>>()
        .join(", ");
    let mut request = ConverseRequest::plain(
        model,
        "You are a dungeon narrator. The world executor is the sole authority: you may select one offered command and narrate it, but your prose cannot create items, alter stats, or change outcomes. Reply only by calling submit_dungeon_turn.",
        format!(
            "The party is in `{room}`. Select exactly one currently legal command: {command_list}. Supply one or two vivid sentences as narration."
        ),
        max_tokens,
    );
    request.tools.push(ToolDef {
        name: DUNGEON_TURN_TOOL.to_string(),
        description:
            "Submit one command from the current room and prose that has no state-transition authority."
                .to_string(),
        input_schema: json!({
            "type": "object",
            "additionalProperties": false,
            "required": ["command", "narration"],
            "properties": {
                "command": {
                    "type": "string",
                    "enum": commands,
                    "description": "One command copied from the current room's closed legal set."
                },
                "narration": {
                    "type": "string",
                    "description": "One or two sentences of flavor prose. Prose cannot change world state."
                }
            }
        }),
    });
    Ok(request)
}

/// Convert one OpenAI-compatible tool call into Dungeon's native typed proposal.
///
/// This deliberately reuses [`parse_confined_response`]. The provider's JSON Schema
/// is guidance; the parser is the fail-closed semantic boundary, so a model that emits
/// a wrong-room command or injecting narration is refused even if a provider skipped
/// schema validation.
pub fn admitted_proposal(
    view: &dungeon_on_dregg::narrator::SceneView,
    response: &ConverseResponse,
) -> Result<Narrated, WeldError> {
    if !response.text.trim().is_empty() {
        return Err(WeldError::Protocol(
            "expected a tool-only response; assistant prose must be carried by `narration`"
                .to_string(),
        ));
    }
    if response.tool_calls.len() != 1 {
        return Err(WeldError::Protocol(format!(
            "expected exactly one `{DUNGEON_TURN_TOOL}` call, got {}",
            response.tool_calls.len()
        )));
    }
    let call = &response.tool_calls[0];
    if call.name != DUNGEON_TURN_TOOL {
        return Err(WeldError::Protocol(format!(
            "expected tool `{DUNGEON_TURN_TOOL}`, got `{}`",
            call.name
        )));
    }
    let input = call
        .input
        .as_object()
        .ok_or_else(|| WeldError::Protocol("tool input must be a JSON object".to_string()))?;
    if input.len() != 2 || !input.contains_key("command") || !input.contains_key("narration") {
        return Err(WeldError::Protocol(
            "tool input must contain exactly `command` and `narration`".to_string(),
        ));
    }
    let command = input
        .get("command")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| WeldError::Protocol("tool input has no string `command`".to_string()))?;
    if command.trim() != command || command.contains('\r') || command.contains('\n') {
        return Err(WeldError::Protocol(
            "tool `command` must be one unpadded line".to_string(),
        ));
    }
    let narration = input
        .get("narration")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| WeldError::Protocol("tool input has no string `narration`".to_string()))?;

    // One native admission path: do not mirror Dungeon's command mapping here.
    let native = format!("COMMAND: {command}\nNARRATION: {narration}");
    parse_confined_response(view, &native).map_err(WeldError::Refused)
}

/// Make one budgeted Chutes call and resolve its admitted proposal as one real
/// Dungeon executor turn.
pub fn run_chutes_turn(
    backend: &(dyn ConverseBackend + Send + Sync),
    ledger: &BudgetLedger,
    registry: &ModelRegistry,
    model: &str,
    max_tokens: u32,
    world: &WorldCell,
    scene: &Scene,
    opt_in: &ChutesTurnOptIn,
) -> Result<ChutesTurnReceipt, WeldError> {
    let requested_view = scene_view(world, scene);
    let requested_head = world_head(world);
    let request = chutes_request(model, &requested_view, max_tokens)?;
    let response =
        metered_converse(ledger, registry, backend, &request).map_err(WeldError::Provider)?;

    // A hosted call crosses time. Never apply a command selected for a room that is no
    // longer current when the response returns.
    // The WHOLE view, not just the room name: the view carries the derived legal set, and a
    // move can leave that set without the room changing (a write-once slot claimed, a budget
    // spent, a ratchet shut).
    let current_view = scene_view(world, scene);
    if current_view != requested_view {
        return Err(WeldError::StaleScene {
            requested: requested_view.room,
            current: current_view.room,
        });
    }
    let current_head = world_head(world);
    if current_head != requested_head {
        return Err(WeldError::StaleWorld {
            requested_nonce: requested_head.nonce,
            current_nonce: current_head.nonce,
        });
    }

    let narrated = admitted_proposal(&current_view, &response)?;
    let display_narration = narrated.narration.clone();
    let bound = Narrated {
        command: narrated.command,
        narration: bound_narration(
            model,
            opt_in.actor(),
            opt_in.session(),
            requested_view.room.as_deref(),
            &display_narration,
        ),
    };
    let narrated = narrate_turn(world, scene, &bound).map_err(WeldError::World)?;
    let provenance = ChutesNarrationProvenance {
        provider: CHUTES_PROVIDER,
        model: model.to_string(),
        actor: opt_in.actor().to_string(),
        session: opt_in.session().to_string(),
        requested_room: requested_view.room,
        input_tokens: response.input_tokens,
        output_tokens: response.output_tokens,
    };
    let out = ChutesTurnReceipt {
        narrated,
        display_narration,
        provenance,
    };
    debug_assert!(out.verify_provenance());
    Ok(out)
}

/// Production charging boundary: reserve before the provider call, consume only
/// after the real executor returns a provenance-bound receipt, and release on
/// every refusal or failure.
pub fn run_chutes_turn_with_credit<G: NarrationCreditGate>(
    backend: &(dyn ConverseBackend + Send + Sync),
    ledger: &BudgetLedger,
    registry: &ModelRegistry,
    model: &str,
    max_tokens: u32,
    world: &WorldCell,
    scene: &Scene,
    opt_in: &ChutesTurnOptIn,
    credit: &G,
) -> Result<ChutesTurnReceipt, WeldError> {
    let hold = credit.hold(opt_in).map_err(WeldError::Credit)?;
    match run_chutes_turn(
        backend, ledger, registry, model, max_tokens, world, scene, opt_in,
    ) {
        Ok(receipt) => {
            credit.commit(hold);
            Ok(receipt)
        }
        Err(err) => {
            credit.release(hold);
            Err(err)
        }
    }
}

fn env_positive_f64(name: &str, default: f64) -> f64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.trim().parse::<f64>().ok())
        .filter(|v| v.is_finite() && *v > 0.0)
        .unwrap_or(default)
}

fn env_positive_u32(name: &str, default: u32) -> u32 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.trim().parse::<u32>().ok())
        .filter(|v| *v > 0)
        .unwrap_or(default)
}

fn live() -> Result<(), WeldError> {
    let model = std::env::var("DREGG_NARRATOR_MODEL").map_err(|_| {
        WeldError::Protocol(
            "DREGG_NARRATOR_MODEL must name a priced Chutes catalog model".to_string(),
        )
    })?;
    let backend = OpenAiCompatClient::from_env().map_err(|err| {
        WeldError::Protocol(format!("cannot configure the Chutes HTTP client: {err}"))
    })?;
    let registry = ModelRegistry::builtin();
    let cap = env_positive_f64("DREGG_NARRATOR_BUDGET_USD", 0.05);
    let max_tokens = env_positive_u32("DREGG_NARRATOR_MAX_TOKENS", 256);
    let ledger_path = std::env::var_os("DREGG_NARRATOR_LEDGER")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join("dungeon-chutes-ledger.json"));
    let ledger = BudgetLedger::new(&ledger_path, cap);

    let scene = dungeon_on_dregg::keep_scene();
    let mut world = dungeon_on_dregg::deploy_keep(63);
    world.seed_var("hp", Value::Int(50));
    let opt_in = ChutesTurnOptIn::new("standalone-operator", "standalone-example")?;

    let result = run_chutes_turn(
        &backend, &ledger, &registry, &model, max_tokens, &world, &scene, &opt_in,
    )?;

    println!("command: {:?}", result.narrated.command);
    println!("narration: {}", result.display_narration);
    println!(
        "provider: {}:{}",
        result.provenance.provider, result.provenance.model
    );
    println!(
        "turn_hash: {}",
        hex::encode(result.narrated.receipt.turn_hash)
    );
    println!("hp: {}", world.read_var("hp"));
    println!("gold: {}", world.read_var("gold"));
    println!("ledger: {}", ledger_path.display());
    Ok(())
}

fn main() {
    if let Err(err) = live() {
        eprintln!("dungeon Chutes turn refused: {err}");
        std::process::exit(2);
    }
}
