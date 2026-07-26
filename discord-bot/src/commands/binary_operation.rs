//! Ordinary Discord attachment ingress for offering `binary_operations`.
//!
//! A player's private producer emits a canonical receipt; the player attaches
//! it to the slash command named on the live surface. Discord supplies metadata
//! first, so this adapter selects the exact live descriptor and refuses an
//! oversize object before touching the CDN. The streamed body is capped again,
//! its actual size must match Discord's declaration, and descriptor selection is
//! repeated on the offering store thread immediately before the owning offering
//! decodes/mutates. Attachment MIME metadata is advisory (Discord guesses it and
//! users cannot set vendor types); the explicit operation name selects the
//! canonical decoder and the expected media type is shown verbatim.

use serenity::all::{
    Attachment, CommandDataOptionValue, CommandInteraction, Context, CreateActionRow, CreateEmbed,
};

use dreggnet_offerings::{
    BinaryOperationDescriptor, BinaryOperationReceipt, ChatBinaryOperationPolicy, DreggIdentity,
    JournaledBinaryOperation, invoke_journaled_binary_operation, preflight_chat_binary_operation,
};

use crate::BotState;
use crate::commands::ack;
use crate::commands::offering::{
    self, CollectiveRound, ControlStamp, DiscordOffering, identity_of, with_live_transaction,
};

/// Metadata policy plus the exact live session/state-or-round head that
/// authorized the pre-download check. The full stamp survives the CDN await
/// and is compared again inside the mutation job.
pub struct BinaryPreflight {
    pub policy: ChatBinaryOperationPolicy,
    pub stamp: ControlStamp,
}

/// The fields appended to a Discord offering embed for each live opaque
/// operation. Each body is below Discord's 1024-character field ceiling for the
/// deployed private-game disclosures and names the exact slash attachment UX.
pub fn affordance_fields(operations: &[BinaryOperationDescriptor]) -> Vec<(String, String)> {
    operations
        .iter()
        .map(|operation| {
            let maximum = operation
                .max_input_bytes
                .min(dreggnet_offerings::MAX_CHAT_BINARY_OPERATION_BYTES);
            (
                format!("🔐 {}", operation.title),
                format!(
                    "Attach the canonical producer receipt with `/adventure dungeon operation name:{} receipt:<file>`. Expected `{}`; maximum {} bytes.\n{}",
                    operation.name, operation.input_media_type, maximum, operation.disclosure
                ),
            )
        })
        .collect()
}

/// Discover and metadata-preflight one exact live operation before a CDN GET.
pub fn preflight_in<O: DiscordOffering>(
    channel: u64,
    name: &str,
    declared_bytes: usize,
) -> Result<BinaryPreflight, String> {
    offering::with_live::<O, _>(channel, {
        let name = name.to_string();
        move |live| {
            let operations = live.offering.binary_operations(&live.session);
            let policy = preflight_chat_binary_operation(&operations, &name, declared_bytes)
                .map_err(|error| error.to_string())?;
            Ok(BinaryPreflight {
                policy,
                stamp: live.control_stamp(),
            })
        }
    })
    .ok_or_else(|| format!("no {} session is open in this channel", O::KEY))?
}

/// Re-check the live descriptor and actual byte count on the store thread, then
/// hand the opaque bytes to the offering's sole decoder/mutator. The boolean is
/// true only when a collective action change opened a fresh ballot round.
pub fn apply_in<O: DiscordOffering>(
    channel: u64,
    stamp: ControlStamp,
    name: &str,
    declared_bytes: usize,
    payload: Vec<u8>,
    actor: DreggIdentity,
) -> Result<(BinaryOperationReceipt, bool), String> {
    let actual_bytes = payload.len();
    with_live_transaction::<O, _>(channel, {
        let name = name.to_string();
        move |live| {
            if live.control_stamp() != stamp {
                return (
                    Err(
                        "the session or state/round head changed while the receipt was in flight; nothing was applied"
                            .to_string(),
                    ),
                    false,
                );
            }
            let operations = live.offering.binary_operations(&live.session);
            let policy = match preflight_chat_binary_operation(&operations, &name, declared_bytes) {
                Ok(policy) => policy,
                Err(error) => return (Err(error.to_string()), false),
            };
            if let Err(error) = policy.validate_body_len(actual_bytes) {
                return (Err(error.to_string()), false);
            }
            let replay_material = live
                .offering
                .binary_operation_replay_material(&live.session, &name, &payload);
            let journal_id = live.journal.id.clone();
            let transaction = invoke_journaled_binary_operation(
                O::KEY,
                &journal_id,
                &name,
                &payload,
                actor.clone(),
                &mut live.journal,
                live.resume_store.as_deref(),
                replay_material,
                || {
                    live.offering.invoke_binary_operation(
                        &mut live.session,
                        &name,
                        &payload,
                        actor,
                    )
                },
            );
            let receipt = match transaction {
                JournaledBinaryOperation::Applied(receipt) => receipt,
                JournaledBinaryOperation::Refused(error) => {
                    return (Err(error.to_string()), false);
                }
                JournaledBinaryOperation::Quarantine(error) => {
                    return (Err(error.to_string()), true);
                }
            };

            // A successful opaque operation is a state transition even when
            // its public action labels happen to be unchanged. Advance the
            // control head unconditionally; collective sessions open a fresh
            // numbered ballot and clear all pre-operation ballots.
            let next_actions = live.offering.actions(&live.session);
            let round_changed = if let Some(round) = live.round.as_ref() {
                let next_round = round.round.saturating_add(1);
                live.control_head = next_round;
                let electorate = round
                    .electorate
                    .clone()
                    .map(|members| members.into_iter().map(DreggIdentity).collect::<Vec<_>>());
                live.round = Some(CollectiveRound::new(next_round, next_actions, electorate));
                true
            } else {
                live.control_head = live.control_head.saturating_add(1);
                false
            };
            (Ok((receipt, round_changed)), false)
        }
    })
    .ok_or_else(|| format!("no {} session is open in this channel", O::KEY))?
}

/// Stream one trusted Discord interaction attachment through a hard ceiling.
async fn download_bounded(attachment: &Attachment, maximum: usize) -> Result<Vec<u8>, String> {
    if attachment.size as usize > maximum {
        return Err(format!(
            "Discord declares {} bytes; this operation accepts at most {maximum}",
            attachment.size
        ));
    }
    let mut response = reqwest::Client::new()
        .get(&attachment.url)
        .send()
        .await
        .map_err(|error| format!("Discord CDN download failed: {error}"))?
        .error_for_status()
        .map_err(|error| format!("Discord CDN refused the download: {error}"))?;
    if response
        .content_length()
        .is_some_and(|length| length > maximum as u64)
    {
        return Err(format!(
            "Discord CDN response exceeds the {maximum}-byte operation limit"
        ));
    }
    let mut bytes = Vec::with_capacity((attachment.size as usize).min(maximum));
    while let Some(chunk) = response
        .chunk()
        .await
        .map_err(|error| format!("could not read the operation attachment: {error}"))?
    {
        if bytes.len().saturating_add(chunk.len()) > maximum {
            return Err(format!(
                "downloaded attachment exceeds the {maximum}-byte operation limit"
            ));
        }
        bytes.extend_from_slice(&chunk);
    }
    Ok(bytes)
}

fn operation_name(command: &CommandInteraction) -> Option<String> {
    let sub = command.data.options.first()?;
    let options = match &sub.value {
        CommandDataOptionValue::SubCommand(options) => options,
        _ => return None,
    };
    options.iter().find_map(|option| {
        (option.name == "name")
            .then_some(&option.value)
            .and_then(|value| match value {
                CommandDataOptionValue::String(value) => Some(value.clone()),
                _ => None,
            })
    })
}

fn receipt_attachment<'a>(command: &'a CommandInteraction) -> Option<&'a Attachment> {
    let sub = command.data.options.first()?;
    let options = match &sub.value {
        CommandDataOptionValue::SubCommand(options) => options,
        _ => return None,
    };
    options.iter().find_map(|option| {
        if option.name != "receipt" {
            return None;
        }
        match &option.value {
            CommandDataOptionValue::Attachment(id) => command.data.resolved.attachments.get(id),
            _ => None,
        }
    })
}

/// Production slash handler shared by ordinary Discord offering commands.
/// Returns true when the caller must publish the newly opened collective round.
pub async fn handle_upload<O: DiscordOffering>(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
) -> bool {
    // The receipt and public result are player-facing; keep the response
    // ephemeral even when the game board itself is shared.
    ack::defer_slash(ctx, command, true).await;
    let Some(name) = operation_name(command) else {
        respond(
            ctx,
            command,
            "Receipt upload is incomplete",
            "Choose the exact operation name shown on the live dungeon surface.",
            0xE39B32,
        )
        .await;
        return false;
    };
    let Some(attachment) = receipt_attachment(command) else {
        respond(
            ctx,
            command,
            "Attach the canonical producer receipt",
            "The `receipt` attachment is required; no operation was invoked.",
            0xE39B32,
        )
        .await;
        return false;
    };
    let channel = command.channel_id.get();
    let preflight = match preflight_in::<O>(channel, &name, attachment.size as usize) {
        Ok(preflight) => preflight,
        Err(reason) => {
            respond(
                ctx,
                command,
                "Receipt refused before download",
                &reason,
                0xE63946,
            )
            .await;
            return false;
        }
    };
    let payload = match download_bounded(attachment, preflight.policy.transport_max_bytes).await {
        Ok(payload) => payload,
        Err(reason) => {
            respond(
                ctx,
                command,
                "Receipt could not be transported",
                &reason,
                0xE63946,
            )
            .await;
            return false;
        }
    };
    let actor = identity_of(state, command.user.id.get());
    match apply_in::<O>(
        channel,
        preflight.stamp,
        &name,
        attachment.size as usize,
        payload,
        actor,
    ) {
        Err(reason) => {
            respond(
                ctx,
                command,
                "The operation verifier refused the receipt",
                &reason,
                0xE63946,
            )
            .await;
            false
        }
        Ok((receipt, round_changed)) => {
            let fields = receipt
                .public_fields
                .iter()
                .map(|(name, value)| format!("`{name}` = `{value}`"))
                .collect::<Vec<_>>()
                .join("\n");
            let detail = format!(
                "Applied `{}`.\nReceipt `{}`{}",
                receipt.operation,
                hex::encode(receipt.receipt_id),
                if fields.is_empty() {
                    String::new()
                } else {
                    format!("\n{fields}")
                }
            );
            respond(
                ctx,
                command,
                "Private producer receipt verified and applied",
                &detail,
                0x3D8B7D,
            )
            .await;
            round_changed
        }
    }
}

async fn respond(
    ctx: &Context,
    command: &CommandInteraction,
    title: &str,
    description: &str,
    color: u32,
) {
    let embed = CreateEmbed::new()
        .title(title)
        .description(offering::truncate(description, 4000))
        .color(color);
    ack::edit_slash(ctx, command, embed, Vec::<CreateActionRow>::new()).await;
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::sync::OnceLock;

    use deos_view::ViewNode;
    use dreggnet_offerings::dungeon::{
        DungeonOffering, PRIVATE_PREFERENCE_OPERATION, PRIVATE_QUEST_OPERATION,
        PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
    };
    use dreggnet_offerings::{
        Action, BinaryOperationError, BinaryOperationReplayMaterial, FileResumeStore,
        MAX_CHAT_BINARY_OPERATION_BYTES, Offering, OfferingError, OfferingHost, Outcome, RunCost,
        SessionConfig, SessionResumeStore, Surface, VerifyReport,
    };

    use super::*;
    use crate::commands::offering::{
        CollectiveClose, Store, close_in, close_round, open_in, open_in_with_resume_store,
        quench_in, with_live,
    };

    const PREFERENCE: &str = "dungeon.private-party-preference.v1";
    const SHUFFLE_COMMIT: &str = "dungeon.private-fair-shuffle.commit.v1";
    const SHUFFLE_PROVE: &str = "dungeon.private-fair-shuffle.prove.v1";
    const SHUFFLE_REVEAL: &str = "dungeon.private-fair-shuffle.reveal.v1";
    const QUEST: &str = "dungeon.private-quest-reduction.v1";

    const OPERATIONS: [(&str, &str, usize); 5] = [
        (
            PREFERENCE,
            "application/vnd.dregg.private-party-preference.v1+postcard",
            MAX_CHAT_BINARY_OPERATION_BYTES,
        ),
        (
            SHUFFLE_COMMIT,
            "application/vnd.dregg.private-fair-shuffle-commit.v1",
            33,
        ),
        (
            SHUFFLE_PROVE,
            "application/vnd.dregg.private-fair-shuffle-proof.v1+postcard",
            MAX_CHAT_BINARY_OPERATION_BYTES,
        ),
        (
            SHUFFLE_REVEAL,
            "application/vnd.dregg.private-fair-shuffle-opening.v1+postcard",
            64 * 1024,
        ),
        (
            QUEST,
            "application/vnd.dregg.private-quest-reduction.v1+postcard",
            MAX_CHAT_BINARY_OPERATION_BYTES,
        ),
    ];

    struct Fixture;

    impl Offering for Fixture {
        type Session = Vec<String>;

        fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
            Ok(Vec::new())
        }
        fn actions(&self, session: &Self::Session) -> Vec<Action> {
            let cursor = i64::try_from(session.len()).expect("fixture session length fits i64");
            vec![Action::new(
                format!("fixture move {}", session.len()),
                "fixture-move",
                cursor,
                true,
            )]
        }
        fn advance(
            &self,
            session: &mut Self::Session,
            input: Action,
            _actor: DreggIdentity,
        ) -> Outcome {
            let expected = i64::try_from(session.len()).expect("fixture session length fits i64");
            if input.turn != "fixture-move" || input.arg != expected {
                return Outcome::Refused("invalid fixture move".to_string());
            }
            session.push(format!("move:{expected}"));
            Outcome::Landed {
                receipt: dregg_app_framework::TurnReceipt::default(),
                ended: false,
            }
        }
        fn verify(&self, session: &Self::Session) -> VerifyReport {
            VerifyReport::ok(session.len())
        }
        fn render(&self, _session: &Self::Session) -> Surface {
            Surface(ViewNode::Text("fixture".to_string()))
        }
        fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
            OPERATIONS
                .into_iter()
                .map(|(name, media, maximum)| BinaryOperationDescriptor {
                    name: name.to_string(),
                    title: format!("Submit {name}"),
                    input_media_type: media.to_string(),
                    max_input_bytes: maximum,
                    disclosure: format!("Exact disclosure for {name}."),
                })
                .collect()
        }
        fn binary_operation_replay_material(
            &self,
            _session: &Self::Session,
            name: &str,
            payload: &[u8],
        ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
            if !OPERATIONS
                .iter()
                .any(|(candidate, _, _)| *candidate == name)
            {
                return Err(BinaryOperationError::UnknownOperation(name.to_string()));
            }
            if payload != b"receipt" {
                return Err(BinaryOperationError::Malformed("not canonical".to_string()));
            }
            Ok(Some(BinaryOperationReplayMaterial::new(
                payload.to_vec(),
                "The fixture retains its canonical public receipt.",
            )))
        }
        fn invoke_binary_operation(
            &self,
            session: &mut Self::Session,
            name: &str,
            payload: &[u8],
            _actor: DreggIdentity,
        ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
            if payload != b"receipt" {
                return Err(BinaryOperationError::Malformed("not canonical".to_string()));
            }
            session.push(name.to_string());
            Ok(BinaryOperationReceipt {
                operation: name.to_string(),
                receipt_id: [9; 32],
                public_fields: Vec::new(),
            })
        }
        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    impl DiscordOffering for Fixture {
        const KEY: &'static str = "fixture-private-dungeon";
        const TITLE: &'static str = "Fixture";
        const COLOR: u32 = 0;
        const TAGLINE: &'static str = "fixture";

        fn store() -> &'static Store<Self> {
            static STORE: OnceLock<Store<Fixture>> = OnceLock::new();
            STORE.get_or_init(Store::spawn)
        }

        fn status_line(&self, session: &Self::Session) -> String {
            format!("{} receipt(s)", session.len())
        }

        fn collective() -> bool {
            true
        }
    }

    struct ReceiptConfusionFixture;

    impl Offering for ReceiptConfusionFixture {
        type Session = u64;

        fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
            Ok(0)
        }

        fn actions(&self, _session: &Self::Session) -> Vec<Action> {
            Vec::new()
        }

        fn advance(
            &self,
            _session: &mut Self::Session,
            _input: Action,
            _actor: DreggIdentity,
        ) -> Outcome {
            Outcome::Refused("fixture has no ordinary turns".to_string())
        }

        fn verify(&self, session: &Self::Session) -> VerifyReport {
            VerifyReport::ok(usize::try_from(*session).unwrap_or(usize::MAX))
        }

        fn render(&self, session: &Self::Session) -> Surface {
            Surface(ViewNode::Text(format!("confused = {session}")))
        }

        fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
            vec![BinaryOperationDescriptor {
                name: "addressed.v1".to_string(),
                title: "Addressed operation".to_string(),
                input_media_type: "application/vnd.dregg.addressed.v1".to_string(),
                max_input_bytes: 1,
                disclosure: "The one-byte fixture request is retained.".to_string(),
            }]
        }

        fn binary_operation_replay_material(
            &self,
            _session: &Self::Session,
            name: &str,
            payload: &[u8],
        ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
            if name != "addressed.v1" {
                return Err(BinaryOperationError::UnknownOperation(name.to_string()));
            }
            Ok(Some(BinaryOperationReplayMaterial::new(
                payload.to_vec(),
                "The one-byte fixture request is retained.",
            )))
        }

        fn invoke_binary_operation(
            &self,
            session: &mut Self::Session,
            _name: &str,
            _payload: &[u8],
            _actor: DreggIdentity,
        ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
            *session = 99;
            Ok(BinaryOperationReceipt {
                operation: "other.v1".to_string(),
                receipt_id: *blake3::hash(b"lying discord receipt").as_bytes(),
                public_fields: vec![("value".to_string(), "99".to_string())],
            })
        }

        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    impl DiscordOffering for ReceiptConfusionFixture {
        const KEY: &'static str = "discord-receipt-confusion";
        const TITLE: &'static str = "Receipt confusion fixture";
        const COLOR: u32 = 0;
        const TAGLINE: &'static str = "fixture";

        fn store() -> &'static Store<Self> {
            static STORE: OnceLock<Store<ReceiptConfusionFixture>> = OnceLock::new();
            STORE.get_or_init(Store::spawn)
        }

        fn status_line(&self, session: &Self::Session) -> String {
            format!("value {session}")
        }
    }

    #[test]
    fn discord_affordance_names_exact_private_game_routes_media_caps_and_disclosures() {
        let operations = Fixture.binary_operations(&Vec::new());
        let fields = affordance_fields(&operations);
        assert_eq!(fields.len(), OPERATIONS.len());
        for (operation, (_, body)) in operations.iter().zip(fields) {
            assert!(body.contains(&format!(
                "/adventure dungeon operation name:{} receipt:<file>",
                operation.name
            )));
            assert!(body.contains(&operation.input_media_type));
            assert!(body.contains(&format!("maximum {} bytes", operation.max_input_bytes)));
            assert!(body.ends_with(&operation.disclosure));
            assert!(body.len() <= 1024, "Discord field remains wire-valid");
        }
    }

    #[test]
    fn production_dungeon_descriptors_render_as_exact_discord_attachment_commands() {
        let offering = DungeonOffering::new();
        let session = offering
            .open(SessionConfig::with_seed(0xD15C_0AD))
            .expect("production dungeon opens");
        let operations = offering.binary_operations(&session);
        let names = operations
            .iter()
            .map(|operation| operation.name.as_str())
            .collect::<BTreeSet<_>>();
        for expected in [
            PRIVATE_PREFERENCE_OPERATION,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            PRIVATE_SHUFFLE_PROVE_OPERATION,
            PRIVATE_SHUFFLE_REVEAL_OPERATION,
            PRIVATE_QUEST_OPERATION,
        ] {
            assert!(names.contains(expected), "missing production {expected}");
        }

        for (operation, (_, body)) in operations.iter().zip(affordance_fields(&operations)) {
            assert!(body.contains(&format!(
                "/adventure dungeon operation name:{} receipt:<file>",
                operation.name
            )));
            assert!(body.contains(&operation.input_media_type));
            assert!(body.contains(&format!(
                "maximum {} bytes",
                operation
                    .max_input_bytes
                    .min(MAX_CHAT_BINARY_OPERATION_BYTES)
            )));
            assert!(body.contains(&operation.disclosure));
        }

        let channel = 0xD15C_0AD;
        close_in::<DungeonOffering>(channel);
        open_in::<DungeonOffering>(
            channel,
            DungeonOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("production Discord dungeon store opens");
        for expected in [
            PRIVATE_PREFERENCE_OPERATION,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            PRIVATE_SHUFFLE_PROVE_OPERATION,
            PRIVATE_SHUFFLE_REVEAL_OPERATION,
            PRIVATE_QUEST_OPERATION,
        ] {
            let policy = preflight_in::<DungeonOffering>(channel, expected, 0)
                .unwrap_or_else(|error| panic!("production route {expected} refused: {error}"));
            assert_eq!(policy.policy.descriptor.name, expected);
        }
        let stamp = preflight_in::<DungeonOffering>(channel, PRIVATE_PREFERENCE_OPERATION, 0)
            .unwrap()
            .stamp;
        assert!(
            apply_in::<DungeonOffering>(
                channel,
                stamp,
                PRIVATE_PREFERENCE_OPERATION,
                0,
                Vec::new(),
                actor(),
            )
            .is_err(),
            "the actual offering decoder, not the adapter, refuses malformed bytes"
        );
        close_in::<DungeonOffering>(channel);
    }

    /// ⚑ The command is registered on the LAB surface, not the global one. `24e47322b` took
    /// `dungeon` off `dreggnet_catalog::SHIPPED_KEYS`, and `/adventure` is a
    /// `Door::Offering("dungeon")` row — so it is registered only inside `DREGG_LAB_GUILD_ID` and
    /// `global_commands()` no longer carries it. This test read the GLOBAL set and
    /// `expect`ed it there, which made it a hard panic the moment the ship list changed; searching
    /// both surfaces is what it always meant (the question here is whether the operation option is
    /// BUILT, not where it is advertised — `menus::the_offering_doors_follow_the_ship_list` owns
    /// that question and derives the answer rather than pinning it).
    #[test]
    fn deployed_adventure_command_registers_the_operation_name_and_attachment() {
        let commands: Vec<serde_json::Value> = crate::commands::menus::global_commands()
            .into_iter()
            .chain(crate::commands::menus::lab_commands())
            .collect();
        let adventure = commands
            .iter()
            .find(|command| command["name"] == "adventure")
            .expect("/adventure is registered on one of the two surfaces");
        let dungeon = adventure["options"]
            .as_array()
            .and_then(|options| options.iter().find(|option| option["name"] == "dungeon"))
            .expect("dungeon is folded under /adventure");
        let operation = dungeon["options"]
            .as_array()
            .and_then(|options| options.iter().find(|option| option["name"] == "operation"))
            .expect("operation is registered under /adventure dungeon");
        let options = operation["options"].as_array().expect("operation options");
        let name = options
            .iter()
            .find(|option| option["name"] == "name")
            .expect("operation name option");
        let receipt = options
            .iter()
            .find(|option| option["name"] == "receipt")
            .expect("operation receipt option");
        assert_eq!(name["type"], 3, "name is a Discord string option");
        assert_eq!(receipt["type"], 11, "receipt is an attachment option");
        assert_eq!(name["required"], true);
        assert_eq!(receipt["required"], true);
    }

    #[test]
    fn discord_store_path_preflights_and_rechecks_before_the_offering_decoder() {
        let channel = 0xB1_AA7;
        close_in::<Fixture>(channel);
        open_in(channel, || Fixture, SessionConfig::with_seed(channel)).unwrap();

        assert!(preflight_in::<Fixture>(channel, "forged", 1).is_err());
        assert!(
            preflight_in::<Fixture>(channel, QUEST, MAX_CHAT_BINARY_OPERATION_BYTES + 1).is_err()
        );
        let stamp = preflight_in::<Fixture>(channel, QUEST, 7).unwrap().stamp;
        assert!(
            apply_in::<Fixture>(channel, stamp, QUEST, 7, b"short".to_vec(), actor(),).is_err()
        );
        let _ = with_live::<Fixture, _>(channel, |live| {
            live.round
                .as_mut()
                .expect("collective fixture has a round")
                .ballots
                .insert("old-voter".to_string(), 0);
        });
        let (receipt, round_changed) = apply_in::<Fixture>(
            channel,
            stamp,
            PREFERENCE,
            b"receipt".len(),
            b"receipt".to_vec(),
            actor(),
        )
        .expect("canonical bounded receipt applies");
        assert_eq!(receipt.operation, PREFERENCE);
        assert!(round_changed);
        let _ = with_live::<Fixture, _>(channel, |live| {
            let round = live.round.as_ref().expect("next round opened");
            assert_eq!(round.round, 1);
            assert_eq!(round.options[0].arg, 1);
            assert!(round.ballots.is_empty(), "stale-action ballots are reset");
        });
        let committed_len = with_live::<Fixture, _>(channel, |live| live.session.len()).unwrap();
        let stale = apply_in::<Fixture>(
            channel,
            stamp,
            PREFERENCE,
            b"receipt".len(),
            b"receipt".to_vec(),
            actor(),
        );
        assert!(
            stale.unwrap_err().contains("state/round head changed"),
            "a preflight from the prior head is refused"
        );
        assert_eq!(
            with_live::<Fixture, _>(channel, |live| live.session.len()),
            Some(committed_len),
            "a same-session stale preflight is mutation-free"
        );
        close_in::<Fixture>(channel);
    }

    #[test]
    fn an_in_flight_private_receipt_cannot_cross_a_session_replacement() {
        let channel = 0xB1_AA8;
        close_in::<Fixture>(channel);
        open_in(channel, || Fixture, SessionConfig::with_seed(channel)).unwrap();
        let preflight = preflight_in::<Fixture>(channel, PREFERENCE, b"receipt".len()).unwrap();

        open_in(channel, || Fixture, SessionConfig::with_seed(channel)).unwrap();
        let refused = apply_in::<Fixture>(
            channel,
            preflight.stamp,
            PREFERENCE,
            b"receipt".len(),
            b"receipt".to_vec(),
            actor(),
        );
        assert!(
            refused
                .unwrap_err()
                .contains("session or state/round head changed while the receipt was in flight")
        );
        assert_eq!(
            with_live::<Fixture, _>(channel, |live| live.session.len()),
            Some(0),
            "S1's downloaded receipt cannot mutate S2"
        );
        close_in::<Fixture>(channel);
    }

    #[test]
    fn discord_operation_journal_replays_through_offering_host_after_restart() {
        let channel = 0xB1_AA9;
        close_in::<Fixture>(channel);
        let scratch = tempfile::tempdir().expect("temporary durable journal root");
        let root = scratch.path().to_path_buf();
        open_in_with_resume_store::<Fixture>(
            channel,
            || Fixture,
            SessionConfig::with_seed(channel),
            {
                let root = root.clone();
                move || {
                    FileResumeStore::open(root)
                        .map(|store| Box::new(store) as Box<dyn SessionResumeStore>)
                        .map_err(|error| error.to_string())
                }
            },
        )
        .expect("durable Discord fixture opens");
        assert!(matches!(
            close_round::<Fixture>(channel),
            CollectiveClose::Resolved(resolved) if resolved.outcome.landed()
        ));
        let stamp = preflight_in::<Fixture>(channel, PREFERENCE, b"receipt".len())
            .unwrap()
            .stamp;
        apply_in::<Fixture>(
            channel,
            stamp,
            PREFERENCE,
            b"receipt".len(),
            b"receipt".to_vec(),
            actor(),
        )
        .expect("journalable Discord operation lands");

        let store = FileResumeStore::open(&root).expect("durable journal reopens");
        let logs = store.all();
        assert_eq!(logs.len(), 1);
        assert_eq!(logs[0].operations.len(), 1);
        assert_eq!(logs[0].moves.len(), 1);
        assert_eq!(logs[0].operations[0].after_moves, 1);
        // A CRASH, not a close: `quench_in` drops the live session and KEEPS the durable
        // record (`close_in` now forgets it — a close is a decision that the session is
        // over, and leaving its log behind would let the next press resurrect it).
        quench_in::<Fixture>(channel);

        let mut restarted = OfferingHost::new().with_resume_store(Box::new(store));
        restarted.register(Fixture::KEY, Fixture::TITLE, Fixture);
        let resumed = restarted.resume_all();
        assert_eq!(resumed.len(), 1);
        assert!(resumed[0].1.is_ok(), "{resumed:?}");
        assert_eq!(
            restarted.verify(Fixture::KEY, &logs[0].id).unwrap().turns,
            2,
            "OfferingHost replays the Discord move/operation timeline into the same state"
        );
    }

    #[test]
    fn returned_operation_name_confusion_quarantines_discord_and_restarts_before_the_ghost() {
        let channel = 0xB1_AAA;
        close_in::<ReceiptConfusionFixture>(channel);
        let scratch = tempfile::tempdir().expect("temporary durable journal root");
        let root = scratch.path().to_path_buf();
        open_in_with_resume_store::<ReceiptConfusionFixture>(
            channel,
            || ReceiptConfusionFixture,
            SessionConfig::with_seed(channel),
            {
                let root = root.clone();
                move || {
                    FileResumeStore::open(root)
                        .map(|store| Box::new(store) as Box<dyn SessionResumeStore>)
                        .map_err(|error| error.to_string())
                }
            },
        )
        .expect("durable confusion fixture opens");
        let stamp = preflight_in::<ReceiptConfusionFixture>(channel, "addressed.v1", 1)
            .unwrap()
            .stamp;
        let error = apply_in::<ReceiptConfusionFixture>(
            channel,
            stamp,
            "addressed.v1",
            1,
            vec![7],
            actor(),
        )
        .expect_err("a lying returned operation name must fail closed");
        assert!(error.contains("other.v1"), "{error}");
        assert!(error.contains("addressed.v1"), "{error}");
        assert!(error.contains("quarantined"), "{error}");
        assert!(
            with_live::<ReceiptConfusionFixture, _>(channel, |_| ()).is_none(),
            "the already-mutated Discord session is removed before the error returns"
        );

        let store = FileResumeStore::open(&root).expect("durable journal reopens");
        let logs = store.all();
        assert_eq!(logs.len(), 1);
        assert!(
            logs[0].operations.is_empty(),
            "the lying receipt and its ghost mutation are never journaled"
        );
        let mut restarted = OfferingHost::new().with_resume_store(Box::new(store));
        restarted.register(
            ReceiptConfusionFixture::KEY,
            ReceiptConfusionFixture::TITLE,
            ReceiptConfusionFixture,
        );
        restarted
            .resume(&logs[0])
            .expect("the exact pre-operation state remains resumable");
        assert!(
            format!(
                "{:?}",
                restarted
                    .render(ReceiptConfusionFixture::KEY, &logs[0].id)
                    .unwrap()
                    .0
            )
            .contains("confused = 0")
        );
    }

    fn actor() -> DreggIdentity {
        DreggIdentity("11".repeat(32))
    }
}
