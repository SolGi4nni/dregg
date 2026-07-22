//! Public Telegram command boundary for a shielded Bazaar crown claim.
//!
//! The player wire contains no proof, opening, order, note, Merkle path, root,
//! price, winner label, game head, or executor action.  The controller derives
//! the exact live Dungeon action from the viewer-blind common game spine,
//! verifies the winner signature, then resolves two public ids through trusted
//! typed custody and calls the durable catalog adapter.

use std::collections::BTreeMap;

use dregg_persist::{FinalizedFaithfulSpend, PersistentStore};
use dreggnet_catalog::{
    GameActionRef, GameAffordance, GameAudience, GameHostIncarnation, GameSessionRef,
    PrivateFheggGameConsequenceReceipt, ShieldedCrownAction, ShieldedCrownHand,
    ShieldedCrownOrchestrationError, ShieldedCrownPolicy, SignedGameAction,
    execute_shielded_crown_action, inspect_bound_game_session, verify_signed_game_action,
};
use dreggnet_market::private_bfv_live_apex::PrivateBfvLiveApexReceipt;
use dreggnet_offerings::{SignedAction, SignedError, verify_signed};

use super::TelegramHost;
use crate::transport::Transport;
use crate::{ChatId, TelegramFrontend};

const DUNGEON_KEY: &str = "dungeon";
const COMMAND: &str = "/shielded-crown";

/// The complete Telegram player wire for one crown attempt.
///
/// The human session id and executor action are deliberately absent: the chat
/// determines the former and `hand` determines the one exact crown action.
/// The client must nevertheless carry and sign the authority coordinates from
/// the surface that offered that action. This prevents a valid old command
/// from being moved across a host replacement, close/reopen generation, or
/// intervening turn. The two custody ids remain public indices into trusted
/// server custody, never portable authority objects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TelegramShieldedCrownRequest {
    pub apex_id: [u8; 32],
    pub finalized_spend_nullifier: [u8; 32],
    pub hand: ShieldedCrownHand,
    pub game_host_incarnation: [u8; 32],
    pub game_session_generation: u64,
    pub game_observed_head: [u8; 32],
    pub actor_pubkey_hex: String,
    pub counter: u64,
    pub signature: [u8; 64],
    pub authority_signature: [u8; 64],
}

impl TelegramShieldedCrownRequest {
    /// Parse the exact command:
    ///
    /// `/shielded-crown red|blue APEX_ID NULLIFIER HOST GENERATION HEAD PUBKEY COUNTER SIGNATURE AUTHORITY_SIGNATURE`
    ///
    /// Every byte-bearing field has a fixed public length and trailing fields
    /// refuse.  There is consequently no extension slot through which a client
    /// can smuggle a private witness or caller-selected executor action.
    pub fn parse_command(input: &str) -> Result<Self, TelegramShieldedCrownError> {
        let mut fields = input.split_whitespace();
        let command = fields
            .next()
            .ok_or(TelegramShieldedCrownError::MalformedRequest)?;
        if command.split('@').next() != Some(COMMAND) {
            return Err(TelegramShieldedCrownError::MalformedRequest);
        }
        let hand = match fields.next() {
            Some("red") => ShieldedCrownHand::Red,
            Some("blue") => ShieldedCrownHand::Blue,
            _ => return Err(TelegramShieldedCrownError::MalformedRequest),
        };
        let apex_id = decode_hex_array::<32>(fields.next())?;
        let finalized_spend_nullifier = decode_hex_array::<32>(fields.next())?;
        let game_host_incarnation = decode_hex_array::<32>(fields.next())?;
        let game_session_generation = fields
            .next()
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|generation| *generation != 0)
            .ok_or(TelegramShieldedCrownError::MalformedRequest)?;
        let game_observed_head = decode_hex_array::<32>(fields.next())?;
        let actor_pubkey_hex = fields
            .next()
            .filter(|value| value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit()))
            .ok_or(TelegramShieldedCrownError::MalformedRequest)?
            .to_ascii_lowercase();
        let counter = fields
            .next()
            .and_then(|value| value.parse::<u64>().ok())
            .ok_or(TelegramShieldedCrownError::MalformedRequest)?;
        let signature = decode_hex_array::<64>(fields.next())?;
        let authority_signature = decode_hex_array::<64>(fields.next())?;
        if fields.next().is_some()
            || apex_id == [0; 32]
            || finalized_spend_nullifier == [0; 32]
            || game_host_incarnation == [0; 32]
            || game_observed_head == [0; 32]
        {
            return Err(TelegramShieldedCrownError::MalformedRequest);
        }
        Ok(Self {
            apex_id,
            finalized_spend_nullifier,
            hand,
            game_host_incarnation,
            game_session_generation,
            game_observed_head,
            actor_pubkey_hex,
            counter,
            signature,
            authority_signature,
        })
    }
}

fn decode_hex_array<const N: usize>(
    field: Option<&str>,
) -> Result<[u8; N], TelegramShieldedCrownError> {
    let value = field.ok_or(TelegramShieldedCrownError::MalformedRequest)?;
    if value.len() != N * 2 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(TelegramShieldedCrownError::MalformedRequest);
    }
    let mut decoded = [0u8; N];
    for (index, slot) in decoded.iter_mut().enumerate() {
        let at = index * 2;
        *slot = u8::from_str_radix(&value[at..at + 2], 16)
            .map_err(|_| TelegramShieldedCrownError::MalformedRequest)?;
    }
    Ok(decoded)
}

/// Trusted typed authority lookup behind the public command boundary.
///
/// Implementations must return the verifier-minted apex type and the private-
/// field persistence authority.  Raw proof/request bytes are intentionally not
/// an alternative method on this trait.
pub trait ShieldedCrownAuthorityCustody {
    fn load_private_apex(
        &self,
        apex_id: &[u8; 32],
    ) -> Result<Option<PrivateBfvLiveApexReceipt>, String>;

    fn load_finalized_spend(
        &self,
        nullifier: &[u8; 32],
    ) -> Result<Option<FinalizedFaithfulSpend>, String>;
}

/// Process-local verified-apex custody joined to the node's real durable spend
/// table.  `retain_private_apex` accepts only an internally binding typed apex
/// and indexes it by its own consequence digest; a player cannot choose either
/// the record contents or its key.
pub struct ShieldedCrownAuthorityStore<'a> {
    apexes: BTreeMap<[u8; 32], PrivateBfvLiveApexReceipt>,
    persist: &'a PersistentStore,
}

impl<'a> ShieldedCrownAuthorityStore<'a> {
    pub fn new(persist: &'a PersistentStore) -> Self {
        Self {
            apexes: BTreeMap::new(),
            persist,
        }
    }

    pub fn retain_private_apex(
        &mut self,
        apex: PrivateBfvLiveApexReceipt,
    ) -> Result<[u8; 32], String> {
        if !apex.binding_verifies() || apex.consequence_digest == [0; 32] {
            return Err("private apex does not verify against its typed authority".to_string());
        }
        let id = apex.consequence_digest;
        if self.apexes.contains_key(&id) {
            return Err("private apex id is already retained".to_string());
        }
        self.apexes.insert(id, apex);
        Ok(id)
    }
}

impl ShieldedCrownAuthorityCustody for ShieldedCrownAuthorityStore<'_> {
    fn load_private_apex(
        &self,
        apex_id: &[u8; 32],
    ) -> Result<Option<PrivateBfvLiveApexReceipt>, String> {
        Ok(self.apexes.get(apex_id).cloned())
    }

    fn load_finalized_spend(
        &self,
        nullifier: &[u8; 32],
    ) -> Result<Option<FinalizedFaithfulSpend>, String> {
        self.persist
            .finalized_faithful_spend(nullifier)
            .map_err(|error| error.to_string())
    }
}

#[derive(Debug)]
pub enum TelegramShieldedCrownError {
    MalformedRequest,
    DungeonNotActive,
    CrownUnavailable(ShieldedCrownHand),
    WrongGameSigner,
    Signature(SignedError),
    StaleGameAuthority,
    Epoch(String),
    Spine(String),
    CustodyUnavailable,
    ApexNotFound,
    SpendNotFound,
    CustodySubstitution(&'static str),
    Orchestration(ShieldedCrownOrchestrationError),
}

impl std::fmt::Display for TelegramShieldedCrownError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedRequest => write!(f, "malformed shielded-crown command"),
            Self::DungeonNotActive => write!(f, "open the dungeon in this chat first"),
            Self::CrownUnavailable(hand) => write!(f, "the {hand:?} crown is not offered now"),
            Self::WrongGameSigner => write!(f, "the signature key is not the mapped winner"),
            Self::Signature(error) => write!(f, "winner signature refused: {error}"),
            Self::StaleGameAuthority => write!(
                f,
                "the shielded-crown command targets a stale host, generation, or game head"
            ),
            Self::Epoch(error) => write!(f, "dungeon epoch unavailable: {error}"),
            Self::Spine(error) => write!(f, "dungeon action unavailable: {error}"),
            Self::CustodyUnavailable => write!(f, "shielded authority custody is unavailable"),
            Self::ApexNotFound => write!(f, "private clearing authority was not found"),
            Self::SpendNotFound => write!(f, "finalized tender authority was not found"),
            Self::CustodySubstitution(kind) => {
                write!(f, "trusted custody returned a different {kind}")
            }
            Self::Orchestration(error) => write!(f, "shielded crown refused: {error}"),
        }
    }
}

impl std::error::Error for TelegramShieldedCrownError {}

impl From<SignedError> for TelegramShieldedCrownError {
    fn from(error: SignedError) -> Self {
        Self::Signature(error)
    }
}

impl<T: Transport> TelegramHost<T> {
    /// Parse and execute the exact public Telegram command envelope.
    pub fn execute_shielded_crown_command<C: ShieldedCrownAuthorityCustody>(
        &mut self,
        chat_id: ChatId,
        topic: Option<i64>,
        policy: &ShieldedCrownPolicy,
        custody: &C,
        command: &str,
    ) -> Result<PrivateFheggGameConsequenceReceipt, TelegramShieldedCrownError> {
        let request = TelegramShieldedCrownRequest::parse_command(command)?;
        self.execute_shielded_crown(chat_id, topic, policy, custody, request)
    }

    /// Execute the strict player command against the active Telegram Dungeon.
    ///
    /// No Telegram user/viewer id enters this operation.  Signature authority
    /// comes only from the mapped game key, while action discovery always uses
    /// [`GameAudience::Shared`].  The returned catalog receipt is already the
    /// public-only consequence projection and contains no private proof or note
    /// witness material.
    pub fn execute_shielded_crown<C: ShieldedCrownAuthorityCustody>(
        &mut self,
        chat_id: ChatId,
        topic: Option<i64>,
        policy: &ShieldedCrownPolicy,
        custody: &C,
        request: TelegramShieldedCrownRequest,
    ) -> Result<PrivateFheggGameConsequenceReceipt, TelegramShieldedCrownError> {
        if request.actor_pubkey_hex.to_ascii_lowercase()
            != policy.winner_route().game_signer_pubkey_hex()
        {
            return Err(TelegramShieldedCrownError::WrongGameSigner);
        }
        let session = TelegramFrontend::<T>::session_id(chat_id, topic);
        if self.active_offering(&session) != Some(DUNGEON_KEY) {
            return Err(TelegramShieldedCrownError::DungeonNotActive);
        }

        // Derive the executor action and verify both client signatures before
        // touching either private authority store. The outer signature is
        // built from the authority coordinates carried by the client; never
        // substitute the server's current coordinates before verifying it.
        // The catalog adapter then repeats all checks immediately before
        // reservation/dispatch.
        let epoch_ledger = self.game_epochs.clone();
        let signed_action = {
            let session_for_job = session.clone();
            let signer = request.actor_pubkey_hex.clone();
            let signature = request.signature;
            let counter = request.counter;
            let hand = request.hand;
            self.host.run(move |host| {
                let bound = epoch_ledger
                    .bound_session(DUNGEON_KEY, &session_for_job)
                    .map_err(|error| TelegramShieldedCrownError::Epoch(error.to_string()))?;
                let generation = epoch_ledger
                    .current_generation(DUNGEON_KEY, &session_for_job)
                    .map_err(|error| TelegramShieldedCrownError::Epoch(error.to_string()))?;
                let view = inspect_bound_game_session(
                    host,
                    epoch_ledger.host_incarnation(),
                    generation,
                    bound,
                    &GameAudience::Shared,
                )
                .map_err(|error| TelegramShieldedCrownError::Spine(error.to_string()))?;
                let desired = match hand {
                    ShieldedCrownHand::Red => dungeon_on_dregg::KP_CLAIM_RED as i64,
                    ShieldedCrownHand::Blue => dungeon_on_dregg::KP_CLAIM_BLUE as i64,
                };
                let (current_reference, action) = view
                    .affordances
                    .into_iter()
                    .find_map(|affordance| match affordance {
                        GameAffordance::Turn {
                            reference, action, ..
                        } if action.turn == dreggnet_offerings::dungeon::TURN_CHOOSE
                            && action.arg == desired
                            && action.text.is_none() =>
                        {
                            Some((reference, action))
                        }
                        _ => None,
                    })
                    .ok_or(TelegramShieldedCrownError::CrownUnavailable(hand))?;
                let expected_counter = host
                    .signed_counter(DUNGEON_KEY, &session_for_job, &signer)
                    .map_or(Ok(0), |last| {
                        last.checked_add(1).ok_or_else(|| {
                            TelegramShieldedCrownError::Spine(
                                "winner replay counter is exhausted".to_string(),
                            )
                        })
                    })?;
                let signed_action = SignedAction {
                    action,
                    actor_pubkey_hex: signer,
                    counter,
                    signature,
                };
                let presented_incarnation = GameHostIncarnation::new(request.game_host_incarnation)
                    .map_err(|error| TelegramShieldedCrownError::Spine(error.to_string()))?;
                let presented_session = GameSessionRef::bound(
                    DUNGEON_KEY,
                    session_for_job.clone(),
                    presented_incarnation,
                    request.game_session_generation,
                )
                .map_err(|error| TelegramShieldedCrownError::Spine(error.to_string()))?;
                let command = SignedGameAction {
                    reference: GameActionRef::new(
                        presented_session,
                        &signed_action.action,
                        request.game_observed_head.to_vec(),
                    ),
                    signed_action,
                    authority_signature: request.authority_signature,
                };
                verify_signed(
                    DUNGEON_KEY,
                    &session_for_job,
                    expected_counter,
                    &command.signed_action,
                )?;
                verify_signed_game_action(&command)?;
                if command.reference != current_reference {
                    return Err(TelegramShieldedCrownError::StaleGameAuthority);
                }
                Ok::<SignedGameAction, TelegramShieldedCrownError>(command)
            })?
        };

        let apex = custody
            .load_private_apex(&request.apex_id)
            .map_err(|_| TelegramShieldedCrownError::CustodyUnavailable)?
            .ok_or(TelegramShieldedCrownError::ApexNotFound)?;
        if apex.consequence_digest != request.apex_id || !apex.binding_verifies() {
            return Err(TelegramShieldedCrownError::CustodySubstitution(
                "private apex",
            ));
        }
        let spend = custody
            .load_finalized_spend(&request.finalized_spend_nullifier)
            .map_err(|_| TelegramShieldedCrownError::CustodyUnavailable)?
            .ok_or(TelegramShieldedCrownError::SpendNotFound)?;
        if spend.nullifier() != request.finalized_spend_nullifier {
            return Err(TelegramShieldedCrownError::CustodySubstitution(
                "finalized spend",
            ));
        }

        let epoch_ledger = self.game_epochs.clone();
        let policy = policy.clone();
        let hand = request.hand;
        self.host.run(move |host| {
            execute_shielded_crown_action(
                host,
                &epoch_ledger,
                &policy,
                &apex,
                &spend,
                ShieldedCrownAction {
                    session,
                    hand,
                    signed_action,
                },
            )
            .map_err(TelegramShieldedCrownError::Orchestration)
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use deos_view::ViewNode;
    use dreggnet_catalog::{
        GameSessionBinding, PrivateFheggWinnerRoute, ShieldedCrownPolicy, sign_game_action,
    };
    use dreggnet_offerings::{
        Action, DreggIdentity, Offering, OfferingError, OfferingHost, Outcome, RunCost,
        SessionConfig, Surface, TurnSigner, VerifyReport,
    };

    use crate::transport::MockTransport;

    use super::*;

    static PRIVATE_RENDER_CALLS: AtomicUsize = AtomicUsize::new(0);

    #[derive(Default)]
    struct CrownState {
        hall: bool,
        crowned: bool,
        turns: usize,
    }

    struct NoViewerCrown;

    impl Offering for NoViewerCrown {
        type Session = CrownState;

        fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
            Ok(CrownState::default())
        }

        fn actions(&self, state: &Self::Session) -> Vec<Action> {
            if !state.hall {
                return vec![Action::new(
                    "press on",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    dungeon_on_dregg::KP_PRESS_ON as i64,
                    true,
                )];
            }
            if state.crowned {
                return Vec::new();
            }
            vec![
                Action::new(
                    "claim red",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    dungeon_on_dregg::KP_CLAIM_RED as i64,
                    true,
                ),
                Action::new(
                    "claim blue",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    dungeon_on_dregg::KP_CLAIM_BLUE as i64,
                    true,
                ),
            ]
        }

        fn advance(
            &self,
            state: &mut Self::Session,
            action: Action,
            _actor: DreggIdentity,
        ) -> Outcome {
            if action.turn != dreggnet_offerings::dungeon::TURN_CHOOSE || action.text.is_some() {
                return Outcome::Refused("not an exact dungeon choice".to_string());
            }
            if !state.hall && action.arg == dungeon_on_dregg::KP_PRESS_ON as i64 {
                state.hall = true;
            } else if state.hall
                && !state.crowned
                && [
                    dungeon_on_dregg::KP_CLAIM_RED as i64,
                    dungeon_on_dregg::KP_CLAIM_BLUE as i64,
                ]
                .contains(&action.arg)
            {
                state.crowned = true;
            } else {
                return Outcome::Refused("dungeon choice unavailable".to_string());
            }
            state.turns += 1;
            Outcome::Landed {
                receipt: Default::default(),
                ended: false,
            }
        }

        fn verify(&self, state: &Self::Session) -> VerifyReport {
            VerifyReport::ok(state.turns)
        }

        fn render(&self, state: &Self::Session) -> Surface {
            Surface(ViewNode::Text(format!(
                "hall={} crowned={}",
                state.hall, state.crowned
            )))
        }

        fn render_for(&self, _state: &Self::Session, _viewer: &DreggIdentity) -> Surface {
            PRIVATE_RENDER_CALLS.fetch_add(1, Ordering::SeqCst);
            panic!("shielded crown discovery must be viewer-blind")
        }

        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    #[derive(Default)]
    struct MissingCustody {
        apex_reads: AtomicUsize,
        spend_reads: AtomicUsize,
    }

    impl ShieldedCrownAuthorityCustody for MissingCustody {
        fn load_private_apex(
            &self,
            _apex_id: &[u8; 32],
        ) -> Result<Option<PrivateBfvLiveApexReceipt>, String> {
            self.apex_reads.fetch_add(1, Ordering::SeqCst);
            Ok(None)
        }

        fn load_finalized_spend(
            &self,
            _nullifier: &[u8; 32],
        ) -> Result<Option<FinalizedFaithfulSpend>, String> {
            self.spend_reads.fetch_add(1, Ordering::SeqCst);
            Ok(None)
        }
    }

    fn policy(signer: &TurnSigner) -> ShieldedCrownPolicy {
        ShieldedCrownPolicy::new(
            [0x31; 32],
            9,
            [0x32; 32],
            [0x33; 32],
            PrivateFheggWinnerRoute::new(
                DreggIdentity("bazaar-winner".to_string()),
                signer.pubkey_hex(),
            )
            .unwrap(),
        )
        .unwrap()
    }

    fn host_in_hall() -> TelegramHost<MockTransport> {
        let mut telegram = TelegramHost::with_host([0x41; 32], MockTransport::new(), || {
            let mut host = OfferingHost::new();
            host.register(DUNGEON_KEY, "no-viewer crown", NoViewerCrown);
            host
        });
        open_and_enter_hall(&mut telegram);
        telegram
    }

    fn open_and_enter_hall(telegram: &mut TelegramHost<MockTransport>) {
        let session = TelegramFrontend::<MockTransport>::session_id(77, None);
        let newly_opened = telegram.host.run({
            let session = session.clone();
            move |host| {
                host.ensure_open(DUNGEON_KEY, &session)
                    .expect("fixture dungeon opens")
            }
        });
        telegram
            .game_epochs
            .bind_after_ensure(DUNGEON_KEY, &session, newly_opened)
            .unwrap();
        telegram
            .active
            .insert(session.clone(), DUNGEON_KEY.to_string());
        telegram.host.run({
            let session = session.clone();
            move |host| {
                let action = host
                    .actions(DUNGEON_KEY, &session)
                    .unwrap()
                    .into_iter()
                    .find(|action| action.arg == dungeon_on_dregg::KP_PRESS_ON as i64)
                    .unwrap();
                assert!(
                    host.advance(
                        DUNGEON_KEY,
                        &session,
                        action,
                        DreggIdentity("pathfinder".to_string()),
                    )
                    .unwrap()
                    .landed()
                );
            }
        });
    }

    fn crown_affordance(
        host: &TelegramHost<MockTransport>,
        hand: ShieldedCrownHand,
    ) -> (GameActionRef, Action) {
        let session = TelegramFrontend::<MockTransport>::session_id(77, None);
        let desired = match hand {
            ShieldedCrownHand::Red => dungeon_on_dregg::KP_CLAIM_RED as i64,
            ShieldedCrownHand::Blue => dungeon_on_dregg::KP_CLAIM_BLUE as i64,
        };
        let ledger = host.game_epochs.clone();
        host.host.run(move |offering| {
            let bound = ledger.bound_session(DUNGEON_KEY, &session).unwrap();
            let generation = ledger.current_generation(DUNGEON_KEY, &session).unwrap();
            inspect_bound_game_session(
                offering,
                ledger.host_incarnation(),
                generation,
                bound,
                &GameAudience::Shared,
            )
            .unwrap()
            .affordances
            .into_iter()
            .find_map(|affordance| match affordance {
                GameAffordance::Turn {
                    reference, action, ..
                } if action.arg == desired => Some((reference, action)),
                _ => None,
            })
            .unwrap()
        })
    }

    fn request(
        host: &TelegramHost<MockTransport>,
        signer: &TurnSigner,
        hand: ShieldedCrownHand,
        counter: u64,
    ) -> TelegramShieldedCrownRequest {
        let (reference, action) = crown_affordance(host, hand);
        let signed = sign_game_action(signer, reference, counter, action).unwrap();
        let GameSessionBinding::Bound {
            host_incarnation,
            session_generation,
        } = signed.reference.session.binding()
        else {
            panic!("crown fixture must publish bound authority")
        };
        TelegramShieldedCrownRequest {
            apex_id: [0x51; 32],
            finalized_spend_nullifier: [0x52; 32],
            hand,
            game_host_incarnation: *host_incarnation.as_bytes(),
            game_session_generation: *session_generation,
            game_observed_head: signed
                .reference
                .expected_pre_head
                .as_slice()
                .try_into()
                .unwrap(),
            actor_pubkey_hex: signed.signed_action.actor_pubkey_hex,
            counter: signed.signed_action.counter,
            signature: signed.signed_action.signature,
            authority_signature: signed.authority_signature,
        }
    }

    #[test]
    fn command_shape_accepts_only_public_fixed_fields() {
        let signer = TurnSigner::from_seed([0x61; 32]);
        let command = format!(
            "{COMMAND} red {} {} {} 3 {} {} 7 {} {}",
            "51".repeat(32),
            "52".repeat(32),
            "53".repeat(32),
            "54".repeat(32),
            signer.pubkey_hex(),
            "63".repeat(64),
            "64".repeat(64),
        );
        let parsed = TelegramShieldedCrownRequest::parse_command(&command).unwrap();
        assert_eq!(parsed.apex_id, [0x51; 32]);
        assert_eq!(parsed.finalized_spend_nullifier, [0x52; 32]);
        assert_eq!(parsed.hand, ShieldedCrownHand::Red);
        assert_eq!(parsed.game_host_incarnation, [0x53; 32]);
        assert_eq!(parsed.game_session_generation, 3);
        assert_eq!(parsed.game_observed_head, [0x54; 32]);
        assert_eq!(parsed.counter, 7);

        for forged in [
            format!("{command} proof-bytes"),
            command.replace(" red ", " green "),
            command.replace(&"51".repeat(32), &"51".repeat(31)),
            command.replace(" 3 ", " 0 "),
            command.replace(" 7 ", " -1 "),
        ] {
            assert!(matches!(
                TelegramShieldedCrownRequest::parse_command(&forged),
                Err(TelegramShieldedCrownError::MalformedRequest)
            ));
        }
    }

    #[test]
    fn wrong_signer_refuses_before_session_or_custody() {
        let signer = TurnSigner::from_seed([0x71; 32]);
        let rival = TurnSigner::from_seed([0x72; 32]);
        let mut host = TelegramHost::with_host([0x73; 32], MockTransport::new(), OfferingHost::new);
        let custody = MissingCustody::default();
        let signed = request(&host_in_hall(), &rival, ShieldedCrownHand::Red, 0);
        // The host below is deliberately inactive. The signer-policy check
        // must happen before either epoch/session or custody access.
        let result = host.execute_shielded_crown(77, None, &policy(&signer), &custody, signed);
        assert!(matches!(
            result,
            Err(TelegramShieldedCrownError::WrongGameSigner)
        ));
        assert_eq!(custody.apex_reads.load(Ordering::SeqCst), 0);
        assert_eq!(custody.spend_reads.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn action_discovery_is_viewer_blind_and_authorities_are_lookup_only() {
        PRIVATE_RENDER_CALLS.store(0, Ordering::SeqCst);
        let signer = TurnSigner::from_seed([0x81; 32]);
        let mut host = host_in_hall();
        let custody = MissingCustody::default();
        let request = request(&host, &signer, ShieldedCrownHand::Red, 0);
        let result = host.execute_shielded_crown(77, None, &policy(&signer), &custody, request);
        assert!(matches!(
            result,
            Err(TelegramShieldedCrownError::ApexNotFound)
        ));
        assert_eq!(PRIVATE_RENDER_CALLS.load(Ordering::SeqCst), 0);
        assert_eq!(custody.apex_reads.load(Ordering::SeqCst), 1);
        assert_eq!(custody.spend_reads.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn tampered_outer_game_authority_refuses_before_private_custody() {
        let signer = TurnSigner::from_seed([0x89; 32]);
        let mut host = host_in_hall();
        let custody = MissingCustody::default();
        let mut request = request(&host, &signer, ShieldedCrownHand::Red, 0);
        request.game_session_generation += 1;

        let result = host.execute_shielded_crown(77, None, &policy(&signer), &custody, request);
        assert!(matches!(
            result,
            Err(TelegramShieldedCrownError::Signature(
                SignedError::BadSignature
            ))
        ));
        assert_eq!(custody.apex_reads.load(Ordering::SeqCst), 0);
        assert_eq!(custody.spend_reads.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn authentically_signed_old_generation_refuses_after_close_reopen_before_custody() {
        let signer = TurnSigner::from_seed([0x8a; 32]);
        let mut host = host_in_hall();
        let stale = request(&host, &signer, ShieldedCrownHand::Red, 0);

        assert!(host.close_game(DUNGEON_KEY, 77, None, 19).unwrap());
        open_and_enter_hall(&mut host);
        let custody = MissingCustody::default();
        let result = host.execute_shielded_crown(77, None, &policy(&signer), &custody, stale);
        assert!(matches!(
            result,
            Err(TelegramShieldedCrownError::StaleGameAuthority)
        ));
        assert_eq!(custody.apex_reads.load(Ordering::SeqCst), 0);
        assert_eq!(custody.spend_reads.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn stale_signature_refuses_before_private_custody() {
        let signer = TurnSigner::from_seed([0x91; 32]);
        let mut host = host_in_hall();
        let session = TelegramFrontend::<MockTransport>::session_id(77, None);
        // Burn counter 4 on an executor-refused move. Signed counters are
        // intentionally single-use even when the game refuses the action.
        host.host.run({
            let stale = signer.sign(
                DUNGEON_KEY,
                &session,
                4,
                Action::new(
                    "unavailable",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    999,
                    true,
                ),
            );
            let session = session.clone();
            move |offering| {
                let outcome = offering
                    .advance_signed(DUNGEON_KEY, &session, stale)
                    .expect("signature itself verifies");
                assert!(!outcome.landed());
            }
        });
        let custody = MissingCustody::default();
        let mut request = request(&host, &signer, ShieldedCrownHand::Red, 4);
        // Keep the outer envelope coherent with the stale inner counter; the
        // replay counter refusal must still precede custody.
        let (reference, action) = crown_affordance(&host, ShieldedCrownHand::Red);
        let stale = sign_game_action(&signer, reference, 4, action).unwrap();
        request.signature = stale.signed_action.signature;
        request.authority_signature = stale.authority_signature;
        let result = host.execute_shielded_crown(77, None, &policy(&signer), &custody, request);
        assert!(matches!(
            result,
            Err(TelegramShieldedCrownError::Signature(
                SignedError::StaleCounter { .. }
            ))
        ));
        assert_eq!(custody.apex_reads.load(Ordering::SeqCst), 0);
        assert_eq!(custody.spend_reads.load(Ordering::SeqCst), 0);
    }
}
