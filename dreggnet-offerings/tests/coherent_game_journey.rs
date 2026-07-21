#![cfg(feature = "private-preference-operation")]

//! One player journey over the common offering/operation/receipt/capability vocabulary.
//!
//! The native Descent remains its own Lean-authored game and the Keep remains its own executor
//! world. Coherence lives at the host boundary: the Descent+overworld campaign exposes its
//! shielded operation through the ordinary operation journal; one exact public result mints a
//! narrow, one-shot consequence for a Bazaar-shaped endpoint; and the next Dungeon scene uses the
//! same host operation route for strictly parsed Chutes narration.

use dreggnet_offerings::campaign::{DescentCampaignOffering, DescentCampaignSession};
use dreggnet_offerings::chutes_consent::CHUTES_CONSENT_WIRE;
use dreggnet_offerings::dungeon::narrated::{CHUTES_NARRATED_OPERATION, ChutesNarratedRequest};
use dreggnet_offerings::dungeon::{DungeonOffering, PRIVATE_PREFERENCE_OPTIONS};
use dreggnet_offerings::native_descent::{
    NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION, encode_native_descent_private_preference,
    native_descent_private_preference_proof_session,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{
    Action, BinaryOperationReceipt, DreggIdentity, Offering, OfferingHost,
    OperationConsequenceBook, OperationConsequenceEndpoint, OperationConsequenceError,
    OperationConsequenceGrant, OperationConsequenceRule, ResumeError, SessionConfig, SessionId,
};
use dungeon_on_dregg::descent::DELVE;
use dungeon_on_dregg::private_preference::{PrivateBallot, prove_private_preference};

const BAZAAR_ENTRANCE: &str = "dark-bazaar.enter.v1";

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn offered(
    offering: &DescentCampaignOffering,
    session: &DescentCampaignSession,
    turn: &str,
) -> Action {
    offering
        .actions(session)
        .into_iter()
        .find(|action| action.turn == turn && action.arg == 0)
        .unwrap_or_else(|| panic!("missing campaign action {turn}"))
}

fn bazaar_ballots() -> [PrivateBallot; 4] {
    core::array::from_fn(|_| {
        PrivateBallot::try_new([0, 0, 3, 0]).expect("option two wins every private ballot")
    })
}

#[derive(Default)]
struct BazaarEntrance {
    accepted: Vec<[u8; 32]>,
}

impl OperationConsequenceEndpoint for BazaarEntrance {
    fn destination(&self) -> &str {
        BAZAAR_ENTRANCE
    }

    fn apply(
        &mut self,
        grant: &OperationConsequenceGrant,
    ) -> Result<BinaryOperationReceipt, OperationConsequenceError> {
        if grant.source_operation() != NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION {
            return Err(OperationConsequenceError::DestinationRefused(
                "the Bazaar entrance requires the shielded party preference".to_string(),
            ));
        }
        let (before, after) = grant.source_heads();
        if before == after {
            return Err(OperationConsequenceError::DestinationRefused(
                "the source operation did not move its hosted commitment".to_string(),
            ));
        }
        self.accepted.push(grant.id());
        Ok(BinaryOperationReceipt {
            operation: BAZAAR_ENTRANCE.to_string(),
            receipt_id: grant.id(),
            public_fields: vec![
                (
                    "sourceOperation".to_string(),
                    grant.source_operation().to_string(),
                ),
                ("sourceReceipt".to_string(), hex(grant.source_receipt_id())),
            ],
        })
    }
}

#[test]
fn descent_overworld_bazaar_consequence_and_narrated_dungeon_are_one_hosted_journey() {
    let alice = actor("alice-cipherclerk");
    let mallory = actor("mallory-cipherclerk");
    let campaign_id = SessionId::new("alice-deepening-ways");
    let dungeon_id = SessionId::new("alice-warden-keep");
    let store = InMemoryResumeStore::new();
    let campaign = DescentCampaignOffering::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DescentCampaignOffering::KEY,
        "The Deepening Ways",
        campaign.clone(),
    );
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session(
        DescentCampaignOffering::KEY,
        campaign_id.clone(),
        SessionConfig::with_seed(111),
    )
    .expect("campaign opens");
    host.open_session("dungeon", dungeon_id.clone(), SessionConfig::with_seed(112))
        .expect("Dungeon opens");

    // Mirror only produces the exact private proof context; both real moves go through the same
    // native executor and are checked equal by the proof/session bindings below.
    let mut mirror = campaign
        .open(SessionConfig::with_seed(111))
        .expect("deterministic campaign mirror");
    let host_delve = host
        .actions(DescentCampaignOffering::KEY, &campaign_id)
        .unwrap()
        .into_iter()
        .find(|action| action.turn == DELVE && action.arg == 0)
        .expect("campaign exposes native delve");
    assert!(
        host.advance(
            DescentCampaignOffering::KEY,
            &campaign_id,
            host_delve,
            alice.clone(),
        )
        .unwrap()
        .landed()
    );
    let mirror_delve = offered(&campaign, &mirror, DELVE);
    assert!(
        campaign
            .advance(&mut mirror, mirror_delve, alice.clone())
            .landed()
    );
    let context = mirror
        .active_descent()
        .private_operation_context()
        .expect("first landed move binds the shielded operation context");
    let proof = prove_private_preference(
        native_descent_private_preference_proof_session(&context),
        &bazaar_ballots(),
    )
    .expect("the private party plan proves");
    let payload = encode_native_descent_private_preference(&context, &proof)
        .expect("exact campaign-head envelope");

    let applied = host
        .invoke_binary_operation_bound(
            DescentCampaignOffering::KEY,
            &campaign_id,
            NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
            &payload,
            alice.clone(),
        )
        .expect("campaign delegates its active native private operation through the host");
    assert_ne!(applied.before, applied.after);
    assert!(
        applied
            .receipt
            .public_fields
            .iter()
            .any(|(name, value)| name == "plan" && value == PRIVATE_PREFERENCE_OPTIONS[2])
    );
    assert!(
        host.verify(DescentCampaignOffering::KEY, &campaign_id)
            .unwrap()
            .verified
    );
    let rendered = format!(
        "{:?}",
        host.render(DescentCampaignOffering::KEY, &campaign_id)
            .unwrap()
            .0
    );
    assert!(rendered.contains("barter in the Dark Bazaar"), "{rendered}");

    // The source game does not import or simulate the market. An exact result rule mints a narrow
    // endpoint grant; the endpoint owns its own receipt and the shared book enforces actor +
    // destination + one-shot use.
    let rule = OperationConsequenceRule::new(
        NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
        "plan",
        PRIVATE_PREFERENCE_OPTIONS[2],
        BAZAAR_ENTRANCE,
    )
    .unwrap();
    let grant = rule.admit(&applied).expect("the proved Bazaar plan admits");
    let wrong_plan = OperationConsequenceRule::new(
        NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION,
        "winner",
        "1",
        BAZAAR_ENTRANCE,
    )
    .unwrap();
    assert!(wrong_plan.admit(&applied).is_err());
    let mut book = OperationConsequenceBook::default();
    let mut bazaar = BazaarEntrance::default();
    assert_eq!(
        book.redeem(&mut bazaar, &grant, &mallory),
        Err(OperationConsequenceError::WrongActor)
    );
    let bazaar_receipt = book
        .redeem(&mut bazaar, &grant, &alice)
        .expect("the bound actor consumes the exact Bazaar consequence once");
    assert_eq!(bazaar_receipt.operation, BAZAAR_ENTRANCE);
    assert!(book.is_consumed(&grant));
    assert_eq!(
        book.redeem(&mut bazaar, &grant, &alice),
        Err(OperationConsequenceError::AlreadyConsumed)
    );

    // The next organ uses the same operation host. The Bazaar result may color narration, but it
    // carries no authority: only `press_on` reaches the Dungeon executor.
    let chutes = ChutesNarratedRequest::new(
        "deepseek-ai/DeepSeek-V3",
        50_000,
        11_000,
        CHUTES_CONSENT_WIRE,
        format!(
            "COMMAND: press_on\nNARRATION: Bazaar seal {} glimmers; the executor opens only the gate.",
            &hex(bazaar_receipt.receipt_id)[..12]
        ),
    )
    .unwrap()
    .encode()
    .unwrap();
    let dungeon_turn = host
        .invoke_binary_operation_bound(
            "dungeon",
            &dungeon_id,
            CHUTES_NARRATED_OPERATION,
            &chutes,
            alice,
        )
        .expect("the exact consented Dungeon command lands through the same host");
    assert_eq!(dungeon_turn.receipt.operation, CHUTES_NARRATED_OPERATION);
    assert_ne!(dungeon_turn.before, dungeon_turn.after);
    assert!(host.verify("dungeon", &dungeon_id).unwrap().verified);

    // The source-specific operation also binds actor in its canonical payload. Mutating only the
    // host journal attribution cannot replay the proof as Mallory. (Host SessionId is not inside
    // the native proof context; the AppliedBinaryOperation docs name that separate route seam.)
    let mut wrong_actor_log = store
        .load(DescentCampaignOffering::KEY, &campaign_id)
        .expect("campaign operation journal");
    wrong_actor_log.operations[0].actor = mallory;
    let mut rejecting = OfferingHost::new();
    rejecting.register(
        DescentCampaignOffering::KEY,
        "The Deepening Ways",
        campaign.clone(),
    );
    assert!(matches!(
        rejecting.resume(&wrong_actor_log),
        Err(ResumeError::OperationRefused { .. })
    ));

    let campaign_head = host
        .commitment(DescentCampaignOffering::KEY, &campaign_id)
        .unwrap();
    let dungeon_head = host.commitment("dungeon", &dungeon_id).unwrap();
    drop(host);
    let mut restarted = OfferingHost::new().with_resume_store(Box::new(store));
    restarted.register(DescentCampaignOffering::KEY, "The Deepening Ways", campaign);
    restarted.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let results = restarted.resume_all();
    assert_eq!(results.len(), 2);
    assert!(
        results.iter().all(|(_, result)| result.is_ok()),
        "{results:?}"
    );
    assert_eq!(
        restarted
            .commitment(DescentCampaignOffering::KEY, &campaign_id)
            .unwrap(),
        campaign_head
    );
    assert_eq!(
        restarted.commitment("dungeon", &dungeon_id).unwrap(),
        dungeon_head
    );
}

fn hex(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
