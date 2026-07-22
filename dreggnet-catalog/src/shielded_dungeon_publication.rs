//! Shared-surface controller for the Dark Bazaar -> Dungeon consequence.
//!
//! The private apex receipt remains an authority object: it names the winner,
//! private root, certificate, asset, signer, and exact action route. A public
//! game surface must never render that object. This adapter accepts only the
//! catalog's viewer-blind game projection plus the exact consequence receipt
//! and emits a deliberately closed, self-authenticating receipt card.

use dreggnet_market::private_bfv_live_apex::PrivateBfvLiveApexReceipt;

use crate::{
    GameKind, PrivateFheggGameConsequenceReceipt, PrivateFheggGameMechanic, PublicGameAttribution,
    PublicGameReceipt, PublicGameReceiptResult,
};

const CARD_DOMAIN: &str = "dregg.dark-bazaar-shielded-dungeon-card.v1";

/// Exact public receipt chain for one shielded Bazaar-authorized Dungeon turn.
///
/// This is the object a shared web page, bot message, or cross-game activity
/// rail may retain. Its closed field set cannot carry the Bazaar winner,
/// signing key, private root, certificate, asset, raw session, action,
/// operation, payload, or state heads from either authority object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedDungeonPublicCard {
    pub kind: GameKind,
    pub authorization_id: [u8; 32],
    pub consequence_id: [u8; 32],
    pub session_route_id: [u8; 32],
    pub router_receipt_id: [u8; 32],
    pub executor_receipt_id: [u8; 32],
    pub publication_id: [u8; 32],
    pub card_id: [u8; 32],
    pub ended: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedDungeonPublicationError {
    InvalidConsequenceBinding,
    AuthorityMismatch,
    InvalidPublicationBinding,
    InvalidCardBinding,
    WrongMechanic,
    WrongGameKind,
    UnsignedTurn,
    NotATurn,
    ReceiptSubstitution,
    ResultSubstitution,
}

impl ShieldedDungeonPublicCard {
    /// Join the viewer-blind projection to the exact one-shot apex consequence.
    ///
    /// Both input bindings and the external live-apex authority are checked
    /// here; a caller cannot mint an authoritative card from a bag of otherwise
    /// well-shaped commitments.
    pub fn from_exact_receipts(
        apex: &PrivateBfvLiveApexReceipt,
        consequence: &PrivateFheggGameConsequenceReceipt,
        game: &PublicGameReceipt,
    ) -> Result<Self, ShieldedDungeonPublicationError> {
        if !consequence.binding_verifies() {
            return Err(ShieldedDungeonPublicationError::InvalidConsequenceBinding);
        }
        if !consequence.matches_authorities(apex, None) {
            return Err(ShieldedDungeonPublicationError::AuthorityMismatch);
        }
        if consequence.mechanic != PrivateFheggGameMechanic::DungeonRaidMender {
            return Err(ShieldedDungeonPublicationError::WrongMechanic);
        }
        if game.validate().is_err() {
            return Err(ShieldedDungeonPublicationError::InvalidPublicationBinding);
        }
        if game.kind != GameKind::Dungeon {
            return Err(ShieldedDungeonPublicationError::WrongGameKind);
        }
        if game.attribution != PublicGameAttribution::Signed {
            return Err(ShieldedDungeonPublicationError::UnsignedTurn);
        }
        let PublicGameReceiptResult::Turn { ended } = &game.result else {
            return Err(ShieldedDungeonPublicationError::NotATurn);
        };
        if game.receipt_id != consequence.game_receipt_id {
            return Err(ShieldedDungeonPublicationError::ReceiptSubstitution);
        }
        if *ended != consequence.ended {
            return Err(ShieldedDungeonPublicationError::ResultSubstitution);
        }

        let card_id = card_id(
            consequence.authorization_id,
            consequence.consequence_digest,
            game.session_route_id,
            game.receipt_id,
            consequence.inner_game_receipt_id,
            game.publication_id,
            *ended,
        );
        Ok(Self {
            kind: game.kind,
            authorization_id: consequence.authorization_id,
            consequence_id: consequence.consequence_digest,
            session_route_id: game.session_route_id,
            router_receipt_id: game.receipt_id,
            executor_receipt_id: consequence.inner_game_receipt_id,
            publication_id: game.publication_id,
            card_id,
            ended: *ended,
        })
    }

    /// Detect a substituted commitment or lifecycle bit after transport.
    pub fn binding_verifies(&self) -> bool {
        self.kind == GameKind::Dungeon
            && self.card_id
                == card_id(
                    self.authorization_id,
                    self.consequence_id,
                    self.session_route_id,
                    self.router_receipt_id,
                    self.executor_receipt_id,
                    self.publication_id,
                    self.ended,
                )
    }

    pub fn validate(&self) -> Result<(), ShieldedDungeonPublicationError> {
        self.binding_verifies()
            .then_some(())
            .ok_or(ShieldedDungeonPublicationError::InvalidCardBinding)
    }

    /// Viewer-blind text suitable for existing bot/web activity surfaces.
    /// Every identifier is an exact receipt commitment, not a truncated alias.
    pub fn render_shared(&self) -> Result<String, ShieldedDungeonPublicationError> {
        self.validate()?;
        Ok(format!(
            "Dungeon · shielded consequence {}\nauthorization {}\nconsequence {}\nroute {}\nrouter receipt {}\nexecutor receipt {}\npublication {}\ncard {}",
            if self.ended { "ended" } else { "landed" },
            hex32(self.authorization_id),
            hex32(self.consequence_id),
            hex32(self.session_route_id),
            hex32(self.router_receipt_id),
            hex32(self.executor_receipt_id),
            hex32(self.publication_id),
            hex32(self.card_id),
        ))
    }
}

fn card_id(
    authorization_id: [u8; 32],
    consequence_id: [u8; 32],
    session_route_id: [u8; 32],
    router_receipt_id: [u8; 32],
    executor_receipt_id: [u8; 32],
    publication_id: [u8; 32],
    ended: bool,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CARD_DOMAIN);
    for value in [
        authorization_id,
        consequence_id,
        session_route_id,
        router_receipt_id,
        executor_receipt_id,
        publication_id,
    ] {
        hasher.update(&(value.len() as u64).to_be_bytes());
        hasher.update(&value);
    }
    hasher.update(&1_u64.to_be_bytes());
    hasher.update(&[u8::from(ended)]);
    *hasher.finalize().as_bytes()
}

fn hex32(bytes: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stored_card() -> ShieldedDungeonPublicCard {
        let authorization_id = [1; 32];
        let consequence_id = [2; 32];
        let session_route_id = [3; 32];
        let router_receipt_id = [4; 32];
        let executor_receipt_id = [5; 32];
        let publication_id = [6; 32];
        let ended = false;
        ShieldedDungeonPublicCard {
            kind: GameKind::Dungeon,
            authorization_id,
            consequence_id,
            session_route_id,
            router_receipt_id,
            executor_receipt_id,
            publication_id,
            card_id: card_id(
                authorization_id,
                consequence_id,
                session_route_id,
                router_receipt_id,
                executor_receipt_id,
                publication_id,
                ended,
            ),
            ended,
        }
    }

    #[test]
    fn stored_card_renders_only_exact_public_commitments() {
        let card = stored_card();
        let rendered = card.render_shared().expect("fixture card binds");
        assert!(rendered.starts_with("Dungeon · shielded consequence landed"));
        assert!(rendered.contains(&"01".repeat(32)));
        assert!(rendered.contains(&"02".repeat(32)));
        assert!(rendered.contains(&"04".repeat(32)));
        assert!(rendered.contains(&"05".repeat(32)));
        assert!(rendered.contains(&"06".repeat(32)));
    }

    #[test]
    fn stored_card_substitution_is_refused_before_render() {
        let mut card = stored_card();
        card.session_route_id[0] ^= 1;
        assert_eq!(
            card.render_shared()
                .expect_err("mutated card must not render"),
            ShieldedDungeonPublicationError::InvalidCardBinding
        );
    }
}
