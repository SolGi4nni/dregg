//! The browser's one interaction grammar for every game offering.
//!
//! This is deliberately a presentation contract, not a new game engine. The
//! Dungeon, native Descent, proof-assigned raid, and Dark Bazaar keep their own
//! state machines and verifiers. The browser makes the player-facing contract
//! uniform: a resumable session, typed actions, an updated result and receipt,
//! and an explicit boundary around opaque private operations.

#[cfg(any(feature = "hosted-binary-operations", test))]
use std::collections::{BTreeMap, BTreeSet};

use dreggnet_catalog::{GameKind, GameSessionRef};
use dreggnet_offerings::SessionId;

fn boundary(kind: GameKind) -> &'static str {
    match kind {
        GameKind::Descent | GameKind::DescentCampaign => {
            "Private choices and proof witnesses stay with the player; committed moves and receipt roots are public."
        }
        GameKind::Dungeon => {
            "Private ballots, cards, quest witnesses, and raid scores stay outside the rendered session; only verified outcomes land."
        }
        GameKind::TacticalRaid => {
            "Suitability scores and the assignment witness stay private; public seats, assigned roles, spent capabilities, and receipts are visible."
        }
        GameKind::DarkBazaarCrawl => {
            "This catalog table is the public crawl. When an opaque clearing operation is offered, uploaded bytes stay out of rendered state and only its accepted effect and receipt are published."
        }
        GameKind::DarkPool => {
            "Encrypted swap inputs stay opaque to the browser surface; accepted public roots, commitments, and receipts are the rendered result."
        }
        GameKind::Council | GameKind::Market | GameKind::MultiwayTug | GameKind::Automatafl => {
            "The current surface and ordinary moves are public; an opaque operation, when offered, keeps uploaded bytes out of rendered state."
        }
    }
}

/// Stable session/action/result chrome shared by every catalog game.
pub(crate) fn session_rail(key: &str, id: &str) -> Option<String> {
    let session = GameSessionRef::new(key, SessionId::new(id)).ok()?;
    let kind = session.kind();
    let key = crate::esc(session.offering());
    let id = crate::esc(&session.session_id().0);
    Some(format!(
        "<section class=\"game-session-rail\" data-game-session=\"true\" \
         data-game-family=\"{family}\" data-session-id=\"{id}\" \
         data-actor-attribution=\"asserted\" \
         aria-label=\"Session continuity and privacy\">\
         <div class=\"game-session-resume\"><span class=\"game-session-kicker\">Session</span>\
         <strong>{id}</strong><a href=\"/offerings/{key}/session/{id}\" \
         rel=\"bookmark\">Resume here</a></div>\
         <ol class=\"game-session-steps\"><li><b>1</b><span>Session</span></li>\
         <li><b>2</b><span>Choose an action</span></li>\
         <li><b>3</b><span>Read the result</span></li></ol>\
         <p class=\"game-session-boundary\"><span aria-hidden=\"true\">◐</span>\
         Browser actor attribution is asserted, not authenticated. {boundary}</p>\
         </section>",
        family = kind.as_str(),
        boundary = crate::esc(boundary(kind)),
    ))
}

/// A descriptor title is public metadata, so it must not carry session-local
/// actor/head material. Labels are derived only from the stable operation name.
pub fn public_operation_title(operation: &str) -> &'static str {
    let lower = operation.to_ascii_lowercase();
    if lower.contains("preference") || lower.contains("ballot") {
        "Verify a shielded party preference"
    } else if lower.contains("raid") || lower.contains("assignment") {
        "Verify a shielded raid assignment"
    } else if lower.contains("shuffle") || lower.contains("deal") {
        "Verify a private shuffle or deal"
    } else if lower.contains("quest") {
        "Verify a shielded quest transition"
    } else if lower.contains("settle") || lower.contains("clearing") {
        "Verify a private clearing"
    } else if lower.contains("amm") || lower.contains("swap") {
        "Verify a shielded pool update"
    } else {
        "Verify a proof-bearing operation"
    }
}

#[cfg(any(feature = "hosted-binary-operations", test))]
fn field_name_is_public(name: &str) -> bool {
    // This is intentionally an exact allowlist rather than a substring
    // denylist. `BinaryOperationReceipt::public_fields` is authored by several
    // independent rule engines; a newly named field is not a browser-safe
    // disclosure until this boundary has reviewed it. Digests and roots below
    // are public commitments, never their source bytes.
    matches!(
        name,
        "acceptedSwaps"
            | "attempt"
            | "ballotRoot"
            | "bfvCustody"
            | "candidateNonce"
            | "card"
            | "collectiveParties"
            | "committedSequence"
            | "dealRoot"
            | "decisionBundleDigest"
            | "decisionClaimDigest"
            | "decisionTaskDigest"
            | "decisionThreshold"
            | "domain"
            | "ended"
            | "index"
            | "initiativeCard"
            | "initiativeSeat"
            | "inputRoot"
            | "invariant"
            | "model"
            | "narrationCommit"
            | "newRoot"
            | "nextSequence"
            | "oldRoot"
            | "operatorSpendMicroUsd"
            | "outcome"
            | "participant"
            | "phase"
            | "plan"
            | "price"
            | "proofDigest"
            | "proofSession"
            | "publicHostMaterialDigest"
            | "replaySlotsConsumed"
            | "requestDigest"
            | "revision"
            | "roles"
            | "root"
            | "rulesetRoot"
            | "sameOpeningClaimDigest"
            | "seat"
            | "sequence"
            | "session"
            | "statementDigest"
            | "volume"
            | "winner"
    )
}

/// Copy only fields whose names are safe public-result carriers. This is a
/// fail-closed second boundary after the offering's own `public_fields` list.
#[cfg(any(feature = "hosted-binary-operations", test))]
pub(crate) fn public_operation_fields(fields: Vec<(String, String)>) -> BTreeMap<String, String> {
    let mut public = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for (name, value) in fields {
        if !field_name_is_public(&name) || ambiguous.contains(&name) {
            continue;
        }
        if public.insert(name.clone(), value).is_some() {
            // Two values for one public name have no canonical meaning. Omit
            // both rather than letting insertion order choose what the viewer
            // believes the verified result said.
            public.remove(&name);
            ambiguous.insert(name);
        }
    }
    public
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operation_titles_are_stable_and_do_not_echo_descriptor_context() {
        assert_eq!(
            public_operation_title("native.private-raid-assignment.actor-alice.root-secret"),
            "Verify a shielded raid assignment"
        );
        assert!(!public_operation_title("anything").contains("anything"));
    }

    #[test]
    fn private_carriers_are_removed_but_public_commitments_survive() {
        let public = public_operation_fields(vec![
            ("actor".into(), "viewer-7".into()),
            ("privateWitness".into(), "do-not-emit".into()),
            ("proofBytes".into(), "do-not-emit".into()),
            ("submitterHandle".into(), "do-not-emit".into()),
            ("apparentlyHarmlessNewField".into(), "do-not-emit".into()),
            ("newRoot".into(), "abcd".into()),
            ("proofDigest".into(), "1234".into()),
            ("winner".into(), "north".into()),
        ]);
        assert_eq!(public.len(), 3);
        assert_eq!(public.get("newRoot").map(String::as_str), Some("abcd"));
        assert_eq!(public.get("proofDigest").map(String::as_str), Some("1234"));
        assert_eq!(public.get("winner").map(String::as_str), Some("north"));
    }

    #[test]
    fn duplicate_public_names_are_omitted_instead_of_order_selected() {
        let public = public_operation_fields(vec![
            ("newRoot".into(), "first".into()),
            ("winner".into(), "north".into()),
            ("newRoot".into(), "second".into()),
            ("newRoot".into(), "third".into()),
        ]);
        assert_eq!(public.len(), 1);
        assert_eq!(public.get("winner").map(String::as_str), Some("north"));
        assert!(!public.contains_key("newRoot"));
    }
}
