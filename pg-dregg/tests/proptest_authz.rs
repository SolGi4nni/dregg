//! Property / fuzz tests for the authz core — the verified capability decision and
//! the no-amplification (attenuation-narrowing) property. The crown jewel here is
//! `attenuation_never_amplifies`: for ARBITRARY caveat trees and ARBITRARY
//! attenuation predicates, the attenuated child's admitted set is a SUBSET of the
//! parent's, over a grid of requests. This is the property `pg-dregg`'s whole RLS
//! pitch rests on, fuzzed.
//!
//! Run: `cargo test --test proptest_authz`
//!
//! NOTE: the authz core uses process-global state (issuer key, LRU, revocation
//! set), so these tests SERIALIZE on a guard, exactly as the unit tests do.

use std::sync::Mutex;

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use proptest::prelude::*;

static SERIAL: Mutex<()> = Mutex::new(());
fn lock() -> std::sync::MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(|p| p.into_inner())
}

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// The fixed issuer for these tests.
fn issuer() -> RootKey {
    RootKey::from_seed([7u8; 32])
}

fn install() {
    authz::set_issuer_pubkey(issuer().public());
    authz::lru_clear();
    authz::revoked_clear();
}

// ---- generators -----------------------------------------------------------
//
// A small alphabet for actions/resources so requests and caveats overlap often
// enough to make the subset property non-vacuous (a request grid that NEVER
// satisfies any caveat would make "child ⊆ parent" trivially true).

fn arb_action() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("read".to_string()),
        Just("write".to_string()),
        Just("submit".to_string())
    ]
}

fn arb_resource() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("org/42/public/doc1".to_string()),
        Just("org/42/private/doc9".to_string()),
        Just("org/99/public/doc1".to_string()),
        Just("a1ff".to_string()),
        Just("b0ff".to_string()),
    ]
}

/// An arbitrary first-party `Pred` over the action/resource/clock attributes, up
/// to a bounded depth. Includes AllOf/AnyOf/Not so the boolean algebra (incl.
/// fail-closed corners) is exercised.
fn arb_pred() -> impl Strategy<Value = Pred> {
    let leaf = prop_oneof![
        arb_action().prop_map(|a| Pred::AttrEq {
            key: "action".into(),
            value: a
        }),
        prop_oneof![
            Just("org/42/".to_string()),
            Just("org/".to_string()),
            Just("org/42/public/".to_string()),
            Just("a1".to_string()),
            Just("".to_string()),
        ]
        .prop_map(|p| Pred::AttrPrefix {
            key: "resource".into(),
            prefix: p
        }),
        (0u64..3000).prop_map(|at| Pred::NotAfter { at }),
        (0u64..3000).prop_map(|at| Pred::NotBefore { at }),
        Just(Pred::True),
        Just(Pred::False),
    ];
    leaf.prop_recursive(3, 12, 4, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 0..3).prop_map(Pred::AllOf),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Pred::AnyOf),
            inner.prop_map(|p| Pred::Not(Box::new(p))),
        ]
    })
}

/// A fixed request grid the subset property is checked over.
fn request_grid() -> Vec<(String, String, i64)> {
    let actions = ["read", "write", "submit"];
    let resources = [
        "org/42/public/doc1",
        "org/42/private/doc9",
        "org/99/public/doc1",
        "a1ff",
        "b0ff",
    ];
    let clocks = [0i64, 500, 1000, 2500];
    let mut v = Vec::new();
    for a in actions {
        for r in resources {
            for c in clocks {
                v.push((a.to_string(), r.to_string(), c));
            }
        }
    }
    v
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 300, ..ProptestConfig::default() })]

    /// THE CROWN JEWEL — attenuation never amplifies. For an arbitrary parent
    /// caveat set and an arbitrary attenuation predicate, the child admits a
    /// SUBSET of what the parent admits, over the whole request grid. (If this
    /// ever fails, the no-amplification guarantee — and the RLS pitch — is broken.)
    #[test]
    fn attenuation_never_amplifies(
        parent_caveats in prop::collection::vec(arb_pred(), 0..4),
        atten in arb_pred(),
    ) {
        let _g = lock();
        install();
        let root = issuer();

        let parent = root
            .mint(parent_caveats.iter().cloned().map(Caveat::FirstParty))
            .encode();
        // Decode the parent and attenuate it by the extra predicate.
        let child = authz::attenuate_token(
            &parent,
            &serde_json::to_string(&vec![atten]).unwrap(),
        )
        .expect("attenuation of a freshly-minted token must succeed");

        for (a, r, c) in request_grid() {
            let parent_admits = authz::decide(&parent, &a, &r, c).allowed();
            let child_admits = authz::decide(&child, &a, &r, c).allowed();
            // child ⇒ parent: the child may never admit a request the parent denied.
            prop_assert!(
                !child_admits || parent_admits,
                "AMPLIFICATION: child admitted ({a},{r},{c}) the parent denied — parent={:?} atten broke subset",
                parent_caveats
            );
        }
    }

    /// Decoding + deciding on an ARBITRARY token string never panics — it denies
    /// (fail-closed). The real fuzz target: a hostile token in `SET dregg.token`
    /// must not panic a backend.
    #[test]
    fn arbitrary_token_string_never_panics(tok in ".{0,256}", a in arb_action(), r in arb_resource(), c in any::<i64>()) {
        let _g = lock();
        install();
        // Must not panic; the verdict for garbage is deny, but we only require
        // no-panic here (a valid-by-accident token is astronomically unlikely).
        let _ = authz::decide(&tok, &a, &r, c).allowed();
        let _ = authz::cap_id(&tok);
        let _ = authz::subject(&tok);
        let _ = authz::explain(&tok, &a, &r, c);
    }

    /// A token from a DIFFERENT issuer NEVER verifies under our key (forged-chain
    /// rejection), for any caveats and any request.
    #[test]
    fn foreign_issuer_token_never_admits(
        caveats in prop::collection::vec(arb_pred(), 0..4),
        a in arb_action(), r in arb_resource(), c in 0i64..3000,
    ) {
        let _g = lock();
        install();
        let foreign = RootKey::from_seed([9u8; 32]); // NOT our issuer
        let tok = foreign.mint(caveats.into_iter().map(Caveat::FirstParty)).encode();
        prop_assert!(!authz::decide(&tok, &a, &r, c).allowed(), "a foreign-issuer token must never verify");
    }

    /// Instant revocation: once a credential's id is revoked, it denies EVERY
    /// request on the next check, regardless of caveats — and un-revoking restores
    /// exactly the pre-revocation verdict.
    #[test]
    fn revocation_denies_everything_then_restores(
        caveats in prop::collection::vec(arb_pred(), 0..4),
        a in arb_action(), r in arb_resource(), c in 0i64..3000,
    ) {
        let _g = lock();
        install();
        let root = issuer();
        let tok = root.mint(caveats.into_iter().map(Caveat::FirstParty)).encode();
        let before = authz::decide(&tok, &a, &r, c).allowed();

        let id = authz::cap_id(&tok).expect("a minted token decodes");
        authz::revoke(&id);
        prop_assert!(!authz::decide(&tok, &a, &r, c).allowed(), "a revoked token must deny");

        authz::unrevoke(&id);
        let after = authz::decide(&tok, &a, &r, c).allowed();
        prop_assert_eq!(before, after, "un-revoking must restore the exact verdict");
    }

    /// No issuer key configured ⇒ every decision denies (fail-closed), for any
    /// token and request.
    #[test]
    fn no_issuer_key_denies_everything(
        caveats in prop::collection::vec(arb_pred(), 0..4),
        a in arb_action(), r in arb_resource(), c in 0i64..3000,
    ) {
        let _g = lock();
        let root = issuer();
        let tok = root.mint(caveats.into_iter().map(Caveat::FirstParty)).encode();
        // Explicitly clear the key.
        authz::clear_issuer_pubkey();
        authz::lru_clear();
        authz::revoked_clear();
        prop_assert!(!authz::decide(&tok, &a, &r, c).allowed(), "no issuer key ⇒ deny");
    }

    /// The hot-LRU and cold-cache paths agree: a decision computed cold (cleared
    /// LRU) equals the same decision computed hot (warm LRU). (The LRU must not
    /// change a verdict — only skip the chain verify.)
    #[test]
    fn lru_does_not_change_the_verdict(
        caveats in prop::collection::vec(arb_pred(), 0..4),
        a in arb_action(), r in arb_resource(), c in 0i64..3000,
    ) {
        let _g = lock();
        install();
        let root = issuer();
        let tok = root.mint(caveats.into_iter().map(Caveat::FirstParty)).encode();

        authz::lru_clear();
        let cold = authz::decide(&tok, &a, &r, c).allowed();
        // Warm it with a different request, then re-decide the original.
        let _ = authz::decide(&tok, "read", "warming/the/cache", 1);
        let hot = authz::decide(&tok, &a, &r, c).allowed();
        prop_assert_eq!(cold, hot, "the LRU must not change a verdict");
    }
}

/// A revoked token denies even when the issuer key is also configured and the
/// token would otherwise be admitted — using a concrete known-admit token (a
/// non-property sanity check that the property generators rest on).
#[test]
fn concrete_revocation_sanity() {
    let _g = lock();
    install();
    let root = issuer();
    let tok = root
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "".into(),
            }),
        ])
        .encode();
    // It admits a read on any resource.
    assert!(authz::decide(&tok, "read", &hx(&[0xa1u8; 32]), 1000).allowed());
    let id = authz::cap_id(&tok).unwrap();
    authz::revoke(&id);
    assert!(!authz::decide(&tok, "read", &hx(&[0xa1u8; 32]), 1000).allowed());
    authz::unrevoke(&id);
}
