//! THE FALSIFIER: two identities must never share a derived ML-DSA key.
//!
//! `RootKey` and `Credential` each memoise the ML-DSA-65 key their own ed25519
//! seed derives (`credential::pq::MlDsaSeedMemo`), because that derivation runs
//! the deployed keygen at 174–227 ms of CPU and every mint, attenuation and
//! hybrid verify used to pay it afresh — twice per block. Memoising a pure
//! function is arithmetic; a memo that ever served one identity's key to another
//! would be a FORGERY ENGINE. This file is the wall, driven through the PUBLIC
//! API only, so it checks the decision a verifier actually makes rather than the
//! mechanism underneath it.
//!
//! Four roots mint and attenuate INTERLEAVED — round-robin, so a memo shared
//! across identities, or a single-slot last-writer cache, mis-serves somebody.
//! Then the falsifier: every credential admits under its OWN enrolled hybrid
//! root and under NO other, before and after the wire roundtrip.
//!
//! ## Scope, stated plainly
//!
//! `dregg-auth` does NOT depend on `dregg-lean-ffi`, so no process running these
//! tests can install the Lean-verified ML-DSA cores — `dregg-pq` either takes its
//! `fips204` fallback (under `DREGG_ALLOW_UNAUDITED_PQ=1`) or fails closed and
//! aborts. What is checked here is therefore the KEY-ROUTING property (which key
//! each identity presents and signs under), which is what the memo can break. It
//! says nothing about the deployed keygen object.

use dregg_auth::credential::{Caveat, Context, Credential, HybridRootPublic, Pred, RootKey};

fn read_caveat() -> Caveat {
    Caveat::FirstParty(Pred::AttrEq {
        key: "tool".into(),
        value: "read".into(),
    })
}

fn ok_ctx() -> Context {
    Context::new().at(10).attr("tool", "read")
}

/// THE MANDATORY ONE. Four identities, minting and attenuating interleaved: no
/// credential may ever verify under another identity's enrolled hybrid root.
#[test]
fn two_identities_never_share_a_derived_pq_key() {
    let roots: Vec<RootKey> = [0x11u8, 0x22, 0x33, 0xf0]
        .iter()
        .map(|b| RootKey::from_seed([*b; 32]))
        .collect();
    let enrolled: Vec<HybridRootPublic> = roots.iter().map(RootKey::public_hybrid).collect();

    // Distinct seeds must derive distinct PQ anchors — otherwise every
    // cross-check below would be vacuous.
    for (i, a) in enrolled.iter().enumerate() {
        for (j, b) in enrolled.iter().enumerate() {
            if i != j {
                assert_ne!(
                    a.ml_dsa, b.ml_dsa,
                    "distinct root seeds must derive distinct ML-DSA anchors ({i} vs {j})"
                );
            }
        }
    }

    // INTERLEAVED. Round 0 mints (filling every memo); rounds 1–2 attenuate,
    // which RE-KEYS each credential in place — the case where a memo bound to the
    // object rather than to the seed would start serving a stale key.
    let mut creds: Vec<Credential> = roots.iter().map(|r| r.mint([read_caveat()])).collect();
    for _round in 0..2 {
        creds = creds
            .into_iter()
            .map(|c| c.attenuate([read_caveat()]))
            .collect();
        // Each root also keeps minting, so its own memo is read repeatedly while
        // its neighbours are reading theirs.
        for (i, root) in roots.iter().enumerate() {
            let extra = root.mint([read_caveat()]);
            assert_eq!(
                extra.verify_hybrid(&enrolled[i], &ok_ctx()),
                Ok(()),
                "root {i} stopped minting credentials that verify under its own anchor"
            );
        }
    }

    // THE FALSIFIER: own root admits, every other root refuses.
    for (i, cred) in creds.iter().enumerate() {
        assert_eq!(
            cred.verify_hybrid(&enrolled[i], &ok_ctx()),
            Ok(()),
            "credential {i} must admit under its own enrolled hybrid root"
        );
        for (j, other) in enrolled.iter().enumerate() {
            if i != j {
                assert!(
                    cred.verify_hybrid(other, &ok_ctx()).is_err(),
                    "credential {i} verified under root {j}'s enrolled anchor — two \
                     identities are sharing a derived key"
                );
            }
        }
    }

    // And again on the wire, where the memo is empty and must be refilled from
    // the seed each credential actually carries.
    for (i, cred) in creds.iter().enumerate() {
        let decoded = Credential::decode(&cred.encode()).expect("decode");
        assert_eq!(decoded.verify_hybrid(&enrolled[i], &ok_ctx()), Ok(()));
        for (j, other) in enrolled.iter().enumerate() {
            if i != j {
                assert!(
                    decoded.verify_hybrid(other, &ok_ctx()).is_err(),
                    "decoded credential {i} verified under root {j}'s anchor"
                );
            }
        }
    }
}

/// The memo is interior mutability, and interior mutability is where `Sync` quietly dies. Both
/// types cross thread boundaries in this crate's real consumers (async forward-auth handlers in
/// `deploy/gateway-ask`, `agent-platform`, `sandstorm-serve`), so losing either bound would be a
/// downstream break with no local symptom.
#[test]
fn a_credential_stays_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Credential>();
    assert_send_sync::<RootKey>();
}

/// A mixed anchor — the right ed25519 root, a NEIGHBOUR's ML-DSA root — must
/// refuse. This is the sharpest cross-identity check the public API exposes: it
/// isolates the PQ half, so a memo leak cannot hide behind a passing classical
/// chain.
#[test]
fn a_neighbours_pq_anchor_does_not_admit() {
    let mine = RootKey::from_seed([0x71; 32]);
    let theirs = RootKey::from_seed([0x72; 32]);
    let cred = mine.mint([read_caveat()]).attenuate([read_caveat()]);

    assert_eq!(cred.verify_hybrid(&mine.public_hybrid(), &ok_ctx()), Ok(()));
    let mixed = HybridRootPublic {
        ed25519: mine.public(),
        ml_dsa: theirs.public_hybrid().ml_dsa,
    };
    assert!(
        cred.verify_hybrid(&mixed, &ok_ctx()).is_err(),
        "the PQ half must be checked against the enrolled anchor, and my chain \
         must not verify under my neighbour's"
    );
}

/// An attenuated credential must present its OWN tail PQ key, never its parent's
/// — the re-key that the memo's seed binding exists to survive. Driven on the
/// wire: the child admits, and the parent's still-valid encoded form admits
/// separately, so neither inherited the other's key.
#[test]
fn attenuation_does_not_inherit_the_parents_pq_key() {
    let root = RootKey::from_seed([0x73; 32]);
    let parent = root.mint([read_caveat()]);
    let parent_wire = parent.encode();
    let child = parent.attenuate([read_caveat()]);

    let enrolled = root.public_hybrid();
    assert_eq!(child.verify_hybrid(&enrolled, &ok_ctx()), Ok(()));
    assert_eq!(
        Credential::decode(&parent_wire)
            .expect("decode")
            .verify_hybrid(&enrolled, &ok_ctx()),
        Ok(()),
        "the parent's own encoded form must still verify — the child did not take \
         its key, and the parent did not take the child's"
    );

    // Different chains: the child carries one more block than the parent.
    assert_ne!(parent_wire, child.encode());
}
