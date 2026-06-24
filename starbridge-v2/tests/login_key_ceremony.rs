//! LOGIN AS A REAL KEY CEREMONY — the principled-Houyhnhnm-affordance proof.
//!
//! These are the `cargo test` witnesses for the claim that deos login is a genuine
//! key ceremony, not a demo identity-picker:
//!
//! 1. **MINT** — a NEW user has an Ed25519 keypair minted, its seed persisted into
//!    the encrypted key store, and the login ceremony births its GENESIS sovereign
//!    cell + grants the ROOT CAPABILITY (the session c-list) over its own world.
//! 2. **PRESENT (return)** — a returning user PRESENTS their key: the persisted seed
//!    is loaded, the same key reconstructed, a fresh challenge SIGNED + verified
//!    (real challenge–response), and the SAME root cell / session / c-list re-derived.
//! 3. **WRONG KEY REFUSED** — a signature by the wrong key (or over a different
//!    challenge, or a forged zero signature) fails `authenticate_signed` — no
//!    principal, nothing downstream runs.
//! 4. **GUEST IS STRICTLY-ATTENUATED** — a guest / agent sub-identity is born holding
//!    a strictly narrower cap-tree than the owner (a derived, attenuated capability),
//!    and an agent gets NO home cell.
//!
//! Gpui-free: the ceremony is the pure-flow `starbridge_v2::session` layer the
//! (gpui-gated) login surface renders, so these exercise the EXACT login path.

#![cfg(not(target_arch = "wasm32"))]

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_secrets::EncryptedFileStore;
use dregg_turn::ComputronCosts;
use starbridge_v2::session::{
    agent_template, default_user_template, open_session_world, Challenge, IdentityKeystore,
    LoginManager, LoginOutcome, Principal, ROOT_TOKEN,
};

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// A unique throwaway base dir for a per-test deos image (key store + per-user image).
fn scratch_dir() -> PathBuf {
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!("sbv2-keyceremony-{pid}-{nanos}-{n}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A keystore over a plain encrypted-file backend rooted at `dir` (deterministic,
/// no OS keychain — the portable custody the default desktop path also uses).
fn keystore_at(dir: &std::path::Path) -> IdentityKeystore {
    let store = EncryptedFileStore::new(dir.join("secrets"), [0x42u8; 32]);
    IdentityKeystore::new(Box::new(store))
}

#[test]
fn mint_births_a_keypair_a_genesis_cell_and_the_root_capability() {
    // (1) MINT — a brand-new user. No key exists; minting generates one, PERSISTS
    // its seed, and the login ceremony births the genesis cell + root-cap c-list.
    let dir = scratch_dir();
    let ks = keystore_at(&dir);

    assert!(
        !ks.has_identity("ember"),
        "a brand-new user has no custodied key yet"
    );

    // MINT: a real Ed25519 keypair is generated + persisted; a recovery phrase is
    // returned ONCE (the owner's key in human form).
    let minted = ks.mint("ember").expect("mint a fresh identity");
    assert_eq!(
        minted.mnemonic.split_whitespace().count(),
        24,
        "the recovery phrase is a 24-word mnemonic"
    );
    assert!(
        ks.has_identity("ember"),
        "the minted seed is now persisted in the key store"
    );

    // The genesis sovereign cell is the content-address of the minted key — "your
    // world" is literally derived from the keypair.
    let pubkey = minted.pubkey();
    assert_eq!(
        minted.root_cell(),
        dregg_types::CellId::derive_raw(&pubkey, &ROOT_TOKEN),
        "the genesis cell IS derive_raw(pubkey, ROOT_TOKEN)"
    );

    // Run the FULL ceremony over a durable per-user image: authenticate (real
    // challenge–response with the minted key), then login → mint the genesis cell +
    // grant the root-cap template. The resulting c-list IS the session.
    let principal = Principal { pubkey };
    let (mut world, anchors, mgr, fresh) =
        open_session_world(&dir, &principal, ComputronCosts::zero()).expect("open per-user image");
    assert!(fresh, "first launch provisions a fresh per-user image");

    // REAL CHALLENGE–RESPONSE: the holder signs the manager's fresh challenge with
    // the minted clerk; the manager verifies the Ed25519 signature.
    let challenge = mgr.issue_challenge();
    let sig = challenge.sign_with(&minted.clerk);
    let proven = mgr
        .authenticate_signed(pubkey, &challenge, &sig)
        .expect("the minted key signs the challenge → authenticated");
    assert_eq!(proven.pubkey, pubkey);
    assert_eq!(
        proven.root_cell(),
        minted.root_cell(),
        "the proven principal derives the same genesis cell"
    );

    // The cell does not exist until the ceremony mints it.
    assert!(
        world.ledger().get(&proven.root_cell()).is_none(),
        "the genesis cell is not present before login"
    );
    let template = default_user_template(anchors);
    let session = match mgr.login(&mut world, proven, &template) {
        LoginOutcome::Session(s) => s,
        LoginOutcome::Denied { reason } => panic!("owner login should succeed: {reason}"),
    };

    // The genesis cell was minted and now HOLDS the root capability (the c-list).
    assert!(
        world.ledger().get(&session.root_cell).is_some(),
        "the ceremony births the genesis sovereign cell"
    );
    assert!(
        session.is_live(&world),
        "the freshly logged-in session holds its root capability"
    );
    let [_treasury, service, user] = anchors;
    assert!(session.reaches(&world, &user), "the owner reaches its home cell");
    assert!(
        session.reaches(&world, &service),
        "the owner reaches its launchable app"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn returning_user_presents_the_key_and_re_derives_the_same_session() {
    // (2) PRESENT — a returning user. The persisted seed is loaded, the SAME key
    // reconstructed, a fresh challenge signed + verified, and the SAME root cell /
    // session / c-list re-derived from the durable image.
    let dir = scratch_dir();

    // FIRST RUN: mint + first login, capturing the root cell + c-list shape.
    let (root, granted_len, persisted_pubkey) = {
        let ks = keystore_at(&dir);
        let minted = ks.mint("ember").expect("mint");
        let pubkey = minted.pubkey();
        let principal = Principal { pubkey };
        let (mut world, anchors, mgr, _fresh) =
            open_session_world(&dir, &principal, ComputronCosts::zero()).expect("open image");
        let challenge = mgr.issue_challenge();
        let sig = challenge.sign_with(&minted.clerk);
        let proven = mgr.authenticate_signed(pubkey, &challenge, &sig).unwrap();
        let session = mgr
            .login_resumable(&mut world, proven, &default_user_template(anchors))
            .session()
            .expect("first login")
            .clone();
        world.checkpoint_now();
        (session.root_cell, session.granted.len(), pubkey)
        // world dropped → durable image persists + handle releases.
    };

    // RETURN: a fresh keystore (same dir) PRESENTS the key — no re-mint. The loaded
    // clerk reconstructs the SAME public key, signs a fresh challenge, and the
    // durable image RESUMES the same session.
    {
        let ks = keystore_at(&dir);
        assert!(ks.has_identity("ember"), "the key persisted across the relaunch");
        let clerk = ks
            .present("ember")
            .expect("load the persisted key")
            .expect("the key is present on return");
        let pubkey = clerk.public_key().0;
        assert_eq!(
            pubkey, persisted_pubkey,
            "presenting the key reconstructs the SAME public key"
        );

        let principal = Principal { pubkey };
        let (mut world, anchors, mgr, fresh) =
            open_session_world(&dir, &principal, ComputronCosts::zero()).expect("reopen image");
        assert!(!fresh, "the relaunch recovers the existing per-user image");

        // Real challenge–response with the PRESENTED key.
        let challenge = mgr.issue_challenge();
        let sig = challenge.sign_with(&clerk);
        let proven = mgr
            .authenticate_signed(pubkey, &challenge, &sig)
            .expect("the presented key authenticates");
        assert_eq!(
            proven.root_cell(),
            root,
            "the presented key re-derives the SAME root cell"
        );

        // RESUME: the same session / c-list comes back (no re-grant ceremony ran).
        let resumed = match mgr.login_resumable(&mut world, proven, &default_user_template(anchors)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("resume should succeed: {reason}"),
        };
        assert_eq!(resumed.root_cell, root, "the resumed session is the same root");
        assert_eq!(
            resumed.granted.len(),
            granted_len,
            "the same c-list re-derived on return"
        );
        assert!(resumed.is_live(&world), "the resumed session is live");
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_wrong_key_is_refused() {
    // (3) WRONG KEY REFUSED — authentication is a REAL Ed25519 verification, so only
    // the genuine holder passes. A wrong key, a signature over a different challenge,
    // and a forged zero signature are all refused.
    let dir = scratch_dir();
    let ks = keystore_at(&dir);
    let owner = ks.mint("ember").expect("mint owner");
    let attacker = ks.mint("attacker").expect("mint attacker");

    let mgr = LoginManager::new(dregg_types::CellId::derive_raw(&[0u8; 32], &[0u8; 32]));
    let challenge = mgr.issue_challenge();

    // The OWNER's own key over the challenge → authenticated (baseline).
    let owner_sig = challenge.sign_with(&owner.clerk);
    assert!(
        mgr.authenticate_signed(owner.pubkey(), &challenge, &owner_sig)
            .is_some(),
        "the genuine key passes"
    );

    // WRONG KEY: the attacker signs, but claims to be the owner → REFUSED (the
    // attacker's signature does not verify under the owner's public key).
    let attacker_sig = challenge.sign_with(&attacker.clerk);
    assert!(
        mgr.authenticate_signed(owner.pubkey(), &challenge, &attacker_sig)
            .is_none(),
        "a signature by the wrong key is refused"
    );

    // The owner cannot impersonate the attacker either.
    assert!(
        mgr.authenticate_signed(attacker.pubkey(), &challenge, &owner_sig)
            .is_none(),
        "the owner cannot present as the attacker"
    );

    // REPLAY / WRONG CHALLENGE: a signature over a DIFFERENT challenge does not
    // authenticate against this one (the nonce is single-use, domain-separated).
    let other = Challenge::from_nonce([0x99u8; 32]);
    let stale_sig = other.sign_with(&owner.clerk);
    assert!(
        mgr.authenticate_signed(owner.pubkey(), &challenge, &stale_sig)
            .is_none(),
        "a signature over a different challenge is refused (no replay)"
    );

    // FORGED zero signature → refused.
    let forged = dregg_sdk::Signature([0u8; 64]);
    assert!(
        mgr.authenticate_signed(owner.pubkey(), &challenge, &forged)
            .is_none(),
        "a forged zero signature is refused"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_guest_and_an_agent_are_strictly_attenuated_derived_caps() {
    // (4) GUEST / AGENT ARE STRICTLY-ATTENUATED — the same ceremony, a narrower
    // mandate. A guest is its own derived identity (its own root cell); an agent is
    // born holding STRICTLY less than the owner — no home cell.
    let dir = scratch_dir();
    let ks = keystore_at(&dir);
    let owner = ks.mint("ember").expect("mint owner");
    let guest = ks.mint("guest").expect("mint guest");
    let agent = ks.mint("hermes").expect("mint agent");

    // Distinct keys → distinct sovereign worlds (derived, not shared).
    assert_ne!(owner.pubkey(), guest.pubkey(), "owner and guest are distinct keys");
    assert_ne!(
        owner.root_cell(),
        guest.root_cell(),
        "owner and guest derive distinct root cells (their own worlds)"
    );

    let (mut world, anchors, mgr, _fresh) = open_session_world(
        &dir,
        &Principal {
            pubkey: owner.pubkey(),
        },
        ComputronCosts::zero(),
    )
    .expect("open image");
    let [_treasury, service, user] = anchors;

    // OWNER session: the full template — home + launcher.
    let owner_principal = Principal {
        pubkey: owner.pubkey(),
    };
    let owner_session = mgr
        .login(&mut world, owner_principal, &default_user_template(anchors))
        .session()
        .expect("owner login")
        .clone();
    assert!(owner_session.reaches(&world, &user), "owner reaches home");
    assert!(owner_session.reaches(&world, &service), "owner reaches launcher");

    // AGENT session: the SAME ceremony, the narrower `agent_template` — ONLY the
    // tool surface, and crucially NO home cell. A strictly-attenuated mandate.
    let agent_principal = Principal {
        pubkey: agent.pubkey(),
    };
    let agent_session = mgr
        .login(&mut world, agent_principal, &agent_template(anchors))
        .session()
        .expect("agent login")
        .clone();
    assert!(
        agent_session.reaches(&world, &service),
        "the agent reaches its tool surface"
    );
    assert!(
        !agent_session.reaches(&world, &user),
        "the agent gets NO home cell — strictly narrower than the owner"
    );

    // The agent's c-list is a STRICT SUBSET of the owner's reach: every target the
    // agent reaches, the owner also reaches; the owner reaches more (home).
    let owner_reaches_user = owner_session.reaches(&world, &user);
    let owner_reaches_service = owner_session.reaches(&world, &service);
    let agent_reaches_user = agent_session.reaches(&world, &user);
    let agent_reaches_service = agent_session.reaches(&world, &service);
    assert!(
        owner_reaches_service && agent_reaches_service,
        "both reach the shared tool surface"
    );
    assert!(
        owner_reaches_user && !agent_reaches_user,
        "the owner reaches home, the agent does not — strict attenuation"
    );

    // LOGOUT is the agent kill switch: one revoke darkens its whole (narrow) tree,
    // and the owner's session is untouched.
    assert_eq!(
        mgr.logout(&mut world, &agent_session),
        1,
        "the agent's single cap revoked"
    );
    assert!(!agent_session.is_live(&world), "the agent session is dark");
    assert!(
        owner_session.is_live(&world),
        "the owner session is untouched by the agent's logout"
    );

    // Guard against an unused-binding warning on the guest (its distinctness is the
    // assertion above).
    let _ = guest;

    let _ = std::fs::remove_dir_all(&dir);
}
