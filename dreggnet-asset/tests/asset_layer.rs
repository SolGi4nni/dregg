//! Driven teeth for the verifiable asset layer — every claim a real executor turn or a
//! real content-address re-derivation, never a mock.
//!
//! The gates, in both polarities:
//!   * MINT binds the owner (the minter) + a stable content-addressed id;
//!   * a valid owner-signed TRANSFER lands + moves ownership (the new owner can then
//!     transfer, the old cannot — authority genuinely moved);
//!   * a NON-OWNER / forged transfer is REFUSED (non-vacuous: the owner-signed one commits);
//!   * a DOUBLE-SPEND (re-spending a spent version) is refused;
//!   * the PROVENANCE chain (mint → transfer → transfer) is recorded + verifies by replay;
//!   * a TAMPERED lineage fails the content-address re-derivation;
//!   * the asset id is STABLE / content-addressed across versions + independent of cells.

use dreggnet_asset::{AssetError, AssetWorld, NoteDesc, ProvenanceBreak, verify_desc_chain};

#[test]
fn mint_binds_the_owner_and_a_content_addressed_id() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let id = w.mint("alice", b"dragon-card-#1");

    // The minter owns the fresh asset.
    assert_eq!(w.current_owner(id), Some(alice), "the minter owns the mint");
    assert_eq!(w.current_holder_label(id), Some("alice"));
    assert_eq!(w.lineage_len(id), 1, "a mint is a one-version lineage");

    // The id is content-addressed: re-minting the SAME (minter, seed) reproduces it, and a
    // different seed / a different minter gives a different id.
    let id_again = AssetWorld::new().mint("alice", b"dragon-card-#1");
    assert_eq!(id.bytes(), id_again.bytes(), "asset id is deterministic");
    let id_other_seed = AssetWorld::new().mint("alice", b"dragon-card-#2");
    assert_ne!(
        id.bytes(),
        id_other_seed.bytes(),
        "a different seed differs"
    );
    let mut w2 = AssetWorld::new();
    let id_other_minter = w2.mint("bob", b"dragon-card-#1");
    assert_ne!(
        id.bytes(),
        id_other_minter.bytes(),
        "a different minter differs"
    );

    // The provenance of a fresh mint verifies (a one-link origin chain).
    let report = w.verify_provenance(id);
    assert!(
        report.verified,
        "a fresh mint verifies: {:?}",
        report.reasons
    );
    assert_eq!(report.length, 1);
    assert_eq!(report.current_owner, alice);
}

#[test]
fn owner_signed_transfer_lands_and_moves_authority() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let bob = w.pubkey_of("bob");
    let carol = w.pubkey_of("carol");
    let id = w.mint("alice", b"loot-sword");

    // Alice (the owner) transfers to Bob — a real committed spend turn.
    let r = w
        .transfer(id, "alice", "bob")
        .expect("the owner-signed transfer commits");
    assert_eq!(r.new_owner, bob);
    assert_eq!(r.serial, 2);
    assert_eq!(w.current_owner(id), Some(bob), "ownership moved to bob");
    assert_eq!(w.lineage_len(id), 2);

    // Authority GENUINELY moved: the NEW owner (bob) can transfer onward...
    w.transfer(id, "bob", "carol")
        .expect("the new owner can transfer");
    assert_eq!(w.current_owner(id), Some(carol), "bob moved it to carol");

    // ...and neither the original minter (alice) nor the intermediate holder (bob) can move
    // it anymore — only carol, the current owner, holds authority.
    assert!(
        matches!(w.transfer(id, "alice", "bob"), Err(AssetError::Refused(_))),
        "the original minter cannot move a transferred asset"
    );
    assert!(
        matches!(w.transfer(id, "bob", "alice"), Err(AssetError::Refused(_))),
        "an intermediate holder cannot move it after passing it on"
    );
    assert_eq!(
        w.current_owner(id),
        Some(carol),
        "the refused moves changed nothing (anti-ghost)"
    );

    // Carol, the real owner, still can.
    w.transfer(id, "carol", "alice")
        .expect("the current owner moves it");
    assert_eq!(w.current_owner(id), Some(alice));
}

#[test]
fn a_forged_non_owner_transfer_is_refused_non_vacuously() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let mallory = w.pubkey_of("mallory");
    let id = w.mint("alice", b"rare-relic");

    // Mallory (not the owner) attempts to transfer alice's asset to herself. Her signature
    // does not verify under the version cell's owner key → a real executor refusal.
    let forged = w.transfer(id, "mallory", "mallory");
    assert!(
        matches!(forged, Err(AssetError::Refused(_))),
        "a forged (non-owner) transfer is refused, got {forged:?}"
    );
    assert_eq!(
        w.current_owner(id),
        Some(alice),
        "the forged transfer moved nothing"
    );
    assert_eq!(w.lineage_len(id), 1, "no successor was minted");

    // NON-VACUOUS: the SAME move signed by the real owner commits.
    w.transfer(id, "alice", "mallory")
        .expect("the owner-signed transfer to mallory commits");
    assert_eq!(w.current_owner(id), Some(mallory));
}

#[test]
fn a_double_spend_is_refused() {
    let mut w = AssetWorld::new();
    let _alice = w.pubkey_of("alice");
    let bob = w.pubkey_of("bob");
    let id = w.mint("alice", b"stake-token");

    // The first transfer spends the origin (version 0) and mints version 1.
    w.transfer(id, "alice", "bob")
        .expect("first transfer lands");
    assert_eq!(w.lineage_len(id), 2);

    // Re-spending the ALREADY-SPENT origin version (a double-spend) is refused by the
    // StrictMonotonic(spent) tooth (1 → 1 is not a strict increase).
    let double = w.attempt_respend(id, 0);
    assert!(
        matches!(double, Err(AssetError::Refused(_))),
        "a double-spend of the origin version is refused, got {double:?}"
    );
    assert_eq!(
        w.lineage_len(id),
        2,
        "no phantom version from a double-spend"
    );
    assert_eq!(w.current_owner(id), Some(bob));

    // NON-VACUOUS: the StrictMonotonic(spent) tooth is what discriminates — a FRESH
    // version's first spend (0 → 1) commits; only the second (1 → 1) is refused.
    let id2 = w.mint("carol", b"fresh-stake");
    w.attempt_respend(id2, 0)
        .expect("the first spend of a fresh version commits (0 -> 1)");
    assert!(
        matches!(w.attempt_respend(id2, 0), Err(AssetError::Refused(_))),
        "the second spend (1 -> 1) is refused by the spent tooth"
    );
}

#[test]
fn the_provenance_chain_verifies_by_replay() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let bob = w.pubkey_of("bob");
    let carol = w.pubkey_of("carol");
    let id = w.mint("alice", b"trophy");

    // mint → transfer → transfer: a three-version lineage.
    w.transfer(id, "alice", "bob").expect("t1");
    w.transfer(id, "bob", "carol").expect("t2");
    assert_eq!(w.lineage_len(id), 3);

    let report = w.verify_provenance(id);
    assert!(
        report.verified,
        "the full lineage verifies: {:?}",
        report.reasons
    );
    assert_eq!(report.length, 3);
    assert_eq!(report.current_owner, carol, "current holder is carol");

    // The published descriptors re-derive as a clean content-address chain, minter first.
    let descs = w.provenance_descs(id);
    assert_eq!(descs.len(), 3);
    assert_eq!(descs[0].owner, alice, "origin owner = minter");
    assert_eq!(descs[0].minter, alice);
    assert_eq!(descs[1].owner, bob);
    assert_eq!(descs[2].owner, carol);
    assert!(
        verify_desc_chain(&descs, id).is_ok(),
        "the pure re-derivation accepts the honest chain"
    );

    // The asset id is carried unchanged across every version (the stable cross-cell address).
    for d in &descs {
        assert_eq!(
            d.asset_id,
            id.bytes(),
            "asset id carried across the lineage"
        );
        assert_eq!(d.minter, alice, "minter (provenance root) carried");
    }
}

#[test]
fn a_tampered_lineage_fails_the_re_derivation() {
    let mut w = AssetWorld::new();
    let _alice = w.pubkey_of("alice");
    let _bob = w.pubkey_of("bob");
    let id = w.mint("alice", b"provenance-target");
    w.transfer(id, "alice", "bob").expect("t1");
    let honest = w.provenance_descs(id);
    assert!(verify_desc_chain(&honest, id).is_ok());

    // (a) A forged prev link (rewrite version 1's predecessor pointer) breaks the chain.
    let mut tampered = honest.clone();
    tampered[1].prev = [0x42u8; 32];
    assert_eq!(
        verify_desc_chain(&tampered, id),
        Err(ProvenanceBreak::BrokenLink { index: 1 }),
        "a forged prev link is caught"
    );

    // (b) A swapped owner on the origin (claiming a mint the minter never made) breaks it.
    let mut bad_origin = honest.clone();
    bad_origin[0].owner = [0x99u8; 32];
    assert!(
        matches!(
            verify_desc_chain(&bad_origin, id),
            Err(ProvenanceBreak::BadOrigin { .. })
        ),
        "a forged origin owner is caught"
    );

    // (c) A rewritten asset id (splicing a foreign asset's lineage) breaks it.
    let mut wrong_id = honest.clone();
    wrong_id[0].asset_id = [0x7u8; 32];
    assert_eq!(
        verify_desc_chain(&wrong_id, id),
        Err(ProvenanceBreak::AssetIdMismatch),
        "a rewritten asset id is caught"
    );

    // (d) A fabricated extra version with the right shape but a broken link is caught.
    let mut spliced = honest.clone();
    spliced.push(NoteDesc {
        asset_id: id.bytes(),
        minter: honest[0].minter,
        owner: [0x5u8; 32],
        prev: [0x0u8; 32], // NOT the digest of the real predecessor
        serial: 3,
    });
    assert_eq!(
        verify_desc_chain(&spliced, id),
        Err(ProvenanceBreak::BrokenLink { index: 2 }),
        "a spliced version with a broken link is caught"
    );
}
