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

use dreggnet_asset::{
    AssetError, AssetId, AssetWorld, NoteDesc, ProvenanceBreak, default_trait_root,
    verify_desc_chain,
};

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
        trait_root: honest[0].trait_root,
        soulbound: honest[0].soulbound,
    });
    assert_eq!(
        verify_desc_chain(&spliced, id),
        Err(ProvenanceBreak::BrokenLink { index: 2 }),
        "a spliced version with a broken link is caught"
    );
}

// ============================================================================
// First-class committed trait_root (E1)
// ============================================================================

#[test]
fn a_plain_mint_carries_a_default_committed_trait_root() {
    let mut w = AssetWorld::new();
    let id = w.mint("alice", b"trait-target");
    // The first-class trait_root is populated (E1): a consumer reads it from the committed
    // asset identity instead of re-deriving from raw AssetId bytes.
    let root = w
        .trait_root_of(id)
        .expect("a minted asset has a committed trait root");
    assert_eq!(
        root,
        default_trait_root(&id),
        "a plain mint commits the deterministic default trait root"
    );
    assert_ne!(
        root, [0u8; 32],
        "the committed root is meaningful, not zero"
    );
    // The descriptors expose it too, and it is carried unchanged.
    let descs = w.provenance_descs(id);
    assert_eq!(descs[0].trait_root, root);
}

#[test]
fn mint_with_traits_commits_an_explicit_root_carried_across_the_lineage() {
    let mut w = AssetWorld::new();
    let explicit = [0x5Au8; 32]; // e.g. a gear StatBlock digest
    let id = w.mint_with_traits("smith", b"flamebrand", explicit);
    assert_eq!(
        w.trait_root_of(id),
        Some(explicit),
        "the explicit content root is the committed trait root"
    );

    // It rides WriteOnce across a transfer (the visual/stat layer sees the same root on every
    // version, so provenance and appearance stay bound together).
    w.transfer(id, "smith", "buyer").expect("transfer lands");
    let report = w.verify_provenance(id);
    assert!(report.verified, "lineage verifies: {:?}", report.reasons);
    for d in w.provenance_descs(id) {
        assert_eq!(
            d.trait_root, explicit,
            "trait root carried across the lineage"
        );
    }
}

#[test]
fn a_forged_trait_root_in_a_successor_fails_the_re_derivation() {
    let mut w = AssetWorld::new();
    let id = w.mint_with_traits("alice", b"heirloom", [0x01u8; 32]);
    w.transfer(id, "alice", "bob").expect("t1");
    let mut descs = w.provenance_descs(id);
    // Rewrite the successor's committed trait root (a re-skin attack) but recompute prev so the
    // hash link would otherwise pass — the carried-root check still catches it.
    descs[1].trait_root = [0xEEu8; 32];
    descs[1].prev = dreggnet_asset::note_digest(&descs[0]);
    assert_eq!(
        verify_desc_chain(&descs, id),
        Err(ProvenanceBreak::Inconsistent {
            index: 1,
            reason: "trait_root not carried",
        }),
        "a rewritten committed trait root is caught"
    );
}

// ============================================================================
// First-class soulbound (non-transferable) — ISA-enforced
// ============================================================================

#[test]
fn a_soulbound_asset_refuses_transfer_at_the_isa_non_vacuously() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let id = w.mint_soulbound("alice", b"achievement-badge");
    assert!(w.is_soulbound(id), "minted soulbound");

    // The OWNER signs a real, valid transfer — and it is STILL refused, because the note's
    // transfer case requires FieldEquals(soulbound, 0). This is cryptographic ISA refusal,
    // not app bookkeeping: the same signer, on a normal note, commits (below).
    let moved = w.transfer(id, "alice", "bob");
    assert!(
        matches!(moved, Err(AssetError::Refused(_))),
        "a soulbound asset refuses even an owner-signed transfer, got {moved:?}"
    );
    assert_eq!(
        w.current_owner(id),
        Some(alice),
        "it stayed bound to the earner"
    );
    assert_eq!(w.lineage_len(id), 1, "no successor minted");

    // NON-VACUOUS: the SAME owner minting a NON-soulbound note CAN transfer it.
    let free = w.mint("alice", b"free-item");
    assert!(!w.is_soulbound(free));
    w.transfer(free, "alice", "bob")
        .expect("a non-soulbound note transfers fine");
    assert_eq!(w.current_owner(free), w.current_owner(free));
}

#[test]
fn a_soulbound_asset_still_verifies_its_provenance() {
    let mut w = AssetWorld::new();
    let id = w.mint_soulbound_with_traits("earner", b"platinum", [0x77u8; 32]);
    let report = w.verify_provenance(id);
    assert!(
        report.verified,
        "a soulbound mint verifies: {:?}",
        report.reasons
    );
    assert_eq!(w.trait_root_of(id), Some([0x77u8; 32]));
    // The soulbound flag is committed and carried.
    assert_eq!(w.provenance_descs(id)[0].soulbound, 1);
}

// ============================================================================
// Batch mint
// ============================================================================

#[test]
fn batch_mint_produces_independent_owned_assets() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let seeds: [&[u8]; 3] = [b"pack-card-1", b"pack-card-2", b"pack-card-3"];
    let ids = w.mint_batch("alice", &seeds);
    assert_eq!(ids.len(), 3);
    // Distinct assets, each a one-version lineage owned by the minter.
    assert_ne!(ids[0].bytes(), ids[1].bytes());
    assert_ne!(ids[1].bytes(), ids[2].bytes());
    for id in &ids {
        assert_eq!(w.current_owner(*id), Some(alice));
        assert_eq!(w.lineage_len(*id), 1);
        assert!(w.verify_provenance(*id).verified);
    }
    // A batch id matches the individual mint of the same seed (batch is pure convenience).
    let solo = AssetWorld::new().mint("alice", b"pack-card-2");
    assert_eq!(ids[1].bytes(), solo.bytes());
}

// ============================================================================
// Revocation — the minter burns a mis-minted, still-held asset
// ============================================================================

#[test]
fn a_minter_can_revoke_a_still_held_asset() {
    let mut w = AssetWorld::new();
    let _alice = w.pubkey_of("alice");
    let id = w.mint("alice", b"oops-wrong-stats");
    assert!(!w.is_revoked(id));

    w.revoke(id, "alice")
        .expect("the minter revokes a still-held asset");
    assert!(w.is_revoked(id), "the asset is now revoked");
    assert_eq!(
        w.current_owner(id),
        None,
        "a revoked asset has no live holder"
    );

    // A revoked asset cannot be transferred (the origin was burned).
    assert!(
        matches!(w.transfer(id, "alice", "bob"), Err(AssetError::Refused(_))),
        "a revoked asset refuses transfer"
    );
    // And its provenance still verifies — as a clean burn (the tail is spent on-chain).
    let report = w.verify_provenance(id);
    assert!(report.revoked);
    assert!(
        report.verified,
        "a cleanly revoked asset verifies as a burn: {:?}",
        report.reasons
    );
}

/// A **soulbound** asset is BURNABLE by its holder while staying non-transferable — the
/// property `revoke`'s doc-comment always claimed and the code did not deliver, because the
/// burn was driven through `TRANSFER_METHOD`, whose case gates on `FieldEquals(soulbound, 0)`.
/// Both polarities on ONE note, so this cannot pass vacuously: the transfer is refused, the
/// burn commits.
#[test]
fn a_soulbound_asset_is_burnable_by_its_holder_though_never_transferable() {
    let mut w = AssetWorld::new();
    let earner = w.pubkey_of("earner");
    let id = w.mint_soulbound("earner", b"platinum-badge");
    assert!(w.is_soulbound(id));

    // Non-transferable, even owner-signed — the ISA gate.
    assert!(
        matches!(
            w.transfer(id, "earner", "buyer"),
            Err(AssetError::Refused(_))
        ),
        "a soulbound note refuses transfer"
    );
    assert_eq!(
        w.current_owner(id),
        Some(earner),
        "still bound to the earner"
    );

    // ...yet the SAME note burns under the holder's own signature.
    w.burn(id, "earner")
        .expect("the holder can destroy their own soulbound credential");
    assert!(w.is_burned(id), "the badge is gone");
    assert_eq!(
        w.current_owner(id),
        None,
        "a burned note has no live holder"
    );
    let report = w.verify_provenance(id);
    assert!(
        report.verified,
        "a cleanly burned soulbound note verifies as a burn: {:?}",
        report.reasons
    );

    // And a minter's revoke of a soulbound asset — the exact doc claim — now really commits.
    let other = w.mint_soulbound("earner", b"gold-badge");
    w.revoke(other, "earner")
        .expect("the minter can revoke a soulbound mis-mint");
    assert!(w.is_revoked(other));
}

/// The general OWNER-gated burn: whoever CURRENTLY holds a note can destroy it, minter or
/// not — the primitive a crafting sink needs so a material a player *bought* is consumable.
/// Non-vacuous in both directions: the minter (who handed it off) can no longer burn it, the
/// new holder can; and after the burn nobody can burn it again.
#[test]
fn the_current_holder_can_burn_a_note_they_did_not_mint() {
    let mut w = AssetWorld::new();
    let _minter = w.pubkey_of("minter");
    let holder = w.pubkey_of("holder");
    let id = w.mint("minter", b"traded-material");
    w.transfer(id, "minter", "holder").expect("the sale");
    assert_eq!(w.current_owner(id), Some(holder));

    // The MINTER is no longer the owner: their burn is a real cryptographic refusal (the
    // signature does not verify against the tail version cell's key).
    let by_minter = w.burn(id, "minter");
    assert!(
        matches!(by_minter, Err(AssetError::Refused(_))),
        "a former owner cannot burn what they handed off, got {by_minter:?}"
    );
    assert_eq!(
        w.current_owner(id),
        Some(holder),
        "anti-ghost: the refused burn destroyed nothing"
    );
    // A third party who never held it cannot either.
    assert!(
        matches!(w.burn(id, "mallory"), Err(AssetError::Refused(_))),
        "a stranger cannot burn someone else's note"
    );
    assert!(!w.is_burned(id));

    // The CURRENT holder can — this is exactly what `revoke` (minter-gated) refuses, so the
    // owner-gated door is doing real work, not duplicating the old one.
    assert!(
        matches!(w.revoke(id, "holder"), Err(AssetError::Refused(_))),
        "revoke still demands the minter; burn is the general door"
    );
    w.burn(id, "holder")
        .expect("the current holder burns the note they acquired");
    assert!(w.is_burned(id));
    assert_eq!(w.current_owner(id), None);

    // Once burned: no re-burn, no transfer, and the lineage still re-verifies as a burn.
    assert!(matches!(w.burn(id, "holder"), Err(AssetError::Refused(_))));
    assert!(matches!(
        w.transfer(id, "holder", "minter"),
        Err(AssetError::Refused(_))
    ));
    let report = w.verify_provenance(id);
    assert!(report.revoked, "the report marks it burned");
    assert!(
        report.verified,
        "the burned lineage verifies: {:?}",
        report.reasons
    );
    assert_eq!(report.length, 2, "mint + one transfer, then the burn");
}

/// **A duplicate mint does not corrupt a lineage.** An `AssetId` is
/// `blake3(minter_pk ‖ mint_seed)`, so the same `(minter, seed)` names the SAME object.
/// Re-minting used to append a second bogus origin (`prev = 0`, `serial = 1`) to the live
/// lineage, which then failed its own content-address re-derivation — silently. Now `mint` is
/// a no-op returning the existing id, and `try_mint` refuses so a caller that needs a FRESH
/// object finds out.
#[test]
fn a_duplicate_mint_is_refused_and_never_breaks_the_lineage() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let id = w.mint("alice", b"one-of-a-kind");
    w.transfer(id, "alice", "bob").expect("a real transfer");
    assert_eq!(w.lineage_len(id), 2);

    // The checked door refuses.
    assert!(
        matches!(
            w.try_mint("alice", b"one-of-a-kind"),
            Err(AssetError::DuplicateMint)
        ),
        "a repeat of the same (minter, seed) is not a second asset"
    );
    // The infallible door is a no-op returning the same address — NOT a second origin.
    let again = w.mint("alice", b"one-of-a-kind");
    assert_eq!(again.bytes(), id.bytes());
    assert_eq!(
        w.lineage_len(id),
        2,
        "the duplicate mint appended no bogus origin"
    );
    let report = w.verify_provenance(id);
    assert!(
        report.verified,
        "the lineage still re-verifies after a duplicate mint: {:?}",
        report.reasons
    );
    assert_eq!(report.current_owner, w.pubkey_of("bob"));

    // NON-VACUOUS: a genuinely different seed still mints a fresh asset.
    let fresh = w
        .try_mint("alice", b"a-different-thing")
        .expect("a new content address mints");
    assert_ne!(fresh.bytes(), id.bytes());
    assert_eq!(w.current_owner(fresh), Some(alice));
}

/// The content address is RECOMPUTABLE by a third party with no ledger: `AssetId::derive`
/// reproduces exactly what a mint of `(minter_pk, seed)` lands on. This is what lets a
/// downstream layer ADOPT an existing note by identity instead of re-minting a look-alike.
#[test]
fn asset_id_derive_reproduces_the_minted_address() {
    let mut w = AssetWorld::new();
    let alice = w.pubkey_of("alice");
    let id = w.mint("alice", b"recomputable");
    assert_eq!(
        AssetId::derive(&alice, b"recomputable").bytes(),
        id.bytes(),
        "anyone holding the minter key + seed recomputes the address"
    );
    assert_ne!(
        AssetId::derive(&alice, b"other").bytes(),
        id.bytes(),
        "and a different seed does not collide"
    );
}

/// The holder inventory read: `assets_held_by` names exactly the live notes a label owns, and
/// tracks transfers and burns.
#[test]
fn assets_held_by_is_the_live_inventory() {
    let mut w = AssetWorld::new();
    let a = w.mint("alice", b"i-1");
    let b = w.mint("alice", b"i-2");
    let c = w.mint("bob", b"i-3");
    assert_eq!(w.assets_held_by("alice").len(), 2);
    assert_eq!(w.assets_held_by("bob"), vec![c]);
    assert_eq!(w.assets_held_by("nobody"), vec![]);

    w.transfer(a, "alice", "bob").expect("hand one over");
    assert_eq!(w.assets_held_by("alice"), vec![b]);
    assert_eq!(w.assets_held_by("bob").len(), 2, "bob now holds two");

    w.burn(b, "alice").expect("alice burns hers");
    assert!(
        w.assets_held_by("alice").is_empty(),
        "a burned note leaves the inventory"
    );
    assert_eq!(w.all_assets().len(), 3, "the census still knows all three");
}

#[test]
fn a_non_minter_cannot_revoke_and_a_transferred_asset_cannot_be_revoked() {
    let mut w = AssetWorld::new();
    let _alice = w.pubkey_of("alice");
    let bob = w.pubkey_of("bob");
    let id = w.mint("alice", b"legit-item");

    // A non-minter revoke is refused.
    assert!(
        matches!(w.revoke(id, "mallory"), Err(AssetError::Refused(_))),
        "a non-minter cannot revoke"
    );
    assert!(!w.is_revoked(id), "the failed revoke changed nothing");
    assert_eq!(w.current_owner(id), Some(w.pubkey_of("alice")));

    // Hand it off; now even the minter cannot revoke (they no longer hold it).
    w.transfer(id, "alice", "bob").expect("transfer");
    assert_eq!(w.current_owner(id), Some(bob));
    assert!(
        matches!(w.revoke(id, "alice"), Err(AssetError::Refused(_))),
        "the minter cannot revoke an asset they have handed off"
    );
    assert!(!w.is_revoked(id));
    assert_eq!(w.current_owner(id), Some(bob), "the asset is untouched");
}
