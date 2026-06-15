//! End-to-end exercise of the sealed-submission commit-reveal curation lifecycle. The
//! in-process [`Gallery`] / [`Submission`] state machine is the executable witness of
//! the commit-reveal CRYPTO (seal binding, the phase gate, the membership gate); the
//! on-ledger floor (`floor_tests` in lib.rs + `tests/factory_birth.rs`) makes the
//! anti-tamper tooth an EXECUTOR REFUSAL.

use super::*;

// Three competing artists and a curator.
const ARTIST_A: ArtistId = 10;
const ARTIST_B: ArtistId = 11;
const ARTIST_C: ArtistId = 12;
const CURATOR: ArtistId = 1;

fn three_artist_gallery() -> (Gallery, Submission, Submission, Submission) {
    let sub_a = Submission::new(ARTIST_A, 30, 7);
    let sub_b = Submission::new(ARTIST_B, 50, 8); // the top piece (max digest)
    let sub_c = Submission::new(ARTIST_C, 40, 9);

    let mut gallery = Gallery::new(CURATOR);
    // SUBMISSION phase: each artist commits a sealed submission (others see only the hash).
    gallery.submit(sub_a.seal()).unwrap();
    gallery.submit(sub_b.seal()).unwrap();
    gallery.submit(sub_c.seal()).unwrap();
    (gallery, sub_a, sub_b, sub_c)
}

#[test]
fn full_flow_top_piece_is_featured() {
    let (mut gallery, sub_a, sub_b, sub_c) = three_artist_gallery();

    // Reveals are rejected while still submitting (no reveal before the call closes).
    assert_eq!(gallery.reveal(sub_b), Err(GalleryError::NotRevealPhase));

    // Close submissions, then everyone reveals.
    gallery.close_submissions();
    gallery.reveal(sub_a).unwrap();
    gallery.reveal(sub_b).unwrap();
    gallery.reveal(sub_c).unwrap();

    // The top piece (B, digest 50) is featured.
    assert_eq!(gallery.featured(), Some(sub_b));

    let featured = gallery.curate().unwrap();
    assert_eq!(featured, sub_b);
    assert_eq!(gallery.phase, Phase::Curated);
}

#[test]
fn no_reveal_before_submissions_close() {
    // While still submitting, valid_reveal is false and reveal errors.
    let (mut gallery, _a, sub_b, _c) = three_artist_gallery();
    assert!(!gallery.valid_reveal(&sub_b)); // still in submission phase
    assert_eq!(gallery.reveal(sub_b), Err(GalleryError::NotRevealPhase));
}

#[test]
fn no_late_swapping_changed_piece_is_rejected() {
    // The anti-tamper guarantee: an artist that committed `sub_b` cannot later reveal a
    // DIFFERENT piece (e.g. having seen others, wanting to swap in a better one) — the
    // changed piece hashes to a different seal that was never committed.
    let (mut gallery, _a, sub_b, _c) = three_artist_gallery();
    gallery.close_submissions();

    // B committed (B, 50, 8). It now tries to reveal (B, 70, 8) — a swapped piece.
    let swapped = Submission::new(ARTIST_B, 70, 8);
    assert_ne!(swapped.seal(), sub_b.seal());
    assert!(!gallery.valid_reveal(&swapped));
    assert_eq!(gallery.reveal(swapped), Err(GalleryError::NotSubmitted));

    // The original committed piece still reveals fine.
    gallery.reveal(sub_b).unwrap();
}

#[test]
fn impostor_cannot_claim_anothers_piece() {
    // The seal binds the artist identity: an impostor copying B's piece/nonce but with its
    // own id has a different seal, so it is not among the submissions.
    let (mut gallery, _a, sub_b, _c) = three_artist_gallery();
    gallery.close_submissions();

    let impostor = Submission::new(ARTIST_A, 50, 8); // copies B's piece+nonce, different artist
    assert_ne!(impostor.seal(), sub_b.seal());
    assert_eq!(gallery.reveal(impostor), Err(GalleryError::NotSubmitted));
}

#[test]
fn non_submitted_artist_cannot_reveal_or_be_featured() {
    // A party that never submitted — even with a stunning piece — cannot reveal, so it can
    // never be featured.
    let (mut gallery, _a, _b, _c) = three_artist_gallery();
    gallery.close_submissions();

    let outsider = Submission::new(13, 999, 1); // never submitted
    assert!(!gallery.valid_reveal(&outsider));
    assert_eq!(gallery.reveal(outsider), Err(GalleryError::NotSubmitted));
    assert_ne!(gallery.featured(), Some(outsider));
}

#[test]
fn cannot_curate_before_reveal_phase() {
    // Curation only fires in the reveal phase (no featuring while still submitting).
    let (mut gallery, _a, _b, _c) = three_artist_gallery();
    assert_eq!(gallery.curate(), Err(GalleryError::NotRevealPhase));
}

#[test]
fn nothing_to_feature_when_no_valid_reveals() {
    // Closing submissions but collecting no reveals yields nothing to feature.
    let (mut gallery, _a, _b, _c) = three_artist_gallery();
    gallery.close_submissions();
    assert_eq!(gallery.curate(), Err(GalleryError::NothingToFeature));
}

#[test]
fn late_submission_after_call_closes_is_rejected() {
    let (mut gallery, _a, _b, _c) = three_artist_gallery();
    gallery.close_submissions();
    let late = Submission::new(13, 5, 5);
    assert_eq!(
        gallery.submit(late.seal()),
        Err(GalleryError::NotSubmissionPhase)
    );
}

#[test]
fn seal_is_deterministic_and_binds_all_fields() {
    let s = Submission::new(7, 42, 99);
    assert_eq!(s.seal(), s.seal()); // deterministic
    // Each field is bound: changing any one changes the seal.
    assert_ne!(s.seal(), Submission::new(8, 42, 99).seal());
    assert_ne!(s.seal(), Submission::new(7, 43, 99).seal());
    assert_ne!(s.seal(), Submission::new(7, 42, 100).seal());
}
