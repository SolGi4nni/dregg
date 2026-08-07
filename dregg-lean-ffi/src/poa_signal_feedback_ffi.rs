//! The Path of Angels mid-run LOCKED/DRIFT boundary.
//!
//! # Why this exists
//!
//! Judged Signal was a slot machine. A public `SignalClaimV1` carries one code,
//! `SignalTriangulation.judge` returns `none` unless the transcript is SOLVED, and the
//! actual deduction game — 216 codes, LOCKED/DRIFT feedback, an information floor of
//! three rounds — existed only in the browser's practice mode against
//! `HiddenInstance.practiceRunSeed`, which no judge will ever score. So on-chain play
//! was a blind 1-in-216 guess and the game beside it settled nothing.
//!
//! Making judged play the real game means applying the scoring rule mid-run, to the
//! JUDGED instance. That rule is `SignalTriangulation.feedback`, and it stays in Lean:
//! a Rust `exactCount`/`presentCount` would be a twin of the function that decides
//! whether a run settles, and a twin that disagrees by one on a duplicate band hands
//! players a different game than the one that settles. Rust computes nothing here. It
//! carries bytes to Lean and back.
//!
//! # The posture that separates this from [`crate::poa_slot_derive_ffi`]
//!
//! That seam's reply is the ANSWER — run seed and target — and its docblock says
//! nothing rendering it may reach a route. This seam's reply is two counts, `exact`
//! and `present`, and it is DELIBERATELY reachable from an authenticated route.
//!
//! The difference is structural, not a policy. `SignalFeedbackRuntime.Reply` has two
//! fields and neither is a digest; there is no secret, run seed, commitment or target
//! it could carry. What Lean PROVES, because it is not visible in a type, is that the
//! served BYTES separate no more than the classification does:
//!
//! * `reply_bytes_are_a_function_of_the_feedback_alone` — two requests whose feedback
//!   agrees serve byte-identical replies, however much else differs.
//! * `served_transcript_cannot_separate_feedback_equivalent_targets` — over a whole
//!   session, two targets consistent with the guesses played serve identical bytes, so
//!   a reader of an unsolved transcript is exactly where the player is and no further.
//! * `SignalTriangulation.one_round_never_determines_the_target` — and that position is
//!   never "solved" after one round, for any opening, so the invariance is not vacuous.
//!
//! # The commitment is an INPUT
//!
//! The request carries the node's installed slot commitment and Lean refuses unless
//! `HiddenInstance.commit secret slot` reproduces it
//! (`signalFeedbackFFI_refuses_an_unopened_commitment`). A node whose secret does not
//! open what the curator published serves nothing rather than a classification against
//! an instance nobody committed to in advance. It is not echoed back: the reply is the
//! classification, and a public value in it would still be a value that is not the
//! classification.
//!
//! ⚠ `SignalFeedbackRuntime.decodeRequest` is `canonicalDecode parseRequestJson
//! Request.toJson` — Lean re-encodes what it parsed and compares BYTES. The request key
//! order at [`SIGNAL_FEEDBACK_INPUT_FORMAT`] is therefore load-bearing, not cosmetic:
//! any other order is refused with the `""` sentinel, which every caller sees as an
//! ordinary rejection. Callers must build this wire from a type whose field order is
//! fixed, never from a map whose order depends on a cargo feature.

use crate::{ensure_lean_init, lean_init_once};

/// Host-transport ceiling. The feedback wire is a fixed handful of digests plus one
/// three-band code; this is a malformed-caller guard, not a semantic bound.
pub const MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES: usize = 64 * 1024;

/// The canonical request format this seam sends to Lean.
///
/// ```text
/// {"format":"POA-SIGNAL-FEEDBACK-1",
///  "slot":<u64>,
///  "secret":"<64 lowercase hex>",
///  "mission_id":<u64>,
///  "epoch":<u64>,
///  "federation_id":"<64 lowercase hex>",
///  "content_session":"<64 lowercase hex>",
///  "player_key":"<64 lowercase hex>",
///  "commitment":"<64 lowercase hex>",
///  "guess":{"low":<0..5>,"mid":<0..5>,"high":<0..5>}}
/// ```
///
/// The first eight fields are byte-identical to `POA-SLOT-DERIVE-1`'s, deliberately:
/// `SignalFeedbackRuntime.request_derives_the_judged_instance` is `rfl` against
/// `SlotDeriveRuntime.derive`, which is what makes a served classification a
/// classification about the instance that will SETTLE.
pub const SIGNAL_FEEDBACK_INPUT_FORMAT: &str = "POA-SIGNAL-FEEDBACK-1";

/// The canonical reply format.
///
/// ```text
/// {"format":"POA-SIGNAL-FEEDBACK-OUT-1","exact":<0..3>,"present":<0..3>}
/// ```
///
/// `exact` is LOCKED and `present` is DRIFT. They are
/// `SignalTriangulation.Feedback`'s own field names rather than the UI's rendering, so
/// there is one spelling of each number between the rule and the browser.
pub const SIGNAL_FEEDBACK_OUTPUT_FORMAT: &str = "POA-SIGNAL-FEEDBACK-OUT-1";

/// Whether the linked archive exports the oracle and the Lean runtime came up.
///
/// `false` means judged sessions cannot be served at all. It never means "use a Rust
/// fallback"; there is none.
pub fn poa_signal_feedback_available() -> bool {
    ffi_feedback::poa_signal_feedback_present() && lean_init_once().is_ok()
}

/// Classify one guess. Returns Lean's exact canonical reply, or `Ok(None)` for Lean's
/// empty refusal sentinel, or `Err` for transport/archive faults.
///
/// The refusal sentinel covers both a non-canonical wire and a secret that does not
/// open the stated commitment. Both are node-side faults from the player's side of the
/// wire, and neither may be reported as a classification.
pub fn classify_poa_signal_guess(wire: &str) -> Result<Option<String>, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA Signal feedback wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_signal_feedback input exceeds \
             {MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    let reply = ffi_feedback::lean_poa_signal_feedback(wire)?;
    Ok(if reply.is_empty() { None } else { Some(reply) })
}

#[cfg(all(lean_lib_present, dregg_poa_signal_feedback_present))]
mod ffi_feedback {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_signal_feedback_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn poa_signal_feedback_present() -> bool {
        true
    }

    pub fn lean_poa_signal_feedback(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire)
            .map_err(|e| format!("PoA Signal feedback wire has interior NUL: {e}"))?;
        let mut cap = MAX_BUFFER_CAP.min(4096);
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_signal_feedback_str(c_in.as_ptr(), buf.as_mut_ptr().cast::<c_char>(), cap)
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_signal_feedback_str refused an unusable or over-limit transport"
                        .into(),
                );
            }
            if full > MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES {
                return Err(format!(
                    "dregg_poa_signal_feedback output exceeds \
                     {MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES}-byte transport ceiling"
                ));
            }
            if full < cap {
                return String::from_utf8(buf[..full].to_vec())
                    .map_err(|e| format!("PoA Signal feedback result is not UTF-8: {e}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "dregg_poa_signal_feedback output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_signal_feedback_present)))]
mod ffi_feedback {
    pub fn poa_signal_feedback_present() -> bool {
        false
    }

    pub fn lean_poa_signal_feedback(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_signal_feedback not exported by the linked archive; a judged \
             Signal session cannot be classified and every session route refuses. There \
             is no Rust classification to fall back to: the rule is \
             `SignalTriangulation.feedback`, the same function that decides whether a \
             transcript settles, and a second copy of it in Rust would hand players a \
             different game than the one that settles"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Absent the export the seam refuses; it never returns a classification.
    #[cfg(not(all(lean_lib_present, dregg_poa_signal_feedback_present)))]
    #[test]
    fn absent_export_refuses_rather_than_classifying() {
        assert!(!poa_signal_feedback_available());
        let error = classify_poa_signal_guess("{}").unwrap_err();
        assert!(
            error.contains("not exported by the linked archive"),
            "unexpected refusal text: {error}"
        );
    }

    #[test]
    fn interior_nul_is_a_transport_fault() {
        let error = classify_poa_signal_guess("a\0b").unwrap_err();
        assert!(error.contains("interior NUL"), "unexpected error: {error}");
    }

    #[test]
    fn oversize_wire_is_refused_before_the_call() {
        let wire = "x".repeat(MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES + 1);
        let error = classify_poa_signal_guess(&wire).unwrap_err();
        assert!(
            error.contains("transport ceiling"),
            "unexpected error: {error}"
        );
    }
}
