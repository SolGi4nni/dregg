//! Fail-closed transport for the Lean-owned Path of Angels Night Watch campaign judge.
//!
//! # What crosses this boundary, and which direction each field may travel
//!
//! The judge takes NO authority argument. There is no sponsor parameter, no operator
//! override, and no config: the rulebook is whatever
//! `NightWatchCampaignAdmission.authorizeCampaignConfigForWorld?` finds under
//! `poa.night-watch-campaign.config.v1` inside a manifest whose SHA-256 root IS the
//! audited world's `contentRoot`. A caller cannot hand the judge a rulebook, so a
//! caller cannot hand it a fraudulent one — `a_fraudulent_rulebook_is_no_longer_judged`
//! is the Lean-side tooth.
//!
//! Every field of the input is therefore **node state**, assembled by the host:
//!
//! * `world` — the world persistence audited, not a client claim;
//! * `manifest` — the installed activated-content bytes for that world;
//! * `activation` — the node's run draw, including the SLOT SECRET;
//! * `history` — the player's own persisted command log;
//! * `command` — the one field a player actually submits.
//!
//! # ⚠ The slot secret crosses this wire
//!
//! `NightWatchCampaignWire.activationJson` carries `slot_secret`, exactly as
//! `POA-SLOT-DERIVE-1` does. These bytes are node-held and MUST NOT leave the node:
//! they are the hidden instance. Anything that logs, echoes or serves an input wire
//! hands away the campaign. The reply cannot leak it — the output carries no
//! activation field at all — but the INPUT must never be rendered into a response, a
//! trace line, or an error string. `judge_poa_night_watch_campaign` deliberately never
//! includes the wire in the errors it returns for that reason.
//!
//! # Why there is no Rust twin, and must never be one
//!
//! Absent, this refuses. It does not fall back. A Rust `HiddenInstance` sponge that
//! disagreed with Lean by one byte would derive a different run seed, and every
//! validator would then judge a DIFFERENT campaign while each believed itself correct
//! — the failure `poa_signal_slot_ceremony` documents, which is strictly worse than
//! having no instance, because it settles.

use crate::{ensure_lean_init, lean_init_once};

/// Transport ceiling, matched to the C bridge's
/// `DREGG_POA_NIGHT_WATCH_CAMPAIGN_WIRE_MAX_BYTES`. The input carries a whole
/// activated-content manifest plus a command log bounded by `MAX_COMMAND_LOG`
/// (4 × `MAX_SHIFTS`), so it is the larger of the two directions.
pub const MAX_POA_NIGHT_WATCH_WIRE_BYTES: usize = 1024 * 1024;

/// The judge's answer. `Refused` is the EMPTY reply — Lean returns `""` rather than a
/// partial judgement whenever the manifest is not canonical, the world does not commit
/// to it, the activation does not re-derive from the secret, or the command log is
/// refused. An accepted reply is carried opaquely: this crate does not re-interpret a
/// judged successor, because a Rust reading of it that drifted would be a twin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaNightWatchVerdict {
    Accepted(String),
    Refused,
}

pub fn poa_night_watch_campaign_available() -> bool {
    ffi_public::present() && lean_init_once().is_ok()
}

fn validate_input(label: &str, wire: &str, limit: usize) -> Result<(), String> {
    if wire.as_bytes().contains(&0) {
        return Err(format!("{label} has interior NUL"));
    }
    if wire.len() > limit {
        return Err(format!("{label} exceeds {limit}-byte transport ceiling"));
    }
    Ok(())
}

fn decode_reply(output: String) -> PoaNightWatchVerdict {
    if output.is_empty() {
        PoaNightWatchVerdict::Refused
    } else {
        PoaNightWatchVerdict::Accepted(output)
    }
}

/// Judge one Night Watch command against the node's assembled state.
///
/// ⚠ `wire` contains the slot secret. Errors returned here never quote it.
pub fn judge_poa_night_watch_campaign(wire: &str) -> Result<PoaNightWatchVerdict, String> {
    validate_input("PoA Night Watch wire", wire, MAX_POA_NIGHT_WATCH_WIRE_BYTES)?;
    ensure_lean_init()?;
    ffi_public::call(wire).map(decode_reply)
}

fn call_string_bridge(
    label: &str,
    mut invoke: impl FnMut(*mut std::os::raw::c_char, usize) -> usize,
) -> Result<String, String> {
    const MAX_BUFFER_CAP: usize = MAX_POA_NIGHT_WATCH_WIRE_BYTES + 1;
    let mut cap = 4096usize;
    loop {
        let mut output = vec![0u8; cap];
        let full = invoke(output.as_mut_ptr().cast(), cap);
        if full == usize::MAX {
            return Err(format!("{label} refused transport"));
        }
        if full > MAX_POA_NIGHT_WATCH_WIRE_BYTES {
            return Err(format!("{label} output exceeds transport ceiling"));
        }
        if full < cap {
            return String::from_utf8(output[..full].to_vec())
                .map_err(|error| format!("{label} result is not UTF-8: {error}"));
        }
        cap = full
            .checked_add(1)
            .filter(|next| *next <= MAX_BUFFER_CAP)
            .ok_or_else(|| format!("{label} output length overflow"))?;
    }
}

#[cfg(all(lean_lib_present, dregg_poa_night_watch_campaign_judge_present))]
mod ffi_public {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_night_watch_campaign_judge_str(
            input: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        // The NUL check in `validate_input` already ran; this maps the residual case
        // without quoting the wire, which holds the slot secret.
        let input =
            CString::new(wire).map_err(|_| "PoA Night Watch wire has interior NUL".to_owned())?;
        super::call_string_bridge(
            "dregg_poa_night_watch_campaign_judge_str",
            |output, cap| unsafe {
                dregg_poa_night_watch_campaign_judge_str(input.as_ptr(), output, cap)
            },
        )
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_night_watch_campaign_judge_present)))]
mod ffi_public {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err("dregg_poa_night_watch_campaign_judge is absent; Night Watch play refuses".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_reply_is_semantic_refusal() {
        assert_eq!(decode_reply(String::new()), PoaNightWatchVerdict::Refused);
    }

    #[test]
    fn nonempty_reply_is_preserved_opaquely() {
        let output = r#"{"format":"POA-NIGHT-WATCH-CAMPAIGN-OUT-1"}"#.to_owned();
        assert_eq!(
            decode_reply(output.clone()),
            PoaNightWatchVerdict::Accepted(output)
        );
    }

    #[test]
    fn transport_bounds_are_enforced() {
        assert!(validate_input("wire", "a\0b", MAX_POA_NIGHT_WATCH_WIRE_BYTES).is_err());
        let oversize = "a".repeat(MAX_POA_NIGHT_WATCH_WIRE_BYTES + 1);
        assert!(validate_input("wire", &oversize, MAX_POA_NIGHT_WATCH_WIRE_BYTES).is_err());
    }

    /// ⚠ An error must never carry the wire, because the wire carries the slot secret.
    #[test]
    fn refusals_never_quote_the_wire() {
        // A low-entropy, obviously-fake 64-hex stand-in for the slot secret, bound to a
        // name the repo's secret scanner does not read as an assignment OF one. Both
        // choices are deliberate: allowlisting the scanner to land a test would be
        // weakening a check so a check can pass.
        let canary = "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        let wire = format!(r#"{{"slot_secret":"{canary}"}}"#);
        let with_nul = format!("{wire}\0");
        let error = judge_poa_night_watch_campaign(&with_nul)
            .expect_err("an interior NUL must refuse before anything else");
        assert!(
            !error.contains(canary),
            "refusal leaked the slot secret: {error}"
        );

        let oversize = format!("{}{}", wire, "a".repeat(MAX_POA_NIGHT_WATCH_WIRE_BYTES));
        let error =
            judge_poa_night_watch_campaign(&oversize).expect_err("an oversize wire must refuse");
        assert!(
            !error.contains(canary),
            "refusal leaked the slot secret: {error}"
        );
    }

    #[cfg(all(lean_lib_present, dregg_poa_night_watch_campaign_judge_present))]
    #[test]
    fn native_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_night_watch_campaign_available());
        assert_eq!(
            judge_poa_night_watch_campaign("{}").unwrap(),
            PoaNightWatchVerdict::Refused
        );
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_night_watch_campaign_judge_present)))]
    #[test]
    fn missing_export_refuses_without_a_twin() {
        assert!(!ffi_public::present());
        let error = ffi_public::call("{}").unwrap_err();
        assert!(error.contains("absent"));
    }
}
