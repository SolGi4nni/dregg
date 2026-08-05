//! The Path of Angels per-run instance derivation boundary.
//!
//! # Why this exists
//!
//! `Judged.admissionChecks` requires two facts the node cannot assert, only supply:
//!
//! * `active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot`
//! * `active.runSeed = HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`
//!
//! The judge RE-DERIVES both and refuses on mismatch. That is only a check if the
//! node derived them independently — a node that shipped `UNBOUND_RUN_SEED` and let
//! the judge fill it in would be asking the judge to compute the answer rather than
//! to verify that the node served the committed one.
//!
//! So the node must derive. `HiddenInstance.commit` and `HiddenInstance.runSeedFor`
//! are a Poseidon2-BabyBear-w16 sponge with its own padding, lane-aliasing rejection
//! (`laneByte?`), domain tags (`POAC` / `POAD`) and squeeze count. Re-typing any of
//! that in Rust would be exactly the twin this repo spends its time deleting, and it
//! would be a twin of a *soundness* function: a Rust/Lean disagreement of one byte
//! silently turns every scored run into a refusal, or worse, agrees on a different
//! instance than the one the player was served.
//!
//! Rust therefore computes nothing here. It carries bytes to Lean and back.
//!
//! # STATUS: closed
//!
//! `Dregg2.Games.PathOfAngels.SlotDeriveRuntime.slotDeriveFFI` is
//! `@[export dregg_poa_signal_slot_derive]` and in the archive, and the symbol is on
//! `REQUIRED_DECISION_EXPORTS`, so a `--release` / `DREGG_REQUIRE_LEAN=1` build now
//! REFUSES to link an archive without it. This seam compiles to its live arm.
//!
//! (It shipped ahead of the export, compiling to the refusing arm, so that the gap
//! was a named refusal rather than a Rust sponge written to avoid one.)
//!
//! ⚠ `SlotDeriveRuntime.decodeRequest` is `canonicalDecode parseRequestJson
//! Request.toJson` — Lean re-encodes what it parsed and compares BYTES. The request
//! key order at [`SLOT_DERIVE_INPUT_FORMAT`] is therefore load-bearing, not
//! cosmetic: any other order is refused with the `""` sentinel, which every caller
//! sees as an ordinary rejection. Callers must build this wire from a type whose
//! field order is fixed, never from a map whose order depends on a cargo feature.

use crate::{ensure_lean_init, lean_init_once};

/// Host-transport ceiling. The derivation wire is a fixed handful of digests; this
/// is a malformed-caller guard, not a semantic bound.
pub const MAX_POA_SLOT_DERIVE_WIRE_BYTES: usize = 64 * 1024;

/// The canonical request format this seam sends to Lean.
///
/// ```text
/// {"format":"POA-SLOT-DERIVE-1",
///  "slot":<u64>,
///  "secret":"<64 lowercase hex>",
///  "mission_id":<u64>,
///  "epoch":<u64>,
///  "federation_id":"<64 lowercase hex>",
///  "content_session":"<64 lowercase hex>",
///  "player_key":"<64 lowercase hex>"}
/// ```
///
/// `mission_id`, `epoch`, `federation_id` and `content_session` are exactly
/// `HiddenInstance.MissionContext` — the projection that deliberately EXCLUDES
/// `runSeed`, so the derivation is visibly not a cycle
/// (`HiddenInstance.context_ignores_the_run_seed`).
pub const SLOT_DERIVE_INPUT_FORMAT: &str = "POA-SLOT-DERIVE-1";

/// The canonical reply format.
///
/// ```text
/// {"format":"POA-SLOT-DERIVE-OUT-1",
///  "commitment":"<64 lowercase hex>",
///  "run_seed":"<64 lowercase hex>",
///  "target":{"low":<0..5>,"mid":<0..5>,"high":<0..5>}}
/// ```
///
/// `commitment` is `HiddenInstance.commit secret slot`; `run_seed` is
/// `HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`; `target` is
/// `SignalTriangulation.targetFromSeed run_seed`, which the node needs because
/// `SignalTriangulation.Config` carries `target_eq : target = targetFromSeed
/// mission.runSeed` as a proof field — a config whose target does not match its
/// seed does not decode at all.
///
/// All three are returned together so the node makes ONE call and holds ONE copy of
/// the derivation. `""` is the fail-closed refusal sentinel, as in every other PoA
/// export.
pub const SLOT_DERIVE_OUTPUT_FORMAT: &str = "POA-SLOT-DERIVE-OUT-1";

/// Whether the linked archive exports the derivation and the Lean runtime came up.
///
/// `false` means scored Signal runs cannot be prepared at all. It never means "use a
/// Rust fallback"; there is none.
pub fn poa_slot_derive_available() -> bool {
    ffi_slot::poa_slot_derive_present() && lean_init_once().is_ok()
}

/// Derive one run instance. Returns Lean's exact canonical reply, or `Ok(None)` for
/// Lean's empty refusal sentinel, or `Err` for transport/archive faults.
pub fn derive_poa_slot_instance(wire: &str) -> Result<Option<String>, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA slot-derive wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_SLOT_DERIVE_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_signal_slot_derive input exceeds \
             {MAX_POA_SLOT_DERIVE_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    let reply = ffi_slot::lean_poa_slot_derive(wire)?;
    Ok(if reply.is_empty() { None } else { Some(reply) })
}

#[cfg(all(lean_lib_present, dregg_poa_signal_slot_derive_present))]
mod ffi_slot {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_SLOT_DERIVE_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_SLOT_DERIVE_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_signal_slot_derive_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn poa_slot_derive_present() -> bool {
        true
    }

    pub fn lean_poa_slot_derive(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire)
            .map_err(|e| format!("PoA slot-derive wire has interior NUL: {e}"))?;
        let mut cap = MAX_BUFFER_CAP.min(4096);
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_signal_slot_derive_str(
                    c_in.as_ptr(),
                    buf.as_mut_ptr().cast::<c_char>(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_signal_slot_derive_str refused an unusable or over-limit transport"
                        .into(),
                );
            }
            if full > MAX_POA_SLOT_DERIVE_WIRE_BYTES {
                return Err(format!(
                    "dregg_poa_signal_slot_derive output exceeds \
                     {MAX_POA_SLOT_DERIVE_WIRE_BYTES}-byte transport ceiling"
                ));
            }
            if full < cap {
                return String::from_utf8(buf[..full].to_vec())
                    .map_err(|e| format!("PoA slot-derive result is not UTF-8: {e}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "dregg_poa_signal_slot_derive output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_signal_slot_derive_present)))]
mod ffi_slot {
    pub fn poa_slot_derive_present() -> bool {
        false
    }

    pub fn lean_poa_slot_derive(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_signal_slot_derive not exported by the linked archive; \
             the per-run instance cannot be derived and every scored Path of Angels \
             Signal run refuses. There is no Rust derivation to fall back to: \
             `HiddenInstance.commit`/`runSeedFor` are a Poseidon2-BabyBear sponge whose \
             Rust twin would be a second, unproven copy of a soundness function"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Absent the export the seam refuses; it never returns a derived value.
    #[cfg(not(all(lean_lib_present, dregg_poa_signal_slot_derive_present)))]
    #[test]
    fn absent_export_refuses_rather_than_deriving() {
        assert!(!poa_slot_derive_available());
        let error = derive_poa_slot_instance("{}").unwrap_err();
        assert!(
            error.contains("not exported by the linked archive"),
            "unexpected refusal text: {error}"
        );
    }

    #[test]
    fn interior_nul_is_a_transport_fault() {
        let error = derive_poa_slot_instance("a\0b").unwrap_err();
        assert!(error.contains("interior NUL"), "unexpected error: {error}");
    }

    #[test]
    fn oversize_wire_is_refused_before_the_call() {
        let wire = "x".repeat(MAX_POA_SLOT_DERIVE_WIRE_BYTES + 1);
        let error = derive_poa_slot_instance(&wire).unwrap_err();
        assert!(
            error.contains("transport ceiling"),
            "unexpected error: {error}"
        );
    }
}
