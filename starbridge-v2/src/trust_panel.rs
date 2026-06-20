//! THE TRUST PANEL (human-layer M1) — the human's view of their own authority.
//!
//! `docs/deos/HUMAN-LAYER.md` §3, Milestone 1: a person *is* a sovereign
//! identity cell, and the load-bearing guarantee is *you cannot lose your own
//! OS.* This panel is the WHO-I-AM face plus the recovery UX, projected
//! entirely off REAL protocol state — the same gpui-free, `cargo test`-proven
//! shape as the other inspector lanes (`presentable.rs`, `cipherclerk.rs`). No
//! gpui type crosses this boundary; a thin gpui layer maps each
//! [`Presentation`] body to a widget.
//!
//! Two faces, both real projections:
//!
//!   * **WHO I AM** — the identity cell as a living card: my devices (the
//!     current key set, each a friendly speaker), my recovery guardians (the
//!     council faces, with the threshold drawn as "any K of these N"), and the
//!     key-event log (the rotation timeline — the KERI KEL shape, an auditable
//!     history of every rotation). Built from the genuine
//!     [`dregg_sdk::identity::inspect_identity`] decode + the
//!     [`CouncilCharter`].
//!
//!   * **RECOVERY** — the "ask your guardians" flow: set guardians (the council
//!     charter), then a progress gauge of arriving guardian approvals against
//!     the threshold, and the cooling window shown as a *safety feature*
//!     ("settling — if this wasn't you, tap here") rather than a delay. The
//!     quorum math mirrors exactly what the executor's `ThresholdSigVerifier`
//!     enforces (weighted K-of-N, fail-closed below threshold); this panel is
//!     the human-readable shadow of that verdict, never a parallel authority.
//!
//! Reuses `reflect.rs`'s [`Inspectable`]/[`Field`] and `presentable.rs`'s
//! [`Presentation`]/[`TimelineView`]/[`GaugeView`] verbatim — no parallel
//! object model.

use dregg_sdk::identity::{IdentityCharter, IdentityState, IdentityStatus, inspect_identity};
use dregg_sdk::polis::CouncilCharter;

use crate::presentable::{
    GaugeView, Presentation, PresentationBody, PresentationKind, TimelineEvent, TimelineView,
};
use crate::reflect::{Field, FieldValue, Inspectable, ObjectKind, short_hex};

// ===========================================================================
// §1 — the model: a friendly device, a guardian face, a recovery-in-progress
// ===========================================================================

/// One **device** — a speaker for the identity (a member of the current key
/// set). Devices are sub-identities, not separate principals: my laptop and my
/// phone both speak for me because their public keys are members of the set
/// committed in `CURRENT_KEYS_COMMIT_SLOT`. The icon is a wonder-first glyph; an
/// adept reads the key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Device {
    /// A friendly name ("laptop", "phone", "paper backup").
    pub name: String,
    /// The device's 32-byte signing public key (a member of the current set).
    pub public_key: [u8; 32],
    /// A wonder-first glyph (a child reads the glyph; an adept reads the key).
    pub glyph: &'static str,
}

impl Device {
    /// A named device with the laptop glyph (the default speaker).
    pub fn laptop(name: impl Into<String>, public_key: [u8; 32]) -> Self {
        Device { name: name.into(), public_key, glyph: "💻" }
    }
    /// A phone device.
    pub fn phone(name: impl Into<String>, public_key: [u8; 32]) -> Self {
        Device { name: name.into(), public_key, glyph: "📱" }
    }
    /// A paper / hardware backup speaker.
    pub fn paper(name: impl Into<String>, public_key: [u8; 32]) -> Self {
        Device { name: name.into(), public_key, glyph: "📄" }
    }
}

/// One **guardian face** — a member of the recovery council. A guardian holds a
/// threshold-sig key; below the threshold they have nothing, so each guardian is
/// chosen, weighted, and visible. The face is the council member's cell id; the
/// weight defaults to 1 (the unweighted council).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuardianFace {
    /// A friendly name ("Spouse", "Best friend", "Paper backup").
    pub name: String,
    /// The guardian's cell id (the council member).
    pub cell: [u8; 32],
    /// The guardian's weight toward the quorum (default 1).
    pub weight: u64,
}

impl GuardianFace {
    /// A unit-weight guardian named `name` at council member cell `cell`.
    pub fn new(name: impl Into<String>, cell: [u8; 32]) -> Self {
        GuardianFace { name: name.into(), cell, weight: 1 }
    }
    /// A heavy guardian (e.g. a paper backup *you* hold counts for more).
    pub fn weighted(name: impl Into<String>, cell: [u8; 32], weight: u64) -> Self {
        GuardianFace { name: name.into(), cell, weight }
    }
}

/// A **recovery-in-progress** — the human-readable shadow of the guardian
/// quorum the executor's `ThresholdSigVerifier` will check. It tracks which
/// guardians have approved (signed the recovery message) against the council's
/// threshold, plus the cooling-window status. This is *not* a parallel
/// authority — the executor decides admission; this is the "ask your guardians"
/// progress bar a person watches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveryProgress {
    /// The guardians who have approved so far (by index into the council).
    pub approved: Vec<usize>,
    /// The weighted threshold the quorum must meet (the council's `threshold`).
    pub threshold: u64,
    /// The total council size (the N in K-of-N).
    pub guardian_count: usize,
    /// The per-guardian weights (parallel to the council members).
    pub weights: Vec<u64>,
    /// The cooling window in blocks (the recovery settles visibly for this long).
    pub cooling_blocks: u64,
    /// Blocks elapsed since the recovery rotation landed (`None` = not yet
    /// landed — still collecting approvals).
    pub cooling_elapsed: Option<u64>,
}

impl RecoveryProgress {
    /// A fresh recovery against `council`: no approvals yet, the council's
    /// threshold, unit weights, and the identity charter's cooling window.
    pub fn begin(council: &CouncilCharter, cooling_blocks: u64) -> Self {
        RecoveryProgress {
            approved: Vec::new(),
            threshold: council.threshold,
            guardian_count: council.members.len(),
            weights: vec![1; council.members.len()],
            cooling_blocks,
            cooling_elapsed: None,
        }
    }

    /// Record guardian `index`'s approval (idempotent — a guardian's signature
    /// counts once).
    pub fn approve(&mut self, index: usize) {
        if index < self.guardian_count && !self.approved.contains(&index) {
            self.approved.push(index);
        }
    }

    /// The total weight that has approved so far (the quorum's `agg_weight`).
    pub fn approved_weight(&self) -> u64 {
        self.approved
            .iter()
            .map(|&i| self.weights.get(i).copied().unwrap_or(1))
            .sum()
    }

    /// Is the weighted quorum met? Mirrors EXACTLY the executor's floor: the
    /// aggregate must carry at least `threshold` weight, else it fails closed.
    /// This is the human-readable shadow of `ThresholdSigVerifier`'s admission;
    /// the executor is the backstop, this is the progress read.
    pub fn quorum_met(&self) -> bool {
        self.approved_weight() >= self.threshold
    }

    /// Has the cooling window cleared (the recovery is final, not just signed)?
    /// `false` until the rotation has landed AND the window has fully elapsed —
    /// the safety pause during which a panic-veto is still possible.
    pub fn cooling_cleared(&self) -> bool {
        matches!(self.cooling_elapsed, Some(e) if e >= self.cooling_blocks)
    }

    /// A plain-language status line — the "ask your guardians" headline.
    pub fn headline(&self) -> String {
        if !self.quorum_met() {
            format!(
                "Asking your guardians — {} of {} weight in (need {})",
                self.approved_weight(),
                self.weights.iter().sum::<u64>(),
                self.threshold
            )
        } else if !self.cooling_cleared() {
            let elapsed = self.cooling_elapsed.unwrap_or(0);
            format!(
                "Quorum reached — settling ({}/{} blocks). If this wasn't you, tap to stop it.",
                elapsed, self.cooling_blocks
            )
        } else {
            "Welcome back — your identity is recovered.".to_string()
        }
    }
}

// ===========================================================================
// §2 — the WHO-I-AM identity card + the recovery face, as Presentations
// ===========================================================================

/// The whole human-layer trust surface for one identity: the decoded key state,
/// the devices that speak for it, the guardian council, and (optionally) a
/// recovery flow underway. Built from REAL `inspect_identity` + the charter.
#[derive(Clone, Debug)]
pub struct TrustPanel {
    /// The identity's friendly name (the person, "ember").
    pub name: String,
    /// The decoded live key state (state, key commitments, last-rotated, council
    /// match) — the genuine `inspect_identity` projection.
    pub status: IdentityStatus,
    /// The devices that currently speak for this identity (the current key set).
    pub devices: Vec<Device>,
    /// The recovery guardians (the council faces) + the threshold.
    pub guardians: Vec<GuardianFace>,
    /// The recovery council's K-of-N threshold (drawn as "any K of these N").
    pub threshold: u64,
    /// The key-event log — the rotation history (KERI KEL), in commit order.
    pub kel: Vec<KeyEvent>,
    /// A recovery flow underway, if any (the "ask your guardians" progress).
    pub recovery: Option<RecoveryProgress>,
}

/// One **key event** in the KEL — a rotation (or the inception). The receipt
/// stream over the two key registers IS this log; here we carry the
/// plain-language row a person reads ("you added your phone · block 1050").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyEvent {
    /// The block height the event landed at (the timeline ordering key).
    pub at: u64,
    /// A plain-language description ("inception", "added your phone", "recovered
    /// with your guardians").
    pub description: String,
    /// The current-keys commitment installed by this event (navigable).
    pub installed_commit: [u8; 32],
}

impl TrustPanel {
    /// Build the panel from a live identity cell's fields + its charter.
    ///
    /// `fields` is the 16-slot cell state (the node read / receipt post-state);
    /// `charter` carries the council (guardians) + cooling window. `devices` and
    /// `kel` are the friendly names the cipherclerk holds for the key set and
    /// the rotation history (the commitments themselves come from the cell).
    pub fn from_cell(
        name: impl Into<String>,
        charter: &IdentityCharter,
        fields: &[[u8; 32]; 16],
        devices: Vec<Device>,
        kel: Vec<KeyEvent>,
    ) -> Self {
        let status = inspect_identity(charter, fields);
        let guardians = charter
            .council
            .members
            .iter()
            .enumerate()
            .map(|(i, m)| GuardianFace::new(format!("Guardian {}", i + 1), *m.as_bytes()))
            .collect();
        TrustPanel {
            name: name.into(),
            status,
            devices,
            guardians,
            threshold: charter.council.threshold,
            kel,
            recovery: None,
        }
    }

    /// Attach a recovery-in-progress (the "ask your guardians" flow).
    pub fn with_recovery(mut self, recovery: RecoveryProgress) -> Self {
        self.recovery = Some(recovery);
        self
    }

    /// A representative WHO-I-AM panel for the cockpit's TRUST tab — a 3-of-5
    /// guardian identity (2 devices, a short KEL) with a recovery-in-progress so the
    /// "ask your guardians" gauge shows. Built off the SAME real `inspect_identity`
    /// decode shape `from_cell` uses (not a parallel mock) — the standing surface for
    /// the human-layer recovery weld until an on-ledger identity cell is wired into
    /// the live image (HORIZONLOG). The cooling window is shown as the safety feature
    /// it is.
    pub fn demo() -> Self {
        use dregg_cell::CellId;
        use dregg_sdk::identity::{
            key_set_commitment, next_keys_digest, COUNCIL_COMMIT_SLOT, CURRENT_KEYS_COMMIT_SLOT,
            LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT, STATE_ACTIVE, STATE_SLOT,
        };
        fn be_u64(v: u64) -> [u8; 32] {
            let mut f = [0u8; 32];
            f[24..32].copy_from_slice(&v.to_be_bytes());
            f
        }
        let council =
            CouncilCharter::new((1u8..=5).map(|i| CellId::from_bytes([i; 32])).collect(), 3);
        let charter = IdentityCharter {
            council: council.clone(),
            cooling_period: 50,
        };
        let g0 = vec![[0x10u8; 32], [0x11u8; 32]];
        let g1 = vec![[0x20u8; 32], [0x21u8; 32]];
        let mut fields = [[0u8; 32]; 16];
        fields[STATE_SLOT as usize] = be_u64(STATE_ACTIVE);
        fields[CURRENT_KEYS_COMMIT_SLOT as usize] = key_set_commitment(&g0);
        fields[NEXT_KEYS_DIGEST_SLOT as usize] = next_keys_digest(&key_set_commitment(&g1));
        fields[COUNCIL_COMMIT_SLOT as usize] = council.members_commitment();
        fields[LAST_ROTATED_AT_SLOT as usize] = be_u64(1_000);
        let devices = vec![
            Device::laptop("laptop", g0[0]),
            Device::phone("phone", g0[1]),
        ];
        let kel = vec![
            KeyEvent {
                at: 0,
                description: "Inception — you were born".to_string(),
                installed_commit: key_set_commitment(&g0),
            },
            KeyEvent {
                at: 1_000,
                description: "You added your phone".to_string(),
                installed_commit: key_set_commitment(&g0),
            },
        ];
        // A recovery underway (2-of-5 approved) so the "ask your guardians" gauge
        // shows the quorum climb + the cooling window.
        let mut recovery = RecoveryProgress::begin(&council, 50);
        recovery.approve(0);
        recovery.approve(1);
        TrustPanel::from_cell("ember", &charter, &fields, devices, kel).with_recovery(recovery)
    }

    /// A one-line legible summary ("ember · Active · 2 devices · 3-of-5 guardians").
    pub fn summary(&self) -> String {
        format!(
            "{} · {} · {} device(s) · {}-of-{} guardians",
            self.name,
            state_word(&self.status.state),
            self.devices.len(),
            self.threshold,
            self.guardians.len()
        )
    }

    // --- WHO I AM: the identity card (RawFields) ---------------------------

    /// The identity card as the mandatory RawFields [`Inspectable`]: the decoded
    /// key state, the devices, and the guardian threshold, in human terms.
    pub fn identity_card(&self) -> Inspectable {
        let mut fields = vec![
            Field::text("state", state_word(&self.status.state).to_string()),
            Field::count("devices", self.devices.len() as u64),
            Field::text(
                "recovery",
                format!("any {} of {} guardians", self.threshold, self.guardians.len()),
            ),
            Field::boolean("council_pinned", self.status.council_commit_matches),
            Field::hash("current_keys_commit", self.status.current_keys_commit),
            Field::hash("next_keys_digest", self.status.next_keys_digest),
            Field::count("last_rotated_at", self.status.last_rotated_at),
        ];
        for d in &self.devices {
            fields.push(Field {
                key: format!("device · {}", d.name),
                value: FieldValue::Text(format!("{} {}", d.glyph, short_hex(&d.public_key))),
            });
        }
        for g in &self.guardians {
            fields.push(Field {
                key: format!("guardian · {}", g.name),
                value: FieldValue::Text(format!(
                    "🛡 {} (weight {})",
                    short_hex(&g.cell),
                    g.weight
                )),
            });
        }
        Inspectable {
            kind: ObjectKind::Capability,
            title: format!("Who I am — {}", self.name),
            subtitle: self.summary(),
            fields,
        }
    }

    /// The key-event log as a [`TimelineView`] (the KERI KEL — the rotation
    /// history a person can audit, plain-language).
    pub fn kel_timeline(&self) -> TimelineView {
        let events = self
            .kel
            .iter()
            .map(|e| TimelineEvent {
                at: e.at,
                label: format!("{} · block {}", e.description, e.at),
                hash: Some(e.installed_commit),
            })
            .collect();
        TimelineView { events }
    }

    /// The recovery progress as a [`GaugeView`]: the approved weight against the
    /// threshold, with the guardian count as rungs. `None` if no recovery is
    /// underway.
    pub fn recovery_gauge(&self) -> Option<GaugeView> {
        let r = self.recovery.as_ref()?;
        Some(GaugeView {
            label: r.headline(),
            value: r.approved_weight() as i64,
            ceiling: Some(r.threshold as i64),
            rungs: (0..r.guardian_count)
                .map(|i| {
                    let signed = r.approved.contains(&i);
                    let name = self
                        .guardians
                        .get(i)
                        .map(|g| g.name.as_str())
                        .unwrap_or("guardian");
                    format!("{} {}", if signed { "✅" } else { "⏳" }, name)
                })
                .collect(),
        })
    }

    /// THE PRESENTATION SET. The trust panel offers the WHO-I-AM card
    /// (RawFields, the mandatory floor), the KEL (Provenance timeline), and —
    /// when a recovery is underway — the "ask your guardians" gauge
    /// (DomainVisual). Pure data; the gpui layer renders each body.
    pub fn present(&self) -> Vec<Presentation> {
        let card = self.identity_card();
        let mut out = vec![Presentation {
            kind: PresentationKind::RawFields,
            label: "Who I Am".to_string(),
            search_text: PresentationBody::Fields(card.clone()).search_text(),
            body: PresentationBody::Fields(card),
        }];

        let kel = self.kel_timeline();
        let kel_text = kel
            .events
            .iter()
            .map(|e| e.label.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Key-Event Log".to_string(),
            search_text: format!("key events rotation history {kel_text}"),
            body: PresentationBody::Timeline(kel),
        });

        if let Some(gauge) = self.recovery_gauge() {
            out.push(Presentation {
                kind: PresentationKind::DomainVisual,
                label: "Recovery".to_string(),
                search_text: format!("recovery ask your guardians {}", gauge.label),
                body: PresentationBody::Gauge(gauge),
            });
        }
        out
    }
}

/// A plain-language word for the identity's lifecycle state (the 5-year-old read).
fn state_word(state: &IdentityState) -> &'static str {
    match state {
        IdentityState::Uninit => "Being born",
        IdentityState::Active => "Active",
        IdentityState::Retired => "Retired",
        IdentityState::Unknown(_) => "Unknown",
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as presentable.rs's tests are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::CellId;
    use dregg_sdk::identity::{
        COUNCIL_COMMIT_SLOT, CURRENT_KEYS_COMMIT_SLOT, LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT,
        STATE_ACTIVE, STATE_SLOT, key_set_commitment, next_keys_digest,
    };
    use dregg_sdk::polis::CouncilCharter;

    fn be_u64(v: u64) -> [u8; 32] {
        let mut f = [0u8; 32];
        f[24..32].copy_from_slice(&v.to_be_bytes());
        f
    }

    /// A genesis'd 3-of-5-guardian identity at height 1_000, holding G0 with G1
    /// pre-committed — the real `inspect_identity` decode shape.
    fn live_panel() -> (TrustPanel, IdentityCharter) {
        let council = CouncilCharter::new(
            (1u8..=5).map(|i| CellId::from_bytes([i; 32])).collect(),
            3,
        );
        let charter = IdentityCharter { council: council.clone(), cooling_period: 50 };

        let g0 = vec![[0x10u8; 32], [0x11u8; 32]];
        let g1 = vec![[0x20u8; 32], [0x21u8; 32]];
        let mut fields = [[0u8; 32]; 16];
        fields[STATE_SLOT as usize] = be_u64(STATE_ACTIVE);
        fields[CURRENT_KEYS_COMMIT_SLOT as usize] = key_set_commitment(&g0);
        fields[NEXT_KEYS_DIGEST_SLOT as usize] = next_keys_digest(&key_set_commitment(&g1));
        fields[COUNCIL_COMMIT_SLOT as usize] = council.members_commitment();
        fields[LAST_ROTATED_AT_SLOT as usize] = be_u64(1_000);

        let devices = vec![
            Device::laptop("laptop", g0[0]),
            Device::phone("phone", g0[1]),
        ];
        let kel = vec![
            KeyEvent {
                at: 0,
                description: "Inception — you were born".to_string(),
                installed_commit: key_set_commitment(&g0),
            },
            KeyEvent {
                at: 1_000,
                description: "You added your phone".to_string(),
                installed_commit: key_set_commitment(&g0),
            },
        ];
        let panel = TrustPanel::from_cell("ember", &charter, &fields, devices, kel);
        (panel, charter)
    }

    #[test]
    fn who_i_am_card_reflects_the_real_decode() {
        let (panel, _charter) = live_panel();
        assert_eq!(panel.status.state, IdentityState::Active);
        assert!(panel.status.council_commit_matches, "the council is pinned");
        assert_eq!(panel.guardians.len(), 5);
        assert_eq!(panel.threshold, 3);

        let card = panel.identity_card();
        assert_eq!(card.kind, ObjectKind::Capability);
        // The card states the human-legible recovery posture.
        assert!(card.fields.iter().any(|f| matches!(
            &f.value,
            FieldValue::Text(t) if t == "any 3 of 5 guardians"
        )));
        // Every device shows up as a friendly face.
        assert!(card.fields.iter().filter(|f| f.key.starts_with("device · ")).count() == 2);
        // Every guardian shows up as a shield face.
        assert!(card.fields.iter().filter(|f| f.key.starts_with("guardian · ")).count() == 5);
    }

    #[test]
    fn the_panel_offers_who_i_am_plus_kel() {
        let (panel, _charter) = live_panel();
        let set = panel.present();
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields), "WHO-I-AM floor");
        assert!(set.iter().any(|p| p.kind == PresentationKind::Provenance), "the KEL timeline");
        // No recovery underway → no recovery gauge.
        assert!(!set.iter().any(|p| p.kind == PresentationKind::DomainVisual));
        // The KEL has both the inception and the device-add events.
        let kel = panel.kel_timeline();
        assert_eq!(kel.events.len(), 2);
        assert_eq!(kel.events[0].at, 0);
    }

    #[test]
    fn demo_panel_surfaces_the_recovery_flow() {
        // The cockpit TRUST tab's source: WHO-I-AM floor + the KEL timeline + the
        // recovery gauge (a recovery is underway, so the DomainVisual gauge shows).
        let panel = TrustPanel::demo();
        assert_eq!(panel.guardians.len(), 5);
        assert_eq!(panel.threshold, 3);
        let set = panel.present();
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields), "WHO-I-AM floor");
        assert!(set.iter().any(|p| p.kind == PresentationKind::Provenance), "the KEL");
        assert!(
            set.iter().any(|p| p.kind == PresentationKind::DomainVisual),
            "the recovery gauge shows (a recovery is underway)"
        );
        assert!(panel.recovery_gauge().is_some(), "the ask-your-guardians gauge");
    }

    #[test]
    fn recovery_quorum_progress_mirrors_the_threshold() {
        let (panel, charter) = live_panel();
        let mut prog = RecoveryProgress::begin(&charter.council, charter.cooling_period);
        assert!(!prog.quorum_met(), "no approvals → no quorum");

        // Two guardians sign — below the 3-of-5 floor: still refused.
        prog.approve(0);
        prog.approve(2);
        assert_eq!(prog.approved_weight(), 2);
        assert!(!prog.quorum_met(), "2-of-5 is below the threshold");
        assert!(prog.headline().contains("Asking your guardians"));

        // A third guardian signs — the weighted quorum is met.
        prog.approve(4);
        assert!(prog.quorum_met(), "3-of-5 meets the threshold");
        // …but the cooling window has not cleared yet (the safety pause).
        assert!(!prog.cooling_cleared());
        assert!(prog.headline().contains("settling"));

        // The recovery rotation lands and the window elapses → welcome back.
        prog.cooling_elapsed = Some(charter.cooling_period);
        assert!(prog.cooling_cleared());
        assert!(prog.headline().contains("Welcome back"));

        // The panel now surfaces the recovery gauge.
        let panel = panel.with_recovery(prog);
        let gauge = panel.recovery_gauge().expect("recovery underway");
        assert_eq!(gauge.value, 3, "approved weight");
        assert_eq!(gauge.ceiling, Some(3), "the threshold");
        assert_eq!(gauge.rungs.len(), 5, "one rung per guardian");
        assert!(panel.present().iter().any(|p| p.kind == PresentationKind::DomainVisual));
    }

    #[test]
    fn idempotent_approval_and_weighting() {
        let council = CouncilCharter::new(
            (1u8..=3).map(|i| CellId::from_bytes([i; 32])).collect(),
            2,
        );
        let mut prog = RecoveryProgress::begin(&council, 10);
        // A guardian's signature counts once, even if recorded twice.
        prog.approve(0);
        prog.approve(0);
        assert_eq!(prog.approved.len(), 1);
        assert_eq!(prog.approved_weight(), 1);
        assert!(!prog.quorum_met());
        // Make guardian 1 a heavy (weight-2) guardian — a paper backup you hold.
        prog.weights[1] = 2;
        prog.approve(1);
        assert_eq!(prog.approved_weight(), 3);
        assert!(prog.quorum_met(), "weight 3 ≥ threshold 2");
    }
}
