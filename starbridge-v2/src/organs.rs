//! THE ORGAN PANELS — reflecting each dregg organ's live cell-state.
//!
//! `docs/ORGANS.md` names dregg's higher-order primitives — the *organs* — as
//! cells whose installed program enforces a quantitative invariant: a
//! **trustline** (a bilateral line of credit, `drawn ≤ ceiling` forever), a
//! **flash well** (a zero-duration line, the net-floor flash-loan invariant), a
//! **channel** (a group-keyed membership organ), a **mailbox** (an async message
//! organ), a **court** (an evidence/obligation organ). Each is a real cell whose
//! state IS the organ's live position; this module reflects that position
//! through the same live-ledger read every other panel uses (never a parallel
//! model, never a mock).
//!
//! ## What is embed-core vs. remote-path (the honest split)
//!
//! The organs split by what the `embedded-executor` build can reach in-process:
//!
//!   * **TRUSTLINE** and **FLASH WELL** are *embed-core* organs: their entire
//!     enforcement is the cell's executor-installed program (re-evaluated on
//!     every touching turn), so their live position is fully readable from the
//!     embedded [`World`]'s ledger — the panel reflects `drawn`/`ceiling`/
//!     `settled`/state for a trustline and `principal`/`fee`/`ratchet` for a
//!     flash well, decoded straight from the cell's state slots
//!     ([`dregg_cell::blueprint`]'s published slot constants — the SAME
//!     constants `dregg_sdk::trustline`/`flashwell` read). These are LIVE.
//!
//!   * **CHANNEL**, **MAILBOX**, and **COURT** are *node-service* organs: their
//!     full operation (group-key epochs, async relay delivery, evidence
//!     adjudication) lives behind `captp` (the network surface), which the
//!     headless `embedded-executor` build deliberately does not link
//!     (`dregg-sdk` is taken `default-features = false`, dropping the
//!     tokio/quinn/captp stack). So this module surfaces them HONESTLY as
//!     remote-path organs: their kind, their seam, and the route by which the
//!     master interface would reach them (a connected node), marked
//!     [`OrganReach::RemotePath`] — NOT faked local state. When the
//!     remote-federation panel lands (`NodeClient::Http`), these become live
//!     reflections of a node's organ cells over the wire.
//!
//! This is the matrix row made real: "trustline/flashwell in embed-core;
//! channel/mailbox/court need captp (network), surfaced as remote-path."
//!
//! gpui-free + `cargo test`-able: built purely from the [`World`] (for the
//! embed-core organs) and from static descriptors (for the remote-path organs).

use dregg_cell::blueprint::{
    FW_FEE_SLOT, FW_PRINCIPAL_SLOT, FW_RATCHET_SLOT, FW_STATE_CLOSED, FW_STATE_SLOT, STATE_OPEN,
    TL_CEILING_SLOT, TL_COLLATERAL_FULL_RESERVE, TL_COLLATERAL_PURE_CREDIT, TL_COLLATERAL_SLOT,
    TL_DRAWN_SLOT, TL_HOLDER_SLOT, TL_ISSUER_SLOT, TL_SETTLED_SLOT, TL_STATE_CLOSED, TL_STATE_SLOT,
};
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId};

use crate::world::World;

/// Decode a state slot's trailing big-endian u64 (the cell-program encoding the
/// blueprint uses — `field_from_u64` writes the value into the last 8 bytes).
/// This is the SAME decode `dregg_sdk::trustline`/`flashwell` apply to read an
/// organ's live position, so the panel cannot drift from the SDK's view.
fn slot_u64(f: &FieldElement) -> u64 {
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

/// Whether a field slot is entirely zero (an unwritten slot).
fn slot_is_zero(f: &FieldElement) -> bool {
    f.iter().all(|b| *b == 0)
}

/// Which organ kind a cell is (detected from its state-slot signature), or
/// `None` if the cell is not a recognized organ.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrganKind {
    /// A bilateral line of credit (trustline) — `drawn ≤ ceiling` forever.
    Trustline,
    /// A zero-duration line of credit (flash well) — the net-floor invariant.
    FlashWell,
}

impl OrganKind {
    pub fn label(self) -> &'static str {
        match self {
            OrganKind::Trustline => "trustline",
            OrganKind::FlashWell => "flash well",
        }
    }
}

/// Whether an organ's live state is reachable in this build, or only over the
/// remote (node-service) path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrganReach {
    /// The organ's enforcement is the cell's executor-installed program, so its
    /// live position is readable from the embedded ledger IN-PROCESS. LIVE.
    EmbedCore,
    /// The organ's full operation lives behind `captp` (the network surface the
    /// headless build does not link). Surfaced honestly — kind + seam + route —
    /// not faked. Becomes live when the remote-federation panel connects a node.
    RemotePath,
}

impl OrganReach {
    pub fn label(self) -> &'static str {
        match self {
            OrganReach::EmbedCore => "live (embed-core)",
            OrganReach::RemotePath => "remote-path (needs a connected node)",
        }
    }
}

/// The collateral point of a trustline line (Lean §12).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustlineCollateral {
    /// The full line is escrowed at open (the cell's balance backs draws).
    FullReserve,
    /// No hard backing; draws move the derived ±drawn pair (issuer's risk).
    PureCredit,
    /// The slot is unwritten/unrecognized (the line is not yet open at a pinned
    /// collateral point — fullReserve is the default before the slot is pinned).
    Unpinned,
}

impl TrustlineCollateral {
    pub fn label(self) -> &'static str {
        match self {
            TrustlineCollateral::FullReserve => "fullReserve",
            TrustlineCollateral::PureCredit => "pureCredit",
            TrustlineCollateral::Unpinned => "fullReserve (default, unpinned)",
        }
    }
}

/// A live trustline position — the SAME shape `dregg_sdk::trustline::TrustlineStatus`
/// reads, decoded straight from the organ cell's state slots in the embedded
/// ledger. This is the organ's live cell-state reflected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustlineReflection {
    /// The trustline organ cell.
    pub cell: CellId,
    /// A short operator-legible id (abbreviated cell id).
    pub short: String,
    /// The extended line N (`ceiling`, the attenuation bound — immutable once open).
    pub line: u64,
    /// Net drawn against the line (up on draw, down on repay; `drawn ≤ ceiling`).
    pub drawn: u64,
    /// Cumulative drawn value already redeemed to the holder by settlement
    /// (`settled ≤ drawn` — the escrow-solvency proof).
    pub settled: u64,
    /// Remaining undrawn line: `line − drawn`.
    pub remaining: u64,
    /// Outstanding (drawn but not yet settled): `drawn − settled`.
    pub outstanding: u64,
    /// The cell's escrowed hard balance backing the line.
    pub escrow: i64,
    /// The issuer identity (the party whose escrow backs draws), if the slot is set.
    pub issuer: Option<CellId>,
    /// The holder identity (the counterparty exercising the line), if set.
    pub holder: Option<CellId>,
    /// The collateral point this line is at (fullReserve / pureCredit / unpinned).
    pub collateral: TrustlineCollateral,
    /// Whether the line is OPEN (terms written, live) vs. uninit / closed.
    pub open: bool,
    /// Whether the line is CLOSED (terminal — the cell is inert).
    pub closed: bool,
}

impl TrustlineReflection {
    /// Reflect a trustline organ's live position from a cell, IF the cell is a
    /// trustline (its state slots carry a written ceiling). Returns `None` for a
    /// non-trustline cell.
    pub fn from_cell(id: &CellId, cell: &Cell) -> Option<Self> {
        // A trustline cell has a written ceiling slot (the line N). A plain cell
        // (no organ program) leaves the slots zero — so a zero ceiling AND a zero
        // state slot means "not a trustline".
        let fields = &cell.state.fields;
        let ceiling = slot_u64(&fields[TL_CEILING_SLOT as usize]);
        let state = slot_u64(&fields[TL_STATE_SLOT as usize]);
        if ceiling == 0 && state == 0 {
            return None;
        }
        let drawn = slot_u64(&fields[TL_DRAWN_SLOT as usize]);
        let settled = slot_u64(&fields[TL_SETTLED_SLOT as usize]);
        let issuer = (!slot_is_zero(&fields[TL_ISSUER_SLOT as usize]))
            .then(|| CellId::from_bytes(fields[TL_ISSUER_SLOT as usize]));
        let holder = (!slot_is_zero(&fields[TL_HOLDER_SLOT as usize]))
            .then(|| CellId::from_bytes(fields[TL_HOLDER_SLOT as usize]));
        let collateral = match slot_u64(&fields[TL_COLLATERAL_SLOT as usize]) {
            x if x == TL_COLLATERAL_FULL_RESERVE && !slot_is_zero(&fields[TL_COLLATERAL_SLOT as usize]) => {
                TrustlineCollateral::FullReserve
            }
            x if x == TL_COLLATERAL_PURE_CREDIT => TrustlineCollateral::PureCredit,
            _ => TrustlineCollateral::Unpinned,
        };
        Some(TrustlineReflection {
            cell: *id,
            short: crate::reflect::short_hex(id.as_bytes()),
            line: ceiling,
            drawn,
            settled,
            remaining: ceiling.saturating_sub(drawn),
            outstanding: drawn.saturating_sub(settled),
            escrow: cell.state.balance(),
            issuer,
            holder,
            collateral,
            open: state == STATE_OPEN,
            closed: state == TL_STATE_CLOSED,
        })
    }

    /// A one-line operator summary of the line's live position.
    pub fn summary(&self) -> String {
        let state = if self.closed {
            "CLOSED"
        } else if self.open {
            "OPEN"
        } else {
            "uninit"
        };
        format!(
            "{state} · line {} · drawn {} · settled {} · remaining {} ({})",
            self.line,
            self.drawn,
            self.settled,
            self.remaining,
            self.collateral.label(),
        )
    }
}

/// A live flash-well position — the SAME shape `dregg_sdk::flashwell::FlashWellStatus`
/// reads, decoded from the organ cell's state slots in the embedded ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlashWellReflection {
    /// The flash-well organ cell.
    pub cell: CellId,
    /// A short operator-legible id.
    pub short: String,
    /// The published liquidity floor (the well must never end an action below it).
    pub principal: u64,
    /// The published flat fee per use.
    pub fee: u64,
    /// THE RATCHET — the fee-schedule position (rung × fee); climbs ≥1 rung per
    /// touch (the fee-evasion tooth).
    pub ratchet: u64,
    /// Redeemable accrued fees: `ratchet − fee` (the priming quantum is the
    /// schedule origin, not income).
    pub accrued_fees: u64,
    /// The well's actual balance (principal + accrued fees + any cushion).
    pub balance: i64,
    /// Whether the well is OPEN (lending).
    pub open: bool,
    /// Whether the well is CLOSED (swept, terminal — inert).
    pub closed: bool,
}

impl FlashWellReflection {
    /// Reflect a flash-well organ's live position from a cell, IF the cell is a
    /// flash well (its state slots carry a written principal). Returns `None`
    /// otherwise.
    ///
    /// NOTE the trustline and flash-well slot 0 are both `STATE`, and slot 1 is
    /// the trustline ceiling vs. the flash-well principal — to disambiguate, a
    /// caller should detect the organ kind via [`detect_organ`], which checks the
    /// trustline's distinctive ISSUER/HOLDER identity slots first.
    pub fn from_cell(id: &CellId, cell: &Cell) -> Option<Self> {
        let fields = &cell.state.fields;
        let principal = slot_u64(&fields[FW_PRINCIPAL_SLOT as usize]);
        let state = slot_u64(&fields[FW_STATE_SLOT as usize]);
        if principal == 0 && state == 0 {
            return None;
        }
        let fee = slot_u64(&fields[FW_FEE_SLOT as usize]);
        let ratchet = slot_u64(&fields[FW_RATCHET_SLOT as usize]);
        Some(FlashWellReflection {
            cell: *id,
            short: crate::reflect::short_hex(id.as_bytes()),
            principal,
            fee,
            ratchet,
            accrued_fees: ratchet.saturating_sub(fee),
            balance: cell.state.balance(),
            open: state == STATE_OPEN,
            closed: state == FW_STATE_CLOSED,
        })
    }

    /// A one-line operator summary of the well's live position.
    pub fn summary(&self) -> String {
        let state = if self.closed {
            "CLOSED"
        } else if self.open {
            "OPEN"
        } else {
            "uninit"
        };
        format!(
            "{state} · principal {} · fee {} · ratchet {} · accrued {}",
            self.principal, self.fee, self.ratchet, self.accrued_fees,
        )
    }
}

/// A remote-path organ the master interface does not reach in this headless
/// build — surfaced HONESTLY (kind + seam + route), not faked. Becomes live when
/// the remote-federation panel connects a node (`NodeClient::Http`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemoteOrgan {
    /// The organ kind (channel / mailbox / court).
    pub kind: &'static str,
    /// The organ's one-seam description (what it enforces / does).
    pub seam: &'static str,
    /// The route by which the master interface would reach it (the honest
    /// "designed-pending" path).
    pub route: &'static str,
}

/// The remote-path organs catalogued honestly: channel, mailbox, court. These
/// need `captp` (the network surface the headless build does not link), so the
/// panel names them + their seam + their route, never fakes their state.
pub fn remote_path_organs() -> Vec<RemoteOrgan> {
    vec![
        RemoteOrgan {
            kind: "channel",
            seam: "group-keyed membership organ — remove(m) darkens ciphertext AND \
                   capabilities in ONE turn (the group-key epoch lift, ORGANS §4)",
            route: "behind captp (group-key epoch service) — reach via a connected node \
                    (NodeClient::Http), then reflect the channel cell's epoch/roster live",
        },
        RemoteOrgan {
            kind: "mailbox",
            seam: "async message organ — an EmitEvent deposits a pending wake the \
                   recipient drains in its OWN future turn (the notify edge; cf. the \
                   SWARM tab's in-process realization)",
            route: "behind captp (relay transport / mailbox crank) — reach via a \
                    connected node, then reflect the mailbox cell's queue live",
        },
        RemoteOrgan {
            kind: "court",
            seam: "evidence / obligation organ — a bonded obligation adjudicated against \
                   submitted evidence (the conflict/obligation-bond machinery)",
            route: "node-service (evidence intake + adjudication) — reach via a connected \
                    node, then reflect the court cell's docket live",
        },
    ]
}

/// Detect which organ a cell is (if any), disambiguating trustline vs. flash
/// well by the trustline's distinctive issuer/holder identity slots (a flash
/// well has no such identity slots — its slot 2 is the FEE, a small u64, and its
/// slot 3 is the OWNER *key*, but it carries no holder slot 3 as a CellId-shaped
/// counterparty *with* a written issuer slot 2-as-CellId).
///
/// The robust discriminator: a trustline writes BOTH the issuer (slot 2) and
/// holder (slot 3) as 32-byte cell identities at open. A flash well's slot 2 is
/// a small fee value (trailing-byte u64, high bytes zero) — never a full
/// 32-byte identity. So "slot 2 is a wide (non-trailing) value" ⇒ trustline.
pub fn detect_organ(cell: &Cell) -> Option<OrganKind> {
    let fields = &cell.state.fields;
    // A trustline at/after open has a written holder identity (slot 3) whose
    // HIGH bytes are non-zero (a real CellId, not a trailing-u64). A flash
    // well's slot 3 is the owner *key* (also wide) — so we instead use slot 2:
    // trustline slot 2 = issuer CellId (wide); flash-well slot 2 = fee (narrow).
    let slot2 = &fields[TL_ISSUER_SLOT as usize]; // == FW_FEE_SLOT index (2)
    let slot2_is_wide_identity = slot2[..24].iter().any(|b| *b != 0);
    let ceiling = slot_u64(&fields[TL_CEILING_SLOT as usize]);
    let state0 = slot_u64(&fields[TL_STATE_SLOT as usize]);
    let principal = slot_u64(&fields[FW_PRINCIPAL_SLOT as usize]);

    if slot2_is_wide_identity && (ceiling != 0 || state0 != 0) {
        // Slot 2 holds a wide identity AND slot 1 has a ceiling ⇒ trustline.
        Some(OrganKind::Trustline)
    } else if (principal != 0 || state0 != 0) && !slot2_is_wide_identity {
        // Slot 1 principal written, slot 2 is a narrow fee ⇒ flash well.
        Some(OrganKind::FlashWell)
    } else {
        None
    }
}

/// THE ORGAN SURVEY — scan the live world for every embed-core organ cell and
/// reflect its position, plus catalog the remote-path organs honestly. The
/// cockpit maps this onto the ORGANS tab.
#[derive(Clone, Debug)]
pub struct OrganSurvey {
    /// Live trustline organ reflections (embed-core).
    pub trustlines: Vec<TrustlineReflection>,
    /// Live flash-well organ reflections (embed-core).
    pub flash_wells: Vec<FlashWellReflection>,
    /// The remote-path organs (channel / mailbox / court), surfaced honestly.
    pub remote: Vec<RemoteOrgan>,
}

impl OrganSurvey {
    /// Build the organ survey from the live world: detect + reflect every
    /// embed-core organ cell in the ledger, and catalog the remote-path organs.
    pub fn build(world: &World) -> Self {
        let mut trustlines = Vec::new();
        let mut flash_wells = Vec::new();
        let mut cells: Vec<(&CellId, &Cell)> = world.ledger().iter().collect();
        cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        for (id, cell) in cells {
            match detect_organ(cell) {
                Some(OrganKind::Trustline) => {
                    if let Some(t) = TrustlineReflection::from_cell(id, cell) {
                        trustlines.push(t);
                    }
                }
                Some(OrganKind::FlashWell) => {
                    if let Some(f) = FlashWellReflection::from_cell(id, cell) {
                        flash_wells.push(f);
                    }
                }
                None => {}
            }
        }
        OrganSurvey {
            trustlines,
            flash_wells,
            remote: remote_path_organs(),
        }
    }

    /// The total count of LIVE (embed-core) organs reflected.
    pub fn live_count(&self) -> usize {
        self.trustlines.len() + self.flash_wells.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::program::field_from_u64;
    use dregg_cell::Cell;

    /// Build a cell and write trustline-shaped state slots into it (mimicking an
    /// open fullReserve line: ceiling, drawn, settled, issuer, holder, state).
    /// This is a fixture for the reflection — the real organ cell is born from
    /// the blueprint factory, but the slot ENCODING the panel decodes is the
    /// same, so reflecting a hand-written fixture validates the decode path.
    fn trustline_fixture(line: u64, drawn: u64, settled: u64, issuer: CellId, holder: CellId) -> (CellId, Cell) {
        let mut cell = crate::world::make_open_cell(0x70, line as i64);
        let id = cell.id();
        cell.state.fields[TL_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        cell.state.fields[TL_CEILING_SLOT as usize] = field_from_u64(line);
        cell.state.fields[TL_DRAWN_SLOT as usize] = field_from_u64(drawn);
        cell.state.fields[TL_SETTLED_SLOT as usize] = field_from_u64(settled);
        cell.state.fields[TL_ISSUER_SLOT as usize] = *issuer.as_bytes();
        cell.state.fields[TL_HOLDER_SLOT as usize] = *holder.as_bytes();
        (id, cell)
    }

    /// A flash-well fixture: principal, fee, ratchet, state.
    fn flashwell_fixture(principal: u64, fee: u64, ratchet: u64) -> (CellId, Cell) {
        let mut cell = crate::world::make_open_cell(0x71, (principal + ratchet) as i64);
        let id = cell.id();
        cell.state.fields[FW_STATE_SLOT as usize] = field_from_u64(STATE_OPEN);
        cell.state.fields[FW_PRINCIPAL_SLOT as usize] = field_from_u64(principal);
        cell.state.fields[FW_FEE_SLOT as usize] = field_from_u64(fee);
        cell.state.fields[FW_RATCHET_SLOT as usize] = field_from_u64(ratchet);
        (id, cell)
    }

    #[test]
    fn reflects_a_trustline_live_position() {
        let issuer = CellId::from_bytes([0x11u8; 32]);
        let holder = CellId::from_bytes([0x22u8; 32]);
        let (id, cell) = trustline_fixture(100, 30, 10, issuer, holder);
        let t = TrustlineReflection::from_cell(&id, &cell).expect("a trustline reflects");
        assert_eq!(t.line, 100);
        assert_eq!(t.drawn, 30);
        assert_eq!(t.settled, 10);
        assert_eq!(t.remaining, 70, "remaining = line − drawn");
        assert_eq!(t.outstanding, 20, "outstanding = drawn − settled");
        assert_eq!(t.issuer, Some(issuer));
        assert_eq!(t.holder, Some(holder));
        assert!(t.open);
        assert!(!t.closed);
        assert!(t.summary().contains("line 100"));
    }

    #[test]
    fn reflects_a_flash_well_live_position() {
        let (id, cell) = flashwell_fixture(1_000, 5, 15);
        let f = FlashWellReflection::from_cell(&id, &cell).expect("a flash well reflects");
        assert_eq!(f.principal, 1_000);
        assert_eq!(f.fee, 5);
        assert_eq!(f.ratchet, 15);
        assert_eq!(f.accrued_fees, 10, "accrued = ratchet − fee");
        assert!(f.open);
        assert!(f.summary().contains("principal 1000"));
    }

    #[test]
    fn detect_organ_disambiguates_trustline_from_flash_well() {
        let issuer = CellId::from_bytes([0x11u8; 32]);
        let holder = CellId::from_bytes([0x22u8; 32]);
        let (_tid, tl) = trustline_fixture(100, 0, 0, issuer, holder);
        let (_fid, fw) = flashwell_fixture(1_000, 5, 5);
        assert_eq!(detect_organ(&tl), Some(OrganKind::Trustline));
        assert_eq!(detect_organ(&fw), Some(OrganKind::FlashWell));
        // A plain cell (no organ slots written) is not an organ.
        let plain = crate::world::make_open_cell(0x99, 500);
        assert_eq!(detect_organ(&plain), None);
    }

    #[test]
    fn a_plain_cell_does_not_reflect_as_an_organ() {
        let cell = crate::world::make_open_cell(0x99, 500);
        let id = cell.id();
        assert!(TrustlineReflection::from_cell(&id, &cell).is_none());
        assert!(FlashWellReflection::from_cell(&id, &cell).is_none());
    }

    #[test]
    fn organ_survey_finds_embed_core_organs_in_the_live_world() {
        let mut world = World::new();
        // Install a trustline organ cell and a flash-well organ cell via the
        // genesis path (writing the organ-shaped state).
        let issuer = CellId::from_bytes([0x11u8; 32]);
        let holder = CellId::from_bytes([0x22u8; 32]);
        let (_tid, tl) = trustline_fixture(100, 30, 0, issuer, holder);
        let (_fid, fw) = flashwell_fixture(1_000, 5, 5);
        world.genesis_install(tl);
        world.genesis_install(fw);
        // Plus a plain cell that is NOT an organ.
        world.genesis_cell(0xAB, 5_000);

        let survey = OrganSurvey::build(&world);
        assert_eq!(survey.trustlines.len(), 1, "one trustline organ found");
        assert_eq!(survey.flash_wells.len(), 1, "one flash-well organ found");
        assert_eq!(survey.live_count(), 2);
        // The remote-path organs are catalogued honestly (channel/mailbox/court).
        assert_eq!(survey.remote.len(), 3);
        assert!(survey.remote.iter().any(|o| o.kind == "channel"));
        assert!(survey.remote.iter().any(|o| o.kind == "mailbox"));
        assert!(survey.remote.iter().any(|o| o.kind == "court"));
    }

    #[test]
    fn remote_path_organs_are_honest_not_faked() {
        let remote = remote_path_organs();
        // Each remote-path organ names its kind, seam, and route — no faked state.
        for o in &remote {
            assert!(!o.kind.is_empty());
            assert!(!o.seam.is_empty());
            assert!(o.route.contains("node") || o.route.contains("captp"));
        }
    }
}
