//! SURFACE MIGRATION — the `migrate(surface_cap, target)` verb.
//!
//! `docs/deos/SURFACE-MIGRATION.md` describes migration as one operation:
//! **relocate a surface along the firmament distance axis with its capability
//! identity preserved.** A surface is a [`SurfaceCapability`] (a REAL
//! [`dregg_firmament::Capability`] over the surface's backing cell, paired with a
//! stable [`SurfaceId`]); "where it runs" is the [`Target`] half of that cap. To
//! migrate is to change the cap's `Target` while keeping its
//! [`SurfaceId`](crate::surface::SurfaceId), its backing cell, and its rights —
//! everything migration must respect is already the law of caps.
//!
//! This module is the missing VERB. The tear-off ([`super::tearoff`]) built the
//! Local→Surface (second-window) arm; the design doc §2(b) describes Local→HostPd
//! but it was PROSE — no function, no call site. This is the real function, the
//! re-mint, and the structural gate, for at least the Local→HostPd leg.
//!
//! ## What is real here
//!
//! [`migrate`] is a total function over caps. Given a held [`SurfaceCapability`]
//! and a [`MigrationTarget`] (the destination point on the distance axis, plus
//! the rights to carry across), it:
//!
//!   1. **Gates** — the requested rights must be `⊆` the held rights
//!      ([`dregg_firmament::is_attenuation`], `granted ⊆ held`). A WIDENING
//!      migration is REFUSED ([`MigrateError::Widening`]). You cannot migrate
//!      authority you don't hold — the same `is_attenuation` gate every window op
//!      runs. This is structural: there is no path that re-mints at wider rights.
//!   2. **Re-mints** — a fresh [`SurfaceCapability`] with the SAME
//!      [`SurfaceId`](crate::surface::SurfaceId) (the identity the migration
//!      preserves), the new `Target` (`HostPd { pd }` for the Local→HostPd leg),
//!      and the carried (narrowed-or-equal) rights. The backing cell is unchanged
//!      — a migration relocates the cap's transport, never the cell it points at.
//!
//! ## The honest distance: the live re-home seam
//!
//! [`migrate`] produces the re-homed CAP — the authority half of the move, which
//! is fully real and proven here. What it does NOT do is the live TRANSPORT
//! re-home: actually spawning/selecting the child PD and re-routing the surface's
//! `present`/`route_input` round-trips over that PD's firmament Endpoint instead
//! of the in-process compositor. That needs the live compositor seam:
//!
//!   * a registered [`dregg_firmament::HostPdId`] for a real confined child (the
//!     firmament's `HostPdBacking::register` over a live control socket, behind
//!     `--features process-pd` on unix), and
//!   * the compositor re-pointing `Shell::present` / `Shell::route_input` for this
//!     surface at that Endpoint.
//!
//! The caller passes the destination [`dregg_firmament::HostPdId`] it has already
//! registered; `migrate` re-mints the cap to name it. Re-pointing the live present
//! path is the named remaining seam — the cap migrates here today; the glass
//! follows when the compositor binds the re-homed cap to the child's Endpoint.

use dregg_firmament::{is_attenuation, HostPdId, Rights, Target};

use crate::surface::SurfaceCapability;

/// Where a surface is migrating TO — a point on the firmament distance axis plus
/// the rights to carry across. This is the `target` argument of
/// `migrate(surface_cap, target)`, made into a type so the verb is total and the
/// gate is uniform across destinations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MigrationTarget {
    /// Re-home the surface's processing into a confined, OS-sandboxed child PD
    /// whose only channel is its firmament Endpoint — the Local→HostPd leg of
    /// `SURFACE-MIGRATION.md` §2(b). `pd` is the destination host-PD the caller
    /// has registered; `rights` are the (narrowed-or-equal) rights to delegate to
    /// it. The re-minted cap targets `HostPd { pd }`; the live present re-home is
    /// the named remaining seam (see the module doc).
    HostPd {
        /// The destination confined child PD (already registered with the
        /// firmament's `HostPdBacking`).
        pd: HostPdId,
        /// The rights to carry across. Must be `⊆` the held cap's rights, else the
        /// migration is refused as a widening.
        rights: Rights,
    },
}

impl MigrationTarget {
    /// The rights this migration carries across (the authority the destination
    /// will hold over the surface).
    pub fn rights(&self) -> &Rights {
        match self {
            MigrationTarget::HostPd { rights, .. } => rights,
        }
    }

    /// The firmament [`Target`] the re-minted cap will name.
    fn firmament_target(&self) -> Target {
        match self {
            MigrationTarget::HostPd { pd, .. } => Target::HostPd { pd: *pd },
        }
    }
}

/// Why a [`migrate`] was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MigrateError {
    /// The migration asked to carry rights WIDER than the held cap holds — a
    /// no-amplification violation. Refused by the same `granted ⊆ held`
    /// ([`is_attenuation`]) gate every window op runs. Carries the held and the
    /// (illegally wider) requested rights for the operator's diagnostic.
    Widening {
        /// The rights the held surface cap actually holds.
        held: Rights,
        /// The (illegally wider) rights the migration requested to carry.
        requested: Rights,
    },
}

impl std::fmt::Display for MigrateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MigrateError::Widening { held, requested } => write!(
                f,
                "surface migration refused: requested rights {requested:?} exceed held {held:?} \
                 (a widening migration cannot amplify authority — granted ⊆ held)"
            ),
        }
    }
}

impl std::error::Error for MigrateError {}

/// MIGRATE a surface capability to `target` — the `migrate(surface_cap, target)`
/// verb of `docs/deos/SURFACE-MIGRATION.md`.
///
/// Relocates `surface_cap` along the firmament distance axis to `target`,
/// PRESERVING its capability identity: the returned cap has the SAME
/// [`SurfaceId`](crate::surface::SurfaceId) and the same backing cell, with only
/// its `Target` (and, if narrowed, its rights) changed. For the Local→HostPd leg
/// this re-mints the surface cap with `Target::HostPd { pd }`, re-homing the
/// surface's authority to a confined child PD.
///
/// The migration is **attenuating and gated**: the rights the migration carries
/// (`target.rights()`) must be `⊆` the held cap's rights
/// ([`is_attenuation`], `granted ⊆ held`). A WIDENING migration is REFUSED with
/// [`MigrateError::Widening`] — you cannot migrate authority you don't hold. This
/// is the same no-amplification law every window op (focus/move/share/present)
/// runs, fired structurally: there is no code path that re-mints at wider rights.
///
/// Returns the re-homed [`SurfaceCapability`] (the AUTHORITY half of the move,
/// fully real). The live TRANSPORT re-home — re-pointing the surface's
/// `present`/`route_input` over the child PD's Endpoint — is the named remaining
/// compositor seam (see the module doc); the cap migrates here, the glass follows
/// when the compositor binds it.
pub fn migrate(
    surface_cap: &SurfaceCapability,
    target: &MigrationTarget,
) -> Result<SurfaceCapability, MigrateError> {
    let held = surface_cap.rights();
    let requested = target.rights();

    // THE GATE: `granted ⊆ held`. A migration carrying wider rights than the held
    // cap is a no-amplification violation — refused identically to a widening
    // share. Never reinvented: the SAME `is_attenuation` the firmament's local,
    // distributed, surface, and host-PD backings all use.
    if !is_attenuation(held, requested) {
        return Err(MigrateError::Widening {
            held: held.clone(),
            requested: requested.clone(),
        });
    }

    // RE-MINT: same SurfaceId (the identity the migration preserves), the new
    // firmament Target, the carried (narrowed-or-equal) rights. The backing cell
    // is unchanged — `Capability` for the new target carries the relocated
    // authority; the surface handle that identifies this window across the move is
    // untouched.
    let relocated = dregg_firmament::Capability {
        target: target.firmament_target(),
        rights: requested.clone(),
    };
    Ok(SurfaceCapability::new(surface_cap.surface(), relocated))
}

// ─────────────────── THE LIVE TRANSPORT RE-HOME (process-pd) ─────────────────
//
// `migrate` above produces the re-homed CAP. This is the OTHER half: once a
// surface migrates to a confined child PD, its present/route_input round-trips
// cross the child's firmament SURFACE Endpoint instead of the in-process
// compositor — the GLASS follows the cap. Gated on `process-pd` (Unix), which
// brings in the confined-child spawn + the surface Endpoint transport.

#[cfg(all(feature = "process-pd", unix))]
mod transport {
    use super::*;
    use dregg_firmament::{HostPdBacking, SurfaceEvent, SurfaceFrame};

    /// THE GLASS-FOLLOWS-THE-CAP transport: binds a migrated [`SurfaceCapability`]
    /// (whose `Target` is now `HostPd { pd }`) to the LIVE surface Endpoint of a
    /// confined child PD, and re-points its present/route_input over that Endpoint.
    ///
    /// The compositor builds one of these AFTER [`migrate`] re-mints the cap and
    /// after the firmament has registered the child's surface Endpoint
    /// ([`HostPdBacking::register_surface`]). Thereafter a present/input for the
    /// migrated surface does NOT go to the in-process compositor — it crosses the
    /// Endpoint to the confined child, which renders in its own MMU-isolated
    /// memory and returns the frame. The cap's rights gate every round-trip
    /// through the SAME `granted ⊆ held` law (the host backing's
    /// `present_over_endpoint`).
    pub struct PresentTransport {
        /// The host backing holding the registered surface Endpoint to the child.
        host: HostPdBacking,
    }

    /// Why a re-homed present/input failed.
    #[derive(Debug)]
    pub enum TransportError {
        /// The cap is not targeting a host-PD (it was not migrated, or the
        /// surface Endpoint was never registered for it).
        NotReHomed,
        /// The firmament rejected the round-trip (closed Endpoint / over-broad
        /// rights / malformed frame). Carries the backing's reason.
        Backing(String),
    }

    impl PresentTransport {
        /// Wrap a host backing whose surface Endpoint(s) are already registered.
        pub fn new(host: HostPdBacking) -> Self {
            PresentTransport { host }
        }

        /// PRESENT the migrated surface over the child's Endpoint — the frame the
        /// confined child rendered crosses back. The `cap` MUST be a re-homed
        /// surface cap (`Target::HostPd { pd }`); its rights gate the op.
        pub fn present(
            &self,
            cap: &SurfaceCapability,
            seq: u64,
        ) -> Result<SurfaceFrame, TransportError> {
            let pd = self.pd_of(cap)?;
            self.host
                .present_over_endpoint(pd, cap.rights(), SurfaceEvent::Present { seq })
                .map_err(|e| TransportError::Backing(format!("{e:?}")))
        }

        /// ROUTE an input event to the migrated surface over the child's Endpoint
        /// — the child folds it and returns the re-rendered frame. The glass
        /// (rendering) AND the input both now flow through the confined child.
        pub fn route_input(
            &self,
            cap: &SurfaceCapability,
            code: u64,
        ) -> Result<SurfaceFrame, TransportError> {
            let pd = self.pd_of(cap)?;
            self.host
                .present_over_endpoint(pd, cap.rights(), SurfaceEvent::Input { code })
                .map_err(|e| TransportError::Backing(format!("{e:?}")))
        }

        /// The host-PD a re-homed cap names, or [`TransportError::NotReHomed`].
        fn pd_of(&self, cap: &SurfaceCapability) -> Result<HostPdId, TransportError> {
            match cap.authority().target {
                Target::HostPd { pd } => Ok(pd),
                _ => Err(TransportError::NotReHomed),
            }
        }
    }
}

#[cfg(all(feature = "process-pd", unix))]
pub use transport::{PresentTransport, TransportError};

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::{AuthRequired, Capability, HostPdId};
    use dregg_types::CellId;

    use crate::surface::{SurfaceCapability, SurfaceId};

    /// A held surface cap over `cell` with `rights` — the shell mints these for a
    /// real surface; here we build one directly to exercise the verb in the
    /// gpui-free, headless-testable layer.
    fn held_surface(id: u64, cell: u8, rights: AuthRequired) -> SurfaceCapability {
        // A distinct, stable cell id per `cell` byte — enough to prove the backing
        // cell rides through the re-mint unchanged (the surface target carries it).
        let mut bytes = [0u8; 32];
        bytes[0] = cell;
        let authority = Capability::surface(CellId::from_bytes(bytes), rights);
        SurfaceCapability::new(SurfaceId(id), authority)
    }

    /// A valid Local→HostPd migration at the SAME rights re-mints with
    /// `Target::HostPd`, preserves the SurfaceId, and keeps the rights. (The gate
    /// is non-vacuous: a valid migration is ADMITTED, not just a bad one refused.)
    #[test]
    fn local_to_hostpd_remints_and_preserves_identity() {
        let cap = held_surface(7, 99, AuthRequired::Signature);
        let target = MigrationTarget::HostPd {
            pd: HostPdId(3),
            rights: AuthRequired::Signature,
        };

        let migrated = migrate(&cap, &target).expect("equal-rights migration is admitted");

        // Identity preserved: SAME SurfaceId across the move.
        assert_eq!(migrated.surface(), cap.surface());
        assert_eq!(migrated.surface(), SurfaceId(7));
        // Re-homed: the cap now names the host-PD point on the distance axis.
        assert_eq!(
            migrated.authority().target,
            Target::HostPd { pd: HostPdId(3) }
        );
        assert!(migrated.authority().target.is_host_pd());
        // Rights carried unchanged.
        assert_eq!(migrated.rights(), &AuthRequired::Signature);
    }

    /// A NARROWING migration (carry less authority to the child) is admitted and
    /// re-mints at the narrowed rights — the receiving end gets exactly the
    /// delegated rights, never more.
    #[test]
    fn narrowing_migration_is_admitted_at_narrowed_rights() {
        // Held: Either (signature OR proof). Migrate carrying only Signature
        // (strictly narrower). `is_attenuation(Either, Signature)` holds.
        let cap = held_surface(11, 42, AuthRequired::Either);
        let target = MigrationTarget::HostPd {
            pd: HostPdId(1),
            rights: AuthRequired::Signature,
        };

        let migrated = migrate(&cap, &target).expect("narrowing migration is admitted");

        assert_eq!(migrated.surface(), SurfaceId(11));
        assert_eq!(migrated.rights(), &AuthRequired::Signature);
        assert_eq!(
            migrated.authority().target,
            Target::HostPd { pd: HostPdId(1) }
        );
    }

    /// A WIDENING migration is REFUSED — you cannot migrate authority you don't
    /// hold. Held = Signature; requesting Either (wider) is rejected.
    #[test]
    fn widening_migration_is_refused() {
        let cap = held_surface(5, 13, AuthRequired::Signature);
        let target = MigrationTarget::HostPd {
            pd: HostPdId(0),
            // Either is WIDER than Signature: is_attenuation(Signature, Either)
            // is false (Either ⊄ Signature).
            rights: AuthRequired::Either,
        };

        let err = migrate(&cap, &target).expect_err("widening must be refused");
        match err {
            MigrateError::Widening { held, requested } => {
                assert_eq!(held, AuthRequired::Signature);
                assert_eq!(requested, AuthRequired::Either);
            }
        }
    }

    /// The gate is structural — even a `None`-held cap (the widest possible "any
    /// authority is wider") refuses a `Signature` request? No: None is the LEAST
    /// restrictive, so EVERYTHING is ⊆ None — a None-held cap admits any
    /// narrowing. Conversely an `Impossible`-held cap admits only `Impossible`.
    /// This pins the lattice ends so the gate is provably non-vacuous at both
    /// extremes.
    #[test]
    fn gate_pins_lattice_extremes() {
        // None-held admits a Signature migration (Signature ⊆ None).
        let wide = held_surface(1, 1, AuthRequired::None);
        assert!(migrate(
            &wide,
            &MigrationTarget::HostPd {
                pd: HostPdId(9),
                rights: AuthRequired::Signature,
            },
        )
        .is_ok());

        // Impossible-held refuses everything but Impossible (None ⊄ Impossible).
        let locked = held_surface(2, 2, AuthRequired::Impossible);
        assert!(migrate(
            &locked,
            &MigrationTarget::HostPd {
                pd: HostPdId(9),
                rights: AuthRequired::None,
            },
        )
        .is_err());
        // ...but Impossible→Impossible is admitted (the gate is non-vacuous even
        // at the locked end).
        assert!(migrate(
            &locked,
            &MigrationTarget::HostPd {
                pd: HostPdId(9),
                rights: AuthRequired::Impossible,
            },
        )
        .is_ok());
    }
}

// ───────────── THE FULL LIVE-TRANSPORT E2E (authority + glass), by RUNNING ────
//
// The tests above prove the AUTHORITY half (the re-mint + the gate). This module
// proves the WHOLE move end-to-end on the live transport: a real held surface
// cap is MIGRATED to a CONFINED child PD, the child's surface Endpoint is
// re-homed, and present/input round-trips cross the Endpoint to the child — the
// glass follows the migrated cap. Gated on `process-pd` (Unix); runs with:
//   cargo test --features process-pd --lib dock::migrate::live_transport -- --nocapture
#[cfg(all(feature = "process-pd", unix))]
mod live_transport {
    use super::transport::PresentTransport;
    use super::{migrate, MigrationTarget};
    use crate::surface::{SurfaceCapability, SurfaceId};
    use dregg_firmament::process_kernel::ProcessKernel;
    use dregg_firmament::{
        serve_one_surface_event, AuthRequired, Capability, CellId, HostPdBacking, SurfaceEvent,
        SurfaceFrame,
    };

    /// The renderer's deterministic frame digest (same on both sides so the
    /// compositor can verify the child genuinely rendered the events it received).
    fn render_digest(state: u64, seq: u64) -> u64 {
        let mut x = state ^ seq.rotate_left(32);
        x ^= x >> 30;
        x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
        x ^= x >> 27;
        x
    }

    /// FULL E2E: hold a surface cap → migrate it to a confined child PD →
    /// re-home its surface Endpoint → drive input + present over the Endpoint
    /// through [`PresentTransport`]. The frames the confined child rendered come
    /// back. The glass follows the migrated cap.
    #[test]
    fn a_held_surface_migrates_and_its_glass_follows_to_a_confined_child() {
        let kernel = ProcessKernel::new();

        // ── spawn the CONFINED child surface renderer (its only channels are its
        //    two firmament Endpoints; file/network/exec denied) ──
        let (pd, parent_surf) = kernel
            .spawn_pd_confined_with_surface(vec![], |_client, mut surf, _granted| {
                let mut acc: u64 = 0;
                let mut seq: u64 = 0;
                loop {
                    let cont = serve_one_surface_event(&mut surf, &mut acc, |state, ev| match ev {
                        SurfaceEvent::Input { code } => {
                            *state = state.wrapping_mul(31).wrapping_add(code);
                            seq += 1;
                            SurfaceFrame {
                                seq,
                                digest: render_digest(*state, seq),
                            }
                        }
                        SurfaceEvent::Present { seq: pseq } => {
                            seq = pseq;
                            SurfaceFrame {
                                seq: pseq,
                                digest: render_digest(*state, pseq),
                            }
                        }
                    });
                    if !matches!(cont, Ok(true)) {
                        break;
                    }
                }
                0
            })
            .expect("spawn confined surface child");

        // Service the control socket in the background.
        let k = kernel.clone();
        let mut ctrl = pd.kernel_sock.try_clone().expect("clone control");
        let server = std::thread::spawn(move || while k.serve_one(&mut ctrl).unwrap_or(false) {});

        // ── register the child + its surface Endpoint in the host backing ──
        let mut host = HostPdBacking::new();
        let pd_id = host.register(
            pd.kernel_sock.try_clone().expect("clone host"),
            AuthRequired::Either,
        );
        assert!(host.register_surface(pd_id, parent_surf));

        // ── the AUTHORITY half: a real held surface cap, migrated to HostPd{pd} ──
        let mut bytes = [0u8; 32];
        bytes[0] = 0x5A;
        let held = SurfaceCapability::new(
            SurfaceId(3),
            Capability::surface(CellId::from_bytes(bytes), AuthRequired::Either),
        );
        let migrated = migrate(
            &held,
            &MigrationTarget::HostPd {
                pd: pd_id,
                rights: AuthRequired::Either,
            },
        )
        .expect("migrate re-mints the cap to the confined child");
        // Identity preserved; the cap now names the child PD.
        assert_eq!(migrated.surface(), SurfaceId(3));
        assert!(migrated.authority().target.is_host_pd());

        // ── the GLASS half: drive input + present over the child's Endpoint ──
        let transport = PresentTransport::new(host);

        // input crosses to the child; the frame it rendered returns.
        let f1 = transport
            .route_input(&migrated, 7)
            .expect("input crosses to the confined child");
        let acc = 0u64.wrapping_mul(31).wrapping_add(7);
        assert_eq!(f1.seq, 1);
        assert_eq!(f1.digest, render_digest(acc, 1));

        // a present renders the child's surface; the OUTPUT comes back.
        let f2 = transport
            .present(&migrated, 99)
            .expect("present renders the migrated surface in the child");
        assert_eq!(f2.seq, 99);
        assert_eq!(f2.digest, render_digest(acc, 99));

        // teardown: drop the transport (closes the surface Endpoint) → child EOFs,
        // then reap the child (PdProcess::join drops the kernel sock + waitpids).
        drop(transport);
        let code = pd.join().expect("reap confined surface child");
        server.join().unwrap();
        assert_eq!(code, 0);

        println!(
            "E2E: a held surface MIGRATED to a confined child PD and its GLASS \
             followed — input + present crossed the firmament Endpoint, the \
             child rendered, the frames returned. (づ｡◕‿‿◕｡)づ"
        );
    }
}
