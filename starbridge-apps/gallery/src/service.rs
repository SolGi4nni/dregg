//! # gallery — the curation lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The sealed-submission curation lifecycle re-expressed as a
//! CELLS-AS-SERVICE-OBJECTS citizen (after the `starbridge-bounty-board`,
//! `starbridge-kvstore`, and `starbridge-escrow-market` exemplars). A new
//! `service` module on the existing crate: it publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the gallery lifecycle through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch
//! layer that sits *slightly above* the effect-VM and desugars a method call to
//! the ordinary verified effects it names. There is **no `Effect::Invoke`**, no
//! kernel change, no new circuit rung: the kernel and the light client keep
//! seeing only the [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical lifecycle program
//!
//! The service face installs the IDENTICAL canonical
//! [`gallery_cell_program`](crate::gallery_cell_program) the
//! [`FactoryDescriptor`](crate::gallery_factory_descriptor) bakes into every
//! factory-born gallery cell. So the lifecycle teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born cell's turns:
//!
//! | Slot               | Caveat                     | Bites on |
//! |--------------------|----------------------------|----------|
//! | `SUBMIT_BASE + i`  | `WriteOnce`                | `submit` (a committed sealed piece is frozen — the anti-tamper tooth) |
//! | `PHASE`            | `Monotonic` / `StrictMonotonic` | every turn (`SUBMISSION → REVEAL → CURATED`, only advances) |
//! | `CURATOR`          | `WriteOnce`                | bound at seed |
//! | `FEATURED` / `FEATURED_HASH` | `WriteOnce`      | `curate` (the featured choice freezes once announced) |
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method              | semantics                 | auth        | args                  | desugars to |
//! |---------------------|---------------------------|-------------|-----------------------|-------------|
//! | `submit`            | [`Semantics::Replayable`] | `Signature` | `(seal)`              | `SetField(SUBMIT_BASE+i), EmitEvent` |
//! | `close_submissions` | [`Semantics::Replayable`] | `Signature` | `()`                  | `SetField(PHASE=REVEAL), EmitEvent` |
//! | `reveal`            | [`Semantics::Replayable`] | `Signature` | `(artist, piece)`     | `EmitEvent` |
//! | `curate`            | [`Semantics::Replayable`] | `Signature` | `(featured, featured_hash)` | `SetField(FEATURED, FEATURED_HASH, PHASE=CURATED), EmitEvent` |
//! | `view`              | [`Semantics::Serviced`]   | `None`      | `()`                  | — (the named OFE seam: a pure read, no turn) |
//!
//! `submit`/`close_submissions`/`reveal`/`curate` are **replayable**: they
//! desugar (via `invoke()`) to a verified turn whose post-state the executor
//! checks against the gallery [`CellProgram`](dregg_cell::program::CellProgram).
//! `view` is **serviced**: the gallery's committed lifecycle state IS the answer
//! (it rides the OFE cross-cell-read), so `invoke()` refuses to desugar it and
//! names the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). Swapping a committed sealed submission is
//! a `WriteOnce(SUBMIT_BASE + i)` EXECUTOR REFUSAL, and a phase that rewinds /
//! does not advance is a `StrictMonotonic(PHASE)` EXECUTOR REFUSAL — the protocol
//! layer, not a userspace check.

use dregg_app_framework::{
    AppCipherclerk, CellId, Effect, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, Turn, field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;

use crate::{Seal, close_submissions_effects, curate_effects, reveal_effects, submit_effects};

// =============================================================================
// Method names — exactly the `MethodIs` symbols of `gallery_cell_program`.
// =============================================================================

/// The `submit` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// commit a sealed submission into the next free `WriteOnce` board slot.
pub const METHOD_SUBMIT: &str = "submit";
/// The `close_submissions` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: close the call (`PHASE SUBMISSION → REVEAL`, `StrictMonotonic`).
pub const METHOD_CLOSE_SUBMISSIONS: &str = "close_submissions";
/// The `reveal` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// open a committed submission (record the revealed `(artist, piece)`).
pub const METHOD_REVEAL: &str = "reveal";
/// The `curate` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// feature a piece (`FEATURED` / `FEATURED_HASH` `WriteOnce`, `PHASE → CURATED`).
pub const METHOD_CURATE: &str = "curate";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the gallery's committed lifecycle state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The gallery's first-class typed interface** — the five methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the gallery wants its four mutators
/// `Signature`-gated and `view` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // submit(seal): commit a sealed submission.
        mutator(METHOD_SUBMIT, 1),
        // close_submissions(): close the call (SUBMISSION → REVEAL).
        mutator(METHOD_CLOSE_SUBMISSIONS, 0),
        // reveal(artist, piece): open a committed submission.
        mutator(METHOD_REVEAL, 2),
        // curate(featured, featured_hash): feature a piece (REVEAL → CURATED).
        mutator(METHOD_CURATE, 2),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the gallery's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the gallery's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed gallery cell** — bundles the gallery cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor
/// ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct GalleryService {
    /// The gallery cell this handle drives.
    pub cell: CellId,
    /// The gallery's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl GalleryService {
    /// A handle to the gallery cell `cell`, carrying the gallery's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        GalleryService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `submit(seal)`** — commit a sealed submission into board `slot`
    /// (a fresh `WriteOnce` slot, admitted from zero on this turn). Routes through
    /// the verified DFA, cap-gates on `Signature`, and desugars to the underlying
    /// [`submit_effects`](crate::submit_effects) targeting the `submit` method
    /// symbol. A later swap of the committed slot is a `WriteOnce` EXECUTOR
    /// refusal (the anti-tamper tooth).
    pub fn submit(
        &self,
        cipherclerk: &AppCipherclerk,
        slot: usize,
        seal: Seal,
        authority: InvokeAuthority,
    ) -> Result<Turn, GalleryServiceError> {
        let effects = submit_effects(self.cell, slot, &seal);
        self.invoke(cipherclerk, METHOD_SUBMIT, vec![seal], effects, authority)
    }

    /// **Invoke `close_submissions()`** — close the call: advance `PHASE
    /// SUBMISSION → REVEAL`. The executor re-enforces `StrictMonotonic(PHASE)` (a
    /// rewind / no-advance is refused).
    pub fn close_submissions(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, GalleryServiceError> {
        let effects = close_submissions_effects(self.cell);
        self.invoke(
            cipherclerk,
            METHOD_CLOSE_SUBMISSIONS,
            vec![],
            effects,
            authority,
        )
    }

    /// **Invoke `reveal(artist, piece)`** — open a committed submission, recording
    /// the revealed `(artist, piece)` (the phase is not advanced).
    pub fn reveal(
        &self,
        cipherclerk: &AppCipherclerk,
        artist: FieldElement,
        piece: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, GalleryServiceError> {
        let effects = reveal_effects(self.cell, artist, piece);
        self.invoke(
            cipherclerk,
            METHOD_REVEAL,
            vec![artist, field_from_u64(piece)],
            effects,
            authority,
        )
    }

    /// **Invoke `curate(featured, featured_hash)`** — feature a piece: write
    /// `FEATURED` / `FEATURED_HASH` (both `WriteOnce`, admitted from zero), advance
    /// `PHASE REVEAL → CURATED`. The executor re-enforces `StrictMonotonic(PHASE)`
    /// + the `WriteOnce` result registers.
    pub fn curate(
        &self,
        cipherclerk: &AppCipherclerk,
        featured: FieldElement,
        featured_hash: Seal,
        authority: InvokeAuthority,
    ) -> Result<Turn, GalleryServiceError> {
        let effects = curate_effects(self.cell, featured, &featured_hash);
        self.invoke(
            cipherclerk,
            METHOD_CURATE,
            vec![featured, featured_hash],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the gallery's committed lifecycle
    /// state), not a replay desugar. This method exists to make the seam legible
    /// (and testable): a serviced read is not a turn, and `invoke()` will not
    /// pretend otherwise. To actually READ the gallery, read the committed state
    /// at its slots ([`PHASE_SLOT`](crate::PHASE_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, GalleryServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this gallery's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, GalleryServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(GalleryServiceError::Refused)
    }
}

/// Why a [`GalleryService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GalleryServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for GalleryServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GalleryServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for GalleryServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::submit_slot;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [
            METHOD_SUBMIT,
            METHOD_CLOSE_SUBMISSIONS,
            METHOD_REVEAL,
            METHOD_CURATE,
        ] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn the_published_interface_names_the_same_methods() {
        // The published descriptor's methods are exactly the lifecycle vocabulary.
        let iface = interface_descriptor();
        for m in [
            METHOD_SUBMIT,
            METHOD_CLOSE_SUBMISSIONS,
            METHOD_REVEAL,
            METHOD_CURATE,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn unauthorized_submit_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GalleryService::new(cclerk.cell_id());
        // `submit` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.submit(&cclerk, submit_slot(0), [0x33; 32], InvokeAuthority::None),
            Err(GalleryServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GalleryService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(GalleryServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
