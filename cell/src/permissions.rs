use serde::{Deserialize, Serialize};

/// What authorization is required to perform an action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthRequired {
    /// Always allowed, no authorization needed.
    None,
    /// Ed25519 signature from the cell's public key required.
    Signature,
    /// A ZK proof matching the cell's verification key required.
    Proof,
    /// Either a signature OR a proof suffices.
    Either,
    /// Permanently locked — this action can never be performed.
    Impossible,
    /// App-defined authorization: requires `Authorization::Custom` whose
    /// `WitnessedPredicate` has kind `Custom { vk_hash }` matching this
    /// `vk_hash`. The verifier identified by `vk_hash` must be
    /// registered in the executor's `WitnessedPredicateRegistry`
    /// (per AUTHORIZATION-CUSTOM-DESIGN §10.4).
    Custom { vk_hash: [u8; 32] },
}

impl AuthRequired {
    /// Check if a given authorization kind satisfies this requirement.
    ///
    /// `AuthRequired::Custom` is NOT satisfied by `AuthKind::Signature` or
    /// `AuthKind::Proof` — it requires `Authorization::Custom` with a
    /// matching `vk_hash`, which the executor checks directly against the
    /// predicate (the `AuthKind` lattice does not carry vk_hash). Callers
    /// that need to enforce `Custom` go through the executor's
    /// per-variant check, not this method.
    pub fn is_satisfied_by(&self, provided: &AuthKind) -> bool {
        match self {
            AuthRequired::None => true,
            AuthRequired::Signature => matches!(provided, AuthKind::Signature),
            AuthRequired::Proof => matches!(provided, AuthKind::Proof),
            AuthRequired::Either => {
                matches!(provided, AuthKind::Signature | AuthKind::Proof)
            }
            AuthRequired::Impossible => false,
            AuthRequired::Custom { .. } => false,
        }
    }

    /// Returns true if this requirement is strictly narrower (more restrictive)
    /// than or equal to `other`.
    ///
    /// `Custom { vk_hash }` is comparable only with itself (vk_hash equality)
    /// or with `Impossible`/`None`; two different `Custom` requirements are
    /// incomparable (neither narrower nor equal).
    pub fn is_narrower_or_equal(&self, other: &AuthRequired) -> bool {
        match (self, other) {
            // Impossible is the most restrictive
            (AuthRequired::Impossible, _) => true,
            (_, AuthRequired::Impossible) => false,
            // None is the least restrictive
            (_, AuthRequired::None) => true,
            (AuthRequired::None, _) => false,
            // Proof/Signature are narrower than Either
            (AuthRequired::Proof, AuthRequired::Either) => true,
            (AuthRequired::Signature, AuthRequired::Either) => true,
            // Custom is narrower-or-equal only to an identical Custom
            // (vk_hash equality). Different vk_hashes are incomparable.
            (AuthRequired::Custom { vk_hash: a }, AuthRequired::Custom { vk_hash: b }) => a == b,
            // Custom and Signature/Proof/Either are incomparable.
            (AuthRequired::Custom { .. }, _) | (_, AuthRequired::Custom { .. }) => false,
            // Same level
            (a, b) => a == b,
        }
    }
}

/// A **credential rung** — an authorization a holder can actually PRESENT, and the
/// only thing [`Requirement::AtLeast`] may demand.
///
/// This is deliberately NOT [`AuthRequired`]. The two degenerate rungs of that
/// lattice are meaningless as the payload of an "at least this much" demand, and
/// spelling them there is exactly how the affordance layer got two opposite
/// readings of the same value:
///
/// * [`AuthRequired::None`] is the lattice **TOP**. `AtLeast(None)` would be
///   satisfied only by a holder of `None` itself — i.e. it is [`Requirement::Root`]
///   wearing a name that reads like "no requirement".
/// * [`AuthRequired::Impossible`] is the lattice **BOTTOM**, narrower than
///   everything, so `AtLeast(Impossible)` is satisfied by *every* holder — i.e. it
///   is [`Requirement::Public`] wearing a name that reads like "never".
///
/// Neither is spellable here. `Public`, `Root` and `Never` are their own
/// constructors on [`Requirement`], so the reading is on the face of the value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Credential {
    /// An Ed25519 signature from the target's key.
    Signature,
    /// A ZK proof against the target's verification key.
    Proof,
    /// Either a signature OR a proof.
    Either,
    /// An app-defined witnessed predicate identified by `vk_hash` (see
    /// [`AuthRequired::Custom`]).
    Custom { vk_hash: [u8; 32] },
}

impl Credential {
    /// The [`AuthRequired`] lattice element this credential denotes — the value the
    /// attenuation comparison (`is_narrower_or_equal`) is run against.
    pub fn as_auth_required(&self) -> AuthRequired {
        match self {
            Credential::Signature => AuthRequired::Signature,
            Credential::Proof => AuthRequired::Proof,
            Credential::Either => AuthRequired::Either,
            Credential::Custom { vk_hash } => AuthRequired::Custom { vk_hash: *vk_hash },
        }
    }

    /// The credential rung an [`AuthRequired`] denotes, or `None` for the two
    /// degenerate ends of the lattice (`AuthRequired::None` = TOP,
    /// `AuthRequired::Impossible` = BOTTOM) — which are [`Requirement::Root`] and
    /// [`Requirement::Public`] respectively and must be named as such.
    pub fn of_auth_required(auth: &AuthRequired) -> Option<Credential> {
        match auth {
            AuthRequired::Signature => Some(Credential::Signature),
            AuthRequired::Proof => Some(Credential::Proof),
            AuthRequired::Either => Some(Credential::Either),
            AuthRequired::Custom { vk_hash } => Some(Credential::Custom { vk_hash: *vk_hash }),
            AuthRequired::None | AuthRequired::Impossible => None,
        }
    }
}

/// **What a holder must HOLD to be admitted** — the requirement side of the
/// authorization lattice, as its own type.
///
/// # Why this is not `AuthRequired`
///
/// [`AuthRequired`] answers "what must be PRESENTED to mutate this cell", and in
/// that role [`AuthRequired::None`] correctly means *ungated*
/// ([`Permissions::access`] defaults to it). The affordance layer reused the same
/// enum to answer a DIFFERENT question — "how much authority must a viewer already
/// hold" — where the comparison is `is_attenuation(held, required)` and `None` is
/// the lattice TOP, i.e. the value only a root holder clears. One enum, two
/// opposite readings of one variant, and the workspace split on which it meant.
///
/// `Requirement` makes the confusion unrepresentable rather than merely fixed:
/// `Public` and `Root` are separate constructors and `AtLeast` cannot carry either.
///
/// The single decision function is [`Requirement::satisfied_by`]; every gate in the
/// workspace must return exactly what it returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Requirement {
    /// **Ungated.** Every holder is admitted, including one holding nothing at all.
    /// (The guarantee that still applies to the resulting action — conservation,
    /// non-amplification, a cell's own `Permissions` — is enforced by the executor,
    /// not by this gate.)
    Public,
    /// The holder must hold **at least** this credential on the attenuation lattice:
    /// `required ⊆ held`, i.e. `credential.as_auth_required().is_narrower_or_equal(held)`.
    /// Incomparable authorities do NOT clear it (a `Proof` holder does not clear
    /// `AtLeast(Signature)`) — this is the real lattice, not a numeric rank.
    AtLeast(Credential),
    /// **Root only.** Satisfied by a holder of the lattice TOP
    /// ([`AuthRequired::None`]) and by nobody else.
    Root,
    /// **Nothing clears it.** Fail-closed; no holder is ever admitted.
    Never,
}

impl Requirement {
    /// **THE decision function.** Is a holder of `held` authority admitted by this
    /// requirement?
    ///
    /// Every affordance cap-gate in the workspace is this function; a gate that
    /// computes its own answer is a gate that can drift from the other four.
    pub fn satisfied_by(&self, held: &AuthRequired) -> bool {
        match self {
            Requirement::Public => true,
            // `is_attenuation(held, required)` = `required.is_narrower_or_equal(held)`.
            Requirement::AtLeast(credential) => {
                credential.as_auth_required().is_narrower_or_equal(held)
            }
            Requirement::Root => matches!(held, AuthRequired::None),
            Requirement::Never => false,
        }
    }

    /// **The one bridge from a surface that has NOT migrated.**
    ///
    /// [`crate::interface::MethodSig::auth_required`] is documented as "what a caller
    /// must hold to invoke this method" — the HOLD reading, so `None` there is the
    /// lattice TOP (root), not "ungated". That descriptor is committed shape and is
    /// still typed `AuthRequired`; this is the single named site that reads it as a
    /// requirement, so the reading is stated once rather than re-guessed per caller.
    ///
    /// It is deliberately NOT a `From` impl: an implicit conversion is how the two
    /// readings got mixed in the first place. Migrating `MethodSig` onto `Requirement`
    /// retires this function.
    pub fn from_interface_auth(auth: &AuthRequired) -> Requirement {
        match auth {
            // ⚑ `None` IS `Public` HERE, NOT `Root`, AND THE FIELD DECIDES IT — NOT THE
            // LATTICE. This mapping was `Root` for one commit (b3ef43204) and produced a
            // live contradiction two lines apart in `service_explorer.rs`: the LABEL said
            // root-only while the GATE beside it admitted everyone, with a committed test
            // pinning both. Caught by the wave audit.
            //
            // The deciding evidence is the field's own definition, not a preference.
            // `MethodSig::auth_required` (cell/src/interface.rs:141) is "what a caller must
            // hold to invoke this method", and `MethodSig::replayable` — the constructor for
            // EVERY auto-derived method-guard — sets it to `None` and calls that the
            // "baseline". A baseline is a floor. Reading it as the lattice TOP would make
            // every auto-derived method root-only, which is the opposite of what the
            // constructor that writes it means, and would have silently re-gated the whole
            // interface surface.
            //
            // This is why the ambiguity was worth a type: `AuthRequired::None` genuinely
            // means "ungated" in one field and "the widest authority" in another, and no
            // single conversion is right for both. `from_interface_auth` is named for, and
            // has only ever been called on, the INTERFACE field (two call sites:
            // starbridge-v2 service_explorer, deos-js-runtime world). It is not a general
            // `AuthRequired -> Requirement` cast and must not become one — an affordance's
            // `required_rights` takes the opposite reading and has its own path.
            AuthRequired::None => Requirement::Public,
            AuthRequired::Impossible => Requirement::Never,
            other => Requirement::AtLeast(
                Credential::of_auth_required(other).expect("None/Impossible are handled above"),
            ),
        }
    }

    /// A short stable label (`"public"`, `"signature"`, `"proof"`, `"either"`,
    /// `"custom:<64 hex>"`, `"root"`, `"never"`) — the wire/UI spelling, and the
    /// inverse of [`Requirement::parse_label`] on EVERY variant.
    ///
    /// ⚑ The `Custom` rung carries its `vk_hash` in the label. It used to emit a bare
    /// `"custom"`, which no parser accepted — so a `Custom`-gated affordance's
    /// descriptor could be EMITTED and never read back (it failed closed at
    /// `ScaffoldError::UnknownRights`). A bare `"custom"` cannot round-trip even in
    /// principle: `AtLeast(Custom { vk_hash })` NAMES a registered verifier
    /// (`WitnessedPredicateRegistry`), and two `Custom` requirements with different
    /// `vk_hash`es are INCOMPARABLE on the lattice — dropping the hash does not lose
    /// detail, it loses the identity of the gate.
    pub fn label(&self) -> String {
        match self {
            Requirement::Public => "public".to_string(),
            Requirement::AtLeast(Credential::Signature) => "signature".to_string(),
            Requirement::AtLeast(Credential::Proof) => "proof".to_string(),
            Requirement::AtLeast(Credential::Either) => "either".to_string(),
            Requirement::AtLeast(Credential::Custom { vk_hash }) => {
                format!("{CUSTOM_LABEL_PREFIX}{}", hex32(vk_hash))
            }
            Requirement::Root => "root".to_string(),
            Requirement::Never => "never".to_string(),
        }
    }

    /// Parse a [`Requirement::label`]. `None` for an unknown label.
    ///
    /// Two spellings are deliberately REFUSED rather than reinterpreted:
    ///
    /// * `"none"` — the old string meant either `public` or `root` depending on who
    ///   read it, so a descriptor carrying it must be rewritten.
    /// * a bare `"custom"` — it names no verifier, and inventing a `vk_hash` to
    ///   accept it would manufacture a gate nobody declared. Only
    ///   `"custom:<64 hex>"` parses.
    pub fn parse_label(label: &str) -> Option<Requirement> {
        match label {
            "public" => Some(Requirement::Public),
            "signature" => Some(Requirement::AtLeast(Credential::Signature)),
            "proof" => Some(Requirement::AtLeast(Credential::Proof)),
            "either" => Some(Requirement::AtLeast(Credential::Either)),
            "root" => Some(Requirement::Root),
            "never" => Some(Requirement::Never),
            other => other
                .strip_prefix(CUSTOM_LABEL_PREFIX)
                .and_then(unhex32)
                .map(|vk_hash| Requirement::AtLeast(Credential::Custom { vk_hash })),
        }
    }
}

/// The `Custom` rung's label prefix. The 64 hex chars after it are the `vk_hash`;
/// see [`Requirement::label`] for why a bare `"custom"` is not a spelling.
const CUSTOM_LABEL_PREFIX: &str = "custom:";

/// Lower-case hex of a 32-byte hash — the `custom:` label payload.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push(char::from_digit((b >> 4) as u32, 16).expect("nibble < 16"));
        out.push(char::from_digit((b & 0x0f) as u32, 16).expect("nibble < 16"));
    }
    out
}

/// Inverse of [`hex32`]. `None` unless `s` is EXACTLY 64 hex digits — a short, long
/// or non-hex payload names no verifier and must refuse, not truncate.
fn unhex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    let mut chars = s.chars();
    for slot in out.iter_mut() {
        let hi = chars.next()?.to_digit(16)?;
        let lo = chars.next()?.to_digit(16)?;
        *slot = ((hi << 4) | lo) as u8;
    }
    Some(out)
}

impl std::fmt::Display for Requirement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.label())
    }
}

/// The kind of authorization actually provided.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthKind {
    /// An Ed25519 signature was provided.
    Signature,
    /// A ZK proof was provided.
    Proof,
}

/// Permissions governing what actions require what authorization for a cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Permissions {
    /// Send computrons or capabilities to another cell.
    pub send: AuthRequired,
    /// Receive computrons or capabilities from another cell.
    pub receive: AuthRequired,
    /// Modify the cell's app_state fields.
    pub set_state: AuthRequired,
    /// Modify the cell's permissions (this field).
    pub set_permissions: AuthRequired,
    /// Change the cell's verification key.
    pub set_verification_key: AuthRequired,
    /// Increment the cell's nonce.
    pub increment_nonce: AuthRequired,
    /// Delegate capabilities to child cells.
    pub delegate: AuthRequired,
    /// General access control (catch-all).
    pub access: AuthRequired,
}

impl Permissions {
    /// Default permissions: signature required for everything except receive.
    pub fn default_user() -> Self {
        Permissions {
            send: AuthRequired::Signature,
            receive: AuthRequired::None,
            set_state: AuthRequired::Signature,
            set_permissions: AuthRequired::Signature,
            set_verification_key: AuthRequired::Signature,
            increment_nonce: AuthRequired::Signature,
            delegate: AuthRequired::Signature,
            access: AuthRequired::None,
        }
    }

    /// Sovereign cell default permissions.
    ///
    /// Like `default_user()` but with `set_verification_key: Proof` (self-upgrading).
    /// This implements the VK upgrade strategy from the sovereign cell design:
    /// the current circuit must produce a proof authorizing its own replacement.
    pub fn sovereign_default() -> Self {
        Permissions {
            send: AuthRequired::Signature,
            receive: AuthRequired::None,
            set_state: AuthRequired::Signature,
            set_permissions: AuthRequired::Signature,
            set_verification_key: AuthRequired::Proof,
            increment_nonce: AuthRequired::Signature,
            delegate: AuthRequired::Signature,
            access: AuthRequired::None,
        }
    }

    /// Locked-down permissions: proof required for everything, receive is impossible.
    pub fn zkapp() -> Self {
        Permissions {
            send: AuthRequired::Proof,
            receive: AuthRequired::None,
            set_state: AuthRequired::Proof,
            set_permissions: AuthRequired::Proof,
            set_verification_key: AuthRequired::Proof,
            increment_nonce: AuthRequired::Proof,
            delegate: AuthRequired::Proof,
            access: AuthRequired::Proof,
        }
    }

    /// Completely locked: nothing can be done.
    pub fn frozen() -> Self {
        Permissions {
            send: AuthRequired::Impossible,
            receive: AuthRequired::Impossible,
            set_state: AuthRequired::Impossible,
            set_permissions: AuthRequired::Impossible,
            set_verification_key: AuthRequired::Impossible,
            increment_nonce: AuthRequired::Impossible,
            delegate: AuthRequired::Impossible,
            access: AuthRequired::Impossible,
        }
    }

    /// **Owner-gated worker permissions — the OWNER-SIGNED ENVELOPE keystone.**
    ///
    /// For a host-keyed worker grain cell (its OWN ed25519 key is the host's, so
    /// `AuthRequired::Signature` gates are host-satisfiable), this routes the
    /// authority-WIDENING actions — `set_permissions`, `delegate`, and
    /// `set_verification_key` — to `AuthRequired::Custom { vk_hash }`, where
    /// `owner_vk_hash` is derived from the renter/owner key
    /// (`dregg_turn::executor::owner_envelope::owner_envelope_vk`, itself
    /// `RenterAnchor.pubkey`). Only a turn carrying an owner ed25519 signature
    /// (verified by the registered `OwnerEnvelopeSigVerifier`) can mutate the
    /// worker's c-list or relax its gates — the host, lacking the owner key,
    /// cannot self-grant a broader cap through the executor.
    ///
    /// The host still DRIVES the grain: `set_state` (scratch/metered slots),
    /// `send`, and `increment_nonce` stay at `AuthRequired::Signature` (its
    /// legitimate job, constrained elsewhere by the mandate program). The gate is
    /// self-protecting — changing `set_permissions` here itself requires the owner
    /// key — so once stamped at rent (owner active) the host cannot un-stamp it
    /// through the executor.
    ///
    /// All three widening slots carry the SAME `owner_vk_hash` on purpose: the
    /// executor's `verify_custom_authorization` pins the FIRST `Custom` slot it
    /// finds, so a single owner vk keeps the pin unambiguous.
    pub fn enveloped_worker(owner_vk_hash: [u8; 32]) -> Self {
        Permissions {
            send: AuthRequired::Signature,
            receive: AuthRequired::None,
            set_state: AuthRequired::Signature,
            set_permissions: AuthRequired::Custom {
                vk_hash: owner_vk_hash,
            },
            set_verification_key: AuthRequired::Custom {
                vk_hash: owner_vk_hash,
            },
            increment_nonce: AuthRequired::Signature,
            delegate: AuthRequired::Custom {
                vk_hash: owner_vk_hash,
            },
            access: AuthRequired::None,
        }
    }

    /// Check if a specific action is authorized given a provided auth kind.
    pub fn check(&self, action: Action, auth: &AuthKind) -> bool {
        let required = self.for_action(action);
        required.is_satisfied_by(auth)
    }

    /// Get the AuthRequired for a specific action.
    pub fn for_action(&self, action: Action) -> &AuthRequired {
        match action {
            Action::Send => &self.send,
            Action::Receive => &self.receive,
            Action::SetState => &self.set_state,
            Action::SetPermissions => &self.set_permissions,
            Action::SetVerificationKey => &self.set_verification_key,
            Action::IncrementNonce => &self.increment_nonce,
            Action::Delegate => &self.delegate,
            Action::Access => &self.access,
        }
    }
}

impl Default for Permissions {
    fn default() -> Self {
        Self::default_user()
    }
}

/// Enumeration of actions that can be performed on a cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action {
    Send,
    Receive,
    SetState,
    SetPermissions,
    SetVerificationKey,
    IncrementNonce,
    Delegate,
    Access,
}

#[cfg(test)]
mod requirement_tests {
    use super::*;

    /// Every `AuthRequired` a holder can carry — the exhaustive domain the gate
    /// oracles sweep.
    pub(crate) const ALL_HELD: [AuthRequired; 6] = [
        AuthRequired::None,
        AuthRequired::Signature,
        AuthRequired::Proof,
        AuthRequired::Either,
        AuthRequired::Impossible,
        AuthRequired::Custom { vk_hash: [9u8; 32] },
    ];

    #[test]
    fn public_and_root_are_the_two_opposite_readings_and_they_differ() {
        // The entire reason this type exists: `AuthRequired::None` in requirement
        // position meant BOTH of these. They are not the same predicate — a
        // `Signature` holder clears one and not the other.
        let sig = AuthRequired::Signature;
        assert!(Requirement::Public.satisfied_by(&sig));
        assert!(!Requirement::Root.satisfied_by(&sig));

        // And they differ on every holding EXCEPT the lattice top itself.
        for held in ALL_HELD {
            let public = Requirement::Public.satisfied_by(&held);
            let root = Requirement::Root.satisfied_by(&held);
            assert!(public, "Public admits everyone, including {held:?}");
            assert_eq!(
                root,
                held == AuthRequired::None,
                "Root admits exactly the lattice top, not {held:?}"
            );
        }
    }

    #[test]
    fn at_least_is_the_attenuation_lattice_not_a_numeric_rank() {
        let sig = Requirement::AtLeast(Credential::Signature);
        let either = Requirement::AtLeast(Credential::Either);

        // Signature ⊆ Signature, Signature ⊆ Either, Signature ⊆ None(top).
        assert!(sig.satisfied_by(&AuthRequired::Signature));
        assert!(sig.satisfied_by(&AuthRequired::Either));
        assert!(sig.satisfied_by(&AuthRequired::None));
        // INCOMPARABLE: a Proof holder does NOT clear a Signature requirement.
        assert!(!sig.satisfied_by(&AuthRequired::Proof));
        assert!(!Requirement::AtLeast(Credential::Proof).satisfied_by(&AuthRequired::Signature));
        // Either ⊄ Signature — the wider demand is refused by the narrower holder.
        assert!(!either.satisfied_by(&AuthRequired::Signature));
        // An `Impossible` holder clears nothing.
        assert!(!sig.satisfied_by(&AuthRequired::Impossible));
        assert!(!either.satisfied_by(&AuthRequired::Impossible));
    }

    #[test]
    fn never_admits_nobody_not_even_root() {
        for held in ALL_HELD {
            assert!(
                !Requirement::Never.satisfied_by(&held),
                "Never must refuse {held:?}"
            );
        }
    }

    #[test]
    fn at_least_cannot_express_public_or_root_because_credential_excludes_them() {
        // The unrepresentability, stated as a test: the two degenerate lattice ends
        // have NO `Credential`, so `AtLeast` cannot be handed either of them.
        assert_eq!(Credential::of_auth_required(&AuthRequired::None), None);
        assert_eq!(
            Credential::of_auth_required(&AuthRequired::Impossible),
            None
        );
        // Every other rung round-trips.
        for held in ALL_HELD {
            match Credential::of_auth_required(&held) {
                Some(c) => assert_eq!(c.as_auth_required(), held),
                None => assert!(matches!(
                    held,
                    AuthRequired::None | AuthRequired::Impossible
                )),
            }
        }
    }

    #[test]
    fn labels_round_trip_and_there_is_no_none_spelling() {
        for req in [
            Requirement::Public,
            Requirement::AtLeast(Credential::Signature),
            Requirement::AtLeast(Credential::Proof),
            Requirement::AtLeast(Credential::Either),
            Requirement::AtLeast(Credential::Custom {
                vk_hash: [0xC5; 32],
            }),
            Requirement::Root,
            Requirement::Never,
        ] {
            assert_eq!(Requirement::parse_label(&req.label()), Some(req.clone()));
        }
        // The ambiguous old spelling is refused, not reinterpreted.
        assert_eq!(Requirement::parse_label("none"), None);
    }

    #[test]
    fn the_custom_label_carries_the_vk_hash_and_a_bare_custom_is_refused() {
        // ⚑ THE GAP THIS CLOSES: `label()` emitted a bare `"custom"` that NO parser
        // accepted, so a `Custom`-gated affordance's descriptor was write-only.
        let a = Requirement::AtLeast(Credential::Custom {
            vk_hash: [0x0A; 32],
        });
        let b = Requirement::AtLeast(Credential::Custom {
            vk_hash: [0x0B; 32],
        });

        // The label NAMES the verifier — it is not the constant string `"custom"`.
        assert_eq!(a.label(), format!("custom:{}", "0a".repeat(32)));
        assert_ne!(
            a.label(),
            b.label(),
            "two Custom requirements are INCOMPARABLE on the lattice; one shared \
             label would collapse two different gates into one descriptor"
        );
        assert!(!a.satisfied_by(&AuthRequired::Custom {
            vk_hash: [0x0B; 32]
        }));

        // And the parse is by vk_hash, not by the word.
        assert_eq!(Requirement::parse_label(&a.label()), Some(a));
        assert_eq!(Requirement::parse_label(&b.label()), Some(b));

        // A payload that names no verifier REFUSES rather than inventing one — the
        // same doctrine as `"none"`.
        assert_eq!(Requirement::parse_label("custom"), None);
        assert_eq!(Requirement::parse_label("custom:"), None);
        assert_eq!(
            Requirement::parse_label(&format!("custom:{}", "0a".repeat(31))),
            None
        );
        assert_eq!(
            Requirement::parse_label(&format!("custom:{}", "0a".repeat(33))),
            None
        );
        assert_eq!(
            Requirement::parse_label(&format!("custom:{}zz", "0a".repeat(31))),
            None
        );
    }
}
