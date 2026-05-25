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
