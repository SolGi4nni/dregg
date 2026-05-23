//! EROS-style Object Factories for pyana.
//!
//! A Factory is a CellProgram that constrains what new cells it can create.
//! The factory's [`FactoryDescriptor`] IS the constructor transparency — anyone
//! can inspect exactly what capabilities the factory grants to its creations,
//! what programs it installs, and what initial state it sets.
//!
//! Factories work in all modes (sovereign, hosted, federated): same VK, same
//! circuit, different verification venue.

use serde::{Deserialize, Serialize};

use crate::cell::CellMode;
use crate::id::CellId;
use crate::permissions::AuthRequired;

/// A factory descriptor: metadata about what a factory creates.
///
/// This is inspectable by anyone without running the circuit. It describes the
/// complete "constructor contract" — what the factory is allowed to produce.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoryDescriptor {
    /// The factory's own program VK hash (identifies the factory).
    pub factory_vk: [u8; 32],
    /// What program (if any) is installed on created cells.
    pub child_program_vk: Option<[u8; 32]>,
    /// Maximum capabilities the factory can grant to created cells.
    pub allowed_cap_templates: Vec<CapTemplate>,
    /// Initial field constraints (which fields are set, value ranges).
    pub field_constraints: Vec<FieldConstraint>,
    /// Whether created cells are sovereign or hosted.
    pub default_mode: CellMode,
    /// Resource budget: max cells this factory can create per epoch.
    pub creation_budget: Option<u64>,
}

impl FactoryDescriptor {
    /// Compute the BLAKE3 hash of this descriptor (content-addressed identity).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-factory-descriptor-v1");
        hasher.update(&self.factory_vk);
        match &self.child_program_vk {
            Some(vk) => {
                hasher.update(&[1u8]);
                hasher.update(vk);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        hasher.update(&(self.allowed_cap_templates.len() as u64).to_le_bytes());
        for tmpl in &self.allowed_cap_templates {
            hasher.update(&tmpl.hash());
        }
        hasher.update(&(self.field_constraints.len() as u64).to_le_bytes());
        for fc in &self.field_constraints {
            hasher.update(&fc.hash());
        }
        let mode_byte = match self.default_mode {
            CellMode::Hosted => 0u8,
            CellMode::Sovereign => 1u8,
        };
        hasher.update(&[mode_byte]);
        match self.creation_budget {
            Some(b) => {
                hasher.update(&[1u8]);
                hasher.update(&b.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Validate that a proposed creation is within this descriptor's constraints.
    ///
    /// Returns `Ok(())` if all constraints pass, or an error describing the violation.
    pub fn validate_creation(&self, params: &FactoryCreationParams) -> Result<(), FactoryError> {
        // Check child program VK.
        if self.child_program_vk != params.program_vk {
            return Err(FactoryError::ProgramMismatch {
                expected: self.child_program_vk,
                got: params.program_vk,
            });
        }

        // Check mode.
        if self.default_mode != params.mode {
            return Err(FactoryError::ModeMismatch {
                expected: self.default_mode.clone(),
                got: params.mode.clone(),
            });
        }

        // Check capabilities are within templates.
        for (i, cap) in params.initial_caps.iter().enumerate() {
            if !self.cap_within_templates(cap) {
                return Err(FactoryError::CapabilityOutsideTemplate { cap_index: i });
            }
        }

        // Check field constraints.
        for constraint in &self.field_constraints {
            constraint.check(&params.initial_fields)?;
        }

        Ok(())
    }

    /// Check that a capability grant is within at least one template.
    fn cap_within_templates(&self, cap: &CapGrant) -> bool {
        self.allowed_cap_templates.iter().any(|tmpl| {
            // Target must match.
            let target_ok = match &tmpl.target {
                CapTarget::Any => true,
                CapTarget::SelfCell => cap.target == CapTarget::SelfCell,
                CapTarget::Specific(id) => cap.target == CapTarget::Specific(*id),
            };
            // Permissions must be no broader than template.
            let perm_ok = cap
                .max_permissions
                .is_narrower_or_equal(&tmpl.max_permissions);
            // Attenuatable only if template allows it.
            let atten_ok = !cap.attenuatable || tmpl.attenuatable;
            target_ok && perm_ok && atten_ok
        })
    }
}

/// A capability template: what the factory is allowed to grant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapTemplate {
    /// Who the capability targets.
    pub target: CapTarget,
    /// Maximum permissions the factory can grant.
    pub max_permissions: AuthRequired,
    /// Whether created cells can further delegate this capability.
    pub attenuatable: bool,
}

impl CapTemplate {
    /// Compute a hash of this template for descriptor hashing.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-cap-template:");
        match &self.target {
            CapTarget::SelfCell => {
                hasher.update(&[0u8]);
            }
            CapTarget::Specific(id) => {
                hasher.update(&[1u8]);
                hasher.update(id.as_bytes());
            }
            CapTarget::Any => {
                hasher.update(&[2u8]);
            }
        }
        let perm_byte = match &self.max_permissions {
            AuthRequired::None => 0u8,
            AuthRequired::Signature => 1u8,
            AuthRequired::Proof => 2u8,
            AuthRequired::Either => 3u8,
            AuthRequired::Impossible => 4u8,
        };
        hasher.update(&[perm_byte]);
        hasher.update(&[self.attenuatable as u8]);
        *hasher.finalize().as_bytes()
    }
}

/// The target of a capability template.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CapTarget {
    /// The created cell itself (self-reference).
    SelfCell,
    /// A specific cell ID.
    Specific(CellId),
    /// Any cell (unrestricted targeting).
    Any,
}

/// A constraint on initial field values.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldConstraint {
    /// A specific field must equal a specific value.
    Equality { field_index: u32, value: u64 },
    /// A specific field must be within a range.
    Range {
        field_index: u32,
        min: u64,
        max: u64,
    },
    /// A specific field must be set (non-zero).
    NonZero { field_index: u32 },
}

impl FieldConstraint {
    /// Compute a hash of this constraint for descriptor hashing.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-field-constraint:");
        match self {
            FieldConstraint::Equality { field_index, value } => {
                hasher.update(&[0u8]);
                hasher.update(&field_index.to_le_bytes());
                hasher.update(&value.to_le_bytes());
            }
            FieldConstraint::Range {
                field_index,
                min,
                max,
            } => {
                hasher.update(&[1u8]);
                hasher.update(&field_index.to_le_bytes());
                hasher.update(&min.to_le_bytes());
                hasher.update(&max.to_le_bytes());
            }
            FieldConstraint::NonZero { field_index } => {
                hasher.update(&[2u8]);
                hasher.update(&field_index.to_le_bytes());
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Check that the initial fields satisfy this constraint.
    fn check(&self, fields: &[(u32, u64)]) -> Result<(), FactoryError> {
        match self {
            FieldConstraint::Equality { field_index, value } => {
                let actual = fields
                    .iter()
                    .find(|(idx, _)| idx == field_index)
                    .map(|(_, v)| *v)
                    .unwrap_or(0);
                if actual != *value {
                    return Err(FactoryError::FieldConstraintViolation {
                        field_index: *field_index,
                        reason: format!("expected {}, got {}", value, actual),
                    });
                }
            }
            FieldConstraint::Range {
                field_index,
                min,
                max,
            } => {
                let actual = fields
                    .iter()
                    .find(|(idx, _)| idx == field_index)
                    .map(|(_, v)| *v)
                    .unwrap_or(0);
                if actual < *min || actual > *max {
                    return Err(FactoryError::FieldConstraintViolation {
                        field_index: *field_index,
                        reason: format!("value {} outside range [{}, {}]", actual, min, max),
                    });
                }
            }
            FieldConstraint::NonZero { field_index } => {
                let actual = fields
                    .iter()
                    .find(|(idx, _)| idx == field_index)
                    .map(|(_, v)| *v)
                    .unwrap_or(0);
                if actual == 0 {
                    return Err(FactoryError::FieldConstraintViolation {
                        field_index: *field_index,
                        reason: "field must be non-zero".to_string(),
                    });
                }
            }
        }
        Ok(())
    }
}

/// A capability grant request in a factory creation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapGrant {
    /// The target of the capability.
    pub target: CapTarget,
    /// What permissions this grants.
    pub max_permissions: AuthRequired,
    /// Whether the created cell can further delegate.
    pub attenuatable: bool,
}

/// Parameters for creating a cell from a factory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoryCreationParams {
    /// The mode of the created cell.
    pub mode: CellMode,
    /// Program VK hash to install on the created cell.
    pub program_vk: Option<[u8; 32]>,
    /// Initial field values (field_index, value).
    pub initial_fields: Vec<(u32, u64)>,
    /// Capabilities to grant to the created cell.
    pub initial_caps: Vec<CapGrant>,
    /// Owner public key for the created cell.
    pub owner_pubkey: [u8; 32],
}

/// Provenance record stored on cells, tracking their creation history.
///
/// This allows anyone to verify who created a cell and under what constraints.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Provenance {
    /// Which factory created this cell (factory VK hash), if any.
    pub created_by_factory: Option<[u8; 32]>,
    /// Hash of the creation STARK proof (for verification).
    pub creation_proof_hash: Option<[u8; 32]>,
    /// The block height at which the cell was created.
    pub creation_height: u64,
}

impl Provenance {
    /// Create a provenance for a cell not created by a factory.
    pub fn genesis(height: u64) -> Self {
        Provenance {
            created_by_factory: None,
            creation_proof_hash: None,
            creation_height: height,
        }
    }

    /// Create a provenance for a factory-created cell.
    pub fn from_factory(factory_vk: [u8; 32], proof_hash: Option<[u8; 32]>, height: u64) -> Self {
        Provenance {
            created_by_factory: Some(factory_vk),
            creation_proof_hash: proof_hash,
            creation_height: height,
        }
    }
}

/// Errors from factory validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactoryError {
    /// The child program VK doesn't match the factory's descriptor.
    ProgramMismatch {
        expected: Option<[u8; 32]>,
        got: Option<[u8; 32]>,
    },
    /// The cell mode doesn't match the factory's descriptor.
    ModeMismatch { expected: CellMode, got: CellMode },
    /// A capability grant is outside the factory's allowed templates.
    CapabilityOutsideTemplate { cap_index: usize },
    /// A field constraint is violated.
    FieldConstraintViolation { field_index: u32, reason: String },
    /// The factory has exceeded its creation budget for this epoch.
    BudgetExceeded { limit: u64, used: u64 },
    /// The factory VK doesn't match the claimed descriptor.
    FactoryVkMismatch { expected: [u8; 32], got: [u8; 32] },
}

impl std::fmt::Display for FactoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FactoryError::ProgramMismatch { expected, got } => {
                write!(
                    f,
                    "child program VK mismatch: expected {:?}, got {:?}",
                    expected, got
                )
            }
            FactoryError::ModeMismatch { expected, got } => {
                write!(
                    f,
                    "cell mode mismatch: expected {:?}, got {:?}",
                    expected, got
                )
            }
            FactoryError::CapabilityOutsideTemplate { cap_index } => {
                write!(
                    f,
                    "capability at index {} outside factory template",
                    cap_index
                )
            }
            FactoryError::FieldConstraintViolation {
                field_index,
                reason,
            } => {
                write!(f, "field {} constraint violated: {}", field_index, reason)
            }
            FactoryError::BudgetExceeded { limit, used } => {
                write!(f, "factory budget exceeded: limit={}, used={}", limit, used)
            }
            FactoryError::FactoryVkMismatch { expected, got } => {
                write!(
                    f,
                    "factory VK mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
        }
    }
}

impl std::error::Error for FactoryError {}

/// A factory registry: tracks deployed factories and their creation counts per epoch.
#[derive(Clone, Debug, Default)]
pub struct FactoryRegistry {
    /// Deployed factory descriptors, keyed by factory VK hash.
    pub descriptors: std::collections::HashMap<[u8; 32], FactoryDescriptor>,
    /// Creation counts per epoch: (factory_vk, epoch) -> count.
    pub creation_counts: std::collections::HashMap<([u8; 32], u64), u64>,
    /// Current epoch number.
    pub current_epoch: u64,
}

impl FactoryRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Deploy a factory, registering its descriptor.
    ///
    /// Returns the factory VK hash as an identifier.
    pub fn deploy(&mut self, descriptor: FactoryDescriptor) -> [u8; 32] {
        let vk = descriptor.factory_vk;
        self.descriptors.insert(vk, descriptor);
        vk
    }

    /// Get a factory descriptor by VK hash.
    pub fn get(&self, factory_vk: &[u8; 32]) -> Option<&FactoryDescriptor> {
        self.descriptors.get(factory_vk)
    }

    /// Record a creation and check budget.
    ///
    /// Returns `Ok(())` if within budget, or an error if exceeded.
    pub fn record_creation(&mut self, factory_vk: &[u8; 32]) -> Result<(), FactoryError> {
        let descriptor =
            self.descriptors
                .get(factory_vk)
                .ok_or(FactoryError::FactoryVkMismatch {
                    expected: *factory_vk,
                    got: [0u8; 32],
                })?;

        if let Some(budget) = descriptor.creation_budget {
            let key = (*factory_vk, self.current_epoch);
            let count = self.creation_counts.entry(key).or_insert(0);
            if *count >= budget {
                return Err(FactoryError::BudgetExceeded {
                    limit: budget,
                    used: *count,
                });
            }
            *count += 1;
        }

        Ok(())
    }

    /// Advance to a new epoch (resets creation counters for previous epochs).
    pub fn advance_epoch(&mut self) {
        self.current_epoch += 1;
        // Retain only current epoch counts.
        let current = self.current_epoch;
        self.creation_counts
            .retain(|(_, epoch), _| *epoch == current);
    }

    /// Validate a creation against the factory descriptor and budget.
    pub fn validate_and_record(
        &mut self,
        factory_vk: &[u8; 32],
        params: &FactoryCreationParams,
    ) -> Result<(), FactoryError> {
        // Get descriptor (clone to avoid borrow conflict).
        let descriptor =
            self.descriptors
                .get(factory_vk)
                .cloned()
                .ok_or(FactoryError::FactoryVkMismatch {
                    expected: *factory_vk,
                    got: [0u8; 32],
                })?;

        // Validate creation params against descriptor.
        descriptor.validate_creation(params)?;

        // Check and record budget.
        self.record_creation(factory_vk)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_factory_vk() -> [u8; 32] {
        *blake3::hash(b"test-factory").as_bytes()
    }

    fn test_child_vk() -> [u8; 32] {
        *blake3::hash(b"test-child-program").as_bytes()
    }

    fn worker_factory_descriptor() -> FactoryDescriptor {
        let coordinator_id = CellId::derive_raw(&[1u8; 32], &[0u8; 32]);
        FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: Some(test_child_vk()),
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::Specific(coordinator_id),
                max_permissions: AuthRequired::None,
                attenuatable: false,
            }],
            field_constraints: vec![
                FieldConstraint::Equality {
                    field_index: 0,
                    value: 42,
                },
                FieldConstraint::Range {
                    field_index: 1,
                    min: 1,
                    max: 100,
                },
            ],
            default_mode: CellMode::Hosted,
            creation_budget: Some(10),
        }
    }

    #[test]
    fn test_deploy_factory() {
        let mut registry = FactoryRegistry::new();
        let desc = worker_factory_descriptor();
        let vk = registry.deploy(desc.clone());
        assert_eq!(vk, test_factory_vk());
        assert_eq!(registry.get(&vk), Some(&desc));
    }

    #[test]
    fn test_valid_creation() {
        let desc = worker_factory_descriptor();
        let coordinator_id = CellId::derive_raw(&[1u8; 32], &[0u8; 32]);
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![CapGrant {
                target: CapTarget::Specific(coordinator_id),
                max_permissions: AuthRequired::None,
                attenuatable: false,
            }],
            owner_pubkey: [2u8; 32],
        };
        assert!(desc.validate_creation(&params).is_ok());
    }

    #[test]
    fn test_program_mismatch() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None, // Wrong: factory requires Some
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::ProgramMismatch { .. }));
    }

    #[test]
    fn test_mode_mismatch() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign, // Wrong: factory specifies Hosted
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::ModeMismatch { .. }));
    }

    #[test]
    fn test_capability_outside_template() {
        let desc = worker_factory_descriptor();
        let rogue_cell = CellId::derive_raw(&[99u8; 32], &[0u8; 32]);
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![CapGrant {
                target: CapTarget::Specific(rogue_cell), // Not in template
                max_permissions: AuthRequired::None,
                attenuatable: false,
            }],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(
            err,
            FactoryError::CapabilityOutsideTemplate { .. }
        ));
    }

    #[test]
    fn test_field_equality_constraint_violated() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 99), (1, 50)], // field 0 must be 42
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::FieldConstraintViolation { .. }));
    }

    #[test]
    fn test_field_range_constraint_violated() {
        let desc = worker_factory_descriptor();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 200)], // field 1 range is [1, 100]
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };
        let err = desc.validate_creation(&params).unwrap_err();
        assert!(matches!(err, FactoryError::FieldConstraintViolation { .. }));
    }

    #[test]
    fn test_budget_enforcement() {
        let mut registry = FactoryRegistry::new();
        let desc = worker_factory_descriptor(); // budget = 10
        let vk = registry.deploy(desc);

        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };

        // Should succeed 10 times.
        for _ in 0..10 {
            assert!(registry.validate_and_record(&vk, &params).is_ok());
        }

        // 11th should fail.
        let err = registry.validate_and_record(&vk, &params).unwrap_err();
        assert!(matches!(
            err,
            FactoryError::BudgetExceeded { limit: 10, .. }
        ));
    }

    #[test]
    fn test_budget_resets_on_epoch_advance() {
        let mut registry = FactoryRegistry::new();
        let desc = worker_factory_descriptor();
        let vk = registry.deploy(desc);

        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some(test_child_vk()),
            initial_fields: vec![(0, 42), (1, 50)],
            initial_caps: vec![],
            owner_pubkey: [2u8; 32],
        };

        // Use up budget.
        for _ in 0..10 {
            registry.validate_and_record(&vk, &params).unwrap();
        }
        assert!(registry.validate_and_record(&vk, &params).is_err());

        // Advance epoch.
        registry.advance_epoch();

        // Should succeed again.
        assert!(registry.validate_and_record(&vk, &params).is_ok());
    }

    #[test]
    fn test_provenance_creation() {
        let prov = Provenance::from_factory(test_factory_vk(), Some([0xAB; 32]), 100);
        assert_eq!(prov.created_by_factory, Some(test_factory_vk()));
        assert_eq!(prov.creation_proof_hash, Some([0xAB; 32]));
        assert_eq!(prov.creation_height, 100);
    }

    #[test]
    fn test_provenance_genesis() {
        let prov = Provenance::genesis(0);
        assert_eq!(prov.created_by_factory, None);
        assert_eq!(prov.creation_proof_hash, None);
        assert_eq!(prov.creation_height, 0);
    }

    #[test]
    fn test_descriptor_hash_deterministic() {
        let desc = worker_factory_descriptor();
        let h1 = desc.hash();
        let h2 = desc.hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_descriptor_hash_changes_with_content() {
        let desc1 = worker_factory_descriptor();
        let mut desc2 = worker_factory_descriptor();
        desc2.creation_budget = Some(20);
        assert_ne!(desc1.hash(), desc2.hash());
    }

    #[test]
    fn test_sovereign_factory() {
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: None,
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            }],
            field_constraints: vec![],
            default_mode: CellMode::Sovereign,
            creation_budget: None,
        };

        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![CapGrant {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            }],
            owner_pubkey: [3u8; 32],
        };

        assert!(desc.validate_creation(&params).is_ok());
    }

    #[test]
    fn test_any_target_template_allows_any_specific() {
        let desc = FactoryDescriptor {
            factory_vk: test_factory_vk(),
            child_program_vk: None,
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::Any,
                max_permissions: AuthRequired::None,
                attenuatable: true,
            }],
            field_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };

        let random_cell = CellId::derive_raw(&[77u8; 32], &[0u8; 32]);
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![CapGrant {
                target: CapTarget::Specific(random_cell),
                max_permissions: AuthRequired::None,
                attenuatable: true,
            }],
            owner_pubkey: [4u8; 32],
        };

        assert!(desc.validate_creation(&params).is_ok());
    }
}
