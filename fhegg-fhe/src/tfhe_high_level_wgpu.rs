//! Exact tfhe-rs high-level `FheUint32` adapter for the transform-resident PBS.
//!
//! tfhe-rs 1.6's deployed default is `KeyswitchBootstrap`: radix blocks enter
//! under the large GLWE-equivalent LWE key, are switched to the 918-dimensional
//! small key, and PBS returns a large-key ciphertext.  The original fhEgg GPU
//! qualification exercised the reverse `BootstrapKeyswitch` order.  This module
//! performs the deployed order and reconstructs a normal high-level ciphertext.
//!
//! The coefficient-domain BSK is intentionally derived from the retained
//! [`tfhe::CompressedServerKey`].  A decompressed [`tfhe::ServerKey`] contains
//! only the Fourier BSK, so it cannot losslessly recreate the exact integer
//! coefficients needed by the portable NTT backend.

use std::fmt;

use tfhe::core_crypto::prelude::*;
use tfhe::integer::IntegerCiphertext;
use tfhe::shortint::atomic_pattern::compressed::CompressedAtomicPatternServerKey;
use tfhe::shortint::ciphertext::NoiseLevel;
use tfhe::shortint::server_key::{
    LookupTableOwned, ModulusSwitchConfiguration, ShortintExpandedBootstrappingKey,
};
use tfhe::shortint::{AtomicPatternKind, PBSOrder};
use tfhe::{CompressedServerKey, FheUint32};

use crate::tfhe_wgpu::{
    prepare_torus_pbs_transform_wgpu_plan, torus_pbs_bootstrap_transform_prepared,
    TorusExternalProductParams, TorusKeyswitchParams, TorusMacBackend, TorusMacError,
    TorusPbsTransformWgpuPlan,
};

/// Refusals at the exact tfhe-rs/high-level adapter boundary.
#[derive(Debug)]
pub enum FheUint32WgpuPbsError {
    UnsupportedAtomicPattern,
    UnsupportedPbsOrder(PBSOrder),
    UnsupportedBootstrappingKey,
    BlockOutOfRange { block: usize, blocks: usize },
    BlockAtomicPattern(AtomicPatternKind),
    BlockMessageModulus { expected: u64, actual: u64 },
    BlockCarryModulus { expected: u64, actual: u64 },
    BlockLweDimension { expected: usize, actual: usize },
    LookupAccumulatorLength { expected: usize, actual: usize },
    Torus(TorusMacError),
}

impl fmt::Display for FheUint32WgpuPbsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedAtomicPattern => write!(f, "only the standard classic TFHE atomic pattern is supported"),
            Self::UnsupportedPbsOrder(order) => write!(f, "expected deployed KeyswitchBootstrap order, got {order:?}"),
            Self::UnsupportedBootstrappingKey => write!(f, "only a classic coefficient-domain bootstrapping key is supported"),
            Self::BlockOutOfRange { block, blocks } => write!(f, "radix block {block} is out of range for {blocks} blocks"),
            Self::BlockAtomicPattern(kind) => write!(f, "radix block has incompatible atomic pattern {kind:?}"),
            Self::BlockMessageModulus { expected, actual } => write!(f, "radix block message modulus {actual} does not match plan modulus {expected}"),
            Self::BlockCarryModulus { expected, actual } => write!(f, "radix block carry modulus {actual} does not match plan modulus {expected}"),
            Self::BlockLweDimension { expected, actual } => write!(f, "radix block LWE dimension {actual} does not match deployed large-key dimension {expected}"),
            Self::LookupAccumulatorLength { expected, actual } => write!(f, "lookup accumulator has {actual} coefficients; expected {expected}"),
            Self::Torus(error) => write!(f, "portable torus PBS failed: {error}"),
        }
    }
}

impl std::error::Error for FheUint32WgpuPbsError {}

impl From<TorusMacError> for FheUint32WgpuPbsError {
    fn from(value: TorusMacError) -> Self {
        Self::Torus(value)
    }
}

/// A lossless coefficient-key bridge plus the resident portable-GPU plan.
pub struct FheUint32KsPbsTransformWgpuPlan {
    transform: TorusPbsTransformWgpuPlan,
    key_switching_key: LweKeyswitchKeyOwned<u64>,
    modulus_switch: ModulusSwitchConfiguration<u64>,
    external: TorusExternalProductParams,
    message_modulus: u64,
    carry_modulus: u64,
}

impl fmt::Debug for FheUint32KsPbsTransformWgpuPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FheUint32KsPbsTransformWgpuPlan")
            .field("transform", &self.transform)
            .field("message_modulus", &self.message_modulus)
            .field("carry_modulus", &self.carry_modulus)
            .finish_non_exhaustive()
    }
}

/// Expand the retained compressed default server key exactly, upload its BSK
/// once in transform form, and retain its coefficient KSK for the deployed
/// pre-PBS key switch.
pub fn prepare_fhe_uint32_ks_pbs_transform_wgpu_plan(
    compressed: &CompressedServerKey,
) -> Result<FheUint32KsPbsTransformWgpuPlan, FheUint32WgpuPbsError> {
    let (integer, _, _, _, _, _, _, _, _) = compressed.clone().into_raw_parts();
    let shortint = integer.into_raw_parts();
    let (compressed_ap, message_modulus, carry_modulus, _, _) = shortint.into_raw_parts();
    let CompressedAtomicPatternServerKey::Standard(compressed_standard) = compressed_ap else {
        return Err(FheUint32WgpuPbsError::UnsupportedAtomicPattern);
    };
    let expanded = compressed_standard.expand();
    if expanded.pbs_order != PBSOrder::KeyswitchBootstrap {
        return Err(FheUint32WgpuPbsError::UnsupportedPbsOrder(
            expanded.pbs_order,
        ));
    }
    let ShortintExpandedBootstrappingKey::Classic {
        bsk,
        modulus_switch_noise_reduction_key,
    } = expanded.bootstrapping_key
    else {
        return Err(FheUint32WgpuPbsError::UnsupportedBootstrappingKey);
    };
    let key_switching_key = expanded.key_switching_key;
    let external = TorusExternalProductParams {
        degree: bsk.polynomial_size().0,
        glwe_size: bsk.glwe_size().0,
        decomposition_base_log: bsk.decomposition_base_log().0,
        decomposition_level_count: bsk.decomposition_level_count().0,
    };
    let keyswitch = TorusKeyswitchParams {
        output_lwe_dimension: key_switching_key.output_key_lwe_dimension().0,
        decomposition_base_log: key_switching_key.decomposition_base_log().0,
        decomposition_level_count: key_switching_key.decomposition_level_count().0,
    };
    let transform = prepare_torus_pbs_transform_wgpu_plan(
        bsk.input_lwe_dimension().0,
        bsk.as_ref(),
        external,
        key_switching_key.as_ref(),
        keyswitch,
    )?;
    Ok(FheUint32KsPbsTransformWgpuPlan {
        transform,
        key_switching_key,
        modulus_switch: modulus_switch_noise_reduction_key,
        external,
        message_modulus: message_modulus.0,
        carry_modulus: carry_modulus.0,
    })
}

impl FheUint32KsPbsTransformWgpuPlan {
    /// Apply one tfhe-rs shortint LUT to one radix block and return an ordinary
    /// large-key `FheUint32`. Other radix blocks and all high-level metadata are
    /// preserved byte-for-byte.
    pub fn apply_lookup_table_to_block(
        &self,
        input: &FheUint32,
        block_index: usize,
        lookup: &LookupTableOwned,
    ) -> Result<(FheUint32, TorusMacBackend), FheUint32WgpuPbsError> {
        let (mut radix, id, tag, rerandomization) = input.clone().into_raw_parts();
        let blocks_len = radix.blocks().len();
        let block = radix.blocks_mut().get_mut(block_index).ok_or(
            FheUint32WgpuPbsError::BlockOutOfRange {
                block: block_index,
                blocks: blocks_len,
            },
        )?;
        if block.atomic_pattern != AtomicPatternKind::Standard(PBSOrder::KeyswitchBootstrap) {
            return Err(FheUint32WgpuPbsError::BlockAtomicPattern(
                block.atomic_pattern,
            ));
        }
        if block.message_modulus.0 != self.message_modulus {
            return Err(FheUint32WgpuPbsError::BlockMessageModulus {
                expected: self.message_modulus,
                actual: block.message_modulus.0,
            });
        }
        if block.carry_modulus.0 != self.carry_modulus {
            return Err(FheUint32WgpuPbsError::BlockCarryModulus {
                expected: self.carry_modulus,
                actual: block.carry_modulus.0,
            });
        }
        let expected_large = self.key_switching_key.input_key_lwe_dimension().0;
        let actual_large = block.ct.lwe_size().to_lwe_dimension().0;
        if actual_large != expected_large {
            return Err(FheUint32WgpuPbsError::BlockLweDimension {
                expected: expected_large,
                actual: actual_large,
            });
        }
        let expected_accumulator = self.external.glwe_size * self.external.degree;
        if lookup.acc.as_ref().len() != expected_accumulator {
            return Err(FheUint32WgpuPbsError::LookupAccumulatorLength {
                expected: expected_accumulator,
                actual: lookup.acc.as_ref().len(),
            });
        }

        let mut small = LweCiphertext::new(
            0u64,
            self.key_switching_key
                .output_key_lwe_dimension()
                .to_lwe_size(),
            self.key_switching_key.ciphertext_modulus(),
        );
        keyswitch_lwe_ciphertext(&self.key_switching_key, &block.ct, &mut small);

        // Preserve the exact modulus-switch policy selected by tfhe-rs's key.
        let log_modulus =
            PolynomialSize(self.external.degree).to_blind_rotation_input_modulus_log();
        let switched = self
            .modulus_switch
            .lwe_ciphertext_modulus_switch::<usize, _>(&small, log_modulus);
        let twice_degree = self.external.degree * 2;
        let body_rotation = (twice_degree - switched.body()) % twice_degree;
        let mask_rotations = switched.mask().collect::<Vec<_>>();
        let result = torus_pbs_bootstrap_transform_prepared(
            &self.transform,
            lookup.acc.as_ref(),
            &mask_rotations,
            body_rotation,
        )?;
        let output = LweCiphertext::from_container(
            result.coefficients,
            self.key_switching_key.ciphertext_modulus(),
        );
        *block = tfhe::shortint::Ciphertext::new(
            output,
            lookup.degree,
            NoiseLevel::NOMINAL,
            block.message_modulus,
            block.carry_modulus,
            block.atomic_pattern,
        );
        Ok((
            FheUint32::from_raw_parts(radix, id, tag, rerandomization),
            result.backend,
        ))
    }
}
