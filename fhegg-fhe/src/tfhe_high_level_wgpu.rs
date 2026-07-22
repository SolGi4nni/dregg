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
use tfhe::shortint::ciphertext::{Degree, NoiseLevel};
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
    UnexpectedRadixBlocks { expected: usize, actual: usize },
    NonEmptyCarries,
    UnsupportedComparisonModuli { message: u64, carry: u64 },
    Torus(TorusMacError),
}

impl fmt::Display for FheUint32WgpuPbsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedAtomicPattern => write!(
                f,
                "only the standard classic TFHE atomic pattern is supported"
            ),
            Self::UnsupportedPbsOrder(order) => write!(
                f,
                "expected deployed KeyswitchBootstrap order, got {order:?}"
            ),
            Self::UnsupportedBootstrappingKey => write!(
                f,
                "only a classic coefficient-domain bootstrapping key is supported"
            ),
            Self::BlockOutOfRange { block, blocks } => {
                write!(f, "radix block {block} is out of range for {blocks} blocks")
            }
            Self::BlockAtomicPattern(kind) => {
                write!(f, "radix block has incompatible atomic pattern {kind:?}")
            }
            Self::BlockMessageModulus { expected, actual } => write!(
                f,
                "radix block message modulus {actual} does not match plan modulus {expected}"
            ),
            Self::BlockCarryModulus { expected, actual } => write!(
                f,
                "radix block carry modulus {actual} does not match plan modulus {expected}"
            ),
            Self::BlockLweDimension { expected, actual } => write!(
                f,
                "radix block LWE dimension {actual} does not match deployed large-key dimension {expected}"
            ),
            Self::LookupAccumulatorLength { expected, actual } => write!(
                f,
                "lookup accumulator has {actual} coefficients; expected {expected}"
            ),
            Self::UnexpectedRadixBlocks { expected, actual } => write!(
                f,
                "FheUint32 comparison has {actual} radix blocks; expected {expected}"
            ),
            Self::NonEmptyCarries => {
                write!(f, "scalar comparison requires carry-clean radix blocks")
            }
            Self::UnsupportedComparisonModuli { message, carry } => write!(
                f,
                "scalar comparison requires message modulus 4 and carry modulus 4, got message={message}, carry={carry}"
            ),
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
    scalar_gt_luts: Option<ScalarGreaterThanLuts>,
}

struct ScalarGreaterThanLuts {
    first: [LookupTableOwned; 4],
    middle: [LookupTableOwned; 4],
    last: [LookupTableOwned; 4],
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
    // A comparison state is encoded as 0=less, 1=equal, 2=greater.  With the
    // deployed radix-4/message-4 carry-4 parameters, one state and one radix
    // digit fit exactly in a single shortint plaintext as `state + 4*digit`.
    // Pre-build the twelve accumulators once; retaining the decompressed
    // Fourier server key beside the resident coefficient BSK would duplicate
    // the dominant evaluation-key allocation.
    let scalar_gt_luts = if message_modulus.0 == 4 && carry_modulus.0 == 4 {
        let decompressed = compressed.decompress();
        let shortint_server: &tfhe::shortint::ServerKey = decompressed.as_ref().as_ref();
        let compare_digit = |digit: u64, expected: u64| {
            if digit < expected {
                0
            } else if digit == expected {
                1
            } else {
                2
            }
        };
        let first = std::array::from_fn(|expected| {
            shortint_server
                .generate_lookup_table(move |value| compare_digit(value % 4, expected as u64))
        });
        let middle = std::array::from_fn(|expected| {
            shortint_server.generate_lookup_table(move |packed| {
                let state = packed % 4;
                let digit = packed / 4;
                if state == 1 {
                    compare_digit(digit, expected as u64)
                } else {
                    state
                }
            })
        });
        let last = std::array::from_fn(|expected| {
            shortint_server.generate_lookup_table(move |packed| {
                let state = packed % 4;
                let digit = packed / 4;
                let final_state = if state == 1 {
                    compare_digit(digit, expected as u64)
                } else {
                    state
                };
                u64::from(final_state == 2)
            })
        });
        Some(ScalarGreaterThanLuts {
            first,
            middle,
            last,
        })
    } else {
        None
    };
    Ok(FheUint32KsPbsTransformWgpuPlan {
        transform,
        key_switching_key,
        modulus_switch: modulus_switch_noise_reduction_key,
        external,
        message_modulus: message_modulus.0,
        carry_modulus: carry_modulus.0,
        scalar_gt_luts,
    })
}

impl FheUint32KsPbsTransformWgpuPlan {
    fn apply_lookup_table_to_lwe(
        &self,
        input: &LweCiphertextOwned<u64>,
        lookup: &LookupTableOwned,
    ) -> Result<(tfhe::shortint::Ciphertext, TorusMacBackend), FheUint32WgpuPbsError> {
        let expected_large = self.key_switching_key.input_key_lwe_dimension().0;
        let actual_large = input.lwe_size().to_lwe_dimension().0;
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
        keyswitch_lwe_ciphertext(&self.key_switching_key, input, &mut small);

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
        Ok((
            tfhe::shortint::Ciphertext::new(
                output,
                lookup.degree,
                NoiseLevel::NOMINAL,
                tfhe::shortint::parameters::MessageModulus(self.message_modulus),
                tfhe::shortint::parameters::CarryModulus(self.carry_modulus),
                AtomicPatternKind::Standard(PBSOrder::KeyswitchBootstrap),
            ),
            result.backend,
        ))
    }

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
        let (output, backend) = self.apply_lookup_table_to_lwe(&block.ct, lookup)?;
        *block = output;
        Ok((
            FheUint32::from_raw_parts(radix, id, tag, rerandomization),
            backend,
        ))
    }

    /// Compare one carry-clean encrypted `u32` with a public scalar using a
    /// radix-4 lexicographic state machine. Every state transition is one exact
    /// deployed-order KS -> transform-resident PBS; no ciphertext block is
    /// decrypted or routed through tfhe-rs's CPU comparison implementation.
    ///
    /// The returned ordinary `FheUint32` encrypts either zero or one and can be
    /// consumed by the high-level arithmetic/control-flow surface. The backend
    /// vector contains one entry per radix block, in execution order.
    pub fn greater_than_scalar(
        &self,
        input: &FheUint32,
        scalar: u32,
    ) -> Result<(FheUint32, Vec<TorusMacBackend>), FheUint32WgpuPbsError> {
        let Some(luts) = &self.scalar_gt_luts else {
            return Err(FheUint32WgpuPbsError::UnsupportedComparisonModuli {
                message: self.message_modulus,
                carry: self.carry_modulus,
            });
        };
        let (mut radix, id, tag, rerandomization) = input.clone().into_raw_parts();
        if !radix.block_carries_are_empty() {
            return Err(FheUint32WgpuPbsError::NonEmptyCarries);
        }
        let blocks = radix.blocks();
        let expected_blocks = u32::BITS as usize / 2;
        if blocks.len() != expected_blocks {
            return Err(FheUint32WgpuPbsError::UnexpectedRadixBlocks {
                expected: expected_blocks,
                actual: blocks.len(),
            });
        }
        for block in blocks {
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
        }

        let digit = |block_index: usize| ((scalar >> (2 * block_index)) & 3) as usize;
        let most_significant = blocks.len() - 1;
        let first_lut = &luts.first[digit(most_significant)];
        let (mut state, first_backend) =
            self.apply_lookup_table_to_lwe(&blocks[most_significant].ct, first_lut)?;
        let mut backends = vec![first_backend];

        for block_index in (0..most_significant).rev() {
            // Pack `(state,digit)` into the 16-element plaintext space. This is
            // the same linear pre-PBS shape as a shortint bivariate LUT, but the
            // resulting PBS is dispatched through our exact resident WGPU key.
            let mut scaled_digit = blocks[block_index].ct.clone();
            lwe_ciphertext_cleartext_mul_assign(&mut scaled_digit, Cleartext(4u64));
            let mut packed = state.ct.clone();
            lwe_ciphertext_add_assign(&mut packed, &scaled_digit);
            let lut = if block_index == 0 {
                &luts.last[digit(block_index)]
            } else {
                &luts.middle[digit(block_index)]
            };
            let (next, backend) = self.apply_lookup_table_to_lwe(&packed, lut)?;
            state = next;
            backends.push(backend);
        }

        // Reify the encrypted predicate as a normal high-level radix value:
        // the final comparison bit is the least-significant block and every
        // other block is an exact public zero under the same large key shape.
        let zero_lwe = || {
            LweCiphertext::new(
                0u64,
                self.key_switching_key
                    .input_key_lwe_dimension()
                    .to_lwe_size(),
                self.key_switching_key.ciphertext_modulus(),
            )
        };
        for block in radix.blocks_mut() {
            *block = tfhe::shortint::Ciphertext::new(
                zero_lwe(),
                Degree::new(0),
                NoiseLevel::ZERO,
                block.message_modulus,
                block.carry_modulus,
                block.atomic_pattern,
            );
        }
        radix.blocks_mut()[0] = state;
        Ok((
            FheUint32::from_raw_parts(radix, id, tag, rerandomization),
            backends,
        ))
    }
}
