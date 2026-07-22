//! The GPU-RESIDENT pipeline — upload once, compute resident, download once (the performance north star).
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §3. OWNED by the `gpu_arena` lane. Wraps
//! `bfv_gpu` (same shader, same lane math, same FOLD_MODULI shape). This is the fix for the transfer-bound
//! one-shot "loss": data stays on-device across the pipeline so the fold becomes a bare dispatch and the
//! single transfer amortizes over the whole computation.
//!
//! WHY the one-shot `fold_gpu` lost (measured, `bin/gpu_saturate.rs` 2026-07-18, hbox 6750 XT N=8192):
//! host pack 485 ms (56%) + create/upload 325 ms (37%) + dispatch/readback ~50 ms (7%) — the GPU did 7% of
//! the work and the host did the rest, EVERY call. The arena removes both dominant costs structurally:
//!   * NO pack loop: `LeanCiphertext` coefficients are `u64`; on a little-endian host their in-memory bytes
//!     ARE the (lo, hi) u32 pairs the shader reads. Upload is a row-granular memcpy into a mapped device
//!     buffer — the u64→2×u32 "conversion" is the identity and is never materialized.
//!   * ONE upload: `upload` transfers the ciphertext set once into a resident STORAGE buffer;
//!     `fold_resident` binds that buffer directly (device→device, no readback, output stays resident);
//!     `download` is the single readback at the end.
//!
//! CORRECTNESS: `fold_resident` dispatches the SAME `bfv_fold.wgsl` pipeline `fold_gpu` uses (identical
//! conditional-subtract modular add per lane), so the resident result equals [`crate::bfv_lean::fold`]
//! bit-for-bit — the parity test proves it, including a fold-of-a-fold (an output buffer re-bound as input).
//!
//! WRAP GATE, stated honestly: the frozen §3 signatures carry no plaintext modulus, so `fold_resident`
//! CANNOT apply the wrap refusal at fold time the way `fold`/`fold_gpu` do. The arena instead carries the
//! exact scalar bookkeeping the gate needs — `download` returns the folded ciphertext with `plain_bound` =
//! the true sum of the inputs' bounds — so every downstream consumer (`fold_add`, decrypt margin checks)
//! gates identically on the downloaded value. The bound sum is tracked in u128 and FAILS LOUDLY (panic) if
//! it would not fit the `plain_bound: u64` field, never silently truncates. A test proves the carried bound
//! still bites downstream.
//!
//! PRODUCTION CUTOVER: [`Arena::fold_streaming`] is the bounded resident entry point. It derives the exact
//! per-adapter ciphertext capacity from both wgpu buffer limits, uploads an arbitrarily large batch in
//! bounded chunks, folds every chunk on-device, concatenates only the one-ciphertext chunk results by
//! device-to-device copies, and reduces those recursively without an intermediate readback. The batch
//! limit that killed the one-shot path is therefore not a correctness cliff anymore. Only the irreducible
//! case where *one* ciphertext cannot fit is refused. [`FoldEngine`] keeps this path reusable and falls
//! back to the bit-exact CPU fold only when no arena exists or the shape is outside this three-modulus GPU
//! stone; validation/capacity failures are returned, never hidden by a fallback.
//!
//! The original low-level `upload`/`fold_resident`/`download` signatures remain for callers that manage
//! residency directly. They have no error channel, so misuse still panics with a named message. Production
//! batch callers should use `fold_streaming` or `FoldEngine` instead.
//!
//! Pool lifetime: resident buffers live in the arena's pool for the arena's lifetime (prototype — no free
//! list; a `ResidentHandle` is an index into the pool, never dangling).

use crate::bfv_lean::{fold, BfvLeanError, LeanCiphertext, RnsPoly, FOLD_MODULI};
use std::sync::Mutex;

type Result<T> = std::result::Result<T, BfvLeanError>;

#[cfg(target_endian = "big")]
compile_error!(
    "gpu_arena uploads u64 coefficients by reinterpreting their bytes as (lo,hi) u32 pairs — little-endian hosts only"
);

/// The ciphertext-set shape a resident buffer holds (everything `download` needs to rebuild
/// `LeanCiphertext`s, and everything `fold_resident` needs to build the shader's Meta uniform).
#[derive(Clone, PartialEq, Eq, Debug)]
struct Shape {
    moduli: Vec<u64>,
    degree: usize,
    level: u64,
    n_polys: usize,
}

impl Shape {
    fn of(ct: &LeanCiphertext) -> Shape {
        Shape {
            moduli: ct.moduli.clone(),
            degree: ct.degree,
            level: ct.level,
            n_polys: ct.polys.len(),
        }
    }
    /// Coefficient lanes per ciphertext: polys × rns-rows × degree.
    fn checked_n_lanes(&self) -> Option<usize> {
        self.n_polys
            .checked_mul(self.moduli.len())?
            .checked_mul(self.degree)
    }
    /// Bytes per resident ciphertext (8 bytes per coefficient lane).
    fn checked_ct_bytes(&self) -> Option<u64> {
        let lanes = u64::try_from(self.checked_n_lanes()?).ok()?;
        lanes.checked_mul(8)
    }
    /// Low-level methods have frozen infallible signatures; production callers pass through the checked
    /// capacity/preflight path before reaching this convenience.
    fn n_lanes(&self) -> usize {
        self.checked_n_lanes()
            .expect("gpu_arena: ciphertext lane-count overflow")
    }
    fn ct_bytes(&self) -> u64 {
        self.checked_ct_bytes()
            .expect("gpu_arena: ciphertext byte-size overflow")
    }
}

struct PoolEntry {
    buf: wgpu::Buffer,
    n_cts: usize,
}

/// A wgpu device + a resident ciphertext buffer pool.
pub struct Arena {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    bgl: wgpu::BindGroupLayout,
    /// min(max_buffer_size, max_storage_buffer_binding_size), the actual input-binding ceiling.
    max_storage_bytes: u64,
    pool: Mutex<Vec<PoolEntry>>,
    /// MAP_READ buffers are reusable after `unmap`. Retaining a small exact-size cache removes one device
    /// allocation from every steady-state FoldEngine call without changing synchronization or bytes.
    readback_cache: Mutex<Vec<wgpu::Buffer>>,
}

/// An on-device ciphertext-set — a buffer id into the arena pool, NEVER downloaded until `download`.
/// Scalar bookkeeping (plaintext bounds, variable-time flag, shape) rides host-side, exactly as it does on
/// `LeanCiphertext` itself; the polynomial data stays on the device.
#[derive(Clone)]
pub struct ResidentHandle {
    id: usize,
    n_cts: usize,
    shape: Shape,
    /// Per-resident-ciphertext flag. Keeping this parallel to `bounds` matters when independently folded
    /// outputs are concatenated for one amortized readback: OR-ing the flags at concatenate time would
    /// incorrectly taint every output when only one input group was variable-time.
    variable_times: Vec<bool>,
    /// Per-resident-ciphertext plaintext bound, tracked in u128 so a fold's sum can never wrap silently.
    bounds: Vec<u128>,
}

/// Adapter-derived capacity for this exact ciphertext shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldCapacity {
    pub max_storage_bytes: u64,
    pub ciphertext_bytes: u64,
    /// Maximum input ciphertexts per resident upload/fold dispatch. Always nonzero on success.
    pub ciphertexts_per_chunk: usize,
}

/// Auditable execution plan returned with a bounded resident fold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResidentFoldPlan {
    pub input_ciphertexts: usize,
    pub ciphertexts_per_chunk: usize,
    pub upload_chunks: usize,
    /// Number of device-resident reduction layers after each upload chunk's first fold.
    pub reduction_rounds: usize,
}

/// Which path actually produced an accelerated-fold result. CPU fallback is explicit, never silent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldBackend {
    GpuResident(ResidentFoldPlan),
    CpuNoArena,
    CpuUnsupportedShape,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FoldExecution {
    pub ciphertext: LeanCiphertext,
    pub backend: FoldBackend,
}

/// Reusable production adapter: one GPU device/pipeline for many folds, or an explicit CPU fallback when
/// this process cannot obtain an arena. A GPU computation error is returned; it never silently retries on
/// CPU and masks a residency bug.
pub struct FoldEngine {
    gpu: Option<Arena>,
    /// One arena pool backs the engine; serialize whole calls so per-call reclamation cannot invalidate a
    /// concurrent call's handles. The underlying queue is one device queue anyway.
    run_lock: Mutex<()>,
}

impl FoldEngine {
    pub fn new() -> Self {
        Self {
            gpu: arena(),
            run_lock: Mutex::new(()),
        }
    }

    /// Construct an explicitly CPU-only engine. This is useful for deployments that disable GPU use
    /// by policy and for consumers that must exercise/report the headless fallback deterministically.
    pub fn cpu_only() -> Self {
        Self {
            gpu: None,
            run_lock: Mutex::new(()),
        }
    }

    pub fn has_gpu_arena(&self) -> bool {
        self.gpu.is_some()
    }

    /// Exact adapter capacity for a ciphertext shape, or `None` when this engine is explicitly/headlessly
    /// CPU-only. This is observation only; execution still validates the complete batch in [`Self::fold`].
    pub fn capacity(&self, ct: &LeanCiphertext) -> Option<Result<FoldCapacity>> {
        self.gpu.as_ref().map(|gpu| {
            let shape = Shape::of(ct);
            if !gpu_shape_supported(&shape) {
                return Err(BfvLeanError::GpuUnsupportedShape);
            }
            gpu.capacity_for_shape(&shape)
        })
    }

    pub fn fold(&self, cts: &[LeanCiphertext], plaintext_modulus: u64) -> Result<FoldExecution> {
        let _run = self.run_lock.lock().unwrap();
        let shape = preflight_fold(cts, plaintext_modulus)?;
        let Some(gpu) = &self.gpu else {
            return Ok(FoldExecution {
                ciphertext: fold(cts, plaintext_modulus)?,
                backend: FoldBackend::CpuNoArena,
            });
        };
        if !gpu_shape_supported(&shape) {
            return Ok(FoldExecution {
                ciphertext: fold(cts, plaintext_modulus)?,
                backend: FoldBackend::CpuUnsupportedShape,
            });
        }
        let execution = (|| {
            let (resident, plan) = gpu.fold_streaming_preflighted(cts, &shape)?;
            let mut downloaded = gpu.download(&resident);
            debug_assert_eq!(downloaded.len(), 1);
            Ok(FoldExecution {
                ciphertext: downloaded
                    .pop()
                    .expect("resident fold returns one ciphertext"),
                backend: FoldBackend::GpuResident(plan),
            })
        })();
        // FoldEngine owns its arena privately, so no external ResidentHandle can alias these entries.
        // On success, download waited for the queue. On error, wgpu's submitted command buffers retain
        // their resources. Either way, reclaim every per-call host handle instead of leaking the pool.
        gpu.clear_pool();
        execution
    }

    /// Fold two independent groups with one batched compute submission, one final GPU readback, and one
    /// device wait when both sides fit one adapter binding. Oversized sides retain the bounded streaming
    /// reducer and still share the final direct-gather readback.
    ///
    /// Demand and supply are the production consumer, but the primitive is deliberately stated in terms
    /// of two same-shaped folds. Each group keeps its own bound and variable-time bookkeeping. When no
    /// arena exists, or the exact deployed GPU modulus set is not in use, both results take the labelled
    /// bit-exact CPU path. GPU failures are returned and never hidden by retrying on CPU.
    pub(crate) fn fold_pair(
        &self,
        first: &[LeanCiphertext],
        second: &[LeanCiphertext],
        plaintext_modulus: u64,
    ) -> Result<(FoldExecution, FoldExecution)> {
        let _run = self.run_lock.lock().unwrap();
        let first_shape = preflight_fold(first, plaintext_modulus)?;
        let second_shape = preflight_fold(second, plaintext_modulus)?;
        if first_shape != second_shape {
            return Err(BfvLeanError::Incompatible(
                "paired resident folds disagree on degree/moduli/polys/level",
            ));
        }

        let cpu_pair = |backend| {
            Ok((
                FoldExecution {
                    ciphertext: fold(first, plaintext_modulus)?,
                    backend,
                },
                FoldExecution {
                    ciphertext: fold(second, plaintext_modulus)?,
                    backend,
                },
            ))
        };
        let Some(gpu) = &self.gpu else {
            return cpu_pair(FoldBackend::CpuNoArena);
        };
        if !gpu_shape_supported(&first_shape) {
            return cpu_pair(FoldBackend::CpuUnsupportedShape);
        }

        let executions = (|| {
            let capacity = gpu.capacity_for_shape(&first_shape)?;
            let ((first_resident, first_plan), (second_resident, second_plan)) = if first.len()
                <= capacity.ciphertexts_per_chunk
                && second.len() <= capacity.ciphertexts_per_chunk
            {
                // The overwhelmingly common market shape fits each side in one storage binding. Upload
                // both, then encode both independent dispatches into ONE compute pass/submission. The
                // generic streaming reducer remains the exact path for larger-than-adapter books.
                let first_uploaded = gpu.upload(first);
                let second_uploaded = gpu.upload(second);
                let mut folded = gpu
                    .fold_resident_many(&[&first_uploaded, &second_uploaded])
                    .into_iter();
                let first_resident = folded
                    .next()
                    .expect("paired resident fold returns first dispatch output");
                let second_resident = folded
                    .next()
                    .expect("paired resident fold returns second dispatch output");
                debug_assert!(folded.next().is_none());
                let plan = |input_ciphertexts| ResidentFoldPlan {
                    input_ciphertexts,
                    ciphertexts_per_chunk: capacity.ciphertexts_per_chunk,
                    upload_chunks: 1,
                    reduction_rounds: 0,
                };
                (
                    (first_resident, plan(first.len())),
                    (second_resident, plan(second.len())),
                )
            } else {
                (
                    gpu.fold_streaming_preflighted(first, &first_shape)?,
                    gpu.fold_streaming_preflighted(second, &second_shape)?,
                )
            };
            // Copy both independent outputs straight into one MAP_READ buffer. The old path first
            // allocated a two-ciphertext STORAGE buffer, submitted a device-to-device concatenate, and
            // then submitted the staging copy. Direct gathering preserves the same one map/wait while
            // removing that intermediate allocation and queue submission from every demand/supply fold.
            let mut downloaded = gpu
                .download_many(&[&first_resident, &second_resident])
                .into_iter();
            let first_ciphertext = downloaded
                .next()
                .expect("paired resident fold returns its first ciphertext");
            let second_ciphertext = downloaded
                .next()
                .expect("paired resident fold returns its second ciphertext");
            debug_assert!(downloaded.next().is_none());
            Ok((
                FoldExecution {
                    ciphertext: first_ciphertext,
                    backend: FoldBackend::GpuResident(first_plan),
                },
                FoldExecution {
                    ciphertext: second_ciphertext,
                    backend: FoldBackend::GpuResident(second_plan),
                },
            ))
        })();
        gpu.clear_pool();
        executions
    }
}

impl Default for FoldEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// One-call convenience. Latency-sensitive repeated callers should retain a [`FoldEngine`] so device and
/// pipeline initialization are amortized.
pub fn fold_resident_or_cpu(
    cts: &[LeanCiphertext],
    plaintext_modulus: u64,
) -> Result<FoldExecution> {
    FoldEngine::new().fold(cts, plaintext_modulus)
}

/// None if there is no wgpu adapter (headless).
pub fn arena() -> Option<Arena> {
    let instance = wgpu::Instance::default();
    let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::HighPerformance,
        ..Default::default()
    }))?;
    let limits = adapter.limits();
    let max_storage_bytes = limits
        .max_buffer_size
        .min(u64::from(limits.max_storage_buffer_binding_size));
    let (device, queue) = pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("bfv-arena"),
            required_features: wgpu::Features::empty(),
            required_limits: limits,
            memory_hints: Default::default(),
        },
        None,
    ))
    .ok()?;
    // The SAME fold shader bfv_gpu dispatches — one pipeline, two call shapes (one-shot vs resident).
    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("bfv_fold.wgsl (arena)"),
        source: wgpu::ShaderSource::Wgsl(include_str!("shaders/bfv_fold.wgsl").into()),
    });
    let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("arena-fold"),
        entries: &[
            buffer_entry(0, wgpu::BufferBindingType::Uniform),
            buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
        ],
    });
    let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: None,
        bind_group_layouts: &[&bgl],
        push_constant_ranges: &[],
    });
    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("arena-fold"),
        layout: Some(&layout),
        module: &shader,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });
    Some(Arena {
        device,
        queue,
        pipeline,
        bgl,
        max_storage_bytes,
        pool: Mutex::new(Vec::new()),
        readback_cache: Mutex::new(Vec::new()),
    })
}

fn buffer_entry(binding: u32, ty: wgpu::BufferBindingType) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty,
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

fn capacity_from_limits(max_storage_bytes: u64, ciphertext_bytes: u64) -> Result<FoldCapacity> {
    if ciphertext_bytes == 0 {
        return Err(BfvLeanError::Incompatible(
            "resident fold: zero-byte ciphertext shape",
        ));
    }
    let ciphertexts_per_chunk =
        usize::try_from(max_storage_bytes / ciphertext_bytes).unwrap_or(usize::MAX);
    if ciphertexts_per_chunk == 0 {
        return Err(BfvLeanError::GpuCiphertextExceedsCapacity {
            ciphertext_bytes,
            max_storage_bytes,
        });
    }
    Ok(FoldCapacity {
        max_storage_bytes,
        ciphertext_bytes,
        // Shader metadata counts ciphertexts in u32. Current adapters are far below this limit, but clamp
        // explicitly rather than allowing a future adapter to truncate the dispatch count.
        ciphertexts_per_chunk: ciphertexts_per_chunk.min(u32::MAX as usize),
    })
}

/// This shader is proved against the deployed three-prime BFV fold set, not merely "three values".
/// Exact matching prevents adapter availability from selecting the split-u32 shader for an arbitrary
/// large modulus whose addition could overflow the shader's two-word carry representation.
fn gpu_shape_supported(shape: &Shape) -> bool {
    shape.moduli.as_slice() == FOLD_MODULI
}

fn validate_storage_layout(ct: &LeanCiphertext) -> Result<()> {
    if ct.moduli.is_empty() || ct.degree == 0 || ct.polys.len() != 2 {
        return Err(BfvLeanError::Incompatible(
            "resident fold: ciphertext must have nonempty moduli/degree and exactly two polynomials",
        ));
    }
    for poly in &ct.polys {
        if poly.rows.len() != ct.moduli.len() {
            return Err(BfvLeanError::Incompatible(
                "resident fold: polynomial RNS row count differs from modulus count",
            ));
        }
        for (modulus_index, (row, &q)) in poly.rows.iter().zip(&ct.moduli).enumerate() {
            // `bfv_lean::add_row` relies on a+b fitting in u64. q <= 2^63 is the exact general
            // carry-safe envelope; the GPU path is narrower still (`FOLD_MODULI` exactly).
            if q == 0 || q > (1u64 << 63) || row.len() != ct.degree {
                return Err(BfvLeanError::Incompatible(
                    "resident fold: invalid/carry-unsafe modulus or RNS row length",
                ));
            }
            if row.iter().any(|&coefficient| coefficient >= q) {
                return Err(BfvLeanError::NonCanonical { modulus_index });
            }
        }
    }
    Ok(())
}

/// One backend-independent acceptance gate. In particular, a one-ciphertext CPU fold must not bypass
/// wrap, structural, or residue validation merely because `bfv_lean::fold` performs no addition for it.
fn preflight_fold(cts: &[LeanCiphertext], plaintext_modulus: u64) -> Result<Shape> {
    let first = cts.first().ok_or(BfvLeanError::EmptyFold)?;
    let shape = Shape::of(first);
    validate_storage_layout(first)?;
    let mut bound_sum = u128::from(first.plain_bound);
    if bound_sum >= u128::from(plaintext_modulus) {
        return Err(BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus,
        });
    }
    for ct in &cts[1..] {
        if Shape::of(ct) != shape {
            return Err(BfvLeanError::Incompatible(
                "resident fold: ciphertexts disagree on degree/moduli/polys/level",
            ));
        }
        validate_storage_layout(ct)?;
        bound_sum = bound_sum
            .checked_add(u128::from(ct.plain_bound))
            .unwrap_or(u128::MAX);
        if bound_sum >= u128::from(plaintext_modulus) {
            return Err(BfvLeanError::WrapRefused {
                bound_sum,
                plaintext_modulus,
            });
        }
    }
    Ok(shape)
}

impl Arena {
    fn clear_pool(&self) {
        self.pool.lock().unwrap().clear();
    }

    fn acquire_readback(&self, size: u64) -> wgpu::Buffer {
        let cached = {
            let mut cache = self.readback_cache.lock().unwrap();
            cache
                .iter()
                .position(|buffer| buffer.size() == size)
                .map(|index| cache.swap_remove(index))
        };
        cached.unwrap_or_else(|| {
            self.device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("arena-read"),
                size,
                usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
                mapped_at_creation: false,
            })
        })
    }

    fn release_readback(&self, buffer: wgpu::Buffer) {
        // The retained engine normally needs one exact-size buffer. A small cap also keeps direct Arena
        // users with several shapes from turning this allocation optimization into an unbounded cache.
        let mut cache = self.readback_cache.lock().unwrap();
        if cache.len() < 4 {
            cache.push(buffer);
        }
    }

    /// Exact adapter capacity for one ciphertext shape. This is the public replacement for benchmark-side
    /// limit probing: callers can report and plan against the same ceiling the production path enforces.
    pub fn capacity(&self, ct: &LeanCiphertext) -> Result<FoldCapacity> {
        let shape = Shape::of(ct);
        if !gpu_shape_supported(&shape) {
            return Err(BfvLeanError::GpuUnsupportedShape);
        }
        self.capacity_for_shape(&shape)
    }

    fn capacity_for_shape(&self, shape: &Shape) -> Result<FoldCapacity> {
        let ciphertext_bytes = shape.checked_ct_bytes().ok_or(BfvLeanError::Incompatible(
            "resident fold: ciphertext shape size overflows host/GPU address space",
        ))?;
        capacity_from_limits(self.max_storage_bytes, ciphertext_bytes)
    }

    /// Bounded resident fold for production batches.
    ///
    /// Every input is validated and the plaintext-wrap budget is checked before any GPU submission. A
    /// batch larger than one storage binding is split into adapter-sized uploads. Each chunk is folded on
    /// device; its one-ciphertext output is copied into a bounded resident reduction buffer, recursively if
    /// needed. There is no intermediate readback. The returned handle remains resident for another kernel
    /// or a single final [`download`](Self::download).
    pub fn fold_streaming(
        &self,
        cts: &[LeanCiphertext],
        plaintext_modulus: u64,
    ) -> Result<(ResidentHandle, ResidentFoldPlan)> {
        self.fold_streaming_with_limit(cts, plaintext_modulus, None)
    }

    fn fold_streaming_with_limit(
        &self,
        cts: &[LeanCiphertext],
        plaintext_modulus: u64,
        chunk_limit: Option<usize>,
    ) -> Result<(ResidentHandle, ResidentFoldPlan)> {
        let shape = preflight_fold(cts, plaintext_modulus)?;
        if !gpu_shape_supported(&shape) {
            return Err(BfvLeanError::GpuUnsupportedShape);
        }
        self.fold_streaming_preflighted_with_limit(cts, &shape, chunk_limit)
    }

    fn fold_streaming_preflighted(
        &self,
        cts: &[LeanCiphertext],
        shape: &Shape,
    ) -> Result<(ResidentHandle, ResidentFoldPlan)> {
        self.fold_streaming_preflighted_with_limit(cts, shape, None)
    }

    /// Device portion of a fold whose complete batch has already passed [`preflight_fold`]. Keeping the
    /// validation outside lets `FoldEngine::fold_pair` validate each side once, then share one readback.
    fn fold_streaming_preflighted_with_limit(
        &self,
        cts: &[LeanCiphertext],
        shape: &Shape,
        chunk_limit: Option<usize>,
    ) -> Result<(ResidentHandle, ResidentFoldPlan)> {
        debug_assert!(!cts.is_empty());
        debug_assert!(gpu_shape_supported(shape));
        let n_lanes = shape.checked_n_lanes().ok_or(BfvLeanError::Incompatible(
            "resident fold: ciphertext lane count overflows host address space",
        ))?;
        if n_lanes == 0 {
            return Err(BfvLeanError::Incompatible(
                "resident fold: zero-degree or zero-polynomial ciphertext",
            ));
        }
        if n_lanes > u32::MAX as usize {
            return Err(BfvLeanError::Incompatible(
                "resident fold: ciphertext lane count exceeds shader u32 metadata",
            ));
        }
        let bound_sum = cts
            .iter()
            .map(|ct| u128::from(ct.plain_bound))
            .sum::<u128>();

        let capacity = self.capacity_for_shape(shape)?;
        let per_chunk = chunk_limit
            .unwrap_or(capacity.ciphertexts_per_chunk)
            .min(capacity.ciphertexts_per_chunk)
            .max(1);
        if cts.len() > 1 && per_chunk < 2 {
            return Err(BfvLeanError::GpuReductionExceedsCapacity {
                pair_bytes: capacity.ciphertext_bytes.saturating_mul(2),
                max_storage_bytes: capacity.max_storage_bytes,
            });
        }
        let upload_chunks = cts.len().div_ceil(per_chunk);
        let mut folded: Vec<ResidentHandle> = cts
            .chunks(per_chunk)
            .map(|chunk| self.fold_resident(&self.upload(chunk)))
            .collect();

        let mut reduction_rounds = 0usize;
        while folded.len() > 1 {
            let mut next = Vec::with_capacity(folded.len().div_ceil(per_chunk));
            for group in folded.chunks(per_chunk) {
                if group.len() == 1 {
                    next.push(group[0].clone());
                } else {
                    next.push(self.fold_resident(&self.concat_resident(group)));
                }
            }
            folded = next;
            reduction_rounds += 1;
        }
        let resident = folded
            .pop()
            .expect("nonempty input produces at least one resident fold");
        debug_assert_eq!(resident.bounds, vec![bound_sum]);
        Ok((
            resident,
            ResidentFoldPlan {
                input_ciphertexts: cts.len(),
                ciphertexts_per_chunk: per_chunk,
                upload_chunks,
                reduction_rounds,
            },
        ))
    }

    /// Device-to-device concatenation of compatible resident results. Production streaming calls this only
    /// with one-ciphertext fold outputs, but keeping the primitive general makes recursive reduction exact.
    fn concat_resident(&self, handles: &[ResidentHandle]) -> ResidentHandle {
        let first = handles.first().expect("gpu_arena concat: empty handle set");
        let shape = first.shape.clone();
        let n_cts: usize = handles.iter().map(|h| h.n_cts).sum();
        assert!(
            handles.iter().all(|h| h.shape == shape),
            "gpu_arena concat: resident shapes disagree"
        );
        let size = shape
            .ct_bytes()
            .checked_mul(n_cts as u64)
            .expect("gpu_arena concat: buffer-size overflow");
        assert!(
            size <= self.max_storage_bytes,
            "gpu_arena concat: {size}-byte reduction buffer exceeds adapter capacity {}",
            self.max_storage_bytes
        );
        let buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena-concat"),
            size,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        {
            let pool = self.pool.lock().unwrap();
            let mut enc = self.device.create_command_encoder(&Default::default());
            let mut offset = 0u64;
            for h in handles {
                let entry = &pool[h.id];
                let bytes = shape.ct_bytes() * h.n_cts as u64;
                enc.copy_buffer_to_buffer(&entry.buf, 0, &buf, offset, bytes);
                offset += bytes;
            }
            debug_assert_eq!(offset, size);
            self.queue.submit([enc.finish()]);
        }
        let id = {
            let mut pool = self.pool.lock().unwrap();
            pool.push(PoolEntry { buf, n_cts });
            pool.len() - 1
        };
        ResidentHandle {
            id,
            n_cts,
            shape,
            variable_times: handles
                .iter()
                .flat_map(|h| h.variable_times.iter().copied())
                .collect(),
            bounds: handles
                .iter()
                .flat_map(|h| h.bounds.iter().copied())
                .collect(),
        }
    }

    /// The ONE upload transfer. Writes every ciphertext's rows straight into a mapped resident STORAGE
    /// buffer (row-granular memcpy; the u64 LE byte layout IS the shader's (lo,hi) u32 layout — no pack
    /// loop, the one-shot path's dominant cost never happens). Panics (fail-loud, no error channel in the
    /// frozen signature) on an empty set, mixed shapes, or a non-3-moduli shape the shader cannot fold.
    pub fn upload(&self, cts: &[LeanCiphertext]) -> ResidentHandle {
        let first = cts
            .first()
            .expect("gpu_arena upload: empty ciphertext set (nothing to make resident)");
        let shape = Shape::of(first);
        assert_eq!(
            shape.moduli.len(),
            3,
            "gpu_arena upload: fold shader supports exactly 3 RNS moduli (got {})",
            shape.moduli.len()
        );
        for (i, ct) in cts.iter().enumerate() {
            assert!(
                Shape::of(ct) == shape,
                "gpu_arena upload: ciphertext {i} disagrees on fold shape (degree/moduli/polys/level)"
            );
        }
        let size = shape
            .ct_bytes()
            .checked_mul(cts.len() as u64)
            .expect("gpu_arena upload: buffer-size overflow");
        assert!(
            size <= self.max_storage_bytes,
            "gpu_arena upload: {size}-byte input exceeds adapter capacity {}; use fold_streaming for bounded chunks",
            self.max_storage_bytes
        );
        let buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena-resident"),
            size,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: true,
        });
        {
            let mut view = buf.slice(..).get_mapped_range_mut();
            let mut off = 0usize;
            for ct in cts {
                for poly in &ct.polys {
                    for row in &poly.rows {
                        let bytes: &[u8] = bytemuck::cast_slice(row); // u64 LE == (lo,hi) u32 pairs
                        view[off..off + bytes.len()].copy_from_slice(bytes);
                        off += bytes.len();
                    }
                }
            }
            debug_assert_eq!(off as u64, size);
        }
        buf.unmap();

        let id = {
            let mut pool = self.pool.lock().unwrap();
            pool.push(PoolEntry {
                buf,
                n_cts: cts.len(),
            });
            pool.len() - 1
        };
        ResidentHandle {
            id,
            n_cts: cts.len(),
            shape,
            variable_times: cts.iter().map(|c| c.variable_time).collect(),
            bounds: cts.iter().map(|c| u128::from(c.plain_bound)).collect(),
        }
    }

    /// Fold WITHOUT download — one compute dispatch, input and output both resident. The output buffer is
    /// itself STORAGE, so the result can be folded again (fold-of-folds) or downloaded later; nothing is
    /// read back here and the submit is not waited on (the single `download` at the end synchronizes).
    pub fn fold_resident(&self, h: &ResidentHandle) -> ResidentHandle {
        self.fold_resident_many(&[h])
            .pop()
            .expect("one resident input produces one fold output")
    }

    /// Encode several independent resident folds in one compute pass and one queue submission.
    ///
    /// Inputs and outputs remain disjoint; this changes only scheduling, not the shader or arithmetic.
    /// It is the two-sided call-auction fast path: demand and supply share launch overhead without ever
    /// sharing ciphertext lanes or host-side bound/variable-time bookkeeping.
    fn fold_resident_many(&self, handles: &[&ResidentHandle]) -> Vec<ResidentHandle> {
        use wgpu::util::DeviceExt;

        assert!(!handles.is_empty(), "gpu_arena fold: empty handle set");
        let n_lanes = handles
            .iter()
            .map(|handle| {
                let lanes = handle.shape.n_lanes();
                assert!(
                    handle.n_cts <= u32::MAX as usize && lanes <= u32::MAX as usize,
                    "gpu_arena fold: shader u32 metadata capacity exceeded"
                );
                lanes
            })
            .collect::<Vec<_>>();
        let output_buffers = handles
            .iter()
            .map(|handle| {
                self.device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some("arena-fold-out"),
                    size: handle.shape.ct_bytes(),
                    usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
                    mapped_at_creation: false,
                })
            })
            .collect::<Vec<_>>();
        let metadata_buffers = handles
            .iter()
            .zip(&n_lanes)
            .map(|(handle, &lanes)| {
                let meta = build_meta(
                    handle.n_cts as u32,
                    lanes as u32,
                    handle.shape.degree as u32,
                    &handle.shape.moduli,
                );
                self.device
                    .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                        label: Some("arena-fold-meta"),
                        contents: bytemuck::cast_slice(&meta),
                        usage: wgpu::BufferUsages::UNIFORM,
                    })
            })
            .collect::<Vec<_>>();
        {
            let pool = self.pool.lock().unwrap();
            let bind_groups = handles
                .iter()
                .zip(&metadata_buffers)
                .zip(&output_buffers)
                .map(|((&handle, meta), output)| {
                    let entry = &pool[handle.id];
                    assert_eq!(
                        entry.n_cts, handle.n_cts,
                        "gpu_arena: handle/pool n_cts mismatch"
                    );
                    self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                        label: None,
                        layout: &self.bgl,
                        entries: &[
                            wgpu::BindGroupEntry {
                                binding: 0,
                                resource: meta.as_entire_binding(),
                            },
                            wgpu::BindGroupEntry {
                                binding: 1,
                                resource: entry.buf.as_entire_binding(),
                            },
                            wgpu::BindGroupEntry {
                                binding: 2,
                                resource: output.as_entire_binding(),
                            },
                        ],
                    })
                })
                .collect::<Vec<_>>();
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(&self.pipeline);
                for (bind, &lanes) in bind_groups.iter().zip(&n_lanes) {
                    pass.set_bind_group(0, bind, &[]);
                    pass.dispatch_workgroups((lanes as u32).div_ceil(256), 1, 1);
                }
            }
            self.queue.submit([enc.finish()]);
        }

        let mut pool = self.pool.lock().unwrap();
        handles
            .iter()
            .zip(output_buffers)
            .map(|(&handle, output)| {
                // The fold's plaintext-bound bookkeeping: the exact sum, u128 so it cannot wrap silently.
                let bound_sum = handle.bounds.iter().copied().fold(0u128, |acc, bound| {
                    acc.checked_add(bound)
                        .expect("gpu_arena fold: plaintext-bound sum exceeds u128 (fail closed)")
                });
                pool.push(PoolEntry {
                    buf: output,
                    n_cts: 1,
                });
                ResidentHandle {
                    id: pool.len() - 1,
                    n_cts: 1,
                    shape: handle.shape.clone(),
                    variable_times: vec![handle.variable_times.iter().any(|&flag| flag)],
                    bounds: vec![bound_sum],
                }
            })
            .collect()
    }

    /// The ONE readback: copy the resident buffer to a MAP_READ staging buffer, wait, rebuild
    /// `LeanCiphertext`s (with the carried plain_bound / variable_time bookkeeping intact).
    pub fn download(&self, h: &ResidentHandle) -> Vec<LeanCiphertext> {
        self.download_many(&[h])
    }

    /// Gather several compatible resident outputs directly into one staging buffer.
    ///
    /// This is not a compute concatenation: there is no intermediate STORAGE buffer and no preliminary
    /// queue submission. All source-to-staging copies share the command buffer whose completion is already
    /// required for mapping. The fold pair uses this to return demand and supply with one allocation,
    /// submission, map, and wait while preserving each output's independent bound/variable-time metadata.
    fn download_many(&self, handles: &[&ResidentHandle]) -> Vec<LeanCiphertext> {
        let first = handles
            .first()
            .expect("gpu_arena download: empty resident handle set");
        let shape = &first.shape;
        assert!(
            handles.iter().all(|handle| handle.shape == *shape),
            "gpu_arena download: resident shapes disagree"
        );
        let total_cts = handles
            .iter()
            .try_fold(0usize, |total, handle| total.checked_add(handle.n_cts))
            .expect("gpu_arena download: ciphertext-count overflow");
        let size = shape
            .ct_bytes()
            .checked_mul(total_cts as u64)
            .expect("gpu_arena download: staging-buffer size overflow");
        let read_buf = self.acquire_readback(size);
        {
            let pool = self.pool.lock().unwrap();
            let mut enc = self.device.create_command_encoder(&Default::default());
            let mut offset = 0u64;
            for handle in handles {
                let entry = &pool[handle.id];
                assert_eq!(
                    entry.n_cts, handle.n_cts,
                    "gpu_arena: handle/pool n_cts mismatch"
                );
                let bytes = shape
                    .ct_bytes()
                    .checked_mul(handle.n_cts as u64)
                    .expect("gpu_arena download: resident byte-size overflow");
                // Only fold outputs carry COPY_SRC; downloading a raw uploaded set would need COPY_SRC on
                // the resident buffer. Supported targets are folded results (the §3 pipeline shape).
                enc.copy_buffer_to_buffer(&entry.buf, 0, &read_buf, offset, bytes);
                offset += bytes;
            }
            debug_assert_eq!(offset, size);
            self.queue.submit([enc.finish()]);
        }
        let slice = read_buf.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let data = slice.get_mapped_range();
        // LE bytes → u64 coeffs (identity layout; explicit from_le_bytes so no alignment assumption).
        let words: Vec<u64> = data
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
            .collect();
        drop(data);
        read_buf.unmap();

        let (deg, r, p) = (shape.degree, shape.moduli.len(), shape.n_polys);
        let mut out = Vec::with_capacity(total_cts);
        let mut idx = 0usize;
        for handle in handles {
            for ct_i in 0..handle.n_cts {
                let mut polys = Vec::with_capacity(p);
                for _ in 0..p {
                    let mut rows = Vec::with_capacity(r);
                    for _ in 0..r {
                        rows.push(words[idx..idx + deg].to_vec());
                        idx += deg;
                    }
                    polys.push(RnsPoly { rows });
                }
                let bound = handle.bounds[ct_i];
                out.push(LeanCiphertext {
                    moduli: shape.moduli.clone(),
                    degree: deg,
                    level: shape.level,
                    variable_time: handle.variable_times[ct_i],
                    polys,
                    plain_bound: u64::try_from(bound).unwrap_or_else(|_| {
                        panic!(
                            "gpu_arena download: folded plain_bound {bound} exceeds u64 — refusing to truncate \
                             the wrap-gate bookkeeping (fail closed)"
                        )
                    }),
                });
            }
        }
        debug_assert_eq!(idx, words.len());
        self.release_readback(read_buf);
        out
    }
}

// Meta layout matches the WGSL `Meta` struct (and bfv_gpu's): n_cts, n_lanes, row_len, _pad, q0/q1/q2 as (lo,hi).
fn build_meta(n_cts: u32, n_lanes: u32, row_len: u32, moduli: &[u64]) -> [u32; 10] {
    let q = |i: usize| (moduli[i] as u32, (moduli[i] >> 32) as u32);
    let (q0l, q0h) = q(0);
    let (q1l, q1h) = q(1);
    let (q2l, q2h) = q(2);
    [n_cts, n_lanes, row_len, 0, q0l, q0h, q1l, q1h, q2l, q2h]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfv_lean::{fold, fold_add, BfvLeanError, FOLD_MODULI};
    use std::time::{Duration, Instant};

    /// Full-shape fresh-fold ciphertext (2 polys × 3 RNS rows × degree-4096) of deterministic canonical
    /// residues — same synth as the bfv_gpu parity test / gpu_saturate bench, so numbers are comparable.
    fn synth_ct(seed: u64, plain_bound: u64) -> LeanCiphertext {
        let deg = 4096usize;
        let mut s = seed;
        let mut next = || {
            s = s
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .rotate_left(17)
                .wrapping_add(1);
            s
        };
        let polys = (0..2)
            .map(|_| RnsPoly {
                rows: FOLD_MODULI
                    .iter()
                    .map(|&q| (0..deg).map(|_| next() % q).collect())
                    .collect(),
            })
            .collect();
        LeanCiphertext {
            moduli: FOLD_MODULI.to_vec(),
            degree: deg,
            level: 0,
            variable_time: false,
            polys,
            plain_bound,
        }
    }

    #[test]
    fn capacity_math_is_bounded_exact_and_fail_closed() {
        let cap = capacity_from_limits(1_000, 100).expect("ten exact ciphertexts fit");
        assert_eq!(
            cap,
            FoldCapacity {
                max_storage_bytes: 1_000,
                ciphertext_bytes: 100,
                ciphertexts_per_chunk: 10,
            }
        );
        assert!(matches!(
            capacity_from_limits(99, 100),
            Err(BfvLeanError::GpuCiphertextExceedsCapacity {
                ciphertext_bytes: 100,
                max_storage_bytes: 99,
            })
        ));
        assert!(matches!(
            capacity_from_limits(1_000, 0),
            Err(BfvLeanError::Incompatible(
                "resident fold: zero-byte ciphertext shape"
            ))
        ));

        // Shape arithmetic itself must fail before either usize multiplication or u64 conversion wraps.
        let overflowing = Shape {
            moduli: vec![1, 2, 3],
            degree: usize::MAX,
            level: 0,
            n_polys: 2,
        };
        assert_eq!(overflowing.checked_n_lanes(), None);
        assert_eq!(overflowing.checked_ct_bytes(), None);
    }

    #[test]
    fn explicit_cpu_fallback_preserves_parity_and_refusals() {
        let t = 1u64 << 20;
        let cts: Vec<_> = (0..7).map(|i| synth_ct(i + 1, 3)).collect();
        let expected = fold(&cts, t).expect("cpu reference");
        let engine = FoldEngine {
            gpu: None,
            run_lock: Mutex::new(()),
        };
        let got = engine.fold(&cts, t).expect("explicit no-arena fallback");
        assert_eq!(got.ciphertext, expected);
        assert_eq!(got.backend, FoldBackend::CpuNoArena);

        let wrapping = vec![synth_ct(1, t - 1), synth_ct(2, 1)];
        assert!(matches!(
            engine.fold(&wrapping, t),
            Err(BfvLeanError::WrapRefused { .. })
        ));
        assert!(matches!(engine.fold(&[], t), Err(BfvLeanError::EmptyFold)));
    }

    #[test]
    fn backend_independent_preflight_rejects_single_input_footguns() {
        let t = 1u64 << 20;
        let engine = FoldEngine::cpu_only();

        let mut noncanonical = synth_ct(1, 1);
        noncanonical.polys[0].rows[0][0] = noncanonical.moduli[0];
        assert!(matches!(
            engine.fold(&[noncanonical], t),
            Err(BfvLeanError::NonCanonical { modulus_index: 0 })
        ));

        let mut zero_degree = synth_ct(2, 1);
        zero_degree.degree = 0;
        for poly in &mut zero_degree.polys {
            for row in &mut poly.rows {
                row.clear();
            }
        }
        assert!(matches!(
            engine.fold(&[zero_degree], t),
            Err(BfvLeanError::Incompatible(_))
        ));

        let wraps_without_an_add = synth_ct(3, t);
        assert!(matches!(
            engine.fold(&[wraps_without_an_add], t),
            Err(BfvLeanError::WrapRefused {
                bound_sum,
                plaintext_modulus,
            }) if bound_sum == u128::from(t) && plaintext_modulus == t
        ));

        // The CPU oracle's one-subtract addition also assumes a+b cannot overflow u64. Refuse an
        // arbitrary modulus outside that proved envelope before adapter presence can affect behavior.
        let mut carry_unsafe = synth_ct(4, 1);
        carry_unsafe.moduli[0] = (1u64 << 63) + 1;
        assert!(matches!(
            engine.fold(&[carry_unsafe], t),
            Err(BfvLeanError::Incompatible(_))
        ));
    }

    #[test]
    fn paired_fold_matches_two_cpu_folds_and_keeps_metadata_separate() {
        let t = 1u64 << 20;
        let first: Vec<_> = (0..5).map(|i| synth_ct(i + 1, 2)).collect();
        let mut second: Vec<_> = (0..7).map(|i| synth_ct(i + 101, 3)).collect();
        second[0].variable_time = true;
        let expected_first = fold(&first, t).expect("first CPU fold");
        let expected_second = fold(&second, t).expect("second CPU fold");

        let engine = FoldEngine::new();
        let (got_first, got_second) = engine
            .fold_pair(&first, &second, t)
            .expect("paired retained fold");
        assert_eq!(got_first.ciphertext, expected_first);
        assert_eq!(got_second.ciphertext, expected_second);
        assert!(!got_first.ciphertext.variable_time);
        assert!(got_second.ciphertext.variable_time);
        assert_eq!(got_first.ciphertext.plain_bound, 10);
        assert_eq!(got_second.ciphertext.plain_bound, 21);
        match (got_first.backend, got_second.backend) {
            (FoldBackend::GpuResident(_), FoldBackend::GpuResident(_)) => {
                eprintln!("paired retained fold: resident wgpu dispatch exercised")
            }
            (FoldBackend::CpuNoArena, FoldBackend::CpuNoArena) => {
                eprintln!("paired retained fold: no arena, CPU fallback exercised")
            }
            other => panic!("paired exact fold selected inconsistent backends: {other:?}"),
        }
    }

    /// The direct staging gather must respect handle boundaries, not merely work for the production
    /// one-ciphertext/one-ciphertext pair. The second handle deliberately contains TWO ciphertexts with
    /// distinct bounds and variable-time flags, so a wrong destination offset or flattened metadata index
    /// changes a full polynomial or visibly attaches the wrong scalar bookkeeping.
    #[test]
    fn gathered_readback_preserves_heterogeneous_handle_boundaries() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — heterogeneous gather parity SKIPPED (headless runner)");
            return;
        };
        let t = 1u64 << 20;
        let first_inputs = vec![synth_ct(1, 2), synth_ct(2, 3)];
        let mut second_inputs = vec![synth_ct(101, 7), synth_ct(102, 11)];
        second_inputs[0].variable_time = true;
        let third_inputs = vec![synth_ct(201, 13), synth_ct(202, 17), synth_ct(203, 19)];
        let expected = vec![
            fold(&first_inputs, t).expect("first CPU fold"),
            fold(&second_inputs, t).expect("second CPU fold"),
            fold(&third_inputs, t).expect("third CPU fold"),
        ];

        let first = a.fold_resident(&a.upload(&first_inputs));
        let second = a.fold_resident(&a.upload(&second_inputs));
        let third = a.fold_resident(&a.upload(&third_inputs));
        let two_outputs = a.concat_resident(&[second, third]);
        assert_eq!(first.n_cts, 1);
        assert_eq!(two_outputs.n_cts, 2);
        assert_eq!(first.bounds, vec![5]);
        assert_eq!(two_outputs.bounds, vec![18, 49]);
        assert_eq!(first.variable_times, vec![false]);
        assert_eq!(two_outputs.variable_times, vec![true, false]);

        assert_eq!(
            a.download_many(&[&first, &two_outputs]),
            expected,
            "direct gather crossed a resident-handle data or metadata boundary"
        );
    }

    /// Production-shaped crossover probe: two independent book sides, comparing two CPU folds, two
    /// separately synchronized retained-GPU folds, and the paired one-readback path. Run explicitly in
    /// release on a real adapter; it is ignored so timing work never enters the default test loop.
    #[test]
    #[ignore = "bench — run release/ignored/no-capture on a real wgpu adapter"]
    fn bench_paired_readback_crossover() {
        let engine = FoldEngine::new();
        if !engine.has_gpu_arena() {
            eprintln!("no wgpu adapter — paired crossover bench SKIPPED (headless runner)");
            return;
        }
        let t = 1u64 << 20;
        let max_n = std::env::var("ARENA_PAIR_MAX_N")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(1024);
        let reps = std::env::var("ARENA_PAIR_REPS")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(3)
            .max(1);
        let sweep = [1usize, 2, 4, 8, 16, 64, 256, 1024]
            .into_iter()
            .filter(|&n| n <= max_n)
            .collect::<Vec<_>>();

        // Warm pipeline, queue, and the exact-size readback cache outside measurements.
        let warm_first = vec![synth_ct(1, 1), synth_ct(2, 1)];
        let warm_second = vec![synth_ct(3, 1), synth_ct(4, 1)];
        engine
            .fold_pair(&warm_first, &warm_second, t)
            .expect("paired warmup");

        eprintln!("\npaired resident crossover (two sides, best-of-{reps}; one ct = 196608 bytes)");
        eprintln!(
            "{:>6} {:>9} {:>12} {:>15} {:>15} {:>10} {:>10}",
            "N/side",
            "input MB",
            "CPU pair",
            "GPU separate",
            "GPU one-read",
            "pair/CPU",
            "pair/sep"
        );
        for n in sweep {
            let first = (0..n as u64)
                .map(|i| synth_ct(i + 11, 1))
                .collect::<Vec<_>>();
            let second = (0..n as u64)
                .map(|i| synth_ct(i + 10_011, 1))
                .collect::<Vec<_>>();
            let expected_first = fold(&first, t).expect("first CPU oracle");
            let expected_second = fold(&second, t).expect("second CPU oracle");

            let mut cpu_best = Duration::MAX;
            let mut separate_best = Duration::MAX;
            let mut paired_best = Duration::MAX;
            for _ in 0..reps {
                let started = Instant::now();
                std::hint::black_box(fold(&first, t).expect("first CPU measurement"));
                std::hint::black_box(fold(&second, t).expect("second CPU measurement"));
                cpu_best = cpu_best.min(started.elapsed());

                let started = Instant::now();
                let separately_first = engine.fold(&first, t).expect("first retained GPU fold");
                let separately_second = engine.fold(&second, t).expect("second retained GPU fold");
                separate_best = separate_best.min(started.elapsed());
                assert_eq!(separately_first.ciphertext, expected_first);
                assert_eq!(separately_second.ciphertext, expected_second);

                let started = Instant::now();
                let (paired_first, paired_second) = engine
                    .fold_pair(&first, &second, t)
                    .expect("paired GPU fold");
                paired_best = paired_best.min(started.elapsed());
                assert_eq!(paired_first.ciphertext, expected_first);
                assert_eq!(paired_second.ciphertext, expected_second);
            }

            let cpu_ms = cpu_best.as_secs_f64() * 1e3;
            let separate_ms = separate_best.as_secs_f64() * 1e3;
            let paired_ms = paired_best.as_secs_f64() * 1e3;
            eprintln!(
                "{n:>6} {:>9.1} {cpu_ms:>10.2}ms {separate_ms:>13.2}ms {paired_ms:>13.2}ms {:>9.2}x {:>9.2}x",
                2.0 * n as f64 * 196_608.0 / 1e6,
                paired_ms / cpu_ms,
                paired_ms / separate_ms,
            );
        }
    }

    /// Force a tiny upload limit even on a large adapter so CI on a real GPU exercises the exact seam the
    /// production adapter limit triggers: multiple bounded uploads, device-to-device concatenate, and two
    /// recursive reduction layers before the only readback. The plan and bound carry are part of parity.
    #[test]
    fn forced_small_chunks_reduce_recursively_and_match_cpu() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — forced streaming parity SKIPPED (headless runner)");
            return;
        };
        let t = 1u64 << 20;
        let cts: Vec<_> = (0..17).map(|i| synth_ct(i + 1, 3)).collect();
        let expected = fold(&cts, t).expect("cpu reference");
        let (resident, plan) = a
            .fold_streaming_with_limit(&cts, t, Some(3))
            .expect("bounded resident fold");
        assert_eq!(
            plan,
            ResidentFoldPlan {
                input_ciphertexts: 17,
                ciphertexts_per_chunk: 3,
                upload_chunks: 6,
                reduction_rounds: 2,
            }
        );
        let got = a.download(&resident);
        assert_eq!(got, vec![expected]);
        assert_eq!(got[0].plain_bound, 51);

        // A real arena plus a shape outside this three-modulus stone takes the explicitly labelled CPU
        // path. This is a capability fallback, not a catch-all: GPU execution errors still propagate.
        let mut unsupported: Vec<_> = (0..3).map(|i| synth_ct(i + 41, 2)).collect();
        for ct in &mut unsupported {
            ct.moduli.pop();
            for poly in &mut ct.polys {
                poly.rows.pop();
            }
        }
        let unsupported_expected = fold(&unsupported, t).expect("two-modulus CPU reference");
        let engine = FoldEngine {
            gpu: Some(a),
            run_lock: Mutex::new(()),
        };
        let fallback = engine
            .fold(&unsupported, t)
            .expect("unsupported shape falls back explicitly");
        assert_eq!(fallback.ciphertext, unsupported_expected);
        assert_eq!(fallback.backend, FoldBackend::CpuUnsupportedShape);
    }

    /// THE PARITY TOOTH: resident upload → fold_resident → download must equal the oracle-validated CPU
    /// `fold` bit-for-bit, INCLUDING a fold-of-a-fold (the output buffer re-bound as shader input — the
    /// device-to-device path one-shot fold_gpu never exercises). Any error in the upload layout, the meta
    /// uniform, the resident rebind, or the download unpack diverges here and goes RED. Headless → explicit
    /// SKIP line, never a silent pass.
    #[test]
    fn resident_fold_matches_cpu_fold_bit_for_bit() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — resident parity SKIPPED (headless runner)");
            return;
        };
        let cts: Vec<_> = (0..23).map(|i| synth_ct(i + 1, 3)).collect();
        let t = 1u64 << 20;
        let cpu = fold(&cts, t).expect("cpu fold");

        let h = a.upload(&cts);
        let folded = a.fold_resident(&h);
        let got = a.download(&folded);
        assert_eq!(got.len(), 1);
        assert_eq!(
            got[0], cpu,
            "resident GPU fold diverged from the oracle-validated CPU fold"
        );

        // fold-of-a-fold: folding the 1-ct resident result must be the identity (sum of one addend),
        // proving a fold OUTPUT is a valid fold INPUT while still resident.
        let refolded = a.fold_resident(&folded);
        let got2 = a.download(&refolded);
        assert_eq!(
            got2[0].polys, cpu.polys,
            "fold-of-a-fold diverged — resident output buffer is not rebinding correctly as input"
        );
        assert_eq!(got2[0].plain_bound, cpu.plain_bound);
    }

    /// The wrap-gate BOOKKEEPING survives residency: the downloaded fold carries plain_bound = the exact
    /// sum of the inputs' bounds, so the downstream gate (fold_add) still REFUSES a wrap on it. This bites:
    /// zero the carried bound (the natural bug — bounds are host-side scalars the GPU never sees) and the
    /// downstream fold_add stops refusing.
    #[test]
    fn downloaded_bound_still_arms_the_downstream_wrap_gate() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — bound-carry test SKIPPED (headless runner)");
            return;
        };
        let t = 1u64 << 20;
        // 8 cts of bound (t-1)/8 fold fine; their sum is t-8... adding one more bound-8 ct must refuse.
        let per = (t - 1) / 8;
        let cts: Vec<_> = (0..8).map(|i| synth_ct(i + 1, per)).collect();
        let h = a.upload(&cts);
        let folded = a.download(&a.fold_resident(&h));
        assert_eq!(
            folded[0].plain_bound,
            per * 8,
            "bound must be the exact sum"
        );
        assert!(folded[0].variable_time == false);

        let extra = synth_ct(99, t - per * 8); // pushes the sum to exactly t → must refuse
        assert!(
            matches!(
                fold_add(&folded[0], &extra, t),
                Err(BfvLeanError::WrapRefused { .. })
            ),
            "downstream wrap gate must still fire on the downloaded fold's carried bound"
        );
        // variable_time ORs through residency like fold_add ORs it.
        let mut vt = synth_ct(7, 1);
        vt.variable_time = true;
        let h2 = a.upload(&[synth_ct(8, 1), vt]);
        assert!(a.download(&a.fold_resident(&h2))[0].variable_time);
    }

    /// Fail-loud shape policy (no error channel in the frozen §3 signature): mixed shapes must panic,
    /// never fold garbage.
    #[test]
    #[should_panic(expected = "disagrees on fold shape")]
    fn upload_panics_on_mixed_shapes() {
        let Some(a) = arena() else {
            // Headless: no adapter to validate against — panic with the expected message so the
            // should_panic contract holds identically (the check itself is host-side and unreachable
            // without an arena).
            panic!("SKIP (headless): ciphertext 1 disagrees on fold shape");
        };
        let good = synth_ct(1, 1);
        let mut bad = synth_ct(2, 1);
        bad.level = 5;
        let _ = a.upload(&[good, bad]);
    }

    /// THE RESIDENCY THESIS, MEASURED (run explicitly: `cargo test -p fhegg-fhe --lib gpu_arena --release
    /// -- --ignored --nocapture`). Pattern: repeated aggregation — upload N cts ONCE, fold_resident K
    /// times on-device, download ONCE. CPU does the identical K full folds. This is exactly the size/shape
    /// where one-shot fold_gpu LOST 5–7x (gpu_saturate 2026-07-18); the one-shot path is timed alongside
    /// as context. Parity asserted at every size. The win assertion (resident < CPU) is the tooth — if
    /// residency cannot beat the CPU even here, this test goes RED and that is the honest finding.
    #[test]
    #[ignore = "bench — run in --release with --ignored --nocapture (debug timings are meaningless)"]
    fn bench_residency_thesis_upload_once_fold_k_times() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — residency bench SKIPPED (headless runner)");
            return;
        };
        let t = 1u64 << 20;
        let k: usize = std::env::var("ARENA_K")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8);
        let sweep: Vec<usize> = [1024usize, 4096, 8192].to_vec();
        // (cpu_s, one_shot_s, res_s) per size — the thesis assertion runs over the whole sweep.
        let mut rows: Vec<(usize, f64, Option<f64>, f64)> = Vec::new();
        println!(
            "\nresidency bench (M-series Metal unless stated): K={k} folds per pattern, deg 4096 x 3 RNS x 2 polys"
        );
        println!(
            "{:>6} {:>9} {:>12} {:>14} {:>14} {:>9} {:>9}",
            "N", "MB", "CPU K-folds", "one-shot xK", "resident e2e", "res/CPU", "parity"
        );
        for &n in &sweep {
            let cts: Vec<_> = (0..n as u64).map(|i| synth_ct(i + 1, 1)).collect();
            let mb = (n * 24576 * 8) as f64 / 1e6;

            // CPU: K full folds (the work the resident path replaces), total wall time.
            let t0 = Instant::now();
            let mut cpu_ref = None;
            for _ in 0..k {
                cpu_ref = Some(fold(&cts, t).expect("cpu fold"));
            }
            let cpu_s = t0.elapsed().as_secs_f64();
            let cpu_ref = cpu_ref.unwrap();

            // One-shot GPU context: K independent fold_gpu calls (pack+upload+dispatch+readback each).
            let one_shot = {
                let t0 = Instant::now();
                let mut r = Ok(());
                for _ in 0..k {
                    if let Err(e) = crate::bfv_gpu::fold_gpu(&cts, t) {
                        r = Err(e);
                        break;
                    }
                }
                r.map(|_| t0.elapsed().as_secs_f64())
            };

            // RESIDENT: upload once, K folds on-device, download once. End-to-end including upload+download.
            let t0 = Instant::now();
            let h = a.upload(&cts);
            let mut last = None;
            for _ in 0..k {
                last = Some(a.fold_resident(&h));
            }
            let got = a.download(&last.unwrap());
            let res_s = t0.elapsed().as_secs_f64();

            let parity = if got[0] == cpu_ref {
                "BIT-EXACT"
            } else {
                "DIVERGED"
            };
            let one_shot_s = one_shot
                .as_ref()
                .map(|s| format!("{:>12.1}ms", s * 1e3))
                .unwrap_or_else(|e| format!("ERR:{e}"));
            println!(
                "{:>6} {:>9.0} {:>10.1}ms {:>14} {:>12.1}ms {:>9.2}x {:>9}",
                n,
                mb,
                cpu_s * 1e3,
                one_shot_s,
                res_s * 1e3,
                cpu_s / res_s,
                parity
            );
            assert_eq!(got[0], cpu_ref, "resident bench parity broke at N={n}");
            rows.push((n, cpu_s, one_shot.ok(), res_s));
        }

        // THE TOOTH — the contract's exact thesis (§3): residency must BEAT THE CPU at a size where the
        // one-shot fold_gpu LOST to the CPU. Also, mechanism check: resident must beat one-shot at EVERY
        // size (if it does not, the arena is not actually removing the transfer). Red = thesis falsified
        // on this adapter, and that red IS the finding.
        for (n, _, one_shot_s, res_s) in &rows {
            if let Some(os) = one_shot_s {
                assert!(
                    res_s < os,
                    "resident ({res_s:.3}s) did not beat one-shot ({os:.3}s) at N={n} — residency mechanism broken"
                );
            }
        }
        let thesis = rows.iter().any(|(_, cpu_s, one_shot_s, res_s)| {
            matches!(one_shot_s, Some(os) if os > cpu_s) // one-shot LOST here
                && res_s < cpu_s // resident WINS here
        });
        assert!(
            thesis,
            "residency thesis FALSIFIED on this adapter (K={k}): no size where one-shot lost AND resident beat the CPU. rows={rows:?}"
        );
    }
}
