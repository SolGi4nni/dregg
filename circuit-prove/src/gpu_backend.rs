//! THE GPU PROVER BACKEND: the measured wgpu kernels wired BEHIND Plonky3's
//! prover trait seams, and a GPU variant of the outer "shrink" config.
//!
//! docs/deos/GPU-PROVER-WIRING-PLAN.md names the two seams of
//! `TwoAdicFriPcs` (both provers are `TwoAdicFriPcs<Val, Dft, ValMmcs,
//! ChallengeMmcs>`):
//!
//! 1. **the DFT** ([`TwoAdicSubgroupDft`]) — [`GpuDft`] here, lifted from the
//!    parity-proven sketch `circuit-prove/sketches/gpu-dft-plonky3` (measured
//!    4-10x vs `Radix2DitParallel` at the pcs-shaped LDE expression). Clean
//!    seam: same `Evaluations = BitReversedMatrixView<RowMajorMatrix<..>>`
//!    type/layout as `Radix2DitParallel`, so the PCS's
//!    `.bit_reverse_rows().to_row_major_matrix()` stays free. ~1-2% of the
//!    shrink prove (the template seam, not the lever).
//! 2. **the MMCS tree build** — there is no batch seam at the hasher traits
//!    (`CryptographicHasher`/`PseudoCompressionFunction` are per-node), so
//!    [`GpuBn254Mmcs`] is an alternative [`Mmcs<BabyBear>`] whose `commit`
//!    builds the digest layers with batched GPU permutation kernels
//!    (`circuit-prove/sketches/bn254-poseidon2-wgpu`: BN254 t=3 Poseidon2).
//!    Native Vulkan uses the precompiled direct-SPIR-V/native-int64 kernel
//!    (13.688 Mperm/s RADV, 24.738 Mperm/s AMDVLK on Navi 22); other backends
//!    retain the portable WGSL engine. This is the shrink prove's dominant
//!    term (~60%, the Amdahl lever).
//!
//! ## Bit-exactness contract (the parity gates in `tests` below)
//!
//! [`GpuBn254Mmcs`] reproduces `MerkleTreeMmcs<BabyBear, Bn254, OuterHash,
//! OuterCompress, 2, 1>` EXACTLY:
//!
//! - same `Commitment` type (`MerkleCap<BabyBear, [Bn254; 1]>`) and same
//!   `Proof` type (`Vec<[Bn254; 1]>`, the unpruned sibling path);
//! - leaf hash = `MultiField32PaddingFreeSponge<BabyBear, Bn254, _, 3, 2, 1>`
//!   (shifted radix-2^31 packing, 8 limbs/slot, 2 slots/permutation,
//!   overwrite-mode absorb, digest = state[0]);
//! - node compression = `TruncatedPermutation<_, 2, 1, 3>`
//!   (permute([l, r, 0]), lane 0);
//! - multi-matrix injection at matching heights (`compress_and_inject`
//!   semantics, restricted to the power-of-two heights the PCS produces);
//! - `verify_batch` DELEGATES to the real CPU `MerkleTreeMmcs` — a GPU-minted
//!   proof is verified by the untouched CPU verifier code path.
//!
//! Because the roots are bit-exact and the Fiat–Shamir transcript only sees
//! commitments + opened values, a proof minted under [`GpuDreggOuterConfig`]
//! is BYTE-IDENTICAL to one minted under the CPU [`DreggOuterConfig`] for the
//! same input (both provers are deterministic), and it round-trips through
//! serde into a `BatchStarkProof<DreggOuterConfig>` that the unchanged CPU
//! `verify_shrink_proof` accepts. Both properties are asserted in tests.
//!
//! ## Runtime dispatch, not feature gates
//!
//! No GPU adapter, non-power-of-two heights, sub-threshold work, or
//! cap_height != 0 all fall back to the CPU path (`Radix2DitParallel` /
//! `MerkleTreeMmcs`) inside the same types. The GPU path only ever changes
//! WHERE the identical function is computed.
//!
//! ## HONEST SCOPE — what is and is not GPU'd
//!
//! - GPU: the LDE/DFT (seam 1); the BN254 Merkle tree build for every commit
//!   whose shape qualifies — main-trace LDEs, quotient LDEs, preprocessed
//!   commit, and the FRI commit-phase trees down to the dispatch threshold.
//! - CPU (by structure, per the wiring plan): the FRI query phase, the
//!   MultiField challenger transcript, per-query Merkle openings (host walks
//!   of already-built layers), constraint/quotient evaluation, and witness
//!   generation.
//! - NTT→hash device residency (plan §3) IS wired for the upload direction:
//!   `coset_lde_batch` parks its output on the device (the final transpose
//!   kernel writes a dedicated retained buffer) and `GpuBn254Mmcs::commit`
//!   consumes it with a device→device blit into the leaf arena, skipping the
//!   host staging copy + `write_buffer` re-upload. The host READBACK remains
//!   by structure: the PCS seam (`.to_row_major_matrix()`) and the FRI
//!   query/fold phases read the committed matrix on the host. See the
//!   "LDE device-residency" section below for the binding contract.
//! - The all-BabyBear inner (apex-fold) MMCS + DFT are wired through the
//!   production recursion-layer dispatch below.  Native uses wgpu when an
//!   adapter is present; native-without-GPU and wasm keep the CPU recursion
//!   path, while the browser async WGSL engine remains available via
//!   [`init_gpu`].

// On wasm32 the sync-config GPU machinery is intentionally CPU-shelled (wgpu
// handles are `!Send + !Sync` there), so the native-only imports and the
// CPU-fallback branches read as dead code / unused imports. That is by design
// — the on-device GPU path on wasm is the async engine at the file end.
#![cfg_attr(
    target_arch = "wasm32",
    allow(dead_code, unused_imports, unused_variables)
)]

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use num_bigint::BigUint;
use p3_baby_bear::{
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
    BABYBEAR_POSEIDON2_RC_16_INTERNAL, BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16,
};
use p3_batch_stark::ProverData;
use p3_bn254::Bn254;
use p3_challenger::DuplexChallenger;
use p3_circuit::{Circuit, CircuitBuilder};
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile,
    TablePacking,
    common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_commit::{BatchOpening, BatchOpeningRef, ExtensionMmcs, Mmcs};
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_lookup::Lookups;
use p3_lookup::logup::LogUpGadget;
use p3_matrix::Matrix;
use p3_matrix::bitrev::{BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::{MerkleTreeError, MerkleTreeMmcs};
use p3_recursion::traits::RecursiveAir;
use p3_recursion::{
    AggExposeHook, BatchOnly, NextLayerExposeHook, PcsRecursionBackend, ProveNextLayerParams,
    RecursionInput, RecursionOutput, VerifierCircuitResult, build_and_prove_next_layer_with_expose,
    build_next_layer_circuit, build_next_layer_circuit_with_expose, ops::Poseidon2Config,
};
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkConfig, StarkGenericConfig};
use rayon::prelude::*;

use crate::apex_shrink::default_shrink_packing;
use crate::dregg_outer_config::{
    DreggOuterConfig, OUTER_FRI_LOG_BLOWUP, OUTER_FRI_NUM_QUERIES, OUTER_FRI_QUERY_POW_BITS,
    OuterChallenge, OuterChallenger, OuterCompress, OuterHash, OuterValMmcs, RC3_EXT_INITIAL,
    RC3_EXT_TERMINAL, RC3_INTERNAL, dregg_poseidon2_bn254,
};
use crate::ivc_turn_chain::ir2_leaf_wrap_config;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, create_recursion_config,
};

// ============================================================================
// Shared BabyBear host helpers (Montgomery <-> canonical, raw casts)
// ============================================================================

/// BabyBear prime.
const BB_P: u32 = 0x7800_0001;

fn bb_to_mont(a: u32) -> u32 {
    (((a as u64) << 32) % BB_P as u64) as u32
}

fn bb_mulmod(a: u64, b: u64) -> u64 {
    a * b % BB_P as u64
}

fn bb_powmod(mut b: u64, mut e: u64) -> u64 {
    let mut acc = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            acc = bb_mulmod(acc, b);
        }
        b = bb_mulmod(b, b);
        e >>= 1;
    }
    acc
}

/// `BabyBear` is repr(transparent) over its Montgomery-form u32
/// (monty-31/src/monty_31.rs) — reinterpret slices directly.
fn bb_as_u32s(v: &[BabyBear]) -> &[u32] {
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u32, v.len()) }
}

/// All GPU outputs are reduced (< P): the kernels keep the Montgomery
/// invariant, so every u32 is a valid MontyField31 representation.
fn u32s_into_bb(mut v: Vec<u32>) -> Vec<BabyBear> {
    let ptr = v.as_mut_ptr();
    let (len, cap) = (v.len(), v.capacity());
    std::mem::forget(v);
    unsafe { Vec::from_raw_parts(ptr as *mut BabyBear, len, cap) }
}

// ============================================================================
// The shared wgpu device — ONE device/queue for the DFT and the hash engine.
//
// Two reasons it is a process-wide static:
// 1. LDE device-residency requires the DFT's output buffer to be bindable by
//    the MMCS blit — wgpu buffers are device-scoped, so both seams must share
//    one device.
// 2. The teardown fix: buffers dropped late (thread-local config destructors
//    at thread exit) used to race the device's own drop — wgpu 24.0.5 panics
//    in `SnatchLock::read` (`Buffer::unmap_inner` → `buffer_drop`) when a
//    buffer drops after its device is destroyed. A `'static` device outlives
//    every buffer by construction, so cleanup is always well-ordered.
// ============================================================================

struct SharedGpu {
    /// Kept alive for the life of the process (never torn down before any
    /// late buffer drop).
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter_name: String,
    /// True only when the selected adapter is Vulkan and the device was
    /// created with the two features required by the precompiled native-int64
    /// BN254 Poseidon2 module.
    direct_bn254_spirv: bool,
    max_buf_u32s: usize,
}

// The process-wide device is a `Sync` static ONLY on native: on wasm32 the
// WebGPU handles are `!Send + !Sync` (they wrap JS objects behind a `RefCell`),
// so they cannot live in a `static`, and adapter/device acquisition MUST be
// async (no `pollster::block_on` on the browser main thread). The wasm path
// therefore acquires the device via `async fn init_gpu()` (see the WASM /
// WebGPU async engine at the end of this file) and threads it explicitly
// through the worker-run async prover core, never through a global. The whole
// blocking-init machinery below is native-only by construction.
#[cfg(not(target_arch = "wasm32"))]
static SHARED_GPU: OnceLock<Option<SharedGpu>> = OnceLock::new();

#[cfg(not(target_arch = "wasm32"))]
fn shared_gpu() -> Option<&'static SharedGpu> {
    SHARED_GPU
        .get_or_init(|| {
            let instance = wgpu::Instance::default();
            let adapter =
                pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
                    power_preference: wgpu::PowerPreference::HighPerformance,
                    ..Default::default()
                }))?;
            let info = adapter.get_info();
            let lims = adapter.limits();
            let direct_spirv_features =
                wgpu::Features::SHADER_INT64 | wgpu::Features::SPIRV_SHADER_PASSTHROUGH;
            let direct_bn254_spirv = info.backend == wgpu::Backend::Vulkan
                && adapter.features().contains(direct_spirv_features);
            let (device, queue) = pollster::block_on(adapter.request_device(
                &wgpu::DeviceDescriptor {
                    label: None,
                    required_features: if direct_bn254_spirv {
                        direct_spirv_features
                    } else {
                        wgpu::Features::empty()
                    },
                    required_limits: lims.clone(),
                    memory_hints: Default::default(),
                },
                None,
            ))
            .ok()?;
            let max_buf_u32s = (lims
                .max_buffer_size
                .min(lims.max_storage_buffer_binding_size as u64)
                .min(1 << 31) as usize)
                / 4;
            Some(SharedGpu {
                _instance: instance,
                device,
                queue,
                adapter_name: format!("{} ({:?})", info.name, info.backend),
                direct_bn254_spirv,
                max_buf_u32s,
            })
        })
        .as_ref()
}

// ============================================================================
// LDE device-residency — the NTT→hash hand-off (plan §3, upload direction).
//
// `TwoAdicFriPcs::commit` computes `coset_lde_batch(evals, ..).bit_reverse_
// rows().to_row_major_matrix()` and passes the result to `Mmcs::commit`. For
// our `Evaluations = BitReversedMatrixView<RowMajorMatrix<BabyBear>>` the
// `bit_reverse_rows()` unwraps to the inner matrix and `to_row_major_matrix`
// is `Vec::to_vec(self) -> self` — the EXACT allocation minted in `gpu_flow`
// arrives at `commit`. So `coset_lde_batch` registers its retained device
// buffer under the key `(thread, values.as_ptr(), values.len())`, and the
// tree build consumes it (device→device blit into the leaf arena) instead of
// re-uploading the host bytes.
//
// Binding contract (why a hit blits the RIGHT data):
// - Among LIVE allocations, (ptr, len) is unique — a hit on a live entry is
//   the registered Vec itself, whose contents are byte-identical to the
//   retained buffer (both are the same kernel output).
// - A STALE entry (registered Vec dropped uncommitted, allocation reused)
//   is guarded three ways: entries are one-shot (removed on consume), the
//   registry is cleared for the thread at the end of every `commit`
//   (in the prover flow every LDE is committed immediately after minting),
//   and a hit must additionally match LDE_GUARD_SAMPLES sampled raw words of
//   the committed matrix against the host copy recorded at registration.
//   A guard mismatch falls back to the host upload, which is always correct.
// - Correctness NEVER depends on a hit: any miss/eviction is the old path.
//   The root-parity and byte-identical gates below re-assert the equivalence
//   on every run.
// ============================================================================

// The residency counters are plain atomics — `Sync` on every target — so the
// public accessor stays available on wasm (it simply reads 0/0 there, since the
// device-resident LDE hand-off is a native-only optimisation: it parks a
// `wgpu::Buffer` in a process-wide `Mutex`, and wgpu buffers are `!Send` on
// wasm, so the registry itself is native-only).
static LDE_RESIDENT_HITS: AtomicU64 = AtomicU64::new(0);
static LDE_RESIDENT_MISSES: AtomicU64 = AtomicU64::new(0);

/// (hits, misses) of the device-resident LDE hand-off across the process —
/// a hit is one leaf-arena upload replaced by a device→device blit.
pub fn lde_residency_counters() -> (u64, u64) {
    (
        LDE_RESIDENT_HITS.load(Ordering::Relaxed),
        LDE_RESIDENT_MISSES.load(Ordering::Relaxed),
    )
}

/// On wasm the resident-LDE registry does not exist (wgpu buffers are `!Send`);
/// the commit path calls this at the end of the CPU fallback, so it is a no-op.
#[cfg(target_arch = "wasm32")]
fn clear_thread_resident_ldes() {}

/// Sampled raw (Montgomery) words checked before a resident buffer is used.
#[cfg(not(target_arch = "wasm32"))]
const LDE_GUARD_SAMPLES: usize = 64;
/// Registry caps — evicting an entry only costs the fallback upload.
#[cfg(not(target_arch = "wasm32"))]
const LDE_REGISTRY_MAX_ENTRIES: usize = 128;
#[cfg(not(target_arch = "wasm32"))]
const LDE_REGISTRY_MAX_BYTES: u64 = 6 << 30;

#[cfg(not(target_arch = "wasm32"))]
struct ResidentLde {
    buf: wgpu::Buffer,
    bytes: u64,
    seq: u64,
    /// (flat index, raw word) samples of the host copy at registration.
    guard: Vec<(usize, u32)>,
}

/// (registering thread, host values ptr, host values len).
#[cfg(not(target_arch = "wasm32"))]
type LdeKey = (std::thread::ThreadId, usize, usize);

#[cfg(not(target_arch = "wasm32"))]
#[derive(Default)]
struct LdeRegistry {
    map: HashMap<LdeKey, ResidentLde>,
    bytes: u64,
    seq: u64,
}

#[cfg(not(target_arch = "wasm32"))]
static LDE_REGISTRY: OnceLock<Mutex<LdeRegistry>> = OnceLock::new();

#[cfg(not(target_arch = "wasm32"))]
fn lde_registry() -> &'static Mutex<LdeRegistry> {
    LDE_REGISTRY.get_or_init(|| Mutex::new(LdeRegistry::default()))
}

/// Runtime escape hatch for isolating/disabling the optional device-resident
/// DFT->MMCS hand-off. The host-upload path remains the bit-exact baseline.
#[cfg(not(target_arch = "wasm32"))]
fn lde_residency_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_GPU_LDE_RESIDENCY")
            .unwrap_or_default()
            .trim()
            .to_ascii_lowercase()
            .as_str(),
        "off" | "false" | "0" | "host"
    )
}

#[cfg(not(target_arch = "wasm32"))]
fn gpu_runtime_stage_enabled(var: &str) -> bool {
    !matches!(
        std::env::var(var)
            .unwrap_or_default()
            .trim()
            .to_ascii_lowercase()
            .as_str(),
        "off" | "false" | "0" | "cpu"
    )
}

/// Park a coset-LDE's retained device buffer, keyed by the host allocation
/// that `TwoAdicFriPcs::commit` will hand to `Mmcs::commit`.
#[cfg(not(target_arch = "wasm32"))]
fn register_resident_lde(values: &[BabyBear], buf: wgpu::Buffer) {
    let len = values.len();
    if len == 0 {
        return;
    }
    let raw = bb_as_u32s(values);
    let guard: Vec<(usize, u32)> = (0..LDE_GUARD_SAMPLES)
        .map(|i| {
            let idx = i * (len - 1) / (LDE_GUARD_SAMPLES - 1);
            (idx, raw[idx])
        })
        .collect();
    let bytes = (len * 4) as u64;
    let key: LdeKey = (std::thread::current().id(), values.as_ptr() as usize, len);
    let mut reg = lde_registry().lock().unwrap();
    reg.seq += 1;
    let seq = reg.seq;
    if let Some(old) = reg.map.insert(
        key,
        ResidentLde {
            buf,
            bytes,
            seq,
            guard,
        },
    ) {
        reg.bytes -= old.bytes;
    }
    reg.bytes += bytes;
    while reg.map.len() > LDE_REGISTRY_MAX_ENTRIES || reg.bytes > LDE_REGISTRY_MAX_BYTES {
        let oldest = reg
            .map
            .iter()
            .min_by_key(|(_, e)| e.seq)
            .map(|(k, _)| *k)
            .expect("non-empty registry over cap");
        let e = reg.map.remove(&oldest).expect("key just found");
        reg.bytes -= e.bytes;
    }
}

/// Take the resident device buffer for a matrix about to be committed, iff
/// the (thread, ptr, len) key AND the sampled-content guard both match.
#[cfg(not(target_arch = "wasm32"))]
fn take_resident_lde<M: Matrix<BabyBear>>(m: &M) -> Option<wgpu::Buffer> {
    if !lde_residency_enabled() {
        return None;
    }
    let h = m.height();
    let w = m.width();
    if h == 0 || w == 0 {
        return None;
    }
    let addr = {
        let r0 = m.row_slice(0)?;
        r0.as_ptr() as usize
    };
    let key: LdeKey = (std::thread::current().id(), addr, h * w);
    let mut reg = lde_registry().lock().unwrap();
    {
        let entry = reg.map.get(&key)?;
        for &(idx, word) in &entry.guard {
            let row = m.row_slice(idx / w)?;
            if bb_as_u32s(&row)[idx % w] != word {
                return None;
            }
        }
    }
    let entry = reg.map.remove(&key).expect("key just found");
    reg.bytes -= entry.bytes;
    Some(entry.buf)
}

/// Drop every resident entry registered by this thread — called at the end
/// of every `GpuBn254Mmcs::commit` (in the PCS flow all LDEs of a batch are
/// consumed by exactly the next commit, so leftovers are dead weight and
/// clearing them promptly closes the stale-pointer window).
#[cfg(not(target_arch = "wasm32"))]
fn clear_thread_resident_ldes() {
    let tid = std::thread::current().id();
    let mut reg = lde_registry().lock().unwrap();
    let mut freed = 0u64;
    reg.map.retain(|k, e| {
        if k.0 == tid {
            freed += e.bytes;
            false
        } else {
            true
        }
    });
    reg.bytes -= freed;
}

// ============================================================================
// SEAM 1 — GpuDft: wgpu-backed TwoAdicSubgroupDft<BabyBear>
// (lifted from circuit-prove/sketches/gpu-dft-plonky3, parity-proven there;
// re-gated in tests below)
// ============================================================================

#[cfg(not(target_arch = "wasm32"))]
const DFT_PRELUDE: &str = r#"
const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64 and no mulhi).
fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}

// Montgomery product, exactly the p3 monty-31 reduce.
fn mmul(a: u32, b: u32) -> u32 {
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r: u32 = ab.y - tp.y;
    if (ab.y < tp.y) { r += P; }
    return r;
}

fn addp(a: u32, b: u32) -> u32 {
    let s = a + b;
    return select(s, s - P, s >= P);
}

fn subp(a: u32, b: u32) -> u32 {
    var r = a - b;
    if (a < b) { r += P; }
    return r;
}

@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(1) var<storage, read> src: array<u32>;
@group(0) @binding(2) var<storage, read> tw: array<u32>;
"#;

/// Tiled transpose, row-major (H x W, W arbitrary) -> column-contiguous.
#[cfg(not(target_arch = "wasm32"))]
const K_TRANS_IN: &str = r#"
var<workgroup> tile: array<u32, 272>;
@compute @workgroup_size(16, 16)
fn main(@builtin(workgroup_id) wg: vec3<u32>, @builtin(local_invocation_id) l: vec3<u32>) {
    let c0 = wg.y * 16u;
    for (var k = 0u; k < $RPT; k++) {
        let r0 = (wg.x * $RPT + k) * 16u;
        let cr = c0 + l.x;
        if (cr < $W) { tile[l.y * 17u + l.x] = src[(r0 + l.y) * $W + cr]; }
        workgroupBarrier();
        let cw = c0 + l.y;
        if (cw < $W) { data[cw * $H + r0 + l.x] = tile[l.x * 17u + l.y]; }
        workgroupBarrier();
    }
}
"#;

/// Tiled transpose out with bit-reversed row order (the `Evaluations` inner
/// layout that makes the PCS's `.bit_reverse_rows().to_row_major_matrix()` free).
#[cfg(not(target_arch = "wasm32"))]
const K_TRANS_OUT_BITREV: &str = r#"
var<workgroup> tile: array<u32, 272>;
@compute @workgroup_size(16, 16)
fn main(@builtin(workgroup_id) wg: vec3<u32>, @builtin(local_invocation_id) l: vec3<u32>) {
    let c0 = wg.y * 16u;
    for (var k = 0u; k < $RPT; k++) {
        let p0 = (wg.x * $RPT + k) * 16u;
        let cr = c0 + l.y;
        if (cr < $W) { tile[l.y * 17u + l.x] = src[cr * $N + p0 + l.x]; }
        workgroupBarrier();
        let cw = c0 + l.x;
        let rp = reverseBits(p0 + l.y) >> $RSH;
        if (cw < $W) { data[rp * $W + cw] = tile[l.x * 17u + l.y]; }
        workgroupBarrier();
    }
}
"#;

/// LDE expand: iDFT finalize + coset scale + zero-pad stage-skip + bitrev,
/// one fused pass (see the sketch doc for the derivation).
#[cfg(not(target_arch = "wasm32"))]
const K_EXPAND: &str = r#"
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let p = gid.x;
    let c = gid.y;
    let jj = (reverseBits(p) >> $RSHN) & $HM1;
    let jsrc = ($H - jj) & $HM1;
    data[c * $N + p] = mmul(src[c * $H + jsrc], tw[$SPOFF + jj]);
}
"#;

/// 2D-tiled first NTT pass: bit-reversal folded into the load, stages 1..E1
/// in a shared tile over 2^LB adjacent columns.
#[cfg(not(target_arch = "wasm32"))]
const K_FUSED1B: &str = r#"
var<workgroup> tile: array<u32, $TILE>;
@compute @workgroup_size($WGSZ)
fn main(@builtin(local_invocation_id) l: vec3<u32>, @builtin(workgroup_id) wg: vec3<u32>) {
    let lid = l.x;
    let off = wg.y * $NN;
    let c0 = wg.x << $LB;
    for (var k = 0u; k < $TPT; k++) {
        let slot = lid + k * $WGSZ;
        let u = slot >> $LB;
        let b = slot & ((1u << $LB) - 1u);
        tile[((reverseBits(u) >> (32u - $E1)) << $LB) + b] = src[off + u * $WW + c0 + b];
    }
    workgroupBarrier();
    for (var s = 1u; s <= $E1; s++) {
        let half = 1u << (s - 1u);
        for (var k = 0u; k < $HBT; k++) {
            let sb = lid + k * $WGSZ;
            let b = sb & ((1u << $LB) - 1u);
            let bf = sb >> $LB;
            let j = bf & (half - 1u);
            let i1 = ((((bf >> (s - 1u)) << s) + j) << $LB) + b;
            let i2 = i1 + (half << $LB);
            let t = mmul(tile[i2], TW(j << ($LOGN - s)));
            let u2 = tile[i1];
            tile[i1] = addp(u2, t);
            tile[i2] = subp(u2, t);
        }
        workgroupBarrier();
    }
    for (var b2 = 0u; b2 < (1u << $LB); b2++) {
        let g = reverseBits(c0 + b2) >> (32u - ($LOGN - $E1));
        let obase = off + (g << $E1);
        for (var k = 0u; k < ($TILE >> $LB) / $WGSZ; k++) {
            let u = lid + k * $WGSZ;
            data[obase + u] = tile[(u << $LB) + b2];
        }
    }
}
"#;

/// Register-tier radix-2^R kernel: R DIT stages unrolled in registers.
#[cfg(not(target_arch = "wasm32"))]
fn radix_kernel(n: u32, logn: u32, l: u32, r: u32, wgsz: u32) -> String {
    let m = 1u32 << r;
    let mut s = String::new();
    s.push_str(&format!(
        "@compute @workgroup_size({wgsz})\nfn main(@builtin(global_invocation_id) gid: vec3<u32>) {{\n    let t = gid.x;\n    let off = gid.y * {n}u;\n"
    ));
    if l == 0 {
        s.push_str("    let tlow = 0u;\n");
        s.push_str(&format!("    let base = off + (t << {r}u);\n"));
    } else {
        s.push_str(&format!(
            "    let tlow = t & {}u;\n    let base = off + ((t >> {l}u) << {}u) + tlow;\n",
            (1u32 << l) - 1,
            l + r
        ));
    }
    for v in 0..m {
        s.push_str(&format!("    var r{v} = data[base + {}u];\n", v << l));
    }
    for st in 0..r {
        let lowmask = (1u32 << st) - 1;
        for p in 0..(m >> 1) {
            let v0 = ((p & !lowmask) << 1) | (p & lowmask);
            let v1 = v0 | (1 << st);
            let jlit = (p & lowmask) << l;
            let sh = logn - l - st - 1;
            s.push_str(&format!(
                "    {{ let tt = mmul(r{v1}, TW(({jlit}u + tlow) << {sh}u)); let uu = r{v0}; r{v0} = addp(uu, tt); r{v1} = subp(uu, tt); }}\n"
            ));
        }
    }
    for v in 0..m {
        s.push_str(&format!("    data[base + {}u] = r{v};\n", v << l));
    }
    s.push_str("}\n");
    s
}

#[cfg(not(target_arch = "wasm32"))]
fn tw_def(off: u32) -> String {
    format!("fn TW(i: u32) -> u32 {{ return tw[{off}u + i]; }}\n")
}

#[cfg(not(target_arch = "wasm32"))]
fn subst(template: &str, pairs: &[(&str, u32)]) -> String {
    let mut s = template.to_string();
    for (k, v) in pairs {
        s = s.replace(k, &format!("{v}u"));
    }
    s
}

/// Split `total` DIT stages into register-radix chunk sizes <= 5.
#[cfg(not(target_arch = "wasm32"))]
fn split_stages(total: u32) -> Vec<u32> {
    let mut out = Vec::new();
    let mut rem = total;
    while rem > 0 {
        match rem {
            6 => {
                out.extend([3, 3]);
                rem = 0;
            }
            7 => {
                out.extend([4, 3]);
                rem = 0;
            }
            r if r <= 5 => {
                out.push(r);
                rem = 0;
            }
            _ => {
                out.push(5);
                rem -= 5;
            }
        }
    }
    out
}

#[cfg(not(target_arch = "wasm32"))]
struct DftBufs {
    a: wgpu::Buffer,
    b: wgpu::Buffer,
    read: wgpu::Buffer,
    cap_u32s: usize,
    bg_ab: wgpu::BindGroup,
    bg_ba: wgpu::BindGroup,
}

#[cfg(not(target_arch = "wasm32"))]
struct DftCtx {
    // Buffers/bind groups/pipelines are declared BEFORE the device handle so
    // they drop first (and the device itself is a clone of the 'static
    // SharedGpu one, so it can never be destroyed under a live buffer).
    bgl: wgpu::BindGroupLayout,
    pipe_layout: wgpu::PipelineLayout,
    pipelines: HashMap<String, wgpu::ComputePipeline>,
    tw_buf: wgpu::Buffer,
    tw_cap_u32s: usize,
    tw_key: Option<(u32, u32, u32)>,
    bufs: Option<DftBufs>,
    max_buf_u32s: usize,
    adapter_name: String,
    device: wgpu::Device,
    queue: wgpu::Queue,
}

/// DFT bind group layout: b0 = data (rw), b1 = src (ro), b2 = tw (ro).
#[cfg(not(target_arch = "wasm32"))]
fn dft_bgl(device: &wgpu::Device) -> wgpu::BindGroupLayout {
    let entry = |binding: u32, read_only: bool| wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Storage { read_only },
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    };
    device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: None,
        entries: &[entry(0, false), entry(1, true), entry(2, true)],
    })
}

#[cfg(not(target_arch = "wasm32"))]
impl DftCtx {
    fn new() -> Option<Self> {
        let shared = shared_gpu()?;
        let device = shared.device.clone();
        let queue = shared.queue.clone();
        let bgl = dft_bgl(&device);
        let pipe_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let max_buf_u32s = shared.max_buf_u32s;
        let tw_cap_u32s = 1 << 20;
        let tw_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("tw"),
            size: (tw_cap_u32s * 4) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        Some(DftCtx {
            bgl,
            pipe_layout,
            pipelines: HashMap::new(),
            tw_buf,
            tw_cap_u32s,
            tw_key: None,
            bufs: None,
            max_buf_u32s,
            adapter_name: shared.adapter_name.clone(),
            device,
            queue,
        })
    }

    /// One DFT bind group: b0 = data (rw), b1 = src (ro), b2 = tw.
    fn bind_dft(&self, data: &wgpu::Buffer, src: &wgpu::Buffer) -> wgpu::BindGroup {
        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &self.bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: data.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: src.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: self.tw_buf.as_entire_binding(),
                },
            ],
        })
    }

    fn make_bind_groups(
        &self,
        a: &wgpu::Buffer,
        b: &wgpu::Buffer,
    ) -> (wgpu::BindGroup, wgpu::BindGroup) {
        (self.bind_dft(a, b), self.bind_dft(b, a))
    }

    fn ensure_bufs(&mut self, need_u32s: usize) {
        let need = need_u32s.next_power_of_two().max(1 << 22);
        if self.bufs.as_ref().is_none_or(|b| b.cap_u32s < need) {
            let sz = (need * 4) as u64;
            let mk = |label: &str| {
                self.device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some(label),
                    size: sz,
                    usage: wgpu::BufferUsages::STORAGE
                        | wgpu::BufferUsages::COPY_SRC
                        | wgpu::BufferUsages::COPY_DST,
                    mapped_at_creation: false,
                })
            };
            let a = mk("dft_work_a");
            let b = mk("dft_work_b");
            let read = self.device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("dft_read"),
                size: sz,
                usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });
            let (bg_ab, bg_ba) = self.make_bind_groups(&a, &b);
            self.bufs = Some(DftBufs {
                a,
                b,
                read,
                cap_u32s: need,
                bg_ab,
                bg_ba,
            });
        }
    }

    /// Ensure the tw buffer holds [tw_N (n/2) | tw_H (h/2) | shiftpow (h)].
    fn ensure_twiddles(&mut self, logh: u32, logn: u32, shift_c: u32) -> (u32, u32, u32) {
        let n = 1usize << logn;
        let h = 1usize << logh;
        let twn_off = 0u32;
        let twh_off = (n / 2) as u32;
        let sp_off = twh_off + (h / 2) as u32;
        let total = sp_off as usize + h;
        if self.tw_key == Some((logh, logn, shift_c)) {
            return (twn_off, twh_off, sp_off);
        }
        if self.tw_cap_u32s < total {
            let cap = total.next_power_of_two();
            self.tw_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("tw"),
                size: (cap * 4) as u64,
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });
            self.tw_cap_u32s = cap;
            if let Some(b) = &self.bufs {
                let (bg_ab, bg_ba) = self.make_bind_groups(&b.a, &b.b);
                let bufs = self.bufs.as_mut().unwrap();
                bufs.bg_ab = bg_ab;
                bufs.bg_ba = bg_ba;
            }
        }
        let mut tv = vec![0u32; total];
        let wn = BabyBear::two_adic_generator(logn as usize).as_canonical_u32() as u64;
        let mut acc = 1u64;
        for t in tv.iter_mut().take(n / 2) {
            *t = bb_to_mont(acc as u32);
            acc = bb_mulmod(acc, wn);
        }
        let wh = BabyBear::two_adic_generator(logh as usize).as_canonical_u32() as u64;
        let mut acc = 1u64;
        for t in 0..h / 2 {
            tv[twh_off as usize + t] = bb_to_mont(acc as u32);
            acc = bb_mulmod(acc, wh);
        }
        // shiftpow[j] = mont( (1/h) * shift^j ) — the iDFT 1/h scale folded in.
        let hinv = bb_powmod(h as u64, (BB_P - 2) as u64);
        let mut acc = hinv;
        for j in 0..h {
            tv[sp_off as usize + j] = bb_to_mont(acc as u32);
            acc = bb_mulmod(acc, shift_c as u64);
        }
        self.queue
            .write_buffer(&self.tw_buf, 0, bytemuck::cast_slice(&tv));
        self.tw_key = Some((logh, logn, shift_c));
        (twn_off, twh_off, sp_off)
    }

    fn pipeline(&mut self, key: String, wgsl: &str) -> wgpu::ComputePipeline {
        if let Some(p) = self.pipelines.get(&key) {
            return p.clone();
        }
        // Trusted module + no workgroup zero-init: both measured decisive on
        // Metal (GPU-PROVER-PROTOTYPE.md §9). Sound: kernels are index-audited
        // and every tile slot is written before read; parity re-gated in tests.
        let module = unsafe {
            self.device.create_shader_module_trusted(
                wgpu::ShaderModuleDescriptor {
                    label: Some(&key),
                    source: wgpu::ShaderSource::Wgsl(wgsl.into()),
                },
                wgpu::ShaderRuntimeChecks::unchecked(),
            )
        };
        let p = self
            .device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(&key),
                layout: Some(&self.pipe_layout),
                module: &module,
                entry_point: Some("main"),
                compilation_options: wgpu::PipelineCompilationOptions {
                    zero_initialize_workgroup_memory: false,
                    ..Default::default()
                },
                cache: None,
            });
        self.pipelines.insert(key, p.clone());
        p
    }
}

#[derive(Clone, Copy, PartialEq)]
#[cfg(not(target_arch = "wasm32"))]
enum Target {
    A,
    B,
}

/// wgpu-backed `TwoAdicSubgroupDft<BabyBear>`. `Default` is cheap; device
/// acquisition is lazy on first use and falls back to `Radix2DitParallel`
/// forever if no adapter (or below the GPU-worthwhile height threshold).
#[derive(Clone, Default)]
pub struct GpuDft {
    cpu: Radix2DitParallel<BabyBear>,
    // The GPU DFT context holds wgpu handles (`!Send + !Sync` on wasm). On
    // wasm32 `GpuDft` is a CPU-only shell so it stays `Sync` (the `TwoAdicFriPcs`
    // config bound requires it); the on-device GPU DFT is a next-pass sharpening
    // (the ~1-2% seam-1 term — the on-device async engine at the file end GPU's
    // the ~60% MMCS lever first).
    #[cfg(not(target_arch = "wasm32"))]
    ctx: Arc<OnceLock<Option<Mutex<DftCtx>>>>,
}

/// Heights below this stay on the CPU path (dispatch overhead dominates).
const MIN_GPU_LOG_H: u32 = 12;
const E1: u32 = 8;
const LB: u32 = 3;

impl GpuDft {
    #[cfg(not(target_arch = "wasm32"))]
    fn gpu(&self) -> Option<&Mutex<DftCtx>> {
        self.ctx
            .get_or_init(|| DftCtx::new().map(Mutex::new))
            .as_ref()
    }

    /// Adapter name if a GPU is available (None = permanent CPU fallback).
    /// On wasm this shell is always CPU (see `init_gpu` for the on-device path).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn adapter_name(&self) -> Option<String> {
        self.gpu().map(|m| m.lock().unwrap().adapter_name.clone())
    }

    /// Adapter name — wasm CPU-shell variant (the on-device GPU is reached via
    /// `init_gpu()`, not through this sync-config type).
    #[cfg(target_arch = "wasm32")]
    pub fn adapter_name(&self) -> Option<String> {
        None
    }

    /// Run the DFT/LDE plan. With `retain`, the final bit-reversed transpose
    /// additionally lands in a dedicated device buffer (its kernel output
    /// target — no extra copy) returned for LDE device-residency; retention
    /// is skipped on the column-chunked path (no single buffer holds the
    /// whole result there).
    #[cfg(not(target_arch = "wasm32"))]
    fn gpu_flow(
        &self,
        ctx: &mut DftCtx,
        mat: &RowMajorMatrix<BabyBear>,
        added_bits: u32,
        shift: BabyBear,
        lde: bool,
        retain: bool,
    ) -> (Vec<u32>, Option<wgpu::Buffer>) {
        let h = mat.height();
        let w = mat.width();
        let logh = h.trailing_zeros();
        let logn = logh + added_bits;
        let n = 1usize << logn;
        let shift_c = shift.as_canonical_u32();
        let (twn_off, twh_off, sp_off) = if lde {
            ctx.ensure_twiddles(logh, logn, shift_c)
        } else {
            ctx.ensure_twiddles(logh, logn, 1)
        };

        let wb_max = (ctx.max_buf_u32s / n).min(w).max(1);
        let mut out: Vec<u32> = Vec::new();
        let single = wb_max >= w;
        if !single {
            out = vec![0u32; n * w];
        }
        let mut retained_out: Option<wgpu::Buffer> = None;

        let vals = bb_as_u32s(&mat.values);
        let mut c0 = 0usize;
        while c0 < w {
            let wb = wb_max.min(w - c0);
            ctx.ensure_bufs(n * wb);

            if single {
                let bufs = ctx.bufs.as_ref().unwrap();
                ctx.queue
                    .write_buffer(&bufs.a, 0, bytemuck::cast_slice(vals));
            } else {
                let mut staging = vec![0u32; h * wb];
                staging
                    .par_chunks_mut(wb)
                    .enumerate()
                    .for_each(|(r, dst)| dst.copy_from_slice(&vals[r * w + c0..r * w + c0 + wb]));
                let bufs = ctx.bufs.as_ref().unwrap();
                ctx.queue
                    .write_buffer(&bufs.a, 0, bytemuck::cast_slice(&staging));
            }

            let mut plan: Vec<(wgpu::ComputePipeline, Target, (u32, u32))> = Vec::new();
            let wgsz = 256u32;

            // transpose in: A (row-major) -> B (column-contiguous)
            {
                let row_tiles = (h as u32) / 16;
                let rpt = row_tiles.div_ceil(32768).max(1);
                let key = format!("trans_in_h{logh}_w{w}_wb{wb}_rpt{rpt}");
                let wgsl = format!(
                    "{}{}",
                    DFT_PRELUDE,
                    subst(
                        K_TRANS_IN,
                        &[("$H", h as u32), ("$W", wb as u32), ("$RPT", rpt)]
                    )
                );
                let p = ctx.pipeline(key, &wgsl);
                plan.push((
                    p,
                    Target::B,
                    (row_tiles.div_ceil(rpt), (wb as u32).div_ceil(16)),
                ));
            }

            // size-h NTT: fused1b (B -> A) + register-radix chunks in-place on A
            {
                let tile1 = 1u32 << (E1 + LB);
                let key = format!("fused1b_l{logh}_two{twh_off}");
                let wgsl = format!(
                    "{}{}{}",
                    DFT_PRELUDE,
                    tw_def(twh_off),
                    subst(
                        K_FUSED1B,
                        &[
                            ("$TILE", tile1),
                            ("$TPT", tile1 / wgsz),
                            ("$HBT", tile1 / 2 / wgsz),
                            ("$WGSZ", wgsz),
                            ("$NN", h as u32),
                            ("$LOGN", logh),
                            ("$E1", E1),
                            ("$LB", LB),
                            ("$WW", (h as u32) >> E1),
                        ],
                    )
                );
                let p = ctx.pipeline(key, &wgsl);
                plan.push((p, Target::A, ((h as u32) >> (E1 + LB), wb as u32)));
                let mut l = E1;
                for r in split_stages(logh - E1) {
                    let key = format!("radix_l{logh}_s{l}_r{r}_two{twh_off}");
                    let wgsl = format!(
                        "{}{}{}",
                        DFT_PRELUDE,
                        tw_def(twh_off),
                        radix_kernel(h as u32, logh, l, r, wgsz)
                    );
                    let p = ctx.pipeline(key, &wgsl);
                    plan.push((p, Target::A, (((h as u32) >> r).div_ceil(wgsz), wb as u32)));
                    l += r;
                }
            }

            let final_src = if lde {
                {
                    let key = format!("expand_h{logh}_n{logn}_sp{sp_off}");
                    let wgsl = format!(
                        "{}{}",
                        DFT_PRELUDE,
                        subst(
                            K_EXPAND,
                            &[
                                ("$RSHN", 32 - logn),
                                ("$HM1", (h - 1) as u32),
                                ("$H", h as u32),
                                ("$N", n as u32),
                                ("$SPOFF", sp_off),
                            ],
                        )
                    );
                    let p = ctx.pipeline(key, &wgsl);
                    plan.push((p, Target::B, ((n as u32).div_ceil(wgsz), wb as u32)));
                }
                let mut l = added_bits;
                for r in split_stages(logn - added_bits) {
                    let key = format!("radix_l{logn}_s{l}_r{r}_two{twn_off}");
                    let wgsl = format!(
                        "{}{}{}",
                        DFT_PRELUDE,
                        tw_def(twn_off),
                        radix_kernel(n as u32, logn, l, r, wgsz)
                    );
                    let p = ctx.pipeline(key, &wgsl);
                    plan.push((p, Target::B, (((n as u32) >> r).div_ceil(wgsz), wb as u32)));
                    l += r;
                }
                Target::B
            } else {
                Target::A
            };

            // transpose out with bit-reversed rows
            let read_from = {
                let row_tiles = (n as u32) / 16;
                let rpt = row_tiles.div_ceil(32768).max(1);
                let key = format!("trans_out_n{logn}_w{w}_wb{wb}_rpt{rpt}");
                let wgsl = format!(
                    "{}{}",
                    DFT_PRELUDE,
                    subst(
                        K_TRANS_OUT_BITREV,
                        &[
                            ("$N", n as u32),
                            ("$W", wb as u32),
                            ("$RSH", 32 - logn),
                            ("$RPT", rpt),
                        ],
                    )
                );
                let p = ctx.pipeline(key, &wgsl);
                let tgt = if final_src == Target::B {
                    Target::A
                } else {
                    Target::B
                };
                plan.push((p, tgt, (row_tiles.div_ceil(rpt), (wb as u32).div_ceil(16))));
                tgt
            };

            let bufs = ctx.bufs.as_ref().unwrap();
            // LDE residency: the final transpose writes a dedicated retained
            // buffer instead of the reusable work buffer, so the result
            // survives the next dft call and can be blitted into the MMCS
            // leaf arena without a host round-trip.
            let retained_bg = if retain && single {
                let rb = ctx.device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some("lde_resident"),
                    size: (n * wb * 4) as u64,
                    usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
                    mapped_at_creation: false,
                });
                let src_buf = match final_src {
                    Target::A => &bufs.a,
                    Target::B => &bufs.b,
                };
                let bg = ctx.bind_dft(&rb, src_buf);
                retained_out = Some(rb);
                Some(bg)
            } else {
                None
            };
            let trans_out_idx = plan.len() - 1;
            let mut enc = ctx.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                for (i, (pipe, tgt, (x, y))) in plan.iter().enumerate() {
                    let bg = match (&retained_bg, i == trans_out_idx) {
                        (Some(bg), true) => bg,
                        _ => match tgt {
                            Target::A => &bufs.bg_ab,
                            Target::B => &bufs.bg_ba,
                        },
                    };
                    pass.set_bind_group(0, bg, &[]);
                    pass.set_pipeline(pipe);
                    pass.dispatch_workgroups(*x, *y, 1);
                }
            }
            let out_buf = match &retained_out {
                Some(rb) => rb,
                None => match read_from {
                    Target::A => &bufs.a,
                    Target::B => &bufs.b,
                },
            };
            enc.copy_buffer_to_buffer(out_buf, 0, &bufs.read, 0, (n * wb * 4) as u64);
            ctx.queue.submit([enc.finish()]);
            let slice = bufs.read.slice(..(n * wb * 4) as u64);
            slice.map_async(wgpu::MapMode::Read, |_| {});
            ctx.device.poll(wgpu::Maintain::Wait);
            {
                let mapped = slice.get_mapped_range();
                let chunk: &[u32] = bytemuck::cast_slice(&mapped);
                if single {
                    out = chunk.to_vec();
                } else {
                    out.par_chunks_mut(w)
                        .zip(chunk.par_chunks(wb))
                        .for_each(|(dst, srcrow)| dst[c0..c0 + wb].copy_from_slice(srcrow));
                }
            }
            bufs.read.unmap();
            c0 += wb;
        }
        (out, retained_out)
    }
}

impl TwoAdicSubgroupDft<BabyBear> for GpuDft {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<BabyBear>>;

    fn dft_batch(&self, mat: RowMajorMatrix<BabyBear>) -> Self::Evaluations {
        // wasm: CPU-shell (the sync-config DFT seam). The on-device GPU DFT is a
        // next-pass sharpening; the async engine at the file end runs on wasm.
        #[cfg(target_arch = "wasm32")]
        {
            return self.cpu.dft_batch(mat);
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            if !gpu_runtime_stage_enabled("DREGG_GPU_DFT") {
                return self.cpu.dft_batch(mat);
            }
            let h = mat.height();
            if h < (1 << MIN_GPU_LOG_H) || !h.is_power_of_two() || mat.width() == 0 {
                return self.cpu.dft_batch(mat);
            }
            let Some(gm) = self.gpu() else {
                return self.cpu.dft_batch(mat);
            };
            let mut ctx = gm.lock().unwrap();
            let (out, _) = self.gpu_flow(&mut ctx, &mat, 0, BabyBear::ONE, false, false);
            RowMajorMatrix::new(u32s_into_bb(out), mat.width()).bit_reverse_rows()
        }
    }

    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<BabyBear>,
        added_bits: usize,
        shift: BabyBear,
    ) -> Self::Evaluations {
        #[cfg(target_arch = "wasm32")]
        {
            return self.cpu.coset_lde_batch(mat, added_bits, shift);
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            if !gpu_runtime_stage_enabled("DREGG_GPU_DFT") {
                return self.cpu.coset_lde_batch(mat, added_bits, shift);
            }
            let h = mat.height();
            if h < (1 << MIN_GPU_LOG_H) || !h.is_power_of_two() || mat.width() == 0 {
                return self.cpu.coset_lde_batch(mat, added_bits, shift);
            }
            let Some(gm) = self.gpu() else {
                return self.cpu.coset_lde_batch(mat, added_bits, shift);
            };
            let mut ctx = gm.lock().unwrap();
            let (out, retained) =
                self.gpu_flow(&mut ctx, &mat, added_bits as u32, shift, true, true);
            drop(ctx);
            let values = u32s_into_bb(out);
            // Park the device copy for the commit that follows in the PCS flow
            // (the returned Vec is the allocation `commit` will receive).
            if let Some(buf) = retained {
                register_resident_lde(&values, buf);
            }
            RowMajorMatrix::new(values, mat.width()).bit_reverse_rows()
        }
    }
}

// ============================================================================
// SEAM 2 — the BN254 Poseidon2 GPU hash engine (portable WGSL plus a native
// Vulkan direct-SPIR-V/native-int64 path, both under the same tree builder).
// The permutation is parity-proven in sketches/bn254-poseidon2-wgpu against
// the pinned Poseidon2Bn254<3> and the gnark gold KAT, then re-gated here by
// root parity vs the CPU MerkleTreeMmcs.
// ============================================================================

/// BN254 scalar field prime.
const BN254_P_HEX: &str = "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

fn biguint_from_hex(s: &str) -> BigUint {
    BigUint::parse_bytes(s.trim_start_matches("0x").as_bytes(), 16).expect("bad hex")
}

fn limbs8(x: &BigUint) -> [u32; 8] {
    let d = x.to_u32_digits();
    assert!(d.len() <= 8, "value exceeds 256 bits");
    let mut out = [0u32; 8];
    out[..d.len()].copy_from_slice(&d);
    out
}

fn fp_lit(x: &BigUint) -> String {
    let l = limbs8(x);
    format!(
        "Fp(0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u, 0x{:08x}u)",
        l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7]
    )
}

/// Canonical little-endian u32x8 limbs -> Bn254 (one monty_mul inside `new`).
fn bn254_from_canonical_limbs(l: &[u32; 8]) -> Bn254 {
    let v: [u64; 4] = core::array::from_fn(|i| (l[2 * i] as u64) | ((l[2 * i + 1] as u64) << 32));
    Bn254::new(v)
}

/// The static WGSL for the hash engine: BabyBear canonicalization + 8-limb
/// BN254 Montgomery field ops + the generated Poseidon2 permutation + the
/// three tree kernels (leaf sponge / pair compress / inject combine).
///
/// All digest buffers hold CANONICAL limbs (little-endian u32x8); the
/// permutation runs in Montgomery form with conversions at kernel edges.
const HASH_WGSL: &str = r#"
alias Fp = array<u32, 8>;

const BB_P: u32 = 0x78000001u;
const BB_MU: u32 = 0x88000001u;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64).
fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}

// BabyBear Montgomery -> canonical: monty_reduce(x * 1).
fn bb_canon(x: u32) -> u32 {
    let t = x * BB_MU;
    let tp = mul64(t, BB_P);
    var r: u32 = 0u - tp.y;
    if (0u < tp.y) { r += BB_P; }
    // r = x*R^{-1} mod P given input < P; the 64-bit value is (0, x):
    // hi(ab)=0 so result = 0 - hi(t*P) (+P). But we must add the carry from
    // lo: lo(ab)=x and lo(t*P)=x by construction of MU, so the subtraction of
    // the low halves is exact and the formula above is complete.
    return r;
}

fn fp_p() -> Fp { return @P_FP@; }

fn fp_geq_p(a: Fp) -> bool {
@GEQ_BODY@
    return true;
}

fn fp_sub_p(a: Fp) -> Fp {
    let p = fp_p();
    var r: Fp;
    var borrow = 0u;
    for (var i = 0u; i < 8u; i++) {
        let d = a[i] - p[i];
        let b1 = select(0u, 1u, a[i] < p[i]);
        let d2 = d - borrow;
        let b2 = select(0u, 1u, d < borrow);
        r[i] = d2;
        borrow = b1 | b2;
    }
    return r;
}

fn fp_add(a: Fp, b: Fp) -> Fp {
    var r: Fp;
    var c = 0u;
    for (var i = 0u; i < 8u; i++) {
        let s = a[i] + b[i];
        let c1 = select(0u, 1u, s < a[i]);
        let s2 = s + c;
        let c2 = select(0u, 1u, s2 < c);
        r[i] = s2;
        c = c1 | c2;
    }
    if (c != 0u || fp_geq_p(r)) { r = fp_sub_p(r); }
    return r;
}

// Montgomery product (R = 2^256): schoolbook 8x8 product + SOS reduction.
fn mont_mul(a: Fp, b: Fp) -> Fp {
    let p = fp_p();
    var t: array<u32, 17>;
    for (var i = 0u; i < 8u; i++) {
        var carry = 0u;
        let ai = a[i];
        for (var j = 0u; j < 8u; j++) {
            let pr = mul64(ai, b[j]);
            let lo1 = pr.x + t[i + j];
            var hi = pr.y + select(0u, 1u, lo1 < pr.x);
            let lo2 = lo1 + carry;
            hi = hi + select(0u, 1u, lo2 < carry);
            t[i + j] = lo2;
            carry = hi;
        }
        t[i + 8u] = carry;
    }
    for (var i = 0u; i < 8u; i++) {
        let m = t[i] * @N0INV@u;
        var carry = 0u;
        for (var j = 0u; j < 8u; j++) {
            let pr = mul64(m, p[j]);
            let lo1 = pr.x + t[i + j];
            var hi = pr.y + select(0u, 1u, lo1 < pr.x);
            let lo2 = lo1 + carry;
            hi = hi + select(0u, 1u, lo2 < carry);
            t[i + j] = lo2;
            carry = hi;
        }
        var k = i + 8u;
        loop {
            if (carry == 0u || k >= 17u) { break; }
            let s = t[k] + carry;
            carry = select(0u, 1u, s < carry);
            t[k] = s;
            k = k + 1u;
        }
    }
    var r: Fp;
    for (var i = 0u; i < 8u; i++) { r[i] = t[i + 8u]; }
    if (t[16] != 0u || fp_geq_p(r)) { r = fp_sub_p(r); }
    return r;
}

fn sbox(x: Fp) -> Fp {
    let x2 = mont_mul(x, x);
    let x4 = mont_mul(x2, x2);
    return mont_mul(x4, x);
}

fn ext_linear(s: ptr<function, array<Fp, 3>>) {
    let sum = fp_add(fp_add((*s)[0], (*s)[1]), (*s)[2]);
    (*s)[0] = fp_add((*s)[0], sum);
    (*s)[1] = fp_add((*s)[1], sum);
    (*s)[2] = fp_add((*s)[2], sum);
}

fn int_linear(s: ptr<function, array<Fp, 3>>) {
    let sum = fp_add(fp_add((*s)[0], (*s)[1]), (*s)[2]);
    (*s)[0] = fp_add((*s)[0], sum);
    (*s)[1] = fp_add((*s)[1], sum);
    (*s)[2] = fp_add(fp_add((*s)[2], (*s)[2]), sum);
}

// Poseidon2-t3 round constants (Montgomery form), emitted as const arrays so
// the permutation LOOPS its rounds instead of unrolling all 64 in-register —
// this keeps the shader IR small enough for RADV's compiler (a fully-unrolled
// permute SIGSEGVs Mesa's create_compute_pipeline). Bit-identical math.
@RC_ARRAYS@

// External (full) round: add RC to all 3 lanes, sbox all 3, external MDS.
fn full_round(s: ptr<function, array<Fp, 3>>, rc: ptr<function, array<Fp, 3>>) {
    (*s)[0] = fp_add((*s)[0], (*rc)[0]);
    (*s)[1] = fp_add((*s)[1], (*rc)[1]);
    (*s)[2] = fp_add((*s)[2], (*rc)[2]);
    (*s)[0] = sbox((*s)[0]);
    (*s)[1] = sbox((*s)[1]);
    (*s)[2] = sbox((*s)[2]);
    ext_linear(s);
}

fn permute(s: ptr<function, array<Fp, 3>>) {
    ext_linear(s);
    for (var r = 0u; r < @N_INIT@u; r++) {
        var rc: array<Fp, 3>;
        rc[0] = RC_INIT[r * 3u + 0u];
        rc[1] = RC_INIT[r * 3u + 1u];
        rc[2] = RC_INIT[r * 3u + 2u];
        full_round(s, &rc);
    }
    for (var r = 0u; r < @N_INT@u; r++) {
        (*s)[0] = fp_add((*s)[0], RC_INT[r]);
        (*s)[0] = sbox((*s)[0]);
        int_linear(s);
    }
    for (var r = 0u; r < @N_TERM@u; r++) {
        var rc: array<Fp, 3>;
        rc[0] = RC_TERM[r * 3u + 0u];
        rc[1] = RC_TERM[r * 3u + 1u];
        rc[2] = RC_TERM[r * 3u + 2u];
        full_round(s, &rc);
    }
}

fn load_canon_to_monty(buf_index: u32, which: u32) -> Fp {
    var x: Fp;
    if (which == 0u) {
        for (var w = 0u; w < 8u; w++) { x[w] = outd[buf_index * 8u + w]; }
    } else {
        for (var w = 0u; w < 8u; w++) { x[w] = src[buf_index * 8u + w]; }
    }
    let r2 = @R2_FP@;
    return mont_mul(x, r2);
}

// b0: matrices arena / prev-layer digests / inject digests (read-only)
// b1: descriptor words (read-only)
// b2: output digests (read-write)
@group(0) @binding(0) var<storage, read> src: array<u32>;
@group(0) @binding(1) var<storage, read> desc: array<u32>;
@group(0) @binding(2) var<storage, read_write> outd: array<u32>;

// desc = [n_mats, base_row, n_rows, _, (off, w) * n_mats]
// One thread = one leaf row: the MultiField32PaddingFreeSponge over the
// concatenation of the row across all matrices in the height group.
// BabyBear values arrive in Montgomery form; digits are canonical+1 packed
// at radix 2^31 (shifted packing), 8 digits per BN254 rate slot, 2 slots per
// permutation, overwrite-mode absorb, digest = state[0], stored canonical.
@compute @workgroup_size(@WG@)
fn leaf_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let n_rows = desc[2];
    if (i >= n_rows) { return; }
    let row = desc[1] + i;
    let n_mats = desc[0];
    let r2 = @R2_FP@;

    var state: array<Fp, 3>;
    var acc: Fp;
    var pos = 0u;
    var slot = 0u;
    for (var m = 0u; m < n_mats; m++) {
        let off = desc[4u + 2u * m];
        let w = desc[5u + 2u * m];
        let rbase = off + row * w;
        for (var c = 0u; c < w; c++) {
            let digit = bb_canon(src[rbase + c]) + 1u;
            let bitpos = 31u * pos;
            let limb = bitpos >> 5u;
            let sh = bitpos & 31u;
            acc[limb] |= digit << sh;
            if (sh > 1u) { acc[limb + 1u] |= digit >> (32u - sh); }
            pos += 1u;
            if (pos == 8u) {
                state[slot] = mont_mul(acc, r2);
                acc = Fp();
                pos = 0u;
                slot += 1u;
                if (slot == 2u) {
                    permute(&state);
                    slot = 0u;
                }
            }
        }
    }
    if (pos != 0u) {
        state[slot] = mont_mul(acc, r2);
        slot += 1u;
    }
    if (slot != 0u) {
        permute(&state);
    }
    var one: Fp;
    one[0] = 1u;
    let d = mont_mul(state[0], one);
    for (var w = 0u; w < 8u; w++) { outd[row * 8u + w] = d[w]; }
}

// desc = [n_out, base, _, _]; src = prev layer digests (canonical);
// outd[i] = TruncatedPermutation compress: permute([prev[2i], prev[2i+1], 0])[0].
@compute @workgroup_size(@WG@)
fn compress_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    let n_out = desc[0];
    if (i0 >= n_out) { return; }
    let i = desc[1] + i0;
    var s: array<Fp, 3>;
    s[0] = load_canon_to_monty(2u * i, 1u);
    s[1] = load_canon_to_monty(2u * i + 1u, 1u);
    permute(&s);
    var one: Fp;
    one[0] = 1u;
    let d = mont_mul(s[0], one);
    for (var w = 0u; w < 8u; w++) { outd[i * 8u + w] = d[w]; }
}

// desc = [n, base, _, _]; outd[i] = compress(outd[i], src[i]) — the
// matrix-injection combine of compress_and_inject.
@compute @workgroup_size(@WG@)
fn combine_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    let n = desc[0];
    if (i0 >= n) { return; }
    let i = desc[1] + i0;
    var s: array<Fp, 3>;
    s[0] = load_canon_to_monty(i, 0u);
    s[1] = load_canon_to_monty(i, 1u);
    permute(&s);
    var one: Fp;
    one[0] = 1u;
    let d = mont_mul(s[0], one);
    for (var w = 0u; w < 8u; w++) { outd[i * 8u + w] = d[w]; }
}
"#;

/// Generate the hash-engine shader with the pinned RC3 constants inlined in
/// Montgomery form (same codegen as the parity-proven bn254-poseidon2-wgpu
/// sketch, extended with the tree kernels).
fn hash_shader_source(wg: u32) -> String {
    let p = biguint_from_hex(BN254_P_HEX);
    let one = BigUint::from(1u32);
    let r = (&one << 256u32) % &p;
    let r2 = (&r * &r) % &p;

    // n0inv = -P^{-1} mod 2^32 (Newton on the odd low limb).
    let p0 = limbs8(&p)[0];
    let mut inv: u32 = 1;
    for _ in 0..5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(p0.wrapping_mul(inv)));
    }
    let n0inv = inv.wrapping_neg();
    assert_eq!(p0.wrapping_mul(n0inv).wrapping_add(1), 0);

    let to_monty = |hex: &str| -> BigUint { (biguint_from_hex(hex) * &r) % &p };

    let pl = limbs8(&p);
    let mut geq = String::new();
    for i in (0..8).rev() {
        geq.push_str(&format!(
            "    if (a[{i}] != 0x{:08x}u) {{ return a[{i}] > 0x{:08x}u; }}\n",
            pl[i], pl[i]
        ));
    }

    // Round constants (Montgomery form) emitted as const arrays, so the WGSL
    // permutation LOOPS its rounds instead of unrolling all 64 inline. Flatten
    // the external rounds to [round*3 + lane]; the internal rounds are already
    // one-per-round (only lane 0 is dosed).
    let n_init = RC3_EXT_INITIAL.len();
    let n_int = RC3_INTERNAL.len();
    let n_term = RC3_EXT_TERMINAL.len();
    let rc_array = |name: &str, elems: &[BigUint]| -> String {
        let mut s = format!(
            "var<private> {name}: array<Fp, {}> = array<Fp, {}>(\n",
            elems.len(),
            elems.len()
        );
        for (i, e) in elems.iter().enumerate() {
            let sep = if i + 1 < elems.len() { "," } else { "" };
            s.push_str(&format!("    {}{sep}\n", fp_lit(e)));
        }
        s.push_str(");\n");
        s
    };
    let init_rc: Vec<BigUint> = (0..n_init)
        .flat_map(|r| (0..3).map(move |l| (r, l)))
        .map(|(r, l)| to_monty(RC3_EXT_INITIAL[r][l]))
        .collect();
    let int_rc: Vec<BigUint> = (0..n_int).map(|r| to_monty(RC3_INTERNAL[r])).collect();
    let term_rc: Vec<BigUint> = (0..n_term)
        .flat_map(|r| (0..3).map(move |l| (r, l)))
        .map(|(r, l)| to_monty(RC3_EXT_TERMINAL[r][l]))
        .collect();
    let mut rc_arrays = String::new();
    rc_arrays.push_str(&rc_array("RC_INIT", &init_rc));
    rc_arrays.push_str(&rc_array("RC_INT", &int_rc));
    rc_arrays.push_str(&rc_array("RC_TERM", &term_rc));

    HASH_WGSL
        .replace("@P_FP@", &fp_lit(&p))
        .replace("@R2_FP@", &fp_lit(&r2))
        .replace("@N0INV@", &format!("0x{n0inv:08x}"))
        .replace("@GEQ_BODY@", &geq)
        .replace("@RC_ARRAYS@", &rc_arrays)
        .replace("@N_INIT@", &n_init.to_string())
        .replace("@N_INT@", &n_int.to_string())
        .replace("@N_TERM@", &n_term.to_string())
        .replace("@WG@", &wg.to_string())
}

/// Workgroup size for the hash kernels — 64 measured best (register pressure
/// from the 8-limb state favors small workgroups; bn254-poseidon2-wgpu §C).
const HASH_WG: u32 = 64;
/// Max permutations per dispatch (Metal watchdog headroom at ~1 Mperm/s).
const HASH_MAX_PERMS_PER_DISPATCH: usize = 1 << 18;
/// The portable 8-limb WGSL kernel is retained for browser/small native
/// workloads, but oversized BN254 commitments use the exact CPU floor.  The
/// production Vulkan lane uses the direct-SPIR-V engine and is not capped.
const HASH_WGSL_MAX_COMMIT_PERMS: usize = HASH_MAX_PERMS_PER_DISPATCH;

/// The direct-SPIR-V kernel was compiled from
/// `sketches/bn254_poseidon2_int64.comp` with workgroup size 128, then passed
/// through `spirv-opt -O` and `spirv-val --target-env vulkan1.2`.
#[cfg(not(target_arch = "wasm32"))]
const BN254_POSEIDON2_INT64_SPIRV: &[u8] = include_bytes!("../sketches/bn254_poseidon2_int64.spv");
#[cfg(not(target_arch = "wasm32"))]
const HASH_SPIRV_WG: u32 = 128;

/// Tree orchestration around the Vulkan permutation primitive. This shader
/// deliberately contains no BN254 arithmetic: it canonicalizes/ packs
/// BabyBear leaf digits, lays out compression inputs as width-three states,
/// and extracts lane zero after the direct-SPIR-V permutation dispatch.
#[cfg(not(target_arch = "wasm32"))]
const HASH_SPIRV_TREE_WGSL: &str = r#"
const BB_P: u32 = 0x78000001u;
const BB_MU: u32 = 0x88000001u;

fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}

fn bb_canon(x: u32) -> u32 {
    let t = x * BB_MU;
    let tp = mul64(t, BB_P);
    var r: u32 = 0u - tp.y;
    if (tp.y != 0u) { r += BB_P; }
    return r;
}

// b0: leaf arena or compact digest source; b1: descriptor words;
// b2: canonical width-three states (read-write) or compact digest output.
@group(0) @binding(0) var<storage, read> src: array<u32>;
@group(0) @binding(1) var<storage, read> desc: array<u32>;
@group(0) @binding(2) var<storage, read_write> dst: array<u32>;

// desc = [n_mats, base_row, n_rows, permutation_index, (off, width)*n_mats].
// Overwrite the next one/two rate lanes in the prior canonical state exactly
// as MultiField32PaddingFreeSponge's overwrite-mode absorb does.
@compute @workgroup_size(128)
fn leaf_pack_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    if (i0 >= desc[2]) { return; }
    let row = desc[1] + i0;
    let block_start = desc[3] * 16u;
    let block_end = block_start + 16u;
    var acc0: array<u32, 8>;
    var acc1: array<u32, 8>;
    var prefix = 0u;
    var digits = 0u;
    for (var m = 0u; m < desc[0]; m++) {
        let off = desc[4u + 2u * m];
        let width = desc[5u + 2u * m];
        let lo = max(block_start, prefix);
        let hi = min(block_end, prefix + width);
        for (var g = lo; g < hi; g++) {
            let rel = g - block_start;
            let pos = rel & 7u;
            let bitpos = 31u * pos;
            let limb = bitpos >> 5u;
            let sh = bitpos & 31u;
            let digit = bb_canon(src[off + row * width + (g - prefix)]) + 1u;
            if (rel < 8u) {
                acc0[limb] |= digit << sh;
                if (sh > 1u) { acc0[limb + 1u] |= digit >> (32u - sh); }
            } else {
                acc1[limb] |= digit << sh;
                if (sh > 1u) { acc1[limb + 1u] |= digit >> (32u - sh); }
            }
            digits += 1u;
        }
        prefix += width;
    }
    for (var w = 0u; w < 8u; w++) { dst[(i0 * 3u) * 8u + w] = acc0[w]; }
    if (digits > 8u) {
        for (var w = 0u; w < 8u; w++) { dst[(i0 * 3u + 1u) * 8u + w] = acc1[w]; }
    }
}

// desc = [n, base, mode, _]. mode 0 lays out [src[2i], src[2i+1], 0]
// for a normal Merkle level. Modes 1 and 2 copy src[i] to lane 0 or lane 1,
// respectively; the pair composes compress(out[i], injected[i]).
@compute @workgroup_size(128)
fn level_pack_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    if (i0 >= desc[0]) { return; }
    let i = desc[1] + i0;
    if (desc[2] == 0u) {
        for (var w = 0u; w < 8u; w++) {
            dst[(i0 * 3u) * 8u + w] = src[(2u * i) * 8u + w];
            dst[(i0 * 3u + 1u) * 8u + w] = src[(2u * i + 1u) * 8u + w];
        }
    } else {
        let lane = desc[2] - 1u;
        for (var w = 0u; w < 8u; w++) {
            dst[(i0 * 3u + lane) * 8u + w] = src[i * 8u + w];
        }
    }
}

// desc = [n, base, _, _]; copy canonical output lane zero back to the compact
// digest arena at indices [base, base+n).
@compute @workgroup_size(128)
fn extract_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    if (i0 >= desc[0]) { return; }
    let i = desc[1] + i0;
    for (var w = 0u; w < 8u; w++) {
        dst[i * 8u + w] = src[(i0 * 3u) * 8u + w];
    }
}
"#;

#[cfg(not(target_arch = "wasm32"))]
fn bn254_round_words() -> Vec<u32> {
    let p = biguint_from_hex(BN254_P_HEX);
    let r = (BigUint::from(1u32) << 256u32) % &p;
    let to_monty = |hex: &str| -> BigUint { (biguint_from_hex(hex) * &r) % &p };
    let mut out = Vec::with_capacity(640);
    for row in RC3_EXT_INITIAL {
        for value in row {
            out.extend_from_slice(&limbs8(&to_monty(value)));
        }
    }
    for value in RC3_INTERNAL {
        out.extend_from_slice(&limbs8(&to_monty(value)));
    }
    for row in RC3_EXT_TERMINAL {
        for value in row {
            out.extend_from_slice(&limbs8(&to_monty(value)));
        }
    }
    assert_eq!(out.len(), 640);
    out
}

#[cfg(not(target_arch = "wasm32"))]
enum HashEngine {
    Wgsl {
        bgl: wgpu::BindGroupLayout,
        leaf_pipe: wgpu::ComputePipeline,
        compress_pipe: wgpu::ComputePipeline,
        combine_pipe: wgpu::ComputePipeline,
    },
    DirectSpirv {
        tree_bgl: wgpu::BindGroupLayout,
        leaf_pack_pipe: wgpu::ComputePipeline,
        level_pack_pipe: wgpu::ComputePipeline,
        extract_pipe: wgpu::ComputePipeline,
        perm_bgl: wgpu::BindGroupLayout,
        perm_pipe: wgpu::ComputePipeline,
        round_constants: wgpu::Buffer,
    },
}

#[cfg(not(target_arch = "wasm32"))]
struct HashCtx {
    // Engine resources precede the device handle (same drop-order discipline
    // as DftCtx; the device is the 'static SharedGpu one).
    engine: HashEngine,
    max_binding_u32s: usize,
    device: wgpu::Device,
    queue: wgpu::Queue,
}

#[cfg(not(target_arch = "wasm32"))]
impl HashCtx {
    fn new() -> Option<Self> {
        let shared = shared_gpu()?;
        let device = shared.device.clone();
        let queue = shared.queue.clone();
        let storage_entry = |binding: u32, read_only: bool| wgpu::BindGroupLayoutEntry {
            binding,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty: wgpu::BindingType::Buffer {
                ty: wgpu::BufferBindingType::Storage { read_only },
                has_dynamic_offset: false,
                min_binding_size: None,
            },
            count: None,
        };
        let engine = if shared.direct_bn254_spirv {
            // The orchestration layout matches the portable tree shader. The
            // raw module has its own mandatory explicit layout: reflection is
            // bypassed by SPIR-V passthrough, so `layout: None` is invalid.
            let tree_bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("bn254_tree_orchestration_bgl"),
                entries: &[
                    storage_entry(0, true),
                    storage_entry(1, true),
                    storage_entry(2, false),
                ],
            });
            let tree_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("bn254_tree_orchestration_layout"),
                bind_group_layouts: &[&tree_bgl],
                push_constant_ranges: &[],
            });
            let tree_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bn254_tree_orchestration"),
                source: wgpu::ShaderSource::Wgsl(HASH_SPIRV_TREE_WGSL.into()),
            });
            let mk_tree_pipe = |entry: &str| {
                device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                    label: Some(entry),
                    layout: Some(&tree_layout),
                    module: &tree_module,
                    entry_point: Some(entry),
                    compilation_options: Default::default(),
                    cache: None,
                })
            };
            let leaf_pack_pipe = mk_tree_pipe("leaf_pack_main");
            let level_pack_pipe = mk_tree_pipe("level_pack_main");
            let extract_pipe = mk_tree_pipe("extract_main");

            // SACRED ABI from the direct-SPIR-V runbook:
            //   b0 readonly canonical input states
            //   b1 read-write canonical output states
            //   b2 readonly Montgomery round constants
            let perm_bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("bn254_poseidon2_int64_bgl"),
                entries: &[
                    storage_entry(0, true),
                    storage_entry(1, false),
                    storage_entry(2, true),
                ],
            });
            let perm_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("bn254_poseidon2_int64_layout"),
                bind_group_layouts: &[&perm_bgl],
                push_constant_ranges: &[],
            });
            let perm_module = unsafe {
                device.create_shader_module_spirv(&wgpu::ShaderModuleDescriptorSpirV {
                    label: Some("bn254_poseidon2_int64"),
                    source: wgpu::util::make_spirv_raw(BN254_POSEIDON2_INT64_SPIRV),
                })
            };
            let perm_pipe = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("bn254_poseidon2_int64"),
                layout: Some(&perm_layout),
                module: &perm_module,
                entry_point: Some("main"),
                compilation_options: Default::default(),
                cache: None,
            });
            let round_constants = device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("bn254_poseidon2_montgomery_round_constants"),
                size: (640 * 4) as u64,
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });
            queue.write_buffer(
                &round_constants,
                0,
                bytemuck::cast_slice(&bn254_round_words()),
            );
            tracing::info!(
                adapter = %shared.adapter_name,
                "GpuBn254Mmcs selected Vulkan direct-SPIR-V + shaderInt64"
            );
            HashEngine::DirectSpirv {
                tree_bgl,
                leaf_pack_pipe,
                level_pack_pipe,
                extract_pipe,
                perm_bgl,
                perm_pipe,
                round_constants,
            }
        } else {
            let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("hash_bgl"),
                entries: &[
                    storage_entry(0, true),
                    storage_entry(1, true),
                    storage_entry(2, false),
                ],
            });
            let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: None,
                bind_group_layouts: &[&bgl],
                push_constant_ranges: &[],
            });
            let src = hash_shader_source(HASH_WG);
            let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bn254_poseidon2_tree"),
                source: wgpu::ShaderSource::Wgsl(src.into()),
            });
            let mk_pipe = |entry: &str| {
                device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                    label: Some(entry),
                    layout: Some(&layout),
                    module: &module,
                    entry_point: Some(entry),
                    compilation_options: Default::default(),
                    cache: None,
                })
            };
            let leaf_pipe = mk_pipe("leaf_main");
            let compress_pipe = mk_pipe("compress_main");
            let combine_pipe = mk_pipe("combine_main");
            HashEngine::Wgsl {
                bgl,
                leaf_pipe,
                compress_pipe,
                combine_pipe,
            }
        };
        let max_binding_u32s = shared.max_buf_u32s;
        Some(HashCtx {
            engine,
            max_binding_u32s,
            device,
            queue,
        })
    }

    fn bind(
        &self,
        layout: &wgpu::BindGroupLayout,
        b0: &wgpu::Buffer,
        b1: &wgpu::Buffer,
        b2: &wgpu::Buffer,
    ) -> wgpu::BindGroup {
        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: b0.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: b1.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: b2.as_entire_binding(),
                },
            ],
        })
    }

    fn storage_buffer(&self, label: &str, u32s: usize, dst: bool) -> wgpu::Buffer {
        let mut usage = wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC;
        if dst {
            usage |= wgpu::BufferUsages::COPY_DST;
        }
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: (u32s.max(4) * 4) as u64,
            usage,
            mapped_at_creation: false,
        })
    }

    /// Upload an immutable descriptor for one queued command.  Reusing and
    /// rewriting one storage buffer across several outstanding dispatches is
    /// racy on host-visible backends once the GPU falls behind the submitter:
    /// a command may observe a later chunk's words.  These buffers are tiny;
    /// the submitted bind group retains each one until its command completes.
    fn descriptor_buffer(&self, label: &str, words: &[u32]) -> wgpu::Buffer {
        let buf = self.storage_buffer(label, words.len(), true);
        self.queue
            .write_buffer(&buf, 0, bytemuck::cast_slice(words));
        buf
    }

    /// `Queue::write_buffer` implementations commonly stage each call in one
    /// temporary allocation.  Keep production trace uploads below the large
    /// allocation/driver thresholds (the outer w=300 LDE is ~150 MiB).
    fn write_u32s_chunked(&self, dst: &wgpu::Buffer, dst_word_offset: usize, words: &[u32]) {
        const UPLOAD_WORDS: usize = (16 << 20) / 4;
        for (chunk_index, chunk) in words.chunks(UPLOAD_WORDS).enumerate() {
            let word_offset = dst_word_offset + chunk_index * UPLOAD_WORDS;
            self.queue
                .write_buffer(dst, (word_offset * 4) as u64, bytemuck::cast_slice(chunk));
        }
    }

    /// Dispatch the leaf sponge over `n_rows` rows in watchdog-safe chunks.
    /// `perms_per_row` sizes the chunks; desc buffer is rewritten per chunk.
    fn dispatch_leaf(
        &self,
        arena: &wgpu::Buffer,
        _desc_buf: &wgpu::Buffer,
        out: &wgpu::Buffer,
        desc_head: &[u32; 4],
        mat_descs: &[u32],
        n_rows: usize,
        perms_per_row: usize,
    ) {
        match &self.engine {
            HashEngine::Wgsl { bgl, leaf_pipe, .. } => {
                let rows_per_chunk = (HASH_MAX_PERMS_PER_DISPATCH / perms_per_row.max(1))
                    .max(HASH_WG as usize)
                    .next_multiple_of(HASH_WG as usize);
                let mut base = 0usize;
                while base < n_rows {
                    let rows = rows_per_chunk.min(n_rows - base);
                    let mut desc = vec![desc_head[0], base as u32, rows as u32, 0];
                    desc.extend_from_slice(mat_descs);
                    let chunk_desc = self.descriptor_buffer("bn254_leaf_desc", &desc);
                    let bindg = self.bind(bgl, arena, &chunk_desc, out);
                    let mut enc = self.device.create_command_encoder(&Default::default());
                    {
                        let mut pass = enc.begin_compute_pass(&Default::default());
                        pass.set_pipeline(leaf_pipe);
                        pass.set_bind_group(0, &bindg, &[]);
                        pass.dispatch_workgroups((rows as u32).div_ceil(HASH_WG), 1, 1);
                    }
                    self.queue.submit([enc.finish()]);
                    base += rows;
                }
            }
            HashEngine::DirectSpirv {
                tree_bgl,
                leaf_pack_pipe,
                extract_pipe,
                perm_bgl,
                perm_pipe,
                round_constants,
                ..
            } => {
                // Each raw dispatch sees an exactly-sized state binding, so
                // the kernel's `input_data.length()/24` guard also fences the
                // padded last workgroup. Keep each dispatch under the same
                // watchdog ceiling used by the portable engine.
                let rows_per_chunk = HASH_MAX_PERMS_PER_DISPATCH
                    .min(self.max_binding_u32s / 24)
                    .max(1);
                let mut base = 0usize;
                while base < n_rows {
                    let rows = rows_per_chunk.min(n_rows - base);
                    let mut state_a = self.storage_buffer("bn254_states_a", rows * 24, true);
                    let mut state_b = self.storage_buffer("bn254_states_b", rows * 24, true);
                    for permutation_index in 0..perms_per_row {
                        let mut desc = vec![
                            desc_head[0],
                            base as u32,
                            rows as u32,
                            permutation_index as u32,
                        ];
                        desc.extend_from_slice(mat_descs);
                        let pack_desc = self.descriptor_buffer("bn254_leaf_pack_desc", &desc);
                        let pack_bg = self.bind(tree_bgl, arena, &pack_desc, &state_a);
                        let perm_bg = self.bind(perm_bgl, &state_a, &state_b, round_constants);
                        let mut enc = self.device.create_command_encoder(&Default::default());
                        {
                            let mut pass = enc.begin_compute_pass(&Default::default());
                            pass.set_pipeline(leaf_pack_pipe);
                            pass.set_bind_group(0, &pack_bg, &[]);
                            pass.dispatch_workgroups((rows as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                        }
                        {
                            let mut pass = enc.begin_compute_pass(&Default::default());
                            pass.set_pipeline(perm_pipe);
                            pass.set_bind_group(0, &perm_bg, &[]);
                            pass.dispatch_workgroups((rows as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                        }
                        self.queue.submit([enc.finish()]);
                        std::mem::swap(&mut state_a, &mut state_b);
                    }
                    let desc = [rows as u32, base as u32, 0u32, 0u32];
                    let extract_desc = self.descriptor_buffer("bn254_leaf_extract_desc", &desc);
                    let extract_bg = self.bind(tree_bgl, &state_a, &extract_desc, out);
                    let mut enc = self.device.create_command_encoder(&Default::default());
                    {
                        let mut pass = enc.begin_compute_pass(&Default::default());
                        pass.set_pipeline(extract_pipe);
                        pass.set_bind_group(0, &extract_bg, &[]);
                        pass.dispatch_workgroups((rows as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                    }
                    self.queue.submit([enc.finish()]);
                    base += rows;
                }
            }
        }
    }

    /// One compress or injection-combine level. `combine` means
    /// `out[i] = compress(out[i], src[i])`; otherwise this is the normal
    /// `out[i] = compress(src[2i], src[2i+1])` Merkle step.
    fn dispatch_level(
        &self,
        src: &wgpu::Buffer,
        _desc_buf: &wgpu::Buffer,
        out: &wgpu::Buffer,
        n: usize,
        combine: bool,
    ) {
        match &self.engine {
            HashEngine::Wgsl {
                bgl,
                compress_pipe,
                combine_pipe,
                ..
            } => {
                let pipe = if combine { combine_pipe } else { compress_pipe };
                let mut base = 0usize;
                while base < n {
                    let cnt = HASH_MAX_PERMS_PER_DISPATCH.min(n - base);
                    let desc = [cnt as u32, base as u32, 0u32, 0u32];
                    let chunk_desc = self.descriptor_buffer("bn254_level_desc", &desc);
                    let bindg = self.bind(bgl, src, &chunk_desc, out);
                    let mut enc = self.device.create_command_encoder(&Default::default());
                    {
                        let mut pass = enc.begin_compute_pass(&Default::default());
                        pass.set_pipeline(pipe);
                        pass.set_bind_group(0, &bindg, &[]);
                        pass.dispatch_workgroups((cnt as u32).div_ceil(HASH_WG), 1, 1);
                    }
                    self.queue.submit([enc.finish()]);
                    base += cnt;
                }
            }
            HashEngine::DirectSpirv {
                tree_bgl,
                level_pack_pipe,
                extract_pipe,
                perm_bgl,
                perm_pipe,
                round_constants,
                ..
            } => {
                let nodes_per_chunk = HASH_MAX_PERMS_PER_DISPATCH
                    .min(self.max_binding_u32s / 24)
                    .max(1);
                let mut base = 0usize;
                while base < n {
                    let cnt = nodes_per_chunk.min(n - base);
                    let state_in = self.storage_buffer("bn254_level_in", cnt * 24, true);
                    let state_out = self.storage_buffer("bn254_level_out", cnt * 24, true);

                    if combine {
                        // First lane is the already-compressed parent in
                        // `out`; the second is this height's injected leaf.
                        let desc = [cnt as u32, base as u32, 1u32, 0u32];
                        let lane0_desc = self.descriptor_buffer("bn254_level_lane0_desc", &desc);
                        let lane0_bg = self.bind(tree_bgl, out, &lane0_desc, &state_in);
                        let mut enc = self.device.create_command_encoder(&Default::default());
                        {
                            let mut pass = enc.begin_compute_pass(&Default::default());
                            pass.set_pipeline(level_pack_pipe);
                            pass.set_bind_group(0, &lane0_bg, &[]);
                            pass.dispatch_workgroups((cnt as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                        }
                        self.queue.submit([enc.finish()]);
                    }

                    let mode = if combine { 2u32 } else { 0u32 };
                    let desc = [cnt as u32, base as u32, mode, 0u32];
                    let pack_desc = self.descriptor_buffer("bn254_level_pack_desc", &desc);
                    let pack_bg = self.bind(tree_bgl, src, &pack_desc, &state_in);
                    let perm_bg = self.bind(perm_bgl, &state_in, &state_out, round_constants);
                    let mut enc = self.device.create_command_encoder(&Default::default());
                    {
                        let mut pass = enc.begin_compute_pass(&Default::default());
                        pass.set_pipeline(level_pack_pipe);
                        pass.set_bind_group(0, &pack_bg, &[]);
                        pass.dispatch_workgroups((cnt as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                    }
                    {
                        let mut pass = enc.begin_compute_pass(&Default::default());
                        pass.set_pipeline(perm_pipe);
                        pass.set_bind_group(0, &perm_bg, &[]);
                        pass.dispatch_workgroups((cnt as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                    }
                    self.queue.submit([enc.finish()]);

                    let desc = [cnt as u32, base as u32, 0u32, 0u32];
                    let extract_desc = self.descriptor_buffer("bn254_level_extract_desc", &desc);
                    let extract_bg = self.bind(tree_bgl, &state_out, &extract_desc, out);
                    let mut enc = self.device.create_command_encoder(&Default::default());
                    {
                        let mut pass = enc.begin_compute_pass(&Default::default());
                        pass.set_pipeline(extract_pipe);
                        pass.set_bind_group(0, &extract_bg, &[]);
                        pass.dispatch_workgroups((cnt as u32).div_ceil(HASH_SPIRV_WG), 1, 1);
                    }
                    self.queue.submit([enc.finish()]);
                    base += cnt;
                }
            }
        }
    }

    /// Read `n_digests` canonical digests back from `buf`.
    fn read_digests(&self, buf: &wgpu::Buffer, n_digests: usize) -> Vec<[u32; 8]> {
        let bytes = (n_digests * 32) as u64;
        let read = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("dig_read"),
            size: bytes.max(32),
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(buf, 0, &read, 0, bytes);
        self.queue.submit([enc.finish()]);
        let slice = read.slice(..bytes);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let out: Vec<[u32; 8]> = {
            let mapped = slice.get_mapped_range();
            let words: &[u32] = bytemuck::cast_slice(&mapped);
            words
                .chunks_exact(8)
                .map(|c| c.try_into().unwrap())
                .collect()
        };
        read.unmap();
        out
    }
}

// ============================================================================
// GpuBn254Mmcs — the GPU Merkle MMCS (bit-exact twin of OuterValMmcs)
// ============================================================================

/// The GPU-built Merkle tree: original matrices + all digest layers
/// (canonical u32x8 limbs; converted to `Bn254` lazily at root/open time).
pub struct GpuMerkleTree<M> {
    leaves: Vec<M>,
    /// digest_layers[0] = leaf digests of the tallest group; last = [root].
    digest_layers: Vec<Vec<[u32; 8]>>,
}

/// ProverData: GPU tree or the CPU `MerkleTree` (fallback shapes keep the
/// exact upstream semantics by construction).
pub enum GpuMmcsProverData<M> {
    Gpu(GpuMerkleTree<M>),
    Cpu(<OuterValMmcs as Mmcs<BabyBear>>::ProverData<M>),
}

/// The GPU BN254-native MMCS. Same `Commitment`/`Proof` types as the CPU
/// `OuterValMmcs`; `verify_batch` delegates to it, so verification is the
/// untouched upstream code path.
#[derive(Clone)]
pub struct GpuBn254Mmcs {
    cpu: OuterValMmcs,
    cap_height: usize,
    // wgpu hash context — `!Send + !Sync` on wasm, so the sync-config MMCS is a
    // CPU-only shell there and stays `Sync`. The on-device GPU BN254 tree build
    // (the ~60% Amdahl lever) is served by the async engine at the file end.
    #[cfg(not(target_arch = "wasm32"))]
    ctx: Arc<OnceLock<Option<Mutex<HashCtx>>>>,
}

/// Minimum estimated permutation count for the GPU path (below this the
/// dispatch/upload overhead beats the kernel win; measured band ~2^13).
const MIN_GPU_MMCS_PERMS: usize = 1 << 13;

impl GpuBn254Mmcs {
    /// Build with the pinned Poseidon2Bn254 permutation and cap_height 0
    /// (the outer config's shape).
    pub fn new(cap_height: usize) -> Self {
        let perm = dregg_poseidon2_bn254();
        let hash = OuterHash::new(perm.clone()).expect("BabyBear order < BN254 order");
        let compress = OuterCompress::new(perm);
        Self {
            cpu: OuterValMmcs::new(hash, compress, cap_height),
            cap_height,
            #[cfg(not(target_arch = "wasm32"))]
            ctx: Arc::new(OnceLock::new()),
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn gpu(&self) -> Option<&Mutex<HashCtx>> {
        self.ctx
            .get_or_init(|| HashCtx::new().map(Mutex::new))
            .as_ref()
    }

    /// Whether a GPU adapter is available (None = permanent CPU fallback).
    /// On wasm the sync-config MMCS is always CPU (see `init_gpu`).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn adapter_available(&self) -> bool {
        self.gpu().is_some()
    }

    /// wasm CPU-shell: the sync-config MMCS never dispatches to the GPU (the
    /// on-device path is the async engine, reached via `init_gpu()`).
    #[cfg(target_arch = "wasm32")]
    pub fn adapter_available(&self) -> bool {
        false
    }

    /// Estimated total permutations for a batch (leaf sponges + compresses).
    fn estimate_perms(heights_widths: &[(usize, usize)]) -> usize {
        let mut by_height: HashMap<usize, usize> = HashMap::new();
        for &(h, w) in heights_widths {
            *by_height.entry(h).or_default() += w;
        }
        let mut perms = 0usize;
        for (&h, &w_total) in &by_height {
            perms += h * w_total.div_ceil(16).max(1);
        }
        let max_h = heights_widths.iter().map(|&(h, _)| h).max().unwrap_or(0);
        perms + 2 * max_h // compress + inject-combine upper bound
    }

    /// The GPU tree build. Preconditions (checked by the caller): all heights
    /// powers of two, at least one matrix, cap_height == 0, GPU available.
    #[cfg(not(target_arch = "wasm32"))]
    fn build_gpu_tree<M: Matrix<BabyBear>>(
        &self,
        ctx: &HashCtx,
        leaves: Vec<M>,
    ) -> GpuMerkleTree<M> {
        // Group matrix indices by height, tallest first (stable order — the
        // upstream sort is stable, so ties keep insertion order).
        let mut order: Vec<usize> = (0..leaves.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(leaves[i].height()));
        let mut groups: Vec<(usize, Vec<usize>)> = Vec::new();
        for i in order {
            let h = leaves[i].height();
            match groups.last_mut() {
                Some((gh, idxs)) if *gh == h => idxs.push(i),
                _ => groups.push((h, vec![i])),
            }
        }
        let max_h = groups[0].0;

        // Fill one height-group's arena buffer — a device→device blit for
        // every matrix whose LDE is still device-resident (the round-trip
        // closure), the host staging upload otherwise — and hash its rows
        // into `out` (digest slots [0, h)).
        let hash_group =
            |group: &[usize], h: usize, out: &wgpu::Buffer, desc_buf: &wgpu::Buffer| {
                let total_w: usize = group.iter().map(|&i| leaves[i].width()).sum();
                let arena_u32s: usize = h * total_w;
                let arena = ctx.storage_buffer("leaf_arena", arena_u32s, true);
                let mut mat_descs: Vec<u32> = Vec::with_capacity(group.len() * 2);
                let mut blits: Vec<(wgpu::Buffer, usize)> = Vec::new();
                if group.len() > 1 && matches!(&ctx.engine, HashEngine::Wgsl { .. }) {
                    // A few native backends miscompile/alias the large
                    // matrix-major offsets reached by production batches
                    // (e.g. the second matrix starts ~80 MiB into the tall
                    // outer trace arena).  Flatten the logical concatenation
                    // into one row-major stream: this is exactly the iterator
                    // seen by `hash_iter_slices`, avoids the high-offset
                    // gather, and is portable WGSL/SPIR-V input.
                    let mut staging = vec![0u32; arena_u32s];
                    staging
                        .par_chunks_mut(total_w)
                        .enumerate()
                        .for_each(|(r, dst)| {
                            let mut c0 = 0usize;
                            for &i in group {
                                let m = &leaves[i];
                                let w = m.width();
                                let row = m.row_slice(r).expect("row in range");
                                dst[c0..c0 + w].copy_from_slice(bb_as_u32s(&row));
                                c0 += w;
                            }
                        });
                    ctx.write_u32s_chunked(&arena, 0, &staging);
                    LDE_RESIDENT_MISSES.fetch_add(group.len() as u64, Ordering::Relaxed);
                    mat_descs.extend_from_slice(&[0, total_w as u32]);
                } else {
                    let mut off = 0usize;
                    for &i in group {
                        let m = &leaves[i];
                        let w = m.width();
                        if let Some(resident) = take_resident_lde(m) {
                            LDE_RESIDENT_HITS.fetch_add(1, Ordering::Relaxed);
                            // The key guarantees the buffer holds exactly h*w u32s.
                            blits.push((resident, off));
                        } else {
                            LDE_RESIDENT_MISSES.fetch_add(1, Ordering::Relaxed);
                            let mut staging = vec![0u32; h * w];
                            staging.par_chunks_mut(w).enumerate().for_each(|(r, dst)| {
                                let row = m.row_slice(r).expect("row in range");
                                dst.copy_from_slice(bb_as_u32s(&row));
                            });
                            ctx.write_u32s_chunked(&arena, off, &staging);
                        }
                        mat_descs.extend_from_slice(&[off as u32, w as u32]);
                        off += h * w;
                    }
                }
                if !blits.is_empty() {
                    // One encoder for all resident blits; submitted after the
                    // write_buffer calls above, so queue ordering puts both
                    // before the leaf dispatches.
                    let mut enc = ctx.device.create_command_encoder(&Default::default());
                    for &(ref resident, boff) in &blits {
                        enc.copy_buffer_to_buffer(
                            resident,
                            0,
                            &arena,
                            (boff * 4) as u64,
                            resident.size(),
                        );
                    }
                    ctx.queue.submit([enc.finish()]);
                }
                let perms_per_row = total_w.div_ceil(16).max(1);
                ctx.dispatch_leaf(
                    &arena,
                    desc_buf,
                    out,
                    &[(mat_descs.len() / 2) as u32, 0, 0, 0],
                    &mat_descs,
                    h,
                    perms_per_row,
                );
            };

        let desc_buf = ctx.storage_buffer("desc", 4 + 2 * leaves.len().max(2), true);
        let dig_a = ctx.storage_buffer("dig_a", max_h * 8, true);
        let dig_b = ctx.storage_buffer("dig_b", max_h * 8, true);
        let inj = ctx.storage_buffer("dig_inj", (max_h / 2).max(1) * 8, true);

        // Layer 0: the tallest group.
        hash_group(&groups[0].1, max_h, &dig_a, &desc_buf);
        let mut digest_layers: Vec<Vec<[u32; 8]>> = vec![ctx.read_digests(&dig_a, max_h)];

        let mut next_group = 1usize;
        let mut cur_len = max_h;
        let mut cur_is_a = true;
        while cur_len > 1 {
            let next_len = cur_len / 2;
            let (src, dst) = if cur_is_a {
                (&dig_a, &dig_b)
            } else {
                (&dig_b, &dig_a)
            };
            ctx.dispatch_level(src, &desc_buf, dst, next_len, false);
            if next_group < groups.len() && groups[next_group].0 == next_len {
                // Inject: hash the group's rows, then combine pairwise.
                hash_group(&groups[next_group].1, next_len, &inj, &desc_buf);
                ctx.dispatch_level(&inj, &desc_buf, dst, next_len, true);
                next_group += 1;
            }
            digest_layers.push(ctx.read_digests(dst, next_len));
            cur_len = next_len;
            cur_is_a = !cur_is_a;
        }
        assert_eq!(next_group, groups.len(), "all height groups consumed");

        GpuMerkleTree {
            leaves,
            digest_layers,
        }
    }
}

impl Mmcs<BabyBear> for GpuBn254Mmcs {
    type ProverData<M> = GpuMmcsProverData<M>;
    type Commitment = <OuterValMmcs as Mmcs<BabyBear>>::Commitment;
    type Proof = <OuterValMmcs as Mmcs<BabyBear>>::Proof;
    type Error = MerkleTreeError;

    fn commit<M: Matrix<BabyBear>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let shapes: Vec<(usize, usize)> = inputs.iter().map(|m| (m.height(), m.width())).collect();
        let estimated_perms = Self::estimate_perms(&shapes);
        let gpu_able = self.cap_height == 0
            && !inputs.is_empty()
            && shapes
                .iter()
                .all(|&(h, w)| h.is_power_of_two() && h > 0 && w > 0)
            && estimated_perms >= MIN_GPU_MMCS_PERMS;
        #[cfg(not(target_arch = "wasm32"))]
        let gpu_able = gpu_able && gpu_runtime_stage_enabled("DREGG_GPU_BN254_MMCS");
        // The GPU fast-path is native-only (holds wgpu handles). On wasm the
        // sync-config MMCS is a CPU shell; the on-device GPU BN254 tree lives in
        // the async engine at the file end (reached via `init_gpu()`).
        #[cfg(not(target_arch = "wasm32"))]
        if gpu_able && let Some(gm) = self.gpu() {
            let ctx = gm.lock().unwrap();
            // Every height-group arena must fit one storage binding; if any
            // exceeds it, fall back to the CPU commit (never mid-build panic).
            let mut group_arena: HashMap<usize, usize> = HashMap::new();
            for &(h, w) in &shapes {
                *group_arena.entry(h).or_default() += h * w;
            }
            let portable_size_ok = !matches!(&ctx.engine, HashEngine::Wgsl { .. })
                || estimated_perms <= HASH_WGSL_MAX_COMMIT_PERMS;
            if portable_size_ok && group_arena.values().all(|&u| u <= ctx.max_binding_u32s) {
                let tree = self.build_gpu_tree(&ctx, inputs);
                let root = tree.digest_layers.last().expect("non-empty tree")[0];
                let commitment = MerkleCap::new(vec![[bn254_from_canonical_limbs(&root)]]);
                // Any resident LDEs this commit did not consume are dead
                // weight — clearing them promptly also closes the
                // stale-pointer window of the residency binding.
                clear_thread_resident_ldes();
                return (commitment, GpuMmcsProverData::Gpu(tree));
            }
        }
        clear_thread_resident_ldes();
        let (c, d) = self.cpu.commit(inputs);
        (c, GpuMmcsProverData::Cpu(d))
    }

    fn open_batch<M: Matrix<BabyBear>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> BatchOpening<BabyBear, Self> {
        match prover_data {
            GpuMmcsProverData::Cpu(tree) => {
                let (opened_values, opening_proof) = self.cpu.open_batch(index, tree).unpack();
                BatchOpening::new(opened_values, opening_proof)
            }
            GpuMmcsProverData::Gpu(tree) => {
                let max_h = tree
                    .leaves
                    .iter()
                    .map(|m| m.height())
                    .max()
                    .expect("non-empty batch");
                assert!(
                    index < max_h,
                    "index {index} out of bounds for height {max_h}"
                );
                let log_max = max_h.trailing_zeros() as usize;
                let opened_values: Vec<Vec<BabyBear>> = tree
                    .leaves
                    .iter()
                    .map(|m| {
                        let bits_reduced = log_max - m.height().trailing_zeros() as usize;
                        m.row(index >> bits_reduced)
                            .expect("reduced index in range")
                            .into_iter()
                            .collect()
                    })
                    .collect();
                // cap_height == 0 on the GPU path: siblings from every layer
                // below the root, binary steps only (power-of-two heights).
                let proof_levels = tree.digest_layers.len() - 1;
                let mut proof = Vec::with_capacity(proof_levels);
                let mut idx = index;
                for layer in &tree.digest_layers[..proof_levels] {
                    proof.push([bn254_from_canonical_limbs(&layer[idx ^ 1])]);
                    idx >>= 1;
                }
                BatchOpening::new(opened_values, proof)
            }
        }
    }

    fn get_matrices<'a, M: Matrix<BabyBear>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        match prover_data {
            GpuMmcsProverData::Cpu(tree) => self.cpu.get_matrices(tree),
            GpuMmcsProverData::Gpu(tree) => tree.leaves.iter().collect(),
        }
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[p3_matrix::Dimensions],
        index: usize,
        batch_proof: BatchOpeningRef<'_, BabyBear, Self>,
    ) -> Result<(), Self::Error> {
        // DELEGATE to the untouched CPU MerkleTreeMmcs verifier (identical
        // Commitment/Proof types) — the verify path never depends on the GPU.
        let (opened_values, opening_proof) = batch_proof.unpack();
        self.cpu.verify_batch(
            commit,
            dimensions,
            index,
            BatchOpeningRef::new(opened_values, opening_proof),
        )
    }
}

// ============================================================================
// SEAM 3 — GpuBabyBearMmcs: the all-BabyBear inner (apex-fold) GPU Merkle MMCS
//
// The FOLD (`prove_turn_chain_recursive` → `DreggRecursionConfig`) commits under
// `MerkleTreeMmcs<Packing, Packing, PaddingFreeSponge<Poseidon2BabyBear<16>,16,8,8>,
// TruncatedPermutation<Poseidon2BabyBear<16>,2,8,16>, 2, 8>` — the SAME two PCS
// seams as the shrink (DFT + MMCS tree build) but the hash is Poseidon2-BabyBear-
// W16, NOT BN254. `GpuDft` already serves the BabyBear DFT (it is native BabyBear).
// This is the BabyBear analog of `GpuBn254Mmcs`: an `Mmcs<BabyBear>` whose
// `commit` builds the digest layers with batched GPU Poseidon2-BabyBear-W16
// permutation kernels, bit-exact vs the CPU `MerkleTreeMmcs`, and whose
// `verify_batch` DELEGATES to the untouched CPU verifier.
//
// The permutation kernels are the KAT-proven codegen lifted from the sketch
// `circuit-prove/sketches/poseidon2-merkle-bench` (parity-verified there against
// the pinned `default_babybear_poseidon2_16` + the exact `PaddingFreeSponge` /
// `TruncatedPermutation` pair). Digests stay in 32-bit Montgomery form on-device
// end-to-end (BabyBear is `repr(transparent)` over its Montgomery u32, so a
// device digest word IS the BabyBear value — no canonicalization round-trip),
// re-gated by root parity vs the CPU tree in `tests` below.
// ============================================================================

/// The fold's Poseidon2-BabyBear-W16 permutation.
type BbPerm = Poseidon2BabyBear<16>;
/// The fold's leaf hash: `PaddingFreeSponge<Perm, WIDTH=16, RATE=8, OUT=8>`.
type BbHash = PaddingFreeSponge<BbPerm, 16, 8, 8>;
/// The fold's node compression: `TruncatedPermutation<Perm, N=2, CHUNK=8, WIDTH=16>`.
type BbCompress = TruncatedPermutation<BbPerm, 2, 8, 16>;
/// The fold's value MMCS — the exact type the inner recursion config commits under
/// (`plonky3_recursion_impl.rs`: `MyMmcs`).
pub type BbValMmcs = MerkleTreeMmcs<
    <BabyBear as Field>::Packing,
    <BabyBear as Field>::Packing,
    BbHash,
    BbCompress,
    2,
    8,
>;

// ---- WGSL codegen (ported verbatim from the KAT-proven sketch) --------------
// Emits ONLY assignments over predeclared u32 vars (s0..s15, t0..t6, m0..m3,
// sum, fsum) using mmul/addp/subp/halve — the identical straight-line body the
// sketch proved bit-exact vs p3.

/// x -> x^7 (4 mmuls), in place on `v`; t5/t6 scratch.
fn bb_sbox(v: &str) -> String {
    format!("t5 = mmul({v}, {v});\nt6 = mmul(t5, {v});\nt5 = mmul(t6, t6);\n{v} = mmul(t5, {v});\n")
}

/// The fast 4x4 MDS ([[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]; p3 apply_mat4).
fn bb_mat4(a: &str, b: &str, c: &str, d: &str) -> String {
    format!(
        "t0 = addp({a}, {b});\nt1 = addp({c}, {d});\nt2 = addp(t0, t1);\n\
         t3 = addp(t2, {b});\nt4 = addp(t2, {d});\n\
         {d} = addp(t4, addp({a}, {a}));\n{b} = addp(t3, addp({c}, {c}));\n\
         {a} = addp(t3, t0);\n{c} = addp(t4, t1);\n"
    )
}

/// External linear layer (p3 mds_light_permutation with MDSMat4, WIDTH=16).
fn bb_mds_light() -> String {
    let mut s = String::new();
    for ch in 0..4 {
        let i = 4 * ch;
        let v: Vec<String> = (i..i + 4).map(|k| format!("s{k}")).collect();
        s += &bb_mat4(&v[0], &v[1], &v[2], &v[3]);
    }
    for k in 0..4 {
        s += &format!(
            "m{k} = addp(addp(s{}, s{}), addp(s{}, s{}));\n",
            k,
            k + 4,
            k + 8,
            k + 12
        );
    }
    for i in 0..16 {
        s += &format!("s{i} = addp(s{i}, m{});\n", i % 4);
    }
    s
}

/// One external round: rc (Montgomery), x^7 each lane, external linear layer.
fn bb_ext_round(rc_mont: &[u32; 16]) -> String {
    let mut s = String::new();
    for i in 0..16 {
        s += &format!("s{i} = addp(s{i}, {}u);\n", rc_mont[i]);
        s += &bb_sbox(&format!("s{i}"));
    }
    s += &bb_mds_light();
    s
}

/// One internal round: rc + x^7 on lane 0, then 1 + Diag(V) (division by 2^k =
/// Montgomery-mul by 2^(32-k) mod P — exact).
fn bb_int_round(rc_mont: u32) -> String {
    let inv2_8 = 1u32 << 24;
    let inv2_2 = 1u32 << 30;
    let inv2_3 = 1u32 << 29;
    let inv2_4 = 1u32 << 28;
    let inv2_27 = 1u32 << 5;
    let mut s = format!("s0 = addp(s0, {rc_mont}u);\n");
    s += &bb_sbox("s0");
    s += "sum = addp(addp(addp(addp(s1, s2), addp(s3, s4)), addp(addp(s5, s6), addp(s7, s8))), addp(addp(addp(s9, s10), addp(s11, s12)), addp(addp(s13, s14), s15)));\n";
    s += "fsum = addp(sum, s0);\n";
    s += "s0 = subp(sum, s0);\n";
    s += "s1 = addp(s1, fsum);\n";
    s += "s2 = addp(addp(s2, s2), fsum);\n";
    s += "s3 = addp(halve(s3), fsum);\n";
    s += "t0 = addp(s4, s4);\ns4 = addp(fsum, addp(t0, s4));\n";
    s += "t0 = addp(s5, s5);\ns5 = addp(fsum, addp(t0, t0));\n";
    s += "s6 = subp(fsum, halve(s6));\n";
    s += "t0 = addp(s7, s7);\ns7 = subp(fsum, addp(t0, s7));\n";
    s += "t0 = addp(s8, s8);\ns8 = subp(fsum, addp(t0, t0));\n";
    s += &format!("s9 = addp(mmul(s9, {inv2_8}u), fsum);\n");
    s += &format!("s10 = addp(mmul(s10, {inv2_2}u), fsum);\n");
    s += &format!("s11 = addp(mmul(s11, {inv2_3}u), fsum);\n");
    s += &format!("s12 = addp(mmul(s12, {inv2_27}u), fsum);\n");
    s += &format!("s13 = subp(fsum, mmul(s13, {inv2_8}u));\n");
    s += &format!("s14 = subp(fsum, mmul(s14, {inv2_4}u));\n");
    s += &format!("s15 = subp(fsum, mmul(s15, {inv2_27}u));\n");
    s
}

/// The full width-16 permutation body (initial mds_light, 4 external, 13
/// internal, 4 external — p3 permute_mut order), RC in Montgomery form.
fn bb_perm_body() -> String {
    let rc_ei: [[u32; 16]; 4] = BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL
        .map(|row| row.map(|x| bb_to_mont(x.as_canonical_u32())));
    let rc_ef: [[u32; 16]; 4] = BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL
        .map(|row| row.map(|x| bb_to_mont(x.as_canonical_u32())));
    let rc_int: [u32; 13] =
        BABYBEAR_POSEIDON2_RC_16_INTERNAL.map(|x| bb_to_mont(x.as_canonical_u32()));
    let mut s = bb_mds_light();
    for rc in &rc_ei {
        s += &bb_ext_round(rc);
    }
    for &rc in &rc_int {
        s += &bb_int_round(rc);
    }
    for rc in &rc_ef {
        s += &bb_ext_round(rc);
    }
    s
}

/// The static WGSL for the BabyBear hash engine: the prelude (BabyBear
/// Montgomery mmul/addp/subp/halve via the 16-bit split), the W16 permutation
/// wrapped as `permute16(ptr)`, and the three tree kernels (leaf sponge /
/// pair compress / inject combine) over 8-u32 Montgomery digests.
const BB_HASH_WGSL: &str = r#"
const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u;

fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}

fn mmul(a: u32, b: u32) -> u32 {
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r: u32 = ab.y - tp.y;
    if (ab.y < tp.y) { r += P; }
    return r;
}

fn addp(a: u32, b: u32) -> u32 {
    let s = a + b;
    return select(s, s - P, s >= P);
}

fn subp(a: u32, b: u32) -> u32 {
    var r = a - b;
    if (a < b) { r += P; }
    return r;
}

fn halve(a: u32) -> u32 {
    return select(a >> 1u, (a >> 1u) + 0x3C000001u, (a & 1u) != 0u);
}

// The Poseidon2-BabyBear-W16 permutation over a function-scoped 16-lane state
// (Montgomery form in, Montgomery form out).
fn permute16(st: ptr<function, array<u32, 16>>) {
    var s0 = (*st)[0]; var s1 = (*st)[1]; var s2 = (*st)[2]; var s3 = (*st)[3];
    var s4 = (*st)[4]; var s5 = (*st)[5]; var s6 = (*st)[6]; var s7 = (*st)[7];
    var s8 = (*st)[8]; var s9 = (*st)[9]; var s10 = (*st)[10]; var s11 = (*st)[11];
    var s12 = (*st)[12]; var s13 = (*st)[13]; var s14 = (*st)[14]; var s15 = (*st)[15];
    var t0 = 0u; var t1 = 0u; var t2 = 0u; var t3 = 0u; var t4 = 0u; var t5 = 0u; var t6 = 0u;
    var m0 = 0u; var m1 = 0u; var m2 = 0u; var m3 = 0u; var sum = 0u; var fsum = 0u;
@PERM_BODY@
    (*st)[0] = s0; (*st)[1] = s1; (*st)[2] = s2; (*st)[3] = s3;
    (*st)[4] = s4; (*st)[5] = s5; (*st)[6] = s6; (*st)[7] = s7;
    (*st)[8] = s8; (*st)[9] = s9; (*st)[10] = s10; (*st)[11] = s11;
    (*st)[12] = s12; (*st)[13] = s13; (*st)[14] = s14; (*st)[15] = s15;
}

// b0: matrices arena / prev-layer digests / inject digests (Montgomery u32).
// b1: descriptor words. b2: output digests (8 Montgomery u32 each).
@group(0) @binding(0) var<storage, read> src: array<u32>;
@group(0) @binding(1) var<storage, read> desc: array<u32>;
@group(0) @binding(2) var<storage, read_write> outd: array<u32>;

// desc = [n_mats, base_row, n_rows, _, (off, w) * n_mats]
// One thread = one leaf row: PaddingFreeSponge<Perm,16,8,8> over the row's
// concatenation across all matrices in the height group. Overwrite-mode absorb:
// rate lanes [0,8) overwritten one element at a time, permute after every 8;
// a partial final block permutes iff it absorbed >=1 element (p3 hash_iter);
// capacity lanes [8,16) persist across permutes. Digest = state[0..8].
@compute @workgroup_size(@WG@)
fn leaf_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i = gid.x;
    let n_rows = desc[2];
    if (i >= n_rows) { return; }
    let row = desc[1] + i;
    let n_mats = desc[0];

    var s: array<u32, 16>;
    for (var k = 0u; k < 16u; k++) { s[k] = 0u; }
    var pos = 0u;
    for (var m = 0u; m < n_mats; m++) {
        let off = desc[4u + 2u * m];
        let w = desc[5u + 2u * m];
        let rbase = off + row * w;
        for (var c = 0u; c < w; c++) {
            s[pos] = src[rbase + c];
            pos += 1u;
            if (pos == 8u) {
                permute16(&s);
                pos = 0u;
            }
        }
    }
    if (pos != 0u) {
        permute16(&s);
    }
    for (var k = 0u; k < 8u; k++) { outd[row * 8u + k] = s[k]; }
}

// desc = [n_out, base, _, _]; src = prev-layer digests (Montgomery u32x8);
// outd[i] = TruncatedPermutation compress = permute([left8 ++ right8])[0..8].
@compute @workgroup_size(@WG@)
fn compress_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    let n_out = desc[0];
    if (i0 >= n_out) { return; }
    let i = desc[1] + i0;
    var s: array<u32, 16>;
    for (var k = 0u; k < 8u; k++) {
        s[k] = src[(2u * i) * 8u + k];
        s[8u + k] = src[(2u * i + 1u) * 8u + k];
    }
    permute16(&s);
    for (var k = 0u; k < 8u; k++) { outd[i * 8u + k] = s[k]; }
}

// desc = [n, base, _, _]; outd[i] = compress(outd[i], src[i]) — the
// matrix-injection combine (compress_and_inject: [current_node, injected_leaf]).
@compute @workgroup_size(@WG@)
fn combine_main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let i0 = gid.x;
    let n = desc[0];
    if (i0 >= n) { return; }
    let i = desc[1] + i0;
    var s: array<u32, 16>;
    for (var k = 0u; k < 8u; k++) {
        s[k] = outd[i * 8u + k];
        s[8u + k] = src[i * 8u + k];
    }
    permute16(&s);
    for (var k = 0u; k < 8u; k++) { outd[i * 8u + k] = s[k]; }
}
"#;

fn bb_hash_shader_source(wg: u32) -> String {
    BB_HASH_WGSL
        .replace("@PERM_BODY@", &bb_perm_body())
        .replace("@WG@", &wg.to_string())
}

/// Workgroup size for the BabyBear hash kernels. The W16 permutation keeps a
/// 16-lane register state — modest pressure; 64 mirrors the BN254 engine.
const BB_HASH_WG: u32 = 64;

#[cfg(not(target_arch = "wasm32"))]
struct BbHashCtx {
    bgl: wgpu::BindGroupLayout,
    leaf_pipe: wgpu::ComputePipeline,
    compress_pipe: wgpu::ComputePipeline,
    combine_pipe: wgpu::ComputePipeline,
    max_binding_u32s: usize,
    device: wgpu::Device,
    queue: wgpu::Queue,
}

#[cfg(not(target_arch = "wasm32"))]
impl BbHashCtx {
    fn new() -> Option<Self> {
        let shared = shared_gpu()?;
        let device = shared.device.clone();
        let queue = shared.queue.clone();
        let ro = |binding: u32, read_only: bool| wgpu::BindGroupLayoutEntry {
            binding,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty: wgpu::BindingType::Buffer {
                ty: wgpu::BufferBindingType::Storage { read_only },
                has_dynamic_offset: false,
                min_binding_size: None,
            },
            count: None,
        };
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("bb_hash_bgl"),
            entries: &[ro(0, true), ro(1, true), ro(2, false)],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let src = bb_hash_shader_source(BB_HASH_WG);
        // Trusted module + unchecked (indices are audited, all constant-indexed
        // in the perm; every tile slot written before read; parity re-gated).
        let module = unsafe {
            device.create_shader_module_trusted(
                wgpu::ShaderModuleDescriptor {
                    label: Some("poseidon2_babybear_w16_tree"),
                    source: wgpu::ShaderSource::Wgsl(src.into()),
                },
                wgpu::ShaderRuntimeChecks::unchecked(),
            )
        };
        let mk_pipe = |entry: &str| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&layout),
                module: &module,
                entry_point: Some(entry),
                compilation_options: wgpu::PipelineCompilationOptions {
                    zero_initialize_workgroup_memory: false,
                    ..Default::default()
                },
                cache: None,
            })
        };
        Some(BbHashCtx {
            leaf_pipe: mk_pipe("leaf_main"),
            compress_pipe: mk_pipe("compress_main"),
            combine_pipe: mk_pipe("combine_main"),
            bgl,
            max_binding_u32s: shared.max_buf_u32s,
            device,
            queue,
        })
    }

    fn bind(&self, src: &wgpu::Buffer, desc: &wgpu::Buffer, out: &wgpu::Buffer) -> wgpu::BindGroup {
        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &self.bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: src.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: desc.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: out.as_entire_binding(),
                },
            ],
        })
    }

    fn storage_buffer(&self, label: &str, u32s: usize, dst: bool) -> wgpu::Buffer {
        let mut usage = wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC;
        if dst {
            usage |= wgpu::BufferUsages::COPY_DST;
        }
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: (u32s.max(4) * 4) as u64,
            usage,
            mapped_at_creation: false,
        })
    }

    /// One immutable descriptor per queued dispatch; see the BN254 twin's
    /// descriptor-buffer invariant above.
    fn descriptor_buffer(&self, label: &str, words: &[u32]) -> wgpu::Buffer {
        let buf = self.storage_buffer(label, words.len(), true);
        self.queue
            .write_buffer(&buf, 0, bytemuck::cast_slice(words));
        buf
    }

    /// Dispatch the leaf sponge over `n_rows` rows in watchdog-safe chunks.
    fn dispatch_leaf(
        &self,
        arena: &wgpu::Buffer,
        _desc_buf: &wgpu::Buffer,
        out: &wgpu::Buffer,
        n_mats: u32,
        mat_descs: &[u32],
        n_rows: usize,
        perms_per_row: usize,
    ) {
        let rows_per_chunk = (HASH_MAX_PERMS_PER_DISPATCH / perms_per_row.max(1))
            .max(BB_HASH_WG as usize)
            .next_multiple_of(BB_HASH_WG as usize);
        let mut base = 0usize;
        while base < n_rows {
            let rows = rows_per_chunk.min(n_rows - base);
            let mut desc = vec![n_mats, base as u32, rows as u32, 0];
            desc.extend_from_slice(mat_descs);
            let chunk_desc = self.descriptor_buffer("bb_leaf_desc", &desc);
            let bindg = self.bind(arena, &chunk_desc, out);
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(&self.leaf_pipe);
                pass.set_bind_group(0, &bindg, &[]);
                pass.dispatch_workgroups((rows as u32).div_ceil(BB_HASH_WG), 1, 1);
            }
            self.queue.submit([enc.finish()]);
            base += rows;
        }
    }

    /// One compress or combine level (single dispatch per watchdog chunk).
    fn dispatch_level(
        &self,
        pipe: &wgpu::ComputePipeline,
        src: &wgpu::Buffer,
        _desc_buf: &wgpu::Buffer,
        out: &wgpu::Buffer,
        n: usize,
    ) {
        let mut base = 0usize;
        while base < n {
            let cnt = HASH_MAX_PERMS_PER_DISPATCH.min(n - base);
            let desc = [cnt as u32, base as u32, 0u32, 0u32];
            let chunk_desc = self.descriptor_buffer("bb_level_desc", &desc);
            let bindg = self.bind(src, &chunk_desc, out);
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(pipe);
                pass.set_bind_group(0, &bindg, &[]);
                pass.dispatch_workgroups((cnt as u32).div_ceil(BB_HASH_WG), 1, 1);
            }
            self.queue.submit([enc.finish()]);
            base += cnt;
        }
    }

    /// Read `n_digests` Montgomery digests (8 u32 each) back from `buf`.
    fn read_digests(&self, buf: &wgpu::Buffer, n_digests: usize) -> Vec<[u32; 8]> {
        let bytes = (n_digests * 32) as u64;
        let read = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("bb_dig_read"),
            size: bytes.max(32),
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(buf, 0, &read, 0, bytes);
        self.queue.submit([enc.finish()]);
        let slice = read.slice(..bytes);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let out: Vec<[u32; 8]> = {
            let mapped = slice.get_mapped_range();
            let words: &[u32] = bytemuck::cast_slice(&mapped);
            words
                .chunks_exact(8)
                .map(|c| c.try_into().unwrap())
                .collect()
        };
        read.unmap();
        out
    }
}

/// The GPU-built BabyBear Merkle tree: original matrices + all digest layers
/// (Montgomery u32x8; reinterpreted to `[BabyBear; 8]` at root/open time).
pub struct GpuBbMerkleTree<M> {
    leaves: Vec<M>,
    digest_layers: Vec<Vec<[u32; 8]>>,
}

/// ProverData: GPU tree or the CPU `MerkleTree` (fallback keeps exact upstream
/// semantics by construction).
pub enum GpuBbMmcsProverData<M> {
    Gpu(GpuBbMerkleTree<M>),
    Cpu(<BbValMmcs as Mmcs<BabyBear>>::ProverData<M>),
}

/// Reinterpret 8 Montgomery u32 words as `[BabyBear; 8]` (BabyBear is
/// `repr(transparent)` over its Montgomery u32 — the device word IS the value).
fn bb8_from_monty(d: &[u32; 8]) -> [BabyBear; 8] {
    core::array::from_fn(|k| u32s_into_bb(vec![d[k]])[0])
}

/// The GPU all-BabyBear MMCS. Same `Commitment`/`Proof` types as the CPU
/// `BbValMmcs`; `verify_batch` delegates to it (untouched upstream verifier).
#[derive(Clone)]
pub struct GpuBabyBearMmcs {
    cpu: BbValMmcs,
    cap_height: usize,
    // wgpu hash context — `!Send + !Sync` on wasm (CPU-only shell there; the
    // inner all-BabyBear GPU tree is a next-pass on-device sharpening).
    #[cfg(not(target_arch = "wasm32"))]
    ctx: Arc<OnceLock<Option<Mutex<BbHashCtx>>>>,
}

impl GpuBabyBearMmcs {
    /// Build with the pinned `default_babybear_poseidon2_16` permutation.
    pub fn new(cap_height: usize) -> Self {
        let perm = default_babybear_poseidon2_16();
        let hash = BbHash::new(perm.clone());
        let compress = BbCompress::new(perm);
        Self {
            cpu: BbValMmcs::new(hash, compress, cap_height),
            cap_height,
            #[cfg(not(target_arch = "wasm32"))]
            ctx: Arc::new(OnceLock::new()),
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn gpu(&self) -> Option<&Mutex<BbHashCtx>> {
        self.ctx
            .get_or_init(|| BbHashCtx::new().map(Mutex::new))
            .as_ref()
    }

    /// Whether a GPU adapter is available (None = permanent CPU fallback).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn adapter_available(&self) -> bool {
        self.gpu().is_some()
    }

    /// wasm CPU-shell (the on-device path is the async engine via `init_gpu()`).
    #[cfg(target_arch = "wasm32")]
    pub fn adapter_available(&self) -> bool {
        false
    }

    /// Estimated total permutations for a batch (leaf sponges + compresses).
    fn estimate_perms(heights_widths: &[(usize, usize)]) -> usize {
        let mut by_height: HashMap<usize, usize> = HashMap::new();
        for &(h, w) in heights_widths {
            *by_height.entry(h).or_default() += w;
        }
        let mut perms = 0usize;
        for (&h, &w_total) in &by_height {
            // One leaf permute per full rate-8 block, +1 for a partial block.
            perms += h * w_total.div_ceil(8).max(1);
        }
        let max_h = heights_widths.iter().map(|&(h, _)| h).max().unwrap_or(0);
        perms + 2 * max_h
    }

    /// The GPU tree build (mirror of `GpuBn254Mmcs::build_gpu_tree`; the leaf
    /// sponge is the BabyBear rate-8 overwrite sponge, digests are 8-u32
    /// Montgomery). Preconditions (checked by the caller): all heights powers
    /// of two, at least one matrix, cap_height == 0, GPU available.
    #[cfg(not(target_arch = "wasm32"))]
    fn build_gpu_tree<M: Matrix<BabyBear>>(
        &self,
        ctx: &BbHashCtx,
        leaves: Vec<M>,
    ) -> GpuBbMerkleTree<M> {
        let mut order: Vec<usize> = (0..leaves.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(leaves[i].height()));
        let mut groups: Vec<(usize, Vec<usize>)> = Vec::new();
        for i in order {
            let h = leaves[i].height();
            match groups.last_mut() {
                Some((gh, idxs)) if *gh == h => idxs.push(i),
                _ => groups.push((h, vec![i])),
            }
        }
        let max_h = groups[0].0;

        let hash_group =
            |group: &[usize], h: usize, out: &wgpu::Buffer, desc_buf: &wgpu::Buffer| {
                let total_w: usize = group.iter().map(|&i| leaves[i].width()).sum();
                let arena_u32s: usize = h * total_w;
                let arena = ctx.storage_buffer("bb_leaf_arena", arena_u32s, true);
                let mut mat_descs: Vec<u32> = Vec::with_capacity(group.len() * 2);
                let mut blits: Vec<(wgpu::Buffer, usize)> = Vec::new();
                let mut off = 0usize;
                for &i in group {
                    let m = &leaves[i];
                    let w = m.width();
                    if let Some(resident) = take_resident_lde(m) {
                        LDE_RESIDENT_HITS.fetch_add(1, Ordering::Relaxed);
                        blits.push((resident, off));
                    } else {
                        LDE_RESIDENT_MISSES.fetch_add(1, Ordering::Relaxed);
                        let mut staging = vec![0u32; h * w];
                        staging.par_chunks_mut(w).enumerate().for_each(|(r, dst)| {
                            let row = m.row_slice(r).expect("row in range");
                            dst.copy_from_slice(bb_as_u32s(&row));
                        });
                        ctx.queue.write_buffer(
                            &arena,
                            (off * 4) as u64,
                            bytemuck::cast_slice(&staging),
                        );
                    }
                    mat_descs.push(off as u32);
                    mat_descs.push(w as u32);
                    off += h * w;
                }
                if !blits.is_empty() {
                    let mut enc = ctx.device.create_command_encoder(&Default::default());
                    for (resident, boff) in &blits {
                        enc.copy_buffer_to_buffer(
                            resident,
                            0,
                            &arena,
                            (*boff * 4) as u64,
                            resident.size(),
                        );
                    }
                    ctx.queue.submit([enc.finish()]);
                }
                let perms_per_row = total_w.div_ceil(8).max(1);
                ctx.dispatch_leaf(
                    &arena,
                    desc_buf,
                    out,
                    group.len() as u32,
                    &mat_descs,
                    h,
                    perms_per_row,
                );
            };

        let desc_buf = ctx.storage_buffer("bb_desc", 4 + 2 * leaves.len().max(2), true);
        let dig_a = ctx.storage_buffer("bb_dig_a", max_h * 8, true);
        let dig_b = ctx.storage_buffer("bb_dig_b", max_h * 8, true);
        let inj = ctx.storage_buffer("bb_dig_inj", (max_h / 2).max(1) * 8, true);

        hash_group(&groups[0].1, max_h, &dig_a, &desc_buf);
        let mut digest_layers: Vec<Vec<[u32; 8]>> = vec![ctx.read_digests(&dig_a, max_h)];

        let mut next_group = 1usize;
        let mut cur_len = max_h;
        let mut cur_is_a = true;
        while cur_len > 1 {
            let next_len = cur_len / 2;
            let (src, dst) = if cur_is_a {
                (&dig_a, &dig_b)
            } else {
                (&dig_b, &dig_a)
            };
            ctx.dispatch_level(&ctx.compress_pipe, src, &desc_buf, dst, next_len);
            if next_group < groups.len() && groups[next_group].0 == next_len {
                hash_group(&groups[next_group].1, next_len, &inj, &desc_buf);
                ctx.dispatch_level(&ctx.combine_pipe, &inj, &desc_buf, dst, next_len);
                next_group += 1;
            }
            digest_layers.push(ctx.read_digests(dst, next_len));
            cur_len = next_len;
            cur_is_a = !cur_is_a;
        }
        assert_eq!(next_group, groups.len(), "all height groups consumed");

        GpuBbMerkleTree {
            leaves,
            digest_layers,
        }
    }
}

impl Mmcs<BabyBear> for GpuBabyBearMmcs {
    type ProverData<M> = GpuBbMmcsProverData<M>;
    type Commitment = <BbValMmcs as Mmcs<BabyBear>>::Commitment;
    type Proof = <BbValMmcs as Mmcs<BabyBear>>::Proof;
    type Error = MerkleTreeError;

    fn commit<M: Matrix<BabyBear>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let shapes: Vec<(usize, usize)> = inputs.iter().map(|m| (m.height(), m.width())).collect();
        let gpu_able = self.cap_height == 0
            && !inputs.is_empty()
            && shapes
                .iter()
                .all(|&(h, w)| h.is_power_of_two() && h > 0 && w > 0)
            && Self::estimate_perms(&shapes) >= MIN_GPU_MMCS_PERMS;
        // Native-only GPU fast-path (wgpu handles); wasm is the CPU shell.
        #[cfg(not(target_arch = "wasm32"))]
        if gpu_able && let Some(gm) = self.gpu() {
            let ctx = gm.lock().unwrap();
            let mut group_arena: HashMap<usize, usize> = HashMap::new();
            for &(h, w) in &shapes {
                *group_arena.entry(h).or_default() += h * w;
            }
            if group_arena.values().all(|&u| u <= ctx.max_binding_u32s) {
                let tree = self.build_gpu_tree(&ctx, inputs);
                let root = tree.digest_layers.last().expect("non-empty tree")[0];
                let commitment = MerkleCap::new(vec![bb8_from_monty(&root)]);
                clear_thread_resident_ldes();
                return (commitment, GpuBbMmcsProverData::Gpu(tree));
            }
        }
        clear_thread_resident_ldes();
        let (c, d) = self.cpu.commit(inputs);
        (c, GpuBbMmcsProverData::Cpu(d))
    }

    fn open_batch<M: Matrix<BabyBear>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> BatchOpening<BabyBear, Self> {
        match prover_data {
            GpuBbMmcsProverData::Cpu(tree) => {
                let (opened_values, opening_proof) = self.cpu.open_batch(index, tree).unpack();
                BatchOpening::new(opened_values, opening_proof)
            }
            GpuBbMmcsProverData::Gpu(tree) => {
                let max_h = tree
                    .leaves
                    .iter()
                    .map(|m| m.height())
                    .max()
                    .expect("non-empty batch");
                assert!(
                    index < max_h,
                    "index {index} out of bounds for height {max_h}"
                );
                let log_max = max_h.trailing_zeros() as usize;
                let opened_values: Vec<Vec<BabyBear>> = tree
                    .leaves
                    .iter()
                    .map(|m| {
                        let bits_reduced = log_max - m.height().trailing_zeros() as usize;
                        m.row(index >> bits_reduced)
                            .expect("reduced index in range")
                            .into_iter()
                            .collect()
                    })
                    .collect();
                let proof_levels = tree.digest_layers.len() - 1;
                let mut proof = Vec::with_capacity(proof_levels);
                let mut idx = index;
                for layer in &tree.digest_layers[..proof_levels] {
                    proof.push(bb8_from_monty(&layer[idx ^ 1]));
                    idx >>= 1;
                }
                BatchOpening::new(opened_values, proof)
            }
        }
    }

    fn get_matrices<'a, M: Matrix<BabyBear>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        match prover_data {
            GpuBbMmcsProverData::Cpu(tree) => self.cpu.get_matrices(tree),
            GpuBbMmcsProverData::Gpu(tree) => tree.leaves.iter().collect(),
        }
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[p3_matrix::Dimensions],
        index: usize,
        batch_proof: BatchOpeningRef<'_, BabyBear, Self>,
    ) -> Result<(), Self::Error> {
        let (opened_values, opening_proof) = batch_proof.unpack();
        self.cpu.verify_batch(
            commit,
            dimensions,
            index,
            BatchOpeningRef::new(opened_values, opening_proof),
        )
    }
}

// ============================================================================
// GpuDreggOuterConfig — the GPU variant of the outer "shrink" config
// ============================================================================

/// GPU value-matrix MMCS (BN254-native tree, GPU-built).
pub type GpuValMmcs = GpuBn254Mmcs;
/// GPU extension-field MMCS (FRI commit phase) — same `ExtensionMmcs`
/// flattening, GPU tree underneath.
pub type GpuChallengeMmcs = ExtensionMmcs<BabyBear, OuterChallenge, GpuValMmcs>;
/// The GPU outer PCS: same `TwoAdicFriPcs` shape, GPU DFT + GPU MMCS.
pub type GpuOuterPcs = TwoAdicFriPcs<BabyBear, GpuDft, GpuValMmcs, GpuChallengeMmcs>;
type GpuOuterStarkConfig = StarkConfig<GpuOuterPcs, OuterChallenge, OuterChallenger>;

/// The GPU variant of [`DreggOuterConfig`]: identical `Val`/`Challenge`/
/// `Challenger`/FRI knobs and BIT-IDENTICAL commitments + transcript — only
/// WHERE the DFT and Merkle hashing are computed changes.
#[derive(Clone)]
pub struct GpuDreggOuterConfig {
    config: Arc<GpuOuterStarkConfig>,
}

impl core::ops::Deref for GpuDreggOuterConfig {
    type Target = GpuOuterStarkConfig;
    fn deref(&self) -> &GpuOuterStarkConfig {
        &self.config
    }
}

impl StarkGenericConfig for GpuDreggOuterConfig {
    type Challenge = OuterChallenge;
    type Challenger = OuterChallenger;
    type Pcs = GpuOuterPcs;

    fn pcs(&self) -> &GpuOuterPcs {
        self.config.pcs()
    }

    fn initialise_challenger(&self) -> OuterChallenger {
        self.config.initialise_challenger()
    }
}

/// Build a [`GpuDreggOuterConfig`] with explicit FRI knobs (the GPU twin of
/// `create_outer_config_with_fri`).
pub fn create_gpu_outer_config_with_fri(
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
) -> GpuDreggOuterConfig {
    let perm = dregg_poseidon2_bn254();
    let val_mmcs = GpuValMmcs::new(0);
    let challenge_mmcs = GpuChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: commit_pow_bits,
        query_proof_of_work_bits: query_pow_bits,
        mmcs: challenge_mmcs,
    };
    let pcs = GpuOuterPcs::new(GpuDft::default(), val_mmcs, fri_params);
    let challenger =
        OuterChallenger::new(perm).expect("BabyBear order < BN254 order, RATE < WIDTH");
    GpuDreggOuterConfig {
        config: Arc::new(StarkConfig::new(pcs, challenger)),
    }
}

/// The production-shape GPU outer config (same FRI knobs as
/// `create_outer_config`). Native builds cache this in process-static storage:
/// wgpu 24 uses TLS internally while dropping buffers, so a Rust `thread_local!`
/// config can run its destructor after wgpu's own TLS is already gone and
/// abort an otherwise-successful proving thread. The static is intentionally
/// never torn down before process exit. wasm retains thread-local storage
/// because its WebGPU handles are not `Send + Sync`.
pub fn create_gpu_outer_config() -> GpuDreggOuterConfig {
    #[cfg(not(target_arch = "wasm32"))]
    {
        static GPU_OUTER_CONFIG: OnceLock<GpuDreggOuterConfig> = OnceLock::new();
        GPU_OUTER_CONFIG
            .get_or_init(|| {
                create_gpu_outer_config_with_fri(
                    OUTER_FRI_LOG_BLOWUP,
                    0,
                    1,
                    OUTER_FRI_NUM_QUERIES,
                    0,
                    OUTER_FRI_QUERY_POW_BITS,
                )
            })
            .clone()
    }
    #[cfg(target_arch = "wasm32")]
    {
        thread_local! {
            static GPU_OUTER_CONFIG: GpuDreggOuterConfig = create_gpu_outer_config_with_fri(
                OUTER_FRI_LOG_BLOWUP,
                0,
                1,
                OUTER_FRI_NUM_QUERIES,
                0,
                OUTER_FRI_QUERY_POW_BITS,
            );
        }
        GPU_OUTER_CONFIG.with(|c| c.clone())
    }
}

// ============================================================================
// The GPU shrink prove — the concrete twin of crate::apex_shrink at
// GpuDreggOuterConfig (same five steps, same split-config seam)
// ============================================================================

/// Extension degree — must match both configs' `Challenge = EF4`.
const D: usize = 4;
type EF = BinomialExtensionField<BabyBear, D>;

/// A shrink proof minted under the GPU config. Bit-identical (asserted in
/// tests) to the CPU [`crate::apex_shrink::ApexShrinkProof`] for the same apex.
pub struct GpuApexShrinkProof {
    pub proof: BatchStarkProof<GpuDreggOuterConfig>,
    pub prover_data: Rc<CircuitProverData<GpuDreggOuterConfig>>,
    /// Wall-clock seconds of the config-independent prepare phase (verifier
    /// circuit build + table-AIR extraction + witness generation — identical
    /// CPU code in the CPU and GPU shrink paths).
    pub prepare_seconds: f64,
    /// Wall-clock seconds of the config-dependent phase (preprocessed commit
    /// + `prove_all_tables` — the part the GPU backend accelerates).
    pub prove_seconds: f64,
}

/// [`crate::apex_shrink::shrink_apex_to_outer`], GPU-backed.
pub fn shrink_apex_to_gpu_outer(
    apex: &RecursionOutput<DreggRecursionConfig>,
    inner_config: &DreggRecursionConfig,
    gpu_outer_config: &GpuDreggOuterConfig,
) -> Result<GpuApexShrinkProof, String> {
    let input = apex.into_recursion_input::<BatchOnly>();
    shrink_recursion_input_to_gpu_outer(&input, inner_config, gpu_outer_config)
}

/// [`crate::apex_shrink::shrink_recursion_input_to_outer`], GPU-backed —
/// byte-for-byte the same five steps with the proving config swapped to the
/// GPU variant (the packing default is the same `default_shrink_packing`).
pub fn shrink_recursion_input_to_gpu_outer<A>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    gpu_outer_config: &GpuDreggOuterConfig,
) -> Result<GpuApexShrinkProof, String>
where
    A: RecursiveAir<BabyBear, EF, LogUpGadget>,
{
    let packing = default_shrink_packing();
    let backend = create_recursion_backend();
    let t_prepare = std::time::Instant::now();

    // (1) The apex-verifier circuit, built against the INNER config.
    let (circuit, verifier_result) =
        build_next_layer_circuit::<DreggRecursionConfig, A, _, D>(input, inner_config, &backend)
            .map_err(|e| format!("apex-verifier circuit build failed: {e:?}"))?;

    let constraint_profile = ProveNextLayerParams::default().constraint_profile;

    // (2) Table AIRs + preprocessed columns AT THE GPU OUTER CONFIG.
    let preprocessors: Vec<Box<dyn NpoPreprocessor<BabyBear>>> = vec![
        poseidon2_preprocessor::<BabyBear>(),
        recompose_preprocessor::<BabyBear>(false),
        expose_claim_preprocessor::<BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<GpuDreggOuterConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<GpuDreggOuterConfig, D>();
        builders.extend(recompose_air_builders::<GpuDreggOuterConfig, D>(1, false));
        builders.extend(expose_claim_air_builders::<GpuDreggOuterConfig, D>());
        builders
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GpuDreggOuterConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            constraint_profile,
        )
        .map_err(|e| format!("gpu-outer-config table-AIR extraction failed: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let ext_degrees: Vec<usize> = degrees
        .iter()
        .map(|&d| d + gpu_outer_config.is_zk())
        .collect();

    // (3) Witness generation (identical: inner-config FRI private data).
    let traces = {
        let public_inputs = verifier_result
            .pack_public_inputs(input)
            .map_err(|e| format!("shrink public-input packing failed: {e:?}"))?;
        let private_inputs = verifier_result
            .pack_private_inputs(input)
            .map_err(|e| format!("shrink private-input packing failed: {e:?}"))?;
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .map_err(|e| format!("shrink runner public inputs: {e:?}"))?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|e| format!("shrink runner private inputs: {e:?}"))?;
        let op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, A>>::op_ids(&verifier_result);
        backend
            .set_private_data(inner_config, &mut runner, op_ids, input)
            .map_err(|e| format!("shrink FRI private data: {e}"))?;
        runner
            .run()
            .map_err(|e| format!("apex-verifier witness generation failed: {e:?}"))?
    };

    let prepare_seconds = t_prepare.elapsed().as_secs_f64();
    let t_prove = std::time::Instant::now();

    // (4)+(5) Preprocessed commit + prove all tables UNDER THE GPU CONFIG.
    let prover_data = ProverData::from_airs_and_degrees(gpu_outer_config, &airs, &ext_degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let alu_variant = match constraint_profile {
        ConstraintProfile::Standard => AirVariant::Baseline,
        ConstraintProfile::RecursionOptimized => AirVariant::Optimized,
    };
    let prover = gpu_outer_shrink_prover(gpu_outer_config)
        .with_table_packing(packing.clone())
        .with_alu_variant(alu_variant);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|e| format!("gpu-outer-config shrink proving failed: {e}"))?;

    Ok(GpuApexShrinkProof {
        proof,
        prover_data: Rc::new(circuit_prover_data),
        prepare_seconds,
        prove_seconds: t_prove.elapsed().as_secs_f64(),
    })
}

/// Verify a GPU-minted shrink proof under the GPU config (the Mmcs verify
/// path delegates to the CPU `MerkleTreeMmcs` — see [`GpuBn254Mmcs`]).
pub fn verify_gpu_shrink_proof(
    proof: &BatchStarkProof<GpuDreggOuterConfig>,
    gpu_outer_config: &GpuDreggOuterConfig,
) -> Result<(), String> {
    gpu_outer_shrink_prover(gpu_outer_config)
        .verify_all_tables(proof)
        .map_err(|e| format!("gpu shrink proof verification failed: {e:?}"))
}

/// Convert a GPU-config shrink proof into a CPU-config one via serde (the
/// associated `Commitment`/`Proof` types are IDENTICAL, so this is a pure
/// type re-tag — used to round-trip a GPU proof through the unchanged CPU
/// `verify_shrink_proof`).
pub fn gpu_shrink_proof_to_cpu(
    proof: &BatchStarkProof<GpuDreggOuterConfig>,
) -> Result<BatchStarkProof<DreggOuterConfig>, String> {
    let bytes = postcard::to_allocvec(proof).map_err(|e| format!("gpu proof serialize: {e}"))?;
    postcard::from_bytes(&bytes).map_err(|e| format!("gpu->cpu proof deserialize: {e}"))
}

/// The GPU twin of `crate::apex_shrink::outer_shrink_prover` — same
/// non-primitive table registration.
pub fn gpu_outer_shrink_prover(
    gpu_outer_config: &GpuDreggOuterConfig,
) -> BatchStarkProver<GpuDreggOuterConfig> {
    let mut prover = BatchStarkProver::new(gpu_outer_config.clone());
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();
    prover
}

/// Convenience: the inner config the shrink verifies (re-export seam for the
/// e2e test).
pub fn gpu_shrink_inner_config() -> DreggRecursionConfig {
    ir2_leaf_wrap_config()
}

// ============================================================================
// GpuDreggRecursionConfig — the GPU variant of the all-BabyBear FOLD config
// (`DreggRecursionConfig`), the parallel of `GpuDreggOuterConfig` for the inner
// recursion tower.
//
// The fold (`prove_turn_chain_recursive` → `DreggRecursionConfig`) commits
// under `TwoAdicFriPcs<BabyBear, Radix2DitParallel, MerkleTreeMmcs<..
// PaddingFreeSponge<Poseidon2BabyBear<16>,16,8,8> ..>, ExtensionMmcs<..>>`.
// This config keeps `Val`/`Challenge`/`Challenger` and the FRI knobs identical
// and swaps only WHERE the two PCS seams compute: the DFT → [`GpuDft`] (native
// BabyBear) and the Poseidon2-BabyBear-W16 Merkle tree build → the bit-exact
// [`GpuBabyBearMmcs`] (whose `Commitment`/`Proof` types EQUAL the CPU
// `MerkleTreeMmcs`'s and whose `verify_batch` delegates to it).
//
// Wiring mirror of the shrink (`shrink_recursion_input_to_gpu_outer`): a fold
// layer's verifier CIRCUIT is built at the CPU inner `DreggRecursionConfig`
// (which carries `FriRecursionConfig`), and only the OUTPUT tables are proved
// under this GPU config, which is a plain `StarkGenericConfig`. The emitted
// `BatchStarkProof<GpuDreggRecursionConfig>` is BYTE-IDENTICAL to the CPU
// `BatchStarkProof<DreggRecursionConfig>` for the same layer (both provers
// deterministic, the GPU path bit-exact) and serde-retags into it, so the next
// fold layer / the in-circuit recursion verifier accepts it unchanged. Both
// properties are asserted in `tests/gpu_recursion_fold_e2e.rs`.
// ============================================================================

/// The fold's DuplexChallenger over Poseidon2-BabyBear-W16 (RATE 8) — the exact
/// challenger `DreggRecursionConfig` uses.
pub type GpuFoldChallenger = DuplexChallenger<BabyBear, BbPerm, 16, 8>;
/// GPU value-matrix MMCS for the fold (all-BabyBear tree, GPU-built).
pub type GpuFoldValMmcs = GpuBabyBearMmcs;
/// GPU extension-field MMCS (FRI commit phase) — same `ExtensionMmcs`
/// flattening, GPU tree underneath.
pub type GpuFoldChallengeMmcs = ExtensionMmcs<BabyBear, EF, GpuFoldValMmcs>;
/// The GPU fold PCS: same `TwoAdicFriPcs` shape, GPU DFT + GPU BabyBear MMCS.
pub type GpuFoldPcs = TwoAdicFriPcs<BabyBear, GpuDft, GpuFoldValMmcs, GpuFoldChallengeMmcs>;
type GpuFoldStarkConfig = StarkConfig<GpuFoldPcs, EF, GpuFoldChallenger>;

/// The GPU variant of [`DreggRecursionConfig`]: identical `Val`/`Challenge`/
/// `Challenger`/FRI knobs and BIT-IDENTICAL commitments + transcript — only
/// WHERE the DFT and Poseidon2-BabyBear-W16 Merkle hashing are computed changes.
#[derive(Clone)]
pub struct GpuDreggRecursionConfig {
    config: Arc<GpuFoldStarkConfig>,
}

impl core::ops::Deref for GpuDreggRecursionConfig {
    type Target = GpuFoldStarkConfig;
    fn deref(&self) -> &GpuFoldStarkConfig {
        &self.config
    }
}

impl StarkGenericConfig for GpuDreggRecursionConfig {
    type Challenge = EF;
    type Challenger = GpuFoldChallenger;
    type Pcs = GpuFoldPcs;

    fn pcs(&self) -> &GpuFoldPcs {
        self.config.pcs()
    }

    fn initialise_challenger(&self) -> GpuFoldChallenger {
        self.config.initialise_challenger()
    }
}

/// Build a [`GpuDreggRecursionConfig`] with explicit FRI knobs (the GPU twin of
/// `create_recursion_config_with_fri`).
pub fn create_gpu_recursion_config_with_fri(
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
) -> GpuDreggRecursionConfig {
    let perm = default_babybear_poseidon2_16();
    let val_mmcs = GpuFoldValMmcs::new(0);
    let challenge_mmcs = GpuFoldChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: commit_pow_bits,
        query_proof_of_work_bits: query_pow_bits,
        mmcs: challenge_mmcs,
    };
    let pcs = GpuFoldPcs::new(GpuDft::default(), val_mmcs, fri_params);
    let challenger = GpuFoldChallenger::new(perm);
    GpuDreggRecursionConfig {
        config: Arc::new(StarkConfig::new(pcs, challenger)),
    }
}

/// The default-shape GPU fold config — the SAME FRI knobs as
/// `create_recursion_config` (log_blowup=3, arity 1, 38 queries, 14 query-PoW
/// bits). Native builds use process-static storage for the same wgpu-TLS
/// teardown reason documented on [`create_gpu_outer_config`].
pub fn create_gpu_recursion_config() -> GpuDreggRecursionConfig {
    #[cfg(not(target_arch = "wasm32"))]
    {
        static GPU_RECURSION_CONFIG: OnceLock<GpuDreggRecursionConfig> = OnceLock::new();
        GPU_RECURSION_CONFIG
            .get_or_init(|| create_gpu_recursion_config_with_fri(3, 0, 1, 38, 0, 14))
            .clone()
    }
    #[cfg(target_arch = "wasm32")]
    {
        thread_local! {
            static GPU_RECURSION_CONFIG: GpuDreggRecursionConfig =
                create_gpu_recursion_config_with_fri(3, 0, 1, 38, 0, 14);
        }
        GPU_RECURSION_CONFIG.with(|c| c.clone())
    }
}

/// GPU recursion config matching the production rotated fold's
/// `ir2_leaf_wrap_config`: log_blowup=6, 19 queries, binary FRI folding, and
/// 16 query-PoW bits.  The CPU and GPU configs differ only in their DFT/MMCS
/// implementations, so proofs re-tag byte-for-byte between them.
pub fn create_gpu_ir2_leaf_wrap_config() -> GpuDreggRecursionConfig {
    #[cfg(not(target_arch = "wasm32"))]
    {
        static GPU_IR2_WRAP_CONFIG: OnceLock<GpuDreggRecursionConfig> = OnceLock::new();
        GPU_IR2_WRAP_CONFIG
            .get_or_init(|| create_gpu_recursion_config_with_fri(6, 0, 1, 19, 0, 16))
            .clone()
    }
    #[cfg(target_arch = "wasm32")]
    {
        thread_local! {
            static GPU_IR2_WRAP_CONFIG: GpuDreggRecursionConfig =
                create_gpu_recursion_config_with_fri(6, 0, 1, 19, 0, 16);
        }
        GPU_IR2_WRAP_CONFIG.with(|c| c.clone())
    }
}

static GPU_RECURSION_LAYERS: AtomicU64 = AtomicU64::new(0);
static CPU_RECURSION_LAYERS: AtomicU64 = AtomicU64::new(0);
static CPU_RECURSION_LEAF_NS: AtomicU64 = AtomicU64::new(0);
static CPU_RECURSION_AGG_NS: AtomicU64 = AtomicU64::new(0);
static GPU_RECURSION_LEAF_PREP_NS: AtomicU64 = AtomicU64::new(0);
static GPU_RECURSION_LEAF_PROVE_NS: AtomicU64 = AtomicU64::new(0);
static GPU_RECURSION_AGG_PREP_NS: AtomicU64 = AtomicU64::new(0);
static GPU_RECURSION_AGG_PROVE_NS: AtomicU64 = AtomicU64::new(0);

/// Cumulative production-dispatch timing, in nanoseconds.  Snapshot before
/// and after a fold to attribute its leaf-wrap vs aggregation time without
/// adding logging to the production hot path.
#[derive(Clone, Copy, Debug, Default)]
pub struct RecursionDispatchProfile {
    pub cpu_leaf_ns: u64,
    pub cpu_aggregation_ns: u64,
    pub gpu_leaf_prepare_ns: u64,
    pub gpu_leaf_prove_ns: u64,
    pub gpu_aggregation_prepare_ns: u64,
    pub gpu_aggregation_prove_ns: u64,
}

pub fn recursion_dispatch_profile() -> RecursionDispatchProfile {
    RecursionDispatchProfile {
        cpu_leaf_ns: CPU_RECURSION_LEAF_NS.load(Ordering::Relaxed),
        cpu_aggregation_ns: CPU_RECURSION_AGG_NS.load(Ordering::Relaxed),
        gpu_leaf_prepare_ns: GPU_RECURSION_LEAF_PREP_NS.load(Ordering::Relaxed),
        gpu_leaf_prove_ns: GPU_RECURSION_LEAF_PROVE_NS.load(Ordering::Relaxed),
        gpu_aggregation_prepare_ns: GPU_RECURSION_AGG_PREP_NS.load(Ordering::Relaxed),
        gpu_aggregation_prove_ns: GPU_RECURSION_AGG_PROVE_NS.load(Ordering::Relaxed),
    }
}

fn seconds_to_ns_saturating(seconds: f64) -> u64 {
    (seconds.max(0.0) * 1e9).min(u64::MAX as f64) as u64
}

/// `(gpu_layers, cpu_layers)` dispatched through the production recursion
/// wrapper.  This is deliberately layer-level telemetry: a GPU-config layer
/// may still CPU-fallback for individual tiny matrices below the kernel
/// thresholds without changing proof bytes.
pub fn recursion_dispatch_counters() -> (u64, u64) {
    (
        GPU_RECURSION_LAYERS.load(Ordering::Relaxed),
        CPU_RECURSION_LAYERS.load(Ordering::Relaxed),
    )
}

/// Runtime policy for the production recursion wrapper.
///
/// `DREGG_GPU_RECURSION=cpu|off|0` forces the original CPU recursion path;
/// `gpu|on|1` forces the GPU config (whose kernels still fail safely to CPU if
/// the adapter disappears); unset/`auto` uses GPU only when the native sync
/// adapter is available.  wasm always keeps the sync CPU path — browser GPU
/// proving remains the async WGSL engine reached through [`init_gpu`].
pub fn production_gpu_recursion_enabled() -> bool {
    let policy = std::env::var("DREGG_GPU_RECURSION")
        .unwrap_or_else(|_| "auto".to_string())
        .to_ascii_lowercase();
    match policy.as_str() {
        "cpu" | "off" | "false" | "0" => false,
        "gpu" | "on" | "true" | "1" => cfg!(not(target_arch = "wasm32")),
        _ => {
            #[cfg(not(target_arch = "wasm32"))]
            {
                GpuDft::default().adapter_name().is_some()
            }
            #[cfg(target_arch = "wasm32")]
            {
                false
            }
        }
    }
}

/// A recursion-layer (fold) proof minted under the GPU fold config. Byte-
/// identical (asserted in tests) to the CPU
/// `RecursionOutput<DreggRecursionConfig>.0` for the same layer.
pub struct GpuRecursionLayerProof {
    pub proof: BatchStarkProof<GpuDreggRecursionConfig>,
    pub prover_data: Rc<CircuitProverData<GpuDreggRecursionConfig>>,
    /// The lookup contexts produced by the exact CPU-config AIR construction
    /// for this circuit. They are not serialized in `BatchStarkProof`, but a
    /// parent recursion/shrink circuit consumes their precise expression order.
    pub cpu_lookups: Vec<Lookups<BabyBear>>,
    /// Wall-clock seconds of the config-independent prepare phase (verifier
    /// circuit build + table-AIR extraction + witness generation — identical
    /// CPU code in the CPU and GPU fold paths).
    pub prepare_seconds: f64,
    /// Wall-clock seconds of the config-dependent phase (preprocessed commit +
    /// `prove_all_tables` — the part the GPU backend accelerates).
    pub prove_seconds: f64,
}

/// Rebuild only the cheap, non-serialized lookup portion of the CPU common
/// data from the exact circuit AIRs. Constructing a full CPU `ProverData` here
/// would also redo the CPU LDE/Merkle preprocessed commitment and erase much of
/// the GPU win; the commitment and its metadata are already present, bit-exact,
/// in the serialized GPU proof.
fn cpu_recursion_lookups_for_circuit(
    circuit: &Circuit<EF>,
    packing: &TablePacking,
    constraint_profile: ConstraintProfile,
) -> Result<Vec<Lookups<BabyBear>>, String> {
    let preprocessors: Vec<Box<dyn NpoPreprocessor<BabyBear>>> = vec![
        poseidon2_preprocessor::<BabyBear>(),
        recompose_preprocessor::<BabyBear>(false),
        expose_claim_preprocessor::<BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<DreggRecursionConfig, D>();
        builders.extend(recompose_air_builders::<DreggRecursionConfig, D>(1, false));
        builders.extend(expose_claim_air_builders::<DreggRecursionConfig, D>());
        builders
    };
    let (airs_degrees, _, _) = get_airs_and_degrees_with_prep::<DreggRecursionConfig, EF, D>(
        circuit,
        packing,
        &preprocessors,
        &air_builders,
        constraint_profile,
    )
    .map_err(|e| format!("cpu lookup-context AIR extraction failed: {e:?}"))?;
    Ok(airs_degrees
        .iter()
        .map(|(air, _)| Lookups::<BabyBear>::from_air::<EF, _>(air))
        .collect())
}

/// Prove ONE recursion layer (the fold's per-step leaf-wrap / aggregation
/// verifier circuit) under the GPU fold config. Byte-for-byte the same steps as
/// the recursion library's `prove_next_layer` (non-cached branch) with the
/// proving config swapped to the GPU variant — mirror of
/// [`shrink_recursion_input_to_gpu_outer`], but the output stays all-BabyBear
/// `DreggRecursionConfig`-shaped (round-trippable, not the BN254 shrink).
///
/// The circuit is built and the FRI private data injected at the CPU
/// `inner_config` (the config of the CHILD being verified in-circuit); only the
/// output preprocessed commit + `prove_all_tables` run under `gpu_config`.
pub fn prove_recursion_layer_gpu<A>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    gpu_config: &GpuDreggRecursionConfig,
) -> Result<GpuRecursionLayerProof, String>
where
    A: RecursiveAir<BabyBear, EF, LogUpGadget>,
{
    prove_recursion_layer_gpu_with_expose(input, inner_config, gpu_config, None)
}

/// [`prove_recursion_layer_gpu`] with the recursion library's exposed-claim
/// hook.  Production descriptor leaves use this form to carry the ordered
/// segment (and, for carrier leaves, the backing claim) into the next layer.
/// The hook changes only the verifier circuit being proved; the GPU/CPU split
/// remains the same and the emitted proof is still byte-identical to the CPU
/// recursion library for that circuit.
pub fn prove_recursion_layer_gpu_with_expose<A>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    gpu_config: &GpuDreggRecursionConfig,
    expose: Option<NextLayerExposeHook<'_, EF>>,
) -> Result<GpuRecursionLayerProof, String>
where
    A: RecursiveAir<BabyBear, EF, LogUpGadget>,
{
    // Match the recursion library's default layer params (TablePacking::new(1,4),
    // Standard profile) — `default_shrink_packing()` IS that packing, so the
    // proof is byte-identical to a `prove_recursive_layer_for_air` layer.
    let packing = default_shrink_packing();
    let backend = create_recursion_backend();
    let t_prepare = std::time::Instant::now();

    // (1) The layer verifier circuit, built against the INNER (child) config.
    let (circuit, verifier_result) = build_next_layer_circuit_with_expose::<
        DreggRecursionConfig,
        A,
        _,
        D,
    >(input, inner_config, &backend, expose)
    .map_err(|e| format!("layer verifier circuit build failed: {e:?}"))?;

    let constraint_profile = ProveNextLayerParams::default().constraint_profile;

    // (2) Table AIRs + preprocessed columns AT THE GPU FOLD CONFIG. The
    // preprocessor/builder set mirrors the FRI backend's own at D=4 default
    // knobs (recompose_lanes=1, coeff-lookups OFF because the W16 challenger's
    // extension degree equals D) — the SAME reconstruction the shrink uses.
    let preprocessors: Vec<Box<dyn NpoPreprocessor<BabyBear>>> = vec![
        poseidon2_preprocessor::<BabyBear>(),
        recompose_preprocessor::<BabyBear>(false),
        expose_claim_preprocessor::<BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<GpuDreggRecursionConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<GpuDreggRecursionConfig, D>();
        builders.extend(recompose_air_builders::<GpuDreggRecursionConfig, D>(
            1, false,
        ));
        builders.extend(expose_claim_air_builders::<GpuDreggRecursionConfig, D>());
        builders
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GpuDreggRecursionConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            constraint_profile,
        )
        .map_err(|e| format!("gpu-fold-config table-AIR extraction failed: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let ext_degrees: Vec<usize> = degrees.iter().map(|&d| d + gpu_config.is_zk()).collect();
    let cpu_lookups = cpu_recursion_lookups_for_circuit(&circuit, &packing, constraint_profile)?;

    // (3) Witness generation: the FRI private data (the child's BabyBear Merkle
    // siblings) is injected via the INNER config — it describes the proof being
    // VERIFIED, not the proof being minted.
    let traces = {
        let public_inputs = verifier_result
            .pack_public_inputs(input)
            .map_err(|e| format!("layer public-input packing failed: {e:?}"))?;
        let private_inputs = verifier_result
            .pack_private_inputs(input)
            .map_err(|e| format!("layer private-input packing failed: {e:?}"))?;
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .map_err(|e| format!("layer runner public inputs: {e:?}"))?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|e| format!("layer runner private inputs: {e:?}"))?;
        let op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, A>>::op_ids(&verifier_result);
        backend
            .set_private_data(inner_config, &mut runner, op_ids, input)
            .map_err(|e| format!("layer FRI private data: {e}"))?;
        runner
            .run()
            .map_err(|e| format!("layer verifier witness generation failed: {e:?}"))?
    };

    let prepare_seconds = t_prepare.elapsed().as_secs_f64();
    let t_prove = std::time::Instant::now();

    // (4)+(5) Preprocessed commit + prove all tables UNDER THE GPU FOLD CONFIG.
    let prover_data = ProverData::from_airs_and_degrees(gpu_config, &airs, &ext_degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let alu_variant = match constraint_profile {
        ConstraintProfile::Standard => AirVariant::Baseline,
        ConstraintProfile::RecursionOptimized => AirVariant::Optimized,
    };
    let prover = gpu_recursion_prover(gpu_config)
        .with_table_packing(packing.clone())
        .with_alu_variant(alu_variant);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|e| format!("gpu-fold-config layer proving failed: {e}"))?;

    Ok(GpuRecursionLayerProof {
        proof,
        prover_data: Rc::new(circuit_prover_data),
        cpu_lookups,
        prepare_seconds,
        prove_seconds: t_prove.elapsed().as_secs_f64(),
    })
}

/// GPU twin of the recursion library's 2-to-1 `BatchOnly` aggregation layer,
/// including the segment-combine exposed-claim hook used by the production
/// turn-chain fold.  Both child proofs are verified in one CPU-built circuit;
/// the output table LDEs and BabyBear Poseidon2 MMCS commits run through the
/// GPU config.
pub fn prove_recursion_aggregation_gpu_with_expose(
    left: &RecursionInput<'_, DreggRecursionConfig, BatchOnly>,
    right: &RecursionInput<'_, DreggRecursionConfig, BatchOnly>,
    inner_config: &DreggRecursionConfig,
    gpu_config: &GpuDreggRecursionConfig,
    expose: Option<AggExposeHook<'_, EF>>,
) -> Result<GpuRecursionLayerProof, String> {
    let packing = default_shrink_packing();
    let backend = create_recursion_backend();
    let t_prepare = std::time::Instant::now();

    // Build the same two-child verifier circuit as
    // `build_and_prove_aggregation_layer_with_expose`.
    let mut cb = CircuitBuilder::new();
    <_ as PcsRecursionBackend<DreggRecursionConfig, BatchOnly, D>>::prepare_circuit(
        &backend,
        inner_config,
        &mut cb,
    )
    .map_err(|e| format!("left aggregation circuit prepare failed: {e:?}"))?;
    <_ as PcsRecursionBackend<DreggRecursionConfig, BatchOnly, D>>::prepare_circuit(
        &backend,
        inner_config,
        &mut cb,
    )
    .map_err(|e| format!("right aggregation circuit prepare failed: {e:?}"))?;
    let left_result =
        <_ as PcsRecursionBackend<DreggRecursionConfig, BatchOnly, D>>::build_verifier_circuit(
            &backend,
            left,
            inner_config,
            &mut cb,
        )
        .map_err(|e| format!("left aggregation verifier build failed: {e:?}"))?;
    let right_result =
        <_ as PcsRecursionBackend<DreggRecursionConfig, BatchOnly, D>>::build_verifier_circuit(
            &backend,
            right,
            inner_config,
            &mut cb,
        )
        .map_err(|e| format!("right aggregation verifier build failed: {e:?}"))?;
    if let Some(expose) = expose {
        let left_apt =
            <_ as VerifierCircuitResult<DreggRecursionConfig, BatchOnly>>::air_public_targets(
                &left_result,
            );
        let right_apt =
            <_ as VerifierCircuitResult<DreggRecursionConfig, BatchOnly>>::air_public_targets(
                &right_result,
            );
        expose(&mut cb, &left_apt, &right_apt);
    }
    let circuit = cb
        .build()
        .map_err(|e| format!("aggregation circuit finalization failed: {e:?}"))?;

    let constraint_profile = ProveNextLayerParams::default().constraint_profile;
    let preprocessors: Vec<Box<dyn NpoPreprocessor<BabyBear>>> = vec![
        poseidon2_preprocessor::<BabyBear>(),
        recompose_preprocessor::<BabyBear>(false),
        expose_claim_preprocessor::<BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<GpuDreggRecursionConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<GpuDreggRecursionConfig, D>();
        builders.extend(recompose_air_builders::<GpuDreggRecursionConfig, D>(
            1, false,
        ));
        builders.extend(expose_claim_air_builders::<GpuDreggRecursionConfig, D>());
        builders
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GpuDreggRecursionConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            constraint_profile,
        )
        .map_err(|e| format!("gpu aggregation table-AIR extraction failed: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let ext_degrees: Vec<usize> = degrees.iter().map(|&d| d + gpu_config.is_zk()).collect();
    let cpu_lookups = cpu_recursion_lookups_for_circuit(&circuit, &packing, constraint_profile)?;

    let traces = {
        let mut public_inputs = left_result
            .pack_public_inputs(left)
            .map_err(|e| format!("left aggregation public inputs: {e:?}"))?;
        public_inputs.extend(
            right_result
                .pack_public_inputs(right)
                .map_err(|e| format!("right aggregation public inputs: {e:?}"))?,
        );
        let mut private_inputs = left_result
            .pack_private_inputs(left)
            .map_err(|e| format!("left aggregation private inputs: {e:?}"))?;
        private_inputs.extend(
            right_result
                .pack_private_inputs(right)
                .map_err(|e| format!("right aggregation private inputs: {e:?}"))?,
        );
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .map_err(|e| format!("aggregation runner public inputs: {e:?}"))?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|e| format!("aggregation runner private inputs: {e:?}"))?;
        let left_op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, BatchOnly>>::op_ids(&left_result);
        let right_op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, BatchOnly>>::op_ids(&right_result);
        <_ as PcsRecursionBackend<DreggRecursionConfig, BatchOnly, D>>::set_private_data(
            &backend,
            inner_config,
            &mut runner,
            left_op_ids,
            left,
        )
        .map_err(|e| format!("left aggregation FRI private data: {e}"))?;
        <_ as PcsRecursionBackend<DreggRecursionConfig, BatchOnly, D>>::set_private_data(
            &backend,
            inner_config,
            &mut runner,
            right_op_ids,
            right,
        )
        .map_err(|e| format!("right aggregation FRI private data: {e}"))?;
        runner
            .run()
            .map_err(|e| format!("aggregation verifier witness generation failed: {e:?}"))?
    };

    let prepare_seconds = t_prepare.elapsed().as_secs_f64();
    let t_prove = std::time::Instant::now();
    let prover_data = ProverData::from_airs_and_degrees(gpu_config, &airs, &ext_degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let alu_variant = match constraint_profile {
        ConstraintProfile::Standard => AirVariant::Baseline,
        ConstraintProfile::RecursionOptimized => AirVariant::Optimized,
    };
    let prover = gpu_recursion_prover(gpu_config)
        .with_table_packing(packing)
        .with_alu_variant(alu_variant);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|e| format!("gpu aggregation proving failed: {e}"))?;

    Ok(GpuRecursionLayerProof {
        proof,
        prover_data: Rc::new(circuit_prover_data),
        cpu_lookups,
        prepare_seconds,
        prove_seconds: t_prove.elapsed().as_secs_f64(),
    })
}

/// Verify a GPU-minted fold-layer proof under the GPU fold config (the Mmcs
/// verify path delegates to the CPU `MerkleTreeMmcs` — see [`GpuBabyBearMmcs`]).
pub fn verify_gpu_recursion_layer(
    proof: &BatchStarkProof<GpuDreggRecursionConfig>,
    gpu_config: &GpuDreggRecursionConfig,
) -> Result<(), String> {
    gpu_recursion_prover(gpu_config)
        .verify_all_tables(proof)
        .map_err(|e| format!("gpu fold-layer proof verification failed: {e:?}"))
}

/// Re-tag a GPU-config fold-layer proof as a CPU-config one via serde (the
/// associated `Commitment`/`Proof` types are IDENTICAL, so this is a pure type
/// re-tag) — round-trips a GPU proof through the unchanged CPU
/// `verify_recursive_batch_proof` / the next fold layer.
pub fn gpu_recursion_proof_to_cpu(
    proof: &BatchStarkProof<GpuDreggRecursionConfig>,
) -> Result<BatchStarkProof<DreggRecursionConfig>, String> {
    gpu_recursion_proof_to_cpu_with_config(proof, &create_recursion_config())
}

/// [`gpu_recursion_proof_to_cpu`] under the output layer's exact CPU FRI
/// config. Postcard performs the generic config re-tag. The lookup contexts
/// are intentionally omitted from `BatchStarkProof` serialization, so copy
/// them directly from the GPU proof: both configs use `BabyBear`, and retaining
/// their original expression order is required for byte-identical parent-layer
/// and shrink proofs.
pub fn gpu_recursion_proof_to_cpu_with_config(
    proof: &BatchStarkProof<GpuDreggRecursionConfig>,
    _cpu_config: &DreggRecursionConfig,
) -> Result<BatchStarkProof<DreggRecursionConfig>, String> {
    gpu_recursion_proof_to_cpu_with_lookups(proof, &proof.stark_common.lookups)
}

fn gpu_recursion_proof_to_cpu_with_lookups(
    proof: &BatchStarkProof<GpuDreggRecursionConfig>,
    cpu_lookups: &[Lookups<BabyBear>],
) -> Result<BatchStarkProof<DreggRecursionConfig>, String> {
    let bytes = postcard::to_allocvec(proof).map_err(|e| format!("gpu proof serialize: {e}"))?;
    let mut cpu_proof: BatchStarkProof<DreggRecursionConfig> =
        postcard::from_bytes(&bytes).map_err(|e| format!("gpu->cpu proof deserialize: {e}"))?;
    cpu_proof.stark_common.lookups = cpu_lookups.to_vec();
    Ok(cpu_proof)
}

/// Production recursion-layer dispatch.  It preserves the original CPU path
/// as an explicit/runtime fallback and otherwise proves the identical verifier
/// circuit through `GpuDft + GpuBabyBearMmcs`, re-tagging the bit-exact proof
/// into the unchanged `DreggRecursionConfig` type consumed by every parent and
/// CPU verifier.
///
/// The prover-only cache is intentionally omitted on the GPU boundary.  A
/// `RecursionOutput` continuation reads its proof's own `stark_common`; the
/// optional cache is neither serialized nor consulted by the fold/verify path.
pub fn prove_recursion_layer_auto_with_expose<A>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    expose: Option<NextLayerExposeHook<'_, EF>>,
) -> Result<RecursionOutput<DreggRecursionConfig>, String>
where
    A: RecursiveAir<BabyBear, EF, LogUpGadget>,
{
    if !production_gpu_recursion_enabled() {
        CPU_RECURSION_LAYERS.fetch_add(1, Ordering::Relaxed);
        let backend = create_recursion_backend();
        let started = std::time::Instant::now();
        let output = build_and_prove_next_layer_with_expose::<DreggRecursionConfig, A, _, D>(
            input,
            inner_config,
            &backend,
            &ProveNextLayerParams::default(),
            expose,
        )
        .map_err(|e| format!("CPU recursion layer failed: {e:?}"));
        CPU_RECURSION_LEAF_NS.fetch_add(
            started.elapsed().as_nanos().min(u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
        return output;
    }

    let gpu_config = create_gpu_ir2_leaf_wrap_config();
    let gpu = prove_recursion_layer_gpu_with_expose(input, inner_config, &gpu_config, expose)?;
    let cpu_proof = gpu_recursion_proof_to_cpu_with_lookups(&gpu.proof, &gpu.cpu_lookups)?;
    GPU_RECURSION_LEAF_PREP_NS.fetch_add(
        seconds_to_ns_saturating(gpu.prepare_seconds),
        Ordering::Relaxed,
    );
    GPU_RECURSION_LEAF_PROVE_NS.fetch_add(
        seconds_to_ns_saturating(gpu.prove_seconds),
        Ordering::Relaxed,
    );
    GPU_RECURSION_LAYERS.fetch_add(1, Ordering::Relaxed);
    Ok(RecursionOutput(cpu_proof, None))
}

/// [`prove_recursion_layer_auto_with_expose`] without an exposed-claim hook.
pub fn prove_recursion_layer_auto<A>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String>
where
    A: RecursiveAir<BabyBear, EF, LogUpGadget>,
{
    prove_recursion_layer_auto_with_expose(input, inner_config, None)
}

/// Production 2-to-1 aggregation dispatch, the aggregation twin of
/// [`prove_recursion_layer_auto_with_expose`].
pub fn prove_recursion_aggregation_auto_with_expose(
    left: &RecursionInput<'_, DreggRecursionConfig, BatchOnly>,
    right: &RecursionInput<'_, DreggRecursionConfig, BatchOnly>,
    inner_config: &DreggRecursionConfig,
    expose: Option<AggExposeHook<'_, EF>>,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if !production_gpu_recursion_enabled() {
        CPU_RECURSION_LAYERS.fetch_add(1, Ordering::Relaxed);
        let backend = create_recursion_backend();
        let started = std::time::Instant::now();
        let output = p3_recursion::build_and_prove_aggregation_layer_with_expose::<
            DreggRecursionConfig,
            BatchOnly,
            BatchOnly,
            _,
            D,
        >(
            left,
            right,
            inner_config,
            &backend,
            &ProveNextLayerParams::default(),
            None,
            expose,
        )
        .map_err(|e| format!("CPU recursion aggregation failed: {e:?}"));
        CPU_RECURSION_AGG_NS.fetch_add(
            started.elapsed().as_nanos().min(u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
        return output;
    }

    let gpu_config = create_gpu_ir2_leaf_wrap_config();
    let gpu = prove_recursion_aggregation_gpu_with_expose(
        left,
        right,
        inner_config,
        &gpu_config,
        expose,
    )?;
    let cpu_proof = gpu_recursion_proof_to_cpu_with_lookups(&gpu.proof, &gpu.cpu_lookups)?;
    GPU_RECURSION_AGG_PREP_NS.fetch_add(
        seconds_to_ns_saturating(gpu.prepare_seconds),
        Ordering::Relaxed,
    );
    GPU_RECURSION_AGG_PROVE_NS.fetch_add(
        seconds_to_ns_saturating(gpu.prove_seconds),
        Ordering::Relaxed,
    );
    GPU_RECURSION_LAYERS.fetch_add(1, Ordering::Relaxed);
    Ok(RecursionOutput(cpu_proof, None))
}

/// The GPU twin of the recursion backend's non-primitive prover registration —
/// the SAME four tables `verify_recursive_batch_proof_with_config` registers
/// (poseidon2 W16 + the isolated segment-digest W24, recompose, expose_claim).
pub fn gpu_recursion_prover(
    gpu_config: &GpuDreggRecursionConfig,
) -> BatchStarkProver<GpuDreggRecursionConfig> {
    let mut prover = BatchStarkProver::new(gpu_config.clone());
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();
    prover
}

/// A recursion-layer (fold) proof minted under the CPU fold config — the
/// prepare/prove-SPLIT twin of [`GpuRecursionLayerProof`], so the config-
/// dependent PROVE phase (the GPU lever) can be measured apples-to-apples.
pub struct CpuRecursionLayerProof {
    pub proof: BatchStarkProof<DreggRecursionConfig>,
    pub prover_data: Rc<CircuitProverData<DreggRecursionConfig>>,
    pub prepare_seconds: f64,
    pub prove_seconds: f64,
}

/// [`prove_recursion_layer_gpu`] at the CPU `DreggRecursionConfig` — byte-for-
/// byte the same steps (so its proof is byte-identical to both the GPU proof
/// and the recursion library's `build_and_prove_next_layer` output for the same
/// layer), with the prepare/prove split exposed for measurement.
pub fn prove_recursion_layer_cpu<A>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    cpu_config: &DreggRecursionConfig,
) -> Result<CpuRecursionLayerProof, String>
where
    A: RecursiveAir<BabyBear, EF, LogUpGadget>,
{
    let packing = default_shrink_packing();
    let backend = create_recursion_backend();
    let t_prepare = std::time::Instant::now();

    let (circuit, verifier_result) =
        build_next_layer_circuit::<DreggRecursionConfig, A, _, D>(input, inner_config, &backend)
            .map_err(|e| format!("layer verifier circuit build failed: {e:?}"))?;

    let constraint_profile = ProveNextLayerParams::default().constraint_profile;

    let preprocessors: Vec<Box<dyn NpoPreprocessor<BabyBear>>> = vec![
        poseidon2_preprocessor::<BabyBear>(),
        recompose_preprocessor::<BabyBear>(false),
        expose_claim_preprocessor::<BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<DreggRecursionConfig, D>();
        builders.extend(recompose_air_builders::<DreggRecursionConfig, D>(1, false));
        builders.extend(expose_claim_air_builders::<DreggRecursionConfig, D>());
        builders
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<DreggRecursionConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            constraint_profile,
        )
        .map_err(|e| format!("cpu-fold-config table-AIR extraction failed: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let ext_degrees: Vec<usize> = degrees.iter().map(|&d| d + cpu_config.is_zk()).collect();

    let traces = {
        let public_inputs = verifier_result
            .pack_public_inputs(input)
            .map_err(|e| format!("layer public-input packing failed: {e:?}"))?;
        let private_inputs = verifier_result
            .pack_private_inputs(input)
            .map_err(|e| format!("layer private-input packing failed: {e:?}"))?;
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .map_err(|e| format!("layer runner public inputs: {e:?}"))?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|e| format!("layer runner private inputs: {e:?}"))?;
        let op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, A>>::op_ids(&verifier_result);
        backend
            .set_private_data(inner_config, &mut runner, op_ids, input)
            .map_err(|e| format!("layer FRI private data: {e}"))?;
        runner
            .run()
            .map_err(|e| format!("layer verifier witness generation failed: {e:?}"))?
    };

    let prepare_seconds = t_prepare.elapsed().as_secs_f64();
    let t_prove = std::time::Instant::now();

    let prover_data = ProverData::from_airs_and_degrees(cpu_config, &airs, &ext_degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let alu_variant = match constraint_profile {
        ConstraintProfile::Standard => AirVariant::Baseline,
        ConstraintProfile::RecursionOptimized => AirVariant::Optimized,
    };
    let mut prover = BatchStarkProver::new(cpu_config.clone())
        .with_table_packing(packing.clone())
        .with_alu_variant(alu_variant);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|e| format!("cpu-fold-config layer proving failed: {e}"))?;

    Ok(CpuRecursionLayerProof {
        proof,
        prover_data: Rc::new(circuit_prover_data),
        prepare_seconds,
        prove_seconds: t_prove.elapsed().as_secs_f64(),
    })
}

// ============================================================================
// WGSL debug seam (NOT a gate — see `examples/wgsl_debug.rs`)
// ============================================================================

/// The RADV-crash bisection tools, as a narrow debug seam rather than as `#[test]`s.
///
/// These two entry points reproduce a live RADV `create_compute_pipeline` SIGSEGV by dumping the
/// generated hash-engine WGSL and re-compiling an externally-edited copy — the shader can then be
/// bisected without a full Rust recompile. They assert nothing and are not gates; they were
/// previously registered as `#[test]`s, which made them report `ok` on every CI run while proving
/// nothing (and writing `/tmp/hash.wgsl` unconditionally).
///
/// `#[doc(hidden)]` and deliberately narrow: the shader source and the wgpu device stay PRIVATE to
/// the prover. Only these two functions cross the wall, so a debug tool cannot become a second,
/// unaudited way into the GPU backend. Driven by `examples/wgsl_debug.rs`.
#[cfg(not(target_arch = "wasm32"))]
#[doc(hidden)]
pub mod wgsl_debug {
    /// The generated hash-engine WGSL at the deployed workgroup size — the exact source the prover
    /// compiles, so a bisection starts from the real text and not a reconstruction.
    pub fn hash_shader_source_at_deployed_wg() -> String {
        super::hash_shader_source(super::HASH_WG)
    }

    /// Create a compute pipeline for `entry` from `src` on the shared adapter. `Ok` carries the
    /// bind-group-layout debug string (the crash reproduces *inside* this call, as a SIGSEGV, so a
    /// returned `Ok` is itself the signal that the shader survived compilation).
    pub fn compile_probe(src: &str, entry: &str) -> Result<String, String> {
        let shared = super::shared_gpu().ok_or("no GPU adapter available")?;
        let device = &shared.device;
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("wgsl-debug-harness"),
            source: wgpu::ShaderSource::Wgsl(src.into()),
        });
        let pipe = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("wgsl-debug-harness"),
            layout: None,
            module: &module,
            entry_point: Some(entry),
            compilation_options: Default::default(),
            cache: None,
        });
        Ok(format!("{:?}", pipe.get_bind_group_layout(0)))
    }
}

// ============================================================================
// Parity gates
// ============================================================================

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::integers::QuotientMap;
    use p3_field::{Field, PrimeField};
    use p3_matrix::Dimensions;
    use p3_uni_stark::{prove, verify};

    use super::*;
    use crate::dregg_outer_config::create_outer_config;

    /// Deterministic xorshift-based BabyBear matrix (no rand-version friction).
    fn rand_matrix(seed: u64, rows: usize, cols: usize) -> RowMajorMatrix<BabyBear> {
        let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            (s % BB_P as u64) as u32
        };
        let values: Vec<BabyBear> = (0..rows * cols)
            .map(|_| BabyBear::from_int(next()))
            .collect();
        RowMajorMatrix::new(values, cols)
    }

    // The two RADV-bisection DIAGNOSTICS that used to sit here — `dump_hash_wgsl` and
    // `compile_wgsl_from_env` — are NOT tests and are no longer registered as such (P7). They were
    // honestly comment-labelled DIAGNOSTIC, but being `#[test]` they reported `ok` on every CI run
    // while asserting nothing: `dump_hash_wgsl` had ZERO assertions and wrote `/tmp/hash.wgsl`
    // unconditionally; `compile_wgsl_from_env` returned early because `WGSL_FILE` is unset in CI,
    // so it never executed its body. They inflated the count and measured nothing.
    //
    // They now live as real debug tools driven by the `wgsl_debug` example:
    //   cargo run -p dregg-circuit-prove --example wgsl_debug -- dump [PATH]
    //   cargo run -p dregg-circuit-prove --example wgsl_debug -- compile FILE [ENTRY]
    // backed by the doc-hidden `crate::gpu_backend::wgsl_debug` seam below.

    #[test]
    #[ignore = "GPU: asserts a real adapter; run on the GPU lane (`scripts/test-gauntlet.sh gpu`)"]
    fn gpu_dft_parity_vs_radix2() {
        let gpu = GpuDft::default();
        assert!(
            gpu.adapter_name().is_some(),
            "no GPU adapter — this gate must run on the GPU lane"
        );
        let cpu = Radix2DitParallel::<BabyBear>::default();
        let shift = BabyBear::GENERATOR;

        for (i, &(logh, w)) in [(12u32, 5usize), (13, 32), (14, 7)].iter().enumerate() {
            let mat = rand_matrix(i as u64 + 1, 1 << logh, w);
            let got = gpu.dft_batch(mat.clone()).to_row_major_matrix();
            let want = cpu.dft_batch(mat).to_row_major_matrix();
            assert_eq!(got.values, want.values, "dft_batch 2^{logh} x {w}");
        }
        let shift2 = BabyBear::from_int(1234567u32);
        for (i, &(logh, w, ab, s)) in [
            (12u32, 3usize, 1usize, shift),
            (13, 10, 3, shift),
            (14, 33, 2, shift2),
        ]
        .iter()
        .enumerate()
        {
            let mat = rand_matrix(100 + i as u64, 1 << logh, w);
            let got = gpu
                .coset_lde_batch(mat.clone(), ab, s)
                .to_row_major_matrix();
            let want = cpu.coset_lde_batch(mat, ab, s).to_row_major_matrix();
            assert_eq!(
                got.values, want.values,
                "coset_lde_batch 2^{logh} x {w} +{ab}"
            );
        }
    }

    #[test]
    #[ignore = "GPU: asserts a real adapter; run on the GPU lane (`scripts/test-gauntlet.sh gpu`)"]
    fn gpu_mmcs_root_parity_openings_and_reject() {
        let gpu_mmcs = GpuBn254Mmcs::new(0);
        assert!(
            gpu_mmcs.adapter_available(),
            "no GPU adapter — this gate must run on the GPU lane"
        );
        let cpu_mmcs = gpu_mmcs.cpu.clone();

        // A multi-height batch exercising the leaf group (two equal-height
        // tallest matrices) AND two injection levels — the shrink commit's
        // structure in miniature. Sized above MIN_GPU_MMCS_PERMS.
        let mats = vec![
            rand_matrix(1, 1 << 12, 21),
            rand_matrix(2, 1 << 12, 5),
            rand_matrix(3, 1 << 11, 34),
            rand_matrix(4, 1 << 9, 17),
        ];
        let dims: Vec<Dimensions> = mats
            .iter()
            .map(|m| Dimensions {
                width: m.width(),
                height: m.height(),
            })
            .collect();

        let (gpu_commit, gpu_data) = gpu_mmcs.commit(mats.clone());
        assert!(
            matches!(gpu_data, GpuMmcsProverData::Gpu(_)),
            "the GPU path must be taken for this shape"
        );
        let (cpu_commit, cpu_data) = cpu_mmcs.commit(mats);
        assert_eq!(
            gpu_commit.roots(),
            cpu_commit.roots(),
            "GPU Merkle root != CPU MerkleTreeMmcs root"
        );

        // Openings from the GPU tree verify under the UNTOUCHED CPU verifier,
        // and match the CPU tree's openings bit-for-bit.
        for index in [0usize, 1, 137, (1 << 12) - 1, 2048] {
            let gpu_open = gpu_mmcs.open_batch(index, &gpu_data);
            let cpu_open = cpu_mmcs.open_batch(index, &cpu_data);
            assert_eq!(
                gpu_open.opened_values, cpu_open.opened_values,
                "opened values diverge at {index}"
            );
            assert_eq!(
                gpu_open.opening_proof, cpu_open.opening_proof,
                "sibling path diverges at {index}"
            );
            cpu_mmcs
                .verify_batch(
                    &cpu_commit,
                    &dims,
                    index,
                    BatchOpeningRef::new(&gpu_open.opened_values, &gpu_open.opening_proof),
                )
                .expect("GPU-tree opening must verify under the CPU verifier");

            // REJECT polarity: a tampered sibling must not verify.
            let mut bad = gpu_open.opening_proof.clone();
            bad[0][0] += Bn254::ONE;
            assert!(
                gpu_mmcs
                    .verify_batch(
                        &gpu_commit,
                        &dims,
                        index,
                        BatchOpeningRef::new(&gpu_open.opened_values, &bad),
                    )
                    .is_err(),
                "tampered sibling accepted at {index}"
            );
        }
    }

    #[test]
    #[ignore = "GPU: asserts a real adapter; run on the GPU lane (`scripts/test-gauntlet.sh gpu`)"]
    fn gpu_bn254_mmcs_wide_leaf_parity() {
        let gpu = GpuBn254Mmcs::new(0);
        assert!(gpu.adapter_available(), "GPU adapter required");
        let cpu = gpu.cpu.clone();

        // The real outer shrink's main-trace height groups have aggregate
        // widths 300 and 80 (76+4). The earlier miniature gate topped out at
        // width 34 and therefore missed wide-row sponge behavior.
        for (case, mats) in [
            ("w300", vec![rand_matrix(0x300, 1 << 12, 300)]),
            ("w300-chunked", vec![rand_matrix(0x301, 1 << 15, 300)]),
            (
                "w76+w4",
                vec![
                    rand_matrix(0x76, 1 << 12, 76),
                    rand_matrix(0x04, 1 << 12, 4),
                ],
            ),
            (
                "production-geometry-small",
                vec![
                    rand_matrix(0x900, 1 << 6, 4),
                    rand_matrix(0x901, 1 << 6, 4),
                    rand_matrix(0x902, 1 << 12, 76),
                    rand_matrix(0x903, 1 << 11, 300),
                    rand_matrix(0x904, 1 << 12, 4),
                ],
            ),
        ] {
            let (want, _) = cpu.commit(mats.clone());
            let (got, _) = gpu.commit(mats);
            assert_eq!(got.roots(), want.roots(), "wide BN254 leaf parity: {case}");
        }
    }

    /// Resident-LDE entries registered by THIS test thread (the registry is
    /// thread-keyed, so parallel tests don't interfere).
    fn thread_resident_entries() -> usize {
        let tid = std::thread::current().id();
        lde_registry()
            .lock()
            .unwrap()
            .map
            .keys()
            .filter(|k| k.0 == tid)
            .count()
    }

    #[test]
    #[ignore = "GPU: asserts a real adapter; run on the GPU lane (`scripts/test-gauntlet.sh gpu`)"]
    fn gpu_lde_device_residency_hit_fallback_and_root_parity() {
        let gpu_dft = GpuDft::default();
        assert!(
            gpu_dft.adapter_name().is_some(),
            "no GPU adapter — this gate must run on the GPU lane"
        );
        let gpu_mmcs = GpuBn254Mmcs::new(0);
        assert!(gpu_mmcs.adapter_available());
        let cpu_dft = Radix2DitParallel::<BabyBear>::default();
        let cpu_mmcs = gpu_mmcs.cpu.clone();
        let shift = BabyBear::GENERATOR;

        // The PCS commit expression, GPU lane: this mints the LDE on the
        // device AND registers the retained buffer under the returned Vec.
        let mat = rand_matrix(42, 1 << 12, 24);
        let entries0 = thread_resident_entries();
        let lde_gpu = gpu_dft
            .coset_lde_batch(mat.clone(), 1, shift)
            .bit_reverse_rows()
            .to_row_major_matrix();
        assert_eq!(
            thread_resident_entries(),
            entries0 + 1,
            "coset_lde_batch must park a device-resident buffer"
        );

        // Same bytes through a FRESH allocation (must MISS the registry) and
        // the CPU reference lane.
        let lde_copy = RowMajorMatrix::new(lde_gpu.values.clone(), lde_gpu.width());
        let lde_cpu = cpu_dft
            .coset_lde_batch(mat, 1, shift)
            .bit_reverse_rows()
            .to_row_major_matrix();
        assert_eq!(lde_gpu.values, lde_cpu.values, "DFT parity precondition");
        assert!(
            take_resident_lde(&lde_copy).is_none(),
            "a fresh allocation must not bind a resident buffer"
        );

        // A second, shorter matrix (below the GPU-DFT height threshold, so
        // host-borne) exercises the mixed blit + upload arena fill and the
        // injection level.
        let side = rand_matrix(43, 1 << 11, 34);
        let dims: Vec<Dimensions> = [&lde_gpu, &side]
            .iter()
            .map(|m| Dimensions {
                width: m.width(),
                height: m.height(),
            })
            .collect();

        let (hits0, _) = lde_residency_counters();
        let (commit_resident, data_resident) = gpu_mmcs.commit(vec![lde_gpu, side.clone()]);
        let (hits1, _) = lde_residency_counters();
        assert!(
            matches!(data_resident, GpuMmcsProverData::Gpu(_)),
            "the GPU path must be taken for this shape"
        );
        assert!(hits1 >= hits0 + 1, "the resident hand-off must be consumed");
        assert_eq!(
            thread_resident_entries(),
            0,
            "commit must clear this thread's registry"
        );

        // Fallback lane: identical bytes, fresh allocation -> host upload.
        let (commit_copy, _) = gpu_mmcs.commit(vec![lde_copy, side.clone()]);
        assert_eq!(
            commit_resident.roots(),
            commit_copy.roots(),
            "device-resident and host-upload commits diverge"
        );

        // CPU reference: the untouched MerkleTreeMmcs.
        let (commit_cpu, cpu_data) = cpu_mmcs.commit(vec![lde_cpu, side]);
        assert_eq!(
            commit_resident.roots(),
            commit_cpu.roots(),
            "device-resident root != CPU MerkleTreeMmcs root"
        );

        // Openings from the resident-built tree match the CPU tree and
        // verify under the untouched CPU verifier.
        for index in [0usize, 999, (1 << 13) - 1] {
            let gpu_open = gpu_mmcs.open_batch(index, &data_resident);
            let cpu_open = cpu_mmcs.open_batch(index, &cpu_data);
            assert_eq!(gpu_open.opened_values, cpu_open.opened_values);
            assert_eq!(gpu_open.opening_proof, cpu_open.opening_proof);
            cpu_mmcs
                .verify_batch(
                    &commit_cpu,
                    &dims,
                    index,
                    BatchOpeningRef::new(&gpu_open.opened_values, &gpu_open.opening_proof),
                )
                .expect("resident-tree opening must verify under the CPU verifier");
        }
    }

    #[test]
    #[ignore = "GPU: asserts a real adapter; run on the GPU lane (`scripts/test-gauntlet.sh gpu`)"]
    fn gpu_babybear_lde_residency_hit_and_root_parity() {
        let gpu_dft = GpuDft::default();
        assert!(
            gpu_dft.adapter_name().is_some(),
            "no GPU adapter — this gate must run on the GPU lane"
        );
        let gpu_mmcs = GpuBabyBearMmcs::new(0);
        assert!(gpu_mmcs.adapter_available());
        let cpu_dft = Radix2DitParallel::<BabyBear>::default();
        let cpu_mmcs = gpu_mmcs.cpu.clone();
        let shift = BabyBear::GENERATOR;

        let mat = rand_matrix(52, 1 << 12, 24);
        let entries0 = thread_resident_entries();
        let lde_gpu = gpu_dft
            .coset_lde_batch(mat.clone(), 1, shift)
            .bit_reverse_rows()
            .to_row_major_matrix();
        assert_eq!(thread_resident_entries(), entries0 + 1);
        let lde_copy = RowMajorMatrix::new(lde_gpu.values.clone(), lde_gpu.width());
        let lde_cpu = cpu_dft
            .coset_lde_batch(mat, 1, shift)
            .bit_reverse_rows()
            .to_row_major_matrix();
        assert_eq!(lde_gpu.values, lde_cpu.values, "DFT parity precondition");

        let side = rand_matrix(53, 1 << 11, 34);
        let dims: Vec<Dimensions> = [&lde_gpu, &side]
            .iter()
            .map(|m| Dimensions {
                width: m.width(),
                height: m.height(),
            })
            .collect();
        let (hits0, _) = lde_residency_counters();
        let (commit_resident, data_resident) = gpu_mmcs.commit(vec![lde_gpu, side.clone()]);
        let (hits1, _) = lde_residency_counters();
        assert!(matches!(data_resident, GpuBbMmcsProverData::Gpu(_)));
        assert!(
            hits1 >= hits0 + 1,
            "BabyBear resident hand-off was not consumed"
        );
        assert_eq!(thread_resident_entries(), 0);

        let (commit_copy, _) = gpu_mmcs.commit(vec![lde_copy, side.clone()]);
        assert_eq!(
            commit_resident.roots(),
            commit_copy.roots(),
            "BabyBear device-resident and host-upload roots diverge"
        );
        let (commit_cpu, cpu_data) = cpu_mmcs.commit(vec![lde_cpu, side]);
        assert_eq!(
            commit_resident.roots(),
            commit_cpu.roots(),
            "BabyBear device-resident root != untouched CPU MMCS root"
        );
        for index in [0usize, 999, (1 << 13) - 1] {
            let gpu_open = gpu_mmcs.open_batch(index, &data_resident);
            let cpu_open = cpu_mmcs.open_batch(index, &cpu_data);
            assert_eq!(gpu_open.opened_values, cpu_open.opened_values);
            assert_eq!(gpu_open.opening_proof, cpu_open.opening_proof);
            cpu_mmcs
                .verify_batch(
                    &commit_cpu,
                    &dims,
                    index,
                    BatchOpeningRef::new(&gpu_open.opened_values, &gpu_open.opening_proof),
                )
                .expect("BabyBear resident-tree opening must verify under CPU MMCS");
        }
    }

    // ------------------------------------------------------------------
    // Synthetic STARK: GPU config proves; the proof is BYTE-IDENTICAL to
    // the CPU config's and round-trips through the CPU verifier.
    // ------------------------------------------------------------------

    struct FibAir;

    impl<F> BaseAir<F> for FibAir {
        fn width(&self) -> usize {
            2
        }
        fn num_public_values(&self) -> usize {
            3
        }
        fn max_constraint_degree(&self) -> Option<usize> {
            Some(2)
        }
    }

    impl<AB: AirBuilder> Air<AB> for FibAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let pis = builder.public_values();
            let (a, b, x) = (pis[0], pis[1], pis[2]);
            let local = main.current_slice();
            let next = main.next_slice();
            let mut when_first_row = builder.when_first_row();
            when_first_row.assert_eq(local[0], a);
            when_first_row.assert_eq(local[1], b);
            let mut when_transition = builder.when_transition();
            when_transition.assert_eq(local[1], next[0]);
            when_transition.assert_eq(local[0] + local[1], next[1]);
            builder.when_last_row().assert_eq(local[1], x);
        }
    }

    fn fib_trace(n: usize) -> (RowMajorMatrix<BabyBear>, Vec<BabyBear>) {
        let mut values = Vec::with_capacity(2 * n);
        let (mut a, mut b) = (BabyBear::ZERO, BabyBear::ONE);
        for _ in 0..n {
            values.push(a);
            values.push(b);
            let next = a + b;
            a = b;
            b = next;
        }
        let pis = vec![BabyBear::ZERO, BabyBear::ONE, values[2 * n - 1]];
        (RowMajorMatrix::new(values, 2), pis)
    }

    #[test]
    fn gpu_outer_config_synthetic_stark_byte_identical_to_cpu() {
        let gpu_config = create_gpu_outer_config();
        let cpu_config = create_outer_config();
        let air = FibAir;
        let (trace, pis) = fib_trace(1 << 12);

        let t0 = Instant::now();
        let gpu_proof = prove(&gpu_config, &air, trace.clone(), &pis);
        let gpu_time = t0.elapsed();
        let t1 = Instant::now();
        let cpu_proof = prove(&cpu_config, &air, trace, &pis);
        let cpu_time = t1.elapsed();

        verify(&gpu_config, &air, &gpu_proof, &pis)
            .expect("GPU-config proof verifies under the GPU config");

        // The decisive parity: both provers are deterministic and the GPU
        // path is bit-exact, so the two proofs must serialize identically.
        let gpu_bytes = postcard::to_allocvec(&gpu_proof).expect("gpu proof serializes");
        let cpu_bytes = postcard::to_allocvec(&cpu_proof).expect("cpu proof serializes");
        assert_eq!(
            gpu_bytes, cpu_bytes,
            "GPU-config proof is not byte-identical to the CPU-config proof"
        );

        // Round-trip: the GPU proof deserializes as a CPU-config proof and
        // verifies under the untouched CPU config.
        let as_cpu: p3_uni_stark::Proof<DreggOuterConfig> =
            postcard::from_bytes(&gpu_bytes).expect("gpu proof re-types to the CPU config");
        verify(&cpu_config, &air, &as_cpu, &pis)
            .expect("GPU-minted proof verifies under the CPU config");

        // REJECT polarity: wrong public values must not verify.
        let bad_pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_int(99u32)];
        assert!(verify(&gpu_config, &air, &gpu_proof, &bad_pis).is_err());

        eprintln!(
            "synthetic fib 2^12 outer prove: GPU {:.2?} | CPU {:.2?} (small shape — the real measurement is the ignored e2e shrink test)",
            gpu_time, cpu_time
        );
        let _ = gpu_proof.commitments.trace.roots()[0][0].as_canonical_biguint();
    }
}

// ============================================================================
// WASM32 / WebGPU — the on-device async prover substrate
//
// The "private AND fast" endgame for the client-side ZK-leaderboard: the proof
// is minted ON THE DEVICE, in the browser, over WebGPU — moves never leave the
// device (privacy) and the Amdahl-dominant Merkle build runs on the GPU (speed).
//
// This section is the ASYNC substrate the browser path needs, and it is the
// STRUCTURAL fix for the two wasm blockers the sync backend above cannot cross:
//
//   * adapter/device init used `pollster::block_on` — forbidden on the browser
//     main thread. `init_gpu()` below `.await`s the adapter/device requests
//     instead (no block_on), and is callable from a Web Worker (WebGPU works in
//     workers / OffscreenCanvas), so init never blocks the main thread.
//   * buffer readback spin-waited on `device.poll(Maintain::Wait)`, which cannot
//     complete on the browser event loop. `map_read_u32s()` below `.await`s the
//     `map_async` completion via a oneshot channel on wasm — no poll spin.
//
// It is compiled on BOTH targets on purpose: on native the same async fns run
// (driven by `pollster::block_on` in the tests) so the on-device path is
// exercised + BIT-IDENTITY-GATED against the CPU floor on a real GPU; on wasm
// the readback/init arms switch to the browser-async form. Only the readback
// mechanism and the device-request driver differ per target — the kernels, the
// descriptor protocol, and the field conversion are the SAME bit-exact ones the
// native `GpuBn254Mmcs` uses.
//
// HONEST SCOPE (scheduled sharpenings, not gaps in what is here):
//   * REAL now: async init + async readback + a worker-runnable async BN254
//     Poseidon2 Merkle commit that is bit-identical to `OuterValMmcs` for a
//     single matrix (the native gate below proves it), and COMPILES for wasm32.
//   * NEXT: the live in-browser run needs a WebGPU device (a browser / headless-
//     WebGPU harness) — this build + async structure is the substrate it runs
//     on; multi-matrix injection + the full opening path on device are the DFT-
//     seam-style extensions; wiring it under the wasm ZK-leaderboard binding
//     (the sync STARK prover driven from the worker) lands with Lane-D's fold.
// ============================================================================

/// A WebGPU device acquired ASYNCHRONOUSLY (no `pollster::block_on`), suitable
/// for the browser main thread OR a Web Worker.
pub struct OnDeviceGpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter_name: String,
    #[allow(dead_code)]
    max_buf_u32s: usize,
}

impl OnDeviceGpu {
    /// The acquired adapter's name (`"<name> (<backend>)"`).
    pub fn adapter_name(&self) -> &str {
        &self.adapter_name
    }
}

/// THE wasm init entry point: acquire a WebGPU device with NO
/// `pollster::block_on` — the adapter and device requests are `.await`ed, so
/// this never blocks the browser main thread and can run on a Web Worker.
///
/// On wasm each call creates the WebGPU instance/adapter/device asynchronously
/// (the worker owns it). On NATIVE it reuses the process-wide `SHARED_GPU`
/// device instead of standing up a second `wgpu::Instance` in the same process
/// — that keeps a single device (the drop-order discipline the `SharedGpu`
/// comment documents against the wgpu 24.0.5 teardown crash) and still
/// exercises the async surface (async fn + async readback) on real GPUs, so the
/// wasm-shaped engine is bit-identity-gated by the native test below.
#[cfg(target_arch = "wasm32")]
pub async fn init_gpu() -> Result<OnDeviceGpu, String> {
    let instance = wgpu::Instance::default();
    let adapter = instance
        .request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        })
        .await
        .ok_or_else(|| "init_gpu: no WebGPU adapter available".to_string())?;
    let info = adapter.get_info();
    let lims = adapter.limits();
    let (device, queue) = adapter
        .request_device(
            &wgpu::DeviceDescriptor {
                label: None,
                required_features: wgpu::Features::empty(),
                required_limits: lims.clone(),
                memory_hints: Default::default(),
            },
            None,
        )
        .await
        .map_err(|e| format!("init_gpu: request_device failed: {e}"))?;
    let max_buf_u32s = (lims
        .max_buffer_size
        .min(lims.max_storage_buffer_binding_size as u64)
        .min(1 << 31) as usize)
        / 4;
    Ok(OnDeviceGpu {
        device,
        queue,
        adapter_name: format!("{} ({:?})", info.name, info.backend),
        max_buf_u32s,
    })
}

/// Native `init_gpu`: reuse the process-wide device (see the wasm variant's doc
/// for why we do NOT create a second instance here). Still `async` so the
/// on-device engine is exercised on native GPUs exactly as it will run on wasm.
#[cfg(not(target_arch = "wasm32"))]
pub async fn init_gpu() -> Result<OnDeviceGpu, String> {
    let shared = shared_gpu().ok_or_else(|| "init_gpu: no GPU adapter available".to_string())?;
    Ok(OnDeviceGpu {
        device: shared.device.clone(),
        queue: shared.queue.clone(),
        adapter_name: shared.adapter_name.clone(),
        max_buf_u32s: shared.max_buf_u32s,
    })
}

/// Await a buffer readback. ASYNC readback: on wasm the `map_async` completion
/// is `.await`ed through a oneshot channel (NO `device.poll(Maintain::Wait)`
/// spin — that never completes on the browser event loop); on native the same
/// async fn blocks inside via `poll(Wait)` (fine off any render thread), so the
/// wasm code path is exercised + gated on native GPUs.
async fn map_read_u32s(device: &wgpu::Device, buffer: &wgpu::Buffer, len_bytes: u64) -> Vec<u32> {
    let slice = buffer.slice(..len_bytes);
    #[cfg(not(target_arch = "wasm32"))]
    {
        slice.map_async(wgpu::MapMode::Read, |_| {});
        device.poll(wgpu::Maintain::Wait);
    }
    #[cfg(target_arch = "wasm32")]
    {
        let (tx, rx) = futures_channel::oneshot::channel();
        slice.map_async(wgpu::MapMode::Read, move |res| {
            let _ = tx.send(res);
        });
        // The browser drives GPU completion on the event loop; awaiting the
        // channel yields to it — no `poll(Wait)` spin (which would deadlock).
        let _ = device;
        rx.await
            .expect("map_async sender dropped")
            .expect("map_async failed");
    }
    let data = slice.get_mapped_range();
    let out = bytemuck::cast_slice::<u8, u32>(&data).to_vec();
    drop(data);
    buffer.unmap();
    out
}

/// A read-only / read-write storage-buffer bind-group-layout entry.
fn od_storage_entry(binding: u32, read_only: bool) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Storage { read_only },
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

impl OnDeviceGpu {
    fn od_storage_buffer(&self, label: &str, u32s: usize, dst: bool) -> wgpu::Buffer {
        let mut usage = wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC;
        if dst {
            usage |= wgpu::BufferUsages::COPY_DST;
        }
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: (u32s.max(4) * 4) as u64,
            usage,
            mapped_at_creation: false,
        })
    }

    /// GPU-build the BN254 Poseidon2 Merkle ROOT of ONE power-of-two-height
    /// matrix, entirely on the WebGPU device, reading back only the 8-word root
    /// through the async path. Uses the SAME kernels (`hash_shader_source`), the
    /// SAME descriptor protocol, and the SAME field conversion as the native
    /// `GpuBn254Mmcs`, so the root is bit-identical to
    /// `OuterValMmcs::commit(vec![mat]).0`'s cap root (asserted in
    /// `ondevice_tests` below, on the native GPU). This is the on-device
    /// commitment primitive the browser leaderboard proof commits its state
    /// with; multi-matrix injection + the opening path are next-pass extensions.
    pub async fn bn254_merkle_root(&self, mat: &RowMajorMatrix<BabyBear>) -> Result<Bn254, String> {
        let h = mat.height();
        let w = mat.width();
        if h == 0 || w == 0 || !h.is_power_of_two() {
            return Err("bn254_merkle_root: need a non-empty power-of-two-height matrix".into());
        }

        // Pipelines — identical 3-binding layout + WGSL as `HashCtx`.
        let bgl = self
            .device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("od_hash_bgl"),
                entries: &[
                    od_storage_entry(0, true),
                    od_storage_entry(1, true),
                    od_storage_entry(2, false),
                ],
            });
        let layout = self
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: None,
                bind_group_layouts: &[&bgl],
                push_constant_ranges: &[],
            });
        let module = self
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("od_bn254_poseidon2_tree"),
                source: wgpu::ShaderSource::Wgsl(hash_shader_source(HASH_WG).into()),
            });
        let mk_pipe = |entry: &str| {
            self.device
                .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                    label: Some(entry),
                    layout: Some(&layout),
                    module: &module,
                    entry_point: Some(entry),
                    compilation_options: Default::default(),
                    cache: None,
                })
        };
        let leaf_pipe = mk_pipe("leaf_main");
        let compress_pipe = mk_pipe("compress_main");

        // Arena (Montgomery u32s, row-major — exactly the native staging bytes),
        // descriptor, and the two ping-pong digest buffers.
        let arena = self.od_storage_buffer("od_leaf_arena", h * w, true);
        self.queue
            .write_buffer(&arena, 0, bytemuck::cast_slice(bb_as_u32s(&mat.values)));
        let desc_buf = self.od_storage_buffer("od_desc", 6, true);
        let dig_a = self.od_storage_buffer("od_dig_a", h * 8, true);
        let dig_b = self.od_storage_buffer("od_dig_b", h * 8, true);

        let bind = |src: &wgpu::Buffer, out: &wgpu::Buffer| {
            self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: None,
                layout: &bgl,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: src.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: desc_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: out.as_entire_binding(),
                    },
                ],
            })
        };

        // Leaf sponge over all rows, watchdog-chunked like `HashCtx::dispatch_leaf`
        // (chunking is transparent to the result: each thread writes its absolute
        // row). desc = [n_mats=1, base, rows, 0, off=0, w].
        let perms_per_row = w.div_ceil(16).max(1);
        let rows_per_chunk = (HASH_MAX_PERMS_PER_DISPATCH / perms_per_row.max(1))
            .max(HASH_WG as usize)
            .next_multiple_of(HASH_WG as usize);
        let leaf_bg = bind(&arena, &dig_a);
        let mut base = 0usize;
        while base < h {
            let rows = rows_per_chunk.min(h - base);
            let desc = [1u32, base as u32, rows as u32, 0u32, 0u32, w as u32];
            self.queue
                .write_buffer(&desc_buf, 0, bytemuck::cast_slice(&desc));
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(&leaf_pipe);
                pass.set_bind_group(0, &leaf_bg, &[]);
                pass.dispatch_workgroups((rows as u32).div_ceil(HASH_WG), 1, 1);
            }
            self.queue.submit([enc.finish()]);
            base += rows;
        }

        // Compress up to the root (single matrix ⇒ no injection). desc = [n_out, 0, 0, 0].
        let mut cur_len = h;
        let mut cur_is_a = true;
        while cur_len > 1 {
            let next_len = cur_len / 2;
            let (src, dst) = if cur_is_a {
                (&dig_a, &dig_b)
            } else {
                (&dig_b, &dig_a)
            };
            let bg = bind(src, dst);
            let desc = [next_len as u32, 0u32, 0u32, 0u32];
            self.queue
                .write_buffer(&desc_buf, 0, bytemuck::cast_slice(&desc));
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(&compress_pipe);
                pass.set_bind_group(0, &bg, &[]);
                pass.dispatch_workgroups((next_len as u32).div_ceil(HASH_WG), 1, 1);
            }
            self.queue.submit([enc.finish()]);
            cur_len = next_len;
            cur_is_a = !cur_is_a;
        }

        // The root sits in whichever buffer received the last (len-1) write.
        let root_buf = if cur_is_a { &dig_a } else { &dig_b };
        let read = self.od_storage_buffer_read("od_root_read", 8);
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(root_buf, 0, &read, 0, 32);
        self.queue.submit([enc.finish()]);
        let words = map_read_u32s(&self.device, &read, 32).await;
        let limbs: [u32; 8] = words[..8].try_into().expect("8-word root");
        Ok(bn254_from_canonical_limbs(&limbs))
    }

    /// A MAP_READ-usable readback buffer.
    fn od_storage_buffer_read(&self, label: &str, u32s: usize) -> wgpu::Buffer {
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: (u32s.max(1) * 4) as u64,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        })
    }
}

/// The WORKER-RUNNABLE on-device proving core (substrate). A Web Worker driver
/// (wasm-bindgen glue + WebGPU-in-workers) calls this on the worker thread: it
/// `.await`s `init_gpu()` (no main-thread block) and GPU-builds the BN254
/// commitment of the leaderboard state on device — the moves never leave the
/// device, and the Amdahl-dominant hashing runs on the GPU. Returns the root.
/// Wiring the full ZK-leaderboard STARK proof (the sync prover driven from the
/// worker over this substrate) lands with Lane-D's fold + the wasm binding.
pub async fn prove_leaderboard_commit_on_device(
    mat: &RowMajorMatrix<BabyBear>,
) -> Result<Bn254, String> {
    let gpu = init_gpu().await?;
    gpu.bn254_merkle_root(mat).await
}

/// Native gate for the on-device async path: drive the async engine with
/// `pollster::block_on` on the real GPU and assert its BN254 Merkle root is
/// bit-identical to the CPU `OuterValMmcs` floor. This proves the wasm-shaped
/// async engine (async init + async readback + on-device commit) is correct;
/// only the readback mechanism differs on wasm.
#[cfg(all(test, not(target_arch = "wasm32")))]
mod ondevice_tests {
    use p3_commit::Mmcs;
    use p3_field::integers::QuotientMap;
    use p3_matrix::dense::RowMajorMatrix;

    use super::{BB_P, BabyBear, GpuBn254Mmcs, init_gpu};

    fn rand_matrix(seed: u64, rows: usize, cols: usize) -> RowMajorMatrix<BabyBear> {
        let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            (s % BB_P as u64) as u32
        };
        let values: Vec<BabyBear> = (0..rows * cols)
            .map(|_| BabyBear::from_int(next()))
            .collect();
        RowMajorMatrix::new(values, cols)
    }

    /// FAIL-CLOSED + explicitly `#[ignore]`d, the one GPU law.
    ///
    /// This gate used to open `Err(e) => { eprintln!("no WebGPU device; on-device gate skipped");
    /// return; }` — the SAME fail-open shape as the two in `tests/gpu_babybear_merkle_e2e.rs`, but
    /// living in the file that is otherwise the reference for doing this right. A test named
    /// `..._matches_cpu` reported **`ok`** on every GPU-less runner having matched nothing against
    /// nothing.
    #[test]
    #[ignore = "GPU: needs a real WebGPU device; run on the GPU lane (`scripts/test-gauntlet.sh gpu`)"]
    fn on_device_async_bn254_root_matches_cpu() {
        let gpu = pollster::block_on(init_gpu()).unwrap_or_else(|e| {
            panic!(
                "no WebGPU device ({e}) — this on-device parity gate must RUN on the GPU lane, \
                 never silently skip. It is `#[ignore]`d so a GPU-less runner skips it EXPLICITLY; \
                 reaching this means the lane opted in with `--ignored` on a host with no device."
            )
        });
        eprintln!("on-device async engine adapter: {}", gpu.adapter_name());

        // The CPU floor is the untouched `OuterValMmcs` inside `GpuBn254Mmcs`.
        let cpu_mmcs = GpuBn254Mmcs::new(0).cpu.clone();
        for &(log_h, w) in &[(12usize, 8usize), (13, 17), (14, 3)] {
            let mat = rand_matrix(log_h as u64 * 131 + w as u64, 1 << log_h, w);
            let got = pollster::block_on(gpu.bn254_merkle_root(&mat)).expect("on-device root");
            let (cpu_commit, _) = cpu_mmcs.commit(vec![mat]);
            let want = cpu_commit.roots()[0][0];
            assert_eq!(
                got, want,
                "on-device async BN254 root != CPU floor at 2^{log_h} x {w}"
            );
        }
    }
}
