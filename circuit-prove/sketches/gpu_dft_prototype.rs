//! ⚠ PROTOTYPE SKETCH — NOT COMPILED, NOT WIRED, NOT A WORKING PROVER. ⚠
//!
//! This file lives outside any cargo target (`circuit-prove/sketches/` is not
//! `src/`/`tests/`/`examples/`); nothing builds it. It illustrates the two
//! Plonky3 trait seams a GPU backend swaps, per
//! docs/deos/GPU-PROVER-PROTOTYPE.md — the wgpu/WGSL cross-platform plan
//! (Metal on Apple Silicon, Vulkan on AMD/NVIDIA), BabyBear-first.
//!
//! What IS validated today: the WGSL BabyBear Montgomery arithmetic this
//! sketch's kernels build on is measured + p3-bit-exact on Apple M2 Max/Metal
//! (see ../sketches/wgpu-babybear-probe). Everything below that layer is
//! design shape only.

// ============================================================================
// SEAM 1: TwoAdicSubgroupDft — the LDE/NTT swap (FIRST loop to GPU)
// ============================================================================
//
// Both provers commit via TwoAdicFriPcs, whose `commit` calls
// `TwoAdicSubgroupDft::coset_lde_batch` (pinned rev 82cfad7,
// fri/src/two_adic_pcs.rs:317,344). Today both configs use
// `Radix2DitParallel<BabyBear>`:
//   - outer: circuit-prove/src/dregg_outer_config.rs:156
//   - inner: circuit-prove/src/plonky3_recursion_impl.rs:75
// The swap is ONE type alias + this impl. CPU fallback stays available by
// construction (keep the enum's Cpu arm).

use p3_baby_bear::BabyBear;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_matrix::bitrev::BitReversedMatrixView;
use p3_matrix::dense::RowMajorMatrix;

/// GPU-or-CPU DFT over BabyBear. `Default` (required by the trait bound,
/// dft/src/traits.rs:27) must be cheap and infallible, so device acquisition
/// is lazy: first use tries a wgpu adapter (Metal on macOS, Vulkan on
/// AMD/NVIDIA Linux) and falls back to `Radix2DitParallel` forever if absent.
#[derive(Clone, Default)]
pub struct GpuDft {
    inner: std::sync::OnceLock<GpuDftBackend>,
}

enum GpuDftBackend {
    /// wgpu device + precompiled NTT pipelines + cached twiddle buffers
    /// per log_n (twiddles uploaded once per size, like Radix2DitParallel's
    /// per-size twiddle cache).
    Gpu {
        device: wgpu::Device,
        queue: wgpu::Queue,
        ntt_pipeline: wgpu::ComputePipeline, // radix-2/4 DIT stage kernel
        coset_shift_pipeline: wgpu::ComputePipeline, // x_i *= shift^i (pre-scale)
        // twiddle cache: log_n -> buffer of w^0..w^{n/2-1} (Montgomery form)
        twiddles: std::sync::Mutex<std::collections::HashMap<usize, wgpu::Buffer>>,
    },
    Cpu(Radix2DitParallel<BabyBear>),
}

impl TwoAdicSubgroupDft<BabyBear> for GpuDft {
    // p3 lets Evaluations be a bit-reversed view — the natural output order
    // of a DIT NTT, so the kernel never pays a reorder pass (the same trick
    // Radix2DitParallel plays).
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<BabyBear>>;

    fn dft_batch(&self, mat: RowMajorMatrix<BabyBear>) -> Self::Evaluations {
        match self.backend() {
            GpuDftBackend::Cpu(cpu) => cpu.dft_batch(mat).to_bit_reversed(), // shape-only sketch
            GpuDftBackend::Gpu { .. } => {
                // 1. upload `mat.values` (u32 monty repr — BabyBear is
                //    repr(transparent) over MontyField31, zero-convert)
                // 2. dispatch log_n DIT stages; each stage = one compute pass,
                //    columns batched along workgroup y (a column IS a poly:
                //    dft/src/traits.rs:52-61)
                // 3. read back / or KEEP RESIDENT for the Merkle kernel (§seam 2)
                //    — on Apple unified memory readback is free; on discrete
                //    boards residency is the point
                unimplemented!("PROTOTYPE: wgsl_ntt dispatch")
            }
        }
    }

    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<BabyBear>,
        added_bits: usize, // = fri.log_blowup (6 today for BOTH configs)
        shift: BabyBear,
    ) -> Self::Evaluations {
        // Standard NTT-LDE: inverse-NTT (trace domain) → zero-extend 2^added_bits
        // → coset-scale by shift^i → forward-NTT. All four steps are the same
        // two kernels; the zero-extend allocates GPU-side.
        // PARITY GATE (must pass before any wiring): differential vs
        // Radix2DitParallel::coset_lde_batch on random matrices, all sizes
        // 2^1..2^21 × widths {1, 452}, both configs' shapes.
        unimplemented!("PROTOTYPE")
    }
}

impl GpuDft {
    fn backend(&self) -> &GpuDftBackend {
        self.inner.get_or_init(|| {
            // pollster::block_on(wgpu::Instance::default().request_adapter(..))
            //   .map(build_pipelines)
            //   .unwrap_or(GpuDftBackend::Cpu(Radix2DitParallel::default()))
            unimplemented!("PROTOTYPE")
        })
    }
}

// The wiring delta in dregg_outer_config.rs — the WHOLE prover-side change
// for seam 1 (its inner twin in plonky3_recursion_impl.rs is identical):
//
//     -type OuterDft = Radix2DitParallel<BabyBear>;
//     +type OuterDft = GpuDft;
//      pub type OuterPcs = TwoAdicFriPcs<BabyBear, OuterDft, OuterValMmcs, OuterChallengeMmcs>;
//
// (and `OuterPcs::new(OuterDft::default(), ..)` at dregg_outer_config.rs:378
// already takes it by Default — zero call-site changes.)

// ============================================================================
// SEAM 2: the MMCS — batched Poseidon2 Merkle build
// ============================================================================
//
// CryptographicHasher (symmetric/src/hasher.rs:6) is per-leaf; there is no
// batch seam inside MerkleTreeMmcs. So GPU hashing = an alternative impl of
// the `Mmcs` trait whose commit() builds the tree with batched permutation
// kernels, BIT-EXACTLY reproducing p3's layout:
//
//   inner (BabyBear tree): leaf = PaddingFreeSponge<Poseidon2BabyBear<16>,16,8,8>
//     (overwrite-mode absorb, digest = first 8 lanes); node compress =
//     TruncatedPermutation over 2×[BabyBear;8].
//   outer (BN254 tree, LATER per the BabyBear-first plan): leaf =
//     MultiField32PaddingFreeSponge (shifted radix-2^31 packing,
//     dregg_outer_config.rs:46-55) — the packing is a cheap linear pass that
//     can stay CPU-side while only the Poseidon2Bn254 permutations batch on
//     GPU; compress = permute([l,r,0]).state[0] (gold-KAT-pinned both sides,
//     dregg_outer_config.rs:425-450).
//
// Kernel shape (per tree level, all leaves in one dispatch):
//   - leaf level: for row-width W, ceil(W/RATE_ELEMS) sequential permutations
//     per leaf, leaves parallel across invocations; state stays in registers.
//   - node levels: one permutation per node, level-parallel; log2(n) passes.
// ACCEPT GATE per platform: commit() root == CPU MerkleTreeMmcs root on the
// same matrices (plus the existing BN254 gold KAT for the outer permutation).
//
// pub struct GpuMerkleMmcs { /* device handles + perm pipeline */ }
// impl Mmcs<BabyBear> for GpuMerkleMmcs { /* commit = kernel tree build;
//     open/verify unchanged CPU (query phase is tiny + sequential) */ }

// ============================================================================
// WGSL kernel core (the measured part + the NTT butterfly it extends into)
// ============================================================================
//
// The Montgomery core below is MEASURED and p3-bit-exact on Apple M2 Max/Metal
// (105.8 Gmul/s; parity on 4.19M lanes vs pinned p3 rev 82cfad7) — see
// sketches/wgpu-babybear-probe. The butterfly is the sketch extension.
pub const WGSL_BABYBEAR: &str = r#"
const P: u32 = 0x78000001u;   // baby_bear.rs:18
const MU: u32 = 0x88000001u;  // baby_bear.rs:21 (P^{-1} mod 2^32)

fn mul64(a: u32, b: u32) -> vec2<u32> { /* 16-bit split; WGSL has no u64 —
    measured version in wgpu-babybear-probe/src/main.rs */ return vec2(0u); }

fn mmul(a: u32, b: u32) -> u32 {        // p3 monty-31 reduce (utils.rs:105)
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r: u32 = ab.y - tp.y;
    if (ab.y < tp.y) { r += P; }
    return r;
}

fn madd(a: u32, b: u32) -> u32 { let s = a + b; return select(s, s - P, s >= P); }
fn msub(a: u32, b: u32) -> u32 { return select(a - b, a + P - b, a < b); }

// One radix-2 DIT stage; dispatched log_n times per column batch.
// buf holds Montgomery-form values; tw holds the stage's twiddles.
@group(0) @binding(0) var<storage, read_write> buf: array<u32>;
@group(0) @binding(1) var<storage, read> tw: array<u32>;
@compute @workgroup_size(256)
fn ntt_stage(@builtin(global_invocation_id) gid: vec3<u32>) {
    // PROTOTYPE: index math for (pair, twiddle) at stage `s` elided.
    let i = 0u; let j = 1u; let w = tw[0];
    let u = buf[i];
    let v = mmul(buf[j], w);
    buf[i] = madd(u, v);
    buf[j] = msub(u, v);
}
"#;
