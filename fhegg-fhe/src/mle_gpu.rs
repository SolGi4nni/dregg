//! The sumcheck prover's MLE fold, on the SAME device the BFV fold runs on.
//!
//! # Why this lives next to `gpu_arena` and not in a prover crate
//!
//! The fusion thesis under test: *a vFHE prover's multilinear evaluation tables ARE the FHE
//! evaluation's intermediates, so a fused pipeline pays the memory traffic once instead of twice.*
//! That claim is only testable if the FHE kernel's output buffer and the prover's table buffer can
//! be the same allocation. Two `wgpu::Device`s cannot share a buffer, so the thesis is not merely
//! unimplemented when each module owns its own device — it is unreachable. [`Arena`] is therefore
//! multi-pipeline (see its docblock), and everything here binds buffers the BFV fold produced.
//!
//! # What a round is
//!
//! `f'(x) = f(x,0) + r * (f(x,1) - f(x,0))`, with the folded variable as the HIGH index bit:
//! `f(x,0) = table[i]`, `f(x,1) = table[i + half]`. [`fold_mle_table`] is the canonical CPU
//! reference and [`Arena::mle_fold_rounds`] is the GPU one; `tests/wgpu_mle_fold.rs` checks them
//! against each other and against Plonky3's own multilinear fold at the workspace's pinned rev.
//!
//! # ⚠ What this is NOT
//!
//! * The fold here is over the BASE field. A real sumcheck folds over the degree-4 extension after
//!   round 1 (`EF4`), which is ~9 base multiplications per lane instead of 1 — so the *arithmetic*
//!   side of every number this module produces is an underestimate of a real prover's, while the
//!   *traffic* side (4 bytes per lane per round, halving) is 4x an underestimate too. The fusion
//!   question is a traffic question and both scale together; the ratio is what is being measured.
//! * No round polynomial is evaluated and nothing is committed. This is the fold, not a prover.
//! * The bridge encoding (`shaders/bfv_to_babybear.wgsl`) is an injective 2-limb split, not a
//!   relation-specific decomposition. See that shader's header.

use std::sync::Mutex;

use crate::gpu_arena::{Arena, ResidentHandle};

/// BabyBear. Same field the deployed STARK prover uses.
pub const BABYBEAR_P: u32 = 2_013_265_921;

/// Montgomery radix for the WGSL kernel: R = 2^32.
const MONTY_R: u64 = 1u64 << 32;

/// `-P^{-1} mod 2^32`, the constant baked into `mle_fold.wgsl`. Asserted equal here so the two
/// cannot drift apart silently.
const MONTY_MU: u32 = 2_013_265_919;

/// Lifts a canonical challenge into the Montgomery form the kernel expects (`r * R mod P`).
///
/// The TABLE stays canonical — only the challenge is converted — so no pass over the table's
/// memory is ever spent on representation.
#[must_use]
pub fn to_montgomery(r: u32) -> u32 {
    u32::try_from((u64::from(r) * MONTY_R) % u64::from(BABYBEAR_P))
        .expect("a residue mod BabyBear fits u32")
}

/// One MLE fold round, canonical BabyBear, on the CPU. The reference the GPU kernel is checked
/// against.
///
/// # Panics
///
/// - `table.len()` must be even and nonzero.
#[must_use]
pub fn fold_mle_table(table: &[u32], r: u32) -> Vec<u32> {
    assert!(
        !table.is_empty() && table.len() % 2 == 0,
        "an MLE evaluation table folds only at even, nonzero length (got {})",
        table.len()
    );
    let p = u64::from(BABYBEAR_P);
    let half = table.len() / 2;
    let r = u64::from(r);
    (0..half)
        .map(|i| {
            let f0 = u64::from(table[i]);
            let f1 = u64::from(table[i + half]);
            let d = (f1 + p - f0) % p;
            u32::try_from((f0 + r * d % p) % p).expect("a residue mod BabyBear fits u32")
        })
        .collect()
}

/// Folds every variable away, returning the single remaining evaluation. Reference for a whole
/// sumcheck's worth of folding.
///
/// # Panics
///
/// - `table.len()` must be a nonzero power of two, and `challenges` must have `log2(len)` entries.
#[must_use]
pub fn fold_mle_all(table: &[u32], challenges: &[u32]) -> u32 {
    assert!(
        table.len().is_power_of_two(),
        "MLE table length must be a power of two (got {})",
        table.len()
    );
    assert_eq!(
        challenges.len(),
        table.len().trailing_zeros() as usize,
        "one challenge per variable"
    );
    let mut current = table.to_vec();
    for &r in challenges {
        current = fold_mle_table(&current, r);
    }
    debug_assert_eq!(current.len(), 1);
    current[0]
}

/// An on-device BabyBear evaluation table — an index into the arena's table pool. Never downloaded
/// until [`Arena::download_table`].
#[derive(Clone, Debug)]
pub struct ResidentTable {
    id: usize,
    /// Live element count. Each completed fold round halves it; the buffer allocation does not
    /// change, because the fold is in place.
    len: usize,
    /// Allocated capacity in elements, so a partially folded table can still be re-bound.
    capacity: usize,
}

impl ResidentTable {
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

/// `MleMeta` in `mle_fold.wgsl`.
#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct MleMeta {
    half: u32,
    r_mont: u32,
    _pad0: u32,
    _pad1: u32,
}

/// `BridgeMeta` in `bfv_to_babybear.wgsl`.
#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct BridgeMeta {
    n_lanes: u32,
    table_len: u32,
    _pad0: u32,
    _pad1: u32,
}

const WORKGROUP: u32 = 256;

/// Elements a BabyBear table needs to hold the injective 2-limb encoding of `lanes` RNS residues,
/// rounded up to the power of two an MLE table requires.
///
/// # Panics
///
/// - `lanes` must be nonzero and the padded length must fit `u32` (the shader's index type).
#[must_use]
pub fn table_len_for_lanes(lanes: usize) -> usize {
    assert!(lanes > 0, "zero RNS lanes cannot become an MLE table");
    let needed = lanes
        .checked_mul(2)
        .expect("bridge table length overflow: 2 BabyBear limbs per RNS lane");
    let padded = needed.next_power_of_two();
    assert!(
        u32::try_from(padded).is_ok(),
        "bridge table length {padded} exceeds the shader's u32 index space"
    );
    padded
}

impl Arena {
    /// The Montgomery constant the WGSL kernel compiles in. Exposed so a test can refuse a drift
    /// between `mle_fold.wgsl` and this module rather than mis-multiplying silently.
    #[must_use]
    pub fn mle_montgomery_mu() -> u32 {
        MONTY_MU
    }

    fn push_table(&self, buf: wgpu::Buffer, len: usize) -> ResidentTable {
        let mut tables = self.tables.lock().unwrap();
        tables.push(buf);
        ResidentTable {
            id: tables.len() - 1,
            len,
            capacity: len,
        }
    }

    fn table_buffer(&self, t: &ResidentTable) -> wgpu::Buffer {
        self.tables.lock().unwrap()[t.id].clone()
    }

    fn new_table_buffer(&self, len: usize, mapped: bool) -> wgpu::Buffer {
        let size = u64::try_from(len)
            .ok()
            .and_then(|n| n.checked_mul(4))
            .expect("MLE table byte-size overflow");
        assert!(
            size <= self.max_storage_bytes,
            "mle table: {size}-byte table exceeds adapter storage-binding capacity {}",
            self.max_storage_bytes
        );
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("mle-table"),
            size,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: mapped,
        })
    }

    /// Upload a host-side evaluation table. This is the UNFUSED path's entry point: bytes that were
    /// just read back off the device go straight back onto it.
    ///
    /// # Panics
    ///
    /// - `evals` must be a nonzero power-of-two length that fits the adapter's storage binding.
    pub fn upload_table(&self, evals: &[u32]) -> ResidentTable {
        assert!(
            !evals.is_empty() && evals.len().is_power_of_two(),
            "MLE table length must be a nonzero power of two (got {})",
            evals.len()
        );
        let buf = self.new_table_buffer(evals.len(), true);
        buf.slice(..)
            .get_mapped_range_mut()
            .copy_from_slice(bytemuck::cast_slice(evals));
        buf.unmap();
        self.push_table(buf, evals.len())
    }

    /// THE FUSED HAND-OFF. Reinterpret a resident BFV ciphertext buffer as a BabyBear MLE
    /// evaluation table with one dispatch, device-to-device. Nothing is read back and the submit is
    /// not waited on.
    ///
    /// # Panics
    ///
    /// - the resident set must have at least one lane and fit the adapter's storage binding.
    pub fn bridge_to_babybear(&self, h: &ResidentHandle) -> ResidentTable {
        use wgpu::util::DeviceExt;

        let lanes = h.total_lanes();
        let table_len = table_len_for_lanes(lanes);
        let src = self.resident_buffer(h);
        let out = self.new_table_buffer(table_len, false);

        let meta = BridgeMeta {
            n_lanes: u32::try_from(lanes).expect("bridge: lane count exceeds u32"),
            table_len: u32::try_from(table_len).expect("bridge: table length exceeds u32"),
            _pad0: 0,
            _pad1: 0,
        };
        let meta_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bridge-meta"),
                contents: bytemuck::bytes_of(&meta),
                usage: wgpu::BufferUsages::UNIFORM,
            });
        let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bridge"),
            layout: &self.bridge_bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: meta_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: src.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: out.as_entire_binding(),
                },
            ],
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            pass.set_pipeline(&self.bridge_pipeline);
            pass.set_bind_group(0, &bind, &[]);
            pass.dispatch_workgroups(meta.table_len.div_ceil(WORKGROUP), 1, 1);
        }
        self.queue.submit([enc.finish()]);
        self.push_table(out, table_len)
    }

    /// Fold `challenges.len()` variables away, IN PLACE, in ONE compute pass and ONE submission.
    ///
    /// Dispatches inside a compute pass are ordered and memory-visible to each other (WebGPU
    /// requires it; the Metal backend gets it from `MTLDispatchTypeSerial`), which is what makes the
    /// whole n-round fold a single submission over a single allocation. Nothing is read back and
    /// nothing is waited on here — [`Arena::download_table`] is the one synchronization point.
    ///
    /// # Panics
    ///
    /// - the table must have at least `2^challenges.len()` live elements.
    pub fn mle_fold_rounds(&self, table: &mut ResidentTable, challenges: &[u32]) {
        use wgpu::util::DeviceExt;

        if challenges.is_empty() {
            return;
        }
        assert!(
            table.len >= 1usize << challenges.len(),
            "cannot fold {} variables out of a {}-element table",
            challenges.len(),
            table.len
        );
        let buf = self.table_buffer(table);

        let mut half = table.len;
        let metas = challenges
            .iter()
            .map(|&r| {
                half /= 2;
                let meta = MleMeta {
                    half: u32::try_from(half).expect("fold round: half exceeds u32"),
                    r_mont: to_montgomery(r),
                    _pad0: 0,
                    _pad1: 0,
                };
                self.device
                    .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                        label: Some("mle-meta"),
                        contents: bytemuck::bytes_of(&meta),
                        usage: wgpu::BufferUsages::UNIFORM,
                    })
            })
            .collect::<Vec<_>>();
        let binds = metas
            .iter()
            .map(|meta| {
                self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("mle-round"),
                    layout: &self.mle_bgl,
                    entries: &[
                        wgpu::BindGroupEntry {
                            binding: 0,
                            resource: meta.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 1,
                            resource: buf.as_entire_binding(),
                        },
                    ],
                })
            })
            .collect::<Vec<_>>();

        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = enc.begin_compute_pass(&Default::default());
            pass.set_pipeline(&self.mle_pipeline);
            let mut remaining = table.len;
            for bind in &binds {
                remaining /= 2;
                pass.set_bind_group(0, bind, &[]);
                pass.dispatch_workgroups(
                    u32::try_from(remaining)
                        .expect("fold round: half exceeds u32")
                        .div_ceil(WORKGROUP),
                    1,
                    1,
                );
            }
        }
        self.queue.submit([enc.finish()]);
        table.len >>= challenges.len();
    }

    /// The ONE readback for a table: copy the live prefix to a MAP_READ staging buffer, wait, and
    /// return it.
    ///
    /// # Panics
    ///
    /// - the table must be nonempty.
    #[must_use]
    pub fn download_table(&self, table: &ResidentTable) -> Vec<u32> {
        assert!(table.len > 0, "download_table: empty table");
        let bytes = u64::try_from(table.len).expect("table length fits u64") * 4;
        // A MAP_READ copy destination must be 4-byte aligned in size, which u32 elements always are.
        let read_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("mle-table-read"),
            size: bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let src = self.table_buffer(table);
        let mut enc = self.device.create_command_encoder(&Default::default());
        enc.copy_buffer_to_buffer(&src, 0, &read_buf, 0, bytes);
        self.queue.submit([enc.finish()]);

        let slice = read_buf.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let data = slice.get_mapped_range();
        let out: Vec<u32> = data
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().expect("chunks_exact(4) yields 4 bytes")))
            .collect();
        drop(data);
        read_buf.unmap();
        out
    }

    /// Gather several resident tables into ONE staging buffer, with ONE map and ONE device wait.
    ///
    /// This is the batched counterpart of [`Arena::download_table`], and it exists because the
    /// per-synchronization cost is not small: on the measured adapter a `map_async` + `Maintain::Wait`
    /// costs ~1.3 ms regardless of how many bytes cross. A K-stage pipeline that syncs per stage pays
    /// that K times; fused, it pays it once. Without this method a "fused" batch measurement would be
    /// silently paying K syncs and the comparison would be rigged against itself.
    ///
    /// # Panics
    ///
    /// - the set must be nonempty and every table nonempty.
    #[must_use]
    pub fn download_tables(&self, tables: &[&ResidentTable]) -> Vec<Vec<u32>> {
        assert!(!tables.is_empty(), "download_tables: empty set");
        let lens: Vec<usize> = tables
            .iter()
            .map(|t| {
                assert!(t.len > 0, "download_tables: empty table");
                t.len
            })
            .collect();
        let total: usize = lens.iter().sum();
        let bytes = u64::try_from(total).expect("total length fits u64") * 4;
        let read_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("mle-tables-read"),
            size: bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let mut enc = self.device.create_command_encoder(&Default::default());
        let mut offset = 0u64;
        for (t, &len) in tables.iter().zip(&lens) {
            let src = self.table_buffer(t);
            let n = u64::try_from(len).expect("length fits u64") * 4;
            enc.copy_buffer_to_buffer(&src, 0, &read_buf, offset, n);
            offset += n;
        }
        self.queue.submit([enc.finish()]);

        let slice = read_buf.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let data = slice.get_mapped_range();
        let flat: Vec<u32> = data
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().expect("chunks_exact(4) yields 4 bytes")))
            .collect();
        drop(data);
        read_buf.unmap();

        let mut out = Vec::with_capacity(tables.len());
        let mut at = 0usize;
        for &len in &lens {
            out.push(flat[at..at + len].to_vec());
            at += len;
        }
        out
    }

    /// Block until every submitted command has completed. The benchmark's timing boundary — without
    /// it, a "fused" measurement would only time command encoding.
    pub fn wait_idle(&self) {
        self.device.poll(wgpu::Maintain::Wait);
    }
}

/// The host-side half of the bridge: the SAME injective 2-limb encoding `bfv_to_babybear.wgsl`
/// applies, over downloaded ciphertext coefficients.
///
/// This is what the UNFUSED path must do, and it is also the oracle the GPU bridge is checked
/// against.
///
/// # Panics
///
/// - every residue must be < 2^60 (the deployed `FOLD_MODULI` are all < 2^37).
#[must_use]
pub fn bridge_lanes_to_babybear(lanes: &[u64], table_len: usize) -> Vec<u32> {
    let mut out = vec![0u32; table_len];
    for (i, &x) in lanes.iter().enumerate() {
        if 2 * i + 1 >= table_len {
            break;
        }
        assert!(
            x < (1u64 << 60),
            "bridge: residue {x} exceeds the 2-limb base-2^30 encoding's domain"
        );
        out[2 * i] = u32::try_from(x & 0x3fff_ffff).expect("30-bit limb fits u32");
        out[2 * i + 1] = u32::try_from(x >> 30).expect("30-bit-shifted limb fits u32");
    }
    out
}

/// Deterministic BabyBear fixture table. SplitMix64 reduced into the field — no `rand`, so a
/// failing measurement reproduces exactly.
///
/// # Panics
///
/// - `len` must be nonzero.
#[must_use]
pub fn fixture_table(len: usize, seed: u64) -> Vec<u32> {
    assert!(len > 0, "fixture_table: zero length");
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    (0..len)
        .map(|_| {
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^= z >> 31;
            u32::try_from(z % u64::from(BABYBEAR_P)).expect("a residue mod BabyBear fits u32")
        })
        .collect()
}

/// Deterministic round challenges, same generator, different stream.
#[must_use]
pub fn fixture_challenges(n: usize, seed: u64) -> Vec<u32> {
    fixture_table(n.max(1), seed ^ 0xA5A5_5A5A_A5A5_5A5A)
        .into_iter()
        .take(n)
        .collect()
}

/// Guards the WGSL constants against host-side drift. `mle_fold.wgsl` hard-codes `P` and `MU`; if
/// either changed without this module changing, every product would be silently wrong rather than
/// loudly wrong.
static CONSTANT_CHECK: Mutex<()> = Mutex::new(());

/// Recomputes `-P^{-1} mod 2^32` and refuses a mismatch with the constant compiled into the shader.
///
/// # Panics
///
/// - if the recomputed Montgomery constant disagrees with [`MONTY_MU`], or the shader source no
///   longer contains the constants this module assumes.
pub fn assert_montgomery_constants() {
    let _guard = CONSTANT_CHECK.lock().unwrap();
    // Newton iteration for the inverse of an odd modulus mod 2^32.
    let p = u64::from(BABYBEAR_P);
    let mut inv: u64 = 1;
    for _ in 0..5 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(inv))) & 0xffff_ffff;
    }
    assert_eq!(p.wrapping_mul(inv) & 0xffff_ffff, 1, "inverse mod 2^32");
    let mu = u32::try_from((1u64 << 32).wrapping_sub(inv) & 0xffff_ffff).expect("fits u32");
    assert_eq!(mu, MONTY_MU, "host MONTY_MU disagrees with its derivation");

    let src = include_str!("shaders/mle_fold.wgsl");
    assert!(
        src.contains(&format!("const P  : u32 = {BABYBEAR_P}u;")),
        "mle_fold.wgsl no longer declares P = {BABYBEAR_P}"
    );
    assert!(
        src.contains(&format!("const MU : u32 = {MONTY_MU}u;")),
        "mle_fold.wgsl no longer declares MU = {MONTY_MU}"
    );
}
