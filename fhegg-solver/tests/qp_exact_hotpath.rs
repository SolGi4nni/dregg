use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Instant;

use fhegg_solver::qp_exact::CertQpExact;

struct CountingAllocator;

static TRACK_ALLOCATIONS: AtomicBool = AtomicBool::new(false);
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static ALLOCATED_BYTES: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if TRACK_ALLOCATIONS.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
            ALLOCATED_BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        }
        // SAFETY: this allocator delegates the unchanged layout to `System`.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` was returned by `System` for this exact layout.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if TRACK_ALLOCATIONS.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
            ALLOCATED_BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        }
        // SAFETY: this allocator delegates the unchanged layout to `System`.
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if TRACK_ALLOCATIONS.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
            ALLOCATED_BYTES.fetch_add(new_size, Ordering::Relaxed);
        }
        // SAFETY: `ptr` and `layout` came from `System`; `new_size` is passed
        // through unchanged.
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn exact_identity_qp(n: usize) -> CertQpExact {
    let mut p = vec![0; n * n];
    let mut a = vec![0; n * n];
    for i in 0..n {
        p[i * n + i] = 1;
        a[i * n + i] = 1;
    }
    CertQpExact {
        n,
        mc: n,
        scale: 0,
        p,
        q: vec![-1; n],
        a,
        l: vec![1; n],
        u: vec![1; n],
        x: vec![1; n],
        y: vec![0; n],
        epsilon: 0,
    }
}

fn row_dot(row: &[i128], vector: &[i128]) -> Option<i128> {
    let mut sum = 0_i128;
    for (a, b) in row.iter().zip(vector) {
        sum = sum.checked_add(a.checked_mul(*b)?)?;
    }
    Some(sum)
}

/// Exact copy of the former production residual implementation. Keeping it in
/// this benchmark target provides a same-process before/after oracle without
/// retaining an allocating path in the library.
fn allocating_residual_oracle(certificate: &CertQpExact) -> Option<(i128, i128, i128, i128)> {
    let scale = 10_i128.pow(certificate.scale);
    let (n, mc) = (certificate.n, certificate.mc);
    let ax: Vec<i128> = (0..mc)
        .map(|i| row_dot(&certificate.a[i * n..(i + 1) * n], &certificate.x))
        .collect::<Option<_>>()?;

    let mut primal = 0_i128;
    for i in 0..mc {
        let upper = certificate.u[i].checked_mul(scale)?;
        let lower = certificate.l[i].checked_mul(scale)?;
        let over = ax[i].checked_sub(upper)?.max(0);
        let under = lower.checked_sub(ax[i])?.max(0);
        primal = primal.max(over.checked_add(under)?);
    }

    let mut dual = 0_i128;
    for j in 0..n {
        let px = row_dot(&certificate.p[j * n..(j + 1) * n], &certificate.x)?;
        let mut aty = 0_i128;
        for i in 0..mc {
            aty = aty.checked_add(certificate.a[i * n + j].checked_mul(certificate.y[i])?)?;
        }
        let objective = certificate.q[j].checked_mul(scale)?;
        dual = dual.max(px.checked_add(objective)?.checked_add(aty)?.checked_abs()?);
    }

    let mut normal = 0_i128;
    for i in 0..mc {
        let upper = certificate.u[i].checked_mul(scale)?;
        let lower = certificate.l[i].checked_mul(scale)?;
        let shifted = ax[i].checked_add(certificate.y[i].checked_mul(scale)?)?;
        let projected = shifted.clamp(lower, upper);
        normal = normal.max(ax[i].checked_sub(projected)?.checked_abs()?);
    }
    Some((
        primal,
        dual,
        normal,
        certificate.epsilon.checked_mul(scale)?,
    ))
}

fn allocation_delta(run: impl FnOnce()) -> (usize, usize) {
    ALLOCATIONS.store(0, Ordering::Relaxed);
    ALLOCATED_BYTES.store(0, Ordering::Relaxed);
    TRACK_ALLOCATIONS.store(true, Ordering::SeqCst);
    run();
    TRACK_ALLOCATIONS.store(false, Ordering::SeqCst);
    (
        ALLOCATIONS.load(Ordering::Relaxed),
        ALLOCATED_BYTES.load(Ordering::Relaxed),
    )
}

fn timed_ns(iterations: usize, mut run: impl FnMut()) -> u128 {
    let started = Instant::now();
    for _ in 0..iterations {
        run();
    }
    started.elapsed().as_nanos()
}

#[test]
fn exact_kkt_revalidation_allocation_and_timing_probe() {
    const N: usize = 256;
    const ITERATIONS: usize = 256;

    let certificate = exact_identity_qp(N);
    assert!(certificate.check().valid, "benchmark fixture must be exact");
    assert_eq!(
        allocating_residual_oracle(&certificate),
        Some((0, 0, 0, 0)),
        "allocating oracle and production checker must name the same fixture"
    );

    let (baseline_allocations, baseline_bytes) = allocation_delta(|| {
        for _ in 0..ITERATIONS {
            assert_eq!(
                std::hint::black_box(allocating_residual_oracle(&certificate)),
                Some((0, 0, 0, 0))
            );
        }
    });
    let (streaming_allocations, streaming_bytes) = allocation_delta(|| {
        for _ in 0..ITERATIONS {
            assert!(std::hint::black_box(certificate.check()).valid);
        }
    });

    // Allocation counting uses atomics only on the old path, so take timing in
    // separate untracked runs. Alternate the order once to reduce one-sided
    // cache/frequency bias and report the aggregate per-check time.
    let baseline_first = timed_ns(ITERATIONS, || {
        assert_eq!(
            std::hint::black_box(allocating_residual_oracle(&certificate)),
            Some((0, 0, 0, 0))
        );
    });
    let streaming_first = timed_ns(ITERATIONS, || {
        assert!(std::hint::black_box(certificate.check()).valid);
    });
    let streaming_second = timed_ns(ITERATIONS, || {
        assert!(std::hint::black_box(certificate.check()).valid);
    });
    let baseline_second = timed_ns(ITERATIONS, || {
        assert_eq!(
            std::hint::black_box(allocating_residual_oracle(&certificate)),
            Some((0, 0, 0, 0))
        );
    });
    let baseline_ns = baseline_first + baseline_second;
    let streaming_ns = streaming_first + streaming_second;
    let measured_checks = ITERATIONS * 2;
    eprintln!(
        "exact-kkt-check n={N} checks={measured_checks} baseline_ns_per_check={} streaming_ns_per_check={} baseline_allocations_per_check={} baseline_bytes_per_check={} streaming_allocations={} streaming_bytes={}",
        baseline_ns / measured_checks as u128,
        streaming_ns / measured_checks as u128,
        baseline_allocations / ITERATIONS,
        baseline_bytes / ITERATIONS,
        streaming_allocations,
        streaming_bytes,
    );

    // The exact checker is settlement authority and is repeatedly replayed by
    // hostile wire/program-binding boundaries. It must not need a verifier-size
    // temporary merely to recompute residuals.
    assert_eq!(
        baseline_allocations / ITERATIONS,
        7,
        "the same-process old-path oracle should retain the measured baseline"
    );
    assert_eq!(baseline_bytes / ITERATIONS, 8_128);
    assert_eq!(
        streaming_allocations, 0,
        "exact KKT revalidation must be allocation-free"
    );
    assert_eq!(streaming_bytes, 0);
}
