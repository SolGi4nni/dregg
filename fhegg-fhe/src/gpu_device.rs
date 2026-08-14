//! ONE `wgpu::Device` for the whole crate — the thing that makes kernel fusion reachable at all.
//!
//! # Why this module exists
//!
//! Two `wgpu::Device`s cannot share a buffer. Until this module landed, every GPU-bearing module
//! here stood up its *own* `Instance` / `Adapter` / `Device` / `Queue` inside its own `OnceLock`:
//! `bfv_gpu`, `bfv_ntt_gpu`, `private_book_bfv_wgpu`, `tfhe_wgpu` (twice), `tfhe_ntt_wgpu`,
//! `tfhe_blind_rotation_wgpu`, `tfhe_blind_rotation_ntt_wgpu`, and `gpu_arena` — nine devices in
//! one process. So "hand the NTT kernel's resident output straight to the fold kernel" was not a
//! missing feature; it was **unreachable by construction**, and the measured fusion win
//! (`~/dev/zkml-research/notes/wgpu-fusion.md`: 2.7x–7.1x on memory traffic alone at 2^20–2^22)
//! was unavailable at every one of those sites.
//!
//! Now there is one device, one queue, and N pipelines — each still owned by the module whose
//! kernel it belongs to, because a pipeline is kernel-local knowledge and a device is not.
//!
//! # Why consolidating is behaviour-preserving here
//!
//! Every one of those nine sites requested a device with **exactly the same descriptor**:
//! `required_features: wgpu::Features::empty()` and `required_limits: adapter.limits()`, i.e. the
//! full limits of the same `HighPerformance` adapter. Only the debug `label` differed. So a single
//! device with that descriptor is not a compromise between nine different requests — it is
//! literally the request each of them already made. Adapter selection was identical too
//! (`PowerPreference::HighPerformance`, no surface, no fallback adapter).
//!
//! Module-level *policy* checks on the adapter are NOT centralized here — e.g.
//! `tfhe_blind_rotation_ntt_wgpu` refuses when `max_storage_buffers_per_shader_stage < 9`. Those
//! stay with their kernels, where the shape they guard is known, and they read [`SharedGpu::limits`].
//!
//! # ⚑ The one hazard consolidation introduces, and how it is closed
//!
//! wgpu error scopes are a **stack on the device**, not a per-caller channel. Nine devices meant
//! nine independent stacks; one device means one, so two threads in two different kernels can
//! interleave `push_error_scope` / `pop_error_scope` and each pop the other's scope. That is not
//! merely a false red: a thread can pop a *sibling's* captured validation error and thereby leave
//! its own scope empty, so a real error is reported against the wrong kernel and the guilty kernel
//! sees `None` and proceeds. A weakened check, introduced by a performance change.
//!
//! [`ValidationScope`] closes it. It is an RAII handle that serializes the whole
//! push..pop region against every other holder in the process, and it is **reentrant per thread**,
//! so a kernel that legitimately nests scopes (or calls another kernel that opens one) cannot
//! deadlock against itself. Nesting on one thread is properly nested and is exactly what the wgpu
//! stack is for; interleaving across threads is what it cannot express.
//!
//! Two properties fall out that the raw calls did not have:
//!
//! * **An early return can no longer leak a scope.** Every previous site pushed a scope and popped
//!   it several hundred lines later with `?`-returns in between; each of those returns left an
//!   unbalanced scope on the device forever. `Drop` now pops it.
//! * **Within a single module it was already unsound.** Each module's device was a `OnceLock`
//!   static shared by all its callers, so two threads calling the same kernel already interleaved
//!   on one stack. The lock fixes that too.
//!
//! The cost is that concurrent GPU calls serialize across the push..pop region. They were never
//! correct concurrently in the first place, and the regions are dominated by device work that a
//! single queue serializes anyway.

use std::cell::{Cell, RefCell};
use std::sync::{Mutex, MutexGuard, OnceLock};

/// The process-wide GPU. One adapter, one device, one queue; pipelines live with their kernels.
pub struct SharedGpu {
    /// Kept alive for the life of the process: dropping the instance while a device derived from
    /// it is still in use is not a thing wgpu promises to survive.
    _instance: wgpu::Instance,
    pub adapter: wgpu::Adapter,
    pub device: wgpu::Device,
    pub queue: wgpu::Queue,
    /// The adapter's limits, which are also the limits the device was granted. Kernels read this
    /// to apply their own shape policy (see the module docblock).
    pub limits: wgpu::Limits,
    pub info: wgpu::AdapterInfo,
}

impl SharedGpu {
    /// `min(max_buffer_size, max_storage_buffer_binding_size)` — the real ceiling on a single
    /// storage binding, which is what every capacity calculation in this crate actually wants.
    #[must_use]
    pub fn max_storage_bytes(&self) -> u64 {
        self.limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size))
    }

    /// Open a validation error scope on the shared device, serialized against every other holder.
    /// See the module docblock for why the raw `push_error_scope` is not safe to call here.
    #[must_use]
    pub fn validation_scope(&self) -> ValidationScope {
        ValidationScope::enter(&self.device)
    }
}

/// Why there is no GPU. Carried as an owned string so each module can wrap it in its own error
/// type without this module knowing about any of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SharedGpuUnavailable {
    /// `request_adapter` returned `None` — headless CI, no GPU, no software fallback.
    NoAdapter,
    /// `request_device` failed on an adapter that exists.
    DeviceRequestFailed(String),
}

impl std::fmt::Display for SharedGpuUnavailable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoAdapter => f.write_str("no wgpu adapter"),
            Self::DeviceRequestFailed(error) => {
                write!(f, "wgpu device request failed: {error}")
            }
        }
    }
}

/// The one device, or the reason there is none. Initialized once per process; every caller after
/// the first gets the same `&'static` and pays nothing.
///
/// Returning `Result` rather than `Option` matters: the two failure modes are operationally
/// different (a box with no GPU vs. a GPU that refused a device) and several callers already
/// distinguish them in their own error enums.
pub fn shared_gpu() -> Result<&'static SharedGpu, SharedGpuUnavailable> {
    static GPU: OnceLock<Result<SharedGpu, SharedGpuUnavailable>> = OnceLock::new();
    GPU.get_or_init(initialize).as_ref().map_err(Clone::clone)
}

/// `true` when this process has a usable shared device. Cheap after the first call.
#[must_use]
pub fn is_available() -> bool {
    shared_gpu().is_ok()
}

fn initialize() -> Result<SharedGpu, SharedGpuUnavailable> {
    let instance = wgpu::Instance::default();
    let Some(adapter) =
        pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: None,
            force_fallback_adapter: false,
        }))
    else {
        return Err(SharedGpuUnavailable::NoAdapter);
    };
    let limits = adapter.limits();
    let info = adapter.get_info();
    // The descriptor every migrated site already used, verbatim. See the docblock.
    let (device, queue) = match pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("fhegg-fhe shared device"),
            required_features: wgpu::Features::empty(),
            required_limits: limits.clone(),
            memory_hints: Default::default(),
        },
        None,
    )) {
        Ok(pair) => pair,
        Err(error) => {
            return Err(SharedGpuUnavailable::DeviceRequestFailed(error.to_string()));
        }
    };
    Ok(SharedGpu {
        _instance: instance,
        adapter,
        device,
        queue,
        limits,
        info,
    })
}

// ── the error-scope stack, made safe to share ────────────────────────────────────────────────

/// Held for the whole push..pop region by whichever thread owns the device's error-scope stack.
static SCOPE_LOCK: Mutex<()> = Mutex::new(());

thread_local! {
    /// How many scopes THIS thread has open. The lock is taken on 0 -> 1 and released on 1 -> 0,
    /// which is what makes the whole thing reentrant within a thread.
    static SCOPE_DEPTH: Cell<usize> = const { Cell::new(0) };
    /// The guard, parked here while this thread owns the stack. `MutexGuard` is `!Send`, and a
    /// thread-local is exactly the place a non-Send value that follows a thread can live.
    static SCOPE_GUARD: RefCell<Option<MutexGuard<'static, ()>>> = const { RefCell::new(None) };
}

/// An open `wgpu::ErrorFilter::Validation` scope on the shared device.
///
/// Construct with [`SharedGpu::validation_scope`]. Finish with [`ValidationScope::pop`] to read the
/// captured error; dropping it without popping still balances the device's stack (and is the right
/// behaviour on an early return, which previously leaked a scope).
#[must_use = "a ValidationScope that is dropped immediately captures nothing"]
pub struct ValidationScope {
    device: wgpu::Device,
    popped: bool,
}

impl ValidationScope {
    /// Same as [`SharedGpu::validation_scope`], for the many call sites that hold a cloned
    /// `wgpu::Device` in their own context struct and never look at the `SharedGpu` again.
    ///
    /// Passing a device that is *not* the shared one is sound — the scope still balances — it just
    /// serializes against holders it does not need to. Nothing in this crate does that any more.
    #[must_use]
    pub fn for_device(device: &wgpu::Device) -> Self {
        Self::enter(device)
    }

    fn enter(device: &wgpu::Device) -> Self {
        SCOPE_DEPTH.with(|depth| {
            if depth.get() == 0 {
                // A poisoned scope lock means some other thread panicked mid-region. The data is
                // `()`; there is no invariant to be poisoned. Take it and carry on rather than
                // turning an unrelated panic into a cascade of GPU unavailability.
                let guard = SCOPE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
                SCOPE_GUARD.with(|slot| *slot.borrow_mut() = Some(guard));
            }
            depth.set(depth.get() + 1);
        });
        device.push_error_scope(wgpu::ErrorFilter::Validation);
        Self {
            device: device.clone(),
            popped: false,
        }
    }

    /// Close the scope and return the validation error it captured, if any. Exactly the value the
    /// bare `pollster::block_on(device.pop_error_scope())` used to return.
    #[must_use]
    pub fn pop(mut self) -> Option<wgpu::Error> {
        self.popped = true;
        let error = pollster::block_on(self.device.pop_error_scope());
        release();
        error
    }
}

impl Drop for ValidationScope {
    fn drop(&mut self) {
        if !self.popped {
            // Balance the device's stack even on an early return. Discarding the error is the
            // pre-existing behaviour of every path that returned between push and pop; the
            // difference is that the scope no longer stays open forever.
            let _ = pollster::block_on(self.device.pop_error_scope());
            release();
        }
    }
}

fn release() {
    SCOPE_DEPTH.with(|depth| {
        let remaining = depth.get().saturating_sub(1);
        depth.set(remaining);
        if remaining == 0 {
            SCOPE_GUARD.with(|slot| slot.borrow_mut().take());
        }
    });
}
