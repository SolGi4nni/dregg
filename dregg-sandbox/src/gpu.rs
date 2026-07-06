//! The GPU cap-tier's typed surface: the GPU class a cap-grade names, the
//! metered GPU-seconds bound, and the host GPU probe. These are the cap-bounds
//! a live passthrough provider enforces + meters. They are pure types (no
//! hardware dependency), so the GPU tier's design is exercised + tested without
//! a GPU on the box; a live passthrough boot itself needs hardware.
//!
//! Ported from the retired operated exec layer (the prior operated layer,
//! `mod gpu`) — the one typed backing the [`crate::CapTier::Gpu`] seam had that
//! the strip-mine port dropped. The seam stays fail-closed
//! ([`crate::RunError::TierNotServed`]); these types are what a real provider
//! binds when the tier is wired.
//!
//! WIRING (one line, not yet applied): `pub mod gpu;` in `src/lib.rs`.

use std::path::Path;
use std::time::Duration;

/// The GPU resource a cap-grade authorizes. A workload either gets a whole
/// physical GPU (VFIO passthrough of the PCI device) or a MIG slice (an
/// NVIDIA A100/H100 partitioned into isolated GPU instances, each a fixed
/// compute + memory fraction). The class fixes the GPU-memory ceiling and
/// the metering rate the live provider binds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuClass {
    /// A MIG slice: `compute_sevenths` of the GPU (the MIG granularity is
    /// 1/7th of an A100/H100) + a fixed memory partition (GiB). The standard
    /// profiles are 1g.5gb, 2g.10gb, 3g.20gb, 7g.40gb.
    Mig {
        compute_sevenths: u8,
        memory_gib: u16,
    },
    /// A whole passed-through GPU (the full PCI device) with its total memory.
    Whole { memory_gib: u16 },
}

impl GpuClass {
    /// The GPU-memory ceiling (MiB) this class grants — the hard cap the
    /// passthrough provider sets on the guest's visible VRAM.
    pub fn memory_mib(self) -> u64 {
        match self {
            GpuClass::Mig { memory_gib, .. } | GpuClass::Whole { memory_gib } => {
                memory_gib as u64 * 1024
            }
        }
    }

    /// The fraction of a physical GPU's compute this class commands, in
    /// 1/7ths (the MIG granularity); a whole GPU is 7/7.
    pub fn compute_sevenths(self) -> u8 {
        match self {
            GpuClass::Mig {
                compute_sevenths, ..
            } => compute_sevenths,
            GpuClass::Whole { .. } => 7,
        }
    }
}

/// The cap-bounds a GPU lease carries: the GPU class + a hard GPU-seconds
/// budget. The live provider refuses to start a workload whose budget is
/// spent and tears one down when it overruns — the GPU analogue of the
/// wall-clock timeout the CPU tiers enforce.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GpuBounds {
    pub class: GpuClass,
    /// Hard ceiling on metered GPU-seconds for the lease.
    pub max_gpu_seconds: u64,
}

/// A GPU-seconds meter: GPU-time accrues while a workload holds the GPU,
/// scaled by the class's compute fraction (a 1g MIG slice bills 1/7th the
/// GPU-seconds of a whole GPU for the same wall-clock). It settles through
/// the same conserving exactly-once rail the CPU / hosting meters use
/// (`dregg-agent`'s `Meter` is the settlement seam; this is the accounting).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct GpuMeter {
    gpu_seconds_milli: u64,
}

impl GpuMeter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Accrue `wall` wall-clock at `class`'s compute fraction. Returns the
    /// running GPU-seconds (milli-resolution) so a caller can compare to the
    /// bound.
    pub fn tick(&mut self, class: GpuClass, wall: Duration) -> u64 {
        let scaled = wall.as_millis() as u64 * class.compute_sevenths() as u64 / 7;
        self.gpu_seconds_milli = self.gpu_seconds_milli.saturating_add(scaled);
        self.gpu_seconds_milli
    }

    /// Total metered GPU-seconds (whole seconds, rounded down).
    pub fn gpu_seconds(self) -> u64 {
        self.gpu_seconds_milli / 1000
    }

    /// `true` once the meter has reached `bounds.max_gpu_seconds` — the
    /// signal to refuse / tear down (the lease's GPU budget is spent).
    pub fn over_budget(self, bounds: &GpuBounds) -> bool {
        self.gpu_seconds() >= bounds.max_gpu_seconds
    }
}

/// Probe the host for GPU character devices: NVIDIA (`/dev/nvidia0..`) and
/// DRM render nodes (`/dev/dri/renderD128..`). Returns the device paths
/// found — empty on a CPU-only host (so the Gpu tier refuses cleanly there).
pub fn host_gpu_devices() -> Vec<String> {
    let mut found = Vec::new();
    for n in 0..8 {
        let nv = format!("/dev/nvidia{n}");
        if Path::new(&nv).exists() {
            found.push(nv);
        }
    }
    for n in 128..136 {
        let dri = format!("/dev/dri/renderD{n}");
        if Path::new(&dri).exists() {
            found.push(dri);
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mig_class_memory_and_compute() {
        let c = GpuClass::Mig {
            compute_sevenths: 1,
            memory_gib: 5,
        };
        assert_eq!(c.memory_mib(), 5 * 1024);
        assert_eq!(c.compute_sevenths(), 1);
        let w = GpuClass::Whole { memory_gib: 40 };
        assert_eq!(w.compute_sevenths(), 7);
        assert_eq!(w.memory_mib(), 40 * 1024);
    }

    #[test]
    fn meter_scales_by_compute_fraction() {
        // A whole GPU bills full wall-clock; a 1/7 MIG slice bills 1/7th.
        let mut whole = GpuMeter::new();
        whole.tick(GpuClass::Whole { memory_gib: 40 }, Duration::from_secs(7));
        assert_eq!(whole.gpu_seconds(), 7);

        let mut mig = GpuMeter::new();
        mig.tick(
            GpuClass::Mig {
                compute_sevenths: 1,
                memory_gib: 5,
            },
            Duration::from_secs(7),
        );
        assert_eq!(mig.gpu_seconds(), 1);
    }

    #[test]
    fn meter_trips_budget() {
        let bounds = GpuBounds {
            class: GpuClass::Whole { memory_gib: 40 },
            max_gpu_seconds: 10,
        };
        let mut m = GpuMeter::new();
        m.tick(bounds.class, Duration::from_secs(9));
        assert!(!m.over_budget(&bounds));
        m.tick(bounds.class, Duration::from_secs(2));
        assert!(m.over_budget(&bounds));
    }
}
