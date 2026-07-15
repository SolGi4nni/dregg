//! A **real** (non-Null) machine launcher: the local sandbox lease plane.
//!
//! [`crate::machines::NullLauncher`] admits a create as `started` without tracking
//! anything — fine for a router demo, but the machines API is then record-keeping over
//! nothing. [`SandboxLauncher`] gives the compute backend substance *in-process*: every
//! machine gets a **lease slot** with an unguessable lease id and a real lifecycle
//! (`open → running → reaped → reopened`), metered by launch/reap counts and a step
//! cursor. It enforces the lifecycle (a reap of an unknown machine is refused; a
//! restart reopens the *same* lease identity, it does not mint a second) and exposes
//! the live slot for observability.
//!
//! This is the local single-box lease — honest and testable. The production upgrade is
//! the resident `hosted-lease` plane (a `HostedLease` over a committed umem execution
//! image with a proven meter); `SandboxLauncher` is the same [`MachineLauncher`] seam a
//! `hosted-lease`-backed launcher slots into, so the machines surface does not change
//! when the backend does.

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::machines::{Machine, MachineLauncher, MachineState};
use crate::util::{lock, mint_token};

/// A live lease slot for one machine — its stable lease identity + lifecycle counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeaseInfo {
    /// The stable lease id (minted once at first launch, kept across restarts).
    pub lease_id: String,
    /// Whether the workload is currently running.
    pub running: bool,
    /// How many times this lease has been (re)launched.
    pub launches: u64,
    /// How many times this lease has been reaped.
    pub reaps: u64,
}

/// The local sandbox lease plane. One [`LeaseInfo`] per machine id.
pub struct SandboxLauncher {
    leases: Mutex<BTreeMap<String, LeaseInfo>>,
}

impl Default for SandboxLauncher {
    fn default() -> SandboxLauncher {
        SandboxLauncher::new()
    }
}

impl SandboxLauncher {
    /// A fresh sandbox with no open leases.
    pub fn new() -> SandboxLauncher {
        SandboxLauncher {
            leases: Mutex::new(BTreeMap::new()),
        }
    }

    /// The live lease for `machine_id`, if one is open.
    pub fn lease_of(&self, machine_id: &str) -> Option<LeaseInfo> {
        lock(&self.leases).get(machine_id).cloned()
    }

    /// How many leases are currently running.
    pub fn running_count(&self) -> usize {
        lock(&self.leases).values().filter(|l| l.running).count()
    }
}

impl MachineLauncher for SandboxLauncher {
    fn launch(&self, machine: &Machine) -> Result<MachineState, String> {
        // A workload with no image reference is rejected: the sandbox has nothing to
        // run. (A real backend would validate the image reference against the lease's
        // funded capability grade.)
        if machine.config.guest.image.trim().is_empty() {
            return Err("no workload image reference to launch".to_string());
        }
        let mut guard = lock(&self.leases);
        let slot = guard
            .entry(machine.id.clone())
            .or_insert_with(|| LeaseInfo {
                lease_id: mint_token("lease_"),
                running: false,
                launches: 0,
                reaps: 0,
            });
        // (Re)launch keeps the SAME lease identity — a restart is not a new lease.
        slot.running = true;
        slot.launches += 1;
        Ok(MachineState::Started)
    }

    fn reap(&self, machine: &Machine) -> Result<(), String> {
        let mut guard = lock(&self.leases);
        match guard.get_mut(&machine.id) {
            Some(slot) => {
                slot.running = false;
                slot.reaps += 1;
                Ok(())
            }
            // Reaping a machine the sandbox never launched is a refusal, not a silent
            // success — it signals a lifecycle inconsistency to the caller.
            None => Err(format!("no open lease for machine `{}`", machine.id)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machines::{GuestConfig, MachineConfig};

    fn machine(id: &str, image: &str) -> Machine {
        Machine {
            id: id.into(),
            name: id.into(),
            app: "app".into(),
            owner: "dregg:alice".into(),
            state: MachineState::Stopped,
            region: "iad".into(),
            config: MachineConfig {
                guest: GuestConfig {
                    image: image.into(),
                    ..GuestConfig::default()
                },
                region: "iad".into(),
            },
        }
    }

    #[test]
    fn a_launch_opens_a_lease_and_a_restart_keeps_its_identity() {
        let sb = SandboxLauncher::new();
        let m = machine("mch_1", "workload:agent");
        assert_eq!(sb.launch(&m).unwrap(), MachineState::Started);
        let first = sb.lease_of("mch_1").unwrap();
        assert!(first.running);
        assert_eq!(first.launches, 1);
        assert_eq!(sb.running_count(), 1);

        // Reap, then relaunch — same lease id, running again, counters advance.
        sb.reap(&m).unwrap();
        assert!(!sb.lease_of("mch_1").unwrap().running);
        assert_eq!(sb.running_count(), 0);
        sb.launch(&m).unwrap();
        let relaunched = sb.lease_of("mch_1").unwrap();
        assert_eq!(relaunched.lease_id, first.lease_id, "same lease identity");
        assert_eq!(relaunched.launches, 2);
        assert_eq!(relaunched.reaps, 1);
    }

    #[test]
    fn an_imageless_workload_is_refused() {
        let sb = SandboxLauncher::new();
        assert!(sb.launch(&machine("mch_x", "  ")).is_err());
        assert!(sb.lease_of("mch_x").is_none(), "no lease opened on refusal");
    }

    #[test]
    fn reaping_an_unknown_machine_is_refused() {
        let sb = SandboxLauncher::new();
        assert!(sb.reap(&machine("mch_ghost", "img")).is_err());
    }
}
