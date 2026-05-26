//! Colored terminal output with pass/fail per subsystem check.

use std::fmt;
use std::time::{Duration, Instant};

/// Result of a single check within a subsystem.
#[derive(Clone, Debug)]
pub struct CheckResult {
    pub name: String,
    pub passed: bool,
    pub error: Option<String>,
    #[allow(dead_code)]
    pub duration: Duration,
}

/// Result of an entire subsystem (group of checks).
#[derive(Clone, Debug)]
pub struct SubsystemResult {
    pub name: String,
    pub checks: Vec<CheckResult>,
}

impl SubsystemResult {
    pub fn passed_count(&self) -> usize {
        self.checks.iter().filter(|c| c.passed).count()
    }

    pub fn total_count(&self) -> usize {
        self.checks.len()
    }

    pub fn all_passed(&self) -> bool {
        self.checks.iter().all(|c| c.passed)
    }

    pub fn check_names(&self) -> String {
        self.checks
            .iter()
            .map(|c| c.name.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// The full preflight report aggregating all subsystems.
pub struct PreflightReport {
    pub subsystems: Vec<SubsystemResult>,
    pub total_duration: Duration,
}

impl PreflightReport {
    pub fn total_checks(&self) -> usize {
        self.subsystems.iter().map(|s| s.total_count()).sum()
    }

    pub fn total_passed(&self) -> usize {
        self.subsystems.iter().map(|s| s.passed_count()).sum()
    }

    pub fn all_passed(&self) -> bool {
        self.subsystems.iter().all(|s| s.all_passed())
    }
}

impl fmt::Display for PreflightReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "\n=== DREGG PREFLIGHT v1 ===")?;

        for subsystem in &self.subsystems {
            let icon = if subsystem.all_passed() {
                "\x1b[32m[PASS]\x1b[0m"
            } else {
                "\x1b[31m[FAIL]\x1b[0m"
            };
            writeln!(
                f,
                "{} {}: {} ({}/{})",
                icon,
                subsystem.name,
                subsystem.check_names(),
                subsystem.passed_count(),
                subsystem.total_count(),
            )?;

            // Print failed check details
            for check in &subsystem.checks {
                if !check.passed {
                    if let Some(ref err) = check.error {
                        writeln!(f, "       \x1b[31m^ {}: {}\x1b[0m", check.name, err)?;
                    }
                }
            }
        }

        writeln!(f)?;
        let total = self.total_checks();
        let passed = self.total_passed();
        if self.all_passed() {
            writeln!(
                f,
                "\x1b[32mPREFLIGHT PASSED: {}/{} checks ({:.1}s)\x1b[0m",
                passed,
                total,
                self.total_duration.as_secs_f64()
            )?;
            writeln!(f, "Ready for testnet promotion.")?;
        } else {
            writeln!(
                f,
                "\x1b[31mPREFLIGHT FAILED: {}/{} checks passed ({:.1}s)\x1b[0m",
                passed,
                total,
                self.total_duration.as_secs_f64()
            )?;
            writeln!(f, "NOT ready for promotion. Fix failures above.")?;
        }

        Ok(())
    }
}

/// Helper to run a named check, capturing panics as failures.
pub fn run_check(name: &str, f: impl FnOnce() -> Result<(), String>) -> CheckResult {
    let start = Instant::now();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    let duration = start.elapsed();

    match result {
        Ok(Ok(())) => CheckResult {
            name: name.to_string(),
            passed: true,
            error: None,
            duration,
        },
        Ok(Err(e)) => CheckResult {
            name: name.to_string(),
            passed: false,
            error: Some(e),
            duration,
        },
        Err(panic) => {
            let msg = if let Some(s) = panic.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown panic".to_string()
            };
            CheckResult {
                name: name.to_string(),
                passed: false,
                error: Some(format!("PANIC: {}", msg)),
                duration,
            }
        }
    }
}

/// Run a subsystem by name with a list of checks.
pub fn run_subsystem(name: &str, checks: Vec<CheckResult>) -> SubsystemResult {
    SubsystemResult {
        name: name.to_string(),
        checks,
    }
}
