//! The CONFINED-RUN CORE and its two faces (L2 runner, L3 re-executor).
//!
//! macOS-only: it drives firmament's heavy-body Seatbelt jail
//! ([`ProcessKernel::spawn_pd_confined_exec`]), whose backend is `sandbox_init`
//! (SBPL). See the crate-root docs for the guarantees and the determinism
//! constraint.

use std::io::{self, Read};
use std::path::Path;

use dregg_doc::{run_ci_verdict, CiVerdict};
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_firmament::sandbox::Confinement;
use dregg_turn::{TurnError, TurnReceipt};

use crate::{confinement_id, input_root_of_dir, WORK_TOKEN};

/// The signed witness a successful [`run_check_confined`] produces: the
/// [`CiVerdict`] plus the committed, executor-signed genesis-turn
/// [`TurnReceipt`]. Present these as the forge's
/// [`dregg_doc::CheckWitness::CiRun`].
#[derive(Clone, Debug)]
pub struct CiRunReceipt {
    /// The work-binding verdict the confined run produced.
    pub verdict: CiVerdict,
    /// The committed, executor-signed receipt of the CI-run genesis turn that
    /// committed exactly `verdict` (`receipt.turn_hash ==
    /// planned_ci_run_hash(editor, region, verdict)`).
    pub receipt: TurnReceipt,
}

/// Why the confined runner failed to produce a signed verdict.
#[derive(Debug)]
pub enum RunError {
    /// An I/O or confinement-spawn failure (seeding the work dir, spawning the
    /// jailed process, reading its stdout, reaping it).
    Io(io::Error),
    /// The `dregg_doc::run_ci_verdict` commit of the verdict as a genesis turn
    /// failed (the executor refused / could not sign).
    Commit(TurnError),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::Io(e) => write!(f, "confined-run I/O error: {e}"),
            RunError::Commit(e) => write!(f, "verdict commit failed: {e:?}"),
        }
    }
}
impl std::error::Error for RunError {}
impl From<io::Error> for RunError {
    fn from(e: io::Error) -> Self {
        RunError::Io(e)
    }
}

/// The verdict of an L3 re-execution audit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuditVerdict {
    /// The re-run reproduced the verdict exactly (`confinement_id`, `exit_code`,
    /// and `output_digest` all match) — the host told the truth.
    Honest,
    /// The re-run diverged: the host signed a verdict that does not match what
    /// re-executing the same command actually produced. `field` names the
    /// divergent field; `claimed`/`recomputed` are its hex/decimal renderings.
    HostLied {
        /// `"confinement_id"`, `"exit_code"`, or `"output_digest"`.
        field: &'static str,
        /// What the signed verdict claimed.
        claimed: String,
        /// What re-execution recomputed.
        recomputed: String,
    },
}

/// The raw result of one confined run: the confinement identity it ran under, the
/// exit code, and the blake3 of the process's stdout.
struct ConfinedRun {
    confinement_id: [u8; 32],
    exit_code: i32,
    output_digest: [u8; 32],
}

/// THE SHARED CORE both L2 and L3 run: build a Seatbelt confinement granting
/// read+write to a fresh work dir seeded from `input_dir` and `execve` of exactly
/// `command_image`, spawn it, read stdout to EOF (→ `output_digest`), reap
/// (→ `exit_code`). `argv` are the args AFTER the image (argv[0] is set to the
/// image); each element has [`WORK_TOKEN`] substituted with the confined work
/// dir. Deterministic in the confined inputs (see the crate-root determinism
/// note).
fn run_confined(
    input_dir: &Path,
    command_image: &Path,
    argv: &[String],
) -> io::Result<ConfinedRun> {
    // A fresh, canonical work dir (the one writable subpath), seeded from the
    // input tree. Canonical because macOS /tmp,/var are symlinks into /private
    // and the sandbox kernel checks writes against the RESOLVED path.
    let work = fresh_work_dir()?;
    copy_tree_into(input_dir, &work)?;
    let work_canon = std::fs::canonicalize(&work).unwrap_or_else(|_| work.clone());
    let work_str = work_canon.to_string_lossy().into_owned();

    let image_str = command_image.to_string_lossy().into_owned();
    let brew = std::env::var("HOMEBREW_PREFIX").unwrap_or_else(|_| "/opt/homebrew".to_string());

    // The confinement id commits the profile SHAPE + command (path-agnostic via
    // the WORK token) — the identity L3 rebuilds from the honest inputs.
    let cid = confinement_id(&image_str, argv, &brew);

    // THE DENY-DEFAULT HEAVY-BODY CONFINEMENT: system reads (dyld/libSystem +
    // process machinery a real binary needs), the homebrew prefix, read+write on
    // the work dir, and the one execve door for the command image. No network,
    // no other write path, no other exec.
    let confinement = Confinement::default()
        .with_system_reads()
        .with_homebrew_prefix(&brew)
        .with_write_path(&work_canon)
        .with_exec_image(&image_str);

    // Full argv: image first, then the WORK-substituted args.
    let full_argv: Vec<String> = std::iter::once(image_str.clone())
        .chain(argv.iter().map(|a| a.replace(WORK_TOKEN, &work_str)))
        .collect();
    // Inherit the parent env (PATH/HOME/dyld vars a real binary needs).
    let env: Vec<(String, String)> = std::env::vars().collect();

    let kernel = ProcessKernel::new();
    let proc = kernel
        .spawn_pd_confined_exec(confinement, &full_argv, &env)
        .map_err(|e| {
            io::Error::new(
                io::ErrorKind::Other,
                format!("confined spawn failed: {e:?}"),
            )
        })?;

    // Read stdout to EOF BEFORE reaping (avoids a pipe-buffer deadlock). The
    // write end is the child's 1/2; EOF arrives when it exits.
    let mut out = Vec::new();
    let mut stdout = proc.stdout.try_clone()?;
    stdout.read_to_end(&mut out)?;
    let exit_code = proc.reap()?;
    let output_digest = *blake3::hash(&out).as_bytes();

    let _ = std::fs::remove_dir_all(&work);

    Ok(ConfinedRun {
        confinement_id: cid,
        exit_code,
        output_digest,
    })
}

/// **L2 — THE CONFINED RUNNER.** Run the check command `command_image` (with
/// `argv`; [`WORK_TOKEN`] → the confined work dir) inside a macOS-Seatbelt
/// confinement seeded from `input_dir`, then commit the result as a signed
/// [`CiVerdict`] via [`dregg_doc::run_ci_verdict`] — the GENESIS turn of a fresh
/// CI-run cell `(editor_seed, region_seed)`, signed by `host_signing_seed`.
///
/// - `input_root` = [`input_root_of_dir`]`(input_dir)` — the REAL
///   `substrate_commit` of the working tree (equals a PR's `input_root` when the
///   tree materializes that PR's `merged_graph`; see the crate-root seam note).
/// - `command_id` is the required check's command id (the forge's `CiRun.command_id`).
/// - `confinement_id` = [`confinement_id`] of the sandbox profile + command.
///
/// Returns the [`CiVerdict`] + its committed, executor-signed [`TurnReceipt`]. The
/// receipt's `turn_hash` equals [`dregg_doc::planned_ci_run_hash`] over the
/// verdict — the in-turn binding the forge `CiRun` check verifies.
#[allow(clippy::too_many_arguments)]
pub fn run_check_confined(
    input_dir: &Path,
    command_image: &Path,
    argv: &[String],
    command_id: [u8; 32],
    host_signing_seed: [u8; 32],
    editor_seed: u8,
    region_seed: u8,
) -> Result<CiRunReceipt, RunError> {
    let run = run_confined(input_dir, command_image, argv)?;
    let input_root = input_root_of_dir(input_dir)?;

    let verdict = CiVerdict {
        input_root,
        command_id,
        confinement_id: run.confinement_id,
        exit_code: run.exit_code,
        output_digest: run.output_digest,
    };

    // Commit the verdict as the GENESIS turn of a fresh CI-run cell — one cell,
    // one verdict, no setup turn — so the signed turn_hash equals the
    // fresh-genesis re-derivation the forge check runs.
    let receipt = run_ci_verdict(editor_seed, region_seed, host_signing_seed, &verdict)
        .map_err(RunError::Commit)?;

    Ok(CiRunReceipt { verdict, receipt })
}

/// **L3 — THE RE-EXECUTOR (the non-circular audit).** Re-run the SAME command
/// (`command_image` + `argv`) in a FRESH confinement seeded from `input_dir`, and
/// compare the recomputed `{confinement_id, exit_code, output_digest}` to
/// `verdict`. [`AuditVerdict::Honest`] iff all three match; otherwise
/// [`AuditVerdict::HostLied`] naming the first divergent field.
///
/// This is what convicts a lying host: the host is the executor and can SIGN a
/// well-formed verdict, but it cannot make a HONEST re-run reproduce a fabricated
/// `output_digest` / `exit_code`. See the crate-root determinism constraint (a
/// nondeterministic check is a false-conviction hazard).
pub fn reexecute_and_verify(
    verdict: &CiVerdict,
    input_dir: &Path,
    command_image: &Path,
    argv: &[String],
) -> io::Result<AuditVerdict> {
    let run = run_confined(input_dir, command_image, argv)?;

    // The sandbox/command the auditor rebuilt must be the one the verdict claims
    // it ran under. A mismatch means the signed verdict was for a different
    // confinement/command than the one being audited.
    if run.confinement_id != verdict.confinement_id {
        return Ok(AuditVerdict::HostLied {
            field: "confinement_id",
            claimed: hex(&verdict.confinement_id),
            recomputed: hex(&run.confinement_id),
        });
    }
    if run.exit_code != verdict.exit_code {
        return Ok(AuditVerdict::HostLied {
            field: "exit_code",
            claimed: verdict.exit_code.to_string(),
            recomputed: run.exit_code.to_string(),
        });
    }
    if run.output_digest != verdict.output_digest {
        return Ok(AuditVerdict::HostLied {
            field: "output_digest",
            claimed: hex(&verdict.output_digest),
            recomputed: hex(&run.output_digest),
        });
    }
    Ok(AuditVerdict::Honest)
}

/// A fresh, unique work dir under the OS temp dir (pid + a process-local counter).
fn fresh_work_dir() -> io::Result<std::path::PathBuf> {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let p = std::env::temp_dir().join(format!(
        "forge-ci-run-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p)?;
    Ok(p)
}

/// Recursively copy the contents of `src` into `dst` (directories re-created,
/// files byte-copied). The seed of the confined work dir.
fn copy_tree_into(src: &Path, dst: &Path) -> io::Result<()> {
    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let from = entry.path();
        let to = dst.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            std::fs::create_dir_all(&to)?;
            copy_tree_into(&from, &to)?;
        } else {
            std::fs::copy(&from, &to)?;
        }
    }
    Ok(())
}

/// Lowercase-hex a byte slice (for the audit-divergence rendering).
fn hex(b: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for &x in b {
        s.push(HEX[(x >> 4) as usize] as char);
        s.push(HEX[(x & 0x0f) as usize] as char);
    }
    s
}
