//! The real firmament OS-jail backing a confined body (`real-jail` feature).
//!
//! [`spawn_confined_body`] forks a body into a firmament process-PD confined to
//! Endpoint-only — file, network, and `exec` denied (macOS Seatbelt / Linux
//! seccomp+Landlock; `sel4/dregg-firmament/src/sandbox.rs`) — and hands back the
//! parent-side [`JailChannel`]. A [`ConfinedBrain`](crate::ConfinedBrain) drives
//! that channel EXACTLY as it drives an in-process one; the only difference is
//! the body is now an OS-jailed subprocess whose sole channel is the socketpair.
//!
//! The body runs as a Rust closure inside the jail (the jail denies `execve`, so
//! it cannot be an arbitrary external binary — that needs a granted exec-door, a
//! later slice; the confined-Rust-harness-plus-granted-egress body is the shape
//! for an LLM-driven agent). Its authority over the grain is still exactly the
//! grain's caps — the jail is the *ambient* floor beneath the cap gate, closing
//! the case where an untrusted body ignores the cap system and makes raw
//! syscalls.

use std::io::BufReader;
use std::os::unix::net::UnixStream;
use std::time::Duration;

use dregg_firmament::process_kernel::{PdProcess, ProcessKernel};

use crate::LineChannel;

/// The parent-side channel to a jailed body: the confined-body line protocol
/// over the process-PD's surface socketpair. Drive it with a
/// [`ConfinedBrain`](crate::ConfinedBrain).
pub type JailChannel = LineChannel<BufReader<UnixStream>, UnixStream>;

/// A running jailed body. [`join`](JailedBody::join) waits for it and returns its
/// exit code (`0` = clean; the firmament `CONFINE_FAILED_EXIT` = 99 means the
/// sandbox could not be applied and the body never ran — fail-closed).
pub struct JailedBody {
    pd: PdProcess,
}

impl JailedBody {
    /// Wait for the jailed body to exit; returns its exit code.
    pub fn join(self) -> std::io::Result<i32> {
        self.pd.join()
    }

    /// SIGKILL the jailed body, then reap it — for a body that HANGS (never
    /// sends, or loops forever). A confined body cannot be trusted to exit; when
    /// the drive ends on a read timeout the host kills it rather than block on
    /// [`join`](JailedBody::join) forever. Returns the reaped exit status.
    pub fn kill(self) -> std::io::Result<i32> {
        // The child is jailed (only its endpoint socket), so a plain SIGKILL to
        // its pid is sufficient and cannot touch anything else.
        unsafe {
            libc::kill(self.pd.pid, libc::SIGKILL);
        }
        self.pd.join()
    }
}

/// Spawn `body` as an OS-jailed subprocess speaking the confined-body line
/// protocol over a socketpair, returning the jailed handle plus the parent-side
/// [`JailChannel`] to drive with a [`ConfinedBrain`](crate::ConfinedBrain).
///
/// `body` runs INSIDE the jail with its end of the socketpair (a [`UnixStream`]).
/// It should keep post-fork work minimal (the process is forked without `exec`):
/// pre-serialize anything heavy in the parent and capture it. Confinement is
/// applied before `body` runs; if it cannot be applied the child exits
/// fail-closed without running `body`.
pub fn spawn_confined_body<F>(
    kernel: &ProcessKernel,
    body: F,
) -> std::io::Result<(JailedBody, JailChannel)>
where
    F: FnOnce(UnixStream) -> i32,
{
    spawn_confined_body_with_timeout(kernel, None, body)
}

/// Like [`spawn_confined_body`], but with a per-read TIMEOUT on the parent's
/// channel: if the body does not send its next message within `read_timeout`,
/// the channel's `recv` returns a timeout error, which the
/// [`ConfinedBrain`](crate::ConfinedBrain) treats as end-of-drive (fail-closed).
///
/// A confined body cannot be trusted to make progress — a hung or wedged body
/// must not block the grain forever. Pair this with
/// [`JailedBody::kill`](JailedBody::kill) to reap a body that timed out. `None`
/// (the [`spawn_confined_body`] default) blocks indefinitely, for a fully-trusted
/// or test body.
pub fn spawn_confined_body_with_timeout<F>(
    kernel: &ProcessKernel,
    read_timeout: Option<Duration>,
    body: F,
) -> std::io::Result<(JailedBody, JailChannel)>
where
    F: FnOnce(UnixStream) -> i32,
{
    let (pd, parent) = kernel
        .spawn_pd_confined_with_surface(vec![], move |_client, surf, _granted| body(surf))
        .map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("firmament confined spawn failed: {e:?}"),
            )
        })?;
    let reader_stream = parent.try_clone()?;
    // The timeout gates the READ side (waiting on the body's next message); the
    // write side (verdicts) is never blocked by the body.
    reader_stream.set_read_timeout(read_timeout)?;
    let channel = LineChannel::new(BufReader::new(reader_stream), parent);
    Ok((JailedBody { pd }, channel))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ConfinedBrain;
    use crate::protocol::{BodyMsg, DoneNote, Proposal};
    use dregg_agent::agent::{ActionObservation, AgentAction, AgentBrain};
    use std::io::{BufRead, Write};

    /// The exit code the jailed body returns if it could open a host file it must
    /// not be able to (a confinement LEAK — the jail failed to deny file reads).
    const CONFINE_LEAK: i32 = 77;
    /// The body returns this if the protocol I/O over the socket faulted.
    const PROTOCOL_FAULT: i32 = 66;

    /// A real firmament-jailed body drives a `ConfinedBrain` over a socketpair,
    /// AND the jail denies it a host-file read. Proves the confined-body seam
    /// works over a genuine OS-jail with the ambient confinement enforced.
    #[test]
    fn jailed_body_drives_the_brain_and_cannot_open_host_files() {
        // Pre-serialize the body's outgoing lines IN THE PARENT so the post-fork
        // child does no serde allocation — one proposal per admitted step, then
        // Done. (Fork-without-exec: keep the child's work minimal.)
        let lines: Vec<Vec<u8>> = [
            BodyMsg::Propose(Proposal::invoke("a")),
            BodyMsg::Propose(Proposal::invoke("b")),
            BodyMsg::Done(DoneNote::default()),
        ]
        .iter()
        .map(|m| {
            let mut s = serde_json::to_string(m).unwrap();
            s.push('\n');
            s.into_bytes()
        })
        .collect();
        let n_proposals = lines.len() - 1; // last line is Done (no verdict follows)

        let kernel = ProcessKernel::new();
        let (handle, channel) = spawn_confined_body(&kernel, move |surf| {
            // IN THE JAIL. Ambient-confinement tooth: a host file read is DENIED.
            if std::fs::File::open("/etc/passwd").is_ok() {
                return CONFINE_LEAK;
            }
            let mut w = match surf.try_clone() {
                Ok(w) => w,
                Err(_) => return PROTOCOL_FAULT,
            };
            let mut r = BufReader::new(surf);
            for (i, line) in lines.iter().enumerate() {
                if w.write_all(line).and_then(|_| w.flush()).is_err() {
                    return PROTOCOL_FAULT;
                }
                // Read the host's verdict after each PROPOSAL (not after Done).
                if i < n_proposals {
                    let mut discard = String::new();
                    if r.read_line(&mut discard).map(|n| n == 0).unwrap_or(true) {
                        return PROTOCOL_FAULT;
                    }
                }
            }
            0
        })
        .expect("spawn the jailed body");

        // Drive the jailed body over the real socket with a ConfinedBrain.
        let mut brain = ConfinedBrain::new(channel);

        assert_eq!(
            brain.next_action(0),
            Some(AgentAction::Invoke {
                service: "a".into()
            }),
            "the jailed body's first proposal crossed the jail socket and mapped"
        );
        brain.observe(&ActionObservation {
            action: "invoke:a".into(),
            admitted: true,
            refusal: None,
            tool_ok: Some(true),
            tool_summary: None,
        });
        assert_eq!(
            brain.next_action(1),
            Some(AgentAction::Invoke {
                service: "b".into()
            })
        );
        brain.observe(&ActionObservation {
            action: "invoke:b".into(),
            admitted: false,
            refusal: Some("no cap".into()),
            tool_ok: None,
            tool_summary: None,
        });
        // Done → the drive ends.
        assert_eq!(brain.next_action(2), None);

        let code = handle.join().expect("join the jailed body");
        assert_eq!(
            code, 0,
            "the jailed body completed the protocol AND could not open /etc/passwd \
             (code {CONFINE_LEAK} would be a confinement leak, {PROTOCOL_FAULT} an I/O fault)"
        );
    }

    /// A jailed body that HANGS (never sends, holds its socket open) does NOT
    /// wedge the host: the channel's read timeout ends the drive fail-closed, the
    /// brain records the timeout, and the body is reaped by SIGKILL rather than a
    /// join that would block forever.
    #[test]
    fn a_hung_body_times_out_and_is_reaped_not_wedging_the_host() {
        use std::time::{Duration, Instant};

        let kernel = ProcessKernel::new();
        let (handle, channel) =
            spawn_confined_body_with_timeout(&kernel, Some(Duration::from_millis(300)), |surf| {
                // Hang: keep the socket open (so the parent's read blocks, not
                // EOFs) and never send. SIGKILL will end this.
                let _keep = surf;
                std::thread::sleep(Duration::from_secs(30));
                0
            })
            .expect("spawn the hung body");

        let mut brain = ConfinedBrain::new(channel);
        let start = Instant::now();
        // The host waits at most ~the timeout, then gives up — it does NOT block
        // on the hung body.
        assert_eq!(brain.next_action(0), None, "a hung body yields no action");
        assert!(
            brain.timed_out(),
            "the drive ended on the read timeout (a hung body), not a clean exit"
        );
        assert!(
            start.elapsed() < Duration::from_secs(5),
            "the host did not block waiting on the hung body (elapsed {:?})",
            start.elapsed()
        );

        // Reap the hung body — `join` alone would block forever; `kill` SIGKILLs
        // then reaps. This must return, not hang.
        let _status = handle.kill().expect("kill + reap the hung body");
    }
}
