//! End-to-end: a [`ConfinedBrain`] drives a REAL `agent-platform` grain.
//!
//! This is the load-bearing proof of the confined-body unification: a body that
//! speaks ONLY the line protocol (it never constructs an in-process
//! `AgentAction`) drives a real rented grain through its real lease, meter,
//! receipt, and R2 attestation machinery — with no change to the grain drive
//! path (the grain is driven exactly as it is with any other `AgentBrain`). The
//! OS-jail is then a swap of the channel's backing transport (an in-process
//! cursor here → a firmament endpoint fd), the seam unchanged.

use std::io::Cursor;

use agent_platform::AgentPlatform;
use dregg_types::CellId;
use grain_jail::protocol::{BodyMsg, DoneNote, Proposal};
use grain_jail::{ConfinedBrain, LineChannel};
use hosted_lease::LeaseTerms;

fn cid(n: u8) -> CellId {
    CellId::from_bytes([n; 32])
}

/// provider=2, lease cell=7, asset=9; rent 100 every 50 blocks from 1000.
fn terms() -> LeaseTerms {
    LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
}

fn workdir() -> String {
    let p = std::env::temp_dir().join(format!(
        "grain-jail-e2e-{}-{}",
        std::process::id(),
        // a cheap per-test suffix so the two tests never share a workdir
        line!()
    ));
    std::fs::create_dir_all(&p).unwrap();
    p.to_str().unwrap().to_string()
}

/// Frame a confined body's script (proposals, then a `Done`) into the ndjson the
/// `ConfinedBrain` reads, capturing the host's verdicts into the writer half.
fn body_script(msgs: &[BodyMsg]) -> LineChannel<Cursor<Vec<u8>>, Vec<u8>> {
    let mut buf = String::new();
    for m in msgs {
        buf.push_str(&serde_json::to_string(m).unwrap());
        buf.push('\n');
    }
    LineChannel::new(Cursor::new(buf.into_bytes()), Vec::new())
}

fn cell_write(path: &str, value: &str) -> BodyMsg {
    BodyMsg::Propose(Proposal {
        tool: "cell-write".into(),
        args: None,
        amount_cents: None,
        path: Some(path.into()),
        value: Some(value.into()),
    })
}

/// A confined body proposes two cell-writes over the wire; the real grain admits,
/// meters, and receipts each; R2 verifies every receipt is a view over a turn the
/// real executor committed; a forged manifest is refused.
#[test]
fn confined_brain_drives_a_real_grain_metered_receipted_and_r2_verified() {
    let platform = AgentPlatform::new();
    let wd = workdir();

    // Rent a grain that may write two of its own cells (`cell:<path>` grants the
    // `cell-read:`/`cell-write:` pair per cell). A raw `shell` would be refused —
    // this is a hosted (confined) session.
    let host = platform
        .rent(
            "confined.agents.dregg",
            "dga1_confined",
            "cell:notes/1,cell:notes/2",
            10_000,
            &wd,
            terms(),
            None,
        )
        .expect("provision the confined grain");

    // The confined body: two cell-write proposals, then Done. It only ever
    // touches the line protocol — the `ConfinedBrain` translates each proposal
    // into the grain's `AgentAction` vocabulary at the seam.
    let body = body_script(&[
        cell_write("notes/1", "hello"),
        cell_write("notes/2", "grain"),
        BodyMsg::Done(DoneNote::default()),
    ]);
    let mut brain = ConfinedBrain::new(body);

    // Drive the REAL grain via the served R2 path (mints each admitted action
    // onto the grain's node as a committed kernel turn).
    let report = platform
        .drive_serving(&host, "write my notes", &mut brain)
        .expect("the confined brain drives the grain");
    assert_eq!(
        report.admitted, 2,
        "both confined cell-writes were admitted + receipted"
    );
    assert!(
        platform.consumed(&host).unwrap() > 0,
        "the lease meter drew down for the confined body's work"
    );

    // R0 — the whole session re-witnesses (chain + budget + durable-image bind).
    platform.verify(&host).expect("R0 re-witness");

    // R2 — every admitted receipt is a VIEW over a committed kernel turn.
    let r2 = platform.verify_r2(&host).expect("R2 verify");
    assert_eq!(
        r2.linked as u64, report.admitted,
        "every confined turn is a committed kernel turn"
    );

    // Anti-forgery: an attestation over the real session, checked against a
    // manifest naming turns never committed, trips the R2 tooth.
    let att = platform.attest(&host).expect("attest the confined grain");
    assert!(
        att.verify_r2(&[[0u8; 32]]).is_err(),
        "a forged manifest (turns never committed) fails R2"
    );
}

/// A confined body does REAL FILE WORK: it proposes an `fs_write` op (the shape
/// the grain's toolkit runs), the grain performs it host-side in the grain's
/// workdir, cap-gated by `fs` — the body itself never touches the filesystem, it
/// requests the write through the seam. The file lands and the turn verifies.
#[test]
fn a_confined_body_requests_real_file_work_through_the_seam() {
    let platform = AgentPlatform::new();
    let wd = workdir();

    // `fs` grants the operator fs tools (fs_write/fs_read/list_dir/mkdir).
    let host = platform
        .rent(
            "fsbody.agents.dregg",
            "dga1_fsbody",
            "fs",
            10_000,
            &wd,
            terms(),
            None,
        )
        .expect("provision");

    // The body proposes an fs_write op, then Done. (A raw shell would be refused;
    // fs_write is the confined file tool.)
    let body = body_script(&[
        BodyMsg::Propose(Proposal::op(
            "fs_write",
            [
                ("path".to_string(), "hello.txt".to_string()),
                (
                    "content".to_string(),
                    "written by a confined body".to_string(),
                ),
            ],
        )),
        BodyMsg::Done(DoneNote::default()),
    ]);
    let mut brain = ConfinedBrain::new(body);

    let report = platform
        .drive_serving(&host, "write a file", &mut brain)
        .expect("the confined body's fs_write drives the grain");
    assert_eq!(report.admitted, 1, "the fs_write op was admitted");

    // The grain performed the write host-side, in the grain's workdir.
    let written = std::fs::read_to_string(std::path::Path::new(&wd).join("hello.txt"))
        .expect("the grain wrote the file the confined body requested");
    assert_eq!(written, "written by a confined body");

    // And the turn verifies at R2.
    let r2 = platform.verify_r2(&host).expect("R2 verify");
    assert_eq!(r2.linked, 1);
}

/// THE COMPLETE MECHANIC: a REAL firmament-jailed body (OS-sandboxed, host-file
/// read denied) drives a REAL grain over a socketpair — the whole north star bar
/// the LLM: an OS-jailed body whose every action is cap-gated, metered,
/// receipted, and R2-verifiable by the renter. Run with `--features real-jail`.
#[cfg(feature = "real-jail")]
#[test]
fn a_real_jailed_body_drives_a_real_grain_and_the_renter_verifies_r2() {
    use grain_jail::jail::spawn_confined_body;

    let platform = AgentPlatform::new();
    let wd = workdir();
    let host = platform
        .rent(
            "jailed.agents.dregg",
            "dga1_jailed",
            "cell:notes/1,cell:notes/2",
            10_000,
            &wd,
            terms(),
            None,
        )
        .expect("provision the jailed grain");

    // The body's outgoing lines, pre-serialized in the parent (the post-fork
    // child does no serde alloc): two cell-writes, then Done.
    let lines: Vec<Vec<u8>> = [
        cell_write("notes/1", "hello-from-the-jail"),
        cell_write("notes/2", "still-jailed"),
        BodyMsg::Done(DoneNote::default()),
    ]
    .iter()
    .map(|m| {
        let mut s = serde_json::to_string(m).unwrap();
        s.push('\n');
        s.into_bytes()
    })
    .collect();
    let n_proposals = lines.len() - 1;

    let kernel = dregg_firmament::process_kernel::ProcessKernel::new();
    let (handle, channel) = spawn_confined_body(&kernel, move |surf| {
        use std::io::{BufRead, BufReader, Write};
        // The jail must deny a host-file read (ambient confinement tooth).
        if std::fs::File::open("/etc/passwd").is_ok() {
            return 77;
        }
        let mut w = match surf.try_clone() {
            Ok(w) => w,
            Err(_) => return 66,
        };
        let mut r = BufReader::new(surf);
        for (i, line) in lines.iter().enumerate() {
            if w.write_all(line).and_then(|_| w.flush()).is_err() {
                return 66;
            }
            if i < n_proposals {
                let mut discard = String::new();
                if r.read_line(&mut discard).map(|n| n == 0).unwrap_or(true) {
                    return 66;
                }
            }
        }
        0
    })
    .expect("spawn the jailed body");

    // Drive the REAL grain with the REAL jailed body. drive_serving pulls a
    // proposal off the jail socket, cap-gates + meters + mints it, and feeds the
    // verdict back — in lockstep with the confined child.
    let mut brain = ConfinedBrain::new(channel);
    let report = platform
        .drive_serving(&host, "write from the jail", &mut brain)
        .expect("the jailed body drives the grain");
    assert_eq!(report.admitted, 2, "both jailed cell-writes were admitted");

    // The renter verifies every jailed turn is a committed kernel turn.
    let r2 = platform
        .verify_r2(&host)
        .expect("R2 verify the jailed session");
    assert_eq!(r2.linked as u64, report.admitted);

    // The jailed body completed cleanly AND could not escape the sandbox.
    let code = handle.join().expect("join the jailed body");
    assert_eq!(
        code, 0,
        "the jailed body finished the drive and was denied /etc/passwd \
         (77 = confinement leak, 66 = I/O fault)"
    );
}

/// THE CAPSTONE (mock brain): a jailed body reads its instructions from a "model"
/// over its ONE granted egress door and relays them as proposals to a REAL grain
/// — the full "rent a coding agent" loop end to end. The body reaches ONLY the
/// model (egress-confined); everything the model asks flows through the grain's
/// cap-gate + meter + R2. A real LLM replaces the mock (reqwest-in-jail is the
/// documented follow-up; the live provider is broken in-env regardless).
#[cfg(feature = "real-jail")]
#[test]
fn a_jailed_body_driven_by_a_model_over_its_egress_door_runs_the_grain_r2() {
    use grain_jail::jail::spawn_confined_body_with_egress;
    use std::io::{BufRead, BufReader, Write};
    use std::net::{SocketAddr, TcpListener, TcpStream};
    use std::time::Duration;

    // The MOCK MODEL: on connect it pushes one proposal line (a cell-write the
    // "agent" decided) then DONE. (A real model would stream tool-calls here.)
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let model_addr: SocketAddr = listener.local_addr().unwrap();
    let proposal_line =
        serde_json::to_string(&cell_write("notes/1", "written via a model")).unwrap();
    std::thread::spawn(move || {
        if let Ok((mut sock, _)) = listener.accept() {
            let _ = writeln!(sock, "{proposal_line}");
            let _ = writeln!(sock, "DONE");
        }
    });

    let platform = AgentPlatform::new();
    let wd = workdir();
    let host = platform
        .rent(
            "model.agents.dregg",
            "dga1_model",
            "cell:notes/1",
            10_000,
            &wd,
            terms(),
            None,
        )
        .expect("provision");

    // The jailed body: granted egress to ONLY the model. It relays the model's
    // instruction lines to the grain over the surface socket (no serde in the
    // child — a pure byte relay), sending the pre-known Done on the model's DONE.
    let done_line = {
        let mut s = serde_json::to_string(&BodyMsg::Done(DoneNote::default())).unwrap();
        s.push('\n');
        s.into_bytes()
    };
    let kernel = dregg_firmament::process_kernel::ProcessKernel::new();
    let (handle, channel) = spawn_confined_body_with_egress(
        &kernel,
        vec![model_addr.to_string()],
        Some(Duration::from_secs(5)),
        move |surf| {
            let model = match TcpStream::connect_timeout(&model_addr, Duration::from_secs(2)) {
                Ok(m) => m,
                Err(_) => return 20, // could not reach the granted model door
            };
            let mut model_r = BufReader::new(model);
            let mut surf_w = match surf.try_clone() {
                Ok(w) => w,
                Err(_) => return 21,
            };
            let mut surf_r = BufReader::new(surf);
            loop {
                let mut line = String::new();
                match model_r.read_line(&mut line) {
                    Ok(0) | Err(_) => break, // model closed
                    Ok(_) => {}
                }
                let line = line.trim_end();
                if line == "DONE" {
                    if surf_w
                        .write_all(&done_line)
                        .and_then(|_| surf_w.flush())
                        .is_err()
                    {
                        return 22;
                    }
                    break;
                }
                // Relay the model's proposal to the grain, read the verdict.
                if surf_w
                    .write_all(line.as_bytes())
                    .and_then(|_| surf_w.write_all(b"\n"))
                    .and_then(|_| surf_w.flush())
                    .is_err()
                {
                    return 23;
                }
                let mut verdict = String::new();
                if surf_r
                    .read_line(&mut verdict)
                    .map(|n| n == 0)
                    .unwrap_or(true)
                {
                    return 24;
                }
            }
            0
        },
    )
    .expect("spawn the model-driven jailed body");

    let mut brain = ConfinedBrain::new(channel);
    let report = platform
        .drive_serving(&host, "do what the model says", &mut brain)
        .expect("the model-driven jailed body drives the grain");
    assert_eq!(
        report.admitted, 1,
        "the model's one instruction was admitted"
    );

    let r2 = platform.verify_r2(&host).expect("R2 verify");
    assert_eq!(
        r2.linked, 1,
        "the model-driven turn is a committed kernel turn"
    );

    let code = handle.join().expect("join the model-driven body");
    assert_eq!(
        code, 0,
        "the body relayed the model over its egress door cleanly \
         (20 = could not reach the granted model, 22/23/24 = surface I/O fault)"
    );
}

/// ROBUSTNESS: a jailed body that CRASHES mid-session (exits after one admitted
/// turn, never sending Done) leaves the grain in a clean, verifiable state — the
/// host is not corrupted by a hostile/faulty body. The drive ends fail-closed on
/// the socket EOF; the one committed turn still verifies at R2.
#[cfg(feature = "real-jail")]
#[test]
fn a_jailed_body_that_crashes_midway_leaves_the_grain_clean_and_verifiable() {
    use grain_jail::jail::spawn_confined_body;

    let platform = AgentPlatform::new();
    let wd = workdir();
    let host = platform
        .rent(
            "crashy.agents.dregg",
            "dga1_crashy",
            "cell:notes/1,cell:notes/2",
            10_000,
            &wd,
            terms(),
            None,
        )
        .expect("provision");

    // The body proposes ONE cell-write, reads its verdict, then EXITS 42 — a
    // crash mid-session (no Done, no second proposal).
    let line = {
        let mut s = serde_json::to_string(&cell_write("notes/1", "partial")).unwrap();
        s.push('\n');
        s.into_bytes()
    };
    let kernel = dregg_firmament::process_kernel::ProcessKernel::new();
    let (handle, channel) = spawn_confined_body(&kernel, move |surf| {
        use std::io::{BufRead, BufReader, Write};
        let mut w = surf.try_clone().unwrap();
        let mut r = BufReader::new(surf);
        if w.write_all(&line).and_then(|_| w.flush()).is_err() {
            return 66;
        }
        let mut discard = String::new();
        let _ = r.read_line(&mut discard); // read the verdict, then...
        42 // ...CRASH (exit non-zero without sending Done).
    })
    .expect("spawn the crashy body");

    let mut brain = ConfinedBrain::new(channel);
    // The drive ends cleanly when the body's socket hits EOF after one turn.
    let report = platform
        .drive_serving(&host, "one then crash", &mut brain)
        .expect("the drive survives a mid-session body crash");
    assert_eq!(
        report.admitted, 1,
        "exactly the one pre-crash turn was admitted"
    );

    // The grain is CONSISTENT and the one turn verifies — a crash cannot leave a
    // half-committed or unverifiable state.
    let r2 = platform
        .verify_r2(&host)
        .expect("R2 still holds after the crash");
    assert_eq!(r2.linked, 1);
    platform
        .verify(&host)
        .expect("R0 re-witness after the crash");

    let code = handle.join().expect("reap the crashed body");
    assert_eq!(
        code, 42,
        "the body did crash (non-zero) — the host absorbed it"
    );
}

/// The confined body's authority is exactly the grain's caps: a proposal for a
/// cell the grain was NOT granted is refused by the braid (no receipt, no meter
/// draw for it), and the drive continues to the granted write.
#[test]
fn confined_body_authority_never_exceeds_the_grain_caps() {
    let platform = AgentPlatform::new();
    let wd = workdir();

    // Granted ONE cell only.
    let host = platform
        .rent(
            "capped.agents.dregg",
            "dga1_capped",
            "cell:allowed",
            10_000,
            &wd,
            terms(),
            None,
        )
        .expect("provision");

    // The body proposes a write to an UNGRANTED cell, then a granted one.
    let body = body_script(&[
        cell_write("forbidden", "nope"),
        cell_write("allowed", "ok"),
        BodyMsg::Done(DoneNote::default()),
    ]);
    let mut brain = ConfinedBrain::new(body);

    let report = platform
        .drive_serving(&host, "try both", &mut brain)
        .expect("drive");

    // Exactly the granted write was admitted; the forbidden one was cap-refused.
    assert_eq!(
        report.admitted, 1,
        "only the granted cell-write was admitted — the confined body cannot exceed its caps"
    );
    assert!(
        report.cap_refused >= 1,
        "the ungranted write was refused by the braid, not silently dropped"
    );

    // R2 still holds over the one admitted turn.
    let r2 = platform.verify_r2(&host).expect("R2 verify");
    assert_eq!(r2.linked, 1);
}
