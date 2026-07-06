//! `rent_a_confined_agent` — a runnable demo of the confined-body grain.
//!
//! Rent a grain, drive it with a body that speaks only the confined-body line
//! protocol, and watch every action get cap-gated, metered, minted as a
//! committed kernel turn, and verified (R2) by the renter.
//!
//! ```text
//! cargo run -p grain-jail --example rent_a_confined_agent
//! cargo run -p grain-jail --example rent_a_confined_agent --features real-jail
//! ```
//!
//! Without a feature the body runs in-process. With `--features real-jail` the
//! SAME body runs in a firmament OS-jail (macOS Seatbelt / Linux seccomp+
//! Landlock) — file/net/exec denied — and the drive is byte-for-byte the same,
//! because the jail is just a swap of the channel's backing transport.

use agent_platform::AgentPlatform;
use dregg_agent::agent::AgentBrain;
use dregg_types::CellId;
use grain_jail::ConfinedBrain;
use grain_jail::protocol::{BodyMsg, DoneNote, Proposal};
use hosted_lease::LeaseTerms;

fn cid(n: u8) -> CellId {
    CellId::from_bytes([n; 32])
}

/// The body's proposed work: write two of the grain's own cells, then finish.
fn body_script() -> Vec<BodyMsg> {
    vec![
        BodyMsg::Propose(Proposal {
            tool: "cell-write".into(),
            args: None,
            amount_cents: None,
            path: Some("notes/1".into()),
            value: Some("hello from a confined agent".into()),
        }),
        BodyMsg::Propose(Proposal {
            tool: "cell-write".into(),
            args: None,
            amount_cents: None,
            path: Some("notes/2".into()),
            value: Some("every turn is auditable".into()),
        }),
        BodyMsg::Done(DoneNote::default()),
    ]
}

/// Drive the grain with `brain`, then print what the renter can verify.
fn drive_and_report(platform: &AgentPlatform, host: &str, brain: &mut dyn AgentBrain) {
    let report = platform
        .drive_serving(host, "write my notes", brain)
        .expect("the confined body drives the grain");
    println!(
        "  the grain admitted {} action(s) — each cap-gated, metered, and minted \
         as a committed kernel turn",
        report.admitted
    );
    if report.cap_refused > 0 {
        println!(
            "  {} proposal(s) were cap-refused (the body cannot exceed its caps)",
            report.cap_refused
        );
    }
    println!(
        "  the lease meter drew down {} budget unit(s)",
        platform.consumed(host).unwrap()
    );

    let r2 = platform.verify_r2(host).expect("R2 verify");
    println!(
        "  R2: the renter verified {}/{} turns are views over committed kernel turns",
        r2.linked, report.admitted
    );
    let att = platform.attest(host).expect("attest");
    let forged_ok = att.verify_r2(&[[0u8; 32]]).is_ok();
    println!(
        "  anti-forgery: a manifest naming turns never committed is {}",
        if forged_ok {
            "ACCEPTED (BUG!)"
        } else {
            "refused"
        }
    );
}

fn main() {
    let platform = AgentPlatform::new();
    let wd = std::env::temp_dir().join(format!("confined-agent-demo-{}", std::process::id()));
    std::fs::create_dir_all(&wd).unwrap();

    // provider=2, lease cell=7, asset=9; rent 100 every 50 blocks from 1000.
    let terms = LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0);
    let host = platform
        .rent(
            "demo.agents.dregg",
            "dga1_demo",
            "cell:notes/1,cell:notes/2",
            10_000,
            wd.to_str().unwrap(),
            terms,
            None,
        )
        .expect("provision the confined grain");

    println!("rented a confined grain at `{host}`");
    println!(
        "  caps: cell:notes/1, cell:notes/2  (a raw `shell` would be refused — hosted session)"
    );

    #[cfg(not(feature = "real-jail"))]
    {
        use grain_jail::LineChannel;
        use std::io::Cursor;
        let mut buf = String::new();
        for m in body_script() {
            buf.push_str(&serde_json::to_string(&m).unwrap());
            buf.push('\n');
        }
        let channel = LineChannel::new(Cursor::new(buf.into_bytes()), Vec::new());
        let mut brain = ConfinedBrain::new(channel);
        println!("driving with an IN-PROCESS body over the line protocol...");
        drive_and_report(&platform, &host, &mut brain);
        println!("(rebuild with `--features real-jail` to run the SAME body OS-jailed)");
    }

    #[cfg(feature = "real-jail")]
    {
        use grain_jail::jail::spawn_confined_body_with_egress;
        use std::io::{BufRead, BufReader, Write};
        use std::net::{SocketAddr, TcpListener, TcpStream};
        use std::time::Duration;

        // THE MOCK MODEL — a stand-in for the agent's language model. On connect
        // it pushes the instructions the "agent" decided (here: write a cell),
        // then DONE. A real deployment points the granted door at a real provider
        // (or a trusted loopback proxy that does the TLS + provider call).
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock model");
        let model_addr: SocketAddr = listener.local_addr().unwrap();
        let instruction = serde_json::to_string(&body_script()[0]).unwrap();
        std::thread::spawn(move || {
            if let Ok((mut sock, _)) = listener.accept() {
                let _ = writeln!(sock, "{instruction}");
                let _ = writeln!(sock, "DONE");
            }
        });

        let done_line = {
            let mut s = serde_json::to_string(&grain_jail::protocol::BodyMsg::Done(
                grain_jail::protocol::DoneNote::default(),
            ))
            .unwrap();
            s.push('\n');
            s.into_bytes()
        };
        let kernel = dregg_firmament::process_kernel::ProcessKernel::new();
        let (handle, channel) = spawn_confined_body_with_egress(
            &kernel,
            vec![model_addr.to_string()], // the ONE door: the model, nothing else
            Some(Duration::from_secs(5)),
            move |surf| {
                // The jail tooth: a host-file read must be denied.
                if std::fs::File::open("/etc/passwd").is_ok() {
                    return 77;
                }
                // Reach the model over the ONE granted door; relay its
                // instructions to the grain over the surface socket.
                let model = match TcpStream::connect_timeout(&model_addr, Duration::from_secs(2)) {
                    Ok(m) => m,
                    Err(_) => return 20,
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
                        Ok(0) | Err(_) => break,
                        Ok(_) => {}
                    }
                    let line = line.trim_end();
                    if line == "DONE" {
                        let _ = surf_w.write_all(&done_line).and_then(|_| surf_w.flush());
                        break;
                    }
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
        .expect("spawn the OS-jailed, egress-confined, model-driven body");

        let mut brain = ConfinedBrain::new(channel);
        println!(
            "driving with an OS-JAILED, MODEL-DRIVEN body (firmament process-PD: file/exec denied, \
             net reaches ONLY the model)..."
        );
        drive_and_report(&platform, &host, &mut brain);
        let code = handle.join().expect("join the model-driven body");
        println!(
            "  the body consulted its model over its ONE granted door, was denied /etc/passwd, \
             and reached nothing else; exit {code} (77 = confinement leak, 20 = model unreachable)"
        );
    }

    println!(
        "\nA renter rented a confined agent, watched it work, and verified every action \
              against the chain — without trusting the host."
    );
}
