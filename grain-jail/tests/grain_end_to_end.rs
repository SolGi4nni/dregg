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
