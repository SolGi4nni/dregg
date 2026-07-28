//! THE SHIPPED SUBMITTER, SPAWNED — not a library call standing in for it.
//!
//! `PrivateBazaarSealedIngressQueue::submit` documented itself "THE PRODUCTION
//! INGRESS" while having, measured 2026-07-28, **0 production callers and 11 test
//! callers** — and the supervisor mounted by `dreggnet-web-server` drained that
//! queue on every tick. `dregg-private-bazaar-submit` is the caller that closes
//! it, and a caller that only ever runs as a library function inside a test is
//! the same wound one level up. So this file runs the real executable, over a
//! real pipe, and checks what it left behind.
//!
//! WHAT EACH LEG PROVES, because no one of them is the whole claim:
//!
//! * HERE: the shipped `main` — stdin, exit codes, no secret in the operator's
//!   scrollback, and a durably chained record whose reopen re-validates schema,
//!   checksum, scope, sequence, predecessor link, the proved-family type gate and
//!   the deployment roster. It deliberately does NOT reach `next_pending`, which
//!   is `pub(crate)`; widening a drain-side API so a test can peek would be a
//!   worse trade than the coverage is worth.
//! * `private_bazaar_live::tests::\
//!   the_deployed_supervisor_clears_a_submitted_sealed_book_end_to_end`: the same
//!   `submit_sealed_book_document` entry this binary is a shell around, with the
//!   exact `(bidder, limit, blind)` decoded back out of the record — and then
//!   queue → supervisor → a verified `HidingFriPcs` proof of the Lean-emitted
//!   `N=4,K=4` descriptor → the executor SETTLE → the pinned game consequence.
//!
//! SUBSTRATE, out loud: nothing here authors a constraint. The AIR is
//! Lean-authored (`metatheory/Market/DarkBazaarPrivateDescriptor.lean` → the
//! emitted `dark-bazaar-private-n4k4.json`); this is transport wiring only, and
//! it mints no proof at all.

#![cfg(feature = "private-bazaar-live")]

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use dregg_app_framework::{CellId, symbol};
use dreggnet_catalog::private_bazaar_live::{
    PRIVATE_BAZAAR_AUTHORITY_DIR_ENV, PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV,
    PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV, PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV,
    PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV, PRIVATE_BAZAAR_RESERVE_ENV,
    PRIVATE_BAZAAR_REWARD_AMOUNT_ENV, PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV,
    PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV, PRIVATE_BAZAAR_REWARD_KIND_ENV,
    PRIVATE_BAZAAR_REWARD_METHOD_ENV, PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV,
    PRIVATE_BAZAAR_ROSTER_ENV, PrivateBazaarLiveDeployment,
};
use dreggnet_market::private_bazaar_journey::PrivateBazaarRaidPolicy;
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_offerings::DreggIdentity;
use dungeon_on_dregg::progression::{PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD};

const LOW_BIDDER: &str = "submitter-low-bidder";
const WINNER: &str = "submitter-winner";
const SELLER: &str = "submitter-seller";

fn hex(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// The EXACT environment a deployment host exports, built the way the deployment
/// itself derives its pins — so the child process and the in-process reader below
/// resolve one deployment, not two that happen to agree.
fn deployment_env(authority: &Path) -> BTreeMap<&'static str, String> {
    let roster = GuildRoster::new(vec![
        GuildMember::new(DreggIdentity(SELLER.to_owned()), CellId([0x41; 32])),
        GuildMember::new(DreggIdentity(LOW_BIDDER.to_owned()), CellId([0x42; 32])),
        GuildMember::new(DreggIdentity(WINNER.to_owned()), CellId([0x43; 32])),
    ])
    .expect("fixed roster");
    let reward = GuildReward::new("raid-xp/submitter-binary/v1", 144).expect("fixed reward");
    BTreeMap::from([
        (PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV, hex(&[0x11; 32])),
        (
            PRIVATE_BAZAAR_ROSTER_ENV,
            format!(
                "{SELLER}={};{LOW_BIDDER}={};{WINNER}={}",
                hex(&[0x41; 32]),
                hex(&[0x42; 32]),
                hex(&[0x43; 32])
            ),
        ),
        (PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV, hex(&roster.digest())),
        (PRIVATE_BAZAAR_REWARD_KIND_ENV, reward.kind.clone()),
        (PRIVATE_BAZAAR_REWARD_AMOUNT_ENV, "144".to_owned()),
        (
            PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV,
            hex(&PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward)),
        ),
        (
            PRIVATE_BAZAAR_REWARD_METHOD_ENV,
            PRIVATE_BAZAAR_XP_METHOD.to_owned(),
        ),
        (
            PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV,
            hex(&symbol(PRIVATE_BAZAAR_XP_EVENT)),
        ),
        (PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV, hex(&[0x22; 32])),
        (PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV, hex(&[0x33; 32])),
        (PRIVATE_BAZAAR_RESERVE_ENV, "1".to_owned()),
        (
            PRIVATE_BAZAAR_AUTHORITY_DIR_ENV,
            authority.display().to_string(),
        ),
        (
            PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV,
            // Submitting never signs; the loader only requires the handle be
            // named, so custody stays with the process that actually settles.
            "/not-opened-by-the-submitter".to_owned(),
        ),
    ])
}

struct Ran {
    code: i32,
    stdout: String,
    stderr: String,
}

/// Spawn the real executable with `document` on stdin.
fn submit(env: &BTreeMap<&'static str, String>, document: &str) -> Ran {
    let mut child = Command::new(env!("CARGO_BIN_EXE_dregg-private-bazaar-submit"))
        .env_clear()
        // PATH only; the deployment is resolved wholly from the pins below.
        .env("PATH", std::env::var("PATH").unwrap_or_default())
        .envs(env.iter().map(|(name, value)| (*name, value.as_str())))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the shipped submitter executes");
    child
        .stdin
        .as_mut()
        .expect("piped stdin")
        .write_all(document.as_bytes())
        .expect("the book is written to the pipe");
    let out = child.wait_with_output().expect("the submitter exits");
    Ran {
        code: out.status.code().expect("a normal exit, not a signal"),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

fn reader(env: &BTreeMap<&'static str, String>) -> PrivateBazaarLiveDeployment {
    PrivateBazaarLiveDeployment::from_config_source(|name| env.get(name).cloned())
        .expect("the same pins resolve")
        .expect("a configured deployment")
}

/// A BOOK PIPED INTO THE SHIPPED BINARY BECOMES THE EXACT DURABLE RECORD.
///
/// Asserted on the decoded VALUE — the bidders, the limits and the blind read
/// back out of the queue file — not on "the process exited 0".
#[test]
fn the_shipped_submitter_puts_the_exact_book_on_the_queue_the_supervisor_drains() {
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let env = deployment_env(&temp.path().join("authority"));

    // Nothing queued before the operator runs anything.
    assert_eq!(
        reader(&env)
            .private_sealed_ingress()
            .expect("queue opens")
            .pending()
            .expect("depth"),
        0
    );

    let ran = submit(
        &env,
        &format!(
            "# the operator's out-of-band sealed book\n\
             seed 0xB42AC1\n\
             \n\
             bid {LOW_BIDDER}=2   # the low bid\n\
             bid {WINNER}=3\n\
             blinding 001157f1001157f1001157f1001157f1001157f1001157f1001157f1001157f1\n"
        ),
    );
    assert_eq!(
        ran.code,
        0,
        "the submitter must accept an in-family book: {ran:?}",
        ran = (&ran.stdout, &ran.stderr)
    );
    assert!(
        ran.stdout.contains("accepted at sequence 1")
            && ran.stdout.contains("1 submission(s) queued"),
        "{:?}",
        ran.stdout
    );

    // ⚑ AND NOT ONE SECRET IN THE OPERATOR'S SCROLLBACK. The queue's whole
    // confidentiality boundary is 0600-under-the-authority-directory; a limit
    // echoed to a terminal walks straight back out of it.
    for secret in [LOW_BIDDER, WINNER, "001157f1"] {
        assert!(
            !ran.stdout.contains(secret) && !ran.stderr.contains(secret),
            "the submitter must report counts only, but leaked {secret:?}: \
             stdout={:?} stderr={:?}",
            ran.stdout,
            ran.stderr
        );
    }

    // THE DURABLE RESULT, read by the same reader the supervisor uses. Opening
    // the queue re-validates the whole chain — schema, checksum, scope, sequence,
    // the link to each physical predecessor, the proved-family type gate and the
    // deployment roster — so a depth of 1 here is a record that passed all of
    // them, not merely 770 bytes on a disk.
    let deployment = reader(&env);
    assert_eq!(
        deployment
            .private_sealed_ingress()
            .expect("the chain revalidates on open")
            .pending()
            .expect("depth"),
        1
    );

    // Exactly ONE fixed-width record was appended, at the pinned 770-byte length
    // (`private_bazaar_ingress::tests::the_ingress_record_length_is_pinned`), mode
    // 0600 — the file the queue's confidentiality boundary is stated in terms of.
    let record = queue_file(&temp.path().join("authority"));
    assert_eq!(record.len(), 770, "one pinned-width ingress record");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(record.path)
            .expect("stat")
            .permissions()
            .mode()
            & 0o777;
        assert_eq!(mode, 0o600, "the queue file must stay operator-private");
    }

    // A second run CHAINS rather than replacing, and the chain still validates.
    let again = submit(&env, &format!("seed 0xB42AC2\nbid {WINNER}=1\n"));
    assert_eq!(again.code, 0, "{:?}", again.stderr);
    assert!(
        again.stdout.contains("accepted at sequence 2") && again.stdout.contains("2 submission(s)"),
        "{:?}",
        again.stdout
    );
    assert_eq!(
        deployment
            .private_sealed_ingress()
            .expect("the two-record chain revalidates")
            .pending()
            .expect("depth"),
        2
    );
    assert_eq!(queue_file(&temp.path().join("authority")).len(), 1540);
}

struct QueueFile {
    path: std::path::PathBuf,
    bytes: u64,
}

impl QueueFile {
    fn len(&self) -> u64 {
        self.bytes
    }
}

/// The one queue file under the deployment's private-ingress root. Found rather
/// than named: the file name is the module's private business.
fn queue_file(authority: &Path) -> QueueFile {
    let root = authority.join("private-ingress");
    let mut found: Vec<_> = std::fs::read_dir(&root)
        .expect("the private-ingress root exists once a book is queued")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "queue"))
        .collect();
    assert_eq!(
        found.len(),
        1,
        "exactly one sealed-ingress queue: {found:?}"
    );
    let path = found.remove(0);
    let bytes = std::fs::metadata(&path).expect("stat the queue").len();
    QueueFile { path, bytes }
}

/// EVERY REFUSAL POLE, THROUGH THE SHIPPED BINARY, LEAVING NOTHING DURABLE.
///
/// The refusals are the QUEUE's, by its own name and naming the exact limit —
/// the submitter deliberately re-implements no gate, so there is no second
/// opinion here that could drift from the one the decoder re-runs.
#[test]
fn the_shipped_submitter_refuses_by_name_and_writes_nothing() {
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let env = deployment_env(&temp.path().join("authority"));

    for (document, expected) in [
        (
            format!("seed 1\nbid {WINNER}=4\n"),
            "bid limit 4 is outside the proved price family 0..4",
        ),
        (
            format!("seed 1\nbid {WINNER}=-1\n"),
            "bid limit -1 is outside the proved price family",
        ),
        (
            format!("seed 1\nbid {SELLER}=0\nbid {LOW_BIDDER}=1\nbid {WINNER}=2\nbid {SELLER}=3\n"),
            "4 sealed bids exceeds PROVEN_MAX_SEALED_BIDS = 3",
        ),
        (
            "seed 1\nbid nobody-on-this-roster=3\n".to_owned(),
            "outside the deployment's immutable policy roster",
        ),
        (
            format!("seed 1\nbid {WINNER}=2\nbid {WINNER}=3\n"),
            "repeats a roster member already bidding in this book",
        ),
        (
            "seed 1\n".to_owned(),
            "an empty book has no clearing to prove",
        ),
        (format!("bid {WINNER}=3\n"), "no `seed` directive"),
        (
            format!("seed 1\nbids {WINNER}=3\n"),
            "line 2 is not one of `seed`, `bid`, `blinding`",
        ),
    ] {
        let ran = submit(&env, &document);
        assert_eq!(
            ran.code, 1,
            "a refusal must exit 1: {:?} / {:?}",
            ran.stdout, ran.stderr
        );
        assert!(
            ran.stderr.contains(expected),
            "the refusal must name the limit: expected {expected:?}, got {:?}",
            ran.stderr
        );
        assert!(ran.stdout.is_empty(), "a refusal prints no success line");
    }

    assert_eq!(
        reader(&env)
            .private_sealed_ingress()
            .expect("queue opens")
            .pending()
            .expect("depth"),
        0,
        "not one refused document may leave a durable trace"
    );
}

/// AN UNCONFIGURED HOST REFUSES DISTINCTLY — it does not invent a queue.
///
/// Exit 2, not 1: "there is nothing here to submit to" is an operator's
/// environment problem, and it must not read as "your book was rejected".
#[test]
fn an_unconfigured_environment_refuses_with_its_own_exit_code() {
    let ran = submit(&BTreeMap::new(), "seed 1\nbid someone=1\n");
    assert_eq!(ran.code, 2, "{:?}", ran.stderr);
    assert!(
        ran.stderr
            .contains("no private Bazaar deployment is configured"),
        "{:?}",
        ran.stderr
    );

    // And a HALF-configured host is a refusal too, never a healthy-looking
    // unmounted feature: the loader's partial-config rule reaches the binary.
    let partial = BTreeMap::from([(PRIVATE_BAZAAR_ROSTER_ENV, "someone=00".to_owned())]);
    let ran = submit(&partial, "seed 1\nbid someone=1\n");
    assert_eq!(ran.code, 2, "{:?}", ran.stderr);
    assert!(
        ran.stderr.contains(PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV),
        "{:?}",
        ran.stderr
    );
}
