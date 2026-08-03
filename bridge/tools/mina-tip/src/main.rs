#![forbid(unsafe_code)]
//! `mina-tip` — dregg's Mina byte source, on the audited Rust stack.
//!
//! This is the transmutation of `bridge/tools/mina-besttip.py` and
//! `bridge/tools/mina-consecutive-pair.py`. Those were a small dependency-light
//! Python reimplementation of Mina's p2p transport. `mina-tip` instead LINKS
//! openmina (`~/dev/mina-rust`) — the maintained Rust implementation of the same
//! stack the Mina ecosystem runs — and issues real RPCs against a live devnet
//! seed:
//!
//!   * `besttip`  — `get_best_tip` v2, emit the tip's raw binprot
//!                  `Protocol_state.Value` to stdout. This is the exact contract
//!                  `bridge/src/mina_head.rs::CommandProtocolStateSource` speaks:
//!                  bytes on stdout, or a nonzero exit.
//!   * `pair`     — `get_best_tip` v2 for the child, then `get_transition_chain`
//!                  v2 for its parent, giving a genuine consecutive pair
//!                  (N -> N+1). Writes both protocol states as raw binprot.
//!   * `bestchain` — ⚑ THE CANDIDATE SET. Asks EACH peer separately for its own
//!                  best tip, and reads the half of the reply the other two
//!                  subcommands throw away: the transition-chain proof anchoring
//!                  that tip to the root of the serving peer's frontier. A tip
//!                  whose anchor does not fold is REFUSED and never enters the
//!                  set. Writes a bundle (see `bundle.rs`).
//!   * `verify-bestchain` — OFFLINE re-judgement of a bundle, and the RED path.
//!
//! ⚑ THE SEAM IS THE BYTES, AND ONLY THE BYTES MOVE. What comes out is the same
//! `Protocol_state.Value` binprot the Lean decoder (`Dregg2.Bridge.MinaBinprot`)
//! and the Lean selection rule (`Dregg2.Bridge.MinaForkChoiceGate`) already
//! consume, unchanged. `mina-tip` decides NOTHING about which chain to accept;
//! like the Python helper it replaced, it is trusted for AVAILABILITY ONLY — the
//! worst a hostile or broken peer achieves is to be refused by the Lean decoder,
//! or to withhold. What it removes is the "small Python client" asterisk: the
//! bytes now come off the same Rust node Mina's own ecosystem runs.

mod behaviour;
mod bundle;
mod chain;
mod client;

use std::io::Write as _;
use std::path::PathBuf;
use std::time::Duration;

use behaviour::Behaviour;
use client::Client;
use libp2p::Multiaddr;
use libp2p_rpc_behaviour::BehaviourBuilder;
use mina_p2p_messages::binprot::{BinProtRead, BinProtWrite};
use mina_p2p_messages::hash::MinaHash;
use mina_p2p_messages::list::List;
use mina_p2p_messages::rpc::{GetBestTipV2, GetTransitionChainV2};
use mina_p2p_messages::v2;

use bundle::BundleEntry;
use chain::{verify_anchor, BestTipWithProof};

/// The devnet chain-id string, exactly as openmina hands it to the transport:
/// the pnet pre-shared key is `Blake2b256(this string's bytes)`
/// (`mina_transport::swarm`), matching the Python helper's
/// `blake2b256("/coda/0.0.1/" + hex(chain_id))`.
const DEVNET_CHAIN_ID: &str =
    "/coda/0.0.1/29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6";

/// Devnet seed peers, copied from `mina_core::network::devnet::default_peers()`
/// (`~/dev/mina-rust/crates/core/src/network.rs`). Full multiaddrs incl. peer id
/// so libp2p's Noise handshake can authenticate the remote static key.
const DEVNET_SEEDS: &[&str] = &[
    "/dns4/seed-1.devnet.gcp.o1test.net/tcp/10003/p2p/12D3KooWAdgYL6hv18M3iDBdaK1dRygPivSfAfBNDzie6YqydVbs",
    "/dns4/seed-2.devnet.gcp.o1test.net/tcp/10003/p2p/12D3KooWLjs54xHzVmMmGYb7W5RVibqbwD1co7M2ZMfPgPm7iAag",
    "/dns4/seed-3.devnet.gcp.o1test.net/tcp/10003/p2p/12D3KooWEiGVAFC7curXWXiGZyMWnZK9h8BKr88U8D5PKV3dXciv",
];

struct Opts {
    cmd: Cmd,
    timeout: Duration,
    peers: Vec<Multiaddr>,
    parent_out: Option<String>,
    child_out: Option<String>,
    parent_in: Option<String>,
    child_in: Option<String>,
    dir: Option<PathBuf>,
    self_test: bool,
}

enum Cmd {
    /// Emit the best tip's `Protocol_state.Value` binprot to stdout.
    BestTip,
    /// Fetch a consecutive (parent, child) pair; write both protocol states.
    Pair,
    /// OFFLINE: decode two captured protocol states and check they are a
    /// genuine consecutive pair — heights differ by 1 and the parent hashes
    /// (openmina's own Poseidon) to the child's `previous_state_hash`.
    VerifyPair,
    /// ⚑ THE CANDIDATE SET. Ask EACH peer separately for its own best tip and
    /// verify the transition-chain proof that anchors it to that peer's frontier
    /// root. Write an anchored-candidate bundle.
    BestChain,
    /// OFFLINE: re-judge a bundle. `--self-test` drives the red legs.
    VerifyBestChain,
}

fn usage() -> ! {
    eprintln!(
        "mina-tip — openmina-sourced Mina byte emitter (devnet)\n\
         \n\
         USAGE:\n\
         \x20 mina-tip besttip [--timeout SECS] [--peer MULTIADDR]...\n\
         \x20     -> raw binprot Protocol_state.Value on stdout\n\
         \x20 mina-tip pair --parent-out P --child-out C [--timeout SECS] [--peer MULTIADDR]...\n\
         \x20     -> two raw binprot Protocol_state.Value files (heights N and N+1)\n\
         \x20 mina-tip verify-pair --parent P --child C   (OFFLINE)\n\
         \x20     -> decode both, assert height+1 and parent-hash == child.previous_state_hash\n\
         \x20 mina-tip bestchain --dir DIR [--timeout SECS] [--peer MULTIADDR]...\n\
         \x20     -> ask EACH peer for ITS best tip; verify the transition-chain proof\n\
         \x20        anchoring that tip to the peer's frontier root; write the\n\
         \x20        anchor-verified candidate SET as a bundle in DIR\n\
         \x20 mina-tip verify-bestchain --dir DIR [--self-test]   (OFFLINE)\n\
         \x20     -> re-judge every anchor in a bundle from its bytes; --self-test\n\
         \x20        additionally requires five forgeries to be REFUSED\n\
         \n\
         Default peers are the three devnet seeds. Default timeout is 120s.\n\
         The chain-id is the public devnet constant; no key or credential is used."
    );
    std::process::exit(2);
}

fn parse_args() -> Opts {
    let mut args = std::env::args().skip(1);
    let cmd = match args.next().as_deref() {
        Some("besttip") => Cmd::BestTip,
        Some("pair") => Cmd::Pair,
        Some("verify-pair") => Cmd::VerifyPair,
        Some("bestchain") => Cmd::BestChain,
        Some("verify-bestchain") => Cmd::VerifyBestChain,
        Some("-h") | Some("--help") | None => usage(),
        Some(other) => {
            eprintln!("mina-tip: unknown subcommand {other:?}");
            usage();
        }
    };
    let mut timeout = Duration::from_secs(120);
    let mut peers = Vec::new();
    let mut parent_out = None;
    let mut child_out = None;
    let mut parent_in = None;
    let mut child_in = None;
    let mut dir = None;
    let mut self_test = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--timeout" => {
                let s = args.next().unwrap_or_else(|| usage());
                timeout = Duration::from_secs(s.parse().unwrap_or_else(|_| usage()));
            }
            "--peer" => peers.push(
                args.next()
                    .unwrap_or_else(|| usage())
                    .parse()
                    .unwrap_or_else(|e| {
                        eprintln!("mina-tip: bad --peer multiaddr: {e}");
                        std::process::exit(2);
                    }),
            ),
            "--parent-out" => parent_out = Some(args.next().unwrap_or_else(|| usage())),
            "--child-out" => child_out = Some(args.next().unwrap_or_else(|| usage())),
            "--parent" => parent_in = Some(args.next().unwrap_or_else(|| usage())),
            "--child" => child_in = Some(args.next().unwrap_or_else(|| usage())),
            "--dir" => dir = Some(PathBuf::from(args.next().unwrap_or_else(|| usage()))),
            "--self-test" => self_test = true,
            other => {
                eprintln!("mina-tip: unexpected argument {other:?}");
                usage();
            }
        }
    }
    if peers.is_empty() {
        peers = DEVNET_SEEDS.iter().map(|s| s.parse().unwrap()).collect();
    }
    Opts {
        cmd,
        timeout,
        peers,
        parent_out,
        child_out,
        parent_in,
        child_in,
        dir,
        self_test,
    }
}

/// Build a swarm over openmina's real Mina transport, wrapped in a `Client`.
fn connect(peers: Vec<Multiaddr>) -> Client {
    let local_key = mina_transport::generate_identity();
    log::info!("local peer id {}", local_key.public().to_peer_id());
    let identify = libp2p::identify::Behaviour::new(libp2p::identify::Config::new(
        "ipfs/0.1.0".into(),
        local_key.public(),
    ));
    let rpc = BehaviourBuilder::default().build();
    let behaviour = Behaviour { rpc, identify };
    let swarm = mina_transport::swarm(
        local_key,
        DEVNET_CHAIN_ID.as_bytes(),
        std::iter::empty(),
        peers,
        behaviour,
    );
    Client::new(swarm)
}

/// openmina's own state hash for a protocol state, as a `StateHash` (Base58Check
/// `3N...`). Same derivation `record.rs` uses; here it is a capture-time
/// cross-check that the parent really hashes to the child's `previous_state_hash`.
fn state_hash(ps: &v2::MinaStateProtocolStateValueStableV2) -> v2::StateHash {
    let h = MinaHash::try_hash(ps).expect("protocol state hashes");
    v2::StateHash::from(v2::DataHashLibStateHashStableV1(h.into()))
}

fn height(ps: &v2::MinaStateProtocolStateValueStableV2) -> u32 {
    ps.body.consensus_state.blockchain_length.as_u32()
}

fn write_bytes(path: &str, ps: &v2::MinaStateProtocolStateValueStableV2) -> std::io::Result<usize> {
    let mut buf = Vec::new();
    ps.binprot_write(&mut buf).expect("binprot write");
    std::fs::write(path, &buf)?;
    Ok(buf.len())
}

#[tokio::main]
async fn main() {
    // env_logger: everything to STDERR, so stdout stays the clean byte channel.
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .target(env_logger::Target::Stderr)
        .init();

    let opts = parse_args();

    // `verify-pair` is OFFLINE — it never touches the network, so it does not
    // go through the connect/timeout path.
    if let Cmd::VerifyPair = opts.cmd {
        if let Err(e) = verify_pair(&opts) {
            eprintln!("mina-tip: {e}");
            std::process::exit(1);
        }
        return;
    }
    // `verify-bestchain` likewise. It is the gateable half: no network, no
    // archive, seconds, and it can go RED.
    if let Cmd::VerifyBestChain = opts.cmd {
        if let Err(e) = verify_bestchain(&opts) {
            eprintln!("mina-tip: {e}");
            std::process::exit(1);
        }
        return;
    }

    let result = tokio::time::timeout(opts.timeout, run(&opts)).await;
    match result {
        Ok(Ok(())) => {}
        Ok(Err(e)) => {
            eprintln!("mina-tip: {e}");
            std::process::exit(1);
        }
        Err(_) => {
            eprintln!(
                "mina-tip: timed out after {}s reaching a devnet seed",
                opts.timeout.as_secs()
            );
            std::process::exit(1);
        }
    }
}

/// OFFLINE consecutive-pair check, on openmina's decoders and hasher.
fn verify_pair(opts: &Opts) -> Result<(), Box<dyn std::error::Error>> {
    let parent_path = opts
        .parent_in
        .as_deref()
        .ok_or("verify-pair needs --parent PATH")?;
    let child_path = opts
        .child_in
        .as_deref()
        .ok_or("verify-pair needs --child PATH")?;

    let read_ps =
        |p: &str| -> Result<v2::MinaStateProtocolStateValueStableV2, Box<dyn std::error::Error>> {
            let bytes = std::fs::read(p)?;
            let mut slice = bytes.as_slice();
            let ps = v2::MinaStateProtocolStateValueStableV2::binprot_read(&mut slice)
                .map_err(|e| format!("{p}: binprot decode failed: {e}"))?;
            Ok(ps)
        };

    let parent_ps = read_ps(parent_path)?;
    let child_ps = read_ps(child_path)?;
    let parent_h = height(&parent_ps);
    let child_h = height(&child_ps);
    let parent_derived = state_hash(&parent_ps);

    let consecutive = parent_h + 1 == child_h;
    let linked = parent_derived == child_ps.previous_state_hash;
    eprintln!(
        "mina-tip: verify-pair (openmina decode + Poseidon, offline)\n\
         mina-tip:   parent block {parent_h}, derived state_hash {parent_derived}\n\
         mina-tip:   child  block {child_h}, previous_state_hash {}\n\
         mina-tip:   consecutive={consecutive} linked={linked}",
        child_ps.previous_state_hash
    );
    if consecutive && linked {
        // ⚑ THE DECIMALS ARE NOT DECORATION. `MinaForkChoiceGate.decodeSide?`
        // re-derives each side's state hash from its bytes and refuses the side
        // unless the `eh=`/`ch=` wire field equals it AS A DECIMAL `Nat`. A caller
        // holding only the Base58Check `3N…` form will be refused — and because
        // `"ERR"` renders as `KeepExisting`, that refusal is indistinguishable from
        // "the rule preferred the head". Printing them is how a fixture's consumer
        // gets the value the gate will actually accept.
        let pd = v2::DataHashLibStateHashStableV1(
            MinaHash::try_hash(&parent_ps)
                .expect("parent hashes")
                .into(),
        )
        .0
        .to_decimal();
        let cd = v2::DataHashLibStateHashStableV1(
            MinaHash::try_hash(&child_ps).expect("child hashes").into(),
        )
        .0
        .to_decimal();
        eprintln!("mina-tip:   parent state_hash (decimal, what the Lean gate wire takes): {pd}");
        eprintln!("mina-tip:   child  state_hash (decimal, what the Lean gate wire takes): {cd}");
        println!(
            "CONSECUTIVE PAIR {parent_h} -> {child_h}: deriveStateHash(parent) == child.previous_state_hash (openmina)"
        );
        Ok(())
    } else {
        Err(format!("not a consecutive pair (consecutive={consecutive}, linked={linked})").into())
    }
}

async fn run(opts: &Opts) -> Result<(), Box<dyn std::error::Error>> {
    // ⚑ `bestchain` does NOT share the single-connection path: the whole point is
    // to ask each peer SEPARATELY, so it opens one swarm per peer and attributes
    // each candidate to the peer that served it.
    if let Cmd::BestChain = opts.cmd {
        return bestchain(opts).await;
    }

    let mut client = connect(opts.peers.clone());

    // The tip (child). `get_best_tip` v2 -> Option<ProofCarryingData<Block, ..>>.
    let tip = client
        .rpc::<GetBestTipV2>(())
        .await?
        .ok_or("peer holds no best tip")?;
    let child_ps = tip.data.header.protocol_state.clone();
    let child_h = height(&child_ps);
    eprintln!(
        "mina-tip: get_best_tip v2 -> block {child_h}, state_hash {}",
        state_hash(&child_ps)
    );

    match opts.cmd {
        Cmd::BestTip => {
            let mut buf = Vec::new();
            child_ps.binprot_write(&mut buf).expect("binprot write");
            let mut out = std::io::stdout().lock();
            out.write_all(&buf)?;
            out.flush()?;
            eprintln!(
                "mina-tip: emitted {} bytes of Protocol_state.Value (openmina, block {child_h})",
                buf.len()
            );
            Ok(())
        }
        Cmd::Pair => {
            let parent_out = opts
                .parent_out
                .as_deref()
                .ok_or("pair needs --parent-out PATH")?;
            let child_out = opts
                .child_out
                .as_deref()
                .ok_or("pair needs --child-out PATH")?;

            // The parent, by the child's own `previous_state_hash`.
            let parent_hash = child_ps.previous_state_hash.clone();
            let blocks = client
                .rpc::<GetTransitionChainV2>(List::one(parent_hash.0.clone()))
                .await?
                .ok_or("peer served no block for the parent hash")?;
            let parent_block = blocks
                .into_iter()
                .next()
                .ok_or("get_transition_chain returned an empty list")?;
            let parent_ps = parent_block.header.protocol_state.clone();
            let parent_h = height(&parent_ps);

            // Capture-time cross-check, on openmina's OWN hasher: the parent must
            // hash to the child's previous_state_hash, and the heights differ by 1.
            let parent_derived = state_hash(&parent_ps);
            let consecutive = parent_h + 1 == child_h;
            let linked = parent_derived == child_ps.previous_state_hash;
            eprintln!(
                "mina-tip: parent block {parent_h}, state_hash {parent_derived}\n\
                 mina-tip: child.previous_state_hash {}\n\
                 mina-tip: consecutive={consecutive} linked={linked}",
                child_ps.previous_state_hash
            );
            if !consecutive || !linked {
                return Err(format!(
                    "not a genuine consecutive pair (consecutive={consecutive}, linked={linked})"
                )
                .into());
            }

            let pn = write_bytes(parent_out, &parent_ps)?;
            let cn = write_bytes(child_out, &child_ps)?;
            eprintln!(
                "mina-tip: wrote parent ({parent_h}, {pn} B) -> {parent_out}\n\
                 mina-tip: wrote child  ({child_h}, {cn} B) -> {child_out}"
            );
            Ok(())
        }
        // Handled before the network path is entered.
        Cmd::VerifyPair | Cmd::VerifyBestChain => {
            unreachable!("the offline subcommands are dispatched in main")
        }
        Cmd::BestChain => unreachable!("bestchain is dispatched at the top of run"),
    }
}

// ===========================================================================
// bestchain — THE CANDIDATE SET
// ===========================================================================

/// **Ask every peer, separately, and keep only what is anchored.**
///
/// # Why one connection per peer
///
/// `Client` latches onto the first peer that establishes a connection
/// (`client.rs`: `self.peer = Some(peer_id)` on `ConnectionEstablished`) and the
/// first stream that handshakes. Handing it all three seeds therefore yields ONE
/// answer from whichever seed was fastest — which is exactly the "ask a node
/// which chain it likes" shape this direction exists to avoid. A candidate SET
/// requires the peers to be asked independently, so each gets its own swarm.
///
/// # What survives
///
/// Only tips whose transition-chain proof folds from the peer's own frontier
/// root to the tip itself. A peer that serves a tip claiming any height it likes
/// — the one field `select` reads and a liar controls for free — dies here, on
/// `chain::verify_anchor`, before its bytes ever reach the fork-choice gate.
///
/// # ⚑ AND IT SELECTS NOTHING
///
/// The bundle is a SET. Which member is canonical is Samasika's question, it is
/// answered in Lean, and it is answered PAIRWISE against a persisted head —
/// `MinaChainSelection.beats_not_transitive` proves `select` has genuine 3-cycles
/// at real Mina constants, so a `max_by` here would be an exploitable fold.
async fn bestchain(opts: &Opts) -> Result<(), Box<dyn std::error::Error>> {
    let dir = opts.dir.as_ref().ok_or("bestchain needs --dir PATH")?;
    std::fs::create_dir_all(dir)?;

    // Per-peer budget. The whole command already runs under `opts.timeout`; this
    // stops one unreachable seed from eating the entire budget and turning a
    // three-candidate set into a one-candidate set by accident.
    let per_peer = opts.timeout / (opts.peers.len().max(1) as u32);

    let mut entries: Vec<BundleEntry> = Vec::new();
    let mut refused: Vec<String> = Vec::new();
    let mut silent: Vec<String> = Vec::new();

    for (i, peer) in opts.peers.iter().enumerate() {
        eprintln!("mina-tip: asking peer {i} ({peer}) for its own best tip");
        let mut client = connect(vec![peer.clone()]);
        let fetched = tokio::time::timeout(per_peer, client.rpc::<GetBestTipV2>(())).await;

        let tip: BestTipWithProof = match fetched {
            Ok(Ok(Some(t))) => t,
            Ok(Ok(None)) => {
                silent.push(format!("peer {i}: holds no best tip"));
                continue;
            }
            Ok(Err(e)) => {
                silent.push(format!("peer {i}: rpc failed: {e}"));
                continue;
            }
            Err(_) => {
                silent.push(format!(
                    "peer {i}: no answer within {}s",
                    per_peer.as_secs()
                ));
                continue;
            }
        };
        let peer_id = client
            .peer_id()
            .map(|p| p.to_string())
            .unwrap_or_else(|| format!("unattributed-{i}"));

        // ⚑ THE ANCHOR IS THE GATE. A tip without one never enters the set.
        match verify_anchor(&tip) {
            Ok(anchored) => {
                let idx = entries.len();
                let (nfull, nps) = bundle::write_candidate(dir, idx, &tip)?;
                eprintln!(
                    "mina-tip:   ANCHORED  tip {} ({}) <- root {} ({}), depth {} \
                     [{nfull} B reply, {nps} B protocol state]",
                    anchored.tip_height,
                    &anchored.tip_hash,
                    anchored.root_height,
                    &anchored.root_hash,
                    anchored.depth
                );
                entries.push(BundleEntry {
                    idx,
                    peer: peer_id,
                    anchored,
                });
            }
            Err(e) => {
                eprintln!("mina-tip:   REFUSED   peer {peer_id}: {e}");
                refused.push(format!("peer {peer_id}: {e}"));
            }
        }
    }

    for s in &silent {
        eprintln!("mina-tip:   silent    {s}");
    }

    if entries.is_empty() {
        return Err(format!(
            "no peer produced an ANCHOR-VERIFIED candidate ({} refused, {} silent). \
             A light client with no anchored candidate does not move its head.",
            refused.len(),
            silent.len()
        )
        .into());
    }

    bundle::write_manifest(dir, &entries)?;

    // The report. Heights are printed sorted, and it says in as many words that
    // ordering by height is NOT the selection.
    let mut sorted: Vec<&BundleEntry> = entries.iter().collect();
    sorted.sort_by_key(|e| std::cmp::Reverse(e.anchored.tip_height));
    println!(
        "CANDIDATE SET: {} anchored, {} refused, {} silent, of {} peers asked",
        entries.len(),
        refused.len(),
        silent.len(),
        opts.peers.len()
    );
    for e in &sorted {
        println!(
            "  cand-{:02}  height {}  depth {}  tip {}  root {}  peer {}",
            e.idx,
            e.anchored.tip_height,
            e.anchored.depth,
            e.anchored.tip_hash,
            e.anchored.root_hash,
            e.peer
        );
    }
    println!(
        "  (order is by height for READING ONLY. Selection is Samasika's, it is decided in Lean, \
         and it is PAIRWISE against a persisted head — `select` has 3-cycles, so the best of a set \
         is not a function of the set.)"
    );
    println!(
        "  (each anchor reaches that peer's own frontier ROOT, at most k=290 blocks back — not \
         genesis. A public node serves only its transition frontier.)"
    );
    Ok(())
}

// ===========================================================================
// verify-bestchain — OFFLINE re-judgement, and the RED path
// ===========================================================================

/// Re-judge a bundle from its bytes, and — under `--self-test` — require five
/// forgeries to be refused.
///
/// ⚑ The `--self-test` legs are not decoration. The headline this command prints
/// is a NEGATIVE assertion ("no candidate in this bundle is unanchored"), which
/// passes just as happily when the checker is broken. The legs mutate a REAL
/// anchored candidate in memory — the bundle on disk is never touched — and the
/// command fails if any mutation is ACCEPTED, or if the untouched control is
/// refused.
fn verify_bestchain(opts: &Opts) -> Result<(), Box<dyn std::error::Error>> {
    let dir = opts
        .dir
        .as_ref()
        .ok_or("verify-bestchain needs --dir PATH")?;
    let entries = bundle::verify_bundle(dir)?;

    eprintln!("mina-tip: verify-bestchain (openmina decode + Poseidon merkle-list fold, offline)");
    for e in &entries {
        eprintln!(
            "mina-tip:   cand-{:02} height {} depth {} root {} -> tip {} (peer {})",
            e.idx,
            e.anchored.tip_height,
            e.anchored.depth,
            e.anchored.root_height,
            e.anchored.tip_height,
            e.peer
        );
    }

    if !opts.self_test {
        println!(
            "ANCHORED CANDIDATE SET: {} candidates, every transition-chain proof folds from its \
             peer's frontier root to the tip it claims (openmina Poseidon)",
            entries.len()
        );
        return Ok(());
    }

    // ── THE RED PATH ────────────────────────────────────────────────────────
    let real = bundle::read_candidate(dir, entries[0].idx)?;
    // CONTROL. If the untouched candidate does not verify, every red below is free.
    verify_anchor(&real).map_err(|e| {
        format!("CONTROL FAILED: the untouched candidate 0 does not verify ({e}) — every red leg below would be free")
    })?;
    eprintln!("mina-tip:   CONTROL   untouched candidate 0 verifies");

    let legs = bundle::red_legs(&real)?;
    let mut admitted = Vec::new();
    let mut wrong_catcher = Vec::new();
    let mut fold_caught = 0usize;
    for leg in &legs {
        match verify_anchor(&leg.mutated) {
            Err(e) => {
                let by_fold = e.came_from_the_fold();
                if by_fold {
                    fold_caught += 1;
                }
                let want_fold = leg.catcher == bundle::Catcher::Fold;
                if by_fold != want_fold {
                    // ⚑ A leg refused by the WRONG check has not tested what it claims to test.
                    wrong_catcher.push(leg.name);
                }
                eprintln!(
                    "mina-tip:   RED  {:<20} REFUSED by the {:<5} — {e}",
                    leg.name,
                    if by_fold { "FOLD" } else { "shape" }
                );
            }
            Ok(_) => {
                eprintln!(
                    "mina-tip:   RED  {:<20} ⚠ ACCEPTED — {} was admitted",
                    leg.name, leg.what
                );
                admitted.push(leg.name);
            }
        }
    }

    // ── The manifest leg. A bundle whose TSV lies about a height must be refused, and this is the
    // only way to prove `verify_bundle` re-derives rather than reads. Done on a SCRATCH COPY; the
    // bundle under test is never mutated.
    let scratch = std::env::temp_dir().join(format!("mina-tip-selftest-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&scratch);
    std::fs::create_dir_all(&scratch)?;
    for e in &entries {
        std::fs::copy(
            bundle::besttip_path(dir, e.idx),
            bundle::besttip_path(&scratch, e.idx),
        )?;
        std::fs::copy(
            bundle::ps_path(dir, e.idx),
            bundle::ps_path(&scratch, e.idx),
        )?;
    }
    let honest = std::fs::read_to_string(bundle::manifest_path(dir))?;
    let lied = honest.replacen(
        &format!("\t{}\t", entries[0].anchored.tip_height),
        &format!("\t{}\t", entries[0].anchored.tip_height + 1_000_000),
        1,
    );
    if lied == honest {
        return Err("the manifest mutation was a no-op — the leg would be vacuous".into());
    }
    std::fs::write(bundle::manifest_path(&scratch), &lied)?;
    let manifest_leg = match bundle::verify_bundle(&scratch) {
        Err(e) => {
            eprintln!(
                "mina-tip:   RED  {:<20} REFUSED by the bytes — {e}",
                "R7 lying-manifest"
            );
            true
        }
        Ok(_) => {
            eprintln!(
                "mina-tip:   RED  {:<20} ⚠ ACCEPTED — a manifest claiming a height 1,000,000 \
                 blocks above the bytes was believed",
                "R7 lying-manifest"
            );
            false
        }
    };
    let _ = std::fs::remove_dir_all(&scratch);
    if !manifest_leg {
        admitted.push("R7 lying-manifest");
    }

    if !admitted.is_empty() {
        return Err(format!(
            "{} RED LEG(S) DID NOT BITE ({}) — this anchor check cannot be trusted",
            admitted.len(),
            admitted.join(", ")
        )
        .into());
    }
    if !wrong_catcher.is_empty() {
        return Err(format!(
            "{} RED LEG(S) DIED ON THE WRONG CHECK ({}) — a leg aimed at the Poseidon fold that is \
             refused by an integer comparison has not exercised the fold, and would stay green if \
             the fold were deleted",
            wrong_catcher.len(),
            wrong_catcher.join(", ")
        )
        .into());
    }
    // ── THE COVERAGE MAP. What the anchor binds, at the BYTE level, on the real
    // encoded reply — offsets derived from the binprot layout, never hardcoded.
    let cov = bundle::probe_coverage(&real, 8)?;
    let mut bound_bytes = 0usize;
    let mut total_bytes = 0usize;
    for r in &cov {
        total_bytes += r.range.len();
        if r.bound {
            bound_bytes += r.range.len();
        }
        eprintln!(
            "mina-tip:   COV  {:<32} {:>6}..{:<6} {:<7} {}/{} sampled flips refused",
            r.name,
            r.range.start,
            r.range.end,
            if r.bound { "BOUND" } else { "unbound" },
            r.refused,
            r.sampled
        );
    }
    let pct = (bound_bytes as f64) * 100.0 / (total_bytes as f64);
    eprintln!(
        "mina-tip:   COV  the anchor binds {bound_bytes} of {total_bytes} bytes ({pct:.1}%) — \
         Mina's state hash is over the PROTOCOL STATE alone, so a chain proof cannot bind a block \
         body or its Pickles proof and does not claim to"
    );

    if fold_caught < 2 {
        return Err(format!(
            "only {fold_caught} leg(s) reached the Poseidon merkle-list fold; at least 2 must, or \
             the anchor is being defended by arithmetic alone"
        )
        .into());
    }
    println!(
        "ANCHORED CANDIDATE SET: {} candidates verified; {} forgeries REFUSED, {} of them BY THE \
         POSEIDON FOLD with every shape check passing (replayed block, reordered chain), the rest \
         by shape (grafted anchor, short list, empty list, foreign tip) — plus a lying manifest \
         refused by the bytes",
        entries.len(),
        legs.len() + 1,
        fold_caught
    );
    Ok(())
}
