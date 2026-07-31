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
mod client;

use std::io::Write as _;
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
        println!(
            "CONSECUTIVE PAIR {parent_h} -> {child_h}: deriveStateHash(parent) == child.previous_state_hash (openmina)"
        );
        Ok(())
    } else {
        Err(format!("not a consecutive pair (consecutive={consecutive}, linked={linked})").into())
    }
}

async fn run(opts: &Opts) -> Result<(), Box<dyn std::error::Error>> {
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
        // Handled in `main` before the network path is entered.
        Cmd::VerifyPair => unreachable!("verify-pair is offline and dispatched in main"),
    }
}
