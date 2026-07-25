//! The mirror server binary.
//!
//! ```text
//!   dregg-mirror [--bind ADDR] [--root DIR] [--origin HOST] [--extension URL]
//!                [--committee KEY,KEY,...] [--seed-demo]
//! ```
//!
//! Every flag also reads an env var, because the deployed shape is a systemd unit with an
//! `EnvironmentFile` (`deploy/mirror/`):
//!
//! | flag | env | default |
//! |---|---|---|
//! | `--bind` | `DREGG_MIRROR_BIND` | `127.0.0.1:8791` |
//! | `--root` | `DREGG_MIRROR_ROOT` | `./mirror-objects` |
//! | `--origin` | `DREGG_MIRROR_ORIGIN` | `dregg.gg` |
//! | `--extension` | `DREGG_MIRROR_EXTENSION_URL` | `https://dregg.gg/extension` |
//! | `--committee` | `DREGG_MIRROR_COMMITTEE` | (empty ⇒ the structural quorum gate) |
//!
//! **The bind default is loopback on purpose.** The mirror is a public-facing read
//! surface, but it terminates no TLS and does no rate limiting; it is meant to sit behind
//! the edge (Caddy, or `tailscale funnel`) that already owns ACME and the security
//! headers. Binding `0.0.0.0` by default would make "exposed straight to the internet" the
//! path of least resistance. Set `DREGG_MIRROR_BIND` deliberately.

use std::process::ExitCode;

use dregg_mirror::{
    Mirror, MirrorConfig, PageConfig, fixtures,
    object::Committee,
    store::{DirStore, MemoryStore, ObjectStore},
    uri::Kind,
};
use http_serve::{WebRequest, WebResponse};

fn main() -> ExitCode {
    let mut bind = env_or("DREGG_MIRROR_BIND", "127.0.0.1:8791");
    let mut root = env_or("DREGG_MIRROR_ROOT", "./mirror-objects");
    let mut origin = env_or("DREGG_MIRROR_ORIGIN", "dregg.gg");
    let mut ext = env_or("DREGG_MIRROR_EXTENSION_URL", "https://dregg.gg/extension");
    let mut committee = env_or("DREGG_MIRROR_COMMITTEE", "");
    let mut seed_demo = false;

    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        let take = |i: &mut usize| -> Option<String> {
            *i += 1;
            args.get(*i).cloned()
        };
        match args[i].as_str() {
            "--bind" => bind = take(&mut i).unwrap_or(bind),
            "--root" => root = take(&mut i).unwrap_or(root),
            "--origin" => origin = take(&mut i).unwrap_or(origin),
            "--extension" => ext = take(&mut i).unwrap_or(ext),
            "--committee" => committee = take(&mut i).unwrap_or(committee),
            "--seed-demo" => seed_demo = true,
            "-h" | "--help" => {
                eprintln!("{}", HELP);
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("dregg-mirror: unknown argument {other}\n\n{HELP}");
                return ExitCode::FAILURE;
            }
        }
        i += 1;
    }

    let cfg = MirrorConfig {
        page: PageConfig {
            origin,
            extension_url: ext,
        },
        committee: Committee {
            keys: committee
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(str::to_string)
                .collect(),
        },
    };

    // A NAMED GAP, said out loud rather than silently ignored. `deploy/edge/compose`
    // sets DREGG_NODE_URL because the intended shape is that the mirror fetches attested
    // envelopes from the node (the transport hop `extension/src/netlayer.ts` injects).
    // That transport is NOT built: the store is the filesystem / in-memory one. An
    // operator who sets this and gets a mirror serving an empty corpus must be told why
    // here, not left to infer it from a 404.
    if std::env::var("DREGG_NODE_URL").is_ok() {
        eprintln!(
            "dregg-mirror: DREGG_NODE_URL is set but UNUSED — the node transport is not \
             built. Objects are served from --root (or --seed-demo) only, so this mirror \
             will 404 every reference until that directory is populated. The seam is \
             `ObjectStore` (dregg-mirror/src/store.rs)."
        );
    }

    if cfg.committee.keys.is_empty() {
        eprintln!(
            "dregg-mirror: no DREGG_MIRROR_COMMITTEE configured — the quorum gate runs \
             STRUCTURALLY (signature counting, not cryptographic anchoring). Every page \
             says so; this is the honest posture, not a silent downgrade."
        );
    }

    if seed_demo {
        let store = seeded_demo_store();
        eprintln!(
            "dregg-mirror: serving {} demo object(s) from memory on {bind}",
            store.len()
        );
        serve(bind, Mirror::new(store, cfg))
    } else {
        eprintln!("dregg-mirror: serving objects from {root} on {bind}");
        serve(bind, Mirror::new(DirStore::new(root), cfg))
    }
}

fn serve<S: ObjectStore + 'static>(bind: String, mirror: Mirror<S>) -> ExitCode {
    let handler = move |req: &http_serve::ServeRequest| -> WebResponse {
        mirror.handle(&WebRequest::new(req.method, &req.target, req.body.clone()))
    };
    match http_serve::serve_http(&bind, handler) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("dregg-mirror: {bind}: {e}");
            ExitCode::FAILURE
        }
    }
}

/// A store with one object of every registered kind, so a fresh deployment (or a local
/// smoke test) has something real to click before any object is published.
fn seeded_demo_store() -> MemoryStore {
    let mut s = MemoryStore::new();
    let a = s.insert(
        Kind::Poll,
        fixtures::poll(
            "Should the mirror ship?",
            &[("yes", 41), ("no", 3), ("show me first", 12)],
            30,
        ),
    );
    eprintln!("  dregg://poll/b3_{a}");
    let a = s.insert(
        Kind::Doc,
        fixtures::doc(
            "The untrusted-transport note",
            &[
                "Twitter is an untrusted transport. It carries a reference; it cannot \
                 forge the object.",
                "The address IS the hash, so a platform that rewrites the URL breaks the \
                 link rather than substituting content.",
            ],
            Some((
                "…so we ask no platform for anything.",
                "…so we ask platforms only to carry text.",
            )),
        ),
    );
    eprintln!("  dregg://doc/b3_{a}");
    let a = s.insert(
        Kind::DocText,
        fixtures::doctext("A shared draft", "the quick brown fox", 7),
    );
    eprintln!("  dregg://doctext/b3_{a}");
    let a = s.insert(
        Kind::Story,
        fixtures::story(
            "The first room",
            "A door, a ledger, and a light that is not yours.",
            &["read the ledger", "open the door", "wait"],
        ),
    );
    eprintln!("  dregg://story/b3_{a}");
    let a = s.insert(
        Kind::Descent,
        fixtures::descent(
            "Descent — today",
            "9f2c1d",
            &[("ember", 14, 2810), ("stranger", 11, 1990)],
        ),
    );
    eprintln!("  dregg://descent/b3_{a}");
    s
}

fn env_or(key: &str, default: &str) -> String {
    std::env::var(key).unwrap_or_else(|_| default.to_string())
}

const HELP: &str = "\
dregg-mirror — the tier-`server` view of a dregg:// object, for readers with no extension.

  --bind ADDR        listen address        (DREGG_MIRROR_BIND, default 127.0.0.1:8791)
  --root DIR         object directory      (DREGG_MIRROR_ROOT, default ./mirror-objects)
  --origin HOST      public origin, named on every page
                                           (DREGG_MIRROR_ORIGIN, default dregg.gg)
  --extension URL    the tier-`extension` upgrade link
                                           (DREGG_MIRROR_EXTENSION_URL)
  --committee KEYS   comma-separated trusted Ed25519 pubkeys (hex) for the anchored
                     quorum gate           (DREGG_MIRROR_COMMITTEE; empty => structural)
  --seed-demo        serve one in-memory object of each kind instead of reading --root

The default bind is LOOPBACK: this service terminates no TLS and does no rate limiting.
Put it behind the edge that already owns ACME (see deploy/mirror/).
";
