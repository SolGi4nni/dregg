//! Steps 5 and 6 of the Path of Angels first-turn ceremony: build the exact
//! player-signed Signal carrier, POST it to the public claims route, and watch the
//! one public number that says a turn settled.
//!
//! # Why this is a command and not a script
//!
//! The carrier is not a JSON body. It is a `postcard`-encoded `SignedTurn` whose
//! single action must satisfy `claim_from_exact_signal_turn`'s no-piggyback
//! predicate, whose agent must be exactly `derive_raw(signer, blake3("default"))`,
//! whose action authorization is a HYBRID (Ed25519 + ML-DSA-65) signature over the
//! federation-bound canonical message, and whose fee was priced against the
//! post-signing carrier shape. `curl` cannot make one.
//!
//! Until this module existed the only thing in the tree that could was
//! `poa_signal_first_turn_e2e::solved_signal_turn` — inside a `#[cfg(test)]`
//! module, unreachable from any binary. [`signed_signal_claim_turn`] IS that
//! function, lifted; the milestone test now calls it. There is one builder, so the
//! carrier an operator ships on the live node is the carrier the milestone proved,
//! not a re-implementation that agrees today.
//!
//! # Custody
//!
//! `--player-key-file` is a 32-byte Ed25519 seed as 64 lowercase hex. It is the
//! PLAYER's key, not the curator's and not the node's: it authorizes one game turn
//! and spends that player cell's fee. `--identity-only` prints the public key and
//! the agent cell id derived from it without signing anything, so the cell can be
//! funded before the claim is built.
//!
//! # ⚑ IT PLAYS THE GAME NOW (2026-08-07)
//!
//! A claim carries the played TRANSCRIPT, and the node refuses one whose rounds it
//! did not itself classify. So this command can no longer take a code and post it:
//! that is precisely the blind path that was closed. It now
//!
//! 1. opens a judged session against the authority's installed slot,
//! 2. submits each code of `--code` as one burst, reading LOCKED/DRIFT back,
//! 3. refuses to submit anything if the session did not SOLVE, and
//! 4. builds the claim out of the transcript **the node reports**, never out of the
//!    codes typed on the command line.
//!
//! Step 4 is not fussiness. If the node's stored transcript and the typed one
//! disagree — a burst that landed but whose response was lost, a session already
//! part-played in a browser — the node's copy is the one the gate compares against,
//! and building from the typed copy would produce a carrier refused for a reason
//! that reads like a judge failure.
//!
//! The session routes are AUTHENTICATED (`--bearer`, or loopback on a node with no
//! passphrase set), while `…/claims` stays public.
//!
//! # What settles, and what does not
//!
//! `accepted: true` from the submit is ADMISSION STAGING and settles nothing — a
//! losing guess gets it too, and a Lean-rejected claim is routed to
//! `persist_finalized_payload_rejection` with no transition and no height. The
//! number that bites is `latest_height` off `GET /status` AFTER finalization, which
//! is why `--await-latest-height` exists and why it TIMES OUT rather than reporting
//! the submit's receipt as a result.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use dregg_sdk::poa_signal::{SIGNAL_MAX_TRANSCRIPT_ROUNDS, SignalClaimV1, SignalCode};
use ed25519_dalek::{Signer as _, SigningKey};
use zeroize::Zeroizing;

use crate::poa_signal_session::{
    SignalCodeWireV1, guess_statement_message, open_statement_message,
};
use crate::poa_signal_slot_instance::{load_claim_document, parse_hex32};

/// THE ONE SIGNAL CARRIER BUILDER.
///
/// Build the one-action `poa-signal` turn, attach the hybrid authorization over the
/// federation-bound canonical message, and sign the turn — byte-for-byte what an
/// SDK client emits and exactly what `POST /api/poa/signal/{authority}/claims`
/// admits.
///
/// The two hash resets are load-bearing: signing the action changes the action, so
/// the action hash and the forest hash computed over the UNSIGNED shape are stale
/// and are zeroed for the canonical recomputation the executor performs.
///
/// `nonce` must be the turn nonce the executor will demand (`agent.state.nonce()`),
/// which is 0 for a player's first turn. It is threaded explicitly rather than read
/// off the cipherclerk's receipt chain because a freshly-loaded key file has no
/// receipts at all — its chain length would answer 0 for the tenth turn as loudly
/// as for the first.
pub fn signed_signal_claim_turn(
    player: &dregg_sdk::AgentCipherclerk,
    federation_id: [u8; 32],
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
    claim: SignalClaimV1,
) -> dregg_sdk::SignedTurn {
    let mut turn = dregg_sdk::poa_signal::signal_claim_turn(
        &player.public_key().0,
        nonce,
        previous_receipt_hash,
        claim,
    );
    let unsigned = turn.call_forest.roots[0].action.clone();
    turn.call_forest.roots[0].action = player.sign_action_hybrid(unsigned, &federation_id, nonce);
    turn.call_forest.roots[0].hash = [0; 32];
    turn.call_forest.forest_hash = [0; 32];
    player.sign_turn(&turn)
}

/// Inputs to `dregg-node poa-signal-submit-claim`.
#[derive(Clone, Debug)]
pub struct PoaSignalSubmitClaimArgs {
    /// Base HTTP URL of a RUNNING node, e.g. `http://127.0.0.1:8423`.
    pub endpoint: String,
    /// Federation id of the Signal authority, 64 lowercase hex.
    pub authority_id: String,
    /// File holding the player's 32-byte Ed25519 seed as 64 lowercase hex.
    pub player_key_file: PathBuf,
    /// A `POA-SIGNAL-INSTANCE-PREVIEW-V1` document (step 4's output).
    pub claim_file: Option<PathBuf>,
    /// The transcript to PLAY: `low,mid,high` triples in base six, separated by
    /// `;`, in submission order, at most [`SIGNAL_MAX_TRANSCRIPT_ROUNDS`] of them.
    ///
    /// ⚠ These are guesses to spend bursts on, not a claim to post. The command
    /// plays them through the judged session and settles only if the LAST one locks
    /// all three bands.
    pub code: Option<String>,
    /// Mission the hand-typed transcript claims. Ignored when `--claim-file` is given.
    pub mission_id: u64,
    /// Bearer token for the AUTHENTICATED session routes. Omit on a node with no
    /// passphrase set when connecting over loopback.
    pub bearer: Option<String>,
    /// The turn nonce (`agent.state.nonce()`); 0 for a player's first turn.
    pub nonce: u64,
    /// The player's previous receipt hash, if it has acted before.
    pub previous_receipt_hash: Option<String>,
    /// Print the player identity and exit, signing and submitting nothing.
    pub identity_only: bool,
    /// After a successful submit, poll `GET /status` until `latest_height` reaches
    /// this value.
    pub await_latest_height: Option<u64>,
    /// How long to poll for.
    pub await_timeout_secs: u64,
}

/// Steps 5 and 6.
pub async fn submit_poa_signal_claim(args: &PoaSignalSubmitClaimArgs) -> Result<String, String> {
    let authority_id = parse_hex32(&args.authority_id, "authority_id")?;
    let player = load_player(&args.player_key_file)?;
    let player_key = player.public_key().0;
    let agent = dregg_sdk::poa_signal::signal_player_cell(&player_key);

    let mut report = String::new();
    report.push_str(&format!(
        "player_key: {}\nplayer_cell: {}\n",
        dregg_types::hex_encode(&player_key),
        dregg_types::hex_encode(&agent.0),
    ));
    if args.identity_only {
        // The ML-DSA-65 half, which is NOT reconstructible from the Ed25519 public
        // key — it derives from the seed. A cell that must be able to ACT has to
        // COMMIT it (`Cell::with_hybrid_balance` / a genesis cell's
        // `ml_dsa_public_key`), or hybrid admission refuses every turn it is the
        // agent of as `pq-identity-not-enrolled`. Printed here because funding a
        // player at genesis is the only way value enters a PoA chain, and whoever
        // writes that descriptor needs this exact string.
        report.push_str(&format!(
            "player_ml_dsa_public_key: {}\n",
            dregg_types::hex_encode(&player.ml_dsa_public_bytes()),
        ));
        report.push_str(
            "identity only: nothing was signed or submitted. Fund this cell before claiming.\n",
        );
        return Ok(report);
    }

    let to_play = resolve_transcript(args)?;
    let previous_receipt_hash = match &args.previous_receipt_hash {
        Some(value) => Some(parse_hex32(value, "previous_receipt_hash")?),
        None => None,
    };

    let base = args.endpoint.trim_end_matches('/');
    let client = reqwest::Client::builder()
        .timeout(Duration::from_secs(30))
        .build()
        .map_err(|error| format!("cannot build an HTTP client: {error}"))?;

    // ── PLAY. The claim is built from what the NODE served, never from `to_play`. ─
    let (mission_id, played) = play_judged_session(
        &client,
        base,
        args.bearer.as_deref(),
        authority_id,
        &player,
        &to_play,
        &mut report,
    )
    .await?;
    let claim = SignalClaimV1::new(mission_id, &played)
        .map_err(|error| format!("the session transcript is not a legal claim: {error}"))?;

    let signed = signed_signal_claim_turn(
        &player,
        authority_id,
        args.nonce,
        previous_receipt_hash,
        claim,
    );
    let wire = postcard::to_stdvec(&signed)
        .map_err(|error| format!("cannot encode the signed Signal carrier: {error}"))?;

    let url = format!(
        "{base}/api/poa/signal/{}/claims",
        dregg_types::hex_encode(&authority_id)
    );
    let response = client
        .post(&url)
        .header("content-type", "application/octet-stream")
        .body(wire)
        .send()
        .await
        .map_err(|error| format!("POST {url} failed: {error}"))?;
    let status = response.status();
    let body = response.text().await.unwrap_or_default();
    report.push_str(&format!("submit: HTTP {status} {body}\n"));
    if !status.is_success() {
        return Err(format!("{report}the claims route refused the carrier"));
    }
    report.push_str(
        "note: `accepted` is ADMISSION STAGING. It settles nothing on its own — a losing \
         guess is accepted too.\n",
    );

    if let Some(want) = args.await_latest_height {
        let (reached, seen) = await_latest_height(
            &client,
            base,
            want,
            Duration::from_secs(args.await_timeout_secs),
        )
        .await?;
        report.push_str(&format!("latest_height: {seen}\n"));
        if !reached {
            return Err(format!(
                "{report}latest_height never reached {want} within {}s. Still 0 means the Lean \
                 judge never finalized the settle — the exact non-event the live PoA node has \
                 shown since genesis.",
                args.await_timeout_secs
            ));
        }
    }
    Ok(report)
}

/// Poll `GET /status` until `latest_height` reaches `want`, or time out. Returns
/// `(reached, last_seen)`.
async fn await_latest_height(
    client: &reqwest::Client,
    base: &str,
    want: u64,
    within: Duration,
) -> Result<(bool, u64), String> {
    let url = format!("{base}/status");
    let deadline = Instant::now() + within;
    let mut seen = 0;
    loop {
        match client.get(&url).send().await {
            Ok(response) => {
                let body: serde_json::Value = response
                    .json()
                    .await
                    .map_err(|error| format!("GET {url} returned no JSON: {error}"))?;
                seen = body["latest_height"].as_u64().unwrap_or(seen);
            }
            // A node restarting mid-poll is not a verdict; keep polling until the
            // deadline and let the TIMEOUT be the failure.
            Err(_) => {}
        }
        if seen >= want {
            return Ok((true, seen));
        }
        if Instant::now() >= deadline {
            return Ok((false, seen));
        }
        tokio::time::sleep(Duration::from_millis(250)).await;
    }
}

/// The codes this invocation will SPEND BURSTS ON, in order.
///
/// ⚠ This is not the claim. The claim is assembled later from the transcript the
/// node reports having served, because that is the copy the settlement gate
/// compares against.
fn resolve_transcript(args: &PoaSignalSubmitClaimArgs) -> Result<Vec<SignalCode>, String> {
    let parse_one = |text: &str| -> Result<SignalCode, String> {
        let bands: Vec<&str> = text.split(',').collect();
        let [low, mid, high] = bands.as_slice() else {
            return Err(
                "--code must be `low,mid,high` triples in base six, separated by `;`".to_owned(),
            );
        };
        let band = |value: &str, name: &str| {
            value
                .trim()
                .parse::<u64>()
                .map_err(|_| format!("--code {name} band is not a number"))
        };
        SignalCode::new(band(low, "low")?, band(mid, "mid")?, band(high, "high")?)
            .map_err(|error| format!("illegal code: {error}"))
    };

    let transcript = match (&args.claim_file, &args.code) {
        (Some(_), Some(_)) => {
            return Err(
                "--claim-file and --code both name the guesses; pass exactly one".to_owned(),
            );
        }
        // The operator preview holds the derived answer, so it plays as ONE burst.
        // It is not a shortcut past the game: that burst is spent against the node's
        // own oracle like any other, and the settlement carries it.
        (Some(path), None) => {
            let document = load_claim_document(path)?;
            vec![
                SignalCode::new(
                    u64::from(document.code.low),
                    u64::from(document.code.mid),
                    u64::from(document.code.high),
                )
                .map_err(|error| format!("the preview carries an illegal code: {error}"))?,
            ]
        }
        (None, Some(codes)) => codes
            .split(';')
            .filter(|part| !part.trim().is_empty())
            .map(parse_one)
            .collect::<Result<Vec<_>, _>>()?,
        (None, None) => {
            return Err(
                "pass --claim-file (from `poa-signal-instance-preview`) or --code".to_owned(),
            );
        }
    };
    if transcript.is_empty() || transcript.len() > SIGNAL_MAX_TRANSCRIPT_ROUNDS {
        return Err(format!(
            "a judged run plays between 1 and {SIGNAL_MAX_TRANSCRIPT_ROUNDS} bursts; \
             {} were given",
            transcript.len()
        ));
    }
    Ok(transcript)
}

fn wire_code(code: SignalCode) -> SignalCodeWireV1 {
    SignalCodeWireV1 {
        low: code.low(),
        mid: code.mid(),
        high: code.high(),
    }
}

/// Open a judged session, spend one burst per code, and return the mission and the
/// transcript **as the node reports it**.
///
/// Refuses — without submitting anything — if the run does not solve. A losing run
/// settles nothing, and posting its carrier would buy a rejected turn and nothing
/// else.
async fn play_judged_session(
    client: &reqwest::Client,
    base: &str,
    bearer: Option<&str>,
    authority_id: [u8; 32],
    player: &dregg_sdk::AgentCipherclerk,
    to_play: &[SignalCode],
    report: &mut String,
) -> Result<(u64, Vec<SignalCode>), String> {
    let authority_hex = dregg_types::hex_encode(&authority_id);
    let player_key = player.public_key().0;
    let signing = SigningKey::from_bytes(&player.gossip_signing_key().to_bytes());

    let post = |path: String, body: serde_json::Value| {
        let mut request = client
            .post(format!("{base}{path}"))
            .header("content-type", "application/json");
        if let Some(token) = bearer {
            request = request.bearer_auth(token);
        }
        request.json(&body).send()
    };

    // The slot is the node's, so the signed statements have to name the node's slot.
    let opening: serde_json::Value = {
        let response = client
            .get(format!("{base}/api/poa/signal/{authority_hex}/slot"))
            .send()
            .await
            .map_err(|error| format!("GET the open slot failed: {error}"))?;
        response
            .json()
            .await
            .map_err(|error| format!("the slot publication is not JSON: {error}"))?
    };
    let slot = opening["opening"]["statement"]["slot"]
        .as_u64()
        .ok_or_else(|| format!("no curator-signed slot is open on this authority: {opening}"))?;

    let signature = signing.sign(&open_statement_message(authority_id, slot, player_key));
    let response = post(
        format!("/api/poa/signal/{authority_hex}/session/open"),
        serde_json::json!({
            "player_key": dregg_types::hex_encode(&player_key),
            "signature": dregg_types::hex_encode(&signature.to_bytes()),
        }),
    )
    .await
    .map_err(|error| format!("opening a judged session failed: {error}"))?;
    let status = response.status();
    let mut session: serde_json::Value = response
        .json()
        .await
        .map_err(|error| format!("the session document is not JSON: {error}"))?;
    if !status.is_success() {
        return Err(format!("the node refused to open a session: {session}"));
    }
    report.push_str(&format!("session: slot {slot}, opened\n"));

    for code in to_play {
        if session["solved"].as_bool() == Some(true) {
            break;
        }
        let round = session["rounds_used"]
            .as_u64()
            .ok_or_else(|| format!("the session document has no round count: {session}"))?
            as u32;
        let wire = wire_code(*code);
        let signature = signing.sign(&guess_statement_message(
            authority_id,
            slot,
            player_key,
            round,
            wire,
        ));
        let response = post(
            format!("/api/poa/signal/{authority_hex}/session/guess"),
            serde_json::json!({
                "player_key": dregg_types::hex_encode(&player_key),
                "round": round,
                "guess": { "low": wire.low, "mid": wire.mid, "high": wire.high },
                "signature": dregg_types::hex_encode(&signature.to_bytes()),
            }),
        )
        .await
        .map_err(|error| format!("spending burst {round} failed: {error}"))?;
        let status = response.status();
        let body: serde_json::Value = response
            .json()
            .await
            .map_err(|error| format!("the guess reply is not JSON: {error}"))?;
        if !status.is_success() {
            return Err(format!("burst {round} was refused: {body}"));
        }
        session = body;
        let served = &session["transcript"][round as usize];
        report.push_str(&format!(
            "  burst {round}: {},{},{}  LOCKED {} DRIFT {}\n",
            wire.low, wire.mid, wire.high, served["exact"], served["present"]
        ));
    }

    let settlement = &session["settlement"];
    if settlement.is_null() {
        return Err(format!(
            "{report}the run did not solve: {} of {} bursts spent and no settlement. \
             Nothing was submitted — a losing transcript is refused on chain and buys a \
             rejected turn.",
            session["rounds_used"], session["max_rounds"]
        ));
    }
    let mission_id = settlement["mission_id"]
        .as_u64()
        .ok_or_else(|| format!("the settlement names no mission: {settlement}"))?;
    let played = settlement["transcript"]
        .as_array()
        .ok_or_else(|| format!("the settlement carries no transcript: {settlement}"))?
        .iter()
        .map(|entry| {
            let band = |name: &str| {
                entry[name]
                    .as_u64()
                    .ok_or_else(|| format!("the settlement transcript has no {name} band"))
            };
            SignalCode::new(band("low")?, band("mid")?, band("high")?)
                .map_err(|error| format!("the settlement transcript is illegal: {error}"))
        })
        .collect::<Result<Vec<_>, String>>()?;
    report.push_str(&format!(
        "  SOLVED in {} bursts; settling with the node's own transcript\n",
        played.len()
    ));
    Ok((mission_id, played))
}

/// Load the player's signing identity from a 64-hex seed file.
fn load_player(path: &Path) -> Result<dregg_sdk::AgentCipherclerk, String> {
    let raw = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read the player key {}: {error}", path.display()))?;
    let trimmed = raw.trim();
    if trimmed.len() != 64 {
        return Err(format!(
            "the player key in {} is {} characters; it must be exactly 64 lowercase hex",
            path.display(),
            trimmed.len()
        ));
    }
    let seed = parse_hex32(trimmed, "player key")?;
    Ok(dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new(
        seed,
    )))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn player() -> dregg_sdk::AgentCipherclerk {
        dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0xC7; 32]))
    }

    /// THE CARRIER THIS COMMAND SHIPS IS THE ONE THE PUBLIC ROUTE ADMITS.
    ///
    /// `post_poa_signal_claim` decodes the body, runs the SDK's no-piggyback
    /// predicate, and requires the agent to be the signer's canonical Signal player
    /// cell. Drive those exact three checks over the built carrier here so the
    /// builder cannot drift into something the route refuses at ceremony time.
    #[test]
    fn the_built_carrier_satisfies_the_public_route_s_own_predicate() {
        let player = player();
        let claim = SignalClaimV1::new(
            1,
            &[
                SignalCode::new(0, 0, 0).unwrap(),
                SignalCode::new(5, 0, 3).unwrap(),
            ],
        )
        .unwrap();
        let signed = signed_signal_claim_turn(&player, [0x44; 32], 0, None, claim);

        let wire = postcard::to_stdvec(&signed).expect("encode");
        let decoded = crate::signed_turn_validation::decode_signed_turn(&wire)
            .expect("the route's strict one-envelope decode");
        let recovered = dregg_sdk::poa_signal::claim_from_exact_signal_turn(&decoded.turn)
            .expect("the route's no-piggyback carrier predicate");
        assert_eq!(recovered, claim, "the carrier must carry the exact claim");
        assert_eq!(
            dregg_sdk::poa_signal::signal_player_cell(&decoded.signer.0),
            decoded.turn.agent,
            "the route requires the agent to be the signer's canonical player cell"
        );
    }

    /// The turn signature covers the carrier: flipping one band invalidates it.
    /// Without this the builder could emit an unsigned-in-effect turn and every
    /// happy-path check above would still pass.
    #[test]
    fn a_substituted_code_breaks_the_envelope_signature() {
        let player = player();
        let claim = SignalClaimV1::new(1, &[SignalCode::new(5, 0, 3).unwrap()]).unwrap();
        let honest = signed_signal_claim_turn(&player, [0x44; 32], 0, None, claim);
        let other = SignalClaimV1::new(1, &[SignalCode::new(4, 0, 3).unwrap()]).unwrap();
        let mut forged = signed_signal_claim_turn(&player, [0x44; 32], 0, None, other);
        // Keep the honest signature, swap in the other claim's body.
        forged.signature = honest.signature;
        forged.pq_signature = honest.pq_signature.clone();
        assert!(
            !forged.signer.verify(&forged.turn.hash(), &forged.signature),
            "a claim body swapped under a signature must not verify"
        );
        assert!(
            honest.signer.verify(&honest.turn.hash(), &honest.signature),
            "the honest carrier must verify"
        );
    }

    #[test]
    fn a_transcript_is_parsed_as_ordered_base_six_triples() {
        let base = PoaSignalSubmitClaimArgs {
            endpoint: "http://127.0.0.1:1".to_owned(),
            authority_id: "44".repeat(32),
            player_key_file: PathBuf::from("/dev/null"),
            claim_file: None,
            code: Some("5,0,3".to_owned()),
            mission_id: 1,
            bearer: None,
            nonce: 0,
            previous_receipt_hash: None,
            identity_only: false,
            await_latest_height: None,
            await_timeout_secs: 60,
        };
        let one = resolve_transcript(&base).expect("a legal code");
        assert_eq!(one.len(), 1);
        assert_eq!((one[0].low(), one[0].mid(), one[0].high()), (5, 0, 3));

        // The whole point of the flag day: a run is a SEQUENCE of bursts, and its
        // order is load-bearing (`SignalTriangulation.replay` is fail-stop and
        // scores them left to right).
        let many = resolve_transcript(&PoaSignalSubmitClaimArgs {
            code: Some("0,0,0;3,3,3;5,0,3".to_owned()),
            ..base.clone()
        })
        .expect("a legal transcript");
        assert_eq!(many.len(), 3);
        assert_eq!((many[0].low(), many[0].mid(), many[0].high()), (0, 0, 0));
        assert_eq!((many[2].low(), many[2].mid(), many[2].high()), (5, 0, 3));

        assert!(
            resolve_transcript(&PoaSignalSubmitClaimArgs {
                code: Some("6,0,0".to_owned()),
                ..base.clone()
            })
            .is_err(),
            "band 6 is not base six"
        );
        assert!(
            resolve_transcript(&PoaSignalSubmitClaimArgs {
                code: Some("0,0,0;0,0,0;0,0,0;0,0,0;0,0,0;0,0,0".to_owned()),
                ..base.clone()
            })
            .is_err(),
            "a sixth burst is outside SignalTriangulation.MAX_TURNS"
        );
        assert!(
            resolve_transcript(&PoaSignalSubmitClaimArgs {
                claim_file: Some(PathBuf::from("/dev/null")),
                ..base.clone()
            })
            .is_err(),
            "two guess sources is ambiguous"
        );
        assert!(
            resolve_transcript(&PoaSignalSubmitClaimArgs { code: None, ..base }).is_err(),
            "no guess source at all"
        );
    }

    /// A key file is a SEED, not a public key: the printed identity must be the
    /// cell the funding has to land on.
    #[test]
    fn the_player_identity_is_the_signal_player_cell() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("player.key");
        std::fs::write(&path, "c7".repeat(32)).unwrap();
        let loaded = load_player(&path).expect("a 64-hex seed loads");
        assert_eq!(loaded.public_key().0, player().public_key().0);
        assert_eq!(
            dregg_sdk::poa_signal::signal_player_cell(&loaded.public_key().0),
            dregg_cell::CellId::derive_raw(
                &loaded.public_key().0,
                blake3::hash(b"default").as_bytes()
            ),
            "the Signal player cell IS the signer's default cell — the one a fee is paid from"
        );

        std::fs::write(&path, "c7".repeat(16)).unwrap();
        assert!(load_player(&path).is_err(), "a short seed is refused");
    }
}
