//! THE PRODUCTION BID COLLECTOR — the caller the sealed-ingress queue never had.
//!
//! [`private_bazaar_ingress`](crate::private_bazaar_ingress) built the durable
//! submission half of the private Dark Bazaar clearing and documented
//! `PrivateBazaarSealedIngressQueue::submit` as "THE PRODUCTION INGRESS". It was
//! not one. Measured 2026-07-28: `submit` had **0 production callers and 11 test
//! callers**, and the only route to a queue —
//! `PrivateBazaarLiveDeployment::private_sealed_ingress` — was likewise reached
//! from tests and from the DRAIN side alone
//! (`PrivateBazaarAuthenticatedReceiptSource::open`). Meanwhile the supervisor
//! mounted at `dreggnet-web/src/bin/dreggnet-web-server.rs:159` polled that queue
//! on every tick. The drain shipped; the submission did not.
//!
//! This module is the missing caller, and it ships as the
//! `dregg-private-bazaar-submit` binary.
//!
//! # Why a local process and not a route
//!
//! A bid limit is a secret, and the queue's own module note is explicit that a
//! submitted book "never crosses a browser or chat boundary". So this is
//! deliberately NOT an HTTP route, an Offering action, or a bot command: it is an
//! operator-run process on the deployment host, resolving the SAME
//! `PrivateBazaarLiveDeployment::from_env` configuration — and therefore the same
//! authority directory — that the serving process drains.
//!
//! The book is read from **stdin, never argv**. `argv` is world-readable through
//! `/proc/<pid>/cmdline` on Linux and through `ps` generally, so a limit passed as
//! an argument would be legible to every local account — strictly wider than the
//! `0600`-under-the-authority-directory boundary the queue documents. The seed is
//! carried on stdin too, simply so there is one document rather than two sources.
//!
//! # What this module does NOT do
//!
//! It does not gate. The proved-family gate is
//! [`PrivateSealedIngressBook::new`](dreggnet_market::private_clearing::PrivateSealedIngressBook)
//! and the roster gate is the queue's, and both are re-run by the DECODER on the
//! way back out of the durable record. Parsing here produces
//! `(DreggIdentity, i64)` pairs and hands them straight to `submit`, so a refusal
//! is the queue's refusal, by its name, and there is no second opinion that could
//! drift from it.

use dreggnet_offerings::DreggIdentity;

use crate::private_bazaar_ingress::{PrivateBazaarIngressError, PrivateBazaarIngressSubmission};
use crate::private_bazaar_live::PrivateBazaarLiveDeployment;
use crate::private_bazaar_worker::PrivateBazaarWorkerError;

/// One parsed out-of-band submission document.
///
/// The bids are NOT yet a `PrivateSealedIngressBook`: constructing one is the
/// proved-family gate, and this type deliberately stops short of it so the gate
/// is applied exactly once, inside `submit`, where the roster gate is too.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SealedBookSubmissionRequest {
    /// The deterministic hosted session seed the book clears against.
    pub seed: u64,
    /// Sealed `(bidder, limit)` pairs in submission order.
    pub bids: Vec<(DreggIdentity, i64)>,
    /// Worker-private commitment blind, when this submission is the one that
    /// establishes the durable binding. Omitted on a replay of an already bound
    /// market.
    pub blinding: Option<[u32; 8]>,
}

/// Why an out-of-band submission was refused. The parse refusals name the exact
/// line so an operator can fix the document; the queue refusals are the queue's
/// own, unmodified.
#[derive(Debug)]
pub enum PrivateBazaarSubmitError {
    /// No `seed` directive. There is no default: a book must name the market it
    /// clears against.
    SeedMissing,
    /// More than one `seed` directive. Picking either would silently discard a
    /// book the operator believed they had submitted.
    SeedRepeated { line: usize },
    /// A `blinding` directive appeared twice.
    BlindingRepeated { line: usize },
    /// A directive this reader does not know. Never ignored: an unread line in a
    /// submission document is a bid that did not happen.
    UnknownDirective { line: usize },
    /// A directive whose payload did not parse. `expected` names the shape.
    Malformed {
        line: usize,
        directive: &'static str,
        expected: &'static str,
    },
    /// The queue refused the book — outside the proved family, off the roster, a
    /// duplicate bidder, or an over-long handle.
    Ingress(PrivateBazaarIngressError),
    /// The durable queue could not be opened.
    Queue(PrivateBazaarWorkerError),
}

impl std::fmt::Display for PrivateBazaarSubmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SeedMissing => write!(
                f,
                "private submission refused: no `seed` directive, and a sealed book must name the \
                 hosted market it clears against"
            ),
            Self::SeedRepeated { line } => write!(
                f,
                "private submission refused: line {line} repeats the `seed` directive"
            ),
            Self::BlindingRepeated { line } => write!(
                f,
                "private submission refused: line {line} repeats the `blinding` directive"
            ),
            Self::UnknownDirective { line } => write!(
                f,
                "private submission refused: line {line} is not one of `seed`, `bid`, `blinding`"
            ),
            Self::Malformed {
                line,
                directive,
                expected,
            } => write!(
                f,
                "private submission refused: line {line} `{directive}` must be {expected}"
            ),
            Self::Ingress(error) => write!(f, "{error}"),
            Self::Queue(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for PrivateBazaarSubmitError {}

impl From<PrivateBazaarIngressError> for PrivateBazaarSubmitError {
    fn from(error: PrivateBazaarIngressError) -> Self {
        Self::Ingress(error)
    }
}

impl From<PrivateBazaarWorkerError> for PrivateBazaarSubmitError {
    fn from(error: PrivateBazaarWorkerError) -> Self {
        Self::Queue(error)
    }
}

/// Accepted submission, plus the queue depth the supervisor still has to clear.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AcceptedSealedBook {
    pub submission: PrivateBazaarIngressSubmission,
    pub pending: u64,
}

/// Parse one out-of-band submission document.
///
/// The grammar is four directives, one per line; `#` starts a comment and blank
/// lines are ignored:
///
/// ```text
/// # a sealed book for one hosted market
/// seed 0xB42AC1
/// bid raider-one=2
/// bid raider-two=3
/// blinding 00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee
/// ```
///
/// `bid` is `actor=limit`, split at the LAST `=`, so a handle may contain one —
/// the deployment roster's own env grammar uses `actor=cell` the same way. An
/// unrecognised line is a refusal, never a skip: silently dropping a line in this
/// document would drop a bid, and the auction would clear without it.
pub fn parse_sealed_book_submission(
    document: &str,
) -> Result<SealedBookSubmissionRequest, PrivateBazaarSubmitError> {
    let mut seed: Option<u64> = None;
    let mut bids = Vec::new();
    let mut blinding: Option<[u32; 8]> = None;

    for (index, raw) in document.lines().enumerate() {
        let line = index + 1;
        let text = raw.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }
        let (directive, payload) = match text.split_once(char::is_whitespace) {
            Some((directive, payload)) => (directive, payload.trim()),
            None => (text, ""),
        };
        match directive {
            "seed" => {
                if seed.is_some() {
                    return Err(PrivateBazaarSubmitError::SeedRepeated { line });
                }
                seed = Some(
                    parse_u64(payload).ok_or(PrivateBazaarSubmitError::Malformed {
                        line,
                        directive: "seed",
                        expected: "a decimal or 0x-prefixed hexadecimal u64",
                    })?,
                );
            }
            "bid" => {
                let (actor, limit) =
                    payload
                        .rsplit_once('=')
                        .ok_or(PrivateBazaarSubmitError::Malformed {
                            line,
                            directive: "bid",
                            expected: "actor=limit",
                        })?;
                let actor = actor.trim();
                if actor.is_empty() {
                    return Err(PrivateBazaarSubmitError::Malformed {
                        line,
                        directive: "bid",
                        expected: "actor=limit with a non-empty actor",
                    });
                }
                let limit = limit.trim().parse::<i64>().map_err(|_| {
                    PrivateBazaarSubmitError::Malformed {
                        line,
                        directive: "bid",
                        expected: "actor=limit with a decimal i64 limit",
                    }
                })?;
                bids.push((DreggIdentity(actor.to_owned()), limit));
            }
            "blinding" => {
                if blinding.is_some() {
                    return Err(PrivateBazaarSubmitError::BlindingRepeated { line });
                }
                blinding = Some(parse_blinding(payload).ok_or(
                    PrivateBazaarSubmitError::Malformed {
                        line,
                        directive: "blinding",
                        expected: "exactly 64 hexadecimal characters (eight big-endian limbs)",
                    },
                )?);
            }
            _ => return Err(PrivateBazaarSubmitError::UnknownDirective { line }),
        }
    }

    Ok(SealedBookSubmissionRequest {
        seed: seed.ok_or(PrivateBazaarSubmitError::SeedMissing)?,
        bids,
        blinding,
    })
}

/// THE PRODUCTION CALL. Hand one parsed book to the deployment's durable
/// sealed-ingress queue.
///
/// This is the whole wiring: it opens the queue the mounted supervisor drains and
/// invokes `PrivateBazaarSealedIngressQueue::submit`. Every gate — proved family,
/// handle width, deployment roster — is that method's, applied before anything is
/// written, so a refusal here leaves no durable trace and never reaches the
/// executor board.
pub fn submit_sealed_book(
    deployment: &PrivateBazaarLiveDeployment,
    request: SealedBookSubmissionRequest,
) -> Result<AcceptedSealedBook, PrivateBazaarSubmitError> {
    let mut queue = deployment.private_sealed_ingress()?;
    let submission = queue.submit(request.seed, request.bids, request.blinding)?;
    let pending = queue.pending()?;
    Ok(AcceptedSealedBook {
        submission,
        pending,
    })
}

/// Parse a document and submit it. The entry point the binary is a shell around.
pub fn submit_sealed_book_document(
    deployment: &PrivateBazaarLiveDeployment,
    document: &str,
) -> Result<AcceptedSealedBook, PrivateBazaarSubmitError> {
    submit_sealed_book(deployment, parse_sealed_book_submission(document)?)
}

fn parse_u64(text: &str) -> Option<u64> {
    let text = text.trim();
    match text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        Some(hex) if !hex.is_empty() => u64::from_str_radix(&hex.replace('_', ""), 16).ok(),
        Some(_) => None,
        None => text.replace('_', "").parse::<u64>().ok(),
    }
}

/// Eight big-endian `u32` limbs, matching the ingress record encoder's
/// `lane.to_be_bytes()` layout exactly.
fn parse_blinding(text: &str) -> Option<[u32; 8]> {
    let text = text.trim();
    if text.len() != 64 || !text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return None;
    }
    let mut limbs = [0u32; 8];
    for (index, limb) in limbs.iter_mut().enumerate() {
        *limb = u32::from_str_radix(&text[index * 8..(index + 1) * 8], 16).ok()?;
    }
    Some(limbs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_document_parses_to_the_exact_bidders_limits_and_blind() {
        let parsed = parse_sealed_book_submission(
            "# one sealed book\n\
             seed 0xB4_2A_C1\n\
             \n\
             bid raider-one=2   # the low bid\n\
             bid raider-two=3\n\
             blinding 00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee\n",
        )
        .unwrap();
        assert_eq!(parsed.seed, 0xB4_2A_C1);
        assert_eq!(
            parsed.bids,
            vec![
                (DreggIdentity("raider-one".to_owned()), 2),
                (DreggIdentity("raider-two".to_owned()), 3),
            ]
        );
        assert_eq!(parsed.blinding, Some([0x00C0_FFEE; 8]));
    }

    /// A DOCUMENT WITH NO BLIND IS A REPLAY, NOT A DEFAULTED ONE.
    ///
    /// The blind is worker-private key-adjacent material; synthesising one here
    /// would bind a market to a value no operator chose.
    #[test]
    fn an_absent_blinding_stays_absent() {
        let parsed = parse_sealed_book_submission("seed 7\nbid solo=1\n").unwrap();
        assert_eq!(parsed.blinding, None);
        assert_eq!(parsed.seed, 7);
    }

    /// AN UNREADABLE LINE IS A REFUSAL, NEVER A SKIP.
    ///
    /// This is the whole reason the reader is strict: a dropped `bid` line is a
    /// bidder who paid attention and did not appear in the auction, and the
    /// clearing would look entirely healthy without them.
    #[test]
    fn every_unreadable_line_is_refused_by_name_and_nothing_is_dropped() {
        for (document, expected) in [
            (
                "bid solo=1\n",
                "private submission refused: no `seed` directive, and a sealed book must name the \
                 hosted market it clears against",
            ),
            (
                "seed 1\nseed 2\n",
                "private submission refused: line 2 repeats the `seed` directive",
            ),
            (
                "seed 1\nblinding 00\nblinding 00\n",
                "private submission refused: line 2 `blinding` must be exactly 64 hexadecimal \
                 characters (eight big-endian limbs)",
            ),
            (
                "seed 1\nbids solo=1\n",
                "private submission refused: line 2 is not one of `seed`, `bid`, `blinding`",
            ),
            (
                "seed 1\nbid solo\n",
                "private submission refused: line 2 `bid` must be actor=limit",
            ),
            (
                "seed 1\nbid =1\n",
                "private submission refused: line 2 `bid` must be actor=limit with a non-empty \
                 actor",
            ),
            (
                "seed 1\nbid solo=two\n",
                "private submission refused: line 2 `bid` must be actor=limit with a decimal i64 \
                 limit",
            ),
            (
                "seed nine\n",
                "private submission refused: line 1 `seed` must be a decimal or 0x-prefixed \
                 hexadecimal u64",
            ),
        ] {
            let named = parse_sealed_book_submission(document)
                .expect_err("the document must be refused")
                .to_string();
            assert_eq!(named, expected, "the refusal must name what is wrong");
        }
    }

    /// A REPEATED BLIND IS CAUGHT EVEN WHEN BOTH ARE WELL-FORMED.
    #[test]
    fn a_repeated_well_formed_blinding_is_refused() {
        let hex = "0".repeat(64);
        let refused =
            parse_sealed_book_submission(&format!("seed 1\nblinding {hex}\nblinding {hex}\n"));
        assert!(
            refused
                .as_ref()
                .expect_err("two blinds is ambiguous")
                .to_string()
                .contains("line 3 repeats the `blinding` directive"),
            "{refused:?}"
        );
    }

    /// THE PARSER DOES NOT GATE, AND MUST NOT.
    ///
    /// An out-of-family book parses cleanly and is refused by the queue's own
    /// gate. A second opinion here would be a second gate, and two gates that
    /// agree today disagree later.
    #[test]
    fn an_out_of_family_book_parses_and_is_left_for_the_queues_gate() {
        let parsed =
            parse_sealed_book_submission("seed 1\nbid a=0\nbid b=1\nbid c=2\nbid d=99\nbid e=-4\n")
                .unwrap();
        assert_eq!(parsed.bids.len(), 5);
        assert_eq!(parsed.bids[3].1, 99);
        assert_eq!(parsed.bids[4].1, -4);
    }

    #[test]
    fn a_handle_may_contain_an_equals_sign_because_the_split_is_the_last_one() {
        let parsed = parse_sealed_book_submission("seed 1\nbid odd=name=3\n").unwrap();
        assert_eq!(parsed.bids, vec![(DreggIdentity("odd=name".to_owned()), 3)]);
    }
}
