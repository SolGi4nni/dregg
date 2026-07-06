//! `grain-jail` — an OS-jailed subprocess body behind the grain's
//! [`AgentBrain`](dregg_agent::agent::AgentBrain) seam.
//!
//! A grain is a hosted agent whose mind is driven by an `AgentBrain`: the seam
//! yields the next `AgentAction`, observes the braid's verdict, repeats. Every
//! brain today runs *in-process*. That is right for a brain that only proposes
//! actions through the seam, and not enough for an untrusted *body* — a coding
//! agent, a BYO binary — which can ignore the cap system and make raw syscalls.
//!
//! [`ConfinedBrain`] is an `AgentBrain` whose decisions come from a jailed
//! subprocess instead of in-process code. The body proposes tool-calls over the
//! [`protocol`] line protocol; `next_action` translates each into an
//! `AgentAction` for the grain's drive loop; the loop cap-gates + meters +
//! receipts it (unchanged); `observe` sends the resulting verdict back to the
//! body, which reacts and proposes its next call. Because a `ConfinedBrain` *is*
//! an `AgentBrain`, the grain's lease, lifecycle, prepaid meter,
//! checkpoint/fork/rewind, and the R0→R2 attestation ladder all apply to a
//! confined body with **no change to the drive path**.
//!
//! The jail itself (firmament `process-pd` / `process-pd-sandbox`) connects a
//! body under [`BodyChannel`]; this module owns the seam + protocol translation
//! and is jail-mechanism-agnostic (any `BufRead + Write` pair is a channel, so
//! the jail's endpoint fd, an in-process pipe, or a test cursor all drive it
//! identically). See `docs/deos/GRAIN-CONFINED-BODY.md`.

use std::io::{self, BufRead, Write};

use dregg_agent::agent::{ActionObservation, AgentAction, AgentBrain};

pub mod protocol;

/// The real firmament OS-jail body-spawn (`real-jail` feature): fork a body into
/// a process-PD confined to Endpoint-only and drive it with a [`ConfinedBrain`].
#[cfg(feature = "real-jail")]
pub mod jail;

pub use protocol::{BodyMsg, DoneNote, Proposal, Verdict};

/// The transport to a confined body: read its next message, write it a verdict.
///
/// One trait so the jail's endpoint fd, an in-process pipe, and a test channel
/// are interchangeable. [`recv`](BodyChannel::recv) returns `Ok(None)` on a clean
/// close (EOF) — the body is gone; the drive ends.
pub trait BodyChannel {
    /// The body's next message, or `None` if the channel closed (EOF).
    fn recv(&mut self) -> io::Result<Option<BodyMsg>>;
    /// Send the host's verdict on the body's last proposal.
    fn send(&mut self, verdict: &Verdict) -> io::Result<()>;
}

/// A [`BodyChannel`] over any newline-delimited-JSON byte streams: one
/// `BufRead` for the body's messages, one `Write` for the host's verdicts.
///
/// This is the concrete channel for every backing transport — the jail endpoint
/// fd (a `BufReader<File>` + `File`), an in-process `os_pipe`, or a test
/// `Cursor`. Framing is one JSON value per line.
pub struct LineChannel<R: BufRead, W: Write> {
    reader: R,
    writer: W,
    line: String,
}

impl<R: BufRead, W: Write> LineChannel<R, W> {
    /// A channel reading the body's messages from `reader`, writing verdicts to
    /// `writer`.
    pub fn new(reader: R, writer: W) -> LineChannel<R, W> {
        LineChannel {
            reader,
            writer,
            line: String::new(),
        }
    }
}

impl<R: BufRead, W: Write> BodyChannel for LineChannel<R, W> {
    fn recv(&mut self) -> io::Result<Option<BodyMsg>> {
        self.line.clear();
        let n = self.reader.read_line(&mut self.line)?;
        if n == 0 {
            return Ok(None); // clean EOF — the body closed its side.
        }
        let trimmed = self.line.trim_end_matches(['\n', '\r']);
        if trimmed.is_empty() {
            // A blank keep-alive line; treat as "nothing yet", try the next.
            return self.recv();
        }
        let msg: BodyMsg = serde_json::from_str(trimmed)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        Ok(Some(msg))
    }

    fn send(&mut self, verdict: &Verdict) -> io::Result<()> {
        let mut buf = serde_json::to_string(verdict)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        buf.push('\n');
        self.writer.write_all(buf.as_bytes())?;
        self.writer.flush()
    }
}

/// Why a [`Proposal`] could not become an `AgentAction`. The host refuses these
/// in-band (a [`Verdict::refuse`]) — the braid never sees them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MapError {
    /// A `cell-write` / `cell-read` proposal without its required `path`.
    MissingPath(String),
    /// A `cell-write` proposal without its `value`.
    MissingValue,
    /// A `Spend` proposal whose `amount_cents` is not `> 0`.
    NonPositiveSpend(i64),
}

impl std::fmt::Display for MapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MapError::MissingPath(t) => write!(f, "proposal `{t}` needs a `path`"),
            MapError::MissingValue => write!(f, "`cell-write` needs a `value`"),
            MapError::NonPositiveSpend(a) => {
                write!(f, "spend amount must be > 0, got {a}")
            }
        }
    }
}

/// Translate a body's [`Proposal`] into the grain's `AgentAction` vocabulary.
///
/// The mapping is intentionally total over the well-formed shapes and refuses
/// the rest in-band (so a malformed proposal costs nothing and never reaches the
/// braid):
/// - any proposal with `amount_cents` ⇒ the priced [`AgentAction::Spend`] rail
///   (the service is `tool` with an optional `spend:` / `invoke:` prefix stripped);
/// - `cell-write` ⇒ [`AgentAction::CellWrite`] (needs `path` + `value`);
/// - `cell-read` ⇒ [`AgentAction::CellRead`] (needs `path`);
/// - anything else ⇒ [`AgentAction::Invoke`] (a bare or `invoke:`-prefixed call).
pub fn map_proposal(p: &Proposal) -> Result<AgentAction, MapError> {
    let service = || {
        p.tool
            .strip_prefix("invoke:")
            .or_else(|| p.tool.strip_prefix("spend:"))
            .unwrap_or(&p.tool)
            .to_string()
    };
    if let Some(amount) = p.amount_cents {
        if amount <= 0 {
            return Err(MapError::NonPositiveSpend(amount));
        }
        return Ok(AgentAction::Spend {
            service: service(),
            amount_cents: amount,
        });
    }
    match p.tool.as_str() {
        "cell-write" => {
            let path = p
                .path
                .clone()
                .ok_or_else(|| MapError::MissingPath("cell-write".into()))?;
            let value = p.value.clone().ok_or(MapError::MissingValue)?;
            Ok(AgentAction::CellWrite { path, value })
        }
        "cell-read" => {
            let path = p
                .path
                .clone()
                .ok_or_else(|| MapError::MissingPath("cell-read".into()))?;
            Ok(AgentAction::CellRead { path })
        }
        _ => Ok(AgentAction::Invoke { service: service() }),
    }
}

/// An [`AgentBrain`] whose actions come from a jailed body over a
/// [`BodyChannel`].
///
/// The drive loop calls [`next_action`](AgentBrain::next_action) to pull the
/// next proposal (translated to an `AgentAction`) and
/// [`observe`](AgentBrain::observe) to hand back the braid's verdict, which this
/// brain forwards to the body. Unmappable proposals are refused in-band and the
/// brain reads on. A `Done` message or a closed channel ends the drive.
pub struct ConfinedBrain<C: BodyChannel> {
    body: C,
    done: bool,
    /// Count of proposals the host refused in-band (never reached the braid).
    unmapped_refusals: u64,
}

impl<C: BodyChannel> ConfinedBrain<C> {
    /// A confined brain driven by `body`.
    pub fn new(body: C) -> ConfinedBrain<C> {
        ConfinedBrain {
            body,
            done: false,
            unmapped_refusals: 0,
        }
    }

    /// How many proposals were refused in-band for being unmappable/malformed
    /// (a health signal: a well-behaved body produces zero).
    pub fn unmapped_refusals(&self) -> u64 {
        self.unmapped_refusals
    }

    /// Consume the brain, returning the underlying channel (to close the jail).
    pub fn into_body(self) -> C {
        self.body
    }
}

impl<C: BodyChannel> AgentBrain for ConfinedBrain<C> {
    fn next_action(&mut self, _step: u64) -> Option<AgentAction> {
        loop {
            if self.done {
                return None;
            }
            match self.body.recv() {
                Ok(Some(BodyMsg::Propose(p))) => match map_proposal(&p) {
                    Ok(action) => return Some(action),
                    Err(reason) => {
                        // Unmappable: refuse in-band, tell the body, read on.
                        // A send failure means the body is gone — end the drive.
                        self.unmapped_refusals += 1;
                        if self
                            .body
                            .send(&Verdict::refuse(reason.to_string()))
                            .is_err()
                        {
                            self.done = true;
                            return None;
                        }
                        continue;
                    }
                },
                // Done, clean EOF, or a broken channel all end the drive. A
                // protocol/parse error ends it fail-closed (never fabricate an
                // action from garbage).
                Ok(Some(BodyMsg::Done(_))) | Ok(None) | Err(_) => {
                    self.done = true;
                    return None;
                }
            }
        }
    }

    fn observe(&mut self, obs: &ActionObservation) {
        let verdict = Verdict {
            admitted: obs.admitted,
            refusal: obs.refusal.clone(),
            tool_ok: obs.tool_ok,
            summary: obs.tool_summary.clone(),
        };
        // If the body has gone, stop driving on the next pull.
        if self.body.send(&verdict).is_err() {
            self.done = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    /// A channel that reads pre-seeded body lines from a cursor and captures the
    /// host's verdicts into a shared buffer we can assert on.
    fn channel(body_lines: &str) -> LineChannel<Cursor<Vec<u8>>, Vec<u8>> {
        LineChannel::new(Cursor::new(body_lines.as_bytes().to_vec()), Vec::new())
    }

    fn line(msg: &BodyMsg) -> String {
        let mut s = serde_json::to_string(msg).unwrap();
        s.push('\n');
        s
    }

    #[test]
    fn maps_every_action_shape() {
        assert_eq!(
            map_proposal(&Proposal::invoke("check_health")).unwrap(),
            AgentAction::Invoke {
                service: "check_health".into()
            }
        );
        assert_eq!(
            map_proposal(&Proposal::invoke("invoke:check_health")).unwrap(),
            AgentAction::Invoke {
                service: "check_health".into()
            },
            "the invoke: prefix is stripped to the bare service"
        );
        assert_eq!(
            map_proposal(&Proposal {
                tool: "spend:stripe_pay".into(),
                amount_cents: Some(250),
                path: None,
                value: None,
            })
            .unwrap(),
            AgentAction::Spend {
                service: "stripe_pay".into(),
                amount_cents: 250
            }
        );
        assert_eq!(
            map_proposal(&Proposal {
                tool: "cell-write".into(),
                amount_cents: None,
                path: Some("notes/1".into()),
                value: Some("hello".into()),
            })
            .unwrap(),
            AgentAction::CellWrite {
                path: "notes/1".into(),
                value: "hello".into()
            }
        );
        assert_eq!(
            map_proposal(&Proposal {
                tool: "cell-read".into(),
                amount_cents: None,
                path: Some("notes/1".into()),
                value: None,
            })
            .unwrap(),
            AgentAction::CellRead {
                path: "notes/1".into()
            }
        );
    }

    #[test]
    fn refuses_malformed_proposals() {
        assert_eq!(
            map_proposal(&Proposal {
                tool: "cell-write".into(),
                amount_cents: None,
                path: Some("p".into()),
                value: None,
            }),
            Err(MapError::MissingValue)
        );
        assert_eq!(
            map_proposal(&Proposal {
                tool: "cell-read".into(),
                amount_cents: None,
                path: None,
                value: None,
            }),
            Err(MapError::MissingPath("cell-read".into()))
        );
        assert_eq!(
            map_proposal(&Proposal {
                tool: "stripe_pay".into(),
                amount_cents: Some(0),
                path: None,
                value: None,
            }),
            Err(MapError::NonPositiveSpend(0))
        );
    }

    #[test]
    fn drives_proposals_then_done() {
        let body = format!(
            "{}{}{}",
            line(&BodyMsg::Propose(Proposal::invoke("a"))),
            line(&BodyMsg::Propose(Proposal::invoke("b"))),
            line(&BodyMsg::Done(DoneNote::default())),
        );
        let mut brain = ConfinedBrain::new(channel(&body));

        // First proposal → Invoke{a}; observe an admit.
        assert_eq!(
            brain.next_action(0),
            Some(AgentAction::Invoke {
                service: "a".into()
            })
        );
        brain.observe(&ActionObservation {
            action: "invoke:a".into(),
            admitted: true,
            refusal: None,
            tool_ok: Some(true),
            tool_summary: Some("ok".into()),
        });
        // Second → Invoke{b}.
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
        // Done → stop.
        assert_eq!(brain.next_action(2), None);
        assert_eq!(brain.next_action(3), None, "stays stopped");

        // The two verdicts were framed back to the body, one per line.
        let out = String::from_utf8(brain.into_body().writer).unwrap();
        let verdicts: Vec<Verdict> = out
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        assert_eq!(verdicts.len(), 2);
        assert!(verdicts[0].admitted && verdicts[0].tool_ok == Some(true));
        assert!(!verdicts[1].admitted && verdicts[1].refusal.as_deref() == Some("no cap"));
    }

    #[test]
    fn unmappable_proposal_is_refused_in_band_then_drive_continues() {
        // A malformed cell-write (no value), then a good invoke, then done.
        let body = format!(
            "{}{}{}",
            line(&BodyMsg::Propose(Proposal {
                tool: "cell-write".into(),
                amount_cents: None,
                path: Some("p".into()),
                value: None,
            })),
            line(&BodyMsg::Propose(Proposal::invoke("recover"))),
            line(&BodyMsg::Done(DoneNote::default())),
        );
        let mut brain = ConfinedBrain::new(channel(&body));

        // The malformed one is refused in-band (never surfaced as an action);
        // next_action skips past it to the good proposal.
        assert_eq!(
            brain.next_action(0),
            Some(AgentAction::Invoke {
                service: "recover".into()
            })
        );
        assert_eq!(brain.unmapped_refusals(), 1);
        brain.observe(&ActionObservation {
            action: "invoke:recover".into(),
            admitted: true,
            refusal: None,
            tool_ok: Some(true),
            tool_summary: None,
        });
        assert_eq!(brain.next_action(1), None);

        // The body saw: one in-band refusal (the malformed write) + one admit.
        let out = String::from_utf8(brain.into_body().writer).unwrap();
        let verdicts: Vec<Verdict> = out
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        assert_eq!(verdicts.len(), 2);
        assert!(!verdicts[0].admitted, "the malformed write was refused");
        assert!(verdicts[0].refusal.as_deref().unwrap().contains("value"));
        assert!(verdicts[1].admitted, "the recover invoke was admitted");
    }

    #[test]
    fn garbage_line_ends_the_drive_fail_closed() {
        let body = "this is not json\n";
        let mut brain = ConfinedBrain::new(channel(body));
        // A parse error must NOT fabricate an action — it ends the drive.
        assert_eq!(brain.next_action(0), None);
    }
}
