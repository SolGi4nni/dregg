//! THE CV-BRIDGE (milestone #1) — "blame this cell": ClusterVision's provenance,
//! live in the deos inspector.
//!
//! `docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md` §2.5/§3.3 names the smallest
//! end-to-end bridge between deos and ClusterVision (`cv`, `~/dev/cv`): a deos
//! inspector pane whose "why does this cell exist?" answer is a cv provenance
//! query, rendered as a [`Presentable`]. cv ships the provenance today (the event
//! catalog + `cv blame <file>`: a file's git history tied back to the agent
//! conversation whose reasoning wrote it); deos adds exactly ONE Presentable.
//!
//! ## The honest call: bridge EXTERNALLY, query cv as the read/query face
//!
//! Per §2.4, cv stays the fast, lossless, external corpus + index; this is the
//! read/query boundary, NOT a ride on the cell substrate (that is the later
//! witnessed-promotion milestone — a cv span lifted into a witnessed document
//! cell). The substrate is UNTOUCHED. We dial cv as a subprocess — the simplest
//! honest bridge, and `cv blame` is cv's own provenance entry
//! (`cv:crates/cv/src/blame.rs`). We do NOT reimplement the correlation: we run
//! `cv blame <path>` and project its (stable, documented) output into the L1
//! presentation bodies.
//!
//! ## Why a subprocess (not the cvd HTTP API or cv-mcp)
//!
//! The §2.5 design lists three dialers — `cv-mcp` (the MCP server an agent uses
//! mid-task), the `cvd` HTTP daemon, and the `cv` CLI. The CLI subprocess is the
//! "simplest honest bridge": no daemon to stand up, no MCP transport to host, no
//! new dependency on cv's crates (which we must NOT edit). `cv blame` is the exact
//! provenance verb the milestone names; its text output is a documented, stable
//! contract (a `✦ blame` header, `◆ <short> <date> <summary>` commit rows, indented
//! `<harness> <session> <date> <title> edit at msg N (<delta>)` match rows, and a
//! `provenance: K of N` summary). We parse that into a [`CvBlame`].
//!
//! ## Graceful degradation — never a fake
//!
//! cv may be absent from PATH (the `embedded-executor` build does not depend on
//! cv), or it may find no agent session for a freshly-written or rebased file. In
//! both cases the Presentable renders an HONEST line ("cv not available on PATH" /
//! "no agent session correlated this file's commits") — never a fabricated
//! provenance edge. This is the `feedback-green-or-bust` discipline: degrade
//! loudly and truthfully, never paper over the gap.
//!
//! ## The shape
//!
//!   * [`CvBlame`] — the parsed result of `cv blame <path>`: the file, the matched
//!     commits, and the best agent sessions correlated to them. Pure data; the
//!     parser ([`CvBlame::parse`]) is unit-tested against real `cv` output without
//!     spawning the binary.
//!   * [`CvProvenance`] — the [`Presentable`]. For a focused cell + its backing
//!     source path it answers "why does this cell exist" with three lenses:
//!       - **Provenance** ← a [`TimelineView`]: one event per matched commit, the
//!         agent · session · reasoning-excerpt that wrote it (the two-way link of
//!         `DOCUMENT-LANGUAGE.md` §1.1, read backward through cv's event catalog).
//!       - **Source** ← a [`PresentationBody::Prose`] "what-is" summary (how cv was
//!         dialed, what it found, the honest limits).
//!       - **RawFields** ← the mandatory L1 floor.
//!
//! Everything renders through the SAME generic `cockpit::render_presentation_body`
//! (Timeline / Prose / Fields are already handled), so no new gpui code is needed.

use std::process::Command;

use dregg_cell::CellId;

use crate::presentable::{
    PresentCtx, Presentable, Presentation, PresentationBody, PresentationKind, TimelineEvent,
    TimelineView,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};

/// The `cv` binary name — dialed off PATH (`which cv` resolves it in the dev
/// environment; absent in a deployment that ships no cv, which degrades honestly).
const CV_BIN: &str = "cv";

// ===========================================================================
// §1 — the parsed cv-blame result (pure data; the bridge's read face)
// ===========================================================================

/// One agent session `cv blame` correlated to a commit that touched the file — a
/// row of the two-way link read backward (file → the conversation that wrote it).
/// Every field is parsed from `cv blame`'s output; nothing is fabricated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CvSession {
    /// The harness the session ran under (`claude`, `codex`, `gemini`, …).
    pub harness: String,
    /// The short session id (cv's `crate::short_id` form — the navigable handle).
    pub session: String,
    /// The session's recorded date (`YYYY-MM-DD`), if cv printed one.
    pub date: String,
    /// The edit's title / a short reasoning excerpt, if the session carried one.
    pub title: String,
    /// How cv tied this session to the commit (its `(8m before commit)` /
    /// `(weak: …)` annotation) — the correlation strength, surfaced verbatim.
    pub correlation: String,
    /// The `cv show <session> --range A-B` hint cv printed (the deep-link into the
    /// conversation window around the edit). Empty when cv printed none.
    pub show_hint: String,
}

/// One commit `cv blame` reports as touching the file, with the best agent
/// sessions it correlated. The commit is git's record; the sessions are cv's
/// event-catalog correlation — together, "why does this code exist".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CvCommit {
    /// The short commit hash.
    pub short: String,
    /// The commit date (`YYYY-MM-DD`).
    pub date: String,
    /// The commit summary line.
    pub summary: String,
    /// The agent sessions cv correlated to this commit (best-first; possibly
    /// empty — cv prints "(no agent session found)" then, which we record as no
    /// sessions, honestly).
    pub sessions: Vec<CvSession>,
}

/// The full parsed `cv blame <path>` result — the bridge's read of cv's
/// provenance graph for one file. Distinguishes the honest outcomes the
/// Presentable renders distinctly: cv absent, cv ran but found no commits / no
/// correlated sessions, or a real provenance answer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CvBlame {
    /// The path cv was asked about (the cell's backing source file).
    pub path: String,
    /// `true` iff the `cv` binary could be invoked at all. `false` ⟹ the honest
    /// "cv not available" degrade (never a fabricated answer).
    pub cv_available: bool,
    /// The commits cv reported, newest-first (empty when cv found none / is absent).
    pub commits: Vec<CvCommit>,
    /// The header / status line cv printed (or our degrade message) — surfaced so
    /// the operator reads exactly what cv said, including its honest limits.
    pub note: String,
}

impl CvBlame {
    /// Dial cv for real: run `cv blame <path>` and parse its output. A missing
    /// `cv` binary (NotFound) degrades to [`CvBlame::unavailable`] — the honest
    /// "cv not on PATH" readout, never an error and never a fake.
    ///
    /// This is the ONLY function that spawns a subprocess; everything else is pure
    /// (so the Presentable and its tests run without cv present).
    pub fn dial(path: &str) -> Self {
        match Command::new(CV_BIN).arg("blame").arg(path).output() {
            Ok(out) => {
                // cv prints its provenance to stdout; a real failure (bad path,
                // git missing) lands on stderr with a non-zero status — surfaced
                // honestly in `note`, never swallowed.
                let stdout = String::from_utf8_lossy(&out.stdout);
                if out.status.success() {
                    CvBlame::parse(path, &stdout)
                } else {
                    let stderr = String::from_utf8_lossy(&out.stderr);
                    let msg = stderr.trim();
                    CvBlame {
                        path: path.to_string(),
                        cv_available: true,
                        commits: Vec::new(),
                        note: if msg.is_empty() {
                            "cv blame exited non-zero (no provenance for this path)".to_string()
                        } else {
                            format!("cv blame: {msg}")
                        },
                    }
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => CvBlame::unavailable(path),
            Err(e) => CvBlame {
                path: path.to_string(),
                cv_available: false,
                commits: Vec::new(),
                note: format!("could not run `cv blame`: {e}"),
            },
        }
    }

    /// The honest "cv not on PATH" result — the graceful degrade the Presentable
    /// renders when cv is absent (a deployment that ships no ClusterVision).
    pub fn unavailable(path: &str) -> Self {
        CvBlame {
            path: path.to_string(),
            cv_available: false,
            commits: Vec::new(),
            note: "cv not available on PATH — install ClusterVision (`cv`) to see \
                   the agent reasoning that wrote this cell's backing file"
                .to_string(),
        }
    }

    /// THE PARSER — project `cv blame`'s text output into the structured result.
    /// Pure (no subprocess), so it is unit-tested against captured real `cv`
    /// output. The output grammar (`cv:crates/cv/src/blame.rs`):
    ///
    /// ```text
    /// ✦ blame <rel> — N commit(s)[ (of M; …)]
    ///
    /// ◆ <short> <date>  <summary>
    ///   <harness> <session>  <date>  ["<title>"  ]edit at msg <n> (<delta>)[ · other checkout]
    ///     ↳ cv show <session> --range A-B
    ///   (no agent session found)
    ///
    /// provenance: K of N commit(s) matched an agent session
    /// ```
    ///
    /// We key on the line glyphs (`◆` a commit, the `↳` a show-hint, the leading
    /// indent + non-`↳` a match row) — robust to the exact spacing.
    pub fn parse(path: &str, text: &str) -> Self {
        let mut commits: Vec<CvCommit> = Vec::new();
        let mut header = String::new();
        let mut provenance_line = String::new();

        for raw in text.lines() {
            let line = raw.trim_end();
            let trimmed = line.trim_start();
            if trimmed.is_empty() {
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("✦") {
                header = rest.trim().to_string();
            } else if let Some(rest) = trimmed.strip_prefix("◆") {
                commits.push(parse_commit_line(rest.trim()));
            } else if let Some(rest) = trimmed.strip_prefix("↳") {
                // A `cv show … --range …` hint attaches to the last session of the
                // current commit (cv prints it directly under its match row).
                if let Some(last) = commits.last_mut().and_then(|c| c.sessions.last_mut()) {
                    last.show_hint = rest.trim().to_string();
                }
            } else if trimmed.starts_with("(no agent session found)") {
                // The commit matched nothing — recorded as zero sessions, honestly.
            } else if trimmed.starts_with("provenance:") {
                provenance_line = trimmed.to_string();
            } else if line.starts_with(' ') || line.starts_with('\t') {
                // An indented, non-glyph line under a commit = a session match row.
                if let Some(commit) = commits.last_mut() {
                    if let Some(s) = parse_session_line(trimmed) {
                        commit.sessions.push(s);
                    }
                }
            }
        }

        // The note prefers cv's own provenance summary (it states K-of-N matched),
        // falling back to the header (the commit count) when cv printed no summary
        // (e.g. the not-in-a-git-repo event-catalog-only path).
        let note = if !provenance_line.is_empty() {
            provenance_line
        } else if !header.is_empty() {
            format!("cv blame {header}")
        } else {
            "cv blame produced no provenance for this path".to_string()
        };

        CvBlame {
            path: path.to_string(),
            cv_available: true,
            commits,
            note,
        }
    }

    /// Every agent session correlated across all commits, best-first (the flat
    /// "who wrote this" list — the backlink rows the timeline renders).
    pub fn sessions(&self) -> Vec<(&CvCommit, &CvSession)> {
        let mut out = Vec::new();
        for c in &self.commits {
            for s in &c.sessions {
                out.push((c, s));
            }
        }
        out
    }

    /// Did cv correlate at least one agent session (a real "why it exists" answer,
    /// vs. an honest empty readout)?
    pub fn has_provenance(&self) -> bool {
        self.commits.iter().any(|c| !c.sessions.is_empty())
    }
}

/// Parse a `◆ <short> <date>  <summary>` commit line into its parts. The hash and
/// date are whitespace-delimited; everything after the date is the summary.
fn parse_commit_line(s: &str) -> CvCommit {
    let mut it = s.splitn(3, char::is_whitespace).filter(|t| !t.is_empty());
    let short = it.next().unwrap_or("").to_string();
    // The date may be followed by ≥2 spaces before the summary; re-split robustly.
    let rest = s
        .strip_prefix(&short)
        .map(|r| r.trim_start())
        .unwrap_or("")
        .to_string();
    let (date, summary) = match rest.split_once(char::is_whitespace) {
        Some((d, sum)) => (d.to_string(), sum.trim_start().to_string()),
        None => (rest, String::new()),
    };
    CvCommit {
        short,
        date,
        summary,
        sessions: Vec::new(),
    }
}

/// Parse a session match row:
/// `<harness> <session>  <date>  ["<title>"  ]edit at msg <n> (<corr>)[ · …]`.
/// Returns `None` for an indented line that is not a match row (defensive).
fn parse_session_line(s: &str) -> Option<CvSession> {
    let mut it = s.split_whitespace();
    let harness = it.next()?.to_string();
    let session = it.next()?.to_string();
    // The 3rd token is the date when it looks like `YYYY-MM-DD` (or cv's `----------`
    // placeholder for a dateless harness); otherwise the session had no date column.
    let third = it.clone().next().unwrap_or("");
    let date = if looks_like_date(third) {
        it.next();
        third.to_string()
    } else {
        String::new()
    };
    // The correlation annotation is the parenthesized tail (`(8m before commit)`,
    // `(weak: …)`). The title is whatever sits between the date and `edit at msg`.
    let rest = remainder_after(s, &[&harness, &session, &date]);
    let correlation = extract_parens(&rest);
    let title = extract_title(&rest);
    Some(CvSession {
        harness,
        session,
        date,
        title,
        correlation,
        show_hint: String::new(),
    })
}

/// `true` iff `t` is a `YYYY-MM-DD` date or cv's `----------` dateless placeholder.
fn looks_like_date(t: &str) -> bool {
    t == "----------"
        || (t.len() == 10
            && t.as_bytes().iter().enumerate().all(|(i, &b)| {
                if i == 4 || i == 7 {
                    b == b'-'
                } else {
                    b.is_ascii_digit()
                }
            }))
}

/// The substring of `s` after the leading `tokens` (each consumed once, in order)
/// — the part of a match row past the harness/session/date columns.
fn remainder_after(s: &str, tokens: &[&str]) -> String {
    let mut rest = s.to_string();
    for t in tokens {
        if t.is_empty() {
            continue;
        }
        if let Some(idx) = rest.find(t) {
            rest = rest[idx + t.len()..].to_string();
        }
    }
    rest.trim().to_string()
}

/// The last parenthesized group of `s` (cv's correlation annotation), unwrapped.
fn extract_parens(s: &str) -> String {
    match (s.rfind('('), s.rfind(')')) {
        (Some(a), Some(b)) if b > a => s[a + 1..b].trim().to_string(),
        _ => String::new(),
    }
}

/// The title cv prints between the date and `edit at msg` (quoted), if any.
fn extract_title(s: &str) -> String {
    if let Some(open) = s.find('"') {
        if let Some(close) = s[open + 1..].find('"') {
            return s[open + 1..open + 1 + close].to_string();
        }
    }
    String::new()
}

// ===========================================================================
// §2 — the Presentable: "blame this cell"
// ===========================================================================

/// THE CV-BRIDGE PRESENTABLE — answers "why does this cell exist?" for a focused
/// cell by querying cv for the agent reasoning that wrote its backing source file.
///
/// It carries the cell id (the focus identity) and the backing source PATH the
/// question is keyed on — because a content-addressed cell does not itself carry a
/// filesystem path; the caller (the cell inspector) supplies the file the cell is
/// backed by, and cv answers "who wrote that file, and what were they thinking".
/// This is the §2.3 "deos query → cv query" projection in one gesture.
#[derive(Clone, Debug)]
pub struct CvProvenance {
    /// The focused cell (the inspector's aim — the navigable identity).
    pub cell: CellId,
    /// The cell's backing source file — the path `cv blame` is dialed on.
    pub source_path: String,
    /// The parsed cv-blame result (dialed live, or stubbed in tests).
    pub blame: CvBlame,
}

impl CvProvenance {
    /// Build by dialing cv LIVE for the cell's backing source path. A missing cv
    /// degrades honestly inside [`CvBlame::dial`].
    pub fn dial(cell: CellId, source_path: impl Into<String>) -> Self {
        let source_path = source_path.into();
        let blame = CvBlame::dial(&source_path);
        CvProvenance {
            cell,
            source_path,
            blame,
        }
    }

    /// Build from an already-parsed [`CvBlame`] (the pure path — tests and any
    /// caller that dialed cv once and reuses the result).
    pub fn from_blame(cell: CellId, blame: CvBlame) -> Self {
        let source_path = blame.path.clone();
        CvProvenance {
            cell,
            source_path,
            blame,
        }
    }

    /// The provenance [`TimelineView`]: one event per matched commit→session pair
    /// (agent · session · reasoning-excerpt · the commit it wrote), newest-first.
    /// When cv found no correlated session the timeline is empty — the Presentable
    /// then speaks an honest "no provenance" line, never a fabricated event.
    fn provenance_timeline(&self) -> TimelineView {
        let mut events: Vec<TimelineEvent> = Vec::new();
        for (i, (commit, session)) in self.blame.sessions().into_iter().enumerate() {
            let excerpt = if session.title.is_empty() {
                String::new()
            } else {
                format!(" · “{}”", session.title)
            };
            let corr = if session.correlation.is_empty() {
                String::new()
            } else {
                format!(" ({})", session.correlation)
            };
            events.push(TimelineEvent {
                at: i as u64,
                label: format!(
                    "{} {} wrote {} {}{}{}",
                    session.harness, session.session, commit.short, commit.summary, excerpt, corr
                ),
                // The commit hash is git's record (text, not a 32-byte protocol
                // hash), so we carry no navigable `hash` here — the show_hint is
                // the deep-link cv prints (surfaced in the Source prose).
                hash: None,
            });
        }
        TimelineView { events }
    }

    /// The Source/"what-is" prose: how cv was dialed, what it found, and cv's own
    /// honest limits — so the operator reads exactly the provenance answer's
    /// provenance (the bridge is legible, never a black box).
    fn source_prose(&self) -> String {
        let mut s = String::new();
        s.push_str("WHY DOES THIS CELL EXIST? — cv-bridge (ClusterVision provenance)\n\n");
        s.push_str(&format!(
            "cell      {}\n",
            reflect::short_hex(self.cell.as_bytes())
        ));
        s.push_str(&format!("backed by {}\n", self.source_path));
        s.push_str(&format!(
            "dialed    `cv blame {}`  (subprocess to the cv binary — the read/query face)\n\n",
            self.source_path
        ));
        s.push_str(&self.blame.note);
        s.push('\n');

        if !self.blame.cv_available {
            s.push_str(
                "\n(honest degrade: cv is not on PATH, so no agent reasoning is shown — \
                 this is the read boundary, never a fabricated answer.)",
            );
            return s;
        }
        if !self.blame.has_provenance() {
            s.push_str(
                "\ncv ran but correlated no agent session to this file's commits — a freshly \
                 written, rebased, or squash-merged file falls outside cv's time-correlation \
                 window (`cv touched` may still list edits). An honest empty readout, not a fake.",
            );
            return s;
        }
        // A real answer: list the show-hints (the deep-links into the reasoning).
        s.push_str("\nthe agent conversation(s) whose reasoning wrote this cell's file:\n");
        for (_c, session) in self.blame.sessions() {
            if !session.show_hint.is_empty() {
                s.push_str(&format!("  · {}\n", session.show_hint));
            }
        }
        s.push_str(
            "\nNEXT (witnessed promotion): lift a cv session-span into a witnessed document \
             cell — a turn that transcludes the cv span, content-addressed and cap-gated; the \
             promotion's receipt becomes the cell's provenance (REFLEXIVE-DISTRIBUTED-IMAGE §2.4).",
        );
        s
    }

    /// The RawFields floor — a compact field tree summarizing the bridge result
    /// (the mandatory L1 universal-coverage floor).
    fn raw_fields(&self) -> Inspectable {
        let mut fields = vec![
            Field::id("cell", *self.cell.as_bytes()),
            Field::text("backed_by", self.source_path.clone()),
            Field::boolean("cv_available", self.blame.cv_available),
            Field::count("commits", self.blame.commits.len() as u64),
            Field::count("correlated_sessions", self.blame.sessions().len() as u64),
        ];
        fields.push(Field::text("status", self.blame.note.clone()));
        Inspectable {
            kind: ObjectKind::Cell,
            title: format!(
                "Provenance · Cell {}",
                reflect::short_hex(self.cell.as_bytes())
            ),
            subtitle: format!("cv blame {}", self.source_path),
            fields,
        }
    }
}

impl Presentable for CvProvenance {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor.
        let insp = self.raw_fields();
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Provenance Summary".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Provenance — the agent-reasoning timeline (the two-way link backward).
        let timeline = self.provenance_timeline();
        let prov_text = timeline
            .events
            .iter()
            .map(|e| e.label.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Why This Cell Exists".to_string(),
            search_text: format!("cv blame provenance agent {}", prov_text),
            body: PresentationBody::Timeline(timeline),
        });

        // (3) Source — the "what-is" prose (how cv was dialed + honest limits).
        let prose = self.source_prose();
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "cv-bridge".to_string(),
            search_text: format!("cv clustervision bridge {}", self.source_path),
            body: PresentationBody::Prose(prose),
        });

        out
    }
}

// ===========================================================================
// TESTS — the bridge proven gpui-free + cv-free (the parser against real cv
// output; the Presentable over stubbed + degraded results).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::PresentableExt;
    use crate::world::World;

    fn ctx_world() -> (World, CellId) {
        let mut w = World::new();
        let cell = w.genesis_cell(0x11, 1_000);
        (w, cell)
    }

    /// Real `cv blame` output (captured from the live binary over a file with a
    /// matched agent session) — the parser's golden fixture.
    const REAL_BLAME_MATCHED: &str = "\
✦ blame circuit/src/lib.rs — 3 commit(s) (of 42; showing the most recent)

◆ 0e352e428 2026-06-19  climb-out (Lean): the KERNEL BRIDGE + faithful chip-table
  claude   a4cfe7cb  2026-06-19  \"the cap-reshape linchpin work\"  edit at msg 142 (8m before commit)
    ↳ cv show a4cfe7cb --range 139-145
  codex    7fd8f4b6  2026-06-19  edit at msg 7 (2h10m before commit)
    ↳ cv show 7fd8f4b6 --range 4-10
◆ b6a64bd0f 2026-06-18  climb-out (Lean half, green 4015)
  (no agent session found)

provenance: 1 of 2 commit(s) matched an agent session
";

    #[test]
    fn parses_real_cv_blame_output_into_commits_and_sessions() {
        let blame = CvBlame::parse("circuit/src/lib.rs", REAL_BLAME_MATCHED);
        assert!(blame.cv_available);
        assert_eq!(blame.commits.len(), 2, "two ◆ commit rows");

        let c0 = &blame.commits[0];
        assert_eq!(c0.short, "0e352e428");
        assert_eq!(c0.date, "2026-06-19");
        assert!(c0.summary.contains("KERNEL BRIDGE"));
        assert_eq!(
            c0.sessions.len(),
            2,
            "two correlated sessions under the first commit"
        );

        let s0 = &c0.sessions[0];
        assert_eq!(s0.harness, "claude");
        assert_eq!(s0.session, "a4cfe7cb");
        assert_eq!(s0.date, "2026-06-19");
        assert_eq!(s0.title, "the cap-reshape linchpin work");
        assert_eq!(s0.correlation, "8m before commit");
        assert_eq!(s0.show_hint, "cv show a4cfe7cb --range 139-145");

        // A title-less session still parses (codex row, no quoted title).
        let s1 = &c0.sessions[1];
        assert_eq!(s1.harness, "codex");
        assert_eq!(s1.correlation, "2h10m before commit");
        assert!(s1.title.is_empty());

        // The second commit matched nothing — zero sessions, honestly.
        assert!(blame.commits[1].sessions.is_empty());

        // The note carries cv's own provenance summary.
        assert!(blame.note.contains("provenance: 1 of 2"));
        assert!(blame.has_provenance());
    }

    #[test]
    fn the_presentable_builds_a_real_provenance_timeline_from_a_stubbed_cv_result() {
        let (w, cell) = ctx_world();
        let blame = CvBlame::parse("circuit/src/lib.rs", REAL_BLAME_MATCHED);
        let view = CvProvenance::from_blame(cell, blame);
        let ctx = PresentCtx::new(&w, cell);

        // The mandatory floor is present.
        assert!(view.has_raw_fields_floor(&ctx), "RawFields is the L1 floor");

        let set = view.present(&ctx);
        // RawFields + Provenance + Source.
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        assert!(set.iter().any(|p| p.kind == PresentationKind::Source));

        let prov = set
            .iter()
            .find(|p| p.kind == PresentationKind::Provenance)
            .expect("the Provenance lens is present");
        match &prov.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(
                    t.events.len(),
                    2,
                    "one event per matched commit→session pair"
                );
                let blob = t
                    .events
                    .iter()
                    .map(|e| e.label.clone())
                    .collect::<Vec<_>>()
                    .join("\n");
                assert!(
                    blob.contains("claude a4cfe7cb"),
                    "names the agent + session"
                );
                assert!(blob.contains("0e352e428"), "names the commit it wrote");
                assert!(
                    blob.contains("cap-reshape linchpin"),
                    "carries the reasoning excerpt"
                );
            }
            other => panic!("Provenance must carry a Timeline, got {other:?}"),
        }

        // The Source prose names the dial + the next (witnessed-promotion) rung.
        let src = set
            .iter()
            .find(|p| p.kind == PresentationKind::Source)
            .unwrap();
        match &src.body {
            PresentationBody::Prose(p) => {
                assert!(
                    p.contains("cv blame circuit/src/lib.rs"),
                    "shows how cv was dialed"
                );
                assert!(
                    p.contains("witnessed promotion"),
                    "names the next milestone"
                );
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn degrades_honestly_when_cv_is_absent_never_a_fake() {
        let (w, cell) = ctx_world();
        // The cv-absent path (as if `cv` were not on PATH).
        let view =
            CvProvenance::from_blame(cell, CvBlame::unavailable("starbridge-v2/src/world.rs"));
        let ctx = PresentCtx::new(&w, cell);
        let set = view.present(&ctx);

        // The timeline is EMPTY (no fabricated events).
        let prov = set
            .iter()
            .find(|p| p.kind == PresentationKind::Provenance)
            .unwrap();
        match &prov.body {
            PresentationBody::Timeline(t) => assert!(t.events.is_empty(), "no fake provenance"),
            _ => unreachable!(),
        }
        // The Source prose says so honestly.
        let src = set
            .iter()
            .find(|p| p.kind == PresentationKind::Source)
            .unwrap();
        match &src.body {
            PresentationBody::Prose(p) => {
                assert!(
                    p.contains("cv not available on PATH"),
                    "honest cv-absent line"
                );
                assert!(
                    p.to_lowercase().contains("never a fabricated"),
                    "states it is not faked"
                );
            }
            _ => unreachable!(),
        }
        // The RawFields floor records cv_available = false.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .unwrap();
        if let PresentationBody::Fields(i) = &raw.body {
            assert!(i.fields.iter().any(|f| f.key == "cv_available"));
        }
    }

    #[test]
    fn cv_ran_but_found_no_correlated_session_is_an_honest_empty_readout() {
        // cv printed commits but matched no agent session (a fresh/rebased file).
        const NO_MATCH: &str = "\
✦ blame starbridge-v2/src/cv_provenance.rs — 1 commit(s)

◆ deadbeef0 2026-06-19  cv-bridge: blame this cell
  (no agent session found)

provenance: 0 of 1 commit(s) matched an agent session
";
        let (w, cell) = ctx_world();
        let blame = CvBlame::parse("starbridge-v2/src/cv_provenance.rs", NO_MATCH);
        assert!(blame.cv_available, "cv ran");
        assert_eq!(blame.commits.len(), 1);
        assert!(!blame.has_provenance(), "no session correlated");

        let view = CvProvenance::from_blame(cell, blame);
        let set = view.present(&PresentCtx::new(&w, cell));
        let src = set
            .iter()
            .find(|p| p.kind == PresentationKind::Source)
            .unwrap();
        match &src.body {
            PresentationBody::Prose(p) => {
                assert!(
                    p.contains("correlated no agent session"),
                    "honest empty readout"
                );
                assert!(
                    !p.contains("witnessed promotion"),
                    "no next-rung pitch when there's no answer"
                );
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn the_date_heuristic_distinguishes_a_dateless_session_row() {
        // cv prints `----------` for a dateless harness; a non-date 3rd token means
        // the row had no date column (the title starts immediately).
        assert!(looks_like_date("2026-06-19"));
        assert!(looks_like_date("----------"));
        assert!(!looks_like_date("edit"));
        assert!(!looks_like_date("2026/06/19"));
    }
}
