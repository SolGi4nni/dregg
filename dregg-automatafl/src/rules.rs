//! **THE GAME ORACLE — every answer comes from the proven Lean.**
//!
//! Each function here marshals a wire, calls `@[export] dregg_automatafl_rules`
//! (`Dregg2.Games.AutomataflFFI.rulesFFI` over `Dregg2.Games.AutomataflRules`, the rules-faithful
//! spec), and decodes the reply. Nothing in this module decides anything: no board is written, no
//! legality is tested, no conflict is detected, no offset is chosen in Rust.
//!
//! ## Why there is no fallback
//!
//! The Rust twin this replaces — `src/reference.rs`, a hand transcription of `~/dev/automatafl/logic`
//! — was not merely unproven, it was WRONG. The conformance audit found the transcribed lineage
//! divergent from the Creator-Approved ruleset on nine clauses; two were live in the file the witness
//! generators consulted (a 2-cycle SWAPPED both pieces where the ruleset keeps them put; the
//! occlusion scan skipped the DESTINATION, so a mover destroyed a stationary piece). Keeping it as a
//! "fallback" would mean answering with known-wrong semantics whenever the Lean archive is thin —
//! which is exactly the failure mode that hid the divergence for as long as it hid. So every function
//! returns `Result` and an absent export is an ERROR, not a quieter answer.
//!
//! Callers check [`available`] once (it is also what `DREGG_REQUIRE_LEAN=1` builds guarantee) and
//! then propagate; the surface refuses a move it cannot adjudicate.
//!
//! ## The three semantic repairs a caller will notice
//!
//! Routing at the ruleset CHANGES three answers the old Rust gave. They are corrections, and the
//! Lean carries `#guard` teeth for each:
//!
//! 1. **A 2-cycle stays put** (README / `PHILOSOPHY.md`; `AutomataflRules.twoCyc`) instead of
//!    swapping. This retires the divergence `resolve_witness.rs` used to document: the oracle and the
//!    descriptor now agree because they are the same object.
//! 2. **The path check includes the DESTINATION** (`model.py::CanMove`; `AutomataflRules.blockedB`),
//!    so a move onto an occupied square fails and the mover is replaced at its origin.
//! 3. **The automaton square is banned as a move SOURCE only** (ruling D; `MoveLegal`). Naming it as
//!    a DESTINATION is legal to propose and then fails to execute by (2). `reference.rs::move_valid`
//!    banned both endpoints.

use dregg_lean_ffi::{automatafl_rules, automatafl_rules_available};

use crate::board::{
    AutomatonSense, Board, Coord, Decision, Move, Raycast, coords_from_wire, coords_wire,
    goals_wire, moves_from_wire, moves_wire, pids_wire,
};

/// Whether the linked Lean archive carries the game oracle. False ⇒ every call below fails, by
/// design: there is no Rust twin left (see the module header).
pub fn available() -> bool {
    automatafl_rules_available()
}

/// Ask the oracle. Returns the reply's payload tokens (the leading `1` stripped); a `0` reply is the
/// Lean's fail-closed refusal of a malformed wire.
fn ask(wire: &str) -> Result<Vec<String>, String> {
    let out = automatafl_rules(wire)?;
    let mut toks = out.split_whitespace();
    match toks.next() {
        Some("1") => Ok(toks.map(str::to_owned).collect()),
        Some("0") => Err(format!(
            "dregg_automatafl_rules REFUSED the wire (fail-closed): {wire:?}"
        )),
        other => Err(format!(
            "dregg_automatafl_rules returned a malformed reply {other:?} for {wire:?}"
        )),
    }
}

/// The board wire, refusing a board that cannot be encoded faithfully ([`Board::validate`]) — so a
/// corrupt position is an `Err` here rather than a different, legal-looking position on the wire.
fn board_wire(b: &Board) -> Result<String, String> {
    b.validate()?;
    Ok(b.to_wire())
}

/// Borrowed view of a token vector, for the `*_from_wire` decoders.
fn refs(toks: &[String]) -> Vec<&str> {
    toks.iter().map(String::as_str).collect()
}

/// Decode a board payload, requiring the whole payload to be exactly one board.
fn board_of(toks: &[String], what: &str) -> Result<Board, String> {
    let r = refs(toks);
    let (b, rest) = Board::from_wire(&r)?;
    if !rest.is_empty() {
        return Err(format!("{what}: {} trailing tokens", rest.len()));
    }
    Ok(b)
}

/// **The stock two-player opening** (`AutomataflRules.stockTwoPlayer`): the 11×11 board with the
/// repulsor/attractor ring on the flanks and the automaton dead centre at `(5,5)`.
pub fn stock_two_player() -> Result<Board, String> {
    board_of(&ask("stock")?, "stock")
}

/// **The stock two-player goal assignment** (`AutomataflRules.stockGoals2`): seat `0` owns the two
/// `y = 0` corners, seat `1` the two `y = size-1` corners — the README's "each player picks two
/// corners that are in the same row".
pub fn stock_goals2(size: usize) -> Result<Vec<(Coord, u32)>, String> {
    let toks = ask(&format!("goals {size}"))?;
    let r = refs(&toks);
    let (k, mut rest) = match r.split_first() {
        Some((kt, rest)) => (
            kt.parse::<usize>()
                .map_err(|e| format!("goal count {kt:?}: {e}"))?,
            rest,
        ),
        None => return Err("goals reply is empty".into()),
    };
    let mut out = Vec::with_capacity(k);
    for _ in 0..k {
        if rest.len() < 3 {
            return Err("goals reply is truncated".into());
        }
        let x: i32 = rest[0].parse().map_err(|e| format!("goal x: {e}"))?;
        let y: i32 = rest[1].parse().map_err(|e| format!("goal y: {e}"))?;
        let seat: u32 = rest[2].parse().map_err(|e| format!("goal seat: {e}"))?;
        out.push(((x, y), seat));
        rest = &rest[3..];
    }
    Ok(out)
}

/// **The automaton's whole decision** on `b` (`Board.raycast` ×4, `evaluateAxis` ×2,
/// `chooseOffsetCfg`) — the Lean's own intermediate values, which is what makes the Leg-A witness a
/// transcription of the spec's trace rather than a recomputation of it.
pub fn sense(b: &Board) -> Result<AutomatonSense, String> {
    let toks = ask(&format!("sense {} {}", b.tie_token(), board_wire(b)?))?;
    if toks.len() != 18 {
        return Err(format!("sense reply has {} tokens, want 18", toks.len()));
    }
    let n = |i: usize| -> Result<usize, String> {
        toks[i]
            .parse::<usize>()
            .map_err(|e| format!("sense field {i} ({:?}): {e}", toks[i]))
    };
    let z = |i: usize| -> Result<i32, String> {
        toks[i]
            .parse::<i32>()
            .map_err(|e| format!("sense field {i} ({:?}): {e}", toks[i]))
    };
    let ray = |i: usize| -> Result<Raycast, String> {
        Ok(Raycast {
            what: n(i)? as u8,
            dist: n(i + 1)?,
        })
    };
    let dec = |i: usize| -> Result<Decision, String> {
        Ok(Decision {
            variant: n(i)? as u8,
            pos: n(i + 1)? != 0,
            att_dist: n(i + 2)?,
            rep_dist: n(i + 3)?,
        })
    };
    Ok(AutomatonSense {
        rays: [ray(0)?, ray(2)?, ray(4)?, ray(6)?],
        x_dec: dec(8)?,
        y_dec: dec(12)?,
        offset: (z(16)?, z(17)?),
    })
}

/// **The automaton step** (`AutomataflRules.automatonStepCfg`): move onto the one-step target iff it
/// is in bounds, a genuine move, and vacuum; otherwise the board is unchanged.
pub fn automaton_step(b: &Board) -> Result<Board, String> {
    board_of(
        &ask(&format!("step {} {}", b.tie_token(), board_wire(b)?))?,
        "step",
    )
}

/// **The move-resolved intermediate board** (Leg R): `AutomataflRules.resolveMoves` over the LEGAL
/// submissions. `marks` are the round's conflict markers (empty on a first round); a marked
/// coordinate is illegal at either endpoint for everyone.
///
/// A round whose landings are not uniquely claimed does not resolve — `resolveMoves` is guarded by
/// `resolvableB` and returns the board unchanged. Ask [`clash`] (or [`round_is_clean`]) if you need
/// to know which it was.
pub fn resolve_mid(b: &Board, marks: &[Coord], ms: &[Move]) -> Result<Board, String> {
    board_of(
        &ask(&format!(
            "mid {} {} {}",
            board_wire(b)?,
            coords_wire(marks),
            moves_wire(ms)
        ))?,
        "mid",
    )
}

/// **One clean round, whole**: resolve, step the automaton, check the win ON ENTRY
/// (`AutomataflRules.winOnEntry` — the automaton must have MOVED into a declared goal, not merely be
/// sitting on one). Returns the post-board and the winning seat.
pub fn turn(
    b: &Board,
    marks: &[Coord],
    ms: &[Move],
    goals: &[(Coord, u32)],
) -> Result<(Board, Option<u32>), String> {
    let toks = ask(&format!(
        "turn {} {} {} {} {}",
        b.tie_token(),
        board_wire(b)?,
        goals_wire(goals),
        coords_wire(marks),
        moves_wire(ms)
    ))?;
    let (win_tok, rest) = toks
        .split_first()
        .ok_or_else(|| "turn reply is empty".to_string())?;
    let win: i64 = win_tok
        .parse()
        .map_err(|e| format!("turn win token {win_tok:?}: {e}"))?;
    let board = board_of(rest, "turn")?;
    Ok((board, if win < 0 { None } else { Some(win as u32) }))
}

/// **The CAPPED match's terminal rule** — `AutomataflRules.adjudicateCapped`.
///
/// The seat strictly nearer its own goal wins; a seat that owns goals beats one that owns none;
/// exact parity is a genuine draw (`None`). This is the only terminal rule in the game with
/// soundness theorems behind it: `adjudicate_seated` (the winner always OWNS a goal corner — the
/// rule cannot award a match to an unseated player) and `adjudicate_sound` (when both seats own
/// goals, the winner is genuinely nearer).
///
/// ⚑ Before this existed the surface called a turn-capped match a bare DRAW, which is a terminal
/// rule no theorem had ever seen. A draw is now a *verdict* — the stock opening adjudicates to
/// `None` because the automaton starts equidistant from both seats' corners, and nudging it one row
/// picks a winner (pinned by `#guard`s in `AutomataflFFI.lean`).
pub fn adjudicate_capped(b: &Board, goals: &[(Coord, u32)]) -> Result<Option<u32>, String> {
    let toks = ask(&format!(
        "adjudicate {} {}",
        board_wire(b)?,
        goals_wire(goals)
    ))?;
    let win_tok = toks
        .first()
        .ok_or_else(|| "adjudicate reply is empty".to_string())?;
    let win: i64 = win_tok
        .parse()
        .map_err(|e| format!("adjudicate win token {win_tok:?}: {e}"))?;
    Ok(if win < 0 { None } else { Some(win as u32) })
}

/// The board half of [`turn`] with no markers and no goals — `automatonStepCfg ∘ resolveMoves`, the
/// two fold legs composed.
///
/// ⚑ The WIN is not available from a board alone: the ruleset fires it on the automaton ENTERING a
/// goal, so it is a property of the transition, not of the post-position. A caller that needs the
/// winner calls [`turn`] and keeps what it returns.
///
/// ⚑⚑ **THIS IS NOT "WHAT A TURN DOES" ON A CONFLICTED ROUND, AND IT IS NOT A SAFE DEFAULT.** This
/// and [`turn`] are the RESOLUTION LEGS. `resolveMoves` is guarded by `resolvableB`, which is the
/// MERGE clause (`unresolved`) alone; the FORK and COLLIDE clauses live in [`round`]
/// (`roundStep`), and neither of these verbs consults them. Handed a clashing pair they will
/// happily resolve whatever survives the inclusive path check — and that is not a hypothetical: on
/// the stock 11×11 opening, two seats forking the attractor at `(3,1)` to `(3,3)` and `(5,1)`
/// EXECUTE seat A's move (seat B's is blocked mid-path, leaving A as the single unblocked edge) and
/// discard seat B's with no trace, which is exactly the wrong outcome the played surface used to
/// ship (`surface::tests::a_forced_clash_re_enters_the_round_instead_of_dropping_the_moves` pins
/// it).
///
/// So: a caller adjudicating a REAL round calls [`round`]. Use these two only where the round is
/// already known clean — after a [`round_is_clean`] gate, or to replay a recorded clean round.
pub fn apply_turn(b: &Board, ms: &[Move]) -> Result<Board, String> {
    Ok(turn(b, &[], ms, &[])?.0)
}

/// **Move legality** (`AutomataflRules.moveLegalB`): distinct endpoints, rook-aligned, both in
/// bounds, the source is not the automaton, and neither endpoint is a marked coordinate.
pub fn move_legal(b: &Board, marks: &[Coord], m: &Move) -> Result<bool, String> {
    let toks = ask(&format!(
        "legal {} {} {} {} {}",
        board_wire(b)?,
        coords_wire(marks),
        m.who,
        Board::wire_coord(m.frm),
        Board::wire_coord(m.to)
    ))?;
    match toks.first().map(String::as_str) {
        Some("1") => Ok(true),
        Some("0") => Ok(false),
        other => Err(format!("legal reply {other:?} is not a bit")),
    }
}

/// **Every legal destination of `frm`** for seat `who` (`AutomataflFFI.targetsOf` = `moveLegalB` over
/// the whole board) — the rook-line highlight set the playable surface paints, so what a player is
/// offered is the ruleset's own legality rather than a Rust re-derivation of it.
pub fn legal_targets(
    b: &Board,
    marks: &[Coord],
    who: u32,
    frm: Coord,
) -> Result<Vec<Coord>, String> {
    let toks = ask(&format!(
        "targets {} {} {} {}",
        board_wire(b)?,
        coords_wire(marks),
        who,
        Board::wire_coord(frm)
    ))?;
    let r = refs(&toks);
    let (cs, rest) = coords_from_wire(&r)?;
    if !rest.is_empty() {
        return Err(format!("targets reply: {} trailing tokens", rest.len()));
    }
    Ok(cs)
}

/// **The round's conflicted coordinates** — `roundStep`'s own `cs`: the fork/collide clashes, or,
/// when there are none, the contested merge landings. EMPTY ⟺ the round resolves.
pub fn clash(b: &Board, marks: &[Coord], ms: &[Move]) -> Result<Vec<Coord>, String> {
    let toks = ask(&format!(
        "clash {} {} {}",
        board_wire(b)?,
        coords_wire(marks),
        moves_wire(ms)
    ))?;
    let r = refs(&toks);
    let (cs, rest) = coords_from_wire(&r)?;
    if !rest.is_empty() {
        return Err(format!("clash reply: {} trailing tokens", rest.len()));
    }
    Ok(cs)
}

/// **Is this round CLEAN?** — every submission is legal AND the round's conflict set is empty, so
/// resolution runs on every move as submitted.
///
/// This is the gate a FOLD must pass, and it is a real restriction. A conflicting round does not
/// resolve at all under the ruleset: it MARKS the contested coordinate and RE-ENTERS ([`round`]), so
/// folding one would mint a succinct proof of a transition the rules do not license. A conflicting
/// round is therefore REFUSED at the fold (blocked-not-faked) rather than attested.
pub fn round_is_clean(b: &Board, ms: &[Move]) -> Result<bool, String> {
    for m in ms {
        if !move_legal(b, &[], m)? {
            return Ok(false);
        }
    }
    Ok(clash(b, &[], ms)?.is_empty())
}

/// What one round did: demand re-entry, or resolve the turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoundOutcome {
    /// The round was conflicted. The contested coordinates are MARKED (illegal at either endpoint
    /// for everyone, for the rest of the turn), every move naming one is dropped and its seat
    /// re-enters, and every other move is LOCKED.
    Again {
        /// The accumulated markers.
        marks: Vec<Coord>,
        /// The moves that still stand.
        locked: Vec<Move>,
        /// The seats that owe a fresh move.
        waiting: Vec<u32>,
    },
    /// The round was clean: it resolved, the automaton stepped, the win was checked on entry.
    Resolved {
        /// The post-board.
        board: Board,
        /// The winning seat, if the automaton entered a goal.
        win: Option<u32>,
    },
}

/// **ONE ROUND** (`AutomataflRules.roundStep`) — the ruleset's actual turn structure: submissions
/// from the seats that owe a move, plus the locked ones, conflict detection, and either re-entry with
/// a fresh marker or resolution.
pub fn round(
    b: &Board,
    goals: &[(Coord, u32)],
    marks: &[Coord],
    locked: &[Move],
    waiting: &[u32],
    subs: &[Move],
) -> Result<RoundOutcome, String> {
    let toks = ask(&format!(
        "round {} {} {} {} {} {} {}",
        b.tie_token(),
        board_wire(b)?,
        goals_wire(goals),
        coords_wire(marks),
        moves_wire(locked),
        pids_wire(waiting),
        moves_wire(subs)
    ))?;
    let (tag, rest) = toks
        .split_first()
        .ok_or_else(|| "round reply is empty".to_string())?;
    match tag.as_str() {
        "A" => {
            let r = refs(rest);
            let (marks, r1) = coords_from_wire(&r)?;
            let (locked, r2) = moves_from_wire(r1)?;
            let (waiting, r3) = crate::board::pids_from_wire(r2)?;
            if !r3.is_empty() {
                return Err(format!("round A reply: {} trailing tokens", r3.len()));
            }
            Ok(RoundOutcome::Again {
                marks,
                locked,
                waiting,
            })
        }
        "R" => {
            let (win_tok, tail) = rest
                .split_first()
                .ok_or_else(|| "round R reply has no win token".to_string())?;
            let win: i64 = win_tok
                .parse()
                .map_err(|e| format!("round win token {win_tok:?}: {e}"))?;
            Ok(RoundOutcome::Resolved {
                board: board_of(tail, "round R")?,
                win: if win < 0 { None } else { Some(win as u32) },
            })
        }
        other => Err(format!("round reply tag {other:?} is neither A nor R")),
    }
}
