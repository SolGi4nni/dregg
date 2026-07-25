//! **THE TERMINAL ORACLE — the round's verdict comes from the proven Lean.**
//!
//! Every function here marshals a wire, calls `@[export] dregg_multiway_tug_rules`
//! (`Dregg2.Games.MultiwayTugFFI.rulesFFI` over `Dregg2.Games.MultiwayTug`, the proven
//! pure-transition spec), and decodes the reply. Nothing in this module decides anything: no row
//! is awarded, no tally is computed, no threshold is compared, no tie is broken in Rust.
//!
//! ## Why there is no fallback
//!
//! The Rust object this replaces — `reference.rs::winner_of` — was not merely unproven, it was
//! WRONG. It was the model's `roundWinner` truncated to its two absolute-threshold branches: no
//! charm tie-break, no row tie-break. Enumerating the control-splits of the seven rows, the two
//! objects disagreed on 54.5% of positions, and every disagreement was one-directional — the Rust
//! answered "no winner" where the ruleset ADJUDICATES a seat. Measured on played rounds that was a
//! **78.5% draw rate against the model's 5.1%**: the shipped game was mostly a non-event, and the
//! fix had been sitting in Lean, proven, unreachable. Keeping the twin as a "fallback" would mean
//! answering with known-wrong semantics whenever the archive is thin — the exact failure mode that
//! hid the divergence for as long as it hid. So every function returns `Result` and an absent
//! export is an ERROR, not a quieter answer.
//!
//! ## What is on the wire, and why that is faithful
//!
//! The adjudication verbs read the per-`(seat, row)` tallies and NOTHING else — the Lean theorem
//! `terminal_rule_reads_only_the_tallies` states exactly that, over `control`, both scores,
//! `roundWinner` and its clause. So [`adjudicate`] encodes the tallies into the wire's `placed`
//! zones and leaves the deck / hands / discards / removed favor / turn stamp empty. That is not a
//! shortcut around an incomplete encoder: it is the theorem's hypothesis, discharged.
//!
//! ## The CLAUSE, and why the caller needs it
//!
//! `roundWinner` is a precedence of nine clauses, and the deployed teeth cannot express a
//! disjunction of register-vs-register comparisons inside one transition case (the deployed
//! `SimpleStateConstraint` — what `AnyOf` ranges over — has no cross-register variant). So
//! `MultiwayTugProgram` gives each clause its own case and a scoring turn NAMES its clause. The
//! `branch` verb is how the caller is told which one; deriving it here would be re-implementing the
//! precedence in Rust, which is the twin this module exists to delete.

use dregg_lean_ffi::{multiway_tug_rules, multiway_tug_rules_available};

use crate::reference::{N_GUILDS, Player};

/// Whether the linked Lean archive carries the game oracle. False ⇒ every call below fails, by
/// design: there is no Rust twin left (see the module header).
pub fn available() -> bool {
    multiway_tug_rules_available()
}

/// Ask the oracle. Returns the reply's payload tokens (the leading `1` stripped); a `0` reply is
/// the Lean's fail-closed refusal of a malformed wire.
fn ask(wire: &str) -> Result<Vec<String>, String> {
    let out = multiway_tug_rules(wire)?;
    let mut toks = out.split_whitespace();
    match toks.next() {
        Some("1") => Ok(toks.map(str::to_owned).collect()),
        Some("0") => Err(format!(
            "dregg_multiway_tug_rules REFUSED the wire (fail-closed): {wire:?}"
        )),
        other => Err(format!(
            "dregg_multiway_tug_rules returned a malformed reply {other:?} for {wire:?}"
        )),
    }
}

/// Encode one card zone: each row's digit repeated by its multiplicity, rows ascending, `-` when
/// empty. Canonical because the model's zones are MULTISETS (`MultiwayTugFFI.encodeCards`).
fn cards(counts: &[u64; N_GUILDS]) -> String {
    let mut s = String::new();
    for (g, &n) in counts.iter().enumerate() {
        for _ in 0..n {
            s.push(char::from(b'0' + g as u8));
        }
    }
    if s.is_empty() { "-".to_string() } else { s }
}

/// The wire `STATE` carrying only the per-`(seat, row)` tallies, everything else empty. Faithful
/// for the adjudication verbs by `terminal_rule_reads_only_the_tallies` (see the module header);
/// it is NOT a general state encoder and must not be used for `act` / `legal` / `total`.
fn tally_state(tallies: &[[u64; 2]; N_GUILDS]) -> String {
    let mut a = [0u64; N_GUILDS];
    let mut b = [0u64; N_GUILDS];
    for (g, row) in tallies.iter().enumerate() {
        a[g] = row[0];
        b[g] = row[1];
    }
    // removed deck hand1 hand2 secret1 secret2 disc1 disc2 placed1 placed2 USED1 USED2 PEND SEAT turns
    format!(
        "- - - - - - - - {} {} 0000 0000 0 0 0",
        cards(&a),
        cards(&b)
    )
}

fn nat(tok: Option<&String>, what: &str) -> Result<u64, String> {
    tok.ok_or_else(|| format!("{what}: missing token"))?
        .parse::<u64>()
        .map_err(|e| format!("{what}: {e}"))
}

/// The round's terminal verdict, entirely as the Lean answered it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Verdict {
    /// `charmScore` per seat.
    pub charm: [u64; 2],
    /// `geishaScore` (rows held) per seat.
    pub guilds: [u64; 2],
    /// The `winner` register value: `0` DRAW, `1` seat A, `2` seat B. ⚑ `0` means an EXACT dead
    /// heat (`roundWinner_draw_iff`), never "unadjudicated".
    pub winner_code: u64,
    /// Which clause of `roundWinner` decided, `0..8` (`roundWinnerBranch`). This is what the
    /// scoring turn's deployed method is named after.
    pub branch: u8,
}

impl Verdict {
    /// The winning seat, or `None` on a genuine dead heat.
    pub fn winner(&self) -> Option<Player> {
        match self.winner_code {
            1 => Some(Player::A),
            2 => Some(Player::B),
            _ => None,
        }
    }
}

/// **Adjudicate a scored round.** One call each to `score` (the two tallies per seat) and `branch`
/// (the clause and its seat), over the committed per-`(seat, row)` placement counts.
///
/// The `branch` reply carries the seat as well as the clause, and the two are proven to agree
/// (`winnerTok_branch_agrees`), so this reads the winner off the clause — one answer, one source.
pub fn adjudicate(tallies: &[[u64; 2]; N_GUILDS]) -> Result<Verdict, String> {
    let st = tally_state(tallies);
    let sc = ask(&format!("score {st}"))?;
    if sc.len() != 4 {
        return Err(format!("score: expected 4 tokens, got {}", sc.len()));
    }
    let br = ask(&format!("branch {st}"))?;
    if br.len() != 2 {
        return Err(format!("branch: expected 2 tokens, got {}", br.len()));
    }
    let branch = nat(br.first(), "branch index")?;
    if branch > 8 {
        return Err(format!("branch index {branch} out of range"));
    }
    Ok(Verdict {
        charm: [nat(sc.first(), "a_charm")?, nat(sc.get(2), "b_charm")?],
        guilds: [nat(sc.get(1), "a_guilds")?, nat(sc.get(3), "b_guilds")?],
        winner_code: nat(br.get(1), "winner")?,
        branch: branch as u8,
    })
}

/// **Row control**, as `control` answers it: `0` uncontrolled, `1` seat A, `2` seat B. Used by the
/// surface to render the lanes, so the rendered board and the adjudicated winner come from the
/// same object.
pub fn control(tallies: &[[u64; 2]; N_GUILDS]) -> Result<[u64; N_GUILDS], String> {
    let toks = ask(&format!("control {}", tally_state(tallies)))?;
    if toks.len() != N_GUILDS + 1 || toks[0] != "7" {
        return Err(format!("control: malformed payload {toks:?}"));
    }
    let mut out = [0u64; N_GUILDS];
    for (i, slot) in out.iter_mut().enumerate() {
        *slot = nat(toks.get(i + 1), "control row")?;
    }
    Ok(out)
}

/// The model's influence table (`charm`), so even the per-row weights are the Lean's.
pub fn influence() -> Result<[u64; N_GUILDS], String> {
    let toks = ask("charm")?;
    if toks.len() != N_GUILDS + 1 || toks[0] != "7" {
        return Err(format!("charm: malformed payload {toks:?}"));
    }
    let mut out = [0u64; N_GUILDS];
    for (i, slot) in out.iter_mut().enumerate() {
        *slot = nat(toks.get(i + 1), "charm row")?;
    }
    Ok(out)
}

/// The committed turns in a full round (`8 + 4 = 12`), as the model counts them.
pub fn round_turns() -> Result<u64, String> {
    let toks = ask("turns")?;
    nat(toks.first(), "turns")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **What ONE oracle call costs** — the number that decides whether the four remaining Rust
    /// deciders in `reference.rs` (`legal_decisions`, `apply`, `apply_action`, `apply_response`)
    /// can be routed verb-by-verb or need a BATCHED verb first.
    ///
    /// The arithmetic this exists to settle:
    ///
    /// * the terminal adjudication — the part this lane routed — is **2 wire calls per scored
    ///   round** (`score` + `branch`), so a 200-round balance run makes **400** of them. That
    ///   cannot dominate anything, which is why the balance run's cost is build/lock, not FFI.
    /// * routing the legality/transition half is a different order entirely: the maximin agent
    ///   enumerates a seat's legal decisions (~86 at a fresh hand: 45 competitions, 20 gifts,
    ///   15 discards, 6 secrets) and APPLIES every one of them, plus each offer's responses — so
    ///   it would be ~200-300 calls per turn, ~12 turns, ~200 rounds ≈ **5 x 10^5 calls**.
    ///
    /// At `t` per call that second figure costs `5e5 * t`. This test measures `t` so the decision
    /// is made on a number rather than on the word "expensive".
    ///
    /// [MEASURED] persvati, 2026-07-25: **31 us per wire call ISOLATED, 112 us under concurrent
    /// test load** — a 3.6x spread on the same box in the same hour, so this is a RANGE and not a
    /// constant; quote it as one. At both ends:
    ///
    /// * the landed adjudication (400 calls per 200-round run) costs **12-45 ms** — invisible. The
    ///   balance run finishes in ~0.5 s, so its cost was never FFI; the 34 minutes it once spent
    ///   were the shared cargo lock and nothing else.
    /// * a fully routed maximin search (~3.8e5 calls, grounded below) costs **12-43 s** per run.
    ///   Real, but ORDINARY.
    ///
    /// That REFUTES the "per-call FFI cost blocks the remaining twins, they need a batched verb
    /// first" claim this lane made BEFORE measuring. The legality half (`legal_decisions`,
    /// `apply`'s legality test) has no such blocker and is routable now. What genuinely blocks the
    /// TRANSITION half (`apply_action`/`apply_response`) is unrelated to speed: `MultiwayTug.lean`
    /// models cards at guild-row resolution (`Geisha := Fin 7`, zones are `Multiset Geisha`) and
    /// has no notion of a distinct card id, so the id bookkeeping has no spec to route to.
    ///
    /// The ~3.8e5 figure is arithmetic, not a guess: a 6-card hand offers 6 secrets + 15 discards
    /// + 20 gifts + 45 competitions = 86 options; maximin applies every one, plus every response
    /// to each offer (20*3 + 45*2 = 150), so ~236 calls per action turn, ~1900 per round, ~380k
    /// over 200 rounds.
    #[test]
    fn one_oracle_call_costs() {
        if !available() {
            // Fail-closed, like every other oracle test in the tree: an absent archive means
            // there is no answer source at all, not a quieter one.
            panic!(
                "the multiway-tug rules oracle is absent — no timing can be taken, and there is \
                 no Rust twin to fall back on"
            );
        }
        // A realistic adjudication wire (the shape `adjudicate` actually sends).
        let tallies = [[1, 0], [0, 1], [2, 0], [0, 1], [1, 1], [1, 0], [0, 2]];
        let n = 2000;
        let start = std::time::Instant::now();
        for _ in 0..n {
            adjudicate(&tallies).expect("the oracle answers");
        }
        let elapsed = start.elapsed();
        // `adjudicate` is TWO wire calls, so divide by 2n for the per-call figure.
        let per_call = elapsed / (2 * n);
        println!("=== ORACLE CALL COST ===");
        println!("  {n} adjudications ({} wire calls) in {elapsed:?}", 2 * n);
        println!("  per wire call: {per_call:?}");
        println!(
            "  a 200-round balance run makes 400 calls  -> {:?}",
            per_call * 400
        );
        println!(
            "  routing the legality/transition half (~5e5 calls) -> {:?}",
            per_call * 500_000
        );
        // A tooth, not just a print: an oracle call must stay under a millisecond, because the
        // whole route-through argument for the remaining twins rests on it being cheap.
        assert!(
            per_call < std::time::Duration::from_millis(1),
            "one oracle wire call took {per_call:?} — over a millisecond, routing the legality \
             half would cost minutes per run and needs a batched verb first"
        );
    }
}
