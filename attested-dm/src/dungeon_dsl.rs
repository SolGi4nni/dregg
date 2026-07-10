//! # dungeon_dsl — a readable TEXT format for authoring attested dungeons.
//!
//! The four bundled adventures ([`crate::sunken_vault`] and friends) are hand-written Rust
//! functions. This module closes the gap between "a dungeon is a data structure" and "a dungeon
//! is a *file a person can write*": a small, forgiving, line-oriented DSL and a fail-closed
//! [`parse_dungeon`] that turns text into a real [`GameWorld`] — so anyone can author a
//! verifiable AI dungeon without writing Rust or recompiling. The parsed world is a first-class
//! [`GameWorld`]: it plays through the same [`crate::GameSession`], lands the same attested,
//! cap-gated, on-chain turns, and re-verifies with [`crate::GameSession::verify`].
//!
//! ## The grammar, in one screen
//!
//! Lines are the unit. Blank lines are ignored; `#` and `//` begin a comment to end-of-line
//! (except inside a `"quoted string"`). Top-level directives start at column zero; a **block**
//! (`room`, `npc`, `spell`, `light`, `combat`, `hostile`) owns the *indented* lines beneath it.
//!
//! ```text
//! name: The Sunken Vault                 # flavour; not load-bearing
//! start: shore                           # the opening room id
//! objective: reach sunken_gate holding amulet
//! lose: slain >= 1 -> "cut down by the Warden"   # >= 1 may be omitted (defaults to 1)
//! player_hp: 10                          # optional; needed only for HP combat
//!
//! room shore "The Salt Shore"            # room <id> "<Name>"
//!   The tide has gone out; the vault's mouth stands open.   # any plain line = description
//!   items: lantern, coil_of_rope         # comma list (or: item lantern)
//!   exit north -> antechamber            # exit <dir> -> <room>
//!   exit down  -> dark_stair requires item lantern    # a Gate (item)
//!   exit east  -> armory   requires flag door_unlocked >= 1   # a Gate (flag)
//!
//! use rusted_key on iron_door in vestry -> flag door_unlocked "The lock turns."
//!
//! npc witch "The Hedge-Witch" in witch_hut
//!   about "a swamp-crone who trades only in fair exchange"
//!   topic sickle requires item nightshade -> gives sickle "A fair trade." else "Bring nightshade."
//!   topic lore -> reveals "She tells of the keep's fall."
//!
//! hostile warden in warden_hall defeated_by sword
//!   victory flag warden_defeated
//!   victory "Your sword finds the gap; the Warden falls."
//!   death flag slain
//!   death "Bare-handed, you are no match."
//!
//! combat voidling in stairhead hp 9 attack 3
//!   weapon flare_blade damage 3
//!   unarmed 0
//!   armor bark_shield 1                  # optional
//!   victory flag voidling_felled
//!   victory "The flare blade sears through the dark."
//!   hit "White fire bites the Voidling."
//!   flail "Your bare strike passes through it like smoke."
//!
//! spell light requires flag learned_light    # or: spell light innate
//!   in gallery -> flag gallery_lit "Mage-light pours up the stair." fizzle "It finds nothing here."
//!   in stairhead -> conjure flare_blade "A blade of white fire kindles."
//!   in shrine   -> buff blessed "A warmth settles over you."
//!
//! light lamp oil 8                       # light <lamp-item> oil <start>
//!   dark: dark_stair, cistern            # the pitch-dark rooms (may repeat)
//!   refuel oil_flask +5 "You fill the lamp." spent "The flask is dry."
//!   stranded stranded -> "the dark keeps you"   # sets the strand flag AND a lose condition
//! ```
//!
//! ## Fail-closed, with line numbers
//!
//! [`parse_dungeon`] returns a legible [`DungeonError`] carrying the offending line
//! (`line 12: exit 'north' in room 'shore' leads to unknown room 'antechamer'`). Syntactic
//! mistakes and *semantic* mistakes (a dangling exit, an unreachable objective, an item that
//! exists nowhere) both refuse the parse — a broken dungeon never becomes a [`GameWorld`].
//!
//! ## The validator an author actually wants
//!
//! [`validate`] runs the same semantic checks over *any* [`GameWorld`] (hand-written ones too)
//! and returns every [`Issue`] rather than the first: dangling exit targets, an objective room
//! unreachable from `start`, a win item or gate item that is never placed, an NPC / combat /
//! spell in an unknown room, a spell with no learn source. Errors block; warnings advise.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::game::{
    CombatEnemy, DialogueGrant, DialogueRule, Exit, GameWorld, Gate, Hostile, LightRule,
    LoseCondition, Npc, Objective, RefuelRule, Room, Spell, SpellEffect, SpellRule, UseRule,
};

// ─────────────────────────────────────────────────────────────────────────────
// Errors + issues.
// ─────────────────────────────────────────────────────────────────────────────

/// **A fail-closed parse error**, carrying the source line it occurred on (`0` = the file as a
/// whole, e.g. a missing `start:`). [`std::fmt::Display`] renders `line {n}: {message}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DungeonError {
    /// The 1-based source line (or `0` for a whole-file error).
    pub line: usize,
    /// The legible message.
    pub message: String,
}

impl DungeonError {
    fn at(line: usize, message: impl Into<String>) -> DungeonError {
        DungeonError {
            line,
            message: message.into(),
        }
    }
}

impl std::fmt::Display for DungeonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.line == 0 {
            write!(f, "dungeon: {}", self.message)
        } else {
            write!(f, "line {}: {}", self.line, self.message)
        }
    }
}

impl std::error::Error for DungeonError {}

/// The weight of a validator [`Issue`]: an `Error` refuses the dungeon; a `Warning` advises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    /// A defect that makes the dungeon unsound/unwinnable — [`parse_dungeon`] refuses it.
    Error,
    /// An advisory an author probably wants to fix, but that does not block the parse.
    Warning,
}

/// **One finding from [`validate`]** — a severity and a legible, id-naming message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Issue {
    /// Whether this blocks (Error) or merely advises (Warning).
    pub severity: Severity,
    /// The human-legible description, naming the room/item/npc involved.
    pub message: String,
}

impl Issue {
    /// Whether this issue is a blocking [`Severity::Error`].
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }
}

impl std::fmt::Display for Issue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        write!(f, "{tag}: {}", self.message)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public entry points.
// ─────────────────────────────────────────────────────────────────────────────

/// **Parse text into a validated [`GameWorld`], fail-closed.** Syntactic errors and blocking
/// semantic errors (dangling exit, unreachable objective, an item that exists nowhere, …) both
/// refuse the parse with a line-numbered [`DungeonError`]. On success the world is guaranteed to
/// pass [`validate`] with no [`Severity::Error`] — a first-class attested dungeon.
pub fn parse_dungeon(src: &str) -> Result<GameWorld, DungeonError> {
    let (world, prov) = build(src)?;
    for (line, issue) in check(&world, Some(&prov)) {
        if issue.severity == Severity::Error {
            return Err(DungeonError::at(line.unwrap_or(0), issue.message));
        }
    }
    Ok(world)
}

/// **Parse text into a [`GameWorld`] without the semantic gate** — syntactic errors still refuse,
/// but a semantically-broken world is returned so [`validate`] can be run over it (the way an
/// authoring tool would surface *all* problems at once). Prefer [`parse_dungeon`] for play.
pub fn parse_world(src: &str) -> Result<GameWorld, DungeonError> {
    Ok(build(src)?.0)
}

/// **Validate any [`GameWorld`]** (parsed or hand-written) and return every [`Issue`] — errors
/// (a dungeon that cannot be won/played) and warnings (advisories). An empty result means the
/// world is sound: reachable objective, every referenced item obtainable, every actor in a real
/// room, every spell learnable.
pub fn validate(world: &GameWorld) -> Vec<Issue> {
    check(world, None).into_iter().map(|(_, i)| i).collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// Lexer — words and "quoted strings".
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Word(String),
    Str(String),
}

impl Tok {
    fn word(&self) -> Option<&str> {
        match self {
            Tok::Word(w) => Some(w),
            _ => None,
        }
    }
}

/// A source line, comment-stripped and trimmed, with its 1-based number and whether it was
/// indented (a block body line) or flush-left (a top-level directive / block header).
struct Line {
    no: usize,
    indented: bool,
    text: String,
}

/// Strip a `#` / `//` comment that is not inside a double-quoted string.
fn strip_comment(raw: &str) -> String {
    let bytes = raw.as_bytes();
    let mut in_str = false;
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'"' {
            // Respect a `\"` escape.
            let escaped = i > 0 && bytes[i - 1] == b'\\';
            if !escaped {
                in_str = !in_str;
            }
        } else if !in_str && c == b'#' {
            return raw[..i].to_string();
        } else if !in_str && c == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            return raw[..i].to_string();
        }
        i += 1;
    }
    raw.to_string()
}

fn collect_lines(src: &str) -> Vec<Line> {
    let mut out = Vec::new();
    for (idx, raw) in src.lines().enumerate() {
        let no = idx + 1;
        let indented = raw.starts_with(|c: char| c.is_whitespace());
        let text = strip_comment(raw);
        let trimmed = text.trim();
        if trimmed.is_empty() {
            continue;
        }
        out.push(Line {
            no,
            indented,
            text: trimmed.to_string(),
        });
    }
    out
}

/// Lex a single line's text into words and `"quoted strings"` (with `\"` / `\\` escapes).
fn lex(text: &str, line: usize) -> Result<Vec<Tok>, DungeonError> {
    let mut toks = Vec::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '"' {
            i += 1;
            let mut s = String::new();
            let mut closed = false;
            while i < chars.len() {
                let d = chars[i];
                if d == '\\' && i + 1 < chars.len() {
                    let n = chars[i + 1];
                    s.push(match n {
                        'n' => '\n',
                        't' => '\t',
                        other => other,
                    });
                    i += 2;
                    continue;
                }
                if d == '"' {
                    closed = true;
                    i += 1;
                    break;
                }
                s.push(d);
                i += 1;
            }
            if !closed {
                return Err(DungeonError::at(line, "unterminated \"quoted string\""));
            }
            toks.push(Tok::Str(s));
        } else {
            let mut w = String::new();
            while i < chars.len() && !chars[i].is_whitespace() && chars[i] != '"' {
                w.push(chars[i]);
                i += 1;
            }
            toks.push(Tok::Word(w));
        }
    }
    Ok(toks)
}

// ─────────────────────────────────────────────────────────────────────────────
// Token-slice helpers.
// ─────────────────────────────────────────────────────────────────────────────

fn first_word(text: &str) -> &str {
    text.split_whitespace().next().unwrap_or("")
}

fn word_at<'a>(
    toks: &'a [Tok],
    i: usize,
    line: usize,
    what: &str,
) -> Result<&'a str, DungeonError> {
    toks.get(i)
        .and_then(Tok::word)
        .ok_or_else(|| DungeonError::at(line, format!("expected {what}")))
}

fn expect(toks: &[Tok], i: usize, kw: &str, line: usize) -> Result<(), DungeonError> {
    match toks.get(i).and_then(Tok::word) {
        Some(w) if w == kw => Ok(()),
        other => Err(DungeonError::at(
            line,
            format!("expected `{kw}`, found {}", show(other)),
        )),
    }
}

fn show(w: Option<&str>) -> String {
    match w {
        Some(w) => format!("`{w}`"),
        None => "end of line".to_string(),
    }
}

fn first_str(toks: &[Tok]) -> Option<String> {
    toks.iter().find_map(|t| match t {
        Tok::Str(s) => Some(s.clone()),
        _ => None,
    })
}

/// All `"quoted"` strings in order — position 0 is the primary narration, 1 the alternate
/// (`else` / `fizzle` / `spent`).
fn strings(toks: &[Tok]) -> Vec<String> {
    toks.iter()
        .filter_map(|t| match t {
            Tok::Str(s) => Some(s.clone()),
            _ => None,
        })
        .collect()
}

fn arrow_pos(toks: &[Tok]) -> Option<usize> {
    toks.iter().position(|t| t.word() == Some("->"))
}

fn keyword_pos(toks: &[Tok], kw: &str) -> Option<usize> {
    toks.iter().position(|t| t.word() == Some(kw))
}

/// Parse a `flag NAME [>= v]` / `item NAME` requirement from a token slice into a [`Gate`].
fn parse_gate(toks: &[Tok], line: usize) -> Result<Gate, DungeonError> {
    match toks.first().and_then(Tok::word) {
        Some("item") => {
            let name = word_at(toks, 1, line, "an item name after `item`")?;
            Ok(Gate::NeedsItem(name.to_string()))
        }
        Some("flag") => {
            let name = word_at(toks, 1, line, "a flag name after `flag`")?;
            let (v, _) = parse_flag_val(&toks[2.min(toks.len())..]);
            Ok(Gate::NeedsFlag(name.to_string(), v))
        }
        other => Err(DungeonError::at(
            line,
            format!(
                "expected `item <name>` or `flag <name>`, found {}",
                show(other)
            ),
        )),
    }
}

/// After a flag name, read an optional `= v` / `>= v`; default value is `1`.
fn parse_flag_val(toks: &[Tok]) -> (i64, usize) {
    if let (Some(op), Some(n)) = (
        toks.first().and_then(Tok::word),
        toks.get(1).and_then(Tok::word),
    ) {
        if op == "=" || op == ">=" {
            if let Ok(v) = n.parse::<i64>() {
                return (v, 2);
            }
        }
    }
    (1, 0)
}

fn parse_num(w: &str, line: usize, what: &str) -> Result<i64, DungeonError> {
    w.trim_start_matches('+')
        .parse::<i64>()
        .map_err(|_| DungeonError::at(line, format!("expected a number for {what}, found `{w}`")))
}

// ─────────────────────────────────────────────────────────────────────────────
// Provenance — source lines for the constructs the validator reports on.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Default)]
struct Prov {
    exit_line: BTreeMap<(String, String), usize>,
    npc_line: BTreeMap<String, usize>,
    combat_line: BTreeMap<String, usize>,
    hostile_line: BTreeMap<String, usize>,
    use_line: Vec<usize>,
    dialogue_line: Vec<usize>,
    spell_line: BTreeMap<String, usize>,
    spellrule_line: Vec<usize>,
    objective_line: usize,
    start_line: usize,
}

// ─────────────────────────────────────────────────────────────────────────────
// The builder — text → GameWorld (syntactic parse only; check() does the semantics).
// ─────────────────────────────────────────────────────────────────────────────

struct Builder {
    rooms: BTreeMap<String, Room>,
    use_rules: Vec<UseRule>,
    hostiles: BTreeMap<String, Hostile>,
    combat: BTreeMap<String, CombatEnemy>,
    npcs: Vec<Npc>,
    dialogue: Vec<DialogueRule>,
    spells: Vec<Spell>,
    spell_rules: Vec<SpellRule>,
    player_max_hp: i64,
    light: Option<LightRule>,
    start: Option<String>,
    objective: Option<Objective>,
    lose: Vec<LoseCondition>,
    prov: Prov,
}

fn build(src: &str) -> Result<(GameWorld, Prov), DungeonError> {
    let lines = collect_lines(src);
    let mut b = Builder {
        rooms: BTreeMap::new(),
        use_rules: Vec::new(),
        hostiles: BTreeMap::new(),
        combat: BTreeMap::new(),
        npcs: Vec::new(),
        dialogue: Vec::new(),
        spells: Vec::new(),
        spell_rules: Vec::new(),
        player_max_hp: 0,
        light: None,
        start: None,
        objective: None,
        lose: Vec::new(),
        prov: Prov::default(),
    };

    let mut i = 0;
    while i < lines.len() {
        let line = &lines[i];
        if line.indented {
            return Err(DungeonError::at(
                line.no,
                "unexpected indented line (indented lines belong under a room / npc / spell / \
                 light / combat / hostile block)",
            ));
        }
        let head = first_word(&line.text).to_string();
        match head.as_str() {
            "name:" | "title:" => {
                // Flavour only — the engine's GameWorld carries no name field.
                i += 1;
            }
            "start:" => {
                let toks = lex(&line.text, line.no)?;
                b.start = Some(word_at(&toks, 1, line.no, "a room id after `start:`")?.to_string());
                b.prov.start_line = line.no;
                i += 1;
            }
            "player_hp:" | "player_max_hp:" => {
                let toks = lex(&line.text, line.no)?;
                b.player_max_hp = parse_num(
                    word_at(&toks, 1, line.no, "a number after `player_hp:`")?,
                    line.no,
                    "player_hp",
                )?;
                i += 1;
            }
            "objective:" => {
                let toks = lex(&line.text, line.no)?;
                // objective: reach <room> holding <item>
                expect(&toks, 1, "reach", line.no)?;
                let room = word_at(&toks, 2, line.no, "the objective room")?.to_string();
                expect(&toks, 3, "holding", line.no)?;
                let holding = word_at(&toks, 4, line.no, "the win item")?.to_string();
                b.objective = Some(Objective { room, holding });
                b.prov.objective_line = line.no;
                i += 1;
            }
            "lose:" => {
                let toks = lex(&line.text, line.no)?;
                // lose: <flag> [>= v] -> "<desc>"
                let arrow = arrow_pos(&toks).ok_or_else(|| {
                    DungeonError::at(line.no, "a lose condition needs `-> \"description\"`")
                })?;
                let flag = word_at(&toks, 1, line.no, "the lose flag")?.to_string();
                let (v, _) = parse_flag_val(&toks[2..arrow]);
                let desc = first_str(&toks[arrow + 1..]).ok_or_else(|| {
                    DungeonError::at(line.no, "a lose condition needs a \"description\" string")
                })?;
                b.lose.push(LoseCondition {
                    flag,
                    at_least: v,
                    description: desc,
                });
                i += 1;
            }
            "use" => {
                parse_use(&mut b, line)?;
                i += 1;
            }
            "room" => {
                i = parse_room(&mut b, &lines, i)?;
            }
            "npc" => {
                i = parse_npc(&mut b, &lines, i)?;
            }
            "hostile" => {
                i = parse_hostile(&mut b, &lines, i)?;
            }
            "combat" => {
                i = parse_combat(&mut b, &lines, i)?;
            }
            "spell" => {
                i = parse_spell(&mut b, &lines, i)?;
            }
            "light" => {
                i = parse_light(&mut b, &lines, i)?;
            }
            other => {
                return Err(DungeonError::at(
                    line.no,
                    format!("unknown directive `{other}`"),
                ));
            }
        }
    }

    let start = b
        .start
        .ok_or_else(|| DungeonError::at(0, "no `start:` room was declared"))?;
    let objective = b
        .objective
        .ok_or_else(|| DungeonError::at(0, "no `objective:` was declared"))?;
    if b.rooms.is_empty() {
        return Err(DungeonError::at(0, "the dungeon declares no rooms"));
    }

    let world = GameWorld {
        rooms: b.rooms,
        use_rules: b.use_rules,
        hostiles: b.hostiles,
        combat: b.combat,
        npcs: b.npcs,
        dialogue: b.dialogue,
        spells: b.spells,
        spell_rules: b.spell_rules,
        player_max_hp: b.player_max_hp,
        light: b.light,
        start,
        objective,
        lose: b.lose,
    };
    Ok((world, b.prov))
}

/// Consume a block header line plus its indented body lines; returns the index after the body.
fn body_range(lines: &[Line], header: usize) -> (usize, usize) {
    let mut j = header + 1;
    while j < lines.len() && lines[j].indented {
        j += 1;
    }
    (header + 1, j)
}

fn parse_room(b: &mut Builder, lines: &[Line], header: usize) -> Result<usize, DungeonError> {
    let hl = &lines[header];
    let toks = lex(&hl.text, hl.no)?;
    // room <id> "<Name>"
    let id = word_at(&toks, 1, hl.no, "a room id after `room`")?.to_string();
    let name = match toks.get(2) {
        Some(Tok::Str(s)) => s.clone(),
        _ => id.clone(),
    };
    let mut room = Room::new(id.clone(), name, String::new());
    let mut desc = String::new();

    let (start, end) = body_range(lines, header);
    for line in &lines[start..end] {
        let fw = first_word(&line.text);
        match fw {
            "items:" | "item" => {
                let rest = line.text[fw.len()..].trim_start().trim_start_matches(':');
                for raw in rest.split(',') {
                    let name = raw.trim().trim_matches(',').trim();
                    if !name.is_empty() {
                        room = room.item(name);
                    }
                }
            }
            "exit" => {
                let toks = lex(&line.text, line.no)?;
                // exit <dir> -> <room> [requires <gate>]
                let dir = word_at(&toks, 1, line.no, "a direction after `exit`")?.to_string();
                expect(&toks, 2, "->", line.no)?;
                let to = word_at(&toks, 3, line.no, "a destination room after `->`")?.to_string();
                let exit = if let Some(rq) = keyword_pos(&toks, "requires") {
                    let gate = parse_gate(&toks[rq + 1..], line.no)?;
                    Exit::gated(to, gate)
                } else {
                    Exit::open(to)
                };
                b.prov.exit_line.insert((id.clone(), dir.clone()), line.no);
                room = room.exit(dir, exit);
            }
            "desc:" => {
                let rest = line.text["desc:".len()..].trim();
                push_desc(&mut desc, rest);
            }
            _ => {
                // A plain prose line is description.
                push_desc(&mut desc, &line.text);
            }
        }
    }
    room.description = desc;
    b.rooms.insert(id, room);
    Ok(end)
}

fn push_desc(desc: &mut String, add: &str) {
    if add.is_empty() {
        return;
    }
    if !desc.is_empty() {
        desc.push(' ');
    }
    desc.push_str(add);
}

fn parse_use(b: &mut Builder, line: &Line) -> Result<(), DungeonError> {
    let toks = lex(&line.text, line.no)?;
    // use <item> [on <target>] in <room> -> flag <flag> [= v] "<narr>"
    let item = word_at(&toks, 1, line.no, "an item after `use`")?.to_string();
    let target = keyword_pos(&toks, "on")
        .and_then(|p| toks.get(p + 1))
        .and_then(Tok::word)
        .map(|s| s.to_string());
    let room = keyword_pos(&toks, "in")
        .and_then(|p| toks.get(p + 1))
        .and_then(Tok::word)
        .ok_or_else(|| DungeonError::at(line.no, "a use-rule needs `in <room>`"))?
        .to_string();
    let arrow = arrow_pos(&toks)
        .ok_or_else(|| DungeonError::at(line.no, "a use-rule needs `-> flag <name> \"...\"`"))?;
    let rhs = &toks[arrow + 1..];
    expect(rhs, 0, "flag", line.no)?;
    let flag = word_at(rhs, 1, line.no, "the flag the use sets")?.to_string();
    let (v, _) = parse_flag_val(&rhs[2.min(rhs.len())..]);
    let narration = first_str(rhs)
        .ok_or_else(|| DungeonError::at(line.no, "a use-rule needs a \"narration\" string"))?;
    b.prov.use_line.push(line.no);
    b.use_rules.push(UseRule {
        room,
        item,
        target,
        sets_flag: (flag, v),
        narration,
    });
    Ok(())
}

fn parse_hostile(b: &mut Builder, lines: &[Line], header: usize) -> Result<usize, DungeonError> {
    let hl = &lines[header];
    let toks = lex(&hl.text, hl.no)?;
    // hostile <name> in <room> defeated_by <item>
    let name = word_at(&toks, 1, hl.no, "a hostile name")?.to_string();
    let room = kv(&toks, "in", hl.no, "hostile needs `in <room>`")?;
    let defeated_by = kv(
        &toks,
        "defeated_by",
        hl.no,
        "hostile needs `defeated_by <item>`",
    )?;

    let mut victory_flag: Option<(String, i64)> = None;
    let mut death_flag: Option<(String, i64)> = None;
    let mut victory_narration = String::new();
    let mut death_narration = String::new();

    let (start, end) = body_range(lines, header);
    for line in &lines[start..end] {
        let toks = lex(&line.text, line.no)?;
        match first_word(&line.text) {
            "victory" if toks.get(1).and_then(Tok::word) == Some("flag") => {
                victory_flag = Some(flag_kv(&toks, 2, line.no, "victory flag")?);
            }
            "victory" => {
                victory_narration = first_str(&toks).unwrap_or_default();
            }
            "death" if toks.get(1).and_then(Tok::word) == Some("flag") => {
                death_flag = Some(flag_kv(&toks, 2, line.no, "death flag")?);
            }
            "death" => {
                death_narration = first_str(&toks).unwrap_or_default();
            }
            other => {
                return Err(DungeonError::at(
                    line.no,
                    format!("unexpected `{other}` in a hostile block"),
                ))
            }
        }
    }
    let victory_flag =
        victory_flag.ok_or_else(|| DungeonError::at(hl.no, "hostile needs a `victory flag`"))?;
    let death_flag =
        death_flag.ok_or_else(|| DungeonError::at(hl.no, "hostile needs a `death flag`"))?;
    b.prov.hostile_line.insert(room.clone(), hl.no);
    b.hostiles.insert(
        room.clone(),
        Hostile {
            room,
            name,
            defeated_by,
            victory_flag,
            death_flag,
            victory_narration,
            death_narration,
        },
    );
    Ok(end)
}

fn parse_combat(b: &mut Builder, lines: &[Line], header: usize) -> Result<usize, DungeonError> {
    let hl = &lines[header];
    let toks = lex(&hl.text, hl.no)?;
    // combat <name> in <room> hp <n> attack <n>
    let name = word_at(&toks, 1, hl.no, "a combat foe name")?.to_string();
    let room = kv(&toks, "in", hl.no, "combat needs `in <room>`")?;
    let hp = num_kv(&toks, "hp", hl.no)?;
    let attack = num_kv(&toks, "attack", hl.no)?;

    let mut armed_by = String::new();
    let mut weapon_damage = 0;
    let mut unarmed_damage = 0;
    let mut armor: Option<(String, i64)> = None;
    let mut victory_flag: Option<(String, i64)> = None;
    let mut victory_narration = String::new();
    let mut hit_narration = String::new();
    let mut flail_narration = String::new();

    let (start, end) = body_range(lines, header);
    for line in &lines[start..end] {
        let toks = lex(&line.text, line.no)?;
        match first_word(&line.text) {
            "weapon" => {
                armed_by = word_at(&toks, 1, line.no, "the weapon item")?.to_string();
                weapon_damage = num_kv(&toks, "damage", line.no)?;
            }
            "unarmed" => {
                unarmed_damage = parse_num(
                    word_at(&toks, 1, line.no, "unarmed damage")?,
                    line.no,
                    "unarmed",
                )?;
            }
            "armor" => {
                let item = word_at(&toks, 1, line.no, "the armor item")?.to_string();
                let mit = parse_num(
                    word_at(&toks, 2, line.no, "armor mitigation")?,
                    line.no,
                    "armor",
                )?;
                armor = Some((item, mit));
            }
            "victory" if toks.get(1).and_then(Tok::word) == Some("flag") => {
                victory_flag = Some(flag_kv(&toks, 2, line.no, "victory flag")?);
            }
            "victory" => victory_narration = first_str(&toks).unwrap_or_default(),
            "hit" => hit_narration = first_str(&toks).unwrap_or_default(),
            "flail" => flail_narration = first_str(&toks).unwrap_or_default(),
            other => {
                return Err(DungeonError::at(
                    line.no,
                    format!("unexpected `{other}` in a combat block"),
                ))
            }
        }
    }
    if armed_by.is_empty() {
        return Err(DungeonError::at(
            hl.no,
            "combat needs a `weapon <item> damage <n>` line",
        ));
    }
    let victory_flag =
        victory_flag.ok_or_else(|| DungeonError::at(hl.no, "combat needs a `victory flag`"))?;
    b.prov.combat_line.insert(room.clone(), hl.no);
    b.combat.insert(
        room.clone(),
        CombatEnemy {
            room,
            name,
            hp,
            armed_by,
            weapon_damage,
            unarmed_damage,
            attack,
            armor,
            victory_flag,
            victory_narration,
            hit_narration,
            flail_narration,
        },
    );
    Ok(end)
}

fn parse_npc(b: &mut Builder, lines: &[Line], header: usize) -> Result<usize, DungeonError> {
    let hl = &lines[header];
    let toks = lex(&hl.text, hl.no)?;
    // npc <id> "<Name>" in <room>
    let id = word_at(&toks, 1, hl.no, "an npc id after `npc`")?.to_string();
    let name = match toks.get(2) {
        Some(Tok::Str(s)) => s.clone(),
        _ => id.clone(),
    };
    let room = kv(&toks, "in", hl.no, "an npc needs `in <room>`")?;
    let mut description = format!("{name}");

    let (start, end) = body_range(lines, header);
    let mut rules: Vec<(usize, DialogueRule)> = Vec::new();
    for line in &lines[start..end] {
        let toks = lex(&line.text, line.no)?;
        match first_word(&line.text) {
            "about" => description = first_str(&toks).unwrap_or_default(),
            "topic" => {
                let rule = parse_topic(&room, &id, &toks, line.no)?;
                rules.push((line.no, rule));
            }
            other => {
                return Err(DungeonError::at(
                    line.no,
                    format!("unexpected `{other}` in an npc block"),
                ))
            }
        }
    }
    b.prov.npc_line.insert(id.clone(), hl.no);
    b.npcs.push(Npc::new(room, id, name, description));
    for (ln, rule) in rules {
        b.prov.dialogue_line.push(ln);
        b.dialogue.push(rule);
    }
    Ok(end)
}

fn parse_topic(
    room: &str,
    npc: &str,
    toks: &[Tok],
    line: usize,
) -> Result<DialogueRule, DungeonError> {
    // topic <topic> [requires <gate>] -> <grant> "<granted>" [else "<withheld>"]
    let topic = word_at(toks, 1, line, "a topic after `topic`")?.to_string();
    let arrow = arrow_pos(toks)
        .ok_or_else(|| DungeonError::at(line, "a topic needs `-> gives/opens/reveals ...`"))?;
    let requires = match keyword_pos(&toks[..arrow], "requires") {
        Some(rq) => Some(parse_gate(&toks[rq + 1..arrow], line)?),
        None => None,
    };
    let rhs = &toks[arrow + 1..];
    let strs = strings(rhs);
    let grant = match rhs.first().and_then(Tok::word) {
        Some("gives") => {
            DialogueGrant::GivesItem(word_at(rhs, 1, line, "the item after `gives`")?.to_string())
        }
        Some("opens") => {
            // opens flag <name> [= v]   (the leading `flag` word is optional)
            let mut idx = 1;
            if rhs.get(1).and_then(Tok::word) == Some("flag") {
                idx = 2;
            }
            let name = word_at(rhs, idx, line, "the flag after `opens`")?.to_string();
            let (v, _) = parse_flag_val(&rhs[(idx + 1).min(rhs.len())..]);
            DialogueGrant::OpensFlag(name, v)
        }
        Some("reveals") => DialogueGrant::Reveals,
        other => {
            return Err(DungeonError::at(
                line,
                format!("expected `gives`/`opens`/`reveals`, found {}", show(other)),
            ))
        }
    };
    Ok(DialogueRule {
        room: room.to_string(),
        npc: npc.to_string(),
        topic,
        requires,
        grant,
        granted_narration: strs.first().cloned().unwrap_or_default(),
        withheld_narration: strs.get(1).cloned().unwrap_or_default(),
    })
}

fn parse_spell(b: &mut Builder, lines: &[Line], header: usize) -> Result<usize, DungeonError> {
    let hl = &lines[header];
    let toks = lex(&hl.text, hl.no)?;
    // spell <word> requires <gate>   |   spell <word> innate
    let word = word_at(&toks, 1, hl.no, "a spell word after `spell`")?.to_string();
    let learned = match toks.get(2).and_then(Tok::word) {
        Some("innate") | None => None,
        Some("requires") => Some(parse_gate(&toks[3..], hl.no)?),
        other => {
            return Err(DungeonError::at(
                hl.no,
                format!(
                    "expected `requires <gate>` or `innate`, found {}",
                    show(other)
                ),
            ))
        }
    };
    b.prov.spell_line.insert(word.clone(), hl.no);
    b.spells.push(Spell {
        word: word.clone(),
        learned,
    });

    let (start, end) = body_range(lines, header);
    for line in &lines[start..end] {
        let toks = lex(&line.text, line.no)?;
        match first_word(&line.text) {
            "in" => {
                let rule = parse_spell_rule(&word, &toks, line.no)?;
                b.prov.spellrule_line.push(line.no);
                b.spell_rules.push(rule);
            }
            other => {
                return Err(DungeonError::at(
                    line.no,
                    format!("unexpected `{other}` in a spell block (spell rules start with `in`)"),
                ))
            }
        }
    }
    Ok(end)
}

fn parse_spell_rule(spell: &str, toks: &[Tok], line: usize) -> Result<SpellRule, DungeonError> {
    // in <room> [on <target>] [requires <gate>] -> flag/conjure/buff ... "<narr>" [fizzle "..."]
    let room = word_at(toks, 1, line, "the room after `in`")?.to_string();
    let arrow = arrow_pos(toks)
        .ok_or_else(|| DungeonError::at(line, "a spell rule needs `-> flag/conjure/buff ...`"))?;
    let pre = &toks[..arrow];
    let target = keyword_pos(pre, "on")
        .and_then(|p| pre.get(p + 1))
        .and_then(Tok::word)
        .map(|s| s.to_string());
    let requires = match keyword_pos(pre, "requires") {
        Some(rq) => Some(parse_gate(&pre[rq + 1..], line)?),
        None => None,
    };
    let rhs = &toks[arrow + 1..];
    let strs = strings(rhs);
    let effect = match rhs.first().and_then(Tok::word) {
        Some("flag") => {
            let name = word_at(rhs, 1, line, "the flag after `flag`")?.to_string();
            let (v, _) = parse_flag_val(&rhs[2.min(rhs.len())..]);
            SpellEffect::SetFlag(name, v)
        }
        Some("buff") => {
            let name = word_at(rhs, 1, line, "the flag after `buff`")?.to_string();
            let (v, _) = parse_flag_val(&rhs[2.min(rhs.len())..]);
            SpellEffect::Buff(name, v)
        }
        Some("conjure") => {
            SpellEffect::Conjure(word_at(rhs, 1, line, "the item after `conjure`")?.to_string())
        }
        other => {
            return Err(DungeonError::at(
                line,
                format!("expected `flag`/`buff`/`conjure`, found {}", show(other)),
            ))
        }
    };
    Ok(SpellRule {
        room,
        spell: spell.to_string(),
        target,
        requires,
        effect,
        narration: strs.first().cloned().unwrap_or_default(),
        fizzle_narration: strs.get(1).cloned().unwrap_or_default(),
    })
}

fn parse_light(b: &mut Builder, lines: &[Line], header: usize) -> Result<usize, DungeonError> {
    let hl = &lines[header];
    let toks = lex(&hl.text, hl.no)?;
    // light <lamp> oil <n>
    let lamp = word_at(&toks, 1, hl.no, "the lamp item after `light`")?.to_string();
    let oil = num_kv(&toks, "oil", hl.no)?;

    let mut dark_rooms: BTreeSet<String> = BTreeSet::new();
    let mut refuels: Vec<RefuelRule> = Vec::new();
    let mut stranded: Option<(String, i64)> = None;

    let (start, end) = body_range(lines, header);
    for line in &lines[start..end] {
        let fw = first_word(&line.text);
        match fw {
            "dark:" | "dark" => {
                let rest = line.text[fw.len()..].trim_start().trim_start_matches(':');
                for raw in rest.split(',') {
                    let name = raw.trim();
                    if !name.is_empty() {
                        dark_rooms.insert(name.to_string());
                    }
                }
            }
            "refuel" => {
                let toks = lex(&line.text, line.no)?;
                // refuel <fuel> +<n> "<narr>" [spent "<spent_narr>"]
                let fuel_item =
                    word_at(&toks, 1, line.no, "the fuel item after `refuel`")?.to_string();
                let add = parse_num(
                    word_at(&toks, 2, line.no, "the oil added")?,
                    line.no,
                    "refuel amount",
                )?;
                let strs = strings(&toks);
                let narration = strs.first().cloned().ok_or_else(|| {
                    DungeonError::at(line.no, "a refuel needs a \"narration\" string")
                })?;
                let spent_narration = strs.get(1).cloned().unwrap_or_default();
                refuels.push(RefuelRule {
                    fuel_item: fuel_item.clone(),
                    add,
                    spent_flag: format!("spent_{fuel_item}"),
                    narration,
                    spent_narration,
                });
            }
            "stranded" => {
                let toks = lex(&line.text, line.no)?;
                // stranded <flag> [= v] -> "<lose desc>"
                let flag = word_at(&toks, 1, line.no, "the strand flag")?.to_string();
                let arrow = arrow_pos(&toks);
                let val_end = arrow.unwrap_or(toks.len());
                let (v, _) = parse_flag_val(&toks[2.min(val_end)..val_end]);
                stranded = Some((flag.clone(), v));
                if let Some(desc) = arrow.and_then(|a| first_str(&toks[a + 1..])) {
                    b.lose.push(LoseCondition {
                        flag,
                        at_least: v,
                        description: desc,
                    });
                }
            }
            other => {
                return Err(DungeonError::at(
                    line.no,
                    format!("unexpected `{other}` in a light block"),
                ))
            }
        }
    }
    b.light = Some(LightRule {
        counter: format!("{lamp}_oil"),
        lamp,
        start: oil,
        dark_rooms,
        refuels,
        stranded,
    });
    Ok(end)
}

/// Read the word following keyword `kw` (`kw <value>`); errors with `msg` if absent.
fn kv(toks: &[Tok], kw: &str, line: usize, msg: &str) -> Result<String, DungeonError> {
    keyword_pos(toks, kw)
        .and_then(|p| toks.get(p + 1))
        .and_then(Tok::word)
        .map(|s| s.to_string())
        .ok_or_else(|| DungeonError::at(line, msg.to_string()))
}

/// Read the number following keyword `kw` (`kw <n>`).
fn num_kv(toks: &[Tok], kw: &str, line: usize) -> Result<i64, DungeonError> {
    let w = keyword_pos(toks, kw)
        .and_then(|p| toks.get(p + 1))
        .and_then(Tok::word)
        .ok_or_else(|| DungeonError::at(line, format!("expected `{kw} <n>`")))?;
    parse_num(w, line, kw)
}

/// Read `<flag> [= v]` starting at index `i`; default value `1`.
fn flag_kv(toks: &[Tok], i: usize, line: usize, what: &str) -> Result<(String, i64), DungeonError> {
    let name = word_at(toks, i, line, what)?.to_string();
    let (v, _) = parse_flag_val(&toks[(i + 1).min(toks.len())..]);
    Ok((name, v))
}

// ─────────────────────────────────────────────────────────────────────────────
// The validator — semantic soundness over a built (or hand-written) GameWorld.
// ─────────────────────────────────────────────────────────────────────────────

fn check(world: &GameWorld, prov: Option<&Prov>) -> Vec<(Option<usize>, Issue)> {
    let mut out: Vec<(Option<usize>, Issue)> = Vec::new();
    // Macros (not closures) so several emitters can coexist without overlapping `&mut out` borrows.
    macro_rules! err {
        ($line:expr, $msg:expr $(,)?) => {
            out.push((
                $line,
                Issue {
                    severity: Severity::Error,
                    message: $msg,
                },
            ))
        };
    }
    let obtainable = world.all_items();
    let room_ids: BTreeSet<&String> = world.rooms.keys().collect();

    // Start room must exist.
    if !world.rooms.contains_key(&world.start) {
        err!(
            prov.map(|p| p.start_line),
            format!("start room `{}` does not exist", world.start),
        );
    }

    // Dangling exits.
    for room in world.rooms.values() {
        for (dir, exit) in &room.exits {
            if !room_ids.contains(&exit.to_room) {
                let line =
                    prov.and_then(|p| p.exit_line.get(&(room.id.clone(), dir.clone())).copied());
                err!(
                    line,
                    format!(
                        "exit `{dir}` in room `{}` leads to unknown room `{}`",
                        room.id, exit.to_room
                    ),
                );
            }
            // A gate needing an item that exists nowhere.
            if let Some(Gate::NeedsItem(item)) = &exit.gate {
                if !obtainable.contains(item) {
                    let line = prov
                        .and_then(|p| p.exit_line.get(&(room.id.clone(), dir.clone())).copied());
                    err!(
                        line,
                        format!(
                            "gate on exit `{dir}` (room `{}`) needs item `{item}`, which exists nowhere",
                            room.id
                        ),
                    );
                }
            }
        }
    }

    // Objective room + win item.
    if !world.rooms.contains_key(&world.objective.room) {
        err!(
            prov.map(|p| p.objective_line),
            format!("objective room `{}` does not exist", world.objective.room),
        );
    } else if reachable(world).contains(&world.objective.room) {
        // reachable — fine
    } else {
        err!(
            prov.map(|p| p.objective_line),
            format!(
                "objective room `{}` is unreachable from start `{}`",
                world.objective.room, world.start
            ),
        );
    }
    if !obtainable.contains(&world.objective.holding) {
        err!(
            prov.map(|p| p.objective_line),
            format!(
                "objective requires holding `{}`, which is never placed in any room",
                world.objective.holding
            ),
        );
    }

    // Actors in unknown rooms.
    for h in world.hostiles.values() {
        if !room_ids.contains(&h.room) {
            err!(
                prov.and_then(|p| p.hostile_line.get(&h.room).copied()),
                format!(
                    "hostile `{}` is placed in unknown room `{}`",
                    h.name, h.room
                ),
            );
        }
    }
    for c in world.combat.values() {
        if !room_ids.contains(&c.room) {
            err!(
                prov.and_then(|p| p.combat_line.get(&c.room).copied()),
                format!(
                    "combat foe `{}` is placed in unknown room `{}`",
                    c.name, c.room
                ),
            );
        }
    }
    for n in &world.npcs {
        if !room_ids.contains(&n.room) {
            err!(
                prov.and_then(|p| p.npc_line.get(&n.id).copied()),
                format!("npc `{}` is placed in unknown room `{}`", n.id, n.room),
            );
        }
    }
    for (idx, r) in world.dialogue.iter().enumerate() {
        if !room_ids.contains(&r.room) {
            err!(
                prov.and_then(|p| p.dialogue_line.get(idx).copied()),
                format!(
                    "dialogue for npc `{}` names unknown room `{}`",
                    r.npc, r.room
                ),
            );
        }
    }
    for (idx, r) in world.spell_rules.iter().enumerate() {
        let line = prov.and_then(|p| p.spellrule_line.get(idx).copied());
        if !room_ids.contains(&r.room) {
            err!(
                line,
                format!(
                    "spell-rule for `{}` names unknown room `{}`",
                    r.spell, r.room
                ),
            );
        }
        if !world.is_spell_word(&r.spell) {
            err!(
                line,
                format!("spell-rule casts undeclared word `{}`", r.spell),
            );
        }
    }
    for (idx, u) in world.use_rules.iter().enumerate() {
        if !room_ids.contains(&u.room) {
            err!(
                prov.and_then(|p| p.use_line.get(idx).copied()),
                format!("use-rule for `{}` names unknown room `{}`", u.item, u.room),
            );
        }
    }

    // Every flag that some rule can SET — a spell's learn-by-flag needs a source in here.
    let mut settable: BTreeSet<String> = BTreeSet::new();
    for u in &world.use_rules {
        settable.insert(u.sets_flag.0.clone());
    }
    for h in world.hostiles.values() {
        settable.insert(h.victory_flag.0.clone());
    }
    for c in world.combat.values() {
        settable.insert(c.victory_flag.0.clone());
    }
    for r in &world.dialogue {
        if let DialogueGrant::OpensFlag(k, _) = &r.grant {
            settable.insert(k.clone());
        }
    }
    for r in &world.spell_rules {
        match &r.effect {
            SpellEffect::SetFlag(k, _) | SpellEffect::Buff(k, _) => {
                settable.insert(k.clone());
            }
            SpellEffect::Conjure(_) => {}
        }
    }

    // Spells: a learn source must exist.
    for s in &world.spells {
        let line = prov.and_then(|p| p.spell_line.get(&s.word).copied());
        match &s.learned {
            None => {}
            Some(Gate::NeedsItem(item)) => {
                if !obtainable.contains(item) {
                    err!(
                        line,
                        format!(
                            "spell `{}` is learned by holding `{item}`, which is never placed",
                            s.word
                        ),
                    );
                }
            }
            Some(Gate::NeedsFlag(flag, _)) => {
                if !settable.contains(flag) {
                    err!(
                        line,
                        format!(
                            "spell `{}` is learned via flag `{flag}`, but no rule ever sets that flag",
                            s.word
                        ),
                    );
                }
            }
        }
    }

    // Referenced-but-unobtainable items (weapons, armor, fuels, gate/dialogue requirements).
    macro_rules! ref_item {
        ($item:expr, $ctx:expr) => {{
            let item: &str = $item;
            if !item.is_empty() && !obtainable.contains(item) {
                let ctx: String = $ctx;
                out.push((
                    None,
                    Issue {
                        severity: Severity::Error,
                        message: format!(
                            "item `{item}` is referenced ({ctx}) but never placed or obtainable"
                        ),
                    },
                ));
            }
        }};
    }
    for h in world.hostiles.values() {
        ref_item!(&h.defeated_by, format!("the weapon vs `{}`", h.name));
    }
    for c in world.combat.values() {
        ref_item!(&c.armed_by, format!("the weapon vs `{}`", c.name));
        if let Some((armor, _)) = &c.armor {
            ref_item!(armor, format!("armor vs `{}`", c.name));
        }
    }
    for u in &world.use_rules {
        ref_item!(&u.item, format!("the item used in `{}`", u.room));
    }
    if let Some(light) = &world.light {
        ref_item!(&light.lamp, "the lamp".to_string());
        for rf in &light.refuels {
            ref_item!(&rf.fuel_item, "lamp fuel".to_string());
        }
    }
    for r in &world.dialogue {
        if let Some(Gate::NeedsItem(item)) = &r.requires {
            ref_item!(item, format!("required to talk to `{}`", r.npc));
        }
    }

    // ── Warnings (advisory, non-blocking). ──
    // Dialogue that addresses an npc not standing in its room.
    for r in &world.dialogue {
        if room_ids.contains(&r.room) && !world.npc_here(&r.room, &r.npc) {
            out.push((
                None,
                Issue {
                    severity: Severity::Warning,
                    message: format!(
                        "dialogue topic `{}` addresses npc `{}`, who does not stand in room `{}`",
                        r.topic, r.npc, r.room
                    ),
                },
            ));
        }
    }

    out
}

/// Rooms reachable from `start` by following exits (gates ignored — a gate is a puzzle, not a
/// disconnection). Used to catch an objective that no path can ever reach.
fn reachable(world: &GameWorld) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut q = VecDeque::new();
    if world.rooms.contains_key(&world.start) {
        seen.insert(world.start.clone());
        q.push_back(world.start.clone());
    }
    while let Some(id) = q.pop_front() {
        if let Some(room) = world.rooms.get(&id) {
            for exit in room.exits.values() {
                if world.rooms.contains_key(&exit.to_room) && seen.insert(exit.to_room.clone()) {
                    q.push_back(exit.to_room.clone());
                }
            }
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{GameSession, PlayResult};

    const LANTERN_FEN: &str = include_str!("../dungeons/lantern_fen.dungeon");
    const BROKEN: &str = include_str!("../dungeons/broken.dungeon");

    /// NON-VACUITY of the validator: a GOOD authored source parses and validates with ZERO errors.
    /// (Without this, "the validator catches X" tests could pass on a validator that flags anything.)
    #[test]
    fn a_good_authored_dungeon_parses_and_validates_clean() {
        let world = parse_dungeon(LANTERN_FEN).expect("the lantern fen must parse");
        let errors: Vec<_> = validate(&world)
            .into_iter()
            .filter(|i| i.is_error())
            .collect();
        assert!(
            errors.is_empty(),
            "a good authored source has zero validator errors, got {errors:?}"
        );
    }

    /// An authored-in-TEXT dungeon is a FIRST-CLASS attested world: it plays through the real
    /// engine and its chain verifies — no Rust, no recompile.
    #[test]
    fn an_authored_dungeon_plays_through_the_real_engine_and_verifies() {
        let world = parse_dungeon(LANTERN_FEN).expect("parses");
        let mut game = GameSession::open(world);
        match game.command("hero", "take lantern") {
            PlayResult::Landed { .. } => {}
            other => panic!("an authored world plays a legal move: {other:?}"),
        }
        assert!(game.world().inventory.contains("lantern"));
        game.verify()
            .expect("an authored world's receipt chain verifies");
    }

    /// FAIL-CLOSED: the deliberately-broken sample is caught — either refused at parse with a
    /// source LINE, or flagged by the validator naming the dangling target.
    #[test]
    fn the_broken_dungeon_is_caught_and_localized() {
        match parse_dungeon(BROKEN) {
            Err(e) => assert!(
                e.line > 0 && !e.message.is_empty(),
                "a parse error carries its source line + message, got {e:?}"
            ),
            Ok(world) => {
                let errors: Vec<_> = validate(&world)
                    .into_iter()
                    .filter(|i| i.is_error())
                    .collect();
                assert!(
                    !errors.is_empty(),
                    "the broken dungeon must be caught by validate"
                );
                assert!(
                    errors.iter().any(|i| i.message.contains("antechamer")),
                    "the dangling exit target is NAMED in the error: {errors:?}"
                );
            }
        }
    }

    /// The validator BITES on a dangling exit: mutate the good source's exit target to a room that
    /// does not exist, and the same source that validated clean now reports it by name.
    #[test]
    fn the_validator_catches_a_dangling_exit_introduced_into_a_good_source() {
        let good = parse_dungeon(LANTERN_FEN).expect("parses");
        assert!(
            validate(&good).iter().all(|i| !i.is_error()),
            "baseline is clean"
        );

        let mutated =
            LANTERN_FEN.replacen("exit north -> gatehouse", "exit north -> nowhere_at_all", 1);
        assert_ne!(mutated, LANTERN_FEN, "the mutation must actually apply");
        match parse_dungeon(&mutated) {
            Err(e) => assert!(e.line > 0, "refused at parse with a line: {e:?}"),
            Ok(w) => {
                let errors: Vec<_> = validate(&w).into_iter().filter(|i| i.is_error()).collect();
                assert!(
                    errors.iter().any(|i| i.message.contains("nowhere_at_all")),
                    "the dangling exit is caught and named: {errors:?}"
                );
            }
        }
    }
}

#[cfg(test)]
mod dogfood {
    use super::*;
    use crate::{GameSession, GameStatus, PlayResult};

    /// DOGFOOD: a world authored BY HAND in this DSL (no Rust) parses, validates clean, and plays
    /// its critical path to a WIN through the real engine — a gated exit and a world-bounded NPC
    /// trade included. If the format is not authorable, this test is where it shows.
    #[test]
    fn a_hand_authored_orchard_parses_validates_and_wins() {
        let src = include_str!("../dungeons/clockwork_orchard.dungeon");
        let world = parse_dungeon(src).expect("a hand-authored world must parse");
        let errors: Vec<_> = validate(&world)
            .into_iter()
            .filter(|i| i.is_error())
            .collect();
        assert!(
            errors.is_empty(),
            "hand-authored world validates clean, got {errors:?}"
        );

        let mut game = GameSession::open(world);
        for cmd in [
            "go north", // rows
            "take brass_apple",
            "go east",              // shed
            "ask keeper about key", // world-bounded: the apple buys the winding-key
            "go west",              // rows
            "go north",             // greenhouse (gated on winding_key)
            "take heartspring",
            "go west", // sundial -> WIN
        ] {
            match game.command("hero", cmd) {
                PlayResult::Landed { .. } => {}
                other => panic!("the authored critical path should land `{cmd}`, got {other:?}"),
            }
        }
        assert_eq!(
            game.status(),
            GameStatus::Won,
            "the hand-authored orchard is winnable"
        );
        game.verify()
            .expect("the authored playthrough verifies on-chain");
    }

    /// NON-VACUITY of the NPC gate in an AUTHORED world: without the apple, the Keeper withholds
    /// the key, so the greenhouse stays wound shut — the DSL's `requires` is load-bearing.
    #[test]
    fn the_authored_keeper_withholds_the_key_without_the_apple() {
        let world = parse_dungeon(include_str!("../dungeons/clockwork_orchard.dungeon")).unwrap();
        let mut game = GameSession::open(world);
        game.command("hero", "go north"); // rows (leave the apple)
        game.command("hero", "go east"); // shed
        game.command("hero", "ask keeper about key");
        assert!(
            !game.world().inventory.contains("winding_key"),
            "no apple, no key — the authored DialogueRule holds"
        );
        game.command("hero", "go west");
        match game.command("hero", "go north") {
            PlayResult::Refused(_) => {} // greenhouse gated on the key
            other => panic!("the greenhouse stays wound shut without the key, got {other:?}"),
        }
    }
}
