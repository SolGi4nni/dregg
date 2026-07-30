//! **THE MEASUREMENT E2 WAS MISSING: does the installed oracle DECIDE every constraint this
//! server's own deployed program installs?**
//!
//! # The wound this is the instrument for
//!
//! `dregg_cell::program::eval` routes the Lean-evaluated `StateConstraint` subset through the
//! installed constraint oracle, and — since the fail-open the game-proof audit found —
//! `undecided_subset_disposition` FAILS CLOSED when the oracle is installed and returns `None`.
//! `dreggnet-web`'s [`install_verified_settlement_gate`] installs that oracle UNCONDITIONALLY
//! (including debug, unlike `dregg-sdk`'s installer), so in this crate the fail-closed refusal is
//! live in every test build. One un-encodable constraint anywhere in the Descent's program therefore
//! refuses EVERY move that lands on its case — which is exactly what a player saw:
//!
//! ```text
//! this world cannot judge a move on this server: the verified rule-checker it needs is not
//! installed, so it refuses every move rather than guess at one.
//! ```
//!
//! Two rounds of that outage were closed by INSPECTING the encoder and guessing which arm was
//! missing (`HeapAtom::AllowedTransitions`, then `AnyOf`). Both guesses were about real gaps and
//! neither was the whole set, because nothing had ever walked the REAL artifact through the REAL
//! marshaller. That is all this file does, and it is a measurement rather than an inspection: for
//! every constraint in every case of all `DAYS` emitted programs, ask the installed
//! [`LeanConstraintOracle`] whether it decides, and name the ones that do not.
//!
//! # The invariant, stated
//!
//! For every constraint `c` the deployed program installs:
//!
//! > `constraint_in_lean_subset(c)` ⟹ `oracle.admits(c, …).is_some()`
//!
//! The left side is `dregg-cell`'s classifier (is this Lean's territory?); the right is
//! `dregg-exec-lean`'s marshaller (can the wire carry it?). When the two disagree the deployed
//! executor refuses an honest move forever, and it refuses it with a message about installation
//! rather than about the move — the hardest possible thing to diagnose from a page.
//!
//! The class-c arms (`PreimageGate`, `CountGe`, …) are the legitimate `None`s and are excluded by
//! the antecedent, not by an allowlist: `constraint_in_lean_subset` already answers `false` for
//! them. The Descent's emitted vocabulary contains none, which
//! [`the_probe_can_see_a_decline_it_is_not_a_tautology`] pins from the other side.
//!
//! # Both poles, in this process, on the outcome
//!
//! A page can render the refusal copy from a template while nothing is refusing, and a lane before
//! this one counted ten such matches in rendered HTML as evidence of ten live refusals. So the two
//! polarity tests here assert on a `Result<TurnReceipt, WorldError>` out of the real
//! `EmbeddedExecutor`, with the real oracle installed, and never on a byte of markup.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::{
    ConstraintOracle, HeapAtom, SimpleStateConstraint, StateConstraint, TransitionGuard,
    TransitionMeta, constraint_in_lean_subset, constraint_oracle_installed,
};
use dregg_cell::state::CellState;
use dregg_cell::{CellProgram, field_from_u64};
use dregg_exec_lean::LeanConstraintOracle;
use dreggnet_web::install_verified_settlement_gate;
use dungeon_on_dregg::descent::{
    self, ASCEND, BANKED, CARRIED, DAYS, DELVE, Deployment, Descent, FLEE, LOOT, SMITE, UNLOCK,
    crowned_line,
};
use spween_dregg::GENESIS_DONE_EXT_KEY;

/// Arm the DEPLOYED install point — the same function `dreggnet-web-server` runs before it binds a
/// listener — and then prove the oracle really is in `dregg-cell`'s slot.
///
/// This is deliberately NOT a local `register_constraint_oracle()` call: what E2 was about is that
/// the surface's own startup path arms the oracle, and a probe that installs its own would measure a
/// configuration no player is ever in.
fn arm_the_deployed_oracle() {
    install_verified_settlement_gate()
        .expect("dreggnet-web's startup install arms the verified executor in this process");
    // `register_constraint_oracle` installs NOTHING unless the linked archive exports
    // `dregg_constraint_admits`, so this one assertion covers both halves — and it is a hard
    // failure, not a `demand_lean` self-skip. A probe for a live outage that returns green when its
    // own precondition is missing is how five reality gates once self-skipped for four days; here
    // the missing archive would make every `admits` below return `None` for FFI reasons and the
    // report would blame the program.
    assert!(
        constraint_oracle_installed(),
        "no constraint oracle in dregg_cell's slot after dreggnet-web's startup install. Either the \
         install path stopped calling `dregg_exec_lean::register_constraint_oracle()`, or the linked \
         archive does not export `dregg_constraint_admits` — get the archive with \
         `bash scripts/fetch-lean-seed.sh` (or `lake build Dregg2.FFI` in metatheory/). Measuring \
         the guest evaluator instead would report this whole program as fine."
    );
}

/// A short kind label off the `Debug` shape — `AnyOf { variants: … }` ⇒ `"AnyOf"`.
fn kind_of(c: &StateConstraint) -> String {
    let d = format!("{c:?}");
    d.split([' ', '{', '('])
        .next()
        .unwrap_or("?")
        .trim()
        .to_string()
}

fn simple_kind_of(s: &SimpleStateConstraint) -> String {
    let d = format!("{s:?}");
    d.split([' ', '{', '('])
        .next()
        .unwrap_or("?")
        .trim()
        .to_string()
}

/// The DIAGNOSIS a decline gets reported with: the combinator's branch shape (peeled `Not` parity +
/// atom kind) and, for the heap branches, the set of distinct keys they name.
///
/// The key count is the load-bearing number. The deployed wire header carries ONE heap
/// `(old, new)` pair, so a combinator whose heap branches all name the SAME key is faithfully
/// marshallable and one that names two is not — and no report of "AnyOf declines" can distinguish
/// those two situations, which is why this walks the branches instead of printing the variant name.
fn shape_of(c: &StateConstraint) -> String {
    match c {
        StateConstraint::AnyOf { variants } | StateConstraint::AllOf { variants } => {
            let mut keys: Vec<u64> = Vec::new();
            let mut branches: Vec<String> = Vec::new();
            for v in variants {
                let mut atom = v;
                let mut negated = false;
                while let SimpleStateConstraint::Not(inner) = atom {
                    negated = !negated;
                    atom = inner.as_ref();
                }
                let parity = if negated { "N1" } else { "N0" };
                match atom {
                    SimpleStateConstraint::HeapField { key, atom } => {
                        if !keys.contains(key) {
                            keys.push(*key);
                        }
                        let a = format!("{atom:?}");
                        let a = a.split([' ', '{', '(']).next().unwrap_or("?").to_string();
                        branches.push(format!("{parity}:HeapField(key={key},{a})"));
                    }
                    other => branches.push(format!("{parity}:{}", simple_kind_of(other))),
                }
            }
            format!(
                "{}[{}]  distinct-heap-keys={}",
                kind_of(c),
                branches.join(" | "),
                keys.len()
            )
        }
        StateConstraint::HeapField { key, atom } => {
            let a = format!("{atom:?}");
            let a = a.split([' ', '{', '(']).next().unwrap_or("?").to_string();
            format!("HeapField(key={key},{a})")
        }
        other => kind_of(other),
    }
}

/// A COMPACT guard label. `TransitionGuard`'s `Debug` prints each `MethodIs` as a 32-element byte
/// array, and the Descent's riders carry eight of them — so one declining constraint rendered with
/// `{guard:?}` is ~2 KB of decimal noise wrapped around the four tokens that matter. A report nobody
/// can read is not a diagnosis, so method symbols collapse to their first four bytes and a
/// same-variant run collapses to a count.
fn guard_label(g: &TransitionGuard) -> String {
    match g {
        TransitionGuard::Always => "Always".to_string(),
        TransitionGuard::MethodIs { method } => format!(
            "MethodIs({:02x}{:02x}{:02x}{:02x}…)",
            method[0], method[1], method[2], method[3]
        ),
        TransitionGuard::EffectKindIs { mask } => format!("EffectKindIs({mask:#x})"),
        TransitionGuard::SlotChanged { index } => format!("SlotChanged({index})"),
        TransitionGuard::AnyOf(cs) | TransitionGuard::AllOf(cs) => {
            let tag = if matches!(g, TransitionGuard::AnyOf(_)) {
                "AnyOf"
            } else {
                "AllOf"
            };
            // Collapse a run of MethodIs children (the rider's eight-verb list) to a count: WHICH
            // verbs the rider covers is not what a decline is about, and the Descent's every rider
            // lists all of them.
            let methods = cs
                .iter()
                .filter(|c| matches!(c, TransitionGuard::MethodIs { .. }))
                .count();
            let rest: Vec<String> = cs
                .iter()
                .filter(|c| !matches!(c, TransitionGuard::MethodIs { .. }))
                .map(guard_label)
                .collect();
            let mut parts = rest;
            if methods > 0 {
                parts.push(format!("MethodIs×{methods}"));
            }
            format!("{tag}[{}]", parts.join(", "))
        }
    }
}

/// A census of the shapes the walk actually reached, so a probe that stopped seeing the program
/// cannot pass by seeing nothing.
#[derive(Default)]
struct Census {
    total: usize,
    combinators: usize,
    combinator_with_heap_branch: usize,
    heap_allowed_transitions: usize,
    register_allowed_transitions: usize,
    fields_count_equals: usize,
    affine_le: usize,
}

impl Census {
    fn record(&mut self, c: &StateConstraint) {
        self.total += 1;
        match c {
            StateConstraint::AnyOf { variants } | StateConstraint::AllOf { variants } => {
                self.combinators += 1;
                let heaps = variants.iter().any(|v| {
                    let mut atom = v;
                    while let SimpleStateConstraint::Not(inner) = atom {
                        atom = inner.as_ref();
                    }
                    matches!(atom, SimpleStateConstraint::HeapField { .. })
                });
                if heaps {
                    self.combinator_with_heap_branch += 1;
                }
            }
            StateConstraint::HeapField {
                atom: HeapAtom::AllowedTransitions { .. },
                ..
            } => self.heap_allowed_transitions += 1,
            StateConstraint::AllowedTransitions { .. } => self.register_allowed_transitions += 1,
            StateConstraint::FieldsCountEquals { .. } => self.fields_count_equals += 1,
            StateConstraint::AffineLe { .. } => self.affine_le += 1,
            _ => {}
        }
    }
}

/// A mid-run `(old, new)` pair over the Descent's own layout: registers moved, the genesis sentinel
/// and every relic custody key PRESENT on both sides.
///
/// The marshaller's decline is a function of the constraint's SHAPE, not of these values — but a
/// state with absent heap keys would make every heap verdict "absent", so the poles below would be
/// measuring the empty case. These are populated so the wire carries real `present 1 <hex>` pairs.
fn descent_states() -> (CellState, CellState) {
    let dep = Deployment::new();
    let mut old = CellState::new(0);
    for (name, v) in [
        ("depth", 1u64),
        ("spent", 1),
        ("wounds", 0),
        ("fate", 0),
        ("pack", 0),
        ("bank", 0),
        ("harm", 0),
        ("way_2", 0),
        ("way_3", 0),
        ("way_4", 0),
        ("hoard_1", 3),
        ("hoard_2", 2),
        ("hoard_3", 2),
        ("hoard_4", 1),
        ("hung", 0),
    ] {
        if let Ok(idx) = dep.reg(name) {
            assert!(old.set_field(idx as usize, field_from_u64(v)));
        }
    }
    for i in 0..8 {
        if let Ok(key) = dep.relic_key(i) {
            assert!(old.set_field_ext(key, field_from_u64(CARRIED)));
        }
    }
    assert!(old.set_field_ext(GENESIS_DONE_EXT_KEY, field_from_u64(1)));
    let mut new = old.clone();
    if let Ok(idx) = dep.reg("depth") {
        assert!(new.set_field(idx as usize, field_from_u64(2)));
    }
    (old, new)
}

/// ⚑ **THE PROBE.** Walk the REAL Lean-emitted artifact through the REAL loader and the REAL
/// marshaller, and name every constraint the installed oracle does not decide.
///
/// It goes RED while any constraint in the deployed program is un-encodable and GREEN when none is,
/// so it cannot decay into a comment about a gap that has moved. Its report is the diagnosis: the
/// day, the case guard, the constraint index, and the branch-level shape (including the distinct
/// heap-key count, which is what tells a missing encoder arm apart from a genuine wire limit).
#[test]
fn the_installed_oracle_decides_every_constraint_the_deployed_descent_installs() {
    arm_the_deployed_oracle();
    let oracle = LeanConstraintOracle;
    let (old, new) = descent_states();
    let ctx = EvalContext {
        block_height: 12,
        timestamp: 1_700_000_000,
        current_epoch: 1,
        sender: Some([9u8; 32]),
        sender_epoch_count: 0,
        revealed_preimage: None,
    };
    let mut meta = TransitionMeta::wildcard();
    meta.delegation_epoch = Some(0);

    let mut census = Census::default();
    let mut declines: Vec<String> = Vec::new();
    let mut worst_label = String::new();

    for day in 0..DAYS {
        let dep = Deployment::for_day(day);
        let program = descent::load_program_for_day(&dep, day)
            .expect("every symbolic name in the Lean-emitted artifact resolves against the layout");
        let CellProgram::Cases(cases) = program else {
            panic!("the descent program is `Cases`; the walk below assumes it");
        };
        for (ci, case) in cases.iter().enumerate() {
            let label = guard_label(&case.guard);
            if label.len() > worst_label.len() {
                worst_label = label;
            }
            for (k, c) in case.constraints.iter().enumerate() {
                census.record(c);
                if !constraint_in_lean_subset(c) {
                    // A class-c arm (crypto / witness / DSL): the oracle declining it is the
                    // NAMED trusted-Rust slot doing its job, and `undecided_subset_disposition`
                    // lets it through to the hand-written evaluator. Not this probe's business —
                    // but the Descent emits none, which the sibling test pins.
                    continue;
                }
                if oracle
                    .admits(c, &new, Some(&old), Some(&ctx), &meta)
                    .is_none()
                {
                    declines.push(format!(
                        "day {day} case {ci} guard {} constraint {k}: {}",
                        guard_label(&case.guard),
                        shape_of(c)
                    ));
                }
            }
        }
    }

    // ── ANTI-VACUITY. A walk that reached nothing would report zero declines and pass.
    assert!(
        census.total >= 5_000,
        "the walk saw only {} constraints; the Lean emission carried 5840 across {DAYS} days on \
         2026-07-30, so this probe has stopped seeing the program",
        census.total
    );
    assert!(
        census.combinator_with_heap_branch >= 400,
        "the walk reached {} combinators with a HeapField branch (576 on 2026-07-30) — that is the \
         exact shape the second round of E2 was, so a probe that no longer sees it proves nothing",
        census.combinator_with_heap_branch
    );
    assert!(
        census.heap_allowed_transitions >= 100,
        "the walk reached {} `HeapField{{AllowedTransitions}}` atoms (176 on 2026-07-30) — the \
         first round of E2",
        census.heap_allowed_transitions
    );
    assert!(
        census.register_allowed_transitions >= 1 && census.fields_count_equals >= 1,
        "the walk reached {} register transition tables and {} fixed-key census teeth; both are \
         emitted (400 and 96 on 2026-07-30)",
        census.register_allowed_transitions,
        census.fields_count_equals
    );
    assert!(
        census.affine_le >= 1,
        "the walk reached no AffineLe (256 emitted) — the arm with a marshalling ENVELOPE, the one \
         shape here that could plausibly decline for a bound rather than a missing case"
    );
    // ⚠ THE REPORT MUST STAY READABLE. Measured with `{guard:?}`: one declining constraint rendered
    // as ~2 KB, because each of a rider's eight `MethodIs` children prints a 32-element decimal byte
    // array — and 576 of those is a diagnosis nobody reads, which is how the first two rounds of
    // this outage got closed by guessing instead. `guard_label` collapses them; this pins that it
    // still does, over the real guards rather than a constructed one.
    assert!(
        worst_label.len() <= 160,
        "the widest deployed guard renders to {} chars ({worst_label}) — the decline report becomes \
         unreadable past ~160 and an unreadable report is not a diagnosis",
        worst_label.len()
    );

    assert!(
        declines.is_empty(),
        "{} of {} constraints in the DEPLOYED Descent program are in the Lean subset but the \
         installed oracle DECLINES them, so `undecided_subset_disposition` refuses every move that \
         lands on their case — this IS the outage, not a description of one:\n{}\n\n(shape census: \
         {} combinators, {} of them with a HeapField branch; {} heap transition tables; {} register \
         transition tables; {} census teeth; {} affine bounds)",
        declines.len(),
        census.total,
        declines
            .iter()
            .take(12)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n"),
        census.combinators,
        census.combinator_with_heap_branch,
        census.heap_allowed_transitions,
        census.register_allowed_transitions,
        census.fields_count_equals,
        census.affine_le,
    );
}

/// ⚠ **THE INSTRUMENT MUST BE ABLE TO ANSWER "DECLINES".** The probe above passes by finding
/// nothing, which is the shape of a test that has quietly stopped looking. So: the same predicate,
/// applied to a constraint that genuinely cannot cross this wire, must report a decline.
///
/// The witness is the REMAINING wire limit, named precisely. `Dregg2.Exec.DeployedConstraint`'s
/// `DInput` carries ONE `(heapOld, heapNew)` pair in the header and `branchAdmits` reads that pair
/// for every `heapField` branch, so a combinator whose heap branches name TWO DIFFERENT keys has no
/// faithful encoding: the marshaller declines it and the subset gate refuses. That is a real Lean-
/// side residual (the arm it needs is a per-branch heap cell run in `DInput`/`parseBranches`), it is
/// NOT exercised by the deployed program (measured: every heap-bearing combinator in
/// `dungeon_program.json` names exactly one key), and it must keep failing CLOSED rather than
/// falling through to the unverified Rust twin.
#[test]
fn the_probe_can_see_a_decline_it_is_not_a_tautology() {
    arm_the_deployed_oracle();
    let oracle = LeanConstraintOracle;
    let (old, new) = descent_states();
    let meta = TransitionMeta::wildcard();

    let two_keys = StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::HeapField {
                key: 20,
                atom: HeapAtom::Equals {
                    value: field_from_u64(8),
                },
            },
            SimpleStateConstraint::HeapField {
                key: 21,
                atom: HeapAtom::Equals {
                    value: field_from_u64(8),
                },
            },
        ],
    };
    assert!(
        constraint_in_lean_subset(&two_keys),
        "a combinator over pure heap atoms is Lean's territory, so its decline must FAIL CLOSED"
    );
    assert!(
        oracle
            .admits(&two_keys, &new, Some(&old), None, &meta)
            .is_none(),
        "a combinator whose heap branches name two DIFFERENT keys cannot be carried by a wire \
         header with one heap pair; encoding it anyway would evaluate branch 2 against branch 1's \
         key — a silently WRONG admission, which is worse than the refusal"
    );

    // …and the one-key sibling, which is the shape the deployed program actually emits, DOES decide.
    // Without this half the assertion above would also pass with the whole family declined, which
    // is precisely the state E2 was in.
    let one_key = StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::HeapField {
                key: 20,
                atom: HeapAtom::Equals {
                    value: field_from_u64(8),
                },
            },
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::HeapField {
                key: 20,
                atom: HeapAtom::DeltaEquals { d: 0 },
            })),
        ],
    };
    assert!(
        oracle
            .admits(&one_key, &new, Some(&old), None, &meta)
            .is_some(),
        "a combinator whose heap branches all name ONE key is faithfully carried by the header's \
         single heap pair and MUST be decided by the verified evaluator"
    );

    // And the class-c control: the probe's antecedent (`constraint_in_lean_subset`) is what excuses
    // a legitimate `None`, so it must be able to answer `false`.
    assert!(
        !constraint_in_lean_subset(&StateConstraint::PreimageGate {
            commitment_index: 0,
            hash_kind: dregg_cell::program::HashKind::Blake3,
        }),
        "the subset classifier must be able to say `not mine`, or the probe's exclusion of the \
         trusted-Rust slot is an exclusion of everything"
    );
}

/// ⚑ **THE RED-PROOF, OVER THE DEPLOYED CONSTRAINTS THEMSELVES — no source mutation, no window.**
///
/// The probe above passes by finding nothing, and a shared tree makes the obvious red-proof (break
/// the encoder, watch it go red, put it back) a disarmed guard for as long as the run takes. So the
/// proof that it can go red is done on the CONSTRAINTS instead of on the encoder: take every
/// heap-bearing combinator the deployed program emits, add ONE branch reading a DIFFERENT heap key,
/// and the walk's own predicate must flag every single one — because a two-key combinator has no
/// faithful encoding against a header with one heap pair.
///
/// Both directions are asserted per constraint, on the SAME predicate the walk uses:
///
/// * the deployed shape DECIDES (so a "declines everything" oracle cannot pass this), and
/// * the re-keyed mutant DECLINES (so a "decides everything" marshaller cannot either).
///
/// Which is exactly the pair of facts that were false in opposite directions before 2026-07-30: the
/// deployed shape declined, and nothing distinguished that from the mutant.
#[test]
fn the_walks_predicate_goes_red_on_a_rekeyed_deployed_constraint() {
    arm_the_deployed_oracle();
    let oracle = LeanConstraintOracle;
    let (old, new) = descent_states();
    let meta = TransitionMeta::wildcard();

    let mut checked = 0usize;
    let mut no_heap_checked = 0usize;
    for day in 0..DAYS {
        let dep = Deployment::for_day(day);
        let program =
            descent::load_program_for_day(&dep, day).expect("the emitted artifact resolves");
        let CellProgram::Cases(cases) = program else {
            panic!("the descent program is `Cases`");
        };
        for case in &cases {
            for c in &case.constraints {
                let StateConstraint::AnyOf { variants } = c else {
                    continue;
                };
                let mut keys: Vec<u64> = Vec::new();
                for v in variants {
                    let mut atom = v;
                    while let SimpleStateConstraint::Not(inner) = atom {
                        atom = inner.as_ref();
                    }
                    if let SimpleStateConstraint::HeapField { key, .. } = atom
                        && !keys.contains(key)
                    {
                        keys.push(*key);
                    }
                }
                let add_key = keys.first().map(|k| k + 1).unwrap_or(4096);
                let mut mutant = variants.clone();
                mutant.push(SimpleStateConstraint::HeapField {
                    key: add_key,
                    atom: HeapAtom::Immutable,
                });
                let mutant = StateConstraint::AnyOf { variants: mutant };
                let mutant_decided = oracle
                    .admits(&mutant, &new, Some(&old), None, &meta)
                    .is_some();

                assert!(
                    oracle.admits(c, &new, Some(&old), None, &meta).is_some(),
                    "the DEPLOYED shape {} must be decided — without this half the mutant's decline \
                     below is satisfied by an oracle that declines everything, which is the state \
                     this file was written to end",
                    shape_of(c)
                );
                if keys.is_empty() {
                    // A combinator with no heap branch, given ONE: still one key, still carried.
                    assert!(
                        mutant_decided,
                        "adding a SINGLE heap-key branch to {} must stay decided; a decline here \
                         would mean the header's heap pair is not being resolved at all",
                        shape_of(c)
                    );
                    no_heap_checked += 1;
                } else {
                    assert!(
                        !mutant_decided,
                        "{} re-keyed with a second, DIFFERENT heap key ({add_key}) must DECLINE: the \
                         wire header carries one (heapOld, heapNew) pair, so encoding it would judge \
                         the added branch against key {}'s cell — a silently wrong verdict. If this \
                         admits, either the header grew per-branch cells in \
                         `Dregg2.Exec.DeployedConstraint` (then say so here) or the marshaller has \
                         started guessing.",
                        shape_of(c),
                        keys[0]
                    );
                    checked += 1;
                }
            }
        }
    }
    assert!(
        checked >= 400,
        "only {checked} heap-bearing combinators were red-proofed (576 emitted on 2026-07-30); a \
         red-proof that reaches nothing is not one"
    );
    assert!(
        no_heap_checked >= 100,
        "only {no_heap_checked} heap-free combinators were checked (400 emitted on 2026-07-30)"
    );
}

/// **POLE 1 — a whole honest Descent run is ADMITTED**, through the real executor, with the oracle
/// armed. Asserted on the `TurnReceipt` chain and the committed registers, not on a page.
///
/// The tape is `descent::crowned_line(day)` — the Lean-mirrored winning line for the day the deploy
/// actually drew — so this drives every verb, not just the one that happens to be cheap. That
/// matters here because the shapes E2 broke sit on the `spent` RIDER (measured on the day-0 emission:
/// 24 `AnyOf`-with-`HeapField` branches, 8 `HeapField{AllowedTransitions}`, 8 `HeapField{MemberOf}`
/// and 6 `FieldsCountEquals` under one `SlotChanged{spent}` guard), and every verb in the game
/// spends breath. One un-encodable constraint there refuses the entire game, which is what "every
/// Descent move" in the outage report meant.
#[test]
fn an_honest_descent_run_is_admitted_with_the_oracle_armed() {
    arm_the_deployed_oracle();
    let mut d = Descent::deploy(7).expect("deploy + genesis with the oracle armed");
    let line = crowned_line(d.day());
    assert!(
        line.len() >= 10,
        "the crowned tape is {} verbs — too short to have driven the riders",
        line.len()
    );

    let mut receipts = Vec::new();
    for (verb, arg) in &line {
        let r = match *verb {
            DELVE => d.delve(),
            ASCEND => d.ascend(),
            SMITE => d.smite(),
            LOOT => d.loot(*arg as usize),
            UNLOCK => d.unlock(*arg as u64),
            FLEE => d.flee(),
            other => panic!("crowned_line emitted unknown verb {other}"),
        };
        let r = r.unwrap_or_else(|e| {
            panic!(
                "the crowned line's `{verb}` must COMMIT — a refusal here is the deployed executor \
                 declining to judge an honest move, not the move being illegal: {e:?}"
            )
        });
        receipts.push(r);
    }
    for w in receipts.windows(2) {
        assert_eq!(
            w[0].post_state_hash, w[1].pre_state_hash,
            "the admitted receipts must chain (each pre-state is its predecessor's post-state)"
        );
    }
    assert_eq!(d.read_reg("fate"), 1, "the crowned run is crowned");
    assert_eq!(
        d.read_relic(0),
        BANKED,
        "the prize's custody hop committed, so the relic teeth admitted a listed transition"
    );
}

/// **POLE 2 — an illegal move is REFUSED**, in the same process, by the same armed oracle.
///
/// Without this the pole above is satisfiable by an oracle that admits everything, and "the moves
/// work again" would be indistinguishable from "the teeth stopped biting" — the exact way a
/// refusal-shaped outage gets closed into an admission-shaped one.
#[test]
fn a_forged_descent_move_is_refused_with_the_oracle_armed() {
    arm_the_deployed_oracle();
    let mut d = Descent::deploy(3).expect("deploy + genesis with the oracle armed");
    d.delve().expect("way 1 is always open");
    let sim = d.sim().clone();

    // A keyless descent, forged at the raw seam so the EXECUTOR is the referee (the mover would
    // refuse this on its own and prove nothing about the installed teeth).
    let mut forged = sim.clone();
    forged.depth = 2;
    forged.wounds = 0;
    forged.spent += 1;
    let effects = d.effects_for(&forged);
    let refused = d.commit_raw(DELVE, effects);
    assert!(
        refused.is_err(),
        "a keyless descent must be REFUSED by the Lean-sourced teeth; an oracle that decides \
         everything as `ok` would pass the admit pole and destroy the game, got {refused:?}"
    );
    // Anti-ghost: the refusal committed nothing.
    assert_eq!(d.read_reg("depth"), 1);
    assert_eq!(d.read_reg("spent"), sim.spent);
}
