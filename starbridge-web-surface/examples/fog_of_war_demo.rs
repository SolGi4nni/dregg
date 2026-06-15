//! End-to-end demo of **fog-of-war IS the membrane** — the deos forcing-function
//! webgame. Run with:
//!
//! ```text
//! cd starbridge-web-surface && cargo run --example fog_of_war_demo
//! # or, for a quiet self-check that exits 0/1:
//! cd starbridge-web-surface && cargo run --example fog_of_war_demo -- --headless
//! ```
//!
//! `docs/deos/DEOS-APPS.md` §"the forcing function: a deos webgame" — the deos
//! novelty *is a game mechanic made into a security property*. This narrates a
//! short hidden-information grid skirmish on the REAL dregg cap + membrane +
//! affordance primitives, showing the five deos properties as game mechanics:
//!
//! (i)   **fog = the membrane's per-viewer projection** — Blue and Red project the
//!       SAME board to DIFFERENT views; each sees only its own frustum;
//! (ii)  **the no-peek KEYSTONE** — Blue *provably cannot rehydrate* a tile gated to
//!       Red (the membrane refuses it on the incomparable-`Custom` identity axis);
//! (iii) **moves = affordances** — a legal move fires a REAL turn; an unauthorized
//!       move (Red firing Blue's move) is a REFUSED turn (anti-cheat is free);
//! (iv)  **agents-as-players** — an AI agent fires the SAME cap-gated affordances;
//! (v)   **vision moves with the units** — marching into range reveals the enemy;
//! (vi)  **spectating = a fog-respecting frustum-snapshot**.

use starbridge_web_surface::game::{demo_skirmish, game_cell, VisionDeck, VisionGateError};
use starbridge_web_surface::{
    game::side_rights, is_attenuation, AffordanceSnapshot, AgentPlayer, AuthRequired, Board, Coord,
    Effect, FireError, InteractionLog, Membrane, MoveOutcome, Rehydration, Side, SurfaceCapability,
};

/// First 8 bytes of a hash as hex (for narrating a vk_hash compactly).
fn hex8(bytes: &[u8; 32]) -> String {
    bytes[..8].iter().map(|b| format!("{b:02x}")).collect()
}

/// Render a player's fogged view of the board as ASCII — the fog made visible. A
/// tile the player can see shows its occupant (`B`/`R`) or `.` (empty); a fogged
/// tile shows `?` (the player provably cannot see it).
fn render_view(board: &Board, side: Side) -> String {
    let view = board.project_for(side, Rehydration::Live);
    let mut out = String::new();
    for row in 0..board.rows {
        for col in 0..board.cols {
            let c = Coord::new(row, col);
            let ch = if let Some(tile) = view.visible.get(&c) {
                match &tile.occupant {
                    Some(u) => match u.side {
                        Side::Blue => 'B',
                        Side::Red => 'R',
                    },
                    None => '.',
                }
            } else {
                '?' // fog — provably un-projectable, not merely unrendered
            };
            out.push(ch);
            out.push(' ');
        }
        out.push('\n');
    }
    out
}

fn main() {
    let headless = std::env::args().any(|a| a == "--headless");
    macro_rules! say {
        ($($t:tt)*) => { if !headless { println!($($t)*); } };
    }
    let mut ok = true;
    macro_rules! check {
        ($cond:expr, $msg:expr) => {
            if !($cond) {
                ok = false;
                eprintln!("SELF-CHECK FAILED: {}", $msg);
            }
        };
    }

    say!("== Fog-of-war IS the membrane — a deos webgame ==\n");
    say!("A 5×5 grid skirmish. Blue starts top-left, Red bottom-right. Vision radius 1,");
    say!("movement radius 2. What a player can SEE is exactly what its caps authorize it");
    say!("to rehydrate — fog of war as a cap-CONFINEMENT property, not a visibility flag.\n");

    let (mut board, board_uri, web) = demo_skirmish();

    // The board is a REAL published cell in the web-of-cells (multiplayer = the
    // web-of-cells: the board a shared cell, fetchable + attested by any peer).
    let (board_resource, board_chrome) =
        web.fetch(&board_uri).expect("the board cell is published");
    assert!(
        board_resource.verify().is_ok(),
        "the board cell's attestation verifies"
    );
    say!(
        "the board is a shared cell in the web-of-cells: {}",
        board_chrome.badge()
    );
    say!("");

    // ── (i) fog = the membrane's per-viewer projection. ───────────────────────
    say!("(i) the SAME board, projected through TWO different vision caps → TWO boards\n");
    say!("    Blue's view (B=blue unit, .=empty&seen, ?=FOG / un-projectable):");
    for line in render_view(&board, Side::Blue).lines() {
        say!("        {line}");
    }
    say!("    Red's view:");
    for line in render_view(&board, Side::Red).lines() {
        say!("        {line}");
    }

    let blue_view = board.project_for(Side::Blue, Rehydration::Live);
    let red_view = board.project_for(Side::Red, Rehydration::Live);
    say!(
        "    → Blue sees {} tiles ({} fogged); Red sees {} tiles ({} fogged).",
        blue_view.visible.len(),
        blue_view.fogged,
        red_view.visible.len(),
        red_view.fogged
    );
    say!("    → SAME board, DIFFERENT views: each player sees only its own frustum.\n");
    check!(
        blue_view.fogged > 0 && red_view.fogged > 0,
        "both players have fog"
    );
    check!(
        blue_view.visible_coords() != red_view.visible_coords(),
        "the two views diverge"
    );
    check!(
        blue_view.visible_enemies().is_empty(),
        "at the opening Blue cannot see Red"
    );
    check!(
        red_view.visible_enemies().is_empty(),
        "at the opening Red cannot see Blue"
    );

    // ── (ii) the no-peek KEYSTONE: a player provably cannot rehydrate an enemy tile. ─
    say!("(ii) the KEYSTONE — Blue PROVABLY CANNOT rehydrate a tile gated to Red\n");
    let enemy_tile = Coord::new(4, 4); // Red's scout is here (ground truth)
    say!("    ground truth      : a Red unit stands at (4,4).");
    let blue_can_peek = board.can_rehydrate_tile(Side::Blue, Side::Red, enemy_tile);
    say!(
        "    Blue rehydrate (4,4) through its membrane → {}",
        if blue_can_peek {
            "RE-EXPANDED (BUG — the fog leaked!)".to_string()
        } else {
            "REFUSED — no interactive state (provable no-peek) ✓".to_string()
        }
    );
    say!("    why              : Blue's vision identity is AuthRequired::Custom{{vk=Blue}};");
    say!("                       the tile is gated to Custom{{vk=Red}}. By the GENUINE lattice");
    say!("                       two distinct Custom vk_hashes are INCOMPARABLE, so");
    say!(
        "                       is_attenuation(Blue, Red) = {} → the membrane mints NO",
        is_attenuation(&side_rights(Side::Blue), &side_rights(Side::Red))
    );
    say!("                       projection. The peek is refused at the cap lattice itself.");
    say!("    in Blue's view   : the enemy tile is ABSENT entirely — Blue cannot even");
    say!("                       distinguish 'occupied' from 'empty' there (no leak).\n");
    check!(
        !blue_can_peek,
        "KEYSTONE: Blue cannot rehydrate a Red-gated tile (no-peek)"
    );
    check!(
        !board.can_rehydrate_tile(Side::Red, Side::Blue, Coord::new(0, 0)),
        "KEYSTONE (symmetric): Red cannot rehydrate a Blue-gated tile"
    );
    check!(
        !blue_view.can_see(enemy_tile),
        "the enemy tile is not in Blue's projection at all"
    );
    check!(
        !is_attenuation(&side_rights(Side::Blue), &side_rights(Side::Red)),
        "the no-peek root cause: incomparable Custom identities"
    );

    // ── (ii-b) the no-peek, FOR REAL: the vk_hash is a genuine proof obligation. ──
    say!("(ii-b) the vk_hash is EARNED — a real proof obligation, not an inert tag\n");
    say!("    The lattice refusal above is real, but on its own the Custom{{vk}} is just an");
    say!("    identity tag — nobody had to PROVE anything to hold it. So we make it earned:");
    say!("    the vk_hash is a genuine canonical_predicate_vk of a real vision program, and");
    say!("    to project a side's tiles you must PRODUCE an Ed25519 proof a real");
    say!("    WitnessedPredicateRegistry verifies (the SAME registry the executor runs).\n");

    // Blue holds ONLY Blue's vision secret. Red holds ONLY Red's.
    let blue_deck = VisionDeck::for_player(Side::Blue);
    let blue_self_msg = board.vision_signing_message(Side::Blue, Coord::new(0, 0));
    let blue_proves_self = board.prove_vision(&blue_deck, Side::Blue, Side::Blue, &blue_self_msg);
    say!(
        "    Blue proves Blue's vision (holds the secret) → {}",
        match &blue_proves_self {
            Ok(()) => "OK — genuine Ed25519 proof, registry-verified ✓".to_string(),
            Err(e) => {
                ok = false;
                format!("UNEXPECTED REFUSAL: {e:?}")
            }
        }
    );
    let enemy_msg = board.vision_signing_message(Side::Blue, enemy_tile);
    let blue_proves_red = board.prove_vision(&blue_deck, Side::Blue, Side::Red, &enemy_msg);
    say!("    Blue proves RED's vision (to peek) → {}",
        match &blue_proves_red {
            Err(VisionGateError::NoSecretForSide { side }) =>
                format!("REFUSED — NoSecretForSide({side:?}): Blue cannot even CONSTRUCT a verifying proof ✓"),
            Ok(()) => { ok = false; "PROVED (BUG — the proof obligation leaked!)".to_string() }
            Err(e) => { ok = false; format!("WRONG ERROR: {e:?}") }
        }
    );
    say!("      → no-peek FOR REAL: the enemy's vision is UNPROVABLE to Blue (it lacks");
    say!("        Red's secret). Not lattice incomparability alone — a real EUF-CMA");
    say!("        obligation, fail-closed. The vk_hash is now load-bearing.");
    say!(
        "      vk_hash(Blue) = canonical_predicate_vk(Blue's vision program): {}",
        hex8(&match side_rights(Side::Blue) {
            AuthRequired::Custom { vk_hash } => vk_hash,
            _ => [0u8; 32],
        })
    );
    say!("");
    check!(
        blue_proves_self.is_ok(),
        "Blue can prove its own vision (holds the secret)"
    );
    check!(
        matches!(
            blue_proves_red,
            Err(VisionGateError::NoSecretForSide { side: Side::Red })
        ),
        "KEYSTONE (proof): Blue cannot PROVE Red's vision — no-peek as a real obligation"
    );
    // And a forged proof (Blue signing, presented as Red's) is rejected by the registry.
    {
        use starbridge_web_surface::vision_predicate::{
            FogVisionProducer, PredicateInput, WitnessProducer,
        };
        let referee = VisionDeck::referee();
        let blue_prog = VisionDeck::keypair_for(Side::Blue).program();
        let blue_proof = FogVisionProducer::new(VisionDeck::keypair_for(Side::Blue))
            .produce(
                &blue_prog.commitment(),
                &PredicateInput::SigningMessage(&enemy_msg),
                &[],
            )
            .expect("Blue produces its own proof");
        let forged = referee.verify_presented_proof(Side::Red, &enemy_msg, &blue_proof);
        say!(
            "    a forged proof (Blue's signature, claimed as Red's vision) → {}",
            if forged.is_err() {
                "REJECTED by the real Ed25519 verifier ✓"
            } else {
                "ACCEPTED (BUG)"
            }
        );
        check!(
            forged.is_err(),
            "a forged cross-side proof is rejected by the real registry"
        );
    }
    say!("");

    // ── (iii) moves = affordances: legal fires a real turn; unauthorized is refused. ─
    say!("(iii) moves = cap-gated affordances — a legal move fires a REAL turn;");
    say!(
        "      an unauthorized move (Red firing Blue's move) is a REFUSED turn (free anti-cheat)\n"
    );

    let blue_moves = board.move_surface_for(Side::Blue);
    let blue_cap = board.vision_cap_for(Side::Blue);
    let red_cap = board.vision_cap_for(Side::Red);

    // Blue fires a legal move (B-scout (0,0)->(2,2), Chebyshev 2 ≤ movement 2).
    let mv = "move:B-scout:2-2";
    let intent = blue_moves
        .fire(mv, game_cell(0xB1, 1), &blue_cap)
        .expect("Blue fires its own legal move (authorized)");
    say!("    Blue fires `{mv}` : ADMITTED → verified-turn intent");
    say!("      effect (the turn) : {:?}", intent.effect_summary());
    say!("      → a REAL dregg_turn::Effect (SetField recording the new position).");
    check!(
        matches!(intent.effect, Effect::SetField { .. }),
        "the move fires a real SetField turn"
    );

    // Red tries to fire BLUE's move — REFUSED (Red's identity ⟂ Blue's).
    let refused = blue_moves.fire(mv, game_cell(0xED, 1), &red_cap);
    say!(
        "    Red fires `{mv}`  : {}",
        match &refused {
            Err(FireError::Unauthorized { .. }) =>
                "REFUSED (Unauthorized — Red's identity ⟂ Blue-required rights) ✓".to_string(),
            Err(e) => {
                ok = false;
                format!("WRONG ERROR: {e:?}")
            }
            Ok(_) => {
                ok = false;
                "WRONGLY ADMITTED (anti-cheat FAILED)".to_string()
            }
        }
    );
    say!("      → anti-cheat is FREE: an illegal move is just an unauthorized turn,");
    say!("        refused by the SAME is_attenuation gate, in-band — never a side check.\n");
    check!(
        matches!(refused, Err(FireError::Unauthorized { .. })),
        "Red firing Blue's move is refused"
    );
    // An out-of-range move is not even DECLARED (the game-rule half of anti-cheat).
    check!(
        blue_moves.get("move:B-scout:4-4").is_none(),
        "an out-of-range move is never declared"
    );

    // Apply Blue's legal move → the board advances, turn passes to Red.
    let outcome = board
        .apply_move(&intent, Side::Blue)
        .expect("Blue's move applies");
    say!("    Blue's move applied: {outcome:?}");
    say!(
        "      → B-scout relocated; the turn passed to Red (ply {}).\n",
        board.ply
    );
    check!(
        matches!(outcome, MoveOutcome::Moved { to, .. } if to == Coord::new(2, 2)),
        "Blue's scout relocated to (2,2)"
    );
    check!(board.turn == Side::Red, "the turn passed to Red");

    // ── (iv) agents-as-players: an AI fires the SAME cap-gated affordances. ────
    say!("(iv) agents-as-players — a Red AI agent fires the SAME cap-gated affordances\n");
    let red_agent = AgentPlayer::new(Side::Red, game_cell(0xA2, 0));
    let agent_intent = red_agent
        .choose_move(&board)
        .expect("the Red agent has a legal authorized move");
    say!("    the Red agent chooses+fires a move through the affordance gate:");
    say!(
        "      effect (the turn) : {:?}",
        agent_intent.effect_summary()
    );
    say!("      actor             : the agent's own cell (it fired as itself)");
    say!("      → the agent is no more privileged than a human: the move it returns was");
    say!("        admitted by the REAL is_attenuation. An AI firing an ENEMY unit's move");
    say!("        would be Unauthorized, identical to a human cheating.");
    check!(
        matches!(agent_intent.effect, Effect::SetField { .. }),
        "the agent's move is a real turn"
    );
    check!(
        agent_intent.actor == game_cell(0xA2, 0),
        "the agent fired as itself"
    );
    let agent_outcome = board
        .apply_move(&agent_intent, Side::Red)
        .expect("the agent's move applies");
    say!(
        "    the agent's move applied: {agent_outcome:?} (ply {})\n",
        board.ply
    );
    check!(board.turn == Side::Blue, "the turn passed back to Blue");

    // ── (v) vision moves with the units — marching into range reveals the enemy. ─
    say!("(v) vision moves with the units — marching toward the enemy lifts the fog on it\n");
    // A fresh, self-contained march scenario (the first board's units are now
    // mid-skirmish — one captured — so we show the reveal mechanic on a clean
    // board where a lone Blue scout marches across an open grid toward a Red unit).
    let (mut march, _march_uri, _march_web) = demo_skirmish();
    say!("    a lone Blue scout marches from its corner toward Red's corner; we fire");
    say!("    successive cap-gated moves and watch the fog lift as Red enters vision:\n");
    say!(
        "    opening — Blue sees {} enemy unit(s) (full fog between the corners):",
        march
            .project_for(Side::Blue, Rehydration::Live)
            .visible_enemies()
            .len()
    );

    let mut revealed = false;
    let target = Coord::new(4, 4); // Red's corner — march toward it
    for step in 0..6 {
        // The march is about the FOG mechanic, not the turn order; keep it Blue's
        // move each step (Red holds position).
        march.turn = Side::Blue;
        let surface = march.move_surface_for(Side::Blue);
        let held = march.vision_cap_for(Side::Blue);
        // Pick the authorized Blue move whose destination gets CLOSEST to Red's
        // corner (marching the lead unit forward). Tie-break: greatest forward step.
        let best = surface
            .project_for(&held)
            .into_iter()
            .filter_map(|a| {
                let rc = a.name.rsplit(':').next()?.to_string();
                let mut p = rc.split('-');
                let r: u8 = p.next()?.parse().ok()?;
                let c: u8 = p.next()?.parse().ok()?;
                Some((a.name.clone(), Coord::new(r, c)))
            })
            .min_by_key(|(_, d)| d.chebyshev(target));
        let Some((name, dest)) = best else { break };
        // Find which unit this move belongs to (its index in the surface effect) so
        // we fire as the owning side; the actor is the moving Blue unit's cell.
        let intent = match surface.fire(&name, game_cell(0xB1, 1), &held) {
            Ok(i) => i,
            Err(_) => break,
        };
        if march.apply_move(&intent, Side::Blue).is_err() {
            break;
        }
        let v = march.project_for(Side::Blue, Rehydration::Live);
        let seen = v.visible_enemies().len();
        say!(
            "    step {}: a Blue unit advances to {:?}; Blue now sees {} enemy unit(s)",
            step + 1,
            dest,
            seen
        );
        if seen > 0 {
            revealed = true;
            say!("\n    Blue's view after the reveal (the fog lifted on the enemy tile):");
            for line in render_view(&march, Side::Blue).lines() {
                say!("        {line}");
            }
            say!("      → the enemy entered the marching unit's vision radius: a tile that");
            say!("        was provably un-projectable is NOW in Blue's frustum. Vision is not");
            say!("        a static map — it moves with the units, as a live cap projection.\n");
            break;
        }
    }
    check!(
        revealed,
        "marching into range reveals an enemy unit (dynamic fog)"
    );

    // ── (vi) spectating = a fog-respecting frustum-snapshot. ──────────────────
    say!("(vi) spectating = a rehydratable frustum-snapshot that RESPECTS the spectator's fog\n");
    // A Blue-gated spectator snapshot: it re-expands only Blue's authorized moves,
    // and a Blue spectator cannot re-expand Red's hidden state.
    let snap = board.snapshot_for(
        Side::Blue,
        board_uri.clone(),
        InteractionLog::new(),
        /* sources_reachable */ true,
    );
    say!("    a Blue spectator's snapshot embeds a Sturdyref + the culling boundary:");
    say!(
        "      lineage identity  : {:?} (gated to Blue's view)",
        snap.sturdyref.lineage.window.rights
    );
    say!(
        "      boundary extent   : {} move-affordance names",
        snap.boundary_extent()
    );
    let names_red = snap
        .boundary
        .affordance_names
        .iter()
        .any(|n| n.contains("R-"));
    say!(
        "      contains Red moves: {} (a Blue spectator's snapshot must name NO Red moves)",
        if names_red {
            "YES (BUG — fog leaked into the snapshot!)"
        } else {
            "NO ✓"
        }
    );
    say!("      → spectating inherits the no-peek property: a Blue-gated spectator");
    say!("        rehydrates ONLY Blue's view; Red's hidden state never re-expands.");
    check!(
        !names_red,
        "the Blue spectator's snapshot names no Red moves (fog respected)"
    );
    check!(
        snap.boundary_extent() > 0,
        "the snapshot names Blue's moves"
    );
    // The snapshot is a real frustum frame (a sturdyref + a boundary), not the state.
    let _is_real: &AffordanceSnapshot = &snap;
    // A Blue-gated spectator's membrane cannot project a Red tile (no-peek carries).
    let blue_spectator = Membrane::new(SurfaceCapability::scoped(
        game_cell(0x5C, 1),
        side_rights(Side::Blue),
        board.frustum_for(Side::Blue),
        [],
    ));
    let red_lineage = board.vision_lineage_for(Side::Red);
    check!(
        blue_spectator.project(&red_lineage).is_err(),
        "a Blue spectator's membrane refuses to project Red's facet (no-peek in spectating)"
    );

    if ok {
        say!("\nOK — fog-of-war runs as a cap-CONFINEMENT property on the real dregg primitives:");
        say!("  · vision is the per-viewer membrane projection — what you see is what your caps");
        say!("    authorize you to rehydrate (the no-peek KEYSTONE: incomparable Custom identities);");
        say!("  · moves are cap-gated affordances firing REAL turns — anti-cheat is the gate itself;");
        say!("  · an AI agent fires the SAME affordances, confined by the SAME caps;");
        say!("  · spectating is a fog-respecting frustum-snapshot. The security property IS the");
        say!("    game mechanic — htmx on crack you can play.");
        // A loud, greppable success marker even in --headless.
        println!("fog_of_war_demo: ALL CHECKS PASSED");
        std::process::exit(0);
    } else {
        eprintln!("fog_of_war_demo: SELF-CHECK FAILURES — see above");
        std::process::exit(1);
    }
}
