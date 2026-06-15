//! **deos WORLD** — the bigger fog-of-war demo: a federated, terrain-shaped,
//! objective-driven, agent-played multiplayer world where every security property
//! is a game mechanic. Run with:
//!
//! ```text
//! cd starbridge-web-surface && cargo run --example deos_world_demo
//! # quiet self-check (exits 0/1):
//! cd starbridge-web-surface && cargo run --example deos_world_demo -- --headless
//! ```
//!
//! This is the `fog_of_war_demo` thesis at SCALE — a genuine "htmx on crack you can
//! PLAY" world that exercises the WHOLE deos thesis on the real dregg cap + membrane
//! + affordance + web-of-cells primitives (Tier A — no circuit crate; the ZK Tier B
//! vision AIR is the named cross-crate follow-up in `docs/deos/DEOS-APPS.md`):
//!
//!   (1) **a real world** — 12×12, a forest belt + mountains that OCCLUDE
//!       line-of-sight (the vision frustum has shape, not a uniform disc), four unit
//!       archetypes (Scout/Soldier/Sensor/Commander), and three capturable objectives;
//!   (2) **fog = the membrane's per-viewer projection** — Blue and Red see different
//!       boards; the no-peek KEYSTONE carries (Blue provably cannot rehydrate a Red
//!       tile, and cannot even PROVE Red's vision);
//!   (3) **moves + objective-captures = cap-gated verified turns** — a move fires a
//!       real `SetField`, an objective claim a real `EmitEvent`; an unauthorized fire
//!       is refused in-band (anti-cheat is free);
//!   (4) **the web-of-cells distribution** — a LOBBY of worlds, each publishing its
//!       board/players/objectives as real attested cells;
//!   (5) **agents-as-players** — TWO AI agents (different policies) play a FULL match
//!       to a win condition, every action through the same cap gate (neither can cheat);
//!   (6) **the membrane as a negotiation surface** (the GitHub-org-settings page) —
//!       a player grants attenuated spectator rights (watch-my-side / scoreboard /
//!       full-post-game), an over-broad grant is refused, a re-share chain (A→B→C)
//!       attenuates, and the spectator view is liveness-typed + fog-respecting.

use starbridge_web_surface::game::{demo_world, play_match};
use starbridge_web_surface::world::{
    ambient_log, player_authority, spectator_cell, witnessed_log_for,
};
use starbridge_web_surface::{
    game::{side_rights, VisionDeck, VisionGateError},
    is_attenuation, AgentPlayer, AgentPolicy, Board, Coord, Effect, FireError, Lobby,
    MembraneNegotiation, NegotiationError, Rehydration, Side, SpectatorSession, UnitKind,
    WinReason,
};

/// First 8 bytes of a hash as hex.
fn hex8(bytes: &[u8; 32]) -> String {
    bytes[..8].iter().map(|b| format!("{b:02x}")).collect()
}

/// Render the board's GROUND TRUTH (the engine's omniscient view) — terrain glyphs
/// with units overlaid. For the narration of the world layout (NOT a player view).
fn render_truth(board: &Board) -> String {
    let mut out = String::new();
    for row in 0..board.rows {
        for col in 0..board.cols {
            let c = Coord::new(row, col);
            let ch = if let Some(u) = board.unit_at(c) {
                // A unit: uppercase = Blue, lowercase = Red; letter = archetype.
                let g = match u.kind {
                    UnitKind::Scout => 's',
                    UnitKind::Soldier => 'o',
                    UnitKind::Sensor => 'e',
                    UnitKind::Commander => 'k',
                };
                if u.side == Side::Blue {
                    g.to_ascii_uppercase()
                } else {
                    g
                }
            } else if board.objective_at(c).is_some() {
                '*' // a control point
            } else {
                board.terrain_at(c).glyph()
            };
            out.push(ch);
            out.push(' ');
        }
        out.push('\n');
    }
    out
}

/// Render a player's FOGGED view: a visible tile shows its occupant (`B`/`R`) or
/// terrain glyph; a fogged tile shows `?` (provably un-projectable).
fn render_view(board: &Board, side: Side) -> String {
    let view = board.project_for(side, Rehydration::Live);
    let mut out = String::new();
    for row in 0..board.rows {
        for col in 0..board.cols {
            let c = Coord::new(row, col);
            let ch = if view.can_see(c) {
                match view.unit_at(c) {
                    Some(u) => {
                        if u.side == Side::Blue {
                            'B'
                        } else {
                            'R'
                        }
                    }
                    None => board.terrain_at(c).glyph(),
                }
            } else {
                '?'
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

    say!("╔══════════════════════════════════════════════════════════════════════════╗");
    say!("║  deos WORLD — fog-of-war as a confinement theorem, at scale                ║");
    say!("║  a federated, terrain-shaped, objective-driven, agent-played multiplayer   ║");
    say!("║  world where every security property IS a game mechanic. htmx on crack.    ║");
    say!("╚══════════════════════════════════════════════════════════════════════════╝\n");

    // ── (1) the world: terrain shapes the fog; the army is heterogeneous. ──────
    say!("(1) THE WORLD — a 12×12 map with terrain (line-of-sight!) + objectives\n");
    let board = demo_world();
    say!("    ground truth (engine's omniscient view):");
    say!("      glyphs: . open  # forest(blocks sight)  ^ mountain(blocks sight+move)");
    say!("              * objective   S/s Scout  O/o Soldier  E/e Sensor  K/k Commander");
    say!("              (UPPER = Blue, lower = Red)\n");
    for line in render_truth(&board).lines() {
        say!("        {line}");
    }
    say!("");
    say!("    → the forest belt across the middle OCCLUDES vision: a unit cannot see");
    say!("      corner-to-corner; the frustum is a line-of-sight CONE the terrain carves,");
    say!("      not a uniform disc. Four archetypes give the army real texture.");
    check!(board.rows == 12 && board.cols == 12, "the world is 12×12");
    check!(board.objectives.len() == 3, "three capturable objectives");
    check!(
        board.units.iter().any(|u| u.kind == UnitKind::Commander),
        "each side fields a Commander (the king)"
    );

    // Show line-of-sight occlusion concretely.
    let scout = board
        .units
        .iter()
        .find(|u| u.side == Side::Blue && u.kind == UnitKind::Scout)
        .unwrap();
    let blue_frustum = board.frustum_for(Side::Blue);
    let lit = blue_frustum.len();
    say!(
        "\n    Blue's Scout at {:?} (vision {}) lights {} tiles — far fewer than a clear",
        scout.at,
        scout.vision,
        lit
    );
    say!("    disc would, because the forest blocks sight past it (occlusion is real).");
    // Find a tile in range but occluded (behind the forest belt) to prove it.
    let mut proved_occlusion = false;
    for r in 0..12u8 {
        for c in 0..12u8 {
            let t = Coord::new(r, c);
            if scout.at.chebyshev(t) <= scout.vision
                && !board.has_line_of_sight(scout.at, t, scout.vision)
            {
                say!(
                    "    e.g. {:?} is IN RANGE (Chebyshev {}) but OCCLUDED → fogged for Blue.",
                    t,
                    scout.at.chebyshev(t)
                );
                proved_occlusion = true;
                break;
            }
        }
        if proved_occlusion {
            break;
        }
    }
    check!(
        proved_occlusion,
        "a tile in range is occluded by terrain (line-of-sight is real)"
    );
    say!("");

    // ── (2) fog = per-viewer projection; the no-peek keystone carries. ─────────
    say!("(2) FOG = the membrane's per-viewer projection — two players, two boards\n");
    let blue_view = board.project_for(Side::Blue, Rehydration::Live);
    let red_view = board.project_for(Side::Red, Rehydration::Live);
    say!("    Blue's fogged view (B/R seen units, terrain glyph if seen, ? = fog):");
    for line in render_view(&board, Side::Blue).lines() {
        say!("        {line}");
    }
    say!(
        "    → Blue sees {} tiles ({} fogged); Red sees {} tiles ({} fogged). SAME world,",
        blue_view.visible.len(),
        blue_view.fogged,
        red_view.visible.len(),
        red_view.fogged
    );
    say!("      DIFFERENT projections. At the opening neither army can see the other.");
    check!(
        blue_view.fogged > 0 && red_view.fogged > 0,
        "both players have fog"
    );
    check!(
        blue_view.visible_coords() != red_view.visible_coords(),
        "the views diverge"
    );

    // The no-peek keystone (carried from the base game): Blue cannot rehydrate a
    // Red-gated tile, and cannot even PROVE Red's vision.
    let red_cmd = board
        .units
        .iter()
        .find(|u| u.side == Side::Red && u.kind == UnitKind::Commander)
        .unwrap();
    let blue_peek = board.can_rehydrate_tile(Side::Blue, Side::Red, red_cmd.at);
    say!(
        "\n    no-peek KEYSTONE: Blue rehydrate Red's Commander tile {:?} → {}",
        red_cmd.at,
        if blue_peek {
            "RE-EXPANDED (BUG!)".to_string()
        } else {
            "REFUSED ✓".to_string()
        }
    );
    check!(
        !blue_peek,
        "no-peek: Blue cannot rehydrate a Red-gated tile"
    );
    let blue_deck = VisionDeck::for_player(Side::Blue);
    let enemy_msg = board.vision_signing_message(Side::Blue, red_cmd.at);
    let proves_red = board.prove_vision(&blue_deck, Side::Blue, Side::Red, &enemy_msg);
    say!(
        "    no-peek FOR REAL : Blue PROVE Red's vision → {}",
        match &proves_red {
            Err(VisionGateError::NoSecretForSide { .. }) =>
                "REFUSED (no secret — unprovable) ✓".to_string(),
            _ => {
                ok = false;
                "PROVED (BUG!)".to_string()
            }
        }
    );
    say!(
        "      (is_attenuation(Blue,Red) = {}; vk(Blue) = {}…)",
        is_attenuation(&side_rights(Side::Blue), &side_rights(Side::Red)),
        match side_rights(Side::Blue) {
            dregg_cell::AuthRequired::Custom { vk_hash } => hex8(&vk_hash),
            _ => "??".into(),
        }
    );
    check!(
        matches!(proves_red, Err(VisionGateError::NoSecretForSide { .. })),
        "no-peek (proof): Blue cannot prove Red's vision"
    );
    say!("");

    // ── (3) moves + objective-captures = cap-gated verified turns. ─────────────
    say!("(3) MOVES + OBJECTIVE-CAPTURES = cap-gated verified turns (anti-cheat is free)\n");
    // A Blue move fires a real SetField; Red firing it is refused.
    let mv_surface = board.move_surface_for(Side::Blue);
    let blue_cap = board.vision_cap_for(Side::Blue);
    let red_cap = board.vision_cap_for(Side::Red);
    let a_move = mv_surface
        .all_names()
        .into_iter()
        .find(|n| n.contains("scout"))
        .expect("a scout move");
    let mover = board
        .units
        .iter()
        .find(|u| a_move.contains(&u.name))
        .unwrap()
        .id;
    let intent = mv_surface
        .fire(&a_move, mover, &blue_cap)
        .expect("Blue's own move is authorized");
    say!("    Blue fires `{a_move}`");
    say!(
        "      → {:?}  (a REAL SetField turn the executor would run)",
        intent.effect_summary()
    );
    check!(
        matches!(intent.effect, Effect::SetField { .. }),
        "a move fires a real SetField"
    );
    let refused = mv_surface.fire(&a_move, board.units[5].id, &red_cap);
    say!(
        "    Red fires the SAME move → {}",
        match &refused {
            Err(FireError::Unauthorized { .. }) =>
                "REFUSED (Unauthorized — incomparable identity) ✓".to_string(),
            _ => {
                ok = false;
                "ADMITTED (anti-cheat FAILED)".to_string()
            }
        }
    );
    check!(
        matches!(refused, Err(FireError::Unauthorized { .. })),
        "Red firing Blue's move is refused"
    );

    // An objective-capture is a real EmitEvent turn (set up a unit on an objective).
    {
        use starbridge_web_surface::Objective;
        let obj = Objective::new("demo-point", Coord::new(0, 0), 9);
        let cap_board = Board::with_terrain_and_objectives(
            5,
            5,
            starbridge_web_surface::game_cell(0xB0, 99),
            vec![starbridge_web_surface::Unit::of_kind(
                Side::Blue,
                UnitKind::Soldier,
                Coord::new(0, 0),
                1,
            )],
            vec![],
            vec![obj],
        );
        let cap_surface = cap_board.capture_surface_for(Side::Blue);
        let cap_intent = cap_surface
            .fire(
                "capture:demo-point",
                cap_board.units[0].id,
                &cap_board.vision_cap_for(Side::Blue),
            )
            .expect("Blue captures the point it stands on");
        say!(
            "    Blue claims an objective it stands on → {:?}  (a REAL EmitEvent turn)",
            cap_intent.effect_summary()
        );
        check!(
            matches!(cap_intent.effect, Effect::EmitEvent { .. }),
            "a capture fires a real EmitEvent"
        );
    }
    say!("      → two different real effect kinds (SetField, EmitEvent), both cap-gated.");
    say!("");

    // ── (4) the web-of-cells distribution — a lobby of worlds. ─────────────────
    say!("(4) THE WEB-OF-CELLS — a LOBBY of federated worlds (each cell attested)\n");
    let mut lobby = Lobby::new(3);
    let _a = lobby.host("alpha", demo_world());
    let _b = lobby.host("bravo", demo_world());
    say!(
        "    hosted {} worlds in one lobby (a federation).",
        lobby.world_count()
    );
    let alpha = lobby.world("alpha").unwrap();
    say!(
        "    world 'alpha' publishes {} cells (board + 2 players + 3 objectives):",
        alpha.cell_count()
    );
    let (board_res, board_chrome) = lobby
        .web
        .fetch(&alpha.board_uri)
        .expect("the board cell is published");
    say!("      board cell : {}", board_chrome.badge());
    say!(
        "      verifies   : {}",
        if board_res.verify().is_ok() {
            "✓ attested"
        } else {
            "✗"
        }
    );
    check!(alpha.cell_count() == 6, "the world publishes 6 cells");
    check!(
        board_res.verify().is_ok(),
        "the world's board cell is attested"
    );
    // Distinct worlds → distinct cells (federated addressing, no collision).
    check!(
        lobby.worlds[0].board_uri != lobby.worlds[1].board_uri,
        "two federated worlds have distinct board cells"
    );
    say!("    → a peer reaches the world by resolving dregg:// refs (a verified attested");
    say!("      read), not by trusting a server. Each player & objective is its own cell.");
    say!("");

    // ── (5) agents-as-players — a FULL match to a decision, all through the gate. ─
    say!("(5) AGENTS-AS-PLAYERS — two AIs play a FULL match to a win condition\n");
    let blue_agent =
        AgentPlayer::with_policy(Side::Blue, spectator_cell(1), AgentPolicy::Aggressive);
    let red_agent = AgentPlayer::with_policy(Side::Red, spectator_cell(2), AgentPolicy::Objective);
    say!("    Blue = Aggressive (hunt the enemy), Red = Objective (contest the map).");
    say!("    every move is fired through the cap-gated affordance surface — NEITHER");
    say!("    agent can cheat (no ambient authority, no out-of-band move).\n");
    let result = play_match(demo_world(), &blue_agent, &red_agent, 600);
    say!(
        "    the match played {} plies; final ground truth:",
        result.board.ply
    );
    for line in render_truth(&result.board).lines() {
        say!("        {line}");
    }
    match &result.game_over {
        Some(go) => {
            let reason = match go.reason {
                WinReason::Decapitation => "DECAPITATION (took the enemy Commander)",
                WinReason::Domination => "DOMINATION (held a majority of objectives)",
                WinReason::Annihilation => "ANNIHILATION (wiped out the enemy)",
            };
            say!(
                "\n    → {} WINS by {} (objectives: Blue {} / Red {}).",
                go.winner.label(),
                reason,
                result.board.objectives_held(Side::Blue),
                result.board.objectives_held(Side::Red)
            );
        }
        None => say!("\n    → a draw (the ply budget was reached)."),
    }
    say!(
        "    the match log is {} fired affordances — each a real verified turn.",
        result.log.len()
    );
    check!(
        result.game_over.is_some(),
        "the agent match reached a decision"
    );
    check!(
        !result.log.is_empty(),
        "the match produced a real fired-affordance log"
    );
    say!("    → THIS is the agentic desktop: AI players whose action space IS their");
    say!("      attenuated cap set. A smarter brain does not get a bigger cage.");
    say!("");

    // ── (6) the membrane as a negotiation surface — the org-settings page. ─────
    say!("(6) THE MEMBRANE NEGOTIATION — the GitHub-org-settings page for spectating\n");
    let world = lobby.world("alpha").unwrap();
    let neg = MembraneNegotiation::for_world(world);
    let blue_held = player_authority(world, Side::Blue);

    // (a) A player grants a view of ITS OWN side (allowed); a view of the ENEMY
    //     side is REFUSED (you can't add someone to a team you're not on).
    let own = neg.propose_one_side(Side::Blue, &blue_held, Side::Blue);
    say!(
        "    Blue grants a spectator a view of BLUE's side → {}",
        if own.is_ok() {
            "GRANTED ✓".to_string()
        } else {
            format!("{own:?}")
        }
    );
    let enemy = neg.propose_one_side(Side::Blue, &blue_held, Side::Red);
    say!(
        "    Blue grants a view of RED's side → {}",
        match &enemy {
            Err(NegotiationError::GranterLacksAuthority { .. }) =>
                "REFUSED (Blue lacks Red's authority — the no-peek, at the grant layer) ✓"
                    .to_string(),
            _ => {
                ok = false;
                "GRANTED (BUG — Blue leaked Red's view!)".to_string()
            }
        }
    );
    check!(own.is_ok(), "a player can grant a view of its own side");
    check!(
        matches!(enemy, Err(NegotiationError::GranterLacksAuthority { .. })),
        "a player CANNOT grant a view of the enemy side"
    );
    let grant = own.unwrap();

    // (b) The grant's spectator session is fog-respecting + liveness-typed.
    let witnessed = witnessed_log_for(&lobby.web, world);
    let live = SpectatorSession::open(world, &grant, &witnessed, /*sources reachable*/ true);
    let replayed = SpectatorSession::open(world, &grant, &witnessed, /*sources gone*/ false);
    let recon = SpectatorSession::open(world, &grant, &ambient_log(), false);
    say!("\n    the Blue-side spectator session is LIVENESS-TYPED (honest by construction):");
    say!("      sources reachable        → {:?}", live.liveness);
    say!("      sources gone, witnessed  → {:?}", replayed.liveness);
    say!("      sources gone, ambient    → {:?}", recon.liveness);
    check!(live.liveness == Rehydration::Live, "reachable → Live");
    check!(
        replayed.liveness == Rehydration::ReplayedDeterministic,
        "witnessed → ReplayedDeterministic"
    );
    check!(
        recon.liveness == Rehydration::ReconstructedApproximate,
        "ambient → ReconstructedApproximate"
    );
    say!("    → the system CANNOT lie about whether you watch the live match or a replay.");

    // (c) A scoreboard (objectives-only) grant leaks no unit positions.
    let scoreboard = neg
        .propose_objectives_only(Side::Blue)
        .expect("anyone may grant a scoreboard");
    let sb_session = SpectatorSession::open(world, &scoreboard, &witnessed, true);
    say!("\n    a SCOREBOARD grant (objectives-only) reveals control points but NO units:");
    say!(
        "      visible tiles: {} (the objective tiles)",
        sb_session.visible.len()
    );
    say!(
        "      leaks Blue units: {}; leaks Red units: {}",
        sb_session.reveals_unit_of(world, Side::Blue),
        sb_session.reveals_unit_of(world, Side::Red)
    );
    check!(
        !sb_session.reveals_unit_of(world, Side::Blue)
            && !sb_session.reveals_unit_of(world, Side::Red),
        "the scoreboard scope leaks no unit positions"
    );

    // (d) A re-share chain (A→B→C) attenuates; an amplifying reshare is refused.
    let mut narrow = std::collections::BTreeSet::new();
    if let Some(first) = grant.cap.fetch_allow.as_ref().and_then(|s| s.iter().next()) {
        narrow.insert(first.clone());
    }
    let narrower = starbridge_web_surface::SurfaceCapability::scoped(
        world.board.cell,
        side_rights(Side::Blue),
        narrow,
        [],
    );
    let reshared = neg.reshare(&grant, narrower);
    say!(
        "\n    re-share A→B→C: B forwards a NARROWER view to C → {}",
        if reshared.is_ok() {
            "ADMITTED ✓".to_string()
        } else {
            format!("{reshared:?}")
        }
    );
    let mut wider = grant.cap.fetch_allow.clone().unwrap_or_default();
    wider.insert("dregg://tile-99-99".to_string());
    let amplifying = starbridge_web_surface::SurfaceCapability::scoped(
        world.board.cell,
        side_rights(Side::Blue),
        wider,
        [],
    );
    let amp = neg.reshare(&grant, amplifying);
    say!(
        "    re-share A→B→C: B forwards a WIDER view than it holds → {}",
        match &amp {
            Err(NegotiationError::ReshareWouldAmplify) =>
                "REFUSED (amplification — the anti-ghost tooth) ✓".to_string(),
            _ => {
                ok = false;
                "ADMITTED (BUG — the chain amplified!)".to_string()
            }
        }
    );
    check!(reshared.is_ok(), "a narrower reshare is admitted");
    check!(
        matches!(amp, Err(NegotiationError::ReshareWouldAmplify)),
        "an amplifying reshare is refused"
    );

    // (e) A full-board grant is refused while the game is live (post-game only).
    let full_live = neg.propose_full_post_game(Side::Blue);
    say!(
        "\n    a FULL-board grant while the game is LIVE → {}",
        match &full_live {
            Err(NegotiationError::GameStillLive) =>
                "REFUSED (would leak the fog — make-public-needs-no-secrets) ✓".to_string(),
            _ => {
                ok = false;
                "GRANTED (BUG!)".to_string()
            }
        }
    );
    check!(
        matches!(full_live, Err(NegotiationError::GameStillLive)),
        "a full grant is refused mid-game"
    );
    say!("    → every membrane primitive has a boring, familiar home on a settings page:");
    say!("      teams=cap groups · roles=the attenuation lattice · visibility=scope ·");
    say!("      fork-policy=re-share rules · member-mgmt=grant/revoke. Familiar UX,");
    say!("      cap+proof substrate. That is what makes it adoptable AND sound.");

    // ── verdict ───────────────────────────────────────────────────────────────
    if ok {
        say!("\n────────────────────────────────────────────────────────────────────────────");
        say!("OK — the deos WORLD runs end-to-end on the genuine dregg cap discipline:");
        say!("  · a terrain-shaped, heterogeneous, objective-driven 12×12 multiplayer world;");
        say!("  · fog = the per-viewer membrane projection (the no-peek keystone carries);");
        say!("  · moves + objective-captures = cap-gated REAL turns (anti-cheat is free);");
        say!("  · the web-of-cells distribution — a lobby of federated, attested worlds;");
        say!("  · TWO AI agents play a FULL match to a decision, confined by the same caps;");
        say!("  · the membrane is a NEGOTIATION surface (the org-settings page): attenuated,");
        say!("    re-shareable, liveness-typed, fog-respecting spectator grants.");
        say!("  The security properties ARE the game mechanics. htmx on crack you can PLAY.");
        say!("  (Tier A — sound cap-discipline; the ZK Tier-B vision AIR is the named");
        say!("   cross-crate follow-up. The intent→live-TurnExecutor dispatch is the one");
        say!("   inherited seam, marked honestly throughout.)");
        // A loud, greppable success marker even in --headless.
        println!("deos_world_demo: ALL CHECKS PASSED");
        std::process::exit(0);
    } else {
        eprintln!("deos_world_demo: SELF-CHECK FAILURES — see above");
        std::process::exit(1);
    }
}
