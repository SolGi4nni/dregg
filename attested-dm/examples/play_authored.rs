//! THE LANTERN OF THE FEN — a full winning playthrough of a dungeon that exists ONLY as text.
//!
//! Run: `cargo run -p attested-dm --example play_authored`
//!
//! Nothing here is a hand-written Rust world. The adventure lives in
//! `dungeons/lantern_fen.dungeon`, is parsed by [`attested_dm::parse_dungeon`] into a real
//! [`GameWorld`], and is played to a WIN through the very same [`GameSession`] as the four
//! bundled dungeons — every legal move a cap-gated, attested, on-chain turn. An authored-in-text
//! world is a first-class attested dungeon: the AI proposes, the world disposes, and the whole
//! playthrough re-verifies as an authentic hash chain.

use attested_dm::{parse_dungeon, GameSession, GameStatus, PlayResult};

const SOURCE: &str = include_str!("../dungeons/lantern_fen.dungeon");

fn main() {
    let world = parse_dungeon(SOURCE).expect("the authored dungeon parses and validates clean");
    let mut game = GameSession::open(world);
    println!("== THE LANTERN OF THE FEN (authored in text) ==\n");
    println!("  {}\n", game.look());

    // The critical path, in the order the gates force it.
    let script = [
        ("take lantern", "a light against the dark stair"),
        ("go north", "into the drowned gatehouse"),
        ("go down", "down the (now lit) stair"),
        ("take brass_key", "the key in the drowned grate"),
        ("go north", "to the chapel vestibule"),
        ("ask friar about charm", "the warding charm — key first"),
        ("go east", "into the mechanism gallery"),
        ("use charm on mechanism", "the span grinds level"),
        ("go north", "out onto the iron span"),
        ("attack gargoyle", "the ward against green stone"),
        ("go north", "into the Fen-Heart sanctum"),
        ("take fen_heart", "the Fen-Heart itself"),
    ];

    for (cmd, why) in script {
        match game.command("pilgrim", cmd) {
            PlayResult::Landed {
                receipt,
                narration,
                status,
                action,
            } => {
                println!(
                    "  turn #{:>2}  {}  [{}]",
                    receipt.seq,
                    hex8(&receipt.id),
                    action.label()
                );
                println!("            {narration}  ({why})");
                if status == GameStatus::Won {
                    println!("\n  *** YOU WIN — the Fen-Heart is carried into the shrine. ***");
                }
            }
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }

    assert_eq!(
        game.status(),
        GameStatus::Won,
        "the authored dungeon must be won"
    );

    // The whole playthrough of a text-authored world re-verifies as an authentic hash chain.
    game.verify()
        .expect("every landed move is authentic, well-formed, injection-free, and on-chain");
    println!(
        "\n  verify: OK — {} moves, each a verified turn; final status: {:?}.",
        game.world().ledger.len(),
        game.status()
    );
}

fn hex8(id: &[u8; 32]) -> String {
    id[..4].iter().map(|b| format!("{b:02x}")).collect()
}
