//! mud_client_e2e.rs — THE PLAYABLE MUD CLIENT, PROVEN BY PLAYING A REAL SESSION.
//!
//! This drives the [`crate::mud_client`] engine through a full text-MUD loop against a
//! REAL HTTP node (a `boot_mud_world` in-process node + served TCP listener), proving you
//! can actually PLAY the node-hosted living world:
//!
//!   1. CONNECT + LOOK — the client reads the room/character/NPC cells off the real ledger
//!      (the character starts level 1, 0 xp, in the Entrance; the watchman calm);
//!   2. GAIN-XP — fire the `gain-xp` affordance (a signed, verified turn) → xp = 120 lands;
//!   3. MOVE — fire `move` → the character walks into the Hall (room = 2) on the ledger;
//!   4. TICK — the GM's reactive program observes the ledger and the WORLD RESPONDS: a
//!      LEVEL-UP (level 2, xp reset) + the NPC going ALERT — GM superpowers a player cannot
//!      reach;
//!   5. DESCEND — fire `descend` into the player's PERSONAL dungeon instance (a fork the GM
//!      admitted them to) → the instance's flag flips on the ledger (the player entered);
//!   6. THE ASYMMETRY (receipted refusals): `descend` into the SEALED dungeon (no cap) and a
//!      GM-only NPC write are both REFUSED by the executor's authority gate, leaving the
//!      world unchanged — while the GM's own moves over the same cells committed.
//!
//! Every accepted step carries a turn hash (a receipt). The whole session runs over the
//! genuine remote-client path (discover + signed `/turns/submit`), the same one a cockpit
//! or a thin terminal uses.
#![cfg(all(test, feature = "deos-host"))]

use crate::mud_client::{MudClient, boot_mud_world, gm_tick, run_repl};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn client_plays_the_node_hosted_mud_living_world() {
    // ── CONNECT ── boot a self-contained playable world (node + hosted GM + served port).
    let session = boot_mud_world("mud-client-test-aria")
        .await
        .expect("boot the playable MUD world");
    let client = MudClient::from_session(&session);

    // ── (1) LOOK ── the world the client reads is the REAL committed ledger state.
    let view = client.look().await.expect("look at the starting room");
    assert!(
        view.contains("the Entrance"),
        "the player starts in the Entrance; view was:\n{view}"
    );
    assert!(
        view.contains("level 1"),
        "the character starts at level 1; view was:\n{view}"
    );
    assert_eq!(
        client.room().await.expect("room"),
        1,
        "starts in the Entrance (room 1)"
    );
    assert_eq!(
        client.stats().await.expect("stats"),
        (1, 0),
        "starts level 1, 0 xp"
    );
    assert_eq!(
        client.npc_mood().await.expect("mood"),
        0,
        "the watchman starts calm"
    );

    // ── (2) GAIN-XP ── a real signed, verified turn → xp lands on the ledger.
    let gain = client.gain_xp().await.expect("fire gain-xp");
    assert!(
        gain.accepted,
        "the player's gain-xp turn was accepted; error={:?}",
        gain.error
    );
    assert!(
        gain.turn_hash.is_some(),
        "an accepted gain-xp turn carries a receipt (turn hash)"
    );
    assert_eq!(
        client.stats().await.expect("stats after gain-xp").1,
        120,
        "xp rose to 120 on the ledger"
    );

    // ── (3) MOVE ── walk into the Hall (room = 2) on the real ledger.
    let mov = client.do_move().await.expect("fire move");
    assert!(
        mov.accepted,
        "the player's move turn was accepted; error={:?}",
        mov.error
    );
    assert_eq!(
        client.room().await.expect("room after move"),
        2,
        "moved into the Hall (room 2)"
    );

    // ── (4) TICK ── the GM observes + the WORLD RESPONDS (level-up + NPC reaction).
    gm_tick(session.node_state(), client.world())
        .await
        .expect("the GM reactive tick runs");
    assert_eq!(
        client.stats().await.expect("stats after tick"),
        (2, 0),
        "the GM LEVELED the character up to 2 and reset xp (a GM superpower)"
    );
    assert_eq!(
        client.npc_mood().await.expect("mood after tick"),
        1,
        "the watchman REACTED to the player's arrival (mood ALERT)"
    );

    // ── (5) DESCEND ── enter the player's PERSONAL dungeon instance (admitted ⇒ succeeds).
    assert!(
        !client.dungeon_descended().await.expect("dungeon flag pre"),
        "the dungeon starts un-descended"
    );
    let (visible, descend) = client
        .descend()
        .await
        .expect("fire descend into the personal dungeon");
    assert!(
        visible,
        "the personal dungeon's `descend` affordance is discoverable"
    );
    assert!(
        descend.accepted,
        "descend into the ADMITTED dungeon is authorized (the GM granted the player a cap); error={:?}",
        descend.error
    );
    assert!(
        client.dungeon_descended().await.expect("dungeon flag post"),
        "the player DESCENDED — the instance's flag flipped on the real ledger"
    );

    // ── (6a) THE ASYMMETRY: descend into the SEALED dungeon (no cap) → REFUSED ───────────
    let (sealed_visible, sealed) = client
        .descend_sealed()
        .await
        .expect("attempt descend into the sealed dungeon");
    assert!(
        sealed_visible,
        "the sealed dungeon's surface is discoverable (you can SEE it)"
    );
    assert!(
        !sealed.accepted,
        "but descending the SEALED dungeon is REFUSED (no cap — fork isolation); outcome={sealed:?}"
    );

    // ── (6b) THE ASYMMETRY: a GM-only NPC write the player holds no cap over → REFUSED ───
    let mood_before = client.npc_mood().await.expect("npc mood before forge");
    let forge = client
        .forge_npc()
        .await
        .expect("attempt the forbidden NPC write");
    assert!(
        !forge.accepted,
        "a player CANNOT write the NPC (no cap held — GM-only); outcome={forge:?}"
    );
    assert_eq!(
        client.npc_mood().await.expect("npc mood after forge"),
        mood_before,
        "the refused forge left the NPC's mood unchanged on the ledger"
    );
}

/// THE RICHER WORLD — exploration, items-as-caps, and speech, all as verified turns.
///
/// This proves the deepened playable loop on the same node-hosted living world:
///
///   1. EXPLORE — `go` walks the exit graph (Entrance → Hall → Tower → Hall → Cellar),
///      each step a signed turn writing the character's ROOM field on the real ledger;
///   2. ITEMS-AS-CAPS — in the Hall a torch lies on the ground. `take torch` flips the
///      item's HELD flag (a verified turn) BECAUSE the GM granted the player a cap over the
///      torch-cell — holding the cap IS being able to take it. `inventory` reflects it;
///   3. THE LOCKED ITEM (the refusal) — a sealed chest also lies in the Hall, but the player
///      was NEVER granted a cap over it: `take chest` is REFUSED by the executor's authority
///      gate, and the chest stays un-held — the locked-door property, as an item;
///   4. DROP — setting the torch down is a verified turn that returns it to the room;
///   5. SAY — speech is a receipted turn bumping the character's utterance counter.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn client_explores_rooms_takes_items_and_speaks() {
    let session = boot_mud_world("mud-client-explore-aria")
        .await
        .expect("boot the playable MUD world");
    let client = MudClient::from_session(&session);

    // ── (0) start in the Entrance, carrying nothing ──────────────────────────────────
    assert_eq!(
        client.room().await.expect("room"),
        1,
        "start in the Entrance"
    );
    assert!(
        client.inventory().await.expect("inv").is_empty(),
        "the player starts empty-handed"
    );

    // ── (1) EXPLORE — walk the exit graph, each step a verified ROOM-write turn ────────
    let (dest, mov) = client
        .go("north")
        .await
        .expect("go north")
        .expect("there is a north exit from the Entrance");
    assert!(
        mov.accepted,
        "the move turn committed; error={:?}",
        mov.error
    );
    assert_eq!(dest, 2, "north from the Entrance reaches the Hall");
    assert_eq!(
        client.room().await.unwrap(),
        2,
        "now in the Hall on the ledger"
    );

    // a bad exit fires NO turn (there is no west exit from the Hall).
    assert!(
        client.go("west").await.expect("go west").is_none(),
        "there is no west exit — no turn is fired"
    );

    // up into the Tower, then back down to the Hall.
    let (tower, up) = client.go("up").await.expect("go up").expect("up exit");
    assert!(up.accepted, "the up move committed");
    assert_eq!(tower, 3, "up from the Hall reaches the Tower");
    assert_eq!(client.room().await.unwrap(), 3, "in the Tower");
    let (back, down) = client
        .go("down")
        .await
        .expect("go down")
        .expect("down exit");
    assert!(down.accepted && back == 2, "down returns to the Hall");

    // ── (2) ITEMS-AS-CAPS — the torch is takeable because the GM granted its cap ──────
    assert!(
        !client.holds("torch").await.expect("holds torch pre"),
        "the torch starts on the ground, not held"
    );
    let take = client
        .take_item("torch")
        .await
        .expect("take torch")
        .expect("the torch is here in the Hall");
    assert!(
        take.accepted,
        "taking the torch is AUTHORIZED (the player holds the torch's cap); error={:?}",
        take.error
    );
    assert!(take.turn_hash.is_some(), "the take left a receipt");
    assert!(
        client.holds("torch").await.expect("holds torch post"),
        "the torch is now held (HELD flag flipped on the ledger)"
    );
    assert_eq!(
        client.inventory().await.expect("inv after take"),
        vec!["torch".to_string()],
        "the inventory reflects the held torch"
    );

    // ── (3) THE LOCKED ITEM — the sealed chest has no cap granted: take is REFUSED ─────
    let take_chest = client
        .take_item("chest")
        .await
        .expect("attempt take chest")
        .expect("the chest is here in the Hall");
    assert!(
        !take_chest.accepted,
        "taking the LOCKED chest is REFUSED (no cap held — the locked-door property); outcome={take_chest:?}"
    );
    assert!(
        !client.holds("chest").await.expect("holds chest post"),
        "the refused take left the chest un-held on the ledger"
    );

    // ── (4) DROP — set the torch down (a verified turn returning it to the room) ───────
    let drop = client
        .drop_item("torch")
        .await
        .expect("drop torch")
        .expect("the torch is carried");
    assert!(drop.accepted, "the drop committed; error={:?}", drop.error);
    assert!(
        !client.holds("torch").await.expect("holds torch after drop"),
        "the torch is no longer held after dropping it"
    );
    assert!(
        client.inventory().await.expect("inv after drop").is_empty(),
        "the inventory is empty again"
    );

    // ── (5) SAY — speech is a receipted turn ──────────────────────────────────────────
    let say = client.say().await.expect("say");
    assert!(
        say.accepted,
        "the say turn committed; error={:?}",
        say.error
    );
    let view = client.look().await.expect("look after speaking");
    assert!(
        view.contains("spoken 1"),
        "the utterance counter advanced on the ledger; view was:\n{view}"
    );
}

/// A FULL PLAYABLE SESSION, driven through the actual REPL — the same `run_repl` a terminal
/// player drives — over scripted input, capturing the narration as a transcript artifact.
/// Run with `--nocapture` to read the played session. This proves the end-to-end command
/// surface (parse → fire verified turn → re-read ledger → narrate) wires together.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn repl_plays_a_full_scripted_session() {
    let session = boot_mud_world("mud-client-repl-aria")
        .await
        .expect("boot the playable MUD world");

    // A scripted play-through: look, walk to the Hall, take the torch, try the locked chest,
    // explore the Tower, speak, check inventory, then leave.
    let script = "\
look
go north
take torch
inventory
take chest
go up
look
go down
say hello, world
inventory
drop torch
quit
";
    let mut out: Vec<u8> = Vec::new();
    run_repl(&session, std::io::Cursor::new(script.as_bytes()), &mut out)
        .await
        .expect("the REPL plays the scripted session");
    let transcript = String::from_utf8_lossy(&out);

    // Print the full transcript (visible under `--nocapture`) — the playable artifact.
    println!(
        "\n========== DREGG-MUD REPL TRANSCRIPT ==========\n{transcript}\n==============================================="
    );

    // The transcript witnesses the load-bearing beats of the session.
    assert!(
        transcript.contains("the Entrance"),
        "looked at the start room"
    );
    assert!(
        transcript.contains("into the Hall"),
        "walked north into the Hall"
    );
    assert!(
        transcript.contains("You take the torch"),
        "took the torch (an authorized item-cap turn)"
    );
    assert!(
        transcript.contains("You carry: torch"),
        "the inventory shows the torch"
    );
    assert!(
        transcript.contains("REFUSES you") || transcript.contains("locked"),
        "the locked chest take was refused; transcript:\n{transcript}"
    );
    assert!(transcript.contains("the Tower"), "explored the Tower");
    assert!(
        transcript.contains("You say, \"hello, world\""),
        "spoke in the room"
    );
    assert!(
        transcript.contains("You set down the torch"),
        "dropped the torch"
    );
    assert!(transcript.contains("Farewell"), "left the world cleanly");
}
