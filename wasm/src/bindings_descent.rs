//! **THE DESCENT, played IN THE BROWSER TAB** — the daily, provably-fair, permadeath
//! procgen roguelite ([`dreggnet_offerings::daily_descent`]) running on the wasm-clean
//! in-tab executor. The moves never leave the device: play is private + fast, exactly the
//! way [`StoryWorld`](crate::bindings_story::StoryWorld) runs `spween-dregg`'s CYOA.
//!
//! [`DescentWorld`] is the action sibling of [`StoryWorld`]. Where the story surface runs a
//! browser-supplied `.scene`, the descent surface draws TODAY'S beacon-seeded world from
//! [`daily_scene`](dreggnet_offerings::daily_descent::daily_scene) — the *same* generator the
//! [`DailyDescentOffering`](dreggnet_offerings::daily_descent::DailyDescentOffering) and the
//! no-cheat leaderboard deploy, so the world played here is byte-identical to the one a
//! stranger re-executes. It then rides `spween-dregg`'s real
//! [`Driver`](spween_dregg::Driver)/[`WorldCell`](spween_dregg::WorldCell): each move is ONE
//! cap-gated verified turn the real [`EmbeddedExecutor`] admits IFF the scene's installed gate
//! passes, and the run is an un-retconnable receipt chain a stranger can replay
//! ([`Self::verify`]).
//!
//! ## What is real here (in-tab, private)
//!
//! - **Today's beacon-seeded world.** [`DescentWorld::from_beacon`] takes a fetched drand
//!   `quicknet` `(round, signature)` and VERIFIES it (the real BLS pairing check via
//!   [`procgen_dregg::beacon::DailyBeacon`]) before it will open a day — a forged reveal opens
//!   NO world (fail-closed, in-tab). [`DescentWorld::new`] takes an already-verified beacon
//!   output (the committed epoch value the day's seed folds from), the honest split the beacon
//!   module documents (the pairing verifier is a pure function of public data; *fetching* the
//!   round is the browser's client seam).
//! - **Permadeath, on the real executor.** The day's world is a stakes-forward trial: an HP
//!   floor (`{ hp >= 16 }`) means a blow you could not survive is REFUSED, and a reckless line
//!   strands you into a real committed DEFEAT passage (`downed -> END`). A run can be genuinely
//!   LOST — [`Self::is_dead`] reads the committed `downed` flag.
//! - **The run state + replay.** Depth / hp / warden-hp / gold, alive-vs-dead, and won are read
//!   straight off the committed cell; [`Self::verify`] re-drives a fresh, identically-seeded
//!   world through the recorded moves and confirms the exact committed state chain reproduces.
//!
//! ## Honest scope — what this leg is NOT
//!
//! This is the **play-private-and-fast leg**: the whole run executes and re-verifies in the tab.
//! Layered ABOVE it, and NOT built here, are:
//! - the JS/UI layer that calls this binding (the `<dregg-descent>` element is a separate piece);
//! - the persistent, cross-day hardcore CHARACTER + the no-cheat LEADERBOARD ranking + the
//!   opt-in node SETTLE — those live on [`DailyDescentOffering`](dreggnet_offerings::daily_descent::DailyDescentOffering)
//!   / [`ugc_dregg`], the "publish a verified run" leg, not the private in-tab play leg here;
//! - the on-device succinct PROOF generation (the ZK-leaderboard lane) — replay-verify here is
//!   re-execution, not a SNARK.
//!
//! ## PLATFORM NOTE — this is in the shipped wasm32 bundle
//!
//! Like [`StoryWorld`], `DescentWorld` rides `dregg-app-framework`'s wasm-clean CORE
//! (`default-features = false`, dropping the non-wasm32 `server` feature). `dreggnet-offerings`
//! (for `daily_scene`) and `procgen-dregg` (for the beacon → daily-seed wire) compile to wasm32
//! the same way; no target gate — this module is in the shipped bundle AND the native
//! `cargo test`.

use wasm_bindgen::prelude::*;

use dreggnet_offerings::daily_descent::{DAILY_DEPLOY_SEED, DailyDescent, HOARD_GOLD, daily_scene};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;
use procgen_dregg::daily_seed;
use spween_dregg::{Driver, Scene, WorldCell, parse, verify};

/// The synthetic filename today's beacon-drawn `.scene` source is parsed under (feeds only the
/// scene id / error spans — the generated source string is authoritative and byte-identical to
/// the one the offering / leaderboard deploy).
const DESCENT_FILENAME: &str = "daily-descent.scene";

/// The committed narrative var the fall-to-defeat move sets (`~ downed = 1`) as it routes into
/// the terminal defeat passage — the in-tab permadeath signal ([`DescentWorld::is_dead`]).
const DOWNED_VAR: &str = "downed";

/// **Today's Descent, running as verifiable turns in the tab.** Owns the beacon-drawn day's
/// [`Scene`] + a `spween-dregg` [`Driver`] at `NodeTarget::Local` (in-process, NO networking).
/// Each [`Self::advance`] runs the stock gate-checked `select_choice` and flushes the resulting
/// cell writes as ONE cap-gated verified turn, appending its receipt; [`Self::verify`] replays
/// that chain against a fresh, identically-seeded day — the "stranger checks the run" tooth.
#[wasm_bindgen]
pub struct DescentWorld {
    /// The beacon-drawn day spec (title / warden HP / depth / committed seed). Kept for the
    /// metadata getters; the `source` inside it is what `scene` was compiled from.
    day: DailyDescent,
    /// The compiled day's scene, LEAKED to `'static` (a `Driver<'s>` borrows the `Scene` for its
    /// runtime and a `#[wasm_bindgen]` struct cannot be self-referential). A `DescentWorld` lives
    /// for the page's lifetime, so one small per-run leak is the honest cost of the borrow. The
    /// same `&'static Scene` re-deploys the fresh world [`Self::verify`] replays.
    scene: &'static Scene,
    /// The stock-runtime driver over the day's world-cell; each `advance` is a verified turn.
    driver: Driver<'static>,
}

#[wasm_bindgen]
impl DescentWorld {
    /// **Open TODAY'S descent from an already-verified beacon output.** `epoch_hex` is the
    /// 32-byte hex committed epoch value (a verified drand round's output — `H(signature)`); the
    /// day's seed is [`daily_seed`] of it, and the day's world is [`daily_scene`] of the seed.
    /// The genesis turn (the gate's entry effects: `hp = 50`, `warden_hp = <beacon draw>`)
    /// commits before any move. FAIL-CLOSED: bad hex / wrong length / a scene that will not
    /// deploy is a `JsError` and NO world is minted.
    ///
    /// Use this when the browser fetched + verified the drand round elsewhere (the pairing check
    /// is a pure function of public data) and holds only the committed output. For the in-tab
    /// verify-the-reveal path, use [`Self::from_beacon`].
    #[wasm_bindgen(constructor)]
    pub fn new(epoch_hex: String) -> Result<DescentWorld, JsError> {
        Self::try_new(&epoch_hex).map_err(|e| JsError::new(&e))
    }

    /// The fallible core of [`Self::new`] — `String` errors, wasm-bindgen-free, so the
    /// fail-closed path is testable NATIVELY (constructing a `JsError` panics off-wasm).
    fn try_new(epoch_hex: &str) -> Result<DescentWorld, String> {
        let output = decode_hex_32(epoch_hex)?;
        Self::try_from_seed(daily_seed(&output))
    }

    /// **Open TODAY'S descent by VERIFYING a fetched drand `quicknet` reveal, in the tab.**
    /// `round` + `signature_hex` are the day's fetched `(round, signature)`; this builds the real
    /// [`DailyBeacon`], runs the BLS pairing check against the pinned `quicknet` group key
    /// (`DailyBeacon::seed` verifies before deriving), folds the verified output through
    /// [`daily_seed`], and draws the day. FAIL-CLOSED: a forged / mutated signature, a wrong
    /// round, or a wrong group key does not verify → a `JsError` and NO world (you cannot open a
    /// forged day, and cannot grind a favourable one). This is the "unpredictable-until-revealed"
    /// tooth carried to the browser.
    #[wasm_bindgen(js_name = fromBeacon)]
    pub fn from_beacon(round: u64, signature_hex: String) -> Result<DescentWorld, JsError> {
        Self::try_from_beacon(round, &signature_hex).map_err(|e| JsError::new(&e))
    }

    /// The fallible core of [`Self::from_beacon`] — `String` errors, natively testable.
    fn try_from_beacon(round: u64, signature_hex: &str) -> Result<DescentWorld, String> {
        let signature = decode_hex_vec(signature_hex)?;
        let beacon = DailyBeacon::quicknet(round, signature);
        // `seed()` runs the pairing check FIRST; a beacon that does not verify yields no seed.
        let seed = beacon
            .seed()
            .map_err(|e| format!("beacon did not verify: {e:?}"))?;
        Self::try_from_seed(seed)
    }

    /// Draw + deploy the day the committed `seed` names, and drive its genesis turn. Shared by
    /// both constructors (the beacon-output path and the verify-the-reveal path).
    fn try_from_seed(seed: CommittedSeed) -> Result<DescentWorld, String> {
        let day = daily_scene(&seed);
        let scene = parse(&day.source, DESCENT_FILENAME).map_err(|e| e.to_string())?;
        // Leak the scene to `'static` so the borrowing `Driver` can be owned by this struct.
        let scene: &'static Scene = Box::leak(Box::new(scene));

        let world = WorldCell::deploy(scene, DAILY_DEPLOY_SEED).map_err(|e| e.to_string())?;
        let driver = Driver::start(world, scene).map_err(|e| e.to_string())?;

        Ok(DescentWorld { day, scene, driver })
    }

    // ── The day's identity (metadata the UI renders around the run) ──────────────────────────

    /// The day's display title (the beacon-drawn theme's title, e.g. "The Sunken Descent").
    pub fn title(&self) -> String {
        self.day.title.clone()
    }

    /// The warden's starting HP for the day (a beacon draw; 60 demands the field-dressing to win).
    #[wasm_bindgen(js_name = wardenStartHp)]
    pub fn warden_start_hp(&self) -> u64 {
        self.day.warden_hp
    }

    /// The number of connecting corridor rooms between the key room and the hoard gate (a beacon
    /// draw — the day's depth).
    #[wasm_bindgen(js_name = deepeningRooms)]
    pub fn deepening_rooms(&self) -> usize {
        self.day.deepening_rooms
    }

    /// The committed daily seed this world was drawn from (hex) — the day's fingerprint. Everyone
    /// who derives the same seed regenerates this byte-identical world.
    #[wasm_bindgen(js_name = seedHex)]
    pub fn seed_hex(&self) -> String {
        crate::bindings::hex_encode(self.day.seed.as_bytes())
    }

    // ── The room + the moves (what to render) ────────────────────────────────────────────────

    /// The current room ("passage") name — `gate` at the start, `downed` in the defeat room,
    /// empty once the run has ended.
    #[wasm_bindgen(js_name = currentRoom)]
    pub fn current_room(&self) -> String {
        self.driver.current_passage().unwrap_or_default()
    }

    /// The current room's narrative prose — the text to render. Empty once the run has ended.
    #[wasm_bindgen(js_name = roomProse)]
    pub fn room_prose(&self) -> String {
        self.driver.prose().unwrap_or_default()
    }

    /// The moves at the current room as JSON: `[{index, text, available}]`. `available` is the
    /// condition-gated availability the stock runtime computes against the committed cell state
    /// (e.g. "Press past the felled warden" is unavailable while `warden_hp > 0`; "Fall to the
    /// warden's blow" only becomes available at `hp <= 20`). The UI renders an unavailable move
    /// disabled; an [`Self::advance`] on it is refused in-band regardless (fail-closed at the
    /// turn — the executor is the sole referee).
    #[wasm_bindgen(js_name = movesJson)]
    pub fn moves_json(&self) -> String {
        use serde_json::json;
        let rows: Vec<serde_json::Value> = self
            .driver
            .choices()
            .into_iter()
            .map(|c| {
                json!({
                    "index": c.index,
                    "text": c.text,
                    "available": c.available,
                })
            })
            .collect();
        json!(rows).to_string()
    }

    // ── Advance one move = one verified turn ─────────────────────────────────────────────────

    /// **Advance the run by taking move `index` — as ONE verified turn.** Runs the stock
    /// `select_choice` (checks the gate, runs the effects, navigates) and flushes the buffered
    /// cell writes as a single cap-gated turn, appending its receipt.
    ///
    /// Returns the full [`Self::state_json`] object with `ok` set, plus `error?` on a refusal.
    /// FAIL-CLOSED: a gated (condition-not-met) or out-of-range move — or a move on an already-
    /// ended run — returns `{ ok: false, error }` and NOTHING commits (the state fields still
    /// describe the last good, committed state). A blow you could not survive, or pressing past a
    /// warden still standing, is refused here — this is the permadeath trial's teeth biting.
    pub fn advance(&mut self, index: usize) -> String {
        use serde_json::json;
        match self.driver.advance(index) {
            Ok(_step) => {
                let mut v = self.state_value();
                v["ok"] = json!(true);
                v.to_string()
            }
            Err(e) => {
                let mut v = self.state_value();
                v["ok"] = json!(false);
                v["error"] = json!(e.to_string());
                v.to_string()
            }
        }
    }

    // ── Read the run state ───────────────────────────────────────────────────────────────────

    /// The run's current committed state as JSON:
    /// `{ room, hp, wardenHp, depth, gold, downed, alive, dead, won, ended, turns, commitmentHex }`.
    /// Every field reads straight off the committed day-cell — the same values a re-executor
    /// reproduces.
    #[wasm_bindgen(js_name = stateJson)]
    pub fn state_json(&self) -> String {
        self.state_value().to_string()
    }

    /// The state object (shared by [`Self::state_json`] and [`Self::advance`]).
    fn state_value(&self) -> serde_json::Value {
        serde_json::json!({
            "room": self.current_room(),
            "hp": self.hp(),
            "wardenHp": self.warden_hp(),
            "depth": self.depth(),
            "gold": self.gold(),
            "downed": self.read_var(DOWNED_VAR),
            "alive": !self.is_dead(),
            "dead": self.is_dead(),
            "won": self.is_won(),
            "ended": self.is_ended(),
            "turns": self.turns(),
            "commitmentHex": self.commitment_hex(),
        })
    }

    /// Read a committed narrative var off the day's cell (`hp` / `warden_hp` / `depth` / `gold` /
    /// `downed` / `heals_used` / …). Unset compiled vars read `0`, as the executor sees them.
    #[wasm_bindgen(js_name = readVar)]
    pub fn read_var(&self, name: &str) -> u64 {
        self.driver.world().read_var(name)
    }

    /// The player's current HP (the committed `hp` slot). A blow that would drop it below the
    /// floor is refused by the gate at [`Self::advance`].
    pub fn hp(&self) -> u64 {
        self.read_var("hp")
    }

    /// The warden's current HP (the committed `warden_hp` slot). The stair opens only once it
    /// reaches `0` (the `{ warden_hp <= 0 }`-gated "press past" move).
    #[wasm_bindgen(js_name = wardenHp)]
    pub fn warden_hp(&self) -> u64 {
        self.read_var("warden_hp")
    }

    /// How deep the run has reached (the committed `depth` counter — the survived-depth signal).
    pub fn depth(&self) -> u64 {
        self.read_var("depth")
    }

    /// The gold carried (the committed `gold` slot). Reaching the hoard sets it to
    /// [`HOARD_GOLD`] — the win value.
    pub fn gold(&self) -> u64 {
        self.read_var("gold")
    }

    /// Whether the run has ended (won at the hoard, lost in the defeat room, or turned back at
    /// the door).
    #[wasm_bindgen(js_name = isEnded)]
    pub fn is_ended(&self) -> bool {
        self.driver.is_ended()
    }

    /// **Whether the run reached the WIN** — ended holding the hoard (`gold == HOARD_GOLD`). This
    /// is exactly the leaderboard's win condition, read locally.
    #[wasm_bindgen(js_name = isWon)]
    pub fn is_won(&self) -> bool {
        self.is_ended() && self.gold() == HOARD_GOLD
    }

    /// **Whether the run fell to the warden** — the committed `downed` flag is set (the
    /// fall-to-defeat move routed into the terminal defeat passage). This is the in-tab
    /// permadeath signal: a genuinely lost run. (The cross-day hardcore-character death that
    /// PERSISTS is the offering/store leg, not this private-play leg.)
    #[wasm_bindgen(js_name = isDead)]
    pub fn is_dead(&self) -> bool {
        self.read_var(DOWNED_VAR) == 1
    }

    /// The number of real verified turns so far (the genesis turn plus one per committed move) —
    /// the audit-tape length. Proves each advance was a real verified turn, not a local poke.
    pub fn turns(&self) -> usize {
        // genesis (1, once started) + one per committed choice-step.
        let genesis = usize::from(self.driver.genesis().is_some());
        genesis + self.driver.steps().len()
    }

    /// The day-cell's current committed state commitment (hex) — the `post_state_hash` of the
    /// last committed turn (genesis if no move has been taken yet). It MOVES on every advance and
    /// pins exactly one committed history — the stranger's check surface.
    #[wasm_bindgen(js_name = commitmentHex)]
    pub fn commitment_hex(&self) -> String {
        let last = self
            .driver
            .steps()
            .last()
            .map(|s| &s.receipt)
            .or_else(|| self.driver.genesis());
        match last {
            Some(r) => crate::bindings::hex_encode(&r.post_state_hash),
            None => String::new(),
        }
    }

    /// **Verify the whole run by replay** — the un-retconnable "stranger checks the run" check.
    /// Re-drives a FRESH, identically-seeded day through the recorded move sequence and confirms
    /// it reproduces the exact committed state at every step, AND that the receipt chain links
    /// cleanly (`spween-dregg`'s `verify` — both teeth). A forged (ineligible) move is refused by
    /// the executor on replay; a tampered receipt breaks the chain. Both a WON run and a LOST run
    /// (downed into the defeat passage) are honest records that re-verify here. Returns `true`
    /// iff the run is authentic.
    pub fn verify(&self) -> bool {
        let Ok(fresh) = WorldCell::deploy(self.scene, DAILY_DEPLOY_SEED) else {
            return false;
        };
        verify(fresh, self.scene, &self.driver.playthrough()).is_ok()
    }
}

/// Decode a 32-byte value from hex (a beacon output / committed epoch value). Fail-closed on bad
/// hex or wrong length — no half-decoded seed.
fn decode_hex_32(hex: &str) -> Result<[u8; 32], String> {
    let bytes = decode_hex_vec(hex)?;
    bytes
        .try_into()
        .map_err(|_| "expected exactly 32 bytes (64 hex chars)".to_string())
}

/// Decode a byte vector from hex (a drand signature / a beacon output). Accepts an optional `0x`
/// prefix; rejects odd length / non-hex digits (fail-closed).
fn decode_hex_vec(hex: &str) -> Result<Vec<u8>, String> {
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    if hex.len() % 2 != 0 {
        return Err("hex string has an odd number of digits".to_string());
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use dreggnet_offerings::daily_descent::{
        CORRIDOR_ON, GATE_FALL, GATE_HEAL, GATE_MEASURED, GATE_PRESS, GATE_RECKLESS, HOARD_FORCE,
        HOARD_SEIZE, KEY_TAKE,
    };

    // A REAL, PUBLISHED drand `quicknet` round (round 1_000_000) — the same vector `dregg-dice`'s
    // interop test and the daily-descent driven test pin. Here it is "today's beacon".
    const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
    const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

    /// A deterministic (test-fixture) epoch commitment — stands in for an already-verified beacon
    /// output, so the in-tab win/die loop is reproducible without a network fetch.
    fn fixture_epoch_hex() -> String {
        crate::bindings::hex_encode(&[0x11u8; 32])
    }

    /// Parse the state JSON `advance` / `state_json` return.
    fn state(json: &str) -> serde_json::Value {
        serde_json::from_str(json).expect("state is JSON")
    }

    /// Drive a CAREFUL winning line to the hoard (mirrors the offering's `drive_win`, but through
    /// the in-tab `DescentWorld` surface): fight the warden down (healing once if the beacon drew a
    /// tough warden), press past, take the key, walk the corridors, force the door, seize the
    /// hoard. Works for any beacon-drawn warden HP / depth. Every move must LAND (ok == true).
    fn drive_win(run: &mut DescentWorld) {
        for _ in 0..64 {
            let room = run.current_room();
            if room.is_empty() {
                break;
            }
            let ci = match room.as_str() {
                "gate" => {
                    if run.warden_hp() == 0 {
                        GATE_PRESS
                    } else if run.hp() >= 16 {
                        GATE_MEASURED
                    } else {
                        GATE_HEAL
                    }
                }
                "keyroom" => KEY_TAKE,
                "hoardgate" => HOARD_FORCE,
                "hoard" => HOARD_SEIZE,
                r if r.starts_with("corridor") => CORRIDOR_ON,
                other => panic!("unexpected room in a winning line: {other}"),
            };
            let out = state(&run.advance(ci));
            assert_eq!(out["ok"], serde_json::json!(true), "move refused in {room}");
        }
    }

    /// THE DESCENT LOOP, IN-TAB: open today's beacon-seeded day, play a CAREFUL run to the hoard
    /// (each move a verified turn, the receipt tape growing), read the run WON, and replay-verify.
    #[test]
    fn a_careful_run_is_won_in_tab_and_reverifies() {
        let mut run = DescentWorld::new(fixture_epoch_hex()).expect("today's day opens");

        // Genesis committed before any move: one receipt, we stand at the warden's gate at full HP.
        assert_eq!(run.current_room(), "gate");
        assert_eq!(run.turns(), 1, "the genesis turn is committed");
        assert_eq!(run.hp(), 50, "the gate's entry effect set hp = 50");
        assert!(
            run.warden_hp() >= 45,
            "the warden stands at its beacon-drawn HP"
        );
        assert!(!run.room_prose().is_empty(), "the gate renders prose");
        assert!(!run.commitment_hex().is_empty());
        assert!(
            !run.is_dead() && !run.is_won() && !run.is_ended(),
            "alive, mid-run"
        );

        // The gate's moves + their gate-computed availability.
        let moves = state(&run.moves_json());
        let moves = moves.as_array().expect("a move array");
        assert_eq!(moves[GATE_MEASURED]["available"], serde_json::json!(true));
        assert_eq!(moves[GATE_RECKLESS]["available"], serde_json::json!(true));
        assert_eq!(
            moves[GATE_PRESS]["available"],
            serde_json::json!(false),
            "cannot press past a warden still standing"
        );
        assert_eq!(
            moves[GATE_FALL]["available"],
            serde_json::json!(false),
            "cannot fall while hp is high"
        );

        // Play the careful winning line.
        drive_win(&mut run);

        let st = state(&run.state_json());
        assert_eq!(
            st["won"],
            serde_json::json!(true),
            "reached the hoard — a win"
        );
        assert_eq!(
            st["gold"],
            serde_json::json!(HOARD_GOLD),
            "the hoard is seized"
        );
        assert_eq!(
            st["dead"],
            serde_json::json!(false),
            "a winner did not perish"
        );
        assert_eq!(st["ended"], serde_json::json!(true));
        assert!(run.depth() > 0, "the run pressed deeper");
        assert!(run.turns() > 1, "real verified turns accrued");

        // THE STRANGER CHECK: the honest in-tab win replays true against a fresh day.
        assert!(run.verify(), "the won run re-verifies by replay");
    }

    /// A run can be genuinely LOST in-tab: a reckless opener burns HP to the brink, then falling
    /// to the warden routes into the committed DEFEAT passage. The lost run is still an honest,
    /// replay-verifiable record (it just never reached the hoard).
    #[test]
    fn a_reckless_run_dies_in_tab_and_the_loss_reverifies() {
        let mut run = DescentWorld::new(fixture_epoch_hex()).expect("today's day opens");
        assert!(!run.is_dead(), "alive at the start");

        // A reckless all-out blow: hp 50 → 20 (the warden still stands).
        let reckless = state(&run.advance(GATE_RECKLESS));
        assert_eq!(
            reckless["ok"],
            serde_json::json!(true),
            "the reckless opener commits"
        );
        assert!(run.hp() <= 20, "at the brink: hp = {}", run.hp());
        assert!(run.warden_hp() > 0, "the warden still stands");

        // Now the fall-to-defeat move is AVAILABLE (its gate is `{ hp <= 20 }`).
        let moves = state(&run.moves_json());
        assert_eq!(
            moves.as_array().unwrap()[GATE_FALL]["available"],
            serde_json::json!(true),
            "at the brink, the fall is on the ballot"
        );

        // Fall into the terminal defeat passage — a real committed loss.
        let fell = state(&run.advance(GATE_FALL));
        assert_eq!(fell["ok"], serde_json::json!(true), "the fall commits");
        assert_eq!(run.current_room(), "downed", "routed into the defeat room");
        assert!(
            run.is_dead(),
            "the downed flag is set — a genuine permadeath loss"
        );

        // Close the defeat passage.
        let closed = state(&run.advance(0));
        assert_eq!(
            closed["ok"],
            serde_json::json!(true),
            "the defeat passage ends"
        );
        assert!(run.is_ended(), "the run is over — lost");
        assert!(!run.is_won(), "a lost run did not reach the hoard");
        assert_eq!(run.gold(), 0, "no hoard for a lost run");

        // The LOST run is an honest, replay-verifiable record.
        assert!(run.verify(), "the lost run re-verifies by replay");
    }

    /// FAIL-CLOSED at the turn: an ineligible move (press past a warden still standing) is refused
    /// in-band — NOTHING commits, the run does not move, the receipt tape does not grow.
    #[test]
    fn a_gated_move_is_refused_and_nothing_commits() {
        let mut run = DescentWorld::new(fixture_epoch_hex()).expect("open");
        assert_eq!(run.current_room(), "gate");
        let turns_before = run.turns();

        let refused = state(&run.advance(GATE_PRESS)); // gated `{ warden_hp <= 0 }`, warden is alive
        assert_eq!(
            refused["ok"],
            serde_json::json!(false),
            "the gated move is refused"
        );
        assert!(refused.get("error").is_some(), "the refusal carries a why");
        assert_eq!(
            run.current_room(),
            "gate",
            "still at the gate; nothing moved"
        );
        assert_eq!(
            run.turns(),
            turns_before,
            "no turn committed on a refused move"
        );
    }

    /// THE BEACON TOOTH, IN-TAB: a REAL published drand `quicknet` reveal VERIFIES and opens the
    /// day (the BLS pairing check runs in the tab); a FORGED reveal (one flipped signature bit)
    /// opens NO world — you cannot open a forged day, nor grind a favourable one.
    #[test]
    fn a_real_beacon_opens_a_day_and_a_forged_reveal_is_refused() {
        // The honest reveal verifies and opens today's day.
        let run =
            DescentWorld::from_beacon(DRAND_QUICKNET_ROUND, DRAND_QUICKNET_SIG_HEX.to_string())
                .expect("a real drand reveal opens the day");
        assert_eq!(
            run.current_room(),
            "gate",
            "the verified day deploys at the gate"
        );
        assert!(!run.title().is_empty(), "the day has a beacon-drawn title");

        // A forged reveal (flip the first signature byte) fails the pairing check → NO world.
        let mut sig = decode_hex_vec(DRAND_QUICKNET_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged_hex = crate::bindings::hex_encode(&sig);
        let forged = DescentWorld::try_from_beacon(DRAND_QUICKNET_ROUND, &forged_hex);
        assert!(
            forged.is_err(),
            "a forged reveal opens no day (fail-closed)"
        );
    }

    /// Same beacon output ⇒ byte-identical world (the day is a pure function of the committed
    /// seed): the two runs draw the same title / warden HP / depth / seed.
    #[test]
    fn the_day_is_a_pure_function_of_the_beacon_output() {
        let a = DescentWorld::new(fixture_epoch_hex()).expect("a");
        let b = DescentWorld::new(fixture_epoch_hex()).expect("b");
        assert_eq!(a.title(), b.title());
        assert_eq!(a.warden_start_hp(), b.warden_start_hp());
        assert_eq!(a.deepening_rooms(), b.deepening_rooms());
        assert_eq!(a.seed_hex(), b.seed_hex());
    }

    /// A bad epoch hex FAILS CLOSED — no `DescentWorld` is minted from a malformed committed value.
    #[test]
    fn bad_epoch_hex_is_fail_closed() {
        assert!(
            DescentWorld::try_new("not hex").is_err(),
            "non-hex is refused"
        );
        assert!(
            DescentWorld::try_new("abcd").is_err(),
            "wrong length is refused"
        );
    }
}
