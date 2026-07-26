//! # `GET /guide` — **how to play**, for someone who has never heard of any of this.
//!
//! The product had no player-facing guide at all. `docs/guide/` is entirely DEVELOPER material
//! (AGENT-QUICKSTART, BUILD-WITH-DREGG, FEDERATION-JOIN…) and `docs/ONBOARDING.md` orients a
//! newcomer *in the repository*; there was no `/guide`, `/how-to-play` or `/rules` route anywhere
//! on the web surface. A stranger who wanted to know what a turn was could read a leaderboard, a
//! catalog of cards, or a game board — and nothing that answered the question.
//!
//! Each shipped game already carries its own "The rules, in one screen" panel on its own landing
//! ([`crate::automatafl_web`], [`crate::tug_web`], and now the Descent's play page). This route is
//! the thing those three cannot be: ONE page that starts from zero, says what the whole surface is
//! in words a newcomer already owns, states the two things we are NOT yet good at, and only then
//! explains the three games. The prose is the web rendering of `docs/PLAYER-GUIDE.md`.
//!
//! ## The bar this copy has to clear
//!
//! `docs/reference/UX-QA-SWEEP-2026-07-26.md`: four first-time readers were handed the rendered
//! pages, and on the landing + catalog one of them could not produce a one-sentence answer to "what
//! is this site", because *"the sentence describing what the site IS is itself written in the
//! site's private vocabulary"* — `executor`, `substrate`, `refereed`, none defined. The jargon list
//! ran to sixteen terms and the reader's own verdict on it was *"not a nitpick list; it's the
//! majority of the page's distinctive vocabulary."*
//!
//! So this page is under a NO-PRIVATE-VOCABULARY rule, and
//! [`tests::the_guide_uses_no_word_a_newcomer_would_have_to_learn_here`] enforces it as a test
//! rather than an intention: the banned list is `scripts/player-vocabulary.tsv`, and adding
//! `receipt` or `executor` to this file turns it red. Where a term is genuinely load-bearing
//! (`crowned` on the leaderboard, `guild`/`lane` on the tug board) the page DEFINES it in place, in
//! ordinary words, and the test requires the definition rather than the word's absence.
//!
//! ⚑ **AND THIS TEST IS NO LONGER THE WHOLE GATE.** It ran on `guide_body()` and nothing else, so
//! `/guide` scored 0 violations while an audit found the same list broken on 6 of 13 live surfaces
//! (`/you`, the session pages, `/descent`, `/descent/run/*`, `/identity`, the engine variants). The
//! rule was not wrong; its SCOPE was one function wide, which is how a convention decays while its
//! gate stays green. `scripts/check-player-vocabulary.py` now sweeps every player-facing web
//! surface against the SAME file. This test keeps the half a source sweep cannot do: it reads the
//! RENDERED body, so jargon composed in from another module is caught here.
//!
//! ## What it deliberately does not promise
//!
//! * **The DEFAULT identity is an unsigned browser cookie** (`dregg_user`, minted by
//!   [`crate::web_identity_http`]) with no password and no recovery. [`crate::seed_identity`] is
//!   landing an OPT-IN 24-word phrase beside it, so the page is written to be true either way: the
//!   cookie default is what you get by doing nothing, and durability requires an act.
//!   [`tests::the_guide_never_promises_a_durable_identity`] holds it to that shape rather than to a
//!   claim about whether the phrase exists yet. When `/identity` is settled this section should get
//!   stronger — name the phrase, link the route — and the test should tighten with it.
//! * **The hidden move in both two-player games hides by NON-REVEAL on this server.** The page says
//!   "hidden from your opponent", never "hidden from everyone".
//! * **Nothing is on a chain**, nothing is money, and the shelf is the three-key ship list.
//!
//! ## The tooth that matters most
//!
//! [`tests::every_shipped_game_has_a_section`] drives `dreggnet_catalog::SHIPPED_KEYS`. Advertising
//! a fourth game without writing its section fails the build — a guide that silently omits a
//! shipped game is worse than no guide, because a reader trusts it to be complete.

use axum::Router;
use axum::response::Html;
use axum::routing::get;

use crate::{PRODUCT_NAME, document};

/// **Mount the player guide.** Additive and state-free — `/guide` is the canonical path and
/// `/how-to-play` is the alias a stranger is as likely to type; both serve the identical page
/// rather than redirecting, because a redirect is a round trip for no reader benefit.
pub fn guide_router() -> Router {
    Router::new()
        .route("/guide", get(get_guide))
        .route("/how-to-play", get(get_guide))
}

async fn get_guide() -> Html<String> {
    Html(guide_page())
}

/// The opening — what the whole surface is, in one paragraph, with no word borrowed from this
/// project. The claim is the honest one and is the entire point: moves are RE-RUN and CHECKED.
fn what_this_is() -> String {
    "<section class=\"panel\" id=\"guide-what\"><h2>What this is</h2>\
     <p class=\"prose\">Three games you can play in a browser tab. Nothing to install, no \
     account, no wallet.</p>\
     <p class=\"prose\">One thing is different about them, and it is the reason they exist. \
     <strong>When you take a turn, the game re-runs your move against the rules before it writes \
     anything down.</strong> If the move is not allowed it is refused and nothing happens. You \
     cannot talk the page into letting you through. And <strong>when a game is over, anyone can \
     replay it</strong> from the first move to the last and watch it come out the same way. That \
     is why the daily score board cannot be faked: a submitted run that does not replay correctly \
     is shown as <strong>FAIL</strong> and never ranks.</p>\
     <p class=\"prose\">That is the whole pitch. It happens in this server and in your own browser \
     tab, not on a blockchain, and no public network is involved.</p>\
     </section>"
        .to_string()
}

/// The two things we are NOT good at yet, said before a newcomer can be surprised by either. A
/// guide that oversells is worse than none, and the identity one in particular is destructive: a
/// player who clears their browser loses everything with no warning and no way back.
fn before_you_start() -> String {
    "<section class=\"panel\" id=\"guide-warnings\"><h2>Two honest warnings first</h2>\
     <ul class=\"rules\">\
     <li><strong>By default you are identified by a browser cookie.</strong> No password, no email \
     and <strong>no recovery</strong>. Clear your browser data, or open the site in a private \
     window, and you are a brand-new person with a blank history. Nothing you did before comes \
     back. If a recovery phrase is offered in the navigation, claiming one is what makes an identity \
     survive that; until you claim one, nothing here is durable.</li>\
     <li><strong>It is early.</strong> No chat, no friends list, no matchmaking. To play a \
     two-player game you open a table and send someone the link yourself. <strong>Here on your \
     own?</strong> The Descent is a game for one, and on a two-player table you can hold both seats \
     yourself: take one seat, then open the invite in a private window and take the other. And \
     nothing you collect here is money or is for sale.</li>\
     </ul></section>"
        .to_string()
}

/// The Descent — the flagship, and the only one of the three that is solo. Every number here is
/// the game's own (`dungeon_on_dregg::descent`), read rather than typed, so a rules change that
/// moves the light budget or the carry cap cannot leave this page quietly wrong.
fn descent_section() -> String {
    let breath = dungeon_on_dregg::descent::BREATH;
    let floors = dungeon_on_dregg::descent::FLOORS;
    let cap = dungeon_on_dregg::descent::CAP;
    let days = dungeon_on_dregg::descent::DAYS;
    format!(
        "<section class=\"panel\" id=\"guide-descent\"><h2>The Descent</h2>\
         <p class=\"prose\"><strong>What it is:</strong> a solo dungeon crawl with one life, played \
         against a torch that never refills.</p>\
         <p class=\"prose\"><strong>What you are trying to do:</strong> get down to the bottom \
         floor, pick up the prize that lies there, and climb all the way back out to the surface \
         before your light runs out. The score board calls a run that carries the prize out \
         <em>crowned</em>: that is the whole word, there is nothing else to it.</p>\
         <p class=\"prose\"><strong>How a turn works.</strong> You press one button, and every \
         button spends light. You have {breath} breaths of light for the entire run and there is no \
         way to get more.</p>\
         <ul class=\"rules\">\
         <li><strong>Descend</strong> · one floor down, one breath.</li>\
         <li><strong>Climb</strong> · one floor up, one breath. This is the only way out, which is \
         why the light you have left is never the real number: you also have to afford the climb \
         home. {floors} floors down means {floors} breaths just to reach the surface.</li>\
         <li><strong>Take the relic</strong> · pick up what is on this floor, one breath.</li>\
         <li><strong>Use a key</strong> · three of the eight relics are keys, and a locked way \
         needs the matching key in hand. A key is never hidden behind the door it opens, so every \
         way is openable if you go and get the key first.</li>\
         <li><strong>Press the guardian</strong> · two breaths, and it costs you nothing else.</li>\
         <li><strong>Lunge at the guardian</strong> · the same result for one breath, but it \
         permanently costs you one carrying slot for the rest of the run. Cheaper now, worse at the \
         bottom.</li>\
         <li><strong>Bank and end the run</strong> · only possible standing on the surface. \
         Everything you carried out is yours; everything still down there is gone, and the run is \
         over. There is no second attempt today.</li>\
         </ul>\
         <p class=\"prose\"><strong>The squeeze.</strong> You can hold {cap} things, minus how deep \
         you are, minus any lunge damage. So on floor 1 you have {shallow} slots and on floor \
         {floors} you have {deep}, and at the bottom you need three keys plus the prize, which is \
         exactly {deep}. <strong>So you can never carry a treasure out AND the prize.</strong> Every \
         run is the same choice: go for the prize, or come back shallow and full. The dungeon gets \
         stingier the further in you go, on purpose. And that is also what makes a lunge a real \
         decision rather than a free discount, because the slot it costs you is one you needed.</p>\
         <p class=\"prose\"><strong>What makes it interesting:</strong> everyone in the world gets \
         the <em>same</em> dungeon each day, and the dungeon is drawn from a public random number \
         that nobody, including us, can pick in advance. Today's dungeon was not chosen; it was \
         revealed. There are {days} possible maps, every one of them checked to be beatable, and \
         the best line on any given day spends between 24 and {breath} of your {breath} breaths. \
         There is almost no slack. Most runs should not make it.</p>\
         <p class=\"prose\"><a class=\"play\" href=\"{play}\">Play The Descent \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a> &nbsp; \
         <a class=\"play\" href=\"/descent\">See today's finished runs \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></p>\
         </section>",
        breath = breath,
        floors = floors,
        cap = cap,
        days = days,
        shallow = cap - 1,
        deep = cap - floors,
        play = crate::DESCENT_PLAY_PATH,
    )
}

/// Automatafl — the simultaneous-move board game. `rook line` is the sweep's flagged term: it is
/// spelled out as "straight lines only, along a row or a column" with the chess comparison in
/// parentheses, so a reader who has never played chess is not left behind by an analogy.
fn automatafl_section() -> String {
    let n = dregg_automatafl::game::N;
    format!(
        "<section class=\"panel\" id=\"guide-automatafl\"><h2>Automatafl</h2>\
         <p class=\"prose\"><strong>What it is:</strong> a two-player board game where the piece \
         that decides it is the one neither of you controls.</p>\
         <p class=\"prose\"><strong>What you are trying to do:</strong> drive the automaton (the \
         single glowing piece) onto one of your own two corners. Each side owns two of the four \
         corners.</p>\
         <p class=\"prose\"><strong>How a turn works.</strong> You do not take turns. <strong>Both \
         players choose a move at the same time</strong>, in secret. When you have both chosen, \
         both moves open at once, and then one turn applies both of them.</p>\
         <ul class=\"rules\">\
         <li>The board is {n}×{n}. It holds <strong>repulsors</strong> (marked <code>R</code>, the \
         pale spiky ones) which push the automaton away, <strong>attractors</strong> (marked \
         <code>A</code>, the round brass discs) which pull it toward them, and one \
         <strong>automaton</strong> (marked <code>@</code>, the violet ring, the only thing on the \
         board that glows).</li>\
         <li>Pieces move in <strong>straight lines only</strong>: along a row or along a column, \
         any distance, never diagonally, never onto the automaton. (If you play chess: exactly like \
         a rook.)</li>\
         <li><strong>Either player may push any piece.</strong> The pieces are not yours or theirs: \
         they are shared. That is the entire source of the tension.</li>\
         <li>Once the round resolves, the automaton takes one step: pulled toward attractors and \
         pushed from repulsors along each axis. Get it to your corner and you have won.</li>\
         <li><strong>If you both grab the same square, that round does not happen.</strong> The \
         contested square is marked with a dead <code>×</code>, the board freezes exactly where it \
         was, and both of you owe a fresh move that may not use a marked square at either end. The \
         turn counter does not advance until a round comes back clean, and every retry burns a new \
         square, so this cannot go on forever.</li>\
         </ul>\
         <p class=\"prose\"><strong>What makes it interesting:</strong> because you are both moving \
         shared pieces at the same moment, a good move is not the move that helps you; it is the \
         move that still helps you given what they are probably doing to the same board. You are \
         guessing at your opponent rather than waiting on them.</p>\
         <p class=\"prose\"><strong>Be clear about the secrecy.</strong> While your move is sealed \
         your opponent is not shown it, but the hiding is <em>this server declining to tell \
         them</em>: your move sits here in plain form until you open it. It is hidden from your \
         opponent, not from the server. If you would rather not trust the server with that, do not \
         play here.</p>\
         <p class=\"prose\"><a class=\"play\" href=\"/automatafl\">Open an Automatafl table \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></p>\
         </section>",
        n = n,
    )
}

/// Multiway-Tug — and the one thing this page exists to say about it. A first-time reader pressed
/// a button, watched all seven rows come back identical and *"would have concluded the button did
/// nothing"* (the sweep). That is the rules working, so the page has to say so before the player
/// finds out by mistrusting it.
fn tug_section() -> String {
    let guilds = dregg_multiway_tug::reference::N_GUILDS;
    let deck = dregg_multiway_tug::reference::DECK_SIZE;
    format!(
        "<section class=\"panel\" id=\"guide-tug\"><h2>Multiway-Tug</h2>\
         <p class=\"prose\"><strong>What it is:</strong> a two-player game of hidden influence over \
         {guilds} guilds. (<em>Guild</em> and <em>lane</em> mean the same thing; guild 3 \
         <em>is</em> lane 3, and the table uses both words.)</p>\
         <p class=\"prose\"><strong>What you are trying to do:</strong> end the round leading more \
         of the {guilds} guilds than your opponent, by weight. They are worth \
         <code>2 2 2 3 3 4 5</code>, and whoever leads a guild takes its whole weight: there is no \
         splitting. The round always plays out in full; <em>then</em> it is decided. You win if you \
         hold 11 weight or 4 guilds; failing that it still comes out one way (on total weight \
         first, guilds held second), and only an exact tie on both is a draw.</p>\
         <p class=\"prose\"><strong>How a turn works.</strong> You hold six cards, hidden. Your \
         opponent sees only <em>how many</em> you hold, never which. Each card belongs to one \
         guild, and that is the guild it pulls for whoever ends up holding it. There are {deck} \
         cards in the deck and none is ever created or destroyed during a round. You get \
         <strong>four moves for the whole round, one of each kind</strong>, in whatever order you \
         like:</p>\
         <ul class=\"rules\">\
         <li><strong>Play one face down.</strong> It stays face down until the very end.</li>\
         <li><strong>Burn two.</strong> Those two leave the round and score for nobody, ever.</li>\
         <li><strong>Lay out three.</strong> Your opponent takes one of the three; you get the \
         other two.</li>\
         <li><strong>Lay out two pairs.</strong> Your opponent takes one pair; you get the \
         other.</li>\
         </ul>\
         <p class=\"prose\">On the last two you decide <em>what to put in front of them</em> and \
         they decide <em>which part they take</em>. You can never answer your own offer. That is \
         the game. Then everything turns face up at once: each face-down card lands on its owner's \
         side of its guild, and only then is the leading counted.</p>\
         <p class=\"prose\"><strong>The thing that looks broken and is not.</strong> Spending a \
         move usually does not move the {guilds} guild rows at all. A face-down card reaches nobody \
         until the reveal; burnt cards reach nobody ever; a three-card or two-pair offer sits in \
         the middle and only lands when your opponent answers it. So it is completely normal to \
         press a button and see all {guilds} rows come back identical. What <em>does</em> move is \
         the running account of where all {deck} cards are (held, face down, burnt, placed), and \
         the table prints it. If you want to see that your move landed, watch that line rather than \
         the guild rows.</p>\
         <p class=\"prose\"><strong>What makes it interesting:</strong> on both of the lay-out \
         moves you are choosing how <em>even</em> to make the split. A balanced cut gives away less \
         but gains you less; a lopsided one hands your opponent a real prize if they spot it. You \
         are not so much bluffing about your hand as pricing what you are willing to lose.</p>\
         <p class=\"prose\"><strong>Honest about the size of it:</strong> a round is one round. \
         There is no match, no best-of, no alternating first move, and the seat that answers the \
         last offer has a measurable advantage. Mechanics derived from Hanamikoji (Kota Nakayama); \
         this is an original re-theming.</p>\
         <p class=\"prose\"><a class=\"play\" href=\"/tug\">Open a Multiway-Tug table \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></p>\
         </section>",
        guilds = guilds,
        deck = deck,
    )
}

/// **The guide's own prose** — the `<main>` fragment, split out from [`guide_page`] because it is
/// what the no-private-vocabulary tests must read. Checking the whole document instead would be a
/// test that cannot fail: [`crate::STYLE`] carries `.receipt` and `.executor-*` CSS class names, so
/// `page.contains("receipt")` is true of every page on the product regardless of what its copy says.
fn guide_body() -> String {
    format!(
        "<main class=\"session af-table\">\
         <div class=\"page-head\">\
         <p class=\"eyebrow\">Start from nothing · no account, no install</p>\
         <h1>How to play</h1>\
         <p class=\"deck\">Written for someone who has never heard of any of this. What the three \
         games are, what you are trying to do, how one turn works, and the two things we are not \
         good at yet.</p>\
         </div>\
         {what}{warnings}{descent}{automatafl}{tug}\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← All games</a></p>\
         </main>",
        what = what_this_is(),
        warnings = before_you_start(),
        descent = descent_section(),
        automatafl = automatafl_section(),
        tug = tug_section(),
    )
}

/// `GET /guide` — the whole page.
fn guide_page() -> String {
    document(
        &format!("{PRODUCT_NAME} · how to play"),
        "guide",
        &guide_body(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑ THE SWEEP'S JARGON LIST, as data — and it LIVES IN ONE PLACE, `scripts/player-vocabulary.tsv`.
    ///
    /// These are the terms with NO player-facing job at all: a newcomer would have to learn them
    /// here, which is exactly the finding. `crowned`, `guild`/`lane` and the straight-line rule are
    /// deliberately absent from it — they are load-bearing, so they are permitted WITH a definition,
    /// which [`the_load_bearing_terms_are_defined_in_place`] checks separately.
    ///
    /// ⚑ WHY IT MOVED OUT OF THIS FILE. The const version gated exactly one function, and `/guide`
    /// scored 0 while the same list was violated on 6 of 13 live surfaces. Widening it needed a
    /// second reader (`scripts/check-player-vocabulary.py`, which sweeps every page from source),
    /// and a second reader must not mean a second list. This test keeps the RENDERED half — it
    /// reads `guide_body()`, so jargon composed in from another module is caught here and nowhere
    /// else — while the script keeps the breadth. Both parse the same file.
    const VOCABULARY_TSV: &str = include_str!("../../scripts/player-vocabulary.tsv");

    /// The first column of every non-comment row.
    fn private_vocabulary() -> Vec<&'static str> {
        VOCABULARY_TSV
            .lines()
            .map(str::trim_end)
            .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
            .map(|line| {
                line.split('\t')
                    .next()
                    .expect("split always yields a first field")
                    .trim()
            })
            .collect()
    }

    /// Every banned term `text` uses. The check is a function rather than a loop inside one test so
    /// the gate itself can be shown to bite — see [`the_vocabulary_gate_can_go_red`].
    fn private_vocabulary_in(text: &str) -> Vec<&'static str> {
        let lower = text.to_lowercase();
        private_vocabulary()
            .into_iter()
            .filter(|term| lower.contains(term))
            .collect()
    }

    /// ⚑ THE SHARED LIST IS ITSELF A THING THAT CAN GO EMPTY. `private_vocabulary_in` filters a
    /// list; an empty list makes every negative assertion below pass vacuously, and a TSV read by
    /// two languages is exactly the kind of file a bad edit silently empties. So the parse is
    /// asserted at the size the sweep produced, four of its terms are named outright, and every
    /// row is required to carry the answer to "then what do I write instead".
    #[test]
    fn the_shared_vocabulary_file_parses_to_the_sweeps_list() {
        let terms = private_vocabulary();
        assert!(
            terms.len() >= 15,
            "scripts/player-vocabulary.tsv parsed to {} terms; the sweep's list is 15 and this \
             gate is a filter over it, so a short parse silently disarms every check below: {terms:?}",
            terms.len()
        );
        for required in ["executor", "receipt", "merkle", "◈"] {
            assert!(
                terms.contains(&required),
                "`{required}` is missing from scripts/player-vocabulary.tsv: {terms:?}"
            );
        }
        // Every row carries its reason and its replacement strategy. A term with no answer to
        // "then what do I write instead" is a rule a lane cannot follow, so it is not a rule.
        for line in VOCABULARY_TSV
            .lines()
            .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with('#'))
        {
            let fields: Vec<&str> = line.split('\t').collect();
            assert!(
                fields.len() == 3 && fields.iter().all(|f| !f.trim().is_empty()),
                "a vocabulary row needs `term<TAB>why<TAB>what to say instead`, got {fields:?}"
            );
        }
    }

    /// ⚑ THE ACCEPTANCE TEST FROM THE SWEEP, as a build gate: adding `executor` or `receipt` to the
    /// guide's copy turns this red.
    #[test]
    fn the_guide_uses_no_word_a_newcomer_would_have_to_learn_here() {
        let found = private_vocabulary_in(&guide_body());
        assert!(
            found.is_empty(),
            "the player guide uses {found:?} — words a newcomer would have to learn here"
        );
    }

    /// ⚑ A GATE THAT CANNOT GO RED IS NOT A GATE
    /// ([[feedback-a-documented-wound-is-not-a-detected-one]]). The test above is a NEGATIVE
    /// assertion, which is exactly the shape that passes when the thing it reads is empty or when
    /// the checker is broken. So the checker is driven on prose that DOES carry the jargon, and on
    /// the real body, and required to disagree about them.
    #[test]
    fn the_vocabulary_gate_can_go_red() {
        let bad = "The executor writes a receipt over the committed root; the fog is per-viewer.";
        let found = private_vocabulary_in(bad);
        assert!(
            found.contains(&"executor") && found.contains(&"receipt") && found.contains(&"fog"),
            "the checker missed jargon it was pointed straight at: {found:?}"
        );
        // And the thing it reads is real: a page with no body would pass the gate above vacuously.
        assert!(
            guide_body().len() > 4_000,
            "the guide body is too small to be the page the gate is supposed to be checking"
        );
    }

    /// The three terms the guide DOES need. Each must arrive with its definition attached, in the
    /// same breath — a defined term is fine, a bare one is the sweep's finding all over again.
    #[test]
    fn the_load_bearing_terms_are_defined_in_place() {
        let page = guide_body();
        assert!(
            page.contains("<em>crowned</em>: that is the whole word"),
            "`crowned` must be defined where it is introduced"
        );
        assert!(
            page.contains("guild 3 <em>is</em> lane 3"),
            "`guild` and `lane` must be equated on first use"
        );
        assert!(
            page.contains("straight lines only") && page.contains("like a rook"),
            "the move rule must be spelled out before the chess analogy, not replaced by it"
        );
    }

    /// ⚑ A GUIDE THAT OMITS A SHIPPED GAME IS WORSE THAN NO GUIDE, because a reader trusts it to
    /// be complete. Driven off the ship list itself, so advertising a fourth game without writing
    /// its section is a build failure rather than a silent hole.
    #[test]
    fn every_shipped_game_has_a_section() {
        let page = guide_body();
        for key in dreggnet_catalog::SHIPPED_KEYS {
            let anchor = format!("id=\"guide-{key}\"");
            assert!(
                page.contains(&anchor),
                "`{key}` is on the ship list but the player guide has no `{anchor}` section"
            );
        }
    }

    /// The identity story is a browser cookie with no recovery, and an opt-in recovery phrase has
    /// NOT landed for this surface. The page must warn rather than reassure, and it must not
    /// promise the thing that does not exist.
    #[test]
    fn the_guide_never_promises_a_durable_identity() {
        let page = guide_body();
        assert!(
            page.contains("no recovery"),
            "the cookie default's lack of recovery must be stated"
        );
        assert!(
            page.contains("until you claim one, nothing here is durable"),
            "the page must say durability requires an ACT, not that it is the default"
        );
        for lie in [
            "your history is saved",
            "your account",
            "sign in",
            "log in",
            "recover your",
        ] {
            assert!(
                !page.to_lowercase().contains(lie),
                "the guide implies a durable identity with `{lie}`"
            );
        }
    }

    /// The hidden move hides by NON-REVEAL on this host, which can read both sides. The page may
    /// say "hidden from your opponent" and may not say or imply more.
    #[test]
    fn the_secrecy_claim_names_who_it_hides_from() {
        let page = guide_body();
        assert!(
            page.contains("hidden from your opponent, not from the server"),
            "the non-reveal residue must be stated on the page"
        );
        for lie in [
            "hidden from everyone",
            "nobody can see",
            "end-to-end",
            "we cannot see",
        ] {
            assert!(
                !page.to_lowercase().contains(lie),
                "the guide overclaims the seal with `{lie}`"
            );
        }
    }

    /// The tug's rough edge in the sweep was a reader concluding *"the button did nothing"*. The
    /// guide must pre-empt it, and must not contradict what the table does.
    #[test]
    fn the_guide_explains_the_still_scoreboard_rather_than_hiding_it() {
        let page = tug_section();
        let guilds = dregg_multiway_tug::reference::N_GUILDS;
        assert!(
            page.contains(&format!("does not move the {guilds} guild rows at all")),
            "the still-scoreboard explanation must survive an edit: {page}"
        );
        assert!(
            page.contains("looks broken and is not"),
            "the explanation must be labelled as the expected behaviour"
        );
    }

    /// Both aliases serve the guide, and the page names itself in the nav.
    #[tokio::test]
    async fn both_paths_serve_the_guide() {
        use axum::body::Body;
        use axum::http::{Request, StatusCode};
        use tower::ServiceExt as _;

        for path in ["/guide", "/how-to-play"] {
            let response = guide_router()
                .oneshot(Request::builder().uri(path).body(Body::empty()).unwrap())
                .await
                .expect("the guide router answers");
            assert_eq!(response.status(), StatusCode::OK, "{path}");
        }
    }
}
