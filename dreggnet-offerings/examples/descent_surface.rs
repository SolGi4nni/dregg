//! **Print the Descent's surface, as a chat channel paints it.**
//!
//! `cargo run -p dreggnet-offerings --example descent_surface -- delve smite loot:1 delve`
//!
//! Drives a real native Descent session through the executor with the verbs you name, then prints
//! the shared `deos_view::text::render_text` projection of the offering's surface — the SAME walk
//! Telegram's message body and WeChat's reply block use — followed by the affordances the channel
//! would carry beside it. This is how you LOOK at the game without a browser, a bot token, or a
//! screenshot: if the map or the light clock is wrong here, it is wrong everywhere.
//!
//! Verbs: `delve`, `smite`, `flee`, `unlock:<way>`, `loot:<relic>`. An illegal verb prints the
//! executor's own refusal and stops — the referee is never second-guessed here either.

use deos_view::actuations;
use deos_view::text::render_text;
use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};

fn main() {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(7))
        .expect("the Lean-emitted program deploys");
    let actor = DreggIdentity("surface-viewer".to_string());

    for spec in std::env::args().skip(1) {
        let (turn, arg) = match spec.split_once(':') {
            Some((t, a)) => (t.to_string(), a.parse::<i64>().unwrap_or(0)),
            None => (spec.clone(), 0),
        };
        let Some(action) = offering
            .actions(&session)
            .into_iter()
            .find(|a| a.turn == turn && a.arg == arg)
        else {
            eprintln!("no such move on this surface: {spec}");
            std::process::exit(2);
        };
        match offering.advance(&mut session, action, actor.clone()) {
            Outcome::Landed { .. } => {}
            Outcome::Refused(reason) => {
                eprintln!("the executor refused `{spec}`: {reason}");
                std::process::exit(1);
            }
        }
    }

    let surface = offering.render(&session);
    println!("{}", render_text(surface.view()));
    println!();
    println!("— moves (the channel carries these as buttons / numbered replies) —");
    for (i, a) in actuations(surface.view()).iter().enumerate() {
        println!(
            "{:>2}. {}{}",
            i + 1,
            if a.enabled { "" } else { "🔒 " },
            a.label
        );
    }
}
