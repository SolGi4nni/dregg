//! # `dregg-drive` — interactively drive a complete flow through a surface's real view model.
//!
//! ```text
//! dregg-drive --surface telegram --offering automatafl --as alice
//! > open                 # opens/joins; prints the view AS TELEGRAM WOULD SEND IT
//! > press 3              # presses the 3rd offered control
//! > send /help           # free text / a slash command, for chat surfaces
//! > act select 42        # a raw (turn, arg), when you want precision
//! > as bob               # switch viewer WITHOUT resetting state, and diff the controls
//! > restart              # drop in-memory state, resume from the durable store
//! > again                # re-request the surface
//! > stale 0              # press a control from the PREVIOUS frame
//! > transcript           # the sequence so far, replayable with --script
//! ```
//!
//! Every surface is reached through its OWN projection and its OWN router. Where an inch is
//! unreachable without a live token, the driver says so at startup and never fakes it — a faked
//! projection would make every finding worthless.

mod out;
mod prose;
mod surface;
mod tg;
mod web;

use std::io::Write as _;
use std::path::PathBuf;

use out::{Frame, fog_diff};
use surface::DrivenSurface;

const USAGE: &str = "\
dregg-drive — drive a real session through a real surface's real view model.

USAGE
  dregg-drive --surface <telegram|web|prose|discord> --offering <key> [options]

OPTIONS
  --surface   <s>   telegram | web | prose | discord      (default: prose)
  --offering  <k>   an offering key; SHIPPED: descent automatafl tug   (default: automatafl)
  --as        <who> the viewer to drive as                (default: alice)
  --session   <id>  the session slot (web/prose)          (default: drive-<offering>)
  --chat      <n>   the telegram chat id; NEGATIVE = a group collective   (default: 424242)
  --topic     <n>   a telegram forum-topic thread id      (default: none)
  --state-dir <p>   the durable store `restart` resumes from
                    (default: a fresh temp dir per run)
  --script    <f>   run a transcript non-interactively, then exit
  --keys            list the host's offering keys and exit
  --help

COMMANDS (also the transcript/script language; `#` starts a comment)
  open              open or join the offering in this surface's slot
  again | back      re-request the surface without acting
  press <n>         press the n-th control of the CURRENT frame
  stale <n>         press the n-th control of the PREVIOUS frame (a screen gone stale)
  act <turn> <arg>  fire a raw affordance, offered or not
  send <text...>    free text / a slash command (chat surfaces)
  as <who>          switch viewer, re-request, and DIFF the offered controls
  restart           rebuild the host from the durable store, mid-session
  verify            re-verify the committed chain through this surface's verify path
  controls          re-print the offered controls
  where             re-print what is REAL about this surface
  transcript        print the command sequence so far, replayable via --script
  quit | exit
";

struct Config {
    surface: String,
    offering: String,
    viewer: String,
    session: Option<String>,
    chat: i64,
    topic: Option<i64>,
    state_dir: Option<PathBuf>,
    script: Option<PathBuf>,
    keys: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            surface: "prose".into(),
            offering: "automatafl".into(),
            viewer: "alice".into(),
            session: None,
            chat: 424_242,
            topic: None,
            state_dir: None,
            script: None,
            keys: false,
        }
    }
}

fn main() {
    let mut cfg = Config::default();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut value = || args.next().unwrap_or_default();
        match arg.as_str() {
            "--surface" => cfg.surface = value(),
            "--offering" | "--game" => cfg.offering = value(),
            "--as" | "--viewer" => cfg.viewer = value(),
            "--session" => cfg.session = Some(value()),
            "--chat" => cfg.chat = value().parse().unwrap_or(424_242),
            "--topic" => cfg.topic = value().parse().ok(),
            "--state-dir" => cfg.state_dir = Some(PathBuf::from(value())),
            "--script" => cfg.script = Some(PathBuf::from(value())),
            "--keys" => cfg.keys = true,
            "--help" | "-h" => {
                print!("{USAGE}");
                return;
            }
            other => {
                eprintln!("unknown argument `{other}`\n\n{USAGE}");
                std::process::exit(2);
            }
        }
    }

    if cfg.keys {
        list_keys();
        return;
    }

    let dir = cfg.state_dir.clone().unwrap_or_else(|| {
        let dir = std::env::temp_dir().join(format!(
            "dregg-drive-{}-{}-{}",
            std::process::id(),
            cfg.surface,
            cfg.offering
        ));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    });
    let session = cfg
        .session
        .clone()
        .unwrap_or_else(|| format!("drive-{}", cfg.offering));

    // ⚑ `descent` will not open on a live-config catalog host until a verified day is published.
    // Offline, pinned, and idempotent enough to just do — and REPORTED, because if it fails the
    // first `open` failure would otherwise look like a defect in the offering.
    let day = dreggnet_catalog::publish_pinned_descent_day();

    println!("┌─ dregg-drive ─────────────────────────────────────────────────");
    println!("│ offering  {} {}", cfg.offering, ship_note(&cfg.offering));
    println!("│ viewer    {}", cfg.viewer);
    println!("│ store     {}", dir.display());
    match &day {
        Ok(()) => println!("│ descent   pinned day published (offline, verified)"),
        Err(e) => {
            println!("│ descent   ⚠ pinned day NOT published: {e:?} — `descent` may refuse to open")
        }
    }

    let mut driver: Box<dyn DrivenSurface> = match cfg.surface.as_str() {
        "telegram" | "tg" => {
            match tg::TgDriver::new(dir.clone(), cfg.chat, cfg.topic, &cfg.offering, &cfg.viewer) {
                Ok(d) => Box::new(d),
                Err(why) => {
                    eprintln!("cannot build the telegram driver: {why}");
                    std::process::exit(1);
                }
            }
        }
        "web" => match web::WebDriver::new(dir.clone(), &cfg.offering, &session, &cfg.viewer) {
            Ok(d) => Box::new(d),
            Err(why) => {
                eprintln!("cannot build the web driver: {why}");
                std::process::exit(1);
            }
        },
        "prose" | "text" | "chat" => {
            match prose::ProseDriver::new(dir.clone(), &cfg.offering, &session, &cfg.viewer) {
                Ok(d) => Box::new(d),
                Err(why) => {
                    eprintln!("cannot build the prose driver: {why}");
                    std::process::exit(1);
                }
            }
        }
        "discord" => {
            println!("│ surface   discord — ⚠ NOT REACHABLE FROM HERE, and not faked.");
            println!("{DISCORD_WHY}");
            std::process::exit(3);
        }
        other => {
            eprintln!("unknown surface `{other}` — telegram | web | prose | discord");
            std::process::exit(2);
        }
    };

    println!(
        "│ surface   {}",
        wrap(&driver.provenance(), 64, "│           ")
    );
    println!("└───────────────────────────────────────────────────────────────");

    let mut transcript: Vec<String> = vec![
        format!(
            "# dregg-drive --surface {} --offering {} --as {} --session {} --chat {}",
            cfg.surface, cfg.offering, cfg.viewer, session, cfg.chat
        ),
        "# replay: dregg-drive <same flags> --script THIS-FILE".to_string(),
    ];
    let mut seq = 0usize;

    match cfg.script.clone() {
        Some(path) => {
            let body = match std::fs::read_to_string(&path) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("cannot read script {}: {e}", path.display());
                    std::process::exit(1);
                }
            };
            for line in body.lines() {
                if !step(&mut driver, line, &mut seq, &mut transcript) {
                    break;
                }
            }
            println!("\n── script complete: {seq} command(s) ──");
        }
        None => {
            println!("\n`help` for commands. `open` to begin.");
            let stdin = std::io::stdin();
            loop {
                print!("{}> ", driver.viewer());
                let _ = std::io::stdout().flush();
                let mut line = String::new();
                match stdin.read_line(&mut line) {
                    Ok(0) => break,
                    Ok(_) => {}
                    Err(e) => {
                        eprintln!("stdin: {e}");
                        break;
                    }
                }
                if !step(&mut driver, &line, &mut seq, &mut transcript) {
                    break;
                }
            }
            println!("\n── transcript ({seq} command(s)) ──");
            for line in &transcript {
                println!("{line}");
            }
        }
    }
}

/// Execute one command line. `false` ends the session.
fn step(
    driver: &mut Box<dyn DrivenSurface>,
    line: &str,
    seq: &mut usize,
    transcript: &mut Vec<String>,
) -> bool {
    let line = line.split('#').next().unwrap_or("").trim();
    if line.is_empty() {
        return true;
    }
    let (word, rest) = line.split_once(' ').unwrap_or((line, ""));
    let rest = rest.trim();

    let frame = match word {
        "quit" | "exit" | "q" => return false,
        "help" | "?" => {
            print!("{USAGE}");
            return true;
        }
        "where" => {
            println!("{}", driver.provenance());
            return true;
        }
        "controls" => {
            let mut f = Frame::new("controls");
            f.controls = driver.controls();
            f
        }
        "transcript" => {
            println!("\n── transcript ──");
            for l in transcript.iter() {
                println!("{l}");
            }
            println!("── replay it with --script ──");
            return true;
        }
        "open" => driver.open(),
        "again" | "back" => driver.again(),
        "restart" => driver.restart(),
        "verify" => driver.verify(),
        "press" => match rest.parse::<usize>() {
            Ok(n) => driver.press(n),
            Err(_) => Frame::driver_note("press", "usage: press <index>"),
        },
        "stale" => match rest.parse::<usize>() {
            Ok(n) => driver.press_stale(n),
            Err(_) => Frame::driver_note("stale", "usage: stale <index>"),
        },
        "act" => {
            let mut parts = rest.split_whitespace();
            match (parts.next(), parts.next()) {
                (Some(turn), Some(arg)) => match arg.parse::<i64>() {
                    Ok(arg) => driver.act(turn, arg),
                    Err(_) => Frame::driver_note("act", "usage: act <turn> <arg:i64>"),
                },
                (Some(turn), None) => driver.act(turn, 0),
                _ => Frame::driver_note("act", "usage: act <turn> <arg:i64>"),
            }
        }
        "send" => {
            if rest.is_empty() {
                Frame::driver_note("send", "usage: send <text or /command>")
            } else {
                driver.send(rest)
            }
        }
        // ⚑ The fog experiment, in one verb: capture the labels, switch who is looking, re-request
        // the SAME session, and diff. Nothing else moved, so every difference is a projection
        // decision — including one that reveals another player's state through a button.
        "as" => {
            if rest.is_empty() {
                Frame::driver_note("as", "usage: as <viewer>")
            } else {
                let was = driver.viewer();
                let before = driver
                    .controls()
                    .into_iter()
                    .map(|c| c.label)
                    .collect::<std::collections::BTreeSet<_>>();
                let switch = driver.become_viewer(rest);
                *seq += 1;
                print!("{}", switch.render(*seq));
                let mut after = driver.again();
                after.verb = format!("again (as {rest})");
                after.note(fog_diff(&was, &before, rest, &after.label_set()));
                transcript.push(format!("as {rest}"));
                *seq += 1;
                print!("{}", after.render(*seq));
                return true;
            }
        }
        other => Frame::driver_note(
            other,
            format!(
                "unknown command `{other}` — `help` lists them. (An illegible refusal is a \
                     defect; this one names the fix.)"
            ),
        ),
    };

    transcript.push(line.to_string());
    *seq += 1;
    print!("{}", frame.render(*seq));
    true
}

fn ship_note(key: &str) -> &'static str {
    if dreggnet_catalog::is_shipped(key) {
        "(SHIPPED — on the curated shelf)"
    } else {
        "(not on the ship list)"
    }
}

fn list_keys() {
    let host = dreggnet_web::demo_host();
    println!("SHIPPED: {}", dreggnet_catalog::SHIPPED_KEYS.join(" "));
    println!("\nALL REGISTERED (advertised marked ✓):");
    for info in host.list_offerings() {
        println!(
            "  {} {}  {}",
            if info.advertised { "✓" } else { " " },
            info.key,
            info.title
        );
    }
}

/// Wrap a long provenance line under a gutter.
fn wrap(text: &str, width: usize, gutter: &str) -> String {
    let mut lines = Vec::new();
    let mut line = String::new();
    for word in text.split_whitespace() {
        if !line.is_empty() && line.chars().count() + 1 + word.chars().count() > width {
            lines.push(std::mem::take(&mut line));
        }
        if !line.is_empty() {
            line.push(' ');
        }
        line.push_str(word);
    }
    if !line.is_empty() {
        lines.push(line);
    }
    lines.join(&format!("\n{gutter}"))
}

/// Why `--surface discord` is not driven here — stated, never faked.
const DISCORD_WHY: &str = "\
│
│ TWO separate reasons, both structural:
│
│ 1. THE ROUTING IS IN ANOTHER WORKSPACE. The Discord command surface lives in
│    `discord-bot/`, which the root Cargo.toml EXCLUDES from the workspace: it
│    pulls sqlx/sqlez -> libsqlite3-sys 0.30, whose `links = \"sqlite3\"` collides
│    with deos-matrix's rusqlite 0.35, and cargo allows one `links=\"sqlite3\"` per
│    workspace. So there is no in-process way to reach discord's own
│    slash-command/component router from a root-workspace binary at all. Driving
│    it needs a second binary inside `discord-bot/`.
│
│ 2. THE PROJECTION IS REACHABLE BUT COSTLY TO ENABLE HERE.
│    `deos_view::discord::render_card(title, tree, binds) -> DiscordCard` is a
│    pure function -- no token, no gateway -- but it sits behind the `discord`
│    feature, which pulls serenity (builder+model+rustls). Cargo unifies features
│    within one resolve, so enabling it HERE enables it for every other consumer
│    of deos-view in this workspace, dreggnet-web included. Paying that on every
│    lane's build to print one more projection is the wrong trade today.
│
│ WHAT TO DO INSTEAD: `--surface prose` is the same *kind* of instrument for the
│ chat class -- it drives `deos_view::text::render_text`, which IS what
│ `TelegramBackend` renders with -- and it reports the projection census (which
│ ViewNode variants the channel drops). Discord's own walk differs (it maps Row
│ and Table rows to embed FIELDS and mints buttons for Slider/Toggle), so a
│ discord-specific hole would need its own driver; the census tells you which
│ variants to go look at.";
