//! The demo adventure scenes (`demo/stories/*.scene`) must COMPILE and PLAY — the content
//! side of the collective-fiction game. Drives the real spween-dregg engine (parse → deploy →
//! start → advance through GATED choices), so a syntax error or an unreachable ending fails
//! here, not in the browser.
use spween_dregg::{Driver, WorldCell, parse};

fn load(src: &str, name: &str) -> Driver<'static> {
    let scene = parse(src, name).unwrap_or_else(|e| panic!("{name} must compile: {e:?}"));
    let scene: &'static _ = Box::leak(Box::new(scene));
    let world = WorldCell::deploy(scene, 7).expect("deploy");
    Driver::start(world, scene).expect("start")
}

/// The lantern-first route (which unlocks the Cipher Door gate) plays through to an ending —
/// a robust greedy playthrough (every step takes the first AVAILABLE choice), so a dead-end or
/// an unreachable ending fails here.
#[test]
fn the_drowned_library_plays_lantern_first_to_an_ending() {
    let src = include_str!("../../demo/stories/the-drowned-library.scene");
    let mut d = load(src, "the-drowned-library.scene");
    assert_eq!(d.current_passage().as_deref(), Some("intro"));
    // Take the LANTERN (sets the flag the Cipher Door / lit-hall gates need).
    let take_lantern = d
        .choices()
        .into_iter()
        .find(|c| c.text.contains("LANTERN"))
        .expect("lantern choice");
    d.advance(take_lantern.index).expect("take lantern");
    assert_eq!(d.current_passage().as_deref(), Some("arches"));
    // With the lantern the Cipher Door IS offered (the gate is met) — proves the gate opens.
    assert!(
        d.choices()
            .into_iter()
            .any(|c| c.text.contains("Cipher") && c.available),
        "with the lantern, the Cipher Door is OFFERED (gate met)"
    );
    // Greedily play the rest until a terminal passage (an ending has no onward choice).
    let mut steps = 0;
    while !d.is_ended() && steps < 16 {
        let choices = d.choices();
        match choices.iter().find(|c| c.available) {
            Some(pick) => {
                d.advance(pick.index).expect("advance an available choice");
                steps += 1;
            }
            None => break, // no onward choice = a terminal (ending) passage
        }
    }
    let end = d.current_passage().unwrap_or_default();
    assert!(
        end.starts_with("ending_"),
        "the lantern-first route reaches a real ending, got passage {end:?}"
    );
}

/// Route B (no lantern) → the Cipher Door is NOT offered (the gate blocks it). Non-vacuity of the gate.
#[test]
fn without_the_lantern_the_cipher_door_is_gated_shut() {
    let src = include_str!("../../demo/stories/the-drowned-library.scene");
    let mut d = load(src, "the-drowned-library.scene");
    // skip the lantern (the second intro choice), reach arches
    let skip = d
        .choices()
        .into_iter()
        .find(|c| c.text.contains("Leave the lantern"))
        .expect("skip choice");
    d.advance(skip.index).expect("skip lantern");
    assert_eq!(d.current_passage().as_deref(), Some("arches"));
    let cipher_available = d
        .choices()
        .into_iter()
        .any(|c| c.text.contains("Cipher") && c.available);
    assert!(
        !cipher_available,
        "without the lantern, the Cipher Door gate blocks it"
    );
}
