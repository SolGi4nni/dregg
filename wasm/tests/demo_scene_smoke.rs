//! The demo story (`demo/stories/the-commons.scene`) must COMPILE and PLAY through a
//! collective branch — the foundation of the collective-fiction demo. Drives the real
//! `spween-dregg` engine the way `StoryWorld::try_new` does (parse → deploy → start →
//! advance), so a syntax error or a dead-end branch fails this test, not the browser demo.
use spween_dregg::{Driver, WorldCell, parse};

#[test]
fn the_commons_compiles_and_plays_a_branch() {
    let src = include_str!("../../demo/stories/the-commons.scene");
    let scene = parse(src, "the-commons.scene").expect("the-commons.scene must compile (spween syntax)");
    let scene: &'static _ = Box::leak(Box::new(scene));
    let world = WorldCell::deploy(scene, 7).expect("deploy the commons world");
    let mut d = Driver::start(world, scene).expect("start the playthrough");

    assert_eq!(d.current_passage().as_deref(), Some("intro"), "opens at intro");
    let choices = d.choices();
    assert!(choices.len() >= 2, "the intro offers the crowd >=2 branches to vote, got {}", choices.len());

    // Drive the first branch (as a winning collective vote would) and confirm it advances.
    let before = d.current_passage();
    d.advance(choices[0].index).expect("advance the winning branch");
    assert!(
        d.current_passage() != before || d.is_ended(),
        "advancing a branch changes the passage (or ends the story)"
    );
}
