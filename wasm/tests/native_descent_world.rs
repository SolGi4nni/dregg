//! The Lean-native Descent binding must execute as an actual wasm module, not merely compile
//! as host Rust. This is deliberately separate from the older daily/procgen `DescentWorld`.

#![cfg(target_arch = "wasm32")]

use dregg_wasm::bindings_native_descent::NativeDescentWorld;
use wasm_bindgen_test::*;

fn value(json: &str) -> serde_json::Value {
    serde_json::from_str(json).expect("binding response is JSON")
}

#[wasm_bindgen_test]
fn native_descent_actor_and_refusal_semantics_run_in_wasm() {
    let mut world = NativeDescentWorld::new(17).expect("Lean-native Offering opens in wasm");
    let genesis_root = world.root_hex();

    let refused = value(&world.advance("smite".to_string(), 0, "mallory".to_string()));
    assert_eq!(refused["ok"], false);
    assert_eq!(world.revision(), 0, "refusal leaves no ghost event");
    assert_eq!(world.actor(), None, "refusal cannot seize an unclaimed run");
    assert_eq!(world.root_hex(), genesis_root);

    let landed = value(&world.advance("delve".to_string(), 0, "alice".to_string()));
    assert_eq!(landed["ok"], true);
    assert_eq!(world.revision(), 1, "one click is one Offering advance");
    assert_eq!(world.actor().as_deref(), Some("alice"));
    assert_ne!(world.root_hex(), genesis_root);
    assert!(world.verify(), "the in-wasm native action tape replays");
}

#[wasm_bindgen_test]
fn portable_native_record_round_trips_by_replay_in_wasm() {
    let mut original = NativeDescentWorld::new(22).expect("Lean-native Offering opens in wasm");
    assert_eq!(
        value(&original.advance("delve".to_string(), 0, "alice".to_string()))["ok"],
        true
    );
    assert_eq!(
        value(&original.advance("smite".to_string(), 0, "alice".to_string()))["ok"],
        true
    );

    let portable = original.record_json();
    let restored = NativeDescentWorld::from_record_json(portable.clone())
        .expect("the untrusted record exactly replays in wasm");
    assert_eq!(restored.record_json(), portable);
    assert_eq!(restored.revision(), 2);
    assert_eq!(restored.root_hex(), original.root_hex());
    assert!(restored.verify());
}
