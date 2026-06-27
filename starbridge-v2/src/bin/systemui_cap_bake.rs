//! **The graphideOS SystemUI cap-chrome bake** — `GRAPHIDEOS.md §1` (the SystemUI row)
//! + `§2` stage 4, made eyeball-able.
//!
//! Builds a REAL [`android_cell::PermWorld`] for a confined "Maps" android-cell (a live
//! ledger + the verified `TurnExecutor`), dresses it as the deos cockpit's SystemUI
//! cap-chrome (the status bar + the quick-settings shade + the powerbox hand-over sheet),
//! prints it, then drives a REAL `Effect::GrantCapability` hand-over of the LOCATION cap
//! and re-prints — so the artifact shows the phone's permission UI being the deos cap
//! surface: a dim badge flips lit because the cell GENUINELY holds the cap after a
//! verified kernel turn. It also exercises the powerbox tooth (a CAMERA hand-over the
//! device principal cannot back is refused by the executor, the cap never lands).
//!
//! gpui-free; run it:
//! ```text
//! cargo run --no-default-features --features android-systemui --bin systemui-cap-bake
//! ```

use android_cell::AndroidPermission;
use starbridge_v2::systemui_caps::SystemUiCapChrome;

fn divider(title: &str) {
    println!("\n══════════ {title} ══════════");
}

fn render(chrome: &SystemUiCapChrome) {
    for line in chrome.all_text() {
        println!("{line}");
    }
}

fn main() {
    println!("graphideOS — SystemUI cap-chrome bake");
    println!(
        "the deos cockpit AS the android system UI · the permission UI IS the deos cap surface"
    );

    // A confined Maps android-cell declaring INTERNET (normal) + ACCESS_FINE_LOCATION +
    // CAMERA (dangerous). The device/system principal holds the LOCATION device authority
    // but NOT the camera authority (you cannot hand over what you do not hold).
    let mut chrome = SystemUiCapChrome::install(
        "Maps · com.example.maps",
        "com.example.maps",
        0x51,
        0x01,
        [
            AndroidPermission::Internet,
            AndroidPermission::AccessFineLocation,
            AndroidPermission::Camera,
        ],
        [AndroidPermission::AccessFineLocation],
    );

    divider("BEFORE — the app's standing authority");
    render(&chrome);

    // THE HAND-OVER — a real Effect::GrantCapability through the verified executor.
    divider("HAND OVER · LOCATION (the device principal can back it)");
    let outcome = chrome.hand_over(AndroidPermission::AccessFineLocation);
    println!("{}", SystemUiCapChrome::outcome_line(&outcome));
    if let Some(receipt) = outcome.receipt() {
        println!(
            "  kernel receipt: agent {} · {} action(s) — a verified turn landed the cap in the app's c-list",
            hex8(receipt.agent.as_bytes()),
            receipt.action_count
        );
    }

    divider("AFTER — the badge flips lit because the cell GENUINELY holds the cap");
    render(&chrome);

    // THE POWERBOX TOOTH — a CAMERA hand-over the principal cannot back is refused by the
    // executor itself; the cap never lands, no ambient escalation.
    divider("HAND OVER · CAMERA (the device principal CANNOT back it)");
    let refused = chrome.hand_over(AndroidPermission::Camera);
    println!("{}", SystemUiCapChrome::outcome_line(&refused));
    println!(
        "  CAMERA stays a dim hand-over row: {}",
        chrome
            .grant_sheet()
            .iter()
            .any(|r| r.permission == AndroidPermission::Camera)
    );

    divider("DONE");
    println!(
        "the chrome rendered an app's held caps + the grant sheet; a real kernel grant lit a badge."
    );
}

/// Short hex of a cell id's first 4 bytes — a glance label for the receipt's agent.
fn hex8(bytes: &[u8]) -> String {
    bytes.iter().take(4).map(|b| format!("{b:02x}")).collect()
}
