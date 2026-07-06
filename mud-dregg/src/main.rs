//! `mud-dregg` — run the playable arc: rooms-as-cells, commands-as-verifiable-turns, and
//! fork→explore→stitch divergent multiplayer with conflicts REFUSED (the config-lattice made
//! playable). gpui-free, no GPU — the real `embedded-executor` only.
//!
//! Run:  `cargo run --bin mud-dregg`

fn main() {
    mud_dregg::run_arc();
}
