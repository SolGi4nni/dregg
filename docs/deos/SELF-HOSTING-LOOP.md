# The self-hosting loop — develop dregg INSIDE deos

deos hosts its own development: a running `dregg-node`, the cockpit attached to
it, a firmament-backed editor whose saves are verified ledger turns, and a real
terminal running `cargo`/`git` over a live PTY — all inside the deos image.

This document records the RUN that demonstrates both real halves in one cockpit
view and the one remaining wire for a true single edit→compile loop.

## The two real halves

* **(a) Editor — firmament over the LIVE World.** The editor pane
  ([`dock::editor_surface::EditorPane::firmament_over`]) edits a sovereign
  *cell*, not a disk file. A save sets the buffer and calls the editor's real
  `save`, which commits a cap-gated `SetField` turn through the verified
  executor, leaving a genuine `TurnReceipt`. The save count on the status line is
  the live on-ledger receipt count — the same ledger the cockpit's cell inspector
  reads.

* **(b) Terminal — a live alacritty PTY.** The terminal pane
  ([`dock::terminal_surface::TerminalPane::spawn`]) runs a real child process on a
  real PTY. The default bake runs `cargo --version`; its genuine stdout lands in
  the cell grid.

The view that mounts both is `starbridge_v2::self_hosting::SelfHostingView`.

## Reproduce (headless bake, RUNS + ASSERTS + screenshots)

```sh
cd starbridge-v2
cargo build --features native-full --bin starbridge-v2
./target/debug/starbridge-v2 --render-self-hosting self-hosting-loop --render-size 1600x1000
# optional: --self-hosting-cmd git --version    (run a different real command)
```

The bake is self-checking — it FAILS (non-zero exit) unless BOTH hold:

* the editor save grew the live `TurnReceipt` count (a real verified turn), and
* the terminal command's genuine output reached the grid (a real PTY child).

A passing run prints both proofs and writes `self-hosting-loop.png`. The captured
frame (`starbridge-v2/self-hosting-loop.png`, 3200×2000) shows the editor pane
(status line: `saved main.rs (… bytes) — N saves · on-ledger FirmamentFs
(cell=file, save=receipted turn)`) beside the terminal pane (the real
`cargo …-nightly (…)` banner), under the live image header (height · cells ·
receipts).

A representative run:

```
OK headless SELF-HOSTING render -> self-hosting-loop.png (3200x2000, logical 1600x1000)
  PROOF (a) editor: save fired a real turn — receipts 5 -> 6 on-ledger …
  PROOF (b) terminal: live alacritty PTY ran `cargo --version` INSIDE deos —
            grid shows: "cargo 1.98.0-nightly (…)"
```

## The one remaining seam (full edit-source-then-cargo loop)

The two halves are each REAL, but they touch different stores: the editor saves
to CELLS (ledger turns) while `cargo` reads DISK. A *single* loop — edit the very
file `cargo` then compiles — needs a **FirmamentFs↔disk dual-write**: on each
save, mirror the cell's new content to the on-disk path the terminal's `cargo`
reads (the cell stays the durable, receipted form; the disk file is a derived
read-mirror). That mirror is the one wire still to lay; neither half is faked to
stand in for it.
