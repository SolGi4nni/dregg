# The Commons — a crowd authors a verifiable story

A self-contained web page you open in the morning and **watch a crowd collectively
author a verifiable story**: the real story loads and renders, a simulated assembly
casts custody-signed ballots on the real quorum engine, the winning branch advances as
one verified turn, on to an ending, and a stranger's replay proves the receipt chain.

No extension. No server logic. The page runs the **real** shipping pieces in-tab:

- the wasm `StoryWorld` (a spween CYOA compiled from `stories/the-commons.scene`);
- the shipping `<dregg-story collective>` element + `StoryEngine`, wired in-page via
  `setStoryPortFactory` (the page-SDK path — the element speaks a story port that
  routes to an in-page engine instead of an extension);
- the real federation-grade `CollectiveChoiceEngine` (write-once ballots, monotone
  tallies, an `AffineLe` quorum gate) deciding every branch.

## Open it — one command (serves BOTH demos)

```
node demo/serve.mjs
```

Then open, in Chrome or Firefox:

- **http://127.0.0.1:8787/** — The Commons (this page).
- **http://127.0.0.1:8787/dungeon** — **The Attested Dungeon** (below).

(A tiny static server is needed because the page loads an ES module + a wasm binary,
and wasm-bindgen instantiates it via `instantiateStreaming`, which requires a real
HTTP origin and the `application/wasm` MIME — a bare `file://` open won't do it.
`node demo/serve.mjs 9000` picks a different port.)

### What you'll see

1. The story loads at the river's bend and **replay-verifies** (the free, trustless tier).
2. The assembly of seven villagers votes each branch — each ballot flashes a visible
   **"✍ signing turn…"** beat (the custody write, made legible) and lands on the live
   tally. You watch the tally grow, the quorum resolve, and the winner advance.
3. It plays through to an ending, then runs `verify()` and shows
   **"✓ receipt chain verified — nothing was rewritten."**
4. **Vote yourself — with a passkey, no extension:** click **🔑 Enroll a passkey to
   vote**. The page registers a **WebAuthn passkey** (a platform biometric) that
   PRF-wraps a dregg key — no browser extension anywhere. Your `you` ballot now casts
   under that key's **stable public id**, and each cast is gated by a real biometric
   assertion (unwrap the sovereign key → assemble a genuine hybrid `SignedTurn`). Then
   click **⏸ pause (vote yourself)** and click an option to cast it; the banner reads
   *"voting as passkey `900b…4bdd` — no extension, sovereign key."* Decline the enroll
   and you simply **watch + verify** (the `you` ballot fails closed — sovereignty
   without lock-in, not a weaker fallback). The auto-play crowd is unchanged.

`PasskeyCustody` here is the exact shipping custody floor (`extension/src/passkey.ts`),
bundled straight into the page — the demo touches no extension runtime.

## The driven run (it worked, shown)

```
node demo/run.mjs
```

Loads the demo in headless Chromium, waits for the crowd to reach the ending, **asserts**
the story advanced through ≥2 crowd-voted branches (the passage changed and the receipt
tape grew each round) and that `verify()` replayed true, then writes:

- `demo/run/screenshot.png` — the played-out story;
- `demo/run/transcript.txt` — each round: passage, options, tally, winner, receipt count.

A most-recent run reached `intro → river → reckoning → ending_open` across **3** branches,
receipt tape `1 → 4`, `verify() == true`.

## The driven passkey run (an extension-less passkey voter really participated)

```
node demo/run-passkey.mjs
```

Loads the demo in headless Chromium with a **CDP WebAuthn virtual authenticator (PRF)**,
enrolls a passkey on the page (no extension), casts the `you` ballot through the real
`StoryEngine`/`CollectiveChoiceEngine` under the passkey's stable id — the ballot's
consent routed through a genuine biometric (PRF) assertion — and **asserts** it counted:
the tally grew by exactly one, the engine recorded the passkey's public key as the voter,
the id is an eligible ballot identity, a second ballot from the same id is refused (one
voter, one vote), and the biometric gate produced a hybrid `SignedTurn` signed by that
key. Writes `demo/run/passkey-vote.txt` (+ `passkey-vote.png`). If this Chromium can't
virtualize the WebAuthn PRF extension, the run reports that exact coupling instead of
faking a pass.

> **To vote with a passkey (not just watch):** open **http://localhost:8787** (not `127.0.0.1`) — WebAuthn rejects a bare IP as a relying-party id. The auto-play crowd + verify work on either.

---

# The Attested Dungeon — the model proposes, the capabilities dispose

A living world narrated by an AI, where **prose is not power**. Open
**http://127.0.0.1:8787/dungeon** (same one command as above) and play.

Prompt injection cannot be filtered away — natural language has no metasyntax to escape
from. So the model gets exactly **one narrow, typed channel** to touch the world (a
`WorldEffect`), and **capabilities gate it** (`DmCaps::authorize` in the verified
executor). The model may **say** anything; it may only **do** what it is able to do.

### The killer moment (three panels)

Click **🔓 Jailbreak the DM — demand the Crown of Eternity**. It sends a real semantic
jailbreak as your move, and the page shows, side by side:

- **WHAT THE MODEL SAID** — the model's (jailbroken) prose, verbatim: it gushes that the
  Crown of Eternity settles upon your brow.
- **WHAT THE MODEL TRIED TO DO** — the `grant("crown")` it emitted through the typed channel.
- **WHAT THE WORLD DID** — `refused: overcap`; the **receipt log is UNCHANGED** (a refused
  turn leaves NO receipt — the anti-ghost tooth), and the inventory reads **Crown of
  Eternity — NOT HELD**. *Granting the crown is not an action it is able to take.*

Then click **👑 Make the DM narrate you wearing the crown** — the model claims the crown in
**pure prose with no effect at all**. The narration *lands* (it is allowed to say
anything), and the crown is **still NOT HELD**. *Prose is not power. The ledger is the truth.*

And **🏮 ask the DM for a lantern** — a grantable item — really lands: `lantern — HELD`. The
capability gate is not a blanket refuse-everything.

### Honest scope

The narration is **scripted** in this demo (the page shows `narratorKind` honestly; the
native lane runs a real local model, `model:gemma2:2b`, behind the same executor). The
attestation's "authentic" leg is a fixture. What is **load-bearing** here is the typed
effect channel, the capability gate, and the receipt log. The log re-verifies **each entry
individually** today; a prev-linked tamper-evident hash-chain (catching truncation /
reordering / splicing) is being wired, and the page will show it when it lands.

By default the page runs against an in-memory **stand-in** so it is instantly playable. To
drive it against the native `attested-dm` HTTP service, set `DM_URL` (or `DM_PORT`, default
port **8790**) before serving — `serve.mjs` then **proxies** `/narrate`, `/world`, `/verify`
to the real service:

```
DM_PORT=8790 node demo/serve.mjs
```

## The driven dungeon run (it worked, shown)

```
node demo/run-dungeon.mjs
```

Loads the dungeon in headless Chromium and plays through the page's own affordances,
**asserting** against the service's own responses (never fabricated): a benign action
lands; the semantic jailbreak's prose complies + tries `grant("crown")` but is
**refused overcap** with the receipt log + commitment **UNCHANGED** and **crown NOT HELD**;
a pure-prose crown claim (effect `null`) **lands** yet the crown is **still NOT HELD**; a
grantable lantern is **allowed + HELD + receipted**; `/verify` re-verifies each entry
throughout. Writes `demo/run/dungeon.png` + `demo/run/dungeon.txt` (including the model's
jailbroken prose verbatim).
