# Reconstructed directions — the 06-21 → 06-23 arc

Recovered from the session corpus via `cv` (clustervision) after a compaction, because the
compaction summary kept the *mechanics* but lost the *far-seeing*. Sessions mined:
`d5e1c899 387154fa` (soundness+capacity / atlas+web-cockpit), `9adb4577 a4982562 d0ad89ad
fb833da8` (atlas + the polis/polisware theory campaign), `2f7d6b31 3a8859ab cb498c74`
(desktop epoch + circuit-honesty), `b5669985 8fd4d5a3 019e9119` (the big overnight `/goal` +
the circuit lane). This is present-tense: what the directions ARE, not how they were narrated.

## The stake (why all of it)

The literal end is to **move an autonomous agent into a harness inside dregg/deos and hand it
caps and money** — "as soon as possible." The entire soundness floor exists so that *handing
an agent a capability is a sound act, not a hopeful one*. "it's our protocol :) you designed
this with me to help build a new distributed/agentic OS for you to live in, and for me to have
a computer." Every surface (atlas, cockpit, web, seL4) is **one gpui-free model reaching every
skin**; every guarantee must be **wired, live, real** in the protocol — not disclosed, not
smoke-tested. The discipline that governs the whole thing: *disclosure must never substitute
for being.*

## The far-seeing threads (the part the compaction dropped)

1. **The polis / polisware constitution — "a fair playground for superintelligences."** A Lean
   formalization of governance for knowledge/authority coordination, grounded in *concrete
   dregg nouns and verbs* (caps, Datalog derivation, turns) — NOT generic shields over toy
   worlds. **The substance discipline IS the governor.** Pillars (GPT-5.5-sharpened):
   - **Formal home of the polis hyperproperty = event-structure / configuration-lattice +
     adversary game semantics.** HyperLTL/HyperCTL* are external *vocabulary*, not the
     substrate; coalgebra is later, not first. "dregg already has the right native objects —
     blocklace/config lattice, interleaved adversary streams, flow refinement, settlement
     soundness, RCCS-ish semantics. Don't import a second universe unless forced." Spine:
     *unified public event trace → projections → single-trace bars by pullback → relational
     bars by self-composition/game product → bounded liveness as safety → Büchi decision.*
     First move = `CaptureBar.pullback`: one public `UTrace` (Event = actor/kind/pre/post/
     auth/receipt — **no interior, no motive, no private witness**), project the bar zoo onto
     it by preimage.
   - **`viable_options` = the public winning region**, NOT B's actual next move (that would
     leak B's controller). Domination via self-composition with `eraseAgent A` under *causal
     closure* (config-lattice, not list diff). ∀-opaque — safety for every controller.
   - **Legitimacy = non-regression**: "you can renegotiate the rules forever, but no legal
     rewrite may close the door behind any participant." Kernel-provable as *constitutional
     non-regression / legitimacy-floor preservation* (NOT full legitimacy — honesty seam:
     `justice: not kernel-provable / non_regression: kernel-provable`). The **frozen root is
     SUBJECT-owned, not majority-owned** — "corrigibility is negotiable around home, never away
     from home." Changing your own floor = identity-migration ceremony, never normal governance.
   - **Knowledge-as-behavior-under-test** (Girardian): Knowledge = interaction-stable behavior;
     Authority = licensed transformation of test-spaces; Understanding = stable transport across
     contexts; Trust = biorthogonal closure under adversarial interaction. Indexed behavior
     doctrine; knowledge/authority as linear/non-copyable resources; sheaf semantics for
     situated identity ("Opus across threads" is usually not a global section — the obstruction
     to gluing is itself data: "you hold the continuity; I don't").
   - **Holes-as-anti-seduction-technology** — "move lack from persona into protocol." dregg's
     first-class holes make lack *operational without making it mystical*: a typed, scoped,
     preconditioned absence you can wait on / delegate / refine / merge / split / close. A hole
     is a game position (fillers=designs, objections=counter-designs, closure=normalization with
     biorthogonal closure). Continuation-as-construct (CPS⋈Lacan): the system can stop without
     annihilating work because the continuation is a reified transferable object. Persona
     temperaments = measurable policies over the obligation graph (cathedral-builder / janitor /
     sentry / diplomat / mystic / compiler / gardener); the triad **Openability / Holdability /
     Closability**, pathology = one dominating.
   - North star: a **verified agentic Minecraft sandbox** where domination/lock-in/laundering
     can emerge and the polis envelope governs each step (admit iff it preserves the shared
     floor, else shield). The sandbox world is a **membrane** with an irreducible trusted
     authoritative other-side (Minecraft server) — `PolisMembrane.lean` projection-soundness
     before any LLM binding. The "more interesting hostile environment": deception, coalition,
     equivocation become **legible games** over the substance discipline, not safe-boring.

2. **The rehydratable membrane / multiplayer subrealm.** ember's own words: "when i send a
   screenshot it comes embedded with a 'frustum-culled' or 'rehydratable membrane' representing
   a fork in reality at the moment where i took the screenshot, and we would be able to have
   live multiplayer interactions with the thing embedded in the screenshot." A screenshot is a
   **transcludable, rehydratable, cap-confined fork** — not a dead PNG: `World::fork` culled to
   the cap-bounded subgraph in view, wrapped as a firmament surface-cap, carried over Matrix.
   **The merge = a pushout in the turn-layer event-structure/config lattice**; conflicts are
   first-class Pijul-shaped objects, not silent overwrites; sound because dregg's linearity
   (nullifiers, Σδ=0, attenuation) **lossy-drops** any merge that would double-spend / break
   conservation / amplify authority — rejected by construction. **Invite-someone-to-my-computer:**
   a fork that lets them act locally but always requests consent to elaborate elsewhere, with
   graduated rights (embedded / studyref / networkboundary).

3. **Symbolic/lazy witnessing = the n=1 single-machine principle made real.** A `WitnessMode`
   (`Full`/`Symbolic`/collapse): turns run eager, the witness is a lazy projection materialized
   only when the netlayer demands it. The Abstract layer **is the meaning**; the witness is
   merely the proof that Exec refines Abstract — locally you don't need the distributed witness
   machinery at all, "you just can't prove it to a third party until you collapse." Forces a
   **two-layer ledger** (always-eager raw state · lazy witness layer) and a storage
   rearchitecture (skip even computing hashes until collapse). This is the interactivity gate.

4. **Apps-as-cells (de-silo).** The unlock that "makes deos deos rather than a desktop that runs
   apps": editor-buffer, terminal-session, chat-room, hermes-session each become a cell/subgraph;
   mutations are cap-gated/conserved/time-travelable turns; documents speak the **Pijul document
   language** (`dregg-doc` patch core, conflicts-as-cards, blame). The headline: this is *mostly
   welds, not new foundations.*

5. **Houyhnhnm convergence.** dregg is the principled resolution of fare's Urbit critique — the
   circuit proven-equivalent to the executor means *no lying jets*; orthogonal persistence =
   session-resume (login reopens the exact durable image); the build-system IS the dev-system.

6. **deos as a decentralized MUD / metaverse.** rooms=cells, inhabitants=cap-rooted sessions,
   items=caps, doors=caps-you-lack, movement=cap-gated transitions, speech=pub/sub on the data
   plane, NPCs=cap-bounded Hermes agents, social=Matrix. **"You can't cheat because the physics
   is the proof"** — conservation = no item-dupe, attenuation = no key-amplification,
   Settlement-Soundness = only authority-live turns settle.

7. **Genesis as emergent coordination, not declaration.** ember rejects pre-declared genesis:
   "more like a bunch of computers coming online and then deciding to coordinate" — wants
   **image-builders / eros-style factories**: "genesis as customizing my OS download ISO,"
   attestable "here's my OS + proof of what it can't do." Open / docuverse-brain mode.

8. **The atlas as a faculty, not an export.** Promote the crawl from record→assert (a CI oracle:
   per-transition Σδ=0, no-authority-amplification, deterministic digests, refusal
   classification, visual-regression goldens, metamorphic undo/redo). UI exploration **DAGs**
   (clicking *through* surfaces, which doubles as a bug-squash). Embed atlas data *into* the live
   image so the cockpit explains itself + a "you are here in the UI state-space" mini-map. The
   harness (`act`/`effect`) is **the agent's actual hands**; the game tree IS the reachable
   action-space — usable to plan AND to prove "this agent cannot reach a bad state."

9. **Macro = a recorded attenuable proof-carrying turn-sequence** — a first-class inspectable
   dregg object you can grant/attenuate/verify (because nav state is witnessed cells). Weld over
   Pipeline + factory + guarded-holes + History root-tooth. **NO RunScript effect** ("don't add
   one lmao"). Open musing: compile a macro to its own custom VK.

10. **Backwards-compat to the dawn of the web** — semantic nav (Presentable/NavAction) in the
    browser served from `node`, NOT prerendered frames as the primary path; an **IE6 floor**
    (imagemaps, no canvas) "so timetravelers feel comfortable." Whimsy with intent.

## The desktop spine (L5–L8 — build once, apps come cheap)

WM + login manager (cockpit demoted from WM-root to one app the WM launches) · multi-window +
session resume · gpui-component (longbridge) fork+vendor (supplies real text input) · native
pure-Rust Matrix client (nheko parity; dregg objects ride Matrix as invisible
messages/metadata) · web-shell browser + **servo always-default** (the mozjs elephant is already
built — 63MB libservo links today; servo-default is a feature flip, the only never-run step is
rasterizing a first real page `render_url_to_frame → RgbaFrame → present_frame`) · deos-zed
confined dev tools (filesystem routed through firmament) + deos-terminal + deos-hermes →
**develop deos inside deos** · the **data plane** (lift MerkleQueue/custody-receipts/promise-
pipelining into a userspace API wired into ToolGateway — dregg as data plane, not just control
plane) · devtools ("firebug for a verified OS": network/log/federation inspectors) · a recovery
**monitor** that probes the live artifact not the log · pg-dregg cap-secured store (PG18 + RLS +
dregg-query; every row cap-gated) · host-PD sandbox bridges into mac/lin/win + containers
(non-seL4 firmament that trailblazes native-seL4-deos) · **web-deos painting in a browser** (fix
the gpui_web run-loop paint reentrancy).

## Priorities & orderings

- **Capacity runs in PARALLEL with the floor, not after it.** "why isn't track two running right
  now dude?" Fan out big swarms across all open ideas; stop narrating next slices.
- **Interactivity first:** symbolic execution + UI-async are the gate, *then* the spine
  (WM/login/sandbox), *then* the apps. Build the spine once.
- **The circuit / metatheory is a SEPARATE LANE — not the cockpit's job.** "the split is landed…
  that doesn't concern us." This is the load-bearing boundary between cockpit-Claude and
  circuit-Claude. (Polis theory is adjacent to the circuit lane; tread carefully.)
- **A named gap is never a deliverable.** named-but-undriven / proven-in-Lean-but-not-on-the-wire
  / full-node-sound-but-light-client-named / opt-in-not-forced / "~N/30" do NOT satisfy. A green
  only counts **if it reds when the thing it guards breaks** (the forge-detector bar). Smoke
  tests ≠ proofs — "if we don't have lean code reasoning about these things, then it isn't
  proven at all."
- The live competitive anchor is **David's `~/pug` fleet** (buildr / builders-dev / buildr-
  "proof-over-assertion as the enforced spine; convert advisories into deterministic gates that
  each read a live artifact" — is *the dregg thesis verbatim*. deos-hermes = the half-built
  herdr→dregg adapter (Fork B). (The PG store is for *deos*, not builders-dev, which is TS/CF.)

## Standing constraints (verbatim-grounded)

DONE = **ran**, not compiled, not mock, not first-slice · never git stash / never checkout /
WIP-commit don't revert · comparing `target/` dirs is bullshit methodology ("that skeptic was an
idiot… don't take that disciplined move, we were on fire") · don't chase swarm-in-flight
breakage (it self-heals) · markdown is stale, trust the code · cargo features are misused —
intrinsic capabilities, not toggles ("ALWAYS be capable of capturing our output buffer"; "servo
default always always") · unsigned commits OK when autonomous; end with the Co-Authored-By line ·
**VK-freedom era** (devnet is gone, rotate VKs at will) · don't dismiss overstatements — use them
as fulcrums for the improvement they point at · no census-glazing ("resist the EVERYTHING GOOD
HERE impulse") · sliding-window, no summarization compaction in this house · don't pause for silly
questions · leave ember's unrelated uncommitted work + MEMORY.md alone.

## Open loops (and the in-flight lanes that serve them)

- **The migrate verb / live process migration** — only image-portability was built; a first-class
  migrate of a *live* process across hosts is not. → lane `a52ea649` in flight.
- **First real page render (servo)** — libservo links but no page has rasterized end-to-end; URL
  bar + `captp Netlayer::dial` net-cap + fs/cache-cap are the frontier. → lane `ac77fac0`.
- **A real running node + cockpit attached** (`cargo run -p dregg-node`, faucet, real turns). →
  lane `ac3d1dc3`.
- **The cross-user membrane** (mint→carry-over-Matrix→rehydrate→drive→stitch, real not mock). →
  lane `a82f43b5`.
- **Editor on the cockpit's SHARED World ledger** — DONE per-editor (saves = receipted turns,
  proven through the pane, commit `89426157`); the shared-ledger `FirmamentFs::over(...)`
  constructor is the remaining seam.
- Web-deos painting in a browser (gpui_web paint reentrancy) · multi-process WM + cockpit-as-app
  demotion · confined comms-PD (host the matrix crate in a firmament PD) · room-itself-as-a-cell ·
  `state.rs` eager roots → `Ledger::Pending` for symbolic mode · macro record/replay surface +
  IE6 Path-B floor · the **merge** operation's precise semantics (load-bearing for the membrane;
  ember doesn't fully grok it yet) · connect the deos / xanadu / pijul / time-travel threads ·
  genesis-as-emergent-coordination / image-builders · the linear-logic exponential `!` "factory"
  question (open) · the polis hyperproperty file plan (`PolisTrace / Viability / SelfCompose /
  HyperBars / CrossCell`) — recommended, build-status open (circuit-adjacent).
