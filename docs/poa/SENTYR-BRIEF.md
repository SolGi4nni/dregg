# Path of Angels platform brief for Sentyr

There is a real protected beta now at <https://beta.pathofangels.network> (`poa` / `eden`). It is
the beginning of a place aboard the Khovokhi rather than a replacement for the YouTube poll. The
show still owns the macro scale — where the ship jumps, what its people decide, and what becomes
canon. The site owns the micro scale: expeditions, instruments, repairs, evidence, rumors, crew work,
and the mostly uninhabited volume of the ship itself. The current terminal serves seven hash views —
Field Drills, Expedition, Archive, Flight Recorder, Crew, Bazaar, and Choir, with Galley alongside;
Expedition, Archive and Flight Recorder are labs under Records rather than top-level organs. **Seven**
short games are playable now (Signal Triangulation, Relay Repair, Salvage Lock, Black Box
Reconstruction, Deck Descent, Artificer Logic, Vent Crawl), all seven enrolled by the curator at epoch
1 counter 10, and the Expedition and Archive contain larger demonstrators. The visual treatment is
still a functional field terminal, not a final art direction, but the deployed bytes are signed and
tested, and served by a **single-validator** PoA federation — `poa/deployments/epoch-1/poa-devnet.json`
carries one node at threshold 1. This brief said "three-validator" until 2026-08-09; the fleet was
collapsed to one on 08-05 and nothing here followed.

⚠ Playable is not the same as finished, and this brief should not be read as saying it is. Three of
the seven ship a descriptor their own Lean kernel has since moved away from — Salvage Lock is signed at
a 12-action budget where `SalvageLock.MAX_TURNS` is 18, Black Box at 15 actions and two answer classes
where the kernel is 11 and three, and Deck Descent at `shoring: 2` where `DeckDescent.SHORING` is 1. The
re-emit and re-sign that closes that gap has not been run. Until it is, those three are playing an older
game than the one the kernels prove.

The engine's useful trick is that a game result is an exact object rather than a number the page
claims happened. We are making activities as Lean state machines wherever practical; the browser
plays tables emitted by Lean instead of carrying a second copy of the rules. Consequential actions
can become an append-only event stream with a named predecessor, mission, content epoch, actor,
transition, contribution, and receipt. That gives us rewindable field records, deterministic
replays, audit trails, public ghosts, corrections that supersede rather than erase, and eventually
independent nodes that can re-judge a run. It also gives us a clean canon boundary: a game may
produce a precise beta artifact inside a possibility space you authored, but only your explicit
curator action can promote it into the show.

The obvious flagship is still Descent, rebuilt for PoA rather than merely reskinned: take an
Expedition Officer and a finite loadout into alien decks, choose between incomplete route
hypotheses, spend several incomparable resources, decide what evidence to trust, and extract before
something becomes unrecoverable. We now have Lean kernels for authenticated crew field missions and
owner-wide persistent attendants as raw material for multi-role expeditions and long-lived personal
continuity. Around that flagship we can make a large ecology of one-to-five-minute activities:
signal triangulation, relay repair, salvage locks, black-box reconstruction, containment inspection,
quarantine classification, sensor fusion, damage control, impossible-deck cartography, language
work, archive restoration, and episode debriefs. A good small game must still be fun in practice
mode; its receipt and place in the ship give it a life beyond the score.

There is room for the Neopets kind of depth you meant: recurring places and systems whose edges
touch. The Galley can have a shared daily ration, maintenance shifts, a reclamation culture, rumors,
and communal provisioning. An Archive entry can begin as a silhouette, acquire separately signed
observations, become a studied object, move into a crew exhibit, and perhaps later receive your
official interpretation. Crews can assemble expeditions, specialize, maintain shared shelves, pass
an asynchronous repair between members, submit theories against evidence, or review a disputed
field record. Later, an eligible discovery can become one exact custody object that may be kept,
loaned, exhibited, researched, consumed, bartered, or offered in the Bazaar. These are different
states of the same provenance-bearing thing, not unrelated balances glued together by a universal
currency.

The Dark Bazaar is where we want DrEX, FHE, and MPC to earn their keep. The interesting version is
not a pretend shop with a privacy label: it is a sealed salvage auction, private wants-list, or
batch barter where the public can verify eligibility, conservation, clearing, and custody movement
without learning the fields the mechanism promises to hide. We have substantial proof and market
machinery plus a new Lean Bazaar kernel, but we are keeping the claims narrow while its production
bridges close. The current crew preference exercise, for example, really uses our deployed
Poseidon2 semantics and catches a concrete collision in the old additive design, but it is still
operator-visible — not FHE, MPC, or proof-backed voting. Likewise, Bazaar settlement will stay shut
until a finalized game receipt, exact crowned object, ciphertext/opening relation, and conserving
settlement all meet in one replayable path.

`$DREGG` can make the world stranger and more participatory without becoming “pay to win.” The
browser already speaks the normal Solana wallet sign-message workflow for Wallet Standard wallets
and an explicit classic-provider seam; the server-side code checks holdings of the exact Token-2022
mint and returns a short-lived wallet-bound admission receipt without trusting a balance supplied by
the browser. That node build is not deployed yet, so today the beta shows the boundary but grants no
game power. Once live, holding can open bounded services or unusual procedures — a sealed Bazaar
hall, sponsored computation, a holder/public two-chamber reading, jury eligibility, extra expedition
formats — but should not improve loot, safety, score, or canon authority. We can also implement
several Choir mechanisms rather than ossifying one constitution: one-person voice, capped or
square-root holder voice, delegation, commit-reveal, sortition, prediction, and deliberately silly
event rules after adversarial simulation.

Aspects should wait until their arrival matters in the fiction. The platform can quietly prepare
the hard generic pieces — persistent companion identity, finite behavior, equipment capabilities,
custody and recovery, and ways to act jointly across games — without spending “Aspect” as the name
of a procedural pet. When you introduce them, the narrative event can also be the platform event:
players meet something precious, slowly learn its constrained communication, fit it to different
bodies or tools, and take it into expeditions. Given that Starfall spends a campaign retrieving one,
loss, copying, ownership, and recovery need authored rules rather than ordinary inventory logic.

What we most need from you is not a giant lore dump or a roadmap approval. Pick one small authored
slice with sharp edges: a first deck or inhabited place, three crew roles, several things the crew
believes about it, one encounter whose mechanical truth can be stated without revealing its full
interpretation, the exact discoveries that may exist there, and what must remain sealed. We can turn
that into a signed content pack, a short game or expedition, and beta field records you can later
ignore, contradict in-world, reinterpret, or promote. The private collaboration source is
<https://github.com/emberian/path-of-angels>; a write invitation is pending for `@alteron808`. The
best next design session is simply to walk the live terminal together and decide which door should
become a real place first.
