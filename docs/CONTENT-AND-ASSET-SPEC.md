# The Descent — Content & Asset Authoring Spec (for spwashi)

A content author's guide + task spec, grounded in the real code (every claim cites file:line, from two ground-truth scouts).
Three tracks spwashi can pick from, plus the small Rust **enablements** we build first so each track has a paved path.

## The guiding principle (what makes this different)
Two properties the whole system already enforces, which content must ride:
1. **Provable rarity.** An asset's traits are drawn by a *provably-fair weighted draw* off a committed (drand-beacon) seed —
   so "I have the legendary" is a *proof anyone re-derives*, not a claim. Rarity = the weight of the trait-combo; the draw is
   verifiable (`procgen-dregg` transcript + `verify_generation`, `procgen-dregg/src/lib.rs:280`).
2. **Deterministic render.** traits → sprite must be a *pure deterministic function* (same traits → same image, so a stranger
   re-renders the identical asset). This matches the house norm — everything is byte-identical replay (`bindings_descent.rs`
   "a stranger re-executes byte-identically"). Free/nondeterministic art would break the "anyone reproduces it" property.

## Content is per-SEASON
The game runs as seasons (one VK-epoch's run, punctuated by upgrades — see `dregg-season/`). This matters for content:
appending to a procgen table **re-buckets every seed's draw** (`pick = draw % table.len()`, `procgen-dregg/src/lib.rs:902`),
which breaks re-generation of *already-published* universes. So **content expansion is a content-epoch bump = a season
boundary**, not a silent edit. A season ships a content SET (`SeasonManifest.content_tag` is the handle). Frame it as the
content cadence, not churn: each season, a fresh set.

---

## TRACK A — Generative visual assets (JS animated/vector sprites)  ⟵ the main new thing
The visual layer is **totally greenfield** — a grep for `canvas|<svg|webgl|sprite|@keyframes` across `extension/`,
`dreggnet-web`, `deos-view` finds *zero* source hits. Today's richest visual is an emoji glyph (`deos-view` `Icon` ->
`<span class="deos-icon">glyph</span>`, `web.rs:339`). So there's nothing to conflict with — the shape below is dictated by
the existing getter-over-port + deterministic-replay conventions.

**The pipeline:** `weighted trait draw (committed seed) → traits_root on the asset (content-addressed) → JS render(traits) →
SVG sprite`. Verifiable rarity in, deterministic vector out.

### Enablements we build (the paved path — small, additive):
- **E1. A trait field on the asset.** Add `traits_root: [u8;32]` (or a small fixed trait vector: shape/material/glow/rune/
  palette indices) as a new `.identity(...)` on `NoteDesc`/`note_schema` (`dreggnet-asset/src/lib.rs:116,157`), folded into
  `note_digest` (`:133`) and derivable into `AssetId` via `mint_seed` (`:101`). Content-addressed, `WriteOnce`-frozen, carried
  across the lineage — the sprite is provably bound to the asset. *(gap: zero trait fields today.)*
- **E2. A first-class weighted draw.** `DrawStream::weighted(index, &committed_weights) -> usize` — a CDF over one
  `draw_bounded` (~10 lines, still one draw per index, stays inside the fixed transcript, `dice/src/draw.rs:125`). The weight
  table **must be committed** (a Rust const, or hashed into the request) so weights can't be swapped after the seed. *(today
  weighting is done by repeated table slots — `loot_slot`, `procgen-dregg/src/lib.rs:925` — impractical for 1/1000.)*
- **E3. A traits getter + a `<dregg-sprite>` element.** A wasm getter `traitsJson()` (mirroring `stateJson`,
  `wasm/src/bindings_descent.rs:251`) delivered over a typed port; a thin `<dregg-sprite>` custom element following the built
  `DreggElement` closed-shadow, port-fed, no-wasm-in-element pattern (`extension/src/elements/dregg-descent.ts`) that hands
  spwashi's `render(traits)` its shadow root to draw into. *(NOT `window.dregg` — that's custody/signing only.)*

### spwashi's work (Track A):
- **The weight tables** (E2's committed weights): the rarity distribution per trait axis (blade-shape weights, glow-rarity,
  palette weights, …). Data/const spwashi tunes; committed so rarity is provable.
- **The JS renderers**: `render(traits) -> SVGString` — a **pure deterministic** function, **SVG via `createElementNS`**
  (vector, animatable via `@keyframes`/SMIL, string-serializable for byte-identical re-render). Animated/vector sprites for
  weapons, armor, characters, monsters, loot. One renderer per asset kind; each a pure `traits -> svg`.
- Optional: a preview harness (feed random trait vectors, see the sprite range) — pure JS, no chain needed.

---

## TRACK B — Scene / content authoring (spween `.scene` + UGC)  ⟵ text, no Rust
The Descent's live daily + the no-cheat board both consume **spween `.scene`** (not the older attested-dm `.dungeon`).
`daily_scene` emits spween text (`daily_descent.rs:248`); `compile_scene` lowers gates → real executor teeth
(`spween-dregg/src/compiler.rs:182`); the leaderboard re-executes the *same* teeth, so **the no-cheat property is preserved
automatically** — no augmentation on the daily path.

### The exact authorable syntax (spween, `~/dev/spween/src/parser.rs`):
```
---
id: my-scene
title: The Salt Vault
tags: [descent]
---
=== entrance
The vault door hangs open.
* [Force it] { strength >= 5 }
  ~ noise += 1
  -> hall
* [Pick the lock] { gold >= "$price" }      # var-op-var: a REAL cross-slot tooth now (compiler.rs:357)
  ~ gold -= 10
  -> hall
=== hall
...
* [Take the crown] { hands < 1 }
  ~ hands = 1
  -> END
```
- **Conditions** `{ … }`: `var op value` (`>= <= > < == !=`), membership `category.key` (e.g. `inventory.sword`), `!`, `&&`/
  `,` (AND), `||` (OR).
- **Effects** `~`: `var = v` / `var += n` / `var -= n` / `call("name", args)`.
- **Lowers to REAL executor teeth:** numeric/bool `var op literal`, membership, `Or`->`AnyOf`, `Not`, and **var-op-var**
  (`{ gold >= "$price" }`, the `$`-sigil, just landed). **Handler-only (not enforced):** a gate on a var the same choice
  `Set`s, string/float compares, `!=`, deep boolean nesting. Budget: 16 slots (`STATE_SLOTS`, `compiler.rs:85`).
- **Stakes pattern** (copy Bloodgate, `bloodgate.rs:81`): a warden that hits back + an HP-floor gate + a `[Fall…]{hp<=20}`
  passage that sets `downed=1 -> END` = real permadeath.

### Publishing (UGC):
- `Universe::authored_signed(name, author, source, win)` (`ugc-dregg/src/lib.rs:409`) content-addresses + ed25519-attests a
  hand-written spween world; remix lineage via a declared `parent` (`:535`). The no-cheat board re-executes to the declared
  `WinCondition` (`verify_completion`, `:819`).
- **Enablement E4 (named gap):** `/gallery publish` today only mints *procgen* universes from a `seed:` string
  (`gallery.rs:1094`); the `authored`-scene machinery exists + reconstructs on boot but **no command accepts a raw `.scene`**.
  Wiring `/gallery publish-scene <spween source>` -> `Universe::authored_signed` is the one surface that lets spwashi (and
  every player) publish hand-written universes to the board **without Rust**. Small; high flywheel leverage.

### spwashi's work (Track B): author `.scene` files (text) — new rooms, encounters, branching, prose, gated logic, stakes,
win conditions. Publish via E4. All executor-refereed automatically.

---

## TRACK C — Procgen content expansion (Rust tables, per-season)
`procgen-dregg/src/lib.rs`: `const THEMES: [Theme; 6]` (`:394`) is the biome table; `struct Theme` (`:347`) is one biome's
schema (adjectives/nouns/descriptions, a weapon, a `monsters: &[Monster]` slice, one `boss`, treasures, a potion, a hazard
trio, a lore NPC, a shrine spell). **Add a biome** = append a `Theme` + bump `[Theme; 6]->[Theme; 7]`. **Add a monster** =
push onto that biome's `monsters` slice. Fairness: appending re-buckets draws → **do it at a season boundary** (a content
epoch bump), never silently on a live season.

### Highest-leverage expansions (most daily variety per effort):
1. **Enrich the daily template** (`daily_scene`, `daily_descent.rs:220` — TEXT, no kernel change): the daily is structurally
   thin (one warden + a key + linear corridors + one hoard) while procgen already models monsters/loot/NPCs/shrines/hazards
   it doesn't use. Inject encounter *types* into the corridor loop — a mid-descent monster with an HP-floor trade, a loot/
   consumable choice, a skill-check door, an NPC lore gate. **Biggest single win.**
2. **Unify the daily's 4 flavor themes** (`daily_descent.rs:116`, a *separate* hardcoded table) **with procgen's 6 biomes**
   (`:394`) — one table, 4→6+ variety, every future biome flows to both.
3. **Grow `Monster` rosters + descriptions/nouns/adjectives** per biome (versioned table appends) — cheap naming variety.
4. Wire E4 (authored-scene publish) — turns the whole UGC flywheel on for text authors.

Items 1/2/4 are text/plumbing; item 3 is a versioned Rust table edit.

---

## Division of labor (the paved-path handoff)
**We build the enablements** (small, additive, they give spwashi something real to plug into): E1 trait field · E2 weighted
draw · E3 `traitsJson` getter + `<dregg-sprite>` element scaffold · E4 `/gallery publish-scene`. Then the daily-template
enrichment (Track C #1) + the theme unification (#2) as the reference content.

**spwashi builds** on the paved path: the JS `render(traits)->svg` sprite renderers + the committed weight tables (Track A),
`.scene` universes (Track B), and — as versioned per-season content — procgen biome/monster appends (Track C).

**The pipeline, end to end:** `spwashi's weight tables + a committed beacon seed → E2 weighted draw → E1 traits on a minted
dreggnet-asset (owned, provenance-bound) → E3 traitsJson → spwashi's render(traits) → an SVG sprite`, and separately
`spwashi's .scene → parse → compile_scene (teeth) → deploy → the no-cheat board re-executes`. Provable rarity + deterministic
render + no-cheat verification, all preserved by construction.
