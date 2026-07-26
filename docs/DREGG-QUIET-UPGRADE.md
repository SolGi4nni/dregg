# DREGG QUIET UPGRADE — building the new world atop the old

*Spec and governing rules for the content-script layer that scans any page for dregg-things in
plaintext and quietly upgrades them into live, verified, hyperinteractive `<dregg-*>` components.
Companion to `DREGG-WEB-SPEC.md` (the element/capability substrate). The layer is built:
`extension/src/detect.ts` (the detector, §2), `extension/src/port.ts` + `extension/src/netlayer.ts`
(the port + resolver, §3), `extension/src/elements/dregg-poll.ts` (the thin view). §§1–7 are the
governing rules the code cites; §9 states build status.*

---

## 0. The thesis

The old web can only carry **references**. That is all it needs to carry, because **dregg content
self-certifies**: `dregg://` objects are blake3-content-addressed and proof-verified. Therefore:

> **Twitter is an untrusted transport.** It carries a plaintext `dregg://poll/…`. It cannot forge
> the object (content hash) and cannot fake the tally (proof). The extension + the proof supply the
> physics. No platform cooperation is required, ever.

So we do not ask platforms to adopt dregg. We let people **paste a reference into the old web**, and
whoever holds the agent sees the new one. It degrades to a plaintext link; it upgrades to verifiable
hyperinteractivity. **This is not a growth hack — it is the content-addressing pillar realized in
the wild.** And it is not Twitter-specific: a detector upgrades *any* page — Mastodon, Discord, HN,
a blog, a wiki, a forum, an email client. **The extension is a universal upgrader of the existing web.**

---

## 1. The payload — one string, two readings

A dregg-thing must survive: plaintext, 280 chars, copy/paste, and link-shorteners (t.co) that rewrite
`href` but preserve the visible text.

**Canonical form:** `dregg://<kind>/<content-addr>[?q]` — e.g. `dregg://poll/b3_7f2a…`
**Mirror form (REQUIRED for graceful degradation):** `https://dregg.net/d/<kind>/<content-addr>[?q]`

The mirror form is a *clickable link* for anyone without the extension (its target is the
server-rendered, still-verifiable tier-`server` view — a named seam, not yet built; §9 item 4),
**and** it is detectable by the scanner as the same dregg-thing. One string, two readings: **inert-but-useful without the agent,
live-and-verified with it.** Posters SHOULD paste the mirror form; the scanner accepts both.

**Served mirror shape (`dregg-mirror`, §9 item 4):** `https://dregg.gg/<kind>/<addr>`, with
`/d/<kind>/<addr>` kept as a permanent alias so every already-published link above keeps
resolving. Two deliberate shortenings, both bought with the same currency — X truncates
*displayed* link text, so every character of path prefix is a character of address that does not
survive the elision: the `/d/` segment is dropped (the kind segment already namespaces the
space, so `/d/` carried no information), and the addr may be a **git-style unambiguous hex
prefix** with the `b3_` tag optional. `dregg.gg/poll/7f2a9c4d` is 22 characters. An ambiguous
prefix is REFUSED, never resolved to a guess; the tag stays mandatory in the canonical
`dregg://` string, which travels and must never lose its algorithm.

Constraints:
- The content-addr is the object's blake3 digest → **the reference is self-authenticating**; a
  platform that rewrites the URL breaks the link (fail-closed), it cannot substitute content.
- Query params are *hints only* (a display label). Never trusted, never rendered before verification.
- Length: keep the canonical under ~64 chars so it fits alongside prose in a post.

## 2. The detector (content script)

A single platform-agnostic content script:
- `MutationObserver` over the document; scans **text nodes** and **anchor `href`s** for the
  dregg-thing pattern (canonical or mirror). Handles t.co by preferring the anchor's *visible text*
  when the `href` is a shortener.
- **Idempotent**: mark upgraded nodes (`data-dregg-upgraded`), never double-upgrade; survive SPA
  re-renders (Twitter re-mounts aggressively) by re-scanning on mutation, keyed by the content-addr.
- **Respectful**: replace only the matched node/anchor; preserve surrounding prose and layout; keep
  the original link text as **light-DOM fallback content** inside the element, so if the component
  fails to boot the reader still sees a working link.
- **Opt-in per origin** (see §6): the user allows quiet-upgrade per site; default-deny on unknown
  origins is the safe posture.
- Platform adapters are DOM-quirk shims only (t.co unwrap, virtualized-list re-scan). **No
  platform-specific trust logic, ever.**

## 3. THE SPLIT — thin view in the page, engine in the extension

**The load-bearing architectural consequence.** A hostile host's CSP will block wasm in the page
context, and a hostile page must not be able to touch the prover. So:

```
  ┌── PAGE (hostile: Twitter) ──────────────────┐      ┌── EXTENSION (the person's agent) ─────┐
  │  <dregg-poll>                               │      │                                        │
  │    · Shadow DOM render surface (closed)     │◄────►│  netlayer  : fetch dregg:// (content-  │
  │    · light-DOM fallback = the original link │ port │              addressed, cross-origin,  │
  │    · NO wasm, NO keys, NO trust             │      │              cached, verified)         │
  │    · reflects trust="extension" + badge     │      │  executor  : the wasm world (in-tab    │
  └─────────────────────────────────────────────┘      │              turn, receipt)            │
                                                        │  verifier  : light-client re-check     │
   the page can neither forge what's in the shadow      │  custody   : cipherclerk + confirm-    │
   nor reach the engine that produced it                │              intent consent (ext. UI)  │
                                                        └────────────────────────────────────────┘
```

This is **more** trustworthy than an in-page engine, not less:
- **Shadow DOM (`mode: "closed"` on hostile hosts)** — page script cannot read or rewrite the
  rendered view. The page can *host* a `<dregg-poll>`; it cannot *lie about what's inside it.*
- **The prover/executor runs in extension context** — a hostile page cannot tamper with it, cannot
  see the witness, cannot swap the wasm.
- **The consent step happens in extension chrome.** `confirm-intent` shows the *faithful reading* of
  the turn bound to `[turn <hash>]` in UI the page **cannot overlay, forge, or clickjack.** So even
  a fully hostile page cannot trick a person into signing a different turn than they see. **This is
  the single most important security property of the whole design.**

### Port protocol (element ↔ background)
Minimal, capability-shaped, all responses carry a trust tier:
- `resolve(uri) → { object, receipt_chain, verified: bool, tier }` — content-addressed fetch + verify
- `render(uri, state) → html` — the world's `render_html()` (in-wasm, extension side)
- `fire(uri, turn, arg) → { receipt, new_state, verified }` — a real cap-gated verified turn
- `sign(turn_bytes) → signature | refused` — routes to `confirm-intent` consent UI (extension chrome)
- `verify(uri) → { ok, tier, receipt_count }` — the self-verify badge's source of truth

The element **never trusts the page for state**; every repaint re-reads through the port. The page
cannot inject affordances (the click wire is scoped to the shadow root).

## 4. The upgrade lifecycle

1. Detector matches a dregg-thing → creates `<dregg-poll>` (or the kind's element), moves the
   original link into its light DOM as fallback, sets `src`.
2. `connectedCallback` → open a port to the background → `resolve(src)`.
3. On `verified: true` → attach **closed** shadow root, `innerHTML = render(…)`, wire clicks *inside
   the shadow*, reflect `trust="extension"` + `[verified]`, render the honest badge.
4. On `verified: false` or resolve failure → **do not render the object**. Keep the fallback link,
   set `[error]`, show "⚠ could not verify — showing the original link." **Fail-closed, visibly.**
5. Click a choice → `fire(...)` → if the turn needs custody, `sign(...)` → the extension's
   confirm-intent shows the faithful reading → person approves → receipt → repaint + re-verify.

## 5. Trust labeling (never hide the tier)

Reflected attribute + visible badge, always:
- `trust="extension"` → "✓ verified by your cipherclerk"
- `trust="sdk"` → "✓ verified in this page" (page-bundled wasm; page code, still content-verified)
- `trust="server"` → "✓ verified by dregg.net (trust the origin)" — the mirror-form fallback
- absent/`[error]` → "⚠ unverified · original link shown"

A person must always be able to tell *who checked this*. The semantic web's failure was that an
asserted claim looked identical to a true one.

## 6. Security posture (the invariants)

- **Transport is untrusted** (content-addressed + proof) → fetch from anywhere; verify always.
- **Page is untrusted** → closed shadow DOM; engine in extension; click wire shadow-scoped; state
  never read from the page.
- **Consent is un-overlayable** → signing happens in extension chrome (confirm-intent), never in-page.
- **Fail-closed and visible** → an unverifiable object renders nothing but the original link + a
  warning. Never render unverified content as if verified.
- **Per-origin opt-in** for quiet-upgrade; default-deny unknown origins. The person decides which
  hostile hosts get upgraded.
- **No platform-specific trust logic.** Adapters may only fix DOM quirks.
- **Privacy**: resolving a dregg-thing reveals interest in that object to the netlayer. The extension
  netlayer SHOULD cache and MAY batch/pad; a per-origin gateway sees the origin's traffic. Document
  this honestly; do not pretend it is private.

## 7. Degradation ladder

| person has | what they see | tier |
|---|---|---|
| extension | live `<dregg-poll>`, can vote (custody), self-verified in-shadow | `extension` |
| page bundles `@dregg/sdk` | live element, verify locally; vote needs passkey/extension | `sdk` |
| nothing | a clickable `https://dregg.net/d/…` mirror link → server-rendered verifiable view | `server` |
| link broken/mangled | plaintext text; nothing pretends to be verified | — |

## 8. Why the poll is the first artifact — and what stands beside it

The `ViewNode` render vocabulary's core competence — buttons + integer args + numeric binds — *is*
a poll, so `<dregg-poll>` is the smallest complete artifact of the split and ships first. The
catalog does not stop there: `<dregg-doc>` (`extension/src/elements/dregg-doc.ts`) renders a
verifiable document, holds a first-class conflict as BOTH alternatives side by side, and publishes
a resolution as a real verified turn through the background DocEngine; `<dregg-story>`,
`<dregg-descent>`, `<dregg-sprite>`, and the composition pair `<dregg-embed>`/`<dregg-transclude>`
register from the same content script (`extension/src/content.ts`). Note the delivery split: the
plaintext *detector* pattern covers `poll` only (`detect.ts`); the other elements upgrade
author-placed tags, not scanned prose.

## 9. Build status

1. **BUILT — `<dregg-poll>` the thin-view element** (`extension/src/elements/dregg-poll.ts`):
   closed shadow root held in a module-private `WeakMap` (never on the instance), light-DOM
   fallback, shadow-scoped click wire, honest trust badge, fail-closed render — over the committed
   `PollWorld` (`wasm/src/bindings_card.rs:1238`, the real `collective-choice` engine's shape as
   an in-tab world; a second click is a genuine double-vote its nullifier refuses).
2. **BUILT — the background port + resolver** (`extension/src/port.ts`:
   `resolve`/`render`/`fire`/`verify`, every response tiered, custody routed through
   `confirm-intent`; `extension/src/netlayer.ts`: the real resolver — `blake3(content) == addr`
   gate, serve-receipt membership, receipt-stream root recompute, committee-anchored quorum, each
   fail-closed). The background wires `netlayerResolveObject` when a node URL is configured;
   `defaultResolveObject` (an FNV addr→shape derivation in `port.ts`) is the fixture/test
   stand-in only.
3. **BUILT — the detector** (`extension/src/detect.ts`): MutationObserver, canonical+mirror
   patterns, idempotent (`data-dregg-upgraded`, keyed by content-addr), per-origin default-deny
   (`dregg_upgrade_origins`), shortener adapter as the only platform-specific shim.
4. **BUILT — the mirror-form server view** (tier `server`): `dregg-mirror/` — resolve a content
   address (full, or an unambiguous git-style hex prefix), run the SAME four-gate ladder
   `netlayer.ts` runs (`dregg-mirror/src/object.rs`, mirrored gate for gate), and render the
   object through the SAME `deos-view` web renderer every other glass paints with. The URI
   grammar is a faithful Rust mirror of `port.ts`, never a second parser
   (`dregg-mirror/src/uri.rs`). Fail-closed throughout: an unknown kind, a bad or ambiguous
   address, a hash mismatch or a failed gate renders an honest refusal page and NONE of the
   object. §5 is held in one module (`src/trust.rs`) and asserted on by the tests — the tier is a
   CONSTANT, since server-side gate passing never promotes it (the reader still checked nothing);
   the badge carries `(trust the origin)` verbatim and never the extension tier's green; the page
   prints the ladder gate by gate including the gates it SKIPPED, and hands over the canonical
   `dregg://…` string plus the way to the tier where the reader checks it themselves.
   ⚠ STILL OPEN: no public devnet serves real attested objects, so the deployed corpus is
   whatever the operator places, and with no trusted committee configured the quorum gate runs
   STRUCTURALLY (signatures counted, not cryptographically anchored) — which every page says in
   those words. Deployment shape: `deploy/mirror/`.
5. **BUILT — packaging**: MV3 manifests for Chromium (`extension/manifest.json`) and Firefox
   (`extension/manifest-firefox.json`).

*Open: whether closed-shadow blocks our own devtools panel (likely: expose a privileged inspection
channel through the background, not the page); rate/padding policy for netlayer privacy. The
canonical URI grammar is pinned in `port.ts` (`dregg://<kind>/<addr>`, addr = `b3_<hex>`); the
detector's kind registry covers `poll`.*
