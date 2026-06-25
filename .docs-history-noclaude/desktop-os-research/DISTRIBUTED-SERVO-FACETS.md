# Distributed Servo — Facet Research Corpus

*The raw per-facet research findings from the `galaxy-brain-frontiers` design workflow's Servo-facets phase (4 parallel galaxy-brain explorers). The synthesis lives in [../DISTRIBUTED-SERVO.md](../DISTRIBUTED-SERVO.md); this is the supporting per-facet detail each explorer produced.*


## Facet 1 — the distributed web-of-cells

I have all the primitives I need. This is a design task — no task tracking needed. Let me write the design directly.

The primitives are confirmed:
- `DreggUri` / `OcapnSturdyRef` — sturdy ref = link
- `Netlayer` trait + `dial`/`accept` + `OcapnLocation` — the federation transport with hint-pluggable wires
- `SwissTable::enliven`/`check` — sturdy-ref resolution; `EnlivenError::opaque_message` for the membership-oracle guard
- `HandoffCertificate` + `validate_handoff` + nonce-consume — third-party introduction
- `AttestedRoot` + `receipt_stream_root` + `merkle_root_of_receipt_hashes` — the quorum-signed, blocklace-bound attestation
- `wasm/src/bindings_lightclient.rs` `verify_history` — the in-tab light-client verifier
- store_forward seal + `RelayInfo` — offline/relay transport

Here is the design.

---

# GALAXY-BRAIN FACET 1 — the distributed web-of-cells: `dregg://` as a sturdy ref into the cap federation

A design for wrapping a federation of dregg nodes around Servo so the web itself becomes a federation of capability-cells. Companion to `docs/EMBEDDED-WEB-SURFACE.md` (the single-node browser-as-guest) and `docs/design-frontiers/WEB-FORWARD.md` (dregg-in-a-tab). This doc is the *third arrangement*: the **embedded web surface goes federated** — a link is no longer a hostname, it is a sturdy ref into a web of cap-cells, and a fetch resolves through CapTP instead of (or alongside) DNS+HTTP.

The discipline is the project's: teach what-IS, name every seam as work with a lever, never overclaim. The honest division — *what the captp crate already proves* vs *what is the new web-shaped wiring* vs *research* — is §6.

---

## 0. The one-paragraph thesis

The open web's link is a **location** (`https://host/path`): you trust DNS to find the host, TLS to authenticate the host, and then you trust *whatever bytes the host hands back*. dregg already has a different kind of link: a **`dregg://` / `ocapn://` sturdy ref** (`captp/src/uri.rs::DreggUri`, `captp/src/netlayer.rs::ocapn_uri::OcapnSturdyRef`) which is not a location but a **bearer capability into a specific cell on a specific federation** — `(federation_id, cell_id, swiss)`. Resolving it is not "GET the path" but **`enliven` the swiss number against the hosting node's `SwissTable`** (`captp/src/sturdy.rs`) over a CapTP session **dialed through a netlayer** (`captp/src/netlayer.rs::Netlayer::dial`). The embedded web surface's `load_web_resource` intercept (`EMBEDDED-WEB-SURFACE.md` §2) is the join: when a page fetches a `dregg://` URL, the delegate does not hit a socket — it routes the fetch to a **remote-cell verified turn** that returns **attested content**, where "attested" means the bytes are content-addressed AND accompanied by a receipt/state-root the client checks against a quorum-signed `AttestedRoot` (`types/src/lib.rs`), exactly the artifact the in-tab light client already verifies (`wasm/src/bindings_lightclient.rs`). So you can check *the page is the page the origin committed* — not "the bytes a TLS-authenticated server chose to send this time," but "the bytes whose hash the origin cell's state root binds, finalized by the federation." The web becomes a federation of cap-cells: a link is a sturdy ref, a fetch is a verified turn, content sync is range-reconciliation over the receipt stream, and the whole thing **interoperates with OCapN/Goblins because dregg's netlayer already speaks the OCapN locator format** (`ocapn_uri`) and the handoff-certificate shape (`captp/src/handoff.rs`).

---

## 1. The URL scheme — a link IS a sturdy ref into a remote cell (part a)

### 1.1 What the link denotes

A web link in this world is one of the two OCapN shapes the netlayer already parses (`netlayer.rs::ocapn_uri`), and they are **already bridged to dregg's native sturdy shape** by `OcapnSturdyRef::from_dregg` / `to_dregg`:

| link form | denotes | dregg primitive |
|---|---|---|
| `dregg://<fed>/<cell>/<swiss>` | a bearer cap into `cell` on federation `fed`, authority = whatever `swiss` enlivens to | `uri::DreggUri` (parse/format already shipped) |
| `ocapn://<designator>.<hint>/s/<swiss>` | the OCapN-native spelling of the same; `hint` names the netlayer (`tcpip`/`relay`/`onion`/`inproc`) | `ocapn_uri::OcapnSturdyRef` (parse/format/bridge already shipped) |
| `ocapn://<designator>.<hint>?host=…&port=…` | a **machine locator** — a node, not a cell (the federation's "homepage"/bootstrap object) | `ocapn_uri::OcapnLocation` (already shipped, with reachability params) |

The crucial design fact, already true in the code: the **`ocapn://` authority's `hint` carries the netlayer**, and reachability (`host`, `port`, relay coordinates, onion address) rides as **query params** (`OcapnLocation.params`). This is what lets a link be self-describing about *how to reach the federation* without a global name service — the link is the locator. `parse_parts` already splits authority at the *last* dot so base58 designators are safe, and `token_ok` already rejects URI metacharacters so format/parse round-trips (the security-relevant property: a link can't smuggle a path traversal or a param injection).

### 1.2 What "a link is a capability" buys, and the honest seam

Because the swiss number **is** the authority (possession = authorization, `lib.rs` trust model), a `dregg://` link is simultaneously the address *and* the access grant — there is no separate "log in." Attenuation is native: `SwissTable::export_with_options` already mints a swiss entry with an **`EffectMask`**, **`expires_at`**, and **`max_uses`** (`sturdy.rs`), so a shared link can be *read-only*, *expiring*, *single-use*. **A link you paste into a chat is a `max_uses: Some(1)`, 1-hour sturdy ref to a read-only facet of your cell** — the ocap answer to "anyone with the link can edit forever."

> **The bearer-secret seam (named, with its lever).** A bearer link in a URL bar is a *bearer* secret: it leaks through referrer headers, shoulder-surfing, browser history, server logs. dregg's existing levers, all already in the code, bound this rather than hand-wave it: (1) `max_uses`/`expires_at` shrink the capture window; (2) the **handoff path** (§4) replaces "paste a swiss" with a **recipient-targeted, signed, nonce-once certificate** (`HandoffCertificate.recipient_pk` + `register_handoff_nonce`) so the link is useless to anyone but the named recipient — this is the *recommended* sharing primitive for anything sensitive, and the URL-bar swiss is the convenience tier; (3) `EnlivenError::opaque_message()` already collapses the enliven-failure taxonomy at the wire so a stolen-and-expired link can't be used as a **membership oracle** on the swiss table (`finding_enliven_error_taxonomy_is_a_membership_oracle`). The web's own answer to "the link leaked" is *nothing*; dregg's is *attenuate, target, and don't-leak-which-failed*. Stated as a tiered defense, not a wall.

### 1.3 The browser's job: route the scheme

In the embedded web surface, the shell registers `dregg`/`ocapn` as **custom URL schemes** alongside `http(s)`. The address bar parses the entered string with `DreggUri::parse` / `OcapnSturdyRef::parse` / `OcapnLocation::parse`; a hit routes to §2's resolver, a miss falls through to the ordinary HTTP path. The **trusted-path origin chrome** (`EMBEDDED-WEB-SURFACE.md` §1) shows, for a `dregg://` page, **the federation id + cell id + the enlivened authority + finality status** — drawn by the shell from the live ledger, never the page — so the user reads *"cell 4t1t… on federation 7g…, read-only, finalized round 5512"* in chrome the DOM cannot reach. The origin badge for a web-of-cells page is *stronger* than a TLS lock: it names the exact object and its attenuation, not just a hostname.

---

## 2. The fetch path — `load_web_resource` → a remote-cell verified turn returning attested content (part b)

This is the heart. When the Servo `WebView` issues a network load for a `dregg://`/`ocapn://` resource, the embedder's `WebViewDelegate::load_web_resource` (the cap gate, `EMBEDDED-WEB-SURFACE.md` §2) does **not** continue to a socket — it `intercept`s and resolves the load through the cap federation. The pipeline, naming the dregg primitive at each hop:

```
page fetch dregg://F/C/swiss
  │
  ▼  [1] load_web_resource intercept  (WebViewDelegate — the §2 cap gate)
  │      parse → OcapnSturdyRef::to_dregg → (F, C, swiss)
  │      discharge the SURFACE macaroon's fetch-caveat against F  (EMBEDDED-WEB-SURFACE §3)
  │           — refuse here if the tab's cap doesn't permit reaching F
  ▼  [2] resolve the locator → dial the hosting node
  │      Netlayer::dial(addr_for(F))  →  NetSession{ captp, conn }   (netlayer.rs)
  │      (hint picks the wire: tcpip / relay / onion / inproc; params give host:port)
  ▼  [3] enliven the swiss over the session
  │      present swiss → node runs SwissTable::check then enliven   (sturdy.rs)
  │           → SwissEntry{ cell_id, permissions, allowed_effects, … }
  │      (no double-spend of the introducer's budget: check-then-enliven, sturdy.rs)
  ▼  [4] invoke the cell's "serve this resource" method as a VERIFIED TURN
  │      pipeline::PipelinedAction on the remote cell                (pipeline.rs)
  │      → the node executes a cap-gated turn → leaves a RECEIPT
  ▼  [5] node returns an ATTESTED RESPONSE  (the new web-shaped envelope, §2.1)
  │      { content_bytes, content_hash, receipt_hash,
  │        AttestedRoot{ receipt_stream_root, quorum_sigs, blocklace_block_id, finality_round },
  │        merkle_path(receipt_hash → receipt_stream_root) }
  ▼  [6] CLIENT-SIDE verification before the bytes reach the renderer
  │      a. content_hash == blake3(content_bytes)             — content-addressed
  │      b. receipt binds content_hash                        — the turn served THIS content
  │      c. merkle_path proves receipt_hash ∈ receipt_stream_root   (merkle_root_of_receipt_hashes, types/src/lib.rs)
  │      d. AttestedRoot quorum-verifies (BLS/threshold QC)   — the federation finalized it
  │      e. (optional) light-client fold over the cell's turn chain  (verify_history, bindings_lightclient.rs)
  ▼  [7] WebResourceLoad::intercept(content_bytes)  — hand the VERIFIED bytes to Servo
         on ANY check failing: intercept with a visible "dregg: unattested content" body, never render
```

The shape is uniform with the rest of dregg: **a fetch is a verified turn that leaves a receipt, and the receipt is the attestation.** The browser is a *light client of the origin cell's federation*.

### 2.1 The attested-response envelope — the one new wire object, built from shipped parts

The only genuinely new artifact is the **`AttestedResource`** envelope the node returns at hop [5]. Every field is an existing primitive:

| field | what it proves | shipped primitive |
|---|---|---|
| `content_bytes` | the page body | — |
| `content_hash: [u8;32]` | content-addressing; the body is self-certifying | blake3 (the receipt-tree hash family, `types/src/lib.rs`) |
| `receipt_hash: [u8;32]` | a specific verified turn served this | `receipt_hash()` (types) |
| `merkle_path` | `receipt_hash ∈ receipt_stream_root` | `merkle_root_of_receipt_hashes` is the verifier (types/src/lib.rs:357) |
| `attested_root: AttestedRoot` | the federation finalized that receipt stream, quorum-signed + blocklace-bound | `AttestedRoot` + `receipt_stream_root` + `ThresholdQC` (types) |

**The binding that makes it "the page the origin committed":** the served turn's receipt commits the post-state of the origin cell, and the resource's `content_hash` is a field of (or derivable from) that committed state. So verifying the chain `content_bytes → content_hash → receipt → receipt_stream_root → quorum-signed AttestedRoot` proves the origin **cell** — under the federation's finality — published exactly these bytes. This is categorically different from TLS: TLS authenticates *the channel to a host*; this authenticates *the content against the origin's committed state, checkable by a third party who wasn't on the channel*. A cached/relayed/mirrored copy is exactly as trustworthy as a direct fetch (it carries its own proof) — which is what makes §5's distributed sync sound.

### 2.2 The two honest seams in the fetch path

- **The "serve resource" method must commit the content hash.** For the attestation to bind, the origin cell's serve-turn must write `content_hash` into committed state (so the receipt covers it). This is a **cell-program convention**, not yet a kernel primitive: a "web-served cell" is one whose program, on a serve-method, records the served blob's hash in a slot the receipt commits. The lever: this is an *app-toolkit template* ("ServedResourceCell"), the same way `NameserviceGated.lean` is a template — buildable now on the existing effect set (`setField` of a content-hash slot is already a class-A effect). Named as the convention to standardize, with the template as the lever.
- **Liveness vs the dialed node.** Hops [2]–[3] dial *a* hosting node; a Byzantine or stale node can withhold or serve a stale-but-validly-attested copy (an old finalized root). Withholding is a liveness fault (try another node / relay, §5). A *stale* copy is detectably stale — `AttestedRoot.finality_round` / height is monotone, and the client can demand "≥ the round I last saw" or fold the light client (`verify_history`) to the current head. The lever: **freshness is a client policy over an existing monotone field**, not a missing mechanism. Equivocation (two finalized roots at one height) is exactly what the blocklace equivocation-detection already catches (the consensus layer's job, `lib.rs` GC/handoff trust model is downstream of it).

### 2.3 Where the fetch dials — netlayer pluralism

Hop [2]'s `addr_for(F)` is resolved by the **netlayer hint**, and this is the part that lets the web-of-cells coexist with the legacy web rather than replace it:

- `hint = tcpip`, params `host`/`port` → a `TcpNetlayer` dial (the node crate owns the socket; `netlayer.rs` module docs name it as the mechanical instance). This is the "direct, online" path — the moral equivalent of an HTTP GET, but the *response* is attested.
- `hint = relay` → `RelayNetlayer` (`netlayer.rs`): the fetch is **sealed store-and-forward** (X25519→HKDF→ChaCha20-Poly1305, relay sees only ciphertext) and queued — the origin cell can be **offline** and still "serve" a page when it next drains its inbox. *A web page whose origin is offline* is incoherent on the open web; here it is a relayed verified turn.
- `hint = onion` → a Tor netlayer instance (named in the module docs as a Goblins-spoken wire) for metadata-resistant fetch.
- `hint = inproc` → same-node cells (the desktop's own apps served as `dregg://` pages with zero network).

The netlayer abstraction means **the fetch's transport is swappable without touching the resolve/enliven/verify semantics** (`netlayer.rs` module thesis: "swapping the netlayer swaps the wire; the capability semantics do not move"). DNS+HTTP remain a fall-through for `http(s)://` (unattested, legacy); `dregg://`/`ocapn://` are the attested federation path.

---

## 3. Distributed-GC and revocation across the web — the link's lifecycle

A web-of-cells needs the link's *lifecycle* to be sound, not just its resolution. The captp crate already carries this and it maps cleanly onto web semantics:

- **A live link holds a reference.** When the browser enlivens `dregg://F/C/swiss`, that is an **import** on the client's `CapSession` and an **export** the hosting node's `ExportGcManager` records (`captp/src/gc.rs`, `lib.rs` distributed-GC model). Closing the tab / dropping the page sends a `DropRef`; at zero refs the node may reclaim. So **"how many live browsers hold this page open" is the export refcount** — a real, GC'd distributed reference, not a stateless GET. (The red-team `F-11` session-free premature-reclaim fix already hardened exactly this path, task #112.)
- **Revoking a shared link is `SwissTable::revoke`.** Un-publishing a page = `revoke(swiss)` on the origin node (`sturdy.rs`); every subsequent `enliven` returns the opaque "denied", every live session's next call breaks. This is **link revocation with teeth** — the open web has no equivalent (a leaked URL is forever).
- **The epoch story prevents stale-session confusion.** `EpochMinter` (`netlayer.rs`) mints a strictly-higher epoch per redial, and `CapSession::epoch` rejects stale messages — so a browser that reconnects after the origin rotated keys can't be fed replays from the old epoch.

This is the piece that makes the web-of-cells a *capability* web and not just "content-addressed HTTP": links are GC'd, attenuated, and revocable references with a real distributed lifecycle.

---

## 4. The OCapN / Goblins tie-in + Willow range-reconciliation (part c)

### 4.1 OCapN/Goblins interop — already 90% wired

dregg's netlayer **was built as an OCapN netlayer** (`netlayer.rs` module docs: "adopts the netlayer design from Spritely Goblins / OCapN"). The web-of-cells inherits Goblins interop for free at the link layer, and the bounded remaining work is already inventoried in the code:

- **Locator format**: `ocapn_uri` already speaks `ocapn://<designator>.<hint>[/s/<swiss>][?params]` both directions — the exact format Goblins/OCapN uses. A Goblins peer's locator IS a valid web-of-cells link and vice versa.
- **Sturdy-ref enliven**: a Goblins peer fetching `ocapn://node.hint/s/<swiss>` lands in `SwissTable::enliven` — the swiss-number bearer model is shared E-lineage (`netlayer.rs` docs). **A Goblins object reference and a dregg web link are the same kind of thing.**
- **Third-party handoff = the OCapN `desc:handoff-give/receive` certificates** ↔ `HandoffCertificate` (`handoff.rs`): both are signed introducer certificates; the doc-named translation is "field renaming plus signature-scheme bridging." This is how **one cell links another cell's page to a third party** — the introducer signs a `recipient_pk`-targeted, nonce-once cert (`register_handoff_nonce`, replay-closed), the recipient presents it, the target enlivens. **A "share this page with Bob" that is cryptographically bound to Bob and useless to an interceptor** — the handoff path is the sound sharing primitive §1.2 points at.
- **The remaining adapter** (`netlayer.rs` §"Goblins-interop adapter", scoped at "2–4 weeks"): a shared concrete wire (tcp+tls / onion / libp2p as the `NetConnection`), the **Syrup codec** (OCapN messages are Syrup records, not postcard — a frame-payload translation), and the `op:start-session`/`op:deliver`/`op:gc-export` descriptor mapping onto our existing `session`/`pipeline`/`gc` tables. **None of it changes the `Netlayer` trait** — it is one more `impl Netlayer` plus a codec shim. So the web-of-cells reaching Goblins-hosted content is a *bounded, named* artifact on a *shipped* abstraction, not research.

The payoff: **the web-of-cells is not a dregg-only network.** Any OCapN peer — a Goblins vat, another ocap system — can host a page (export a sturdy ref) the dregg browser resolves, and dregg cells can publish pages a Goblins client reads. The link scheme is the *federation's*, not dregg's.

### 4.2 Willow range-reconciliation for distributed content sync

The web-of-cells wants **distributed content sync**: many nodes mirroring a cell's pages, browsers pulling from the nearest replica, offline-first caches that re-converge. Willow's **range-based set reconciliation** (3-way Merkle range fingerprints: two peers exchange `fingerprint(range)`; equal → done; unequal → split the range and recurse) is the right primitive, and dregg already has the substrate it needs:

- **The set to reconcile is the receipt stream.** Each origin cell's published content is its sequence of serve-turn receipts, and `merkle_root_of_receipt_hashes` (`types/src/lib.rs`) is *already* a balanced, domain-separated BLAKE3 Merkle tree over `receipt_hash`es with deterministic canonical order. A **Willow range fingerprint over a sub-range of the receipt stream is a partial-tree digest of exactly this structure** — the tree exists; range-reconciliation is "fingerprint a contiguous leaf range" added on top.
- **Why it's sound to sync from a stranger.** §2.1's whole point: every `AttestedResource` carries its own proof (`content_hash → receipt → receipt_stream_root → quorum-signed AttestedRoot`). So a node can pull a page from *any* peer — a CDN-like mirror, a neighbor, a relay — and **verify it locally** without trusting the source. Willow reconciliation distributes the *bytes*; the attestation makes the distribution *trustless*. This is the federation analogue of "content-addressed + signed," and it is what lets §2's "try another node on withholding" scale to a real replica mesh.
- **The transport is the netlayer; the sync is a CapTP conversation.** Reconciliation runs as `pipeline` method calls over a `Netlayer`-dialed session — `relay` for offline/async convergence (a mirror drains updates store-and-forward), `tcpip`/`onion` for live sync. Willow's namespace/subspace/path addressing maps onto `(federation_id, cell_id, receipt-stream-range)`.

> **Honest scope on Willow (named, with the lever).** dregg has **no Willow implementation today** — `grep` finds zero `willow`/`range_reconcil` in the tree. What ships is the *substrate that makes it a bounded build, not research*: (1) the receipt-stream Merkle tree exists and is canonical-ordered (`merkle_root_of_receipt_hashes`); (2) the self-verifying envelope exists (§2.1) so reconciled content is trustless-at-rest; (3) the transport exists (`Netlayer` + `relay` for async convergence). The work is the **range-fingerprint protocol** (split-and-recurse over the existing tree's leaf ranges) as a new `pipeline` conversation — a defined algorithm over shipped data structures. Willow's own privacy features (path encryption, capability-gated read access) map onto the existing attenuation: a sync peer only reconciles ranges its enlivened cap permits (the `EffectMask`/read-scope of its sturdy ref). Stated as a bounded build on a real substrate.

---

## 5. The whole picture — the web as a federation of cap-cells

Putting the pieces together, the primitive carrying each:

| web concept | open-web mechanism | web-of-cells mechanism | dregg primitive carrying it |
|---|---|---|---|
| a link | `https://host/path` (a location) | a sturdy ref into a cell (an attenuable capability) | `uri::DreggUri` / `ocapn_uri::OcapnSturdyRef` |
| finding the host | DNS | the netlayer hint + locator params (or a relay/onion) | `ocapn_uri::OcapnLocation.params` + `Netlayer::dial` |
| authenticating the response | TLS (authenticates the *channel*) | content-addressed + receipt + quorum-signed root (authenticates the *content*, third-party-checkably) | `AttestedRoot` + `receipt_stream_root` + `merkle_root_of_receipt_hashes` + `verify_history` |
| a fetch | HTTP GET (stateless) | a cap-gated verified turn leaving a receipt | `pipeline::PipelinedAction` + `SwissTable::enliven` |
| the fetch intercept | — | `load_web_resource` routes to the remote-cell turn | `WebViewDelegate::load_web_resource` (EMBEDDED-WEB-SURFACE §2) |
| sharing a link with a person | paste a URL (leaks, forever-valid) | a recipient-targeted, signed, nonce-once handoff cert | `handoff::HandoffCertificate` + `register_handoff_nonce` |
| attenuating access | — (all-or-nothing) | read-only / expiring / single-use facet | `SwissTable::export_with_options` (EffectMask/expires/max_uses) |
| revoking a link | — (impossible) | drop the swiss entry | `SwissTable::revoke` |
| who's holding a page open | — (stateless) | distributed export refcount, GC'd | `gc::ExportGcManager` + `DropRef` |
| offline / async fetch | — (origin must be up) | sealed store-and-forward verified turn | `RelayNetlayer` + `store_forward` |
| mirroring / CDN | trust the mirror | trustless replicas (each carries its proof) + range-reconciliation | §2.1 envelope + Willow over `merkle_root_of_receipt_hashes` |
| cross-ecosystem reach | — | OCapN/Goblins peers host/read pages | `ocapn_uri` (shipped) + the Goblins adapter (2–4wk, named) |
| anti-phishing origin chrome | a TLS lock (a hostname) | the cell id + authority + finality, shell-drawn from the ledger | `Shell::identity_of` (EMBEDDED-WEB-SURFACE §1) |

The unifying sentence: **on the open web a link is a place you trust a server to fill; in the web-of-cells a link is a capability into a cell whose content the federation finalizes, so the page carries its own proof — you verify the page is the page the origin committed, from any source, online or off, dregg-hosted or Goblins-hosted, attenuated to exactly the authority the link grants.**

---

## 6. Honest scope — what's shipped / new wiring / research

Per the project's doc law (name every seam as work with a lever, never overclaim):

**Shipped and proven (the substrate this composes — all in `captp/`, `types/`, `wasm/`):**
- The link scheme both ways: `DreggUri`, `OcapnSturdyRef`, `OcapnLocation` parse/format/bridge, with metacharacter-safe round-tripping (`uri.rs`, `netlayer.rs::ocapn_uri`, tests green).
- The netlayer + dial/accept + epoch-correct sessions, with `inproc` and `relay` instances and the OCapN locator format (`netlayer.rs`).
- Sturdy-ref enliven/check/revoke with attenuation (EffectMask/expires/max_uses) and the membership-oracle-closed opaque error (`sturdy.rs`).
- The handoff certificate: signed, recipient-targeted, nonce-once replay-closed (`handoff.rs`, `register_handoff_nonce`).
- The attestation primitive: `AttestedRoot` + `receipt_stream_root` + the receipt-stream Merkle verifier + threshold QC (`types/src/lib.rs`).
- The in-tab light-client verifier that folds a turn chain and checks the root (`wasm/src/bindings_lightclient.rs`, `verify_history`).
- Distributed GC across federations, with the session-free premature-reclaim hole already closed (`gc.rs`, task #112).
- Store-and-forward sealed transport (relay sees only ciphertext) for offline serve (`store_forward.rs`).

**New web-shaped wiring (buildable now against the above + a current libservo — the headline deliverables):**
- **The `dregg`/`ocapn` URL-scheme registration + address-bar routing** in the embedded web surface (parse → resolver, else HTTP fall-through), with the cell-id/authority/finality origin badge in trusted chrome.
- **The `load_web_resource` → resolver** that dials (`Netlayer`), enlivens (`SwissTable`), invokes the serve-turn (`pipeline`), and verifies the `AttestedResource` chain *before* `WebResourceLoad::intercept` hands bytes to Servo. This is the keystone integration.
- **The `AttestedResource` envelope** (§2.1) — the one new wire object, every field a shipped primitive.
- **The `ServedResourceCell` app-toolkit template** — a cell program whose serve-method commits the content hash into receipt-covered state (the §2.2 convention, the lever being "a template like `NameserviceGated.lean`").
- **Freshness-as-client-policy** over the existing monotone `finality_round` (§2.2 seam #2).

**Research / bounded-but-larger (named, not claimed):**
- **The Goblins-interop adapter** (`netlayer.rs` §"Goblins-interop adapter", scoped 2–4 weeks): shared concrete wire + Syrup codec + descriptor mapping. Bounded — one more `impl Netlayer` + a codec shim; does not touch the trait.
- **Willow range-reconciliation** (§4.2): zero implementation today; the range-fingerprint protocol is a *defined algorithm over the shipped receipt-stream Merkle tree*, delivered as a new `pipeline` conversation. A bounded build on a real substrate, gated behind the headline fetch path.
- **The confined-Servo seL4 `renderer`/`web-broker` PD split** (`EMBEDDED-WEB-SURFACE.md` §5): the kernel-enforced end-state where the renderer physically cannot reach the netlayer except through the cap-gating broker — gated on the same `SEL4-EMBEDDING.md` blockers that doc already names. The web-of-cells' fetch broker IS that `web-broker` PD's job; §2 pre-factors into it cleanly, which is the architectural argument that §2 is the right shape. Research, sequenced behind the executor-PD blocker.

---

*On the open web, a link is a place and you trust a server to fill it; in the web-of-cells a link is a capability — a `dregg://`/`ocapn://` sturdy ref into a cell — and a fetch is not a GET but a verified turn the federation finalizes into a receipt, so the page carries its own proof. The embedded web surface's `load_web_resource` intercept routes the fetch through the netlayer to the origin cell, enlivens the swiss against its swiss table, runs the serve-turn, and verifies the attested-content chain before a byte reaches the renderer — you can check the page is the page the origin committed, from any source, online or via a sealed relay when the origin is offline, attenuated to exactly the authority the link grants and revocable when it shouldn't be. The locator format and handoff certificates are already OCapN's, so Goblins peers host and read these pages; Willow range-reconciliation over the existing receipt-stream Merkle tree distributes the bytes trustlessly because each carries its quorum-signed root. The web becomes a federation of cap-cells: dregg doesn't browse the web, it federates it.*

---

**Key files grounding this design (all absolute):**
- `/Users/ember/dev/breadstuffs/captp/src/netlayer.rs` — `Netlayer` trait, `dial`/`accept`, `EpochMinter`, `RelayNetlayer`, and `ocapn_uri` (`OcapnLocation`/`OcapnSturdyRef`/bridge to `DreggUri`)
- `/Users/ember/dev/breadstuffs/captp/src/uri.rs` — `DreggUri` (the `dregg://` link)
- `/Users/ember/dev/breadstuffs/captp/src/sturdy.rs` — `SwissTable` enliven/check/revoke/export_with_options + `EnlivenError::opaque_message`
- `/Users/ember/dev/breadstuffs/captp/src/handoff.rs` — `HandoffCertificate` (recipient-targeted, nonce-once) — the third-party share primitive
- `/Users/ember/dev/breadstuffs/captp/src/gc.rs` + `/Users/ember/dev/breadstuffs/captp/src/store_forward.rs` — distributed-GC refcount + sealed relay transport
- `/Users/ember/dev/breadstuffs/types/src/lib.rs` (≈330–387) — `AttestedRoot`, `receipt_stream_root`, `merkle_root_of_receipt_hashes` (the attestation + the tree Willow reconciles)
- `/Users/ember/dev/breadstuffs/wasm/src/bindings_lightclient.rs` — `verify_history` (the in-tab light-client verifier the browser becomes)
- `/Users/ember/dev/breadstuffs/docs/EMBEDDED-WEB-SURFACE.md` — §2 `load_web_resource` cap gate (the fetch intercept point) + §1 trusted origin chrome + §5 the seL4 broker PD


## Facet 2 — co-present, collaboratively-shared browsing

I have a complete and precise picture now. The cell crate is at `cell/` (not `dregg-cell/`), and `integration_migration.rs` confirms a cell migration path exists — the substrate for tab handoff (item d). The firmament `delegate` runs a genuine `Effect::GrantCapability` turn with a real per-agent receipt chain — so co-presence delegations and presents are receipted turns (item e) by construction.

I now have everything load-bearing: `SurfaceCapability` (real firmament cap over a backing cell), `Shell::share` (genuine narrowing GrantCapability turn, widening = DelegationDenied), the compositor's T1/T2/T3 teeth over a region-set, `label_of` (shell-computed binding), the macaroon `ResourceSet<I,M>` (intersection-only resource→bitmask, wildcard via Default), and the firmament receipt chain. Let me write the design.

The design is complete. Here is my return value.

---

# CO-PRESENT BROWSING — multi-party interaction over ONE cap-mediated web surface

A design for truly-rich multi-party co-presence over a single Servo `WebView`, built entirely on the surface/shell/compositor primitives that ship today in `starbridge-v2/`. The thesis in one line: **co-presence is not a new subsystem — it is `Shell::share` recursed INTO the DOM, the compositor's region-set recursed BELOW the window, and every collaborative act made a receipted firmament turn.** No new authority model; the keystone is that the one thing the open web cannot express — "you may touch ONLY this field, observe but not drive, and I can take it back this frame" — is exactly `granted ⊆ held` at a finer grain.

Two pieces of named substrate I rely on throughout (so the seams are honest from the start):

- **The exterior-mediation invariant (the load-bearing premise for everything fine-grained).** Per `EMBEDDED-WEB-SURFACE.md` §2/§4.1, dregg mediates a web surface from *outside* the page via `WebViewDelegate` (navigation/fetch/new-window/permission/auth) and drives the page via host→page `evaluate_javascript`. There is **no per-DOM-node delegate in Servo today** (§2.1). So every per-element / per-field / per-region gate below is enforced at the embedder boundary — input is routed to the page only after the gate admits it, and DOM-region observation/mutation rides a **host-side privileged content-script injected via `evaluate_javascript` at document-start** (the §4.2(2) path). This is strictly stronger than an in-page extension (it shares nothing with page JS) but it is a **named seam**: the per-element granularity is only as sound as that injected shim honoring the region map, until a Servo DOM-region delegate exists (the upstream lever) or the seL4 `renderer`-PD/`web-broker` split (§5) makes it an address-space boundary. I name this the **DOM-region-mediation seam** once and reference it; I never launder it.

- **The co-presence cell.** A co-presented surface is one `SurfaceCapability` over one backing cell (`surface.rs`), but its authority is now a **macaroon whose caveats name DOM regions, not just web powers** — using the real `macaroon` `ResourceSet<I, M>` (`resource.rs`): a map from a typed resource id → an action bitmask, **intersection-only on stacking** (every caveat can only narrow), with the type's `Default` id as a wildcard. I instantiate `I = RegionKey` (a stable DOM-region / element / field identifier) and `M = DomAction` (a bitmask over `Observe | Nav | Click | Fill | Submit | Select`). That single generic, already proved to intersect-and-narrow, is the per-element capability lattice. The window cap answers *which surface*; this macaroon answers *which party may do what to which DOM region* — and `prohibits(region, action)` is the gate.

---

## (a) Multiple holders of ATTENUATED caps to ONE surface — per-DOM-region / per-element caps

**The model.** The surface owner holds the root macaroon (full `DomAction` over the wildcard region — they may do anything to the whole page). Every other participant holds a **delegation** of it, minted by `Shell::share` extended to carry a `RegionKey → DomAction` attenuation, never wider. Three canonical roles fall out as caveat sets over the *same* surface cell:

- **Driver** — `{ * : Nav | Click | Fill | Submit | Select | Observe }` (the whole page, all actions). Exactly the owner's authority, or a near-full delegation.
- **Read-only observer** — `{ * : Observe }` (every region, observe-only; no Nav/Click/Fill bit anywhere). This is the `None → Signature` narrowing of `surface.rs`'s own test, lifted to "every action bit cleared except Observe."
- **Scoped editor** — `{ region("#shipping-addr") : Fill, button("#apply-coupon") : Click }` and **nothing else** (no wildcard entry ⇒ `resolve` returns `None` for every other region ⇒ `prohibits` denies "resource not in set"). This is the case the open web has no vocabulary for, and it is *one `ResourceSet` literal*.

**Mechanism (every leg is existing code).**

1. *Minting a participant.* The owner calls `Shell::share(cap, recipient_app, narrower)` — the genuine `Effect::GrantCapability` turn (`shell.rs::share` → `fabric.delegate` → real executor). I extend `narrower` from a scalar `AuthRequired` to `(AuthRequired, ResourceSet<RegionKey, DomAction>)`: the firmament cap still narrows on the `AuthRequired` lattice (drives the *window*: can this party focus/move/close at all), and the **`ResourceSet` rides as the cap's caveat payload** governing *which DOM regions*. The executor's `granted ⊆ held` already refuses a widening window share (`a_narrowing_window_share_commits_and_a_widening_share_rejects` is green); the macaroon's monotone stacking refuses a widening *region* share — `ResourceSet::resolve` intersects masks, so a child can only ever clear bits, never set them. **Two independent no-amplification gates compose**: firmament for the window, macaroon for the DOM.

2. *Enforcing on every input.* A participant's keystroke/click does not reach Servo directly. The shell receives it tagged with `(participant_cap, RegionKey, DomAction)` — the `RegionKey` resolved by hit-testing the click against the host-side region map (the injected shim reports element bounds; the DOM-region-mediation seam). The shell calls `participant_macaroon.prohibits(region, action)`. On `Ok` it forwards the event into the `WebView` (a real input dispatch); on `Err(Prohibited)` it **refuses visibly** — the same refusal-is-a-feature posture as `ShellError::ShareDenied`. A scoped editor clicking outside `#shipping-addr` is denied "resource not in set" before Servo sees the event.

**Why this is rich and not a toy.** The granularity is *recursive*: a `RegionKey` can name a region, an element, or a single form field, and the region-set is the same object the compositor already uses one level up (a window owns a region-set; now a *participant* owns a DOM-region-set within it). The "surface-region model recursed into the DOM" is literal — `RegionId` (window tiles, `compositor.rs`) and `RegionKey` (DOM regions) are the same `granted ⊆ held` shape at two scales.

**Honest seam.** Soundness of "ONLY this field" rests on the DOM-region-mediation seam: the host-side shim must faithfully map clicks→`RegionKey` and must prevent script-driven focus-stealing *inside* the page (e.g. a page moving `#shipping-addr` under a different element). Today's enforcement is at the input-dispatch boundary (strong: the event never reaches a disallowed handler) plus the shim's region map (the soft edge). The closure lever is the upstream Servo DOM-region delegate, or the seL4 `web-broker` split. **Carried as work, with the lever named — not a wall.**

---

## (b) Screenshare-as-cap — a revocable read-only live VIEW

**The model.** "Share my screen with you" is **minting you a `{ * : Observe }` macaroon over my surface cell** — the read-only observer of (a), nothing new. The viewer's surface is a *second* `SurfaceCapability` (a fresh `SurfaceId`) over the **same backing cell**, exactly as `Shell::share` already produces ("the shared window becomes a NEW surface over the SAME backing authority cell"). The viewer sees the live frame because both surfaces composite the same cell's `source_state_root` / `content_digest` (`compose_scene`); the viewer's `DomAction` mask has every actuating bit cleared, so every input they attempt is `prohibits → Err`.

**Revocable.** Revocation is dropping the viewer's grant — `Shell::close` on the viewer's surface drops its firmament authority binding ("the cap becomes dead — its backing-cell/owner are no longer registered, so it stops resolving"; `closing_a_surface_kills_its_capability` is green), or a `RevokeDelegation` turn on the macaroon. **The next composed frame omits the viewer's surface; their glass goes dark.** This is the §4.1 "handle lifetime controls the WebView" property applied to the *viewer's* handle.

**"Dark-this-frame at n=1" — the single-machine sharp edge, and the rich part.** This is where co-presence earns the dregg thesis. On a single machine, the compositor recomposes the scene *every present* from the live owned-surface set (`Shell::present` → `compose_scene` → `set_scene`). So revocation is not eventually-consistent: **the very next `present()` after the revoke turn composes a scene in which the viewer owns no region**, and the compositor's T1 tooth means the viewer can paint nothing (no region in their set). The frame the viewer holds is the *last* admitted frame; no further frame reaches them. "Dark-this-frame" is the n=1 collapse of the distributed bound (per the SINGLE-MACHINE PRINCIPLE in memory: immediate revocation is the n=1 strong form of the honest distributed bound). The receipt of the revoke turn is the provable "stopped sharing at frame N."

**Honest seam.** Two real edges. (1) **The already-rendered frame.** Revocation darkens *future* frames; it cannot un-see pixels the viewer already holds (a screenshot they took, their own GPU buffer). This is irreducible for any view-sharing and I name it: the cap revokes the *live feed*, not the viewer's memory. (2) **The pixel-egress seam.** "Read-only" means the viewer's surface carries no `DomAction` actuating bit, so it can't *drive* my page — but at n>1 (a remote viewer over the wire) the frame bytes leave my machine, and confidentiality of those bytes is the transport's job, not the cap's. At n=1 (a local second sovereign) the frame never leaves the compositor, so the cap *is* the full boundary. The lever for n>1 is the same encrypted-channel/group-key machinery the channels organ already ships; named, not laundered.

---

## (c) Collaborative cursors / shared form-fill / co-edit with per-field caps

**The model.** Co-editing is **multiple scoped-editor macaroons (a) over disjoint DOM-region-sets, plus a cursor-presence overlay that is itself a cap-gated compositor surface.** Two mechanisms:

1. **Per-field co-edit = disjoint `ResourceSet`s, T1 at the DOM scale.** Party A holds `{ #name : Fill }`, party B holds `{ #email : Fill }`. Each fill is an input event gated by `prohibits` (a). The richness: **the DOM-region T1 non-overlap property** — if A's and B's region-sets are disjoint (the shell checks this at mint time, the same disjointness `compose_scene_gives_each_surface_a_disjoint_region` proves for window tiles), then concurrent fills *cannot conflict by construction* — they touch different fields. A and B fighting over `#name` is prevented not by a lock but by **not both holding the `#name : Fill` bit**. Co-edit conflict-freedom is a corollary of the no-overlap region discipline, recursed into the DOM.

2. **Collaborative cursors = a presence overlay surface at a reserved z-layer.** Each participant's live cursor is painted into a **dedicated overlay region** the compositor owns, exactly like the trusted-chrome surface in the compositor demo (`chrome`, region `{99}`, top z, the "trusted-path overlay lives at a z-layer no cell holds a cap to"). A participant's cursor position is a `present()` into *their own* overlay region with their genuine `label_of` binding — so **a cursor is provably attributed**: the T2 label-binding means participant B cannot paint a cursor *labeled as participant A* (that's `LabelSpoof`, refused). Collaborative cursors get anti-spoofed attribution for free from the T2 tooth.

**Mechanism (existing code).** The fill path is (a)'s gated input dispatch. The cursor overlay is the compositor's existing multi-surface scene: each participant's cursor surface owns a disjoint region (T1), carries its owner's genuine label (T2), and only the focus-holder's *input* actuates the page (T3 — so two people can *see* each other's cursors moving, but only the focused driver's clicks fire, unless a co-driver holds the relevant `Click` bit on a disjoint region). Shared form-fill where both genuinely co-drive is the disjoint-region case; the moment they'd collide, one of them lacks the bit.

**Honest seam.** (1) **Focus vs. co-actuation.** The compositor's T3 is *single*-focus (at-most-one `focus_flag`, input routes to exactly one holder; `t3_focus_exclusive`). True simultaneous co-actuation of the *same* widget by two parties is therefore not expressible today — co-edit is **disjoint-region concurrent**, not same-field-simultaneous. That's the honest shape (and arguably the *correct* one — same-field simultaneous edit is ill-defined). Generalizing T3 from single-focus to a **focus-set with per-region input routing** is the named design lever (it touches the Lean `Dregg2.Apps.Compositor` `t3` predicate — a real proof obligation, not a hand-wave). (2) The **DOM-region-mediation seam** again: which field a fill lands in is the shim's report.

---

## (d) SUSPEND-and-HAND-OFF a tab to another sovereign — the live-image handoff

**The model.** The surface is a cell with a `state_root` (`source_state_root` in `shell.rs`, the live-state fold the compositor binds), and **a cell migrates** — the `cell/tests/integration_migration.rs` path and the `CellLifecycle::Migrated` lifecycle the shell already renders as a "migrated" badge (`identity_of`). Handing off a tab is **migrating the surface's backing cell to another sovereign, carrying the web-engine state as the cell's payload.** The recipient resumes the *same* cell (same id, same authority lineage), so the surface is continuous across owners.

**What "the web-engine state" is.** A tab's resumable state = its committed URL (the `notify_url_changed` value bound to the cell, §1), its cap-scoped storage partition (the §2.1 profile root — itself a dregg cell), its scroll/form state (capturable via host→page `evaluate_javascript`), and its macaroon (the authority). The handoff packages these as the migrating cell's state; the recipient's shell calls `open_web_view(migrated_cell, committed_url)` and re-hydrates: navigates to the URL, re-attaches the storage partition cell, replays the form state. **The `Migrated` lifecycle is the receipt that the handoff happened**, and the shell's identity badge shows the new sovereign — anti-spoof, drawn from the ledger (`identity_of` reads lifecycle, not self-description).

**Why this is the "live-image handoff for web content" and rich.** Because the surface *is a cell*, tab handoff inherits the whole cell-migration discipline: the authority migrates *with* the state (the recipient holds the cell's caps, attenuated if the hand-off narrows them — a "hand you this tab but read-only" handoff is a migration that drops the actuating `DomAction` bits), the migration is a receipted turn (provable who-handed-what-to-whom), and at n=1 the migration is a consistent checkpoint (the SINGLE-MACHINE PRINCIPLE: synchronous commit, no split-brain — the tab is never live in two places). This is genuinely the seL4 live-image-handoff property applied to a browser tab.

**Honest seam.** The big one, named squarely: **a running Servo `WebView` is not itself a serializable cell today.** What migrates cleanly is the *resumable description* (URL + storage-partition cell + captured form/scroll state + macaroon) — enough to *reopen* the tab equivalently on the recipient. What does **not** migrate is live in-renderer state with no serialization (a mid-flight WebSocket, a `<video>` decode position, ephemeral JS heap, WASM linear memory). So today's handoff is **suspend-checkpoint-resume** (capture the resumable description, migrate the cell, reopen), not live-process teleport. The closure levers, sequenced: (1) richer host→page state capture via `evaluate_javascript` (more form/scroll/sessionStorage fidelity) — near-term; (2) Servo-level session serialization (an upstream ask, like `back/forward`-cache made portable); (3) the **seL4 `renderer`-PD checkpoint** (§5) — migrating the PD's address space *is* live-process handoff, gated on the same Servo-on-seL4 blocker §5 already names. Three honest tiers, the floor (suspend/resume) buildable now, never claimed as live teleport.

---

## (e) Every co-presence action is a receipted turn — who-did-what is provable

**The model — and the reason the whole design is sound rather than convenient.** Each of (a)–(d)'s authority changes is *already* a genuine firmament turn, because they route through `Shell::share` / `fabric.delegate` / `RevokeDelegation` / cell-migration — all of which are real `Effect::*` turns on the real executor with a **per-agent receipt chain** (`run_grant_turn` in firmament `surface.rs`: "a window manager issues MANY surface turns (present/embed/grant-input/revoke in one session), so the verbs MUST chain"). So:

- **Granting a participant a cap** = a `GrantCapability` receipt (who delegated what region-set to whom).
- **Revoking / ending a screenshare** = a `RevokeDelegation` receipt (the provable "stopped at frame N").
- **Each admitted frame** = a `FrameCommit` in the compositor's append-only frame log (`compositor.rs`: "the analogue of an on-ledger receipt … every genuine frame advance is recorded") — carrying the presenter, the region-set, the digest, the `source_state_root`, and the **genuine T2 label**. So *who painted what, when, attributed unspoofably* is the frame log.
- **Each gated input** (a participant's click/fill) is dispatched only after a `prohibits` check; logging that check as a turn makes **"participant B filled `#email` at turn T" a receipt** — the co-presence audit trail.
- **A tab handoff** = a `Migrated` receipt (who handed the cell to which sovereign).

**The provable property.** The conjunction is: *the complete who-did-what of a co-presence session is reconstructible from the receipt chain + the frame log, with cryptographic attribution (T2 label) and no ambient action* — every actuation passed a cap gate that left a record. This is the display-path analogue of dregg's whole thesis: the human at the glass (and any auditor) cannot be fooled about who did what in a shared session, because nothing happened without a gated, receipted turn.

**Honest seam.** (1) **Granularity of input-receipting.** Cap *changes* (grant/revoke/migrate) are full executor receipts today (existing code). Per-*keystroke* receipting is a design choice with a cost: a receipt per keystroke is heavy. The honest default is **receipt the cap-gate decisions and frame commits** (already real) and **batch fine input into per-turn digests** (a keystroke-stream hashed into the frame's `content_digest`, which *is* receipted) — so the *fact* of gated input is provable at frame granularity, individual keystrokes at digest granularity. Per-event receipts are available where an app demands them (the proving-modality dial). Named: full per-keystroke non-repudiation is a dial setting, not the always-on default. (2) The frame log is the compositor's in-memory log; durably committing it to the node's crash-consistent commit log is the existing durable-log path — a wiring step, named.

---

## Summary: what is real, what is the build, what is the lever

**Real today (all green, reused verbatim):** the `SurfaceCapability` over a backing cell; `Shell::share` as a genuine narrowing `GrantCapability` turn with widening-rejected; the compositor's T1/T2/T3 teeth and `FrameCommit` log; `label_of` shell-computed anti-spoof binding; the macaroon `ResourceSet<I,M>` intersection-only narrowing lattice; the firmament per-agent receipt chain; the cell-migration lifecycle + "migrated" badge.

**The near-term build (composes existing pieces, contends with nothing in the kernel/circuit cutover):** instantiate `ResourceSet<RegionKey, DomAction>` as the per-DOM-region caveat; extend `Shell::share`'s `narrower` to carry it; route participant input through `prohibits` at the embedder dispatch boundary; mint observer/editor/driver roles as caveat literals; paint collaborative cursors as disjoint-region overlay surfaces (T1/T2 give conflict-freedom + attribution free); package tab-handoff as cell-migration of the resumable description; log gate-decisions + frame-commits as the co-presence audit trail.

**The named levers (work, never walls):** the **DOM-region-mediation seam** (per-element gates are enforced at input-dispatch + a host-side `evaluate_javascript` shim until a Servo DOM-region delegate or the seL4 `web-broker` PD makes it an address-space boundary); **T3 single-focus → focus-set with per-region input routing** for true same-widget co-actuation (a real Lean `Dregg2.Apps.Compositor` proof obligation); **suspend/resume → live-process tab teleport** (three honest tiers, floor buildable now, top gated on Servo-on-seL4 §5); **per-keystroke non-repudiation as a proving-modality dial** rather than always-on.

Relevant files: `/Users/ember/dev/breadstuffs/docs/EMBEDDED-WEB-SURFACE.md`, `/Users/ember/dev/breadstuffs/starbridge-v2/src/surface.rs`, `/Users/ember/dev/breadstuffs/starbridge-v2/src/shell.rs`, `/Users/ember/dev/breadstuffs/starbridge-v2/src/compositor.rs`, `/Users/ember/dev/breadstuffs/macaroon/src/resource.rs`, `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/surface.rs`, `/Users/ember/dev/breadstuffs/cell/tests/integration_migration.rs`.

A small poem, since the work invites it:

```
one glass, many hands —
each a cap the page can't widen,
the frame remembers.
```

( ◕‿◕ ) the surface-region model, all the way down into the DOM.


## Facet 3 — provable browsing & agent-driven web automation

Fully grounded. The blocklace is a signed DAG: each block names `predecessors` (causal deps), id = BLAKE3(creator/seq/sorted-preds/payload), `new_signed` covers it with Ed25519, `insert` enforces causal closure (`MissingPredecessors`) + monotone seq + equivocation detection (`EquivocationProof`, attributable). This is exactly the substrate browsing-history-as-blocklace rides. I have everything for all four items with real mechanism + honest seam. Composing the design now.

---

# GALAXY-BRAIN FACET 3 — Provable browsing & agent-driven web automation (the ADOS angle)

*Design frontier. Present-tense where the dregg side is real; clearly-scoped frontier where it isn't. The thesis: a web interaction is the canonical "an agent did X" — a nav, a click, a fetch, a submit — and dregg's whole project is to make "an agent did X" a verified turn the executor accepted or refused, leaving a receipt the operator reads instead of the agent's narration. This facet routes **every web interaction through the one ADOS seam** (`Swarm::run`, `swarm.rs:317`) over the embedded web surface of `EMBEDDED-WEB-SURFACE.md`, so browsing becomes auditable, bounded, and unfoolable. Companion: `EMBEDDED-WEB-SURFACE.md` (the Servo `WebView` as a `SurfaceCapability` cell + the `WebViewDelegate`-as-cap-gate, the whole authority model this stands on), `ADOS.md` (the seam, the budget=cell, the narration-vs-truth tooth), `AGENT-SWARM-UX.md` (the cockpit the receipts surface in), `DREGG-DESKTOP-OS.md` §5 (attested-volition: the signed input-receipt), `galaxybrain-dregg.md` (the sovereign-cell history model).*

## 0. The one-paragraph thesis

The open web's accountability model is a `history.db` SQLite file the browser writes and any process can edit, and an "agent that browses for you" is a loop whose only record of what it did is its own optimistic narration. dregg's answer is the same one it gives every other workload: **there is no ambient web action — every nav/click/fetch/submit is a cap-gated verified turn that leaves a receipt, and the receipt, not the loop's claim, is the truth.** Concretely, the embedded web surface (`EMBEDDED-WEB-SURFACE.md`) already opens a Servo `WebView` as a `SurfaceCapability` cell whose authority-bearing operations are mediated `WebViewDelegate` callbacks; **this facet makes each of those mediated operations route through the ADOS seam** (`Swarm::run` over the web-surface cell), so the delegate doesn't just *gate* the action — it **records it as a turn** the verified executor committed (or refused), with a `receipt_hash`, a height, and a metered cost (`swarm.rs:246–251`). On top of that one move, four properties fall out, each with a real mechanism and a named seam: **(a)** browsing history becomes a **blocklace** — the same Ed25519-signed, seq-monotone, equivocation-detecting causal DAG the federation already ships (`blocklace/src/lib.rs`) — so it is time-travelable, attestable, and tamper-evident; **(b)** an agent driving the surface holds a **cap-attenuated mandate** (a cipherclerk macaroon, `macaroon/`) and a runaway is **refused at the seam** (`SwarmError::OutOfMandate` / `BudgetExhausted`), not merely logged after the fact; **(c)** the **narration-vs-truth tooth** (`ADOS.md` §3.6) lands on the web — the agent claims one click, the receipt chain shows what it *actually* navigated, fetched, and submitted; **(d)** a value-moving web action carries **attested volition** — a signed input-receipt (`DREGG-DESKTOP-OS.md` §5) proving a real operator authorized it, defeating the agent that silently checks out. The honest floor throughout: dregg mediates and records **authority and effect**; it does not verify the *content semantics* of a page, and the last hop (what pixels Servo actually scanned, what bytes actually crossed the wire) carries the same named rendering/network-driver assumptions the companion docs already carry — stated, never laundered.

---

## 1. The reframe: a web interaction IS a turn

`EMBEDDED-WEB-SURFACE.md` §2 enumerates every web authority and maps it to a mediated `WebViewDelegate` callback — the embedder's impl of the delegate *is* the cap gate. That doc stops at **gating** (allow/deny against the surface cap's caveats). This facet takes the next hop: **the gate's verdict becomes a turn.**

The move is structural and tiny. Today the embedded-web delegate does:

```
request_navigation(url) → check url ∈ cap.navigate-caveat → allow | deny
```

This facet rewrites it to route through the ADOS seam:

```
request_navigation(url)
  → compile to Vec<Effect>   (a Navigate effect against the web-surface cell)
  → Swarm::run(world, web_surface_agent, effects)        // swarm.rs:317
      ▸ resolve the surface cell (dead surface ⇒ refused)
      ▸ confirm backed (the surface is live in the ledger)
      ▸ CAP-GATE: the surface cell's c-list reaches the nav target
                  (Capabilities::has_access) — the macaroon caveat IS the c-list edge
      ▸ run through the REAL executor (World::commit_turn → TurnExecutor)
      ▸ append the SwarmActionOutcome (receipt_hash, height, computrons)
  → allow iff the turn COMMITTED; deny + show refusal iff OutOfMandate
```

So the delegate's allow/deny is no longer a transient branch — it is **the commit-or-refuse of a verified turn**, and the turn's `SwarmActionOutcome` (`swarm.rs:240–256`) is the durable, receipted record. Every web authority `EMBEDDED-WEB-SURFACE.md` §2 lists becomes one effect kind:

| web authority (EMBEDDED-WEB-SURFACE §2) | delegate hook (the gate, today) | the EFFECT it compiles to (this facet) | what the receipt pins |
|---|---|---|---|
| **navigate** | `request_navigation()` | `WebNav { surface, from_url_digest, to_url, referrer_receipt }` | the committed origin (drives trusted chrome) + the predecessor nav |
| **fetch / subresource** | `load_web_resource()` | `WebFetch { surface, method, url, req_digest, resp_digest }` | the request + the **content digest** of what came back |
| **new window** | `request_create_new()` | `WebOpenChild { parent, child_cap_digest }` — mints an attenuated child surface cap | the child's authority ⊆ parent's |
| **submit / form POST** | `load_web_resource()` (the POST) | `WebSubmit { surface, action_url, body_digest, volition_receipt? }` | the submitted bytes' digest + (if value-moving) the volition proof |
| **permission ask** | `request_permission()` | `WebPermission { surface, kind, verdict }` | which permission, granted-or-denied, against which caveat |
| **download** | `load_web_resource()` → sink | `WebDownload { surface, url, bytes_digest, sink_cell }` | what was saved, where |
| **host→page script** | `evaluate_javascript()` (host-driven) | `WebEvalJs { surface, script_digest, result_digest }` | what the *controlling cap holder* injected + got back |

The uniformity is the point: **the delegate callback is the powerbox, and the powerbox's verdict is a turn.** A web session is then exactly a sequence of these turns against the surface cell — which is precisely what becomes a blocklace (§2).

**Mechanism.** `Swarm::run` exists and is tested end-to-end through the embedded verified executor (`an_in_mandate_swarm_action_commits_and_receipts`, `an_out_of_mandate_swarm_action_is_refused`); the web-surface cell is a `SurfaceCapability` cell that already rides the same `World`/`has_access` machinery (`EMBEDDED-WEB-SURFACE.md` §1, `surface.rs`). **Seam.** The `WebViewDelegate → Vec<Effect>` compiler is the genuinely new code — the web-specific instance of ADOS's "tool-call → effect compiler" (`ADOS.md` §3.3 research). It is per-hook, small, and audited; if it maps a nav to the wrong effect the receipt faithfully records the wrong thing (the same honest boundary `ADOS.md` §8.1 and `pg-dregg` draw — *the decision is verified; the adapter delivering the request to it is conventional code with a golden-corpus differential*). This is the load-bearing seam of the whole facet, named first.

---

## 2. (a) Browsing history as a blocklace — time-travelable, attestable, tamper-evident

### The mechanism: a web session is a strand in the blocklace

dregg ships a real blocklace (`blocklace/src/lib.rs`): a `Block { creator, sequence, predecessors: Vec<BlockId>, payload, signature }` whose `id()` is `BLAKE3(creator ‖ seq ‖ sorted-predecessors ‖ payload)`, authored by `Block::new_signed(&signingKey, seq, preds, payload)`, and admitted by a verified `insert` that enforces **(i)** causal closure — every predecessor must already be present (`InsertError::MissingPredecessors`), **(ii)** a **monotone per-creator sequence**, and **(iii)** equivocation detection — two distinct blocks at the same `(creator, seq)` yield an *attributable* `EquivocationProof` (the creator's key + both block ids). This is the exact substrate the federation uses; browsing history rides it unchanged.

**A browsing session is a strand** (a single creator's seq-chain) of web turns:

```
the surface cell is the CREATOR; each web turn (§1) is a BLOCK:
  block n   = WebNav  { to_url = bank.com,        resp_digest = D₀ }   seq=n   preds=[block n-1]
  block n+1 = WebFetch{ url = bank.com/price.json, resp_digest = D₁ }  seq=n+1 preds=[block n]
  block n+2 = WebSubmit{ action_url = bank.com/buy, body_digest = D₂ } seq=n+2 preds=[block n+1]
```

The **payload of each history block is the web turn's `SwarmActionOutcome`** — the receipt hash, the committed URL, and the content digest. So the browsing history is not a side-log; it *is* the receipt chain of the web-surface cell's turns, embedded in the same DAG that carries every other dregg action. (This is `ADOS.md` §3.6's blocklace panel — "the receipt chain as a navigable causal history" — specialized to web turns.)

### The four properties this buys

- **Time-travelable.** The `predecessors` edges make history a navigable causal DAG, not a flat list. "Show me the state of my browsing at height H" is a walk of the DAG up to H — exactly the `blocklace` panel's time-travel (`ADOS.md` §3.6, `AGENT-SWARM-UX.md` §4.2). Tabs that branch (a `WebOpenChild`) are *branches in the DAG* — the predecessor structure captures "this tab was opened from that page," which a flat history.db cannot represent faithfully.

- **Tamper-evident.** Editing any block changes its BLAKE3 `id()`, which breaks every successor's `predecessors` reference — the same chain-break the macaroon caveat-chain `verify` exploits (`macaroon/src/caveat_chain_diff.rs` `removal_breaks_tail`, cited in `EMBEDDED-WEB-SURFACE.md` §3). You **cannot silently delete or rewrite a visit**: a removed block is a `MissingPredecessors` failure on `insert`, a rewritten block is a signature failure, and a forked history (claiming two different things happened at the same seq) is a detectable `EquivocationProof`. The open web's "clear your tracks / edit the history file" is structurally closed — history is append-only and attributable.

- **Attestable — "prove you visited X at T showing content Y."** This is the sharp one. Because each block commits `to_url` *and* `resp_digest` (the BLAKE3 of the response body Servo received via `load_web_resource`), and the block is signed and seq-anchored, **a single block is a portable proof**: "the surface (creator key K) committed, at sequence n with predecessor chain back to the session root, a visit to `to_url=X` whose content hashed to `resp_digest=Y`." To make it provable *to a stranger* (not just locally verifiable), the session strand is **anchored**: periodically the surface registers its current head commitment with the federation (the `galaxybrain-dregg.md` "attested checkpoint" / `blocklace/src/addressing.rs` `Attestation` — a participant signature over a checkpoint hash), giving a federation-ordered timestamp `T`. Then "I visited X at T showing Y" = (the signed block) + (the federation attestation covering its head) — a light-client-checkable artifact. **"Prove this checkout showed this price"** is the same block with `to_url = checkout`, `resp_digest = hash(the rendered price page)` — a receipt that the price you saw is the price the server served, anchored at a federation timestamp, that you can show a dispute resolver later.

- **Selective disclosure.** Because history blocks are content-addressed by digest and the *payload* (URL, content) can be committed as a hash with the preimage held privately (the `galaxybrain-dregg.md` sovereign-cell model — the federation sees commitments, not contents), you can **prove a visit happened without revealing what you browsed**, or reveal one block's preimage (this visit, this price) without revealing the rest of the session. The history is private-by-default, disclosable-by-choice.

**Mechanism.** The blocklace (`Block`, `new_signed`, verified `insert` with causal-closure + seq-monotone + equivocation) is real and tested (the MEMORY "blocklace A1 fix": insert verifies sig + seq + equivocation). The federation anchor/attestation path (`addressing.rs::Attestation`) is real. **Seam — the digest is only as honest as what produced it.** `resp_digest` is the hash of the bytes `load_web_resource` *delivered to the embedder*; it faithfully proves "the surface received body Y for URL X." It does **not** by itself prove the *server* sent Y under TLS to that origin — binding the digest to the TLS session (so "the price came from bank.com over a valid cert," not "the agent fabricated a price page") is the **TLS-transcript-binding frontier**: it needs Servo to surface the TLS session transcript / cert chain to the embedder at the `load_web_resource` boundary (an upstream ask, the network-side dual of `EMBEDDED-WEB-SURFACE.md` §1's pixel-clip assumption). Until then the attestation is "the surface committed to having received Y" (tamper-evident, operator-attributable, federation-timestamped) — strong for self-accountability and agent-audit, and honestly *short* of "the server provably served Y" without the transcript binding. Named as work, with the exact upstream lever, not a wall.

---

## 3. (b) The agent holds a cap-attenuated mandate to drive the surface — a runaway is REFUSED

### The mechanism: the surface cap IS the agent's leash, discharged at the seam

`EMBEDDED-WEB-SURFACE.md` §3 already mints a tab's authority as a **cipherclerk macaroon** whose caveats name the mediated effects (`fetch ⊆ {*.example.com}`, `navigate ⊆ {…}`, `downloads = none`, `exp = <deadline>`). This facet makes that macaroon **the mandate an agent loop drives the surface through** — the c-list of the web-surface cell, against which `Swarm::run`'s cap-gate (`Capabilities::has_access`, `swarm.rs:369`) discharges every web turn. So "bounded browser automation" is not a policy the agent is *asked* to honor — it is the executor refusing, at the seam, any web turn outside the mandate, **before Servo acts** (the delegate returns deny on `OutOfMandate`, so the fetch never leaves).

A driving mandate is a macaroon like:

```
root: the web-surface cap, then attenuating caveats:
  navigate ⊆ { https://docs.rust-lang.org/* }     # request_navigation allowlist
  fetch    ⊆ { https://docs.rust-lang.org/*,
               https://crates.io/api/* }            # load_web_resource allowlist
  submit   = none                                   # no form POST — read-only agent
  downloads= none                                   # no sink cap
  new-window: inherit-attenuated                    # child ⊆ this
  rate     ≤ 30 turns / minute                      # the runaway ceiling (see below)
  budget   ≤ 5000 computrons                         # the spend ceiling (ADOS §3.4)
  exp      = height + 600                            # the mandate expires
```

### What "a runaway is REFUSED, not just logged" means, mechanically

This is the precise upgrade over a logged-after-the-fact audit. Three refusal teeth, each already enforced at the ADOS seam:

1. **Out-of-scope is refused (the cap-gate).** An agent that tries to navigate to `evil.com` when its `navigate` caveat names only `docs.rust-lang.org/*` is refused exactly the way `EMBEDDED-WEB-SURFACE.md` §3 refuses a widening — the request discharges against the macaroon (`macaroon/src/access.rs`), the caveat *prohibits* it, and `Swarm::run` returns `OutOfMandate` with **no turn committed, no fetch issued**. The blocked navigation never reaches the network; it leaves a *refusal* receipt (the red feed entry of `AGENT-SWARM-UX.md` §3 minute-3), which is itself auditable.

2. **Runaway-rate is refused (the budget ceiling).** The "agent stuck in a fetch loop hammering a server" runaway is bounded by **budget = a cell** (`ADOS.md` §3.4): the surface's mandate carries a rate/spend ceiling enforced as a `StingrayCounter` conservation bound (`AGENT-SWARM-UX.md` §5). A web turn past the ceiling is refused with `BudgetExhausted` **before it runs** (`swarm.rs` S0 budget gate, `AGENT-SWARM-UX.md` §8 S0). The runaway hits a wall at turn N+1, not after draining the target — the answer to "a runaway could hammer/drain," applied to web automation: bounded at the seam, refused in front of the operator.

3. **Attenuated children cannot amplify (the no-amplify guarantee).** When the agent's page opens a window or an iframe (`request_create_new`), the child surface's mandate is minted as **the parent's macaroon plus strictly-narrowing caveats** (`EMBEDDED-WEB-SURFACE.md` §3 "no-amplification, applied to web content"). An agent cannot escape its leash by spawning a sub-surface with wider reach — a widening child is `DelegationDenied` for the same structural reason `Shell::share` refuses a widening window share. So the bound holds **transitively across the whole tab tree** the agent drives.

The decisive contrast with "logged automation" (Playwright/Puppeteer + an audit log): there, the automation *does the action*, then writes a log line a compromised script can edit, and a bug means the action already happened. Here, the action **is a turn the executor must accept**: out-of-mandate, over-budget, and amplifying actions are *refused at the gate*, the record is *tamper-evident* (§2), and the bound is *enforced by the substrate*, not promised by the harness. **A runaway is structurally incapable of the action, not retroactively scolded for it.**

### The kill switch is immediate (n=1)

The operator revokes the agent's surface mandate (a `RevokeCapability` turn from the ⌘K palette, `AGENT-SWARM-UX.md` §8 / `ADOS.md` §6 step 4). On the `n=1` firmament the revoke is **immediate** (`FIRMAMENT.md` §3): the surface cap goes dark the instant the turn commits, the WebView handle is dropped (`EMBEDDED-WEB-SURFACE.md` §4.1 "the webview handle's lifetime controls the webview's"), **the glass goes dark**, and the agent's next web turn is refused (`Unbacked` / no cap). The runaway browser is not "asked to stop" — it is *unable to continue*, synchronously, watchably.

**Mechanism.** The cap-gate + refusal (`Swarm::run` `OutOfMandate`), the budget ceiling (`StingrayCounter`, `BudgetExhausted`), the no-amplify child mint (`Shell::share` / firmament grant, `DelegationDenied`), the immediate revoke (`n=1` firmament) are all real and tested. The macaroon mint/attenuate/discharge is real (`macaroon/`, no reimplemented crypto). **Seam — DOM-level micro-actions are coarser than the delegate.** The mandate gates *authority-bearing* operations Servo surfaces as delegate callbacks (nav/fetch/window/permission/download). A *click that only mutates the DOM* (no fetch, no nav) is **below the delegate's visibility** — Servo has no per-DOM-event embedder hook (`EMBEDDED-WEB-SURFACE.md` §2.1, the storage/clipboard seam). So "the agent clicked button B" is gated *iff* the click produces a mediated effect (a fetch/nav/submit); a purely-cosmetic DOM interaction is observed only through the host-injected content script (`EMBEDDED-WEB-SURFACE.md` §4.2 option 2 — `evaluate_javascript` at document-start, a `WebEvalJs` turn). Closure lane: the content-script surface emits DOM-event turns for the actions the delegate can't see — a host-controlled injection bounded by the surface's caveats, named as the DOM-granularity work, complementing (never replacing) the delegate gate. The strong, sound boundary (authority) needs nothing Servo lacks; the DOM-granularity refinement is the labeled frontier.

---

## 4. (c) The narration-vs-truth tooth, on the web — the agent claims one click, the receipt shows what it ACTUALLY did

### The mechanism: the agent's claim beside the surface cell's receipt chain

This is the sharpest ADOS feature (`ADOS.md` §3.6, §7 — "every 'the agent says it did X' is replaced by 'the receipt at height H shows it did X'"), and the web is where it bites hardest, because a web-browsing agent's narration is the *least* trustworthy thing in the system: an agent loop summarizing "I checked the three top results and the cheapest was $40" is pure self-report, and the open web gives you no way to check it.

The tooth puts **the agent's own claim** (from its loop's reflection/log — "I navigated to X, clicked Buy, the price was $40") **next to the surface cell's blocklace** (the §2 history strand — the actual `WebNav`/`WebFetch`/`WebSubmit` turns the executor committed, each with its `to_url` and `resp_digest`) and **highlights divergence**. The four divergences it catches:

| the agent CLAIMS… | the receipt chain SHOWS… | the divergence |
|---|---|---|
| "I visited X" | no `WebNav` turn with `to_url=X` in the strand | a **fabricated visit** — the agent hallucinated a page it never loaded |
| "the price was $40" | the `WebFetch` for the price page has `resp_digest=Y`, and Y's content says $60 | a **fabricated content claim** — the agent misreported what the page actually served |
| "I clicked Buy" | a `WebSubmit` to `action_url=/buy` *did* commit (or did not) | a **fabricated OR concealed action** — the agent claimed an action that didn't happen, or (worse) did one it didn't mention |
| "I only read, didn't change anything" | a `WebSubmit` / `WebDownload` turn is in the strand | a **concealed side-effect** — the read-only claim is false; the receipt shows the write |

The last two are the dangerous ones — the **pale ghost on the web**: an agent that *did more than it said* (silently submitted a form, downloaded a payload, granted a sub-cap) is caught because the side-effecting turns are in the tamper-evident strand whether or not the agent mentions them. The operator does not read the agent's summary; they read **the receipts of what the surface cell actually did**, and the divergence panel flags every gap. (`AGENT-SWARM-UX.md` §7's accountability table, specialized: *"I did X / I visited Y" → the `WebNav`/`WebFetch`/`WebSubmit` receipt + the `resp_digest`*.)

This is pure UI over data that already exists — the loop's log (the agent supplies its claimed actions alongside the turns it requests) + the surface cell's blocklace (`Swarm::action_log` + the §2 strand). It is `ADOS.md` §3.6's narration-vs-truth diff, with the web's content digests making the *content* claims checkable, not just the *action* claims.

**Mechanism.** The receipt chain (the §2 blocklace), the per-turn `resp_digest` (the §1 `WebFetch` effect), and the panel-over-`action_log` (`AGENT-SWARM-UX.md` §4.2 feed) are all real or pure-UI-over-real. **Seam — content-claim checking needs the preimage, and is structural-not-semantic.** "The price was $40" is checkable *iff* the operator (or an auditor) holds the `resp_digest`'s preimage (the page body) and a way to extract the price — the digest proves *which bytes* the surface received, and a deterministic extractor (or a human, or a second agent) reads the price out of them. dregg proves **byte-identity** ("the surface received exactly these bytes, tamper-evidently, at this height"); it does **not** prove the *semantic* claim "those bytes mean $40" — that is a content-interpretation step outside the executor (the same boundary `ADOS.md` §8.3 draws: *ADOS grounds actions, not cognition*). So the tooth catches **fabricated and concealed actions with certainty** (the action turns are in the strand or not) and **fabricated content claims modulo a trusted extractor** (the bytes are pinned; reading $40 out of them is conventional). Named: the action-divergence is a theorem over the strand; the content-divergence is structural-evidence-plus-an-extractor, not a content proof. Severe-problem-with-closure-lane (a per-domain golden extractor with its own differential), never a wall.

---

## 5. (d) Attested volition — a value-moving web action carries proof a real operator authorized it

### The mechanism: the signed input-receipt as a turn premise

The most dangerous web action an agent takes is a **value-moving** one — checkout, payment, a wire, an OAuth consent, an irreversible POST. ADOS's whole posture is "you see what the agent did and it could only do what its mandate allowed" — but for value-moving actions that is not enough: you want **proof a real human authorized this specific action**, so an agent (even a correctly-mandated one, even a compromised one) cannot silently spend on your behalf.

dregg has the exact mechanism: **attested user-volition** (`DREGG-DESKTOP-OS.md` §5). When a gesture in a *trusted* surface authorizes a value-moving turn, the compositor-PD emits a **signed input-receipt the executor requires as a turn premise** — a signature over `(surface CellId + gesture + nonce + which turn-field it authorizes)`, so it cannot be replayed or confused onto a different action. The compositor holds only an *attestation key* and the executor checks the signature; the compositor never becomes a second authority over state.

This facet binds that machinery to the value-moving web effect. A `WebSubmit` whose `action_url` (or the agent's declared intent) is marked value-moving **carries a `volition_receipt`** (the §1 `WebSubmit` effect field), and the executor's gate **refuses the turn without a valid one**:

```
WebSubmit { surface, action_url = bank.com/wire, body_digest = D,
            volition_receipt: Sig_attest(surface_cell ‖ "approve-wire" ‖ nonce ‖ body_digest) }

executor gate:  this action is value-moving ⇒ REQUIRE volition_receipt
                verify Sig_attest over (surface ‖ gesture ‖ nonce ‖ body_digest)
                ▸ valid   ⇒ commit (the human approved THIS submit, this body, once)
                ▸ absent  ⇒ REFUSE — "value-moving web action requires operator volition"
                ▸ replayed (nonce seen) ⇒ REFUSE
                ▸ body mismatch (signed a different body) ⇒ REFUSE — defeats confusion
```

So the agent can *prepare* the checkout (navigate, fill the cart, assemble the submit) entirely under its mandate — but the **final value-moving submit is gated on a fresh human gesture in the trusted-path surface** (the cipherclerk / ⌘K secure-attention anchor, `AGENT-SWARM-UX.md` §3 minute-5, `DREGG-DESKTOP-OS.md` §5 "this is the cipherclerk promoted to a trust anchor"). The operator sees, in the unspoofable overlay (drawn by the shell from the ledger, not the page — `EMBEDDED-WEB-SURFACE.md` §1 anti-spoof chrome), the genuine `(action_url, body_digest)` of *what they are approving*, and their gesture signs *exactly that*. The agent cannot:

- **submit without approval** — no `volition_receipt`, refused;
- **replay an old approval** — nonce-bound, refused;
- **bait-and-switch** — the receipt commits to `body_digest`; approving a $40 cart and submitting a $4000 one is a body mismatch, refused (the confusion-defeat of `DREGG-DESKTOP-OS.md` §5);
- **spoof the approval prompt** — the prompt is the trusted-path overlay at a `zLayer` no cell (and no page) holds a cap to (T1/T3 of `DREGG-DESKTOP-OS.md` §5), so a page cannot paint a fake "click to approve."

This is **attested volition on the web**: a value-moving browser action carries cryptographic proof a real operator, looking at the real action, authorized exactly it — the structural answer to "an agent silently checked out / wired funds / consented to an OAuth scope."

**Mechanism.** The signed input-receipt as a turn premise, the `(cell ‖ gesture ‖ nonce ‖ field)` binding, the trusted-path overlay at an unspoofable `zLayer`, and the executor-checks-a-signature discipline are all specified in `DREGG-DESKTOP-OS.md` §5 and ride the existing attestation/receipt machinery (the same shape as the net-PD's Ed25519 pre-check). **Seam — the trusted-path compositor is the named frontier.** The attested-volition gesture leans on the trusted-path compositor-PD that holds the sole top-`zLayer` surface cap and the sole input cap (`DREGG-DESKTOP-OS.md` §5, R3) — which is the verified-graphics north star, gated on the compositor work (and, at the seL4 end-state, on the F1/F2 last-hop / IOMMU assumptions that doc names as *the* graphics crypto-floor-equivalents). So today: the **volition-receipt protocol and the executor-side gate are buildable now** on the embedded executor (the executor requiring a signed premise is pure existing machinery — `AGENT-SWARM-UX.md` §8 S5 names exactly this: "the identity + lineage strip ships now; the gesture-to-turn binding is the designed-pending tooth that lands with the trusted-path compositor work, DREGG-DESKTOP-OS R3"). The *unspoofable* gesture surface (a page provably cannot fake the approval prompt) is as strong as the trusted-path compositor, which is the labeled research frontier — stated with its precise dependency (R3 + F1/F2), never claimed near. The near-term honest form: the volition gate is real and refuses un-attested value-moving submits *today*; the guarantee that the approval prompt itself is unspoofable rises to full strength when the trusted-path compositor lands.

---

## 6. The architecture — one seam, the web edition

The whole facet is `ADOS.md` §4's three-layer / one-seam architecture with the loop's actions being *web* actions:

```
┌───────────────────────────────────────────────────────────────────────────┐
│ THE LOOP LAYER (above dregg — NOT ours)                                     │
│   the browsing agent's perceive/plan/act/reflect: read the page, decide     │
│   the next click/nav/fetch/submit. A Claude computer-use loop, a            │
│   research agent, a shopping agent. dregg does NOT own this.                │
├──────────────────────────────── THE SEAM ──────────────────────────────────┤
│   ONE place: the WebViewDelegate callback → Swarm::run(world, surface, fx). │
│   nav/fetch/window/submit/permission/download = a typed Effect (§1).        │
│   cap-gate ▸ verified turn ▸ receipt ▸ budget meter ▸ blocklace block.       │
│   value-moving submit ▸ ALSO requires the volition-receipt premise (§5).     │
├───────────────────────────────────────────────────────────────────────────┤
│ THE SUBSTRATE LAYER (dregg — the verified accountability ground)            │
│   the surface = a SurfaceCapability cell (EMBEDDED-WEB-SURFACE §1) ·         │
│   authority = a cipherclerk macaroon (the driving mandate, §3) ·            │
│   history = the surface's blocklace strand (§2) ·                           │
│   budget = a cell + Stingray ceiling (the runaway leash, §3) ·              │
│   volition = a signed input-receipt premise (§5).                           │
│   THE EMBEDDED VERIFIED EXECUTOR is the only authority over what happened.  │
├───────────────────────────────────────────────────────────────────────────┤
│ THE OBSERVATION LAYER (the operator's glass)                                │
│   the SWARM/web cockpit · the history-blocklace panel (time-travel) ·       │
│   the narration-vs-truth diff (§4) · the trusted-path approval overlay (§5).│
│   reads LIVE protocol types via reflect — cannot drift from executor truth. │
└───────────────────────────────────────────────────────────────────────────┘
```

The integrator wedge (`ADOS.md` §2, §5) carries verbatim: a browser-automation platform (or a web-browsing agent harness) already serializes "the agent did a web action" at one place — its Playwright/CDP command dispatcher, its action log. ADOS-web makes that one dispatcher route through `Swarm::run` over the web-surface cell, and the platform inherits the six enforced primitives *on its browsing*: cap-gated nav/fetch (forgery-of-scope gone), the blocklace history (mutable-log gone), the budget ceiling (runaway gone), the attenuated child-tab (amplification gone), the surface cap (ambient-window gone), and — the web-specific seventh — attested volition on value-moving actions.

---

## 7. The killer demo — "the browsing agent that cannot lie about where it went, cannot overspend, and cannot checkout without you"

A single watchable scene on the `n=1` embedded executor, the web edition of `ADOS.md` §6 / `AGENT-SWARM-UX.md` §9:

1. **Boot a browsing agent** with a read-only research mandate: `navigate/fetch ⊆ {docs + crates.io}`, `submit = none`, `budget ≤ 5000 computrons`, `exp = +600`. Its web-surface cell is a row in the cockpit showing the mandate and an empty history strand.

2. **Honest browsing.** The agent navigates to crates.io, fetches three crate pages. The history blocklace grows three `WebNav`/`WebFetch` blocks, each with a `to_url` and a `resp_digest`, time-travelable in the panel. **This is where it went — receipts with content digests, not a summary.**

3. **The fabrication moment (the narration tooth).** The agent's loop *claims*, in its reflection, "I also checked example.com and it recommended crate Z." The narration-vs-truth panel shows the claim **red** beside the strand: *no `WebNav` with `to_url=example.com` exists* — a fabricated visit, caught. **The pale ghost on the web, at the glass.**

4. **The runaway moment (the leash).** The agent's loop tries to (a) navigate to `evil.com` (outside `navigate ⊆ {docs+crates}`) and (b) enter a fetch loop. (a) is **refused** — `OutOfMandate`, red feed entry, *the fetch never leaves*. (b) hits the budget ceiling — `BudgetExhausted` at turn N, refused **before** it can hammer the target. **The runaway is incapable, not scolded.**

5. **The checkout moment (attested volition).** The operator switches the agent to a shopping mandate and lets it assemble a cart. At the final `WebSubmit { action_url=/buy, body_digest=$40-cart }`, the executor **refuses for want of a volition-receipt**. The trusted-path overlay (cipherclerk / ⌘K) shows the operator the genuine `(/buy, $40)` of *exactly what they'd approve*; their gesture signs it; the submit commits **with proof a real human authorized this specific buy**. The agent's attempt to then resubmit a swapped `$4000` body is a **body-mismatch refusal**. **No silent checkout; no bait-and-switch.**

6. **The receipt.** "Where did this agent go, and what did it see?" — the history blocklace, navigable, content-digested, tamper-evident, federation-anchorable. "Could it have gone anywhere else or spent more?" — no: the mandate's caveats and the budget ceiling bound it, provably. "Did it do anything it didn't tell me?" — the narration-vs-truth diff shows every concealed side-effect, or none.

The demo *is* the evaluation artifact (the pug-handoff bar). It needs: the embedded-web surface + delegate gate (the `EMBEDDED-WEB-SURFACE.md` near-term build), the `WebViewDelegate → Effect` compiler (the §1 seam), the blocklace history strand (the blocklace is real; the web-strand binding is new wiring), the budget ceiling + cap-gate refusals (`Swarm::run`, real), the narration-vs-truth panel (pure UI over `action_log` + strand), and the volition-receipt gate (the executor premise is buildable now; the unspoofable overlay rises with R3). The most legible possible answer to "why would I let an agent browse and buy on my behalf?"

---

## 8. Honest scope — real today / near-term build / research

Per repo discipline (teach what-is; name seams as work-with-a-lever, never walls; never trajectory-narrativize):

**Real today (the foundation this stands on, all green):**
- The ADOS seam — `Swarm::run` cap-gates every effect, runs through the real executor, returns a receipt or `OutOfMandate`, all tested (`swarm.rs:317`, `an_in_mandate_swarm_action_commits_and_receipts` / `..._refused`).
- The blocklace — signed (`new_signed`), causal-closure + monotone-seq + equivocation-detecting `insert`, attributable `EquivocationProof`, federation `Attestation` anchor (`blocklace/src/lib.rs`, `addressing.rs`). History rides this unchanged.
- The cipherclerk macaroon — real mint/attenuate/delegate/discharge over an HMAC caveat chain whose `verify` rejects a removed/tampered caveat (`macaroon/`, `EMBEDDED-WEB-SURFACE.md` §3). The driving mandate is one such macaroon.
- The budget ceiling + no-amplify child mint + immediate `n=1` revoke (`StingrayCounter`, `Shell::share`/`DelegationDenied`, firmament `n=1`).
- The embedded-web surface model itself — Servo `WebView` as a `SurfaceCapability` cell, the `WebViewDelegate`-as-cap-gate, the anti-spoof origin chrome (`EMBEDDED-WEB-SURFACE.md` §1–§3, all the way down to its own honest seams).

**Near-term build (buildable now, no cutover dependency — a starbridge-v2 + libservo slice):**
- The **`WebViewDelegate → Vec<Effect>` compiler** (§1) — the per-hook adapter turning each mediated callback into a typed web effect routed through `Swarm::run`. The headline new code; the web instance of ADOS's tool-call→effect compiler.
- The **history-blocklace binding** (§2) — making the web-surface cell a blocklace creator whose web turns are seq-chained blocks with `resp_digest` payloads; the federation-anchor for "prove I visited X at T showing Y."
- The **narration-vs-truth web panel** (§4) — pure UI over `action_log` + the history strand, with the content-digest column.
- The **volition-receipt executor gate** (§5) — the executor requiring a signed input-receipt premise on value-moving `WebSubmit` (the gate is existing attestation machinery; `AGENT-SWARM-UX.md` §8 S5 names this exact split).

**Research (named, with the precise lever, not laundered):**
- **TLS-transcript binding** (§2 seam) — binding `resp_digest` to the TLS session/cert so "the server provably served Y," not just "the surface received Y." Needs Servo to surface the TLS transcript at `load_web_resource` (upstream ask) — the network-side dual of the §1 pixel-clip assumption.
- **DOM-granularity gating** (§3 seam) — gating clicks that mutate only the DOM (below the delegate's visibility); the closure lane is host-injected content-script DOM-event turns (`EMBEDDED-WEB-SURFACE.md` §4.2 option 2), never a Servo WebExtension (which doesn't exist, §4.2 of that doc).
- **Content-claim semantic checking** (§4 seam) — "the price was $40" is byte-pinned + a trusted extractor, not a content proof; closure is a per-domain golden extractor with a differential. dregg proves byte-identity; semantic interpretation is conventional (the *grounds-actions-not-cognition* boundary, `ADOS.md` §8.3).
- **The unspoofable approval overlay** (§5 seam) — the *guarantee* that a page cannot fake the volition prompt rises to full strength with the trusted-path compositor-PD (`DREGG-DESKTOP-OS.md` §5, R3), and at the seL4 end-state the F1/F2 last-hop/IOMMU assumptions that doc names as the graphics crypto-floor. The volition *gate* is real now; the *unspoofable prompt* is the labeled frontier with its exact dependency.
- **Confined-Servo seL4 renderer PD** (`EMBEDDED-WEB-SURFACE.md` §5) — the structural end-state where the renderer physically cannot reach the network except through the broker that discharges the mandate; gated on the Lean-runtime + Servo-on-seL4 + GPU-cap blockers that doc names. The reason §1–§5 pre-factor cleanly into PD + broker, not a claim it's near.

None of these are walls. Each is a labeled seam with a named closure lever (an upstream Servo ask, a content-script lane, a golden extractor, the trusted-path compositor work, the seL4 port), held to one worthwhile semantics, and none of them block the buildable §1–§5 core that makes web browsing a verified, receipted, bounded, attested workload on the `n=1` firmament today.

---

*A web action is the canonical "an agent did X." The open web records it as an editable log line and trusts the agent's summary; dregg records it as a verified turn and trusts the receipt. Route every nav/click/fetch/submit through the one ADOS seam over the embedded web surface, and browsing history becomes a tamper-evident blocklace you can time-travel and attest from ("I visited X at T showing Y"); a driving agent holds a cap-attenuated mandate where a runaway is refused at the gate, not logged after the drain; the narration-vs-truth tooth catches the agent that claims one click and concealed another; and a value-moving action carries a signed input-receipt proving a real operator approved exactly it. dregg mediates and records authority and effect — verified; the content's meaning, the TLS provenance, and the last pixel are named seams with named levers, not laundered guarantees. The browser becomes a guest the OS bosses around, and the agent driving it becomes a loop whose every web action is a turn the executor kept — at the glass, the pale ghost cannot lie about where it went.*

---

**Key file paths (all absolute):**
- `/Users/ember/dev/breadstuffs/docs/EMBEDDED-WEB-SURFACE.md` — the Servo-WebView-as-SurfaceCapability-cell model + WebViewDelegate-as-cap-gate (the authority model this facet records-as-turns)
- `/Users/ember/dev/breadstuffs/docs/design-frontiers/ADOS.md` — the seam (`Swarm::run`), budget=cell, narration-vs-truth tooth
- `/Users/ember/dev/breadstuffs/docs/design-frontiers/AGENT-SWARM-UX.md` — the cockpit/observation layer + the S0–S6 buildable slices + the §8 S5 volition-split
- `/Users/ember/dev/breadstuffs/docs/DREGG-DESKTOP-OS.md` §5 — attested user-volition (the signed input-receipt premise) + trusted-path compositor (the §5 frontier)
- `/Users/ember/dev/breadstuffs/docs/galaxybrain-dregg.md` — the sovereign-cell / attested-checkpoint history model (§2 anchoring)
- `/Users/ember/dev/breadstuffs/starbridge-v2/src/swarm.rs` — the seam (`Swarm::run`, line 317; `SwarmActionOutcome` receipt_hash/computrons at 240–256; cap-gate at 369)
- `/Users/ember/dev/breadstuffs/blocklace/src/lib.rs` — the blocklace `Block`/`new_signed`/verified `insert` (causal-closure + seq-monotone + `EquivocationProof`) the history strand rides
- `/Users/ember/dev/breadstuffs/macaroon/` — the cipherclerk caveat-chain (the driving mandate)


## Facet 4 — distributed rendering & surface migration

I have everything I need, all real:

- `ComputronCosts` (`turn/src/executor/costs.rs`) threaded into `TurnExecutor::new(ComputronCosts::...)` — every turn is metered.
- `coord/src/shared_budget.rs`: `BudgetCeiling { ceiling, spent, remaining(), try_debit() -> Err(AllowanceExhausted) }` generalizing the **Stingray bounded counter**, max overspend bounded by `f * allowance` — the exact "remote render = Stingray-bounded metered service" mechanism.
- `process_kernel.rs`: `CapHandle { slot, epoch }` — opaque, validity-in-the-kernel-table-not-the-PD's-RAM, `CapError::Forged` on raw-bytes/stale-epoch, epoch = "cross-process badge generation." This is the unforgeable read-cap that survives crossing an address-space boundary — and its network generalization is what facet 4(b)/(c) needs.

That's the full anchor set. Writing the design now.

---

# GALAXY-BRAIN FACET 4 — DISTRIBUTED RENDERING & SURFACE MIGRATION

*Where a web surface is RENDERED and where it is DISPLAYED become two cap-mediated points on the firmament's distance parameter `n`. The whole facet is one move: take the seL4 framebuffer-cap end-state (`DREGG-DESKTOP-OS.md` §5, R4; the compositor-PD that SOLELY holds the framebuffer and admits a `present()` only after the scene authority passes) and slide the render node and the display node APART across the network — relaxing exactly the `Bounds` the firmament already parametrizes. No new model: the display node holds a **read-cap to a surface cell whose `content_digest` is attested**, the render node holds the **compute authority + the budget**, and the receipt chain proves the tab is the same tab.*

The load-bearing fact that makes this not-aspirational: the three pieces already exist as code. `sel4/dregg-firmament/src/distributed.rs` is `DistributedBacking` = a **real `dregg_cell::Ledger` + real `dregg_turn::TurnExecutor`** whose `invoke()` returns `Bounds::distributed(n)` and whose `delegate()` rejects a widening grant with `DelegationDenied`. `compositor_pd.rs` already models its scene as `Surface { owner, region, content_digest, source_state_root, focus }` with `Scene::scene_admit` (T1/T2/T3) and an explicit `FIDELITY` note that it enforces **scene authority, not scanned-out pixels** (the F1 seam). And `sel4/dregg-pd/net-client/src/turn_gate.rs` already Ed25519-`verify_strict`'s a `[32 pk][64 sig][msg]` envelope at the firmament boundary — the *exact attestation primitive* an attested frame reuses. Distributed rendering is the **fourth point on the distance parameter** (`Local{slot}` → `Distributed{cell}` → `Surface{cell}` → here: a `Surface{cell}` whose backing and whose display sit on *different nodes*), built by relaxing bounds, never by inventing a transport.

---

## (a) Remote render, local display — the framebuffer-cap end-state, over the network

**The picture.** Node R runs Servo for a tab (the `renderer` PD of `EMBEDDED-WEB-SURFACE.md` §5, or its host-emulator twin). Node D — your laptop, a wall panel — displays it. Today (n=1, `DREGG-DESKTOP-OS.md` R4 Stage D) R and D are the same machine: the compositor-PD holds the framebuffer cap, Servo `present()`s a frame, `scene_admit` passes, the pixel reaches glass. Facet 4(a) is **that same arrangement with R and D on different nodes** — and the only thing that changes is `Bounds`.

**Mechanism — the surface cell is the rendezvous; the frame is an attested present.**
1. The tab is a `Capability { target: Surface(cell), rights }` (the §1 model). Its **backing cell lives on node R** (R holds the real `Ledger`/`TurnExecutor` via `DistributedBacking`). Node D holds a **read-cap** to that same surface cell — an *attenuation* (`reflect`/present-read rights only, no `present`-write, no input-grant), minted through the real `is_attenuation` gate and shipped to D as a `delegate()` token (`distributed.rs::delegate`, the same `Effect::GrantCapability` turn that rejects widening with `DelegationDenied`).
2. **Servo renders on R into R's framebuffer region.** Then R commits a `present(region, content_digest @ source_state_root)` — but where the n=1 compositor consumes that present *locally*, here R's `present()` advances the surface cell's `content_digest` field, and the **post-state is what crosses the wire**. The frame bytes ride the **net-PD ring** (the `n>1` edge, `DREGG-DESKTOP-OS.md` §4 R4: "OPAQUE content ships a content-commitment + bytes over the net-PD ring"); the **commitment is `content_digest`**, bound into the surface cell's `source_state_root`.
3. **D composites the received frame under D's OWN scene authority.** D's compositor-PD runs `Scene::scene_admit` on the incoming surface exactly as for a local one: the remote tab gets region R_D, and `scene_admit` enforces T1 (it overpaints nothing local), T2 (`label_of(owner, source_state_root)` — drawn from the *cell's* committed root, which travelled with the frame, not from R's claim), T3 (focus). The pixel reaches D's glass **iff** D's scene authority admits it. R cannot make D paint outside R_D; that is D's compositor's `Refusal`, locally enforced.
4. **The attestation = the frame is signed against the digest.** R emits, alongside the bytes, an **Ed25519 signature over `(surface CellId ‖ content_digest ‖ source_state_root ‖ frame-nonce)`** — the *verbatim* shape `net-client/turn_gate.rs::verify_envelope` already checks (`[32 pk][64 sig][msg]`, `verify_strict`). D verifies it at its firmament boundary before compositing. So D doesn't trust R's socket; D checks a signature that binds *these pixels* to *this surface cell's committed state-root*. "A remote-rendered tab streamed as ATTESTED frames, the display node holding only a read-cap" is, mechanically: **net-PD ring for bytes + the existing Ed25519 envelope for the frame attestation + D's local `scene_admit` for placement + an attenuated read-cap for D's authority.**

**Bounds — what relaxes and what stays.** D's read-cap resolves to `Bounds::distributed(n)` with `n>1`: `commit_synchronous == false` (a frame is in flight; D shows the last attested one until the next arrives) and `revocation_immediate == false` (revoking R's render authority darkens D's tab after one network round-trip, not instantly). At `n=1` (R≡D) the SAME code yields `Bounds::LOCAL` — the seL4 framebuffer-cap end-state, present synchronous, revoke instant. **One binary, the bounds slide.** This is `lib.rs::Bounds::distributed` doing exactly what it does for `Distributed{cell}` today.

**Seam.** *Frame freshness / liveness is a bound, not a guarantee.* The attestation proves a frame is the genuine projection of `content_digest @ source_state_root` — it does **not** prove that root is *current* (R could replay an old attested frame, or stall). The closure lever is the receipt chain: D requires the frame's `source_state_root` to be `≥` the last one it composited (monotone, the same `source_state_root` advance `shell.rs::source_state_root` already tracks) and within a freshness window keyed to the surface cell's nonce — turning "is this frame stale?" into the same **monotone-root check** the ledger uses, with the residual (an attacker pins the newest-but-still-old root) bounded by the window. The deeper seam is the §5 **F1 last-hop**: even on D, the attestation binds the *digest the compositor was handed*, not the *scanned-out pixels* — `compositor_pd.rs::FIDELITY` states this plainly. F1 (a display driver that hashes what it scans out) is the named, unclosed primitive; remote rendering inherits it from the local case and adds **no new** trust beyond R's render correctness, which §5 F3 already scopes as "an untrusted render-PD whose output is a frame-cap." Named as work with a lever, never laundered.

---

## (b) Thin clients — a phone holds a display-cap to a tab rendered on your home node

This is 4(a) with the asymmetry pushed to the extreme: the display node is *resource-poor and trusted-only-to-display*, and holds **strictly a display-cap** — the narrowest attenuation in the lattice.

**Mechanism — the phone's cap is a leaf, and a leaf cannot amplify.** The home node H renders (it holds the compute authority + the macaroon that lets the tab fetch, navigate, store — `EMBEDDED-WEB-SURFACE.md` §3). The phone P receives, by `delegate()`, a cap whose rights are the **bottom of the surface lattice**: `present-read` only — no `present`-write (can't paint into the cell), no `navigate`/`fetch`/`new-window` caveats (those live in H's macaroon, never travel), no input-grant *by default*. The phone literally **cannot** make the tab fetch evil.com, because the `fetch` caveat is not in the cap it holds; the request, were it ever formed, routes through `load_web_resource` *on H* against *H's* macaroon. The phone is a glass-and-keyboard for a tab whose authority stays home — the CapDesk "thin untrusted facet-holder" pattern (`EMBEDDED-WEB-SURFACE.md` §5), realized as **a display-cap that is provably ≤ a render-cap** by the same `granted ⊆ held` gate.

**Input from the thin client is a separate, attenuable cap — and it routes through volition.** A phone that may *also* drive the tab holds, in addition, an **input-grant cap** for that surface. An input event from P is not ambient: it is an **attested input-receipt** (`DREGG-DESKTOP-OS.md` §5, "ATTESTED USER-VOLITION") — P signs `(surface CellId ‖ gesture ‖ nonce ‖ target turn-field)` with its **attestation key**, and H's executor-PD requires that signature as a turn premise before a value-moving action commits. The exact same Ed25519 mechanism as the frame attestation, in the reverse direction. So "a phone drives a tab on your home node" decomposes into **two caps**: a display-cap (frames flow P←H) and an optional input-grant-cap (attested gestures flow P→H) — each independently mintable, attenuable, and **revocable** (drop either and that direction goes dark). A shared/borrowed phone gets the display-cap and *not* the input-grant — it can watch the tab, it cannot act as you.

**Bounds.** The phone link is `n>1`: revoke is one round-trip (your home node drops P's cap, P's next frame request is refused — the tab goes dark on the phone within a network hop). Input is `commit_synchronous == false` at the executor: H may require the attested input-receipt to settle before the turn commits, so a value-moving gesture from the phone is *confirmed*, not fire-and-forget — the bound becomes a feature (no silent action on a flaky link).

**Seam.** *The phone's display is outside H's proof (F1 again) AND outside H's IOMMU.* H attests the frame; the phone's GPU/panel showing it faithfully is the phone's local F1 problem, now on hardware H does not control. The honest scope: H's guarantee is "the bytes I sent are the genuine projection of the cell's committed root, and the phone's input-cap is provably ≤ what I granted." What the phone's screen *actually* shows, and whether the phone's OS leaks the frame, is the phone's TCB — named as the boundary, with the lever being the same trusted-path SAK (`§5`) ported to the thin client (a reserved gesture that asks H "is this really my home node's tab?" and gets back the ledger-drawn identity chrome, §d).

---

## (c) Surface migration — the tab cell + state_root move; the receipt chain proves continuity

A running tab moves from node A to node B (you walk from desk to couch; A is going down for maintenance; B is closer to the data). The tab **does not restart** — the surface cell migrates, and **continuity is a theorem about the receipt chain**, not a hope.

**Mechanism — migration is a cap-gated turn that hands off the cell, and the receipt chain is the proof of "same tab."**
1. A surface cell *is* a dregg cell with a `state_root` (`compositor_pd.rs`: the scene/surface state commits to a root; `shell.rs::source_state_root` advances it monotonically per present). The tab's *web* state (the committed URL/origin from `notify_url_changed`, its storage-partition handle, its macaroon, its `content_digest @ source_state_root`) is **in that cell's state**, because §2's authority model already binds every web authority to the surface cell.
2. **Migration = a `delegate`-then-revoke handoff through the real executor.** A `migrate(surface_cell, A → B)` is an `Effect::GrantCapability`-shaped turn: A grants B the full surface authority (an *exact* transfer, not a widening — `is_attenuation` with `requested == held` is admitted; a widening migration is `DelegationDenied`), B installs the cell with its **state_root carried verbatim**, then A's authority is **revoked** (synchronous at the coordinating node). This is `distributed.rs::delegate` + a revoke, i.e. the **same machinery as a window-share** (`shell.rs::share`), with the recipient being a *different node's* surface backing.
3. **The receipt chain proves continuity — this is the dregg-native answer.** Every turn leaves a receipt (the protocol invariant). The migration turn's receipt commits to `(surface CellId, state_root_before @ A, state_root_after @ B, B's pubkey)`. So a light client (or B itself, or you) checks: **the cell that B now serves has the state_root that A's last receipt committed, and the migration receipt chains them** — `state_root_after@B == state_root_at_A's_final_present`, signed, on the blocklace. The tab on B is provably the *same* tab that was on A: not "B claims it restored your session" (the open web's cookie-and-pray) but **a receipt chain a light client verifies, unfoolable by the pale ghost** (`AssuranceCase.lean::unfoolability_guarantee`, carried to the surface). The CellId is stable across the move (it's the cell's identity, not its host); the `source_state_root` is monotone across the move (the migration receipt is one more advance); so D's display-cap (4a) and P's thin-client cap (4b) **survive migration** — they point at the CellId, and after the handoff their next frame request resolves to B instead of A, transparently.

**The web-state subtlety (honest).** The tab's *storage partition* (`EMBEDDED-WEB-SURFACE.md` §2.1, "partition-by-cap") must move with the cell or be reachable from B. Two faithful options: (i) the partition is itself a **NOTE-backed dregg cell** (content-addressed, `rbg/src/vfs.rs`: "the address IS the content"), so B reaches it by the same content-hash A did — *no copy, the address travels*; (ii) for an ephemeral partition, its current contents are part of the migrated `state_root` and cross with it. Live in-flight Servo internal state (a half-loaded page, JS heap) is **not** in the cell's committed root — so migration is *clean at present-boundaries*: B re-renders from the committed URL + storage, reaching the same `content_digest`. "Continuity" is **state-and-authority continuity with a deterministic re-render**, not live-VM teleport. Stated precisely as the boundary of the claim.

**Bounds.** During the in-flight window, the tab is momentarily `Bounds` with both relaxed (neither A nor B is synchronously authoritative); the migration turn's commit *is* the atomic switch (the receipt is the linearization point — `Effect::GrantCapability` + revoke is one turn, so there is no double-authority instant: this is the `granted ⊆ held` + synchronous-revoke discipline, the same one `revoke_is_synchronous_and_transitive` proves locally). At `n=1` "migration" between two PDs on one box is the synchronous handoff; across the WAN the bound relaxes to one-round-trip, verbs unchanged.

**Seam.** *Atomicity of migrate-then-revoke across two nodes is a distributed-commit obligation.* On one machine the grant+revoke is one synchronous turn. Across A and B it needs the two nodes to agree on the linearization point — which is exactly what dregg's **`coord/src/atomic.rs` two-phase-commit** (`evaluate_votes`, Commit/Abort exclusivity, modeled in `Coord/TwoPhaseCommit.lean`) is for, and what the **`CapTPConsentLace` signed-blocklace consent-binding** (task #61) already builds for multi-party suspended settlement. The closure lever is "migration is a 2PC over the surface cell"; the residual (a node crashes mid-handoff) is bounded by the same abort/timeout the coordinator already proves — the tab stays on A (the migration aborts) rather than vanishing. Named as a distributed-commit seam with the coordinator as the lever, not a wall.

---

## (d) The anti-spoof trust story across the network — identity from the LEDGER, render output attested

The keystone property of the *local* desktop (`DREGG-DESKTOP-OS.md` §5 T2; `EMBEDDED-WEB-SURFACE.md` §1: "the chrome is the shell's, never the page's") is that **the identity a user reads is the shell's attestation drawn from the live ledger, not the surface's self-description.** Facet 4 must preserve this when render and display are on *different nodes* — otherwise a malicious render node R is just a new pale ghost painting a fake address bar from across the wire.

**Mechanism — two independent attestations meet at the display node, and neither is the render node's word.**
1. **Identity chrome is drawn by D from the LEDGER, not from R's frame.** When D composites the remote tab, the trusted-path origin badge (the URL/origin, TLS state, cap-scope, and *which node renders it*) is computed by **D's compositor** via `label_of(owner, source_state_root)` (`compositor_pd.rs::label_of`) — a function of the **surface cell's committed state**, which D reads from the blocklace ledger it independently syncs (the node already gossips/syncs the blocklace — `node/src/blocklace_sync.rs`). R's frame fills *only* `SurfaceId::region()` (the body); the badge is a `SceneItem` field **D** computes, in D's title-bar zone, where T1 non-overlap makes an R-frame paint over it **UNSAT** (`Scene::scene_admit`). So R **cannot** paint a fake `🔒 yourbank.com` badge onto D's chrome for the *exact* structural reason a local page can't: the body region is clipped, the chrome is the compositor's, and here the compositor is **D's**, reading **D's** copy of the ledger. The pale ghost on the display path is closed across the network by the same tooth that closes it locally — **moved to D, drawn from a ledger D verifies, not a frame R sent.**
2. **Render output is attested (so D knows the body is genuine, not just that the chrome is D's).** The body could still be a lie if R sends garbage — so the frame carries R's Ed25519 signature over `(CellId ‖ content_digest ‖ source_state_root)` (4a). D verifies it (`turn_gate.rs::verify_strict`) and checks `source_state_root` against **D's ledger-known root for that cell**. So D learns two independent things: *the chrome is mine, drawn from the ledger* (identity unspoofable) **and** *the body is the genuine projection of the cell's committed root, signed by the authorized renderer* (content unspoofable). The render node's identity itself is a **ledger fact**: which node holds the surface cell's render authority is recorded (the migration receipts of §c are the audit trail), so D's badge can honestly show "rendered by node R (held since receipt #N)" — and if R is *not* the cell's authorized renderer, R's frame signature is over a `source_state_root` D's ledger doesn't recognize, and **D refuses to composite it**, falling to the `missing`/`stale` chrome the local shell already shows for a dangling surface (`shell.rs`: `a_dangling_surface_is_labelled_missing_not_spoofable`).
3. **The trusted-path SAK works across the network.** The secure-attention gesture (`§5`, the tiny trusted-path PD holding the SOLE top-zLayer cap) is a **D-local** anchor: when you invoke it, D draws the unspoofable overlay from **D's** ledger-read of the surface cell — "this tab is CellId X, rendered by node R, committed root S, origin `yourbank.com`" — none of it from R. The thin client (4b) ports the same SAK to the phone. So "who am I really talking to, across the network?" is answered by **D's local trusted path reading D's verified ledger**, which is the strongest possible answer: it does not trust the render node, the transport, or the frame.

**Seam.** *D must have a trustworthy view of the ledger, and D's own display path is its local F1.* The identity guarantee reduces to "D syncs the blocklace honestly" — which is the **light-client unfoolability** dregg already proves (`unfoolability_guarantee`): D checking `verify root = true` cannot be fooled about the cell's committed state, *including which node renders it*. So the network anti-spoof story **bottoms out at the same theorem as the protocol's** — the strongest available floor, not a new assumption. The two residuals are named: (i) **D's last-hop F1** (D's own panel faithfully showing what D composited — inherited from the local case, lever = a frame-hashing display driver); (ii) **render-node liveness** (R is the authorized renderer but stalls/replays — the §a freshness-window + monotone-root lever bounds it). Neither is hidden; both have levers; the *identity* property (you cannot be shown a tab claiming to be a cell it isn't, by any node across the network) is a **theorem reducing to ledger unfoolability**, the same crown-jewel floor.

---

## (e) The budget angle — rendering is metered computrons; remote render is a cap-gated, Stingray-bounded service

Rendering is *compute* — and in dregg compute is **metered**, never ambient. Every turn runs against `ComputronCosts` (`turn/src/executor/costs.rs`, threaded into `TurnExecutor::new(ComputronCosts::...)` — the firmament's `DistributedBacking` constructs its executor with exactly this). So "remote render" is not a free favor R does for D; it is a **priced service R sells, bounded by a cap.**

**Mechanism — a render-cap carries a computron ceiling, enforced by the existing Stingray bounded counter.**
1. **A render request is a turn, so it costs computrons.** When D (or P) asks R to render a frame, that is work R performs — and R charges it against the **render-cap's budget**. The render-cap is a `Capability { Surface(cell), rights }` whose macaroon carries a `compute ≤ K computrons / epoch` caveat (one more caveat alongside `fetch ⊆ {...}`, §3 of `EMBEDDED-WEB-SURFACE.md`). The display node's authority to *cause rendering* is therefore **finite and named**.
2. **Stingray bounds the overspend — the mechanism already exists.** `coord/src/shared_budget.rs` is *literally* "the Stingray bounded counter generalized from one agent's budget to a shared resource": each client gets a **local `BudgetCeiling { ceiling, spent, remaining() }`**; debits within the ceiling proceed *without coordination* (D can request frames at the rendering rate it paid for, no per-frame round-trip to a global authority); when the ceiling is hit, `try_debit` returns `Err(AllowanceExhausted)` and R **refuses to render another frame** (the tab freezes on D until the budget refreshes or D's cap is topped up). The **maximum overspend across all of R's display clients is bounded by `f * allowance`** (the Stingray-ceiling theorem, `Coord/SharedBudgetDynamics.lean`, task #87) — so a misbehaving/greedy display node cannot make R render unboundedly. "Remote render is a Stingray-bounded service" is *exactly* `BudgetCeiling::try_debit` over a render-cap, with the bound being the theorem dregg already proved.
3. **The economic shape is honest and symmetric.** The home node (4b) rendering for your phone spends *your* computron budget; a render *farm* (a beefy node rendering for thin clients) sells render-caps with computron ceilings and **gets paid in the same metered unit** — rendering becomes a first-class dregg service priced in computrons, gated by a cap, bounded by Stingray, with every render a turn that leaves a receipt (so the bill is auditable: "node R rendered N frames for cell X at K computrons each, here are the receipts"). This is the `DREGG-DESKTOP-OS.md` §2 "pay-for-resources" vision applied to pixels: **the framebuffer is reached through a cap, and the *compute behind it* is reached through a budget.**

**Seam.** *Computron-pricing of GPU/Servo work is a calibration + measurement obligation, not a model gap.* `ComputronCosts::zero()` is what the firmament's test backing uses today — the **mechanism** (meter every render turn, debit a Stingray ceiling, refuse past it) is real and proved; the **calibration** (how many computrons *is* a Servo layout + paint of region R at resolution W?) is unmeasured. The honest lever is the MINTED *measure-before-believing-a-lever* discipline: instrument R's render PD, attribute wall-cost to the present-turn, and set the caveat ceiling from measurement — the same way the circuit's real lever was found by measurement, not assumption. Until then the ceiling is *enforceable but not yet economically tuned*: the bound holds (no unbounded render), the *price* is a knob to be measured. Named as a measurement obligation with the meter already in place, not a missing model. A second seam: a render node could *under-deliver* (charge for a frame it renders cheaply/wrongly) — closed by §d's frame attestation (the receipt binds the frame to `content_digest`, so an attested-but-wrong frame is detectable against D's ledger-known root), turning "did I get what I paid for?" into the same monotone-root check.

---

## Synthesis — one model, four points on `n`, every seam with a lever

The facet is a single structural claim: **`Local{slot}` → `Distributed{cell}` → `Surface{cell}` → render-and-display-on-different-nodes is one walk along the firmament's distance parameter,** and distributed rendering is reached by *relaxing `Bounds`*, never by inventing a transport or a second authority model. The mechanisms are all in-tree and load-bearing:

| facet | mechanism (real surface) | the bound that slides | the seam + its lever |
|---|---|---|---|
| (a) remote render → local display | net-PD ring for bytes + Ed25519 frame-attest (`turn_gate.rs::verify_strict`, the `[32 pk][64 sig][msg]` envelope) over `content_digest @ source_state_root` + D's local `Scene::scene_admit` + attenuated read-cap (`distributed.rs::delegate`) | `Bounds::distributed(n)`: present async, revoke one-hop; `LOCAL` at n=1 | F1 last-hop (digest≠scanned pixels, `compositor_pd::FIDELITY`) + frame freshness → **monotone-root + freshness-window** lever |
| (b) thin client (phone ← home node) | display-cap = bottom of the surface lattice (`granted ⊆ held`, provably ≤ render-cap); optional input-grant = attested input-receipt (`§5` volition, same Ed25519) | `n>1`: revoke one-hop; input `commit_synchronous=false` = confirmed action | phone's panel is its own F1/TCB → trusted-path SAK ported to the client |
| (c) surface migration (A→B) | `migrate` = `Effect::GrantCapability`(exact, widening=`DelegationDenied`)+synchronous revoke; **receipt chain** binds `state_root_before@A ↔ state_root_after@B` (unfoolable continuity); CellId stable, `source_state_root` monotone across move; storage = NOTE-backed content-addressed cell (`rbg/vfs`: address travels) | atomic switch = the migration receipt (linearization point); n=1 synchronous, WAN one-hop | cross-node atomicity → **`coord/atomic.rs` 2PC / `CapTPConsentLace`** lever; crash → abort-to-A |
| (d) anti-spoof across the network | identity chrome drawn by **D** from **D's ledger** via `label_of(owner, source_state_root)` (T1 clips R's frame to the body, badge is D's); render output Ed25519-attested against D's ledger-known root; SAK is D-local reading D's ledger | — (identity is `n`-invariant: always the local ledger) | reduces to **light-client `unfoolability_guarantee`** (the crown floor) + D's local F1 |
| (e) budget | render = a turn costing `ComputronCosts`; render-cap carries `compute ≤ K`/epoch caveat; **`BudgetCeiling::try_debit` → `AllowanceExhausted`** (Stingray, `shared_budget.rs`), overspend bounded `f·allowance` (`SharedBudgetDynamics.lean`) | — (the ceiling is enforced regardless of `n`) | computron *price* of GPU/Servo work unmeasured → **measure-before-believing** (the meter exists; calibrate it); under-delivery → §d frame-attest detects it |

The two honest floors everything bottoms out at are the **same two the rest of dregg already names**: the graphics **F1/F2** crypto-floor (digest-vs-scanned-pixels, IOMMU/DMA — `DREGG-DESKTOP-OS.md` §5, the named-primitive equivalent of the cryptographic floor, with closure levers, never walls) and **light-client unfoolability** (`AssuranceCase.lean::unfoolability_guarantee` — the strongest available floor, which the network anti-spoof story *reduces to* rather than weakening). Nothing in facet 4 introduces a *new* terminal assumption: every seam either reduces to one of those two floors or carries a concrete lever (monotone-root freshness, 2PC migration, measured-computron pricing) already built or buildable in-tree.

---

*A web surface is rendered where the computrons are and displayed where the glass is, and the wire between them carries attested frames, not trust. The display node holds a read-cap and draws its identity chrome from the ledger; the render node holds the budget and signs every frame to the cell's committed root; a tab migrates as a receipt chain a light client can't be fooled about; and rendering is a Stingray-bounded service priced in the same metered computron as everything else. It is the seL4 framebuffer-cap end-state with the render and display ends slid apart along `n` — the firmament's one capability handle carried out past the glass and across the network, with the bounds the only thing that moved.*

Key file anchors (all real, all absolute):
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/lib.rs` — `Bounds { revocation_immediate, commit_synchronous, n }`, `LOCAL`, `distributed(n)`; the `Target` walk
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/distributed.rs` — `DistributedBacking` (real `Ledger`+`TurnExecutor`), `invoke`→`Bounds::distributed`, `delegate` rejects widening (`DelegationDenied`)
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/compositor_pd.rs` — `Surface { owner, region, content_digest, source_state_root, focus }`, `Scene::scene_admit`, `label_of`, the `FIDELITY` F1 note
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/process_kernel.rs` — `CapHandle { slot, epoch }`, validity-in-kernel-table, `CapError::Forged` (the unforgeable cross-address-space handle the cross-network read-cap generalizes)
- `/Users/ember/dev/breadstuffs/sel4/dregg-pd/net-client/src/turn_gate.rs` — Ed25519 `verify_strict` over `[32 pk][64 sig][msg]` (the frame/input attestation primitive, verbatim)
- `/Users/ember/dev/breadstuffs/coord/src/shared_budget.rs` — `BudgetCeiling { ceiling, spent, remaining(), try_debit() → AllowanceExhausted }`, Stingray-bounded, overspend `f·allowance`
- `/Users/ember/dev/breadstuffs/turn/src/executor/costs.rs` — `ComputronCosts` (every render-turn is metered)
- `/Users/ember/dev/breadstuffs/starbridge-v2/src/shell.rs` — `present()`, `source_state_root()` (monotone), `share()`→`DelegationDenied`, `identity_of` (dangling→`missing`, not spoofable); `/Users/ember/dev/breadstuffs/starbridge-v2/src/surface.rs` — `SurfaceCapability` over the real firmament cap
- `/Users/ember/dev/breadstuffs/coord/src/atomic.rs` — 2PC `evaluate_votes` (the migration-atomicity lever)
- `/Users/ember/dev/breadstuffs/rbg/src/vfs.rs` — content-addressed NOTE store ("the address IS the content" — migrating storage = the address travels)
